// SPDX-License-Identifier: MIT

//! Result sets, summary table formatting, `fuchsiaperf.json` serialization, and schema validation.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write;

use crate::stats::summarize;

/// Suite identifier written into every runtime `fuchsiaperf.json` record.
pub const TEST_SUITE: &str = "atmosphere.microbenchmarks";

/// Line emitted directly before the serialized `fuchsiaperf.json` array on the serial console.
pub const JSON_BEGIN_MARKER: &str = "--- FUCHSIAPERF JSON BEGIN ---";

/// Line emitted directly after the serialized `fuchsiaperf.json` array on the serial console.
pub const JSON_END_MARKER: &str = "--- FUCHSIAPERF JSON END ---";

/// Values collected for one benchmark series (`label` + `unit`).
#[derive(Clone, Debug, PartialEq)]
pub struct TestCaseResults {
    pub test_suite: String,
    pub label: String,
    pub unit: String,
    pub values: Vec<f64>,
}

/// Ordered collection of result series emitted by a benchmark run.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ResultsSet {
    pub results: Vec<TestCaseResults>,
}

impl ResultsSet {
    /// Creates an empty result set.
    pub const fn new() -> Self {
        Self {
            results: Vec::new(),
        }
    }

    /// Appends an empty named series and returns a mutable handle for filling its batch values.
    pub fn add_test_case(
        &mut self,
        test_suite: &str,
        label: &str,
        unit: &str,
    ) -> &mut TestCaseResults {
        self.results.push(TestCaseResults {
            test_suite: String::from(test_suite),
            label: String::from(label),
            unit: String::from(unit),
            values: Vec::new(),
        });
        let idx = self.results.len() - 1;
        &mut self.results[idx]
    }

    /// Formats the fixed-width per-batch summary table (`Mean Std dev Min Max Median Unit Test case`).
    pub fn print_summary_table(&self, out: &mut dyn Write) -> core::fmt::Result {
        writeln!(
            out,
            "{:>10} {:>10} {:>10} {:>10} {:>10} {:<12} {}",
            "Mean", "Std dev", "Min", "Max", "Median", "Unit", "Test case"
        )?;
        if self.results.is_empty() {
            return writeln!(out, "(No test results)");
        }
        for case in &self.results {
            if let Some(stats) = summarize(&case.values) {
                writeln!(
                    out,
                    "{:>10.2} {:>10.2} {:>10.2} {:>10.2} {:>10.2} {:<12} {}",
                    stats.mean,
                    stats.std_dev,
                    stats.min,
                    stats.max,
                    stats.median,
                    case.unit,
                    case.label
                )?;
            } else {
                writeln!(
                    out,
                    "{:>10} {:>10} {:>10} {:>10} {:>10} {:<12} {}",
                    "NaN", "NaN", "NaN", "NaN", "NaN", case.unit, case.label
                )?;
            }
        }
        Ok(())
    }

    /// Serializes this result set as a runtime `fuchsiaperf.json` array.
    pub fn write_json(&self, out: &mut dyn Write) -> core::fmt::Result {
        out.write_str("[\n")?;
        for (i, case) in self.results.iter().enumerate() {
            if i > 0 {
                out.write_str(",\n")?;
            }
            out.write_str("{\"label\":")?;
            write_json_str(out, &case.label)?;
            out.write_str(",\"test_suite\":")?;
            write_json_str(out, &case.test_suite)?;
            out.write_str(",\"unit\":")?;
            write_json_str(out, &case.unit)?;
            out.write_str(",\"values\":[")?;
            for (j, &value) in case.values.iter().enumerate() {
                if j > 0 {
                    out.write_char(',')?;
                }
                if value.is_finite() {
                    write!(out, "{value:.6}")?;
                } else {
                    out.write_str("0.000000")?;
                }
            }
            out.write_str("]}")?;
        }
        if !self.results.is_empty() {
            out.write_char('\n')?;
        }
        out.write_char(']')
    }
}

fn write_json_str(out: &mut dyn Write, text: &str) -> core::fmt::Result {
    out.write_char('"')?;
    for byte in text.bytes() {
        match byte {
            b'"' => out.write_str("\\\"")?,
            b'\\' => out.write_str("\\\\")?,
            b'\n' => out.write_str("\\n")?,
            b'\r' => out.write_str("\\r")?,
            b'\t' => out.write_str("\\t")?,
            0x00..=0x1f | 0x7f..=0xff => write!(out, "\\u{:04x}", byte)?,
            _ => out.write_char(byte as char)?,
        }
    }
    out.write_char('"')
}

/// Extracts the JSON payload delimited by `JSON_BEGIN_MARKER` and `JSON_END_MARKER` from a serial log.
pub fn extract_perftest_json(log: &str) -> Option<&str> {
    let mut begin_end = None;
    let mut offset = 0usize;
    for raw_line in log.split('\n') {
        let line_len_with_lf = raw_line.len() + 1;
        let trimmed = raw_line.trim_end_matches('\r');
        if trimmed == JSON_BEGIN_MARKER {
            let after = offset + line_len_with_lf;
            if after <= log.len() {
                begin_end = Some(after);
            }
        } else if trimmed == JSON_END_MARKER {
            if let Some(start) = begin_end {
                let slice = log[start..offset].trim_end_matches(&['\r', '\n'][..]);
                return Some(slice);
            }
        }
        offset = offset.saturating_add(line_len_with_lf);
    }
    None
}

struct JsonParser<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> JsonParser<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            bytes: input.as_bytes(),
            pos: 0,
        }
    }

    fn skip_ws(&mut self) {
        while let Some(&b) = self.bytes.get(self.pos) {
            if matches!(b, b' ' | b'\n' | b'\r' | b'\t') {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn expect(&mut self, ch: u8) -> Result<(), &'static str> {
        self.skip_ws();
        if self.bytes.get(self.pos) == Some(&ch) {
            self.pos += 1;
            Ok(())
        } else {
            Err("unexpected character in perftest JSON")
        }
    }

    fn peek(&mut self) -> Option<u8> {
        self.skip_ws();
        self.bytes.get(self.pos).copied()
    }

    fn parse_string(&mut self) -> Result<String, &'static str> {
        self.expect(b'"')?;
        let mut out = String::new();
        while let Some(&b) = self.bytes.get(self.pos) {
            self.pos += 1;
            match b {
                b'"' => return Ok(out),
                b'\\' => {
                    let esc = *self.bytes.get(self.pos).ok_or("truncated escape")?;
                    self.pos += 1;
                    match esc {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\x08'),
                        b'f' => out.push('\x0c'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let hex = self.bytes.get(self.pos..self.pos + 4).ok_or("bad \\u escape")?;
                            self.pos += 4;
                            let hex_str =
                                core::str::from_utf8(hex).map_err(|_| "bad utf8 in \\u escape")?;
                            let code = u32::from_str_radix(hex_str, 16)
                                .map_err(|_| "invalid hex in \\u escape")?;
                            let ch = char::from_u32(code).ok_or("invalid scalar in \\u escape")?;
                            out.push(ch);
                        }
                        _ => return Err("unsupported JSON escape"),
                    }
                }
                0x00..=0x1f => return Err("unescaped control byte in JSON string"),
                _ => out.push(b as char),
            }
        }
        Err("unterminated JSON string")
    }

    fn parse_number(&mut self) -> Result<f64, &'static str> {
        self.skip_ws();
        let start = self.pos;
        while let Some(&b) = self.bytes.get(self.pos) {
            if b.is_ascii_digit() || matches!(b, b'-' | b'+' | b'.' | b'e' | b'E') {
                self.pos += 1;
            } else {
                break;
            }
        }
        let raw = core::str::from_utf8(&self.bytes[start..self.pos]).map_err(|_| "bad utf8")?;
        if raw.is_empty() {
            return Err("expected JSON number");
        }
        let val = raw.parse::<f64>().map_err(|_| "invalid JSON number")?;
        if !val.is_finite() {
            return Err("non-finite JSON number");
        }
        Ok(val)
    }

    fn parse_values(&mut self) -> Result<Vec<f64>, &'static str> {
        self.expect(b'[')?;
        let mut values = Vec::new();
        if self.peek() == Some(b']') {
            self.pos += 1;
            return Ok(values);
        }
        loop {
            values.push(self.parse_number()?);
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b']') => {
                    self.pos += 1;
                    return Ok(values);
                }
                _ => return Err("expected ',' or ']' in values array"),
            }
        }
    }

    fn parse_entry(&mut self) -> Result<TestCaseResults, &'static str> {
        self.expect(b'{')?;
        let mut label: Option<String> = None;
        let mut test_suite: Option<String> = None;
        let mut unit: Option<String> = None;
        let mut values: Option<Vec<f64>> = None;
        if self.peek() == Some(b'}') {
            return Err("empty benchmark JSON object");
        }
        loop {
            let key = self.parse_string()?;
            self.expect(b':')?;
            match key.as_str() {
                "label" => {
                    if label.is_some() {
                        return Err("duplicate label field");
                    }
                    label = Some(self.parse_string()?);
                }
                "test_suite" => {
                    if test_suite.is_some() {
                        return Err("duplicate test_suite field");
                    }
                    test_suite = Some(self.parse_string()?);
                }
                "unit" => {
                    if unit.is_some() {
                        return Err("duplicate unit field");
                    }
                    unit = Some(self.parse_string()?);
                }
                "values" => {
                    if values.is_some() {
                        return Err("duplicate values field");
                    }
                    values = Some(self.parse_values()?);
                }
                _ => return Err("unexpected key in perftest JSON object"),
            }
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b'}') => {
                    self.pos += 1;
                    break;
                }
                _ => return Err("expected ',' or '}' in perftest JSON object"),
            }
        }
        let label = label.ok_or("missing label field")?;
        let test_suite = test_suite.ok_or("missing test_suite field")?;
        let unit = unit.ok_or("missing unit field")?;
        let values = values.ok_or("missing values field")?;
        if label.is_empty() || test_suite.is_empty() || unit.is_empty() || values.is_empty() {
            return Err("empty required perftest JSON field");
        }
        Ok(TestCaseResults {
            test_suite,
            label,
            unit,
            values,
        })
    }

    fn parse_array(&mut self) -> Result<Vec<TestCaseResults>, &'static str> {
        self.expect(b'[')?;
        let mut entries = Vec::new();
        if self.peek() == Some(b']') {
            self.pos += 1;
            self.skip_ws();
            if self.pos != self.bytes.len() {
                return Err("trailing characters after JSON array");
            }
            return Ok(entries);
        }
        loop {
            entries.push(self.parse_entry()?);
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b']') => {
                    self.pos += 1;
                    break;
                }
                _ => return Err("expected ',' or ']' in top-level array"),
            }
        }
        self.skip_ws();
        if self.pos != self.bytes.len() {
            return Err("trailing characters after JSON array");
        }
        Ok(entries)
    }
}

/// Parses and validates a runtime `fuchsiaperf.json` array (`[{"label","test_suite","unit","values"}]`).
pub fn parse_perftest_json(json: &str) -> Result<Vec<TestCaseResults>, &'static str> {
    JsonParser::new(json).parse_array()
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{format, vec};

    #[test]
    fn json_round_trip_and_escaping() {
        let mut set = ResultsSet::new();
        set.add_test_case(TEST_SUITE, "Syscall/Null\"quote\\slash\n", "nanoseconds")
            .values
            .extend([123.5, 125.0]);
        set.add_test_case(TEST_SUITE, "Syscall/Null.tsc_cycles", "cycles")
            .values
            .extend([300.0, 310.0]);

        let mut json = String::new();
        set.write_json(&mut json).expect("write_json");
        let parsed = parse_perftest_json(&json).expect("valid perftest JSON");
        assert_eq!(parsed.len(), 2);
        assert_eq!(parsed[0].label, "Syscall/Null\"quote\\slash\n");
        assert_eq!(parsed[0].unit, "nanoseconds");
        assert_eq!(parsed[0].values, vec![123.5, 125.0]);
        assert_eq!(parsed[1].label, "Syscall/Null.tsc_cycles");
    }

    #[test]
    fn json_extraction_handles_ansi_and_crlf_logs() {
        let log = format!(
            "\x1b[34m INFO boot ok\x1b[0m\r\n{JSON_BEGIN_MARKER}\r\n[{{\"label\":\"Syscall/Null\",\"test_suite\":\"{TEST_SUITE}\",\"unit\":\"nanoseconds\",\"values\":[10.0,12.0]}}]\r\n{JSON_END_MARKER}\r\ndom0 capability done\r\n"
        );
        let extracted = extract_perftest_json(&log).expect("extract markers");
        let parsed = parse_perftest_json(extracted).expect("parse extracted");
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].label, "Syscall/Null");
        assert_eq!(parsed[0].values, vec![10.0, 12.0]);
    }

    #[test]
    fn json_parser_rejects_malformed_or_missing_schema_fields() {
        assert!(parse_perftest_json("[]").is_ok());
        assert!(parse_perftest_json("{}").is_err());
        assert!(parse_perftest_json("[{\"label\":\"x\",\"unit\":\"ns\",\"values\":[1]}]").is_err());
        assert!(parse_perftest_json(
            "[{\"label\":\"x\",\"test_suite\":\"atmosphere.microbenchmarks\",\"unit\":\"ns\",\"values\":[]}]"
        )
        .is_err());
        assert!(parse_perftest_json(
            "[{\"label\":\"x\",\"test_suite\":\"atmosphere.microbenchmarks\",\"unit\":\"ns\",\"values\":[1],\"extra\":1}]"
        )
        .is_err());
    }

    #[test]
    fn summary_table_includes_header_and_metrics() {
        let mut set = ResultsSet::new();
        set.add_test_case(TEST_SUITE, "Syscall/Null", "nanoseconds")
            .values
            .extend([10.0, 20.0, 30.0]);
        let mut table = String::new();
        set.print_summary_table(&mut table).expect("summary table");
        assert!(table.contains("Mean"));
        assert!(table.contains("Median"));
        assert!(table.contains("Unit"));
        assert!(table.contains("Syscall/Null"));
        assert!(table.contains("20.00"));
    }
}
