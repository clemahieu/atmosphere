// SPDX-License-Identifier: MIT

//! Batch summary statistics (`min`, `max`, `mean`, population `std_dev`, interpolated `median`).

use alloc::vec::Vec;

/// Summary statistics over a batch sample series, matching Fuchsia `perftest::SummaryStatistics`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SummaryStatistics {
    pub min: f64,
    pub max: f64,
    pub mean: f64,
    pub std_dev: f64,
    pub median: f64,
}

/// Computes `sqrt(x)` in `#![no_std]` using IEEE-754 exponent halving + Newton-Raphson refinement.
pub fn sqrt_f64(x: f64) -> f64 {
    if x < 0.0 || x.is_nan() {
        return f64::NAN;
    }
    if x == 0.0 || x.is_infinite() {
        return x;
    }
    // Scale subnormal inputs into the normal range by 2^54 so exponent halving stays normalized.
    const TWO_POW_54: f64 = 18_014_398_509_481_984.0;
    const INV_TWO_POW_27: f64 = 1.0 / 134_217_728.0;
    let (scaled, scale_back) = if x < f64::MIN_POSITIVE {
        (x * TWO_POW_54, INV_TWO_POW_27)
    } else {
        (x, 1.0)
    };
    let guess_bits = (scaled.to_bits() >> 1) + (0x3ff0_0000_0000_0000_u64 >> 1);
    let mut y = f64::from_bits(guess_bits);
    for _ in 0..7 {
        y = 0.5 * (y + scaled / y);
    }
    y * scale_back
}

/// Summarizes a non-empty slice of finite sample values. Returns `None` if empty or non-finite.
pub fn summarize(values: &[f64]) -> Option<SummaryStatistics> {
    if values.is_empty() || values.iter().any(|v| !v.is_finite()) {
        return None;
    }
    let mut min = values[0];
    let mut max = values[0];
    let mut sum = 0.0;
    for &value in values {
        if value < min {
            min = value;
        }
        if value > max {
            max = value;
        }
        sum += value;
    }
    let n = values.len() as f64;
    let mean = sum / n;
    let mut sum_sq = 0.0;
    for &value in values {
        let diff = value - mean;
        sum_sq += diff * diff;
    }
    let std_dev = sqrt_f64(sum_sq / n);

    let mut sorted = Vec::with_capacity(values.len());
    sorted.extend_from_slice(values);
    sorted.sort_by(f64::total_cmp);
    let mid = sorted.len() / 2;
    let median = if sorted.len().is_multiple_of(2) {
        (sorted[mid - 1] + sorted[mid]) * 0.5
    } else {
        sorted[mid]
    };

    Some(SummaryStatistics {
        min,
        max,
        mean,
        std_dev,
        median,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn summarize_empty_returns_none() {
        assert_eq!(summarize(&[]), None);
        assert_eq!(summarize(&[1.0, f64::NAN]), None);
    }

    #[test]
    fn summarize_odd_and_even_medians_and_population_stddev() {
        let odd = summarize(&[100.0, 10.0, 20.0]).expect("non-empty");
        assert_eq!(odd.min, 10.0);
        assert_eq!(odd.max, 100.0);
        assert_eq!(odd.median, 20.0);
        assert!((odd.mean - 130.0 / 3.0).abs() < 1e-12);

        let even = summarize(&[40.0, 10.0, 30.0, 20.0]).expect("non-empty");
        assert_eq!(even.min, 10.0);
        assert_eq!(even.max, 40.0);
        assert_eq!(even.mean, 25.0);
        assert_eq!(even.median, 25.0);
        let expected_std = (125.0_f64).sqrt();
        assert!((even.std_dev - expected_std).abs() < 1e-12);
    }

    #[test]
    fn sqrt_f64_matches_std_across_scales() {
        for &v in &[0.0_f64, 1.0, 2.0, 1e-12, 1e18, f64::MIN_POSITIVE, 5e-315] {
            let got = sqrt_f64(v);
            let want = v.sqrt();
            let diff = (got - want).abs();
            assert!(diff <= want * 1e-15 + 1e-320, "v={v} got={got} want={want}");
        }
        assert!(sqrt_f64(-1.0).is_nan());
    }
}
