//! ACPI.

use core::mem;
use core::ptr;
use core::slice;

use acpi::{AcpiTables, AcpiTable, PhysicalMapping};
use acpi::handler::AcpiHandler;
use acpi::sdt::{Signature, SdtHeader};

#[derive(Clone, Debug)]
struct NullAcpiHandler {}

#[derive(Debug)]
#[repr(C, packed)]
struct Dmar {
    header: SdtHeader,

    host_address_width: u8,
    flags: u8,
    _reserved: [u8; 10],
}

#[derive(Debug, Clone, Copy)]
#[repr(C, packed)]
struct RemappingHeader {
    struct_type: u16,
    length: u16,
}

#[derive(Debug)]
struct RemappingPtrIter {
    cur: *const u8,
    limit: *const u8,
}

/// DMA Remapping Hardware Unit Definition
///
/// Section 8.3
#[derive(Debug)]
#[repr(C, packed)]
struct Drhd {
    header: RemappingHeader,
    flags: u8,
    size: u8,
    segment_number: u16,
    register_base_address: u64,
}

impl NullAcpiHandler {
    fn new() -> Self {
        Self {}
    }
}

impl AcpiHandler for NullAcpiHandler {
    unsafe fn map_physical_region<T>(&self, physical_address: usize, size: usize) -> PhysicalMapping<Self, T> {
        let p = ptr::NonNull::new_unchecked(physical_address as *mut T);
        PhysicalMapping::new(
            physical_address,
            p,
            size,
            size,
            self.clone(),
        )
    }

    fn unmap_physical_region<T>(_region: &PhysicalMapping<Self, T>) {
        // no-op
    }
}

impl Dmar {
    fn iter_remapping_structs(&self) -> RemappingPtrIter {
        let entries_length = self.header.length as usize - mem::size_of::<Self>();
        let start = unsafe {
            (self as *const Self).add(1) as *const u8
        };
        let limit = unsafe {
            start.add(entries_length)
        };
        RemappingPtrIter {
            cur: start,
            limit,
        }
    }
}

unsafe impl AcpiTable for Dmar {
    const SIGNATURE: Signature = Signature::DMAR;

    fn header(&self) -> &SdtHeader {
        &self.header
    }
}

impl Iterator for RemappingPtrIter {
    type Item = &'static RemappingHeader;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cur >= self.limit {
            return None;
        }

        let header = unsafe {
            &*(self.cur as *const RemappingHeader)
        };
        self.cur = unsafe {
            self.cur.add(header.length as usize)
        };

        log::info!("Header: {:?}", header);

        Some(header)
    }
}

impl RemappingHeader {
    const TYPE_DRHD: u16 = 0;

    fn as_drhd<'a>(&self) -> Option<&'a Drhd> {
        if self.struct_type != Self::TYPE_DRHD {
            return None;
        }

        let p = self as *const RemappingHeader as *const Drhd;
        let r = unsafe { &*p };
        Some(r)
    }
}

/// The IO Remapping Table, Arm DEN 0049 E.g, cited as IORT: the header, then nodes this module
/// reads as bytes.
#[repr(C, packed)]
struct Iort {
    header: SdtHeader,
}

unsafe impl AcpiTable for Iort {
    const SIGNATURE: Signature = Signature::IORT;

    fn header(&self) -> &SdtHeader {
        &self.header
    }
}

/// IORT Table 3: the number of nodes, at byte 36, and the offset of the first, at 40.
const IORT_NODE_COUNT: usize = 36;
const IORT_NODE_OFFSET: usize = 40;

/// IORT Table 4: a node's type, at byte 0, and its length, at 1; the bytes a node has at least.
const NODE_LENGTH: usize = 1;
const NODE_HEADER_BYTES: usize = 16;

/// IORT Table 13: an SMMUv3 node is type 4, its registers' base address at byte 16.
const NODE_SMMUV3: u8 = 4;
const SMMUV3_BASE: usize = 16;

/// The `N` bytes of `table` at `at`.
fn bytes<const N: usize>(table: &[u8], at: usize) -> Result<[u8; N], &'static str> {
    let field = table.get(at..at + N).ok_or("IORT shorter than what it holds")?;
    Ok(field.try_into().unwrap())
}

/// The register base of the first SMMUv3 the IORT `table` names, which is the firmware's and is
/// checked against its own length.
fn smmuv3_base(table: &[u8]) -> Result<Option<u64>, &'static str> {
    let nodes = u32::from_le_bytes(bytes(table, IORT_NODE_COUNT)?);
    let mut at = u32::from_le_bytes(bytes(table, IORT_NODE_OFFSET)?) as usize;
    for _ in 0..nodes {
        let [kind] = bytes(table, at)?;
        let length = u16::from_le_bytes(bytes(table, at + NODE_LENGTH)?) as usize;
        if length < NODE_HEADER_BYTES || table.len() < at + length {
            return Err("IORT node outside its table or shorter than its header");
        }
        if kind == NODE_SMMUV3 {
            return Ok(Some(u64::from_le_bytes(bytes(&table[at..at + length], SMMUV3_BASE)?)));
        }
        at += length;
    }
    Ok(None)
}

/// The IOMMU's register base, from the DMAR table under the RSDP at `rsdp`, or from the IORT's
/// first SMMUv3.
pub fn probe_iommu(rsdp: u64) -> Option<u64> {
    let handler = NullAcpiHandler::new();
    let acpi = unsafe { AcpiTables::from_rsdp(handler, rsdp as usize).expect("failed to read the ACPI tables under the RSDP") };

    log::info!("ACPI: {:?}", acpi);

    let dmar = if let Ok(dmar) = acpi.find_table::<Dmar>() {
        dmar
    } else if let Ok(iort) = acpi.find_table::<Iort>() {
        let length = iort.header.length as usize;
        let table = unsafe { slice::from_raw_parts(iort.virtual_start().as_ptr() as *const u8, length) };
        return match smmuv3_base(table) {
            Ok(Some(base)) => {
                log::info!("IORT: SMMUv3 at {:#x}", base);
                Some(base)
            }
            Ok(None) => {
                log::warn!("IOMMU not available - No SMMUv3 in the IORT");
                None
            }
            Err(error) => {
                log::warn!("IOMMU not available - {}", error);
                None
            }
        };
    } else {
        log::warn!("IOMMU not available - No DMAR or IORT table");
        return None;
    };

    log::info!("DMAR: {:#?}", *dmar);

    let drhde = dmar.iter_remapping_structs().find_map(|header| {
        header.as_drhd()
    }).expect("failed to find DRHD entry");

    Some(drhde.register_base_address)
}

#[cfg(test)]
mod tests {
    use std::vec::Vec;

    use super::smmuv3_base;

    /// An IORT of `nodes`, each a type and its bytes after the type and the length, from byte 48.
    fn iort(nodes: &[(u8, Vec<u8>)]) -> Vec<u8> {
        let mut table = std::vec![0u8; 48];
        table[0..4].copy_from_slice(b"IORT");
        table[36..40].copy_from_slice(&(nodes.len() as u32).to_le_bytes());
        table[40..44].copy_from_slice(&48u32.to_le_bytes());
        for (kind, rest) in nodes {
            table.push(*kind);
            table.extend_from_slice(&(3 + rest.len() as u16).to_le_bytes());
            table.extend_from_slice(rest);
        }
        let length = table.len() as u32;
        table[4..8].copy_from_slice(&length.to_le_bytes());
        table
    }

    /// An SMMUv3 node's bytes after its type and length: revision 5, then the ID mapping fields,
    /// the base at byte 16, and the rest of IORT Table 13's 68 bytes.
    fn smmuv3(base: u64) -> Vec<u8> {
        let mut node = std::vec![0u8; 65];
        node[0] = 5;
        node[13..21].copy_from_slice(&base.to_le_bytes());
        node
    }

    /// An ITS group node's bytes after its type and length, with one ITS.
    fn its() -> Vec<u8> {
        let mut node = std::vec![0u8; 21];
        node[13] = 1;
        node
    }

    #[test]
    fn the_first_smmuv3_s_base_is_found_past_other_nodes() {
        let table = iort(&[(0, its()), (4, smmuv3(0x0905_0000)), (4, smmuv3(0x1000_0000))]);
        assert_eq!(smmuv3_base(&table), Ok(Some(0x0905_0000)));
    }

    #[test]
    fn an_iort_without_an_smmuv3_names_none() {
        assert_eq!(smmuv3_base(&iort(&[(0, its()), (2, std::vec![0u8; 33])])), Ok(None));
        assert_eq!(smmuv3_base(&iort(&[])), Ok(None));
    }

    #[test]
    fn a_node_count_past_the_nodes_is_refused() {
        let mut table = iort(&[(0, its())]);
        table[36] = 2;
        assert!(smmuv3_base(&table).is_err());
    }

    #[test]
    fn a_node_shorter_than_its_header_is_refused_and_ends_the_walk() {
        let mut table = iort(&[(0, its()), (4, smmuv3(0x0905_0000))]);
        table[49..51].copy_from_slice(&0u16.to_le_bytes());
        assert!(smmuv3_base(&table).is_err());
    }

    #[test]
    fn an_smmuv3_node_too_short_for_its_base_is_refused() {
        let table = iort(&[(4, std::vec![0u8; 17])]);
        assert!(smmuv3_base(&table).is_err());
    }

    #[test]
    fn a_table_shorter_than_its_header_is_refused() {
        assert!(smmuv3_base(&iort(&[])[..40]).is_err());
    }
}
