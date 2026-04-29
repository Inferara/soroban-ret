/// Data section extractor.
///
/// Extracts constant strings, KEYS/CASES arrays from WASM data segments.

#[derive(Debug, Clone)]
pub struct DataSegment {
    pub offset: u32,
    pub data: Vec<u8>,
}

#[derive(Debug, Default)]
pub struct DataSection {
    pub segments: Vec<DataSegment>,
}

impl DataSection {
    pub fn new() -> Self {
        Self {
            segments: Vec::new(),
        }
    }

    pub fn add(&mut self, offset: u32, data: Vec<u8>) {
        self.segments.push(DataSegment { offset, data });
    }

    /// Read raw bytes at a memory offset.
    ///
    /// Bounds arithmetic is done in `u64` so a data segment that ends right at
    /// (or near) `u32::MAX` cannot wrap u32 and trigger out-of-bounds slice
    /// indexing on adversarial input.
    pub fn read_bytes(&self, offset: u32, len: u32) -> Option<&[u8]> {
        let req_start = offset as u64;
        let req_end = req_start.checked_add(len as u64)?;
        for seg in &self.segments {
            let seg_start = seg.offset as u64;
            let seg_end = seg_start.checked_add(seg.data.len() as u64)?;
            if req_start >= seg_start && req_end <= seg_end {
                let start = (req_start - seg_start) as usize;
                let end = start.checked_add(len as usize)?;
                return seg.data.get(start..end);
            }
        }
        None
    }

    /// Read a UTF-8 string at a memory offset.
    pub fn read_string(&self, offset: u32, len: u32) -> Option<String> {
        let bytes = self.read_bytes(offset, len)?;
        std::str::from_utf8(bytes).ok().map(|s| s.to_string())
    }

    /// Read an array of 64-bit values at an offset (for KEYS/CASES Val arrays).
    pub fn read_val_array(&self, offset: u32, count: u32) -> Vec<u64> {
        let mut values = Vec::new();
        for i in 0..count {
            let Some(byte_offset) = i.checked_mul(8).and_then(|d| offset.checked_add(d)) else {
                break;
            };
            if let Some(bytes) = self.read_bytes(byte_offset, 8) {
                let val = u64::from_le_bytes(bytes.try_into().unwrap_or([0; 8]));
                values.push(val);
            }
        }
        values
    }

    /// Read an array of string slice descriptors at an offset.
    ///
    /// The Soroban SDK stores KEYS arrays for `map_new_from_linear_memory` as
    /// `(u32 ptr, u32 len)` pairs packed into 8 bytes each. Each pair points to
    /// a UTF-8 string elsewhere in the data section.
    pub fn read_string_slice_array(&self, offset: u32, count: u32) -> Option<Vec<String>> {
        let mut strings = Vec::new();
        for i in 0..count {
            let byte_offset = i.checked_mul(8).and_then(|d| offset.checked_add(d))?;
            let bytes = self.read_bytes(byte_offset, 8)?;
            let ptr = u32::from_le_bytes(bytes[0..4].try_into().ok()?);
            let len = u32::from_le_bytes(bytes[4..8].try_into().ok()?);
            let s = self.read_string(ptr, len)?;
            strings.push(s);
        }
        Some(strings)
    }

    /// Find all potential string constants in data segments.
    /// Returns (offset, string) pairs for printable ASCII sequences.
    pub fn find_strings(&self) -> Vec<(u32, String)> {
        let mut results = Vec::new();
        for seg in &self.segments {
            let mut start = None;
            for (i, &byte) in seg.data.iter().enumerate() {
                if (0x20..0x7f).contains(&byte) {
                    if start.is_none() {
                        start = Some(i);
                    }
                } else {
                    if let Some(s) = start {
                        let len = i - s;
                        if len >= 2
                            && let Ok(text) = std::str::from_utf8(&seg.data[s..i])
                        {
                            results.push((seg.offset + s as u32, text.to_string()));
                        }
                    }
                    start = None;
                }
            }
            // Handle string at end of segment
            if let Some(s) = start {
                let len = seg.data.len() - s;
                if len >= 2
                    && let Ok(text) = std::str::from_utf8(&seg.data[s..])
                {
                    results.push((seg.offset + s as u32, text.to_string()));
                }
            }
        }
        results
    }

    /// Decode a Soroban Symbol from a 64-bit Val representation.
    /// Soroban small symbols encode up to 9 characters in a 64-bit value.
    ///
    /// Character codes (6 bits each):
    ///   1='_', 2-11='0'-'9', 12-37='A'-'Z', 38-63='a'-'z'
    ///
    /// Characters are packed MSB-first: first char in highest 6 bits of the body.
    pub fn decode_symbol_val(val: u64) -> Option<String> {
        // Soroban Val tag for small symbols: tag bits [0:7] = 0x0e (SymbolSmall)
        let tag = val & 0xff;
        if tag != 0x0e {
            return None;
        }

        let mut body = val >> 8;
        let mut chars = Vec::new();

        // Characters are packed MSB-first: extract from top 6 bits, shift left
        while body != 0 {
            let code = ((body >> (8 * 6)) & 0x3f) as u8; // top 6 bits of 54-bit field
            body <<= 6;
            body &= 0x003f_ffff_ffff_ffff; // mask to 54 bits
            if code == 0 {
                continue;
            }
            let ch = match code {
                1 => '_',
                n @ 2..=11 => (b'0' + n - 2) as char,
                n @ 12..=37 => (b'A' + n - 12) as char,
                n @ 38..=63 => (b'a' + n - 38) as char,
                _ => return None,
            };
            chars.push(ch);
        }
        if chars.is_empty() {
            None
        } else {
            Some(chars.into_iter().collect())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_bytes() {
        let mut ds = DataSection::new();
        ds.add(100, vec![1, 2, 3, 4, 5]);
        assert_eq!(ds.read_bytes(100, 3), Some(&[1u8, 2, 3][..]));
        assert_eq!(ds.read_bytes(102, 3), Some(&[3u8, 4, 5][..]));
        assert_eq!(ds.read_bytes(100, 6), None); // out of bounds
    }

    #[test]
    fn test_read_bytes_does_not_overflow() {
        // Adversarial: data segment near end of u32 address space.
        let mut ds = DataSection::new();
        ds.add(0xFFFF_FFF0, vec![0u8; 16]);
        // offset+len wraps u32 — must return None instead of panicking.
        assert_eq!(ds.read_bytes(0xFFFF_FFFE, 8), None);
        // legitimate read inside the segment still works.
        assert_eq!(ds.read_bytes(0xFFFF_FFF0, 4), Some(&[0u8, 0, 0, 0][..]));
    }

    #[test]
    fn test_read_val_array_does_not_overflow() {
        let mut ds = DataSection::new();
        ds.add(0xFFFF_FFF0, vec![0u8; 16]);
        // Huge count near u32::MAX cannot wrap and panic.
        let _ = ds.read_val_array(0xFFFF_FFF0, u32::MAX);
    }

    #[test]
    fn test_read_string() {
        let mut ds = DataSection::new();
        ds.add(0, b"hello world".to_vec());
        assert_eq!(ds.read_string(0, 5), Some("hello".to_string()));
    }

    #[test]
    fn test_decode_symbol_val() {
        // Test known symbol encodings from the soroban-env test vectors
        // "a" => body = 0b100_110 = 38
        let a_body: u64 = 38;
        let a_val = (a_body << 8) | 0x0E;
        assert_eq!(DataSection::decode_symbol_val(a_val), Some("a".to_string()));

        // Test that non-symbol tags return None
        assert_eq!(DataSection::decode_symbol_val(0x01), None); // True tag

        // Test round-trip: encode "persisted" using the known algorithm, then decode
        fn encode_symbol(s: &str) -> u64 {
            let mut accum: u64 = 0;
            for b in s.bytes() {
                let v = match b {
                    b'_' => 1,
                    b'0'..=b'9' => 2 + (b - b'0'),
                    b'A'..=b'Z' => 12 + (b - b'A'),
                    b'a'..=b'z' => 38 + (b - b'a'),
                    _ => 0,
                };
                accum <<= 6;
                accum |= v as u64;
            }
            (accum << 8) | 0x0E
        }

        assert_eq!(
            DataSection::decode_symbol_val(encode_symbol("persisted")),
            Some("persisted".to_string())
        );
        assert_eq!(
            DataSection::decode_symbol_val(encode_symbol("fn1")),
            Some("fn1".to_string())
        );
        assert_eq!(
            DataSection::decode_symbol_val(encode_symbol("hello")),
            Some("hello".to_string())
        );
        assert_eq!(
            DataSection::decode_symbol_val(encode_symbol("_")),
            Some("_".to_string())
        );
        assert_eq!(
            DataSection::decode_symbol_val(encode_symbol("ABC123")),
            Some("ABC123".to_string())
        );
    }
}
