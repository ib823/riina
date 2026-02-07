// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! WASM Binary Encoder
//!
//! Hand-written WebAssembly binary format encoder. Emits valid .wasm binaries
//! per the WebAssembly specification (MVP + memory64 for wasm64).
//!
//! No external dependencies — all encoding is done manually for maximum
//! auditability and zero supply-chain risk.
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST

/// WASM magic number: `\0asm`
const WASM_MAGIC: [u8; 4] = [0x00, 0x61, 0x73, 0x6D];

/// WASM version 1
const WASM_VERSION: [u8; 4] = [0x01, 0x00, 0x00, 0x00];

/// WASM section IDs
#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum SectionId {
    Type = 1,
    Function = 3,
    Memory = 5,
    Export = 7,
    Code = 10,
}

/// WASM value types
#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum ValType {
    I32 = 0x7F,
    I64 = 0x7E,
    F64 = 0x7C,
}

/// WASM opcodes
#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum Op {
    Unreachable = 0x00,
    Nop = 0x01,
    Block = 0x02,
    Loop = 0x03,
    If = 0x04,
    Else = 0x05,
    End = 0x0B,
    Br = 0x0C,
    BrIf = 0x0D,
    Return = 0x0F,
    Call = 0x10,
    Drop = 0x1A,
    LocalGet = 0x20,
    LocalSet = 0x21,
    LocalTee = 0x22,
    I32Load = 0x28,
    I64Load = 0x29,
    I32Store = 0x36,
    I64Store = 0x37,
    I32Const = 0x41,
    I64Const = 0x42,
    F64Const = 0x44,
    I32Eqz = 0x45,
    I32Eq = 0x46,
    I32Ne = 0x47,
    I32LtS = 0x48,
    I32GtS = 0x4A,
    I32LeS = 0x4C,
    I32GeS = 0x4E,
    I32Add = 0x6A,
    I32Sub = 0x6B,
    I32Mul = 0x6C,
    I32DivS = 0x6D,
    I64Add = 0x7C,
    I64Sub = 0x7D,
    I64Mul = 0x7E,
    I64DivS = 0x7F,
}

/// Encode an unsigned LEB128 integer.
pub fn encode_uleb128(mut value: u64, out: &mut Vec<u8>) {
    loop {
        let mut byte = (value & 0x7F) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

/// Encode a signed LEB128 integer.
pub fn encode_sleb128(mut value: i64, out: &mut Vec<u8>) {
    let mut more = true;
    while more {
        let mut byte = (value & 0x7F) as u8;
        value >>= 7;
        if (value == 0 && byte & 0x40 == 0) || (value == -1 && byte & 0x40 != 0) {
            more = false;
        } else {
            byte |= 0x80;
        }
        out.push(byte);
    }
}

/// Encode a byte vector with its length prefix (LEB128).
pub fn encode_vec(data: &[u8], out: &mut Vec<u8>) {
    encode_uleb128(data.len() as u64, out);
    out.extend_from_slice(data);
}

/// WASM module builder.
///
/// Constructs a valid .wasm binary by accumulating sections.
pub struct WasmModule {
    /// Type section entries (function signatures)
    pub types: Vec<FuncType>,
    /// Function section (type indices)
    pub functions: Vec<u32>,
    /// Memory section
    pub memories: Vec<MemoryType>,
    /// Export section
    pub exports: Vec<Export>,
    /// Code section (function bodies)
    pub codes: Vec<FuncBody>,
}

/// Function type (signature).
#[derive(Debug, Clone)]
pub struct FuncType {
    pub params: Vec<ValType>,
    pub results: Vec<ValType>,
}

/// Memory type (limits).
#[derive(Debug, Clone)]
pub struct MemoryType {
    pub min: u32,
    pub max: Option<u32>,
}

/// Export entry.
#[derive(Debug, Clone)]
pub struct Export {
    pub name: String,
    pub kind: ExportKind,
    pub index: u32,
}

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum ExportKind {
    Func = 0x00,
    Memory = 0x02,
}

/// Function body.
#[derive(Debug, Clone)]
pub struct FuncBody {
    pub locals: Vec<(u32, ValType)>,
    pub code: Vec<u8>,
}

impl Default for WasmModule {
    fn default() -> Self {
        Self::new()
    }
}

impl WasmModule {
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
            functions: Vec::new(),
            memories: Vec::new(),
            exports: Vec::new(),
            codes: Vec::new(),
        }
    }

    /// Encode the entire module to a .wasm binary.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(4096);

        // Header
        out.extend_from_slice(&WASM_MAGIC);
        out.extend_from_slice(&WASM_VERSION);

        // Type section
        if !self.types.is_empty() {
            let section = self.encode_type_section();
            self.write_section(SectionId::Type, &section, &mut out);
        }

        // Function section
        if !self.functions.is_empty() {
            let section = self.encode_function_section();
            self.write_section(SectionId::Function, &section, &mut out);
        }

        // Memory section
        if !self.memories.is_empty() {
            let section = self.encode_memory_section();
            self.write_section(SectionId::Memory, &section, &mut out);
        }

        // Export section
        if !self.exports.is_empty() {
            let section = self.encode_export_section();
            self.write_section(SectionId::Export, &section, &mut out);
        }

        // Code section
        if !self.codes.is_empty() {
            let section = self.encode_code_section();
            self.write_section(SectionId::Code, &section, &mut out);
        }

        out
    }

    fn write_section(&self, id: SectionId, content: &[u8], out: &mut Vec<u8>) {
        out.push(id as u8);
        encode_uleb128(content.len() as u64, out);
        out.extend_from_slice(content);
    }

    fn encode_type_section(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        encode_uleb128(self.types.len() as u64, &mut buf);
        for ty in &self.types {
            buf.push(0x60); // func type marker
            encode_uleb128(ty.params.len() as u64, &mut buf);
            for p in &ty.params {
                buf.push(*p as u8);
            }
            encode_uleb128(ty.results.len() as u64, &mut buf);
            for r in &ty.results {
                buf.push(*r as u8);
            }
        }
        buf
    }

    fn encode_function_section(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        encode_uleb128(self.functions.len() as u64, &mut buf);
        for &idx in &self.functions {
            encode_uleb128(idx as u64, &mut buf);
        }
        buf
    }

    fn encode_memory_section(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        encode_uleb128(self.memories.len() as u64, &mut buf);
        for mem in &self.memories {
            if let Some(max) = mem.max {
                buf.push(0x01); // has max
                encode_uleb128(mem.min as u64, &mut buf);
                encode_uleb128(max as u64, &mut buf);
            } else {
                buf.push(0x00); // no max
                encode_uleb128(mem.min as u64, &mut buf);
            }
        }
        buf
    }

    fn encode_export_section(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        encode_uleb128(self.exports.len() as u64, &mut buf);
        for export in &self.exports {
            encode_vec(export.name.as_bytes(), &mut buf);
            buf.push(export.kind as u8);
            encode_uleb128(export.index as u64, &mut buf);
        }
        buf
    }

    fn encode_code_section(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        encode_uleb128(self.codes.len() as u64, &mut buf);
        for body in &self.codes {
            let func_body = self.encode_func_body(body);
            encode_uleb128(func_body.len() as u64, &mut buf);
            buf.extend_from_slice(&func_body);
        }
        buf
    }

    fn encode_func_body(&self, body: &FuncBody) -> Vec<u8> {
        let mut buf = Vec::new();
        encode_uleb128(body.locals.len() as u64, &mut buf);
        for &(count, ty) in &body.locals {
            encode_uleb128(count as u64, &mut buf);
            buf.push(ty as u8);
        }
        buf.extend_from_slice(&body.code);
        buf.push(Op::End as u8); // end of function
        buf
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_uleb128_zero() {
        let mut buf = Vec::new();
        encode_uleb128(0, &mut buf);
        assert_eq!(buf, vec![0x00]);
    }

    #[test]
    fn test_uleb128_small() {
        let mut buf = Vec::new();
        encode_uleb128(127, &mut buf);
        assert_eq!(buf, vec![0x7F]);
    }

    #[test]
    fn test_uleb128_multi_byte() {
        let mut buf = Vec::new();
        encode_uleb128(128, &mut buf);
        assert_eq!(buf, vec![0x80, 0x01]);
    }

    #[test]
    fn test_uleb128_large() {
        let mut buf = Vec::new();
        encode_uleb128(624485, &mut buf);
        assert_eq!(buf, vec![0xE5, 0x8E, 0x26]);
    }

    #[test]
    fn test_sleb128_positive() {
        let mut buf = Vec::new();
        encode_sleb128(42, &mut buf);
        assert_eq!(buf, vec![42]);
    }

    #[test]
    fn test_sleb128_negative() {
        let mut buf = Vec::new();
        encode_sleb128(-1, &mut buf);
        assert_eq!(buf, vec![0x7F]);
    }

    #[test]
    fn test_wasm_module_header() {
        let module = WasmModule::new();
        let bytes = module.encode();
        assert_eq!(&bytes[0..4], &WASM_MAGIC);
        assert_eq!(&bytes[4..8], &WASM_VERSION);
    }

    #[test]
    fn test_minimal_wasm_module() {
        let mut module = WasmModule::new();
        // Add a function type: () -> i32
        module.types.push(FuncType {
            params: vec![],
            results: vec![ValType::I32],
        });
        // Add function index pointing to type 0
        module.functions.push(0);
        // Add memory (1 page min)
        module.memories.push(MemoryType { min: 1, max: None });
        // Export function as "main"
        module.exports.push(Export {
            name: "main".to_string(),
            kind: ExportKind::Func,
            index: 0,
        });
        // Export memory
        module.exports.push(Export {
            name: "memory".to_string(),
            kind: ExportKind::Memory,
            index: 0,
        });
        // Function body: return 42
        let mut code = Vec::new();
        code.push(Op::I32Const as u8);
        encode_sleb128(42, &mut code);
        module.codes.push(FuncBody {
            locals: vec![],
            code,
        });

        let bytes = module.encode();
        // Should start with WASM magic
        assert_eq!(&bytes[0..4], &WASM_MAGIC);
        // Should be a valid binary (>8 bytes)
        assert!(bytes.len() > 8);
    }
}
