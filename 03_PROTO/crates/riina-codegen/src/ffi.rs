// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! FFI Marshaling Module
//!
//! Handles translation between RIINA types and C types at the FFI boundary.
//! Used by the C emitter to generate correct extern declarations and
//! marshaling code for `luaran "C"` blocks.

use riina_types::Ty;

/// Map a RIINA type to its C representation string.
pub fn ty_to_c(ty: &Ty) -> &'static str {
    match ty {
        Ty::CInt => "int",
        Ty::CChar => "char",
        Ty::CVoid => "void",
        Ty::Int => "int64_t",
        Ty::Bool => "int",
        Ty::String => "const char*",
        Ty::Unit => "void",
        Ty::RawPtr(inner) => match inner.as_ref() {
            Ty::CVoid => "void*",
            Ty::CChar => "char*",
            Ty::String => "const char*",
            _ => "void*",
        },
        _ => "riina_value_t*",
    }
}

/// Generate a C extern declaration for an FFI function.
pub fn emit_extern_decl(name: &str, params: &[(String, Ty)], ret_ty: &Ty) -> String {
    let ret = ty_to_c(ret_ty);
    let param_strs: Vec<String> = params
        .iter()
        .map(|(pname, pty)| format!("{} {}", ty_to_c(pty), pname))
        .collect();
    let params_str = if param_strs.is_empty() {
        "void".to_string()
    } else {
        param_strs.join(", ")
    };
    format!("extern {ret} {name}({params_str});")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ty_to_c_primitives() {
        assert_eq!(ty_to_c(&Ty::CInt), "int");
        assert_eq!(ty_to_c(&Ty::CChar), "char");
        assert_eq!(ty_to_c(&Ty::CVoid), "void");
        assert_eq!(ty_to_c(&Ty::Int), "int64_t");
        assert_eq!(ty_to_c(&Ty::String), "const char*");
        assert_eq!(ty_to_c(&Ty::Unit), "void");
    }

    #[test]
    fn test_ty_to_c_raw_ptr() {
        assert_eq!(ty_to_c(&Ty::RawPtr(Box::new(Ty::CVoid))), "void*");
        assert_eq!(ty_to_c(&Ty::RawPtr(Box::new(Ty::CChar))), "char*");
    }

    #[test]
    fn test_emit_extern_decl_printf() {
        let decl = emit_extern_decl(
            "printf",
            &[("fmt".to_string(), Ty::RawPtr(Box::new(Ty::CChar)))],
            &Ty::CInt,
        );
        assert_eq!(decl, "extern int printf(char* fmt);");
    }

    #[test]
    fn test_emit_extern_decl_no_params() {
        let decl = emit_extern_decl("getpid", &[], &Ty::CInt);
        assert_eq!(decl, "extern int getpid(void);");
    }

    #[test]
    fn test_emit_extern_decl_multiple_params() {
        let decl = emit_extern_decl(
            "memcpy",
            &[
                ("dest".to_string(), Ty::RawPtr(Box::new(Ty::CVoid))),
                ("src".to_string(), Ty::RawPtr(Box::new(Ty::CVoid))),
                ("n".to_string(), Ty::CInt),
            ],
            &Ty::RawPtr(Box::new(Ty::CVoid)),
        );
        assert_eq!(decl, "extern void* memcpy(void* dest, void* src, int n);");
    }
}
