use cranelift_codegen::cursor::{Cursor, FuncCursor};
use cranelift_codegen::ir::Block;
use cranelift_codegen::{isa, settings, verify_function, Context};
use cranelift_native::builder_with_options;
use cranelift_reader::parse_functions;
use target_lexicon::triple;

fn main() {
    let code = "function u0:1(i64 vmctx, i64) fast {
    gv0 = vmctx
    gv1 = load.i64 notrap aligned readonly gv0+8
    gv2 = load.i64 notrap aligned gv1
    gv3 = vmctx
    gv4 = load.i64 notrap aligned readonly checked gv3+112
    sig0 = (i64 vmctx, i32 uext, i32 uext, i32 uext) -> i32 uext apple_aarch64
    sig1 = (i64 vmctx, i64, i32, i32, i32, i32) -> i32 fast
    sig2 = (i64 vmctx, i32 uext, i32 uext) -> i32 uext apple_aarch64
    sig3 = (i64 vmctx, i32 uext) -> i32 uext apple_aarch64
    fn0 = u0:0 sig1
    stack_limit = gv2

                                block0(v0: i64, v1: i64):
@005e                               v2 = iconst.i32 0xffff_fff0
@0060                               v3 = iconst.i32 9
@0062                               v4 = uextend.i64 v2  ; v2 = 0xffff_fff0
@0062                               v5 = global_value.i64 gv4
@0062                               v6 = iadd v5, v4
@0062                               store little heap v3, v6  ; v3 = 9
@0065                               v7 = iconst.i32 4
@0067                               v8 = iconst.i32 11
@0069                               v9 = uextend.i64 v7  ; v7 = 4
@0069                               v10 = global_value.i64 gv4
@0069                               v11 = iadd v10, v9
@0069                               store little heap v8, v11  ; v8 = 11
@006c                               v12 = iconst.i32 1
@006e                               v13 = iconst.i32 0
@0070                               v14 = iconst.i32 1
@0072                               v15 = iconst.i32 20
@0074                               v16 = global_value.i64 gv3
@0074                               v17 = load.i64 notrap aligned readonly v16+72
@0074                               v18 = load.i64 notrap aligned readonly v16+96
@0074                               v19 = call_indirect sig1, v17(v18, v0, v12, v13, v14, v15)  ; v12 = 1, v13 = 0, v14 = 1, v15 = 20
@0077                               jump block1

                                block1:
@0077                               return
}
";

    let mut functions = parse_functions(code).unwrap();
    let mut func = functions.pop().unwrap();
    let mut pos = FuncCursor::new(&mut func);
    while let Some(_block) = pos.next_block() {
        while let Some(inst) = pos.next_inst() {
            let opcode = pos.func.dfg.insts[inst].opcode();
            println!("{}", opcode)
        }
    }
    let flags = settings::Flags::new(settings::builder());

    let res = verify_function(&func, &flags);

    println!("{}", func.display());

    let signature = func.stencil.signature.clone();

    let isa = match isa::lookup(triple!("aarch64")) {
        Err(err) => panic!("Error looking up target: {}", err),
        Ok(isa_builder) => isa_builder.finish(flags).unwrap(),
    };

    let mut ctx = Context::for_function(func);
    let compiled_code = ctx.compile(&*isa, &mut Default::default()).unwrap();

    std::fs::write("dump.bin", compiled_code.code_buffer()).unwrap();

    println!("{}", ctx.func.display());

    if let Err(errors) = res {
        panic!("{}", errors);
    }
}
