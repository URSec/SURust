use rustc_middle::mir::*;
use rustc_data_structures::fx::{FxHashSet};

use super::unsafe_obj::{UnsafeAllocSite};

// This function whitelist is a helper for development only.
lazy_static!{
    pub static ref FN_TO_PROCESS: FxHashSet<String> = {
        let mut vec = Vec::new();
        vec.push("foo".to_string());
        vec.push("bar".to_string());
        vec.push("f0".to_string());
        vec.push("f1".to_string());

        // For exa (https://github.com/ogham/exa)
        vec.push("add_files_to_table".to_string());
        vec.push("translate_attribute_name".to_string());
        vec.push("listxattr_first".to_string());

        // For qdrant
        vec.push("vf_to_u8".to_string());
        vec.push("open_read".to_string());
        vec.push("open_write".to_string());
        vec.push("iter_points".to_string());

        vec.into_iter().collect()
    };
}


/// Print a Statement for debugging.
#[allow(dead_code)]
#[inline(always)]
crate fn print_stmt_assign(stmt: &Statement<'tcx>, rvalue: &Rvalue<'tcx>) {
    print!("[Assign]: {:?}; ", stmt);
    match rvalue {
        Rvalue::Use(operand) => {print_operand("Use", operand)},
        Rvalue::Repeat(operand, num) => {
            println!("Repeat {:?} {} times.", operand, num);
        },
        Rvalue::Ref(.., place) => {
            println!("Ref: {:?}", place);
        },
        Rvalue::ThreadLocalRef(def_id) => {
            println!("[ThreadLocalRef]: DefId = {:?}", def_id);
        },
        Rvalue::AddressOf(mutability, place) => {
            println!("[AddressOf]: {:?} {:?}", mutability, place);
        },
        Rvalue::Len(place) => {
            println!("[Len]: {:?}", place);
        },
        Rvalue::Cast(_cast_kind, operand, ty) => {
            println!("[Cast]: {:?} to Type {:?}", operand, ty);
        },
        Rvalue::BinaryOp(bin_op, box (op1, op2))
        | Rvalue::CheckedBinaryOp(bin_op, box (op1, op2)) => {
            println!("[BinaryOp]: {:?} on {:?} and {:?}", bin_op, op1, op2);
        },
        Rvalue::NullaryOp(null_op, ty) => {
            println!("[NullaryOp]: {:?}, {:?}", null_op, ty);
        },
        Rvalue::UnaryOp(un_op, operand) => {
            println!("[UnaryOp]: {:?} {:?}", un_op, operand);
        },
        Rvalue::Discriminant(place) => {
            println!("[Discriminant]: {:?}", place);
        },
        Rvalue::Aggregate(box kind, operands) => {
            println!("[Aggregate]: kind = {:?}, operands = {:?}", kind, operands);
        },
        Rvalue::ShallowInitBox(operand, ty) => {
            println!("[ShallowInitBox]: operand = {:?}, ty = {:?}", operand, ty);
        }
    }
}

#[allow(dead_code)]
#[inline(always)]
crate fn print_stmt(type_name: &str, stmt: &Statement<'_>) {
    println!("[{}]: {:?}", type_name, stmt);
}

#[allow(dead_code)]
#[inline(always)]
crate fn print_operand(type_name: &str, operand: &Operand<'tcx>) {
    println!("[{}]: {:?}", type_name, operand);
}

#[allow(dead_code)]
#[inline(always)]
crate fn print_terminator(type_name: &str, terminator: &Terminator<'_>) {
    println!("[{}]: {:?}", type_name, terminator.kind);
}


#[allow(dead_code)]
#[inline(always)]
crate fn print_local(type_name: &str, local: Local) {
    println!("{:?} is a {}", local, type_name);
}

/// Print all the unsafe allocation sites of a function.
#[allow(dead_code)]
#[inline(always)]
crate fn print_unsafe_alloc(results: &FxHashSet::<UnsafeAllocSite<'tcx>>) {
    println!("Unsafe allocation sites:");

    for site in results.iter() {
        match &site {
            UnsafeAllocSite::Alloc(alloc) => {
                print_terminator("Heap Alloc", alloc);
            },
            UnsafeAllocSite::Ret(ret) => {
                print_terminator("Fn Ret", ret);
            },
            UnsafeAllocSite::Arg(arg) => {
                println!("Argument: {:?}", arg);
            }
        }
    }

    println!("");
}
