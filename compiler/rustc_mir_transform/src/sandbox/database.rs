use rustc_data_structures::fx::{FxHashSet};

// The set of native libraries provided by Rust.
lazy_static!{
    pub static ref NATIVE_LIBS: FxHashSet<String> = {
        let libs = vec![
            "core",
            "std",
            "stdarch",
            "alloc",
            "test",
            "backtrace",
            "unwind",
            "panic_unwind",
            "panic_abort",
            "proc_macro",
            "rustc_std_workspace_alloc",
            "rustc_std_workspace_core",
            "rustc_std_workspace_std",
            "compiler_builtins",
            // Any others?
        ];

        libs.into_iter().map(|x| x.to_string()).collect()
    };
}

// A set of heap allocation calls.
//
// TODO: The currently list may be incomplete. A thorough study is needed.
lazy_static!{
    pub static ref HEAP_ALLOC: FxHashSet<String> = {
        // The name ignors the crate and module and struct and only keeps the
        // final method, e.g., "new" of "Box::<i32>::new". Perhaps when query
        // this set, we should check where a method is from; we would otherwise
        // run the risk of introducing false positives.
        let allocs = vec![
            "new",
            "new_in",
            "with_capacity",
            "with_capacity_in",
            // Box
            "new_uninit",
            "new_zeroed",
            "pin",  // Maybe we should check if it's really from Box::?
            "try_new",
            "try_new_unint",
            "try_new_zeroed",
            // Unsafe
            "from_raw_parts",
            "from_raw_parts_in",
            // Others
            // From something like vec![..]
            "exchange_malloc"
                          ];

        allocs.into_iter().map(|x| x.to_string()).collect()
    };
}
