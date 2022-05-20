use rustc_data_structures::fx::{FxHashSet};

// A set of heap allocation calls.
//
// TODO: The currently list may be incomplete. A thorough study is needed.
lazy_static!{
    pub static ref HEAP_ALLOC: FxHashSet<String> = {
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
