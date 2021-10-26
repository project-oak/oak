# Oak Functions `lookup_benchmark` example

This example does the same as the `key_value_lookup` example, except that it
repeats the lookup 101 times. By comparing the elapsed time when doing 101
lookups to doing a single lookup we can get a more accurate estimate of the
performance of key-value lookups under different conditions.

See /oak_functions/loader/benches/loookup.rs for usage.
