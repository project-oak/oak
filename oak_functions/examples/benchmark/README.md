# Oak Functions `benchmark` example

The sole purpose of this example is for benchmarking the performance of ABI
calls. By comparing the elapsed time when doing multiple calls of the same type
(e.g. a lookup) to doing a single call we can get a more accurate estimate of
the performance characteristics under different conditions.

See `/oak_functions/loader/benches/loookup.rs` for example usage with key-value
lookups.
