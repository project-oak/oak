# port_check
A simple rust library to get a free local port or to check if a port somewhere is reachable

Example:
```rust

// get a free local port
let free_port = port_check::free_local_port();

// get a free local port between 10000 and 15000
let free_port_in_range = port_check::free_local_port_in_range(10000, 15000);

// check whether a remote port is reachable
let is_reachable = port_check::is_port_reachable("192.0.2.0:8080");
// or
let is_reachable = is_port_reachable_with_timeout("192.0.2.0:8080", Duration::from_millis(10_000));


```