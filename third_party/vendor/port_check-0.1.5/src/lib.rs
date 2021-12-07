use std::net::{Ipv4Addr, SocketAddrV4, TcpListener, TcpStream, ToSocketAddrs};
use std::time::Duration;

/// Attempts a TCP connection to an address and returns whether it succeeded
pub fn is_port_reachable<A: ToSocketAddrs>(address: A) -> bool {
    TcpStream::connect(address).is_ok()
}

/// Attempts a TCP connection to an address and returns whether it succeeded
pub fn is_port_reachable_with_timeout<A: ToSocketAddrs>(address: A, timeout: Duration) -> bool {
    match address.to_socket_addrs() {
        Ok(addrs) => {
            for address in addrs {
                if TcpStream::connect_timeout(&address, timeout).is_ok() {
                    return true;
                }
            };
            false
        },
        Err(_err) => {
            false
        }
    }
}

/// Returns whether a port is available on the localhost
pub fn is_local_port_free(port: u16) -> bool {
    let ipv4 = SocketAddrV4::new(Ipv4Addr::LOCALHOST, port);
    TcpListener::bind(ipv4).is_ok()
}

/// Returns an available localhost port within the specified range.
///
/// 'min' and 'max' values are included in the range
///
pub fn free_local_port_in_range(min: u16, max: u16) -> Option<u16> {
    (min..max).find(|port| is_local_port_free(*port))
}

/// Returns an available localhost port
pub fn free_local_port() -> Option<u16> {
    let socket = SocketAddrV4::new(Ipv4Addr::LOCALHOST, 0);
    TcpListener::bind(socket)
        .and_then(|listener| listener.local_addr())
        .and_then(|addr| Ok(addr.port()))
        .ok()
}

#[cfg(test)]
mod tests {

    use super::*;
    use std::net::{Ipv4Addr, SocketAddrV4, TcpListener};
    use std::time::Instant;
    use std::{thread, time::Duration};

    #[test]
    fn should_return_an_unused_port() {
        let result = free_local_port();
        assert!(result.is_some());
        assert!(is_local_port_free(result.unwrap()));
    }

    #[test]
    fn should_return_an_unused_port_in_range() {
        let free_port = free_local_port().unwrap();
        let min = free_port - 100;
        let max = free_port;
        let port_found = free_local_port_in_range(min, max).unwrap();
        assert!(port_found >= min);
        assert!(port_found <= max);
    }

    #[test]
    fn a_free_port_should_not_be_reachable() {
        let available_port = free_local_port().unwrap();
        assert!(!is_port_reachable(&format!("127.0.0.1:{}", available_port)));
    }

    #[test]
    fn free_port_should_resolve_domain_name() {
        let available_port = free_local_port().unwrap();
        assert!(!is_port_reachable(&format!("localhost:{}", available_port)));
    }

    #[test]
    fn an_open_port_should_be_reachable() {
        let socket = SocketAddrV4::new(Ipv4Addr::LOCALHOST, 0);
        let listener = TcpListener::bind(socket).unwrap();
        let listener_port = listener.local_addr().unwrap().to_string();

        thread::spawn(move || loop {
            match listener.accept() {
                Ok(_) => {
                    println!("Connection received!");
                }
                Err(_) => {
                    println!("Error in received connection!");
                }
            }
        });

        let mut port_reachable = false;
        while !port_reachable {
            println!("Check for available connections on {}", &listener_port);
            port_reachable = is_port_reachable(&listener_port);
            thread::sleep(Duration::from_millis(10));
        }
        assert!(port_reachable)
    }

    #[test]
    fn is_port_reachable_should_respect_timeout() {
        let timeout = 100;
        let start = Instant::now();

        assert!(!is_port_reachable_with_timeout(
            "198.19.255.255:1",
            Duration::from_millis(timeout)
        ));

        let elapsed = (start.elapsed().subsec_nanos() / 1000000) as u64;
        println!("Millis elapsed {}", elapsed);
        assert!(elapsed >= timeout);
        assert!(elapsed < 2 * timeout);
    }

    #[test]
    fn free_port_with_timeout_should_resolve_domain_name() {
        let available_port = free_local_port().unwrap();
        assert!(!is_port_reachable_with_timeout(
            &format!("localhost:{}", available_port),
            Duration::from_millis(10)
        ));
    }

    #[test]
    fn an_open_port_should_be_reachable_with_timeout() {
        let socket = SocketAddrV4::new(Ipv4Addr::LOCALHOST, 0);
        let listener = TcpListener::bind(socket).unwrap();
        let listener_port = listener.local_addr().unwrap().to_string();

        thread::spawn(move || loop {
            match listener.accept() {
                Ok(_) => {
                    println!("Connection received!");
                }
                Err(_) => {
                    println!("Error in received connection!");
                }
            }
        });

        let mut port_reachable = false;
        while !port_reachable {
            println!("Check for available connections on {}", &listener_port);
            port_reachable = is_port_reachable_with_timeout(&listener_port, Duration::from_secs(1));
            thread::sleep(Duration::from_millis(10));
        }
        assert!(port_reachable)
    }
}
