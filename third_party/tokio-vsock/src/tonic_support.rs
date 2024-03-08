use tonic::transport::server::Connected;

use crate::{VsockAddr, VsockStream};

/// Connection info for a Vsock Stream.
///
/// See [`Connected`] for more details.
///
#[cfg_attr(docsrs, doc(cfg(feature = "tonic-conn")))]
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct VsockConnectInfo {
    peer_addr: Option<VsockAddr>,
}

#[cfg_attr(docsrs, doc(cfg(feature = "tonic-conn")))]
impl VsockConnectInfo {
    /// Return the remote address the IO resource is connected too.
    pub fn peer_addr(&self) -> Option<VsockAddr> {
        self.peer_addr
    }
}

/// Allow consumers of VsockStream to check that it is connected and valid before use.
///
#[cfg_attr(docsrs, doc(cfg(feature = "tonic-conn")))]
impl Connected for VsockStream {
    type ConnectInfo = VsockConnectInfo;

    fn connect_info(&self) -> Self::ConnectInfo {
        VsockConnectInfo {
            peer_addr: self.peer_addr().ok(),
        }
    }
}
