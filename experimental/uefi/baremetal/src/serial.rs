use atomic_refcell::AtomicRefCell;
use uart_16550::SerialPort;

pub struct Serial {
    port: AtomicRefCell<SerialPort>,
}

impl Serial {
    pub fn new() -> Serial {
        let mut port = unsafe { SerialPort::new(0x2f8) };
        port.init();
        Serial {
            port: AtomicRefCell::new(port),
        }
    }
}

impl runtime::Channel for Serial {
    type Error = ();

    fn send(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        for byte in data {
            self.port.borrow_mut().send(*byte);
        }
        Ok(())
    }

    fn recv(&mut self, data: &mut [u8]) -> Result<(), Self::Error> {
        for i in 0..data.len() {
            data[i] = self.port.borrow_mut().receive();
        }
        Ok(())
    }
}
