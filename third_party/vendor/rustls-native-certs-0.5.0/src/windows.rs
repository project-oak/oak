use crate::RootStoreBuilder;
use schannel;
use std::io::{Error, ErrorKind};

static PKIX_SERVER_AUTH: &str = "1.3.6.1.5.5.7.3.1";

fn usable_for_rustls(uses: schannel::cert_context::ValidUses) -> bool {
    match uses {
        schannel::cert_context::ValidUses::All => true,
        schannel::cert_context::ValidUses::Oids(strs) => {
            strs.iter().any(|x| x == PKIX_SERVER_AUTH)
        }
    }
}

pub fn build_native_certs<B: RootStoreBuilder>(builder: &mut B) -> Result<(), Error> {
    let mut first_error = None;

    let current_user_store = schannel::cert_store::CertStore::open_current_user("ROOT")?;

    for cert in current_user_store.certs() {
        if !usable_for_rustls(cert.valid_uses().unwrap()) {
            continue;
        }

        match builder.load_der(cert.to_der().to_vec()) {
            Err(err) => {
                first_error = first_error
                    .or_else(|| Some(Error::new(ErrorKind::InvalidData, err)));
            }
            _ => {}
        };
    }

    if let Some(err) = first_error {
        Err(err)
    } else {
        Ok(())
    }
}
