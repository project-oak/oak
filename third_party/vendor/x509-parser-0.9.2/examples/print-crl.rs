use der_parser::oid::Oid;
use nom::HexDisplay;
use std::cmp::min;
use std::env;
use std::io;
use x509_parser::prelude::*;

fn print_hex_dump(bytes: &[u8], max_len: usize) {
    let m = min(bytes.len(), max_len);
    print!("{}", &bytes[..m].to_hex(16));
    if bytes.len() > max_len {
        println!("... <continued>");
    }
}

fn format_oid(oid: &Oid) -> String {
    match oid2sn(oid) {
        Ok(s) => s.to_owned(),
        _ => format!("{}", oid),
    }
}

fn print_authority_key_identifier(aki: &AuthorityKeyIdentifier, level: usize) {
    if let Some(id) = &aki.key_identifier {
        let mut s =
            id.0.iter()
                .fold(String::with_capacity(3 * id.0.len()), |a, b| {
                    a + &format!("{:02x}:", b)
                });
        s.pop();
        println!("{:indent$}keyid: {}", "", &s, indent = level);
    }
    if aki.authority_cert_issuer.is_some() {
        unimplemented!();
    }
    if let Some(serial) = aki.authority_cert_serial {
        let mut s = serial
            .iter()
            .fold(String::with_capacity(3 * serial.len()), |a, b| {
                a + &format!("{:02x}:", b)
            });
        s.pop();
        println!("{:indent$}serial: {}", "", &s, indent = level);
    }
}

fn print_x509_extension(oid: &Oid, ext: &X509Extension, level: usize) {
    match ext.parsed_extension() {
        ParsedExtension::CRLNumber(num) => {
            println!("{:indent$}X509v3 CRL Number: {}", "", num, indent = level);
        }
        ParsedExtension::ReasonCode(code) => {
            println!(
                "{:indent$}X509v3 CRL Reason Code: {}",
                "",
                code,
                indent = level
            );
        }
        ParsedExtension::InvalidityDate(date) => {
            println!(
                "{:indent$}Invalidity Date: {}",
                "",
                date.to_rfc2822(),
                indent = level
            );
        }
        ParsedExtension::AuthorityKeyIdentifier(aki) => {
            println!(
                "{:indent$}X509v3 Authority Key Identifier:",
                "",
                indent = level
            );
            print_authority_key_identifier(aki, level + 2);
        }
        x => {
            print!("{:indent$}{}:", "", format_oid(oid), indent = level);
            print!(" Critical={}", ext.critical);
            print!(" len={}", ext.value.len());
            println!();
            println!(" {:indent$}{:?}", "", x, indent = level);
        }
    }
}

fn print_x509_digest_algorithm(alg: &AlgorithmIdentifier, level: usize) {
    println!(
        "{:indent$}Oid: {}",
        "",
        format_oid(&alg.algorithm),
        indent = level
    );
    if let Some(parameter) = &alg.parameters {
        println!(
            "{:indent$}Parameter: <PRESENT> {:?}",
            "",
            parameter.header.tag,
            indent = level
        );
        if let Ok(bytes) = parameter.as_slice() {
            print_hex_dump(bytes, 32);
        }
    } else {
        println!("{:indent$}Parameter: <ABSENT>", "", indent = level);
    }
}

fn print_revoked_certificate(revoked: &RevokedCertificate, level: usize) {
    println!(
        "{:indent$}Serial number: {}",
        "",
        revoked.raw_serial_as_string(),
        indent = level
    );
    println!(
        "{:indent$}Revocation Date: {}",
        "",
        revoked.revocation_date.to_rfc2822(),
        indent = level + 2
    );
    println!("{:indent$}CRL Extensions:", "", indent = level + 2);
    for (oid, ext) in revoked.extensions() {
        print_x509_extension(oid, ext, level + 4);
    }
}

fn print_crl_info(crl: &CertificateRevocationList) {
    println!("  Version: {}", crl.version().unwrap_or(X509Version(0)));
    // println!("  Subject: {}", crl.subject());
    println!("  Signature Algorithm:");
    print_x509_digest_algorithm(&crl.signature_algorithm, 4);
    println!("  Issuer: {}", crl.issuer());
    // println!("  Serial: {}", crl.tbs_certificate.raw_serial_as_string());
    println!("  Last Update: {}", crl.last_update().to_rfc2822());
    println!(
        "  Next Update: {}",
        crl.next_update()
            .map_or("NONE".to_owned(), |d| d.to_rfc2822())
    );
    println!("{:indent$}CRL Extensions:", "", indent = 2);
    for (oid, ext) in crl.extensions() {
        print_x509_extension(oid, ext, 4);
    }
    println!("  Revoked certificates:");
    for revoked in crl.iter_revoked_certificates() {
        print_revoked_certificate(revoked, 4);
    }
    println!();
}

pub fn main() -> io::Result<()> {
    for file_name in env::args().skip(1) {
        // placeholder to store decoded PEM data, if needed
        let tmpdata;

        println!("File: {}", file_name);
        let data = std::fs::read(file_name.clone()).expect("Unable to read file");
        let der_data: &[u8] = if (data[0], data[1]) == (0x30, 0x82) {
            // probably DER
            &data
        } else {
            // try as PEM
            let (_, data) = parse_x509_pem(&data).expect("Could not decode the PEM file");
            tmpdata = data;
            &tmpdata.contents
        };
        let (_, crl) = parse_x509_crl(&der_data).expect("Could not decode DER data");
        print_crl_info(&crl);
    }
    Ok(())
}
