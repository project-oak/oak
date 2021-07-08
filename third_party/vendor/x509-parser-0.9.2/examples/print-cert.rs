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

fn print_x509_extension(oid: &Oid, ext: &X509Extension) {
    print!("    {}: ", format_oid(oid));
    print!(" Critical={}", ext.critical);
    print!(" len={}", ext.value.len());
    println!();
    match ext.parsed_extension() {
        ParsedExtension::BasicConstraints(bc) => {
            println!("      X509v3 CA: {}", bc.ca);
        }
        ParsedExtension::KeyUsage(ku) => {
            println!("      X509v3 Key Usage: {}", ku);
        }
        ParsedExtension::NSCertType(ty) => {
            println!("      Netscape Cert Type: {}", ty);
        }
        ParsedExtension::SubjectAlternativeName(san) => {
            for name in &san.general_names {
                println!("      X509v3 SAN: {:?}", name);
            }
        }
        ParsedExtension::SubjectKeyIdentifier(id) => {
            let mut s =
                id.0.iter()
                    .fold(String::with_capacity(3 * id.0.len()), |a, b| {
                        a + &format!("{:02x}:", b)
                    });
            s.pop();
            println!("      X509v3 Subject Key Identifier: {}", &s);
        }
        x => println!("      {:?}", x),
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

fn print_x509_info(x509: &X509Certificate) {
    println!("  Subject: {}", x509.subject());
    println!("  Signature Algorithm:");
    print_x509_digest_algorithm(&x509.signature_algorithm, 4);
    println!("  Issuer: {}", x509.issuer());
    println!("  Serial: {}", x509.tbs_certificate.raw_serial_as_string());
    println!("  Validity:");
    println!("    NotBefore: {}", x509.validity().not_before.to_rfc2822());
    println!("    NotAfter:  {}", x509.validity().not_after.to_rfc2822());
    println!("    is_valid:  {}", x509.validity().is_valid());
    println!("  Extensions:");
    for (oid, ext) in x509.extensions() {
        print_x509_extension(oid, ext);
    }
    println!();
}

pub fn main() -> io::Result<()> {
    for file_name in env::args().skip(1) {
        println!("File: {}", file_name);
        let data = std::fs::read(file_name.clone()).expect("Unable to read file");
        if (data[0], data[1]) == (0x30, 0x82) {
            // probably DER
            let (_, x509) = parse_x509_certificate(&data).expect("Could not decode DER data");
            print_x509_info(&x509);
        } else {
            // try as PEM
            for (n, pem) in Pem::iter_from_buffer(&data).enumerate() {
                let pem = pem.expect("Could not decode the PEM file");
                let data = &pem.contents;
                let (_, x509) = parse_x509_certificate(&data).expect("Could not decode DER data");
                println!("Certificate [{}]", n);
                print_x509_info(&x509);
            }
        }
    }
    Ok(())
}
