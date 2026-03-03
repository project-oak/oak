# Falsify

A framework for writing falsification tests as binaries.

## Overview

A falsification test expresses a **claim** about a system -- a property that
should hold for all possible inputs. The framework then evaluates the claim
against a specific input provided via a file, and reports whether the claim was
**intact**, **falsified**, or whether the evaluation was **inconclusive** due to
an error.

## Usage

Define a struct implementing the `Claim` trait:

```rust
struct MyClaim;

impl falsify::Claim for MyClaim {
    fn evaluate(&self, input: &[u8]) -> Result<falsify::Evaluation, Box<dyn core::error::Error>> {
        // Parse input, evaluate the claim.
        // Return Evaluation::Intact if the claim holds.
        // Return Evaluation::Falsified if a counterexample is found.
        // Return Err(..) if the input is invalid (inconclusive) or other unforeseen error occurs.
    }
}

fn main() {
    falsify::falsify(falsify::FalsifyArgs::parse(), &MyClaim);
}
```

The binary reads `--input-file` and writes the result to `--output-file-toml`.

## Evaluation Semantics

| Return value                | Meaning                       |
| --------------------------- | ----------------------------- |
| `Ok(Evaluation::Intact)`    | Claim holds for this input    |
| `Ok(Evaluation::Falsified)` | Counterexample found          |
| `Err(..)`                   | Inconclusive (e.g. bad input) |
