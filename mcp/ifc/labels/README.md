# IFC Labels

Information Flow Control (IFC) labels for AI agent frameworks.

IFC tracks how data flows through a system using security labels. Each piece of
data carries:

- **Secrecy labels**: Who can read it (e.g., `pii`, `confidential`)
- **Integrity labels**: How trusted it is (e.g., `user-verified`, `external`)

This library provides primitives to check whether data can safely flow between
components, preventing leaks (secret data to public channels) and taint
(untrusted data to trusted sinks). Trusted actors can use _privileges_ to
declassify (reduce secrecy) or endorse (increase integrity) data when
appropriate.

## Requirements

- Python 3.10+
- No runtime dependencies (uses only standard library)
- For tests: `pip install pytest`

## Usage

```python
from labels import Label, SecrecyLabel, IntegrityLabel
from labels import Privilege, Declassification, Endorsement

# Create labels
secret = Label(secrecy=SecrecyLabel(frozenset({"pii"})))
public = Label()

# Check flow
secret.can_flow_to(public)  # False - would leak pii

# Declassify with privilege
priv = Privilege(declassification=Declassification(frozenset({"pii"})))
declassified = priv.declassify(secret, frozenset({"pii"}))
declassified.can_flow_to(public)  # True
```

## API

- `SecrecyLabel` / `IntegrityLabel` - individual label types with `can_flow_to`,
  `join`, `meet`
- `Label` - combined secrecy + integrity
- `Declassification` / `Endorsement` - privilege to modify labels
- `Privilege` - combined privileges with convenience methods
