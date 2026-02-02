"""IFC Labels Library - Exceptions.

Informative exceptions for security policy violations.
"""

from dataclasses import dataclass
from typing import FrozenSet

Tag = str


@dataclass
class SecrecyFlowError(Exception):
    """Data would leak to a context with lower secrecy."""

    leaking_tags: FrozenSet[Tag]

    def __str__(self) -> str:
        return f"Secrecy flow denied: tags {self.leaking_tags} would leak"


@dataclass
class IntegrityFlowError(Exception):
    """Data from untrusted source would taint a trusted target."""

    missing_trust: FrozenSet[Tag]

    def __str__(self) -> str:
        return f"Integrity flow denied: target requires trust tags {self.missing_trust}"


@dataclass
class DeclassificationError(Exception):
    """Declassification not permitted for requested tags."""

    requested: FrozenSet[Tag]
    permitted: FrozenSet[Tag]

    def __str__(self) -> str:
        denied = self.requested - self.permitted
        return f"Cannot declassify tags {denied}: not in privilege"


@dataclass
class EndorsementError(Exception):
    """Endorsement not permitted for requested tags."""

    requested: FrozenSet[Tag]
    permitted: FrozenSet[Tag]

    def __str__(self) -> str:
        denied = self.requested - self.permitted
        return f"Cannot endorse with tags {denied}: not in privilege"
