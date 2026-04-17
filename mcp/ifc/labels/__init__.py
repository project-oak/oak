"""IFC Labels Library.

Information Flow Control primitives for AI agent frameworks.
"""

from .error import (
    DeclassificationError,
    EndorsementError,
    IntegrityFlowError,
    SecrecyFlowError,
)
from .label import IntegrityLabel, Label, SecrecyLabel, Tag
from .privilege import Declassification, Endorsement, Privilege

__all__ = [
    # Types
    "Tag",
    "SecrecyLabel",
    "IntegrityLabel",
    "Label",
    # Privilege
    "Declassification",
    "Endorsement",
    "Privilege",
    # Errors
    "SecrecyFlowError",
    "IntegrityFlowError",
    "DeclassificationError",
    "EndorsementError",
]
