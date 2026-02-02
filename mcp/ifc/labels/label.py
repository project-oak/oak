"""IFC Labels Library - Labels.

Provides SecrecyLabel, IntegrityLabel and combined Label with lattice operations.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import FrozenSet, TypeVar

Tag = str
T = TypeVar("T", bound="BaseLabel")


@dataclass(frozen=True)
class BaseLabel:
    """Base class for labels with lattice operations.

    Labels form a lattice under subset ordering:
    - Join (⊔) = union (least upper bound)
    - Meet (⊓) = intersection (greatest lower bound)
    """

    tags: FrozenSet[Tag] = frozenset()

    def join(self: T, other: T) -> T:
        """Least upper bound (union of tags)."""
        return type(self)(self.tags | other.tags)

    def meet(self: T, other: T) -> T:
        """Greatest lower bound (intersection of tags)."""
        return type(self)(self.tags & other.tags)


@dataclass(frozen=True)
class SecrecyLabel(BaseLabel):
    """Secrecy label - tracks who can read.

    Data with more tags is MORE restrictive (higher in lattice).
    Flow rule: source.tags ⊆ target.tags (no write down)
    """

    def can_flow_to(self, target: SecrecyLabel) -> bool:
        """Check if data can flow to target (source ⊆ target)."""
        return self.tags <= target.tags


@dataclass(frozen=True)
class IntegrityLabel(BaseLabel):
    """Integrity label - tracks trust/provenance.

    Data with more tags is LESS restrictive (lower in lattice).
    Flow rule: target.tags ⊆ source.tags (no read down)
    """

    def can_flow_to(self, target: IntegrityLabel) -> bool:
        """Check if data can flow to target (target ⊆ source)."""
        return target.tags <= self.tags


@dataclass(frozen=True)
class Label:
    """Combined secrecy + integrity label."""

    secrecy: SecrecyLabel = SecrecyLabel()
    integrity: IntegrityLabel = IntegrityLabel()

    def can_flow_to(self, target: Label) -> bool:
        """Check if data can flow to target."""
        return self.secrecy.can_flow_to(
            target.secrecy
        ) and self.integrity.can_flow_to(target.integrity)

    def join(self, other: Label) -> Label:
        """Least upper bound."""
        return Label(
            self.secrecy.join(other.secrecy), self.integrity.join(other.integrity)
        )

    def meet(self, other: Label) -> Label:
        """Greatest lower bound."""
        return Label(
            self.secrecy.meet(other.secrecy), self.integrity.meet(other.integrity)
        )
