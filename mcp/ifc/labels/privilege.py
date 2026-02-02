"""IFC Labels Library - Privileges.

Provides Declassification, Endorsement and combined Privilege for label transformations.
"""

from dataclasses import dataclass
from typing import FrozenSet

from .error import DeclassificationError, EndorsementError
from .label import IntegrityLabel, Label, SecrecyLabel, Tag


@dataclass(frozen=True)
class Declassification:
    """Privilege to remove secrecy tags."""

    tags: FrozenSet[Tag] = frozenset()

    def declassify(
        self, label: SecrecyLabel, tags_to_remove: FrozenSet[Tag]
    ) -> SecrecyLabel:
        """Remove secrecy tags from label.

        Raises:
            DeclassificationError: If any requested tag is not in privilege.
        """
        if not tags_to_remove <= self.tags:
            raise DeclassificationError(tags_to_remove, self.tags)
        return SecrecyLabel(label.tags - tags_to_remove)


@dataclass(frozen=True)
class Endorsement:
    """Privilege to add integrity tags."""

    tags: FrozenSet[Tag] = frozenset()

    def endorse(
        self, label: IntegrityLabel, tags_to_add: FrozenSet[Tag]
    ) -> IntegrityLabel:
        """Add integrity tags to label.

        Raises:
            EndorsementError: If any requested tag is not in privilege.
        """
        if not tags_to_add <= self.tags:
            raise EndorsementError(tags_to_add, self.tags)
        return IntegrityLabel(label.tags | tags_to_add)


@dataclass(frozen=True)
class Privilege:
    """Combined declassification and endorsement privileges."""

    declassification: Declassification = Declassification()
    endorsement: Endorsement = Endorsement()

    def declassify(self, label: Label, tags: FrozenSet[Tag]) -> Label:
        """Convenience: declassify secrecy tags from a Label."""
        return Label(
            self.declassification.declassify(label.secrecy, tags), label.integrity
        )

    def endorse(self, label: Label, tags: FrozenSet[Tag]) -> Label:
        """Convenience: endorse with integrity tags on a Label."""
        return Label(
            label.secrecy, self.endorsement.endorse(label.integrity, tags)
        )
