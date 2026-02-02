"""Unit tests for IFC Labels library."""

import pytest
from labels import (
    Label,
    SecrecyLabel,
    IntegrityLabel,
    Privilege,
    Declassification,
    Endorsement,
    DeclassificationError,
    EndorsementError,
)


class TestSecrecyLabel:
    def test_can_flow_to_subset(self):
        """Source with fewer tags can flow to target with more."""
        source = SecrecyLabel(frozenset({"pii"}))
        target = SecrecyLabel(frozenset({"pii", "medical"}))
        assert source.can_flow_to(target)

    def test_cannot_flow_to_superset(self):
        """Source with more tags cannot flow to target with fewer (would leak)."""
        source = SecrecyLabel(frozenset({"pii", "medical"}))
        target = SecrecyLabel(frozenset({"pii"}))
        assert not source.can_flow_to(target)

    def test_join_unions_tags(self):
        a = SecrecyLabel(frozenset({"pii"}))
        b = SecrecyLabel(frozenset({"medical"}))
        assert a.join(b) == SecrecyLabel(frozenset({"pii", "medical"}))

    def test_meet_intersects_tags(self):
        a = SecrecyLabel(frozenset({"pii", "medical"}))
        b = SecrecyLabel(frozenset({"medical", "financial"}))
        assert a.meet(b) == SecrecyLabel(frozenset({"medical"}))


class TestIntegrityLabel:
    def test_can_flow_to_superset(self):
        """Source with more trust can flow to target with less."""
        source = IntegrityLabel(frozenset({"verified", "trusted"}))
        target = IntegrityLabel(frozenset({"verified"}))
        assert source.can_flow_to(target)

    def test_cannot_flow_to_subset(self):
        """Source with less trust cannot flow to target with more (taint)."""
        source = IntegrityLabel(frozenset({"verified"}))
        target = IntegrityLabel(frozenset({"verified", "trusted"}))
        assert not source.can_flow_to(target)

    def test_join_unions_tags(self):
        """Join is least upper bound (union)."""
        a = IntegrityLabel(frozenset({"verified", "trusted"}))
        b = IntegrityLabel(frozenset({"verified"}))
        assert a.join(b) == IntegrityLabel(frozenset({"verified", "trusted"}))

    def test_meet_intersects_tags(self):
        """Meet is greatest lower bound (intersection)."""
        a = IntegrityLabel(frozenset({"verified"}))
        b = IntegrityLabel(frozenset({"trusted"}))
        assert a.meet(b) == IntegrityLabel(frozenset())


class TestLabel:
    def test_can_flow_to_both_pass(self):
        source = Label(
            secrecy=SecrecyLabel(frozenset({"pii"})),
            integrity=IntegrityLabel(frozenset({"verified", "trusted"})),
        )
        target = Label(
            secrecy=SecrecyLabel(frozenset({"pii", "medical"})),
            integrity=IntegrityLabel(frozenset({"verified"})),
        )
        assert source.can_flow_to(target)

    def test_cannot_flow_secrecy_violation(self):
        source = Label(secrecy=SecrecyLabel(frozenset({"pii", "medical"})))
        target = Label(secrecy=SecrecyLabel(frozenset({"pii"})))
        assert not source.can_flow_to(target)

    def test_cannot_flow_integrity_violation(self):
        source = Label(integrity=IntegrityLabel(frozenset({"verified"})))
        target = Label(integrity=IntegrityLabel(frozenset({"verified", "trusted"})))
        assert not source.can_flow_to(target)


class TestDeclassification:
    def test_declassify_permitted_tags(self):
        decl = Declassification(frozenset({"pii", "medical"}))
        label = SecrecyLabel(frozenset({"pii", "medical", "financial"}))
        result = decl.declassify(label, frozenset({"pii"}))
        assert result == SecrecyLabel(frozenset({"medical", "financial"}))

    def test_declassify_unpermitted_raises(self):
        decl = Declassification(frozenset({"pii"}))
        label = SecrecyLabel(frozenset({"pii", "medical"}))
        with pytest.raises(DeclassificationError) as exc:
            decl.declassify(label, frozenset({"pii", "medical"}))
        assert exc.value.requested == frozenset({"pii", "medical"})
        assert exc.value.permitted == frozenset({"pii"})


class TestEndorsement:
    def test_endorse_permitted_tags(self):
        end = Endorsement(frozenset({"verified", "trusted"}))
        label = IntegrityLabel(frozenset({"verified"}))
        result = end.endorse(label, frozenset({"trusted"}))
        assert result == IntegrityLabel(frozenset({"verified", "trusted"}))

    def test_endorse_unpermitted_raises(self):
        end = Endorsement(frozenset({"verified"}))
        label = IntegrityLabel(frozenset())
        with pytest.raises(EndorsementError) as exc:
            end.endorse(label, frozenset({"verified", "trusted"}))
        assert exc.value.requested == frozenset({"verified", "trusted"})
        assert exc.value.permitted == frozenset({"verified"})


class TestPrivilege:
    def test_declassify_on_label(self):
        priv = Privilege(declassification=Declassification(frozenset({"pii"})))
        label = Label(secrecy=SecrecyLabel(frozenset({"pii", "medical"})))
        result = priv.declassify(label, frozenset({"pii"}))
        assert result.secrecy == SecrecyLabel(frozenset({"medical"}))

    def test_endorse_on_label(self):
        priv = Privilege(endorsement=Endorsement(frozenset({"verified"})))
        label = Label(integrity=IntegrityLabel(frozenset()))
        result = priv.endorse(label, frozenset({"verified"}))
        assert result.integrity == IntegrityLabel(frozenset({"verified"}))
