"""Regression checks for partial and full replay of root symmetry references."""
from collections import Counter
from contextlib import nullcontext
import unittest
from unittest.mock import patch

import replay_q47_archive as replay

# Reflection exchanges the two diagonal deficits.
SOURCE = (2, 7, 7, 7, 0, 1, 2, 0)
TARGET = (2, 7, 7, 7, 0, 1, 0, 2)
DIRECT = dict(case=TARGET, root="digest", leaves=[("", {"rule": "frame"})])
REFERENCE = dict(case=SOURCE, representative=TARGET)


def audit(rows, selected=(), cube=None):
    # Supply the rest of the standard census counter without materialising it.
    counts = Counter(indexed_roots=98112)
    with patch.object(replay, "cases", return_value=[SOURCE, TARGET]), patch.object(
        replay, "index_rows", side_effect=lambda index: nullcontext(iter(rows))
    ):
        return list(replay.audited_rows(None, set(selected), cube, False, counts))


class WholeRootSymmetry(unittest.TestCase):
    def test_proves_representative_once_in_either_order(self):
        expected = [(TARGET, "digest", DIRECT["leaves"])]
        for rows in ([DIRECT, REFERENCE], [REFERENCE, DIRECT]):
            for selected in ((), (SOURCE,), (TARGET,), (SOURCE, TARGET)):
                self.assertEqual(audit(rows, selected), expected)

    def test_rejects_invalid_reference_or_missing_root(self):
        for rows in ([DIRECT], [REFERENCE], [DIRECT, dict(REFERENCE, representative=SOURCE)],
                     [DIRECT, dict(REFERENCE, representative=SOURCE[::-1])],
                     [dict(case=TARGET, representative=SOURCE), REFERENCE],
                     [DIRECT, dict(REFERENCE, leaves=DIRECT["leaves"])]):
            with self.assertRaises(ValueError):
                audit(rows)

    def test_cube_selection_uses_the_indexed_orientation(self):
        with self.assertRaisesRegex(ValueError, "select a cube"):
            audit([REFERENCE, DIRECT], [SOURCE], "")
        historical = dict(DIRECT, case=SOURCE)
        self.assertEqual(audit([historical, DIRECT], [SOURCE], ""), [(SOURCE, "digest", DIRECT["leaves"])])


if __name__ == "__main__":
    unittest.main()
