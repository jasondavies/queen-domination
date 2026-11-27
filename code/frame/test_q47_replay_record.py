"""A failed root must never turn into a completed root after a restart."""

import json
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import replay_q47_archive as replay
from q47_replay_record import ReplayRecord


class ResumeTest(unittest.TestCase):
    def test_interruption_and_input_binding(self):
        args = SimpleNamespace(index=None, cube=None, index_only=False, certificates_only=False,
                               regenerate=True, workers=1)
        cases = [(0,), (1,)]
        rows = [(case, str(case), [("", {"rule": "frame"})]) for case in cases]
        inputs = {"mode": "regenerate"}
        with TemporaryDirectory() as tmp, patch.object(replay, "check_witness"), \
                patch.object(replay, "audited_rows", return_value=rows):
            path = Path(tmp) / "record"
            with path.open("a+b") as f, patch.object(replay, "replay_case", side_effect=[1, RuntimeError]):
                with self.assertRaises(RuntimeError):
                    replay.run(args, None, set(cases), ReplayRecord(f, inputs))
            with path.open("ab") as f:
                f.write(b'[{"case":')  # torn append
            with path.open("a+b") as f, patch.object(replay, "replay_case", return_value=1) as check:
                replay.run(args, None, set(cases), ReplayRecord(f, inputs))
                self.assertEqual([c.args[0] for c in check.call_args_list], [cases[1]])
            final, _ = json.loads(path.read_bytes().splitlines()[-1])
            self.assertEqual(final["result"], "selected-proofs")
            self.assertEqual(final["counts"], {"checked_leaves": 2, "checked_roots": 2})
            with path.open("a+b") as f, self.assertRaises(ValueError):
                ReplayRecord(f, {"mode": "certificates"})
            data = path.read_bytes().replace(b'"leaves":1', b'"leaves":2', 1)
            path.write_bytes(data)
            with path.open("a+b") as f, self.assertRaises(ValueError):
                ReplayRecord(f, inputs)


if __name__ == "__main__":
    unittest.main()
