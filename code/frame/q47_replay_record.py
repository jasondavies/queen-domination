"""Local append-only receipts for the public Q47 replay, owned by one coordinator."""

import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys


def digest(path):
    with path.open("rb") as src:
        return hashlib.file_digest(src, "sha256").hexdigest()


def manifest(repo, index, mode, cases, cube):
    paths = {Path(m.__file__).resolve() for m in tuple(sys.modules.values())
             if getattr(m, "__file__", None) and str(m.__file__).endswith(".py")}
    sources = sorted(p for p in paths if p.parent == repo / "code/frame")
    data = repo / "data/frame"
    files = [*sources, data / "q47_24_two_holes.json", data / "q47_closeout.json",
             data / "q47_independent_25.json", data / "q47_release/core-certificates.zip",
             data / "q47_release/regeneration-formulas.json", repo / "tools/drat-trim"]
    if mode == "regenerate":
        files.append(repo / "tools/cadical")
    return dict(format=1, mode=mode, cases=sorted(map(list, cases)), cube=cube,
                python=sys.version, index_sha256=digest(index),
                pysat={name: digest(Path(module.__file__)) for name, module in sys.modules.items()
                       if name == "pycard" or name == "pysat" or name.startswith("pysat.")},
                zstd_sha256=digest(Path(shutil.which("zstd"))),
                files={str(p.relative_to(repo)): digest(p) for p in files})


def encode(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


class ReplayRecord:
    def __init__(self, stream, inputs):
        self.stream = stream
        fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        self.completed = {}
        self.last = None
        self.inputs_hash = hashlib.sha256(encode(inputs)).hexdigest()
        stream.seek(0)
        while True:
            offset = stream.tell()
            line = stream.readline()
            if not line:
                break
            if not line.endswith(b"\n"):
                # A crash may leave just the last append incomplete.
                if not offset:
                    header = {"inputs": inputs}
                    if not encode([header, self.checksum(header)]).startswith(line):
                        raise ValueError("existing file is not a replay record for these inputs")
                stream.truncate(offset)
                break
            data, checksum = json.loads(line)
            if self.checksum(data) != checksum:
                raise ValueError("checkpoint inputs differ or record is corrupt")
            if offset == 0:
                if data != {"inputs": inputs}:
                    raise ValueError("checkpoint manifest mismatch")
            elif "case" in data:
                case = tuple(data["case"])
                if case in self.completed:
                    raise ValueError("duplicate root receipt")
                self.completed[case] = (data["root"], data["leaves"])
            elif "result" not in data:
                raise ValueError("unexpected checkpoint entry")
            self.last = data
        if self.last is None:
            self.append({"inputs": inputs})

    def checksum(self, data):
        return hashlib.sha256(self.inputs_hash.encode() + encode(data)).hexdigest()

    def append(self, data):
        self.stream.write(encode([data, self.checksum(data)]) + b"\n")
        self.stream.flush()
        os.fsync(self.stream.fileno())
        self.last = data
