# Verify the domination number of the 47 × 47 board

The release checks two 25-queen placements, including an independent one, and gives a computer-assisted exclusion of every 24-queen placement. A reviewer can regenerate and check the selected proofs from a Git checkout. The 12.2 MB index records the 98,114 surviving cases and the branch partitions of their 91,017 symmetry representatives. The 4.3 MB core bundle supplies 1,527 short refutations reused across branches. The arithmetic certificates and placement are also in Git.

## Run from a clean checkout

Use Python 3.11 or later, the `zstd` executable and a C/C++ build toolchain. From the repository root, install the Python dependency and build the pinned CaDiCaL and drat-trim versions.

```sh
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
sh scripts/get_tools.sh
```

For a quick check, verify both placements, the census of surviving frames, every symmetry reference and every branch partition. This command reports 98,114 indexed roots.

```sh
.venv/bin/python code/frame/replay_q47_archive.py data/frame/q47_release/proof-index.jsonl.zst --index-only
```

To try a complete frame, regenerate its SAT proof and check it with drat-trim.

```sh
.venv/bin/python code/frame/replay_q47_archive.py data/frame/q47_release/proof-index.jsonl.zst --regenerate --case 0,19,1,2,2,0,1,1
```

For the full verification, use

```sh
.venv/bin/python code/frame/replay_q47_archive.py data/frame/q47_release/proof-index.jsonl.zst --regenerate --workers 8
```

A successful full run reports 98,114 indexed roots, 7,097 symmetry roots, 91,017 checked roots and 131,547 checked leaves. For each SAT leaf the verifier rebuilds the indexed formula, checks its SHA-256, runs CaDiCaL and independently checks the fresh DRAT proof before discarding it. Temporary space scales with the proofs being checked concurrently. Set `TMPDIR` to choose a scratch disk.

The verifier computes the lexicographically least eight-parameter case under rotations and reflections. Each symmetry reference must point directly to that case, which must have its own proof partition. Selecting a whole root with `--case` replays its representative. For `--cube`, use the representative’s coordinates.

Fresh verification uses the colour encoding on all 5,895 SAT leaves with a square, zero-deficit frame. The release records replacement digests in `regeneration-formulas.json` for 3,867 formerly ordinary leaves and 62 historical leaves. Of the 62, 46 use the colour encoding and 16 use the current ordinary frame encoding. For core and arithmetic leaves the verifier checks the selected exclusion and its applicability to the branch. A failed solve, formula hash check or proof check stops verification with an error.

Before the symmetry reduction the mixed moment rule replaced 895 former leaves with 25 branches across six frames. On each branch the verifier enumerates the possible row, column and queen colour counts. Only the profile with one occupied even row and one occupied even column survives. It checks every possible intersection for the exceptional queen against the diagonal moment conditions. This replaces 34 SAT leaves, 188 core-covered leaves, 667 axis exclusions and six terminal certificates.

As a runtime guide, the historical SAT subtotal was 224.4 CPU-hours solving and 92.5 checking. The colour pass used 3.12 CPU-hours for 3,868 leaves whose earlier proofs took 25.4 CPU-hours. The mixed moment pass subsequently removed 34 SAT leaves, including one of those colour conversions. The symmetry reduction removes a further 9,609 SAT leaves with 15.85 recorded CPU-hours. The component timings suggest about 35 hours on eight fully occupied cores for the current release. They span different machines. Formula construction, the other checks and scheduling also affect elapsed time.

### Release validation

The original release audit reconstructed all 98,114 root formulas, compared all 137,788 original SAT leaf formulas with their indexed digests and checked every core and arithmetic leaf. The colour pass brought the total of regenerated and DRAT-checked replacement formulas to 3,930. The mixed moment partition retained 137,754 SAT leaves. The current symmetry representatives retain 128,145 SAT leaves, including 3,929 replacements.

For the mixed moment update we checked that the 25 new branches cover exactly the 895 former leaves and that every other indexed leaf and root agrees with the audited release. In a clean checkout we replayed all 4,333 core-covered leaves, 237 axis exclusions and 25 mixed moment exclusions. A second diagonal enumeration checked all 94 site and deficit combinations. For the symmetry update, an independent check transformed rectangle corners and line directions, verified all 7,097 references, and compared all 91,017 direct partitions with that prior release. The current core bundle contains exactly the 1,527 referenced certificates. The clean-checkout audit replays all 3,203 core leaves, 182 axis exclusions and 17 mixed moment leaves. The orthodox exclusions also run an independent diagonal enumeration (`code/frame/check_q47_orthodox_enumeration.py`). A fresh full SAT run is available to independent reviewers.

## Replay stored proofs

Reviewers with the separate proof archive can omit `--regenerate` and use `--payload-dir /path/to/archive`. This mode checks the digest and validity of the selected stored DRAT trace for each SAT leaf. Both modes support `--case` and `--cube` for targeted checks.

The original backfill used a separate historical manifest. Fresh verification uses the proof index and bundled certificates in this directory. The optimisation summary records the release file digests and the measured size of the stored evidence. [Optimisation summary](../q47_optimisation_summary.json)
