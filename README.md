# The domination numbers of the 26 × 26 and 28 × 28 queen's graphs

This repository holds a paper and its verification material. The paper proves γ(Q₂₆) = 14 and
γ(Q₂₈) = 15:
- thirteen queens cannot occupy or attack every square of a 26 × 26 board, and fourteen can;
- fourteen queens cannot do so on a 28 × 28 board, and fifteen can.

These were the two smallest open cases of the queen domination problem (OEIS A075458). Known results give
the other values up to n = 31: γ(Q₂₇) = 14 (Östergård and Weakley, Electron. J. Combin. 8 (2001) #R29),
γ(Q₂₉) = γ(Q₃₀) = 15 and γ(Q₃₁) = 16. So γ(Q_n) is now known for all n ≤ 31 (Corollary 1.2). The
smallest open case is now n = 32, where γ(Q₃₂) ∈ {16, 17}.

## Results

- **Theorem 1.1.** γ(Q₂₆) = 14 and γ(Q₂₈) = 15. The upper bounds come from explicit 14- and 15-queen
  sets. The lower bounds are computer-assisted.
- **Method.** Take a dominating set D of 13 queens, with z_q queens of colour q. Choose 13 empty rows A
  and 13 empty columns B. Every colour-q square of A × B is attacked diagonally, so these squares are
  covered by at most z_q difference diagonals and at most z_q sum diagonals of colour q (Lemma 2.2).
  Stage 1 enumerates the pairs (A, B) that pass this test, up to the four colour-preserving symmetries
  and for z₀ ≤ 6. Only 10 888 pairs pass: 10 887 with colour split (6, 7) and one with (0, 13). Stage 2
  shows that for none of these pairs do 13 queens outside the rows A and columns B dominate the board.
  For n = 28 the same method, with 14 queens and z₀ ≤ 7, leaves 118 765 pairs: 118 662 with split
  (7, 7), 101 with (6, 8), and one each with (0, 14) and (1, 13).
- **Certificates.** For both n, both stages are certified by DRAT proofs checked with drat-trim, so the
  lower bounds do not depend on the search programs:
  - Stage 2: one unsatisfiable CNF per pair (10 888 and 118 765 of them).
  - Stage 1: a cube-and-conquer refutation of the relaxation with every listed pair excluded, reduced by
    symmetry. It has 6 × 76 + 1072 cubes for n = 26 and 6 × 76 + 2 × 1072 cubes for n = 28.

  The proof rests on Lemmas 2.2 and 2.3 and Proposition 2.4, which are proved in the paper, on two short
  CNF encoders, on the cube-orbit enumeration, and on drat-trim.
- **Second programs.** For n = 26 the second stage-1 program and the branch-and-bound stage 2 were run on
  everything. For n = 28 they were run only in part: the second stage-1 program on all parts with
  z₀ ≤ 5 and on 1549 of the 4800 parts with z₀ = 6, and the branch-and-bound stage 2 on the 102 pairs with
  z₀ ∈ {1, 6}. They agree with the main programs wherever they were run.
- **Cloud.** 7457 of the 16 800 stage-1 parts for n = 28 ran on single-core Modal containers, about
  US$4, using `code/modal_stage1.py`. Every returned part was checked locally (log, survivor count,
  SHA-256). The certificates do not depend on this computation.
- **Validation.** The pipeline reproduces the known numbers of n/2-dominating sets for even n ≤ 18 (and
  the known values for n = 20, 22, 24). It also reproduces the 638, 588 and 371 classes of minimum
  dominating sets for n = 8, 14, 16, which are mostly bichromatic. An independent referee wrote SAT-only
  checks (`code/refcheck.py`). They reproduce stage 1 exactly for n ≤ 18, and the class counts by a
  separate pipeline for n ≤ 12.

## Read

- [Manuscript](paper/queen-domination.pdf) and its [LaTeX source](paper/queen-domination.tex).

## Reproduce

You need:
- Python 3.12 with `python-sat==1.9.dev24` (`requirements.txt`). It bundles the CaDiCaL 1.9.5 used for
  the incremental enumerations in `refcheck.py`.
- gcc, `curl`, `sha256sum`, `latexmk`/`pdflatex`.
- CaDiCaL rel-3.1.0 and drat-trim (commit `2e3b2dc`). Neither is included in this repository.
  `scripts/get_tools.sh` downloads both from GitHub, checks their SHA-256 and builds them in `tools/`,
  which is git-ignored. To use local copies of the tarballs, set `CADICAL_TARBALL=…` and
  `DRATTRIM_TARBALL=…`.

```sh
python3 -m venv .venv && .venv/bin/pip install -r requirements.txt
.venv/bin/python scripts/verify.py                   # default: about 20 minutes, at most 3 processes
.venv/bin/python scripts/verify.py --only build|small|referee|records|sample|records28|sample28|upper|paper
.venv/bin/python scripts/verify.py --full            # also reruns the whole n = 26 computation (~15 CPU hours)
.venv/bin/python scripts/verify.py --heavy28         # also reruns a larger part of n = 28 (~6 CPU hours)
```

`scripts/verify.py` works as follows:
- Each step writes a JSON file to `verification/`.
- Each gate compares that output, or the committed records, exactly with [claims.json](claims.json).
- The paper's numbers come from the same file, through the generated macros `paper/claims.tex`
  (`scripts/make_claims_tex.py`).
- It writes logs to `verification/<step>.log` and a summary with input and PDF hashes to
  `verification/summary.json`.
- It exits nonzero on any failed gate, LaTeX warning or bad box.

The default run covers the following steps.
- **build:** compiles the four C programs and fetches and builds CaDiCaL and drat-trim.
- **small:** the full C pipeline for g = n/2 and even n ≤ 18, and for (n, g) = (8, 5), (14, 8). It
  also compares the orbit sets of the two stage-1 programs for every colour split, and for n ≤ 12 with
  brute force.
- **referee:**
  - SAT enumeration of all feasible pairs, compared with stage 1 for n ≤ 18;
  - an independent SAT pipeline for n ≤ 12;
  - direct SAT enumeration of dominating sets for n ≤ 10;
  - the stage-1 DRAT certificate for n = 16 and 18;
  - sanity checks of the two encoders against known positives.
- **records:** consistency of the committed n = 26 records in `data/n26/`:
  - per-part SHA-256 against `MANIFEST`;
  - every one of the 3360 stage-1 parts present;
  - the two stage-1 programs give the same orbits;
  - one UNSAT, DRAT-verified SAT record per survivor;
  - the certificate's base-CNF hash rebuilt from the survivor list, and a verified record for every cube.
- **sample:** reruns a seeded random sample of the n = 26 computation and compares it with the records:
  - 31 stage-1 parts with their stage-2 runs, compared by SHA-256;
  - SAT instances;
  - certificate cubes, compared by CNF hash, UNSAT and VERIFIED.
- **records28:** consistency of the committed n = 28 records in `data/n28/`:
  - every one of the 16 800 stage-1 parts present, with per-part SHA-256 against `MANIFEST`;
  - one UNSAT, DRAT-verified SAT record per survivor, and nothing else;
  - for every z₀ = 0..7, the certificate's base-CNF hash rebuilt from the survivor list, the cube-orbit
    cover, and a verified record for every cube;
  - the partial runs of the second programs and the cloud ledger;
  - the encoders accept the n = 28 survivors and the 15-queen set (known positives).
- **sample28:** reruns a seeded random sample of the n = 28 computation: 20 stage-1 parts, 40 SAT
  instances and 16 certificate cubes, compared with the records.
- **upper:** Kamenetsky's 14-queen set and the independent 14-set of Östergård–Weakley dominate Q₂₆. Their
  14-set dominates Q₂₇. The 15-set in `data/q28_15.txt` dominates Q₂₈. Weakley's 15-set dominates Q₃₀,
  and the sets derived from it dominate Q₂₉ (15 queens) and Q₃₁ (16 queens).
- **paper:** the claims macros and a clean LaTeX build.

`--full` additionally reruns the following, comparing every output with the records:
- n = 20 and 22, and (n, g) = (16, 9);
- the whole n = 26 computation: stage 1 (3360 parts), stage 2, the second stage-1 program (1080 parts),
  SAT + DRAT on all 10 888 pairs, and all 1528 certificate cubes.

`--heavy28` additionally reruns, for n = 28:
- stage 1 on all 7200 parts with z₀ ≤ 5 and on 24 random parts with z₀ = 6, 7;
- SAT + DRAT on 2000 random survivors;
- the whole stage-1 certificate for z₀ ≤ 6 and 40 random cubes for z₀ = 7.

The full n = 28 stage 1 (about 80 CPU hours) is not part of the script.

`--full` has not been run end to end from this repository. Its parts were run when the records
were made, and the default run reruns a sample of each part.

The DRAT proofs of the stage-1 certificates (about 25 GB for n = 26 and 182 GB for n = 28) are not stored. They are regenerated deterministically
from the same CNF with the same solver version and options. The records give each CNF's SHA-256.

## What is proved, and what is computed

**Proved in the paper:** the line relaxation (Lemma 2.2), the symmetry reduction (Lemma 2.3), the
reduction to conditions (a) and (b) (Proposition 2.4), and the symmetry argument for the cube reduction.

**Certified by DRAT proofs checked with drat-trim:** conditions (a) and (b) for n = 26 and n = 28.

**Trusted, small and auditable code:**
- `relax_cnf` in `code/refcheck.py`, which uses PySAT's sequential-counter encoding;
- `build` in `code/sat_place.py`;
- `rep_cubes` and `check_cover` in `code/cert_stage1.py`;
- drat-trim.

**From the literature:** the upper-bound constructions (except the 15-set for Q₂₈, found here), which
are checked here, i(Q₂₈) = 15, and γ(Q_n) ≥ n/2, which is used only for Corollary 1.2.

**Main residual risks:**
- errors in the short encoders. They are cross-checked by agreement with two independent search programs
  for n ≤ 18 and by known positives at n = 26 and 28;
- errors in drat-trim;
- errors in the hand proofs.

No independent human review has been recorded.

## Layout

- `paper/`: manuscript, generated `claims.tex`.
- `code/`:
  - `stage1.c`: stage 1;
  - `stage1_v.c`: second stage-1 program;
  - `brute_ab.c`: all pairs, no pruning;
  - `place.c`: stage 2;
  - `sat_place.py`: stage-2 CNF + CaDiCaL + drat-trim;
  - `refcheck.py`: the referee's SAT checks and `relax_cnf`;
  - `cert_stage1.py`: the stage-1 certificate;
  - `pipeline.py`: the small-n driver;
  - `run_n26.py`, `run_n28.py`: n = 26 and n = 28 reruns;
  - `check_records.py`, `check_records28.py`: record checks;
  - `encode_check28.py`: n = 28 known positives for the encoders;
  - `check_upper.py`: the upper-bound sets;
  - `modal_stage1.py`: the cloud driver used for part of the n = 28 stage 1.
- `scripts/`: `verify.py`, `make_claims_tex.py`, `get_tools.sh`.
- `data/n26/`: the n = 26 records:
  - `survivors.txt`: the 10 888 pairs;
  - `MANIFEST`: per-part SHA-256 of the stage-1 and stage-2 outputs;
  - `stage1_parts.txt` and `stage2_logs.txt`: logs of the two stages;
  - `stage2_place.txt`: stage-2 results;
  - `survivors_v.txt` and `stage1_v_parts.txt`: output of the second stage-1 program;
  - `sat_stage2.txt`: the SAT/DRAT records;
  - `cert_stage1_z*.jsonl`: the certificate records.
- `data/n28/`: the n = 28 records (`.xz` files are xz-compressed text):
  - `survivors.txt.xz`: the 118 765 pairs;
  - `MANIFEST`: per-part SHA-256 of the stage-1 outputs, in the order of `survivors.txt.xz`;
  - `stage1_parts.txt.xz`: stage-1 logs, one per part, with where the part ran;
  - `sat_stage2.txt.xz`: the SAT/DRAT records;
  - `cert_stage1_z*.jsonl`: the certificate records;
  - `stage1_v_parts.txt.xz`, `survivors_v.txt`: the partial second stage-1 run;
  - `stage2_place.txt`, `stage2_logs.txt`: the partial branch-and-bound stage 2;
  - `modal_parts.tsv.xz`, `modal_calls.tsv`: the cloud ledger.

  In these records the program names `lines2` and `lines_v` are `code/stage1.c` and `code/stage1_v.c`
  under their working names. The files used then differed only in comments and one usage string.
- `data/validation/`: part logs of the n = 20, 22, 24 runs.
- `data/kamenetsky26.txt`: Kamenetsky's 14-queen set.
- `data/q28_15.txt`: a 15-queen dominating set of Q₂₈.
- `verification/`: outputs of the last verification run.

## Authorship and AI disclosure

Author: Jason Davies. AI systems produced the mathematics, the code and the manuscript: Claude Opus 5.5
(Anthropic), via Claude Code, under the author's direction. An independent AI referee reviewed the work
and wrote the SAT-based checks and the stage-1 certificate. The author has not read the manuscript or
checked the arguments; see the declaration in the paper.

## License

Apache License 2.0; see [LICENSE](LICENSE). CaDiCaL (MIT) and drat-trim (MIT), which are downloaded
separately, have their own licences.
