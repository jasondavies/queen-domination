# γ(Q₃₅) = 19, γ(Q₄₇) = 25 and queen domination numbers up to n = 47

## γ(Q₄₇) = i(Q₄₇) = 25 (27 November 2026)

Twenty-four queens cannot occupy or attack every square of a 47 × 47 board, and twenty-five can. Since
Östergård and Weakley (2001) it had been known only that γ(Q₄₇) ∈ {24, 25}. The paper is
[`paper/q47-domination.pdf`](paper/q47-domination.pdf) ([LaTeX source](paper/q47-domination.tex)).

Östergård and Weakley’s independent 25-queen placement also gives **i(Q₄₇) = 25**. The verifier checks both placements. [Independent placement](data/frame/q47_independent_25.json) · [Verification guide](data/frame/q47_release/README.md)

- **Upper bound.** In zero-based (column, row) coordinates, 24 queens in columns 0, 2, …, 46 leave only the square (7, 46) uncovered
  (`data/frame/q47_24_one_hole.json`). A queen there gives the 25-queen set in `data/frame/q47_closeout.json`.
- **Lower bound.** The frame method of the γ(Q₃₅) paper below, with new odd-board reductions:
  - A margin bound for odd boards removes 271 298 of the 369 412 cases on canonical frame rectangles, leaving 98 114.
  - Board symmetries reduce the 98 114 remaining cases to 91 017 representatives. Their proofs use
    - SAT refutations with DRAT proofs checked by drat-trim, with cube splitting where needed;
    - colour-specific perimeter budgets for square frames;
    - a shared certificate for an orthodox profile;
    - reuse of verified unsatisfiable cores across sibling cubes.
  - First- and second-moment identities for the diagonals closed the last 15 branches of the original
    search, across 13 frames. After combining branches and applying board symmetries, the published
    index includes 182 leaves closed by the axis rule and 17 by the mixed-moment rule.
- **Context.** Đukić established γ(Q₄₈) = 25, Östergård and Weakley gave γ(Q₄₉) = 25, and Chan
  established γ(Q₅₀) = 26 as part of his results for even boards through 64. Together with Q₄₇,
  these give every value through n = 50. As of 27 November 2026, the smallest open case is n = 51.
  [Đukić on Q₄₈](https://doi.org/10.5281/zenodo.24537290) · [Östergård and Weakley](https://doi.org/10.37236/1573) · [Chan on even boards from 50 through 64](https://hexagonmath.org/pdf/2611.01169v1)

### Verify the Q₄₇ result

Install the dependencies and pinned tools following the [verification guide](data/frame/q47_release/README.md).
From the repository root, this quick check verifies both placements, counts the 98,114 surviving cases,
and checks the symmetry references and branch partitions.

```sh
.venv/bin/python code/frame/replay_q47_archive.py data/frame/q47_release/proof-index.jsonl.zst --index-only
```

Full verification also checks the arithmetic exclusions and core certificates, and regenerates and checks
the SAT proofs. The estimated runtime is about 35 hours on eight fully occupied cores, based on component timings.

```sh
.venv/bin/python code/frame/replay_q47_archive.py data/frame/q47_release/proof-index.jsonl.zst --regenerate --workers 8
```

The original 15 terminal exclusions can also be checked separately.

- `code/frame/check_q47_terminal_enumeration.py` is a separate enumeration of the 15 terminal exclusions.
  It uses no SAT solver.
- `data/frame/q47_terminal_moments/` holds the 15 terminal receipts with their CNFs and DRAT proofs, and
  `terminal-roots.json`, the root hashes of the 13 terminal cases.
  `data/frame/q47_same_parity/` holds the related same-parity moment certificates. To replay them, follow
  `data/frame/q47_terminal_moments/README.md`.

**Historical audit.** The closeout checker reconciles the original run ledgers and branch archives in the local `build/` directory. The five-second first pass refuted 87,116 cases and timed out on 10,998. Some early runs retained verification receipts. The Git-only verifier above generates fresh SAT proofs from the release index. The Lean formalisation described below covers the earlier results.

## γ(Q₃₅) = i(Q₃₅) = 19 and certified values through n = 46

The first paper proves that eighteen queens cannot occupy or attack every square of a 35 × 35
board, and nineteen can. [Paper](paper/queen-domination.pdf) · [LaTeX source](paper/queen-domination.tex) · [OEIS A075458](https://oeis.org/A075458)

Since Östergård and Weakley (Electron. J. Combin. 8 (2001) #R29) it had been known
only that γ(Q₃₅) ∈ {18, 19}. Their 19-queen set is independent, so also i(Q₃₅) = 19, and 35 is the smallest
odd n > 15 with γ(Q_n) = ⌈n/2⌉ + 1.

The lower bound is computer-assisted:
- A dominating set is split by the box of its outermost empty rows and columns (the *frame*) and by the
  deficits of occupied lines.
- Exact counting identities for the border and the sides of the box make each of the 128 941 cases a
  small SAT problem.
- Every case is refuted by CaDiCaL with a DRAT proof checked by drat-trim.

The reduction and the completeness of the case list are formalised in Lean 4 (`lean/`), modulo the CNF
encoding and the SAT certificates. A separately written second encoding, solved with Kissat and without
symmetry breaking, independently refutes the 585 hardest cases and a sample of 2200 others.

The same method, with DRAT proofs, gives **γ(Q₄₀) = 21, γ(Q₄₂) = 22, γ(Q₄₄) = 23 and γ(Q₄₆) = 24**. These are
the first certified values for these boards. They confirm the claims in S. Neuhaus's 2009 dissertation
(below), which rest on an uncertified integer-programming computation. Hint and Conquer covers even
n ≤ 38 only.

The repository also contains **independent confirmations of known even values**:
- The same frame method gives DRAT-checked proofs of γ(Q₃₂) = 17, γ(Q₃₄) = 18 and γ(Q₃₆) = 19, and of
  γ(Q₂₆) = 14 and γ(Q₂₈) = 15.
- For n = 26, 28 there is also a second, completely independent two-stage method: a line relaxation plus
  SAT, with DRAT certificates for both stages and a complete certificate replay.

**The even values are not new.**
- They were first established, with DRAT-checked SAT proofs, in the preprint *Hint and Conquer: New
  Queen Domination Numbers by SAT Solving* (October 2026; `doc.pdf` on branch `hint-and-conquer` of
  [github.com/TahaRostami/Gamma](https://github.com/TahaRostami/Gamma)), together with γ(Q₃₈) = 20. Its
  box split with counting hints is the basis of the frame method here.
- They had been claimed earlier, by an integer-programming computation without certificates, in
  S. Neuhaus's dissertation (Universität zu Köln, 2009, [kups.ub.uni-koeln.de/2916](https://kups.ub.uni-koeln.de/2916/)).
- For n = 26, the repository [github.com/jkolantree/BSC](https://github.com/jkolantree/BSC) contains a Lean 4
  development, committed in August 2026, whose final theorem states γ(Q₂₆) = 14. Its proof uses parity
  shadows, polynomial identities and a monochromatic case analysis, not SAT. We have not built or checked it.
- An earlier version of this repository presented γ(Q₂₆) and γ(Q₂₈) as new; that was wrong and has been
  corrected.

With these values, γ(Q_n) is known for all n ≤ 46 (and, with γ(Q₄₇) = 25 above and the results cited
there, for all n ≤ 50). The odd values 37, 39, 41 and 45 are ⌈n/2⌉ by Östergård–Weakley. For 43,
Neuhaus's explicit 22-set (checked here) and the lower bound ⌈n/2⌉ give γ(Q₄₃) = 22.

### Results of the first paper

- **Theorem 1.1.** γ(Q₃₅) = i(Q₃₅) = 19.
  - **Upper bound.** Two explicit 19-sets, checked by the script. One is ours. The other is the
    independent set of Östergård–Weakley.
  - **Lower bound (paper, Sections 2–3).**
    - The list L(35, 18) has 5050 canonical frames and 128 941 cases.
    - 128 356 cases are refuted by a plain formula.
    - The remaining 585 zero-deficit cases need residual symmetry breaking (Lemma 2.5). Of these, 508 are
      refuted whole and 77 by verified 16-way cube covers (1755 cubes).
    - Every proof was checked by drat-trim, and there is no satisfiable case.
    - The run took 53.1 + 27.6 CPU hours (solve + check), and the proofs came to about 232 GB.
    - All 130 111 formulas were rebuilt and their SHA-256 hashes compared with the records.
- **Theorem 1.3** (claimed by Neuhaus). γ(Q₄₀) = 21, γ(Q₄₂) = 22, γ(Q₄₄) = 23, γ(Q₄₆) = 24.
  - The frame method gives 24 871, 29 447, 34 854 and 40 728 cases, all UNSAT with drat-trim-verified
    proofs.
  - No case timed out at 1800 s, so neither symmetry breaking nor cubes were used.
  - The case lists were also rebuilt by a separate enumeration with a Burnside check of the frame counts
    (`code/frame/final_check40.py`).
  - Upper-bound sets:
    - for Q₄₀, Q₄₂ and Q₄₆, found by SAT search and checked;
    - for Q₄₄, Neuhaus's 22-set of Q₄₃ plus a corner (file from
      [github.com/stefanneuhaus/queens-domination-solutions](https://github.com/stefanneuhaus/queens-domination-solutions),
      CC BY 4.0, included unchanged in `data/frame/neuhaus/`).
- **Theorem 1.4** (Hint and Conquer; claimed by Neuhaus). γ(Q₂₆) = 14, γ(Q₂₈) = 15, γ(Q₃₂) = 17,
  γ(Q₃₄) = 18, γ(Q₃₆) = 19.
  - The frame method has records for all five, every case UNSAT and DRAT-verified, plus the explicit
    upper-bound sets.
  - For n = 26, 28 the line-relaxation method is a second proof (below).
- **Lean (paper, Section 7).** `lean/` formalises the reduction (Layer 1) for general n and k ≤ n − 2:
  - the identities (F), (V), (H);
  - the covering Proposition 2.3;
  - the semantic part of Lemma 2.4 (soundness of the formulas) and Lemma 2.5 (residual symmetry);
  - that the enumerated case list equals the lists of the n = 32 and n = 35 runs (343 kernel computations);
  - the 19-queen upper bound.

  Its final theorem `gamma_35_eq_19_of_cases35_unsat_mixed` derives γ(Q₃₅) = 19 from the hypothesis that
  every listed case has no model (plain, or with the symmetry-breaking condition). **Not formalised:**
  - Layer 2: that the CNF written by `code/frame/enc.py` (and the symmetry-breaking clauses and cubes)
    has a model whenever `CaseSat` does;
  - the DRAT certificates;
  - the link between the Lean data file and the records. A script checks that link (the `leandata`
    step).

  Axioms: only `propext`, `Classical.choice`, `Quot.sound`. There is no `sorry` and no `native_decide`.
- **Cross-check for n = 35 (paper, Section 6).** This is a second case enumeration and a second encoding
  (`code/xcheck35/`): sorting networks, the product at-most-one encoding, and the identities as
  equalities for every box shape. It is solved with Kissat 4.0.4 without any symmetry breaking.
  - Its controls are finished:
    - k = (n−1)/2 for every odd n ≤ 35;
    - complete runs of (13, 7) and (15, 8);
    - zero-deficit differential tests against the main encoder.
  - **The 585 hard cases:** all refuted. 14 needed cube splitting, giving 795 UNSAT leaves; the run took
    76.5 CPU hours.
  - **A sample of 2200 other cases** (2000 random and the 200 slowest in the main run): all UNSAT.
  - There is no SAT formula and no disagreement with the main computation.
  - The script rebuilds all 809 + 2200 formulas and compares their hashes.
- **Line relaxation for n = 26, 28 (paper, Section 8).** Take a dominating set D of n/2 queens, with z_q
  queens of colour q. Choose n/2 empty rows A and n/2 empty columns B.
  - Every colour-q square of A × B is attacked diagonally, so these squares are covered by at most z_q
    difference diagonals and at most z_q sum diagonals of colour q.
  - Stage 1 enumerates the pairs (A, B) that pass this test, up to the four colour-preserving symmetries:
    10 888 pairs for n = 26 and 118 765 for n = 28.
  - Stage 2 shows that for none of these pairs do n/2 queens outside the rows A and columns B dominate
    the board.
  - Both stages are certified by DRAT proofs checked with drat-trim:
    - stage 2 with one unsatisfiable CNF per pair;
    - stage 1 with a cube-and-conquer refutation of the relaxation with every listed pair excluded.
  - The complete certificate replay (`--certify-all`) has been run. Its records are in `data/replay/`.
  - Second programs, the cloud ledger and the validation are described in the paper (Section 8.4).

### Reproduce the Q₃₅ paper and its results through n = 46

You need:
- Python 3.12 with `python-sat==1.9.dev24` (`requirements.txt`). It bundles the CaDiCaL 1.9.5 used for
  the incremental enumerations in `refcheck.py`.
- gcc, `curl`, `sha256sum`, `latexmk`/`pdflatex`.
- CaDiCaL rel-3.1.0 and drat-trim (commit `2e3b2dc`). Neither is included in this repository.
  `scripts/get_tools.sh` downloads both from GitHub, checks their SHA-256 and builds them in `tools/`,
  which is git-ignored. To use local copies of the tarballs, set `CADICAL_TARBALL=…` and
  `DRATTRIM_TARBALL=…`.
- For `--lean` only: elan (it installs Lean 4.35.0 from `lean/lean-toolchain`), network access for
  `lake exe cache get` (prebuilt Mathlib), and about 8 GB of disk in `lean/.lake/` (git-ignored).
- To rerun the cross-check solver calls (not needed by the script): Kissat 4.0.4 (built from git
  `8af8e56f`, SHA-256 of the binary `1aeb303c…6be52`) at `tools/kissat`.

```sh
python3 -m venv .venv && .venv/bin/pip install -r requirements.txt
.venv/bin/python scripts/verify.py                   # default: about an hour, at most 3 processes
.venv/bin/python scripts/verify.py --only upper      # check the upper-bound placements
.venv/bin/python scripts/verify.py --help            # list the other verification steps
.venv/bin/python scripts/verify.py --frame-rehash-all  # the frame step rebuilds every formula hash (~1 CPU hour)
.venv/bin/python scripts/verify.py --lean            # also builds lean/ and checks its axioms (~11 minutes)
.venv/bin/python scripts/verify.py --full            # also reruns the whole n = 26 computation (~15 CPU hours)
.venv/bin/python scripts/verify.py --heavy28         # also reruns a larger part of n = 28 (~6 CPU hours)
.venv/bin/python scripts/verify.py --certify-all --jobs 10   # also replays every certificate formula (~45 CPU hours)
```

`--certify-all` is the certificate-only full verification. For n = 26 and n = 28 it rebuilds every
stage-1 cube formula and every stage-2 placement formula from the committed survivor lists, solves each
with CaDiCaL, checks each DRAT proof with drat-trim and deletes it. It does not rerun the searches,
which the certificates do not depend on. Its work directory `build/certify/` is bound to a manifest of
n, g, the survivor-list hash, the solver, checker and encoder hashes and T. An interrupted run resumes,
and a directory made for different inputs is refused. A completed replay writes compacted records to
`data/replay/` and compares them with the original records.

`scripts/verify.py` works as follows:
- Each step writes a JSON file to `verification/`.
- Each gate compares that output, or the committed records, exactly with [claims.json](claims.json).
- The paper's numbers come from the same file, through the generated macros `paper/claims.tex`
  (`scripts/make_claims_tex.py`).
- It writes logs to `verification/<step>.log` and a summary with input and PDF hashes to
  `verification/summary.json`.
- It exits nonzero on any failed gate, LaTeX warning or bad box.
- `verification/` is not tracked, and a run modifies no tracked file. The paper is built in
  `build/paper` with `SOURCE_DATE_EPOCH` from `claims.json`, and the build must be byte-identical to the
  committed `paper/queen-domination.pdf` (`--write-pdf` replaces it).

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
  - sanity checks of the two encoders against known positives;
  - `resume_test` (`code/test_resume.py`): the resume regression tests for the certificate driver,
    including the external reviewer's example.
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
- **replay:** the records of the completed `--certify-all` replay in `data/replay/`, compared with the
  original records (`code/certify_all.py --compare`):
  - every one of the 1528 + 2600 stage-1 cubes and 10 888 + 118 765 stage-2 formulas is present;
  - each is UNSAT and VERIFIED, with the original CNF hash.
- **frame:** the frame-method records in `data/frame/` (`code/frame/check_frame.py coverage`):
  - for (n, k) = (35, 18), the case list L(35, 18) is rebuilt from first principles and must equal the set
    of case keys in the records;
  - every case is refuted, by a plain UNSAT + VERIFIED record or by a complete cover of verified cube
    records, and there is no SAT record;
  - the counts, CPU hours and proof sizes match the claims;
  - the CNFs of a seeded sample of 2000 plain and 200 cube records are rebuilt by `enc.py` (and
    `run_hard.build`) and their hashes compared (all 130 111 with `--frame-rehash-all`);
  - the same checks (300 sampled formulas each) for (32, 16), (34, 17), (36, 18), (40, 20), (42, 21),
    (44, 22), (46, 23), (26, 13), (28, 14) and (35, 17).
- **framesample:** re-solves 8 cases for n = 35 and 3 each for n = 32, 34, 36 with CaDiCaL + drat-trim:
  same CNF hash, UNSAT, VERIFIED.
- **frametests:**
  - the brute-force test of the identities;
  - the waste-term test of the encoder;
  - the symmetry-breaking test;
  - the exact solution-set comparison with a theory-free enumeration for 9 pairs (n, k);
  - **framevalid:** the recorded validation runs of the frame method:
    - k = n/2 for even n ≤ 30: SAT exactly for 4, 6, 10, 12, 18, 30;
    - k = (n−1)/2 for odd n ≤ 31: SAT exactly for 3, 11;
    - k = (n+1)/2: SAT for 5, 7, 9, 13, 17, 19, 21, UNSAT for 15;
    - n = 32 with a second encoding and Glucose;
    - every model checked.
- **leandata:** `lean/scripts/check_cases.py` for n = 35 and 32. The case list in
  `lean/QueenDom/Cases<N>Data.lean` must equal the refuted cases in the records and `geom.cases_by_frame`.
- **xcheck:** the cross-check records in `data/xcheck35/` (`code/xcheck35/check_xcheck.py`):
  - the separately written case list equals L(35, 18);
  - the negative controls k = (n−1)/2 for n = 5..35;
  - the complete runs (13, 7) and (15, 8);
  - the zero-deficit differential tests;
  - the 585 hard cases and the 2200-case sample: all refuted by complete cube trees, with no SAT record;
  - every CNF of the trees (809 + 2200) rebuilt by `encx.py` and compared by hash.
- **upper:**
  - Kamenetsky's 14-queen set and the independent 14-set of Östergård–Weakley dominate Q₂₆. Their 14-set
    dominates Q₂₇.
  - The 15-set in `data/q28_15.txt` dominates Q₂₈.
  - Weakley's 15-set dominates Q₃₀, and the sets derived from it dominate Q₂₉ (15 queens) and Q₃₁
    (16 queens).
  - The independent 19-set of Östergård–Weakley dominates Q₃₅.
  - **upper_frame:** these sets in `data/frame/` dominate:
    - the 17-, 18-, 19- and 19-sets of Q₃₂, Q₃₄, Q₃₅ and Q₃₆;
    - the 21-, 22-, 23- and 24-sets of Q₄₀, Q₄₂, Q₄₄ and Q₄₆.

    Neuhaus's 22-set dominates Q₄₃, and the Q₄₄ set is that set plus the corner.
- **tamper:** `scripts/tamper.py` copies the tracked files and alters one record at a time, then requires
  the corresponding step to fail. It also requires an unaltered copy to pass. There are 15 cases:
  - n = 28: survivors, certificate cubes, SAT records, a claim, a part record, the 15-set;
  - n = 26: survivors and base hash;
  - frame records: an n = 35 record marked SAT, a cube of a split case dropped, an n = 32 record dropped;
  - the Q₃₅ 19-set;
  - a replay record.
- **lean** (only with `--lean`):
  - `lake exe cache get && lake build` in `lean/`;
  - `lake env lean Axioms.lean`;
  - all 116 reported theorems, including `gamma_35_eq_19_of_cases35_unsat_mixed`, and all 343 case-list
    pieces must depend only on `propext`, `Classical.choice`, `Quot.sound`.
- **paper:** the claims macros and a clean, reproducible LaTeX build.

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

### What is proved and computed in the first paper

#### Frame method (n = 35 and the even confirmations)

**Proved in the paper (Section 2):** facts (E1)–(E5) (Lemma 2.1), the identities (F), (V), (H)
(Theorem 2.2), the covering Proposition 2.3, the soundness of the formulas (Lemma 2.4), residual symmetry
breaking (Lemma 2.5) and the cube cover. `code/frame/PROOFS.md` has the same proofs in the numbering used by
`lean/README.md`. Comments in `enc.py` and `geom.py` that refer to "NOTES" mean these notes.

**Formalised in Lean (`lean/`):**
- Lemma 2.1, Theorem 2.2 and Proposition 2.3;
- the semantic parts of Lemmas 2.4 and 2.5;
- that the case lists of the n = 32 and n = 35 runs are exactly L(n, k);
- the upper-bound sets for n = 32 and n = 35.

The explicit case lists for the other n are not in Lean. They rest on `geom.py`; for n = 40–46 they are
also checked against a separate enumeration.

**Certified by DRAT proofs checked with drat-trim:** every case formula for n = 26, 28, 32, 34, 35, 36, 40,
42, 44, 46 (and (35, 17)).

**Trusted, small and auditable code (not formalised):**
- `code/frame/enc.py`, the formula Φ(case) with its own sequential counter;
- `sbp_clauses` in `code/frame/hard_test.py`, with `layer_vars` and `build` in `code/frame/run_hard.py`;
- the coverage rule in `code/frame/check_frame.py` (as in `final_check35.py`);
- `lean/scripts/check_cases.py`;
- drat-trim.

**Cross-checked:**
- by a separately written enumeration and encoding with Kissat (`code/xcheck35/`): the 585 hard cases and
  a 2200-case sample;
- for n = 32, by `enc_b.py` with Glucose 4.

#### Line relaxation (n = 26, 28)

**Proved in the paper:** the line relaxation (Lemma 8.2), the symmetry reduction (Lemma 8.3), the
reduction to conditions (a) and (b) (Proposition 8.4), and the symmetry argument for the cube reduction.

**Certified by DRAT proofs checked with drat-trim:** conditions (a) and (b) for n = 26 and n = 28.

**Trusted, small and auditable code:**
- `relax_cnf` in `code/refcheck.py`, which uses PySAT's sequential-counter encoding;
- `build` in `code/sat_place.py`;
- `rep_cubes` and `check_cover` in `code/cert_stage1.py`;
- drat-trim.

#### Literature

**From the literature:**
- the upper-bound constructions, which are checked here; the 15-set for Q₂₈ and the sets for Q₃₂, Q₃₄,
  Q₃₅, Q₃₆, Q₄₀, Q₄₂, Q₄₆ were found here;
- the Q₄₃ set of Neuhaus used for Q₄₄;
- the odd values of Proposition 1.5 for n = 33, 37, 39, 41, 45 (Östergård–Weakley) and the upper bound for
  n = 43 (Neuhaus);
- i(Q₂₈) = 15;
- γ(Q_n) ≥ ⌈n/2⌉ for all n except 3 and 11. The first paper uses this bound in Proposition 1.5.

**External review.** An external AI review (ChatGPT Pro) of the code regenerated all 15 base formulas
and all 4128 cube formulas of the stage-1 certificates (1528 for n = 26, 2600 for n = 28) from the
survivor lists, and their hashes are equal to the recorded ones. It found three defects, now corrected,
none of which affected the claimed values:
- When resumed, `code/cert_stage1.py` reused recorded cubes without checking the header, the base
  formula or each cube's formula hash. It now validates all three and re-solves failed, interrupted or
  mismatched cubes. `code/test_resume.py` includes the reviewer's repro.
- drat-trim did not compile under GCC 14. It now builds with `-D_DEFAULT_SOURCE`.
- The paper omitted the exceptions n = 3, 11 when stating the range of γ(Q_n) for n ≤ 120.

Every recorded cube's formula hash was computed from the exact CNF text given to the solver. The n = 28,
z₀ = 7 certificate run was stopped once, after 292 of its 1072 cubes, and resumed with the same
arguments and the same, unchanged survivor list; only the number of processes changed.

**Main residual risks:**
- errors in the short encoders (Layer 2 of the frame method is not formalised):
  - the relaxation encoders are cross-checked by agreement with two independent search programs for
    n ≤ 18 and by known positives at n = 26 and 28;
  - the frame encoder is cross-checked by exact solution sets for small (n, k), known values, planted
    positives and the second encodings;
  - for odd boards with k = (n+1)/2 the only negative control is n = 15;
- errors in drat-trim;
- errors in the hand proofs of the relaxation (those of the frame method are formalised in Lean).

No independent human review has been recorded.

### Files for the first paper

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
  - `certify_all.py`: the certificate-only full replay (`verify.py --certify-all`);
  - `test_resume.py`: resume regression tests for `cert_stage1.py`;
  - `modal_stage1.py`: the cloud driver used for part of the n = 28 stage 1.
  - `frame/`: the frame method. The original Q₃₅ versions of `enc.py` and `geom.py` are in
    [revision bc37cb0](https://github.com/jasondavies/queen-domination/tree/bc37cb0a1c0d1f70ba93fe1c6c7eb04d6773e25e/code/frame).
    Both match the [recorded source hashes](data/frame/SHA256SUMS_code_n35run.txt).
    The current `geom.py` still matches. The current `enc.py` accepts an optional
    `queen_cardinality` argument and uses the original `exactly` function by default.
    - `geom.py`: frames, the action of the symmetries on cases, admissibility, `cases_by_frame` = L(n, k);
    - `enc.py`: the formula Φ(case), with its own sequential counter;
    - `enc_b.py`: the second encoding used for n = 32;
    - `run_cases.py`, `run_hard.py`, `hard_test.py`, `plan35.py`: the drivers (DRAT mode: CaDiCaL +
      drat-trim). Residual symmetry breaking and cubes are in `hard_test.py` and `run_hard.py`;
    - `final_check35.py`, `check_hard.py`, `check_records.py`, `status35.py`: the checkers used at run
      time, on uncompressed records;
    - `check_frame.py`: the checks run by `verify.py`;
    - `verify_identities.py`, `test_enc.py`, `test_waste.py`, `test_sbp.py`: tests;
    - `find_plus1.py`: the SAT search for the upper-bound sets;
    - `final_check40.py`: the final check used for n = 40–46. It rebuilds the case list independently with a
      Burnside count, then calls `final_check35.py`;
    - `q44_from_q43.py`: the Q₄₄ set from Neuhaus's Q₄₃ set;
    - `find_odd_perm.py`: an unsuccessful search variant, kept for the record;
    - `PROOFS.md`: the proofs.
  - `xcheck35/`: the independent cross-check:
    - `cases.py`: the separate case list;
    - `cnf.py`, `encx.py`: encoding X;
    - `xrun.py`, `ksolve.py`: Kissat driver;
    - `xcover.py`: tree coverage;
    - `diff_cases.py`, `plain_indep.py`: differential tests;
    - `test_cnf.py`, `test_sets.py`, `planted_x.py`: tests;
    - `check_xcheck.py`: the checks run by `verify.py`.
- `scripts/`: `verify.py`, `tamper.py`, `make_claims_tex.py`, `get_tools.sh`.
- `lean/`: the Lean 4 formalisation; see `lean/README.md` (build, map from the proofs to Lean, what is
  outside Lean) and `lean/AXIOMS.txt`.
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
- `data/replay/n26/`, `data/replay/n28/`: records of the completed certificate replay (`--certify-all`).
  Each directory has the manifest, the cube records and the stage-2 records.
- `data/frame/`: frame-method records (`.jsonl.xz`: one JSON line per case or cube, with case, cube,
  `cnf_sha256`, result, drat status, CPU times, proof size):
  - `d_35_18.jsonl.xz`, `d_35_18_sq.jsonl.xz`, `h_35_18.jsonl.xz`: n = 35 phases 1, 2, 3;
  - `d_{26_13,28_14,32_16,34_17,36_18,40_20,42_21,44_22,46_23,35_17}.jsonl.xz`: the other runs;
  - `final_check_{40_20,42_21,44_22,46_23}.json`, `n40.log` to `n46.log`, `even42_46.log`: the final checks
    (independent case list, coverage, full CNF rehash) and the run logs for n = 40–46;
  - `hard35_cases.jsonl`: the 585 phase-3 cases;
  - `final_check_35_18.json`, `check_hard_35_18.json`: the checks at the end of the run, all CNF hashes
    rebuilt;
  - `n35_master.log`: the run log;
  - `SHA256SUMS_*.txt`: hashes of code and uncompressed records at run time;
  - `enc_as_of_n32_run.py`: the encoder version of the n = 32 run. Its default output is byte-identical,
    see `d_32_16.check*.json`;
  - `plus1_{32,34,36}.json`, `q35_19.json`, `q{40_21,42_22,44_23,46_24}.json`: the upper-bound sets;
  - `neuhaus/appendix_01_q43_01cover.txt`: Neuhaus's 22-set of Q₄₃. It is from
    github.com/stefanneuhaus/queens-domination-solutions, CC BY 4.0, unchanged;
  - `validation/`: records of the validation runs (`v_*` even, `om_*` and `o_*` odd, `vb_*` second
    encoding), `planted.log` and `planted{40,42,44,46}.log`.
- `data/xcheck35/`: cross-check records:
  - `hard_cases_35_18.jsonl.xz`, `sample_cases_35_18.jsonl.xz`: inputs;
  - `x_hard_35_18.jsonl.xz`, `x_sample_35_18.jsonl.xz`: results;
  - `xcover_hard.json`, `xcover_sample.json`: the tree checks with full rehash at the end of the run;
  - `ctl/`: controls;
  - `logs/`: test logs.
- `data/validation/`: part logs of the n = 20, 22, 24 runs.
- `data/kamenetsky26.txt`: Kamenetsky's 14-queen set.
- `data/q28_15.txt`: a 15-queen dominating set of Q₂₈.
- Upper-bound sets for Q₃₂ to Q₄₆ are in `data/frame/`. The Östergård–Weakley sets are in
  `code/check_upper.py`.
- `verification/` (not tracked): outputs of verification runs.

### Authorship and AI disclosure for the Q₃₅ paper

Author: Jason Davies.
- AI systems produced the mathematics, the code, the Lean formalisation and the manuscript: Claude Opus 5.5
  (Anthropic), via Claude Code, under the author's direction.
- The frame/deficit case split was first proposed in an earlier, uncertified attempt by Claude Fable 5.2
  (Claude for web), run by the author. It was re-derived, proved and reimplemented here, and compared
  with that attempt's logs only afterwards.
- An independent AI referee reviewed the work and wrote the SAT-based checks and the stage-1
  certificate. An external AI review (ChatGPT Pro) of the code
found the defects listed above. The AI system's literature search missed the prior work of Hint and
Conquer and of Neuhaus, so the first published version of this repository and of the OEIS entry
presented the values as new; this was corrected. The author has not read the manuscript or checked the
arguments; see the declaration in the paper.

## License

Apache License 2.0; see [LICENSE](LICENSE), except `data/frame/neuhaus/appendix_01_q43_01cover.txt`, which is
S. Neuhaus's file under CC BY 4.0 (its header gives the licence). CaDiCaL (MIT) and drat-trim (MIT), which are downloaded
separately, have their own licences; Kissat (MIT) is not included. The Lean sources use Mathlib
(Apache 2.0), which `lake` downloads.
