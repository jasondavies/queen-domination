/-
GENERATED FILE -- do not edit.  Produced by scripts/gen_cases.py from the run logs
  frame/out/d_35_18.jsonl        (115608 records, sha256 c01d73d09133e76b1b83ab94dbc0502a842cf77713fa9d9cf854fb595706e1a5)
  frame/out/d_35_18_sq.jsonl     ( 12755 records, sha256 57fac31758db85c3580c3e6ded72d5954da7a952ee44197ddbc11c5aaa2ac976)
  frame/out/h_35_18.jsonl        (  1756 records, sha256 257d74c1a7fd5ae3530a5fea44eeb3fec72b5c31658a2c0b82229c732ba10b0f)
of the referee's frame-method run for n = 35, k = 18: 128941 cases, 5050 frames;
128356 refuted by a plain record (UNSAT, drat-trim VERIFIED), 585 by verified cube records of run_hard.py.
Kernel computations: the case list `L(35, 18)` is the decoded table `caseCodes35T`, checked piece
by piece (one theorem per pair of horizontal margins (ml, mr), so that each kernel computation is
small and the pieces are checked in parallel).  No `native_decide`.
-/

module

public import QueenDom.Main
public import QueenDom.Cases35Data

@[expose] public section

namespace QueenDom

set_option maxRecDepth 100000 in
/-- The 190 pairs `(ml, mr)` with `ml + mr <= 18`. -/
theorem marginPairs_18 : marginPairs 18 = [
    (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11),
    (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (0, 17), (0, 18), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4),
    (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16),
    (1, 17), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10),
    (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (2, 16), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5),
    (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (4, 0), (4, 1),
    (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13),
    (4, 14), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10),
    (5, 11), (5, 12), (5, 13), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8),
    (6, 9), (6, 10), (6, 11), (6, 12), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7),
    (7, 8), (7, 9), (7, 10), (7, 11), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7),
    (8, 8), (8, 9), (8, 10), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8),
    (9, 9), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 0), (11, 1),
    (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5),
    (12, 6), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4),
    (15, 0), (15, 1), (15, 2), (15, 3), (16, 0), (16, 1), (16, 2), (17, 0), (17, 1), (18, 0)
  ] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_0 : casesPQ 35 18 0 0 = (tableCodes caseCodes35T 0 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_1 : casesPQ 35 18 0 1 = (tableCodes caseCodes35T 0 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_2 : casesPQ 35 18 0 2 = (tableCodes caseCodes35T 0 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_3 : casesPQ 35 18 0 3 = (tableCodes caseCodes35T 0 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_4 : casesPQ 35 18 0 4 = (tableCodes caseCodes35T 0 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_5 : casesPQ 35 18 0 5 = (tableCodes caseCodes35T 0 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_6 : casesPQ 35 18 0 6 = (tableCodes caseCodes35T 0 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_7 : casesPQ 35 18 0 7 = (tableCodes caseCodes35T 0 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_8 : casesPQ 35 18 0 8 = (tableCodes caseCodes35T 0 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_9 : casesPQ 35 18 0 9 = (tableCodes caseCodes35T 0 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_10 : casesPQ 35 18 0 10 = (tableCodes caseCodes35T 0 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_11 : casesPQ 35 18 0 11 = (tableCodes caseCodes35T 0 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_12 : casesPQ 35 18 0 12 = (tableCodes caseCodes35T 0 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_13 : casesPQ 35 18 0 13 = (tableCodes caseCodes35T 0 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_14 : casesPQ 35 18 0 14 = (tableCodes caseCodes35T 0 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_15 : casesPQ 35 18 0 15 = (tableCodes caseCodes35T 0 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_16 : casesPQ 35 18 0 16 = (tableCodes caseCodes35T 0 16).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_17 : casesPQ 35 18 0 17 = (tableCodes caseCodes35T 0 17).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_0_18 : casesPQ 35 18 0 18 = (tableCodes caseCodes35T 0 18).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_0 : casesPQ 35 18 1 0 = (tableCodes caseCodes35T 1 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_1 : casesPQ 35 18 1 1 = (tableCodes caseCodes35T 1 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_2 : casesPQ 35 18 1 2 = (tableCodes caseCodes35T 1 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_3 : casesPQ 35 18 1 3 = (tableCodes caseCodes35T 1 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_4 : casesPQ 35 18 1 4 = (tableCodes caseCodes35T 1 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_5 : casesPQ 35 18 1 5 = (tableCodes caseCodes35T 1 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_6 : casesPQ 35 18 1 6 = (tableCodes caseCodes35T 1 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_7 : casesPQ 35 18 1 7 = (tableCodes caseCodes35T 1 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_8 : casesPQ 35 18 1 8 = (tableCodes caseCodes35T 1 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_9 : casesPQ 35 18 1 9 = (tableCodes caseCodes35T 1 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_10 : casesPQ 35 18 1 10 = (tableCodes caseCodes35T 1 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_11 : casesPQ 35 18 1 11 = (tableCodes caseCodes35T 1 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_12 : casesPQ 35 18 1 12 = (tableCodes caseCodes35T 1 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_13 : casesPQ 35 18 1 13 = (tableCodes caseCodes35T 1 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_14 : casesPQ 35 18 1 14 = (tableCodes caseCodes35T 1 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_15 : casesPQ 35 18 1 15 = (tableCodes caseCodes35T 1 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_16 : casesPQ 35 18 1 16 = (tableCodes caseCodes35T 1 16).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_1_17 : casesPQ 35 18 1 17 = (tableCodes caseCodes35T 1 17).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_0 : casesPQ 35 18 2 0 = (tableCodes caseCodes35T 2 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_1 : casesPQ 35 18 2 1 = (tableCodes caseCodes35T 2 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_2 : casesPQ 35 18 2 2 = (tableCodes caseCodes35T 2 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_3 : casesPQ 35 18 2 3 = (tableCodes caseCodes35T 2 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_4 : casesPQ 35 18 2 4 = (tableCodes caseCodes35T 2 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_5 : casesPQ 35 18 2 5 = (tableCodes caseCodes35T 2 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_6 : casesPQ 35 18 2 6 = (tableCodes caseCodes35T 2 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_7 : casesPQ 35 18 2 7 = (tableCodes caseCodes35T 2 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_8 : casesPQ 35 18 2 8 = (tableCodes caseCodes35T 2 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_9 : casesPQ 35 18 2 9 = (tableCodes caseCodes35T 2 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_10 : casesPQ 35 18 2 10 = (tableCodes caseCodes35T 2 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_11 : casesPQ 35 18 2 11 = (tableCodes caseCodes35T 2 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_12 : casesPQ 35 18 2 12 = (tableCodes caseCodes35T 2 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_13 : casesPQ 35 18 2 13 = (tableCodes caseCodes35T 2 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_14 : casesPQ 35 18 2 14 = (tableCodes caseCodes35T 2 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_15 : casesPQ 35 18 2 15 = (tableCodes caseCodes35T 2 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_2_16 : casesPQ 35 18 2 16 = (tableCodes caseCodes35T 2 16).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_0 : casesPQ 35 18 3 0 = (tableCodes caseCodes35T 3 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_1 : casesPQ 35 18 3 1 = (tableCodes caseCodes35T 3 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_2 : casesPQ 35 18 3 2 = (tableCodes caseCodes35T 3 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_3 : casesPQ 35 18 3 3 = (tableCodes caseCodes35T 3 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_4 : casesPQ 35 18 3 4 = (tableCodes caseCodes35T 3 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_5 : casesPQ 35 18 3 5 = (tableCodes caseCodes35T 3 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_6 : casesPQ 35 18 3 6 = (tableCodes caseCodes35T 3 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_7 : casesPQ 35 18 3 7 = (tableCodes caseCodes35T 3 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_8 : casesPQ 35 18 3 8 = (tableCodes caseCodes35T 3 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_9 : casesPQ 35 18 3 9 = (tableCodes caseCodes35T 3 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_10 : casesPQ 35 18 3 10 = (tableCodes caseCodes35T 3 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_11 : casesPQ 35 18 3 11 = (tableCodes caseCodes35T 3 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_12 : casesPQ 35 18 3 12 = (tableCodes caseCodes35T 3 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_13 : casesPQ 35 18 3 13 = (tableCodes caseCodes35T 3 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_14 : casesPQ 35 18 3 14 = (tableCodes caseCodes35T 3 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_3_15 : casesPQ 35 18 3 15 = (tableCodes caseCodes35T 3 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_0 : casesPQ 35 18 4 0 = (tableCodes caseCodes35T 4 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_1 : casesPQ 35 18 4 1 = (tableCodes caseCodes35T 4 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_2 : casesPQ 35 18 4 2 = (tableCodes caseCodes35T 4 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_3 : casesPQ 35 18 4 3 = (tableCodes caseCodes35T 4 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_4 : casesPQ 35 18 4 4 = (tableCodes caseCodes35T 4 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_5 : casesPQ 35 18 4 5 = (tableCodes caseCodes35T 4 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_6 : casesPQ 35 18 4 6 = (tableCodes caseCodes35T 4 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_7 : casesPQ 35 18 4 7 = (tableCodes caseCodes35T 4 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_8 : casesPQ 35 18 4 8 = (tableCodes caseCodes35T 4 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_9 : casesPQ 35 18 4 9 = (tableCodes caseCodes35T 4 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_10 : casesPQ 35 18 4 10 = (tableCodes caseCodes35T 4 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_11 : casesPQ 35 18 4 11 = (tableCodes caseCodes35T 4 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_12 : casesPQ 35 18 4 12 = (tableCodes caseCodes35T 4 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_13 : casesPQ 35 18 4 13 = (tableCodes caseCodes35T 4 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_4_14 : casesPQ 35 18 4 14 = (tableCodes caseCodes35T 4 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_0 : casesPQ 35 18 5 0 = (tableCodes caseCodes35T 5 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_1 : casesPQ 35 18 5 1 = (tableCodes caseCodes35T 5 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_2 : casesPQ 35 18 5 2 = (tableCodes caseCodes35T 5 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_3 : casesPQ 35 18 5 3 = (tableCodes caseCodes35T 5 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_4 : casesPQ 35 18 5 4 = (tableCodes caseCodes35T 5 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_5 : casesPQ 35 18 5 5 = (tableCodes caseCodes35T 5 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_6 : casesPQ 35 18 5 6 = (tableCodes caseCodes35T 5 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_7 : casesPQ 35 18 5 7 = (tableCodes caseCodes35T 5 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_8 : casesPQ 35 18 5 8 = (tableCodes caseCodes35T 5 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_9 : casesPQ 35 18 5 9 = (tableCodes caseCodes35T 5 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_10 : casesPQ 35 18 5 10 = (tableCodes caseCodes35T 5 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_11 : casesPQ 35 18 5 11 = (tableCodes caseCodes35T 5 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_12 : casesPQ 35 18 5 12 = (tableCodes caseCodes35T 5 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_5_13 : casesPQ 35 18 5 13 = (tableCodes caseCodes35T 5 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_6_0 : casesPQ 35 18 6 0 = (tableCodes caseCodes35T 6 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_6_1 : casesPQ 35 18 6 1 = (tableCodes caseCodes35T 6 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_6_2 : casesPQ 35 18 6 2 = (tableCodes caseCodes35T 6 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_6_3 : casesPQ 35 18 6 3 = (tableCodes caseCodes35T 6 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_6_4 : casesPQ 35 18 6 4 = (tableCodes caseCodes35T 6 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_6_5 : casesPQ 35 18 6 5 = (tableCodes caseCodes35T 6 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_6_6 : casesPQ 35 18 6 6 = (tableCodes caseCodes35T 6 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_6_7 : casesPQ 35 18 6 7 = (tableCodes caseCodes35T 6 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_6_8 : casesPQ 35 18 6 8 = (tableCodes caseCodes35T 6 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_6_9 : casesPQ 35 18 6 9 = (tableCodes caseCodes35T 6 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_6_10 : casesPQ 35 18 6 10 = (tableCodes caseCodes35T 6 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_6_11 : casesPQ 35 18 6 11 = (tableCodes caseCodes35T 6 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_6_12 : casesPQ 35 18 6 12 = (tableCodes caseCodes35T 6 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_7_0 : casesPQ 35 18 7 0 = (tableCodes caseCodes35T 7 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_7_1 : casesPQ 35 18 7 1 = (tableCodes caseCodes35T 7 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_7_2 : casesPQ 35 18 7 2 = (tableCodes caseCodes35T 7 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_7_3 : casesPQ 35 18 7 3 = (tableCodes caseCodes35T 7 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_7_4 : casesPQ 35 18 7 4 = (tableCodes caseCodes35T 7 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_7_5 : casesPQ 35 18 7 5 = (tableCodes caseCodes35T 7 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_7_6 : casesPQ 35 18 7 6 = (tableCodes caseCodes35T 7 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_7_7 : casesPQ 35 18 7 7 = (tableCodes caseCodes35T 7 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_7_8 : casesPQ 35 18 7 8 = (tableCodes caseCodes35T 7 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_7_9 : casesPQ 35 18 7 9 = (tableCodes caseCodes35T 7 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_7_10 : casesPQ 35 18 7 10 = (tableCodes caseCodes35T 7 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_7_11 : casesPQ 35 18 7 11 = (tableCodes caseCodes35T 7 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_8_0 : casesPQ 35 18 8 0 = (tableCodes caseCodes35T 8 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_8_1 : casesPQ 35 18 8 1 = (tableCodes caseCodes35T 8 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_8_2 : casesPQ 35 18 8 2 = (tableCodes caseCodes35T 8 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_8_3 : casesPQ 35 18 8 3 = (tableCodes caseCodes35T 8 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_8_4 : casesPQ 35 18 8 4 = (tableCodes caseCodes35T 8 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_8_5 : casesPQ 35 18 8 5 = (tableCodes caseCodes35T 8 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_8_6 : casesPQ 35 18 8 6 = (tableCodes caseCodes35T 8 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_8_7 : casesPQ 35 18 8 7 = (tableCodes caseCodes35T 8 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_8_8 : casesPQ 35 18 8 8 = (tableCodes caseCodes35T 8 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_8_9 : casesPQ 35 18 8 9 = (tableCodes caseCodes35T 8 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_8_10 : casesPQ 35 18 8 10 = (tableCodes caseCodes35T 8 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_9_0 : casesPQ 35 18 9 0 = (tableCodes caseCodes35T 9 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_9_1 : casesPQ 35 18 9 1 = (tableCodes caseCodes35T 9 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_9_2 : casesPQ 35 18 9 2 = (tableCodes caseCodes35T 9 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_9_3 : casesPQ 35 18 9 3 = (tableCodes caseCodes35T 9 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_9_4 : casesPQ 35 18 9 4 = (tableCodes caseCodes35T 9 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_9_5 : casesPQ 35 18 9 5 = (tableCodes caseCodes35T 9 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_9_6 : casesPQ 35 18 9 6 = (tableCodes caseCodes35T 9 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_9_7 : casesPQ 35 18 9 7 = (tableCodes caseCodes35T 9 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_9_8 : casesPQ 35 18 9 8 = (tableCodes caseCodes35T 9 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_9_9 : casesPQ 35 18 9 9 = (tableCodes caseCodes35T 9 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_10_0 : casesPQ 35 18 10 0 = (tableCodes caseCodes35T 10 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_10_1 : casesPQ 35 18 10 1 = (tableCodes caseCodes35T 10 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_10_2 : casesPQ 35 18 10 2 = (tableCodes caseCodes35T 10 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_10_3 : casesPQ 35 18 10 3 = (tableCodes caseCodes35T 10 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_10_4 : casesPQ 35 18 10 4 = (tableCodes caseCodes35T 10 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_10_5 : casesPQ 35 18 10 5 = (tableCodes caseCodes35T 10 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_10_6 : casesPQ 35 18 10 6 = (tableCodes caseCodes35T 10 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_10_7 : casesPQ 35 18 10 7 = (tableCodes caseCodes35T 10 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_10_8 : casesPQ 35 18 10 8 = (tableCodes caseCodes35T 10 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_11_0 : casesPQ 35 18 11 0 = (tableCodes caseCodes35T 11 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_11_1 : casesPQ 35 18 11 1 = (tableCodes caseCodes35T 11 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_11_2 : casesPQ 35 18 11 2 = (tableCodes caseCodes35T 11 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_11_3 : casesPQ 35 18 11 3 = (tableCodes caseCodes35T 11 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_11_4 : casesPQ 35 18 11 4 = (tableCodes caseCodes35T 11 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_11_5 : casesPQ 35 18 11 5 = (tableCodes caseCodes35T 11 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_11_6 : casesPQ 35 18 11 6 = (tableCodes caseCodes35T 11 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_11_7 : casesPQ 35 18 11 7 = (tableCodes caseCodes35T 11 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_12_0 : casesPQ 35 18 12 0 = (tableCodes caseCodes35T 12 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_12_1 : casesPQ 35 18 12 1 = (tableCodes caseCodes35T 12 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_12_2 : casesPQ 35 18 12 2 = (tableCodes caseCodes35T 12 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_12_3 : casesPQ 35 18 12 3 = (tableCodes caseCodes35T 12 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_12_4 : casesPQ 35 18 12 4 = (tableCodes caseCodes35T 12 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_12_5 : casesPQ 35 18 12 5 = (tableCodes caseCodes35T 12 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_12_6 : casesPQ 35 18 12 6 = (tableCodes caseCodes35T 12 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_13_0 : casesPQ 35 18 13 0 = (tableCodes caseCodes35T 13 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_13_1 : casesPQ 35 18 13 1 = (tableCodes caseCodes35T 13 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_13_2 : casesPQ 35 18 13 2 = (tableCodes caseCodes35T 13 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_13_3 : casesPQ 35 18 13 3 = (tableCodes caseCodes35T 13 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_13_4 : casesPQ 35 18 13 4 = (tableCodes caseCodes35T 13 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_13_5 : casesPQ 35 18 13 5 = (tableCodes caseCodes35T 13 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_14_0 : casesPQ 35 18 14 0 = (tableCodes caseCodes35T 14 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_14_1 : casesPQ 35 18 14 1 = (tableCodes caseCodes35T 14 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_14_2 : casesPQ 35 18 14 2 = (tableCodes caseCodes35T 14 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_14_3 : casesPQ 35 18 14 3 = (tableCodes caseCodes35T 14 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_14_4 : casesPQ 35 18 14 4 = (tableCodes caseCodes35T 14 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_15_0 : casesPQ 35 18 15 0 = (tableCodes caseCodes35T 15 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_15_1 : casesPQ 35 18 15 1 = (tableCodes caseCodes35T 15 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_15_2 : casesPQ 35 18 15 2 = (tableCodes caseCodes35T 15 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_15_3 : casesPQ 35 18 15 3 = (tableCodes caseCodes35T 15 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_16_0 : casesPQ 35 18 16 0 = (tableCodes caseCodes35T 16 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_16_1 : casesPQ 35 18 16 1 = (tableCodes caseCodes35T 16 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_16_2 : casesPQ 35 18 16 2 = (tableCodes caseCodes35T 16 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_17_0 : casesPQ 35 18 17 0 = (tableCodes caseCodes35T 17 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_17_1 : casesPQ 35 18 17 1 = (tableCodes caseCodes35T 17 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece35_18_0 : casesPQ 35 18 18 0 = (tableCodes caseCodes35T 18 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The case list `L(35, 18)` is the decoded table of the run** (assembled from the pieces). -/
theorem enumCases_35_18_table : enumCases 35 18 = (tableList 18 caseCodes35T).map Case.ofCode := by
  refine enumCases_eq_table ?_
  rw [marginPairs_18]
  exact List.forall_mem_cons.2 ⟨piece35_0_0,
    List.forall_mem_cons.2 ⟨piece35_0_1,
    List.forall_mem_cons.2 ⟨piece35_0_2,
    List.forall_mem_cons.2 ⟨piece35_0_3,
    List.forall_mem_cons.2 ⟨piece35_0_4,
    List.forall_mem_cons.2 ⟨piece35_0_5,
    List.forall_mem_cons.2 ⟨piece35_0_6,
    List.forall_mem_cons.2 ⟨piece35_0_7,
    List.forall_mem_cons.2 ⟨piece35_0_8,
    List.forall_mem_cons.2 ⟨piece35_0_9,
    List.forall_mem_cons.2 ⟨piece35_0_10,
    List.forall_mem_cons.2 ⟨piece35_0_11,
    List.forall_mem_cons.2 ⟨piece35_0_12,
    List.forall_mem_cons.2 ⟨piece35_0_13,
    List.forall_mem_cons.2 ⟨piece35_0_14,
    List.forall_mem_cons.2 ⟨piece35_0_15,
    List.forall_mem_cons.2 ⟨piece35_0_16,
    List.forall_mem_cons.2 ⟨piece35_0_17,
    List.forall_mem_cons.2 ⟨piece35_0_18,
    List.forall_mem_cons.2 ⟨piece35_1_0,
    List.forall_mem_cons.2 ⟨piece35_1_1,
    List.forall_mem_cons.2 ⟨piece35_1_2,
    List.forall_mem_cons.2 ⟨piece35_1_3,
    List.forall_mem_cons.2 ⟨piece35_1_4,
    List.forall_mem_cons.2 ⟨piece35_1_5,
    List.forall_mem_cons.2 ⟨piece35_1_6,
    List.forall_mem_cons.2 ⟨piece35_1_7,
    List.forall_mem_cons.2 ⟨piece35_1_8,
    List.forall_mem_cons.2 ⟨piece35_1_9,
    List.forall_mem_cons.2 ⟨piece35_1_10,
    List.forall_mem_cons.2 ⟨piece35_1_11,
    List.forall_mem_cons.2 ⟨piece35_1_12,
    List.forall_mem_cons.2 ⟨piece35_1_13,
    List.forall_mem_cons.2 ⟨piece35_1_14,
    List.forall_mem_cons.2 ⟨piece35_1_15,
    List.forall_mem_cons.2 ⟨piece35_1_16,
    List.forall_mem_cons.2 ⟨piece35_1_17,
    List.forall_mem_cons.2 ⟨piece35_2_0,
    List.forall_mem_cons.2 ⟨piece35_2_1,
    List.forall_mem_cons.2 ⟨piece35_2_2,
    List.forall_mem_cons.2 ⟨piece35_2_3,
    List.forall_mem_cons.2 ⟨piece35_2_4,
    List.forall_mem_cons.2 ⟨piece35_2_5,
    List.forall_mem_cons.2 ⟨piece35_2_6,
    List.forall_mem_cons.2 ⟨piece35_2_7,
    List.forall_mem_cons.2 ⟨piece35_2_8,
    List.forall_mem_cons.2 ⟨piece35_2_9,
    List.forall_mem_cons.2 ⟨piece35_2_10,
    List.forall_mem_cons.2 ⟨piece35_2_11,
    List.forall_mem_cons.2 ⟨piece35_2_12,
    List.forall_mem_cons.2 ⟨piece35_2_13,
    List.forall_mem_cons.2 ⟨piece35_2_14,
    List.forall_mem_cons.2 ⟨piece35_2_15,
    List.forall_mem_cons.2 ⟨piece35_2_16,
    List.forall_mem_cons.2 ⟨piece35_3_0,
    List.forall_mem_cons.2 ⟨piece35_3_1,
    List.forall_mem_cons.2 ⟨piece35_3_2,
    List.forall_mem_cons.2 ⟨piece35_3_3,
    List.forall_mem_cons.2 ⟨piece35_3_4,
    List.forall_mem_cons.2 ⟨piece35_3_5,
    List.forall_mem_cons.2 ⟨piece35_3_6,
    List.forall_mem_cons.2 ⟨piece35_3_7,
    List.forall_mem_cons.2 ⟨piece35_3_8,
    List.forall_mem_cons.2 ⟨piece35_3_9,
    List.forall_mem_cons.2 ⟨piece35_3_10,
    List.forall_mem_cons.2 ⟨piece35_3_11,
    List.forall_mem_cons.2 ⟨piece35_3_12,
    List.forall_mem_cons.2 ⟨piece35_3_13,
    List.forall_mem_cons.2 ⟨piece35_3_14,
    List.forall_mem_cons.2 ⟨piece35_3_15,
    List.forall_mem_cons.2 ⟨piece35_4_0,
    List.forall_mem_cons.2 ⟨piece35_4_1,
    List.forall_mem_cons.2 ⟨piece35_4_2,
    List.forall_mem_cons.2 ⟨piece35_4_3,
    List.forall_mem_cons.2 ⟨piece35_4_4,
    List.forall_mem_cons.2 ⟨piece35_4_5,
    List.forall_mem_cons.2 ⟨piece35_4_6,
    List.forall_mem_cons.2 ⟨piece35_4_7,
    List.forall_mem_cons.2 ⟨piece35_4_8,
    List.forall_mem_cons.2 ⟨piece35_4_9,
    List.forall_mem_cons.2 ⟨piece35_4_10,
    List.forall_mem_cons.2 ⟨piece35_4_11,
    List.forall_mem_cons.2 ⟨piece35_4_12,
    List.forall_mem_cons.2 ⟨piece35_4_13,
    List.forall_mem_cons.2 ⟨piece35_4_14,
    List.forall_mem_cons.2 ⟨piece35_5_0,
    List.forall_mem_cons.2 ⟨piece35_5_1,
    List.forall_mem_cons.2 ⟨piece35_5_2,
    List.forall_mem_cons.2 ⟨piece35_5_3,
    List.forall_mem_cons.2 ⟨piece35_5_4,
    List.forall_mem_cons.2 ⟨piece35_5_5,
    List.forall_mem_cons.2 ⟨piece35_5_6,
    List.forall_mem_cons.2 ⟨piece35_5_7,
    List.forall_mem_cons.2 ⟨piece35_5_8,
    List.forall_mem_cons.2 ⟨piece35_5_9,
    List.forall_mem_cons.2 ⟨piece35_5_10,
    List.forall_mem_cons.2 ⟨piece35_5_11,
    List.forall_mem_cons.2 ⟨piece35_5_12,
    List.forall_mem_cons.2 ⟨piece35_5_13,
    List.forall_mem_cons.2 ⟨piece35_6_0,
    List.forall_mem_cons.2 ⟨piece35_6_1,
    List.forall_mem_cons.2 ⟨piece35_6_2,
    List.forall_mem_cons.2 ⟨piece35_6_3,
    List.forall_mem_cons.2 ⟨piece35_6_4,
    List.forall_mem_cons.2 ⟨piece35_6_5,
    List.forall_mem_cons.2 ⟨piece35_6_6,
    List.forall_mem_cons.2 ⟨piece35_6_7,
    List.forall_mem_cons.2 ⟨piece35_6_8,
    List.forall_mem_cons.2 ⟨piece35_6_9,
    List.forall_mem_cons.2 ⟨piece35_6_10,
    List.forall_mem_cons.2 ⟨piece35_6_11,
    List.forall_mem_cons.2 ⟨piece35_6_12,
    List.forall_mem_cons.2 ⟨piece35_7_0,
    List.forall_mem_cons.2 ⟨piece35_7_1,
    List.forall_mem_cons.2 ⟨piece35_7_2,
    List.forall_mem_cons.2 ⟨piece35_7_3,
    List.forall_mem_cons.2 ⟨piece35_7_4,
    List.forall_mem_cons.2 ⟨piece35_7_5,
    List.forall_mem_cons.2 ⟨piece35_7_6,
    List.forall_mem_cons.2 ⟨piece35_7_7,
    List.forall_mem_cons.2 ⟨piece35_7_8,
    List.forall_mem_cons.2 ⟨piece35_7_9,
    List.forall_mem_cons.2 ⟨piece35_7_10,
    List.forall_mem_cons.2 ⟨piece35_7_11,
    List.forall_mem_cons.2 ⟨piece35_8_0,
    List.forall_mem_cons.2 ⟨piece35_8_1,
    List.forall_mem_cons.2 ⟨piece35_8_2,
    List.forall_mem_cons.2 ⟨piece35_8_3,
    List.forall_mem_cons.2 ⟨piece35_8_4,
    List.forall_mem_cons.2 ⟨piece35_8_5,
    List.forall_mem_cons.2 ⟨piece35_8_6,
    List.forall_mem_cons.2 ⟨piece35_8_7,
    List.forall_mem_cons.2 ⟨piece35_8_8,
    List.forall_mem_cons.2 ⟨piece35_8_9,
    List.forall_mem_cons.2 ⟨piece35_8_10,
    List.forall_mem_cons.2 ⟨piece35_9_0,
    List.forall_mem_cons.2 ⟨piece35_9_1,
    List.forall_mem_cons.2 ⟨piece35_9_2,
    List.forall_mem_cons.2 ⟨piece35_9_3,
    List.forall_mem_cons.2 ⟨piece35_9_4,
    List.forall_mem_cons.2 ⟨piece35_9_5,
    List.forall_mem_cons.2 ⟨piece35_9_6,
    List.forall_mem_cons.2 ⟨piece35_9_7,
    List.forall_mem_cons.2 ⟨piece35_9_8,
    List.forall_mem_cons.2 ⟨piece35_9_9,
    List.forall_mem_cons.2 ⟨piece35_10_0,
    List.forall_mem_cons.2 ⟨piece35_10_1,
    List.forall_mem_cons.2 ⟨piece35_10_2,
    List.forall_mem_cons.2 ⟨piece35_10_3,
    List.forall_mem_cons.2 ⟨piece35_10_4,
    List.forall_mem_cons.2 ⟨piece35_10_5,
    List.forall_mem_cons.2 ⟨piece35_10_6,
    List.forall_mem_cons.2 ⟨piece35_10_7,
    List.forall_mem_cons.2 ⟨piece35_10_8,
    List.forall_mem_cons.2 ⟨piece35_11_0,
    List.forall_mem_cons.2 ⟨piece35_11_1,
    List.forall_mem_cons.2 ⟨piece35_11_2,
    List.forall_mem_cons.2 ⟨piece35_11_3,
    List.forall_mem_cons.2 ⟨piece35_11_4,
    List.forall_mem_cons.2 ⟨piece35_11_5,
    List.forall_mem_cons.2 ⟨piece35_11_6,
    List.forall_mem_cons.2 ⟨piece35_11_7,
    List.forall_mem_cons.2 ⟨piece35_12_0,
    List.forall_mem_cons.2 ⟨piece35_12_1,
    List.forall_mem_cons.2 ⟨piece35_12_2,
    List.forall_mem_cons.2 ⟨piece35_12_3,
    List.forall_mem_cons.2 ⟨piece35_12_4,
    List.forall_mem_cons.2 ⟨piece35_12_5,
    List.forall_mem_cons.2 ⟨piece35_12_6,
    List.forall_mem_cons.2 ⟨piece35_13_0,
    List.forall_mem_cons.2 ⟨piece35_13_1,
    List.forall_mem_cons.2 ⟨piece35_13_2,
    List.forall_mem_cons.2 ⟨piece35_13_3,
    List.forall_mem_cons.2 ⟨piece35_13_4,
    List.forall_mem_cons.2 ⟨piece35_13_5,
    List.forall_mem_cons.2 ⟨piece35_14_0,
    List.forall_mem_cons.2 ⟨piece35_14_1,
    List.forall_mem_cons.2 ⟨piece35_14_2,
    List.forall_mem_cons.2 ⟨piece35_14_3,
    List.forall_mem_cons.2 ⟨piece35_14_4,
    List.forall_mem_cons.2 ⟨piece35_15_0,
    List.forall_mem_cons.2 ⟨piece35_15_1,
    List.forall_mem_cons.2 ⟨piece35_15_2,
    List.forall_mem_cons.2 ⟨piece35_15_3,
    List.forall_mem_cons.2 ⟨piece35_16_0,
    List.forall_mem_cons.2 ⟨piece35_16_1,
    List.forall_mem_cons.2 ⟨piece35_16_2,
    List.forall_mem_cons.2 ⟨piece35_17_0,
    List.forall_mem_cons.2 ⟨piece35_17_1,
    List.forall_mem_cons.2 ⟨piece35_18_0,
    List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end QueenDom
