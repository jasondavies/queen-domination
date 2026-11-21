/-
GENERATED FILE -- do not edit.  Produced by scripts/gen_cases.py from the run logs
  frame/out/d_32_16.jsonl        ( 11466 records, sha256 749888e97da7ac831b9abd2b7d7000dbadb6f684880239c7496eddc4883e9bc5)
of the referee's frame-method run for n = 32, k = 16: 11466 cases, 3321 frames;
11466 refuted by a plain record (UNSAT, drat-trim VERIFIED), 0 by verified cube records of run_hard.py.
Kernel computations: the case list `L(32, 16)` is the decoded table `caseCodes32T`, checked piece
by piece (one theorem per pair of horizontal margins (ml, mr), so that each kernel computation is
small and the pieces are checked in parallel).  No `native_decide`.
-/

module

public import QueenDom.Main
public import QueenDom.Cases32Data

@[expose] public section

namespace QueenDom

set_option maxRecDepth 100000 in
/-- The 153 pairs `(ml, mr)` with `ml + mr <= 16`. -/
theorem marginPairs_16 : marginPairs 16 = [
    (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11),
    (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
    (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (2, 0), (2, 1), (2, 2),
    (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14),
    (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11),
    (3, 12), (3, 13), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9),
    (4, 10), (4, 11), (4, 12), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8),
    (5, 9), (5, 10), (5, 11), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8),
    (6, 9), (6, 10), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9),
    (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 0), (9, 1), (9, 2),
    (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6),
    (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, 0),
    (13, 1), (13, 2), (13, 3), (14, 0), (14, 1), (14, 2), (15, 0), (15, 1), (16, 0)
  ] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_0 : casesPQ 32 16 0 0 = (tableCodes caseCodes32T 0 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_1 : casesPQ 32 16 0 1 = (tableCodes caseCodes32T 0 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_2 : casesPQ 32 16 0 2 = (tableCodes caseCodes32T 0 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_3 : casesPQ 32 16 0 3 = (tableCodes caseCodes32T 0 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_4 : casesPQ 32 16 0 4 = (tableCodes caseCodes32T 0 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_5 : casesPQ 32 16 0 5 = (tableCodes caseCodes32T 0 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_6 : casesPQ 32 16 0 6 = (tableCodes caseCodes32T 0 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_7 : casesPQ 32 16 0 7 = (tableCodes caseCodes32T 0 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_8 : casesPQ 32 16 0 8 = (tableCodes caseCodes32T 0 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_9 : casesPQ 32 16 0 9 = (tableCodes caseCodes32T 0 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_10 : casesPQ 32 16 0 10 = (tableCodes caseCodes32T 0 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_11 : casesPQ 32 16 0 11 = (tableCodes caseCodes32T 0 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_12 : casesPQ 32 16 0 12 = (tableCodes caseCodes32T 0 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_13 : casesPQ 32 16 0 13 = (tableCodes caseCodes32T 0 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_14 : casesPQ 32 16 0 14 = (tableCodes caseCodes32T 0 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_15 : casesPQ 32 16 0 15 = (tableCodes caseCodes32T 0 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_0_16 : casesPQ 32 16 0 16 = (tableCodes caseCodes32T 0 16).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_0 : casesPQ 32 16 1 0 = (tableCodes caseCodes32T 1 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_1 : casesPQ 32 16 1 1 = (tableCodes caseCodes32T 1 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_2 : casesPQ 32 16 1 2 = (tableCodes caseCodes32T 1 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_3 : casesPQ 32 16 1 3 = (tableCodes caseCodes32T 1 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_4 : casesPQ 32 16 1 4 = (tableCodes caseCodes32T 1 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_5 : casesPQ 32 16 1 5 = (tableCodes caseCodes32T 1 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_6 : casesPQ 32 16 1 6 = (tableCodes caseCodes32T 1 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_7 : casesPQ 32 16 1 7 = (tableCodes caseCodes32T 1 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_8 : casesPQ 32 16 1 8 = (tableCodes caseCodes32T 1 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_9 : casesPQ 32 16 1 9 = (tableCodes caseCodes32T 1 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_10 : casesPQ 32 16 1 10 = (tableCodes caseCodes32T 1 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_11 : casesPQ 32 16 1 11 = (tableCodes caseCodes32T 1 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_12 : casesPQ 32 16 1 12 = (tableCodes caseCodes32T 1 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_13 : casesPQ 32 16 1 13 = (tableCodes caseCodes32T 1 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_14 : casesPQ 32 16 1 14 = (tableCodes caseCodes32T 1 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_1_15 : casesPQ 32 16 1 15 = (tableCodes caseCodes32T 1 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_0 : casesPQ 32 16 2 0 = (tableCodes caseCodes32T 2 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_1 : casesPQ 32 16 2 1 = (tableCodes caseCodes32T 2 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_2 : casesPQ 32 16 2 2 = (tableCodes caseCodes32T 2 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_3 : casesPQ 32 16 2 3 = (tableCodes caseCodes32T 2 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_4 : casesPQ 32 16 2 4 = (tableCodes caseCodes32T 2 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_5 : casesPQ 32 16 2 5 = (tableCodes caseCodes32T 2 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_6 : casesPQ 32 16 2 6 = (tableCodes caseCodes32T 2 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_7 : casesPQ 32 16 2 7 = (tableCodes caseCodes32T 2 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_8 : casesPQ 32 16 2 8 = (tableCodes caseCodes32T 2 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_9 : casesPQ 32 16 2 9 = (tableCodes caseCodes32T 2 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_10 : casesPQ 32 16 2 10 = (tableCodes caseCodes32T 2 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_11 : casesPQ 32 16 2 11 = (tableCodes caseCodes32T 2 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_12 : casesPQ 32 16 2 12 = (tableCodes caseCodes32T 2 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_13 : casesPQ 32 16 2 13 = (tableCodes caseCodes32T 2 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_2_14 : casesPQ 32 16 2 14 = (tableCodes caseCodes32T 2 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_0 : casesPQ 32 16 3 0 = (tableCodes caseCodes32T 3 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_1 : casesPQ 32 16 3 1 = (tableCodes caseCodes32T 3 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_2 : casesPQ 32 16 3 2 = (tableCodes caseCodes32T 3 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_3 : casesPQ 32 16 3 3 = (tableCodes caseCodes32T 3 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_4 : casesPQ 32 16 3 4 = (tableCodes caseCodes32T 3 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_5 : casesPQ 32 16 3 5 = (tableCodes caseCodes32T 3 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_6 : casesPQ 32 16 3 6 = (tableCodes caseCodes32T 3 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_7 : casesPQ 32 16 3 7 = (tableCodes caseCodes32T 3 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_8 : casesPQ 32 16 3 8 = (tableCodes caseCodes32T 3 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_9 : casesPQ 32 16 3 9 = (tableCodes caseCodes32T 3 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_10 : casesPQ 32 16 3 10 = (tableCodes caseCodes32T 3 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_11 : casesPQ 32 16 3 11 = (tableCodes caseCodes32T 3 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_12 : casesPQ 32 16 3 12 = (tableCodes caseCodes32T 3 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_3_13 : casesPQ 32 16 3 13 = (tableCodes caseCodes32T 3 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_4_0 : casesPQ 32 16 4 0 = (tableCodes caseCodes32T 4 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_4_1 : casesPQ 32 16 4 1 = (tableCodes caseCodes32T 4 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_4_2 : casesPQ 32 16 4 2 = (tableCodes caseCodes32T 4 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_4_3 : casesPQ 32 16 4 3 = (tableCodes caseCodes32T 4 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_4_4 : casesPQ 32 16 4 4 = (tableCodes caseCodes32T 4 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_4_5 : casesPQ 32 16 4 5 = (tableCodes caseCodes32T 4 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_4_6 : casesPQ 32 16 4 6 = (tableCodes caseCodes32T 4 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_4_7 : casesPQ 32 16 4 7 = (tableCodes caseCodes32T 4 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_4_8 : casesPQ 32 16 4 8 = (tableCodes caseCodes32T 4 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_4_9 : casesPQ 32 16 4 9 = (tableCodes caseCodes32T 4 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_4_10 : casesPQ 32 16 4 10 = (tableCodes caseCodes32T 4 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_4_11 : casesPQ 32 16 4 11 = (tableCodes caseCodes32T 4 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_4_12 : casesPQ 32 16 4 12 = (tableCodes caseCodes32T 4 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_5_0 : casesPQ 32 16 5 0 = (tableCodes caseCodes32T 5 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_5_1 : casesPQ 32 16 5 1 = (tableCodes caseCodes32T 5 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_5_2 : casesPQ 32 16 5 2 = (tableCodes caseCodes32T 5 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_5_3 : casesPQ 32 16 5 3 = (tableCodes caseCodes32T 5 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_5_4 : casesPQ 32 16 5 4 = (tableCodes caseCodes32T 5 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_5_5 : casesPQ 32 16 5 5 = (tableCodes caseCodes32T 5 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_5_6 : casesPQ 32 16 5 6 = (tableCodes caseCodes32T 5 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_5_7 : casesPQ 32 16 5 7 = (tableCodes caseCodes32T 5 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_5_8 : casesPQ 32 16 5 8 = (tableCodes caseCodes32T 5 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_5_9 : casesPQ 32 16 5 9 = (tableCodes caseCodes32T 5 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_5_10 : casesPQ 32 16 5 10 = (tableCodes caseCodes32T 5 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_5_11 : casesPQ 32 16 5 11 = (tableCodes caseCodes32T 5 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_6_0 : casesPQ 32 16 6 0 = (tableCodes caseCodes32T 6 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_6_1 : casesPQ 32 16 6 1 = (tableCodes caseCodes32T 6 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_6_2 : casesPQ 32 16 6 2 = (tableCodes caseCodes32T 6 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_6_3 : casesPQ 32 16 6 3 = (tableCodes caseCodes32T 6 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_6_4 : casesPQ 32 16 6 4 = (tableCodes caseCodes32T 6 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_6_5 : casesPQ 32 16 6 5 = (tableCodes caseCodes32T 6 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_6_6 : casesPQ 32 16 6 6 = (tableCodes caseCodes32T 6 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_6_7 : casesPQ 32 16 6 7 = (tableCodes caseCodes32T 6 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_6_8 : casesPQ 32 16 6 8 = (tableCodes caseCodes32T 6 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_6_9 : casesPQ 32 16 6 9 = (tableCodes caseCodes32T 6 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_6_10 : casesPQ 32 16 6 10 = (tableCodes caseCodes32T 6 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_7_0 : casesPQ 32 16 7 0 = (tableCodes caseCodes32T 7 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_7_1 : casesPQ 32 16 7 1 = (tableCodes caseCodes32T 7 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_7_2 : casesPQ 32 16 7 2 = (tableCodes caseCodes32T 7 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_7_3 : casesPQ 32 16 7 3 = (tableCodes caseCodes32T 7 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_7_4 : casesPQ 32 16 7 4 = (tableCodes caseCodes32T 7 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_7_5 : casesPQ 32 16 7 5 = (tableCodes caseCodes32T 7 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_7_6 : casesPQ 32 16 7 6 = (tableCodes caseCodes32T 7 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_7_7 : casesPQ 32 16 7 7 = (tableCodes caseCodes32T 7 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_7_8 : casesPQ 32 16 7 8 = (tableCodes caseCodes32T 7 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_7_9 : casesPQ 32 16 7 9 = (tableCodes caseCodes32T 7 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_8_0 : casesPQ 32 16 8 0 = (tableCodes caseCodes32T 8 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_8_1 : casesPQ 32 16 8 1 = (tableCodes caseCodes32T 8 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_8_2 : casesPQ 32 16 8 2 = (tableCodes caseCodes32T 8 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_8_3 : casesPQ 32 16 8 3 = (tableCodes caseCodes32T 8 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_8_4 : casesPQ 32 16 8 4 = (tableCodes caseCodes32T 8 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_8_5 : casesPQ 32 16 8 5 = (tableCodes caseCodes32T 8 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_8_6 : casesPQ 32 16 8 6 = (tableCodes caseCodes32T 8 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_8_7 : casesPQ 32 16 8 7 = (tableCodes caseCodes32T 8 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_8_8 : casesPQ 32 16 8 8 = (tableCodes caseCodes32T 8 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_9_0 : casesPQ 32 16 9 0 = (tableCodes caseCodes32T 9 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_9_1 : casesPQ 32 16 9 1 = (tableCodes caseCodes32T 9 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_9_2 : casesPQ 32 16 9 2 = (tableCodes caseCodes32T 9 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_9_3 : casesPQ 32 16 9 3 = (tableCodes caseCodes32T 9 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_9_4 : casesPQ 32 16 9 4 = (tableCodes caseCodes32T 9 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_9_5 : casesPQ 32 16 9 5 = (tableCodes caseCodes32T 9 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_9_6 : casesPQ 32 16 9 6 = (tableCodes caseCodes32T 9 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_9_7 : casesPQ 32 16 9 7 = (tableCodes caseCodes32T 9 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_10_0 : casesPQ 32 16 10 0 = (tableCodes caseCodes32T 10 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_10_1 : casesPQ 32 16 10 1 = (tableCodes caseCodes32T 10 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_10_2 : casesPQ 32 16 10 2 = (tableCodes caseCodes32T 10 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_10_3 : casesPQ 32 16 10 3 = (tableCodes caseCodes32T 10 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_10_4 : casesPQ 32 16 10 4 = (tableCodes caseCodes32T 10 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_10_5 : casesPQ 32 16 10 5 = (tableCodes caseCodes32T 10 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_10_6 : casesPQ 32 16 10 6 = (tableCodes caseCodes32T 10 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_11_0 : casesPQ 32 16 11 0 = (tableCodes caseCodes32T 11 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_11_1 : casesPQ 32 16 11 1 = (tableCodes caseCodes32T 11 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_11_2 : casesPQ 32 16 11 2 = (tableCodes caseCodes32T 11 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_11_3 : casesPQ 32 16 11 3 = (tableCodes caseCodes32T 11 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_11_4 : casesPQ 32 16 11 4 = (tableCodes caseCodes32T 11 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_11_5 : casesPQ 32 16 11 5 = (tableCodes caseCodes32T 11 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_12_0 : casesPQ 32 16 12 0 = (tableCodes caseCodes32T 12 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_12_1 : casesPQ 32 16 12 1 = (tableCodes caseCodes32T 12 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_12_2 : casesPQ 32 16 12 2 = (tableCodes caseCodes32T 12 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_12_3 : casesPQ 32 16 12 3 = (tableCodes caseCodes32T 12 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_12_4 : casesPQ 32 16 12 4 = (tableCodes caseCodes32T 12 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_13_0 : casesPQ 32 16 13 0 = (tableCodes caseCodes32T 13 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_13_1 : casesPQ 32 16 13 1 = (tableCodes caseCodes32T 13 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_13_2 : casesPQ 32 16 13 2 = (tableCodes caseCodes32T 13 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_13_3 : casesPQ 32 16 13 3 = (tableCodes caseCodes32T 13 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_14_0 : casesPQ 32 16 14 0 = (tableCodes caseCodes32T 14 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_14_1 : casesPQ 32 16 14 1 = (tableCodes caseCodes32T 14 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_14_2 : casesPQ 32 16 14 2 = (tableCodes caseCodes32T 14 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_15_0 : casesPQ 32 16 15 0 = (tableCodes caseCodes32T 15 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_15_1 : casesPQ 32 16 15 1 = (tableCodes caseCodes32T 15 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece32_16_0 : casesPQ 32 16 16 0 = (tableCodes caseCodes32T 16 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The case list `L(32, 16)` is the decoded table of the run** (assembled from the pieces). -/
theorem enumCases_32_16_table : enumCases 32 16 = (tableList 16 caseCodes32T).map Case.ofCode := by
  refine enumCases_eq_table ?_
  rw [marginPairs_16]
  exact List.forall_mem_cons.2 ⟨piece32_0_0,
    List.forall_mem_cons.2 ⟨piece32_0_1,
    List.forall_mem_cons.2 ⟨piece32_0_2,
    List.forall_mem_cons.2 ⟨piece32_0_3,
    List.forall_mem_cons.2 ⟨piece32_0_4,
    List.forall_mem_cons.2 ⟨piece32_0_5,
    List.forall_mem_cons.2 ⟨piece32_0_6,
    List.forall_mem_cons.2 ⟨piece32_0_7,
    List.forall_mem_cons.2 ⟨piece32_0_8,
    List.forall_mem_cons.2 ⟨piece32_0_9,
    List.forall_mem_cons.2 ⟨piece32_0_10,
    List.forall_mem_cons.2 ⟨piece32_0_11,
    List.forall_mem_cons.2 ⟨piece32_0_12,
    List.forall_mem_cons.2 ⟨piece32_0_13,
    List.forall_mem_cons.2 ⟨piece32_0_14,
    List.forall_mem_cons.2 ⟨piece32_0_15,
    List.forall_mem_cons.2 ⟨piece32_0_16,
    List.forall_mem_cons.2 ⟨piece32_1_0,
    List.forall_mem_cons.2 ⟨piece32_1_1,
    List.forall_mem_cons.2 ⟨piece32_1_2,
    List.forall_mem_cons.2 ⟨piece32_1_3,
    List.forall_mem_cons.2 ⟨piece32_1_4,
    List.forall_mem_cons.2 ⟨piece32_1_5,
    List.forall_mem_cons.2 ⟨piece32_1_6,
    List.forall_mem_cons.2 ⟨piece32_1_7,
    List.forall_mem_cons.2 ⟨piece32_1_8,
    List.forall_mem_cons.2 ⟨piece32_1_9,
    List.forall_mem_cons.2 ⟨piece32_1_10,
    List.forall_mem_cons.2 ⟨piece32_1_11,
    List.forall_mem_cons.2 ⟨piece32_1_12,
    List.forall_mem_cons.2 ⟨piece32_1_13,
    List.forall_mem_cons.2 ⟨piece32_1_14,
    List.forall_mem_cons.2 ⟨piece32_1_15,
    List.forall_mem_cons.2 ⟨piece32_2_0,
    List.forall_mem_cons.2 ⟨piece32_2_1,
    List.forall_mem_cons.2 ⟨piece32_2_2,
    List.forall_mem_cons.2 ⟨piece32_2_3,
    List.forall_mem_cons.2 ⟨piece32_2_4,
    List.forall_mem_cons.2 ⟨piece32_2_5,
    List.forall_mem_cons.2 ⟨piece32_2_6,
    List.forall_mem_cons.2 ⟨piece32_2_7,
    List.forall_mem_cons.2 ⟨piece32_2_8,
    List.forall_mem_cons.2 ⟨piece32_2_9,
    List.forall_mem_cons.2 ⟨piece32_2_10,
    List.forall_mem_cons.2 ⟨piece32_2_11,
    List.forall_mem_cons.2 ⟨piece32_2_12,
    List.forall_mem_cons.2 ⟨piece32_2_13,
    List.forall_mem_cons.2 ⟨piece32_2_14,
    List.forall_mem_cons.2 ⟨piece32_3_0,
    List.forall_mem_cons.2 ⟨piece32_3_1,
    List.forall_mem_cons.2 ⟨piece32_3_2,
    List.forall_mem_cons.2 ⟨piece32_3_3,
    List.forall_mem_cons.2 ⟨piece32_3_4,
    List.forall_mem_cons.2 ⟨piece32_3_5,
    List.forall_mem_cons.2 ⟨piece32_3_6,
    List.forall_mem_cons.2 ⟨piece32_3_7,
    List.forall_mem_cons.2 ⟨piece32_3_8,
    List.forall_mem_cons.2 ⟨piece32_3_9,
    List.forall_mem_cons.2 ⟨piece32_3_10,
    List.forall_mem_cons.2 ⟨piece32_3_11,
    List.forall_mem_cons.2 ⟨piece32_3_12,
    List.forall_mem_cons.2 ⟨piece32_3_13,
    List.forall_mem_cons.2 ⟨piece32_4_0,
    List.forall_mem_cons.2 ⟨piece32_4_1,
    List.forall_mem_cons.2 ⟨piece32_4_2,
    List.forall_mem_cons.2 ⟨piece32_4_3,
    List.forall_mem_cons.2 ⟨piece32_4_4,
    List.forall_mem_cons.2 ⟨piece32_4_5,
    List.forall_mem_cons.2 ⟨piece32_4_6,
    List.forall_mem_cons.2 ⟨piece32_4_7,
    List.forall_mem_cons.2 ⟨piece32_4_8,
    List.forall_mem_cons.2 ⟨piece32_4_9,
    List.forall_mem_cons.2 ⟨piece32_4_10,
    List.forall_mem_cons.2 ⟨piece32_4_11,
    List.forall_mem_cons.2 ⟨piece32_4_12,
    List.forall_mem_cons.2 ⟨piece32_5_0,
    List.forall_mem_cons.2 ⟨piece32_5_1,
    List.forall_mem_cons.2 ⟨piece32_5_2,
    List.forall_mem_cons.2 ⟨piece32_5_3,
    List.forall_mem_cons.2 ⟨piece32_5_4,
    List.forall_mem_cons.2 ⟨piece32_5_5,
    List.forall_mem_cons.2 ⟨piece32_5_6,
    List.forall_mem_cons.2 ⟨piece32_5_7,
    List.forall_mem_cons.2 ⟨piece32_5_8,
    List.forall_mem_cons.2 ⟨piece32_5_9,
    List.forall_mem_cons.2 ⟨piece32_5_10,
    List.forall_mem_cons.2 ⟨piece32_5_11,
    List.forall_mem_cons.2 ⟨piece32_6_0,
    List.forall_mem_cons.2 ⟨piece32_6_1,
    List.forall_mem_cons.2 ⟨piece32_6_2,
    List.forall_mem_cons.2 ⟨piece32_6_3,
    List.forall_mem_cons.2 ⟨piece32_6_4,
    List.forall_mem_cons.2 ⟨piece32_6_5,
    List.forall_mem_cons.2 ⟨piece32_6_6,
    List.forall_mem_cons.2 ⟨piece32_6_7,
    List.forall_mem_cons.2 ⟨piece32_6_8,
    List.forall_mem_cons.2 ⟨piece32_6_9,
    List.forall_mem_cons.2 ⟨piece32_6_10,
    List.forall_mem_cons.2 ⟨piece32_7_0,
    List.forall_mem_cons.2 ⟨piece32_7_1,
    List.forall_mem_cons.2 ⟨piece32_7_2,
    List.forall_mem_cons.2 ⟨piece32_7_3,
    List.forall_mem_cons.2 ⟨piece32_7_4,
    List.forall_mem_cons.2 ⟨piece32_7_5,
    List.forall_mem_cons.2 ⟨piece32_7_6,
    List.forall_mem_cons.2 ⟨piece32_7_7,
    List.forall_mem_cons.2 ⟨piece32_7_8,
    List.forall_mem_cons.2 ⟨piece32_7_9,
    List.forall_mem_cons.2 ⟨piece32_8_0,
    List.forall_mem_cons.2 ⟨piece32_8_1,
    List.forall_mem_cons.2 ⟨piece32_8_2,
    List.forall_mem_cons.2 ⟨piece32_8_3,
    List.forall_mem_cons.2 ⟨piece32_8_4,
    List.forall_mem_cons.2 ⟨piece32_8_5,
    List.forall_mem_cons.2 ⟨piece32_8_6,
    List.forall_mem_cons.2 ⟨piece32_8_7,
    List.forall_mem_cons.2 ⟨piece32_8_8,
    List.forall_mem_cons.2 ⟨piece32_9_0,
    List.forall_mem_cons.2 ⟨piece32_9_1,
    List.forall_mem_cons.2 ⟨piece32_9_2,
    List.forall_mem_cons.2 ⟨piece32_9_3,
    List.forall_mem_cons.2 ⟨piece32_9_4,
    List.forall_mem_cons.2 ⟨piece32_9_5,
    List.forall_mem_cons.2 ⟨piece32_9_6,
    List.forall_mem_cons.2 ⟨piece32_9_7,
    List.forall_mem_cons.2 ⟨piece32_10_0,
    List.forall_mem_cons.2 ⟨piece32_10_1,
    List.forall_mem_cons.2 ⟨piece32_10_2,
    List.forall_mem_cons.2 ⟨piece32_10_3,
    List.forall_mem_cons.2 ⟨piece32_10_4,
    List.forall_mem_cons.2 ⟨piece32_10_5,
    List.forall_mem_cons.2 ⟨piece32_10_6,
    List.forall_mem_cons.2 ⟨piece32_11_0,
    List.forall_mem_cons.2 ⟨piece32_11_1,
    List.forall_mem_cons.2 ⟨piece32_11_2,
    List.forall_mem_cons.2 ⟨piece32_11_3,
    List.forall_mem_cons.2 ⟨piece32_11_4,
    List.forall_mem_cons.2 ⟨piece32_11_5,
    List.forall_mem_cons.2 ⟨piece32_12_0,
    List.forall_mem_cons.2 ⟨piece32_12_1,
    List.forall_mem_cons.2 ⟨piece32_12_2,
    List.forall_mem_cons.2 ⟨piece32_12_3,
    List.forall_mem_cons.2 ⟨piece32_12_4,
    List.forall_mem_cons.2 ⟨piece32_13_0,
    List.forall_mem_cons.2 ⟨piece32_13_1,
    List.forall_mem_cons.2 ⟨piece32_13_2,
    List.forall_mem_cons.2 ⟨piece32_13_3,
    List.forall_mem_cons.2 ⟨piece32_14_0,
    List.forall_mem_cons.2 ⟨piece32_14_1,
    List.forall_mem_cons.2 ⟨piece32_14_2,
    List.forall_mem_cons.2 ⟨piece32_15_0,
    List.forall_mem_cons.2 ⟨piece32_15_1,
    List.forall_mem_cons.2 ⟨piece32_16_0,
    List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end QueenDom
