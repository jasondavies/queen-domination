# Terminal moment certificates for Q47

The 15 receipts in this directory cover the terminal branches of the last 13 frame cases in the search for a 24-queen cover. Each receipt identifies the frame, layer bits, original root and cube SHA-256 hashes, projected CNF, and DRAT proof. The other branches of those frames have separate evidence in the run ledgers.

The row and column counts force one of three profiles. Six branches are permutations on the 24 even rows and columns. Three occupy the 23 odd rows and columns, with one repeated coordinate on each axis. In the other six, each axis has all 23 odd coordinates and one even coordinate. The even row and column must intersect at a queen, by the odd-grid polynomial bound. Removing that queen leaves an odd-coordinate permutation. The derivation and the key enumeration are in `code/frame/q47_terminal_moments.py`.

From the repository root, replay a receipt with the case's root hash from the initial frame manifest. `terminal-roots.json` in this directory lists the root hashes of the 13 terminal cases. For example:

```sh
python3 code/frame/q47_terminal_moments.py data/frame/q47_terminal_moments/0e28e4379b1be47d5701d690fa8e53dc23376323c8d0925fc9443a4946bcf34c.receipt.json --root-sha256 aebb4479f4ea3dcde17734d288512b7423993d96e1b77adfddecddca42bdaa85
```

Run `python3 code/frame/check_q47_terminal_enumeration.py` for a separate enumeration of the 15 terminal exclusions. Run `python3 code/frame/check_q47_closeout.py` with the original build ledgers and branch archives available to check the complete case census, reconcile coverage, and verify the explicit upper bound. Both checks require the frame encoder's Python dependencies. DRAT replay also uses the repository's `tools/drat-trim` binary.
