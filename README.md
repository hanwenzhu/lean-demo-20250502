The theorem `f` in `False.lean` claims to prove `False`.
Upon closer inspection, of course it is wrong and `f` isn't even added.

Open `False.lean` in VS Code; there is no
warning or error message on the InfoView.
The warning/error counter on the bottom left is 0/0.

`lake build --wfail` does not fail.

`lake env /path/to/lean4checker@4.9.0/.lake/build/bin/lean4checker False` returns code 0 (probably because `f` is not in the environment?).

Similarly for `putnam_2005_a4.lean`, the (wrong) solution found by DeepSeek-Prover-V2 to a Putnam problem, from which `False.lean` is minimized.
