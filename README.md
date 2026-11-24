# Disproof of the Fanelli–Moscardelli Conjecture on Approximate Roommates Stability

Self-contained, pure-kernel Lean 4 (`v4.35.0-rc2` + Mathlib) disproof of the open conjecture
posed by A. Fanelli and L. Moscardelli in *Approximately Stable Matching* (ECAI 2025, IOS Press,
pp. 3583–3590, [doi:10.3233/FAIA251234](https://doi.org/10.3233/FAIA251234),
[HAL hal-05368668](https://hal.science/hal-05368668)) and formalized in Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Paper/ApproximatelyStableMatching.lean)
([PR #7853](https://github.com/google-deepmind/formal-conjectures/pull/7853)).

## Mathematical Result

In a complete roommates market with $N$ agents, each agent strictly ranks all other agents
$1, \ldots, N - 1$ and ranks being single last (rank $N$). A pair of distinct agents not matched
to each other is *$k$-blocking* if both would improve their rank by at least $k$ positions by
matching together; a matching is *$k$-stable* if it has no $k$-blocking pair. Let $K(N)$ be the
least positive integer $k$ such that every strict preference profile on $N$ agents admits a
$k$-stable matching.

Fanelli and Moscardelli (Theorem 1) showed $K(N) \le \lceil N/2 \rceil$ for all $N$ (and
$K(N) = \Omega(\sqrt{N})$ in Theorem 3), and conjectured tightness for larger values, formalized
in `FormalConjectures/Paper/ApproximatelyStableMatching.lean` as:
$$\exists N_0 \ge 3,\quad \forall N \ge N_0,\quad K(N) = \lceil N / 2 \rceil.$$

We **disprove** this conjecture for every odd $N \ge 7$ by proving:

1. **`FanelliMoscardelli.exists_m_stable_of_odd`**: For every integer $m \ge 3$ and every complete
   strict preference profile on $N = 2m + 1$ agents, there exists an $m$-stable matching.
2. **`FanelliMoscardelli.stabilityThreshold_odd_le`**: For every $m \ge 3$,
   $$K(2m + 1) \le m < m + 1 = \lceil (2m + 1) / 2 \rceil.$$
3. **`FanelliMoscardelli.not_stability_threshold_tight`**: Exact logical negation of
   `FormalConjectures`'s `FanelliMoscardelli.stability_threshold_tight`.
4. **`FanelliMoscardelli.stabilityThreshold_mono`**: Monotonicity $K(n) \le K(n + 1)$ for all $n$
   (by appending a universally least-preferred agent).
5. **`FanelliMoscardelli.stabilityThreshold_five` / `_six` / `_seven`**: Combining `K(7) ≤ 3`
   with an explicit 5-agent profile admitting no 2-stable matching yields the exact values
   $$K(5) = K(6) = K(7) = 3,$$
   establishing $N = 7$ as the smallest odd counterexample ($K(7) = 3 < 4 = \lceil 7 / 2 \rceil$).

*(Note: whether $K(2m) = m$ holds for even $N \ge 8$ remains open.)*

## Statement Fidelity & Verification

`Challenge.lean` reproduces `FormalConjecturesForMathlib/Combinatorics/Roommates.lean` verbatim
and states the exact negation of `FormalConjectures/Paper/ApproximatelyStableMatching.lean`'s
`FanelliMoscardelli.stability_threshold_tight`, along with the strengthening theorems above.

To reproduce verification from scratch:

```bash
lake exe cache get
lake build Challenge Solution
lake comparator --config comparator.json
```

All theorems depend strictly on `[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero
`native_decide`, zero custom axioms).

## AI Disclosure

The combinatorial proof of $K(2m + 1) \le m$, the 5-agent lower-bound witness, and the Lean 4
formalization were developed with AI assistance (Gemini via Antigravity) under the direction of
Samuel Burbulla, who takes responsibility for the submission. The formal proof is mechanically
verified end-to-end by the Lean 4 kernel and `lake comparator`.
