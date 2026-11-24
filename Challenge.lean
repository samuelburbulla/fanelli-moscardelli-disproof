/-
Copyright 2026 The Formal Conjectures Authors and Samuel Burbulla.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Find

/-!
# Disproof of the Fanelli–Moscardelli Conjecture on Approximate Roommates Stability

*References:*
- A. Fanelli and L. Moscardelli, *Approximately Stable Matching*, ECAI 2025,
  IOS Press, pp. 3583–3590, https://doi.org/10.3233/FAIA251234
  (preprint: https://hal.science/hal-05368668).
- Google DeepMind Formal Conjectures, `FormalConjectures/Paper/ApproximatelyStableMatching.lean`
  and `FormalConjecturesForMathlib/Combinatorics/Roommates.lean` (PR #7853).

For complete strict preferences on $N$ agents (with being single ranked last, at rank $N$),
let $K(N) = \mathrm{Roommates.stabilityThreshold}\, N$ be the least positive integer $k$
such that every strict preference profile on $N$ agents admits a $k$-stable matching (a
matching with no pair of distinct agents who would each improve their rank by at least $k$
positions by matching with each other).

Fanelli and Moscardelli (Theorem 1) proved $K(N) \le \lceil N/2 \rceil$ and conjectured
tightness for larger values, formalized in `FormalConjectures/Paper/ApproximatelyStableMatching.lean`
as `∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, Roommates.stabilityThreshold N = (N + 1) / 2`.

This challenge states the disproof of that conjecture via the constructive upper bound
$K(2m + 1) \le m$ for every $m \ge 3$, together with monotonicity $K(n) \le K(n + 1)$ and the
exact values $K(5) = K(6) = K(7) = 3$ (showing $N = 7$ is the smallest odd counterexample).
-/

@[expose] public section

namespace Roommates

/-- A possibly partial matching, with fixed points representing single agents. -/
abbrev Matching (α : Type*) := {μ : Equiv.Perm α // Function.Involutive μ}

/-- Matchings form a finite type when the agents do. -/
instance {α : Type*} [Fintype α] [DecidableEq α] : Fintype (Matching α) := by
  letI : DecidablePred (fun μ : Equiv.Perm α ↦ Function.Involutive μ) := fun μ ↦ by
    unfold Function.Involutive
    infer_instance
  exact Subtype.fintype _

/-- The matching in which every agent is single. -/
def emptyMatching (α : Type*) : Matching α := ⟨Equiv.refl α, fun _ ↦ rfl⟩

/-- Every matched pair must be an edge of the acceptability graph. -/
def IsAcceptable {α : Type*} (G : SimpleGraph α) (μ : Matching α) : Prop :=
  ∀ i, μ.val i = i ∨ G.Adj i (μ.val i)

/-- An acceptable pair blocks when both endpoints strictly prefer it to their assignments. -/
def IsBlockingPair {α : Type*} (G : SimpleGraph α) (rank : α → α → ℕ)
    (μ : Matching α) (i j : α) : Prop :=
  G.Adj i j ∧ μ.val i ≠ j ∧ rank i j < rank i (μ.val i) ∧ rank j i < rank j (μ.val j)

/-- A stable matching is acceptable and has no blocking pair. -/
def IsStable {α : Type*} (G : SimpleGraph α) (rank : α → α → ℕ)
    (μ : Matching α) : Prop :=
  IsAcceptable G μ ∧ ∀ i j, ¬ IsBlockingPair G rank μ i j

/-- An acceptable pair $k$-blocks if both agents gain at least $k$ rank positions. -/
def IsKBlockingPair {α : Type*} (G : SimpleGraph α) (rank : α → α → ℕ)
    (k : ℕ) (μ : Matching α) (i j : α) : Prop :=
  G.Adj i j ∧ μ.val i ≠ j ∧
    rank i j + k ≤ rank i (μ.val i) ∧ rank j i + k ≤ rank j (μ.val j)

/-- A $k$-stable matching is acceptable and has no $k$-blocking pair. -/
def IsKStable {α : Type*} (G : SimpleGraph α) (rank : α → α → ℕ)
    (k : ℕ) (μ : Matching α) : Prop :=
  IsAcceptable G μ ∧ ∀ i j, ¬ IsKBlockingPair G rank k μ i j

/-- The matching with all agents single is acceptable. -/
theorem isAcceptable_emptyMatching {α : Type*} (G : SimpleGraph α) :
    IsAcceptable G (emptyMatching α) := fun _ ↦ Or.inl rfl

/-- Improvement by one position is ordinary strict improvement. -/
@[simp] theorem isKBlockingPair_one {α : Type*} (G : SimpleGraph α)
    (rank : α → α → ℕ) (μ : Matching α) (i j : α) :
    IsKBlockingPair G rank 1 μ i j ↔ IsBlockingPair G rank μ i j := by
  simp [IsKBlockingPair, IsBlockingPair, Nat.add_one_le_iff]

/-- One-stability is ordinary stability. -/
@[simp] theorem isKStable_one {α : Type*} (G : SimpleGraph α)
    (rank : α → α → ℕ) (μ : Matching α) :
    IsKStable G rank 1 μ ↔ IsStable G rank μ := by
  simp [IsKStable, IsStable]

/-- Complete strict preferences, with the agent's own name ranked last. -/
structure CompleteProfile (n : ℕ) where
  /-- Permutations map candidate labels to zero-based ranks. -/
  rank : Fin n → Equiv.Perm (Fin n)
  /-- Being single is worse than every other assignment. -/
  self_last : ∀ i, (rank i i).val + 1 = n

/-- A complete profile exists at every size, by swapping each agent's own label to last. -/
def CompleteProfile.canonical (n : ℕ) : CompleteProfile n where
  rank i := Equiv.swap i ⟨n - 1, by have := i.isLt; omega⟩
  self_last i := by
    simp only [Equiv.swap_apply_left]
    have := i.isLt
    omega

/-- One-based ranks, assigning rank $n$ to being single. -/
def CompleteProfile.partnerRank {n : ℕ} (p : CompleteProfile n) (i j : Fin n) : ℕ :=
  (p.rank i j).val + 1

/-- Being single has rank equal to the number of agents. -/
@[simp] theorem CompleteProfile.partnerRank_self {n : ℕ} (p : CompleteProfile n) (i : Fin n) :
    p.partnerRank i i = n := p.self_last i

/-- All assigned ranks are at most the number of agents. -/
theorem CompleteProfile.partnerRank_le {n : ℕ} (p : CompleteProfile n) (i j : Fin n) :
    p.partnerRank i j ≤ n := (p.rank i j).isLt

/-- A gain of $n$ positions is impossible with one-based ranks in a market of size $n$. -/
theorem CompleteProfile.not_isKBlockingPair_card {n : ℕ} (p : CompleteProfile n)
    (μ : Matching (Fin n)) (i j : Fin n) :
    ¬ IsKBlockingPair ⊤ p.partnerRank n μ i j := by
  rintro ⟨_, _, hi, _⟩
  have hbound := p.partnerRank_le i (μ.val i)
  have hpositive : 0 < p.partnerRank i j := Nat.zero_lt_succ _
  omega

/-- Every complete preference profile admits a positive stability threshold. -/
theorem exists_stabilityThreshold (n : ℕ) :
    ∃ k : ℕ, 0 < k ∧ ∀ p : CompleteProfile n,
      ∃ μ : Matching (Fin n), IsKStable ⊤ p.partnerRank k μ :=
  ⟨n + 1, Nat.zero_lt_succ _, fun p ↦ ⟨emptyMatching _,
    isAcceptable_emptyMatching _, fun i _ h ↦
      Nat.not_succ_le_self n (Nat.le_trans (Nat.le_add_left (n + 1) _)
        (Nat.le_trans h.2.2.1 (p.partnerRank_le i ((emptyMatching (Fin n)).val i))))⟩⟩

open scoped Classical in
/-- The least positive $k$ for which every complete profile has a $k$-stable matching. -/
noncomputable def stabilityThreshold (n : ℕ) : ℕ :=
  Nat.find (exists_stabilityThreshold n)

/-- The threshold is positive and guarantees existence for every complete profile. -/
theorem stabilityThreshold_spec (n : ℕ) :
    0 < stabilityThreshold n ∧ ∀ p : CompleteProfile n,
      ∃ μ : Matching (Fin n), IsKStable ⊤ p.partnerRank (stabilityThreshold n) μ := by
  classical
  exact Nat.find_spec (exists_stabilityThreshold n)

/-- Any positive universal existence bound is at least the threshold. -/
theorem stabilityThreshold_le {n k : ℕ} (hk : 0 < k)
    (h : ∀ p : CompleteProfile n, ∃ μ : Matching (Fin n), IsKStable ⊤ p.partnerRank k μ) :
    stabilityThreshold n ≤ k := by
  classical
  exact Nat.find_min' (exists_stabilityThreshold n) ⟨hk, h⟩

/-- In a nonempty market, a gain of the full market size is a universal existence bound. -/
theorem stabilityThreshold_le_card {n : ℕ} (hn : 0 < n) : stabilityThreshold n ≤ n := by
  apply stabilityThreshold_le hn
  intro p
  exact ⟨emptyMatching _, isAcceptable_emptyMatching _, p.not_isKBlockingPair_card _⟩

/-- A single agent has no possible blocking pair. -/
theorem stabilityThreshold_one : stabilityThreshold 1 = 1 := by
  apply Nat.le_antisymm
  · apply stabilityThreshold_le (by decide)
    intro p
    refine ⟨emptyMatching _, isAcceptable_emptyMatching _, ?_⟩
    intro i j h
    have hij : i = j := Subsingleton.elim _ _
    subst j
    exact h.2.1 rfl
  · exact (stabilityThreshold_spec 1).1

/-- Two agents can always be matched to each other. -/
theorem stabilityThreshold_two : stabilityThreshold 2 = 1 := by
  apply Nat.le_antisymm
  · apply stabilityThreshold_le (by decide)
    intro p
    let μ : Matching (Fin 2) := ⟨Equiv.swap 0 1, Equiv.swap_apply_self 0 1⟩
    refine ⟨μ, ?_, ?_⟩
    · intro i
      by_cases h : μ.val i = i
      · exact Or.inl h
      · exact Or.inr ((SimpleGraph.top_adj _ _).2 (Ne.symm h))
    · intro i j h
      have hswap : ∀ i j : Fin 2, i ≠ j → Equiv.swap 0 1 i = j := by decide
      exact h.2.1 (hswap i j ((SimpleGraph.top_adj _ _).1 h.1))
  · exact (stabilityThreshold_spec 2).1

/-- Three agents whose first choices form a directed cycle. -/
noncomputable def CompleteProfile.cyclicThree : CompleteProfile 3 where
  rank := ![Equiv.ofBijective ![2, 0, 1] (by decide),
    Equiv.ofBijective ![1, 2, 0] (by decide),
    Equiv.ofBijective ![0, 1, 2] (by decide)]
  self_last := by decide

/-- The cyclic three-agent profile has no stable matching, even when singles are allowed. -/
theorem CompleteProfile.not_isStable_cyclicThree :
    ∀ μ : Matching (Fin 3), ¬ IsStable ⊤ CompleteProfile.cyclicThree.partnerRank μ := by
  unfold IsStable IsAcceptable IsBlockingPair
  decide

end Roommates

namespace FanelliMoscardelli

/-- For every `m ≥ 3` and every complete strict preference profile on `2m + 1` agents,
there exists an `m`-stable matching. -/
theorem exists_m_stable_of_odd (m : ℕ) (hm : 3 ≤ m)
    (p : Roommates.CompleteProfile (2 * m + 1)) :
    ∃ μ : Roommates.Matching (Fin (2 * m + 1)),
      Roommates.IsKStable ⊤ p.partnerRank m μ := by
  sorry

/-- For every `m ≥ 3`, `K(2m + 1) ≤ m < m + 1 = ⌈(2m + 1) / 2⌉`. -/
theorem stabilityThreshold_odd_le (m : ℕ) (hm : 3 ≤ m) :
    Roommates.stabilityThreshold (2 * m + 1) ≤ m := by
  sorry

/-- **Disproof of the Fanelli–Moscardelli Conjecture**: It is NOT the case that
`K(N) = ⌈N / 2⌉` for all sufficiently large `N`. -/
theorem not_stability_threshold_tight :
    ¬ (∃ N₀ : ℕ, 3 ≤ N₀ ∧
        ∀ N ≥ N₀, Roommates.stabilityThreshold N = (N + 1) / 2) := by
  sorry

/-- Monotonicity of the stability threshold: `K(n) ≤ K(n + 1)` for all `n`. -/
theorem stabilityThreshold_mono (n : ℕ) :
    Roommates.stabilityThreshold n ≤ Roommates.stabilityThreshold (n + 1) := by
  sorry

/-- Exact stability threshold for 5 agents: `K(5) = 3`. -/
theorem stabilityThreshold_five : Roommates.stabilityThreshold 5 = 3 := by
  sorry

/-- Exact stability threshold for 6 agents: `K(6) = 3`. -/
theorem stabilityThreshold_six : Roommates.stabilityThreshold 6 = 3 := by
  sorry

/-- Exact stability threshold for 7 agents: `K(7) = 3 < 4 = ⌈7 / 2⌉`. -/
theorem stabilityThreshold_seven : Roommates.stabilityThreshold 7 = 3 := by
  sorry

end FanelliMoscardelli
