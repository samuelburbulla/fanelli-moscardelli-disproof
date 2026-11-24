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
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

/-!
# Disproof of the Fanelli–Moscardelli Conjecture on Approximate Roommates Stability

This file provides a completely self-contained Lean 4 formalization of:

1. The `Roommates` matching and rank-improvement stability definitions of
   A. Fanelli and L. Moscardelli, *Approximately Stable Matching* (ECAI 2025,
   https://doi.org/10.3233/FAIA251234).
2. The main constructive upper bound `FanelliMoscardelli.exists_m_stable_of_odd`:
   for every integer `m ≥ 3` and every complete strict preference profile on `N = 2m + 1`
   agents, there exists an `m`-stable matching.
3. The threshold bound `FanelliMoscardelli.stabilityThreshold_odd_le`:
   for every `m ≥ 3`, `K(2m + 1) ≤ m < m + 1 = ⌈(2m + 1) / 2⌉`.
4. The disproof `FanelliMoscardelli.not_stability_threshold_tight` of the open
   Fanelli–Moscardelli conjecture that `K(N) = ⌈N / 2⌉` for all sufficiently large `N`.
5. Monotonicity `FanelliMoscardelli.stabilityThreshold_mono`: `K(n) ≤ K(n + 1)` for all `n`.
6. Explicit computable 5-agent 2-blocking profile `FanelliMoscardelli.fiveAgentWitness`
   yielding `3 ≤ K(5)` and hence the exact values `K(5) = 3`, `K(6) = 3`, and `K(7) = 3`
   (the smallest odd counterexample to `K(N) = ⌈N / 2⌉`, since `K(7) = 3 < 4 = ⌈7 / 2⌉`).
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
  simp [IsKBlockingPair, IsBlockingPair]

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

open scoped BigOperators
open Roommates

section InvolutionHelpers

private def ofInvolutive {N : ℕ} (f : Fin N → Fin N) (hf : Function.Involutive f) :
    Matching (Fin N) :=
  ⟨hf.toPerm f, hf⟩

@[simp]
private lemma ofInvolutive_apply {N : ℕ} (f : Fin N → Fin N) (hf : Function.Involutive f)
    (x : Fin N) : (ofInvolutive f hf).val x = f x := rfl

private def matchedSet {N : ℕ} (μ : Matching (Fin N)) : Finset (Fin N) :=
  Finset.univ.filter (fun i => μ.val i ≠ i)

@[simp]
private lemma mem_matchedSet {N : ℕ} (μ : Matching (Fin N)) (i : Fin N) :
    i ∈ matchedSet μ ↔ μ.val i ≠ i := by
  simp [matchedSet]

private lemma matchedSet_map {N : ℕ} (μ : Matching (Fin N)) {i : Fin N}
    (hi : i ∈ matchedSet μ) : μ.val i ∈ matchedSet μ := by
  rw [mem_matchedSet] at hi ⊢
  intro h
  exact hi (by simpa [μ.property i] using h.symm)

private lemma matchedSet_emptyMatching (N : ℕ) :
    matchedSet (emptyMatching (Fin N)) = ∅ := by
  ext i
  simp [matchedSet, emptyMatching]

private def eraseEdge {N : ℕ} (μ : Matching (Fin N)) (a b : Fin N) (hab : μ.val a = b) :
    Matching (Fin N) :=
  ofInvolutive (fun x => if x = a ∨ x = b then x else μ.val x) (by
    intro x
    have hba : μ.val b = a := by rw [← hab, μ.property a]
    by_cases hx : x = a ∨ x = b
    · simp [hx]
    · push Not at hx
      have hμx : μ.val x ≠ a ∧ μ.val x ≠ b := by
        constructor
        · intro h; exact hx.2 (by rw [← μ.property x, h, hab])
        · intro h; exact hx.1 (by rw [← μ.property x, h, hba])
      simp [hx.1, hx.2, hμx.1, hμx.2, μ.property x])

private lemma eraseEdge_apply {N : ℕ} (μ : Matching (Fin N)) {a b : Fin N} (hab : μ.val a = b)
    (x : Fin N) :
    (eraseEdge μ a b hab).val x = if x = a ∨ x = b then x else μ.val x := rfl

private lemma matchedSet_eraseEdge {N : ℕ} (μ : Matching (Fin N)) {a b : Fin N}
    (hab : μ.val a = b) :
    matchedSet (eraseEdge μ a b hab) = ((matchedSet μ).erase a).erase b := by
  ext x
  simp only [mem_matchedSet, eraseEdge_apply, Finset.mem_erase]
  by_cases hxa : x = a
  · simp [hxa]
  · by_cases hxb : x = b
    · simp [hxb]
    · simp [hxa, hxb]

private lemma isAcceptable_eraseEdge {N : ℕ} {G : SimpleGraph (Fin N)}
    (μ : Matching (Fin N)) (hμ : IsAcceptable G μ) {a b : Fin N} (hab : μ.val a = b) :
    IsAcceptable G (eraseEdge μ a b hab) := by
  intro i
  rw [eraseEdge_apply]
  split_ifs
  · exact Or.inl rfl
  · exact hμ i

private def addEdge {N : ℕ} (μ : Matching (Fin N)) (a b : Fin N)
    (ha : μ.val a = a) (hb : μ.val b = b) : Matching (Fin N) :=
  ofInvolutive (fun x => if x = a then b else if x = b then a else μ.val x) (by
    intro x
    by_cases hxa : x = a
    · rw [hxa]
      by_cases hab : a = b
      · simp [hab]
      · simp [Ne.symm hab]
    · by_cases hxb : x = b
      · have hba : b ≠ a := hxb ▸ hxa
        rw [hxb]
        simp [hba]
      · have hμxa : μ.val x ≠ a := by
          intro h; exact hxa (by rw [← μ.property x, h, ha])
        have hμxb : μ.val x ≠ b := by
          intro h; exact hxb (by rw [← μ.property x, h, hb])
        simp [hxa, hxb, hμxa, hμxb, μ.property x])

private lemma addEdge_apply {N : ℕ} (μ : Matching (Fin N)) {a b : Fin N}
    (ha : μ.val a = a) (hb : μ.val b = b) (x : Fin N) :
    (addEdge μ a b ha hb).val x = if x = a then b else if x = b then a else μ.val x := rfl

private lemma matchedSet_addEdge {N : ℕ} (μ : Matching (Fin N)) {a b : Fin N}
    (hne : a ≠ b) (ha : μ.val a = a) (hb : μ.val b = b) :
    matchedSet (addEdge μ a b ha hb) = insert a (insert b (matchedSet μ)) := by
  ext x
  simp only [mem_matchedSet, addEdge_apply, Finset.mem_insert]
  by_cases hxa : x = a
  · rw [hxa]; simp [hne.symm]
  · by_cases hxb : x = b
    · rw [hxb]; simp [hne, hne.symm]
    · simp [hxa, hxb]

private lemma isAcceptable_addEdge {N : ℕ} {G : SimpleGraph (Fin N)}
    (μ : Matching (Fin N)) (hμ : IsAcceptable G μ) {a b : Fin N}
    (ha : μ.val a = a) (hb : μ.val b = b) (hadj : G.Adj a b) :
    IsAcceptable G (addEdge μ a b ha hb) := by
  intro i
  rw [addEdge_apply]
  split_ifs with h1 h2
  · rw [h1]; exact Or.inr hadj
  · rw [h2]; exact Or.inr hadj.symm
  · exact hμ i

private def combineMatchings {N : ℕ} (A : Finset (Fin N)) (μ₁ μ₂ : Matching (Fin N))
    (h₁ : matchedSet μ₁ ⊆ A) (h₂ : Disjoint A (matchedSet μ₂)) : Matching (Fin N) :=
  ofInvolutive (fun x => if x ∈ A then μ₁.val x else μ₂.val x) (by
    intro x
    by_cases hx : x ∈ A
    · have hμ₁ : μ₁.val x ∈ A := by
        by_cases hfix : μ₁.val x = x
        · rwa [hfix]
        · exact h₁ (matchedSet_map μ₁ ((mem_matchedSet μ₁ x).2 hfix))
      simp [hx, hμ₁, μ₁.property x]
    · have hμ₂ : μ₂.val x ∉ A := by
        by_cases hfix : μ₂.val x = x
        · rwa [hfix]
        · exact Finset.disjoint_right.1 h₂ (matchedSet_map μ₂ ((mem_matchedSet μ₂ x).2 hfix))
      simp [hx, hμ₂, μ₂.property x])

private lemma combineMatchings_apply {N : ℕ} (A : Finset (Fin N)) (μ₁ μ₂ : Matching (Fin N))
    (h₁ : matchedSet μ₁ ⊆ A) (h₂ : Disjoint A (matchedSet μ₂)) (x : Fin N) :
    (combineMatchings A μ₁ μ₂ h₁ h₂).val x = if x ∈ A then μ₁.val x else μ₂.val x := rfl

private lemma matchedSet_combineMatchings {N : ℕ} (A : Finset (Fin N)) (μ₁ μ₂ : Matching (Fin N))
    (h₁ : matchedSet μ₁ ⊆ A) (h₂ : Disjoint A (matchedSet μ₂)) :
    matchedSet (combineMatchings A μ₁ μ₂ h₁ h₂) = matchedSet μ₁ ∪ matchedSet μ₂ := by
  ext x
  simp only [mem_matchedSet, combineMatchings_apply, Finset.mem_union]
  by_cases hx : x ∈ A
  · simp only [hx, ↓reduceIte]
    have hx₂ : x ∉ matchedSet μ₂ := Finset.disjoint_left.1 h₂ hx
    rw [mem_matchedSet, not_not] at hx₂
    simp [hx₂]
  · simp only [hx, ↓reduceIte]
    have hx₁ : x ∉ matchedSet μ₁ := fun h => hx (h₁ h)
    rw [mem_matchedSet, not_not] at hx₁
    simp [hx₁]

private lemma isAcceptable_combineMatchings {N : ℕ} {G : SimpleGraph (Fin N)}
    (A : Finset (Fin N)) (μ₁ μ₂ : Matching (Fin N))
    (h₁ : matchedSet μ₁ ⊆ A) (h₂ : Disjoint A (matchedSet μ₂))
    (hG₁ : IsAcceptable G μ₁) (hG₂ : IsAcceptable G μ₂) :
    IsAcceptable G (combineMatchings A μ₁ μ₂ h₁ h₂) := by
  intro i
  rw [combineMatchings_apply]
  split_ifs
  · exact hG₁ i
  · exact hG₂ i

private def restrictMatching {N : ℕ} (A : Finset (Fin N)) (μ : Matching (Fin N))
    (hA : ∀ x ∈ A, μ.val x ∈ A) : Matching (Fin N) :=
  ofInvolutive (fun x => if x ∈ A then μ.val x else x) (by
    intro x
    by_cases hx : x ∈ A
    · simp [hx, hA x hx, μ.property x]
    · simp [hx])

private lemma restrictMatching_apply {N : ℕ} (A : Finset (Fin N)) (μ : Matching (Fin N))
    (hA : ∀ x ∈ A, μ.val x ∈ A) (x : Fin N) :
    (restrictMatching A μ hA).val x = if x ∈ A then μ.val x else x := rfl

private lemma matchedSet_restrictMatching {N : ℕ} (A : Finset (Fin N)) (μ : Matching (Fin N))
    (hA : ∀ x ∈ A, μ.val x ∈ A) :
    matchedSet (restrictMatching A μ hA) = A ∩ matchedSet μ := by
  ext x
  simp only [mem_matchedSet, restrictMatching_apply, Finset.mem_inter]
  by_cases hx : x ∈ A <;> simp [hx]

private lemma isAcceptable_restrictMatching {N : ℕ} {G : SimpleGraph (Fin N)}
    (A : Finset (Fin N)) (μ : Matching (Fin N)) (hA : ∀ x ∈ A, μ.val x ∈ A)
    (hG : IsAcceptable G μ) : IsAcceptable G (restrictMatching A μ hA) := by
  intro i
  rw [restrictMatching_apply]
  split_ifs
  · exact hG i
  · exact Or.inl rfl

private lemma even_card_matchedSet {N : ℕ} (μ : Matching (Fin N)) :
    Even (matchedSet μ).card := by
  suffices h : ∀ k (μ : Matching (Fin N)), (matchedSet μ).card = k → Even k from
    h (matchedSet μ).card μ rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro μ hk
    by_cases h0 : (matchedSet μ).card = 0
    · rw [← hk, h0]; exact ⟨0, rfl⟩
    · obtain ⟨a, ha⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h0)
      have hne : μ.val a ≠ a := (mem_matchedSet μ a).1 ha
      have hb : μ.val a ∈ matchedSet μ := matchedSet_map μ ha
      let μ' := eraseEdge μ a (μ.val a) rfl
      have hms : matchedSet μ' = ((matchedSet μ).erase a).erase (μ.val a) :=
        matchedSet_eraseEdge μ rfl
      have hb' : μ.val a ∈ (matchedSet μ).erase a := Finset.mem_erase.2 ⟨hne, hb⟩
      have hcard' : (matchedSet μ').card + 2 = k := by
        rw [hms, Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
        have h2 : 2 ≤ (matchedSet μ).card := by
          have := Finset.card_pos.2 ⟨μ.val a, hb'⟩
          rw [Finset.card_erase_of_mem ha] at this
          omega
        omega
      obtain ⟨r, hr⟩ := ih (matchedSet μ').card (by omega) μ' rfl
      exact ⟨r + 1, by omega⟩

private lemma exists_pm_on_even {N : ℕ} (A : Finset (Fin N)) (hA : Even A.card) :
    ∃ μ : Matching (Fin N), matchedSet μ = A := by
  obtain ⟨k, hk⟩ := hA
  induction k generalizing A with
  | zero =>
    have hAe : A = ∅ := Finset.card_eq_zero.1 (by omega)
    subst hAe
    exact ⟨emptyMatching (Fin N), matchedSet_emptyMatching N⟩
  | succ k ih =>
    have hpos : 0 < A.card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.1 hpos
    have hpos' : 0 < (A.erase a).card := by
      rw [Finset.card_erase_of_mem ha]; omega
    obtain ⟨b, hb'⟩ := Finset.card_pos.1 hpos'
    have hba : b ≠ a := (Finset.mem_erase.1 hb').1
    have hb : b ∈ A := (Finset.mem_erase.1 hb').2
    let A' := (A.erase a).erase b
    have hA'card : A'.card = k + k := by
      dsimp [A']
      rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
      omega
    obtain ⟨μ', hμ'⟩ := ih A' hA'card
    have ha_fix : μ'.val a = a := by
      by_contra h
      have : a ∈ A' := hμ' ▸ (mem_matchedSet μ' a).2 h
      simp [A'] at this
    have hb_fix : μ'.val b = b := by
      by_contra h
      have : b ∈ A' := hμ' ▸ (mem_matchedSet μ' b).2 h
      simp [A'] at this
    refine ⟨addEdge μ' a b ha_fix hb_fix, ?_⟩
    rw [matchedSet_addEdge μ' hba.symm ha_fix hb_fix, hμ']
    ext x
    simp only [A', Finset.mem_insert, Finset.mem_erase]
    by_cases hxa : x = a
    · simp [hxa, ha]
    · by_cases hxb : x = b
      · simp [hxb, hb]
      · simp [hxa, hxb]

private lemma exists_pm_on_even_pair {N : ℕ} (A : Finset (Fin N)) (hA : Even A.card)
    {a b : Fin N} (ha : a ∈ A) (hb : b ∈ A) (hne : a ≠ b) :
    ∃ μ : Matching (Fin N), matchedSet μ = A ∧ μ.val a = b := by
  let A' := (A.erase a).erase b
  have hb' : b ∈ A.erase a := Finset.mem_erase.2 ⟨hne.symm, hb⟩
  have hA'even : Even A'.card := by
    dsimp [A']
    rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
    obtain ⟨k, hk⟩ := hA
    have h2 : 2 ≤ A.card := by
      have := Finset.card_pos.2 ⟨b, hb'⟩
      rw [Finset.card_erase_of_mem ha] at this
      omega
    exact ⟨k - 1, by omega⟩
  obtain ⟨μ', hμ'⟩ := exists_pm_on_even A' hA'even
  have ha_fix : μ'.val a = a := by
    by_contra h
    have : a ∈ A' := hμ' ▸ (mem_matchedSet μ' a).2 h
    simp [A'] at this
  have hb_fix : μ'.val b = b := by
    by_contra h
    have : b ∈ A' := hμ' ▸ (mem_matchedSet μ' b).2 h
    simp [A'] at this
  refine ⟨addEdge μ' a b ha_fix hb_fix, ?_, ?_⟩
  · rw [matchedSet_addEdge μ' hne ha_fix hb_fix, hμ']
    ext x
    simp only [A', Finset.mem_insert, Finset.mem_erase]
    by_cases hxa : x = a
    · simp [hxa, ha]
    · by_cases hxb : x = b
      · simp [hxb, hb]
      · simp [hxa, hxb]
  · simp [addEdge_apply]

private lemma walk_cross {α : Type*} [DecidableEq α] {G : SimpleGraph α} {T : Finset α}
    {a b : α} (w : G.Walk a b) (ha : a ∈ T) (hb : b ∉ T) :
    ∃ u v, u ∈ T ∧ v ∉ T ∧ G.Adj u v := by
  induction w with
  | nil => exact absurd ha hb
  | @cons u v _ huv _ ih =>
    by_cases hv : v ∈ T
    · exact ih hv hb
    · exact ⟨u, v, ha, hv, huv⟩

end InvolutionHelpers

section CoreProof

variable {m : ℕ}

private lemma rk_pos (p : CompleteProfile (2 * m + 1)) (i j : Fin (2 * m + 1)) :
    1 ≤ p.partnerRank i j :=
  Nat.succ_le_succ (Nat.zero_le _)

private lemma rk_inj (p : CompleteProfile (2 * m + 1)) (i : Fin (2 * m + 1)) :
    Function.Injective (p.partnerRank i) := by
  intro a b h
  apply (p.rank i).injective
  apply Fin.ext
  unfold CompleteProfile.partnerRank at h
  omega

private lemma rk_eq_self_iff (p : CompleteProfile (2 * m + 1)) (i j : Fin (2 * m + 1)) :
    p.partnerRank i j = 2 * m + 1 ↔ j = i := by
  constructor
  · intro h
    exact rk_inj p i (h.trans (p.partnerRank_self i).symm)
  · rintro rfl; exact p.partnerRank_self _

private lemma rk_le_two_mul_of_ne (p : CompleteProfile (2 * m + 1)) {i j : Fin (2 * m + 1)}
    (hne : j ≠ i) : p.partnerRank i j ≤ 2 * m := by
  have hle := p.partnerRank_le i j
  have hne' : p.partnerRank i j ≠ 2 * m + 1 := fun h => hne ((rk_eq_self_iff p i j).1 h)
  omega

private lemma card_filter_rk_le (p : CompleteProfile (2 * m + 1)) (i : Fin (2 * m + 1))
    (k : ℕ) (hk : k ≤ 2 * m + 1) :
    (Finset.univ.filter (fun j => p.partnerRank i j ≤ k)).card = k := by
  have hbij :
      (Finset.univ.filter (fun j => p.partnerRank i j ≤ k)).card =
      (Finset.univ.filter (fun r : Fin (2 * m + 1) => r.val + 1 ≤ k)).card := by
    refine Finset.card_bij (fun j _ => p.rank i j) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hj
    · intro a _ b _ h; exact (p.rank i).injective h
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      refine ⟨(p.rank i).symm r, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by simp⟩
      simpa [CompleteProfile.partnerRank] using hr
  rw [hbij]
  have hbij2 :
      (Finset.univ.filter (fun r : Fin (2 * m + 1) => r.val + 1 ≤ k)).card =
      (Finset.range k).card := by
    refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      simp only [Finset.mem_range]
      omega
    · intro a _ b _ h; exact Fin.ext h
    · intro x hx
      simp only [Finset.mem_range] at hx
      refine ⟨⟨x, by omega⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  rw [hbij2, Finset.card_range]

private lemma card_filter_rk_ge (p : CompleteProfile (2 * m + 1)) (i : Fin (2 * m + 1))
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * m + 1) :
    (Finset.univ.filter (fun j => k ≤ p.partnerRank i j)).card = 2 * m + 2 - k := by
  have hpart :
      (Finset.univ.filter (fun j => k ≤ p.partnerRank i j)).card +
      (Finset.univ.filter (fun j => p.partnerRank i j ≤ k - 1)).card = 2 * m + 1 := by
    have hdisj : Disjoint (Finset.univ.filter (fun j => k ≤ p.partnerRank i j))
        (Finset.univ.filter (fun j => p.partnerRank i j ≤ k - 1)) := by
      rw [Finset.disjoint_filter]
      intro j _ h1 h2; omega
    have hunion : Finset.univ.filter (fun j => k ≤ p.partnerRank i j) ∪
        Finset.univ.filter (fun j => p.partnerRank i j ≤ k - 1) = Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      omega
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  have hle := card_filter_rk_le p i (k - 1) (by omega)
  omega

private def vstar (p : CompleteProfile (2 * m + 1)) (i : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  (p.rank i).symm ⟨m, by omega⟩

private lemma rk_vstar (p : CompleteProfile (2 * m + 1)) (i : Fin (2 * m + 1)) :
    p.partnerRank i (vstar p i) = m + 1 := by
  simp [CompleteProfile.partnerRank, vstar]

private lemma vstar_ne_self (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (i : Fin (2 * m + 1)) : vstar p i ≠ i := by
  intro h
  have := rk_vstar p i
  rw [h, p.partnerRank_self] at this
  omega

private lemma rk_eq_succ_iff (p : CompleteProfile (2 * m + 1)) (i j : Fin (2 * m + 1)) :
    p.partnerRank i j = m + 1 ↔ j = vstar p i := by
  constructor
  · intro h
    exact rk_inj p i (h.trans (rk_vstar p i).symm)
  · rintro rfl; exact rk_vstar p i

private def HGraph (p : CompleteProfile (2 * m + 1)) : SimpleGraph (Fin (2 * m + 1)) where
  Adj i j := i ≠ j ∧ p.partnerRank i j ≤ m ∧ p.partnerRank j i ≤ m
  symm := ⟨by rintro i j ⟨hne, h1, h2⟩; exact ⟨hne.symm, h2, h1⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

private instance (p : CompleteProfile (2 * m + 1)) : DecidableRel (HGraph p).Adj :=
  fun i j =>
    inferInstanceAs (Decidable (i ≠ j ∧ p.partnerRank i j ≤ m ∧ p.partnerRank j i ≤ m))

private abbrev IsHMatching (p : CompleteProfile (2 * m + 1)) (μ : Matching (Fin (2 * m + 1))) :
    Prop :=
  IsAcceptable (HGraph p) μ

private lemma isAcceptable_top {N : ℕ} (μ : Matching (Fin N)) :
    IsAcceptable ⊤ μ := by
  intro i
  by_cases h : μ.val i = i
  · exact Or.inl h
  · exact Or.inr ((SimpleGraph.top_adj _ _).2 (Ne.symm h))

private lemma exists_blocking_of_not_stable (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    (μ : Matching (Fin (2 * m + 1))) :
    ∃ a b : Fin (2 * m + 1), IsKBlockingPair ⊤ p.partnerRank m μ a b := by
  have h := hno μ
  unfold IsKStable at h
  push Not at h
  exact h (isAcceptable_top μ)

private lemma blocking_symm (p : CompleteProfile (2 * m + 1)) {μ : Matching (Fin (2 * m + 1))}
    {a b : Fin (2 * m + 1)} (h : IsKBlockingPair ⊤ p.partnerRank m μ a b) :
    IsKBlockingPair ⊤ p.partnerRank m μ b a := by
  rcases h with ⟨hadj, hne, h1, h2⟩
  refine ⟨hadj.symm, ?_, h2, h1⟩
  intro hba
  exact hne (by rw [← hba, μ.property b])

/-- Basic Lemma (Safe vertices): any agent assigned a top-`m` partner cannot `m`-block. -/
private lemma not_blocking_of_safe_left (p : CompleteProfile (2 * m + 1))
    {μ : Matching (Fin (2 * m + 1))} {a b : Fin (2 * m + 1)}
    (hsafe : p.partnerRank a (μ.val a) ≤ m) :
    ¬ IsKBlockingPair ⊤ p.partnerRank m μ a b := by
  rintro ⟨_, _, ha, _⟩
  have := rk_pos p a b
  omega

private lemma not_blocking_of_safe_right (p : CompleteProfile (2 * m + 1))
    {μ : Matching (Fin (2 * m + 1))} {a b : Fin (2 * m + 1)}
    (hsafe : p.partnerRank b (μ.val b) ≤ m) :
    ¬ IsKBlockingPair ⊤ p.partnerRank m μ a b :=
  fun h => not_blocking_of_safe_left p hsafe (blocking_symm p h)

/-- Basic Lemma (Non-`H`-edge, matched-matched): two matched agents not adjacent in `H`
cannot `m`-block. -/
private lemma not_blocking_matched_matched_non_H (p : CompleteProfile (2 * m + 1))
    {μ : Matching (Fin (2 * m + 1))} {a b : Fin (2 * m + 1)}
    (hnonH : ¬ (HGraph p).Adj a b) (ha : μ.val a ≠ a) (hb : μ.val b ≠ b) :
    ¬ IsKBlockingPair ⊤ p.partnerRank m μ a b := by
  rintro ⟨hadj, _, h1, h2⟩
  have hne : a ≠ b := (SimpleGraph.top_adj _ _).1 hadj
  have hle_a : p.partnerRank a (μ.val a) ≤ 2 * m := rk_le_two_mul_of_ne p ha
  have hle_b : p.partnerRank b (μ.val b) ≤ 2 * m := rk_le_two_mul_of_ne p hb
  have hor : m < p.partnerRank a b ∨ m < p.partnerRank b a := by
    by_contra h
    push Not at h
    exact hnonH ⟨hne, h.1, h.2⟩
  rcases hor with h | h <;> omega

/-- Basic Lemma (Non-`H`-edge, single-matched): if `a` is single, `b` is matched, and `a, b`
are not adjacent in `H`, then `(a, b)` `m`-blocks only if `b = vstar a` and
`rk b a + m ≤ rk b (μ b)`. -/
private lemma blocking_single_matched_non_H (p : CompleteProfile (2 * m + 1))
    {μ : Matching (Fin (2 * m + 1))} {a b : Fin (2 * m + 1)}
    (hnonH : ¬ (HGraph p).Adj a b) (ha : μ.val a = a) (hb : μ.val b ≠ b)
    (hblk : IsKBlockingPair ⊤ p.partnerRank m μ a b) :
    b = vstar p a ∧ p.partnerRank b a + m ≤ p.partnerRank b (μ.val b) := by
  rcases hblk with ⟨hadj, _, h1, h2⟩
  have hne : a ≠ b := (SimpleGraph.top_adj _ _).1 hadj
  rw [ha, p.partnerRank_self] at h1
  have hle_b : p.partnerRank b (μ.val b) ≤ 2 * m := rk_le_two_mul_of_ne p hb
  have hrba : p.partnerRank b a ≤ m := by omega
  have hrab_gt : m < p.partnerRank a b := by
    by_contra h
    push Not at h
    exact hnonH ⟨hne, h, hrba⟩
  have hrab_eq : p.partnerRank a b = m + 1 := by omega
  exact ⟨(rk_eq_succ_iff p a b).1 hrab_eq, h2⟩

private def IsMaxHMatching (p : CompleteProfile (2 * m + 1)) (M : Matching (Fin (2 * m + 1))) :
    Prop :=
  IsHMatching p M ∧ ∀ M' : Matching (Fin (2 * m + 1)),
    IsHMatching p M' → (matchedSet M').card ≤ (matchedSet M).card

private lemma exists_maxHMatching (p : CompleteProfile (2 * m + 1)) :
    ∃ M : Matching (Fin (2 * m + 1)), IsMaxHMatching p M := by
  classical
  let s : Finset (Matching (Fin (2 * m + 1))) := Finset.univ.filter (fun M => IsHMatching p M)
  have hne : s.Nonempty := ⟨emptyMatching _, by
    simp [s, IsHMatching, isAcceptable_emptyMatching]⟩
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image s (fun M => (matchedSet M).card) hne
  refine ⟨M, (Finset.mem_filter.1 hM).2, fun M' hM' => ?_⟩
  exact hmax M' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hM'⟩)

/-! ### Step 1: Structure of the unmatched set `U` for any maximum `H`-matching -/

section Step1

private lemma H_adj_of_mem_matchedSet (p : CompleteProfile (2 * m + 1))
    {M : Matching (Fin (2 * m + 1))} (hMH : IsHMatching p M) {v : Fin (2 * m + 1)}
    (hv : v ∈ matchedSet M) : (HGraph p).Adj v (M.val v) := by
  have hne : M.val v ≠ v := (mem_matchedSet M v).1 hv
  rcases hMH v with hfix | hadj
  · exact absurd hfix hne
  · exact hadj

private lemma rk_M_le_m_of_mem_matchedSet (p : CompleteProfile (2 * m + 1))
    {M : Matching (Fin (2 * m + 1))} (hMH : IsHMatching p M) {v : Fin (2 * m + 1)}
    (hv : v ∈ matchedSet M) : p.partnerRank v (M.val v) ≤ m :=
  (H_adj_of_mem_matchedSet p hMH hv).2.1

private lemma odd_card_U (M : Matching (Fin (2 * m + 1))) :
    Odd (Finset.univ \ matchedSet M).card := by
  have hev : Even (matchedSet M).card := even_card_matchedSet M
  have hsum : (matchedSet M).card + (Finset.univ \ matchedSet M).card = 2 * m + 1 := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (matchedSet M))
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨k, hk⟩ := hev
  exact ⟨m - k, by omega⟩

private lemma U_indep (p : CompleteProfile (2 * m + 1)) {M : Matching (Fin (2 * m + 1))}
    (hM : IsMaxHMatching p M) {u v : Fin (2 * m + 1)}
    (hu : u ∈ Finset.univ \ matchedSet M) (hv : v ∈ Finset.univ \ matchedSet M) :
    ¬ (HGraph p).Adj u v := by
  intro hadj
  have hne : u ≠ v := hadj.1
  have hu_fix : M.val u = u := by
    have := (Finset.mem_sdiff.1 hu).2
    rwa [mem_matchedSet, not_not] at this
  have hv_fix : M.val v = v := by
    have := (Finset.mem_sdiff.1 hv).2
    rwa [mem_matchedSet, not_not] at this
  let M' := addEdge M u v hu_fix hv_fix
  have hM'H : IsHMatching p M' := isAcceptable_addEdge M hM.1 hu_fix hv_fix hadj
  have hle := hM.2 M' hM'H
  have hms : matchedSet M' = insert u (insert v (matchedSet M)) :=
    matchedSet_addEdge M hne hu_fix hv_fix
  have hu_not : u ∉ insert v (matchedSet M) := by
    simp [hne, (Finset.mem_sdiff.1 hu).2]
  have hv_not : v ∉ matchedSet M := (Finset.mem_sdiff.1 hv).2
  rw [hms, Finset.card_insert_of_notMem hu_not, Finset.card_insert_of_notMem hv_not] at hle
  omega

/-- Claim 1.1: `3 ≤ U.card`. -/
private lemma three_le_U_card (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M : Matching (Fin (2 * m + 1))} (hM : IsMaxHMatching p M) :
    3 ≤ (Finset.univ \ matchedSet M).card := by
  by_contra hlt
  have hodd := odd_card_U M
  have h1 : (Finset.univ \ matchedSet M).card = 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨a, b, hblk⟩ := exists_blocking_of_not_stable p hno M
  have hne : a ≠ b := (SimpleGraph.top_adj _ _).1 hblk.1
  by_cases ha : a ∈ matchedSet M
  · exact not_blocking_of_safe_left p (rk_M_le_m_of_mem_matchedSet p hM.1 ha) hblk
  · by_cases hb : b ∈ matchedSet M
    · exact not_blocking_of_safe_right p (rk_M_le_m_of_mem_matchedSet p hM.1 hb) hblk
    · have haU : a ∈ Finset.univ \ matchedSet M := Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ha⟩
      have hbU : b ∈ Finset.univ \ matchedSet M := Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hb⟩
      obtain ⟨u, hu⟩ := Finset.card_eq_one.1 h1
      rw [hu, Finset.mem_singleton] at haU hbU
      exact hne (haU.trans hbU.symm)

private lemma S_card_le (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M : Matching (Fin (2 * m + 1))} (hM : IsMaxHMatching p M) :
    (matchedSet M).card ≤ 2 * m - 2 := by
  have h3 := three_le_U_card p hno hM
  have hsum : (matchedSet M).card + (Finset.univ \ matchedSet M).card = 2 * m + 1 := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (matchedSet M))
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  omega

/-- Key auxiliary lemma for Claim 1.2: extending `M` by any perfect matching `M₂` on `U \ {u}`
forces `vstar u ∈ U \ {u}` and `rk (vstar u) u + m ≤ rk (vstar u) (M₂ (vstar u))`. -/
private lemma U_pm_forces_vstar (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M : Matching (Fin (2 * m + 1))} (hM : IsMaxHMatching p M)
    {u : Fin (2 * m + 1)} (hu : u ∈ Finset.univ \ matchedSet M)
    {M₂ : Matching (Fin (2 * m + 1))}
    (hM₂ : matchedSet M₂ = (Finset.univ \ matchedSet M).erase u) :
    vstar p u ∈ (Finset.univ \ matchedSet M).erase u ∧
      p.partnerRank (vstar p u) u + m ≤ p.partnerRank (vstar p u) (M₂.val (vstar p u)) := by
  have hdisj : Disjoint (matchedSet M) (matchedSet M₂) := by
    rw [hM₂]
    exact Finset.disjoint_sdiff.mono_right (Finset.erase_subset _ _)
  let μ := combineMatchings (matchedSet M) M M₂ Finset.Subset.rfl hdisj
  obtain ⟨a, b, hblk⟩ := exists_blocking_of_not_stable p hno μ
  have haS : a ∉ matchedSet M := by
    intro ha
    have hval : μ.val a = M.val a := by simp [μ, combineMatchings_apply, ha]
    exact not_blocking_of_safe_left p
      (by rw [hval]; exact rk_M_le_m_of_mem_matchedSet p hM.1 ha) hblk
  have hbS : b ∉ matchedSet M := by
    intro hb
    have hval : μ.val b = M.val b := by simp [μ, combineMatchings_apply, hb]
    exact not_blocking_of_safe_right p
      (by rw [hval]; exact rk_M_le_m_of_mem_matchedSet p hM.1 hb) hblk
  have haU : a ∈ Finset.univ \ matchedSet M := Finset.mem_sdiff.2 ⟨Finset.mem_univ _, haS⟩
  have hbU : b ∈ Finset.univ \ matchedSet M := Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hbS⟩
  have hnonH : ¬ (HGraph p).Adj a b := U_indep p hM haU hbU
  have hfix : ∀ v ∈ Finset.univ \ matchedSet M, μ.val v = v ↔ v = u := by
    intro v hv
    have hvS : v ∉ matchedSet M := (Finset.mem_sdiff.1 hv).2
    have hμv : μ.val v = M₂.val v := by simp [μ, combineMatchings_apply, hvS]
    rw [hμv]
    constructor
    · intro h
      have hv_not : v ∉ matchedSet M₂ := by rw [mem_matchedSet]; exact not_not.2 h
      rw [hM₂, Finset.mem_erase, not_and_or] at hv_not
      rcases hv_not with hvu | hnotU
      · exact not_not.1 hvu
      · exact absurd hv hnotU
    · intro hvu
      rw [hvu]
      have : u ∉ matchedSet M₂ := by rw [hM₂]; simp
      rwa [mem_matchedSet, not_not] at this
  by_cases hau : a = u
  · subst hau
    have hbu : b ≠ a := ((SimpleGraph.top_adj _ _).1 hblk.1).symm
    have ha_fix : μ.val a = a := (hfix a haU).2 rfl
    have hb_mat : μ.val b ≠ b := fun h => hbu ((hfix b hbU).1 h)
    obtain ⟨hbv, hrk⟩ := blocking_single_matched_non_H p hnonH ha_fix hb_mat hblk
    have hμb : μ.val b = M₂.val b := by simp [μ, combineMatchings_apply, hbS]
    rw [hμb] at hrk
    rw [← hbv]
    exact ⟨Finset.mem_erase.2 ⟨hbu, hbU⟩, hrk⟩
  · by_cases hbu : b = u
    · subst hbu
      have hab : a ≠ b := (SimpleGraph.top_adj _ _).1 hblk.1
      have hb_fix : μ.val b = b := (hfix b hbU).2 rfl
      have ha_mat : μ.val a ≠ a := fun h => hab ((hfix a haU).1 h)
      obtain ⟨hav, hrk⟩ := blocking_single_matched_non_H p (fun h => hnonH h.symm)
        hb_fix ha_mat (blocking_symm p hblk)
      have hμa : μ.val a = M₂.val a := by simp [μ, combineMatchings_apply, haS]
      rw [hμa] at hrk
      rw [← hav]
      exact ⟨Finset.mem_erase.2 ⟨hab, haU⟩, hrk⟩
    · exact absurd hblk (not_blocking_matched_matched_non_H p hnonH
        (fun h => hau ((hfix a haU).1 h)) (fun h => hbu ((hfix b hbU).1 h)))

private lemma even_card_U_erase (M : Matching (Fin (2 * m + 1))) {u : Fin (2 * m + 1)}
    (hu : u ∈ Finset.univ \ matchedSet M) :
    Even ((Finset.univ \ matchedSet M).erase u).card := by
  obtain ⟨k, hk⟩ := odd_card_U M
  rw [Finset.card_erase_of_mem hu]
  exact ⟨k, by omega⟩

/-- Claim 1.2 (Part 1): `vstar` maps `U` into `U`, and for `u ∈ U`, `z ∈ U \ {u, vstar u}`,
`rk (vstar u) u + m ≤ rk (vstar u) z`. -/
private lemma vstar_mem_U (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M : Matching (Fin (2 * m + 1))} (hM : IsMaxHMatching p M)
    {u : Fin (2 * m + 1)} (hu : u ∈ Finset.univ \ matchedSet M) :
    vstar p u ∈ Finset.univ \ matchedSet M := by
  obtain ⟨M₂, hM₂⟩ := exists_pm_on_even _ (even_card_U_erase M hu)
  exact Finset.erase_subset _ _ (U_pm_forces_vstar p hno hM hu hM₂).1

private lemma rk_vstar_u_add_m_le (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M : Matching (Fin (2 * m + 1))} (hM : IsMaxHMatching p M)
    {u z : Fin (2 * m + 1)}
    (hu : u ∈ Finset.univ \ matchedSet M) (hz : z ∈ Finset.univ \ matchedSet M)
    (hzu : z ≠ u) (hzv : z ≠ vstar p u) :
    p.partnerRank (vstar p u) u + m ≤ p.partnerRank (vstar p u) z := by
  have hvU : vstar p u ∈ Finset.univ \ matchedSet M := vstar_mem_U p hno hM hu
  have hvu : vstar p u ≠ u := vstar_ne_self hm p u
  have hv_er : vstar p u ∈ (Finset.univ \ matchedSet M).erase u := Finset.mem_erase.2 ⟨hvu, hvU⟩
  have hz_er : z ∈ (Finset.univ \ matchedSet M).erase u := Finset.mem_erase.2 ⟨hzu, hz⟩
  obtain ⟨M₂, hM₂, hpair⟩ := exists_pm_on_even_pair _ (even_card_U_erase M hu) hv_er hz_er hzv.symm
  have h := (U_pm_forces_vstar p hno hM hu hM₂).2
  rwa [hpair] at h

/-- Claim 1.2 (Part 2): `vstar` is injective and bijective on `U`, with no 2-cycles. -/
private lemma vstar_injOn_U (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M : Matching (Fin (2 * m + 1))} (hM : IsMaxHMatching p M) :
    Set.InjOn (vstar p) ((Finset.univ \ matchedSet M : Finset (Fin (2 * m + 1))) : Set (Fin (2 * m + 1))) := by
  intro u₁ hu₁ u₂ hu₂ heq
  by_contra hne
  have h1 := rk_vstar_u_add_m_le hm p hno hM hu₁ hu₂ (Ne.symm hne) (by
    rw [heq]; exact (vstar_ne_self hm p u₂).symm)
  have h2 := rk_vstar_u_add_m_le hm p hno hM hu₂ hu₁ hne (by
    rw [← heq]; exact (vstar_ne_self hm p u₁).symm)
  rw [heq] at h1
  omega

private lemma vstar_surjOn_U (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M : Matching (Fin (2 * m + 1))} (hM : IsMaxHMatching p M)
    {w : Fin (2 * m + 1)} (hw : w ∈ Finset.univ \ matchedSet M) :
    ∃ u ∈ Finset.univ \ matchedSet M, vstar p u = w := by
  let U := Finset.univ \ matchedSet M
  have himg_sub : U.image (vstar p) ⊆ U := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    exact vstar_mem_U p hno hM hu
  have hcard : (U.image (vstar p)).card = U.card :=
    Finset.card_image_of_injOn (vstar_injOn_U hm p hno hM)
  have heq : U.image (vstar p) = U := Finset.eq_of_subset_of_card_le himg_sub (by omega)
  have hw' : w ∈ U.image (vstar p) := by rw [heq]; exact hw
  exact Finset.mem_image.1 hw'

private lemma vstar_no_two_cycle (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M : Matching (Fin (2 * m + 1))} (hM : IsMaxHMatching p M)
    {u : Fin (2 * m + 1)} (hu : u ∈ Finset.univ \ matchedSet M) :
    vstar p (vstar p u) ≠ u := by
  intro h2
  let U := Finset.univ \ matchedSet M
  have h3 := three_le_U_card p hno hM
  have hcard : ((U.erase u).erase (vstar p u)).card ≥ 1 := by
    have hvU : vstar p u ∈ U := vstar_mem_U p hno hM hu
    have hvu : vstar p u ≠ u := vstar_ne_self hm p u
    have hv' : vstar p u ∈ U.erase u := Finset.mem_erase.2 ⟨hvu, hvU⟩
    rw [Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hu]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.1 (by omega : 0 < ((U.erase u).erase (vstar p u)).card)
  simp only [Finset.mem_erase] at hz
  have hrk := rk_vstar_u_add_m_le hm p hno hM hu hz.2.2 hz.2.1 hz.1
  have hrwu : p.partnerRank (vstar p u) u = m + 1 := by
    simpa [h2] using rk_vstar p (vstar p u)
  have hle := rk_le_two_mul_of_ne p hz.1
  omega

/-- Claim 1.2 (Part 3): For `u, w ∈ U` with `vstar u = w`, `rk w u = 1`, and for all
`z ∈ U \ {u, w}`, `m + 1 ≤ rk w z`. -/
private lemma rk_vstar_preimage_eq_one (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M : Matching (Fin (2 * m + 1))} (hM : IsMaxHMatching p M)
    {u : Fin (2 * m + 1)} (hu : u ∈ Finset.univ \ matchedSet M) :
    p.partnerRank (vstar p u) u = 1 := by
  have hvU : vstar p u ∈ Finset.univ \ matchedSet M := vstar_mem_U p hno hM hu
  have hvvU : vstar p (vstar p u) ∈ Finset.univ \ matchedSet M := vstar_mem_U p hno hM hvU
  have hne1 : vstar p (vstar p u) ≠ u := vstar_no_two_cycle hm p hno hM hu
  have hne2 : vstar p (vstar p u) ≠ vstar p u := vstar_ne_self hm p (vstar p u)
  have h := rk_vstar_u_add_m_le hm p hno hM hu hvvU hne1 hne2
  rw [rk_vstar] at h
  have hpos := rk_pos p (vstar p u) u
  omega

private lemma rk_ge_succ_of_U (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M : Matching (Fin (2 * m + 1))} (hM : IsMaxHMatching p M)
    {u z : Fin (2 * m + 1)}
    (hu : u ∈ Finset.univ \ matchedSet M) (hz : z ∈ Finset.univ \ matchedSet M)
    (hzu : z ≠ u) (hzv : z ≠ vstar p u) :
    m + 1 ≤ p.partnerRank (vstar p u) z := by
  have h1 := rk_vstar_u_add_m_le hm p hno hM hu hz hzu hzv
  have h2 := rk_vstar_preimage_eq_one hm p hno hM hu
  omega

/-- Claim 1.2 (Part 4): `m - 1 ≤ S.card`. -/
private lemma m_sub_one_le_S_card (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M : Matching (Fin (2 * m + 1))} (hM : IsMaxHMatching p M) :
    m - 1 ≤ (matchedSet M).card := by
  have h3 := three_le_U_card p hno hM
  obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (Finset.univ \ matchedSet M).card)
  have hsub : Finset.univ.filter (fun j => 2 ≤ p.partnerRank (vstar p u) j ∧ p.partnerRank (vstar p u) j ≤ m) ⊆
      matchedSet M := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_contra hjS
    have hjU : j ∈ Finset.univ \ matchedSet M := Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hjS⟩
    by_cases hju : j = u
    · subst hju
      have := rk_vstar_preimage_eq_one hm p hno hM hu
      omega
    · by_cases hjw : j = vstar p u
      · subst hjw
        have := p.partnerRank_self (vstar p u)
        omega
      · have := rk_ge_succ_of_U hm p hno hM hu hjU hju hjw
        omega
  have hcard_le := Finset.card_le_card hsub
  have hfilt :
      (Finset.univ.filter (fun j => 2 ≤ p.partnerRank (vstar p u) j ∧ p.partnerRank (vstar p u) j ≤ m)).card + 1 =
        m := by
    have hdisj : Disjoint
        (Finset.univ.filter (fun j => 2 ≤ p.partnerRank (vstar p u) j ∧ p.partnerRank (vstar p u) j ≤ m))
        ({u} : Finset (Fin (2 * m + 1))) := by
      rw [Finset.disjoint_singleton_right, Finset.mem_filter]
      intro h
      have := rk_vstar_preimage_eq_one hm p hno hM hu
      omega
    have hunion :
        Finset.univ.filter (fun j => 2 ≤ p.partnerRank (vstar p u) j ∧ p.partnerRank (vstar p u) j ≤ m) ∪ {u} =
        Finset.univ.filter (fun j => p.partnerRank (vstar p u) j ≤ m) := by
      ext j
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro (⟨_, h2⟩ | rfl)
        · exact h2
        · have := rk_vstar_preimage_eq_one hm p hno hM hu; omega
      · intro hle
        by_cases hju : j = u
        · exact Or.inr hju
        · refine Or.inl ⟨?_, hle⟩
          have h1 : p.partnerRank (vstar p u) j ≠ 1 := by
            intro h
            exact hju (rk_inj p (vstar p u) (h.trans (rk_vstar_preimage_eq_one hm p hno hM hu).symm))
          have := rk_pos p (vstar p u) j
          omega
    have hcm := card_filter_rk_le p (vstar p u) m (by omega)
    rw [← hunion, Finset.card_union_of_disjoint hdisj, Finset.card_singleton] at hcm
    exact hcm
  omega

/-- Claim 1.3: `U` is completely isolated in `H`. -/
private lemma U_isolated (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M : Matching (Fin (2 * m + 1))} (hM : IsMaxHMatching p M)
    {u : Fin (2 * m + 1)} (hu : u ∈ Finset.univ \ matchedSet M) (x : Fin (2 * m + 1)) :
    ¬ (HGraph p).Adj u x := by
  intro hadj
  have hxS : x ∈ matchedSet M := by
    by_contra hx
    exact U_indep p hM hu (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx⟩) hadj
  let y := M.val x
  have hxy : y ≠ x := (mem_matchedSet M x).1 hxS
  have hyS : y ∈ matchedSet M := matchedSet_map M hxS
  have huS : u ∉ matchedSet M := (Finset.mem_sdiff.1 hu).2
  have huy : u ≠ y := fun h => huS (h ▸ hyS)
  have hux : u ≠ x := hadj.1
  let M_er := eraseEdge M x y rfl
  have hM_er_H : IsHMatching p M_er := isAcceptable_eraseEdge M hM.1 rfl
  have hu_fix : M_er.val u = u := by
    rw [eraseEdge_apply]
    split_ifs with h
    · rfl
    · rwa [mem_matchedSet, not_not] at huS
  have hx_fix : M_er.val x = x := by simp [M_er, eraseEdge_apply]
  let M' := addEdge M_er u x hu_fix hx_fix
  have hM'H : IsHMatching p M' := isAcceptable_addEdge M_er hM_er_H hu_fix hx_fix hadj
  have hms' : matchedSet M' = insert u ((matchedSet M).erase y) := by
    rw [matchedSet_addEdge M_er hux hu_fix hx_fix, matchedSet_eraseEdge M rfl]
    ext z
    simp only [Finset.mem_insert, Finset.mem_erase]
    by_cases hzu : z = u
    · simp [hzu]
    · by_cases hzx : z = x
      · simp [hzx, hxy.symm, hxS]
      · by_cases hzy : z = y
        · simp [hzy, huy.symm, hxy, y]
        · simp [hzu, hzx, hzy, y]
  have hcard' : (matchedSet M').card = (matchedSet M).card := by
    rw [hms', Finset.card_insert_of_notMem (by simp [huS]), Finset.card_erase_of_mem hyS]
    have hpos : 0 < (matchedSet M).card := Finset.card_pos.2 ⟨y, hyS⟩
    omega
  have hM'max : IsMaxHMatching p M' := ⟨hM'H, fun M'' hM'' => by rw [hcard']; exact hM.2 M'' hM''⟩
  let w := vstar p u
  have hwU : w ∈ Finset.univ \ matchedSet M := vstar_mem_U p hno hM hu
  have hwu : w ≠ u := vstar_ne_self hm p u
  have hwU' : w ∈ Finset.univ \ matchedSet M' := by
    rw [Finset.mem_sdiff, hms']
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [hwu, (Finset.mem_sdiff.1 hwU).2]
  obtain ⟨u', hu'U', hvstar_u'⟩ := vstar_surjOn_U hm p hno hM'max hwU'
  have hrk1 : p.partnerRank w u = 1 := rk_vstar_preimage_eq_one hm p hno hM hu
  have hrk2 : p.partnerRank w u' = 1 := by
    rw [← hvstar_u']; exact rk_vstar_preimage_eq_one hm p hno hM'max hu'U'
  have heq : u' = u := rk_inj p w (hrk2.trans hrk1.symm)
  rw [heq, Finset.mem_sdiff, hms'] at hu'U'
  exact hu'U'.2 (Finset.mem_insert_self u _)

end Step1

/-! ### Step 2 & Step 3: Neutralizing matchings, Master Lemma, `S_ge2`, and connected components -/

section Step2And3

/-- Claim 2.1 (Neutralizing): For `u ∈ U` and `w ∈ S`, there exists a perfect matching `M₂`
on `U.erase u` such that `vstar w` (if in `U.erase u`) cannot `m`-block with `w`. -/
private lemma exists_neutralizing_pm (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {u w : Fin (2 * m + 1)}
    (hu : u ∈ Finset.univ \ matchedSet M₁) (hw : w ∈ matchedSet M₁) :
    ∃ M₂ : Matching (Fin (2 * m + 1)),
      matchedSet M₂ = (Finset.univ \ matchedSet M₁).erase u ∧
      ∀ v ∈ (Finset.univ \ matchedSet M₁).erase u,
        v = vstar p w → ¬ (p.partnerRank v w + m ≤ p.partnerRank v (M₂.val v)) := by
  let U := Finset.univ \ matchedSet M₁
  have hev := even_card_U_erase M₁ hu
  by_cases hvw : vstar p w ∈ U.erase u
  · let v := vstar p w
    have hvU : v ∈ U := Finset.erase_subset _ _ hvw
    obtain ⟨f, hfU, hfv⟩ := vstar_surjOn_U hm p hno hM₁ hvU
    have hrf : p.partnerRank v f = 1 := by
      rw [← hfv]; exact rk_vstar_preimage_eq_one hm p hno hM₁ hfU
    by_cases hfu : f = u
    · -- Pair `v` with `vstar v`
      let z := vstar p v
      have hzU : z ∈ U := vstar_mem_U p hno hM₁ hvU
      have hzv : z ≠ v := vstar_ne_self hm p v
      have hzu : z ≠ u := by
        rw [← hfu]; dsimp [z]; rw [← hfv]
        exact vstar_no_two_cycle hm p hno hM₁ hfU
      have hz_er : z ∈ U.erase u := Finset.mem_erase.2 ⟨hzu, hzU⟩
      obtain ⟨M₂, hM₂, hpair⟩ := exists_pm_on_even_pair (U.erase u) hev hvw hz_er hzv.symm
      refine ⟨M₂, hM₂, fun v' _ hv' => ?_⟩
      subst hv'
      rw [hpair, rk_vstar]
      have hwf : w ≠ f := fun h => (Finset.mem_sdiff.1 hfU).2 (h ▸ hw)
      have hrw_ne1 : p.partnerRank v w ≠ 1 := fun h => hwf (rk_inj p v (h.trans hrf.symm))
      have hrw_pos := rk_pos p v w
      dsimp [v] at hrw_ne1 hrw_pos
      omega
    · -- Pair `v` with `f`
      have hfv_ne : f ≠ v := by
        rw [← hfv]; exact (vstar_ne_self hm p f).symm
      have hf_er : f ∈ U.erase u := Finset.mem_erase.2 ⟨hfu, hfU⟩
      obtain ⟨M₂, hM₂, hpair⟩ := exists_pm_on_even_pair (U.erase u) hev hvw hf_er hfv_ne.symm
      refine ⟨M₂, hM₂, fun v' _ hv' => ?_⟩
      subst hv'
      rw [hpair, hrf]
      have := rk_pos p v w
      omega
  · obtain ⟨M₂, hM₂⟩ := exists_pm_on_even (U.erase u) hev
    exact ⟨M₂, hM₂, fun v hv h => absurd (h ▸ hv) hvw⟩

private noncomputable def Rset (p : CompleteProfile (2 * m + 1)) (M₁ : Matching (Fin (2 * m + 1)))
    (x : Fin (2 * m + 1)) : Finset (Fin (2 * m + 1)) := by
  classical
  exact (matchedSet M₁).filter (fun w =>
    w ≠ x ∧ ∃ M' : Matching (Fin (2 * m + 1)),
      IsHMatching p M' ∧ matchedSet M' = ((matchedSet M₁).erase x).erase w)

private lemma mem_Rset (p : CompleteProfile (2 * m + 1)) {M₁ : Matching (Fin (2 * m + 1))}
    {x w : Fin (2 * m + 1)} :
    w ∈ Rset p M₁ x ↔
      w ∈ matchedSet M₁ ∧ w ≠ x ∧
      ∃ M' : Matching (Fin (2 * m + 1)),
        IsHMatching p M' ∧ matchedSet M' = ((matchedSet M₁).erase x).erase w := by
  classical
  simp [Rset]

private lemma M1_mem_Rset (p : CompleteProfile (2 * m + 1)) {M₁ : Matching (Fin (2 * m + 1))}
    (hM₁ : IsMaxHMatching p M₁) {x : Fin (2 * m + 1)} (hx : x ∈ matchedSet M₁) :
    M₁.val x ∈ Rset p M₁ x := by
  rw [mem_Rset]
  refine ⟨matchedSet_map M₁ hx, (mem_matchedSet M₁ x).1 hx,
    eraseEdge M₁ x (M₁.val x) rfl, isAcceptable_eraseEdge M₁ hM₁.1 rfl,
    matchedSet_eraseEdge M₁ rfl⟩

private lemma mem_Rset_symm (p : CompleteProfile (2 * m + 1)) {M₁ : Matching (Fin (2 * m + 1))}
    {x w : Fin (2 * m + 1)} (hx : x ∈ matchedSet M₁) :
    w ∈ Rset p M₁ x ↔ x ∈ Rset p M₁ w := by
  simp only [mem_Rset]
  constructor
  · rintro ⟨hw, hne, M', hM'H, hms⟩
    refine ⟨hx, hne.symm, M', hM'H, ?_⟩
    rw [hms, Finset.erase_right_comm]
  · rintro ⟨_, hne, M', hM'H, hms⟩
    have hw : w ∈ matchedSet M₁ := by
      by_contra hw'
      have hcard : (matchedSet M').card = (matchedSet M₁).card - 1 := by
        rw [hms, Finset.erase_eq_of_notMem hw', Finset.card_erase_of_mem hx]
      have hev1 := even_card_matchedSet M₁
      have hev2 := even_card_matchedSet M'
      have hpos : 0 < (matchedSet M₁).card := Finset.card_pos.2 ⟨x, hx⟩
      obtain ⟨k₁, hk₁⟩ := hev1
      obtain ⟨k₂, hk₂⟩ := hev2
      omega
    refine ⟨hw, hne.symm, M', hM'H, ?_⟩
    rw [hms, Finset.erase_right_comm]

/-- Claim 2.2 (Master Lemma): For `x ∈ S`, `w ∈ R x`, `u ∈ U`, either
(A) `rk x w + m ≤ rk x u ∧ rk w x ≤ m + 1` or
(B) `u = vstar w ∧ rk u w ≤ m ∧ rk u w + m ≤ rk u x`. -/
private lemma master_lemma (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x w u : Fin (2 * m + 1)}
    (hx : x ∈ matchedSet M₁) (hw : w ∈ Rset p M₁ x)
    (hu : u ∈ Finset.univ \ matchedSet M₁) :
    (p.partnerRank x w + m ≤ p.partnerRank x u ∧ p.partnerRank w x ≤ m + 1) ∨
      (u = vstar p w ∧ p.partnerRank u w ≤ m ∧ p.partnerRank u w + m ≤ p.partnerRank u x) := by
  obtain ⟨hwS, hwx, M', hM'H, hM'ms⟩ := (mem_Rset p).1 hw
  obtain ⟨M₂, hM₂ms, hM₂neut⟩ := exists_neutralizing_pm hm p hno hM₁ hu hwS
  have hdisj1 : Disjoint (matchedSet M') (matchedSet M₂) := by
    rw [hM'ms, hM₂ms]
    exact Finset.disjoint_sdiff.mono
      ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
      (Finset.erase_subset _ _)
  let μ₀ := combineMatchings (matchedSet M') M' M₂ Finset.Subset.rfl hdisj1
  have hμ₀ms : matchedSet μ₀ = matchedSet M' ∪ matchedSet M₂ :=
    matchedSet_combineMatchings _ _ _ Finset.Subset.rfl hdisj1
  have hx_fix : μ₀.val x = x := by
    by_contra h
    have hx_in : x ∈ matchedSet M' ∪ matchedSet M₂ := hμ₀ms ▸ (mem_matchedSet μ₀ x).2 h
    rw [hM'ms, hM₂ms] at hx_in
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff] at hx_in
    rcases hx_in with ⟨_, hxx, _⟩ | ⟨_, _, hxnot⟩
    · exact hxx rfl
    · exact hxnot hx
  have hu_fix : μ₀.val u = u := by
    by_contra h
    have hu_in : u ∈ matchedSet M' ∪ matchedSet M₂ := hμ₀ms ▸ (mem_matchedSet μ₀ u).2 h
    rw [hM'ms, hM₂ms] at hu_in
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff] at hu_in
    rcases hu_in with ⟨_, _, huS⟩ | ⟨huu, _⟩
    · exact (Finset.mem_sdiff.1 hu).2 huS
    · exact huu rfl
  let μ := addEdge μ₀ x u hx_fix hu_fix
  have hxu : x ≠ u := fun h => (Finset.mem_sdiff.1 hu).2 (h ▸ hx)
  have hwu : w ≠ u := fun h => (Finset.mem_sdiff.1 hu).2 (h ▸ hwS)
  have hμ_M' : ∀ v ∈ matchedSet M', μ.val v = M'.val v := by
    intro v hv
    have hvx : v ≠ x := by rw [hM'ms] at hv; exact (Finset.mem_erase.1 (Finset.mem_erase.1 hv).2).1
    have hvu : v ≠ u := fun h => (Finset.mem_sdiff.1 hu).2 (by
      rw [hM'ms] at hv; exact h ▸ (Finset.erase_subset _ _ (Finset.erase_subset _ _ hv)))
    simp [μ, addEdge_apply, hvx, hvu, μ₀, combineMatchings_apply, hv]
  have hμ_M₂ : ∀ v ∈ (Finset.univ \ matchedSet M₁).erase u, μ.val v = M₂.val v := by
    intro v hv
    have hvu : v ≠ u := (Finset.mem_erase.1 hv).1
    have hvnotS : v ∉ matchedSet M₁ := (Finset.mem_sdiff.1 (Finset.mem_erase.1 hv).2).2
    have hvx : v ≠ x := fun h => hvnotS (h ▸ hx)
    have hvnotM' : v ∉ matchedSet M' := by
      rw [hM'ms]; intro h; exact hvnotS (Finset.erase_subset _ _ (Finset.erase_subset _ _ h))
    simp [μ, addEdge_apply, hvx, hvu, μ₀, combineMatchings_apply, hvnotM']
  have hμx : μ.val x = u := by simp [μ, addEdge_apply]
  have hμu : μ.val u = x := by simp [μ, addEdge_apply, hxu.symm]
  have hμw : μ.val w = w := by
    have hwnotM' : w ∉ matchedSet M' := by rw [hM'ms]; simp
    have hwnotM₂ : w ∉ matchedSet M₂ := by rw [hM₂ms]; simp [hwS]
    have hμ₀w : μ₀.val w = w := by
      simp only [μ₀, combineMatchings_apply, hwnotM', ↓reduceIte]
      rwa [mem_matchedSet, not_not] at hwnotM₂
    simp [μ, addEdge_apply, hwx, hwu, hμ₀w]
  have hμ_single : ∀ v : Fin (2 * m + 1), μ.val v = v ↔ v = w := by
    intro v
    constructor
    · intro hv
      by_contra hvw
      by_cases hvS : v ∈ matchedSet M₁
      · by_cases hvx : v = x
        · subst hvx; rw [hμx] at hv; exact hxu hv.symm
        · have hvM' : v ∈ matchedSet M' := by
            rw [hM'ms]; exact Finset.mem_erase.2 ⟨hvw, Finset.mem_erase.2 ⟨hvx, hvS⟩⟩
          rw [hμ_M' v hvM'] at hv
          exact (mem_matchedSet M' v).1 hvM' hv
      · by_cases hvu : v = u
        · subst hvu; rw [hμu] at hv; exact hxu hv
        · have hvM₂ : v ∈ (Finset.univ \ matchedSet M₁).erase u :=
            Finset.mem_erase.2 ⟨hvu, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hvS⟩⟩
          rw [hμ_M₂ v hvM₂] at hv
          exact (mem_matchedSet M₂ v).1 (hM₂ms ▸ hvM₂) hv
    · rintro rfl; exact hμw
  obtain ⟨a, b, hblk⟩ := exists_blocking_of_not_stable p hno μ
  have ha_notM' : a ∉ matchedSet M' := by
    intro ha
    exact not_blocking_of_safe_left p
      (by rw [hμ_M' a ha]; exact rk_M_le_m_of_mem_matchedSet p hM'H ha) hblk
  have hb_notM' : b ∉ matchedSet M' := by
    intro hb
    exact not_blocking_of_safe_right p
      (by rw [hμ_M' b hb]; exact rk_M_le_m_of_mem_matchedSet p hM'H hb) hblk
  by_cases hwx_pair : (a = w ∧ b = x) ∨ (a = x ∧ b = w)
  · left
    have hblk' : IsKBlockingPair ⊤ p.partnerRank m μ x w := by
      rcases hwx_pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact blocking_symm p hblk
      · exact hblk
    rcases hblk' with ⟨_, _, hxblk, hwblk⟩
    rw [hμx] at hxblk
    rw [hμw, p.partnerRank_self] at hwblk
    exact ⟨hxblk, by omega⟩
  · have hmem_rest : ∀ v, v ∉ matchedSet M' →
        v = w ∨ v = x ∨ v ∈ Finset.univ \ matchedSet M₁ := by
      intro v hv
      by_cases hvS : v ∈ matchedSet M₁
      · by_cases hvw : v = w
        · exact Or.inl hvw
        · by_cases hvx : v = x
          · exact Or.inr (Or.inl hvx)
          · exfalso; apply hv; rw [hM'ms]
            exact Finset.mem_erase.2 ⟨hvw, Finset.mem_erase.2 ⟨hvx, hvS⟩⟩
      · exact Or.inr (Or.inr (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hvS⟩))
    have hnonH : ¬ (HGraph p).Adj a b := by
      have hab_ne : a ≠ b := (SimpleGraph.top_adj _ _).1 hblk.1
      rcases hmem_rest a ha_notM' with haw | hax | haU
      · rcases hmem_rest b hb_notM' with hbw | hbx | hbU
        · exact absurd (haw.trans hbw.symm) hab_ne
        · exact absurd (Or.inl ⟨haw, hbx⟩) hwx_pair
        · exact fun h => U_isolated hm p hno hM₁ hbU a h.symm
      · rcases hmem_rest b hb_notM' with hbw | hbx | hbU
        · exact absurd (Or.inr ⟨hax, hbw⟩) hwx_pair
        · exact absurd (hax.trans hbx.symm) hab_ne
        · exact fun h => U_isolated hm p hno hM₁ hbU a h.symm
      · exact U_isolated hm p hno hM₁ haU b
    have hone_w : ∃ v, v ≠ w ∧ IsKBlockingPair ⊤ p.partnerRank m μ w v ∧
        v ∉ matchedSet M' ∧ v ≠ x := by
      have hab_ne : a ≠ b := (SimpleGraph.top_adj _ _).1 hblk.1
      by_cases haw : a = w
      · subst haw
        have hbx : b ≠ x := fun h => hwx_pair (Or.inl ⟨rfl, h⟩)
        exact ⟨b, hab_ne.symm, hblk, hb_notM', hbx⟩
      · by_cases hbw : b = w
        · subst hbw
          have hax : a ≠ x := fun h => hwx_pair (Or.inr ⟨h, rfl⟩)
          exact ⟨a, hab_ne, blocking_symm p hblk, ha_notM', hax⟩
        · exact absurd hblk (not_blocking_matched_matched_non_H p hnonH
            (fun h => haw ((hμ_single a).1 h)) (fun h => hbw ((hμ_single b).1 h)))
    obtain ⟨v, hvw, hblkv, hv_notM', hvx⟩ := hone_w
    have hvU : v ∈ Finset.univ \ matchedSet M₁ := by
      rcases hmem_rest v hv_notM' with h | h | h
      · exact absurd h hvw
      · exact absurd h hvx
      · exact h
    have hv_nonH : ¬ (HGraph p).Adj w v := fun h => U_isolated hm p hno hM₁ hvU w h.symm
    obtain ⟨hv_vstar, hrkv⟩ := blocking_single_matched_non_H p hv_nonH hμw
      (fun h => hvw ((hμ_single v).1 h)) hblkv
    by_cases hvu : v = u
    · subst hvu
      rw [hμu] at hrkv
      right
      have hle : p.partnerRank v x ≤ 2 * m := rk_le_two_mul_of_ne p hxu
      exact ⟨hv_vstar, by omega, hrkv⟩
    · exfalso
      have hv_er : v ∈ (Finset.univ \ matchedSet M₁).erase u := Finset.mem_erase.2 ⟨hvu, hvU⟩
      rw [hμ_M₂ v hv_er] at hrkv
      exact hM₂neut v hv_er hv_vstar hrkv

/-! ### Step 3: Vertices with `|R(w)| ≥ 2` and connected components of `H[S]` -/

private noncomputable def Sge2 (p : CompleteProfile (2 * m + 1)) (M₁ : Matching (Fin (2 * m + 1))) :
    Finset (Fin (2 * m + 1)) := by
  classical
  exact (matchedSet M₁).filter (fun w => 2 ≤ (Rset p M₁ w).card)

private lemma mem_Sge2 (p : CompleteProfile (2 * m + 1)) {M₁ : Matching (Fin (2 * m + 1))}
    {w : Fin (2 * m + 1)} :
    w ∈ Sge2 p M₁ ↔ w ∈ matchedSet M₁ ∧ 2 ≤ (Rset p M₁ w).card := by
  classical
  simp [Sge2]

/-- Claim 3.1: For `w ∈ S_ge2`, we cannot have `vstar w ∈ U` and `rk (vstar w) w ≤ m`. -/
private lemma not_vstar_U_of_Sge2 (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {w : Fin (2 * m + 1)} (hw : w ∈ Sge2 p M₁) :
    ¬ (vstar p w ∈ Finset.univ \ matchedSet M₁ ∧ p.partnerRank (vstar p w) w ≤ m) := by
  rintro ⟨hvU, hrk⟩
  obtain ⟨hwS, hcard⟩ := (mem_Sge2 p).1 hw
  have hgt : ∃ z ∈ Rset p M₁ w, 2 ≤ p.partnerRank w z := by
    obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (Rset p M₁ w).card)
    by_cases h1 : p.partnerRank w z₁ = 1
    · refine ⟨z₂, hz₂, ?_⟩
      have hne1 : p.partnerRank w z₂ ≠ 1 := fun h => hne (rk_inj p w (h1.trans h.symm))
      have := rk_pos p w z₂
      omega
    · refine ⟨z₁, hz₁, ?_⟩
      have := rk_pos p w z₁
      omega
  obtain ⟨z, hz, hrz⟩ := hgt
  rcases master_lemma hm p hno hM₁ hwS hz hvU with ⟨hA, _⟩ | ⟨_, _, hB⟩
  · rw [rk_vstar] at hA
    omega
  · have := rk_pos p (vstar p w) z
    omega

/-- Claim 3.2 (Part 1): For `w ∈ S_ge2`, `x ∈ R w`, and `u ∈ U`, `rk x w + m ≤ rk x u`. -/
private lemma rk_add_m_le_U_of_Sge2 (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {w x u : Fin (2 * m + 1)} (hw : w ∈ Sge2 p M₁) (hx : x ∈ Rset p M₁ w)
    (hu : u ∈ Finset.univ \ matchedSet M₁) :
    p.partnerRank x w + m ≤ p.partnerRank x u := by
  have hxS : x ∈ matchedSet M₁ := ((mem_Rset p).1 hx).1
  have hwx : w ∈ Rset p M₁ x := (mem_Rset_symm p hxS).2 hx
  rcases master_lemma hm p hno hM₁ hxS hwx hu with ⟨hA, _⟩ | ⟨hu_eq, hrk, _⟩
  · exact hA
  · exact absurd ⟨hu_eq ▸ hu, hu_eq ▸ hrk⟩ (not_vstar_U_of_Sge2 hm p hno hM₁ hw)

/-- General counting bound for `q(x, w)` when every `u ∈ U` satisfies `rk x w + m ≤ rk x u`. -/
private lemma rk_add_q_add_m_le_S_card (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x w : Fin (2 * m + 1)} (hx : x ∈ matchedSet M₁)
    (hU : ∀ u ∈ Finset.univ \ matchedSet M₁, p.partnerRank x w + m ≤ p.partnerRank x u) :
    p.partnerRank x w +
        (((matchedSet M₁).erase x).filter (fun y => p.partnerRank x w + m ≤ p.partnerRank x y)).card
        + m ≤ (matchedSet M₁).card := by
  let U := Finset.univ \ matchedSet M₁
  let Q := ((matchedSet M₁).erase x).filter (fun y => p.partnerRank x w + m ≤ p.partnerRank x y)
  have hUpos : U.Nonempty := Finset.card_pos.1 (by have := three_le_U_card p hno hM₁; dsimp [U]; omega)
  obtain ⟨u₀, hu₀⟩ := hUpos
  have hle_2m : p.partnerRank x w + m ≤ 2 * m := by
    have h1 := hU u₀ hu₀
    have h2 : u₀ ≠ x := fun h => (Finset.mem_sdiff.1 hu₀).2 (h ▸ hx)
    have h3 := rk_le_two_mul_of_ne p h2
    omega
  have h1 : 1 ≤ p.partnerRank x w + m := by have := rk_pos p x w; omega
  have h2 : p.partnerRank x w + m ≤ 2 * m + 1 := by omega
  let T := Finset.univ.filter (fun y => p.partnerRank x w + m ≤ p.partnerRank x y)
  have hTcard : T.card = 2 * m + 2 - (p.partnerRank x w + m) :=
    card_filter_rk_ge p x (p.partnerRank x w + m) h1 h2
  have hsub : U ∪ ({x} ∪ Q) ⊆ T := by
    intro y hy
    simp only [Finset.mem_union, Finset.mem_singleton, T, Finset.mem_filter,
      Finset.mem_univ, true_and] at hy ⊢
    rcases hy with hyU | rfl | hyQ
    · exact hU y hyU
    · rw [p.partnerRank_self]; omega
    · exact (Finset.mem_filter.1 hyQ).2
  have hd1 : Disjoint U ({x} ∪ Q) := by
    rw [Finset.disjoint_union_right]
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_singleton_right]; simp [U, hx]
    · exact Finset.disjoint_sdiff.symm.mono_right
        ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _))
  have hd2 : Disjoint ({x} : Finset (Fin (2 * m + 1))) Q := by
    rw [Finset.disjoint_singleton_left]
    simp [Q]
  have hcard_le := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
    Finset.card_singleton, hTcard] at hcard_le
  have hUS : (matchedSet M₁).card + U.card = 2 * m + 1 := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (matchedSet M₁))
    rw [Finset.card_univ, Fintype.card_fin] at this
    dsimp [U]
    omega
  dsimp [Q] at hcard_le
  omega

/-- Counting bound for `q(x, w)` when all `u ∈ U \ {vstar w}` satisfy `rk x w + m ≤ rk x u`
(used for `K_alpha`). -/
private lemma q_add_m_le_S_card_of_except_one (p : CompleteProfile (2 * m + 1))
    {M₁ : Matching (Fin (2 * m + 1))}
    {x w : Fin (2 * m + 1)} (hx : x ∈ matchedSet M₁) (hrw : p.partnerRank x w ≤ m)
    (hU : ∀ u ∈ (Finset.univ \ matchedSet M₁).erase (vstar p w),
      p.partnerRank x w + m ≤ p.partnerRank x u) :
    (((matchedSet M₁).erase x).filter (fun y => p.partnerRank x w + m ≤ p.partnerRank x y)).card
      + m ≤ (matchedSet M₁).card := by
  let U := Finset.univ \ matchedSet M₁
  let U' := U.erase (vstar p w)
  let Q := ((matchedSet M₁).erase x).filter (fun y => p.partnerRank x w + m ≤ p.partnerRank x y)
  have h1 : 1 ≤ p.partnerRank x w + m := by have := rk_pos p x w; omega
  have h2 : p.partnerRank x w + m ≤ 2 * m + 1 := by omega
  let T := Finset.univ.filter (fun y => p.partnerRank x w + m ≤ p.partnerRank x y)
  have hTcard : T.card = 2 * m + 2 - (p.partnerRank x w + m) :=
    card_filter_rk_ge p x (p.partnerRank x w + m) h1 h2
  have hsub : U' ∪ ({x} ∪ Q) ⊆ T := by
    intro y hy
    simp only [Finset.mem_union, Finset.mem_singleton, T, Finset.mem_filter,
      Finset.mem_univ, true_and] at hy ⊢
    rcases hy with hyU' | rfl | hyQ
    · exact hU y hyU'
    · rw [p.partnerRank_self]; omega
    · exact (Finset.mem_filter.1 hyQ).2
  have hd1 : Disjoint U' ({x} ∪ Q) := by
    rw [Finset.disjoint_union_right]
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_singleton_right]
      intro h; exact (Finset.mem_sdiff.1 (Finset.erase_subset _ _ h)).2 hx
    · exact Finset.disjoint_sdiff.symm.mono (Finset.erase_subset _ _)
        ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _))
  have hd2 : Disjoint ({x} : Finset (Fin (2 * m + 1))) Q := by
    rw [Finset.disjoint_singleton_left]; simp [Q]
  have hcard_le := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
    Finset.card_singleton, hTcard] at hcard_le
  have hUS : (matchedSet M₁).card + U.card = 2 * m + 1 := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (matchedSet M₁))
    rw [Finset.card_univ, Fintype.card_fin] at this
    dsimp [U]
    omega
  have hU'card : U.card - 1 ≤ U'.card := by
    dsimp [U']
    by_cases hv : vstar p w ∈ U
    · rw [Finset.card_erase_of_mem hv]
    · rw [Finset.erase_eq_of_notMem hv]; omega
  have hrw_pos := rk_pos p x w
  dsimp [Q] at hcard_le
  omega

/-- Claim 3.2 (Part 2): For `w ∈ S_ge2` and `x ∈ R w`, `rk x w + m ≤ S.card`. -/
private lemma rk_add_m_le_S_card_of_Sge2 (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {w x : Fin (2 * m + 1)} (hw : w ∈ Sge2 p M₁) (hx : x ∈ Rset p M₁ w) :
    p.partnerRank x w + m ≤ (matchedSet M₁).card := by
  have hxS : x ∈ matchedSet M₁ := ((mem_Rset p).1 hx).1
  have h := rk_add_q_add_m_le_S_card p hno hM₁ hxS
    (fun u hu => rk_add_m_le_U_of_Sge2 hm p hno hM₁ hw hx hu)
  omega

/-- Claim 3.3 (Part 1): `x ∈ S_ge2 ↔ 2 ≤ |N_{H[S]}(M₁ x)|`. -/
private lemma mem_Sge2_iff_nbrs (p : CompleteProfile (2 * m + 1))
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x : Fin (2 * m + 1)} (hx : x ∈ matchedSet M₁) :
    x ∈ Sge2 p M₁ ↔
      2 ≤ ((matchedSet M₁).filter (fun z => (HGraph p).Adj (M₁.val x) z)).card := by
  let y := M₁.val x
  have hyS : y ∈ matchedSet M₁ := matchedSet_map M₁ hx
  have hxy : y ≠ x := (mem_matchedSet M₁ x).1 hx
  have hMy : M₁.val y = x := M₁.property x
  have hHad : (HGraph p).Adj y x := (H_adj_of_mem_matchedSet p hM₁.1 hx).symm
  rw [mem_Sge2]
  constructor
  · rintro ⟨_, hcard⟩
    have hyR : y ∈ Rset p M₁ x := M1_mem_Rset p hM₁ hx
    have hpos : 0 < ((Rset p M₁ x).erase y).card := by
      rw [Finset.card_erase_of_mem hyR]; omega
    obtain ⟨w, hw⟩ := Finset.card_pos.1 hpos
    have hwy : w ≠ y := (Finset.mem_erase.1 hw).1
    obtain ⟨hwS, hwx, M', hM'H, hM'ms⟩ := (mem_Rset p).1 (Finset.mem_erase.1 hw).2
    have hyM' : y ∈ matchedSet M' := by
      rw [hM'ms]; exact Finset.mem_erase.2 ⟨hwy.symm, Finset.mem_erase.2 ⟨hxy, hyS⟩⟩
    let z := M'.val y
    have hzM' : z ∈ matchedSet M' := matchedSet_map M' hyM'
    have hzS : z ∈ matchedSet M₁ := by
      rw [hM'ms] at hzM'
      exact Finset.erase_subset _ _ (Finset.erase_subset _ _ hzM')
    have hzx : z ≠ x := by
      rw [hM'ms] at hzM'
      exact (Finset.mem_erase.1 (Finset.mem_erase.1 hzM').2).1
    have hyz : (HGraph p).Adj y z := H_adj_of_mem_matchedSet p hM'H hyM'
    have hx_in : x ∈ (matchedSet M₁).filter (fun z => (HGraph p).Adj y z) :=
      Finset.mem_filter.2 ⟨hx, hHad⟩
    have hz_in : z ∈ (matchedSet M₁).filter (fun z => (HGraph p).Adj y z) :=
      Finset.mem_filter.2 ⟨hzS, hyz⟩
    have hlt : 1 < ((matchedSet M₁).filter (fun z => (HGraph p).Adj y z)).card :=
      Finset.one_lt_card.2 ⟨x, hx_in, z, hz_in, hzx.symm⟩
    dsimp [y] at hlt
    omega
  · intro hcard
    refine ⟨hx, ?_⟩
    have hx_in : x ∈ (matchedSet M₁).filter (fun z => (HGraph p).Adj y z) :=
      Finset.mem_filter.2 ⟨hx, hHad⟩
    have hpos : 0 < (((matchedSet M₁).filter (fun z => (HGraph p).Adj y z)).erase x).card := by
      rw [Finset.card_erase_of_mem hx_in]; dsimp [y]; omega
    obtain ⟨z, hz⟩ := Finset.card_pos.1 hpos
    have hzx : z ≠ x := (Finset.mem_erase.1 hz).1
    have hzS : z ∈ matchedSet M₁ := (Finset.mem_filter.1 (Finset.mem_erase.1 hz).2).1
    have hyz : (HGraph p).Adj y z := (Finset.mem_filter.1 (Finset.mem_erase.1 hz).2).2
    have hzy : z ≠ y := hyz.1.symm
    let w := M₁.val z
    have hwS : w ∈ matchedSet M₁ := matchedSet_map M₁ hzS
    have hwz : w ≠ z := (mem_matchedSet M₁ z).1 hzS
    have hwx : w ≠ x := fun h => hzy (by rw [← M₁.property z]; change M₁.val w = y; rw [h])
    have hwy : w ≠ y := fun h => hzx (by rw [← M₁.property z]; change M₁.val w = x; rw [h, hMy])
    let M_e1 := eraseEdge M₁ x y rfl
    have hM_e1_zw : M_e1.val z = w := by simp [M_e1, eraseEdge_apply, hzx, hzy, w]
    let M_e2 := eraseEdge M_e1 z w hM_e1_zw
    have hy_fix : M_e2.val y = y := by
      simp [M_e2, eraseEdge_apply, hzy.symm, hwy.symm, M_e1]
    have hz_fix : M_e2.val z = z := by simp [M_e2, eraseEdge_apply]
    let M' := addEdge M_e2 y z hy_fix hz_fix
    have hM'H : IsHMatching p M' :=
      isAcceptable_addEdge M_e2
        (isAcceptable_eraseEdge M_e1 (isAcceptable_eraseEdge M₁ hM₁.1 rfl) hM_e1_zw)
        hy_fix hz_fix hyz
    have hM'ms : matchedSet M' = ((matchedSet M₁).erase x).erase w := by
      rw [matchedSet_addEdge M_e2 hzy.symm hy_fix hz_fix,
        matchedSet_eraseEdge M_e1 hM_e1_zw, matchedSet_eraseEdge M₁ rfl]
      ext v
      simp only [Finset.mem_insert, Finset.mem_erase]
      by_cases hvy : v = y
      · simp [hvy, hwy.symm, hxy, hyS]
      · by_cases hvz : v = z
        · simp [hvz, hwz.symm, hzx, hzS]
        · by_cases hvw : v = w
          · simp [hvw, hwy, hwz]
          · by_cases hvx : v = x
            · simp [hvx, hxy.symm, hzx.symm]
            · simp [hvy, hvz, hvw, hvx, y]
    have hwR : w ∈ Rset p M₁ x := (mem_Rset p).2 ⟨hwS, hwx, M', hM'H, hM'ms⟩
    have hyR : y ∈ Rset p M₁ x := M1_mem_Rset p hM₁ hx
    have hlt : 1 < (Rset p M₁ x).card := Finset.one_lt_card.2 ⟨y, hyR, w, hwR, hwy.symm⟩
    omega

/-- Claim 3.3 (Part 2): If `x, w ∈ S_ge2` and `w ∈ R x`, then `H.Adj x w`. -/
private lemma H_adj_of_Sge2_Rset (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x w : Fin (2 * m + 1)} (hx : x ∈ Sge2 p M₁) (hw : w ∈ Sge2 p M₁)
    (hwr : w ∈ Rset p M₁ x) : (HGraph p).Adj x w := by
  have hxS : x ∈ matchedSet M₁ := ((mem_Sge2 p).1 hx).1
  have hwx : w ≠ x := ((mem_Rset p).1 hwr).2.1
  have hxr : x ∈ Rset p M₁ w := (mem_Rset_symm p hxS).1 hwr
  have h1 := rk_add_m_le_S_card_of_Sge2 hm p hno hM₁ hw hxr
  have h2 := rk_add_m_le_S_card_of_Sge2 hm p hno hM₁ hx hwr
  have hSle := S_card_le p hno hM₁
  exact ⟨hwx.symm, by omega, by omega⟩

/-- The induced subgraph of `H` on `S`, kept as a graph on `Fin (2*m+1)` for convenience. -/
private def HSGraph (p : CompleteProfile (2 * m + 1)) (M₁ : Matching (Fin (2 * m + 1))) :
    SimpleGraph (Fin (2 * m + 1)) where
  Adj u v := u ∈ matchedSet M₁ ∧ v ∈ matchedSet M₁ ∧ (HGraph p).Adj u v
  symm := ⟨by rintro u v ⟨hu, hv, hadj⟩; exact ⟨hv, hu, hadj.symm⟩⟩
  loopless := ⟨by intro u h; exact h.2.2.1 rfl⟩

private noncomputable def comp (p : CompleteProfile (2 * m + 1)) (M₁ : Matching (Fin (2 * m + 1)))
    (x : Fin (2 * m + 1)) : Finset (Fin (2 * m + 1)) := by
  classical
  exact (matchedSet M₁).filter (fun y => (HSGraph p M₁).Reachable x y)

private lemma mem_comp (p : CompleteProfile (2 * m + 1)) {M₁ : Matching (Fin (2 * m + 1))}
    {x y : Fin (2 * m + 1)} :
    y ∈ comp p M₁ x ↔ y ∈ matchedSet M₁ ∧ (HSGraph p M₁).Reachable x y := by
  classical
  simp [comp]

private lemma comp_subset_S (p : CompleteProfile (2 * m + 1)) (M₁ : Matching (Fin (2 * m + 1)))
    (x : Fin (2 * m + 1)) : comp p M₁ x ⊆ matchedSet M₁ := by
  intro y hy; exact ((mem_comp p).1 hy).1

private lemma self_mem_comp (p : CompleteProfile (2 * m + 1)) {M₁ : Matching (Fin (2 * m + 1))}
    {x : Fin (2 * m + 1)} (hx : x ∈ matchedSet M₁) : x ∈ comp p M₁ x :=
  (mem_comp p).2 ⟨hx, SimpleGraph.Reachable.refl x⟩

private lemma comp_eq_of_mem (p : CompleteProfile (2 * m + 1)) {M₁ : Matching (Fin (2 * m + 1))}
    {x y : Fin (2 * m + 1)} (hy : y ∈ comp p M₁ x) :
    comp p M₁ y = comp p M₁ x := by
  have hreach := ((mem_comp p).1 hy).2
  ext z
  simp only [mem_comp]
  exact ⟨fun ⟨hz, h⟩ => ⟨hz, hreach.trans h⟩, fun ⟨hz, h⟩ => ⟨hz, hreach.symm.trans h⟩⟩

private lemma comp_disjoint_of_ne (p : CompleteProfile (2 * m + 1))
    {M₁ : Matching (Fin (2 * m + 1))} {x y : Fin (2 * m + 1)}
    (hne : comp p M₁ x ≠ comp p M₁ y) :
    Disjoint (comp p M₁ x) (comp p M₁ y) := by
  rw [Finset.disjoint_left]
  intro z hzx hzy
  exact hne ((comp_eq_of_mem p hzx).symm.trans (comp_eq_of_mem p hzy))

private lemma H_matching_preserves_comp (p : CompleteProfile (2 * m + 1))
    {M₁ M' : Matching (Fin (2 * m + 1))}
    (hM'H : IsHMatching p M') (hsub : matchedSet M' ⊆ matchedSet M₁)
    (x : Fin (2 * m + 1)) : ∀ v ∈ comp p M₁ x, M'.val v ∈ comp p M₁ x := by
  intro v hv
  by_cases hfix : M'.val v = v
  · rwa [hfix]
  · have hvM' : v ∈ matchedSet M' := (mem_matchedSet M' v).2 hfix
    have hvS : v ∈ matchedSet M₁ := ((mem_comp p).1 hv).1
    have hMvS : M'.val v ∈ matchedSet M₁ := hsub (matchedSet_map M' hvM')
    have hadj : (HSGraph p M₁).Adj v (M'.val v) :=
      ⟨hvS, hMvS, H_adj_of_mem_matchedSet p hM'H hvM'⟩
    exact (mem_comp p).2 ⟨hMvS, ((mem_comp p).1 hv).2.trans hadj.reachable⟩

private lemma M1_mem_comp (p : CompleteProfile (2 * m + 1)) {M₁ : Matching (Fin (2 * m + 1))}
    (hM₁ : IsMaxHMatching p M₁) {x : Fin (2 * m + 1)} (hx : x ∈ matchedSet M₁) :
    M₁.val x ∈ comp p M₁ x :=
  H_matching_preserves_comp p hM₁.1 Finset.Subset.rfl x x (self_mem_comp p hx)

private lemma even_card_comp (p : CompleteProfile (2 * m + 1)) {M₁ : Matching (Fin (2 * m + 1))}
    (hM₁ : IsMaxHMatching p M₁) (x : Fin (2 * m + 1)) : Even (comp p M₁ x).card := by
  let μ := restrictMatching (comp p M₁ x) M₁
    (H_matching_preserves_comp p hM₁.1 Finset.Subset.rfl x)
  have hms : matchedSet μ = comp p M₁ x := by
    rw [matchedSet_restrictMatching]
    exact Finset.inter_eq_left.2 (comp_subset_S p M₁ x)
  rw [← hms]
  exact even_card_matchedSet μ

private lemma Rset_subset_comp (p : CompleteProfile (2 * m + 1)) {M₁ : Matching (Fin (2 * m + 1))}
    (hM₁ : IsMaxHMatching p M₁) {x : Fin (2 * m + 1)} (hx : x ∈ matchedSet M₁) :
    Rset p M₁ x ⊆ comp p M₁ x := by
  intro w hw
  obtain ⟨hwS, hwx, M', hM'H, hM'ms⟩ := (mem_Rset p).1 hw
  have hsub : matchedSet M' ⊆ matchedSet M₁ := by
    rw [hM'ms]; exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  let μ := restrictMatching (comp p M₁ x) M' (H_matching_preserves_comp p hM'H hsub x)
  have hms : matchedSet μ = comp p M₁ x ∩ (((matchedSet M₁).erase x).erase w) := by
    rw [matchedSet_restrictMatching, hM'ms]
  have hev1 : Even (comp p M₁ x).card := even_card_comp p hM₁ x
  have hev2 : Even (matchedSet μ).card := even_card_matchedSet μ
  by_contra hw_not
  have heq : comp p M₁ x ∩ (((matchedSet M₁).erase x).erase w) = (comp p M₁ x).erase x := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · rintro ⟨hvC, _, hvx, _⟩; exact ⟨hvx, hvC⟩
    · rintro ⟨hvx, hvC⟩
      refine ⟨hvC, ?_, hvx, comp_subset_S p M₁ x hvC⟩
      intro hvw; exact hw_not (hvw ▸ hvC)
  rw [heq] at hms
  rw [hms, Finset.card_erase_of_mem (self_mem_comp p hx)] at hev2
  have hpos : 0 < (comp p M₁ x).card := Finset.card_pos.2 ⟨x, self_mem_comp p hx⟩
  obtain ⟨k₁, hk₁⟩ := hev1
  obtain ⟨k₂, hk₂⟩ := hev2
  omega

private lemma comp_card_two_not_Sge2 (p : CompleteProfile (2 * m + 1))
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x : Fin (2 * m + 1)} (hx : x ∈ matchedSet M₁) (hcard : (comp p M₁ x).card = 2) :
    x ∉ Sge2 p M₁ := by
  intro hx2
  have hnbrs := (mem_Sge2_iff_nbrs p hM₁ hx).1 hx2
  have hsub : (matchedSet M₁).filter (fun z => (HGraph p).Adj (M₁.val x) z) ⊆
      (comp p M₁ x).erase (M₁.val x) := by
    intro z hz
    obtain ⟨hzS, hadj⟩ := Finset.mem_filter.1 hz
    have hMy : M₁.val x ∈ comp p M₁ x := M1_mem_comp p hM₁ hx
    have hreach : (HSGraph p M₁).Reachable x z :=
      ((mem_comp p).1 hMy).2.trans (SimpleGraph.Adj.reachable ⟨matchedSet_map M₁ hx, hzS, hadj⟩)
    exact Finset.mem_erase.2 ⟨hadj.1.symm, (mem_comp p).2 ⟨hzS, hreach⟩⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (M1_mem_comp p hM₁ hx), hcard] at hle
  omega

/-- Claim 3.3 (Part 3): Every component `C` of size `≥ 4` is complete bipartite with respect
to `M₁`, satisfies `C ⊆ S_ge2`, and `C.card ≤ 2 * (R v).card` for all `v ∈ C`. -/
private lemma comp_card_ge_four_structure (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x₀ : Fin (2 * m + 1)} (hx₀ : x₀ ∈ matchedSet M₁) (h4 : 4 ≤ (comp p M₁ x₀).card) :
    comp p M₁ x₀ ⊆ Sge2 p M₁ ∧
      ∀ v ∈ comp p M₁ x₀, (comp p M₁ x₀).card ≤ 2 * (Rset p M₁ v).card := by
  let C := comp p M₁ x₀
  let IsGood (L : Finset (Fin (2 * m + 1))) : Prop :=
    L ⊆ C ∧ L.Nonempty ∧ Disjoint L (L.image M₁.val) ∧
      ∀ a ∈ L, ∀ b ∈ L, (HGraph p).Adj a (M₁.val b)
  classical
  let goodSets : Finset (Finset (Fin (2 * m + 1))) :=
    C.powerset.filter (fun L => IsGood L)
  have hx₀_good : ({x₀} : Finset (Fin (2 * m + 1))) ∈ goodSets := by
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.singleton_subset_iff.2
      (self_mem_comp p hx₀)), ?_⟩
    refine ⟨Finset.singleton_subset_iff.2 (self_mem_comp p hx₀),
      Finset.singleton_nonempty x₀, ?_, ?_⟩
    · rw [Finset.image_singleton, Finset.disjoint_singleton]
      exact ((mem_matchedSet M₁ x₀).1 hx₀).symm
    · intro a ha b hb
      rw [Finset.mem_singleton] at ha hb
      subst ha; subst hb
      exact H_adj_of_mem_matchedSet p hM₁.1 hx₀
  obtain ⟨L, hLmem, hLmax⟩ :=
    Finset.exists_max_image goodSets Finset.card ⟨{x₀}, hx₀_good⟩
  obtain ⟨hLC, hLne, hLdisj, hLadj⟩ := (Finset.mem_filter.1 hLmem).2
  let B := L.image M₁.val
  have hBC : B ⊆ C := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    exact H_matching_preserves_comp p hM₁.1 Finset.Subset.rfl x₀ a (hLC ha)
  have hBcard : B.card = L.card :=
    Finset.card_image_of_injective L M₁.val.injective
  have hBM1 : B.image M₁.val = L := by
    ext x
    simp only [B, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; simpa [M₁.property a] using ha
    · intro hx; exact ⟨M₁.val x, ⟨x, hx, rfl⟩, M₁.property x⟩
  have hBgood : IsGood B := by
    refine ⟨hBC, hLne.image M₁.val, ?_, ?_⟩
    · rw [hBM1]; exact hLdisj.symm
    · intro b₁ hb₁ b₂ hb₂
      obtain ⟨a₁, ha₁, rfl⟩ := Finset.mem_image.1 hb₁
      obtain ⟨a₂, ha₂, rfl⟩ := Finset.mem_image.1 hb₂
      rw [M₁.property a₂]
      exact (hLadj a₂ ha₂ a₁ ha₁).symm
  have hextend : ∀ L₁ : Finset (Fin (2 * m + 1)), IsGood L₁ →
      ∀ b₀ ∈ L₁.image M₁.val, ∀ z ∈ C \ (L₁ ∪ L₁.image M₁.val),
        (HGraph p).Adj b₀ z → ∃ L₂ ∈ goodSets, L₁.card < L₂.card := by
    intro L₁ ⟨hL₁C, _, hL₁disj, hL₁adj⟩ b₀ hb₀ z hz hbz
    let B₁ := L₁.image M₁.val
    obtain ⟨a₀, ha₀L₁, rfl⟩ := Finset.mem_image.1 hb₀
    have hzC : z ∈ C := (Finset.mem_sdiff.1 hz).1
    have hznot : z ∉ L₁ ∪ B₁ := (Finset.mem_sdiff.1 hz).2
    have hznotL₁ : z ∉ L₁ := fun h => hznot (Finset.mem_union_left _ h)
    have hznotB₁ : z ∉ B₁ := fun h => hznot (Finset.mem_union_right _ h)
    have hzS : z ∈ matchedSet M₁ := comp_subset_S p M₁ x₀ hzC
    let w := M₁.val z
    have hwC : w ∈ C := H_matching_preserves_comp p hM₁.1 Finset.Subset.rfl x₀ z hzC
    have hwS : w ∈ matchedSet M₁ := comp_subset_S p M₁ x₀ hwC
    have hwz : w ≠ z := (mem_matchedSet M₁ z).1 hzS
    have hwnot : w ∉ L₁ ∪ B₁ := by
      intro hw_in
      rcases Finset.mem_union.1 hw_in with hwL₁ | hwB₁
      · exact hznotB₁ (Finset.mem_image.2 ⟨w, hwL₁, M₁.property z⟩)
      · obtain ⟨a, ha, haw⟩ := Finset.mem_image.1 hwB₁
        have : z = a := M₁.val.injective (by simpa [w] using haw.symm)
        exact hznotL₁ (this ▸ ha)
    have hwnotL₁ : w ∉ L₁ := fun h => hwnot (Finset.mem_union_left _ h)
    have hwnotB₁ : w ∉ B₁ := fun h => hwnot (Finset.mem_union_right _ h)
    have ha₀S : a₀ ∈ matchedSet M₁ := comp_subset_S p M₁ x₀ (hL₁C ha₀L₁)
    have hb₀S : M₁.val a₀ ∈ matchedSet M₁ := matchedSet_map M₁ ha₀S
    have hw_ge2 : w ∈ Sge2 p M₁ := by
      rw [mem_Sge2_iff_nbrs p hM₁ hwS]
      have hMw : M₁.val w = z := M₁.property z
      rw [hMw]
      have h1 : w ∈ (matchedSet M₁).filter (fun v => (HGraph p).Adj z v) :=
        Finset.mem_filter.2 ⟨hwS, H_adj_of_mem_matchedSet p hM₁.1 hzS⟩
      have h2 : M₁.val a₀ ∈ (matchedSet M₁).filter (fun v => (HGraph p).Adj z v) :=
        Finset.mem_filter.2 ⟨hb₀S, hbz.symm⟩
      have hne : w ≠ M₁.val a₀ := fun h => hwnotB₁ (h ▸ Finset.mem_image_of_mem _ ha₀L₁)
      have hlt := Finset.one_lt_card.2 ⟨w, h1, M₁.val a₀, h2, hne⟩
      omega
    have hLw : ∀ a ∈ L₁, (HGraph p).Adj a w := by
      intro a haL₁
      have haS : a ∈ matchedSet M₁ := comp_subset_S p M₁ x₀ (hL₁C haL₁)
      let b := M₁.val a
      have hbS : b ∈ matchedSet M₁ := matchedSet_map M₁ haS
      have hba : b ≠ a := (mem_matchedSet M₁ a).1 haS
      have ha_ge2 : a ∈ Sge2 p M₁ := by
        rw [mem_Sge2_iff_nbrs p hM₁ haS]
        have h1 : a ∈ (matchedSet M₁).filter (fun v => (HGraph p).Adj b v) :=
          Finset.mem_filter.2 ⟨haS, (H_adj_of_mem_matchedSet p hM₁.1 haS).symm⟩
        by_cases haa₀ : a = a₀
        · subst haa₀
          have h2 : z ∈ (matchedSet M₁).filter (fun v => (HGraph p).Adj b v) :=
            Finset.mem_filter.2 ⟨hzS, hbz⟩
          have hne : a ≠ z := fun h => hznotL₁ (h ▸ haL₁)
          have hlt := Finset.one_lt_card.2 ⟨a, h1, z, h2, hne⟩
          dsimp [b] at hlt
          omega
        · have h2 : a₀ ∈ (matchedSet M₁).filter (fun v => (HGraph p).Adj b v) :=
            Finset.mem_filter.2 ⟨ha₀S, (hL₁adj a₀ ha₀L₁ a haL₁).symm⟩
          have hlt := Finset.one_lt_card.2 ⟨a, h1, a₀, h2, haa₀⟩
          dsimp [b] at hlt
          omega
      have hwRa : w ∈ Rset p M₁ a := by
        rw [mem_Rset]
        have hwa : w ≠ a := fun h => hwnotL₁ (h ▸ haL₁)
        refine ⟨hwS, hwa, ?_⟩
        by_cases haa₀ : a = a₀
        · subst haa₀
          have hza : z ≠ a := fun h => hznotL₁ (h ▸ haL₁)
          have hzb : z ≠ b := hbz.1.symm
          have hwb : w ≠ b := fun h => hwnotB₁ (h ▸ Finset.mem_image_of_mem _ haL₁)
          let M_e1 := eraseEdge M₁ a b rfl
          have hM_e1_zw : M_e1.val z = w := by simp [M_e1, eraseEdge_apply, hza, hzb, w]
          let M_e2 := eraseEdge M_e1 z w hM_e1_zw
          have hb_fix : M_e2.val b = b := by
            simp [M_e2, eraseEdge_apply, hzb.symm, hwb.symm, M_e1]
          have hz_fix : M_e2.val z = z := by simp [M_e2, eraseEdge_apply]
          refine ⟨addEdge M_e2 b z hb_fix hz_fix,
            isAcceptable_addEdge M_e2
              (isAcceptable_eraseEdge M_e1 (isAcceptable_eraseEdge M₁ hM₁.1 rfl) hM_e1_zw)
              hb_fix hz_fix hbz, ?_⟩
          rw [matchedSet_addEdge M_e2 hzb.symm hb_fix hz_fix,
            matchedSet_eraseEdge M_e1 hM_e1_zw, matchedSet_eraseEdge M₁ rfl]
          ext v
          simp only [Finset.mem_insert, Finset.mem_erase]
          by_cases hvb : v = b
          · simp [hvb, hwb.symm, hba, hbS]
          · by_cases hvz : v = z
            · simp [hvz, hwz.symm, hza, hzS]
            · by_cases hvw : v = w
              · simp [hvw, hwb, hwz]
              · by_cases hva : v = a
                · simp [hva, hba.symm, hza.symm]
                · simp [hvb, hvz, hvw, hva, b]
        · have hb₀a : M₁.val a₀ ≠ a := fun h =>
            Finset.disjoint_left.1 hL₁disj haL₁ (h ▸ Finset.mem_image_of_mem _ ha₀L₁)
          have hb₀b : M₁.val a₀ ≠ b := fun h => haa₀ (M₁.val.injective h.symm)
          have ha₀b : a₀ ≠ b := fun h =>
            Finset.disjoint_left.1 hL₁disj ha₀L₁ (h ▸ Finset.mem_image_of_mem _ haL₁)
          have hza : z ≠ a := fun h => hznotL₁ (h ▸ haL₁)
          have hzb : z ≠ b := fun h => hznotB₁ (h ▸ Finset.mem_image_of_mem _ haL₁)
          have hza₀ : z ≠ a₀ := fun h => hznotL₁ (h ▸ ha₀L₁)
          have hzb₀ : z ≠ M₁.val a₀ := hbz.1.symm
          have hwb : w ≠ b := fun h => hwnotB₁ (h ▸ Finset.mem_image_of_mem _ haL₁)
          have hwa₀ : w ≠ a₀ := fun h => hwnotL₁ (h ▸ ha₀L₁)
          have hwb₀ : w ≠ M₁.val a₀ := fun h => hwnotB₁ (h ▸ Finset.mem_image_of_mem _ ha₀L₁)
          have hb₀a₀ : M₁.val a₀ ≠ a₀ := (mem_matchedSet M₁ a₀).1 ha₀S
          let M_e1 := eraseEdge M₁ a b rfl
          have hM_e1_a₀ : M_e1.val a₀ = M₁.val a₀ := by
            simp [M_e1, eraseEdge_apply, Ne.symm haa₀, ha₀b]
          let M_e2 := eraseEdge M_e1 a₀ (M₁.val a₀) hM_e1_a₀
          have hM_e2_z : M_e2.val z = w := by
            simp [M_e2, eraseEdge_apply, hza₀, hzb₀, M_e1, hza, hzb, w]
          let M_e3 := eraseEdge M_e2 z w hM_e2_z
          have ha₀_fix : M_e3.val a₀ = a₀ := by
            simp [M_e3, eraseEdge_apply, hza₀.symm, hwa₀.symm, M_e2]
          have hb_fix : M_e3.val b = b := by
            simp [M_e3, eraseEdge_apply, hzb.symm, hwb.symm, M_e2, ha₀b.symm, hb₀b.symm, M_e1]
          let M_a1 := addEdge M_e3 a₀ b ha₀_fix hb_fix
          have hb₀_fix : M_a1.val (M₁.val a₀) = M₁.val a₀ := by
            simp [M_a1, addEdge_apply, hb₀a₀, hb₀b, M_e3, eraseEdge_apply, hzb₀.symm, hwb₀.symm, M_e2]
          have hz_fix : M_a1.val z = z := by
            simp [M_a1, addEdge_apply, hza₀, hzb, M_e3, eraseEdge_apply]
          let M' := addEdge M_a1 (M₁.val a₀) z hb₀_fix hz_fix
          have hM'H : IsHMatching p M' :=
            isAcceptable_addEdge M_a1
              (isAcceptable_addEdge M_e3
                (isAcceptable_eraseEdge M_e2
                  (isAcceptable_eraseEdge M_e1 (isAcceptable_eraseEdge M₁ hM₁.1 rfl) hM_e1_a₀)
                  hM_e2_z)
                ha₀_fix hb_fix (hL₁adj a₀ ha₀L₁ a haL₁))
              hb₀_fix hz_fix hbz
          refine ⟨M', hM'H, ?_⟩
          rw [matchedSet_addEdge M_a1 hzb₀.symm hb₀_fix hz_fix,
            matchedSet_addEdge M_e3 ha₀b ha₀_fix hb_fix,
            matchedSet_eraseEdge M_e2 hM_e2_z,
            matchedSet_eraseEdge M_e1 hM_e1_a₀,
            matchedSet_eraseEdge M₁ rfl]
          ext v
          simp only [Finset.mem_insert, Finset.mem_erase]
          by_cases hvb₀ : v = M₁.val a₀
          · simp [hvb₀, hwb₀.symm, hb₀a, hb₀S]
          · by_cases hvz : v = z
            · simp [hvz, hwz.symm, hza, hzS]
            · by_cases hva₀ : v = a₀
              · simp [hva₀, hwa₀.symm, Ne.symm haa₀, ha₀S]
              · by_cases hvb : v = b
                · simp [hvb, hwb.symm, hba, hbS]
                · by_cases hvw : v = w
                  · simp [hvw, hwb₀, hwz, hwa₀, hwb]
                  · by_cases hva : v = a
                    · simp [hva, hb₀a.symm, hza.symm, haa₀, hba.symm]
                    · simp [hvb₀, hvz, hva₀, hvb, hvw, hva, b]
      exact H_adj_of_Sge2_Rset hm p hno hM₁ ha_ge2 hw_ge2 hwRa
    have hz_ge2 : z ∈ Sge2 p M₁ := by
      rw [mem_Sge2_iff_nbrs p hM₁ hzS]
      have h1 : z ∈ (matchedSet M₁).filter (fun v => (HGraph p).Adj w v) :=
        Finset.mem_filter.2 ⟨hzS, (H_adj_of_mem_matchedSet p hM₁.1 hzS).symm⟩
      have h2 : a₀ ∈ (matchedSet M₁).filter (fun v => (HGraph p).Adj w v) :=
        Finset.mem_filter.2 ⟨ha₀S, (hLw a₀ ha₀L₁).symm⟩
      have hne : z ≠ a₀ := fun h => hznotL₁ (h ▸ ha₀L₁)
      have hlt := Finset.one_lt_card.2 ⟨z, h1, a₀, h2, hne⟩
      dsimp [w] at hlt
      omega
    have hBz : ∀ b ∈ B₁, (HGraph p).Adj z b := by
      intro b hbB₁
      obtain ⟨a, haL₁, rfl⟩ := Finset.mem_image.1 hbB₁
      have haS : a ∈ matchedSet M₁ := comp_subset_S p M₁ x₀ (hL₁C haL₁)
      have hbS : M₁.val a ∈ matchedSet M₁ := matchedSet_map M₁ haS
      have hba : M₁.val a ≠ a := (mem_matchedSet M₁ a).1 haS
      have hb_ge2 : M₁.val a ∈ Sge2 p M₁ := by
        rw [mem_Sge2_iff_nbrs p hM₁ hbS]
        rw [M₁.property a]
        have h1 : M₁.val a ∈ (matchedSet M₁).filter (fun v => (HGraph p).Adj a v) :=
          Finset.mem_filter.2 ⟨hbS, H_adj_of_mem_matchedSet p hM₁.1 haS⟩
        have h2 : w ∈ (matchedSet M₁).filter (fun v => (HGraph p).Adj a v) :=
          Finset.mem_filter.2 ⟨hwS, hLw a haL₁⟩
        have hne : M₁.val a ≠ w := fun h => hwnotB₁ (h ▸ Finset.mem_image_of_mem _ haL₁)
        have hlt := Finset.one_lt_card.2 ⟨M₁.val a, h1, w, h2, hne⟩
        omega
      have hzRb : z ∈ Rset p M₁ (M₁.val a) := by
        rw [mem_Rset]
        have hzb : z ≠ M₁.val a := fun h => hznotB₁ (h ▸ Finset.mem_image_of_mem _ haL₁)
        have hza : z ≠ a := fun h => hznotL₁ (h ▸ haL₁)
        have hwa : w ≠ a := fun h => hwnotL₁ (h ▸ haL₁)
        have hwb : w ≠ M₁.val a := fun h => hwnotB₁ (h ▸ Finset.mem_image_of_mem _ haL₁)
        refine ⟨hzS, hzb, ?_⟩
        let M_e1 := eraseEdge M₁ a (M₁.val a) rfl
        have hM_e1_zw : M_e1.val z = w := by simp [M_e1, eraseEdge_apply, hza, hzb, w]
        let M_e2 := eraseEdge M_e1 z w hM_e1_zw
        have ha_fix : M_e2.val a = a := by
          simp [M_e2, eraseEdge_apply, hza.symm, hwa.symm, M_e1]
        have hw_fix : M_e2.val w = w := by simp [M_e2, eraseEdge_apply]
        refine ⟨addEdge M_e2 a w ha_fix hw_fix,
          isAcceptable_addEdge M_e2
            (isAcceptable_eraseEdge M_e1 (isAcceptable_eraseEdge M₁ hM₁.1 rfl) hM_e1_zw)
            ha_fix hw_fix (hLw a haL₁), ?_⟩
        rw [matchedSet_addEdge M_e2 hwa.symm ha_fix hw_fix,
          matchedSet_eraseEdge M_e1 hM_e1_zw, matchedSet_eraseEdge M₁ rfl]
        ext v
        simp only [Finset.mem_insert, Finset.mem_erase]
        by_cases hva : v = a
        · simp [hva, hza.symm, hba.symm, haS]
        · by_cases hvw : v = w
          · simp [hvw, hwz, hwb, hwS]
          · by_cases hvz : v = z
            · simp [hvz, hza, hwz.symm]
            · by_cases hvb : v = M₁.val a
              · simp [hvb, hba, hwb.symm]
              · simp [hva, hvw, hvz, hvb]
      exact (H_adj_of_Sge2_Rset hm p hno hM₁ hb_ge2 hz_ge2 hzRb).symm
    refine ⟨insert z L₁, Finset.mem_filter.2 ⟨Finset.mem_powerset.2
      (Finset.insert_subset hzC hL₁C), ?_⟩, ?_⟩
    · refine ⟨Finset.insert_subset hzC hL₁C, Finset.insert_nonempty z L₁, ?_, ?_⟩
      · rw [Finset.image_insert, Finset.disjoint_insert_left, Finset.disjoint_insert_right]
        refine ⟨?_, ?_, ?_⟩
        · intro h
          rw [Finset.mem_insert] at h
          rcases h with h | h
          · exact hwz.symm h
          · exact hznotB₁ h
        · exact hwnotL₁
        · exact hL₁disj
      · intro u hu v hv
        rw [Finset.mem_insert] at hu hv
        rcases hu with rfl | huL₁ <;> rcases hv with rfl | hvL₁
        · exact H_adj_of_mem_matchedSet p hM₁.1 hzS
        · exact hBz (M₁.val v) (Finset.mem_image_of_mem _ hvL₁)
        · exact hLw u huL₁
        · exact hL₁adj u huL₁ v hvL₁
    · rw [Finset.card_insert_of_notMem hznotL₁]
      omega
  have hLB_eq : L ∪ B = C := by
    by_contra hne
    have hsub : L ∪ B ⊆ C := Finset.union_subset hLC hBC
    have hssub : (C \ (L ∪ B)).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hCsub
      exact hne (Finset.Subset.antisymm hsub hCsub)
    obtain ⟨t, ht⟩ := hssub
    rcases hLne with ⟨s, hs⟩
    have hsC : s ∈ C := hLC hs
    have htC : t ∈ C := (Finset.mem_sdiff.1 ht).1
    have hreach : (HSGraph p M₁).Reachable s t :=
      ((mem_comp p).1 hsC).2.symm.trans ((mem_comp p).1 htC).2
    obtain ⟨walk⟩ := hreach
    obtain ⟨u, v, huLB, hvnot, huv⟩ := walk_cross walk (Finset.mem_union_left B hs)
      (Finset.mem_sdiff.1 ht).2
    have hvC : v ∈ C := (mem_comp p).2 ⟨huv.2.1, ((mem_comp p).1 (hsub huLB)).2.trans huv.reachable⟩
    have hv_sdiff : v ∈ C \ (L ∪ B) := Finset.mem_sdiff.2 ⟨hvC, hvnot⟩
    rcases Finset.mem_union.1 huLB with huL | huB
    · have hvs : v ∈ C \ (B ∪ B.image M₁.val) := by
        rwa [hBM1, Finset.union_comm]
      obtain ⟨L₂, hL₂mem, hL₂gt⟩ := hextend B hBgood u (hBM1 ▸ huL) v hvs huv.2.2
      have := hLmax L₂ hL₂mem
      omega
    · obtain ⟨L₂, hL₂mem, hL₂gt⟩ := hextend L ⟨hLC, ⟨s, hs⟩, hLdisj, hLadj⟩ u huB v hv_sdiff huv.2.2
      have := hLmax L₂ hL₂mem
      omega
  have hCcard : C.card = 2 * L.card := by
    rw [← hLB_eq, Finset.card_union_of_disjoint hLdisj, hBcard]
    omega
  have hL2 : 2 ≤ L.card := by dsimp [C] at hCcard; omega
  have hside : ∀ L₁ : Finset (Fin (2 * m + 1)), IsGood L₁ →
      L₁.card = L.card →
      ∀ a ∈ L₁, a ∈ Sge2 p M₁ ∧ L₁.image M₁.val ⊆ Rset p M₁ a := by
    intro L₁ ⟨hL₁C, _, hL₁disj, hL₁adj⟩ hL₁card a haL₁
    have haS : a ∈ matchedSet M₁ := comp_subset_S p M₁ x₀ (hL₁C haL₁)
    constructor
    · rw [mem_Sge2_iff_nbrs p hM₁ haS]
      have hsub : L₁ ⊆ (matchedSet M₁).filter (fun z => (HGraph p).Adj (M₁.val a) z) := by
        intro u hu
        exact Finset.mem_filter.2 ⟨comp_subset_S p M₁ x₀ (hL₁C hu), (hL₁adj u hu a haL₁).symm⟩
      have := Finset.card_le_card hsub
      omega
    · intro b hb
      obtain ⟨a', ha'L₁, rfl⟩ := Finset.mem_image.1 hb
      by_cases haa' : a' = a
      · subst haa'; exact M1_mem_Rset p hM₁ haS
      · rw [mem_Rset]
        have ha'S : a' ∈ matchedSet M₁ := comp_subset_S p M₁ x₀ (hL₁C ha'L₁)
        have hbS : M₁.val a' ∈ matchedSet M₁ := matchedSet_map M₁ ha'S
        have hb'S : M₁.val a ∈ matchedSet M₁ := matchedSet_map M₁ haS
        have hba : M₁.val a' ≠ a := fun h =>
          Finset.disjoint_left.1 hL₁disj haL₁ (h ▸ Finset.mem_image_of_mem _ ha'L₁)
        have hb'a : M₁.val a ≠ a := (mem_matchedSet M₁ a).1 haS
        have hba' : M₁.val a' ≠ a' := (mem_matchedSet M₁ a').1 ha'S
        have ha'b' : a' ≠ M₁.val a := fun h =>
          Finset.disjoint_left.1 hL₁disj ha'L₁ (h ▸ Finset.mem_image_of_mem _ haL₁)
        have hbb' : M₁.val a' ≠ M₁.val a := fun h => haa' (M₁.val.injective h)
        refine ⟨hbS, hba, ?_⟩
        let M_e1 := eraseEdge M₁ a (M₁.val a) rfl
        have hM_e1_a' : M_e1.val a' = M₁.val a' := by
          simp [M_e1, eraseEdge_apply, haa', ha'b']
        let M_e2 := eraseEdge M_e1 a' (M₁.val a') hM_e1_a'
        have ha'_fix : M_e2.val a' = a' := by simp [M_e2, eraseEdge_apply]
        have hb'_fix : M_e2.val (M₁.val a) = M₁.val a := by
          simp [M_e2, eraseEdge_apply, ha'b'.symm, hbb'.symm, M_e1]
        refine ⟨addEdge M_e2 a' (M₁.val a) ha'_fix hb'_fix,
          isAcceptable_addEdge M_e2
            (isAcceptable_eraseEdge M_e1 (isAcceptable_eraseEdge M₁ hM₁.1 rfl) hM_e1_a')
            ha'_fix hb'_fix (hL₁adj a' ha'L₁ a haL₁), ?_⟩
        rw [matchedSet_addEdge M_e2 ha'b' ha'_fix hb'_fix,
          matchedSet_eraseEdge M_e1 hM_e1_a', matchedSet_eraseEdge M₁ rfl]
        ext v
        simp only [Finset.mem_insert, Finset.mem_erase]
        by_cases hva' : v = a'
        · simp [hva', hba'.symm, haa', ha'S]
        · by_cases hvb' : v = M₁.val a
          · simp [hvb', hbb'.symm, hb'a, hb'S]
          · by_cases hvb : v = M₁.val a'
            · simp [hvb, hba', hbb']
            · by_cases hva : v = a
              · simp [hva, Ne.symm haa', hb'a.symm]
              · simp [hva', hvb', hvb, hva]
  constructor
  · intro v hv
    change v ∈ C at hv
    rw [← hLB_eq, Finset.mem_union] at hv
    rcases hv with hvL | hvB
    · exact (hside L ⟨hLC, hLne, hLdisj, hLadj⟩ rfl v hvL).1
    · exact (hside B hBgood hBcard v hvB).1
  · intro v hv
    change v ∈ C at hv
    rw [← hLB_eq, Finset.mem_union] at hv
    rcases hv with hvL | hvB
    · have hsub := (hside L ⟨hLC, hLne, hLdisj, hLadj⟩ rfl v hvL).2
      have hle := Finset.card_le_card hsub
      rw [hBcard] at hle
      change C.card ≤ _
      omega
    · have hsub := (hside B hBgood hBcard v hvB).2
      have hle := Finset.card_le_card hsub
      rw [hBM1] at hle
      change C.card ≤ _
      omega

private lemma mem_Sge2_iff_four_le_comp_card (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x : Fin (2 * m + 1)} (hx : x ∈ matchedSet M₁) :
    x ∈ Sge2 p M₁ ↔ 4 ≤ (comp p M₁ x).card := by
  constructor
  · intro hx2
    have hev := even_card_comp p hM₁ x
    have h2 : 2 ≤ (comp p M₁ x).card := by
      have h1 : x ∈ comp p M₁ x := self_mem_comp p hx
      have h2' : M₁.val x ∈ comp p M₁ x := M1_mem_comp p hM₁ hx
      have hlt := Finset.one_lt_card.2 ⟨x, h1, M₁.val x, h2', ((mem_matchedSet M₁ x).1 hx).symm⟩
      omega
    by_contra hlt
    obtain ⟨k, hk⟩ := hev
    have hcard2 : (comp p M₁ x).card = 2 := by omega
    exact comp_card_two_not_Sge2 p hM₁ hx hcard2 hx2
  · intro h4
    exact (comp_card_ge_four_structure hm p hno hM₁ hx h4).1 (self_mem_comp p hx)

private lemma S_iso_comp_eq_pair (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x : Fin (2 * m + 1)} (hx : x ∈ matchedSet M₁) (hx_not : x ∉ Sge2 p M₁) :
    comp p M₁ x = {x, M₁.val x} := by
  have hev := even_card_comp p hM₁ x
  have hnot4 : ¬ 4 ≤ (comp p M₁ x).card := fun h =>
    hx_not ((mem_Sge2_iff_four_le_comp_card hm p hno hM₁ hx).2 h)
  have hsub : ({x, M₁.val x} : Finset (Fin (2 * m + 1))) ⊆ comp p M₁ x := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact self_mem_comp p hx
    · exact M1_mem_comp p hM₁ hx
  have hpair_card : ({x, M₁.val x} : Finset (Fin (2 * m + 1))).card = 2 :=
    Finset.card_pair ((mem_matchedSet M₁ x).1 hx).symm
  have hle : 2 ≤ (comp p M₁ x).card := by
    have := Finset.card_le_card hsub
    omega
  obtain ⟨k, hk⟩ := hev
  have hcard2 : (comp p M₁ x).card = 2 := by omega
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

private lemma S_iso_comp_card (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x : Fin (2 * m + 1)} (hx : x ∈ matchedSet M₁) (hx_not : x ∉ Sge2 p M₁) :
    (comp p M₁ x).card = 2 := by
  rw [S_iso_comp_eq_pair hm p hno hM₁ hx hx_not, Finset.card_pair ((mem_matchedSet M₁ x).1 hx).symm]

private lemma S_iso_no_other_H_adj (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x y : Fin (2 * m + 1)} (hx : x ∈ matchedSet M₁) (hx_not : x ∉ Sge2 p M₁)
    (hy : y ∈ matchedSet M₁) (hyx : y ≠ x) (hyM : y ≠ M₁.val x) :
    ¬ (HGraph p).Adj x y := by
  intro hadj
  have hyC : y ∈ comp p M₁ x :=
    (mem_comp p).2 ⟨hy, SimpleGraph.Adj.reachable ⟨hx, hy, hadj⟩⟩
  rw [S_iso_comp_eq_pair hm p hno hM₁ hx hx_not, Finset.mem_insert, Finset.mem_singleton] at hyC
  rcases hyC with h | h
  · exact hyx h
  · exact hyM h

end Step2And3

/-! ### Step 4: Claim 4.0 — Purely Isolated Case (`S_ge2.Nonempty`) -/

section Step4

/-- Claim 4.0: `S_ge2` is nonempty. -/
private lemma Sge2_nonempty (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁) :
    (Sge2 p M₁).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  let S := matchedSet M₁
  let U := Finset.univ \ S
  let D : Fin (2 * m + 1) → Finset (Fin (2 * m + 1)) :=
    fun x => S.filter (fun z => p.partnerRank x z ≤ m)
  let Kbeta : Finset (Fin (2 * m + 1)) := S.filter (fun x => vstar p (M₁.val x) ∉ U)
  have hSge : m - 1 ≤ S.card := m_sub_one_le_S_card hm p hno hM₁
  have hSle : S.card ≤ 2 * m - 2 := S_card_le p hno hM₁
  have hS2 : 2 ≤ S.card := by omega
  have hno_edge : ∀ x ∈ S, ∀ z ∈ S, z ≠ x → z ≠ M₁.val x → ¬ (HGraph p).Adj x z := by
    intro x hx z hz hzx hzM
    have hx_not : x ∉ Sge2 p M₁ := by rw [hne]; simp
    exact S_iso_no_other_H_adj hm p hno hM₁ hx hx_not hz hzx hzM
  have hD_info : ∀ x ∈ S,
      (Finset.univ.filter (fun z => p.partnerRank x z ≤ m) ∩ U) ⊆ {vstar p (M₁.val x)} ∧
      m - 1 ≤ (D x).card ∧
      (x ∈ Kbeta → m ≤ (D x).card) := by
    intro x hx
    let T := Finset.univ.filter (fun z => p.partnerRank x z ≤ m)
    have hTU_sub : T ∩ U ⊆ {vstar p (M₁.val x)} := by
      intro u hu
      rw [Finset.mem_singleton]
      obtain ⟨huT, huU⟩ := Finset.mem_inter.1 hu
      have hru : p.partnerRank x u ≤ m := (Finset.mem_filter.1 huT).2
      have hMxR : M₁.val x ∈ Rset p M₁ x := M1_mem_Rset p hM₁ hx
      rcases master_lemma hm p hno hM₁ hx hMxR huU with ⟨hA, _⟩ | ⟨hu_eq, _, _⟩
      · have := rk_pos p x (M₁.val x)
        omega
      · exact hu_eq
    have hdisj : Disjoint (D x) (T ∩ U) := by
      rw [Finset.disjoint_left]
      intro z hzD hzTU
      exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 hzTU).2).2 (Finset.mem_filter.1 hzD).1
    have hunion : D x ∪ (T ∩ U) = T := by
      ext z
      simp only [D, T, U, Finset.mem_union, Finset.mem_inter, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_sdiff]
      by_cases hzS : z ∈ S <;> simp [hzS]
    have hTcard : T.card = m := card_filter_rk_le p x m (by omega)
    have hsum : (D x).card + (T ∩ U).card = m := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, hTcard]
    have hTUle : (T ∩ U).card ≤ 1 := by
      have := Finset.card_le_card hTU_sub
      simpa using this
    refine ⟨hTU_sub, by omega, fun hxK => ?_⟩
    have hv_notU : vstar p (M₁.val x) ∉ U := (Finset.mem_filter.1 hxK).2
    have hTU0 : T ∩ U = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro u hu
      have heq : u = vstar p (M₁.val x) := Finset.mem_singleton.1 (hTU_sub hu)
      exact hv_notU (heq ▸ (Finset.mem_inter.1 hu).2)
    rw [hTU0, Finset.card_empty] at hsum
    omega
  have hsum_lb : S.card * (m - 1) + Kbeta.card ≤ ∑ x ∈ S, (D x).card := by
    have hsplit : ∑ x ∈ S, (D x).card =
        (∑ x ∈ Kbeta, (D x).card) + (∑ x ∈ S \ Kbeta, (D x).card) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset (Finset.filter_subset _ _)]
    have h1 : Kbeta.card * m ≤ ∑ x ∈ Kbeta, (D x).card := by
      calc Kbeta.card * m = ∑ _x ∈ Kbeta, m := by simp
        _ ≤ ∑ x ∈ Kbeta, (D x).card :=
          Finset.sum_le_sum (fun x hx => (hD_info x (Finset.filter_subset _ _ hx)).2.2 hx)
    have h2 : (S \ Kbeta).card * (m - 1) ≤ ∑ x ∈ S \ Kbeta, (D x).card := by
      calc (S \ Kbeta).card * (m - 1) = ∑ _x ∈ S \ Kbeta, (m - 1) := by simp
        _ ≤ ∑ x ∈ S \ Kbeta, (D x).card :=
          Finset.sum_le_sum (fun x hx => (hD_info x (Finset.mem_sdiff.1 hx).1).2.1)
    have hKcard : (S \ Kbeta).card + Kbeta.card = S.card :=
      Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
    rw [hsplit]
    have hmul : Kbeta.card * m = Kbeta.card * (m - 1) + Kbeta.card := by
      have hm1 : m = (m - 1) + 1 := by omega
      calc Kbeta.card * m = Kbeta.card * ((m - 1) + 1) := congrArg (Kbeta.card * ·) hm1
        _ = Kbeta.card * (m - 1) + Kbeta.card := by rw [Nat.mul_add, Nat.mul_one]
    have htot : (S \ Kbeta).card * (m - 1) + Kbeta.card * (m - 1) = S.card * (m - 1) := by
      rw [← Nat.add_mul, hKcard]
    omega
  let NonM1 : Finset (Fin (2 * m + 1) × Fin (2 * m + 1)) :=
    (S ×ˢ S).filter (fun q => q.2 ≠ q.1 ∧ q.2 ≠ M₁.val q.1)
  let Arcs : Finset (Fin (2 * m + 1) × Fin (2 * m + 1)) :=
    NonM1.filter (fun q => p.partnerRank q.1 q.2 ≤ m)
  have hNonM1_card : NonM1.card = S.card * (S.card - 2) := by
    have hbij : NonM1.card = ∑ x ∈ S, (S.filter (fun z => z ≠ x ∧ z ≠ M₁.val x)).card := by
      have hfiber : NonM1 = S.biUnion (fun x => (S.filter (fun z => z ≠ x ∧ z ≠ M₁.val x)).image
          (fun z => (x, z))) := by
        ext ⟨x, z⟩
        simp only [NonM1, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
          Finset.mem_image]
        constructor
        · rintro ⟨⟨hx, hz⟩, h1, h2⟩
          exact ⟨x, hx, z, ⟨hz, h1, h2⟩, rfl⟩
        · rintro ⟨x', hx', z', ⟨hz', h1, h2⟩, heq⟩
          rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
          exact ⟨⟨hx', hz'⟩, h1, h2⟩
      rw [hfiber, Finset.card_biUnion]
      · refine Finset.sum_congr rfl (fun x _ => ?_)
        exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
      · intro x₁ _ x₂ _ hne
        dsimp [Function.onFun]
        rw [Finset.disjoint_left]
        intro q hq1 hq2
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.1 hq1
        obtain ⟨_, _, heq⟩ := Finset.mem_image.1 hq2
        exact hne (Prod.mk.inj heq).1.symm
    rw [hbij]
    have hconst : ∀ x ∈ S, (S.filter (fun z => z ≠ x ∧ z ≠ M₁.val x)).card = S.card - 2 := by
      intro x hx
      have heq : S.filter (fun z => z ≠ x ∧ z ≠ M₁.val x) = (S.erase x).erase (M₁.val x) := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_erase]
        tauto
      rw [heq]
      have hMx_in : M₁.val x ∈ S.erase x :=
        Finset.mem_erase.2 ⟨(mem_matchedSet M₁ x).1 hx, matchedSet_map M₁ hx⟩
      rw [Finset.card_erase_of_mem hMx_in, Finset.card_erase_of_mem hx]
      omega
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  have hArcs_swap_sub : Arcs.image Prod.swap ⊆ NonM1 := by
    intro q hq
    obtain ⟨⟨x, z⟩, hxz, rfl⟩ := Finset.mem_image.1 hq
    have hmem := (Finset.mem_filter.1 hxz).1
    obtain ⟨hprod, hzx, hzMx⟩ := Finset.mem_filter.1 hmem
    obtain ⟨hx, hz⟩ := Finset.mem_product.1 hprod
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hz, hx⟩, hzx.symm, ?_⟩
    intro h
    dsimp [Prod.swap] at h hzMx
    exact hzMx (by rw [← M₁.property z, ← h])
  have hArcs_disj : Disjoint Arcs (Arcs.image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro ⟨x, z⟩ h1 h2
    obtain ⟨⟨z', x'⟩, h2', heq⟩ := Finset.mem_image.1 h2
    obtain ⟨h1eq, h2eq⟩ := Prod.mk.inj heq
    dsimp [Prod.swap] at h1eq h2eq
    rw [h1eq, h2eq] at h2'
    obtain ⟨hnm, hr1⟩ := Finset.mem_filter.1 h1
    obtain ⟨hprod, hzx, hzMx⟩ := Finset.mem_filter.1 hnm
    obtain ⟨hx, hz⟩ := Finset.mem_product.1 hprod
    have hr2 : p.partnerRank z x ≤ m := (Finset.mem_filter.1 h2').2
    exact hno_edge x hx z hz hzx hzMx ⟨hzx.symm, hr1, hr2⟩
  have hArcs_sub : Arcs ∪ Arcs.image Prod.swap ⊆ NonM1 :=
    Finset.union_subset (Finset.filter_subset _ _) hArcs_swap_sub
  have hArcs_swap_card : (Arcs.image Prod.swap).card = Arcs.card :=
    Finset.card_image_of_injective Arcs Prod.swap_injective
  have h2Arcs_le : 2 * Arcs.card ≤ S.card * (S.card - 2) := by
    have hle := Finset.card_le_card hArcs_sub
    rw [Finset.card_union_of_disjoint hArcs_disj, hArcs_swap_card, hNonM1_card] at hle
    omega
  have hArcs_sum : Arcs.card + S.card = ∑ x ∈ S, (D x).card := by
    have hArcs_eq : Arcs.card = ∑ x ∈ S, ((D x).erase (M₁.val x)).card := by
      have hfiber : Arcs = S.biUnion (fun x => ((D x).erase (M₁.val x)).image (fun z => (x, z))) := by
        ext ⟨x, z⟩
        simp only [Arcs, NonM1, D, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
          Finset.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨⟨⟨hx, hz⟩, _, hzM⟩, hrk⟩
          exact ⟨x, hx, z, ⟨hzM, hz, hrk⟩, rfl⟩
        · rintro ⟨x', hx', z', ⟨hzM, hz', hrk⟩, heq⟩
          rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
          have hzx : z' ≠ x' := by
            intro h; subst h; have := p.partnerRank_self z'; omega
          exact ⟨⟨⟨hx', hz'⟩, hzx, hzM⟩, hrk⟩
      rw [hfiber, Finset.card_biUnion]
      · refine Finset.sum_congr rfl (fun x _ => ?_)
        exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
      · intro x₁ _ x₂ _ hne
        dsimp [Function.onFun]
        rw [Finset.disjoint_left]
        intro q hq1 hq2
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.1 hq1
        obtain ⟨_, _, heq⟩ := Finset.mem_image.1 hq2
        exact hne (Prod.mk.inj heq).1.symm
    rw [hArcs_eq]
    have hadd : ∑ x ∈ S, ((D x).erase (M₁.val x)).card + ∑ _x ∈ S, 1 = ∑ x ∈ S, (D x).card := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have hMxD : M₁.val x ∈ D x :=
        Finset.mem_filter.2 ⟨matchedSet_map M₁ hx, rk_M_le_m_of_mem_matchedSet p hM₁.1 hx⟩
      rw [Finset.card_erase_of_mem hMxD]
      have hpos : 0 < (D x).card := Finset.card_pos.2 ⟨M₁.val x, hMxD⟩
      omega
    simpa using hadd
  have hsum_ub : 2 * ∑ x ∈ S, (D x).card ≤ S.card * S.card := by
    have hmul : S.card * (S.card - 2) + 2 * S.card = S.card * S.card := by
      have : S.card - 2 + 2 = S.card := by omega
      calc S.card * (S.card - 2) + 2 * S.card
          = S.card * (S.card - 2) + S.card * 2 := by ring
        _ = S.card * (S.card - 2 + 2) := by rw [← Nat.mul_add]
        _ = S.card * S.card := by rw [this]
    omega
  have hSS_le : S.card * S.card ≤ 2 * (S.card * (m - 1)) := by
    have h1 : S.card ≤ 2 * (m - 1) := by omega
    calc S.card * S.card ≤ S.card * (2 * (m - 1)) := Nat.mul_le_mul_left S.card h1
      _ = 2 * (S.card * (m - 1)) := by ring
  -- Squeeze!
  have hKbeta_zero : Kbeta.card = 0 := by omega
  have hS_eq : S.card = 2 * m - 2 := by
    have hsq : S.card * S.card = S.card * (2 * (m - 1)) := by
      have : 2 * (S.card * (m - 1)) = S.card * (2 * (m - 1)) := by ring
      omega
    have hpos : 0 < S.card := by omega
    have := Nat.eq_of_mul_eq_mul_left hpos hsq
    omega
  have hsum_eq : ∑ x ∈ S, (D x).card = S.card * (m - 1) := by omega
  have h2Arcs_eq : 2 * Arcs.card = S.card * (S.card - 2) := by
    have hmul : S.card * (S.card - 2) + 2 * S.card = S.card * S.card := by
      have : S.card - 2 + 2 = S.card := by omega
      calc S.card * (S.card - 2) + 2 * S.card
          = S.card * (S.card - 2) + S.card * 2 := by ring
        _ = S.card * (S.card - 2 + 2) := by rw [← Nat.mul_add]
        _ = S.card * S.card := by rw [this]
    omega
  have hvstar_in_U : ∀ v ∈ S, vstar p v ∈ U := by
    intro v hv
    by_contra hnot
    have hMvS : M₁.val v ∈ S := matchedSet_map M₁ hv
    have hmem : M₁.val v ∈ Kbeta := by
      refine Finset.mem_filter.2 ⟨hMvS, ?_⟩
      rwa [M₁.property v]
    have hpos : 0 < Kbeta.card := Finset.card_pos.2 ⟨M₁.val v, hmem⟩
    omega
  have hrk_x_vstar_M1 : ∀ x ∈ S, p.partnerRank x (vstar p (M₁.val x)) ≤ m := by
    intro x hx
    have hDx_eq : (D x).card = m - 1 := by
      by_contra hne_card
      have hge := (hD_info x hx).2.1
      have hgt : m - 1 < (D x).card := by omega
      have hsum_gt : S.card * (m - 1) < ∑ v ∈ S, (D v).card := by
        calc S.card * (m - 1) = ∑ _v ∈ S, (m - 1) := by simp
          _ < ∑ v ∈ S, (D v).card :=
            Finset.sum_lt_sum (fun v hv => (hD_info v hv).2.1) ⟨x, hx, hgt⟩
      omega
    let T := Finset.univ.filter (fun z => p.partnerRank x z ≤ m)
    have hTU_sub := (hD_info x hx).1
    have hdisj : Disjoint (D x) (T ∩ U) := by
      rw [Finset.disjoint_left]
      intro z hzD hzTU
      exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 hzTU).2).2 (Finset.mem_filter.1 hzD).1
    have hunion : D x ∪ (T ∩ U) = T := by
      ext z
      simp only [D, T, U, Finset.mem_union, Finset.mem_inter, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_sdiff]
      by_cases hzS : z ∈ S <;> simp [hzS]
    have hTcard : T.card = m := card_filter_rk_le p x m (by omega)
    have hTUcard : (T ∩ U).card = 1 := by
      have hsum := Finset.card_union_of_disjoint hdisj
      rw [hunion, hTcard, hDx_eq] at hsum
      omega
    have hTUeq : T ∩ U = {vstar p (M₁.val x)} :=
      Finset.eq_of_subset_of_card_le hTU_sub (by simp [hTUcard])
    have hvmem : vstar p (M₁.val x) ∈ T ∩ U := by rw [hTUeq]; simp
    exact (Finset.mem_filter.1 (Finset.mem_inter.1 hvmem).1).2
  have htourn : ∀ x ∈ S, ∀ z ∈ S, z ≠ x → z ≠ M₁.val x →
      p.partnerRank x z ≤ m ∨ p.partnerRank z x ≤ m := by
    have heq_union : Arcs ∪ Arcs.image Prod.swap = NonM1 := by
      refine Finset.eq_of_subset_of_card_le hArcs_sub ?_
      rw [Finset.card_union_of_disjoint hArcs_disj, hArcs_swap_card, hNonM1_card]
      omega
    intro x hx z hz hzx hzM
    have hmem : (x, z) ∈ NonM1 := Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx, hz⟩, hzx, hzM⟩
    rw [← heq_union, Finset.mem_union] at hmem
    rcases hmem with h1 | h2
    · exact Or.inl (Finset.mem_filter.1 h1).2
    · obtain ⟨⟨z', x'⟩, h2', heq⟩ := Finset.mem_image.1 h2
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact Or.inr (Finset.mem_filter.1 h2').2
  have hvstar_ne_M1 : ∀ x ∈ S, vstar p x ≠ vstar p (M₁.val x) := by
    intro x hx h
    have h1 := hrk_x_vstar_M1 x hx
    rw [← h, rk_vstar] at h1
    omega
  have hswap : ∀ x ∈ S, ∀ z ∈ S, z ≠ x → z ≠ M₁.val x →
      p.partnerRank (M₁.val x) (M₁.val z) ≤ m → vstar p x = vstar p (M₁.val z) := by
    intro x hx z hz hzx hzMx hyw_le
    let y := M₁.val x
    let w := M₁.val z
    have hzy : z ≠ y := hzMx
    have hyS : y ∈ S := matchedSet_map M₁ hx
    have hwS : w ∈ S := matchedSet_map M₁ hz
    have hxy : y ≠ x := (mem_matchedSet M₁ x).1 hx
    have hwz : w ≠ z := (mem_matchedSet M₁ z).1 hz
    have hwx : w ≠ x := fun h => hzMx (by rw [← M₁.property z]; change M₁.val w = y; rw [h])
    have hwy : w ≠ y := fun h => hzx (by rw [← M₁.property z]; change M₁.val w = x; rw [h, M₁.property x])
    let u := vstar p w
    have huU : u ∈ U := hvstar_in_U w hwS
    have huS : u ∉ S := (Finset.mem_sdiff.1 huU).2
    have hzu : z ≠ u := fun h => huS (h ▸ hz)
    have hxu : x ≠ u := fun h => huS (h ▸ hx)
    have hyu : y ≠ u := fun h => huS (h ▸ hyS)
    have hwu : w ≠ u := fun h => huS (h ▸ hwS)
    have hrz_u : p.partnerRank z u ≤ m := hrk_x_vstar_M1 z hz
    obtain ⟨M₂, hM₂ms, hM₂neut⟩ := exists_neutralizing_pm hm p hno hM₁ huU hx
    let M_e1 := eraseEdge M₁ x y rfl
    have hM_e1_zw : M_e1.val z = w := by simp [M_e1, eraseEdge_apply, hzx, hzy, w]
    let M_e2 := eraseEdge M_e1 z w hM_e1_zw
    have hM_e2_H : IsHMatching p M_e2 :=
      isAcceptable_eraseEdge M_e1 (isAcceptable_eraseEdge M₁ hM₁.1 rfl) hM_e1_zw
    have hM_e2_ms : matchedSet M_e2 = (((S.erase x).erase y).erase z).erase w := by
      rw [matchedSet_eraseEdge M_e1 hM_e1_zw, matchedSet_eraseEdge M₁ rfl]
    have hdisj : Disjoint (matchedSet M_e2) (matchedSet M₂) := by
      rw [hM_e2_ms, hM₂ms]
      exact Finset.disjoint_sdiff.mono
        ((((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)).trans
          (Finset.erase_subset _ _)).trans (Finset.erase_subset _ _))
        (Finset.erase_subset _ _)
    let μ₀ := combineMatchings (matchedSet M_e2) M_e2 M₂ Finset.Subset.rfl hdisj
    have hμ₀_ms : matchedSet μ₀ = matchedSet M_e2 ∪ matchedSet M₂ :=
      matchedSet_combineMatchings _ _ _ Finset.Subset.rfl hdisj
    have hfix0 : ∀ v, v ∉ matchedSet M_e2 → v ∉ matchedSet M₂ → μ₀.val v = v := by
      intro v hv1 hv2
      by_contra h
      rcases Finset.mem_union.1 (hμ₀_ms ▸ (mem_matchedSet μ₀ v).2 h) with h1 | h2
      · exact hv1 h1
      · exact hv2 h2
    have hnot_M_e2 : ∀ v, v ∈ ({x, y, z, w, u} : Finset (Fin (2 * m + 1))) → v ∉ matchedSet M_e2 := by
      intro v hv; rw [hM_e2_ms]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · simp
      · simp
      · simp
      · simp
      · simp [huS]
    have hnot_M₂ : ∀ v, v ∈ ({x, y, z, w, u} : Finset (Fin (2 * m + 1))) → v ∉ matchedSet M₂ := by
      intro v hv; rw [hM₂ms]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · simp [hx, S]
      · simp [hyS, S]
      · simp [hz, S]
      · simp [hwS, S]
      · simp
    have hz_fix0 : μ₀.val z = z := hfix0 z (hnot_M_e2 z (by simp)) (hnot_M₂ z (by simp))
    have hu_fix0 : μ₀.val u = u := hfix0 u (hnot_M_e2 u (by simp)) (hnot_M₂ u (by simp))
    let μ₁ := addEdge μ₀ z u hz_fix0 hu_fix0
    have hy_fix1 : μ₁.val y = y := by
      simp [μ₁, addEdge_apply, hzy.symm, hyu, hfix0 y (hnot_M_e2 y (by simp)) (hnot_M₂ y (by simp))]
    have hw_fix1 : μ₁.val w = w := by
      simp [μ₁, addEdge_apply, hwz, hwu, hfix0 w (hnot_M_e2 w (by simp)) (hnot_M₂ w (by simp))]
    let μ := addEdge μ₁ y w hy_fix1 hw_fix1
    have hμ_M_e2 : ∀ v ∈ matchedSet M_e2, μ.val v = M_e2.val v := by
      intro v hv
      have hv_not : v ≠ x ∧ v ≠ y ∧ v ≠ z ∧ v ≠ w ∧ v ≠ u := by
        rw [hM_e2_ms] at hv
        simp only [Finset.mem_erase] at hv
        exact ⟨hv.2.2.2.1, hv.2.2.1, hv.2.1, hv.1, fun h => huS (h ▸ hv.2.2.2.2)⟩
      simp [μ, addEdge_apply, hv_not.2.1, hv_not.2.2.2.1, μ₁, hv_not.2.2.1, hv_not.2.2.2.2,
        μ₀, combineMatchings_apply, hv]
    have hμ_M₂ : ∀ v ∈ U.erase u, μ.val v = M₂.val v := by
      intro v hv
      have hvu : v ≠ u := (Finset.mem_erase.1 hv).1
      have hvS : v ∉ S := (Finset.mem_sdiff.1 (Finset.mem_erase.1 hv).2).2
      have hv_not : v ≠ y ∧ v ≠ w ∧ v ≠ z :=
        ⟨fun h => hvS (h ▸ hyS), fun h => hvS (h ▸ hwS), fun h => hvS (h ▸ hz)⟩
      have hv_not_e2 : v ∉ matchedSet M_e2 := by
        rw [hM_e2_ms]; intro h; apply hvS
        exact (((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)).trans
          (Finset.erase_subset _ _)).trans (Finset.erase_subset _ _) h
      simp [μ, addEdge_apply, hv_not.1, hv_not.2.1, μ₁, hv_not.2.2, hvu,
        μ₀, combineMatchings_apply, hv_not_e2]
    have hμy : μ.val y = w := by simp [μ, addEdge_apply]
    have hμw : μ.val w = y := by simp [μ, addEdge_apply, hwy]
    have hμz : μ.val z = u := by simp [μ, addEdge_apply, hzy, hwz.symm, μ₁]
    have hμu : μ.val u = z := by simp [μ, addEdge_apply, hyu.symm, hwu.symm, μ₁, hzu.symm]
    have hμx : μ.val x = x := by
      simp [μ, addEdge_apply, hxy.symm, hwx.symm, μ₁, hzx.symm, hxu,
        hfix0 x (hnot_M_e2 x (by simp)) (hnot_M₂ x (by simp))]
    have hμ_single : ∀ v, μ.val v = v ↔ v = x := by
      intro v
      constructor
      · intro hv
        by_contra hvx
        by_cases hvS : v ∈ S
        · by_cases hvy : v = y
          · subst hvy; rw [hμy] at hv; exact hwy hv
          · by_cases hvz : v = z
            · subst hvz; rw [hμz] at hv; exact hzu hv.symm
            · by_cases hvw : v = w
              · subst hvw; rw [hμw] at hv; exact hwy hv.symm
              · have hve2 : v ∈ matchedSet M_e2 := by
                  rw [hM_e2_ms]
                  exact Finset.mem_erase.2 ⟨hvw, Finset.mem_erase.2 ⟨hvz,
                    Finset.mem_erase.2 ⟨hvy, Finset.mem_erase.2 ⟨hvx, hvS⟩⟩⟩⟩
                rw [hμ_M_e2 v hve2] at hv
                exact (mem_matchedSet M_e2 v).1 hve2 hv
        · by_cases hvu : v = u
          · subst hvu; rw [hμu] at hv; exact hzu hv
          · have hv_er : v ∈ U.erase u :=
              Finset.mem_erase.2 ⟨hvu, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hvS⟩⟩
            rw [hμ_M₂ v hv_er] at hv
            exact (mem_matchedSet M₂ v).1 (hM₂ms ▸ hv_er) hv
      · rintro rfl; exact hμx
    obtain ⟨a, b, hblk⟩ := exists_blocking_of_not_stable p hno μ
    have hsafe : ∀ v, v ∈ matchedSet M_e2 ∨ v = y ∨ v = z → p.partnerRank v (μ.val v) ≤ m := by
      intro v hv
      rcases hv with hve2 | rfl | rfl
      · rw [hμ_M_e2 v hve2]; exact rk_M_le_m_of_mem_matchedSet p hM_e2_H hve2
      · rw [hμy]; exact hyw_le
      · rw [hμz]; exact hrz_u
    have hmem_rem : ∀ v, ¬ (v ∈ matchedSet M_e2 ∨ v = y ∨ v = z) →
        v = x ∨ v = w ∨ v ∈ U := by
      intro v hv
      push Not at hv
      by_cases hvS : v ∈ S
      · by_cases hvx : v = x
        · exact Or.inl hvx
        · by_cases hvw : v = w
          · exact Or.inr (Or.inl hvw)
          · exfalso; apply hv.1; rw [hM_e2_ms]
            exact Finset.mem_erase.2 ⟨hvw, Finset.mem_erase.2 ⟨hv.2.2,
              Finset.mem_erase.2 ⟨hv.2.1, Finset.mem_erase.2 ⟨hvx, hvS⟩⟩⟩⟩
      · exact Or.inr (Or.inr (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hvS⟩))
    have ha_rem : a = x ∨ a = w ∨ a ∈ U := hmem_rem a (fun h =>
      not_blocking_of_safe_left p (hsafe a h) hblk)
    have hb_rem : b = x ∨ b = w ∨ b ∈ U := hmem_rem b (fun h =>
      not_blocking_of_safe_right p (hsafe b h) hblk)
    have hnonH : ¬ (HGraph p).Adj a b := by
      have hab_ne : a ≠ b := (SimpleGraph.top_adj _ _).1 hblk.1
      rcases ha_rem with hax | haw | haU
      · rcases hb_rem with hbx | hbw | hbU
        · exact absurd (hax.trans hbx.symm) hab_ne
        · rw [hax, hbw]; exact hno_edge x hx w hwS hwx hwy
        · exact fun h => U_isolated hm p hno hM₁ hbU a h.symm
      · rcases hb_rem with hbx | hbw | hbU
        · rw [haw, hbx]; exact fun h => hno_edge x hx w hwS hwx hwy h.symm
        · exact absurd (haw.trans hbw.symm) hab_ne
        · exact fun h => U_isolated hm p hno hM₁ hbU a h.symm
      · exact U_isolated hm p hno hM₁ haU b
    have hone_x : ∃ v, v ≠ x ∧ IsKBlockingPair ⊤ p.partnerRank m μ x v ∧
        (v = w ∨ v ∈ U) := by
      have hab_ne : a ≠ b := (SimpleGraph.top_adj _ _).1 hblk.1
      by_cases hax : a = x
      · subst hax
        rcases hb_rem with hbx | hbw | hbU
        · exact absurd hbx.symm hab_ne
        · exact ⟨b, hab_ne.symm, hblk, Or.inl hbw⟩
        · exact ⟨b, hab_ne.symm, hblk, Or.inr hbU⟩
      · by_cases hbx : b = x
        · subst hbx
          rcases ha_rem with hax' | haw | haU
          · exact absurd hax' hax
          · exact ⟨a, hab_ne, blocking_symm p hblk, Or.inl haw⟩
          · exact ⟨a, hab_ne, blocking_symm p hblk, Or.inr haU⟩
        · exact absurd hblk (not_blocking_matched_matched_non_H p hnonH
            (fun h => hax ((hμ_single a).1 h)) (fun h => hbx ((hμ_single b).1 h)))
    obtain ⟨v, hvx, hblkv, hv_rem⟩ := hone_x
    have hv_nonH : ¬ (HGraph p).Adj x v := by
      rcases hv_rem with rfl | hvU
      · exact hno_edge x hx w hwS hwx hwy
      · exact fun h => U_isolated hm p hno hM₁ hvU x h.symm
    obtain ⟨hv_vstar, hrkv⟩ := blocking_single_matched_non_H p hv_nonH hμx
      (fun h => hvx ((hμ_single v).1 h)) hblkv
    rcases hv_rem with rfl | hvU
    · exfalso
      have hvxU : vstar p x ∈ U := hvstar_in_U x hx
      rw [← hv_vstar] at hvxU
      exact (Finset.mem_sdiff.1 hvxU).2 hwS
    · by_cases hvu : v = u
      · rw [← hv_vstar, hvu]
      · exfalso
        have hv_er : v ∈ U.erase u := Finset.mem_erase.2 ⟨hvu, hvU⟩
        rw [hμ_M₂ v hv_er] at hrkv
        exact hM₂neut v hv_er hv_vstar hrkv
  have hcontra : ∀ x ∈ S, ∀ z ∈ S, z ≠ x → z ≠ M₁.val x →
      vstar p x = vstar p (M₁.val z) → False := by
    intro x hx z hz hzx hzMx heqv
    let y := M₁.val x
    let w := M₁.val z
    have hyS : y ∈ S := matchedSet_map M₁ hx
    have hwS : w ∈ S := matchedSet_map M₁ hz
    have hwx : w ≠ x := fun h => hzMx (by rw [← M₁.property z]; change M₁.val w = y; rw [h])
    have hwy : w ≠ y := fun h => hzx (by rw [← M₁.property z]; change M₁.val w = x; rw [h, M₁.property x])
    rcases htourn x hx w hwS hwx hwy with hxw | hwx_le
    · have h1 := hswap y hyS z hz hzMx (by rw [M₁.property x]; exact hzx)
        (by rw [M₁.property x]; exact hxw)
      exact hvstar_ne_M1 x hx (heqv.trans h1.symm)
    · have h1 := hswap z hz y hyS hzMx.symm hwy.symm
        (by rw [M₁.property x]; exact hwx_le)
      rw [M₁.property x] at h1
      exact hvstar_ne_M1 z hz (h1.trans heqv)
  have hS4 : 4 ≤ S.card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega : 0 < S.card)
  have hMx_in : M₁.val x ∈ S.erase x :=
    Finset.mem_erase.2 ⟨(mem_matchedSet M₁ x).1 hx, matchedSet_map M₁ hx⟩
  have hrem_pos : 0 < ((S.erase x).erase (M₁.val x)).card := by
    rw [Finset.card_erase_of_mem hMx_in, Finset.card_erase_of_mem hx]; omega
  obtain ⟨z, hz_mem⟩ := Finset.card_pos.1 hrem_pos
  have hzMx : z ≠ M₁.val x := (Finset.mem_erase.1 hz_mem).1
  have hzx : z ≠ x := (Finset.mem_erase.1 (Finset.mem_erase.1 hz_mem).2).1
  have hz : z ∈ S := (Finset.mem_erase.1 (Finset.mem_erase.1 hz_mem).2).2
  have hyS : M₁.val x ∈ S := matchedSet_map M₁ hx
  have hwS : M₁.val z ∈ S := matchedSet_map M₁ hz
  have hwy : M₁.val z ≠ M₁.val x := fun h => hzx (M₁.val.injective h)
  have hwx : M₁.val z ≠ x := fun h => hzMx (by rw [← M₁.property z, h])
  rcases htourn (M₁.val x) hyS (M₁.val z) hwS hwy (by rw [M₁.property x]; exact hwx) with hyw | hwy_le
  · exact hcontra x hx z hz hzx hzMx (hswap x hx z hz hzx hzMx hyw)
  · exact hcontra z hz x hx hzx.symm hwx.symm (hswap z hz x hx hzx.symm hwx.symm hwy_le)

end Step4

/-! ### Step 5: Cross-Component Swaps, Global Ordered-Pair Inequality, and Final Contradiction -/

section Step5

/-- Helper: given `x, b ∈ S` in distinct components of `H[S]`, `y ∈ R x`, and `z ∈ R b`,
there exists an `H`-matching on `S \ {x, y, b, z}`. -/
private lemma exists_HMatching_erase_four (p : CompleteProfile (2 * m + 1))
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x y b z : Fin (2 * m + 1)}
    (hx : x ∈ matchedSet M₁) (hb : b ∈ matchedSet M₁)
    (hcomp_ne : comp p M₁ x ≠ comp p M₁ b)
    (hy : y ∈ Rset p M₁ x) (hz : z ∈ Rset p M₁ b) :
    ∃ M'' : Matching (Fin (2 * m + 1)),
      IsHMatching p M'' ∧
      matchedSet M'' = ((((matchedSet M₁).erase x).erase y).erase b).erase z := by
  let S := matchedSet M₁
  let Cx := comp p M₁ x
  let Cb := comp p M₁ b
  have hdisj_xb : Disjoint Cx Cb := comp_disjoint_of_ne p hcomp_ne
  obtain ⟨_, _, Mx, hMxH, hMxms⟩ := (mem_Rset p).1 hy
  obtain ⟨_, _, Mb, hMbH, hMbms⟩ := (mem_Rset p).1 hz
  have hxCx : x ∈ Cx := self_mem_comp p hx
  have hyCx : y ∈ Cx := Rset_subset_comp p hM₁ hx hy
  have hbCb : b ∈ Cb := self_mem_comp p hb
  have hzCb : z ∈ Cb := Rset_subset_comp p hM₁ hb hz
  have hMx_sub : matchedSet Mx ⊆ S := by
    rw [hMxms]; exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hMb_sub : matchedSet Mb ⊆ S := by
    rw [hMbms]; exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  let μx := restrictMatching Cx Mx (H_matching_preserves_comp p hMxH hMx_sub x)
  let μb := restrictMatching Cb Mb (H_matching_preserves_comp p hMbH hMb_sub b)
  let Rest := S \ (Cx ∪ Cb)
  have hM1_rest : ∀ v ∈ Rest, M₁.val v ∈ Rest := by
    intro v hv
    obtain ⟨hvS, hvnot⟩ := Finset.mem_sdiff.1 hv
    refine Finset.mem_sdiff.2 ⟨matchedSet_map M₁ hvS, fun h => hvnot ?_⟩
    rcases Finset.mem_union.1 h with hCx | hCb
    · exact Finset.mem_union_left _ (by
        rw [← M₁.property v]; exact H_matching_preserves_comp p hM₁.1 Finset.Subset.rfl x _ hCx)
    · exact Finset.mem_union_right _ (by
        rw [← M₁.property v]; exact H_matching_preserves_comp p hM₁.1 Finset.Subset.rfl b _ hCb)
  let μr := restrictMatching Rest M₁ hM1_rest
  have hμx_sub : matchedSet μx ⊆ Cx := by
    rw [matchedSet_restrictMatching]; exact Finset.inter_subset_left
  have hμb_sub : matchedSet μb ⊆ Cb := by
    rw [matchedSet_restrictMatching]; exact Finset.inter_subset_left
  have hμr_sub : matchedSet μr ⊆ Rest := by
    rw [matchedSet_restrictMatching]; exact Finset.inter_subset_left
  let μxb := combineMatchings Cx μx μb hμx_sub (hdisj_xb.mono_right hμb_sub)
  have hμxb_sub : matchedSet μxb ⊆ Cx ∪ Cb := by
    rw [matchedSet_combineMatchings]; exact Finset.union_subset_union hμx_sub hμb_sub
  let M'' := combineMatchings (Cx ∪ Cb) μxb μr hμxb_sub (Finset.disjoint_sdiff.mono_right hμr_sub)
  have hM''H : IsHMatching p M'' :=
    isAcceptable_combineMatchings _ _ _ _ _
      (isAcceptable_combineMatchings _ _ _ _ _
        (isAcceptable_restrictMatching _ _ _ hMxH) (isAcceptable_restrictMatching _ _ _ hMbH))
      (isAcceptable_restrictMatching _ _ _ hM₁.1)
  refine ⟨M'', hM''H, ?_⟩
  rw [matchedSet_combineMatchings, matchedSet_combineMatchings,
    matchedSet_restrictMatching, matchedSet_restrictMatching, matchedSet_restrictMatching,
    hMxms, hMbms]
  ext v
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_erase, Finset.mem_sdiff, Rest]
  constructor
  · rintro ((⟨hvCx, hvy, hvx, hvS⟩ | ⟨hvCb, hvz, hvb, hvS⟩) | ⟨⟨hvS, hvnot⟩, _⟩)
    · have hvb : v ≠ b := fun h => Finset.disjoint_left.1 hdisj_xb hvCx (h ▸ hbCb)
      have hvz : v ≠ z := fun h => Finset.disjoint_left.1 hdisj_xb hvCx (h ▸ hzCb)
      exact ⟨hvz, hvb, hvy, hvx, hvS⟩
    · have hvx : v ≠ x := fun h => Finset.disjoint_right.1 hdisj_xb hvCb (h ▸ hxCx)
      have hvy : v ≠ y := fun h => Finset.disjoint_right.1 hdisj_xb hvCb (h ▸ hyCx)
      exact ⟨hvz, hvb, hvy, hvx, hvS⟩
    · have hvx : v ≠ x := fun h => hvnot (Or.inl (h ▸ hxCx))
      have hvy : v ≠ y := fun h => hvnot (Or.inl (h ▸ hyCx))
      have hvb : v ≠ b := fun h => hvnot (Or.inr (h ▸ hbCb))
      have hvz : v ≠ z := fun h => hvnot (Or.inr (h ▸ hzCb))
      exact ⟨hvz, hvb, hvy, hvx, hvS⟩
  · rintro ⟨hvz, hvb, hvy, hvx, hvS⟩
    by_cases hvCx : v ∈ Cx
    · exact Or.inl (Or.inl ⟨hvCx, hvy, hvx, hvS⟩)
    · by_cases hvCb : v ∈ Cb
      · exact Or.inl (Or.inr ⟨hvCb, hvz, hvb, hvS⟩)
      · exact Or.inr ⟨⟨hvS, by simp [hvCx, hvCb]⟩, hvS⟩

/-- Helper: given `x, b ∈ S` in distinct components, `y ∈ R x`, `z ∈ R b`, `u ∈ U`,
a neutralizing PM `M₂` on `U.erase u`, and `M''` on `S \ {x, y, b, z}`, construct the
matching `M'' ∪ {{x, b}, {y, u}} ∪ M₂` leaving ONLY `z` single, and extract its blocking pair
inside `{x, y, b, z} ∪ U`. -/
private lemma four_swap_matching (p : CompleteProfile (2 * m + 1))
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x y b z u : Fin (2 * m + 1)}
    (hx : x ∈ matchedSet M₁) (hb : b ∈ matchedSet M₁)
    (hcomp_ne : comp p M₁ x ≠ comp p M₁ b)
    (hy : y ∈ Rset p M₁ x) (hz : z ∈ Rset p M₁ b)
    (hu : u ∈ Finset.univ \ matchedSet M₁)
    {M₂ : Matching (Fin (2 * m + 1))}
    (hM₂ms : matchedSet M₂ = (Finset.univ \ matchedSet M₁).erase u) :
    ∃ μ : Matching (Fin (2 * m + 1)),
      (∀ v ∈ ((((matchedSet M₁).erase x).erase y).erase b).erase z, p.partnerRank v (μ.val v) ≤ m) ∧
      (∀ v ∈ (Finset.univ \ matchedSet M₁).erase u, μ.val v = M₂.val v) ∧
      μ.val x = b ∧ μ.val b = x ∧ μ.val y = u ∧ μ.val u = y ∧
      (∀ v, μ.val v = v ↔ v = z) := by
  let S := matchedSet M₁
  let U := Finset.univ \ S
  have hyS : y ∈ S := ((mem_Rset p).1 hy).1
  have hzS : z ∈ S := ((mem_Rset p).1 hz).1
  have hdisj_xb : Disjoint (comp p M₁ x) (comp p M₁ b) := comp_disjoint_of_ne p hcomp_ne
  have hxCx : x ∈ comp p M₁ x := self_mem_comp p hx
  have hyCx : y ∈ comp p M₁ x := Rset_subset_comp p hM₁ hx hy
  have hbCb : b ∈ comp p M₁ b := self_mem_comp p hb
  have hzCb : z ∈ comp p M₁ b := Rset_subset_comp p hM₁ hb hz
  have hxy : y ≠ x := ((mem_Rset p).1 hy).2.1
  have hzb : z ≠ b := ((mem_Rset p).1 hz).2.1
  have hxb : x ≠ b := fun h => Finset.disjoint_left.1 hdisj_xb hxCx (h ▸ hbCb)
  have hxz : x ≠ z := fun h => Finset.disjoint_left.1 hdisj_xb hxCx (h ▸ hzCb)
  have hyb : y ≠ b := fun h => Finset.disjoint_left.1 hdisj_xb hyCx (h ▸ hbCb)
  have hyz : y ≠ z := fun h => Finset.disjoint_left.1 hdisj_xb hyCx (h ▸ hzCb)
  have huS : u ∉ S := (Finset.mem_sdiff.1 hu).2
  have hxu : x ≠ u := fun h => huS (h ▸ hx)
  have hyu : y ≠ u := fun h => huS (h ▸ hyS)
  have hbu : b ≠ u := fun h => huS (h ▸ hb)
  have hzu : z ≠ u := fun h => huS (h ▸ hzS)
  obtain ⟨M'', hM''H, hM''ms⟩ := exists_HMatching_erase_four p hM₁ hx hb hcomp_ne hy hz
  have hdisj1 : Disjoint (matchedSet M'') (matchedSet M₂) := by
    rw [hM''ms, hM₂ms]
    exact Finset.disjoint_sdiff.mono
      ((((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)).trans
        (Finset.erase_subset _ _)).trans (Finset.erase_subset _ _))
      (Finset.erase_subset _ _)
  let μ₀ := combineMatchings (matchedSet M'') M'' M₂ Finset.Subset.rfl hdisj1
  have hμ₀_ms : matchedSet μ₀ = matchedSet M'' ∪ matchedSet M₂ :=
    matchedSet_combineMatchings _ _ _ Finset.Subset.rfl hdisj1
  have hfix0 : ∀ v, v ∉ matchedSet M'' → v ∉ matchedSet M₂ → μ₀.val v = v := by
    intro v hv1 hv2
    by_contra h
    rcases Finset.mem_union.1 (hμ₀_ms ▸ (mem_matchedSet μ₀ v).2 h) with h1 | h2
    · exact hv1 h1
    · exact hv2 h2
  have hnot_M'' : ∀ v, v ∈ ({x, y, b, z, u} : Finset (Fin (2 * m + 1))) → v ∉ matchedSet M'' := by
    intro v hv; rw [hM''ms]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · simp
    · simp [huS, S]
  have hnot_M₂ : ∀ v, v ∈ ({x, y, b, z, u} : Finset (Fin (2 * m + 1))) → v ∉ matchedSet M₂ := by
    intro v hv; rw [hM₂ms]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · simp [hx]
    · simp [hyS, S]
    · simp [hb]
    · simp [hzS, S]
    · simp
  have hx_fix0 : μ₀.val x = x := hfix0 x (hnot_M'' x (by simp)) (hnot_M₂ x (by simp))
  have hb_fix0 : μ₀.val b = b := hfix0 b (hnot_M'' b (by simp)) (hnot_M₂ b (by simp))
  let μ₁ := addEdge μ₀ x b hx_fix0 hb_fix0
  have hy_fix1 : μ₁.val y = y := by
    simp [μ₁, addEdge_apply, hxy, hyb, hfix0 y (hnot_M'' y (by simp)) (hnot_M₂ y (by simp))]
  have hu_fix1 : μ₁.val u = u := by
    simp [μ₁, addEdge_apply, hxu.symm, hbu.symm, hfix0 u (hnot_M'' u (by simp)) (hnot_M₂ u (by simp))]
  let μ := addEdge μ₁ y u hy_fix1 hu_fix1
  have hμ_M'' : ∀ v ∈ matchedSet M'', μ.val v = M''.val v := by
    intro v hv
    have hv_not : v ≠ x ∧ v ≠ y ∧ v ≠ b ∧ v ≠ z ∧ v ≠ u := by
      rw [hM''ms] at hv
      simp only [Finset.mem_erase] at hv
      exact ⟨hv.2.2.2.1, hv.2.2.1, hv.2.1, hv.1, fun h => huS (h ▸ hv.2.2.2.2)⟩
    simp [μ, addEdge_apply, hv_not.2.1, hv_not.2.2.2.2, μ₁, hv_not.1, hv_not.2.2.1,
      μ₀, combineMatchings_apply, hv]
  have hμ_M₂ : ∀ v ∈ U.erase u, μ.val v = M₂.val v := by
    intro v hv
    have hvu : v ≠ u := (Finset.mem_erase.1 hv).1
    have hvS : v ∉ S := (Finset.mem_sdiff.1 (Finset.mem_erase.1 hv).2).2
    have hv_not : v ≠ y ∧ v ≠ x ∧ v ≠ b :=
      ⟨fun h => hvS (h ▸ hyS), fun h => hvS (h ▸ hx), fun h => hvS (h ▸ hb)⟩
    have hv_not'' : v ∉ matchedSet M'' := by
      rw [hM''ms]; intro h; apply hvS
      exact (((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)).trans
        (Finset.erase_subset _ _)).trans (Finset.erase_subset _ _) h
    simp [μ, addEdge_apply, hv_not.1, hvu, μ₁, hv_not.2.1, hv_not.2.2,
      μ₀, combineMatchings_apply, hv_not'']
  have hμy : μ.val y = u := by simp [μ, addEdge_apply]
  have hμu : μ.val u = y := by simp [μ, addEdge_apply, hyu.symm]
  have hμx : μ.val x = b := by simp [μ, addEdge_apply, hxy.symm, hxu, μ₁]
  have hμb : μ.val b = x := by simp [μ, addEdge_apply, hyb.symm, hbu, μ₁, hxb.symm]
  have hμz : μ.val z = z := by
    simp [μ, addEdge_apply, hyz.symm, hzu, μ₁, hxz.symm, hzb,
      hfix0 z (hnot_M'' z (by simp)) (hnot_M₂ z (by simp))]
  refine ⟨μ, ?_, hμ_M₂, hμx, hμb, hμy, hμu, ?_⟩
  · intro v hv
    have hvM'' : v ∈ matchedSet M'' := hM''ms ▸ hv
    rw [hμ_M'' v hvM'']
    exact rk_M_le_m_of_mem_matchedSet p hM''H hvM''
  · intro v
    constructor
    · intro hv
      by_contra hvz
      by_cases hvS : v ∈ S
      · by_cases hvx : v = x
        · subst hvx; rw [hμx] at hv; exact hxb hv.symm
        · by_cases hvy : v = y
          · subst hvy; rw [hμy] at hv; exact hyu hv.symm
          · by_cases hvb : v = b
            · subst hvb; rw [hμb] at hv; exact hxb hv
            · have hv'' : v ∈ matchedSet M'' := by
                rw [hM''ms]
                exact Finset.mem_erase.2 ⟨hvz, Finset.mem_erase.2 ⟨hvb,
                  Finset.mem_erase.2 ⟨hvy, Finset.mem_erase.2 ⟨hvx, hvS⟩⟩⟩⟩
              rw [hμ_M'' v hv''] at hv
              exact (mem_matchedSet M'' v).1 hv'' hv
      · by_cases hvu : v = u
        · subst hvu; rw [hμu] at hv; exact hyu hv
        · have hv_er : v ∈ U.erase u :=
            Finset.mem_erase.2 ⟨hvu, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hvS⟩⟩
          rw [hμ_M₂ v hv_er] at hv
          exact (mem_matchedSet M₂ v).1 (hM₂ms ▸ hv_er) hv
    · rintro rfl; exact hμz

/-- Claim 5.1 (C1): For `x, b ∈ S` in distinct components, `y ∈ R x`, `z ∈ R b` with
`H.Adj b z`, `rk x b < rk x y + m`, and `rk b x < rk b z + m`, either
`x = vstar z ∧ rk x z + m ≤ rk x b` or `y = vstar z ∧ ∀ u ∈ U, rk y z + m ≤ rk y u`. -/
private lemma claim_5_1 (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x y b z : Fin (2 * m + 1)}
    (hx : x ∈ matchedSet M₁) (hb : b ∈ matchedSet M₁)
    (hcomp_ne : comp p M₁ x ≠ comp p M₁ b)
    (hy : y ∈ Rset p M₁ x) (hz : z ∈ Rset p M₁ b)
    (hbz_H : (HGraph p).Adj b z)
    (hlt_xb : p.partnerRank x b < p.partnerRank x y + m)
    (hlt_bx : p.partnerRank b x < p.partnerRank b z + m) :
    (x = vstar p z ∧ p.partnerRank x z + m ≤ p.partnerRank x b) ∨
    (y = vstar p z ∧ ∀ u ∈ Finset.univ \ matchedSet M₁,
      p.partnerRank y z + m ≤ p.partnerRank y u) := by
  let S := matchedSet M₁
  let U := Finset.univ \ S
  have hyS : y ∈ S := ((mem_Rset p).1 hy).1
  have hzS : z ∈ S := ((mem_Rset p).1 hz).1
  have hxy : y ≠ x := ((mem_Rset p).1 hy).2.1
  have hdisj_xb : Disjoint (comp p M₁ x) (comp p M₁ b) := comp_disjoint_of_ne p hcomp_ne
  have hxCx : x ∈ comp p M₁ x := self_mem_comp p hx
  have hyCx : y ∈ comp p M₁ x := Rset_subset_comp p hM₁ hx hy
  have hbCb : b ∈ comp p M₁ b := self_mem_comp p hb
  have hzCb : z ∈ comp p M₁ b := Rset_subset_comp p hM₁ hb hz
  have hU3 : 3 ≤ U.card := three_le_U_card p hno hM₁
  have hfor_u : ∀ u ∈ U, u ≠ vstar p z →
      (x = vstar p z ∧ p.partnerRank x z + m ≤ p.partnerRank x b) ∨
      (y = vstar p z ∧ p.partnerRank y z + m ≤ p.partnerRank y u) := by
    intro u huU huvz
    obtain ⟨M₂, hM₂ms, hM₂neut⟩ := exists_neutralizing_pm hm p hno hM₁ huU hzS
    obtain ⟨μ, hsafe_rest, hμ_M₂, hμx, hμb, hμy, _, hμ_single⟩ :=
      four_swap_matching p hM₁ hx hb hcomp_ne hy hz huU hM₂ms
    have hμz : μ.val z = z := (hμ_single z).2 rfl
    obtain ⟨p₁, p₂, hblk⟩ := exists_blocking_of_not_stable p hno μ
    have hp_rem : ∀ v, v ∉ ((((S.erase x).erase y).erase b).erase z) →
        v = x ∨ v = y ∨ v = b ∨ v = z ∨ v ∈ U := by
      intro v hv
      by_cases hvS : v ∈ S
      · by_cases hvx : v = x
        · exact Or.inl hvx
        · by_cases hvy : v = y
          · exact Or.inr (Or.inl hvy)
          · by_cases hvb : v = b
            · exact Or.inr (Or.inr (Or.inl hvb))
            · by_cases hvz : v = z
              · exact Or.inr (Or.inr (Or.inr (Or.inl hvz)))
              · exfalso; apply hv
                exact Finset.mem_erase.2 ⟨hvz, Finset.mem_erase.2 ⟨hvb,
                  Finset.mem_erase.2 ⟨hvy, Finset.mem_erase.2 ⟨hvx, hvS⟩⟩⟩⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hvS⟩))))
    have hp1_rem := hp_rem p₁ (fun h => not_blocking_of_safe_left p (hsafe_rest p₁ h) hblk)
    have hp2_rem := hp_rem p₂ (fun h => not_blocking_of_safe_right p (hsafe_rest p₂ h) hblk)
    have hnot_xy : ¬ ((p₁ = x ∧ p₂ = y) ∨ (p₁ = y ∧ p₂ = x)) := by
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · have h1 := hblk.2.2.1; rw [hμx] at h1; omega
      · have h1 := hblk.2.2.2; rw [hμx] at h1; omega
    have hnot_bz : ¬ ((p₁ = b ∧ p₂ = z) ∨ (p₁ = z ∧ p₂ = b)) := by
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · have h1 := hblk.2.2.1; rw [hμb] at h1; omega
      · have h1 := hblk.2.2.2; rw [hμb] at h1; omega
    have hcross : ∀ u₁ ∈ comp p M₁ x, ∀ u₂ ∈ comp p M₁ b, ¬ (HGraph p).Adj u₁ u₂ := by
      intro u₁ hu₁ u₂ hu₂ hadj
      have hu₂Cx : u₂ ∈ comp p M₁ x := (mem_comp p).2
        ⟨comp_subset_S p M₁ b hu₂, ((mem_comp p).1 hu₁).2.trans
          (SimpleGraph.Adj.reachable ⟨comp_subset_S p M₁ x hu₁, comp_subset_S p M₁ b hu₂, hadj⟩)⟩
      exact Finset.disjoint_left.1 hdisj_xb hu₂Cx hu₂
    have hnonH : ¬ (HGraph p).Adj p₁ p₂ := by
      have hne12 : p₁ ≠ p₂ := (SimpleGraph.top_adj _ _).1 hblk.1
      rcases hp1_rem with h1x | h1y | h1b | h1z | h1U
      · rcases hp2_rem with h2x | h2y | h2b | h2z | h2U
        · exact absurd (h1x.trans h2x.symm) hne12
        · exact absurd (Or.inl ⟨h1x, h2y⟩) hnot_xy
        · rw [h1x, h2b]; exact hcross x hxCx b hbCb
        · rw [h1x, h2z]; exact hcross x hxCx z hzCb
        · exact fun h => U_isolated hm p hno hM₁ h2U p₁ h.symm
      · rcases hp2_rem with h2x | h2y | h2b | h2z | h2U
        · exact absurd (Or.inr ⟨h1y, h2x⟩) hnot_xy
        · exact absurd (h1y.trans h2y.symm) hne12
        · rw [h1y, h2b]; exact hcross y hyCx b hbCb
        · rw [h1y, h2z]; exact hcross y hyCx z hzCb
        · exact fun h => U_isolated hm p hno hM₁ h2U p₁ h.symm
      · rcases hp2_rem with h2x | h2y | h2b | h2z | h2U
        · rw [h1b, h2x]; exact fun h => hcross x hxCx b hbCb h.symm
        · rw [h1b, h2y]; exact fun h => hcross y hyCx b hbCb h.symm
        · exact absurd (h1b.trans h2b.symm) hne12
        · exact absurd (Or.inl ⟨h1b, h2z⟩) hnot_bz
        · exact fun h => U_isolated hm p hno hM₁ h2U p₁ h.symm
      · rcases hp2_rem with h2x | h2y | h2b | h2z | h2U
        · rw [h1z, h2x]; exact fun h => hcross x hxCx z hzCb h.symm
        · rw [h1z, h2y]; exact fun h => hcross y hyCx z hzCb h.symm
        · exact absurd (Or.inr ⟨h1z, h2b⟩) hnot_bz
        · exact absurd (h1z.trans h2z.symm) hne12
        · exact fun h => U_isolated hm p hno hM₁ h2U p₁ h.symm
      · exact U_isolated hm p hno hM₁ h1U p₂
    have hone_z : ∃ v, v ≠ z ∧ IsKBlockingPair ⊤ p.partnerRank m μ z v ∧
        (v = x ∨ v = y ∨ v = b ∨ v ∈ U) := by
      have hne12 : p₁ ≠ p₂ := (SimpleGraph.top_adj _ _).1 hblk.1
      by_cases h1z : p₁ = z
      · subst h1z
        rcases hp2_rem with h | h | h | h | h
        · exact ⟨p₂, hne12.symm, hblk, Or.inl h⟩
        · exact ⟨p₂, hne12.symm, hblk, Or.inr (Or.inl h)⟩
        · exact ⟨p₂, hne12.symm, hblk, Or.inr (Or.inr (Or.inl h))⟩
        · exact absurd h.symm hne12
        · exact ⟨p₂, hne12.symm, hblk, Or.inr (Or.inr (Or.inr h))⟩
      · by_cases h2z : p₂ = z
        · subst h2z
          rcases hp1_rem with h | h | h | h | h
          · exact ⟨p₁, hne12, blocking_symm p hblk, Or.inl h⟩
          · exact ⟨p₁, hne12, blocking_symm p hblk, Or.inr (Or.inl h)⟩
          · exact ⟨p₁, hne12, blocking_symm p hblk, Or.inr (Or.inr (Or.inl h))⟩
          · exact absurd h h1z
          · exact ⟨p₁, hne12, blocking_symm p hblk, Or.inr (Or.inr (Or.inr h))⟩
        · exact absurd hblk (not_blocking_matched_matched_non_H p hnonH
            (fun h => h1z ((hμ_single p₁).1 h)) (fun h => h2z ((hμ_single p₂).1 h)))
    obtain ⟨v, hvz, hblkv, hv_rem⟩ := hone_z
    have hv_nonH : ¬ (HGraph p).Adj z v := by
      rcases hv_rem with hvx | hvy | hvb | hvU
      · rw [hvx]; exact fun h => hcross x hxCx z hzCb h.symm
      · rw [hvy]; exact fun h => hcross y hyCx z hzCb h.symm
      · exfalso
        have h1 := hblkv.2.2.2; rw [hvb, hμb] at h1; omega
      · exact fun h => U_isolated hm p hno hM₁ hvU z h.symm
    obtain ⟨hv_vstar, hrkv⟩ := blocking_single_matched_non_H p hv_nonH hμz
      (fun h => hvz ((hμ_single v).1 h)) hblkv
    rcases hv_rem with hvx | hvy | hvb | hvU
    · rw [hvx] at hv_vstar hrkv; rw [hμx] at hrkv; exact Or.inl ⟨hv_vstar, hrkv⟩
    · rw [hvy] at hv_vstar hrkv; rw [hμy] at hrkv; exact Or.inr ⟨hv_vstar, hrkv⟩
    · exfalso
      have h1 := hbz_H.2.2
      have h2 := rk_vstar p z
      rw [← hv_vstar, hvb] at h2
      omega
    · exfalso
      by_cases hvu : v = u
      · exact huvz (hvu ▸ hv_vstar)
      · have hv_er : v ∈ U.erase u := Finset.mem_erase.2 ⟨hvu, hvU⟩
        rw [hμ_M₂ v hv_er] at hrkv
        exact hM₂neut v hv_er hv_vstar hrkv
  have hUer_pos : 0 < (U.erase (vstar p z)).card := by
    by_cases hvU : vstar p z ∈ U
    · rw [Finset.card_erase_of_mem hvU]; omega
    · rw [Finset.erase_eq_of_notMem hvU]; omega
  obtain ⟨u₀, hu₀⟩ := Finset.card_pos.1 hUer_pos
  rcases hfor_u u₀ (Finset.erase_subset _ _ hu₀) (Finset.mem_erase.1 hu₀).1 with h1 | ⟨hyvz, _⟩
  · exact Or.inl h1
  · right
    refine ⟨hyvz, fun u huU => ?_⟩
    have huvz : u ≠ vstar p z := by
      rw [← hyvz]; exact fun h => (Finset.mem_sdiff.1 huU).2 (h ▸ hyS)
    rcases hfor_u u huU huvz with ⟨hxvz, _⟩ | ⟨_, hrk⟩
    · exact absurd (hxvz.trans hyvz.symm) hxy.symm
    · exact hrk

/-- Universal swap lemma: if `x ∈ S`, `w ∈ S`, `comp x ≠ comp w`, `y ∈ R x`, `z ∈ R w`,
`x = vstar w`, `rk x w ≤ m`, `2 ≤ rk w z`, `H.Adj w z`, and `u ∈ U` with `u ≠ vstar z`,
then `y = vstar z`! (Used BOTH to kill `E_conn` and for the 4-line final contradiction!) -/
private lemma force_y_eq_vstar_z (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ)
    {M₁ : Matching (Fin (2 * m + 1))} (hM₁ : IsMaxHMatching p M₁)
    {x y w z : Fin (2 * m + 1)}
    (hx : x ∈ matchedSet M₁) (hw : w ∈ matchedSet M₁)
    (hcomp_ne : comp p M₁ x ≠ comp p M₁ w)
    (hy : y ∈ Rset p M₁ x) (hz : z ∈ Rset p M₁ w)
    (hxv : x = vstar p w) (hrxw : p.partnerRank x w ≤ m)
    (hrwz : 2 ≤ p.partnerRank w z) (hwz_H : (HGraph p).Adj w z) :
    y = vstar p z := by
  let S := matchedSet M₁
  let U := Finset.univ \ S
  have hyS : y ∈ S := ((mem_Rset p).1 hy).1
  have hzS : z ∈ S := ((mem_Rset p).1 hz).1
  have hdisj_xw : Disjoint (comp p M₁ x) (comp p M₁ w) := comp_disjoint_of_ne p hcomp_ne
  have hyCx : y ∈ comp p M₁ x := Rset_subset_comp p hM₁ hx hy
  have hwCw : w ∈ comp p M₁ w := self_mem_comp p hw
  have hzCw : z ∈ comp p M₁ w := Rset_subset_comp p hM₁ hw hz
  have hU3 : 3 ≤ U.card := three_le_U_card p hno hM₁
  have hUer_pos : 0 < (U.erase (vstar p z)).card := by
    by_cases hvU : vstar p z ∈ U
    · rw [Finset.card_erase_of_mem hvU]; omega
    · rw [Finset.erase_eq_of_notMem hvU]; omega
  obtain ⟨u, hu_er⟩ := Finset.card_pos.1 hUer_pos
  have huv : u ≠ vstar p z := (Finset.mem_erase.1 hu_er).1
  have huU : u ∈ U := (Finset.mem_erase.1 hu_er).2
  obtain ⟨M₂, hM₂ms, hM₂neut⟩ := exists_neutralizing_pm hm p hno hM₁ huU hzS
  obtain ⟨μ, hsafe_rest, hμ_M₂, hμx, hμw, _, _, hμ_single⟩ :=
    four_swap_matching p hM₁ hx hw hcomp_ne hy hz huU hM₂ms
  have hμz : μ.val z = z := (hμ_single z).2 rfl
  obtain ⟨p₁, p₂, hblk⟩ := exists_blocking_of_not_stable p hno μ
  have hsafe : ∀ v, v ∈ ((((S.erase x).erase y).erase w).erase z) ∨ v = x →
      p.partnerRank v (μ.val v) ≤ m := by
    intro v hv
    rcases hv with hv' | rfl
    · exact hsafe_rest v hv'
    · rw [hμx]; exact hrxw
  have hp_rem : ∀ v, ¬ (v ∈ ((((S.erase x).erase y).erase w).erase z) ∨ v = x) →
      v = y ∨ v = w ∨ v = z ∨ v ∈ U := by
    intro v hv
    push Not at hv
    by_cases hvS : v ∈ S
    · by_cases hvy : v = y
      · exact Or.inl hvy
      · by_cases hvw : v = w
        · exact Or.inr (Or.inl hvw)
        · by_cases hvz : v = z
          · exact Or.inr (Or.inr (Or.inl hvz))
          · exfalso; apply hv.1
            exact Finset.mem_erase.2 ⟨hvz, Finset.mem_erase.2 ⟨hvw,
              Finset.mem_erase.2 ⟨hvy, Finset.mem_erase.2 ⟨hv.2, hvS⟩⟩⟩⟩
    · exact Or.inr (Or.inr (Or.inr (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hvS⟩)))
  have hp1_rem := hp_rem p₁ (fun h => not_blocking_of_safe_left p (hsafe p₁ h) hblk)
  have hp2_rem := hp_rem p₂ (fun h => not_blocking_of_safe_right p (hsafe p₂ h) hblk)
  have hnot_wz : ¬ ((p₁ = w ∧ p₂ = z) ∨ (p₁ = z ∧ p₂ = w)) := by
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have h1 := hblk.2.2.1; rw [hμw, hxv, rk_vstar] at h1; omega
    · have h1 := hblk.2.2.2; rw [hμw, hxv, rk_vstar] at h1; omega
  have hcross : ∀ u₂ ∈ comp p M₁ w, ¬ (HGraph p).Adj y u₂ := by
    intro u₂ hu₂ hadj
    have hu₂Cx : u₂ ∈ comp p M₁ x := (mem_comp p).2
      ⟨comp_subset_S p M₁ w hu₂, ((mem_comp p).1 hyCx).2.trans
        (SimpleGraph.Adj.reachable ⟨hyS, comp_subset_S p M₁ w hu₂, hadj⟩)⟩
    exact Finset.disjoint_left.1 hdisj_xw hu₂Cx hu₂
  have hnonH : ¬ (HGraph p).Adj p₁ p₂ := by
    have hne12 : p₁ ≠ p₂ := (SimpleGraph.top_adj _ _).1 hblk.1
    rcases hp1_rem with h1y | h1w | h1z | h1U
    · rcases hp2_rem with h2y | h2w | h2z | h2U
      · exact absurd (h1y.trans h2y.symm) hne12
      · rw [h1y, h2w]; exact hcross w hwCw
      · rw [h1y, h2z]; exact hcross z hzCw
      · exact fun h => U_isolated hm p hno hM₁ h2U p₁ h.symm
    · rcases hp2_rem with h2y | h2w | h2z | h2U
      · rw [h1w, h2y]; exact fun h => hcross w hwCw h.symm
      · exact absurd (h1w.trans h2w.symm) hne12
      · exact absurd (Or.inl ⟨h1w, h2z⟩) hnot_wz
      · exact fun h => U_isolated hm p hno hM₁ h2U p₁ h.symm
    · rcases hp2_rem with h2y | h2w | h2z | h2U
      · rw [h1z, h2y]; exact fun h => hcross z hzCw h.symm
      · exact absurd (Or.inr ⟨h1z, h2w⟩) hnot_wz
      · exact absurd (h1z.trans h2z.symm) hne12
      · exact fun h => U_isolated hm p hno hM₁ h2U p₁ h.symm
    · exact U_isolated hm p hno hM₁ h1U p₂
  have hone_z : ∃ v, v ≠ z ∧ IsKBlockingPair ⊤ p.partnerRank m μ z v ∧
      (v = y ∨ v = w ∨ v ∈ U) := by
    have hne12 : p₁ ≠ p₂ := (SimpleGraph.top_adj _ _).1 hblk.1
    by_cases h1z : p₁ = z
    · subst h1z
      rcases hp2_rem with h | h | h | h
      · exact ⟨p₂, hne12.symm, hblk, Or.inl h⟩
      · exact ⟨p₂, hne12.symm, hblk, Or.inr (Or.inl h)⟩
      · exact absurd h.symm hne12
      · exact ⟨p₂, hne12.symm, hblk, Or.inr (Or.inr h)⟩
    · by_cases h2z : p₂ = z
      · subst h2z
        rcases hp1_rem with h | h | h | h
        · exact ⟨p₁, hne12, blocking_symm p hblk, Or.inl h⟩
        · exact ⟨p₁, hne12, blocking_symm p hblk, Or.inr (Or.inl h)⟩
        · exact absurd h h1z
        · exact ⟨p₁, hne12, blocking_symm p hblk, Or.inr (Or.inr h)⟩
      · exact absurd hblk (not_blocking_matched_matched_non_H p hnonH
          (fun h => h1z ((hμ_single p₁).1 h)) (fun h => h2z ((hμ_single p₂).1 h)))
  obtain ⟨v, hvz, hblkv, hv_rem⟩ := hone_z
  have hv_nonH : ¬ (HGraph p).Adj z v := by
    rcases hv_rem with hvy | hvw | hvU
    · rw [hvy]; exact fun h => hcross z hzCw h.symm
    · exfalso; have h1 := hblkv.2.2.2; rw [hvw, hμw, hxv, rk_vstar] at h1; omega
    · exact fun h => U_isolated hm p hno hM₁ hvU z h.symm
  obtain ⟨hv_vstar, hrkv⟩ := blocking_single_matched_non_H p hv_nonH hμz
    (fun h => hvz ((hμ_single v).1 h)) hblkv
  rcases hv_rem with hvy | hvw | hvU
  · exact hvy.symm.trans hv_vstar
  · exfalso
    have h1 := hwz_H.2.2
    have h2 := rk_vstar p z
    rw [← hv_vstar, hvw] at h2
    omega
  · exfalso
    by_cases hvu : v = u
    · exact huv (hvu ▸ hv_vstar)
    · have hv_er : v ∈ U.erase u := Finset.mem_erase.2 ⟨hvu, hvU⟩
      rw [hμ_M₂ v hv_er] at hrkv
      exact hM₂neut v hv_er hv_vstar hrkv

/-- Step 5: Complete contradiction from `hno` for any `m ≥ 3` and any `p : CompleteProfile (2m+1)`. -/
private lemma no_stable_false (hm : 3 ≤ m) (p : CompleteProfile (2 * m + 1))
    (hno : ∀ μ : Matching (Fin (2 * m + 1)), ¬ IsKStable ⊤ p.partnerRank m μ) : False := by
  classical
  obtain ⟨M₁, hM₁⟩ := exists_maxHMatching p
  let S := matchedSet M₁
  let U := Finset.univ \ S
  let Sconn := Sge2 p M₁
  let Siso := S \ Sconn
  have hSconn_sub : Sconn ⊆ S := Finset.filter_subset _ _
  have hSconn_ne : Sconn.Nonempty := Sge2_nonempty hm p hno hM₁
  have hSle : S.card ≤ 2 * m - 2 := S_card_le p hno hM₁
  have hU3 : 3 ≤ U.card := three_le_U_card p hno hM₁
  have hS_disj : Disjoint Siso Sconn := Finset.sdiff_disjoint
  have hS_union : Siso ∪ Sconn = S := Finset.sdiff_union_of_subset hSconn_sub
  have hS_card_split : Siso.card + Sconn.card = S.card := by
    rw [← Finset.card_union_of_disjoint hS_disj, hS_union]
  have hcomp_sub_Sconn : ∀ v ∈ Sconn, comp p M₁ v ⊆ Sconn := by
    intro v hv
    have hvS : v ∈ S := hSconn_sub hv
    have h4 : 4 ≤ (comp p M₁ v).card := (mem_Sge2_iff_four_le_comp_card hm p hno hM₁ hvS).1 hv
    exact (comp_card_ge_four_structure hm p hno hM₁ hvS h4).1
  have hcomp_le_2R : ∀ v ∈ Sconn, (comp p M₁ v).card ≤ 2 * (Rset p M₁ v).card := by
    intro v hv
    have hvS : v ∈ S := hSconn_sub hv
    have h4 : 4 ≤ (comp p M₁ v).card := (mem_Sge2_iff_four_le_comp_card hm p hno hM₁ hvS).1 hv
    exact (comp_card_ge_four_structure hm p hno hM₁ hvS h4).2 v (self_mem_comp p hvS)
  have hM1_Siso : ∀ v ∈ Siso, M₁.val v ∈ Siso := by
    intro v hv
    obtain ⟨hvS, hvnot⟩ := Finset.mem_sdiff.1 hv
    refine Finset.mem_sdiff.2 ⟨matchedSet_map M₁ hvS, fun hM2 => hvnot ?_⟩
    have hC : comp p M₁ (M₁.val v) = comp p M₁ v := comp_eq_of_mem p (M1_mem_comp p hM₁ hvS)
    exact hcomp_sub_Sconn (M₁.val v) hM2 (hC ▸ self_mem_comp p hvS)
  -- Define w_of v
  have hw_exists : ∀ v : Fin (2 * m + 1), ∃ w : Fin (2 * m + 1),
      (v ∈ Sconn → w ∈ Rset p M₁ v ∧ ∀ w' ∈ Rset p M₁ v, p.partnerRank v w' ≤ p.partnerRank v w) ∧
      (v ∉ Sconn → w = M₁.val v) := by
    intro v
    by_cases hv : v ∈ Sconn
    · have hne : (Rset p M₁ v).Nonempty := ⟨M₁.val v, M1_mem_Rset p hM₁ (hSconn_sub hv)⟩
      obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image (Rset p M₁ v) (fun w => p.partnerRank v w) hne
      exact ⟨w, fun _ => ⟨hw, hmax⟩, fun h => absurd hv h⟩
    · exact ⟨M₁.val v, fun h => absurd h hv, fun _ => rfl⟩
  let w_of : Fin (2 * m + 1) → Fin (2 * m + 1) := fun v => Classical.choose (hw_exists v)
  have hw_spec : ∀ v,
      (v ∈ Sconn → w_of v ∈ Rset p M₁ v ∧
        ∀ w' ∈ Rset p M₁ v, p.partnerRank v w' ≤ p.partnerRank v (w_of v)) ∧
      (v ∉ Sconn → w_of v = M₁.val v) :=
    fun v => Classical.choose_spec (hw_exists v)
  have hw_iso : ∀ v ∈ Siso, w_of v = M₁.val v :=
    fun v hv => (hw_spec v).2 (Finset.mem_sdiff.1 hv).2
  have hw_mem_R : ∀ v ∈ S, w_of v ∈ Rset p M₁ v := by
    intro v hv
    by_cases hvc : v ∈ Sconn
    · exact ((hw_spec v).1 hvc).1
    · rw [(hw_spec v).2 hvc]; exact M1_mem_Rset p hM₁ hv
  have hw_mem_comp : ∀ v ∈ S, w_of v ∈ comp p M₁ v :=
    fun v hv => Rset_subset_comp p hM₁ hv (hw_mem_R v hv)
  have hw_comp_eq : ∀ v ∈ S, comp p M₁ (w_of v) = comp p M₁ v :=
    fun v hv => comp_eq_of_mem p (hw_mem_comp v hv)
  have hw_mem_Sconn : ∀ v ∈ Sconn, w_of v ∈ Sconn :=
    fun v hv => hcomp_sub_Sconn v hv (hw_mem_comp v (hSconn_sub hv))
  have hw_H_adj : ∀ v ∈ S, (HGraph p).Adj v (w_of v) := by
    intro v hv
    by_cases hvc : v ∈ Sconn
    · exact H_adj_of_Sge2_Rset hm p hno hM₁ hvc (hw_mem_Sconn v hvc) (hw_mem_R v hv)
    · rw [(hw_spec v).2 hvc]; exact H_adj_of_mem_matchedSet p hM₁.1 hv
  have hw_rk_ge_Rcard : ∀ v ∈ Sconn, (Rset p M₁ v).card ≤ p.partnerRank v (w_of v) := by
    intro v hv
    have hsub : Rset p M₁ v ⊆
        Finset.univ.filter (fun z => p.partnerRank v z ≤ p.partnerRank v (w_of v)) := by
      intro z hz
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((hw_spec v).1 hv).2 z hz⟩
    have hle := Finset.card_le_card hsub
    rw [card_filter_rk_le p v (p.partnerRank v (w_of v)) (p.partnerRank_le v _)] at hle
    exact hle
  have hw_rk_ge_two : ∀ v ∈ Sconn, 2 ≤ p.partnerRank v (w_of v) := by
    intro v hv
    have h1 := hw_rk_ge_Rcard v hv
    have h2 : 2 ≤ (Rset p M₁ v).card := ((mem_Sge2 p).1 hv).2
    omega
  -- Partition Siso = K_alpha ⊔ K_beta, K_beta = K_beta_I ⊔ K_beta_II
  let Kalpha : Finset (Fin (2 * m + 1)) := Siso.filter (fun v => vstar p (w_of v) ∈ U)
  let Kbeta : Finset (Fin (2 * m + 1)) := Siso.filter (fun v => vstar p (w_of v) ∉ U)
  let KbetaI : Finset (Fin (2 * m + 1)) := Kbeta.filter (fun v => vstar p (w_of v) ∈ Sconn)
  let KbetaII : Finset (Fin (2 * m + 1)) := Kbeta.filter (fun v => vstar p (w_of v) ∈ Siso)
  have hK_disj : Disjoint Kalpha Kbeta := by
    rw [Finset.disjoint_filter]; intro _ _ h1 h2; exact h2 h1
  have hK_union : Kalpha ∪ Kbeta = Siso := by
    ext v; simp only [Kalpha, Kbeta, Finset.mem_union, Finset.mem_filter]; tauto
  have hKb_disj : Disjoint KbetaI KbetaII := by
    rw [Finset.disjoint_filter]
    intro v _ h1 h2
    exact (Finset.mem_sdiff.1 h2).2 h1
  have hKb_union : KbetaI ∪ KbetaII = Kbeta := by
    ext v
    simp only [KbetaI, KbetaII, Kbeta, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · rintro ⟨hv, hnotU⟩
      have hvS : vstar p (w_of v) ∈ S := by
        by_contra hnotS
        exact hnotU (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hnotS⟩)
      by_cases hvc : vstar p (w_of v) ∈ Sconn
      · exact Or.inl ⟨⟨hv, hnotU⟩, hvc⟩
      · exact Or.inr ⟨⟨hv, hnotU⟩, Finset.mem_sdiff.2 ⟨hvS, hvc⟩⟩
  have hKb_card : KbetaI.card + KbetaII.card = Kbeta.card := by
    rw [← Finset.card_union_of_disjoint hKb_disj, hKb_union]
  -- Define q_of and prove the three bounds
  let q_of : Fin (2 * m + 1) → ℕ :=
    fun v => ((S.erase v).filter (fun y => p.partnerRank v (w_of v) + m ≤ p.partnerRank v y)).card
  have hq_Kalpha : ∀ v ∈ Kalpha, 2 * q_of v + 2 * m ≤ 2 * S.card := by
    intro v hv
    have hvIso : v ∈ Siso := (Finset.mem_filter.1 hv).1
    have hvS : v ∈ S := (Finset.mem_sdiff.1 hvIso).1
    have hU : ∀ u ∈ U.erase (vstar p (w_of v)), p.partnerRank v (w_of v) + m ≤ p.partnerRank v u := by
      intro u hu
      obtain ⟨hne, huU⟩ := Finset.mem_erase.1 hu
      rcases master_lemma hm p hno hM₁ hvS (hw_mem_R v hvS) huU with ⟨hA, _⟩ | ⟨heq, _, _⟩
      · exact hA
      · exact absurd heq hne
    have h1 := q_add_m_le_S_card_of_except_one p hvS (hw_H_adj v hvS).2.1 hU
    dsimp [q_of, S]
    omega
  have hq_Kbeta : ∀ v ∈ Kbeta,
      2 * q_of v + 2 + 2 * (p.partnerRank v (w_of v) - 1) + 2 * m ≤ 2 * S.card := by
    intro v hv
    obtain ⟨hvIso, hnotU⟩ := Finset.mem_filter.1 hv
    have hvS : v ∈ S := (Finset.mem_sdiff.1 hvIso).1
    have hU : ∀ u ∈ U, p.partnerRank v (w_of v) + m ≤ p.partnerRank v u := by
      intro u hu
      rcases master_lemma hm p hno hM₁ hvS (hw_mem_R v hvS) hu with ⟨hA, _⟩ | ⟨heq, _, _⟩
      · exact hA
      · exact absurd (heq ▸ hu) hnotU
    have h1 := rk_add_q_add_m_le_S_card p hno hM₁ hvS hU
    have hpos := rk_pos p v (w_of v)
    dsimp [q_of, S]
    omega
  have hq_Sconn : ∀ v ∈ Sconn, 2 * q_of v + (comp p M₁ v).card + 2 * m ≤ 2 * S.card := by
    intro v hv
    have hvS : v ∈ S := hSconn_sub hv
    have hwC : w_of v ∈ Sconn := hw_mem_Sconn v hv
    have hvRw : v ∈ Rset p M₁ (w_of v) := (mem_Rset_symm p hvS).1 (hw_mem_R v hvS)
    have hU : ∀ u ∈ U, p.partnerRank v (w_of v) + m ≤ p.partnerRank v u :=
      fun u hu => rk_add_m_le_U_of_Sge2 hm p hno hM₁ hwC hvRw hu
    have h1 := rk_add_q_add_m_le_S_card p hno hM₁ hvS hU
    have h2 := hw_rk_ge_Rcard v hv
    have h3 := hcomp_le_2R v hv
    dsimp [q_of, S]
    omega
  -- Ordered cross-component pairs and E_exc_ord
  let Cross : Finset (Fin (2 * m + 1) × Fin (2 * m + 1)) :=
    (S ×ˢ S).filter (fun q => comp p M₁ q.1 ≠ comp p M₁ q.2)
  let E_exc_ord : Finset (Fin (2 * m + 1) × Fin (2 * m + 1)) :=
    Cross.filter (fun q =>
      p.partnerRank q.1 q.2 < p.partnerRank q.1 (w_of q.1) + m ∧
      p.partnerRank q.2 q.1 < p.partnerRank q.2 (w_of q.2) + m)
  have hE_symm : ∀ x b, (x, b) ∈ E_exc_ord → (b, x) ∈ E_exc_ord := by
    intro x b h
    simp only [E_exc_ord, Cross, Finset.mem_filter, Finset.mem_product] at h ⊢
    exact ⟨⟨⟨h.1.1.2, h.1.1.1⟩, h.1.2.symm⟩, h.2.2, h.2.1⟩
  have hClaim51 : ∀ x b, (x, b) ∈ E_exc_ord →
      (x = vstar p (w_of b) ∧ p.partnerRank x (w_of b) + m ≤ p.partnerRank x b) ∨
      (w_of x = vstar p (w_of b) ∧
        ∀ u ∈ U, p.partnerRank (w_of x) (w_of b) + m ≤ p.partnerRank (w_of x) u) := by
    intro x b hE
    simp only [E_exc_ord, Cross, Finset.mem_filter, Finset.mem_product] at hE
    obtain ⟨⟨⟨hxS, hbS⟩, hcomp_ne⟩, hlt_xb, hlt_bx⟩ := hE
    exact claim_5_1 hm p hno hM₁ hxS hbS hcomp_ne (hw_mem_R x hxS) (hw_mem_R b hbS)
      (hw_H_adj b hbS) hlt_xb hlt_bx
  have hno_cross_conn : ∀ x ∈ Sconn, ∀ w ∈ Sconn, comp p M₁ x ≠ comp p M₁ w →
      ¬ (x = vstar p w ∧ p.partnerRank x w ≤ m) := by
    rintro x hxC w hwC hcomp_ne ⟨hxv, hrxw⟩
    have hxS : x ∈ S := hSconn_sub hxC
    have hwS : w ∈ S := hSconn_sub hwC
    have hRx2 : 2 ≤ (Rset p M₁ x).card := ((mem_Sge2 p).1 hxC).2
    have hRx_pos : 0 < ((Rset p M₁ x).erase (vstar p (w_of w))).card := by
      by_cases h : vstar p (w_of w) ∈ Rset p M₁ x
      · rw [Finset.card_erase_of_mem h]; omega
      · rw [Finset.erase_eq_of_notMem h]; omega
    obtain ⟨y, hy_er⟩ := Finset.card_pos.1 hRx_pos
    have hyv : y ≠ vstar p (w_of w) := (Finset.mem_erase.1 hy_er).1
    have hyR : y ∈ Rset p M₁ x := (Finset.mem_erase.1 hy_er).2
    exact hyv (force_y_eq_vstar_z hm p hno hM₁ hxS hwS hcomp_ne hyR (hw_mem_R w hwS)
      hxv hrxw (hw_rk_ge_two w hwC) (hw_H_adj w hwS))
  -- Classify E_exc_ord
  let E_conn := E_exc_ord.filter (fun q => q.1 ∈ Sconn ∧ q.2 ∈ Sconn)
  let E_II := E_exc_ord.filter (fun q => q.1 ∈ Siso ∧ q.2 ∈ Siso)
  let E_I_fwd := E_exc_ord.filter (fun q => q.1 ∈ Siso ∧ q.2 ∈ Sconn)
  let E_I_bwd := E_exc_ord.filter (fun q => q.1 ∈ Sconn ∧ q.2 ∈ Siso)
  have hE_conn_empty : E_conn = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    rintro ⟨x, b⟩ hmem
    obtain ⟨hE, hxC, hbC⟩ := Finset.mem_filter.1 hmem
    have hcomp_ne : comp p M₁ x ≠ comp p M₁ b :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 hE).1).2
    have hxS : x ∈ S := hSconn_sub hxC
    have hbS : b ∈ S := hSconn_sub hbC
    have hwbC : w_of b ∈ Sconn := hw_mem_Sconn b hbC
    have hcomp_wb : comp p M₁ (w_of b) = comp p M₁ b := hw_comp_eq b hbS
    rcases hClaim51 x b hE with ⟨hxv, hrk⟩ | ⟨hyv, hU⟩
    · have hxb_ne : x ≠ b := fun h => hcomp_ne (by rw [h])
      have hle : p.partnerRank x b ≤ 2 * m := rk_le_two_mul_of_ne p hxb_ne.symm
      exact hno_cross_conn x hxC (w_of b) hwbC (by rw [hcomp_wb]; exact hcomp_ne) ⟨hxv, by omega⟩
    · obtain ⟨u₀, hu₀⟩ := Finset.card_pos.1 (by omega : 0 < U.card)
      have hyC : w_of x ∈ Sconn := hw_mem_Sconn x hxC
      have hyS : w_of x ∈ S := hSconn_sub hyC
      have hcomp_y : comp p M₁ (w_of x) = comp p M₁ x := hw_comp_eq x hxS
      have hyu : u₀ ≠ w_of x := fun h => (Finset.mem_sdiff.1 hu₀).2 (h ▸ hyS)
      have hle : p.partnerRank (w_of x) u₀ ≤ 2 * m := rk_le_two_mul_of_ne p hyu
      have h1 := hU u₀ hu₀
      exact hno_cross_conn (w_of x) hyC (w_of b) hwbC (by rw [hcomp_y, hcomp_wb]; exact hcomp_ne)
        ⟨hyv, by omega⟩
  have hE_II_le : E_II.card ≤ 2 * KbetaII.card := by
    have hsub : E_II ⊆ KbetaII.biUnion (fun x =>
        ({(x, vstar p (w_of x)), (x, M₁.val (vstar p (w_of x)))} :
          Finset (Fin (2 * m + 1) × Fin (2 * m + 1)))) := by
      rintro ⟨x, b⟩ hmem
      obtain ⟨hE, hxIso, hbIso⟩ := Finset.mem_filter.1 hmem
      have hE' := hE_symm x b hE
      have hbm : M₁.val b ∈ Siso := hM1_Siso b hbIso
      have hwb : w_of b = M₁.val b := hw_iso b hbIso
      have hv_cases : vstar p (w_of x) = b ∨ vstar p (w_of x) = M₁.val b := by
        rcases hClaim51 b x hE' with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inl h1.symm
        · exact Or.inr (hwb ▸ h1.symm)
      have hvIso : vstar p (w_of x) ∈ Siso := by
        rcases hv_cases with h | h
        · rw [h]; exact hbIso
        · rw [h]; exact hbm
      have hxKb : x ∈ KbetaII := by
        refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hxIso, fun hU =>
          (Finset.mem_sdiff.1 hU).2 (Finset.mem_sdiff.1 hvIso).1⟩, hvIso⟩
      refine Finset.mem_biUnion.2 ⟨x, hxKb, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, true_and]
      rcases hv_cases with h | h
      · exact Or.inl h.symm
      · right; rw [h, M₁.property b]
    calc E_II.card
        ≤ (KbetaII.biUnion (fun x =>
            ({(x, vstar p (w_of x)), (x, M₁.val (vstar p (w_of x)))} :
              Finset (Fin (2 * m + 1) × Fin (2 * m + 1))))).card := Finset.card_le_card hsub
      _ ≤ ∑ x ∈ KbetaII, ({(x, vstar p (w_of x)), (x, M₁.val (vstar p (w_of x)))} :
            Finset (Fin (2 * m + 1) × Fin (2 * m + 1))).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ KbetaII, 2 := Finset.sum_le_sum (fun _ _ => Finset.card_le_two)
      _ = 2 * KbetaII.card := by simp [Nat.mul_comm]
  let E_I_1 := E_I_fwd.filter (fun q => q.2 = vstar p (w_of q.1))
  let E_I_2 := E_I_fwd.filter (fun q => q.2 ≠ vstar p (w_of q.1))
  have hEI_disj : Disjoint E_I_1 E_I_2 := by
    rw [Finset.disjoint_filter]; intro _ _ h1 h2; exact h2 h1
  have hEI_union : E_I_1 ∪ E_I_2 = E_I_fwd := by
    ext q; simp only [E_I_1, E_I_2, Finset.mem_union, Finset.mem_filter]; tauto
  have hEI_card : E_I_1.card + E_I_2.card = E_I_fwd.card := by
    rw [← Finset.card_union_of_disjoint hEI_disj, hEI_union]
  have hEI_bwd_card : E_I_bwd.card = E_I_fwd.card := by
    refine Finset.card_bij (fun q _ => Prod.swap q) ?_ ?_ ?_
    · rintro ⟨b, x⟩ hmem
      obtain ⟨hE, hbC, hxI⟩ := Finset.mem_filter.1 hmem
      exact Finset.mem_filter.2 ⟨hE_symm b x hE, hxI, hbC⟩
    · intro q₁ _ q₂ _ h; exact Prod.swap_injective h
    · rintro ⟨x, b⟩ hmem
      obtain ⟨hE, hxI, hbC⟩ := Finset.mem_filter.1 hmem
      exact ⟨(b, x), Finset.mem_filter.2 ⟨hE_symm x b hE, hbC, hxI⟩, rfl⟩
  have hEI_1_le : E_I_1.card ≤ KbetaI.card := by
    have hinj : Set.InjOn Prod.fst (E_I_1 : Set (Fin (2 * m + 1) × Fin (2 * m + 1))) := by
      rintro ⟨x₁, b₁⟩ h1 ⟨x₂, b₂⟩ h2 heq
      simp only [Finset.mem_coe, E_I_1, Finset.mem_filter] at h1 h2
      dsimp at heq
      subst heq
      exact Prod.ext rfl (h1.2.trans h2.2.symm)
    have himg : E_I_1.image Prod.fst ⊆ KbetaI := by
      intro x hx
      obtain ⟨⟨x', b⟩, hmem, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨hfwd, hbv⟩ := Finset.mem_filter.1 hmem
      obtain ⟨_, hxIso, hbC⟩ := Finset.mem_filter.1 hfwd
      have hvC : vstar p (w_of x') ∈ Sconn := hbv ▸ hbC
      exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hxIso, fun hU =>
        (Finset.mem_sdiff.1 hU).2 (hSconn_sub hvC)⟩, hvC⟩
    calc E_I_1.card = (E_I_1.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ KbetaI.card := Finset.card_le_card himg
  have hEI_2_prop : ∀ x b, (x, b) ∈ E_I_2 →
      x ∈ KbetaI ∧ w_of b = vstar p (M₁.val x) ∧
      x = vstar p (w_of b) ∧ p.partnerRank x (w_of b) + m ≤ p.partnerRank x b := by
    intro x b hmem
    obtain ⟨hfwd, hne_b⟩ := Finset.mem_filter.1 hmem
    obtain ⟨hE, hxIso, hbC⟩ := Finset.mem_filter.1 hfwd
    have hE' := hE_symm x b hE
    have hwx : w_of x = M₁.val x := hw_iso x hxIso
    have hwb_eq : w_of b = vstar p (M₁.val x) := by
      rcases hClaim51 b x hE' with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd h1 hne_b
      · rw [← hwx]; exact h1
    have hxKbI : x ∈ KbetaI := by
      have hvC : vstar p (w_of x) ∈ Sconn := by
        rw [hwx, ← hwb_eq]; exact hw_mem_Sconn b hbC
      exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hxIso, fun hU =>
        (Finset.mem_sdiff.1 hU).2 (hSconn_sub hvC)⟩, hvC⟩
    rcases hClaim51 x b hE with ⟨hxv, hrk⟩ | ⟨_, hU⟩
    · exact ⟨hxKbI, hwb_eq, hxv, hrk⟩
    · exfalso
      obtain ⟨u₀, hu₀⟩ := Finset.card_pos.1 (by omega : 0 < U.card)
      have h1 := hU u₀ hu₀
      rw [hwx, hwb_eq, rk_vstar] at h1
      have hMyS : M₁.val x ∈ S := (Finset.mem_sdiff.1 (hM1_Siso x hxIso)).1
      have hne_u : u₀ ≠ M₁.val x := fun h => (Finset.mem_sdiff.1 hu₀).2 (h ▸ hMyS)
      have hle := rk_le_two_mul_of_ne p hne_u
      omega
  have hEI_2_inj : Set.InjOn Prod.snd (E_I_2 : Set (Fin (2 * m + 1) × Fin (2 * m + 1))) := by
    rintro ⟨x₁, b₁⟩ h1 ⟨x₂, b₂⟩ h2 heq
    simp only [Finset.mem_coe] at h1 h2
    dsimp at heq
    subst heq
    have hx1 := (hEI_2_prop x₁ b₁ h1).2.2.1
    have hx2 := (hEI_2_prop x₂ b₁ h2).2.2.1
    exact Prod.ext (hx1.trans hx2.symm) rfl
  have hEI_2_img_sub : E_I_2.image Prod.snd ⊆ Sconn := by
    intro b hb
    obtain ⟨⟨_, _⟩, hmem, rfl⟩ := Finset.mem_image.1 hb
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 hmem).1).2.2
  have hEI_2_le : E_I_2.card ≤ Sconn.card := by
    calc E_I_2.card = (E_I_2.image Prod.snd).card := (Finset.card_image_of_injOn hEI_2_inj).symm
      _ ≤ Sconn.card := Finset.card_le_card hEI_2_img_sub
  have hE_exc_le : E_exc_ord.card ≤ 2 * Kbeta.card + 2 * E_I_2.card := by
    have hcover : E_exc_ord ⊆ E_II ∪ (E_I_fwd ∪ E_I_bwd) := by
      rintro ⟨x, b⟩ hE
      have hxS : x ∈ S :=
        (Finset.mem_product.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hE).1).1).1
      have hbS : b ∈ S :=
        (Finset.mem_product.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hE).1).1).2
      by_cases hxC : x ∈ Sconn <;> by_cases hbC : b ∈ Sconn
      · exfalso
        have hmem : (x, b) ∈ E_conn := Finset.mem_filter.2 ⟨hE, hxC, hbC⟩
        rw [hE_conn_empty] at hmem
        exact Finset.notMem_empty _ hmem
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hE, hxC, Finset.mem_sdiff.2 ⟨hbS, hbC⟩⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hE, Finset.mem_sdiff.2 ⟨hxS, hxC⟩, hbC⟩))
      · exact Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hE, Finset.mem_sdiff.2 ⟨hxS, hxC⟩, Finset.mem_sdiff.2 ⟨hbS, hbC⟩⟩)
    have hle := Finset.card_le_card hcover
    have h2 := Finset.card_union_le E_II (E_I_fwd ∪ E_I_bwd)
    have h3 := Finset.card_union_le E_I_fwd E_I_bwd
    omega
  -- Global ordered-pair counting inequality (pure addition in ℕ!)
  have hCross_card : Cross.card + ∑ x ∈ S, (comp p M₁ x).card = S.card * S.card := by
    have hCross_sum : Cross.card =
        ∑ x ∈ S, (S.filter (fun b => comp p M₁ x ≠ comp p M₁ b)).card := by
      have hfiber : Cross = S.biUnion (fun x =>
          (S.filter (fun b => comp p M₁ x ≠ comp p M₁ b)).image (fun b => (x, b))) := by
        ext ⟨x, b⟩
        simp only [Cross, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro ⟨⟨hx, hb⟩, hne⟩; exact ⟨x, hx, b, ⟨hb, hne⟩, rfl⟩
        · rintro ⟨x', hx', b', ⟨hb', hne⟩, heq⟩
          rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
          exact ⟨⟨hx', hb'⟩, hne⟩
      rw [hfiber, Finset.card_biUnion]
      · refine Finset.sum_congr rfl (fun x _ => ?_)
        exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
      · intro x₁ _ x₂ _ hne
        dsimp [Function.onFun]
        rw [Finset.disjoint_left]
        intro q hq1 hq2
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.1 hq1
        obtain ⟨_, _, heq⟩ := Finset.mem_image.1 hq2
        exact hne (Prod.mk.inj heq).1.symm
    rw [hCross_sum, ← Finset.sum_add_distrib]
    have hrow : ∀ x ∈ S,
        (S.filter (fun b => comp p M₁ x ≠ comp p M₁ b)).card + (comp p M₁ x).card = S.card := by
      intro x hx
      have hdisj : Disjoint (S.filter (fun b => comp p M₁ x ≠ comp p M₁ b)) (comp p M₁ x) := by
        rw [Finset.disjoint_left]
        intro b hb1 hb2
        exact (Finset.mem_filter.1 hb1).2 (comp_eq_of_mem p hb2).symm
      have hunion : S.filter (fun b => comp p M₁ x ≠ comp p M₁ b) ∪ comp p M₁ x = S := by
        ext b
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hb, _⟩ | hbC)
          · exact hb
          · exact comp_subset_S p M₁ x hbC
        · intro hb
          by_cases hbC : b ∈ comp p M₁ x
          · exact Or.inr hbC
          · refine Or.inl ⟨hb, fun h => hbC ?_⟩
            rw [h]; exact self_mem_comp p hb
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    rw [Finset.sum_congr rfl hrow, Finset.sum_const, smul_eq_mul]
  have hCross_le : Cross.card ≤ 2 * (∑ x ∈ S, q_of x) + E_exc_ord.card := by
    let Q₁ := Cross.filter (fun q => p.partnerRank q.1 (w_of q.1) + m ≤ p.partnerRank q.1 q.2)
    let Q₂ := Cross.filter (fun q => p.partnerRank q.2 (w_of q.2) + m ≤ p.partnerRank q.2 q.1)
    have hcov : Cross ⊆ Q₁ ∪ (Q₂ ∪ E_exc_ord) := by
      intro q hq
      by_cases h1 : p.partnerRank q.1 (w_of q.1) + m ≤ p.partnerRank q.1 q.2
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hq, h1⟩)
      · by_cases h2 : p.partnerRank q.2 (w_of q.2) + m ≤ p.partnerRank q.2 q.1
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hq, h2⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_filter.2 ⟨hq, by omega, by omega⟩))
    have hQ₂_eq : Q₂.card = Q₁.card := by
      refine Finset.card_bij (fun q _ => Prod.swap q) ?_ ?_ ?_
      · rintro ⟨x, b⟩ hmem
        simp only [Q₂, Q₁, Cross, Finset.mem_filter, Finset.mem_product] at hmem ⊢
        exact ⟨⟨⟨hmem.1.1.2, hmem.1.1.1⟩, hmem.1.2.symm⟩, hmem.2⟩
      · intro q₁ _ q₂ _ h; exact Prod.swap_injective h
      · rintro ⟨x, b⟩ hmem
        simp only [Q₁, Cross, Finset.mem_filter, Finset.mem_product] at hmem
        exact ⟨(b, x), Finset.mem_filter.2 ⟨Finset.mem_filter.2
          ⟨Finset.mem_product.2 ⟨hmem.1.1.2, hmem.1.1.1⟩, hmem.1.2.symm⟩, hmem.2⟩, rfl⟩
    have hQ₁_le : Q₁.card ≤ ∑ x ∈ S, q_of x := by
      have hsub : Q₁ ⊆ S.biUnion (fun x =>
          ((S.erase x).filter (fun b => p.partnerRank x (w_of x) + m ≤ p.partnerRank x b)).image
            (fun b => (x, b))) := by
        rintro ⟨x, b⟩ hmem
        simp only [Q₁, Cross, Finset.mem_filter, Finset.mem_product] at hmem
        obtain ⟨⟨⟨hx, hb⟩, hne⟩, hrk⟩ := hmem
        have hbx : b ≠ x := fun h => hne (by rw [h])
        exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2
          ⟨b, Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hbx, hb⟩, hrk⟩, rfl⟩⟩
      calc Q₁.card
          ≤ (S.biUnion (fun x =>
              ((S.erase x).filter (fun b => p.partnerRank x (w_of x) + m ≤ p.partnerRank x b)).image
                (fun b => (x, b)))).card := Finset.card_le_card hsub
        _ ≤ ∑ x ∈ S, (((S.erase x).filter
              (fun b => p.partnerRank x (w_of x) + m ≤ p.partnerRank x b)).image
                (fun b => (x, b))).card := Finset.card_biUnion_le
        _ = ∑ x ∈ S, q_of x := Finset.sum_congr rfl (fun x _ =>
              Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2))
    have h1 := Finset.card_le_card hcov
    have h2 := Finset.card_union_le Q₁ (Q₂ ∪ E_exc_ord)
    have h3 := Finset.card_union_le Q₂ E_exc_ord
    omega
  have hcomp_sum : ∑ x ∈ S, (comp p M₁ x).card =
      2 * Siso.card + ∑ x ∈ Sconn, (comp p M₁ x).card := by
    rw [← hS_union, Finset.sum_union hS_disj]
    have hiso_sum : ∑ x ∈ Siso, (comp p M₁ x).card = 2 * Siso.card := by
      have hconst : ∀ x ∈ Siso, (comp p M₁ x).card = 2 := fun x hx =>
        S_iso_comp_card hm p hno hM₁ (Finset.mem_sdiff.1 hx).1 (Finset.mem_sdiff.1 hx).2
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    rw [hiso_sum]
  have hq_sum : 2 * (∑ x ∈ S, q_of x) + 2 * Kbeta.card +
      2 * (∑ v ∈ Kbeta, (p.partnerRank v (w_of v) - 1)) +
      (∑ v ∈ Sconn, (comp p M₁ v).card) + 2 * (m * S.card) ≤ 2 * (S.card * S.card) := by
    have hsum_ka : ∑ v ∈ Kalpha, (2 * q_of v + 2 * m) ≤ ∑ _v ∈ Kalpha, (2 * S.card) :=
      Finset.sum_le_sum hq_Kalpha
    have hsum_kb : ∑ v ∈ Kbeta, (2 * q_of v + 2 + 2 * (p.partnerRank v (w_of v) - 1) + 2 * m) ≤
        ∑ _v ∈ Kbeta, (2 * S.card) := Finset.sum_le_sum hq_Kbeta
    have hsum_sc : ∑ v ∈ Sconn, (2 * q_of v + (comp p M₁ v).card + 2 * m) ≤
        ∑ _v ∈ Sconn, (2 * S.card) := Finset.sum_le_sum hq_Sconn
    simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hsum_ka hsum_kb hsum_sc
    have hsplit_q : ∑ x ∈ S, q_of x =
        (∑ v ∈ Kalpha, q_of v) + (∑ v ∈ Kbeta, q_of v) + (∑ v ∈ Sconn, q_of v) := by
      rw [← hS_union, Finset.sum_union hS_disj, ← hK_union, Finset.sum_union hK_disj]
    have hcard_tot : Kalpha.card + Kbeta.card + Sconn.card = S.card := by
      have : Kalpha.card + Kbeta.card = Siso.card := by
        rw [← Finset.card_union_of_disjoint hK_disj, hK_union]
      omega
    have h1 : Kalpha.card * (2 * m) + Kbeta.card * (2 * m) + Sconn.card * (2 * m) =
        2 * (m * S.card) := by
      rw [← hcard_tot]; ring
    have h2 : Kalpha.card * (2 * S.card) + Kbeta.card * (2 * S.card) + Sconn.card * (2 * S.card) =
        2 * (S.card * S.card) := by
      rw [← hcard_tot]; ring
    have h5 : Kbeta.card * 2 = 2 * Kbeta.card := Nat.mul_comm _ _
    omega
  -- Squeeze to get equality!
  have hmul_s : S.card * S.card + 2 * S.card ≤ 2 * (m * S.card) := by
    have hle2 : S.card + 2 ≤ 2 * m := by omega
    calc S.card * S.card + 2 * S.card = (S.card + 2) * S.card := by ring
      _ ≤ (2 * m) * S.card := Nat.mul_le_mul_right S.card hle2
      _ = 2 * (m * S.card) := by ring
  have hKbeta_rk_sum_zero : ∑ v ∈ Kbeta, (p.partnerRank v (w_of v) - 1) = 0 := by omega
  have hEI_2_eq : E_I_2.card = Sconn.card := by omega
  -- Extract equality consequences
  have hKbeta_rk_one : ∀ v ∈ Kbeta, p.partnerRank v (M₁.val v) = 1 := by
    intro v hv
    have h0 : p.partnerRank v (w_of v) - 1 = 0 :=
      (Finset.sum_eq_zero_iff.1 hKbeta_rk_sum_zero) v hv
    have hpos := rk_pos p v (w_of v)
    rw [hw_iso v (Finset.mem_filter.1 hv).1] at h0 hpos
    omega
  have hEI_2_surj : ∀ b ∈ Sconn, ∃ x, (x, b) ∈ E_I_2 := by
    have himg_eq : E_I_2.image Prod.snd = Sconn := by
      refine Finset.eq_of_subset_of_card_le hEI_2_img_sub ?_
      rw [Finset.card_image_of_injOn hEI_2_inj, hEI_2_eq]
    intro b hb
    rw [← himg_eq] at hb
    obtain ⟨⟨x, b'⟩, hmem, heq⟩ := Finset.mem_image.1 hb
    dsimp at heq
    subst heq
    exact ⟨x, hmem⟩
  -- 4-line final contradiction!
  obtain ⟨b₁, hb₁C⟩ := hSconn_ne
  obtain ⟨x₁, hx₁b₁⟩ := hEI_2_surj b₁ hb₁C
  obtain ⟨hx₁KbI, hw₁_vstar, hx₁_vstar, hrx₁_le⟩ := hEI_2_prop x₁ b₁ hx₁b₁
  let w₁ := w_of b₁
  let y₁ := M₁.val x₁
  have hx₁Iso : x₁ ∈ Siso := (Finset.mem_filter.1 (Finset.mem_filter.1 hx₁KbI).1).1
  have hx₁S : x₁ ∈ S := (Finset.mem_sdiff.1 hx₁Iso).1
  have hw₁C : w₁ ∈ Sconn := hw_mem_Sconn b₁ hb₁C
  have hw₁S : w₁ ∈ S := hSconn_sub hw₁C
  have hrx₁w₁ : p.partnerRank x₁ w₁ ≤ m := by
    have hne : b₁ ≠ x₁ := fun h => (Finset.mem_sdiff.1 hx₁Iso).2 (h ▸ hb₁C)
    have hle := rk_le_two_mul_of_ne p hne
    dsimp [w₁] at hrx₁_le ⊢
    omega
  obtain ⟨x₂, hx₂w₁⟩ := hEI_2_surj w₁ hw₁C
  obtain ⟨hx₂KbI, _, hx₂_vstar, hrx₂_le⟩ := hEI_2_prop x₂ w₁ hx₂w₁
  let w₂ := w_of w₁
  have hw₂C : w₂ ∈ Sconn := hw_mem_Sconn w₁ hw₁C
  have hcomp_ne : comp p M₁ x₁ ≠ comp p M₁ w₁ := by
    intro h
    have hx₁_in : x₁ ∈ comp p M₁ w₁ := h ▸ self_mem_comp p hx₁S
    exact (Finset.mem_sdiff.1 hx₁Iso).2 (hcomp_sub_Sconn w₁ hw₁C hx₁_in)
  -- Force y₁ = vstar w₂ = x₂ using `force_y_eq_vstar_z`!
  have hy₁_vstar : y₁ = vstar p w₂ :=
    force_y_eq_vstar_z hm p hno hM₁ hx₁S hw₁S hcomp_ne (M1_mem_Rset p hM₁ hx₁S)
      (hw_mem_R w₁ hw₁S) hx₁_vstar hrx₁w₁ (hw_rk_ge_two w₁ hw₁C) (hw_H_adj w₁ hw₁S)
  have hy₁_eq_x₂ : y₁ = x₂ := hy₁_vstar.trans hx₂_vstar.symm
  -- rk y₁ x₁ = 1 AND rk y₁ w₂ = 1 with x₁ ≠ w₂!
  have hrk1 : p.partnerRank y₁ x₁ = 1 := by
    have hy₁Kb : y₁ ∈ Kbeta := hy₁_eq_x₂ ▸ (Finset.mem_filter.1 hx₂KbI).1
    have h := hKbeta_rk_one y₁ hy₁Kb
    rwa [show M₁.val y₁ = x₁ from M₁.property x₁] at h
  have hrk2 : p.partnerRank y₁ w₂ = 1 := by
    have h := hrx₂_le
    rw [← hy₁_eq_x₂] at h
    have hrw1 : p.partnerRank y₁ w₁ = m + 1 := by
      dsimp [w₁, y₁]; rw [hw₁_vstar, rk_vstar]
    dsimp [w₂] at h ⊢
    have hpos := rk_pos p y₁ (w_of w₁)
    omega
  have hx₁w₂ : x₁ ≠ w₂ := fun h => (Finset.mem_sdiff.1 hx₁Iso).2 (h ▸ hw₂C)
  exact hx₁w₂ (rk_inj p y₁ (hrk1.trans hrk2.symm))

end Step5

end CoreProof

/-! ### Main Public Theorems -/

/-- **Main Constructive Theorem**: For every `m ≥ 3` and every complete strict preference
profile on `2m + 1` agents, there exists an `m`-stable matching. -/
theorem exists_m_stable_of_odd (m : ℕ) (hm : 3 ≤ m)
    (p : Roommates.CompleteProfile (2 * m + 1)) :
    ∃ μ : Roommates.Matching (Fin (2 * m + 1)),
      Roommates.IsKStable ⊤ p.partnerRank m μ := by
  by_contra h
  push Not at h
  exact no_stable_false hm p h

/-- **Threshold Upper Bound**: For every `m ≥ 3`, `K(2m + 1) ≤ m < m + 1 = ⌈(2m + 1) / 2⌉`. -/
theorem stabilityThreshold_odd_le (m : ℕ) (hm : 3 ≤ m) :
    Roommates.stabilityThreshold (2 * m + 1) ≤ m :=
  Roommates.stabilityThreshold_le (by omega) (exists_m_stable_of_odd m hm)

/-- **Disproof of the Fanelli–Moscardelli Conjecture**: It is NOT the case that
`K(N) = ⌈N / 2⌉` for all sufficiently large `N`. -/
theorem not_stability_threshold_tight :
    ¬ (∃ N₀ : ℕ, 3 ≤ N₀ ∧
        ∀ N ≥ N₀, Roommates.stabilityThreshold N = (N + 1) / 2) := by
  rintro ⟨N₀, _, hN⟩
  let m := max 3 N₀
  have hm : 3 ≤ m := le_max_left _ _
  have hge : 2 * m + 1 ≥ N₀ := by
    have : N₀ ≤ m := le_max_right _ _
    omega
  have heq := hN (2 * m + 1) hge
  have hle := stabilityThreshold_odd_le m hm
  omega

/-- Extend a permutation of `Fin (n + 1)` to `Fin (n + 2)` by fixing `Fin.last (n + 1)`. -/
private def extendPerm {n : ℕ} (e : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 2)) where
  toFun := Fin.lastCases (Fin.last (n + 1)) (fun j => (e j).castSucc)
  invFun := Fin.lastCases (Fin.last (n + 1)) (fun j => (e.symm j).castSucc)
  left_inv := by
    intro x
    refine Fin.lastCases ?_ ?_ x
    · simp
    · intro j; simp
  right_inv := by
    intro x
    refine Fin.lastCases ?_ ?_ x
    · simp
    · intro j; simp

@[simp]
private lemma extendPerm_castSucc {n : ℕ} (e : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    extendPerm e j.castSucc = (e j).castSucc := by
  simp [extendPerm]

@[simp]
private lemma extendPerm_last {n : ℕ} (e : Equiv.Perm (Fin (n + 1))) :
    extendPerm e (Fin.last (n + 1)) = Fin.last (n + 1) := by
  simp [extendPerm]

/-- **Monotonicity of the Stability Threshold** (Pariah lifting):
Appending a universally least-preferred agent shows `K(n) ≤ K(n + 1)` for every `n`. -/
theorem stabilityThreshold_mono (n : ℕ) :
    Roommates.stabilityThreshold n ≤ Roommates.stabilityThreshold (n + 1) := by
  obtain ⟨hk_pos, hk_ex⟩ := Roommates.stabilityThreshold_spec (n + 1)
  apply Roommates.stabilityThreshold_le hk_pos
  intro p
  cases n with
  | zero =>
    refine ⟨Roommates.emptyMatching (Fin 0), Roommates.isAcceptable_emptyMatching ⊤, ?_⟩
    intro i; exact Fin.elim0 i
  | succ n =>
    let rank' : Fin (n + 2) → Equiv.Perm (Fin (n + 2)) :=
      Fin.lastCases (Equiv.refl (Fin (n + 2))) (fun i =>
        (extendPerm (p.rank i)).trans (Equiv.swap ⟨n, by omega⟩ (Fin.last (n + 1))))
    have hself' : ∀ a : Fin (n + 2), (rank' a a).val + 1 = n + 2 := by
      intro a
      refine Fin.lastCases ?_ ?_ a
      · simp [rank']
      · intro i
        have hself_i : (p.rank i i).val + 1 = n + 1 := p.self_last i
        have hcast : (p.rank i i).castSucc = ⟨n, by omega⟩ := by
          apply Fin.ext; simp; omega
        simp only [rank', Fin.lastCases_castSucc, Equiv.trans_apply, extendPerm_castSucc, hcast,
          Equiv.swap_apply_left, Fin.val_last]
    let p' : Roommates.CompleteProfile (n + 2) := ⟨rank', hself'⟩
    obtain ⟨μ', _, hμ'_stab⟩ := hk_ex p'
    let f : Fin (n + 1) → Fin (n + 1) := fun i =>
      if h : (μ'.val i.castSucc).val < n + 1 then ⟨(μ'.val i.castSucc).val, h⟩ else i
    have hf_inv : Function.Involutive f := by
      intro i
      dsimp [f]
      split_ifs with h1 h2
      · apply Fin.ext
        have h_eq : (⟨(μ'.val i.castSucc).val, h1⟩ : Fin (n + 1)).castSucc = μ'.val i.castSucc :=
          Fin.ext rfl
        have h_inv : μ'.val (⟨(μ'.val i.castSucc).val, h1⟩ : Fin (n + 1)).castSucc = i.castSucc := by
          rw [h_eq, μ'.property i.castSucc]
        exact congrArg (Fin.val : Fin (n + 2) → ℕ) h_inv
      · exfalso
        have h_eq : (⟨(μ'.val i.castSucc).val, h1⟩ : Fin (n + 1)).castSucc = μ'.val i.castSucc :=
          Fin.ext rfl
        have h_inv : μ'.val (⟨(μ'.val i.castSucc).val, h1⟩ : Fin (n + 1)).castSucc = i.castSucc := by
          rw [h_eq, μ'.property i.castSucc]
        rw [h_inv] at h2
        exact h2 i.isLt
      · rfl
    let μ : Roommates.Matching (Fin (n + 1)) := ofInvolutive f hf_inv
    refine ⟨μ, isAcceptable_top μ, ?_⟩
    intro i j hblk
    rcases hblk with ⟨hadj, hne_μ, hi_blk, hj_blk⟩
    have hij : i ≠ j := (SimpleGraph.top_adj _ _).1 hadj
    have hrk_ne : ∀ a b : Fin (n + 1), b ≠ a →
        p'.partnerRank a.castSucc b.castSucc = p.partnerRank a b := by
      intro a b hba
      have hne_last : (p.rank a b).castSucc ≠ Fin.last (n + 1) := Fin.castSucc_ne_last _
      have hne_n : (p.rank a b).castSucc ≠ ⟨n, by omega⟩ := by
        intro h
        have hval : (p.rank a b).val = n := congrArg Fin.val h
        have hself_a : (p.rank a a).val = n := by have := p.self_last a; omega
        exact hba ((p.rank a).injective (Fin.ext (hval.trans hself_a.symm)))
      simp only [Roommates.CompleteProfile.partnerRank, p', rank', Fin.lastCases_castSucc,
        Equiv.trans_apply, extendPerm_castSucc,
        Equiv.swap_apply_of_ne_of_ne hne_n hne_last, Fin.val_castSucc]
    have hrk_μ : ∀ a : Fin (n + 1),
        p.partnerRank a (μ.val a) ≤ p'.partnerRank a.castSucc (μ'.val a.castSucc) := by
      intro a
      change p.partnerRank a (f a) ≤ _
      dsimp [f]
      split_ifs with hlt
      · let b : Fin (n + 1) := ⟨(μ'.val a.castSucc).val, hlt⟩
        have hb_eq : μ'.val a.castSucc = b.castSucc := Fin.ext rfl
        change p.partnerRank a b ≤ p'.partnerRank a.castSucc (μ'.val a.castSucc)
        rw [hb_eq]
        by_cases hba : b = a
        · rw [hba, p.partnerRank_self, p'.partnerRank_self]; omega
        · rw [hrk_ne a b hba]
      · have hlast : μ'.val a.castSucc = Fin.last (n + 1) := by
          apply Fin.ext; have := (μ'.val a.castSucc).isLt; simp; omega
        rw [hlast, p.partnerRank_self]
        simp only [Roommates.CompleteProfile.partnerRank, p', rank', Fin.lastCases_castSucc,
          Equiv.trans_apply, extendPerm_last, Equiv.swap_apply_right]
        omega
    have hμ'_ne : μ'.val i.castSucc ≠ j.castSucc := by
      intro heq
      apply hne_μ
      change f i = j
      dsimp [f]
      rw [heq]
      simp [j.isLt]
    apply hμ'_stab i.castSucc j.castSucc
    refine ⟨(SimpleGraph.top_adj _ _).2 (fun h => hij (Fin.castSucc_injective _ h)), hμ'_ne, ?_, ?_⟩
    · rw [hrk_ne i j hij.symm]
      exact le_trans hi_blk (hrk_μ i)
    · rw [hrk_ne j i hij]
      exact le_trans hj_blk (hrk_μ j)

/-- Explicit 5-agent complete strict preference profile with no 2-stable matching
(1-based rank matrix: `(5,3,1,2,4)`, `(1,5,3,2,4)`, `(3,1,5,4,2)`, `(3,4,2,5,1)`, `(2,4,3,1,5)`). -/
def fiveAgentWitness : Roommates.CompleteProfile 5 where
  rank := ![
    ⟨![4, 2, 0, 1, 3], ![2, 3, 1, 4, 0], by decide, by decide⟩,
    ⟨![0, 4, 2, 1, 3], ![0, 3, 2, 4, 1], by decide, by decide⟩,
    ⟨![2, 0, 4, 3, 1], ![1, 4, 0, 3, 2], by decide, by decide⟩,
    ⟨![2, 3, 1, 4, 0], ![4, 2, 0, 1, 3], by decide, by decide⟩,
    ⟨![1, 3, 2, 0, 4], ![3, 0, 2, 1, 4], by decide, by decide⟩]
  self_last := by decide

/-- No matching on 5 agents is 2-stable for `fiveAgentWitness`. -/
theorem not_isKStable_two_fiveAgentWitness (μ : Roommates.Matching (Fin 5)) :
    ¬ Roommates.IsKStable ⊤ fiveAgentWitness.partnerRank 2 μ := by
  intro hstab
  have hno := hstab.2
  have hinv := μ.property
  have hblk : ∀ (i j : Fin 5), i ≠ j → μ.val i ≠ j →
      fiveAgentWitness.partnerRank i j + 2 ≤ fiveAgentWitness.partnerRank i (μ.val i) →
      fiveAgentWitness.partnerRank j i + 2 ≤ fiveAgentWitness.partnerRank j (μ.val j) → False :=
    fun i j hij hμ h1 h2 => hno i j ⟨(SimpleGraph.top_adj _ _).2 hij, hμ, h1, h2⟩
  have hne_of : ∀ {a b c : Fin 5}, μ.val b = c → a ≠ c → μ.val a ≠ b := by
    intro a b c hbc hac hab
    have := hinv a
    rw [hab, hbc] at this
    exact hac this.symm
  -- (3, 4) blocks unless μ 3 = 4, μ 3 = 2, or μ 4 = 0
  have hcases : μ.val 3 = 4 ∨ μ.val 3 = 2 ∨ μ.val 4 = 0 := by
    by_contra h
    push Not at h
    rcases h with ⟨h34, h32, h40⟩
    have h43 : μ.val 4 ≠ 3 := fun h => h34 (by rw [← h, hinv 4])
    have hr3 := (by decide : ∀ x : Fin 5, x ≠ 4 → x ≠ 2 →
      fiveAgentWitness.partnerRank 3 4 + 2 ≤ fiveAgentWitness.partnerRank 3 x) (μ.val 3) h34 h32
    have hr4 := (by decide : ∀ x : Fin 5, x ≠ 3 → x ≠ 0 →
      fiveAgentWitness.partnerRank 4 3 + 2 ≤ fiveAgentWitness.partnerRank 4 x) (μ.val 4) h43 h40
    exact hblk 3 4 (by decide) h34 hr3 hr4
  rcases hcases with h34 | h32 | h40
  · -- Case 1: μ 3 = 4 (so μ 4 = 3)
    have h43 : μ.val 4 = 3 := by rw [← h34, hinv 3]
    have h0cases := (by decide : ∀ x : Fin 5, x ≠ 3 → x ≠ 4 → x = 0 ∨ x = 1 ∨ x = 2)
      (μ.val 0) (hne_of h34 (by decide)) (hne_of h43 (by decide))
    rcases h0cases with h00 | h01 | h02
    · have hr1 := (by decide : ∀ x : Fin 5, x ≠ 0 → x ≠ 3 → x ≠ 4 →
        fiveAgentWitness.partnerRank 1 0 + 2 ≤ fiveAgentWitness.partnerRank 1 x)
        (μ.val 1) (hne_of h00 (by decide)) (hne_of h34 (by decide)) (hne_of h43 (by decide))
      exact hblk 0 1 (by decide) (by rw [h00]; decide) (by rw [h00]; decide) hr1
    · have h10 : μ.val 1 = 0 := by rw [← h01, hinv 0]
      have h22 := (by decide : ∀ x : Fin 5, x ≠ 0 → x ≠ 1 → x ≠ 3 → x ≠ 4 → x = 2)
        (μ.val 2) (hne_of h01 (by decide)) (hne_of h10 (by decide))
        (hne_of h34 (by decide)) (hne_of h43 (by decide))
      exact hblk 0 2 (by decide) (by rw [h01]; decide)
        (by rw [h01]; decide) (by rw [h22]; decide)
    · have h20 : μ.val 2 = 0 := by rw [← h02, hinv 0]
      have h11 := (by decide : ∀ x : Fin 5, x ≠ 0 → x ≠ 2 → x ≠ 3 → x ≠ 4 → x = 1)
        (μ.val 1) (hne_of h02 (by decide)) (hne_of h20 (by decide))
        (hne_of h34 (by decide)) (hne_of h43 (by decide))
      exact hblk 1 2 (by decide) (by rw [h11]; decide)
        (by rw [h11]; decide) (by rw [h20]; decide)
  · -- Case 2: μ 3 = 2 (so μ 2 = 3)
    have h23 : μ.val 2 = 3 := by rw [← h32, hinv 3]
    have h0cases := (by decide : ∀ x : Fin 5, x ≠ 2 → x ≠ 3 → x = 0 ∨ x = 1 ∨ x = 4)
      (μ.val 0) (hne_of h23 (by decide)) (hne_of h32 (by decide))
    rcases h0cases with h00 | h01 | h04
    · have hr1 := (by decide : ∀ x : Fin 5, x ≠ 0 → x ≠ 2 → x ≠ 3 →
        fiveAgentWitness.partnerRank 1 0 + 2 ≤ fiveAgentWitness.partnerRank 1 x)
        (μ.val 1) (hne_of h00 (by decide)) (hne_of h23 (by decide)) (hne_of h32 (by decide))
      exact hblk 0 1 (by decide) (by rw [h00]; decide) (by rw [h00]; decide) hr1
    · have h10 : μ.val 1 = 0 := by rw [← h01, hinv 0]
      have h44 := (by decide : ∀ x : Fin 5, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ≠ 3 → x = 4)
        (μ.val 4) (hne_of h01 (by decide)) (hne_of h10 (by decide))
        (hne_of h23 (by decide)) (hne_of h32 (by decide))
      exact hblk 2 4 (by decide) (by rw [h23]; decide)
        (by rw [h23]; decide) (by rw [h44]; decide)
    · have h40' : μ.val 4 = 0 := by rw [← h04, hinv 0]
      have h11 := (by decide : ∀ x : Fin 5, x ≠ 0 → x ≠ 2 → x ≠ 3 → x ≠ 4 → x = 1)
        (μ.val 1) (hne_of h04 (by decide)) (hne_of h23 (by decide))
        (hne_of h32 (by decide)) (hne_of h40' (by decide))
      exact hblk 1 2 (by decide) (by rw [h11]; decide)
        (by rw [h11]; decide) (by rw [h23]; decide)
  · -- Case 3: μ 4 = 0 (so μ 0 = 4)
    have h04 : μ.val 0 = 4 := by rw [← h40, hinv 4]
    have h3cases := (by decide : ∀ x : Fin 5, x ≠ 0 → x ≠ 4 → x = 1 ∨ x = 2 ∨ x = 3)
      (μ.val 3) (hne_of h04 (by decide)) (hne_of h40 (by decide))
    rcases h3cases with h31 | h32' | h33
    · have h13 : μ.val 1 = 3 := by rw [← h31, hinv 3]
      have h22 := (by decide : ∀ x : Fin 5, x ≠ 0 → x ≠ 1 → x ≠ 3 → x ≠ 4 → x = 2)
        (μ.val 2) (hne_of h04 (by decide)) (hne_of h13 (by decide))
        (hne_of h31 (by decide)) (hne_of h40 (by decide))
      exact hblk 0 2 (by decide) (by rw [h04]; decide)
        (by rw [h04]; decide) (by rw [h22]; decide)
    · have h23 : μ.val 2 = 3 := by rw [← h32', hinv 3]
      have h11 := (by decide : ∀ x : Fin 5, x ≠ 0 → x ≠ 2 → x ≠ 3 → x ≠ 4 → x = 1)
        (μ.val 1) (hne_of h04 (by decide)) (hne_of h23 (by decide))
        (hne_of h32' (by decide)) (hne_of h40 (by decide))
      exact hblk 1 2 (by decide) (by rw [h11]; decide)
        (by rw [h11]; decide) (by rw [h23]; decide)
    · exact hblk 0 3 (by decide) (by rw [h04]; decide)
        (by rw [h04]; decide) (by rw [h33]; decide)

/-- Lower bound `3 ≤ K(5)`, witnessed by `fiveAgentWitness`. -/
theorem three_le_stabilityThreshold_five : 3 ≤ Roommates.stabilityThreshold 5 := by
  by_contra hlt
  obtain ⟨hpos, hex⟩ := Roommates.stabilityThreshold_spec 5
  obtain ⟨μ, hacc, hstab⟩ := hex fiveAgentWitness
  have hk_le : Roommates.stabilityThreshold 5 ≤ 2 := by omega
  apply not_isKStable_two_fiveAgentWitness μ
  refine ⟨hacc, fun i j ⟨hadj, hne, h1, h2⟩ => hstab i j ⟨hadj, hne, ?_, ?_⟩⟩ <;> omega

/-- Exact stability threshold for 5 agents: `K(5) = 3`. -/
theorem stabilityThreshold_five : Roommates.stabilityThreshold 5 = 3 := by
  have h1 : 3 ≤ Roommates.stabilityThreshold 5 := three_le_stabilityThreshold_five
  have h2 : Roommates.stabilityThreshold 5 ≤ Roommates.stabilityThreshold 6 := stabilityThreshold_mono 5
  have h3 : Roommates.stabilityThreshold 6 ≤ Roommates.stabilityThreshold 7 := stabilityThreshold_mono 6
  have h4 : Roommates.stabilityThreshold 7 ≤ 3 := stabilityThreshold_odd_le 3 (le_refl 3)
  omega

/-- Exact stability threshold for 6 agents: `K(6) = 3`. -/
theorem stabilityThreshold_six : Roommates.stabilityThreshold 6 = 3 := by
  have h1 : 3 ≤ Roommates.stabilityThreshold 5 := three_le_stabilityThreshold_five
  have h2 : Roommates.stabilityThreshold 5 ≤ Roommates.stabilityThreshold 6 := stabilityThreshold_mono 5
  have h3 : Roommates.stabilityThreshold 6 ≤ Roommates.stabilityThreshold 7 := stabilityThreshold_mono 6
  have h4 : Roommates.stabilityThreshold 7 ≤ 3 := stabilityThreshold_odd_le 3 (le_refl 3)
  omega

/-- Exact stability threshold for 7 agents: `K(7) = 3 < 4 = ⌈7 / 2⌉`
(smallest odd counterexample to the Fanelli–Moscardelli conjecture). -/
theorem stabilityThreshold_seven : Roommates.stabilityThreshold 7 = 3 := by
  have h1 : 3 ≤ Roommates.stabilityThreshold 5 := three_le_stabilityThreshold_five
  have h2 : Roommates.stabilityThreshold 5 ≤ Roommates.stabilityThreshold 6 := stabilityThreshold_mono 5
  have h3 : Roommates.stabilityThreshold 6 ≤ Roommates.stabilityThreshold 7 := stabilityThreshold_mono 6
  have h4 : Roommates.stabilityThreshold 7 ≤ 3 := stabilityThreshold_odd_le 3 (le_refl 3)
  omega

end FanelliMoscardelli

