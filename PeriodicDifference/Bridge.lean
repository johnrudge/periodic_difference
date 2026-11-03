/-
# `PeriodicDifference/Bridge.lean` — from `Eqn` to `Trop.GloballyPeriodic`

`PeriodicDifference/Tropical.lean` states its own periodicity predicate,

  `GloballyPeriodic K J co p := ∀ x, (∀ n, 0 < x n) →
      (∀ n, x (n + K) * x n = rhs J co x n) → ∀ n, x (n + p) = x n`,

and the periodicity of the degeneration (`thm:P`) is a statement about it.  The rest of the
development works with `Eqn k` — Gasull's family as written in the paper — and its state map
`Eqn.F`.  Nothing connected the two: the certificates proved facts about a predicate that was
*asserted* to encode branch (a) rather than *derived* from it.

This file supplies the missing step.  For an equation in branch (a) (`Astar`: no
`x_n` in the numerator, no constant in the denominator, and no `x_{n+j}` in the
denominator for `j ≥ 1`), global periodicity of `Eqn.F` implies
`Trop.GloballyPeriodic` for the slot list and coefficients read off `E`.

The content is bookkeeping, and that is the point: it is exactly where an off-by-one
between `E.A j.succ` and the tropical slot index would hide, and an off-by-one there
would attach every certificate to the wrong support.  Making Lean check it is the only
way to know.

## The dictionary

| `Eqn k` (order `k+1`) | tropical |
|---|---|
| `E.a` (the paper's `A₀`) | slot `0`, present iff `E.a > 0` — this is `θ = 1` |
| `E.A ⟨m, _⟩`, `1 ≤ m ≤ k` | slot `m`, present iff the coefficient is positive |
| `E.B 0` (the paper's `B₁`) | the normalisation: every coefficient is divided by it |
| `Eqn.F^[p] = id` on positive states | `p`-periodicity of every positive solution |

`E.A 0` is the coefficient of the *oldest* term `x_n`, and `Astar` sets it to zero — so
slot indices run `1 … k` and never `0` from the `A`s, which is why slot `0` is free to
mean the constant term.
-/

import PeriodicDifference.FamilyA
import PeriodicDifference.Tropical

namespace PeriodicDifference

open Trop

variable {k : ℕ}

/-! ## Two list-sum lemmas

`rhs` sums over a *list* of slots; the equation sums over a `Finset` of coefficient
indices.  These convert, and let the zero coefficients be dropped.
-/

namespace Bridge

lemma list_range_map_sum (f : ℕ → ℝ) : ∀ n : ℕ,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

lemma list_filter_map_sum {p : ℕ → Bool} {f : ℕ → ℝ}
    (h : ∀ m, p m = false → f m = 0) : ∀ l : List ℕ,
    ((l.filter p).map f).sum = (l.map f).sum := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    rcases hp : p a with _ | _
    · rw [List.filter_cons_of_neg (by simp [hp]), ih, List.map_cons, List.sum_cons,
        h a hp, zero_add]
    · rw [List.filter_cons_of_pos (by simp [hp]), List.map_cons, List.sum_cons, ih,
        List.map_cons, List.sum_cons]

end Bridge

namespace Eqn

/-! ## The slot list and the coefficients -/

open Classical in
/-- The coefficient attached to slot `m`, normalised by `B₀`: slot `0` is the constant
term `a`, slot `m ∈ {1,…,k}` is `A_m`, and everything else is `0`. -/
noncomputable def coefAt (E : Eqn k) (m : ℕ) : ℝ :=
  (if m = 0 then E.a else if h : m < k + 1 then E.A ⟨m, h⟩ else 0) / E.B 0

open Classical in
/-- The slot list: every `m ≤ k` whose coefficient is positive.  Slot `0` is present
exactly when the constant term is, i.e. exactly when `θ = 1`. -/
noncomputable def slots (E : Eqn k) : List ℕ :=
  (List.range (k + 1)).filter fun m => decide (0 < E.coefAt m)

lemma coefAt_nonneg (E : Eqn k) (hB : 0 < E.B 0) (m : ℕ) : 0 ≤ E.coefAt m := by
  rw [coefAt]
  refine div_nonneg ?_ hB.le
  split
  · exact E.a_nonneg
  · split
    · exact E.A_nonneg _
    · exact le_rfl

lemma coefAt_eq_zero_of_not_pos (E : Eqn k) (hB : 0 < E.B 0) {m : ℕ}
    (h : ¬ 0 < E.coefAt m) : E.coefAt m = 0 :=
  le_antisymm (not_lt.mp h) (E.coefAt_nonneg hB m)

lemma mem_slots (E : Eqn k) {m : ℕ} (h : m ∈ E.slots) : m ≤ k ∧ 0 < E.coefAt m := by
  classical
  rw [slots, List.mem_filter] at h
  exact ⟨by have := List.mem_range.mp h.1; omega, by simpa using h.2⟩

lemma slots_le (E : Eqn k) : ∀ m ∈ E.slots, m ≤ k := fun _ h => (E.mem_slots h).1

lemma slots_pos (E : Eqn k) : ∀ m ∈ E.slots, 0 < E.coefAt m :=
  fun _ h => (E.mem_slots h).2

lemma mem_slots_of (E : Eqn k) {m : ℕ} (hm : m ≤ k) (hpos : 0 < E.coefAt m) :
    m ∈ E.slots := by
  classical
  rw [slots, List.mem_filter]
  exact ⟨List.mem_range.mpr (by omega), by simpa using hpos⟩

/-! ## The right-hand side, in both languages -/

/-- `rhs` over the slot list is the equation's numerator over `B₀`.  The zero
coefficients drop out of the list, and `Astar` kills the `m = 0` term of the `A`-sum,
which is what leaves slot `0` free to mean the constant term. -/
lemma rhs_slots (E : Eqn k) (h : Astar E) (hB : 0 < E.B 0) (x : ℕ → ℝ) (n : ℕ) :
    rhs E.slots E.coefAt x n
      = (E.a + ∑ j : Fin (k + 1), E.A j * x (n + j)) / E.B 0 := by
  classical
  set f : ℕ → ℝ := fun m => E.coefAt m * (if m = 0 then 1 else x (n + m)) with hf
  have hzero : ∀ m, (decide (0 < E.coefAt m)) = false → f m = 0 := by
    intro m hm
    simp only [decide_eq_false_iff_not] at hm
    simp [hf, E.coefAt_eq_zero_of_not_pos hB hm]
  have h1 : rhs E.slots E.coefAt x n = ((List.range (k + 1)).map f).sum := by
    rw [rhs, slots]; exact Bridge.list_filter_map_sum hzero _
  rw [h1, Bridge.list_range_map_sum, Finset.sum_range f, add_div, Finset.sum_div,
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hz : E.A 0 * x (n + ((0 : Fin (k + 1)) : ℕ)) / E.B 0 = 0 := by
    rw [h.A0]; simp
  rw [hz, zero_add]
  congr 1
  · -- the constant slot
    show f 0 = E.a / E.B 0
    simp [hf, coefAt]
  · -- slots `1 … k`
    refine Finset.sum_congr rfl fun i _ => ?_
    have hne : ((i.succ : Fin (k + 1)) : ℕ) ≠ 0 := by simp [Fin.val_succ]
    have hlt : ((i.succ : Fin (k + 1)) : ℕ) < k + 1 := i.succ.isLt
    show f _ = _
    rw [hf]
    simp only [coefAt, if_neg hne, dif_pos hlt]
    rw [Fin.eta]
    ring

/-! ## The window of a sequence, and the state map -/

/-- The state at time `n` of a sequence: `k + 1` consecutive terms, oldest first. -/
def win (x : ℕ → ℝ) (n : ℕ) : Fin (k + 1) → ℝ := fun j => x (n + j)

lemma win_pos {x : ℕ → ℝ} (hx : ∀ n, 0 < x n) (n : ℕ) : Pos (win (k := k) x n) :=
  fun _ => hx _

/-- One step of `Eqn.F` advances the window, provided the sequence solves the equation
in the tropical normalisation. -/
lemma F_win (E : Eqn k) (h : Astar E) (hB : 0 < E.B 0) {x : ℕ → ℝ}
    (hx : ∀ n, 0 < x n)
    (hrec : ∀ n, x (n + (k + 1)) * x n = rhs E.slots E.coefAt x n) (n : ℕ) :
    E.F (win x n) = win x (n + 1) := by
  classical
  -- the denominator collapses to `B₀ · xₙ`
  have hden : E.den (win (k := k) x n) = E.B 0 * x n := by
    rw [den, h.b0, zero_add, Fin.sum_univ_succ]
    have : ∀ i : Fin k, E.B i.succ * win (k := k) x n i.succ = 0 := by
      intro i; rw [h.Bsucc i]; ring
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp [win]
  have hdpos : 0 < E.den (win (k := k) x n) := by rw [hden]; exact mul_pos hB (hx n)
  -- the numerator is `B₀ ·` the tropical right-hand side
  have hnum : E.num (win (k := k) x n) = E.B 0 * rhs E.slots E.coefAt x n := by
    rw [E.rhs_slots h hB, num]
    field_simp
    rfl
  -- so the appended value is the next term
  have hg : E.g (win (k := k) x n) = x (n + (k + 1)) := by
    rw [g, hnum, hden, ← hrec n]
    field_simp
    rw [mul_div_assoc, div_self (hx n).ne', mul_one]
  funext j
  refine Fin.lastCases ?_ ?_ j
  · rw [F, Fin.snoc_last, hg, win]
    congr 1
    simp [Fin.val_last]
    omega
  · intro i
    rw [F, Fin.snoc_castSucc, Fin.tail, win, win]
    congr 1
    simp [Fin.val_succ]
    omega

/-! ## The bridge -/

/-- **The bridge.**  A globally `p`-periodic branch-(a) equation gives a globally
`p`-periodic min-plus problem for the slot list and coefficients read off `E`.

Consequently every refutation of `GloballyPeriodic` (a σ-bump carrier, a tangent
direction, a certificate) refutes global periodicity of the *equation*, for every positive
coefficient choice on that support. -/
theorem Astar.trop_globallyPeriodic {E : Eqn k} (h : Astar E) (hB : 0 < E.B 0)
    {p : ℕ} (hper : ∀ u, Pos u → E.F^[p] u = u) :
    GloballyPeriodic (k + 1) E.slots E.coefAt p := by
  intro x hx hrec n
  -- the window advances with the sequence, so it advances `m` steps at a time
  have hiter : ∀ m n, E.F^[m] (win x n) = win (k := k) x (n + m) := by
    intro m
    induction m with
    | zero => intro n; simp
    | succ m ih =>
      intro n
      rw [Function.iterate_succ_apply, E.F_win h hB hx hrec n, ih (n + 1)]
      congr 1
      omega
  have := hper (win x n) (win_pos hx n)
  rw [hiter p n] at this
  have hcongr := congrFun this ⟨0, by omega⟩
  simpa [win] using hcongr

end Eqn

/-! ## The slot dictionary, checked against its description

Three statements pinning down what `slots` means, so that "slot `0` is `θ`" and
"slot `m` is `A_m`" are theorems rather than comments. -/

/-- `θ = 1` exactly when the constant term is present. -/
theorem Eqn.zero_mem_slots_iff {E : Eqn k} (hB : 0 < E.B 0) :
    0 ∈ E.slots ↔ 0 < E.a := by
  constructor
  · intro h
    have := (E.mem_slots h).2
    rw [Eqn.coefAt, if_pos rfl] at this
    exact (div_pos_iff_of_pos_right hB).mp this
  · intro h
    refine E.mem_slots_of (by omega) ?_
    rw [Eqn.coefAt, if_pos rfl]
    exact div_pos h hB

/-- Slot `m ≥ 1` is present exactly when the coefficient `A_m` is positive — the
coefficient of `x_{n+m}`, not of `x_{n+m±1}`. -/
theorem Eqn.mem_slots_iff {E : Eqn k} (hB : 0 < E.B 0) {m : ℕ} (hm0 : m ≠ 0)
    (hmk : m < k + 1) : m ∈ E.slots ↔ 0 < E.A ⟨m, hmk⟩ := by
  constructor
  · intro h
    have := (E.mem_slots h).2
    rw [Eqn.coefAt, if_neg hm0, dif_pos hmk] at this
    exact (div_pos_iff_of_pos_right hB).mp this
  · intro h
    refine E.mem_slots_of (by omega) ?_
    rw [Eqn.coefAt, if_neg hm0, dif_pos hmk]
    exact div_pos h hB

/-! ## Where the bridge is used

`PeriodicDifference/Problem11Complete.lean` (`thm:main`) passes every equation of branch (a) through
`Astar.trop_globallyPeriodic` and then closes every support in the sequence form
(`PeriodicDifference/Problem11Prim.lean`): the σ-bump carriers, the order-6 certificates of
`PeriodicDifference/QppCertsOrder6.lean`, the full support (`PeriodicDifference/FullSupport.lean`) and the two-term
supports (`PeriodicDifference/TwoTermFinal.lean`). -/

end PeriodicDifference
