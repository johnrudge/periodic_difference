/-
# `PeriodicDifference/Problem11Defs.lean` — the statement of Problem 11 and the sequence form

Definitions for `PeriodicDifference/Problem11Complete.lean` (`thm:main`):

* `Problem11.Member E` — `E` is equivalent (rescaling, unfolding) to one of the five
  equations of `eq:fivefamilies`, written out as explicit coefficient patterns;
* `Problem11.Admissible K J co` — the data `x_{n+K} xₙ = rhs J co x n` that a periodic
  branch-(a) equation produces through the bridge (slot list, positive palindromic
  coefficients), and `TropMember`, the members in that form.

Only `Eqn`/`Astar` (`PeriodicDifference/FamilyA.lean`), `rhs`/`GloballyPeriodic` (`PeriodicDifference/Tropical.lean`)
and `Pal`/`Prim` (`PeriodicDifference/PerSupportDefs.lean`) are imported.
-/
import PeriodicDifference.FamilyA
import PeriodicDifference.Tropical
import PeriodicDifference.PerSupportDefs

namespace PeriodicDifference
namespace Problem11

open Trop
open Trop.Bump.PerSupport (Pal Prim)

/-! ## The equations -/

/-- The coefficient of `x_{n+m}` in the numerator of `E` (`0` beyond the order). -/
noncomputable def coef {k : ℕ} (E : Eqn k) (m : ℕ) : ℝ :=
  if h : m < k + 1 then E.A ⟨m, h⟩ else 0

/-- `E` is `x_{n+k+1} = xₙ` (the `(k+1)`-fold unfolding of `x_{n+1} = xₙ`). -/
def IsShift {k : ℕ} (E : Eqn k) : Prop :=
  E.B 0 = 0 ∧ E.a = 0 ∧ (∀ j : Fin k, E.A j.succ = 0) ∧ (∀ j : Fin k, E.B j.succ = 0) ∧
    E.A 0 = E.b

/-- **The five known equations, up to rescaling and unfolding.**  Writing `K = k + 1` for the
order, `E` is one of
* the shift `x_{n+K} = xₙ` (unfolding of `x_{n+1} = xₙ`);
* `B₀ x_{n+K} xₙ = a` (unfolding of `x_{n+1} = 1/xₙ`);
* `B₀ x_{n+2m} xₙ = A_m x_{n+m}` (unfolding of `x_{n+2} = x_{n+1}/xₙ`);
* `B₀ x_{n+2m} xₙ = a + A_m x_{n+m}`, `a B₀ = A_m²` (unfolding of Lyness);
* `B₀ x_{n+3m} xₙ = a + A_m (x_{n+m} + x_{n+2m})`, `a B₀ = A_m²` (unfolding of the
  period-8 equation). -/
def Member {k : ℕ} (E : Eqn k) : Prop :=
  IsShift E ∨
  (E.Astar ∧ ∀ m, 1 ≤ m → coef E m = 0) ∨
  (E.Astar ∧ E.a = 0 ∧ ∃ m, k + 1 = 2 * m ∧ ∀ j, 1 ≤ j → j ≠ m → coef E j = 0) ∨
  (E.Astar ∧ ∃ m, k + 1 = 2 * m ∧ (∀ j, 1 ≤ j → j ≠ m → coef E j = 0) ∧
    E.a * E.B 0 = coef E m ^ 2) ∨
  (E.Astar ∧ ∃ m, k + 1 = 3 * m ∧ (∀ j, 1 ≤ j → j ≠ m → j ≠ 2 * m → coef E j = 0) ∧
    coef E (2 * m) = coef E m ∧ E.a * E.B 0 = coef E m ^ 2)

/-! ## The sequence form -/

/-- The support: the nonzero slots. -/
def supp (J : List ℕ) : Finset ℕ := J.toFinset.erase 0

/-- The data of `x_{n+K} xₙ = Σ_{j ∈ J} co_j x_{n+j}` (slot `0` the constant term) as a
periodic branch-(a) equation produces it: a duplicate-free slot list below `K`, positive
coefficients on it, palindromic support and palindromic coefficients. -/
structure Admissible (K : ℕ) (J : List ℕ) (co : ℕ → ℝ) : Prop where
  K_pos : 0 < K
  nodup : J.Nodup
  lt : ∀ j ∈ J, j < K
  pos : ∀ j ∈ J, 0 < co j
  pal : ∀ j ∈ J, j ≠ 0 → K - j ∈ J
  copal : ∀ j ∈ J, j ≠ 0 → co (K - j) = co j

/-- The members in the sequence form. -/
def TropMember (K : ℕ) (J : List ℕ) (co : ℕ → ℝ) : Prop :=
  supp J = ∅ ∨ (∃ m, K = 2 * m ∧ supp J = {m} ∧ (0 ∉ J ∨ co 0 = co m ^ 2)) ∨
    (∃ m, K = 3 * m ∧ supp J = {m, 2 * m} ∧ co 0 = co m ^ 2)

/-! ## Basic facts -/

lemma mem_supp {J : List ℕ} {m : ℕ} : m ∈ supp J ↔ m ≠ 0 ∧ m ∈ J := by
  simp [supp]

namespace Admissible

variable {K : ℕ} {J : List ℕ} {co : ℕ → ℝ}

lemma supp_sub (h : Admissible K J co) : supp J ⊆ Finset.Icc 1 (K - 1) := by
  intro m hm
  rw [mem_supp] at hm
  have := h.lt m hm.2
  simp only [Finset.mem_Icc]; omega

lemma pal_supp (h : Admissible K J co) : Pal K (supp J) := by
  intro m hm
  rw [mem_supp] at hm ⊢
  have := h.lt m hm.2
  exact ⟨by omega, h.pal m hm.2 hm.1⟩

end Admissible

/-- The coefficient function, zero off the slot list. -/
noncomputable def cJ (J : List ℕ) (co : ℕ → ℝ) (m : ℕ) : ℝ := if m ∈ J then co m else 0

lemma cJ_of_mem {J : List ℕ} {co : ℕ → ℝ} {m : ℕ} (hm : m ∈ J) : cJ J co m = co m := if_pos hm

lemma cJ_of_not_mem {J : List ℕ} {co : ℕ → ℝ} {m : ℕ} (hm : m ∉ J) : cJ J co m = 0 := if_neg hm

/-- A common divisor of a primitive support and its order is `1`. -/
lemma eq_one_of_prim {K : ℕ} {S : Finset ℕ} (hprim : Prim K S) {c : ℕ} (hS : ∀ x ∈ S, c ∣ x)
    (hK : c ∣ K) : c = 1 :=
  Nat.dvd_one.mp (hprim ▸ Nat.dvd_gcd (Finset.dvd_gcd hS) hK)

lemma rhs_eq_range {K : ℕ} {J : List ℕ} {co : ℕ → ℝ} (h : Admissible K J co)
    (x : ℕ → ℝ) (n : ℕ) :
    rhs J co x n = ∑ m ∈ Finset.range K, cJ J co m * (if m = 0 then 1 else x (n + m)) := by
  rw [rhs, ← List.sum_toFinset _ h.nodup]
  have hsub : J.toFinset ⊆ Finset.range K := by
    intro m hm
    exact Finset.mem_range.mpr (h.lt m (List.mem_toFinset.mp hm))
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [cJ, if_pos (List.mem_toFinset.mp hm)]
  · intro m _ hm
    rw [cJ, if_neg (fun h' => hm (List.mem_toFinset.mpr h'))]
    ring

lemma gp_congr {K : ℕ} {J J' : List ℕ} {co co' : ℕ → ℝ} {p : ℕ}
    (h : ∀ x n, rhs J co x n = rhs J' co' x n) (hg : GloballyPeriodic K J co p) :
    GloballyPeriodic K J' co' p := by
  intro x hx hrec
  exact hg x hx fun n => (hrec n).trans (h x n).symm

end Problem11
end PeriodicDifference
