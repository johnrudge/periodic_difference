/-
# `PeriodicDifference/Problem11Small.lean` — the primitive supports at orders 2 and 3

The analytic cases of `thm:main` in the sequence form: `S = {1}` at `K = 2`
(`thm:order2`, `Lyness.order2_classification`), `S = {1, 2}` at `K = 3` (`thm:order3`,
`Order3.order3_classification`, and `Order3Zero.not_periodic_of_admissible` at `θ = 0`).  The one
support at `K = 6` that needs separate treatment, `{1, 3, 5}`, is `PeriodicDifference/Order6Cert.lean`.
-/
import PeriodicDifference.Problem11Fold
import PeriodicDifference.Order2
import PeriodicDifference.Order3
import PeriodicDifference.Order3Zero

namespace PeriodicDifference
namespace Problem11

open Trop
open Trop.Bump.PerSupport (Pal Prim)

variable {K : ℕ} {J : List ℕ} {co : ℕ → ℝ}

/-! ## `K = 2`, `S = {1}` -/

theorem order2_case (h : Admissible 2 J co) (hs : supp J = {1}) {p : ℕ} (hp : 0 < p)
    (hg : GloballyPeriodic 2 J co p) : 0 ∉ J ∨ co 0 = co 1 ^ 2 := by
  by_cases h0 : 0 ∈ J
  · right
    have h1 : 1 ∈ J := (mem_supp.mp (hs ▸ Finset.mem_singleton_self 1)).2
    have := Lyness.order2_classification (h.pos 0 h0) (h.pos 1 h1) one_pos hp
      (fun x hx hrec => hg x hx fun n => by
        rw [rhs_eq_range h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
          cJ_of_mem h0, cJ_of_mem h1]
        have := hrec n; simp only [if_pos, one_ne_zero, if_false] at *; linarith)
    linarith
  · exact Or.inl h0

/-! ## `K = 3`, `S = {1, 2}` -/

theorem order3_case (h : Admissible 3 J co) (hs : supp J = {1, 2}) {p : ℕ} (hp : 0 < p)
    (hg : GloballyPeriodic 3 J co p) : co 0 = co 1 ^ 2 := by
  have h1 : 1 ∈ J := (mem_supp.mp (hs ▸ (by simp : (1 : ℕ) ∈ ({1, 2} : Finset ℕ)))).2
  have h2 : 2 ∈ J := (mem_supp.mp (hs ▸ (by simp : (2 : ℕ) ∈ ({1, 2} : Finset ℕ)))).2
  have hc2 : co 2 = co 1 := h.copal 1 h1 one_ne_zero
  by_cases h0 : 0 ∈ J
  · have := Lyness3.order3_classification (h.pos 0 h0) (h.pos 1 h1) one_pos hp
      (fun x hx hrec => hg x hx fun n => by
        rw [rhs_eq_range h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_zero, cJ_of_mem h0, cJ_of_mem h1, cJ_of_mem h2, hc2]
        have := hrec n; simp only [if_pos, one_ne_zero, if_false] at *; norm_num at *; linarith)
    linarith
  · exact (Order3Zero.not_periodic_of_admissible h hs h0 hp hg).elim

end Problem11
end PeriodicDifference
