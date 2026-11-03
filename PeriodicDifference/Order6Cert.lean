/-
# `PeriodicDifference/Order6Cert.lean` — the support `{1, 3, 5}` at order 6

The only primitive palindromic support at order `6` with at least three elements that carries
no σ-bump is `{1, 3, 5}` (`BumpSat1.exc_none`).  It is killed, at both `θ`, by the one
tied-carrier certificate `Cert6.cert` of `PeriodicDifference/QppCertsOrder6.lean` (`prop:order6cert`),
applied to any slot list with the certificate's members.
-/
import PeriodicDifference.Problem11Defs
import PeriodicDifference.QppCertsOrder6

namespace PeriodicDifference
namespace Problem11

open Trop

variable {J : List ℕ} {co : ℕ → ℝ}

/-- **`prop:order6cert`**: no equation of order `6` with support `{1, 3, 5}` is globally
periodic, with or without the constant term. -/
theorem order6_135 (h : Admissible 6 J co) (hs : supp J = {1, 3, 5}) {p : ℕ} (hp : 0 < p)
    (hg : GloballyPeriodic 6 J co p) : False := by
  refine Cert6.no_periodic (decide (0 ∈ J)) (fun m => ?_) h.pos hp hg
  have : m ∈ supp J ↔ m ∈ ({1, 3, 5} : Finset ℕ) := by rw [hs]
  rw [mem_supp] at this
  rcases eq_or_ne m 0 with rfl | hm0
  · by_cases h0 : 0 ∈ J <;> simp [Cert6.cert, h0]
  · by_cases h0 : 0 ∈ J <;> simp_all [Cert6.cert]

end Problem11
end PeriodicDifference
