/-
# `PeriodicDifference/Kronecker.lean` — the totally real Kronecker step

Theorem U settles every two-term support `S = {j, k-j}` at every order, and its
endgame is Kronecker's theorem in the **closed-interval form**: a totally real
algebraic integer all of whose conjugates lie in `[-2,2]` is `ζ + ζ⁻¹` for a root of
unity `ζ`.  Mathlib has Kronecker on the closed unit *disc*
(`NumberField.Embeddings.pow_eq_one_of_norm_le_one`); this file supplies the bridge
from the interval to the disc, which is the step the whole endgame pivots on.

The bridge is the observation that `z + 1/z = r` puts `z` on the unit circle exactly
when `r` is real with `|r| ≤ 2`.  Proved here without any polar decomposition: if
`z ≠ z̄` then `z` and `z̄` are the two roots of `X² − rX + 1`, so `z z̄ = 1` by Vieta;
and if `z = z̄` then `z` is real, `(z − r/2)² = r²/4 − 1 ≤ 0` forces `r² = 4` and
`z = ±1`.

## Where it is used

`PeriodicDifference/TwoTermKron.lean` applies `isRootOfUnity_of_conj_mem_Icc` to the two-term
supports; the rest of Theorem U (the root-of-unity endgame) is in the `TwoTerm*` modules.
-/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Tactic

namespace PeriodicDifference
namespace Kron

open Complex

/-- **The interval-to-circle bridge.**  A root of `X² − rX + 1` with `r` real and
`|r| ≤ 2` lies on the unit circle. -/
theorem norm_eq_one_of_quadratic {z : ℂ} {r : ℝ} (hr : |r| ≤ 2)
    (h : z ^ 2 - (r : ℂ) * z + 1 = 0) : ‖z‖ = 1 := by
  have hconj : (starRingEnd ℂ z) ^ 2 - (r : ℂ) * (starRingEnd ℂ z) + 1 = 0 := by
    have := congrArg (starRingEnd ℂ) h; simpa using this
  by_cases hz : z = starRingEnd ℂ z
  · -- `z` is real; the discriminant `r² − 4` is `≤ 0`, so it must vanish
    have him : z.im = 0 := Complex.conj_eq_iff_im.mp hz.symm
    have hre : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
    rw [hre] at h
    have hR : z.re ^ 2 - r * z.re + 1 = 0 := by exact_mod_cast h
    obtain ⟨hl, hu⟩ := abs_le.mp hr
    have hkey : (z.re - r / 2) ^ 2 = r ^ 2 / 4 - 1 := by linear_combination hR
    have hr4 : r ^ 2 ≤ 4 := by nlinarith
    have hr4' : r ^ 2 = 4 := by nlinarith [sq_nonneg (z.re - r / 2)]
    have hzero : z.re - r / 2 = 0 := by
      have h0 : (z.re - r / 2) ^ 2 = 0 := by rw [hkey, hr4']; ring
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
    have hsq : z.re ^ 2 = 1 := by
      have hhalf : z.re = r / 2 := by linarith
      rw [hhalf]; nlinarith
    have hpm : z.re = 1 ∨ z.re = -1 := by
      have hfac : (z.re - 1) * (z.re + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hfac with h1 | h1
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rw [hre, Complex.norm_real]
    rcases hpm with h1 | h1 <;> rw [h1] <;> norm_num
  · -- `z ≠ z̄`, so they are the two roots and Vieta gives `z z̄ = 1`
    have hd : (z - starRingEnd ℂ z) * (z + starRingEnd ℂ z - (r : ℂ)) = 0 := by
      linear_combination h - hconj
    have hsum : z + starRingEnd ℂ z = (r : ℂ) :=
      sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left (sub_ne_zero.mpr hz))
    have hprod : z * starRingEnd ℂ z = 1 := by linear_combination -h + z * hsum
    have hn : ‖z‖ * ‖z‖ = 1 := by
      have := congrArg Norm.norm hprod
      simpa [norm_mul, RCLike.norm_conj] using this
    nlinarith [norm_nonneg z]

/-- **Kronecker in the closed-interval form.**  Let `K` be a number field, `μ ∈ K` an
algebraic integer every one of whose complex embeddings is real and lies in `[-2,2]`,
and let `ζ ∈ K` satisfy `ζ² − μζ + 1 = 0`.  Then `ζ` is a root of unity.

This is the form Theorem U's endgame uses: `μ = ε + 1` is the shifted coefficient, the
interval is `[t₋ + 1, 2] ⊆ [-2,2]` supplied by Facts A and B, and the conclusion feeds
the classification of `2cos(2πq/n)` with all conjugates bounded below. -/
theorem isRootOfUnity_of_conj_mem_Icc {K : Type*} [Field K] [NumberField K] {μ ζ : K}
    (hμ : IsIntegral ℤ μ) (hζ : ζ ^ 2 - μ * ζ + 1 = 0)
    (hconj : ∀ φ : K →+* ℂ, ∃ r : ℝ, φ μ = (r : ℂ) ∧ |r| ≤ 2) :
    ∃ (n : ℕ) (_ : 0 < n), ζ ^ n = 1 := by
  classical
  -- `ζ` is integral: a root of a monic quadratic over `ℤ[μ]`, and `ℤ[μ]` is integral
  have hζint : IsIntegral ℤ ζ := by
    have hsub : IsIntegral (Algebra.adjoin ℤ ({μ} : Set K)) ζ := by
      refine ⟨Polynomial.X ^ 2 -
        Polynomial.C ⟨μ, Algebra.self_mem_adjoin_singleton ℤ μ⟩ * Polynomial.X + 1,
        ?_, ?_⟩
      · monicity!
      · simp [Polynomial.eval₂_add, Polynomial.eval₂_sub]
        linear_combination hζ
    haveI : Algebra.IsIntegral ℤ (Algebra.adjoin ℤ ({μ} : Set K)) :=
      Algebra.IsIntegral.adjoin (fun x hx => by rcases hx with rfl; exact hμ)
    exact isIntegral_trans ζ hsub
  -- `ζ ≠ 0`, since `ζ² − μζ + 1 = 0` would otherwise give `1 = 0`
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0] at hζ
    simp at hζ
  -- every embedding sends `ζ` to a point of the unit circle
  refine NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hζ0 hζint fun φ => ?_
  obtain ⟨r, hr, hrle⟩ := hconj φ
  have hquad : (φ ζ) ^ 2 - (r : ℂ) * (φ ζ) + 1 = 0 := by
    have := congrArg φ hζ
    simpa [hr] using this
  exact le_of_eq (norm_eq_one_of_quadratic hrle hquad)

end Kron
end PeriodicDifference
