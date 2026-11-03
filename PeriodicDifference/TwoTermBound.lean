/-
# `PeriodicDifference/TwoTermBound.lean` — the interval bound for `χ_t` with roots on the unit circle

If `∏ᵢ (X − ηᵢ) = X^K + 1 − t (X^j + X^{K−j})` with every `|ηᵢ| = 1`, `0 < j`, `2j < K`,
`gcd(j, K) = 1` and `K ≠ 3j`, then `t` is real, `|t| ≤ 2` and `t ≤ √2` (`conj_bound`).

This is `lem:small-bound`, used in the proof of `thm:twoterm`: rather than locating the
admissible interval `I(k, j)` by critical-point analysis, the power sums do it.  For `j ≥ 2`,
`K (t² − 1) = p_K` is a sum of `K` unit vectors, so `t² ≤ 2`; for `j = 1`,
`t^{K−2} = p_{K−2}` and `(K−1) t + t^{K−1} = p_{K−1}` give `|t| ≤ 2` and `t ≤ 1`.
Reality: the inverses `ηᵢ⁻¹ = η̄ᵢ` are the roots of the same (palindromic) polynomial,
so `j t̄ = p̄_j = j t`.
-/
import PeriodicDifference.TwoTermNewton

namespace PeriodicDifference
namespace TwoTerm

open Polynomial Finset ComplexConjugate

variable {K j : ℕ} {η : Fin K → ℂ} {t : ℂ}

lemma eval_chiP (K j : ℕ) (t x : ℂ) :
    (chiP ℂ K j t).eval x = x ^ K + 1 - t * (x ^ j + x ^ (K - j)) := by
  simp [chiP]

/-- The inverses of the roots are the roots of the same polynomial. -/
lemma prod_inv (hprod : ∏ i, (X - C (η i)) = chiP ℂ K j t) (hj0 : 0 < j) (hjK : 2 * j < K) :
    ∏ i, (X - C (η i)⁻¹) = chiP ℂ K j t := by
  -- `∏ ηᵢ = (−1)^K`
  have h0 := congrArg (Polynomial.eval 0) hprod
  rw [eval_prod, eval_chiP] at h0
  simp only [eval_sub, eval_X, eval_C, zero_sub, Finset.prod_neg] at h0
  rw [zero_pow (by omega), zero_pow (by omega), zero_pow (by omega)] at h0
  simp only [Finset.card_univ, Fintype.card_fin, mul_zero, add_zero, sub_zero, zero_add] at h0
  have hne : ∀ i, η i ≠ 0 := by
    intro i hi
    have : ∏ i, η i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [this, mul_zero] at h0; exact zero_ne_one h0
  refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
  refine Set.Infinite.mono (s := {x : ℂ | x ≠ 0}) (fun x hx => ?_) ?_
  · simp only [Set.mem_setOf_eq] at hx ⊢
    rw [eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    have hfac : ∀ i, x - (η i)⁻¹ = (-x * (η i)⁻¹) * (x⁻¹ - η i) := by
      intro i
      have := hne i
      field_simp
      ring
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_inv_distrib]
    have h1 := congrArg (Polynomial.eval x⁻¹) hprod
    rw [eval_prod, eval_chiP] at h1
    simp only [eval_sub, eval_X, eval_C] at h1
    rw [h1, eval_chiP]
    simp only [Finset.card_univ, Fintype.card_fin]
    obtain ⟨m, rfl⟩ : ∃ m, K = m + j := ⟨K - j, by omega⟩
    rw [show m + j - j = m by omega]
    have hP : ∏ i, η i = (-1) ^ (m + j) := by
      have hsq : ((-1 : ℂ) ^ (m + j)) * (-1) ^ (m + j) = 1 := by
        rw [← mul_pow]; norm_num
      calc ∏ i, η i = ((-1) ^ (m + j) * (-1) ^ (m + j)) * ∏ i, η i := by rw [hsq, one_mul]
        _ = (-1) ^ (m + j) := by rw [mul_assoc, h0, mul_one]
    rw [hP, neg_pow]
    have hs : ((-1 : ℂ) ^ (m + j)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hcan : ∀ y : ℂ, (-1) ^ (m + j) * x ^ (m + j) * ((-1) ^ (m + j))⁻¹ * y
        = x ^ (m + j) * y := by
      intro y; field_simp
    rw [hcan]
    simp only [inv_pow]
    field_simp
    ring
  · exact (Set.finite_singleton (0 : ℂ)).infinite_compl.mono (fun x hx => hx)

lemma norm_ps_le (hη : ∀ i, ‖η i‖ = 1) (r : ℕ) : ‖ps η r‖ ≤ K := by
  unfold ps
  calc ‖∑ i, η i ^ r‖ ≤ ∑ i, ‖η i ^ r‖ := norm_sum_le _ _
    _ = K := by simp [norm_pow, hη]

lemma two_pow_ge {K : ℕ} (hK : 3 < K) : (K : ℝ) ≤ 2 ^ (K - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 4 := ⟨K - 4, by omega⟩
  have h := Nat.lt_two_pow_self (n := m)
  have : (m : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast h
  rw [show m + 4 - 2 = m + 2 by omega, pow_add]
  push_cast; nlinarith

/-- **The interval bound** (`lem:small-bound`). -/
theorem conj_bound (hprod : ∏ i, (X - C (η i)) = chiP ℂ K j t) (hη : ∀ i, ‖η i‖ = 1)
    (hj0 : 0 < j) (hjK : 2 * j < K) (hcop : Nat.Coprime j K) (h3 : K ≠ 3 * j) :
    ∃ r : ℝ, t = r ∧ |r| ≤ 2 ∧ r ≤ Real.sqrt 2 := by
  -- reality
  have hconj : ps (fun i => (η i)⁻¹) j = conj (ps η j) := by
    unfold ps
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow]
    show (η i)⁻¹ ^ j = _
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hη i]
    simp
  rw [ps_j (prod_inv hprod hj0 hjK) hj0 hjK, ps_j hprod hj0 hjK, map_mul, map_natCast] at hconj
  have hjne : (j : ℂ) ≠ 0 := by exact_mod_cast hj0.ne'
  have ht : conj t = t := (mul_left_cancel₀ hjne hconj).symm
  obtain ⟨r, rfl⟩ : ∃ r : ℝ, t = r := ⟨t.re, (Complex.conj_eq_iff_re.mp ht).symm⟩
  refine ⟨r, rfl, ?_⟩
  have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hs22 : Real.sqrt 2 ≤ 2 := by nlinarith
  rcases Nat.lt_or_ge j 2 with hj | hj
  · -- `j = 1`
    obtain rfl : j = 1 := by omega
    have hK : 3 < K := by omega
    obtain ⟨h2, h1⟩ := ps_one hprod hK
    have n2 := norm_ps_le hη (K - 2)
    have n1 := norm_ps_le hη (K - 1)
    rw [h2] at n2
    rw [h1] at n1
    have n2' : |r| ^ (K - 2) ≤ K := by
      have : ‖((r ^ (K - 2) : ℝ) : ℂ)‖ ≤ K := by push_cast; exact n2
      rwa [Complex.norm_real, Real.norm_eq_abs, abs_pow] at this
    have n1' : (K - 1 : ℕ) * r + r ^ (K - 1) ≤ K := by
      have : ‖(((K - 1 : ℕ) * r + r ^ (K - 1) : ℝ) : ℂ)‖ ≤ K := by push_cast; exact n1
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    constructor
    · by_contra hr
      push_neg at hr
      have := pow_lt_pow_left₀ hr (by norm_num) (show K - 2 ≠ 0 by omega)
      linarith [two_pow_ge hK]
    · by_contra hr
      push_neg at hr
      have hr1 : 1 < r := lt_of_le_of_lt hs2 hr
      have hp : 1 < r ^ (K - 1) := one_lt_pow₀ hr1 (by omega)
      have hK1 : ((K - 1 : ℕ) : ℝ) = K - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [hK1] at n1'
      have : ((K : ℝ) - 1) * 1 < (K - 1) * r :=
        mul_lt_mul_of_pos_left hr1 (by
          have h3K : (3 : ℝ) < K := by exact_mod_cast hK
          linarith)
      linarith
  · -- `j ≥ 2`
    have hK := ps_K_coprime hprod hj hjK hcop
    have n := norm_ps_le hη K
    rw [hK] at n
    have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have n' : |r ^ 2 - 1| ≤ 1 := by
      have : ‖((K * (r ^ 2 - 1) : ℝ) : ℂ)‖ ≤ K := by push_cast; exact n
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hK0] at this
      nlinarith
    have hsq : r ^ 2 ≤ 2 := by have := (abs_le.mp n').2; linarith
    have habs : |r| ≤ Real.sqrt 2 := Real.abs_le_sqrt hsq
    exact ⟨habs.trans hs22, (le_abs_self r).trans habs⟩

end TwoTerm
end PeriodicDifference
