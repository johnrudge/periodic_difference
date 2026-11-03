/-
# `PeriodicDifference/TwoTermSmall.lean` — the endgame of `thm:twoterm`: small root orders

* `small_order_absurd`: if `ζ² − εζ + 1 = 0` with `ε ∈ (0, 1/2]` then `ζ^n ≠ 1` for
  `1 ≤ n ≤ 8` (the values `2cos(2πa/n)`, `n ≤ 8`, avoid `(0, 1/2]`);
* `sqrt_two_lt_two_cos`: `√2 < 2 cos(2π/n)` for `n ≥ 9`.
-/
import Mathlib

namespace PeriodicDifference
namespace TwoTerm

open Complex

/-- `ζ^m = A_m ζ + B_m` modulo `ζ² = εζ − 1`. -/
def chebA (ε : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | m + 1 => (ε * (chebA ε m).1 + (chebA ε m).2, -(chebA ε m).1)

lemma pow_eq_cheb {ε : ℝ} {ζ : ℂ} (hq : ζ ^ 2 - ε * ζ + 1 = 0) (m : ℕ) :
    ζ ^ m = (chebA ε m).1 * ζ + (chebA ε m).2 := by
  induction m with
  | zero => simp [chebA]
  | succ m ih =>
    simp only [chebA]
    push_cast
    rw [pow_succ, ih]
    linear_combination ((chebA ε m).1 : ℂ) * hq

/-- For `|ε| < 2` the roots of `ζ² − εζ + 1` are not real. -/
lemma im_ne_zero {ε : ℝ} (hε : ε ^ 2 < 4) {ζ : ℂ}
    (hq : ζ ^ 2 - ε * ζ + 1 = 0) : ζ.im ≠ 0 := by
  intro him
  have hz : ζ = (ζ.re : ℂ) := Complex.ext rfl (by simp [him])
  rw [hz] at hq
  have : (ζ.re ^ 2 - ε * ζ.re + 1 : ℝ) = 0 := by exact_mod_cast hq
  nlinarith [sq_nonneg (ζ.re - ε / 2)]

lemma small_order_absurd {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) {ζ : ℂ}
    (hq : ζ ^ 2 - ε * ζ + 1 = 0) {n : ℕ} (hn : 0 < n) (hn8 : n ≤ 8) (hpow : ζ ^ n = 1) :
    False := by
  have him := im_ne_zero (by nlinarith) hq
  rw [pow_eq_cheb hq n] at hpow
  have hI := congrArg Complex.im hpow
  have hR := congrArg Complex.re hpow
  simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, one_im, add_re,
    mul_re, sub_zero, one_re, zero_mul] at hI hR
  have hA : (chebA ε n).1 = 0 := by
    rcases mul_eq_zero.mp hI with h | h
    · exact h
    · exact absurd h him
  rw [hA, zero_mul, zero_add] at hR
  have h2 : 0 < ε ^ 2 := by positivity
  have h4 : ε ^ 2 ≤ 1 / 4 := by nlinarith
  interval_cases n <;> simp [chebA] at hA hR <;> ring_nf at hR <;>
    nlinarith [mul_pos h2 h2, mul_pos h0 h2, mul_nonneg h2.le (sub_nonneg.mpr h4),
      mul_nonneg (mul_pos h2 h2).le (sub_nonneg.mpr h4)]

lemma sqrt_two_lt_two_cos {n : ℕ} (hn : 9 ≤ n) :
    Real.sqrt 2 < 2 * Real.cos (2 * Real.pi / n) := by
  have hn' : (9 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have hlt : 2 * Real.pi / n < Real.pi / 4 := by
    rw [div_lt_div_iff₀ hpos (by norm_num)]
    nlinarith [Real.pi_pos]
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity)
    (by linarith [Real.pi_pos]) hlt
  rw [Real.cos_pi_div_four] at hc
  linarith

end TwoTerm
end PeriodicDifference
