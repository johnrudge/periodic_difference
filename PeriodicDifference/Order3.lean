/-
# Order 3 of family (a)

Palindromy (`PeriodicDifference/Palindromic.lean`) forces `A₂ = A₃` for a periodic order-3 member
of family (a), which is then

  `x_{n+3} xₙ = a₀ + a₁ (x_{n+1} + x_{n+2})`,   `a₀ = A₀/B₁ ≥ 0`, `a₁ = A₂/B₁ > 0`;

the scaling `yₙ = xₙ/a₁` turns it into `y_{n+3} yₙ = α + y_{n+1} + y_{n+2}` with
`α = a₀/a₁²`.  This file proves that for `a₀ > 0` global periodicity forces `α = 1`
(`Lyness3.eq_sq_of_periodic`, `thm:order3`), i.e. the equation is Gasull's `8`-periodic
example `x_{n+3} = (1 + x_{n+1} + x_{n+2})/xₙ` up to scaling.

## The argument

The one of order 2 (`PeriodicDifference/Order2.lean`): the periodicity of the degeneration with leading
coefficients (`Trop.tendsto_leading`, `thm:leading`) along the boundary **8-cycle**

  `e = (1, 0, −1, −2, −2, −1, 0, 1)`

of `e_{n+3} + eₙ = min(0, e_{n+1}, e_{n+2})`, i.e. the orbit from
`x₀ = δ`, `x₁ = 1`, `x₂ = 1/δ`.  Along the attaining slots,

  `C_{8m+4} C_{8m+1} = a₁ C_{8m+3}`,  `C_{8m+6} C_{8m+3} = a₁ C_{8m+4}`,  `C_{8m+9} C_{8m+6} = a₀`,

so `C_{8m+9} = α C_{8m+1}` and `C_{8m+1} = αᵐ`; `theoremP` gives `8 ∣ p` and makes the
leading coefficients `p`-periodic, so `α^{p/8} = 1`.

## What is left at order 3

Only `a₀ = 0`, i.e. `x_{n+3} xₙ = x_{n+1} + x_{n+2}` up to scaling.  That case is settled in
`PeriodicDifference/Order3Zero.lean` by the two-term linearisation at the equilibrium, whose
characteristic polynomial has a root that is not a root of unity, so order 3 is complete.
-/

import PeriodicDifference.Tropical

namespace PeriodicDifference

namespace Lyness3

open Filter Topology Trop

/-- The boundary 8-cycle `e = (1, 0, −1, −2, −2, −1, 0, 1)`. -/
def ecyc (n : ℕ) : ℤ := [1, 0, -1, -2, -2, -1, 0, 1].getI (n % 8)

lemma ecyc_add (m r : ℕ) : ecyc (8 * m + r) = ecyc r := by
  simp [ecyc, Nat.add_mod]

lemma ecyc_trop : IsTrop 3 [0, 1, 2] ecyc := by
  intro n
  have h := Nat.mod_lt n (show 8 > 0 by norm_num)
  have e : ∀ j, ecyc (n + j) = ecyc (n % 8 + j) := fun j => by simp [ecyc, Nat.add_mod]
  have e0 : ecyc n = ecyc (n % 8) := by simp [ecyc]
  simp only [mval, slot, lmin, List.map, e, e0]
  generalize n % 8 = r at h ⊢
  interval_cases r <;> decide

/-- **Order 3 (`thm:order3`), `a₀ > 0`.**  If every positive solution of
`x_{n+3} xₙ = a₀ + a₁ (x_{n+1} + x_{n+2})` is `p`-periodic for a fixed `p ≥ 1`, then
`a₀ = a₁²`. -/
theorem eq_sq_of_periodic {a₀ a₁ : ℝ} (h₀ : 0 < a₀) (h₁ : 0 < a₁) {p : ℕ} (hp : 0 < p)
    (hg : GloballyPeriodic 3 [0, 1, 2] (fun j => if j = 0 then a₀ else a₁) p) :
    a₀ = a₁ ^ 2 := by
  set co : ℕ → ℝ := fun j => if j = 0 then a₀ else a₁
  have hJk : ∀ j ∈ [0, 1, 2], j ≤ 2 := by decide
  have hco : ∀ j ∈ [0, 1, 2], 0 < co j := by simp [co, h₀, h₁]
  -- the cycle is `p`-periodic, so `p = 8m`
  have h8 : p % 8 = 0 := by
    have h0 := theoremP (List.cons_ne_nil _ _) hJk hco hg ecyc ecyc_trop 0
    have h1 := theoremP (List.cons_ne_nil _ _) hJk hco hg ecyc ecyc_trop 1
    have hr := Nat.mod_lt p (show 8 > 0 by norm_num)
    rw [zero_add, ← Nat.div_add_mod p 8, ecyc_add] at h0
    rw [← Nat.div_add_mod p 8, add_left_comm, ecyc_add] at h1
    interval_cases hr' : p % 8 <;> simp_all [ecyc]
  obtain ⟨C, hCpos, hC1, hrec, hC⟩ :=
    tendsto_leading (co := co) (List.cons_ne_nil _ _) hJk hco ecyc_trop
  have hper := leading_periodic (List.cons_ne_nil _ _) hJk hco hg ecyc_trop hC 1
  -- the recursion of the leading coefficients at the three steps that matter
  have hstep : ∀ m, C (8 * m + 9) = a₀ / a₁ ^ 2 * C (8 * m + 1) := by
    intro m
    have r1 := hrec (8 * m + 1)
    have r3 := hrec (8 * m + 3)
    have r6 := hrec (8 * m + 6)
    simp [leadNum, mval, slot, lmin, co, add_assoc, ecyc_add] at r1 r3 r6
    simp [ecyc] at r1 r3 r6
    have h61 : C (8 * m + 6) * C (8 * m + 1) = a₁ ^ 2 := by
      have h : (C (8 * m + 6) * C (8 * m + 1) - a₁ ^ 2) * (C (8 * m + 3) * C (8 * m + 4)) = 0 := by
        linear_combination (C (8 * m + 1) * C (8 * m + 4)) * r3 + (a₁ * C (8 * m + 4)) * r1
      have := mul_pos (hCpos (8 * m + 3)) (hCpos (8 * m + 4))
      linarith [(mul_eq_zero.mp h).resolve_right this.ne']
    rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
    linear_combination C (8 * m + 1) * r6 - C (8 * m + 9) * h61
  have hpow : ∀ m, C (8 * m + 1) = (a₀ / a₁ ^ 2) ^ m := by
    intro m
    induction m with
    | zero => exact hC1 1 (by norm_num)
    | succ m ih => rw [pow_succ, show 8 * (m + 1) + 1 = 8 * m + 9 by ring, hstep, ih]; ring
  have hα : (a₀ / a₁ ^ 2) ^ (p / 8) = 1 := by
    rw [← hpow, ← hC1 1 (by norm_num), ← hper]; congr 1; omega
  rw [pow_eq_one_iff_of_nonneg (by positivity) (by omega), div_eq_one_iff_eq (by positivity)] at hα
  exact hα

/-- **Order 3 of family (a).**  Suppose every positive solution of
`B₁ x_{n+3} xₙ = A₀ + A₂ x_{n+1} + A₃ x_{n+2}` is `p`-periodic for some `p ≥ 1`,
with `A₀ > 0`, `A₂ > 0` and `A₂ = A₃` (the latter being forced by palindromy).
Then `A₀ B₁ = A₂²` — i.e. the equation is Gasull's `8`-periodic
`x_{n+3} = (1 + x_{n+1} + x_{n+2})/xₙ` up to scaling. -/
theorem order3_classification {A0 A2 B1 : ℝ} (hA0 : 0 < A0) (hA2 : 0 < A2) (hB1 : 0 < B1)
    {p : ℕ} (hp : 0 < p)
    (hper : ∀ x : ℕ → ℝ, (∀ n, 0 < x n) →
      (∀ n, B1 * x (n + 3) * x n = A0 + A2 * x (n + 1) + A2 * x (n + 2)) →
      ∀ n, x (n + p) = x n) :
    A0 * B1 = A2 ^ 2 := by
  have h := eq_sq_of_periodic (div_pos hA0 hB1) (div_pos hA2 hB1) hp fun x hx hrec =>
    hper x hx fun n => by
      have := hrec n
      simp only [rhs, List.map, List.sum_cons, List.sum_nil] at this
      norm_num at this
      field_simp at this
      linarith
  field_simp at h
  linarith

end Lyness3

end PeriodicDifference
