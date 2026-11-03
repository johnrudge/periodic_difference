/-
# Order 2 of family (a): the Lyness classification

`PeriodicDifference/FamilyA.lean` does not settle family (a) in even order, the first case being
order 2.  The order-2 members of family (a) with `A₂ > 0` are

  `x_{n+2} xₙ = a₀ + a₁ x_{n+1}`,   `a₀ = A₀/B₀ ≥ 0`, `a₁ = A₂/B₀ > 0`,

and the scaling `yₙ = xₙ/a₁` turns them into the **Lyness equations**
`y_{n+2} yₙ = α + y_{n+1}` with `α = a₀/a₁²`.  This file proves the classical fact that a
Lyness equation with `α > 0` is globally periodic **only** for `α = 1`
(`Lyness.eq_sq_of_periodic`, `thm:order2`).  Together with the two known periodic cases
`α = 0` (period 6) and `α = 1` (period 5), that settles order 2 completely.

## The argument

The textbook proofs (invariant curves and rotation numbers, or degree growth of the
birational map) need machinery far beyond what is available here.  The argument used here
stays inside the closed positive quadrant: it is the periodicity of the degeneration with
leading coefficients (`Trop.tendsto_leading`, `thm:leading`) along the boundary **5-cycle**
`e = (1, 0, −1, −1, 0)` of the min-plus recursion `e_{n+2} + eₙ = min(0, e_{n+1})`.  Run the
orbit from `x₀ = δ`, `x₁ = 1`; then `xₙ δ^{−eₙ} → Cₙ > 0`, and the recursion of the `Cₙ`
along the attaining slots gives

  `C_{5m+3} C_{5m+1} = a₁ C_{5m+2}`,  `C_{5m+4} C_{5m+2} = a₁ C_{5m+3}`,  `C_{5m+6} C_{5m+4} = a₀`,

so `C_{5m+6} = α C_{5m+1}` and `C_{5m+1} = αᵐ`.  `theoremP` makes the cycle `p`-periodic, so
`5 ∣ p`, and the leading coefficients are `p`-periodic too: `α^{p/5} = 1`, i.e. `α = 1`.
-/

import PeriodicDifference.Tropical

namespace PeriodicDifference

namespace Lyness

open Filter Topology Trop

/-- The boundary 5-cycle `e = (1, 0, −1, −1, 0)`. -/
def ecyc (n : ℕ) : ℤ := [1, 0, -1, -1, 0].getI (n % 5)

lemma ecyc_add (m r : ℕ) : ecyc (5 * m + r) = ecyc r := by
  simp [ecyc, Nat.add_mod]

lemma ecyc_trop : IsTrop 2 [0, 1] ecyc := by
  intro n
  have h := Nat.mod_lt n (show 5 > 0 by norm_num)
  have e : ∀ j, ecyc (n + j) = ecyc (n % 5 + j) := fun j => by simp [ecyc, Nat.add_mod]
  have e0 : ecyc n = ecyc (n % 5) := by simp [ecyc]
  simp only [mval, slot, lmin, List.map, e, e0]
  generalize n % 5 = r at h ⊢
  interval_cases r <;> decide

/-- **Order 2 (`thm:order2`), `a₀ > 0`.**  If every positive solution of
`x_{n+2} xₙ = a₀ + a₁ x_{n+1}` is `p`-periodic for a fixed `p ≥ 1`, then `a₀ = a₁²`. -/
theorem eq_sq_of_periodic {a₀ a₁ : ℝ} (h₀ : 0 < a₀) (h₁ : 0 < a₁) {p : ℕ} (hp : 0 < p)
    (hg : GloballyPeriodic 2 [0, 1] (fun j => if j = 0 then a₀ else a₁) p) : a₀ = a₁ ^ 2 := by
  set co : ℕ → ℝ := fun j => if j = 0 then a₀ else a₁
  have hJk : ∀ j ∈ [0, 1], j ≤ 1 := by decide
  have hco : ∀ j ∈ [0, 1], 0 < co j := by simp [co, h₀, h₁]
  -- the cycle is `p`-periodic, so `p = 5m`
  have h5 : p % 5 = 0 := by
    have := theoremP (List.cons_ne_nil _ _) hJk hco hg ecyc ecyc_trop 0
    have hr := Nat.mod_lt p (show 5 > 0 by norm_num)
    rw [zero_add, ← Nat.div_add_mod p 5, ecyc_add] at this
    interval_cases hr' : p % 5 <;> simp_all [ecyc]
  obtain ⟨C, hCpos, hC1, hrec, hC⟩ :=
    tendsto_leading (co := co) (List.cons_ne_nil _ _) hJk hco ecyc_trop
  have hper := leading_periodic (List.cons_ne_nil _ _) hJk hco hg ecyc_trop hC 1
  -- the recursion of the leading coefficients at the three steps that matter
  have hr : ∀ m r, C (5 * m + r + 2) * C (5 * m + r) = leadNum [0, 1] co ecyc C (5 * m + r) :=
    fun m r => hrec _
  have hstep : ∀ m, C (5 * m + 6) = a₀ / a₁ ^ 2 * C (5 * m + 1) := by
    intro m
    have r1 := hr m 1
    have r2 := hr m 2
    have r4 := hr m 4
    simp [leadNum, mval, slot, lmin, co, add_assoc, ecyc_add] at r1 r2 r4
    simp [ecyc] at r1 r2 r4
    have h41 : C (5 * m + 4) * C (5 * m + 1) = a₁ ^ 2 := by
      have h : (C (5 * m + 4) * C (5 * m + 1) - a₁ ^ 2) * (C (5 * m + 2) * C (5 * m + 3)) = 0 := by
        linear_combination (C (5 * m + 1) * C (5 * m + 3)) * r2 + (a₁ * C (5 * m + 3)) * r1
      have := mul_pos (hCpos (5 * m + 2)) (hCpos (5 * m + 3))
      linarith [(mul_eq_zero.mp h).resolve_right this.ne']
    rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
    linear_combination C (5 * m + 1) * r4 - C (5 * m + 6) * h41
  have hpow : ∀ m, C (5 * m + 1) = (a₀ / a₁ ^ 2) ^ m := by
    intro m
    induction m with
    | zero => exact hC1 1 le_rfl
    | succ m ih => rw [pow_succ, show 5 * (m + 1) + 1 = 5 * m + 6 by ring, hstep, ih]; ring
  have hα : (a₀ / a₁ ^ 2) ^ (p / 5) = 1 := by
    rw [← hpow, ← hC1 1 le_rfl, ← hper]; congr 1; omega
  rw [pow_eq_one_iff_of_nonneg (by positivity) (by omega), div_eq_one_iff_eq (by positivity)] at hα
  exact hα

/-- **Order 2 of family (a).**  If every positive solution of
`B₀ x_{n+2} xₙ = A₀ + A₂ x_{n+1}` (with `A₀ > 0`, `A₂ > 0`, `B₀ > 0`) is
`p`-periodic for some `p ≥ 1`, then `A₀ B₀ = A₂²` — i.e. the equation is
Lyness' equation up to scaling. -/
theorem order2_classification {A0 A2 B0 : ℝ} (hA0 : 0 < A0) (hA2 : 0 < A2) (hB0 : 0 < B0)
    {p : ℕ} (hp : 0 < p)
    (hper : ∀ x : ℕ → ℝ, (∀ n, 0 < x n) →
      (∀ n, B0 * x (n + 2) * x n = A0 + A2 * x (n + 1)) → ∀ n, x (n + p) = x n) :
    A0 * B0 = A2 ^ 2 := by
  have h := eq_sq_of_periodic (div_pos hA0 hB0) (div_pos hA2 hB0) hp fun x hx hrec =>
    hper x hx fun n => by
      have := hrec n
      simp only [rhs, List.map, List.sum_cons, List.sum_nil] at this
      norm_num at this
      field_simp at this
      linarith
  field_simp at h
  linarith

end Lyness

end PeriodicDifference
