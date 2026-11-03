/-
# Order 3 of family (a): the remaining case `α = 0`

`PeriodicDifference/Order3.lean` settles `x_{n+3} xₙ = α + x_{n+1} + x_{n+2}` for `α > 0`.
This file disposes of the one remaining member of the order-3 family,

  `x_{n+3} xₙ = c (x_{n+1} + x_{n+2})`,

which is *not* periodic.  (Its boundary cycle has length 9 rather than 8, so the
degeneration argument of `Order3.lean` does not apply verbatim.)

## The argument

This is the two-term support `{1, 2}` at `K = 3` with no constant term, so the linearisation
of `PeriodicDifference/TwoTermLinear.lean` applies: at the equilibrium `x* = 2c` the coefficient is
`ε = c / x* = 1/2`, and global periodicity makes every root of
`χ(z) = z³ + 1 − ½ (z + z²) = (z + 1)(z² − (3/2) z + 1)` a root of unity
(`TwoTerm.root_pow_eq_one`).  A root `ζ` of `z² − (3/2) z + 1` is not real, and
`ζ^m = A_m ζ + B_m` (`TwoTerm.pow_eq_cheb`) with `2^{m−1} A_m` an odd integer for `m ≥ 1`
(`cheb_odd`); so `ζ^m ≠ 1`.  (Equivalently: `3/2 = 2cos θ` is not an algebraic integer, so `θ`
is not a rational angle.)
-/

import PeriodicDifference.TwoTermLinear
import PeriodicDifference.TwoTermSmall

namespace PeriodicDifference

namespace Order3Zero

open Trop Problem11 TwoTerm

/-- `2^m A_{m+1}` is an odd integer and `2^m B_{m+1}` an even one, for the Chebyshev
coefficients `ζ^m = A_m ζ + B_m` at `ε = 3/2`. -/
lemma cheb_odd : ∀ m : ℕ, ∃ s t : ℤ, Odd s ∧ (2 : ℝ) ^ m * (chebA (3 / 2) (m + 1)).1 = s ∧
    (2 : ℝ) ^ m * (chebA (3 / 2) (m + 1)).2 = 2 * t := by
  intro m
  induction m with
  | zero => exact ⟨1, 0, odd_one, by norm_num [chebA], by norm_num [chebA]⟩
  | succ m ih =>
    obtain ⟨s, t, hs, h1, h2⟩ := ih
    refine ⟨3 * s + 4 * t, -s, by
      obtain ⟨u, rfl⟩ := hs; exact ⟨3 * u + 2 * t + 1, by ring⟩, ?_, ?_⟩
    · rw [show m + 1 + 1 = (m + 1) + 1 from rfl, chebA]
      push_cast
      linear_combination 3 * h1 + 2 * h2
    · rw [show m + 1 + 1 = (m + 1) + 1 from rfl, chebA]
      push_cast
      linear_combination -2 * h1

/-- **`α = 0` is not periodic**, in the sequence form: an admissible equation of order `3`
with support `{1, 2}` and no constant term is never globally periodic. -/
theorem not_periodic_of_admissible {J : List ℕ} {co : ℕ → ℝ} (h : Admissible 3 J co)
    (hs : supp J = {1, 2}) (h0 : 0 ∉ J) {p : ℕ} (hp : 0 < p) (hg : GloballyPeriodic 3 J co p) :
    False := by
  have h1 : 1 ∈ J := (mem_supp.mp (hs ▸ (by simp : (1 : ℕ) ∈ ({1, 2} : Finset ℕ)))).2
  have hc := h.pos 1 h1
  obtain ⟨ε, hεdef, -, -, hlin⟩ := linear_periodic h hs (j := 1) one_pos (by norm_num) hg
  -- `x* = 2c`, so `ε = 1/2`
  have hε : ε = 1 / 2 := by
    rw [hεdef, cJ_of_not_mem h0, xs, add_zero, Real.sqrt_sq hc.le]
    field_simp; ring
  subst hε
  -- a root of `z² − (3/2) z + 1`
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, ζ ^ 2 - ((3 / 2 : ℝ) : ℂ) * ζ + 1 = 0 := by
    obtain ⟨z, hz⟩ := Complex.exists_root (f := Polynomial.C 1 * Polynomial.X ^ 2 +
      Polynomial.C (-((3 / 2 : ℝ) : ℂ)) * Polynomial.X + Polynomial.C 1)
      (by rw [Polynomial.degree_quadratic one_ne_zero]; norm_num)
    refine ⟨z, ?_⟩
    have := hz.eq_zero
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] at this
    linear_combination this
  have hζc : ζ ^ 2 - 3 / 2 * ζ + 1 = 0 := by have := hζ; push_cast at this; exact this
  have hpow := root_pow_eq_one hlin (z := ζ) (by
    unfold chi
    rw [show (3 : ℕ) - 1 = 2 from rfl]
    push_cast
    linear_combination (ζ + 1) * hζc)
  -- `ζ` is not real, and `ζ^p = A_p ζ + B_p` with `A_p ≠ 0`
  have him := im_ne_zero (by norm_num) hζ
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [pow_eq_cheb hζ] at hpow
  have hI := congrArg Complex.im hpow
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.one_im] at hI
  obtain ⟨s, t, ⟨u, rfl⟩, hA, -⟩ := cheb_odd q
  have hA0 : (chebA (3 / 2) (q + 1)).1 = 0 := by
    rcases mul_eq_zero.mp hI with h' | h'
    · exact h'
    · exact absurd h' him
  rw [hA0, mul_zero] at hA
  have : (2 * u + 1 : ℤ) = 0 := by exact_mod_cast hA.symm
  omega

/-- The same in the scaled form of family (a): `B₁ x_{n+3} xₙ = A₂ x_{n+1} + A₂ x_{n+2}`
(order 3 with `A₀ = 0`) is never globally periodic. -/
theorem scaled_not_periodic {A2 B1 : ℝ} (hA2 : 0 < A2) (hB1 : 0 < B1) {p : ℕ} (hp : 0 < p)
    (hper : ∀ x : ℕ → ℝ, (∀ n, 0 < x n) →
      (∀ n, B1 * x (n + 3) * x n = A2 * x (n + 1) + A2 * x (n + 2)) → ∀ n, x (n + p) = x n) :
    False := by
  have hc : 0 < A2 / B1 := div_pos hA2 hB1
  have hadm : Admissible 3 [1, 2] (fun _ => A2 / B1) :=
    { K_pos := by norm_num
      nodup := by decide
      lt := by decide
      pos := fun _ _ => hc
      pal := by decide
      copal := fun _ _ _ => rfl }
  refine not_periodic_of_admissible hadm (by decide) (by decide) hp fun x hx hrec => ?_
  refine hper x hx fun n => ?_
  have := hrec n
  simp only [rhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_ne_zero,
    OfNat.ofNat_ne_zero, if_false, add_zero] at this
  rw [mul_assoc, this]
  field_simp

end Order3Zero

end PeriodicDifference
