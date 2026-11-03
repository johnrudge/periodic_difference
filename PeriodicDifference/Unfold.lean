/-
# `PeriodicDifference/Unfold.lean` — the unfolding route

An `(S, θ)` pair at order `K` with `d = gcd(S ∪ {K}) > 1` (the paper's `ℓ` in `lem:unfold`) is not
killed by an argument of its own: it is the `d`-fold unfolding of the pair `(S/d, θ)` at order
`K/d`, and it inherits whatever settles the lower order.  22 of the archive's 166 entries take that
route, and it is what makes "order `K` is closed" an *induction* on `K` rather than a self-contained
statement — a point worth having in Lean, since it means the orders cannot be checked independently
of one another.

The tropical form is what the certificates need, and it is clean: if every slot of
`J` is a multiple of `d` and `d ∣ K`, then a solution `x` of the order-`K/d`
equation spreads to the solution `y n = x (n / d)` of the order-`K` equation — the
`d` interleaved subsequences evolve independently, which is exactly what "unfolding"
means.  Global periodicity of the big equation then forces global periodicity of the
small one.

The period bookkeeping needs one step of care.  From `y (n + p) = y n` at `n = d·m`
one gets `x (m + p/d) = x m`, and `p/d` can be `0` when `p < d`.  That is dealt with
by first replacing `p` with `p·d`, which is legitimate because global periodicity at
`p` implies it at every multiple of `p`.
-/

import PeriodicDifference.Tropical

namespace PeriodicDifference
namespace Trop

/-! ## Periodicity passes to multiples -/

lemma periodic_mul {x : ℕ → ℝ} {p : ℕ} (h : ∀ n, x (n + p) = x n) :
    ∀ m n, x (n + p * m) = x n := by
  intro m
  induction m with
  | zero => intro n; simp
  | succ m ih =>
    intro n
    have hrw : n + p * (m + 1) = (n + p * m) + p := by ring
    rw [hrw, h, ih]

/-- Global periodicity at `p` gives it at every multiple of `p`. -/
lemma GloballyPeriodic.mul {K : ℕ} {J : List ℕ} {co : ℕ → ℝ} {p : ℕ}
    (h : GloballyPeriodic K J co p) (m : ℕ) : GloballyPeriodic K J co (p * m) :=
  fun x hx hrec n => periodic_mul (h x hx hrec) m n

/-! ## The spread of a solution

`y n = x (n / d)` holds each value of `x` for `d` consecutive steps.  Because every
slot is a multiple of `d`, the order-`K` recursion read at `y` is exactly the
order-`K/d` recursion read at `x`.
-/

section Unfold
variable {d K' : ℕ} {J' : List ℕ} {co' : ℕ → ℝ}

/-- The coefficients of the unfolded equation: slot `j'·d` carries `co' j'`. -/
def spreadCo (d : ℕ) (co' : ℕ → ℝ) : ℕ → ℝ := fun m => co' (m / d)

/-- The right-hand side is unchanged by spreading. -/
lemma rhs_spread (hd : 0 < d) (x : ℕ → ℝ) (n : ℕ) :
    rhs (J'.map (· * d)) (spreadCo d co') (fun m => x (m / d)) n
      = rhs J' co' x (n / d) := by
  rw [rhs, rhs, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun j' _ => ?_)
  simp only [Function.comp_apply, spreadCo]
  have hdiv : j' * d / d = j' := by
    rw [Nat.mul_div_cancel _ hd]
  rw [hdiv]
  by_cases hj : j' = 0
  · simp [hj]
  · have hne : j' * d ≠ 0 := Nat.mul_ne_zero hj hd.ne'
    rw [if_neg hne, if_neg hj]
    congr 2
    exact Nat.add_mul_div_right n j' hd

/-- **The spread solves the unfolded equation.** -/
lemma spread_rec (hd : 0 < d) {x : ℕ → ℝ}
    (hrec : ∀ n, x (n + K') * x n = rhs J' co' x n) (n : ℕ) :
    (fun m => x (m / d)) (n + d * K') * (fun m => x (m / d)) n
      = rhs (J'.map (· * d)) (spreadCo d co') (fun m => x (m / d)) n := by
  have hshift : (n + d * K') / d = n / d + K' := by
    rw [mul_comm d K']
    exact Nat.add_mul_div_right n K' hd
  simp only []
  rw [hshift, rhs_spread hd, hrec]

/-- **The unfolding lemma.**  If the `d`-fold unfolding is globally `p·d`-periodic
then the original equation is globally `p`-periodic.

Contrapositively — and this is the form the archive uses — if no equation with slot
list `J'` at order `K'` is globally periodic for any period, then none with slot list
`J'.map (·*d)` at order `d·K'` is either. -/
theorem unfold_globallyPeriodic (hd : 0 < d) {p : ℕ}
    (h : GloballyPeriodic (d * K') (J'.map (· * d)) (spreadCo d co') (p * d)) :
    GloballyPeriodic K' J' co' p := by
  intro x hx hrec n
  have hy := h (fun m => x (m / d)) (fun m => hx _) (spread_rec hd hrec)
  have hn := hy (n * d)
  have h1 : (n * d + p * d) / d = n + p := by
    rw [← Nat.add_mul, Nat.mul_div_cancel _ hd]
  have h2 : n * d / d = n := Nat.mul_div_cancel _ hd
  simpa [h1, h2] using hn

end Unfold

end Trop
end PeriodicDifference
