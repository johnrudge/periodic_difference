/-
# Killing the last branch of `Eqn.trichotomy`

`PeriodicDifference/GeneralK.lean` reduces a `p`-periodic equation of Gasull's family to three
shapes.  This file eliminates the third one,

  (b⋆)  `B 0 = 0`, `a = 0`, `A j = 0` for `j ≠ 0`, `∑_{j≠0} B j > 0`, `b < A 0`,

i.e. `x_{n+k+1} = A₁ xₙ / (b + Σ_{j≥1} B_j x_{n+j})` with `A₁ > b ≥ 0`, leaving

  **every `p`-periodic equation of the family is either `x_{n+k+1} = xₙ`
  or of the reciprocal type `x_{n+k+1} = (a + Σ_{j≥1} A_j x_{n+j}) / (B₀ xₙ)`.**

## The argument, and why it needs no derivatives

Morally this is "linearise at the interior fixed point `P = (x*, …, x*)` and
observe that the characteristic polynomial has a real root in `(0,1)`, which
contradicts `(DF)^p = I`".  Formalising that literally would need `fderiv`, the
chain rule, companion matrices and eigenvalues.

It is avoidable.  In branch (b⋆) the numerator is just `A 0 * u 0`, so with
`Θ w = Σ_{j≥1} B_j w_j` and `b + (Σ_{j≥1} B_j) * x* = A 0` one gets the *exact*
algebraic identity (no limits, no error terms)

  `F (P + ε • w) = P + ε • G ε w`,   `G ε w = (w₁, …, w_k, (A₀ w₀ - x* Θw)/(A₀ + ε Θw))`.

So the rescaled orbit `Ψ m ε` defined by `Ψ 0 ε = v`, `Ψ (m+1) ε = G ε (Ψ m ε)`
satisfies `F^[m] (P + ε • v) = P + ε • Ψ m ε` for every `ε > 0`, while `G 0` is
*linear* — it is the derivative, obtained for free.  Choosing `v i = λ ^ i` with
`λ ∈ (0,1)` a root of `λ^{k+1} + Σ_j d_j λ^{j+1} = 1` (which exists by the
intermediate value theorem, since the left side is `0` at `λ = 0` and `1 + σ > 1`
at `λ = 1`) makes `v` an eigenvector: `Ψ m 0 = λ^m • v`.

Periodicity forces `Ψ p ε = v` for every `ε > 0`; `Ψ p` is continuous at `0`;
hence `λ^p • v = v`, and reading off the `0`-th coordinate, `λ^p = 1` — impossible
for `λ ∈ (0,1)` and `p ≥ 1`.
-/

import PeriodicDifference.GeneralK

namespace PeriodicDifference

open Finset Filter Topology

variable {k : ℕ}

namespace Eqn

/-- The hypotheses of the third branch of `Eqn.trichotomy`. -/
structure Bstar (E : Eqn k) : Prop where
  B0 : E.B 0 = 0
  a0 : E.a = 0
  Asucc : ∀ j : Fin k, E.A j.succ = 0
  Spos : 0 < ∑ j : Fin k, E.B j.succ
  ab : E.b < E.A 0

/-- `Θ w = Σ_{j ≥ 1} B_j w_j`, the part of the denominator that involves the
later coordinates. -/
def Theta (E : Eqn k) (w : Fin (k + 1) → ℝ) : ℝ := ∑ j : Fin k, E.B j.succ * w j.succ

/-- The interior equilibrium `x* = (A₀ - b) / Σ_{j ≥ 1} B_j`. -/
noncomputable def xstar (E : Eqn k) : ℝ := (E.A 0 - E.b) / (∑ j : Fin k, E.B j.succ)

/-- The rescaled state map: `F (P + ε • w) = P + ε • G ε w`. -/
noncomputable def Gm (E : Eqn k) (ε : ℝ) (w : Fin (k + 1) → ℝ) : Fin (k + 1) → ℝ :=
  Fin.snoc (Fin.tail w) ((E.A 0 * w 0 - E.xstar * E.Theta w) / (E.A 0 + ε * E.Theta w))

/-- The rescaled orbit through `v i = λ ^ i`. -/
noncomputable def Psi (E : Eqn k) (lam ε : ℝ) : ℕ → (Fin (k + 1) → ℝ)
  | 0 => fun i => lam ^ (i : ℕ)
  | (m + 1) => E.Gm ε (E.Psi lam ε m)

/-! ### A helper: continuity of a finite sum at a point -/

/-! ### Elementary consequences of `Bstar` -/

variable {E : Eqn k}

lemma Psi_succ (E : Eqn k) (lam ε : ℝ) (m : ℕ) :
    E.Psi lam ε (m + 1) = E.Gm ε (E.Psi lam ε m) := rfl

lemma Psi_zero_eq (E : Eqn k) (lam ε : ℝ) :
    E.Psi lam ε 0 = fun i : Fin (k + 1) => lam ^ (i : ℕ) := rfl

lemma Bstar.A0_pos (h : Bstar E) : 0 < E.A 0 := lt_of_le_of_lt E.b_nonneg h.ab

lemma Bstar.xstar_pos (h : Bstar E) : 0 < E.xstar :=
  div_pos (by linarith [h.ab]) h.Spos

/-- The equilibrium equation `b + (Σ_{j≥1} B_j) * x* = A₀`. -/
lemma Bstar.key (h : Bstar E) : E.b + (∑ j : Fin k, E.B j.succ) * E.xstar = E.A 0 := by
  rw [xstar, mul_div_cancel₀ _ h.Spos.ne']
  ring

lemma Bstar.num_eq (h : Bstar E) (u : Fin (k + 1) → ℝ) : E.num u = E.A 0 * u 0 := by
  simp only [num, Fin.sum_univ_succ, h.a0, h.Asucc, zero_mul, zero_add,
    Finset.sum_const_zero, add_zero]

lemma Bstar.den_eq (h : Bstar E) (u : Fin (k + 1) → ℝ) : E.den u = E.b + E.Theta u := by
  simp only [den, Fin.sum_univ_succ, h.B0, zero_mul, zero_add, Theta]

/-- `Θ` of a shifted state. -/
lemma Theta_shift (E : Eqn k) (c ε : ℝ) (w : Fin (k + 1) → ℝ) :
    E.Theta (fun i => c + ε * w i) = (∑ j : Fin k, E.B j.succ) * c + ε * E.Theta w := by
  simp only [Theta, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The denominator at a shifted state is `A₀ + ε Θw`. -/
lemma Bstar.den_shift (h : Bstar E) (ε : ℝ) (w : Fin (k + 1) → ℝ) :
    E.den (fun i => E.xstar + ε * w i) = E.A 0 + ε * E.Theta w := by
  rw [h.den_eq, Theta_shift]
  linarith [h.key]

/-! ### The exact rescaling identity -/

/-- **The key identity.** `F (P + ε • w) = P + ε • G ε w`, exactly. -/
lemma Bstar.F_shift (h : Bstar E) (ε : ℝ) (w : Fin (k + 1) → ℝ)
    (hpos : Pos (fun i : Fin (k + 1) => E.xstar + ε * w i)) :
    E.F (fun i => E.xstar + ε * w i) = fun i => E.xstar + ε * (E.Gm ε w) i := by
  have hden : E.den (fun i => E.xstar + ε * w i) = E.A 0 + ε * E.Theta w := h.den_shift ε w
  have hd0 : E.A 0 + ε * E.Theta w ≠ 0 := by
    rw [← hden]; exact (E.den_pos hpos).ne'
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [F, Fin.snoc_last, Gm, g]
    rw [h.num_eq, hden]
    field_simp
    ring
  · intro j
    simp [F, Gm, Fin.tail]

/-- Iterating the identity. -/
lemma Bstar.F_iterate_shift (h : Bstar E) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam) :
    ∀ m, E.F^[m] (fun i : Fin (k + 1) => E.xstar + ε * lam ^ (i : ℕ))
        = fun i => E.xstar + ε * (E.Psi lam ε m) i := by
  have hv : Pos (fun i : Fin (k + 1) => E.xstar + ε * lam ^ (i : ℕ)) := by
    intro i
    have : 0 < ε * lam ^ (i : ℕ) := mul_pos hε (pow_pos hlam _)
    linarith [h.xstar_pos]
  intro m
  induction m with
  | zero => simp [Psi_zero_eq]
  | succ m ih =>
    have hposm : Pos (E.F^[m] (fun i : Fin (k + 1) => E.xstar + ε * lam ^ (i : ℕ))) :=
      E.F_iterate_pos hv m
    rw [ih] at hposm
    rw [Function.iterate_succ_apply', ih, h.F_shift ε _ hposm, Psi_succ]

/-! ### `G 0` is linear and `v` is an eigenvector -/

/-- `d j = B_{j+1} x* / A₀`, the coefficients of the characteristic polynomial. -/
noncomputable def dcoef (E : Eqn k) (j : Fin k) : ℝ := E.B j.succ * E.xstar / E.A 0

/-- The characteristic polynomial `λ ↦ λ^{k+1} + Σ_j d_j λ^{j+1} - 1`. -/
noncomputable def charPoly (E : Eqn k) (x : ℝ) : ℝ :=
  x ^ (k + 1) + (∑ j : Fin k, E.dcoef j * x ^ ((j : ℕ) + 1)) - 1

lemma charPoly_continuous (E : Eqn k) : Continuous E.charPoly := by
  unfold charPoly
  fun_prop

lemma charPoly_zero_eq (E : Eqn k) : E.charPoly 0 = -1 := by
  simp [charPoly]

lemma Bstar.charPoly_one_pos (h : Bstar E) : 0 < E.charPoly 1 := by
  have h1 : E.charPoly 1 = ∑ j : Fin k, E.dcoef j := by simp [charPoly]
  have h2 : ∑ j : Fin k, E.dcoef j = (∑ j : Fin k, E.B j.succ) * E.xstar / E.A 0 := by
    simp only [dcoef, ← Finset.sum_div, ← Finset.sum_mul]
  rw [h1, h2]
  exact div_pos (mul_pos h.Spos h.xstar_pos) h.A0_pos

/-- The characteristic polynomial has a root in `(0,1)`: it is `-1` at `0` and
positive at `1`. -/
lemma Bstar.exists_root (h : Bstar E) :
    ∃ lam : ℝ, lam ∈ Set.Ioo (0:ℝ) 1 ∧ E.charPoly lam = 0 := by
  have hsub := intermediate_value_Ioo (le_of_lt zero_lt_one)
    (E.charPoly_continuous.continuousOn (s := Set.Icc (0:ℝ) 1))
  have hmem : (0:ℝ) ∈ Set.Ioo (E.charPoly 0) (E.charPoly 1) := by
    rw [E.charPoly_zero_eq]
    exact ⟨by norm_num, h.charPoly_one_pos⟩
  obtain ⟨lam, hlam, hval⟩ := hsub hmem
  exact ⟨lam, hlam, hval⟩

/-- With `λ` a root, `G 0` scales the geometric vector `v i = λ ^ i` by `λ`:
`v` is an eigenvector of the linearisation. -/
lemma Bstar.Gm_zero_geom (h : Bstar E) {lam : ℝ} (hroot : E.charPoly lam = 0) (c : ℝ) :
    E.Gm 0 (fun i : Fin (k + 1) => c * lam ^ (i : ℕ))
      = fun i : Fin (k + 1) => (c * lam) * lam ^ (i : ℕ) := by
  have hA0 := h.A0_pos
  have hTheta : E.Theta (fun i : Fin (k + 1) => c * lam ^ (i : ℕ))
      = c * ∑ j : Fin k, E.B j.succ * lam ^ ((j : ℕ) + 1) := by
    simp only [Theta, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.val_succ]
    ring
  have hchar : (∑ j : Fin k, E.B j.succ * lam ^ ((j : ℕ) + 1)) * E.xstar
      = E.A 0 * (1 - lam ^ (k + 1)) := by
    have hd : (∑ j : Fin k, E.dcoef j * lam ^ ((j : ℕ) + 1)) * E.A 0
        = (∑ j : Fin k, E.B j.succ * lam ^ ((j : ℕ) + 1)) * E.xstar := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [dcoef]
      field_simp
    have hr : lam ^ (k + 1) + (∑ j : Fin k, E.dcoef j * lam ^ ((j : ℕ) + 1)) - 1 = 0 := hroot
    have hmul := congrArg (fun x : ℝ => x * E.A 0) hr
    simp only [add_mul, sub_mul, zero_mul, one_mul] at hmul
    rw [hd] at hmul
    linear_combination hmul
  funext i
  refine Fin.lastCases ?_ ?_ i
  · have hw0 : (fun i : Fin (k + 1) => c * lam ^ (i : ℕ)) 0 = c := by simp
    simp only [Gm, Fin.snoc_last, hTheta, hw0, Fin.val_last]
    rw [show E.A 0 + 0 * (c * ∑ j : Fin k, E.B j.succ * lam ^ ((j : ℕ) + 1)) = E.A 0 from by ring,
      div_eq_iff hA0.ne']
    linear_combination (-c) * hchar
  · intro j
    simp only [Gm, Fin.snoc_castSucc, Fin.tail, Fin.val_succ, Fin.val_castSucc]
    ring

/-- Hence the whole rescaled orbit at `ε = 0` is geometric. -/
lemma Bstar.Psi_geom (h : Bstar E) {lam : ℝ} (hroot : E.charPoly lam = 0) :
    ∀ m, E.Psi lam 0 m = fun i : Fin (k + 1) => lam ^ m * lam ^ (i : ℕ) := by
  intro m
  induction m with
  | zero => funext i; simp [Psi_zero_eq]
  | succ m ih =>
    rw [Psi_succ, ih, h.Gm_zero_geom hroot]
    funext i
    ring

/-! ### Continuity in `ε` at `ε = 0` -/

lemma Bstar.Psi_continuousAt (h : Bstar E) (lam : ℝ) :
    ∀ m, ∀ i, ContinuousAt (fun ε => E.Psi lam ε m i) 0 := by
  intro m
  induction m with
  | zero => intro i; simp only [Psi_zero_eq]; exact continuousAt_const
  | succ m ih =>
    have hTheta : ContinuousAt (fun ε => E.Theta (E.Psi lam ε m)) 0 := by
      simp only [Theta]
      exact tendsto_finset_sum _ fun j _ => continuousAt_const.mul (ih j.succ)
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simp only [Psi_succ, Gm, Fin.snoc_last]
      refine ContinuousAt.div ?_ ?_ ?_
      · exact (continuousAt_const.mul (ih 0)).sub (continuousAt_const.mul hTheta)
      · exact continuousAt_const.add (continuousAt_id.mul hTheta)
      · simpa using h.A0_pos.ne'
    · intro j
      simp only [Psi_succ, Gm, Fin.snoc_castSucc, Fin.tail]
      exact ih j.succ

/-! ### The contradiction -/

/-- **Branch (b⋆) is impossible.** -/
theorem Bstar.not_periodic (h : Bstar E) {p : ℕ} (hp : 0 < p)
    (hper : ∀ u, Pos u → E.F^[p] u = u) : False := by
  obtain ⟨lam, ⟨hlam0, hlam1⟩, hroot⟩ := h.exists_root
  -- periodicity pins the rescaled orbit back to `v`, for every `ε > 0`
  have hfix : ∀ ε : ℝ, 0 < ε → E.Psi lam ε p 0 = 1 := by
    intro ε hε
    have hv : Pos (fun i : Fin (k + 1) => E.xstar + ε * lam ^ (i : ℕ)) := by
      intro i
      have : 0 < ε * lam ^ (i : ℕ) := mul_pos hε (pow_pos hlam0 _)
      linarith [h.xstar_pos]
    have h1 := h.F_iterate_shift hε hlam0 p
    rw [hper _ hv] at h1
    have h2 := congrFun h1 0
    simp only [Fin.val_zero, pow_zero, mul_one] at h2
    have h3 : ε * E.Psi lam ε p 0 = ε * 1 := by linarith
    exact mul_left_cancel₀ hε.ne' h3
  -- continuity at `0` transports this to `ε = 0`
  have hcont := h.Psi_continuousAt lam p 0
  have hlim1 : Tendsto (fun ε => E.Psi lam ε p 0) (𝓝[>] (0:ℝ)) (𝓝 (E.Psi lam 0 p 0)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun ε => E.Psi lam ε p 0) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hfix ε hε).symm
  have heq : E.Psi lam 0 p 0 = 1 := tendsto_nhds_unique hlim1 hlim2
  -- but at `ε = 0` the orbit is geometric, so this says `λ ^ p = 1`
  rw [h.Psi_geom hroot p] at heq
  simp only [Fin.val_zero, pow_zero, mul_one] at heq
  have : lam ^ p < 1 := pow_lt_one₀ hlam0.le hlam1 hp.ne'
  linarith

/-! ### The complete classification -/

/-- **Full reduction of Gasull's Problem 11.**  Every `p`-periodic equation of the
family is either of the reciprocal type
`x_{n+k+1} = (a + Σ_{j≠0} A_j x_{n+j}) / (B₀ xₙ)`, or is literally `x_{n+k+1} = xₙ`. -/
theorem classification (E : Eqn k) {p : ℕ} (hp : 0 < p)
    (hper : ∀ u, Pos u → E.F^[p] u = u) :
    (E.A 0 = 0 ∧ E.b = 0 ∧ ∀ j : Fin k, E.B j.succ = 0) ∨
    (E.B 0 = 0 ∧ E.a = 0 ∧ (∀ j : Fin k, E.A j.succ = 0) ∧
      (∀ j : Fin k, E.B j.succ = 0) ∧ E.A 0 = E.b) := by
  rcases E.trichotomy hp hper with h | h | ⟨hB0, ha, hA, hS, hab⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (Bstar.not_periodic ⟨hB0, ha, hA, hS, hab⟩ hp hper).elim


end Eqn

end PeriodicDifference
