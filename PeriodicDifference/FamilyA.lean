/-
# Family (a): the hard core of Gasull's Problem 11

`PeriodicDifference/KillBStar.lean` reduces every `p`-periodic equation of Gasull's family to
`x_{n+k+1} = xₙ` or to the *reciprocal family*

  (a)  `B₀ * x_{n+k+1} * xₙ = a + Σ_{j≥1} A_j x_{n+j}`,  all coefficients `≥ 0`,
       `B₀ > 0`, `a + Σ_{j≥1} A_j > 0`.

This is where the substance of the problem lives: it contains the four nontrivial
known periodic equations
`x_{n+1} = 1/xₙ`, `x_{n+2} = x_{n+1}/xₙ`, `x_{n+2} = (1+x_{n+1})/xₙ`,
`x_{n+3} = (1+x_{n+1}+x_{n+2})/xₙ`, and all their unfoldings.

## What is proved here

The engine of `KillBStar` generalises.  Family (a) always has an interior
equilibrium `x*` (the positive root of `B₀ x² = a + σ x`, `σ = Σ_{j≥1} A_j`), and
the same *exact* rescaling identity holds:

  `F (P + ε • w) = P + ε • G ε w`,   `G ε w = (w₁,…,w_k, (Θw - B₀ x* w₀)/(B₀(x* + ε w₀)))`.

Hence (`Astar.linear_periodic`) the linearisation `C = G 0` satisfies `C^[p] = id`.
In companion form its coefficients are `e_j = A_{j+1}/(B₀ x*)` (`ecoef`);
`PeriodicDifference/Palindromic.lean` reads palindromy of the support off this, and
`PeriodicDifference/TwoTermLinear.lean` reruns the argument in sequence form for two-term supports.
(Theorem E — real roots of the characteristic polynomial are `±1`, and the alternating
balance at odd order — was proved here earlier; the proof of Problem 11 does not need it.)
-/

import PeriodicDifference.GeneralK

namespace PeriodicDifference

open Finset Filter Topology

variable {k : ℕ}

namespace Eqn

/-- The hypotheses of branch (a) of `Eqn.classification`. -/
structure Astar (E : Eqn k) : Prop where
  A0 : E.A 0 = 0
  b0 : E.b = 0
  Bsucc : ∀ j : Fin k, E.B j.succ = 0

/-- `σ = Σ_{j ≥ 1} A_j`. -/
def sig (E : Eqn k) : ℝ := ∑ j : Fin k, E.A j.succ

/-- `Θ w = Σ_{j ≥ 1} A_j w_j`. -/
def ATheta (E : Eqn k) (w : Fin (k + 1) → ℝ) : ℝ := ∑ j : Fin k, E.A j.succ * w j.succ

/-- The interior equilibrium: the positive root of `B₀ x² = a + σ x`. -/
noncomputable def astar (E : Eqn k) : ℝ :=
  (E.sig + Real.sqrt (E.sig ^ 2 + 4 * E.B 0 * E.a)) / (2 * E.B 0)

/-- The rescaled state map: `F (P + ε • w) = P + ε • G ε w`. -/
noncomputable def AG (E : Eqn k) (ε : ℝ) (w : Fin (k + 1) → ℝ) : Fin (k + 1) → ℝ :=
  Fin.snoc (Fin.tail w)
    ((E.ATheta w - E.B 0 * E.astar * w 0) / (E.B 0 * (E.astar + ε * w 0)))

/-- The rescaled orbit through the direction `v`. -/
noncomputable def APsi (E : Eqn k) (v : Fin (k + 1) → ℝ) (ε : ℝ) : ℕ → (Fin (k + 1) → ℝ)
  | 0 => v
  | (m + 1) => E.AG ε (E.APsi v ε m)

variable {E : Eqn k}

lemma APsi_succ (E : Eqn k) (v : Fin (k + 1) → ℝ) (ε : ℝ) (m : ℕ) :
    E.APsi v ε (m + 1) = E.AG ε (E.APsi v ε m) := rfl

/-- At `ε = 0` the rescaled orbit is the orbit of the linearisation. -/
lemma APsi_zero_iterate (E : Eqn k) (v : Fin (k + 1) → ℝ) :
    ∀ m, E.APsi v 0 m = (E.AG 0)^[m] v := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [APsi_succ, ih, Function.iterate_succ_apply']

/-! ### Elementary consequences of `Astar` -/

lemma Astar.B0_pos (h : Astar E) : 0 < E.B 0 := by
  have hb := E.b_pos
  rw [Fin.sum_univ_succ, h.b0] at hb
  have : ∑ j : Fin k, E.B j.succ = 0 :=
    Finset.sum_eq_zero fun j _ => h.Bsucc j
  rw [this] at hb
  linarith

lemma Astar.sig_nonneg (_h : Astar E) : 0 ≤ E.sig :=
  Finset.sum_nonneg fun _ _ => E.A_nonneg _

lemma Astar.a_sig_pos (h : Astar E) : 0 < E.a + E.sig := by
  have ha := E.a_pos
  rw [Fin.sum_univ_succ, h.A0] at ha
  simpa [sig] using ha

private lemma Astar.disc_nonneg (h : Astar E) : 0 ≤ E.sig ^ 2 + 4 * E.B 0 * E.a := by
  have := h.B0_pos
  nlinarith [E.a_nonneg, sq_nonneg E.sig]

lemma Astar.astar_pos (h : Astar E) : 0 < E.astar := by
  have hB := h.B0_pos
  have hsig := h.sig_nonneg
  have hs : 0 ≤ Real.sqrt (E.sig ^ 2 + 4 * E.B 0 * E.a) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (E.sig ^ 2 + 4 * E.B 0 * E.a) ^ 2 = E.sig ^ 2 + 4 * E.B 0 * E.a :=
    Real.sq_sqrt h.disc_nonneg
  have hnum : 0 < E.sig + Real.sqrt (E.sig ^ 2 + 4 * E.B 0 * E.a) := by
    by_contra hcon
    push_neg at hcon
    have h1 : E.sig = 0 := by linarith
    have h2 : Real.sqrt (E.sig ^ 2 + 4 * E.B 0 * E.a) = 0 := by linarith
    rw [h2, h1] at hsq
    have ha : E.a = 0 := by nlinarith [E.a_nonneg]
    have := h.a_sig_pos
    rw [h1, ha] at this
    linarith
  exact div_pos hnum (by linarith)

/-- The equilibrium equation. -/
lemma Astar.astar_eq (h : Astar E) : E.B 0 * E.astar ^ 2 = E.a + E.sig * E.astar := by
  have hB := h.B0_pos
  set s : ℝ := Real.sqrt (E.sig ^ 2 + 4 * E.B 0 * E.a) with hsdef
  have hsq : s ^ 2 = E.sig ^ 2 + 4 * E.B 0 * E.a := Real.sq_sqrt h.disc_nonneg
  have hxs : 2 * E.B 0 * E.astar = E.sig + s := by
    simp only [astar, ← hsdef]
    field_simp
  have h4 : (4 * E.B 0) * (E.B 0 * E.astar ^ 2) = (4 * E.B 0) * (E.a + E.sig * E.astar) := by
    linear_combination hsq + (2 * E.B 0 * E.astar - E.sig + s) * hxs
  exact mul_left_cancel₀ (by positivity : (4 * E.B 0) ≠ 0) h4

lemma Astar.num_eq (h : Astar E) (u : Fin (k + 1) → ℝ) : E.num u = E.a + E.ATheta u := by
  simp only [num, Fin.sum_univ_succ, h.A0, zero_mul, zero_add, ATheta]

lemma Astar.den_eq (h : Astar E) (u : Fin (k + 1) → ℝ) : E.den u = E.B 0 * u 0 := by
  simp only [den, Fin.sum_univ_succ, h.b0, zero_add, h.Bsucc, zero_mul,
    Finset.sum_const_zero, add_zero]

lemma ATheta_shift (E : Eqn k) (c ε : ℝ) (w : Fin (k + 1) → ℝ) :
    E.ATheta (fun i => c + ε * w i) = E.sig * c + ε * E.ATheta w := by
  simp only [ATheta, sig, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### The exact rescaling identity -/

/-- **The key identity.** `F (P + ε • w) = P + ε • G ε w`, exactly. -/
lemma Astar.F_shift (h : Astar E) (ε : ℝ) (w : Fin (k + 1) → ℝ)
    (hpos : Pos (fun i : Fin (k + 1) => E.astar + ε * w i)) :
    E.F (fun i => E.astar + ε * w i) = fun i => E.astar + ε * (E.AG ε w) i := by
  have hB := h.B0_pos
  have hden : E.den (fun i => E.astar + ε * w i) = E.B 0 * (E.astar + ε * w 0) := by
    rw [h.den_eq]
  have hd0 : E.B 0 * (E.astar + ε * w 0) ≠ 0 := by
    rw [← hden]; exact (E.den_pos hpos).ne'
  have hd1 : E.astar + ε * w 0 ≠ 0 := by
    have := hpos 0; simp only at this; linarith
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [F, Fin.snoc_last, AG, g]
    rw [h.num_eq, hden, ATheta_shift]
    have hnum2 : E.a + (E.sig * E.astar + ε * E.ATheta w)
        = E.astar * (E.B 0 * (E.astar + ε * w 0))
          + ε * (E.ATheta w - E.B 0 * E.astar * w 0) := by
      linear_combination (-1 : ℝ) * h.astar_eq
    rw [hnum2]
    field_simp
  · intro j
    simp [F, AG, Fin.tail]

/-- A direction `v` keeps `P + ε • v` inside `Ω` for all small enough `ε > 0`. -/
lemma Astar.shift_pos (_h : Astar E) {v : Fin (k + 1) → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hlt : ε < E.astar / (∑ i, |v i| + 1)) :
    Pos (fun i : Fin (k + 1) => E.astar + ε * v i) := by
  have hM : (0:ℝ) ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  intro i
  have hvi : |v i| ≤ ∑ i, |v i| :=
    Finset.single_le_sum (f := fun i => |v i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have h1 : ε * (∑ i, |v i| + 1) < E.astar := by
    rw [lt_div_iff₀ (by linarith)] at hlt; linarith
  have h2 : |ε * v i| ≤ ε * (∑ i, |v i| + 1) := by
    rw [abs_mul, abs_of_pos hε]
    have : |v i| ≤ ∑ i, |v i| + 1 := by linarith
    exact mul_le_mul_of_nonneg_left this hε.le
  have := abs_le.mp h2
  linarith [this.1]

/-- Iterating the identity. -/
lemma Astar.F_iterate_shift (h : Astar E) {v : Fin (k + 1) → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hlt : ε < E.astar / (∑ i, |v i| + 1)) :
    ∀ m, E.F^[m] (fun i : Fin (k + 1) => E.astar + ε * v i)
        = fun i => E.astar + ε * (E.APsi v ε m) i := by
  have hv := h.shift_pos hε hlt
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    have hposm : Pos (E.F^[m] (fun i : Fin (k + 1) => E.astar + ε * v i)) :=
      E.F_iterate_pos hv m
    rw [ih] at hposm
    rw [Function.iterate_succ_apply', ih, h.F_shift ε _ hposm, APsi_succ]

/-! ### Continuity in `ε` at `ε = 0` -/

lemma Astar.APsi_continuousAt (h : Astar E) (v : Fin (k + 1) → ℝ) :
    ∀ m, ∀ i, ContinuousAt (fun ε => E.APsi v ε m i) 0 := by
  intro m
  induction m with
  | zero => intro i; exact continuousAt_const
  | succ m ih =>
    have hTheta : ContinuousAt (fun ε => E.ATheta (E.APsi v ε m)) 0 := by
      simp only [ATheta]
      exact tendsto_finset_sum _ fun j _ => continuousAt_const.mul (ih j.succ)
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simp only [APsi_succ, AG, Fin.snoc_last]
      refine ContinuousAt.div ?_ ?_ ?_
      · exact hTheta.sub (continuousAt_const.mul (ih 0))
      · exact continuousAt_const.mul (continuousAt_const.add (continuousAt_id.mul (ih 0)))
      · simpa using (mul_pos h.B0_pos h.astar_pos).ne'
    · intro j
      simp only [APsi_succ, AG, Fin.snoc_castSucc, Fin.tail]
      exact ih j.succ

/-! ### The linearisation is `p`-periodic -/

/-- **Theorem D.**  If the equation is `p`-periodic, its linearisation at the
interior equilibrium is `p`-periodic too: `C^[p] = id` for `C = AG 0`. -/
theorem Astar.linear_periodic (h : Astar E) {p : ℕ}
    (hper : ∀ u, Pos u → E.F^[p] u = u) (v : Fin (k + 1) → ℝ) :
    (E.AG 0)^[p] v = v := by
  set δ : ℝ := E.astar / (∑ i, |v i| + 1) with hδdef
  have hM : (0:ℝ) ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hδ : 0 < δ := div_pos h.astar_pos (by linarith)
  -- periodicity pins the rescaled orbit back to `v`, for all small `ε > 0`
  have hfix : ∀ ε : ℝ, 0 < ε → ε < δ → ∀ i, E.APsi v ε p i = v i := by
    intro ε hε hεδ i
    have h1 := h.F_iterate_shift hε hεδ p
    rw [hper _ (h.shift_pos hε hεδ)] at h1
    have h2 := congrFun h1 i
    simp only at h2
    have h3 : ε * v i = ε * E.APsi v ε p i := by linarith
    exact (mul_left_cancel₀ hε.ne' h3).symm
  -- continuity at `0` transports this to `ε = 0`
  have key : ∀ i, E.APsi v 0 p i = v i := by
    intro i
    have hcont := h.APsi_continuousAt v p i
    have hlim1 : Tendsto (fun ε => E.APsi v ε p i) (𝓝[>] (0:ℝ)) (𝓝 (E.APsi v 0 p i)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun ε => E.APsi v ε p i) (𝓝[>] (0:ℝ)) (𝓝 (v i)) := by
      refine tendsto_const_nhds.congr' ?_
      have hmem : {ε : ℝ | ε < δ} ∈ 𝓝[>] (0:ℝ) :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
      filter_upwards [self_mem_nhdsWithin, hmem] with ε hε hεδ
      exact (hfix ε hε hεδ i).symm
    exact tendsto_nhds_unique hlim1 hlim2
  rw [← E.APsi_zero_iterate v p]
  funext i
  exact key i

/-! ### The coefficients of the linearisation -/

/-- `e j = A_{j+1} / (B₀ x*)`. -/
noncomputable def ecoef (E : Eqn k) (j : Fin k) : ℝ := E.A j.succ / (E.B 0 * E.astar)

end Eqn

end PeriodicDifference
