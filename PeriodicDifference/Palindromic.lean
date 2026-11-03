/-
# The palindromic theorem

`PeriodicDifference/FamilyA.lean` proves `Astar.linear_periodic`: for a `p`-periodic member of
family (a), the linearisation `C = AG 0` at the interior equilibrium satisfies
`C^[p] = id`.  Its characteristic polynomial is

  `χ(λ) = λ^{k+1} - Σ_j e_j λ^{j+1} + 1`,   `e_j = A_{j+1} / (B₀ x*)`.

This file proves that `χ` is **palindromic**:

  `Astar.ecoef_rev` :  `e_j = e_{k-1-j}`,   i.e.   `A_{j+1} = A_{k-j}`.

In the paper's indexing that is `A_i = A_{k+2-i}` for `2 ≤ i ≤ k`; at order 4, for
instance, it gives `A₂ = A₄`.

## The argument

The textbook proof is spectral: `C^[p] = id` makes every eigenvalue a root of
unity, so `λ⁻¹ = λ̄`; `C` is real, so its eigenvalue multiset is closed under
conjugation, hence under inversion, hence `χ` is self-reciprocal.  Formalising that
needs complex eigenvalues, `Matrix.charpoly` and a multiset argument.

None of it is necessary.  Everything happens at the level of sequences.  A state
orbit of `C` is a solution of the linear recurrence

  `u_{n+k+1} + u_n = Σ_j e_j u_{n+j+1}`,                                  (R)

and `C^[p] = id` says every solution is `p`-periodic.  On `p`-periodic sequences
the *period sum* `⟪u,v⟫ = Σ_{n<p} u_n v_n` is positive definite, and it is
invariant under shifting.  So shifting is orthogonal, its inverse is its adjoint,
and (R) must be reversible.  Concretely: pairing (R) for `u` against `v` shifted,
and moving every shift off `u` and onto `v` (legitimate because both are
`p`-periodic), gives

  `Σ_{n<p} u_n · ρ_n = 0`   for all solutions `u`,   where
  `ρ_n := v_n + v_{n+k+1} - Σ_j e_j v_{n+k-j}`.

Using (R) for `v` turns `ρ` into `ρ_n = Σ_j (e_j - e_{k-1-j}) v_{n+j+1}` — a linear
combination of shifts of `v`, hence itself a solution.  Taking `u := ρ` yields
`Σ_{n<p} ρ_n² = 0`, so `ρ ≡ 0`.  Reading `ρ₀ = 0` on the solution with initial
window a standard basis vector gives `e_j = e_{k-1-j}`.
-/

import PeriodicDifference.FamilyA

namespace PeriodicDifference

open Finset

/-! ## Linear recurrences with all solutions periodic -/

namespace Seq

variable {k : ℕ}

/-- `u` satisfies the recurrence `u_{n+k+1} + u_n = Σ_j e_j u_{n+j+1}`. -/
def SatRec (e : Fin k → ℝ) (u : ℕ → ℝ) : Prop :=
  ∀ n, u (n + k + 1) + u n = ∑ j : Fin k, e j * u (n + j + 1)

/-- `u` is `p`-periodic. -/
def SatPer (p : ℕ) (u : ℕ → ℝ) : Prop := ∀ n, u (n + p) = u n

variable {e : Fin k → ℝ} {p : ℕ} {u v : ℕ → ℝ}

/-- A period sum is unchanged by shifting. -/
lemma sum_shift (hu : SatPer p u) : ∀ a, ∑ n ∈ range p, u (n + a) = ∑ n ∈ range p, u n := by
  have step : ∀ w : ℕ → ℝ, SatPer p w → ∑ n ∈ range p, w (n + 1) = ∑ n ∈ range p, w n := by
    intro w hw
    have h1 : ∑ n ∈ range (p + 1), w n = (∑ n ∈ range p, w n) + w p := Finset.sum_range_succ _ _
    have h2 : ∑ n ∈ range (p + 1), w n = (∑ n ∈ range p, w (n + 1)) + w 0 :=
      Finset.sum_range_succ' _ _
    have h3 : w p = w 0 := by simpa using hw 0
    rw [h3] at h1
    linarith [h1, h2]
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have hper : SatPer p (fun n => u (n + a)) := by
      intro n; simpa [Nat.add_right_comm] using hu (n + a)
    have hstep := step (fun n => u (n + a)) hper
    simp only at hstep
    calc ∑ n ∈ range p, u (n + (a + 1))
        = ∑ n ∈ range p, u (n + 1 + a) :=
          Finset.sum_congr rfl fun n _ => by rw [show n + (a + 1) = n + 1 + a from by omega]
      _ = ∑ n ∈ range p, u (n + a) := hstep
      _ = ∑ n ∈ range p, u n := ih

/-- A linear combination of shifts of a solution is a solution. -/
lemma satRec_comb {ι : Type*} (s : Finset ι) (d : ι → ℝ) (f : ι → ℕ)
    (hv : SatRec e v) : SatRec e (fun n => ∑ i ∈ s, d i * v (n + f i)) := by
  intro n
  simp only
  have key : ∀ i, d i * v (n + f i + k + 1) + d i * v (n + f i)
      = ∑ j : Fin k, e j * (d i * v (n + j + 1 + f i)) := by
    intro i
    have h := hv (n + f i)
    rw [← mul_add, h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show n + f i + (j : ℕ) + 1 = n + (j : ℕ) + 1 + f i from by omega]
    ring
  calc (∑ i ∈ s, d i * v (n + k + 1 + f i)) + ∑ i ∈ s, d i * v (n + f i)
      = ∑ i ∈ s, (d i * v (n + f i + k + 1) + d i * v (n + f i)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show n + k + 1 + f i = n + f i + k + 1 from by omega]
    _ = ∑ i ∈ s, ∑ j : Fin k, e j * (d i * v (n + j + 1 + f i)) :=
        Finset.sum_congr rfl fun i _ => key i
    _ = ∑ j : Fin k, e j * ∑ i ∈ s, d i * v (n + j + 1 + f i) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]

lemma satPer_comb {ι : Type*} (s : Finset ι) (d : ι → ℝ) (f : ι → ℕ)
    (hv : SatPer p v) : SatPer p (fun n => ∑ i ∈ s, d i * v (n + f i)) := by
  intro n
  simp only
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show n + p + f i = n + f i + p from by omega, hv]

/-- `ρ`, the "reversed-recurrence defect" of `v`. -/
def rho (e : Fin k → ℝ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  v n + v (n + k + 1) - ∑ j : Fin k, e j * v (n + k - j)

/-- **The pairing.**  Moving every shift from `u` onto `v` inside the period sum. -/
lemma pairing (hu : SatRec e u) (hup : SatPer p u) (hvp : SatPer p v) :
    ∑ n ∈ range p, u n * rho e v n = 0 := by
  have e1 : ∑ n ∈ range p, u n * v n = ∑ n ∈ range p, v (n + k + 1) * u (n + k + 1) := by
    have hper : SatPer p (fun m => u m * v m) := by
      intro m; simp only; rw [hup, hvp]
    have h := sum_shift hper (k + 1)
    simp only at h
    rw [← h]
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  have e3 : ∀ j : Fin k, ∑ n ∈ range p, u n * v (n + k - j)
      = ∑ n ∈ range p, v (n + k + 1) * u (n + j + 1) := by
    intro j
    have hper : SatPer p (fun m => u m * v (m + k - (j : ℕ))) := by
      intro m; simp only
      rw [hup, show m + p + k - (j : ℕ) = m + k - (j : ℕ) + p from by omega, hvp]
    have h := sum_shift hper ((j : ℕ) + 1)
    simp only at h
    rw [← h]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show n + ((j : ℕ) + 1) + k - (j : ℕ) = n + k + 1 from by omega,
      show n + ((j : ℕ) + 1) = n + j + 1 from by omega]
    ring
  calc ∑ n ∈ range p, u n * rho e v n
      = (∑ n ∈ range p, u n * v n) + (∑ n ∈ range p, u n * v (n + k + 1))
        - ∑ j : Fin k, e j * ∑ n ∈ range p, u n * v (n + k - j) := by
        rw [show (∑ j : Fin k, e j * ∑ n ∈ range p, u n * v (n + k - (j : ℕ)))
            = ∑ n ∈ range p, ∑ j : Fin k, e j * (u n * v (n + k - (j : ℕ))) from by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]]
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [rho, mul_sub, mul_add, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ n ∈ range p, v (n + k + 1) * u (n + k + 1))
        + (∑ n ∈ range p, v (n + k + 1) * u n)
        - ∑ j : Fin k, e j * ∑ n ∈ range p, v (n + k + 1) * u (n + j + 1) := by
        have hcomm : ∑ n ∈ range p, u n * v (n + k + 1)
            = ∑ n ∈ range p, v (n + k + 1) * u n :=
          Finset.sum_congr rfl fun n _ => mul_comm _ _
        rw [e1, hcomm]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by rw [e3 j]
    _ = 0 := by
        rw [← Finset.sum_add_distrib]
        rw [show (∑ j : Fin k, e j * ∑ n ∈ range p, v (n + k + 1) * u (n + j + 1))
            = ∑ n ∈ range p, ∑ j : Fin k, e j * (v (n + k + 1) * u (n + j + 1)) from by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_eq_zero fun n _ => ?_
        have hin : ∑ j : Fin k, e j * (v (n + k + 1) * u (n + j + 1))
            = v (n + k + 1) * ∑ j : Fin k, e j * u (n + j + 1) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hin, ← mul_add, hu n, sub_self]

lemma sum_rev {m : ℕ} (f : Fin m → ℝ) : ∑ j : Fin m, f j.rev = ∑ j : Fin m, f j :=
  Fintype.sum_bijective Fin.rev Fin.rev_involutive.bijective _ _ (fun _ => rfl)

/-- Using the recurrence for `v`, `ρ` becomes a combination of shifts of `v` with the
*antisymmetrised* coefficients. -/
lemma rho_eq (hv : SatRec e v) (n : ℕ) :
    rho e v n = ∑ j : Fin k, (e j - e j.rev) * v (n + j + 1) := by
  have hrev : ∑ j : Fin k, e j * v (n + k - (j : ℕ))
      = ∑ j : Fin k, e j.rev * v (n + j + 1) := by
    rw [← sum_rev (fun j : Fin k => e j * v (n + k - (j : ℕ)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : ((j.rev : Fin k) : ℕ) = k - 1 - (j : ℕ) := by
      rw [Fin.val_rev]; omega
    rw [hj, show n + k - (k - 1 - (j : ℕ)) = n + (j : ℕ) + 1 from by omega]
  rw [rho, hrev]
  have h1 : v n + v (n + k + 1) = ∑ j : Fin k, e j * v (n + j + 1) := by
    rw [← hv n]; ring
  rw [h1, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The reversed recurrence holds too.**  Hence the antisymmetrised coefficients
annihilate every solution. -/
lemma rho_eq_zero (hp : 0 < p) (hv : SatRec e v) (hvp : SatPer p v) (n : ℕ) :
    rho e v n = 0 := by
  have hrho : rho e v = fun m => ∑ j : Fin k, (e j - e j.rev) * v (m + ((j : ℕ) + 1)) := by
    funext m
    exact rho_eq hv m
  have hR : SatRec e (rho e v) := by
    rw [hrho]
    exact satRec_comb Finset.univ (fun j => e j - e j.rev) (fun j => (j : ℕ) + 1) hv
  have hP : SatPer p (rho e v) := by
    rw [hrho]
    exact satPer_comb Finset.univ (fun j => e j - e j.rev) (fun j => (j : ℕ) + 1) hvp
  have hzero : ∑ m ∈ range p, rho e v m * rho e v m = 0 := pairing hR hP hvp
  have hall : ∀ m ∈ range p, rho e v m * rho e v m = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => mul_self_nonneg _)).mp hzero
  have hbase : ∀ m, m < p → rho e v m = 0 := by
    intro m hm
    have h := hall m (Finset.mem_range.mpr hm)
    nlinarith [h]
  have hstep : ∀ q m, m < p → rho e v (m + q * p) = 0 := by
    intro q
    induction q with
    | zero => intro m hm; simpa using hbase m hm
    | succ q ih =>
      intro m hm
      rw [show m + (q + 1) * p = m + q * p + p from by ring, hP]
      exact ih m hm
  have hkey := hstep (n / p + 1) (n % p) (Nat.mod_lt _ hp)
  have hdm : p * (n / p) + n % p = n := Nat.div_add_mod n p
  have hmul : (n / p + 1) * p = p * (n / p) + p := by ring
  rw [show n % p + (n / p + 1) * p = n + p from by omega, hP] at hkey
  exact hkey

/-- **The palindromic theorem, sequence form.**  If every solution of the
recurrence is `p`-periodic and every initial window is realised, the coefficients
are symmetric. -/
theorem coeff_rev (hp : 0 < p)
    (hall : ∀ w : Fin (k + 1) → ℝ, ∃ v : ℕ → ℝ, SatRec e v ∧ SatPer p v ∧
      ∀ i : Fin (k + 1), v (i : ℕ) = w i) (j₀ : Fin k) :
    e j₀ = e j₀.rev := by
  set w₀ : Fin (k + 1) → ℝ := Pi.single j₀.succ 1 with hw₀
  obtain ⟨v, hv, hvp, hvw⟩ := hall w₀
  have h0 := rho_eq_zero hp hv hvp 0
  rw [rho_eq hv 0] at h0
  have hterm : ∀ j : Fin k, (e j - e j.rev) * v (0 + j + 1)
      = if j = j₀ then e j₀ - e j₀.rev else 0 := by
    intro j
    have hvj : v (0 + (j : ℕ) + 1) = w₀ j.succ := by
      rw [show (0 : ℕ) + (j : ℕ) + 1 = ((j.succ : Fin (k + 1)) : ℕ) from by simp]
      exact hvw j.succ
    rw [hvj]
    by_cases hj : j = j₀
    · subst hj; simp [hw₀]
    · have hne : (j.succ : Fin (k + 1)) ≠ j₀.succ := fun hc => hj (Fin.succ_injective _ hc)
      simp [hw₀, hne, hj]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)] at h0
  simp at h0
  linarith

end Seq

/-! ## Back to the difference equation -/

namespace Eqn

variable {k : ℕ} {E : Eqn k}

/-- The trajectory of the linearisation from an initial window. -/
noncomputable def traj (E : Eqn k) (w : Fin (k + 1) → ℝ) (n : ℕ) : ℝ :=
  ((E.AG 0)^[n] w) 0

lemma AG_zero_castSucc (E : Eqn k) (w : Fin (k + 1) → ℝ) (j : Fin k) :
    E.AG 0 w (Fin.castSucc j) = w j.succ := by
  simp [AG, Fin.tail]

lemma Astar.AG_zero_last (h : Astar E) (w : Fin (k + 1) → ℝ) :
    E.AG 0 w (Fin.last k) = (∑ j : Fin k, E.ecoef j * w j.succ) - w 0 := by
  have hBx : E.B 0 * E.astar ≠ 0 := (mul_pos h.B0_pos h.astar_pos).ne'
  simp only [AG, Fin.snoc_last]
  rw [show E.B 0 * (E.astar + 0 * w 0) = E.B 0 * E.astar from by ring, sub_div]
  congr 1
  · simp only [ATheta, ecoef, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  · rw [mul_comm (E.B 0 * E.astar) (w 0), mul_div_assoc, div_self hBx, mul_one]

lemma traj_index (E : Eqn k) (w : Fin (k + 1) → ℝ) :
    ∀ (i : ℕ) (hi : i < k + 1) (n : ℕ), ((E.AG 0)^[n] w) ⟨i, hi⟩ = E.traj w (n + i) := by
  intro i
  induction i with
  | zero => intro hi n; simp [traj]
  | succ i ih =>
    intro hi n
    have hik : i < k := by omega
    have hcast : (⟨i + 1, hi⟩ : Fin (k + 1)) = Fin.succ ⟨i, hik⟩ := by apply Fin.ext; simp
    have hcs : (Fin.castSucc ⟨i, hik⟩ : Fin (k + 1)) = ⟨i, by omega⟩ := by apply Fin.ext; simp
    rw [hcast, show ((E.AG 0)^[n] w) (Fin.succ ⟨i, hik⟩)
        = ((E.AG 0)^[n + 1] w) (Fin.castSucc ⟨i, hik⟩) from by
      rw [Function.iterate_succ_apply', E.AG_zero_castSucc], hcs, ih (by omega) (n + 1)]
    congr 1
    omega

lemma traj_init (E : Eqn k) (w : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    E.traj w (i : ℕ) = w i := by
  have := E.traj_index w (i : ℕ) i.isLt 0
  simpa using this.symm

lemma Astar.traj_satRec (h : Astar E) (w : Fin (k + 1) → ℝ) :
    Seq.SatRec E.ecoef (E.traj w) := by
  intro n
  have h1 := E.traj_index w k (by omega) (n + 1)
  rw [show (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k from rfl,
    Function.iterate_succ_apply', h.AG_zero_last] at h1
  have h2 : ∀ j : Fin k, ((E.AG 0)^[n] w) j.succ = E.traj w (n + j + 1) := by
    intro j
    have := E.traj_index w ((j : ℕ) + 1) (by omega) n
    rw [show (⟨(j : ℕ) + 1, by omega⟩ : Fin (k + 1)) = j.succ from by apply Fin.ext; simp] at this
    exact this
  have h3 : ((E.AG 0)^[n] w) 0 = E.traj w n := by
    have := E.traj_index w 0 (by omega) n
    simpa using this
  rw [h3] at h1
  rw [Finset.sum_congr rfl (fun j _ => by rw [h2 j])] at h1
  rw [show n + 1 + k = n + k + 1 from by omega] at h1
  linarith [h1]

lemma Astar.traj_satPer (h : Astar E) {p : ℕ}
    (hper : ∀ u, Pos u → E.F^[p] u = u) (w : Fin (k + 1) → ℝ) :
    Seq.SatPer p (E.traj w) := by
  intro n
  simp only [traj]
  rw [show n + p = p + n from by omega, Function.iterate_add_apply, h.linear_periodic hper]

/-- **The palindromic theorem.**  For a `p`-periodic member of family (a) the
characteristic polynomial of the linearisation is self-reciprocal. -/
theorem Astar.ecoef_rev (h : Astar E) {p : ℕ} (hp : 0 < p)
    (hper : ∀ u, Pos u → E.F^[p] u = u) (j : Fin k) : E.ecoef j = E.ecoef j.rev := by
  refine Seq.coeff_rev hp (fun w => ⟨E.traj w, h.traj_satRec w, h.traj_satPer hper w, ?_⟩) j
  intro i
  exact E.traj_init w i

/-- In terms of the original coefficients: `A_{j+1} = A_{k-j}`, i.e. the paper's
`A_i = A_{k+2-i}`. -/
theorem Astar.coeff_rev (h : Astar E) {p : ℕ} (hp : 0 < p)
    (hper : ∀ u, Pos u → E.F^[p] u = u) (j : Fin k) :
    E.A j.succ = E.A (Fin.rev j).succ := by
  have hBx : E.B 0 * E.astar ≠ 0 := (mul_pos h.B0_pos h.astar_pos).ne'
  have hx := h.ecoef_rev hp hper j
  simp only [ecoef] at hx
  have h2 := congrArg (fun x : ℝ => x * (E.B 0 * E.astar)) hx
  simp only at h2
  rwa [div_mul_cancel₀ _ hBx, div_mul_cancel₀ _ hBx] at h2


end Eqn

end PeriodicDifference
