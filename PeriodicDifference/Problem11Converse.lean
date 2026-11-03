/-
# `PeriodicDifference/Problem11Converse.lean` — every member is globally periodic

The converse of `problem11_complete`: each of the five equations of `Member`, in every
rescaling and unfolding, is globally periodic on positive states, with periods

* the shift `x_{n+K} = xₙ`: `K`;
* `B₀ x_{n+K} xₙ = a`: `2K`;
* `B₀ x_{n+2m} xₙ = A_m x_{n+m}`: `6m`;
* `B₀ x_{n+2m} xₙ = a + A_m x_{n+m}`, `a B₀ = A_m²` (Lyness): `5m`;
* `B₀ x_{n+3m} xₙ = a + A_m (x_{n+m} + x_{n+2m})`, `a B₀ = A_m²` (Todd): `8m`,

where `K = k + 1`.  The proof works with the sequence `n ↦ (E.F^[n] u) 0`: the state
`E.F^[n] u` is its window at `n`, and the sequence solves the equation.  With
`c = A_m / B₀ > 0`, the unfolded equations read `x_{n+2m} xₙ = c² + c x_{n+m}` and so on;
the base periodicities are computed directly along the progression `n, n+m, n+2m, …`,
so no splitting into residue classes is needed.
-/
import PeriodicDifference.Problem11Defs

namespace PeriodicDifference
namespace Problem11

namespace Converse

/-! ## The base periodicities, along a progression -/

section Base

variable {y : ℕ → ℝ} {c : ℝ}

/-- `y_{i+2} yᵢ = c² + c y_{i+1}` (Lyness, rescaled) is `5`-periodic. -/
lemma base_five (hc : 0 < c) (hy : ∀ i, 0 < y i)
    (h : ∀ i, y (i + 2) * y i = c ^ 2 + c * y (i + 1)) : y 5 = y 0 := by
  have e : ∀ i, y (i + 2) = (c ^ 2 + c * y (i + 1)) / y i :=
    fun i => eq_div_of_mul_eq (hy i).ne' (h i)
  have ha := hy 0
  have hb := hy 1
  have ha' := ha.ne'
  have hb' := hb.ne'
  have hc' := hc.ne'
  have h1 : y 0 + y 1 + c ≠ 0 := by positivity
  have h2 : c + y 1 ≠ 0 := by positivity
  have h3 : y 0 + c ≠ 0 := by positivity
  have f2 : y 2 = c * (c + y 1) / y 0 := by
    rw [e 0]; ring
  have f3 : y 3 = c ^ 2 * (y 0 + y 1 + c) / (y 0 * y 1) := by
    rw [e 1, f2]; field_simp; ring
  have f4 : y 4 = c * (y 0 + c) / y 1 := by
    rw [e 2, f3, f2]; field_simp; ring
  rw [e 3, f4, f3]; field_simp; ring

/-- `y_{i+2} yᵢ = c y_{i+1}` (rescaled) is `6`-periodic. -/
lemma base_six (hc : 0 < c) (hy : ∀ i, 0 < y i)
    (h : ∀ i, y (i + 2) * y i = c * y (i + 1)) : y 6 = y 0 := by
  have e : ∀ i, y (i + 2) = c * y (i + 1) / y i :=
    fun i => eq_div_of_mul_eq (hy i).ne' (h i)
  have ha' := (hy 0).ne'
  have hb' := (hy 1).ne'
  have hc' := hc.ne'
  have f2 : y 2 = c * y 1 / y 0 := e 0
  have f3 : y 3 = c ^ 2 / y 0 := by rw [e 1, f2]; field_simp
  have f4 : y 4 = c ^ 2 / y 1 := by rw [e 2, f3, f2]; field_simp
  have f5 : y 5 = c * y 0 / y 1 := by rw [e 3, f4, f3]; field_simp
  rw [e 4, f5, f4]; field_simp

/-- `y_{i+3} yᵢ = c² + c (y_{i+1} + y_{i+2})` (Todd, rescaled) is `8`-periodic. -/
lemma base_eight (hc : 0 < c) (hy : ∀ i, 0 < y i)
    (h : ∀ i, y (i + 3) * y i = c ^ 2 + c * (y (i + 1) + y (i + 2))) : y 8 = y 0 := by
  have e : ∀ i, y (i + 3) = (c ^ 2 + c * (y (i + 1) + y (i + 2))) / y i :=
    fun i => eq_div_of_mul_eq (hy i).ne' (h i)
  have ha := hy 0
  have hb := hy 1
  have hd := hy 2
  have ha' := ha.ne'
  have hb' := hb.ne'
  have hd' := hd.ne'
  have hc' := hc.ne'
  have g1 : y 1 + c + y 2 ≠ 0 := by positivity
  have g2 : y 0 + y 1 + c ≠ 0 := by positivity
  have g3 : y 0 * c + y 0 * y 2 + y 1 * c + c ^ 2 + c * y 2 ≠ 0 := by positivity
  have f3 : y 3 = c * (y 1 + c + y 2) / y 0 := by rw [e 0]; ring
  have f4 : y 4 = c * (y 0 * c + y 0 * y 2 + y 1 * c + c ^ 2 + c * y 2) / (y 0 * y 1) := by
    rw [e 1, f3]; field_simp; ring
  have f5 : y 5 = c ^ 2 * (y 0 + y 1 + c) * (y 1 + c + y 2) / (y 0 * y 1 * y 2) := by
    rw [e 2, f4, f3]; field_simp; ring
  have f6 : y 6 = c * (y 0 * c + y 0 * y 2 + y 1 * c + c ^ 2 + c * y 2) / (y 1 * y 2) := by
    rw [e 3, f5, f4, f3]; field_simp; ring
  have f7 : y 7 = c * (y 0 + y 1 + c) / y 2 := by
    rw [e 4, f6, f5, f4]; field_simp; ring
  rw [e 5, f7, f6, f5]; field_simp; ring

end Base

/-! ## Transfer along `n, n+m, n+2m, …` -/

section Step

variable {x : ℕ → ℝ} {m : ℕ} {c : ℝ}

lemma step_two (hx : ∀ n, 0 < x n) (h : ∀ n, x (n + m) * x n = c) (n : ℕ) :
    x (n + 2 * m) = x n := by
  have h1 := h n
  have h2 := h (n + m)
  rw [show n + m + m = n + 2 * m by ring] at h2
  refine mul_left_cancel₀ (hx (n + m)).ne' ?_
  rw [mul_comm, h2, h1]

lemma step_five (hc : 0 < c) (hx : ∀ n, 0 < x n)
    (h : ∀ n, x (n + 2 * m) * x n = c ^ 2 + c * x (n + m)) (n : ℕ) :
    x (n + 5 * m) = x n := by
  have := base_five (y := fun i => x (n + i * m)) hc (fun i => hx _) (fun i => by
    have := h (n + i * m)
    rw [show n + i * m + 2 * m = n + (i + 2) * m by ring,
      show n + i * m + m = n + (i + 1) * m by ring] at this
    exact this)
  simpa using this

lemma step_six (hc : 0 < c) (hx : ∀ n, 0 < x n)
    (h : ∀ n, x (n + 2 * m) * x n = c * x (n + m)) (n : ℕ) :
    x (n + 6 * m) = x n := by
  have := base_six (y := fun i => x (n + i * m)) hc (fun i => hx _) (fun i => by
    have := h (n + i * m)
    rw [show n + i * m + 2 * m = n + (i + 2) * m by ring,
      show n + i * m + m = n + (i + 1) * m by ring] at this
    exact this)
  simpa using this

lemma step_eight (hc : 0 < c) (hx : ∀ n, 0 < x n)
    (h : ∀ n, x (n + 3 * m) * x n = c ^ 2 + c * (x (n + m) + x (n + 2 * m))) (n : ℕ) :
    x (n + 8 * m) = x n := by
  have := base_eight (y := fun i => x (n + i * m)) hc (fun i => hx _) (fun i => by
    have := h (n + i * m)
    rw [show n + i * m + 3 * m = n + (i + 3) * m by ring,
      show n + i * m + m = n + (i + 1) * m by ring,
      show n + i * m + 2 * m = n + (i + 2) * m by ring] at this
    exact this)
  simpa using this

end Step

/-! ## The orbit as a sequence -/

section Orbit

variable {k : ℕ} (E : Eqn k)

lemma F_castSucc (v : Fin (k + 1) → ℝ) (i : Fin k) : E.F v i.castSucc = v i.succ := by
  simp [Eqn.F, Fin.tail]

lemma F_last (v : Fin (k + 1) → ℝ) : E.F v (Fin.last k) = E.g v := by
  simp [Eqn.F]

lemma iter_apply (u : Fin (k + 1) → ℝ) : ∀ (j : ℕ) (hj : j < k + 1) (n : ℕ),
    (E.F^[n] u) ⟨j, hj⟩ = (E.F^[n + j] u) 0 := by
  intro j
  induction j with
  | zero => intro _ n; rfl
  | succ j ih =>
    intro hj n
    have hjk : j < k := by omega
    have e1 : (⟨j + 1, hj⟩ : Fin (k + 1)) = (⟨j, hjk⟩ : Fin k).succ := rfl
    rw [e1, ← F_castSucc E (E.F^[n] u), ← Function.iterate_succ_apply' E.F n u]
    have e2 : (⟨j, hjk⟩ : Fin k).castSucc = ⟨j, by omega⟩ := rfl
    rw [e2, ih, show n + 1 + j = n + (j + 1) by omega]

/-- The orbit of `u`, read off in its oldest coordinate. -/
noncomputable def sq (u : Fin (k + 1) → ℝ) (n : ℕ) : ℝ := (E.F^[n] u) 0

lemma orbit_win (u : Fin (k + 1) → ℝ) (n : ℕ) :
    E.F^[n] u = fun j : Fin (k + 1) => sq E u (n + j) := by
  funext j
  exact iter_apply E u j.val j.isLt n

lemma sq_add (u : Fin (k + 1) → ℝ) (n : ℕ) :
    sq E u (n + (k + 1)) = E.g (fun j : Fin (k + 1) => sq E u (n + j)) := by
  rw [← orbit_win, sq, show n + (k + 1) = (n + 1) + k by omega,
    ← iter_apply E u k (by omega) (n + 1), Function.iterate_succ_apply', ← F_last]
  rfl

lemma sq_pos {u : Fin (k + 1) → ℝ} (hu : Pos u) (n : ℕ) : 0 < sq E u n :=
  E.F_iterate_pos hu n 0

lemma periodic_of_sq {u : Fin (k + 1) → ℝ} {p : ℕ}
    (h : ∀ n, sq E u (n + p) = sq E u n) : E.F^[p] u = u := by
  have h0 := orbit_win E u 0
  simp only [Function.iterate_zero, id_eq, zero_add] at h0
  calc E.F^[p] u = fun j : Fin (k + 1) => sq E u (p + j) := orbit_win E u p
    _ = u := by
      funext j
      rw [add_comm, h]
      exact (congrFun h0 j).symm

end Orbit

/-! ## Branch (a): the recurrence in coefficient form -/

section Astar

variable {k : ℕ} (E : Eqn k)

lemma sum_coef (f : ℕ → ℝ) :
    ∑ j : Fin (k + 1), E.A j * f j = ∑ j ∈ Finset.range (k + 1), coef E j * f j := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => coef E j * f j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [coef, j.isLt]

lemma coef_zero (h : E.Astar) : coef E 0 = 0 := by
  simp [coef, ← h.A0]

lemma coef_nonneg (j : ℕ) : 0 ≤ coef E j := by
  unfold coef
  split
  · exact E.A_nonneg _
  · exact le_rfl

/-- `a + Σ_j coef_j > 0`. -/
lemma a_sum_pos : 0 < E.a + ∑ j ∈ Finset.range (k + 1), coef E j * 1 := by
  rw [← sum_coef E (fun _ => 1)]
  simpa using E.a_pos

/-- Branch (a) in sequence form: `B₀ x_{n+K} xₙ = a + Σ_j coef_j x_{n+j}`. -/
lemma rec_astar (h : E.Astar) {u : Fin (k + 1) → ℝ} (hu : Pos u) (n : ℕ) :
    sq E u (n + (k + 1)) * sq E u n * E.B 0
      = E.a + ∑ j ∈ Finset.range (k + 1), coef E j * sq E u (n + j) := by
  have hB := h.B0_pos
  have hx := sq_pos E hu n
  have hden : E.den (fun j : Fin (k + 1) => sq E u (n + j)) = E.B 0 * sq E u n := by
    simp [Eqn.den, h.b0, Fin.sum_univ_succ, h.Bsucc]
  have hnum : E.num (fun j : Fin (k + 1) => sq E u (n + j))
      = E.a + ∑ j ∈ Finset.range (k + 1), coef E j * sq E u (n + j) := by
    rw [Eqn.num, ← sum_coef E (fun j : ℕ => sq E u (n + j))]
  rw [sq_add, Eqn.g, hden, hnum]
  field_simp

lemma sum_zero (h : E.Astar) (hz : ∀ m, 1 ≤ m → coef E m = 0) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range (k + 1), coef E j * f j = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [coef_zero E h, zero_mul]
  · rw [hz j hj, zero_mul]

lemma sum_one (h : E.Astar) {m : ℕ} (hm : m < k + 1)
    (hz : ∀ j, 1 ≤ j → j ≠ m → coef E j = 0) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range (k + 1), coef E j * f j = coef E m * f m := by
  rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr hm)]
  intro j _ hj
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · rw [coef_zero E h, zero_mul]
  · rw [hz j hj1 hj, zero_mul]

lemma sum_two (h : E.Astar) {m : ℕ} (hm1 : 1 ≤ m) (hm : 2 * m < k + 1)
    (hz : ∀ j, 1 ≤ j → j ≠ m → j ≠ 2 * m → coef E j = 0) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range (k + 1), coef E j * f j
      = coef E m * f m + coef E (2 * m) * f (2 * m) := by
  rw [Finset.sum_eq_add_of_mem m (2 * m) (Finset.mem_range.mpr (by omega))
    (Finset.mem_range.mpr hm) (by omega)]
  intro j _ hj
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · rw [coef_zero E h, zero_mul]
  · rw [hz j hj1 hj.1 hj.2, zero_mul]

end Astar

end Converse

open Converse

/-- **The converse of Problem 11.**  Every member — the five known equations, up to
rescaling and unfolding — is globally periodic on positive states. -/
theorem member_periodic {k : ℕ} (E : Eqn k) (h : Member E) :
    ∃ p, 0 < p ∧ ∀ u, Pos u → E.F^[p] u = u := by
  rcases h with ⟨hB0, ha, hA, hB, hAb⟩ | ⟨hA, hz⟩ | ⟨hA, ha0, m, hm, hz⟩ |
    ⟨hA, m, hm, hz, hcm⟩ | ⟨hA, m, hm, hz, h2m, hcm⟩
  · -- the shift, period `k + 1`
    refine ⟨k + 1, by omega, fun u hu => periodic_of_sq E fun n => ?_⟩
    have hb : 0 < E.b := by
      have := E.b_pos
      simpa [Fin.sum_univ_succ, hB0, hB] using this
    rw [sq_add, Eqn.g]
    simp only [Eqn.num, Eqn.den, ha, Fin.sum_univ_succ, hA, hB0, hB, hAb]
    simp only [Fin.val_zero, add_zero, zero_mul, Finset.sum_const_zero, zero_add]
    field_simp
  · -- `B₀ x_{n+K} xₙ = a`, period `2K`
    refine ⟨2 * (k + 1), by omega, fun u hu => periodic_of_sq E fun n => ?_⟩
    have hB := hA.B0_pos
    refine step_two (c := E.a / E.B 0) (sq_pos E hu) (fun n => ?_) n
    have := rec_astar E hA hu n
    rw [sum_zero E hA hz] at this
    field_simp
    linarith
  · -- `B₀ x_{n+2m} xₙ = A_m x_{n+m}`, period `6m`
    have hB := hA.B0_pos
    have hmk : m < k + 1 := by omega
    have hcpos : 0 < coef E m := by
      have := a_sum_pos E
      rw [sum_one E hA hmk hz, ha0] at this
      linarith
    refine ⟨6 * m, by omega, fun u hu => periodic_of_sq E fun n => ?_⟩
    refine step_six (c := coef E m / E.B 0) (div_pos hcpos hB) (sq_pos E hu) (fun n => ?_) n
    have := rec_astar E hA hu n
    rw [sum_one E hA hmk hz, ha0, show n + (k + 1) = n + 2 * m by omega] at this
    field_simp
    linarith
  · -- Lyness unfolded, period `5m`
    have hB := hA.B0_pos
    have hmk : m < k + 1 := by omega
    have hcpos : 0 < coef E m := by
      have hs := a_sum_pos E
      rw [sum_one E hA hmk hz] at hs
      rcases (coef_nonneg E m).lt_or_eq with h' | h'
      · exact h'
      · exfalso
        rw [← h'] at hcm hs
        have : E.a = 0 := by
          rcases (by simpa using hcm : E.a = 0 ∨ E.B 0 = 0) with h'' | h''
          · exact h''
          · exact absurd h'' hB.ne'
        linarith
    refine ⟨5 * m, by omega, fun u hu => periodic_of_sq E fun n => ?_⟩
    refine step_five (c := coef E m / E.B 0) (div_pos hcpos hB) (sq_pos E hu) (fun n => ?_) n
    have := rec_astar E hA hu n
    rw [sum_one E hA hmk hz, show n + (k + 1) = n + 2 * m by omega] at this
    field_simp
    linear_combination E.B 0 * this + hcm
  · -- the period-8 equation unfolded, period `8m`
    have hB := hA.B0_pos
    have hm1 : 1 ≤ m := by omega
    have h2k : 2 * m < k + 1 := by omega
    have hcpos : 0 < coef E m := by
      have hs := a_sum_pos E
      rw [sum_two E hA hm1 h2k hz, h2m] at hs
      rcases (coef_nonneg E m).lt_or_eq with h' | h'
      · exact h'
      · exfalso
        rw [← h'] at hcm hs
        have : E.a = 0 := by
          rcases (by simpa using hcm : E.a = 0 ∨ E.B 0 = 0) with h'' | h''
          · exact h''
          · exact absurd h'' hB.ne'
        linarith
    refine ⟨8 * m, by omega, fun u hu => periodic_of_sq E fun n => ?_⟩
    refine step_eight (c := coef E m / E.B 0) (div_pos hcpos hB) (sq_pos E hu) (fun n => ?_) n
    have := rec_astar E hA hu n
    rw [sum_two E hA hm1 h2k hz, h2m, show n + (k + 1) = n + 3 * m by omega] at this
    field_simp
    linear_combination E.B 0 * this + hcm

end Problem11
end PeriodicDifference
