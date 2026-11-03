/-
# Gasull's Problem 11: a structural theorem for every order `k`

Companion to `PeriodicDifference/PeriodicMobius.lean`, which handles the case `k = 1`.

Setting (Gasull, arXiv:2012.02524v1, §2.8, Problem 11): the order-`(k+1)` rational
difference equation

  `x_{n+k+1} = (a + Σ_j A j * x_{n+j}) / (b + Σ_j B j * x_{n+j})`,   `j : Fin (k+1)`,

with all coefficients `≥ 0`, `a + Σ A > 0`, `b + Σ B > 0`.  Here `A 0` and `B 0`
are the coefficients of the *oldest* term `x_n` (the paper's `A₁`, `B₁`), and
`a`, `b` are the paper's `A₀`, `B₀`.

We work with the state map `F u = (u₁, …, u_k, g u)` on `Ω = (0,∞)^{k+1}`; the
equation is `p`-periodic exactly when `F^[p] = id` on `Ω`.

The main results:

* `Eqn.dichotomy` — if `F` is *surjective* onto `Ω` (which `F^[p] = id` implies),
  then either
    (a) `A 0 = 0`, `b = 0`, and `B j = 0` for every `j ≠ 0`
        — the "reciprocal" shape `x_{n+k+1} = (a + Σ_{j≠0} A j x_{n+j}) / (B 0 * x_n)`;
    (b) `B 0 = 0`, `a = 0`, and `A j = 0` for every `j ≠ 0`
        — the shape `x_{n+k+1} = A 0 * x_n / (b + Σ_{j≠0} B j x_{n+j})`.
  This needs no derivatives, no fixed point, and no Perron–Frobenius: only that
  each state `(1, …, 1, t)` has a preimage.

* `Eqn.trichotomy` — using genuine periodicity (not just surjectivity), branch (b)
  splits further: either it is literally `x_{n+k+1} = x_n` (`A 0 = b`, all the
  other `B j` vanishing), or `Σ_{j≠0} B j > 0` and `A 0 > b`.

The one surviving branch of `trichotomy` is excluded in `PeriodicDifference/KillBStar.lean`,
which then gives the full classification `Eqn.classification`: a `p`-periodic
equation of this family is either of the reciprocal type (a) or is `x_{n+k+1} = xₙ`.
-/

import Mathlib

namespace PeriodicDifference

open Finset

/-! ## The arithmetic core

Everything about the difference equation is squeezed into the following statement
about six nonnegative reals.  Reading `a₁ = A 0`, `b₁ = B 0`,
`T = Σ_{j≠0} A j`, `S = Σ_{j≠0} B j`, the hypothesis `H` says exactly that the
state `(1, …, 1, t)` has a preimage `(u, 1, …, 1)`. -/

/-- **Core lemma.**  Let `a, a₁, T, b, b₁, S ≥ 0` with `a + a₁ + T > 0` and
`b + b₁ + S > 0`.  If for every `t > 0` there is a `u > 0` with
`t * (b + b₁ * u + S) = a + a₁ * u + T`, then either `a₁ = b = S = 0` or
`b₁ = a = T = 0`.

(Only the denominator's positivity `b + b₁ + S > 0` is needed; the corresponding
hypothesis on the numerator plays no role.) -/
theorem core {a a₁ T b b₁ S : ℝ}
    (ha : 0 ≤ a) (ha₁ : 0 ≤ a₁) (hT : 0 ≤ T)
    (hb : 0 ≤ b) (hb₁ : 0 ≤ b₁) (hS : 0 ≤ S)
    (hBpos : 0 < b + b₁ + S)
    (H : ∀ t : ℝ, 0 < t → ∃ u : ℝ, 0 < u ∧ t * (b + b₁ * u + S) = a + a₁ * u + T) :
    (a₁ = 0 ∧ b = 0 ∧ S = 0) ∨ (b₁ = 0 ∧ a = 0 ∧ T = 0) := by
  rcases eq_or_lt_of_le ha₁ with ha₁0 | ha₁pos
  · -- `a₁ = 0`
    rcases eq_or_lt_of_le hb₁ with hb₁0 | hb₁pos
    · -- `a₁ = b₁ = 0`: the equation cannot hold for two different `t`.
      exfalso
      obtain ⟨u₁, _, e₁⟩ := H 1 one_pos
      obtain ⟨u₂, _, e₂⟩ := H 2 two_pos
      -- `b + S = a + T` and `2 * (b + S) = a + T`, so `b + S = 0`.
      have h1 : b + S = a + T := by nlinarith [e₁]
      have h2 : 2 * (b + S) = a + T := by nlinarith [e₂]
      have : b + S = 0 := by linarith
      linarith
    · -- `a₁ = 0 < b₁`: forced into branch (a).
      left
      have key : ∀ t : ℝ, 0 < t → t * (b + S) < a + T := by
        intro t ht
        obtain ⟨u, hu, e⟩ := H t ht
        rw [← ha₁0] at e
        nlinarith [mul_pos (mul_pos ht hb₁pos) hu]
      have hbS : b + S ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        have ht : (0:ℝ) < (|a + T| + 1) / (b + S) := by positivity
        have := key _ ht
        rw [div_mul_cancel₀ _ hcon.ne'] at this
        have := le_abs_self (a + T)
        linarith
      exact ⟨ha₁0.symm, by linarith, by linarith⟩
  · -- `0 < a₁`
    rcases eq_or_lt_of_le hb₁ with hb₁0 | hb₁pos
    · -- `b₁ = 0 < a₁`: forced into branch (b).
      right
      have key : ∀ t : ℝ, 0 < t → a + T < t * (b + S) := by
        intro t ht
        obtain ⟨u, hu, e⟩ := H t ht
        rw [← hb₁0] at e
        nlinarith [mul_pos ha₁pos hu]
      have haT : a + T ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        have hd : (0:ℝ) < b + S + 1 := by linarith
        have ht : (0:ℝ) < (a + T) / (b + S + 1) := by positivity
        have hlt := key _ ht
        rw [div_mul_eq_mul_div, lt_div_iff₀ hd] at hlt
        nlinarith
      exact ⟨hb₁0.symm, by linarith, by linarith⟩
    · -- `0 < a₁` and `0 < b₁`: impossible.
      exfalso
      set lam : ℝ := a₁ / b₁ with hlam
      have hlampos : 0 < lam := by positivity
      have hlb : lam * b₁ = a₁ := by rw [hlam]; field_simp
      -- At `t = lam` the unknown `u` drops out, forcing `lam * (b + S) = a + T`.
      obtain ⟨u, hu, e⟩ := H lam hlampos
      have hid : lam * (b + S) = a + T := by nlinarith [e, hlb]
      -- At `t = lam + 1` we then get `(b + S) + b₁ * u' = 0`, absurd.
      obtain ⟨u', hu', e'⟩ := H (lam + 1) (by linarith)
      nlinarith [e', hid, hlb, mul_pos hb₁pos hu']

/-! ## The difference equation and its state map -/

/-- Coefficients of an order-`(k+1)` rational difference equation of Gasull's
family.  `A j` (resp. `B j`) is the coefficient of `x_{n+j}`; `a` and `b` are the
constant terms. -/
structure Eqn (k : ℕ) where
  a : ℝ
  A : Fin (k + 1) → ℝ
  b : ℝ
  B : Fin (k + 1) → ℝ
  a_nonneg : 0 ≤ a
  A_nonneg : ∀ j, 0 ≤ A j
  b_nonneg : 0 ≤ b
  B_nonneg : ∀ j, 0 ≤ B j
  a_pos : 0 < a + ∑ j, A j
  b_pos : 0 < b + ∑ j, B j

variable {k : ℕ}

/-- A state has all coordinates positive. -/
def Pos (u : Fin (k + 1) → ℝ) : Prop := ∀ j, 0 < u j

namespace Eqn

/-- Numerator of the right-hand side, evaluated at a state. -/
def num (E : Eqn k) (u : Fin (k + 1) → ℝ) : ℝ := E.a + ∑ j, E.A j * u j

/-- Denominator of the right-hand side, evaluated at a state. -/
def den (E : Eqn k) (u : Fin (k + 1) → ℝ) : ℝ := E.b + ∑ j, E.B j * u j

/-- The new value produced from a state. -/
noncomputable def g (E : Eqn k) (u : Fin (k + 1) → ℝ) : ℝ := E.num u / E.den u

/-- The state map: shift left and append the new value. -/
noncomputable def F (E : Eqn k) (u : Fin (k + 1) → ℝ) : Fin (k + 1) → ℝ :=
  Fin.snoc (Fin.tail u) (E.g u)

/-- A nonnegative family with positive total sum has a positive member. -/
private lemma exists_pos_of_sum_pos {C : Fin (k + 1) → ℝ} (hC : ∀ j, 0 ≤ C j)
    (h : 0 < ∑ j, C j) : ∃ j, 0 < C j := by
  by_contra hcon
  push_neg at hcon
  have : ∑ j, C j = 0 := Finset.sum_eq_zero fun j _ => le_antisymm (hcon j) (hC j)
  linarith

lemma num_pos (E : Eqn k) {u : Fin (k + 1) → ℝ} (hu : Pos u) : 0 < E.num u := by
  have hnn : 0 ≤ ∑ j, E.A j * u j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (E.A_nonneg j) (hu j).le
  rcases eq_or_lt_of_le E.a_nonneg with h | h
  · have hsum : 0 < ∑ j, E.A j := by have := E.a_pos; linarith
    obtain ⟨j₀, hj₀⟩ := exists_pos_of_sum_pos E.A_nonneg hsum
    have : 0 < ∑ j, E.A j * u j :=
      Finset.sum_pos' (fun j _ => mul_nonneg (E.A_nonneg j) (hu j).le)
        ⟨j₀, Finset.mem_univ _, mul_pos hj₀ (hu j₀)⟩
    simp only [num]; linarith
  · simp only [num]; linarith

lemma den_pos (E : Eqn k) {u : Fin (k + 1) → ℝ} (hu : Pos u) : 0 < E.den u := by
  have hnn : 0 ≤ ∑ j, E.B j * u j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (E.B_nonneg j) (hu j).le
  rcases eq_or_lt_of_le E.b_nonneg with h | h
  · have hsum : 0 < ∑ j, E.B j := by have := E.b_pos; linarith
    obtain ⟨j₀, hj₀⟩ := exists_pos_of_sum_pos E.B_nonneg hsum
    have : 0 < ∑ j, E.B j * u j :=
      Finset.sum_pos' (fun j _ => mul_nonneg (E.B_nonneg j) (hu j).le)
        ⟨j₀, Finset.mem_univ _, mul_pos hj₀ (hu j₀)⟩
    simp only [den]; linarith
  · simp only [den]; linarith

lemma g_pos (E : Eqn k) {u : Fin (k + 1) → ℝ} (hu : Pos u) : 0 < E.g u :=
  div_pos (E.num_pos hu) (E.den_pos hu)

lemma F_pos (E : Eqn k) {u : Fin (k + 1) → ℝ} (hu : Pos u) : Pos (E.F u) := by
  intro j
  refine Fin.lastCases ?_ ?_ j
  · simpa [F] using E.g_pos hu
  · intro i; simpa [F, Fin.tail] using hu i.succ

lemma F_iterate_pos (E : Eqn k) {u : Fin (k + 1) → ℝ} (hu : Pos u) :
    ∀ n, Pos (E.F^[n] u) := by
  intro n
  induction n with
  | zero => simpa using hu
  | succ n ih => rw [Function.iterate_succ_apply']; exact E.F_pos ih

/-- `F^[p] = id` on `Ω` makes `F` surjective onto `Ω`. -/
lemma surjective_of_periodic (E : Eqn k) {p : ℕ} (hp : 0 < p)
    (hper : ∀ u, Pos u → E.F^[p] u = u) :
    ∀ x, Pos x → ∃ u, Pos u ∧ E.F u = x := by
  intro x hx
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  refine ⟨E.F^[m] x, E.F_iterate_pos hx m, ?_⟩
  have h := hper x hx
  rwa [Function.iterate_succ_apply'] at h

/-! ## The dichotomy -/

/-- The state `(1, 1, …, 1, t)`. -/
noncomputable def probe (t : ℝ) : Fin (k + 1) → ℝ := Fin.snoc (fun _ => 1) t

lemma probe_pos {t : ℝ} (ht : 0 < t) : Pos (probe (k := k) t) := by
  intro j
  refine Fin.lastCases ?_ ?_ j
  · simpa [probe] using ht
  · intro i; simp [probe]

/-- **Main structural theorem.**  If every positive state has a positive preimage
under `F`, then the equation is of one of exactly two shapes. -/
theorem dichotomy (E : Eqn k) (hsurj : ∀ x, Pos x → ∃ u, Pos u ∧ E.F u = x) :
    (E.A 0 = 0 ∧ E.b = 0 ∧ ∀ j : Fin k, E.B j.succ = 0) ∨
    (E.B 0 = 0 ∧ E.a = 0 ∧ ∀ j : Fin k, E.A j.succ = 0) := by
  have hT : (0:ℝ) ≤ ∑ j : Fin k, E.A j.succ := Finset.sum_nonneg fun j _ => E.A_nonneg _
  have hS : (0:ℝ) ≤ ∑ j : Fin k, E.B j.succ := Finset.sum_nonneg fun j _ => E.B_nonneg _
  have hBpos : 0 < E.b + E.B 0 + ∑ j : Fin k, E.B j.succ := by
    have h := E.b_pos; rw [Fin.sum_univ_succ] at h; linarith
  -- Feed the states `(1, …, 1, t)` to surjectivity.
  have H : ∀ t : ℝ, 0 < t → ∃ u : ℝ, 0 < u ∧
      t * (E.b + E.B 0 * u + ∑ j : Fin k, E.B j.succ)
        = E.a + E.A 0 * u + ∑ j : Fin k, E.A j.succ := by
    intro t ht
    obtain ⟨v, hv, hFv⟩ := hsurj (probe t) (probe_pos ht)
    -- The preimage must be `(v 0, 1, …, 1)` with `g v = t`.
    have htail : ∀ i : Fin k, v i.succ = 1 := by
      intro i
      have h := congrFun hFv (Fin.castSucc i)
      simpa [F, probe, Fin.tail] using h
    have hgv : E.g v = t := by
      have h := congrFun hFv (Fin.last k)
      simpa [F, probe] using h
    refine ⟨v 0, hv 0, ?_⟩
    have hden : E.den v = E.b + E.B 0 * v 0 + ∑ j : Fin k, E.B j.succ := by
      simp only [den, Fin.sum_univ_succ, htail, mul_one]; ring
    have hnum : E.num v = E.a + E.A 0 * v 0 + ∑ j : Fin k, E.A j.succ := by
      simp only [num, Fin.sum_univ_succ, htail, mul_one]; ring
    have hd : E.den v ≠ 0 := (E.den_pos hv).ne'
    rw [← hden, ← hnum, ← hgv, g, div_mul_cancel₀ _ hd]
  -- Apply the core lemma.
  rcases core E.a_nonneg (E.A_nonneg 0) hT E.b_nonneg (E.B_nonneg 0) hS hBpos H with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1, h2, fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => E.B_nonneg i.succ).mp h3 j (Finset.mem_univ j)⟩
  · exact Or.inr ⟨h1, h2, fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => E.A_nonneg i.succ).mp h3 j (Finset.mem_univ j)⟩

/-- The same conclusion straight from `p`-periodicity. -/
theorem dichotomy_of_periodic (E : Eqn k) {p : ℕ} (hp : 0 < p)
    (hper : ∀ u, Pos u → E.F^[p] u = u) :
    (E.A 0 = 0 ∧ E.b = 0 ∧ ∀ j : Fin k, E.B j.succ = 0) ∨
    (E.B 0 = 0 ∧ E.a = 0 ∧ ∀ j : Fin k, E.A j.succ = 0) :=
  E.dichotomy (E.surjective_of_periodic hp hper)

/-! ## Refining branch (b) using genuine periodicity

The sum of the coordinates is a strict Lyapunov function whenever `g u` is always
below (or always above) the oldest coordinate `u 0`. -/

private lemma sum_F (E : Eqn k) (u : Fin (k + 1) → ℝ) :
    ∑ j, E.F u j = (∑ i : Fin k, u i.succ) + E.g u := by
  simp [F, Fin.sum_univ_castSucc, Fin.tail]

private lemma sum_F_sub (E : Eqn k) (u : Fin (k + 1) → ℝ) :
    ∑ j, E.F u j = (∑ j, u j) - u 0 + E.g u := by
  rw [E.sum_F, Fin.sum_univ_succ (f := u)]
  ring

/-- If `g u < u 0` always, no positive state can be periodic. -/
lemma not_periodic_of_lt (E : Eqn k) {p : ℕ} (hp : 0 < p)
    (hper : ∀ u, Pos u → E.F^[p] u = u)
    (hlt : ∀ u, Pos u → E.g u < u 0) : False := by
  set u₀ : Fin (k + 1) → ℝ := fun _ => 1 with hu₀
  have hu₀pos : Pos u₀ := fun _ => one_pos
  have step : ∀ n, 0 < n → ∑ j, E.F^[n] u₀ j < ∑ j, u₀ j := by
    intro n
    induction n with
    | zero => intro h; exact absurd h (lt_irrefl 0)
    | succ m ih =>
      intro _
      have hposm := E.F_iterate_pos hu₀pos m
      have hstep := hlt _ hposm
      rw [Function.iterate_succ_apply', E.sum_F_sub]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp only [Function.iterate_zero_apply] at hstep ⊢
        linarith
      · have hih := ih hm; linarith
  have := step p hp
  rw [hper u₀ hu₀pos] at this
  exact lt_irrefl _ this

/-- If `u 0 < g u` always, no positive state can be periodic. -/
lemma not_periodic_of_gt (E : Eqn k) {p : ℕ} (hp : 0 < p)
    (hper : ∀ u, Pos u → E.F^[p] u = u)
    (hgt : ∀ u, Pos u → u 0 < E.g u) : False := by
  set u₀ : Fin (k + 1) → ℝ := fun _ => 1 with hu₀
  have hu₀pos : Pos u₀ := fun _ => one_pos
  have step : ∀ n, 0 < n → ∑ j, u₀ j < ∑ j, E.F^[n] u₀ j := by
    intro n
    induction n with
    | zero => intro h; exact absurd h (lt_irrefl 0)
    | succ m ih =>
      intro _
      have hposm := E.F_iterate_pos hu₀pos m
      have hstep := hgt _ hposm
      rw [Function.iterate_succ_apply', E.sum_F_sub]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp only [Function.iterate_zero_apply] at hstep ⊢
        linarith
      · have hih := ih hm; linarith
  have := step p hp
  rw [hper u₀ hu₀pos] at this
  exact lt_irrefl _ this

/-- **Trichotomy.**  For a genuinely `p`-periodic equation, branch (b) of
`dichotomy` splits: either the equation is literally `x_{n+k+1} = x_n`, or the
denominator really involves a later term and `A 0 > b`. -/
theorem trichotomy (E : Eqn k) {p : ℕ} (hp : 0 < p)
    (hper : ∀ u, Pos u → E.F^[p] u = u) :
    (E.A 0 = 0 ∧ E.b = 0 ∧ ∀ j : Fin k, E.B j.succ = 0) ∨
    (E.B 0 = 0 ∧ E.a = 0 ∧ (∀ j : Fin k, E.A j.succ = 0) ∧
      (∀ j : Fin k, E.B j.succ = 0) ∧ E.A 0 = E.b) ∨
    (E.B 0 = 0 ∧ E.a = 0 ∧ (∀ j : Fin k, E.A j.succ = 0) ∧
      0 < ∑ j : Fin k, E.B j.succ ∧ E.b < E.A 0) := by
  rcases E.dichotomy_of_periodic hp hper with hA | ⟨hB0, ha, hA0⟩
  · exact Or.inl hA
  -- Branch (b): `num u = A 0 * u 0` and `den u = b + Σ_{j≠0} B j * u j`.
  have hnum : ∀ u : Fin (k + 1) → ℝ, E.num u = E.A 0 * u 0 := by
    intro u
    simp only [num, Fin.sum_univ_succ, ha, hA0, zero_mul, zero_add,
      Finset.sum_const_zero, add_zero]
  have hden : ∀ u : Fin (k + 1) → ℝ,
      E.den u = E.b + ∑ i : Fin k, E.B i.succ * u i.succ := by
    intro u
    simp only [den, Fin.sum_univ_succ, hB0, zero_mul, zero_add]
  have hSnn : (0:ℝ) ≤ ∑ j : Fin k, E.B j.succ :=
    Finset.sum_nonneg fun j _ => E.B_nonneg _
  rcases eq_or_lt_of_le hSnn with hS0 | hSpos
  · -- `Σ_{j≠0} B j = 0`: the equation is `x_{n+k+1} = (A 0 / b) * x_n`.
    have hBsucc : ∀ j : Fin k, E.B j.succ = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => E.B_nonneg i.succ).mp hS0.symm j
        (Finset.mem_univ j)
    have hbpos : 0 < E.b := by
      have h := E.b_pos
      rw [Fin.sum_univ_succ, hB0, ← hS0] at h
      linarith
    have hdenb : ∀ u : Fin (k + 1) → ℝ, E.den u = E.b := by
      intro u
      rw [hden u]
      have : ∑ i : Fin k, E.B i.succ * u i.succ = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hBsucc i]; ring
      rw [this]; ring
    refine Or.inr (Or.inl ⟨hB0, ha, hA0, hBsucc, ?_⟩)
    -- `A 0 = b`, else the coordinate sum is a strict Lyapunov function.
    rcases lt_trichotomy (E.A 0) E.b with h | h | h
    · exact (E.not_periodic_of_lt hp hper (fun u hu => by
        rw [g, hnum u, hdenb u, div_lt_iff₀ hbpos]
        nlinarith [hu 0])).elim
    · exact h
    · exact (E.not_periodic_of_gt hp hper (fun u hu => by
        rw [g, hnum u, hdenb u, lt_div_iff₀ hbpos]
        nlinarith [hu 0])).elim
  · -- `Σ_{j≠0} B j > 0`: then `A 0 > b`, else `g u < u 0` always.
    right; right
    refine ⟨hB0, ha, hA0, hSpos, ?_⟩
    by_contra hcon
    push_neg at hcon  -- `E.A 0 ≤ E.b`
    refine E.not_periodic_of_lt hp hper (fun u hu => ?_)
    have hd : 0 < E.den u := E.den_pos hu
    have hextra : 0 < ∑ i : Fin k, E.B i.succ * u i.succ := by
      obtain ⟨j₀, hj₀⟩ : ∃ j : Fin k, 0 < E.B j.succ := by
        by_contra hc
        push_neg at hc
        have : ∑ j : Fin k, E.B j.succ = 0 :=
          Finset.sum_eq_zero fun j _ => le_antisymm (hc j) (E.B_nonneg _)
        linarith
      exact Finset.sum_pos' (fun i _ => mul_nonneg (E.B_nonneg _) (hu _).le)
        ⟨j₀, Finset.mem_univ _, mul_pos hj₀ (hu _)⟩
    rw [g, hnum u, div_lt_iff₀ hd, hden u]
    nlinarith [hu 0, mul_pos (hu 0) hextra]

end Eqn

end PeriodicDifference
