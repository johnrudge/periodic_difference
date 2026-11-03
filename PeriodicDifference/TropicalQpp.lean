/-
# `PeriodicDifference/TropicalQpp.lean` — Theorem Q″: certificates on **tied** carriers

An earlier Theorem Q needed a *tie-free* periodic orbit of the
min-plus map: at every step exactly one slot attains the minimum.  Tie-free orbits are rare
and often long.

Theorem Q″ removes the tie-freeness.  Along a periodic orbit `E` with argmin **sets**
`A_t` (ties welcome), the one-sided directional derivative of `T` is
`Φ_t(d) = (d_1,…,d_{k-1}, μ_t(d) − d_0)` with `μ_t(d) = min_{a ∈ A_t} val_d(a)`.
If some integer vector has an unbounded `Φ`-orbit, then `T^p ≠ id` for every `p ≥ 1`, and the
periodicity of the degeneration (`thm:P`) rules out the support for every choice of positive
coefficients.

The checkable certificate designates a slot `σ_t ∈ A_t` at each step, which makes the
linearisation the *linear* map `Λ_{σ_t}`, and asks for

* `Λ h = h + δ` and `Λ δ = δ` over one period — the affine pair, exactly Theorem Q's
  Jordan pair `(V, W)`;
* `δ ≠ 0`;
* the **weak margins**: `σ_t` attains the minimum over `A_t` on the orbits of both `h`
  and `δ`.

The margins are the whole point.  With them, `val_{h + m·δ}(σ_t) ≤ val_{h + m·δ}(a)`
for every `a ∈ A_t` and every `m ≥ 0` — a nonnegative combination of two inequalities
— so `Φ_t` agrees with `Λ_{σ_t}` along the entire ray and induction gives
`d^{(mq)} = h + m·δ` for **all** `m`.  Without them one can only run the tangent map
for finitely many periods, which is an observation rather than a proof.

## The structure

The word-driven run below is generic in the word: none of `runW_E`, `runW_len`,
`dOf_lin` or `uOf_lin` knows that the word is an argmin word; that is what lets a *tied*
step be linearised along a designated slot.

The perturbation lemma `pert_agree_tied` requires only that the designated slot `σ n`
attains on `e` and beats every other attaining slot on `d`; the integer gap to
*non*-attaining slots is automatic over `ℤ`.  With it, `not_tropPeriodic_of_tangent` is the
two-scale argument of `thm:tangent`(i) once and for all: an exact integer solution and a
non-periodic integer tangent orbit along it show that no power `T^p` of the min-plus map is the
identity (`TropPeriodic`); `not_globallyPeriodic_of_tangent` adds `theoremP` to rule out global
periodicity of the equation (`thm:tangent`(ii)), and `GloballyPeriodic.tropPeriodic` is that
step on its own.  Theorem Q″ (`not_tropPeriodic_of_certPP`), the carrier rays
(`Bump.not_tropPeriodic_of_ray`: the σ-bump and the full support) and the odd orders
(`OddK.not_tropPeriodic_of_vrec`) are its instances, each with a `not_globallyPeriodic` form for
the equation (`not_globallyPeriodic_of_certPP`, `theoremQpp`, …); the min-plus forms give
`cor:trop-nonperiodic` (`PeriodicDifference/TropicalCor.lean`).
-/

import PeriodicDifference.Tropical

namespace PeriodicDifference
namespace Trop

/-! ## Shared helpers: the coupled state, linearised solutions, window chains -/

/-- Coupled state: the exponent window and the two perturbation windows, each of
length `k` (most recent last). -/
structure St where
  E : List ℤ
  D : List ℤ
  U : List ℤ
  deriving DecidableEq

/-- Two solutions of the linearised recursion agreeing on an initial window agree
everywhere.  This is what propagates the certificate's drift relation from the window
to all of `ℕ`, so no linearity-of-the-run bookkeeping is needed. -/
lemma lin_unique {k : ℕ} {wd : ℕ → ℕ} {d d' : ℕ → ℤ} (hwdk : ∀ n, wd n ≤ k)
    (hd : IsLin (k + 1) wd d) (hd' : IsLin (k + 1) wd d')
    (h0 : ∀ i ≤ k, d i = d' i) : ∀ n, d n = d' n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hnk : n ≤ k
    · exact h0 n hnk
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + (k + 1) := ⟨n - (k + 1), by omega⟩
      have h1 := hd m
      have h2 := hd' m
      have hm : d m = d' m := ih m (by omega)
      have hs : slot d m (wd m) = slot d' m (wd m) := by
        by_cases hw : wd m = 0
        · simp [hw, slot]
        · simp only [slot, if_neg hw]
          exact ih (m + wd m) (by have := hwdk m; omega)
      omega

/-- Any integer sequence is bounded on an initial segment. -/
lemma exists_bound (f : ℕ → ℤ) (N : ℕ) : ∃ B : ℤ, 0 ≤ B ∧ ∀ n ≤ N, |f n| ≤ B := by
  induction N with
  | zero =>
    refine ⟨|f 0|, abs_nonneg _, ?_⟩
    intro n hn
    have : n = 0 := by omega
    subst this; exact le_rfl
  | succ N ih =>
    obtain ⟨B, hB0, hB⟩ := ih
    refine ⟨max B |f (N + 1)|, le_trans hB0 (le_max_left _ _), ?_⟩
    intro n hn
    rcases Nat.lt_or_ge n (N + 1) with h | h
    · exact le_trans (hB n (by omega)) (le_max_left _ _)
    · have : n = N + 1 := by omega
      subst this; exact le_max_right _ _


/-- A chain of windows of the shift-append shape reads off a sequence: entry `j` of the
window at time `i` is the head of the window at time `i + j`.  Unlike `getI_winIter`
this does not assume the windows come from *one* window map, so it applies to the
`D`- and `U`-components of a certificate run, whose step depends on the argmin word. -/
lemma getI_chain {W : ℕ → List ℤ} {k : ℕ} (hlen : ∀ i, (W i).length = k + 1)
    (hshift : ∀ i, ∃ v, W (i + 1) = (W i).tail ++ [v]) :
    ∀ j ≤ k, ∀ i, (W i).getI j = (W (i + j)).getI 0 := by
  intro j
  induction j with
  | zero => intro _ i; simp
  | succ j ih =>
    intro hj i
    obtain ⟨v, hv⟩ := hshift i
    have h1 : (W (i + 1)).getI j = (W i).getI (j + 1) := by
      rw [hv]
      have hj' : j < (W i).tail.length := by
        simp [List.length_tail, hlen i]; omega
      rw [List.getI_append _ _ _ hj', getI_tail]
    have hidx : i + 1 + j = i + (j + 1) := by omega
    rw [← h1, ih (by omega) (i + 1), hidx]

/-- If the exponent window returns after `q` steps it is `q`-periodic. -/
lemma winIter_periodic {J : List ℕ} {E0 : List ℤ} {q : ℕ}
    (hq : winIter (shiftApp (fZ J)) E0 q = E0) :
    ∀ n, winIter (shiftApp (fZ J)) E0 (n + q) = winIter (shiftApp (fZ J)) E0 n := by
  intro n
  induction n with
  | zero => simpa using hq
  | succ n ih =>
    have h : n + 1 + q = (n + q) + 1 := by omega
    rw [h, winIter_succ, winIter_succ, ih]
/-- Slot values on the window are slot values of the sequence. -/
lemma slotW_eq {J : List ℕ} {k : ℕ} {E0 : List ℤ} (hE : E0.length = k + 1)
    (hJk : ∀ j ∈ J, j ≤ k) (n : ℕ) {j : ℕ} (hj : j ∈ J) :
    (if j = 0 then (0:ℤ) else (winIter (shiftApp (fZ J)) E0 n).getI j)
      = slot (seqOf (fZ J) E0) n j := by
  by_cases hj0 : j = 0
  · simp [hj0, slot]
  · simp only [if_neg hj0, slot]
    exact getI_winIter hE j (hJk j hj) n

lemma getI_zipWith (f : ℤ → ℤ → ℤ) {A B : List ℤ} (h : A.length = B.length) {i : ℕ}
    (hi : i < A.length) :
    (List.zipWith f A B).getI i = f (A.getI i) (B.getI i) := by
  have hz : i < (List.zipWith f A B).length := by
    rw [List.length_zipWith]; omega
  rw [List.getI_eq_getElem _ hz, List.getI_eq_getElem _ hi,
    List.getI_eq_getElem _ (by omega : i < B.length), List.getElem_zipWith]

lemma getI_zipWith_add {A B : List ℤ} (h : A.length = B.length) {i : ℕ}
    (hi : i < A.length) :
    (List.zipWith (· + ·) A B).getI i = A.getI i + B.getI i :=
  getI_zipWith _ h hi

/-! ## The word-driven coupled run

`St` carries the exponent window `E` and two perturbation windows `D` and `U`.  A
step advances `E` by the true min-plus map `fZ` (ties or not) and advances `D` and `U`
by the linear map attached to the designated slot `a`.
-/

/-- The slot value read off a window: slot `0` is the constant slot, worth `0`. -/
def slotW (w : List ℤ) (j : ℕ) : ℤ := if j = 0 then 0 else w.getI j

@[simp] lemma slotW_zero (w : List ℤ) : slotW w 0 = 0 := rfl

lemma slotW_of_ne {w : List ℤ} {j : ℕ} (hj : j ≠ 0) : slotW w j = w.getI j := by
  simp [slotW, hj]

/-- One coupled step with the linearisation slot **dictated** by `a` rather than
recomputed (Theorem Q's step failed unless the argmin was unique). -/
def stepW (J : List ℕ) (a : ℕ) (s : St) : St :=
  ⟨shiftApp (fZ J) s.E,
   s.D.tail ++ [slotW s.D a - s.D.getI 0],
   s.U.tail ++ [slotW s.U a - s.U.getI 0]⟩

/-- Run the coupled step along the word `w`. -/
def runW (J : List ℕ) (w : ℕ → ℕ) (s0 : St) : ℕ → St
  | 0 => s0
  | (n + 1) => stepW J (w n) (runW J w s0 n)

@[simp] lemma runW_zero (J : List ℕ) (w : ℕ → ℕ) (s0 : St) : runW J w s0 0 = s0 := rfl

lemma runW_succ (J : List ℕ) (w : ℕ → ℕ) (s0 : St) (n : ℕ) :
    runW J w s0 (n + 1) = stepW J (w n) (runW J w s0 n) := rfl

/-- The exponent component is the plain min-plus window: the word never touches it. -/
lemma runW_E (J : List ℕ) (w : ℕ → ℕ) (s0 : St) : ∀ n,
    (runW J w s0 n).E = winIter (shiftApp (fZ J)) s0.E n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [runW_succ]; show shiftApp (fZ J) _ = _; rw [ih, winIter_succ]

/-- Both perturbation windows keep their length. -/
lemma runW_len {J : List ℕ} {w : ℕ → ℕ} {s0 : St} {k : ℕ}
    (hD : s0.D.length = k + 1) (hU : s0.U.length = k + 1) : ∀ n,
    (runW J w s0 n).D.length = k + 1 ∧ (runW J w s0 n).U.length = k + 1 := by
  intro n
  induction n with
  | zero => exact ⟨hD, hU⟩
  | succ n ih =>
    rw [runW_succ]
    refine ⟨?_, ?_⟩
    · show ((runW J w s0 n).D.tail ++ _).length = k + 1
      simp [List.length_tail, ih.1]
    · show ((runW J w s0 n).U.tail ++ _).length = k + 1
      simp [List.length_tail, ih.2]

/-! ### The sequences carried by a run -/

/-- The drifting solution of the linearisation. -/
def dOf (J : List ℕ) (w : ℕ → ℕ) (s0 : St) (n : ℕ) : ℤ := (runW J w s0 n).D.getI 0

/-- The drift: a solution of the same linearisation, fixed over a period. -/
def uOf (J : List ℕ) (w : ℕ → ℕ) (s0 : St) (n : ℕ) : ℤ := (runW J w s0 n).U.getI 0

section Seq
variable {J : List ℕ} {w : ℕ → ℕ} {s0 : St} {k : ℕ}
  (hD : s0.D.length = k + 1) (hU : s0.U.length = k + 1)
include hD hU

lemma dOf_getI : ∀ j ≤ k, ∀ n, (runW J w s0 n).D.getI j = dOf J w s0 (n + j) := by
  apply getI_chain (fun i => (runW_len hD hU i).1)
  intro i; exact ⟨_, rfl⟩

lemma uOf_getI : ∀ j ≤ k, ∀ n, (runW J w s0 n).U.getI j = uOf J w s0 (n + j) := by
  apply getI_chain (fun i => (runW_len hD hU i).2)
  intro i; exact ⟨_, rfl⟩

/-- `dOf` solves the recursion linearised along `w`.  Nothing here uses that `w` is
an argmin word — only that it lands in range. -/
lemma dOf_lin (hwk : ∀ n, w n ≤ k) : IsLin (k + 1) w (dOf J w s0) := by
  intro n
  have htl : (runW J w s0 n).D.tail.length = k := by
    simp [List.length_tail, (runW_len hD hU n).1]
  have hlast : (runW J w s0 (n + 1)).D.getI k
      = slotW (runW J w s0 n).D (w n) - (runW J w s0 n).D.getI 0 := by
    rw [runW_succ]
    show ((runW J w s0 n).D.tail ++ _).getI k = _
    rw [List.getI_append_right _ _ _ (by omega), htl]
    simp
  have h1 : (runW J w s0 (n + 1)).D.getI k = dOf J w s0 (n + (k + 1)) := by
    rw [dOf_getI hD hU k le_rfl (n + 1)]; congr 1; omega
  have h3 : (runW J w s0 n).D.getI 0 = dOf J w s0 n := by
    have := dOf_getI (J := J) (w := w) hD hU 0 (by omega) n; simpa using this
  rw [h1] at hlast
  rw [hlast, h3, slot, slotW]
  by_cases h0 : w n = 0
  · simp [h0]
  · rw [if_neg h0, if_neg h0, dOf_getI hD hU _ (hwk n) n]; omega

lemma uOf_lin (hwk : ∀ n, w n ≤ k) : IsLin (k + 1) w (uOf J w s0) := by
  intro n
  have htl : (runW J w s0 n).U.tail.length = k := by
    simp [List.length_tail, (runW_len hD hU n).2]
  have hlast : (runW J w s0 (n + 1)).U.getI k
      = slotW (runW J w s0 n).U (w n) - (runW J w s0 n).U.getI 0 := by
    rw [runW_succ]
    show ((runW J w s0 n).U.tail ++ _).getI k = _
    rw [List.getI_append_right _ _ _ (by omega), htl]
    simp
  have h1 : (runW J w s0 (n + 1)).U.getI k = uOf J w s0 (n + (k + 1)) := by
    rw [uOf_getI hD hU k le_rfl (n + 1)]; congr 1; omega
  have h3 : (runW J w s0 n).U.getI 0 = uOf J w s0 n := by
    have := uOf_getI (J := J) (w := w) hD hU 0 (by omega) n; simpa using this
  rw [h1] at hlast
  rw [hlast, h3, slot, slotW]
  by_cases h0 : w n = 0
  · simp [h0]
  · rw [if_neg h0, if_neg h0, uOf_getI hD hU _ (hwk n) n]; omega

end Seq

/-! ## The tie-tolerant perturbation lemma

The minimum may be attained many times; the designated slot `wd n` must attain on `e`
and beat every other attaining slot on `d`.

The gap to slots that do **not** attain is automatic: the values are integers, so a
slot that is not equal to the minimum exceeds it by at least `1`.  That is exactly the
GAP the paper's Lemma 1 uses, and here it costs no hypothesis at all.
-/

lemma pert_agree_tied {J : List ℕ} {k N : ℕ} (hJ : J ≠ []) (hJk : ∀ j ∈ J, j ≤ k)
    {e d g : ℕ → ℤ} {wd : ℕ → ℕ} {c B : ℤ}
    (he : IsTrop (k + 1) J e) (hg : IsTrop (k + 1) J g)
    (hwd : ∀ n < N, wd n ∈ J ∧ slot e n (wd n) = mval J e n ∧
        ∀ j ∈ J, slot e n j = mval J e n → slot d n (wd n) ≤ slot d n j)
    (hd : ∀ n < N, d (n + (k + 1)) + d n = slot d n (wd n))
    (hB : ∀ n ≤ N + k, |d n| ≤ B) (hc : 2 * B < c)
    (hinit : ∀ i ≤ k, g i = c * e i + d i) :
    ∀ n ≤ N + k, g n = c * e n + d n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hnk : n ≤ k
    · exact hinit n hnk
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + (k + 1) := ⟨n - (k + 1), by omega⟩
      have hmN : m < N := by omega
      obtain ⟨hwdJ, hwdmin, hwdmarg⟩ := hwd m hmN
      have hwin : ∀ j ≤ k, g (m + j) = c * e (m + j) + d (m + j) :=
        fun j hj => ih (m + j) (by omega) (by omega)
      have hslot : ∀ j ∈ J, slot g m j = c * slot e m j + slot d m j := by
        intro j hj
        by_cases hj0 : j = 0
        · simp [hj0, slot]
        · simp only [slot, if_neg hj0]
          exact hwin j (hJk j hj)
      have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 (by omega))
      have hcpos : 0 < c := by linarith
      have hsd : ∀ j ∈ J, |slot d m j| ≤ B := by
        intro j hj
        by_cases hj0 : j = 0
        · simpa [hj0, slot] using hB0
        · simp only [slot, if_neg hj0]
          exact hB (m + j) (by have := hJk j hj; omega)
      -- the minimum for `g` is attained inside the argmin SET, and there at `wd m`
      have hmin : mval J g m = c * mval J e m + slot d m (wd m) := by
        have hle : mval J g m ≤ c * mval J e m + slot d m (wd m) := by
          have h := mval_le (e := g) (n := m) hwdJ
          rw [hslot _ hwdJ, hwdmin] at h
          exact h
        obtain ⟨j, hjJ, hjeq⟩ := mval_attained (e := g) (n := m) hJ
        rcases eq_or_lt_of_le (mval_le (e := e) (n := m) hjJ) with heq | hlt
        · -- `j` attains on `e`: the margin condition puts `wd m` no higher
          have hmarg := hwdmarg j hjJ heq.symm
          rw [hjeq, hslot _ hjJ, ← heq]
          exact le_antisymm (by rw [hjeq, hslot _ hjJ, ← heq] at hle; exact hle)
            (by linarith)
        · -- `j` misses on `e`: integrality gives a gap of at least `1`, which the
          -- scale `c > 2B` cannot be beaten by the perturbation
          exfalso
          have h1 : mval J e m + 1 ≤ slot e m j := Int.add_one_le_iff.mpr hlt
          have habs2 := abs_le.mp (hsd j hjJ)
          have habs3 := abs_le.mp (hsd _ hwdJ)
          rw [hjeq, hslot _ hjJ] at hle
          have hmul : c * mval J e m + c ≤ c * slot e m j := by
            calc c * mval J e m + c = c * (mval J e m + 1) := by ring
              _ ≤ c * slot e m j := mul_le_mul_of_nonneg_left h1 hcpos.le
          linarith [habs2.1, habs2.2, habs3.1, habs3.2]
      have hge := he m
      have hgg := hg m
      have hdm := hd m hmN
      rw [hmin] at hgg
      have hgm : g m = c * e m + d m := by
        have := hwin 0 (by omega); simpa using this
      have hexp : c * mval J e m = c * e (m + (k + 1)) + c * e m := by
        rw [← hge]; ring
      linarith [hgg, hdm, hgm, hexp]


/-! ## The two-scale tangent argument (`thm:tangent`)

An integer tangent orbit `d` along an exact integer solution `E` of the min-plus recursion,
which is **not periodic**, rules out global periodicity for every positive coefficient choice
on the slot list.  Theorem Q″ (`theoremQpp`), the σ-bump (`Bump.not_globallyPeriodic_of_bumpSat`)
and the odd orders (`OddK.not_globallyPeriodic_of_vrec`) are all instances. -/

/-- The first `k + 1` terms of a sequence, as a window. -/
def window (f : ℕ → ℤ) (k : ℕ) : List ℤ := (List.range (k + 1)).map f

@[simp] lemma window_length (f : ℕ → ℤ) (k : ℕ) : (window f k).length = k + 1 := by
  simp [window]

lemma window_getI (f : ℕ → ℤ) (k : ℕ) {i : ℕ} (hi : i ≤ k) : (window f k).getI i = f i := by
  have hlt : i < (window f k).length := by rw [window_length]; omega
  rw [List.getI_eq_getElem _ hlt]
  simp [window]

lemma seqOf_window {J : List ℕ} {k : ℕ} (f : ℕ → ℤ) {i : ℕ} (hi : i ≤ k) :
    seqOf (fZ J) (window f k) i = f i := by
  have h := getI_winIter (f := fZ J) (window_length f k) i hi 0
  rw [← window_getI f k hi]
  simpa using h.symm

/-- `d` is an integer tangent orbit along `E` for the slot list `J` at order `k`: at every
time some slot `w ∈ J` attains the minimum of `E`, minimises `d` among the attaining slots,
and gives the tangent recursion. -/
def TanAlong (k : ℕ) (J : List ℕ) (E d : ℕ → ℤ) : Prop :=
  ∀ n, ∃ w ∈ J, slot E n w = mval J E n ∧
    (∀ j ∈ J, slot E n j = mval J E n → slot d n w ≤ slot d n j) ∧
    d (n + k) + d n = slot d n w

/-- The min-plus map has `p`-th power the identity on integer windows: every integer solution
of the recursion is `p`-periodic. -/
def TropPeriodic (k : ℕ) (J : List ℕ) (p : ℕ) : Prop :=
  ∀ e : ℕ → ℤ, IsTrop k J e → ∀ n, e (n + p) = e n

/-- **`thm:tangent`.**  If `E` is an integer solution and `d` an integer tangent orbit along
it that is not `p`-periodic (witnessed on a multiple `n + m·p`), then the min-plus map does
not have `p`-th power the identity.  Two scales: the solution started at `(2B+1)·E + d` stays
on that ray (`pert_agree_tied`), and it and `E` would both be `p`-periodic. -/
theorem not_tropPeriodic_of_tangent {k' : ℕ} {J : List ℕ} (hJne : J ≠ [])
    (hJk : ∀ j ∈ J, j ≤ k')
    {E d : ℕ → ℤ} (hE : IsTrop (k' + 1) J E) (hd : TanAlong (k' + 1) J E d)
    {p : ℕ} (hnp : ∃ m n, d (n + m * p) ≠ d n) :
    ¬ TropPeriodic (k' + 1) J p := by
  intro hper
  obtain ⟨m₀, n₀, hne⟩ := hnp
  have hep := hper _ hE
  choose wd hwJ hwE hwmin hwrec using hd
  obtain ⟨N, hN⟩ : ∃ N, N = n₀ + m₀ * p := ⟨_, rfl⟩
  obtain ⟨B, hB0, hB⟩ := exists_bound d (N + k')
  have hcgt : 2 * B < 2 * B + 1 := by omega
  obtain ⟨g, hgtrop, hinit⟩ : ∃ g : ℕ → ℤ, IsTrop (k' + 1) J g ∧
      ∀ i ≤ k', g i = (2 * B + 1) * E i + d i :=
    ⟨seqOf (fZ J) (window (fun i => (2 * B + 1) * E i + d i) k'),
      isTrop_seqOf (window_length _ _) hJk, fun i hi => seqOf_window _ hi⟩
  have hgp := hper _ hgtrop
  have hagree := pert_agree_tied (N := N) hJne hJk hE hgtrop
    (fun n _ => ⟨hwJ n, hwE n, hwmin n⟩) (fun n _ => hwrec n) hB hcgt hinit
  have hDp : ∀ n, n + p ≤ N + k' → d (n + p) = d n := by
    intro n hn
    have h1 := hagree (n + p) hn
    have h2 := hagree n (by omega)
    have h3 := hgp n
    have h4 := hep n
    rw [h1, h2, h4] at h3
    linarith
  have hDmp : ∀ m n, n + m * p ≤ N + k' → d (n + m * p) = d n := by
    intro m
    induction m with
    | zero => intro n _; simp
    | succ m ih =>
      intro n hn
      have h1 : n + (m + 1) * p = (n + m * p) + p := by ring
      rw [h1, hDp _ (by nlinarith), ih n (by nlinarith)]
  exact hne (hDmp m₀ n₀ (by omega))

/-- **`thm:tangent`, for the equation.**  By `theoremP` (`thm:P`), a globally `p`-periodic
equation makes the min-plus map `p`-periodic, so an integer tangent orbit that is not
`p`-periodic rules out global periodicity for every positive coefficient choice on `J`. -/
theorem not_globallyPeriodic_of_tangent {k' : ℕ} {J : List ℕ} (hJne : J ≠ [])
    (hJk : ∀ j ∈ J, j ≤ k') {co : ℕ → ℝ} (hco : ∀ j ∈ J, 0 < co j)
    {E d : ℕ → ℤ} (hE : IsTrop (k' + 1) J E) (hd : TanAlong (k' + 1) J E d)
    {p : ℕ} (hnp : ∃ m n, d (n + m * p) ≠ d n) :
    ¬ GloballyPeriodic (k' + 1) J co p := fun hper =>
  not_tropPeriodic_of_tangent hJne hJk hE hd hnp
    (fun e he => theoremP hJne hJk hco hper e he)

/-- **`thm:P`, for the min-plus map.**  A globally `p`-periodic equation makes every integer
solution of the min-plus recursion `p`-periodic, so a refutation of `TropPeriodic` refutes global
periodicity at every positive coefficient choice. -/
lemma GloballyPeriodic.tropPeriodic {k : ℕ} {J : List ℕ} {co : ℕ → ℝ} {p : ℕ}
    (hJne : J ≠ []) (hJk : ∀ j ∈ J, j < k) (hco : ∀ j ∈ J, 0 < co j)
    (hg : GloballyPeriodic k J co p) : TropPeriodic k J p := by
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hJne
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := hJk j hj; omega⟩
  exact fun e he => theoremP hJne (fun j hj => Nat.lt_succ_iff.mp (hJk j hj)) hco hg e he

/-- `GloballyPeriodic.tropPeriodic` for a slot list whose nonzero slots are a nonempty
`S ⊆ [1, k)`, the constant slot `0` present or not. -/
lemma GloballyPeriodic.tropPeriodic_of_supp {k : ℕ} {S : Finset ℕ} {J : List ℕ} {co : ℕ → ℝ}
    {p : ℕ} (hS : ∀ j ∈ S, 0 < j ∧ j < k) (hSne : S.Nonempty)
    (hJS : ∀ j ∈ J, j = 0 ∨ j ∈ S) (hSJ : ∀ j ∈ S, j ∈ J) (hco : ∀ j ∈ J, 0 < co j)
    (hg : GloballyPeriodic k J co p) : TropPeriodic k J p := by
  obtain ⟨s, hs⟩ := hSne
  refine hg.tropPeriodic (List.ne_nil_of_mem (hSJ s hs)) (fun j hj => ?_) hco
  rcases hJS j hj with rfl | hjS
  · exact (hS s hs).1.trans (hS s hs).2
  · exact (hS j hjS).2

/-- The min-plus value depends only on the members of the slot list. -/
lemma mval_congr {J J' : List ℕ} (hJ : J ≠ []) (hJ' : J' ≠ []) (hJJ : ∀ j, j ∈ J ↔ j ∈ J')
    (e : ℕ → ℤ) (n : ℕ) : mval J e n = mval J' e n := by
  obtain ⟨j, hj, hjeq⟩ := mval_attained (e := e) (n := n) hJ
  obtain ⟨j', hj', hjeq'⟩ := mval_attained (e := e) (n := n) hJ'
  have h1 := mval_le (e := e) (n := n) ((hJJ j').mpr hj')
  have h2 := mval_le (e := e) (n := n) ((hJJ j).mp hj)
  omega

/-! ## The certificate -/

/-- Certificate data for one support/θ half on a **tied** carrier: the order `k`, the
slot list `J` (containing `0` iff `θ = 1`), the return time `q`, the integer exponent
window `E0`, the affine pair `V` (the ray `h`, which drifts) and `W` (the drift `δ`,
fixed), and the designated argmin word `sg` of length `q`.

Compared with `Cert` the only new field is `sg`.  For a tie-free carrier `sg` is
forced and `Cert` recomputes it; here it must be supplied, because at a tied step
several slots attain and the certificate has to say which one it linearises along. -/
structure CertPP where
  k : ℕ
  J : List ℕ
  q : ℕ
  E0 : List ℤ
  V : List ℤ
  W : List ℤ
  sg : List ℕ

/-- The designated word, extended `q`-periodically to all of `ℕ`. -/
def CertPP.word (c : CertPP) (n : ℕ) : ℕ := c.sg.getI (n % c.q)

lemma CertPP.word_periodic (c : CertPP) (n : ℕ) : c.word (n + c.q) = c.word n := by
  simp [CertPP.word, Nat.add_mod_right]

lemma CertPP.word_mod (c : CertPP) (n : ℕ) : c.word n = c.word (n % c.q) := by
  by_cases hq : c.q = 0
  · simp [CertPP.word, hq]
  · simp [CertPP.word, Nat.mod_mod_of_dvd n (dvd_refl c.q)]

/-- The initial coupled state: the carrier window together with the affine pair. -/
def CertPP.st (c : CertPP) : St := ⟨c.E0, c.V, c.W⟩

@[simp] lemma CertPP.st_E (c : CertPP) : c.st.E = c.E0 := rfl
@[simp] lemma CertPP.st_D (c : CertPP) : c.st.D = c.V := rfl
@[simp] lemma CertPP.st_U (c : CertPP) : c.st.U = c.W := rfl

/-- The drifting solution of the linearisation carried by the certificate. -/
def CertPP.dseq (c : CertPP) : ℕ → ℤ := dOf c.J c.word c.st

/-- The drift itself. -/
def CertPP.useq (c : CertPP) : ℕ → ℤ := uOf c.J c.word c.st

/-- The per-step check: the designated slot `a` lies in `J`, attains the min-plus
minimum on the exponent window, and — the **weak margin** — is no worse than any other
attaining slot on *both* perturbation windows.

Only slots that attain on `E` are compared.  Slots that miss are handled for free by
integrality: they exceed the minimum by at least `1`, which the two-scale argument in
`pert_agree_tied` beats outright. -/
def stepOK (J : List ℕ) (a : ℕ) (s : St) : Bool :=
  decide (a ∈ J) && decide (slotW s.E a = mvalW J s.E) &&
    J.all fun j => !decide (slotW s.E j = mvalW J s.E) ||
      (decide (slotW s.D a ≤ slotW s.D j) && decide (slotW s.U a ≤ slotW s.U j))

/-- The per-step check over the first `n` steps of the run. -/
def runOK (J : List ℕ) (w : ℕ → ℕ) (s0 : St) : ℕ → Bool
  | 0 => true
  | (n + 1) => runOK J w s0 n && stepOK J (w n) (runW J w s0 n)

lemma runOK_spec {J : List ℕ} {w : ℕ → ℕ} {s0 : St} : ∀ {N : ℕ},
    runOK J w s0 N = true → ∀ n < N, stepOK J (w n) (runW J w s0 n) = true := by
  intro N
  induction N with
  | zero => intro _ n hn; omega
  | succ N ih =>
    intro h n hn
    rw [runOK, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | rfl
    · exact ih h.1 n hlt
    · exact h.2

/-- The certificate check.  Everything is integer arithmetic on lists, so `decide`
settles it by kernel computation. -/
def CertPP.ok (c : CertPP) : Bool :=
  decide (0 < c.q) && decide (c.sg.length = c.q) &&
    decide (c.E0.length = c.k) && decide (c.V.length = c.k) &&
    decide (c.W.length = c.k) && (c.W.any fun x => decide (x ≠ 0)) &&
    runOK c.J c.word c.st c.q &&
    decide ((runW c.J c.word c.st c.q).E = c.E0) &&
    decide ((runW c.J c.word c.st c.q).D
      = List.zipWith (· + ·) c.V c.W) &&
    decide ((runW c.J c.word c.st c.q).U = c.W)

lemma CertPP.ok_parts {c : CertPP} (hc : c.ok = true) :
    0 < c.q ∧ c.sg.length = c.q ∧ c.E0.length = c.k ∧ c.V.length = c.k ∧
      c.W.length = c.k ∧ (∃ i, i < c.k ∧ c.W.getI i ≠ 0) ∧
      runOK c.J c.word c.st c.q = true ∧
      (runW c.J c.word c.st c.q).E = c.E0 ∧
      (runW c.J c.word c.st c.q).D = List.zipWith (· + ·) c.V c.W ∧
      (runW c.J c.word c.st c.q).U = c.W := by
  rw [CertPP.ok] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
  obtain ⟨h9, hsU⟩ := hc
  obtain ⟨h8, hsD⟩ := h9
  obtain ⟨h7, hsE⟩ := h8
  obtain ⟨h6, hrun⟩ := h7
  obtain ⟨h5, hany⟩ := h6
  obtain ⟨h4, hW⟩ := h5
  obtain ⟨h3, hV⟩ := h4
  obtain ⟨h2, hE⟩ := h3
  obtain ⟨hq, hsg⟩ := h2
  obtain ⟨x, hxmem, hx⟩ := hany
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxmem
  exact ⟨hq, hsg, hE, hV, hW, ⟨i, by omega, by
    rw [List.getI_eq_getElem _ hi, hix]; simpa using hx⟩, hrun, hsE, hsD, hsU⟩

/-! ### From the check to statements about every step

The exponent window is `q`-periodic, so *attainment* propagates from the first `q`
steps to all of `ℕ` at once.  The margins do not: the `D`-window drifts.  They
propagate instead through the drift relations below — margin at `t` on `V` plus
margin at `t` on `W` gives margin at `t + m·q` on `V + m·W`, a nonnegative
combination.  That is the whole content of Theorem Q″'s certificate.
-/

section PP
variable {c : CertPP} {k : ℕ} (hc : c.ok = true)
include hc

/-- Each step of the first period passes its check. -/
lemma pp_step {n : ℕ} (hn : n < c.q) :
    stepOK c.J (c.word n) (runW c.J c.word c.st n) = true :=
  runOK_spec (CertPP.ok_parts hc).2.2.2.2.2.2.1 n hn

/-- The word lands in `J` at every time, by `q`-periodicity of the word. -/
lemma pp_word_mem (n : ℕ) : c.word n ∈ c.J := by
  obtain ⟨hq, -⟩ := CertPP.ok_parts hc
  have := pp_step hc (Nat.mod_lt n hq)
  rw [stepOK, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  rw [c.word_mod n]
  exact this.1.1

/-- The exponent window returns after `q` steps, hence is `q`-periodic. -/
lemma pp_return : winIter (shiftApp (fZ c.J)) c.E0 c.q = c.E0 := by
  have h := (CertPP.ok_parts hc).2.2.2.2.2.2.2.1
  rwa [runW_E] at h

variable (hk : c.k = k + 1)
include hk

lemma pp_lenE : c.E0.length = k + 1 := by rw [(CertPP.ok_parts hc).2.2.1, hk]
lemma pp_lenV : c.V.length = k + 1 := by rw [(CertPP.ok_parts hc).2.2.2.1, hk]
lemma pp_lenW : c.W.length = k + 1 := by rw [(CertPP.ok_parts hc).2.2.2.2.1, hk]

end PP

lemma pp_word_le {c : CertPP} {k : ℕ} (hc : c.ok = true) (hJk : ∀ j ∈ c.J, j ≤ k)
    (n : ℕ) : c.word n ≤ k := hJk _ (pp_word_mem hc n)

/-! ### The drift

`dOf` advances by `uOf` per period and `uOf` is `q`-periodic — exactly Theorem Q's
`drift`, and proved the same way, by `lin_unique`: the two sides solve the same
linearised recursion and agree on the initial window, which is what the certificate
checks.  Nothing here needs tie-freeness, because the linearisation is along the
designated word either way. -/

section PPDrift
variable {c : CertPP} {k : ℕ} (hc : c.ok = true) (hk : c.k = k + 1)
  (hJk : ∀ j ∈ c.J, j ≤ k)
include hc hk hJk

lemma pp_drift : (∀ n, c.dseq (n + c.q) = c.dseq n + c.useq n) ∧
    (∀ n, c.useq (n + c.q) = c.useq n) := by
  have hV := pp_lenV hc hk
  have hW := pp_lenW hc hk
  have hwk : ∀ n, c.word n ≤ k := pp_word_le hc hJk
  have hDlin : IsLin (k + 1) c.word c.dseq :=
    dOf_lin (J := c.J) (w := c.word) (s0 := c.st) hV hW hwk
  have hUlin : IsLin (k + 1) c.word c.useq :=
    uOf_lin (J := c.J) (w := c.word) (s0 := c.st) hV hW hwk
  -- shifting a solution by one period is again a solution: the word is `q`-periodic
  have hshiftlin : ∀ (f : ℕ → ℤ), IsLin (k + 1) c.word f →
      IsLin (k + 1) c.word (fun n => f (n + c.q)) := by
    intro f hf n
    have h1 := hf (n + c.q)
    have h2 : n + c.q + (k + 1) = n + (k + 1) + c.q := by omega
    have h3 : slot f (n + c.q) (c.word (n + c.q))
        = slot (fun m => f (m + c.q)) n (c.word n) := by
      rw [c.word_periodic n]
      by_cases h0 : c.word n = 0
      · simp [h0, slot]
      · simp only [slot, if_neg h0]; congr 1; omega
    rw [h2] at h1
    rw [← h3]; exact h1
  -- the window conditions, straight from the certificate
  obtain ⟨-, -, -, -, -, -, -, -, hsD, hsU⟩ := CertPP.ok_parts hc
  have hwin : ∀ i ≤ k, c.dseq (c.q + i) = c.dseq i + c.useq i ∧
      c.useq (c.q + i) = c.useq i := by
    intro i hi
    have hDq : c.dseq (c.q + i) = (runW c.J c.word c.st c.q).D.getI i :=
      (dOf_getI (J := c.J) (w := c.word) (s0 := c.st) hV hW i hi c.q).symm
    have hUq : c.useq (c.q + i) = (runW c.J c.word c.st c.q).U.getI i :=
      (uOf_getI (J := c.J) (w := c.word) (s0 := c.st) hV hW i hi c.q).symm
    have hD0 : c.dseq i = c.V.getI i := by
      have := dOf_getI (J := c.J) (w := c.word) (s0 := c.st) hV hW i hi 0
      simpa [CertPP.dseq] using this.symm
    have hU0 : c.useq i = c.W.getI i := by
      have := uOf_getI (J := c.J) (w := c.word) (s0 := c.st) hV hW i hi 0
      simpa [CertPP.useq] using this.symm
    exact ⟨by rw [hDq, hsD, getI_zipWith_add (by omega) (by omega), hD0, hU0],
           by rw [hUq, hsU, hU0]⟩
  refine ⟨?_, ?_⟩
  · refine lin_unique hwk (hshiftlin _ hDlin) (fun n => ?_) (fun i hi => ?_)
    · have h3 : slot (fun m => c.dseq m + c.useq m) n (c.word n)
          = slot c.dseq n (c.word n) + slot c.useq n (c.word n) := by
        by_cases h0 : c.word n = 0
        · simp [h0, slot]
        · simp [slot, if_neg h0]
      have h1 := hDlin n
      have h2 := hUlin n
      show c.dseq (n + (k + 1)) + c.useq (n + (k + 1)) + (c.dseq n + c.useq n) = _
      rw [h3]; omega
    · have := (hwin i hi).1
      have hcomm : i + c.q = c.q + i := by omega
      rw [hcomm, this]
  · refine lin_unique hwk (hshiftlin _ hUlin) hUlin (fun i hi => ?_)
    have := (hwin i hi).2
    have hcomm : i + c.q = c.q + i := by omega
    rw [hcomm, this]

lemma pp_uOf_iter : ∀ (m n : ℕ), c.useq (n + m * c.q) = c.useq n := by
  intro m
  induction m with
  | zero => intro n; simp
  | succ m ih =>
    intro n
    have h3 : n + (m + 1) * c.q = (n + m * c.q) + c.q := by ring
    rw [h3, (pp_drift hc hk hJk).2, ih]

lemma pp_drift_iter : ∀ (m n : ℕ), c.dseq (n + m * c.q) = c.dseq n + m * c.useq n := by
  intro m
  induction m with
  | zero => intro n; simp
  | succ m ih =>
    intro n
    have h1 : n + (m + 1) * c.q = (n + m * c.q) + c.q := by ring
    rw [h1, (pp_drift hc hk hJk).1, ih n, pp_uOf_iter hc hk hJk m n]
    push_cast; ring

end PPDrift

/-! ### From one period to all time

Attainment propagates by periodicity of the exponent window alone.  The margins do
not — the `D`-window drifts — and propagate instead by the nonnegative combination
`h + m·δ`, which is what the drift relations above deliver. -/

section PPAll
variable {c : CertPP} {k : ℕ} (hc : c.ok = true) (hk : c.k = k + 1)
  (hJk : ∀ j ∈ c.J, j ≤ k)
include hc

/-- The exponent window depends only on the time modulo `q`. -/
lemma pp_win_mod (n : ℕ) : winIter (shiftApp (fZ c.J)) c.E0 n
    = winIter (shiftApp (fZ c.J)) c.E0 (n % c.q) := by
  obtain ⟨hq, -⟩ := CertPP.ok_parts hc
  have hper : ∀ m i, winIter (shiftApp (fZ c.J)) c.E0 (i + m * c.q)
      = winIter (shiftApp (fZ c.J)) c.E0 i := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      have h : i + (m + 1) * c.q = (i + m * c.q) + c.q := by ring
      rw [h, winIter_periodic (pp_return hc), ih i]
  conv_lhs => rw [show n = n % c.q + (n / c.q) * c.q from (Nat.mod_add_div' n c.q).symm]
  rw [hper]

include hk hJk

/-- The min-plus sequence carried by the certificate. -/
local notation "eSeq" => seqOf (fZ c.J) c.E0

omit hJk in
/-- Slot values of the sequence depend only on the time modulo `q`. -/
lemma pp_slot_mod {j : ℕ} (hj : j ≤ k) (n : ℕ) :
    slot eSeq n j = slot eSeq (n % c.q) j := by
  by_cases hj0 : j = 0
  · simp [hj0, slot]
  · simp only [slot, if_neg hj0]
    rw [← getI_winIter (pp_lenE hc hk) j hj n,
      ← getI_winIter (pp_lenE hc hk) j hj (n % c.q), pp_win_mod hc n]

lemma pp_mval_mod (n : ℕ) : mval c.J eSeq n = mval c.J eSeq (n % c.q) := by
  rw [← mvalW_window (pp_lenE hc hk) hJk n, ← mvalW_window (pp_lenE hc hk) hJk (n % c.q),
    pp_win_mod hc n]

omit hJk in
/-- Window slot values are sequence slot values, for the two perturbation windows. -/
lemma pp_slotW_D {j : ℕ} (hj : j ≤ k) (n : ℕ) :
    slotW (runW c.J c.word c.st n).D j = slot c.dseq n j := by
  by_cases hj0 : j = 0
  · simp [hj0, slot]
  · rw [slotW_of_ne hj0, slot, if_neg hj0,
      dOf_getI (J := c.J) (w := c.word) (s0 := c.st) (pp_lenV hc hk) (pp_lenW hc hk) j hj n]
    rfl

omit hJk in
lemma pp_slotW_U {j : ℕ} (hj : j ≤ k) (n : ℕ) :
    slotW (runW c.J c.word c.st n).U j = slot c.useq n j := by
  by_cases hj0 : j = 0
  · simp [hj0, slot]
  · rw [slotW_of_ne hj0, slot, if_neg hj0,
      uOf_getI (J := c.J) (w := c.word) (s0 := c.st) (pp_lenV hc hk) (pp_lenW hc hk) j hj n]
    rfl

/-- Unpacked form of the per-step check at a time inside the first period. -/
lemma pp_step_seq {t : ℕ} (ht : t < c.q) :
    slot eSeq t (c.word t) = mval c.J eSeq t ∧
      ∀ j ∈ c.J, slot eSeq t j = mval c.J eSeq t →
        slot c.dseq t (c.word t) ≤ slot c.dseq t j ∧
          slot c.useq t (c.word t) ≤ slot c.useq t j := by
  have hs := pp_step hc ht
  rw [stepOK, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    List.all_eq_true] at hs
  obtain ⟨⟨hmem, hattain⟩, hmarg⟩ := hs
  have hE : (runW c.J c.word c.st t).E = winIter (shiftApp (fZ c.J)) c.E0 t := runW_E _ _ _ t
  have htr : ∀ j ∈ c.J, slotW (runW c.J c.word c.st t).E j = slot eSeq t j := by
    intro j hj; rw [hE]; exact slotW_eq (pp_lenE hc hk) hJk t hj
  have hmv : mvalW c.J (runW c.J c.word c.st t).E = mval c.J eSeq t := by
    rw [hE]; exact mvalW_window (pp_lenE hc hk) hJk t
  refine ⟨by rw [← htr _ hmem, hattain, hmv], ?_⟩
  intro j hj hjeq
  have := hmarg j hj
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with hno | ⟨h1, h2⟩
  · exact absurd (by rw [htr _ hj, hmv]; exact hjeq) hno
  · rw [← pp_slotW_D hc hk (hJk _ hmem) t, ← pp_slotW_D hc hk (hJk _ hj) t,
      ← pp_slotW_U hc hk (hJk _ hmem) t, ← pp_slotW_U hc hk (hJk _ hj) t]
    exact ⟨h1, h2⟩

/-- **The certificate's hypothesis, at every time.**  This is `pert_agree_tied`'s
`hwd`, and the second component — the margin — is where the drift relations do their
work: at time `t + m·q` the perturbation slot values are `h`-values plus `m` times
`δ`-values, so an inequality that holds for both holds for the combination. -/
lemma pp_hwd (n : ℕ) : c.word n ∈ c.J ∧ slot eSeq n (c.word n) = mval c.J eSeq n ∧
    ∀ j ∈ c.J, slot eSeq n j = mval c.J eSeq n →
      slot c.dseq n (c.word n) ≤ slot c.dseq n j := by
  obtain ⟨hq, -⟩ := CertPP.ok_parts hc
  set t := n % c.q with hT
  set m := n / c.q with hM
  have hn : n = t + m * c.q := (Nat.mod_add_div' n c.q).symm
  have ht : t < c.q := Nat.mod_lt _ hq
  obtain ⟨hattain, hmarg⟩ := pp_step_seq hc hk hJk ht
  have hword : c.word n = c.word t := c.word_mod n
  -- perturbation slot values at time `n`, in terms of time `t`
  have hcomb : ∀ j ≤ k, slot c.dseq n j = slot c.dseq t j + m * slot c.useq t j := by
    intro j hj
    by_cases hj0 : j = 0
    · simp [hj0, slot]
    · simp only [slot, if_neg hj0]
      rw [show n + j = (t + j) + m * c.q by omega]
      exact pp_drift_iter hc hk hJk m (t + j)
  refine ⟨pp_word_mem hc n, ?_, ?_⟩
  · rw [hword, pp_slot_mod hc hk (hJk _ (pp_word_mem hc t)) n, pp_mval_mod hc hk hJk n]
    exact hattain
  · intro j hj hjeq
    have hjt : slot eSeq t j = mval c.J eSeq t := by
      rw [← pp_slot_mod hc hk (hJk _ hj) n, ← pp_mval_mod hc hk hJk n]; exact hjeq
    obtain ⟨hD, hU⟩ := hmarg j hj hjt
    rw [hword, hcomb _ (hJk _ (pp_word_mem hc t)), hcomb _ (hJk _ hj)]
    have hm : (0:ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    have := mul_le_mul_of_nonneg_left hU hm
    linarith

end PPAll

/-! ## Theorem Q″ -/

/-- **Theorem Q″**, for the min-plus map and any slot list with the certificate's members: a
checked tied-carrier certificate shows that no power `T^p`, `p ≥ 1`, of the min-plus map is the
identity.  The certificate's orbit is the exact solution, its affine pair the tangent orbit, and
its drift `δ ≠ 0` makes the tangent orbit non-periodic. -/
theorem not_tropPeriodic_of_certPP {c : CertPP} {k : ℕ} (hk : c.k = k + 1)
    (hc : c.ok = true) (hJ : c.J ≠ []) (hJk : ∀ j ∈ c.J, j ≤ k) {J : List ℕ}
    (hJJ : ∀ j, j ∈ J ↔ j ∈ c.J) {p : ℕ} (hp : 0 < p) : ¬ TropPeriodic c.k J p := by
  obtain ⟨hq, -, -, -, -, ⟨i, hik, hWi⟩, -⟩ := CertPP.ok_parts hc
  rw [hk] at hik ⊢
  have hE0 := pp_lenE hc hk
  have hV0 := pp_lenV hc hk
  have hW0 := pp_lenW hc hk
  have hJ' : J ≠ [] := by
    obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hJ
    exact List.ne_nil_of_mem ((hJJ j).mpr hj)
  have hmv := mval_congr hJ' hJ hJJ
  have hDlin : IsLin (k + 1) c.word c.dseq :=
    dOf_lin (J := c.J) (w := c.word) (s0 := c.st) hV0 hW0 (pp_word_le hc hJk)
  refine not_tropPeriodic_of_tangent hJ' (fun j hj => hJk j ((hJJ j).mp hj))
    (E := seqOf (fZ c.J) c.E0) (d := c.dseq) ?_ ?_ ⟨c.q, i, ?_⟩
  · intro n; rw [hmv]; exact isTrop_seqOf hE0 hJk n
  · intro n
    obtain ⟨hw, hwE, hwmin⟩ := pp_hwd hc hk hJk n
    refine ⟨c.word n, (hJJ _).mpr hw, by rw [hmv]; exact hwE, fun j hj hje => ?_, hDlin n⟩
    exact hwmin j ((hJJ j).mp hj) (by rw [← hmv]; exact hje)
  · -- the drift: `d (i + q·p) = d i + p · u i` with `u i = W i ≠ 0`
    have hdr := pp_drift_iter hc hk hJk p i
    have hUi0 : c.useq i = c.W.getI i := by
      have := uOf_getI (J := c.J) (w := c.word) (s0 := c.st) hV0 hW0 i (by omega) 0
      simpa [CertPP.useq] using this.symm
    rw [hUi0] at hdr
    have hpz : (0:ℤ) < p := by exact_mod_cast hp
    intro hfix
    rw [show i + c.q * p = i + p * c.q by ring, hdr] at hfix
    have h : (p : ℤ) * c.W.getI i = 0 := by omega
    rcases mul_eq_zero.mp h with h | h
    · omega
    · exact hWi h

/-- **Theorem Q″**, for any slot list with the certificate's members: a checked tied-carrier
certificate rules out global periodicity for every positive coefficient choice
(`not_tropPeriodic_of_certPP` and `thm:P`). -/
theorem not_globallyPeriodic_of_certPP {c : CertPP} {k : ℕ} (hk : c.k = k + 1)
    (hc : c.ok = true) (hJ : c.J ≠ []) (hJk : ∀ j ∈ c.J, j ≤ k) {J : List ℕ}
    (hJJ : ∀ j, j ∈ J ↔ j ∈ c.J) {co : ℕ → ℝ} (hco : ∀ j ∈ J, 0 < co j) {p : ℕ}
    (hp : 0 < p) : ¬ GloballyPeriodic c.k J co p := by
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hJ
  refine fun hg => not_tropPeriodic_of_certPP hk hc hJ hJk hJJ hp
    (hg.tropPeriodic (List.ne_nil_of_mem ((hJJ j).mpr hj)) (fun i hi => ?_) hco)
  have := hJk i ((hJJ i).mp hi)
  omega

/-- **Theorem Q″** on the certificate's own slot list. -/
theorem theoremQpp {c : CertPP} {k : ℕ} (hk : c.k = k + 1) (hc : c.ok = true)
    (hJ : c.J ≠ []) (hJk : ∀ j ∈ c.J, j ≤ k) {co : ℕ → ℝ}
    (hco : ∀ j ∈ c.J, 0 < co j) {p : ℕ} (hp : 0 < p) :
    ¬ GloballyPeriodic c.k c.J co p :=
  not_globallyPeriodic_of_certPP hk hc hJ hJk (fun _ => Iff.rfl) hco hp

end Trop
end PeriodicDifference
