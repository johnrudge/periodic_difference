/-
# The periodicity of the degeneration: exact tropicalisation

Family (a), normalised to `B₁ = 1`, is

  `x_{n+k} xₙ = c₀ + Σ_{j ∈ S} c_j x_{n+j}`,   `c_j > 0` on `S`, `θ = [c₀ > 0]`.

**Periodicity of the degeneration** (`thm:P`).  Put `xᵢ = δ^{eᵢ}` and let `δ → 0⁺`.  Because
every coefficient is *positive*, nothing can cancel, so each `xₙ` has an exact leading term
`aₙ δ^{eₙ}` with `aₙ > 0`, where the exponents obey the **min-plus recursion**

  `e_{n+k} + eₙ = min({0} if θ ; {e_{n+j}}_{j ∈ S})`.

Global `p`-periodicity of the equation therefore forces `e_{n+p} = eₙ` for *every*
integer solution `e` of the min-plus recursion — a condition on the **support alone**.

`theoremP` goes through `tendsto_leading`: the orbit from `xᵢ = δ^{eᵢ}` satisfies
`xₙ(δ) δ^{−eₙ} → Cₙ > 0` as `δ → 0⁺`, where the leading coefficients `Cₙ` obey the
recursion of the equation restricted to the slots attaining the minimum.  Positivity of the
coefficients is what keeps `Cₙ > 0`: the attaining terms cannot cancel.  Since the min-plus
map is positively homogeneous, `ℤ` exponents lose nothing and `zpow` suffices.

The proof uses `theoremP` through the tangent argument of `PeriodicDifference/TropicalQpp.lean`
(`not_globallyPeriodic_of_tangent`).
-/

import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

namespace PeriodicDifference
namespace Trop

/-! ## The min-plus recursion -/

/-- Slot `0` is the constant term (contributing `0`); slot `j ≥ 1` contributes
`e (n+j)`. -/
def slot {α : Type*} [Zero α] (e : ℕ → α) (n j : ℕ) : α :=
  if j = 0 then 0 else e (n + j)

/-- Minimum of a list, given a default for the empty case. -/
def lmin {α : Type*} [LinearOrder α] (d : α) : List α → α
  | [] => d
  | a :: l => lmin (min d a) l

/-- The min-plus value at position `n`: the minimum of the slot values over `J`. -/
def mval {α : Type*} [Zero α] [LinearOrder α] (J : List ℕ) (e : ℕ → α) (n : ℕ) : α :=
  match J with
  | [] => 0
  | j :: js => lmin (slot e n j) (js.map (slot e n))

section LMin
variable {α : Type*} [LinearOrder α]

@[simp] lemma lmin_nil (d : α) : lmin d [] = d := rfl

@[simp] lemma lmin_cons (d a : α) (l : List α) :
    lmin d (a :: l) = lmin (min d a) l := rfl

/-- `lmin d l` is the minimum of `d :: l`. -/
lemma lmin_le_head (d : α) (l : List α) : lmin d l ≤ d := by
  induction l generalizing d with
  | nil => exact le_rfl
  | cons a l ih => exact (ih (min d a)).trans (min_le_left _ _)

lemma lmin_le_of_mem {d : α} {l : List α} {x : α} (hx : x ∈ l) : lmin d l ≤ x := by
  induction l generalizing d with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with h | h
    · cases h; exact (lmin_le_head _ l).trans (min_le_right _ _)
    · exact ih h

lemma lmin_mem (d : α) (l : List α) : lmin d l ∈ d :: l := by
  induction l generalizing d with
  | nil => simp
  | cons a l ih =>
    rw [lmin_cons]
    have hm := ih (min d a)
    rcases List.mem_cons.mp hm with h | h
    · rcases min_cases d a with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h, h1]; simp
      · rw [h, h1]; simp
    · simp [h]

end LMin

section MVal
variable {α : Type*} [Zero α] [LinearOrder α]

/-- The min-plus value is a lower bound for every slot. -/
lemma mval_le {J : List ℕ} {e : ℕ → α} {n : ℕ} {j : ℕ} (hj : j ∈ J) :
    mval J e n ≤ slot e n j := by
  cases J with
  | nil => exact absurd hj (List.not_mem_nil)
  | cons i js =>
    rcases List.mem_cons.mp hj with h | h
    · subst h; exact lmin_le_head _ _
    · exact lmin_le_of_mem (List.mem_map_of_mem h)

/-- The min-plus value is attained at some slot. -/
lemma mval_attained {J : List ℕ} (hJ : J ≠ []) (e : ℕ → α) (n : ℕ) :
    ∃ j ∈ J, mval J e n = slot e n j := by
  cases J with
  | nil => exact absurd rfl hJ
  | cons i js =>
    have h := lmin_mem (slot e n i) (js.map (slot e n))
    rcases List.mem_cons.mp h with h | h
    · exact ⟨i, List.mem_cons_self .., h⟩
    · obtain ⟨j, hj, hje⟩ := List.mem_map.mp h
      exact ⟨j, List.mem_cons_of_mem _ hj, hje.symm⟩

end MVal

/-- `e` solves the min-plus recursion of order `k` with slot list `J`. -/
def IsTrop {α : Type*} [Zero α] [LinearOrder α] [Add α]
    (k : ℕ) (J : List ℕ) (e : ℕ → α) : Prop :=
  ∀ n, e (n + k) + e n = mval J e n

/-- `δ` solves the recursion *linearised* along the argmin word `wd`. -/
def IsLin (k : ℕ) (wd : ℕ → ℕ) (d : ℕ → ℤ) : Prop :=
  ∀ n, d (n + k) + d n = slot d n (wd n)

/-! ## Sequences from an initial window

Both bridges need the same construction: a sequence obeying a `k`-step recursion,
built from an initial window.  Iterating a *window map* of the shift-append shape
`w ↦ w.tail ++ [f w]` avoids well-founded recursion entirely.
-/

section Window
variable {α : Type*}

/-- Shift the window left and append the new value produced by `f`. -/
def shiftApp (f : List α → α) (w : List α) : List α := w.tail ++ [f w]

/-- Iterate a window map. -/
def winIter (st : List α → List α) (w0 : List α) : ℕ → List α
  | 0 => w0
  | (m + 1) => st (winIter st w0 m)

@[simp] lemma winIter_zero (st : List α → List α) (w0 : List α) :
    winIter st w0 0 = w0 := rfl

lemma winIter_succ (st : List α → List α) (w0 : List α) (m : ℕ) :
    winIter st w0 (m + 1) = st (winIter st w0 m) := rfl

lemma winIter_shift (st : List α → List α) (w0 : List α) : ∀ n,
    winIter st (st w0) n = winIter st w0 (n + 1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [winIter_succ, ih]
    exact (winIter_succ st w0 (n + 1)).symm

lemma length_shiftApp {f : List α → α} {w : List α} {k : ℕ} (hw : w.length = k + 1) :
    (shiftApp f w).length = k + 1 := by
  simp [shiftApp, List.length_tail, hw]

lemma length_winIter {f : List α → α} {w0 : List α} {k : ℕ} (hw : w0.length = k + 1)
    (m : ℕ) : (winIter (shiftApp f) w0 m).length = k + 1 := by
  induction m with
  | zero => simpa using hw
  | succ m ih => rw [winIter_succ]; exact length_shiftApp ih

variable [Inhabited α]

lemma getI_tail (l : List α) (j : ℕ) : l.tail.getI j = l.getI (j + 1) := by
  cases l with
  | nil => simp [List.getI_nil]
  | cons x xs => simp [List.getI_cons_succ]

/-- The sequence read off the windows: `seqOf f w0 n` is the head of the `n`-th
window, i.e. the `n`-th term. -/
def seqOf (f : List α → α) (w0 : List α) (n : ℕ) : α :=
  (winIter (shiftApp f) w0 n).headI

/-- Pushing the window forward one step drops the first entry. -/
lemma getI_winIter_succ {f : List α → α} {w0 : List α} {k : ℕ}
    (hw : w0.length = k + 1) (m : ℕ) {j : ℕ} (hjk : j < k) :
    (winIter (shiftApp f) w0 (m + 1)).getI j = (winIter (shiftApp f) w0 m).getI (j + 1) := by
  have hlen := length_winIter (f := f) hw m
  have hj' : j < (winIter (shiftApp f) w0 m).tail.length := by
    simp [List.length_tail, hlen]; omega
  rw [winIter_succ, shiftApp, List.getI_append _ _ _ hj', getI_tail]

/-- Entry `j` of the window at time `m` is the term at time `m + j`. -/
lemma getI_winIter {f : List α → α} {w0 : List α} {k : ℕ} (hw : w0.length = k + 1) :
    ∀ (j : ℕ), j ≤ k → ∀ m : ℕ,
      (winIter (shiftApp f) w0 m).getI j = seqOf f w0 (m + j) := by
  intro j
  induction j with
  | zero => intro _ m; simp [seqOf, List.getI_zero_eq_headI]
  | succ j ih =>
    intro hj m
    have h1 := getI_winIter_succ (f := f) hw m (j := j) (by omega)
    rw [← h1, ih (by omega) (m + 1)]
    congr 1
    omega

/-- The `k`-step recursion satisfied by `seqOf`: the new term is `f` applied to the
window of the previous `k + 1` terms. -/
lemma seqOf_rec {f : List α → α} {w0 : List α} {k : ℕ} (hw : w0.length = k + 1)
    (m : ℕ) : seqOf f w0 (m + (k + 1)) = f (winIter (shiftApp f) w0 m) := by
  have hlen := length_winIter (f := f) hw m
  have htl : (winIter (shiftApp f) w0 m).tail.length = k := by
    simp [List.length_tail, hlen]
  have h : seqOf f w0 (m + 1 + k) = (winIter (shiftApp f) w0 (m + 1)).getI k :=
    (getI_winIter hw k le_rfl (m + 1)).symm
  have h2 : (winIter (shiftApp f) w0 (m + 1)).getI k = f (winIter (shiftApp f) w0 m) := by
    rw [winIter_succ, shiftApp, List.getI_append_right _ _ _ (by omega), htl]
    simp
  have hmk : m + (k + 1) = m + 1 + k := by omega
  rw [hmk, h, h2]

end Window

/-! ## Towards Theorem Q: tropical sequences from integer windows -/

section Qbridge

/-- The min-plus value read off a window (slot `0` contributes `0`). -/
def mvalW (J : List ℕ) (w : List ℤ) : ℤ :=
  match J with
  | [] => 0
  | j :: js => lmin (if j = 0 then 0 else w.getI j)
      (js.map (fun i => if i = 0 then 0 else w.getI i))

/-- The integer min-plus step: the new exponent is `min − (oldest exponent)`. -/
def fZ (J : List ℕ) (w : List ℤ) : ℤ := mvalW J w - w.getI 0

variable {J : List ℕ} {k : ℕ}

/-- On the window at time `m`, `mvalW` agrees with `mval` of the sequence. -/
lemma mvalW_window {w0 : List ℤ} (hw : w0.length = k + 1) (hJk : ∀ j ∈ J, j ≤ k)
    (m : ℕ) :
    mvalW J (winIter (shiftApp (fZ J)) w0 m) = mval J (seqOf (fZ J) w0) m := by
  cases J with
  | nil => simp [mvalW, mval]
  | cons i js =>
    have hget : ∀ j ∈ (i :: js), (winIter (shiftApp (fZ (i :: js))) w0 m).getI j
        = seqOf (fZ (i :: js)) w0 (m + j) :=
      fun j hj => getI_winIter hw j (hJk j hj) m
    have h1 : (if i = 0 then (0:ℤ) else (winIter (shiftApp (fZ (i :: js))) w0 m).getI i)
        = slot (seqOf (fZ (i :: js)) w0) m i := by
      by_cases h : i = 0
      · simp [h, slot]
      · simp only [if_neg h, slot]
        rw [hget i (List.mem_cons_self ..)]
    have h2 : (js.map fun x => if x = 0 then (0:ℤ)
          else (winIter (shiftApp (fZ (i :: js))) w0 m).getI x)
        = js.map (slot (seqOf (fZ (i :: js)) w0) m) := by
      apply List.map_congr_left
      intro j hj
      by_cases h : j = 0
      · simp [h, slot]
      · simp only [if_neg h, slot]
        rw [hget j (List.mem_cons_of_mem _ hj)]
    show lmin _ _ = lmin _ _
    rw [h1, h2]

/-- **Every integer window generates a solution of the min-plus recursion.** -/
lemma isTrop_seqOf {w0 : List ℤ} (hw : w0.length = k + 1) (hJk : ∀ j ∈ J, j ≤ k) :
    IsTrop (k + 1) J (seqOf (fZ J) w0) := by
  intro m
  have hstep : seqOf (fZ J) w0 (m + (k + 1))
      = fZ J (winIter (shiftApp (fZ J)) w0 m) := seqOf_rec hw m
  have h0 : (winIter (shiftApp (fZ J)) w0 m).getI 0 = seqOf (fZ J) w0 m := by
    have := getI_winIter (f := fZ J) hw 0 (by omega) m
    simpa using this
  rw [hstep, fZ, mvalW_window hw hJk m, h0]
  ring

end Qbridge
/-! ## What a certificate rules out

`GloballyPeriodic k J c p` says the family-(a) equation of order `k` with slot list
`J` and coefficients `c` has every positive solution `p`-periodic.
-/

/-- The right-hand side `c₀ + Σ_{j ∈ S} c_j x_{n+j}`, with slot `0` the constant. -/
def rhs (J : List ℕ) (co : ℕ → ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (J.map fun j => co j * (if j = 0 then 1 else x (n + j))).sum

/-- Every positive solution of the order-`k` equation is `p`-periodic. -/
def GloballyPeriodic (k : ℕ) (J : List ℕ) (co : ℕ → ℝ) (p : ℕ) : Prop :=
  ∀ x : ℕ → ℝ, (∀ n, 0 < x n) → (∀ n, x (n + k) * x n = rhs J co x n) →
    ∀ n, x (n + p) = x n

/-! ## The orbit of the equation from a window -/

section OrbitR

/-- The value the equation appends, read off a window: `(Σ_{j∈J} c_j ·) / x_n`. -/
noncomputable def fR (J : List ℕ) (co : ℕ → ℝ) (w : List ℝ) : ℝ :=
  (J.map fun j => co j * (if j = 0 then 1 else w.getI j)).sum / w.getI 0

/-- The orbit of the equation with initial window `w0`. -/
noncomputable def orbR (J : List ℕ) (co : ℕ → ℝ) (w0 : List ℝ) : ℕ → ℝ :=
  seqOf (fR J co) w0

variable {J : List ℕ} {co : ℕ → ℝ} {w0 : List ℝ} {k : ℕ}

lemma fR_eq (J : List ℕ) (co : ℕ → ℝ) (w : List ℝ) :
    fR J co w = (J.map fun j => co j * (if j = 0 then 1 else w.getI j)).sum / w.getI 0 :=
  rfl

lemma orbR_init (hw : w0.length = k + 1) {n : ℕ} (hn : n ≤ k) :
    orbR J co w0 n = w0.getI n := by
  have := getI_winIter (f := fR J co) hw n hn 0
  simpa [orbR] using this.symm

/-- `fR` at the window at time `m`, expressed in terms of the orbit. -/
lemma fR_win (hw : w0.length = k + 1) (hJk : ∀ j ∈ J, j ≤ k) (m : ℕ) :
    fR J co (winIter (shiftApp (fR J co)) w0 m)
      = (J.map fun j => co j * (if j = 0 then 1 else orbR J co w0 (m + j))).sum
          / orbR J co w0 m := by
  rw [fR_eq]
  have h0 : (winIter (shiftApp (fR J co)) w0 m).getI 0 = orbR J co w0 m := by
    have := getI_winIter (f := fR J co) hw 0 (by omega) m
    simpa [orbR] using this
  have hmap : (J.map fun j => co j *
        (if j = 0 then 1 else (winIter (shiftApp (fR J co)) w0 m).getI j))
      = (J.map fun j => co j * (if j = 0 then 1 else orbR J co w0 (m + j))) := by
    apply List.map_congr_left
    intro j hj
    by_cases hj0 : j = 0
    · simp [hj0]
    · simp only [if_neg hj0]
      rw [getI_winIter (f := fR J co) hw j (hJk j hj) m]
      rfl
  rw [hmap, h0]

/-- The orbit stays positive. -/
lemma orbR_pos (hJ : J ≠ []) (hco : ∀ j ∈ J, 0 < co j) (hw : w0.length = k + 1)
    (hJk : ∀ j ∈ J, j ≤ k) (hw0 : ∀ i ≤ k, 0 < w0.getI i) :
    ∀ n, 0 < orbR J co w0 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ k
    · rw [orbR_init hw hn]; exact hw0 n hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + (k + 1) := ⟨n - (k + 1), by omega⟩
      have hstep : orbR J co w0 (m + (k + 1))
          = fR J co (winIter (shiftApp (fR J co)) w0 m) := seqOf_rec hw m
      rw [hstep, fR_win hw hJk m]
      apply div_pos
      · apply List.sum_pos
        · intro y hy
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
          have hjk : j ≤ k := hJk j hj
          by_cases hj0 : j = 0
          · simpa [hj0] using hco j hj
          · have : 0 < orbR J co w0 (m + j) := ih _ (by omega)
            simpa [if_neg hj0] using mul_pos (hco j hj) this
        · simpa using hJ
      · exact ih m (by omega)

/-- The orbit solves the equation. -/
lemma orbR_rec (hJ : J ≠ []) (hco : ∀ j ∈ J, 0 < co j) (hw : w0.length = k + 1)
    (hJk : ∀ j ∈ J, j ≤ k) (hw0 : ∀ i ≤ k, 0 < w0.getI i) (n : ℕ) :
    orbR J co w0 (n + (k + 1)) * orbR J co w0 n = rhs J co (orbR J co w0) n := by
  have hpos := orbR_pos hJ hco hw hJk hw0 n
  have hstep : orbR J co w0 (n + (k + 1))
      = fR J co (winIter (shiftApp (fR J co)) w0 n) := seqOf_rec hw n
  rw [hstep, fR_win hw hJk n]
  rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
  rfl

end OrbitR

/-! ## Leading coefficients

Run the orbit from `xᵢ = δ^{eᵢ}` (`i ≤ k`) for an integer min-plus solution `e`.  Then
`xₙ(δ) δ^{−eₙ}` tends to a positive limit `Cₙ` as `δ → 0⁺` (`tendsto_leading`), and the
limits obey the recursion of the equation restricted to the **attaining** slots,

  `C_{n+k+1} Cₙ = Σ_{j ∈ Aₙ} c_j C_{n+j}`   (the constant slot contributing `c₀`),

`Aₙ` being the slots at which the min-plus minimum is attained (`leadNum`).  Every
coefficient is positive, so the attaining terms cannot cancel: this is the "no
cancellation" of the Laurent-polynomial argument.  The periodicity of the degeneration
(`thm:P`) is the immediate consequence that `e_{n+p} ≠ eₙ` makes `x_{n+p}/xₙ` tend to `0`
or `∞`; the order-2 and order-3 classifications read the drift of the `Cₙ` along a cycle of
`e` (`PeriodicDifference/Order2.lean`, `PeriodicDifference/Order3.lean`).
-/

section Leading
variable {J : List ℕ} {co : ℕ → ℝ} {k : ℕ}

open Filter Topology

/-- The initial window `xᵢ = δ^{eᵢ}`. -/
noncomputable def winit (e : ℕ → ℤ) (k : ℕ) (δ : ℝ) : List ℝ :=
  (List.range (k + 1)).map (fun i => δ ^ (e i))

@[simp] lemma winit_length (e : ℕ → ℤ) (k : ℕ) (δ : ℝ) :
    (winit e k δ).length = k + 1 := by simp [winit]

lemma winit_getI (e : ℕ → ℤ) (k : ℕ) (δ : ℝ) {i : ℕ} (hi : i ≤ k) :
    (winit e k δ).getI i = δ ^ (e i) := by
  have hlt : i < (winit e k δ).length := by rw [winit_length]; omega
  rw [List.getI_eq_getElem _ hlt]
  simp [winit]

lemma winit_pos {δ : ℝ} (hδ : 0 < δ) (e : ℕ → ℤ) (k : ℕ) :
    ∀ i ≤ k, 0 < (winit e k δ).getI i := by
  intro i hi; rw [winit_getI e k δ hi]; exact zpow_pos hδ _

/-- One step of the orbit, in division form. -/
lemma orbR_step {w0 : List ℝ} (hw : w0.length = k + 1) (hJk : ∀ j ∈ J, j ≤ k) (n : ℕ) :
    orbR J co w0 (n + (k + 1))
      = (J.map fun j => co j * (if j = 0 then 1 else orbR J co w0 (n + j))).sum
          / orbR J co w0 n := by
  rw [orbR, seqOf_rec hw n]; exact fR_win hw hJk n

/-- The orbit from `xᵢ = δ^{eᵢ}`, normalised by its expected order `δ^{eₙ}`. -/
noncomputable def xN (J : List ℕ) (co : ℕ → ℝ) (e : ℕ → ℤ) (k : ℕ) (n : ℕ) (δ : ℝ) : ℝ :=
  orbR J co (winit e k δ) n * δ ^ (-e n)

/-- The right-hand side of the leading-coefficient recursion: the attaining slots only. -/
noncomputable def leadNum (J : List ℕ) (co : ℕ → ℝ) (e : ℕ → ℤ) (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  (J.map fun j => co j * (if j = 0 then 1 else C (n + j)) *
    (if slot e n j = mval J e n then 1 else 0)).sum

/-- `δ^d → [d = 0]` as `δ → 0⁺`, for `d ≥ 0`. -/
lemma tendsto_zpow_nonneg {d : ℤ} (hd : 0 ≤ d) :
    Tendsto (fun δ : ℝ => δ ^ d) (𝓝[>] 0) (𝓝 (if d = 0 then 1 else 0)) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hd
  simp only [zpow_natCast, Nat.cast_eq_zero]
  rcases m with _ | m
  · simp
  · simpa using ((continuous_pow (m + 1)).tendsto' (0 : ℝ) 0 (by simp)).mono_left
      nhdsWithin_le_nhds

variable {e : ℕ → ℤ}

/-- **One step**, as an exact identity: the normalised new term is the sum of the slot terms,
each carrying `δ^{slot − min}`, over the normalised oldest term. -/
lemma xN_step (hJk : ∀ j ∈ J, j ≤ k) (he : IsTrop (k + 1) J e) {δ : ℝ} (hδ : 0 < δ)
    (n : ℕ) :
    xN J co e k (n + (k + 1)) δ
      = (J.map fun j => co j * (if j = 0 then 1 else xN J co e k (n + j) δ) *
          δ ^ (slot e n j - mval J e n)).sum / xN J co e k n δ := by
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hterm : ∀ j ∈ J, co j * (if j = 0 then 1 else xN J co e k (n + j) δ) *
      δ ^ (slot e n j - mval J e n)
      = co j * (if j = 0 then 1 else orbR J co (winit e k δ) (n + j)) * δ ^ (-mval J e n) := by
    intro j _
    by_cases hj : j = 0
    · simp [hj, slot]
    · simp only [hj, if_false, slot, xN, mul_assoc]
      rw [← zpow_add₀ hδ0]
      ring_nf
  have hM : e (n + (k + 1)) = mval J e n - e n := by have := he n; omega
  rw [List.map_congr_left hterm, List.sum_map_mul_right, xN, xN,
    orbR_step (winit_length e k δ) hJk n, hM]
  have h1 : δ ^ (-(mval J e n - e n)) = δ ^ (-mval J e n) * δ ^ (e n) := by
    rw [← zpow_add₀ hδ0]; ring_nf
  have h2 : δ ^ (-e n) = (δ ^ (e n))⁻¹ := zpow_neg δ (e n)
  have h3 : δ ^ (e n) ≠ 0 := zpow_ne_zero _ hδ0
  rw [h1, h2]
  field_simp

/-- The limit of one step, given the limits over the preceding window. -/
lemma tendsto_xN_step (hJ : J ≠ []) (hJk : ∀ j ∈ J, j ≤ k) (hco : ∀ j ∈ J, 0 < co j)
    (he : IsTrop (k + 1) J e) (C : ℕ → ℝ) (n : ℕ)
    (hC : ∀ j ≤ k, 0 < C (n + j) ∧
      Tendsto (xN J co e k (n + j)) (𝓝[>] 0) (𝓝 (C (n + j)))) :
    0 < leadNum J co e C n ∧
      Tendsto (xN J co e k (n + (k + 1))) (𝓝[>] 0) (𝓝 (leadNum J co e C n / C n)) := by
  have hpos : 0 < leadNum J co e C n := by
    obtain ⟨j, hj, hjM⟩ := mval_attained (e := e) (n := n) hJ
    have hCj : 0 < (if j = 0 then 1 else C (n + j)) := by
      split_ifs; exacts [one_pos, (hC j (hJk j hj)).1]
    refine lt_of_lt_of_le ?_ (List.single_le_sum ?_ _ (List.mem_map_of_mem hj))
    · rw [if_pos hjM.symm, mul_one]; exact mul_pos (hco j hj) hCj
    · intro y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      have : 0 ≤ (if i = 0 then 1 else C (n + i)) := by
        split_ifs; exacts [zero_le_one, (hC i (hJk i hi)).1.le]
      have : (0 : ℝ) ≤ (if slot e n i = mval J e n then 1 else 0) := by split_ifs <;> norm_num
      have := (hco i hi).le
      positivity
  refine ⟨hpos, ?_⟩
  have hsum : Tendsto (fun δ => (J.map fun j => co j * (if j = 0 then 1 else xN J co e k (n + j) δ)
      * δ ^ (slot e n j - mval J e n)).sum) (𝓝[>] 0) (𝓝 (leadNum J co e C n)) := by
    refine tendsto_list_sum J fun j hj => ?_
    have hx : Tendsto (fun δ => if j = 0 then 1 else xN J co e k (n + j) δ) (𝓝[>] 0)
        (𝓝 (if j = 0 then 1 else C (n + j))) := by
      split_ifs; exacts [tendsto_const_nhds, (hC j (hJk j hj)).2]
    have hd := tendsto_zpow_nonneg (sub_nonneg.mpr (mval_le (e := e) (n := n) hj))
    simp only [sub_eq_zero] at hd
    exact (tendsto_const_nhds.mul hx).mul hd
  have h0 := hC 0 (Nat.zero_le _)
  rw [Nat.add_zero] at h0
  refine (hsum.div h0.2 h0.1.ne').congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (xN_step hJk he hδ n).symm

/-- **Leading coefficients** (`thm:leading`).  For an integer min-plus
solution `e`, the orbit from `xᵢ = δ^{eᵢ}` satisfies `xₙ(δ) δ^{−eₙ} → Cₙ > 0` as `δ → 0⁺`,
where `Cₙ = 1` on the initial window and `C_{n+k+1} Cₙ = Σ_{j ∈ Aₙ} c_j C_{n+j}` (`leadNum`). -/
theorem tendsto_leading (hJ : J ≠ []) (hJk : ∀ j ∈ J, j ≤ k) (hco : ∀ j ∈ J, 0 < co j)
    (he : IsTrop (k + 1) J e) :
    ∃ C : ℕ → ℝ, (∀ n, 0 < C n) ∧ (∀ n ≤ k, C n = 1) ∧
      (∀ n, C (n + (k + 1)) * C n = leadNum J co e C n) ∧
      ∀ n, Tendsto (xN J co e k n) (𝓝[>] 0) (𝓝 (C n)) := by
  have hinit : ∀ n ≤ k, Tendsto (xN J co e k n) (𝓝[>] 0) (𝓝 1) := by
    intro n hn
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [xN, orbR_init (winit_length e k δ) hn, winit_getI e k δ hn, zpow_neg,
      mul_inv_cancel₀ (zpow_ne_zero _ (ne_of_gt hδ))]
  have hex : ∀ m, ∃ C : ℕ → ℝ, ∀ i ≤ m + k,
      0 < C i ∧ Tendsto (xN J co e k i) (𝓝[>] 0) (𝓝 (C i)) := by
    intro m
    induction m with
    | zero => exact ⟨fun _ => 1, fun i hi => ⟨one_pos, hinit i (by omega)⟩⟩
    | succ m ih =>
      obtain ⟨C, hC⟩ := ih
      have hs := tendsto_xN_step hJ hJk hco he C m fun j hj => hC (m + j) (by omega)
      refine ⟨Function.update C (m + (k + 1)) (leadNum J co e C m / C m), fun i hi => ?_⟩
      rcases eq_or_ne i (m + (k + 1)) with rfl | hne
      · rw [Function.update_self]
        exact ⟨div_pos hs.1 (hC m (by omega)).1, hs.2⟩
      · rw [Function.update_of_ne hne]; exact hC i (by omega)
  have hlim : ∀ n, ∃ c, 0 < c ∧ Tendsto (xN J co e k n) (𝓝[>] 0) (𝓝 c) := fun n =>
    (hex n).elim fun C hC => ⟨C n, hC n (by omega)⟩
  choose C hCpos hC using hlim
  refine ⟨C, hCpos, fun n hn => tendsto_nhds_unique (hC n) (hinit n hn), fun n => ?_, hC⟩
  have hs := tendsto_xN_step hJ hJk hco he C n fun j _ => ⟨hCpos _, hC _⟩
  rw [tendsto_nhds_unique (hC _) hs.2, div_mul_cancel₀ _ (hCpos n).ne']

end Leading

open Filter Topology in
/-- The orbit from `xᵢ = δ^{eᵢ}` is a positive solution, so global `p`-periodicity applies
to it. -/
lemma orbR_winit_periodic {k : ℕ} {J : List ℕ} {co : ℕ → ℝ}
    (hJ : J ≠ []) (hJk : ∀ j ∈ J, j ≤ k) (hco : ∀ j ∈ J, 0 < co j)
    {p : ℕ} (hper : GloballyPeriodic (k + 1) J co p) (e : ℕ → ℤ) {δ : ℝ} (hδ : 0 < δ)
    (n : ℕ) : orbR J co (winit e k δ) (n + p) = orbR J co (winit e k δ) n :=
  hper _ (orbR_pos hJ hco (winit_length e k δ) hJk (winit_pos hδ e k))
    (fun m => orbR_rec hJ hco (winit_length e k δ) hJk (winit_pos hδ e k) m) n

open Filter Topology in
/-- **Periodicity of the degeneration** (`thm:P`).  Global `p`-periodicity of the equation
forces every integer solution of the min-plus recursion to be `p`-periodic.

Run the orbit from `xᵢ = δ^{eᵢ}`: it is `p`-periodic, and by `tendsto_leading`
`xₙ δ^{−eₙ}` and `x_{n+p} δ^{−e_{n+p}}` have positive limits.  If `e_{n+p} ≠ eₙ` their ratio is
`δ^{±(e_{n+p} − eₙ)} → 0`, a contradiction.

Since the min-plus map is positively homogeneous, the integer case gives the rational
and hence the real one, so nothing is lost by stating it over `ℤ`. -/
theorem theoremP {k : ℕ} {J : List ℕ} {co : ℕ → ℝ}
    (hJ : J ≠ []) (hJk : ∀ j ∈ J, j ≤ k) (hco : ∀ j ∈ J, 0 < co j)
    {p : ℕ} (hper : GloballyPeriodic (k + 1) J co p)
    (e : ℕ → ℤ) (he : IsTrop (k + 1) J e) : ∀ n, e (n + p) = e n := by
  intro n
  obtain ⟨C, hCpos, -, -, hC⟩ := tendsto_leading (co := co) hJ hJk hco he
  -- `xN b = xN a · δ^{e a − e b}` whenever the orbit takes the same value at `a` and `b`
  have hsame : ∀ a b, (∀ δ : ℝ, 0 < δ → orbR J co (winit e k δ) a = orbR J co (winit e k δ) b) →
      e b ≤ e a → e a = e b := by
    intro a b hab hle
    by_contra hne
    have hd := tendsto_zpow_nonneg (sub_nonneg.mpr hle)
    rw [if_neg (sub_ne_zero.mpr hne)] at hd
    have hlim : Tendsto (xN J co e k b) (𝓝[>] 0) (𝓝 (C a * 0)) := by
      refine ((hC a).mul hd).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ0 : δ ≠ 0 := ne_of_gt hδ
      simp only [xN]
      rw [hab δ hδ, mul_assoc, ← zpow_add₀ hδ0]
      ring_nf
    rw [mul_zero] at hlim
    exact (hCpos b).ne' (tendsto_nhds_unique (hC b) hlim)
  have hsol := fun δ (hδ : (0 : ℝ) < δ) => orbR_winit_periodic hJ hJk hco hper e hδ n
  rcases le_total (e n) (e (n + p)) with h | h
  · exact hsame _ _ hsol h
  · exact (hsame _ _ (fun δ hδ => (hsol δ hδ).symm) h).symm

open Filter Topology in
/-- The leading coefficients are `p`-periodic too: with `e` periodic by `theoremP`, the
normalised orbit itself is. -/
theorem leading_periodic {k : ℕ} {J : List ℕ} {co : ℕ → ℝ}
    (hJ : J ≠ []) (hJk : ∀ j ∈ J, j ≤ k) (hco : ∀ j ∈ J, 0 < co j)
    {p : ℕ} (hper : GloballyPeriodic (k + 1) J co p)
    {e : ℕ → ℤ} (he : IsTrop (k + 1) J e) {C : ℕ → ℝ}
    (hC : ∀ n, Tendsto (xN J co e k n) (𝓝[>] 0) (𝓝 (C n))) (n : ℕ) : C (n + p) = C n := by
  refine tendsto_nhds_unique (hC (n + p)) ((hC n).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [xN, xN, orbR_winit_periodic hJ hJk hco hper e hδ n, theoremP hJ hJk hco hper e he n]

end Trop
end PeriodicDifference
