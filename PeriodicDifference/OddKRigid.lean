/-
# `PeriodicDifference/OddKRigid.lean` — translate and reflection rigidity (`lem:odd-trigid`,
`lem:odd-symfail`, `lem:odd-wunique`)

Residues modulo odd `k = 2c+1`, as naturals `< k`; `X ⊆ [1, c]` (`Bd k X`).  Translating
`X` by `ζ` is `x ↦ (x + ζ) % k`; reflecting it in `n` is `x ↦ (n + k − x) % k`.

* `trigid` (`lem:odd-trigid`): if `ζ ≠ 0` and `(ζ + X) ∖ {0} ⊆ X`, then `X` is a dilated
  interval `μ·{1,…,M}` (`Dil X`).  As in the paper: `ζ ≤ c` is
  impossible (the maximum of `X` would move up inside `X`), so `μ = k − ζ ≤ c`, and then the
  translate is `x ↦ x − μ`, which forces `X` to be closed under `x ↦ x − μ` down to `μ`.
* `symfail` (`lem:odd-symfail`): if moreover `X` is symmetric about `j` and
  `ζ + X ⊆ X ∪ {0, j}`, then `X` is a dilated interval.  As in the paper: a translate
  exiting only at `0` is `trigid`; one exiting only at `j` is `trigid` for `−ζ` after
  reflecting; one exiting at both puts `ζ` and `−ζ` into `[1, c]`.
* `symW_unique` (`lem:odd-wunique`, uniqueness of the centre of `W = X ∪ {0}`).
-/
import Mathlib.Tactic

namespace PeriodicDifference
namespace Trop
namespace OddK

/-- `X ⊆ [1, c]` at `k = 2c + 1`. -/
def Bd (k : ℕ) (X : Finset ℕ) : Prop := ∀ x ∈ X, 1 ≤ x ∧ 2 * x < k

/-- `X = μ·{1, …, M}`: a dilated interval. -/
def Dil (X : Finset ℕ) : Prop := ∃ μ M, 0 < μ ∧ ∀ x, x ∈ X ↔ ∃ i, 1 ≤ i ∧ i ≤ M ∧ x = μ * i

/-- `X` symmetric about `n`: `n − X ⊆ X`. -/
def SymX (k : ℕ) (X : Finset ℕ) (n : ℕ) : Prop := ∀ x ∈ X, (n + k - x) % k ∈ X

/-- `W = X ∪ {0}` symmetric about `q`: `q ∈ X` and `q − (X ∖ {q}) ⊆ X`. -/
def SymW (k : ℕ) (X : Finset ℕ) (q : ℕ) : Prop := q ∈ X ∧ ∀ x ∈ X, x ≠ q → (q + k - x) % k ∈ X

lemma add_mod_lt {k a b : ℕ} (ha : a < k) (hb : b < k) :
    (a + b) % k = if a + b < k then a + b else a + b - k := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma sub_mod_lt {k a b : ℕ} (ha : a < k) (hb : b ≤ k) :
    (a + k - b) % k = if b ≤ a then a - b else a + k - b := by
  split_ifs with h
  · have : a + k - b = (a - b) + k := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

lemma add_cases {k a b : ℕ} (ha : a < k) (hb : b < k) :
    ((a + b) % k = a + b ∧ a + b < k) ∨ ((a + b) % k = a + b - k ∧ k ≤ a + b) := by
  rw [add_mod_lt ha hb]; split_ifs <;> omega

lemma sub_cases {k a b : ℕ} (ha : a < k) (hb : b ≤ k) :
    ((a + k - b) % k = a - b ∧ b ≤ a) ∨ ((a + k - b) % k = a + k - b ∧ a < b) := by
  rw [sub_mod_lt ha hb]; split_ifs <;> omega

/-- **`lem:odd-trigid`.** -/
theorem trigid {k : ℕ} {X : Finset ℕ} (hk : k % 2 = 1) (hX : Bd k X) (hne : X.Nonempty)
    {ζ : ℕ} (hζ0 : 0 < ζ) (hζk : ζ < k)
    (hT : ∀ x ∈ X, (x + ζ) % k ∈ X ∨ (x + ζ) % k = 0) : Dil X := by
  have hstep : ∀ x ∈ X, (x + ζ) % k = if x + ζ < k then x + ζ else x + ζ - k := by
    intro x hx; have := hX x hx; exact add_mod_lt (by omega) hζk
  -- `ζ ≤ c` is impossible
  have hbig : k < 2 * ζ := by
    by_contra hc
    set xm := X.max' hne
    have hxm := X.max'_mem hne
    have hb := hX xm hxm
    have e := hstep xm hxm
    rw [if_pos (by omega)] at e
    rcases hT xm hxm with h | h
    · rw [e] at h
      have := X.le_max' _ h
      omega
    · omega
  set μ := k - ζ with hμ
  have h2 : ∀ x ∈ X, μ ≤ x ∧ (x = μ ∨ x - μ ∈ X) := by
    intro x hx
    have hb := hX x hx
    have e := hstep x hx
    by_cases hlt : x + ζ < k
    · rw [if_pos hlt] at e
      rcases hT x hx with h | h
      · rw [e] at h; have := hX _ h; omega
      · omega
    · rw [if_neg hlt] at e
      have e' : x + ζ - k = x - μ := by omega
      rw [e'] at e
      refine ⟨by omega, ?_⟩
      rcases hT x hx with h | h
      · rw [e] at h; exact Or.inr h
      · rw [e] at h; left; omega
  have hμ0 : 0 < μ := by omega
  -- every element is a multiple of `μ`
  have hdvd : ∀ x ∈ X, μ ∣ x := by
    intro x
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      intro hx
      obtain ⟨hle, h | h⟩ := h2 x hx
      · rw [h]
      · have := ih (x - μ) (by have := hX x hx; omega) h
        have e : x = (x - μ) + μ := by omega
        rw [e]; exact dvd_add this dvd_rfl
  set xm := X.max' hne
  have hxm := X.max'_mem hne
  obtain ⟨M, hM⟩ := hdvd xm hxm
  -- downward closure from the maximum
  have hdown : ∀ d, d + 1 ≤ M → μ * (M - d) ∈ X := by
    intro d
    induction d with
    | zero => intro _; rw [Nat.sub_zero, ← hM]; exact hxm
    | succ d ih =>
      intro hd
      have hin := ih (by omega)
      obtain ⟨-, h | h⟩ := h2 _ hin
      · exfalso
        have : μ * (M - d) = μ * 1 := by rw [h]; ring
        have := Nat.eq_of_mul_eq_mul_left hμ0 this
        omega
      · have e : μ * (M - d) - μ = μ * (M - (d + 1)) := by
          rw [show M - d = (M - (d + 1)) + 1 by omega, mul_add, mul_one, Nat.add_sub_cancel]
        rw [e] at h; exact h
  refine ⟨μ, M, hμ0, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨i, rfl⟩ := hdvd x hx
    have hb := hX _ hx
    have hle : μ * i ≤ μ * M := by rw [← hM]; exact X.le_max' _ hx
    refine ⟨i, ?_, Nat.le_of_mul_le_mul_left hle hμ0, rfl⟩
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp at hb
    · exact h
  · rintro ⟨i, hi1, hiM, rfl⟩
    have := hdown (M - i) (by omega)
    rwa [show M - (M - i) = i by omega] at this

/-! ## Casting residues to `ZMod k` -/

lemma cast_add_mod (k a b : ℕ) : (((a + b) % k : ℕ) : ZMod k) = a + b := by
  rw [ZMod.natCast_mod]; push_cast; ring

lemma cast_sub_mod {k a b : ℕ} (hb : b ≤ a + k) : (((a + k - b) % k : ℕ) : ZMod k) = a - b := by
  rw [ZMod.natCast_mod, Nat.cast_sub hb]; push_cast; rw [ZMod.natCast_self]; ring

lemma eq_of_cast {k a b : ℕ} (ha : a < k) (hb : b < k) (h : (a : ZMod k) = b) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- **`lem:odd-symfail`.** -/
theorem symfail {k : ℕ} {X : Finset ℕ} (hk : k % 2 = 1) (hX : Bd k X) (hne : X.Nonempty)
    {j : ℕ} (hsym : SymX k X j)
    {ζ : ℕ} (hζ0 : 0 < ζ) (hζk : ζ < k)
    (hT : ∀ x ∈ X, (x + ζ) % k ∈ X ∨ (x + ζ) % k = 0 ∨ (x + ζ) % k = j) : Dil X := by
  have hk0 : 0 < k := by omega
  have hlt : ∀ x ∈ X, x < k := fun x hx => by have := hX x hx; omega
  have hmod : ∀ n, n % k < k := fun n => Nat.mod_lt n hk0
  by_cases hJ : ∃ x ∈ X, (x + ζ) % k = j
  · by_cases h0 : ∃ x ∈ X, (x + ζ) % k = 0
    · exfalso
      obtain ⟨x₁, hx₁, h₁⟩ := h0
      obtain ⟨x₂, hx₂, h₂⟩ := hJ
      have hy := hsym x₂ hx₂
      have c₁ := cast_add_mod k x₁ ζ
      have c₂ := cast_add_mod k x₂ ζ
      have c₃ := cast_sub_mod (k := k) (a := j) (b := x₂) (by have := hlt x₂ hx₂; omega)
      rw [h₁] at c₁; rw [h₂] at c₂
      -- `y := j − x₂ ≡ ζ ≡ −x₁`, so `y + x₁ ≡ 0` with `0 < y + x₁ < k`
      have hsum : (((j + k - x₂) % k + x₁ : ℕ) : ZMod k) = ((0 : ℕ) : ZMod k) := by
        push_cast; rw [c₃]
        have e1 : (x₁ : ZMod k) = -ζ := by
          have : ((0 : ℕ) : ZMod k) = 0 := by simp
          rw [this] at c₁; linear_combination -c₁
        have e2 : (j : ZMod k) = x₂ + ζ := c₂
        rw [e1, e2]; ring
      have b₁ := hX x₁ hx₁
      have b₂ := hX _ hy
      have := eq_of_cast (by omega) hk0 hsum
      omega
    · -- exits only at `j`: reflect, and translate by `−ζ`
      push_neg at h0
      refine trigid hk hX hne (ζ := k - ζ) (by omega) (by omega) ?_
      intro y hy
      have hx := hsym y hy
      set x := (j + k - y) % k with hxdef
      have cx : (x : ZMod k) = j - y := cast_sub_mod (by have := hlt y hy; omega)
      have cy : (((y + (k - ζ)) % k : ℕ) : ZMod k) = y - ζ := by
        rw [cast_add_mod, Nat.cast_sub hζk.le, ZMod.natCast_self]; ring
      rcases hT x hx with h | h | h
      · left
        have hz := hsym _ h
        set z := (x + ζ) % k with hzdef
        have cz : (z : ZMod k) = x + ζ := cast_add_mod k x ζ
        have cw : (((j + k - z) % k : ℕ) : ZMod k) = j - z :=
          cast_sub_mod (by have := hmod (x + ζ); omega)
        have : (y + (k - ζ)) % k = (j + k - z) % k := by
          refine eq_of_cast (hmod _) (hmod _) ?_
          rw [cy, cw, cz, cx]; ring
        rw [this]; exact hz
      · exact absurd h (h0 x hx)
      · right
        have cz : (((x + ζ) % k : ℕ) : ZMod k) = x + ζ := cast_add_mod k x ζ
        rw [h, cx] at cz
        refine eq_of_cast (hmod _) hk0 ?_
        rw [cy]; push_cast; linear_combination cz
  · push_neg at hJ
    refine trigid hk hX hne hζ0 hζk ?_
    intro x hx
    rcases hT x hx with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hJ x hx)

/-- **`lem:odd-wunique`** (uniqueness of the centre of `W = X ∪ {0}`): two centres make `X`
a dilated interval. -/
theorem symW_unique {k : ℕ} {X : Finset ℕ} (hk : k % 2 = 1) (hX : Bd k X) (hne : X.Nonempty)
    {q q' : ℕ} (hq : SymW k X q) (hq' : SymW k X q') (hqq : q ≠ q') : Dil X := by
  have hk0 : 0 < k := by omega
  have hlt : ∀ x ∈ X, x < k := fun x hx => by have := hX x hx; omega
  have hmod : ∀ n, n % k < k := fun n => Nat.mod_lt n hk0
  have hqk := hlt q hq.1
  have hqk' := hlt q' hq'.1
  set ζ := (q' + k - q) % k with hζdef
  have cζ : (ζ : ZMod k) = q' - q := cast_sub_mod (by omega)
  have hζ0 : 0 < ζ := by
    rcases Nat.eq_zero_or_pos ζ with h | h
    · exfalso
      have : q' = q := by
        refine eq_of_cast hqk' hqk ?_
        have : ((ζ : ℕ) : ZMod k) = ((0 : ℕ) : ZMod k) := by rw [h]
        rw [cζ] at this; push_cast at this; linear_combination this
      exact hqq this.symm
    · exact h
  refine trigid hk hX hne hζ0 (hmod _) ?_
  intro x hx
  have cx : (((x + ζ) % k : ℕ) : ZMod k) = x + q' - q := by rw [cast_add_mod, cζ]; ring
  by_cases hxq : x = q
  · left
    have : (x + ζ) % k = q' := by
      refine eq_of_cast (hmod _) hqk' ?_
      rw [cx, hxq]; ring
    rw [this]; exact hq'.1
  · have hy := hq.2 x hx hxq
    have cy : (((q + k - x) % k : ℕ) : ZMod k) = q - x := cast_sub_mod (by have := hlt x hx; omega)
    by_cases hyq : (q + k - x) % k = q'
    · right
      refine eq_of_cast (hmod _) hk0 ?_
      rw [hyq] at cy
      rw [cx]; push_cast; linear_combination cy
    · left
      have hw := hq'.2 _ hy hyq
      have cw : (((q' + k - (q + k - x) % k) % k : ℕ) : ZMod k) = q' - ((q + k - x) % k : ℕ) :=
        cast_sub_mod (by have := hmod (q + k - x); omega)
      have : (x + ζ) % k = (q' + k - (q + k - x) % k) % k := by
        refine eq_of_cast (hmod _) (hmod _) ?_
        rw [cx, cw, cy]; ring
      rw [this]; exact hw

end OddK
end Trop
end PeriodicDifference
