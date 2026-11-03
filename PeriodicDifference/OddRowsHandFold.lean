/-
# `PeriodicDifference/OddRowsHandFold.lean` — folding the interval carrier onto `ℤ/k` (`thm:odd-rowcarrier`)

The folding step of the hand proof of `thm:odd-rowcarrier`: `g(p) = [p ∈ P]` on `ℤ`
(`gfun`, anti-periodic: `g(p + k) = 1 − g(p)`), and `γ(u) = g(2u)` (`gam`, of period `k`).
The reads of the taps `2a`, `k − 2a` at an index `i = 2s + εk` are `γ(s + a) ⊕ ε` and
`(1 − γ(s − a)) ⊕ ε` (`read_plus`, `read_minus`, in `OddRowsHand.lean`).

The folded pattern of `foldQ`: `γ(u) = [2u ∈ Q]` for `0 ≤ u ≤ c` and
`γ(−w) = 1 − [k − 2w ∈ Q]` for `1 ≤ w ≤ c` (`gam_nat`, `gam_neg`); on `A₊ = [r + 1, c]`
it is the paper's `γ(u) = [u ≡ r + 1 (mod 2)]`, `γ(−u) = 1 − γ(u)` (`gam_Aplus`,
`gam_Aminus`), which gives the hypotheses `Hand.Folded` of the arc argument (`folded`).
-/
import PeriodicDifference.OddRowsHandCore

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace Rows
namespace Hand

/-! ## `g` and `γ` -/

/-- `g(p) = [p ∈ P]` for `p ∈ ℤ`, `P` the anti-periodic set coded by `Q`. -/
def gfun (k : ℕ) (Q : Finset ℕ) (p : ℤ) : Prop := inP k Q (p % (2 * (k : ℤ))).toNat

/-- The folded pattern `γ(u) = g(2u)`. -/
def gam (k : ℕ) (Q : Finset ℕ) (u : ℤ) : Prop := gfun k Q (2 * u)

variable {k : ℕ} {Q : Finset ℕ}

lemma gfun_congr {p q : ℤ} (h : p ≡ q [ZMOD 2 * k]) : gfun k Q p ↔ gfun k Q q := by
  unfold gfun; unfold Int.ModEq at h; rw [h]

lemma gfun_nat (hk : 0 < k) (n : ℕ) : gfun k Q n ↔ inP k Q n := by
  unfold gfun
  have : ((n : ℤ) % (2 * (k : ℤ))).toNat = n % (2 * k) := by
    rw [show (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) by push_cast; ring, ← Int.natCast_mod,
      Int.toNat_natCast]
  rw [this, ← Dilate.inP_mod_two_k hk]

/-- Anti-periodicity: `g(p + k) = 1 − g(p)`. -/
lemma gfun_add_k (hk : 0 < k) (p : ℤ) : gfun k Q (p + k) ↔ ¬ gfun k Q p := by
  set n := (p % (2 * (k : ℤ))).toNat with hn
  have hn' : (n : ℤ) = p % (2 * k) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have h1 : p ≡ n [ZMOD 2 * k] := by rw [hn']; exact (Int.mod_modEq p _).symm
  have h2 : p + k ≡ ((n + k : ℕ) : ℤ) [ZMOD 2 * k] := by push_cast; exact h1.add_right _
  rw [gfun_congr h2, gfun_congr h1, gfun_nat hk, gfun_nat hk, inP_add_k hk Q n]

/-- `γ` has period `k`. -/
lemma gam_per (hk : 0 < k) (u : ℤ) : gam k Q (u + k) ↔ gam k Q u := by
  unfold gam
  rw [show 2 * (u + k) = 2 * u + k + k by ring, gfun_add_k hk, gfun_add_k hk, not_not]

/-- `γ(u) = [2u ∈ Q]` for `0 ≤ u`, `2u < k`. -/
lemma gam_nat (hk : 0 < k) {u : ℤ} (h0 : 0 ≤ u) (h1 : 2 * u < k) :
    gam k Q u ↔ 2 * u.toNat ∈ Q := by
  unfold gam
  rw [show 2 * u = ((2 * u.toNat : ℕ) : ℤ) by omega, gfun_nat hk, inP_of_lt Q (by omega)]

/-- `γ(−w) = 1 − [k − 2w ∈ Q]` for `1 ≤ w`, `2w ≤ k`. -/
lemma gam_neg (hk : 0 < k) {u : ℤ} (h0 : 1 ≤ u) (h1 : 2 * u ≤ k) :
    gam k Q (-u) ↔ k - 2 * u.toNat ∉ Q := by
  unfold gam
  have := gfun_add_k (Q := Q) hk (2 * -u)
  rw [show 2 * -u + k = ((k - 2 * u.toNat : ℕ) : ℤ) by omega, gfun_nat hk,
    inP_of_lt Q (by omega)] at this
  rw [this, not_not]

/-! ## The folded pattern of `foldQ` -/

section Pattern

variable {r : ℕ} (hk : k % 2 = 1) (hrk : 2 * r + 3 ≤ k)
include hk hrk

/-- `γ = 0` on `F₊ = [2, r]`. -/
lemma gam_Fplus {u : ℤ} (h1 : 2 ≤ u) (h2 : u ≤ r) : ¬ gam k (foldQ k r) u := by
  rw [gam_nat (by omega) (by omega) (by omega), mem_foldQ hk hrk]
  rintro (h | ⟨-, -, h, -⟩) <;> omega

/-- `γ = 1` on `F₋ = [-r, -1]`. -/
lemma gam_Fminus {u : ℤ} (h1 : 1 ≤ u) (h2 : u ≤ r) : gam k (foldQ k r) (-u) := by
  rw [gam_neg (by omega) h1 (by omega), mem_foldQ hk hrk]
  rintro (h | ⟨-, -, h, -⟩) <;> omega

/-- `γ(u) = [u ≡ r + 1 (mod 2)]` on `A₊ = [r + 1, c]`. -/
lemma gam_Aplus {u : ℤ} (h1 : r + 1 ≤ u) (h2 : 2 * u < k) :
    gam k (foldQ k r) u ↔ u % 2 = ((r : ℤ) + 1) % 2 := by
  rw [gam_nat (by omega) (by omega) h2, mem_foldQ hk hrk]
  unfold foldPat
  constructor
  · rintro (h | ⟨-, -, -, h⟩) <;> omega
  · intro h; exact Or.inr ⟨by omega, by omega, by omega, by omega⟩

/-- `γ(−u) = 1 − γ(u)` on `A₊`. -/
lemma gam_Aminus {u : ℤ} (h1 : r + 1 ≤ u) (h2 : 2 * u < k) :
    gam k (foldQ k r) (-u) ↔ ¬ u % 2 = ((r : ℤ) + 1) % 2 := by
  rw [gam_neg (by omega) (by omega) (by omega), mem_foldQ hk hrk]
  apply not_congr
  unfold foldPat
  constructor
  · rintro (h | ⟨-, -, -, h⟩) <;> omega
  · intro h; exact Or.inr ⟨by omega, by omega, by omega, by omega⟩

/-- **The folded pattern** satisfies the hypotheses of the arc argument, with
`c = k / 2`. -/
theorem folded (hr : 2 ≤ r) : Folded ((k / 2 : ℕ) : ℤ) (r : ℤ) (gam k (foldQ k r)) where
  hr := by omega
  hrc := by omega
  per u := by
    rw [show u + (2 * ((k / 2 : ℕ) : ℤ) + 1) = u + k by omega]; exact gam_per (by omega) u
  fplus u h1 h2 := gam_Fplus hk hrk h1 h2
  fminus u h1 h2 := by
    have := gam_Fminus hk hrk (u := -u) (by omega) (by omega)
    rwa [neg_neg] at this
  refl u h1 h2 := by
    rcases le_or_gt u r with h | h
    · -- on `F₊`: both sides are `1`
      have a := gam_Fminus hk hrk (u := u) (by omega) h
      have b := gam_Fplus hk hrk h1 h
      tauto
    · rw [gam_Aminus hk hrk (by omega) (by omega), gam_Aplus hk hrk (by omega) (by omega)]
  p2 := by rw [gam_Aplus hk hrk (by omega) (by omega)]
  p3 u h1 h2 := by
    rw [gam_Aplus hk hrk (by omega) (by omega), gam_Aplus hk hrk (by omega) (by omega)]
    omega

end Pattern

end Hand
end Rows
end Bump
end Trop
end PeriodicDifference
