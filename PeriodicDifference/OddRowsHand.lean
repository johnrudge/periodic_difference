/-
# `PeriodicDifference/OddRowsHand.lean` — `thm:odd-rowcarrier` by the paper's hand proof

At odd `k = 2c + 1` with `2 ≤ r ≤ c − 1`, the base member `S_r = {2a, k − 2a : 1 ≤ a ≤ r}`
carries the σ-bump `σ = 2`, `Q = foldQ k r`, the paper's folded carrier, proved as in the
paper:

* (B1) holds by construction;
* **folding** (`PeriodicDifference/OddRowsHandFold.lean`): write the index as `i = 2s + εk` with
  `s ∈ [-c, c] ∖ {0}`; the tap `2a` reads `γ(s + a) ⊕ ε` and the tap `k − 2a` reads
  `(1 − γ(s − a)) ⊕ ε` (`read_plus`, `read_minus`), and a tap is deleted exactly when its
  residue `s ± a` is `0` or `1`;
* the definition of `γ` gives its properties (i)–(iii) (`Hand.folded`);
* the **arc argument** (`PeriodicDifference/OddRowsHandCore.lean`) gives `(∗)` at every `s`
  (`Hand.Folded.core`), by the four boundary pairs and (iii).
-/
import PeriodicDifference.OddRowsHandFold

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace Rows

namespace Hand

variable {k : ℕ} {Q : Finset ℕ}

/-- The tap `2a` at the index `i = 2s + εk` reads `γ(s + a) ⊕ ε` (here `E ⟺ ε = 0`). -/
lemma read_plus (hk0 : 0 < k) {i a : ℕ} {s : ℤ} {E : Prop}
    (hi : ((i : ℤ) = 2 * s ∧ E) ∨ ((i : ℤ) = 2 * s + k ∧ ¬ E)) :
    inP k Q (i + 2 * a) ↔ (gam k Q (s + a) ↔ E) := by
  rw [← gfun_nat hk0]; unfold gam
  rcases hi with ⟨h, hE⟩ | ⟨h, hE⟩
  · rw [show ((i + 2 * a : ℕ) : ℤ) = 2 * (s + a) by push_cast; omega]; tauto
  · rw [show ((i + 2 * a : ℕ) : ℤ) = 2 * (s + a) + k by push_cast; omega, gfun_add_k hk0]
    tauto

/-- The tap `k − 2a` at the index `i = 2s + εk` reads `(1 − γ(s − a)) ⊕ ε`. -/
lemma read_minus (hk0 : 0 < k) {i a : ℕ} (ha : 2 * a ≤ k) {s : ℤ} {E : Prop}
    (hi : ((i : ℤ) = 2 * s ∧ E) ∨ ((i : ℤ) = 2 * s + k ∧ ¬ E)) :
    inP k Q (i + (k - 2 * a)) ↔ ¬ (gam k Q (s - a) ↔ E) := by
  rw [← gfun_nat hk0]; unfold gam
  rcases hi with ⟨h, hE⟩ | ⟨h, hE⟩
  · rw [show ((i + (k - 2 * a) : ℕ) : ℤ) = 2 * (s - a) + k by omega, gfun_add_k hk0]; tauto
  · rw [show ((i + (k - 2 * a) : ℕ) : ℤ) = 2 * (s - a) + k + k by omega, gfun_add_k hk0,
      gfun_add_k hk0]
    tauto

end Hand

open Hand

variable {k r : ℕ}

/-- **`thm:odd-rowcarrier`**, by the hand proof of the paper.  At odd `k` with `2 ≤ r` and
`2r + 3 ≤ k`, the base member `S_r = {2a, k − 2a : a ≤ r}` carries the σ-bump `σ = 2`,
`Q = foldQ k r`. -/
theorem rowcarrier_hand (hk : k % 2 = 1) (hr : 2 ≤ r) (hrk : 2 * r + 3 ≤ k) :
    BumpSat k (rowS k r) 2 (foldQ k r) := by
  have hk0 : 0 < k := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj; rw [mem_rowS' hk hrk] at hj; unfold Slin at hj; omega
  · rw [mem_rowS' hk hrk]; unfold Slin; omega
  · -- (B1), by construction
    ext y
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, mem_foldQ hk hrk]
    rw [mem_rowS hk hrk]
    constructor
    · rintro ⟨h1 | ⟨h0, -, h1, -⟩, h2⟩ <;> omega
    · rintro rfl; exact ⟨Or.inl rfl, Or.inr (by omega)⟩
  -- (B2)
  intro i hi0 hik
  have hF := folded hk hrk hr
  -- the half-residue `s` of the index: `i = 2s + εk`, `s ∈ [-c, c] ∖ {0}`
  obtain ⟨s, hs1, hs2, hs0, hi⟩ : ∃ s : ℤ, -((k / 2 : ℕ) : ℤ) ≤ s ∧ s ≤ ((k / 2 : ℕ) : ℤ) ∧
      s ≠ 0 ∧ (((i : ℤ) = 2 * s ∧ i % 2 = 0) ∨ ((i : ℤ) = 2 * s + k ∧ ¬ i % 2 = 0)) := by
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · exact ⟨((i / 2 : ℕ) : ℤ), by omega, by omega, by omega, Or.inl ⟨by omega, h⟩⟩
    · exact ⟨((i : ℤ) - k) / 2, by omega, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩
  -- `(∗)` at `s`, turned into a tap reading any prescribed value `T`
  have wit : ∀ T : Prop, ∃ j ∈ rowS k r, (i + j) % k ≠ 0 ∧ (i + j) % k ≠ 2 ∧
      (inP k (foldQ k r) (i + j) ↔ T) := by
    intro T
    obtain ⟨a, ha1, ha2, hpm⟩ := hF.core hs1 hs2 hs0 (i % 2 = 0 ↔ ¬ T)
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ a)
    rcases hpm with ⟨hx0, hx1, hne⟩ | ⟨hx0, hx1, hne⟩
    · -- a read of the tap `2a`
      have hd := del_lin (k := k) (σ := 2) (i := i) (j := 2 * n) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      refine ⟨2 * n, (mem_rowS hk hrk).mpr (Or.inl ⟨by omega, by omega, by omega⟩), hd.1, hd.2,
        ?_⟩
      rw [read_plus hk0 hi]; tauto
    · -- a read of the tap `k − 2a`
      have hd := del_lin (k := k) (σ := 2) (i := i) (j := k - 2 * n) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      refine ⟨k - 2 * n, (mem_rowS hk hrk).mpr (Or.inr ⟨by omega, by omega, by omega⟩), hd.1,
        hd.2, ?_⟩
      rw [read_minus hk0 (by omega) hi]; tauto
  obtain ⟨j1, hj1, a1, b1, c1⟩ := wit True
  obtain ⟨j0, hj0, a0, b0, c0⟩ := wit False
  exact ⟨⟨j1, hj1, a1, b1, c1.mpr trivial⟩, ⟨j0, hj0, a0, b0, fun h => c0.mp h⟩⟩

end Rows
end Bump
end Trop
end PeriodicDifference

