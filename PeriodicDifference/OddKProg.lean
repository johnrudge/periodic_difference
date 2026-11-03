/-
# `PeriodicDifference/OddKProg.lean` — the progressions are killed (`thm:odd-rowcarrier`, `eq:odd-prog`)

At odd `k`, the residue of `thm:odd-nondil` is `S = 2μ·T_M = {2μi, k − 2μi : 1 ≤ i ≤ M}` with
`2μM < k` (`progS`).  It carries a σ-bump: the interval carrier of the base member
`S_M = 2·T_M` (`Rows.rowcarrier_hand`, needs `2M + 3 ≤ k`) transported by the block-preserving
dilation `d ≡ μ (mod k)`, `d` odd (`Dilate.bumpSat_dilate`; the unit dilation of
`sec:odd-dil`).  The dilation is block-preserving because every `2μi` and every `k − 2μi` stays below `k` modulo `2k`.
-/
import PeriodicDifference.OddRowsHand

namespace PeriodicDifference
namespace Trop
namespace OddK

open Bump

/-- The progression row `2μ·T_M`. -/
def progS (k μ M : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 M).image (fun i => 2 * μ * i)) ∪ ((Finset.Icc 1 M).image (fun i => k - 2 * μ * i))

/-- The odd representative of `μ` modulo `k`. -/
def oddRep (k μ : ℕ) : ℕ := if μ % 2 = 1 then μ else μ + k

lemma dil_low {k μ M i : ℕ} (hk : k % 2 = 1) (hi : i ≤ M) (hbd : 2 * μ * M < k) :
    oddRep k μ * (2 * i) % (2 * k) = 2 * μ * i := by
  have hle : 2 * μ * i ≤ 2 * μ * M := Nat.mul_le_mul_left _ hi
  unfold oddRep
  split_ifs with h
  · rw [show μ * (2 * i) = 2 * μ * i by ring]; exact Nat.mod_eq_of_lt (by omega)
  · rw [show (μ + k) * (2 * i) = 2 * μ * i + 2 * k * i by ring, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)

lemma dil_high {k μ M i : ℕ} (hk : k % 2 = 1) (hμ : 1 ≤ μ) (hi1 : 1 ≤ i) (hi : i ≤ M)
    (hbd : 2 * μ * M < k) :
    oddRep k μ * (k - 2 * i) % (2 * k) = k - 2 * μ * i := by
  have hle : 2 * μ * i ≤ 2 * μ * M := Nat.mul_le_mul_left _ hi
  have h2i : 2 * i ≤ 2 * μ * i := by nlinarith
  have hlt : k - 2 * μ * i < 2 * k := by omega
  rw [← Nat.mod_eq_of_lt hlt]
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd]
  push_cast [show 2 * i ≤ k by omega, show 2 * μ * i ≤ k by omega]
  unfold oddRep
  split_ifs with h
  · obtain ⟨a, rfl⟩ : ∃ a, μ = 2 * a + 1 := ⟨μ / 2, by omega⟩
    exact ⟨(a : ℤ), by push_cast; ring⟩
  · obtain ⟨a, rfl⟩ : ∃ a, μ = 2 * a := ⟨μ / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, k = 2 * b + 1 := ⟨k / 2, by omega⟩
    exact ⟨(a : ℤ) + b - i, by push_cast; ring⟩

lemma oddRep_odd {k μ : ℕ} (hk : k % 2 = 1) : oddRep k μ % 2 = 1 := by
  unfold oddRep; split_ifs <;> omega

lemma oddRep_coprime {k μ : ℕ} (hk : k % 2 = 1) (hcop : Nat.Coprime μ k) :
    Nat.Coprime (oddRep k μ) (2 * k) := by
  apply Nat.Coprime.mul_right
  · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    have := oddRep_odd (μ := μ) hk; omega
  · unfold oddRep; split_ifs
    · exact hcop
    · rw [Nat.coprime_add_self_left]; exact hcop

/-- **`thm:odd-rowcarrier` with the unit dilation of `sec:odd-proof`** (carrier form): the
progression row carries a σ-bump. -/
theorem prog_bumpSat {k μ M : ℕ} (hk : k % 2 = 1) (hM : 2 ≤ M) (h2 : 2 * M + 3 ≤ k)
    (hbd : 2 * μ * M < k) (hcop : Nat.Coprime μ k) : ∃ σ Q, BumpSat k (progS k μ M) σ Q := by
  have hrow := Rows.rowcarrier_hand hk hM h2
  have hμ : 1 ≤ μ := by
    rcases Nat.eq_zero_or_pos μ with h | h
    · subst h; simp at hcop; omega
    · exact h
  set d := oddRep k μ
  obtain ⟨e, -, he⟩ := Nat.exists_mul_mod_eq_one_of_coprime (oddRep_coprime hk hcop)
    (show 1 < 2 * k by omega)
  have hmemS : ∀ s, s ∈ Rows.rowS k M ↔ ∃ i, 1 ≤ i ∧ i ≤ M ∧ (s = 2 * i ∨ s = k - 2 * i) := by
    intro s
    simp only [Rows.rowS, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact ⟨i, hi.1, hi.2, Or.inl rfl⟩
      · exact ⟨i, hi.1, hi.2, Or.inr rfl⟩
    · rintro ⟨i, h1, h2, rfl | rfl⟩
      · exact Or.inl ⟨i, ⟨h1, h2⟩, rfl⟩
      · exact Or.inr ⟨i, ⟨h1, h2⟩, rfl⟩
  have hblock : ∀ s ∈ Rows.rowS k M, d * s % (2 * k) < k := by
    intro s hs
    obtain ⟨i, h1, h2', rfl | rfl⟩ := (hmemS s).mp hs
    · rw [dil_low hk h2' hbd]
      have : 2 * μ * i ≤ 2 * μ * M := Nat.mul_le_mul_left _ h2'
      omega
    · rw [dil_high hk hμ h1 h2' hbd]
      have : 2 * i ≤ 2 * μ * i := by nlinarith
      omega
  have hdil := Dilate.bumpSat_dilate hrow he hblock
  suffices hS : progS k μ M = Dilate.dilS k (Rows.rowS k M) d by
    rw [hS]; exact ⟨_, _, hdil⟩
  ext y
  simp only [progS, Dilate.dilS, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
  have hred : ∀ s, d * s % k = d * s % (2 * k) % k := fun s =>
    (Nat.mod_mod_of_dvd _ (dvd_mul_left k 2)).symm
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · refine ⟨2 * i, (hmemS _).mpr ⟨i, hi.1, hi.2, Or.inl rfl⟩, ?_⟩
      rw [hred, dil_low hk hi.2 hbd]
      have : 2 * μ * i ≤ 2 * μ * M := Nat.mul_le_mul_left _ hi.2
      exact Nat.mod_eq_of_lt (by omega)
    · refine ⟨k - 2 * i, (hmemS _).mpr ⟨i, hi.1, hi.2, Or.inr rfl⟩, ?_⟩
      rw [hred, dil_high hk hμ hi.1 hi.2 hbd]
      have : 0 < 2 * μ * i := by have := hi.1; positivity
      exact Nat.mod_eq_of_lt (by omega)
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨i, h1, h2', rfl | rfl⟩ := (hmemS s).mp hs
    · left
      refine ⟨i, ⟨h1, h2'⟩, ?_⟩
      rw [hred, dil_low hk h2' hbd]
      have : 2 * μ * i ≤ 2 * μ * M := Nat.mul_le_mul_left _ h2'
      exact (Nat.mod_eq_of_lt (by omega)).symm
    · right
      refine ⟨i, ⟨h1, h2'⟩, ?_⟩
      rw [hred, dil_high hk hμ h1 h2' hbd]
      have : 0 < 2 * μ * i := by positivity
      exact (Nat.mod_eq_of_lt (by omega)).symm

end OddK
end Trop
end PeriodicDifference
