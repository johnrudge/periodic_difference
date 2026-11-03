/-
# `PeriodicDifference/AllOddOne.lean` — all-odd supports containing `1` (`prop:allodd-one`)

Paper, `sec:allodd-one`.  `S` is palindromic and all-odd at even `k`, with `1 ∈ S`:

* `lem:allodd-mid` (`mid`): for `b ∈ S` with `5 ≤ b ≤ k/2`, `σ = b`, `Q = {b − 1, b, b + 1}`;
* `lem:allodd-three4` (`three4`): for `3 ∈ S`, `k ≥ 8`, `σ = 3`, `Q = {2, 3, 6}`, used when
  `3 ∈ S`; otherwise some `b ∈ S` has `5 ≤ b ≤ k/2` and `lem:allodd-mid` applies;
* `prop:allodd-one` (`allodd_one`), the assembly.

Each carrier lemma uses only the taps `1, k − 1, b, k − b` of an otherwise arbitrary `S`, through
the witness criterion `BumpSat1.bumpSat_of_wit`; `mid` allows `b = k/2`, using parity.
-/
import PeriodicDifference.BumpSat1Basic
import PeriodicDifference.PerSupportDefs

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace AllOddOne

open Lin (Rd)
open BumpSat1

set_option maxHeartbeats 1000000 in
/-- **`lem:allodd-mid`**: `σ = b`, `Q = {b − 1, b, b + 1}` for `b ∈ S`, `5 ≤ b`, `2b ≤ k`. -/
theorem mid {k b : ℕ} {S : Finset ℕ} (hk : k % 2 = 0) (hS : BumpSat1.Pal k S)
    (hodd : ∀ j ∈ S, j % 2 = 1) (h1 : 1 ∈ S) (hb : b ∈ S) (hb5 : 5 ≤ b) (hbk : 2 * b ≤ k) :
    BumpSat k S b {b - 1, b, b + 1} := by
  have hk1 := hS.mirror h1
  have hkb := hS.mirror hb
  have hbo := hodd b hb
  refine bumpSat_of_wit (Qp := fun y => y = b - 1 ∨ y = b ∨ y = b + 1) hS.bounds
    (fun y _ => by simp only [Finset.mem_insert, Finset.mem_singleton])
    (fun y hy => by simp only [Finset.mem_insert, Finset.mem_singleton] at hy; omega)
    hb (by omega) (fun y _ hy => ?_) (fun i hi0 hik => ⟨?_, ?_⟩)
  · rcases hy with rfl | rfl | rfl
    · exact Or.inr ⟨by omega, fun h => by have := hodd _ h; omega⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨by omega, fun h => by have := hodd _ h; omega⟩
  · rcases Nat.mod_two_eq_zero_or_one i with hi | hi
    · by_cases h : i = b + 1
      · exact w1 hkb (by simp only [L1, Rd]; omega)
      · exact w1 hk1 (by simp only [L1, Rd]; omega)
    · by_cases h : i = 1
      · exact w1 hb (by simp only [L1, Rd]; omega)
      by_cases h' : i = b
      · exact w1 h1 (by simp only [L1, Rd]; omega)
      by_cases h'' : i = b + 2
      · exact w1 hkb (by simp only [L1, Rd]; omega)
      · exact w1 hk1 (by simp only [L1, Rd]; omega)
  · rcases Nat.mod_two_eq_zero_or_one i with hi | hi
    · by_cases h : i = b - 1
      · exact w0 hb (by simp only [L0, Rd]; omega)
      · exact w0 h1 (by simp only [L0, Rd]; omega)
    · by_cases h : i = k - 1 ∨ i = b - 2
      · exact w0 hb (by simp only [L0, Rd]; omega)
      by_cases h' : i = b
      · exact w0 hk1 (by simp only [L0, Rd]; omega)
      · exact w0 h1 (by simp only [L0, Rd]; omega)

set_option maxHeartbeats 1000000 in
/-- **`lem:allodd-three4`**: `σ = 3`, `Q = {2, 3, 6}` for `1, 3 ∈ S`, `k ≥ 8` (only the taps
`1, 3, k − 3, k − 1` are used). -/
theorem three4 {k : ℕ} {S : Finset ℕ} (hk : k % 2 = 0) (hS : BumpSat1.Pal k S)
    (hodd : ∀ j ∈ S, j % 2 = 1) (h1 : 1 ∈ S) (h3 : 3 ∈ S) (hk8 : 8 ≤ k) :
    BumpSat k S 3 {2, 3, 6} := by
  have hk1 := hS.mirror h1
  have hk3 := hS.mirror h3
  refine bumpSat_of_wit (Qp := fun y => y = 2 ∨ y = 3 ∨ y = 6) hS.bounds
    (fun y _ => by simp only [Finset.mem_insert, Finset.mem_singleton])
    (fun y hy => by simp only [Finset.mem_insert, Finset.mem_singleton] at hy; omega)
    h3 (by omega) (fun y _ hy => ?_) (fun i hi0 hik => ⟨?_, ?_⟩)
  · rcases hy with rfl | rfl | rfl
    · exact Or.inr ⟨by omega, fun h => by have := hodd _ h; omega⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨by omega, fun h => by have := hodd _ h; omega⟩
  · rcases Nat.mod_two_eq_zero_or_one i with hi | hi
    · by_cases h : i = 4
      · exact w1 hk3 (by simp only [L1, Rd]; omega)
      · exact w1 hk1 (by simp only [L1, Rd]; omega)
    · by_cases h : i = 1
      · exact w1 h1 (by simp only [L1, Rd]; omega)
      by_cases h' : i = 3
      · exact w1 h3 (by simp only [L1, Rd]; omega)
      by_cases h'' : i = 7
      · exact w1 hk3 (by simp only [L1, Rd]; omega)
      · exact w1 hk1 (by simp only [L1, Rd]; omega)
  · rcases Nat.mod_two_eq_zero_or_one i with hi | hi
    · by_cases h : i = 2
      · exact w0 h3 (by simp only [L0, Rd]; omega)
      · exact w0 h1 (by simp only [L0, Rd]; omega)
    · by_cases h : i = 1 ∨ i = k - 1
      · exact w0 h3 (by simp only [L0, Rd]; omega)
      by_cases h' : i = 5
      · exact w0 hk3 (by simp only [L0, Rd]; omega)
      · exact w0 h1 (by simp only [L0, Rd]; omega)

/-- **`prop:allodd-one`**: an all-odd palindromic support at even `k` containing `1`, with at
least three elements and other than `(6, {1,3,5})`, carries a σ-bump. -/
theorem allodd_one {k : ℕ} {S : Finset ℕ} (hk : k % 2 = 0) (hsub : S ⊆ Finset.Icc 1 (k - 1))
    (hodd : ∀ j ∈ S, j % 2 = 1) (hpal : PerSupport.Pal k S) (h1 : 1 ∈ S) (h3 : 3 ≤ S.card)
    (h6 : ¬ (k = 6 ∧ S = {1, 3, 5})) : ∃ σ Q, BumpSat k S σ Q := by
  have hmem : ∀ j ∈ S, 0 < j ∧ j < k := by
    intro j hj; have := Finset.mem_Icc.mp (hsub hj); omega
  have hS : BumpSat1.Pal k S := ⟨hmem, hpal⟩
  by_cases h3S : 3 ∈ S
  · -- `3 ∈ S`: `lem:allodd-three4`, once `k ≥ 8`
    rcases Nat.lt_or_ge k 8 with hk8 | hk8
    · exfalso
      have hsub' : S ⊆ {1, 3, 5} := fun s hs => by
        have := hodd s hs; have := hmem s hs
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      have hk6 : k = 6 := by
        by_contra hne
        have hsub'' : S ⊆ {1, 3} := fun s hs => by
          have := hodd s hs; have := hmem s hs
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        have := Finset.card_le_card hsub''
        have := Finset.card_le_two (a := 1) (b := 3)
        omega
      have hc : ({1, 3, 5} : Finset ℕ).card ≤ S.card := by
        have : ({1, 3, 5} : Finset ℕ).card = 3 := by decide
        omega
      exact h6 ⟨hk6, Finset.eq_of_subset_of_card_le hsub' hc⟩
    · exact ⟨_, _, three4 hk hS hodd h1 h3S hk8⟩
  -- `3 ∉ S`: an element `b` with `5 ≤ b ≤ k/2`, `lem:allodd-mid`
  have hb : ∃ b ∈ S, 5 ≤ b ∧ 2 * b ≤ k := by
    by_contra hb
    push_neg at hb
    have hsub' : S ⊆ {1, k - 1} := fun s hs => by
      have hso := hodd s hs
      have hsk := hmem s hs
      have hm := hpal s hs
      have hmo := hodd _ hm
      have hmk := hmem _ hm
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h2 : 2 * s ≤ k
      · rcases Nat.lt_or_ge s 5 with h | h
        · have : s ≠ 3 := fun e => h3S (e ▸ hs)
          omega
        · have := hb s hs h; omega
      · rcases Nat.lt_or_ge (k - s) 5 with h | h
        · have : k - s ≠ 3 := fun e => h3S (e ▸ hm)
          omega
        · have := hb _ hm h; omega
    have := Finset.card_le_card hsub'
    have := Finset.card_le_two (a := 1) (b := k - 1)
    omega
  obtain ⟨b, hbS, hb5, hbk⟩ := hb
  exact ⟨_, _, mid hk hS hodd h1 hbS hb5 hbk⟩

end AllOddOne
end Bump
end Trop
end PeriodicDifference
