/-
# `PeriodicDifference/AllOddAll.lean` — every primitive all-odd support carries a σ-bump (`thm:alloddall`)

The proof of `thm:alloddall` (`sec:allodd-proof`), from Lemma A (`E3All.LemmaA`, `thm:lemmaA`)
as a hypothesis; it is proved as `Problem11.lemmaA` (`PeriodicDifference/Problem11Prim.lean`):

* `1 ∈ S` — `AllOddOne.allodd_one` (`prop:allodd-one`);
* a support of `tab:allodd-base` — `AllOddBase.base` (`lem:allodd-base`);
* a second element below `k/2` — `E3All.bumpSat_e3all` (`thm:allodd-e3all` and
  `prop:allodd-e3bump`: a half-arc carrier with a unit multiplier and `t ∈ {0, k}`);
* otherwise `S = {a, k/2, k − a}`, with `3δ < h = k/2` since the five pairs with `3δ ≥ h` are in
  the table — `ThreeAll.threeall` (`thm:allodd-threeall`).
-/
import PeriodicDifference.AllOddOne
import PeriodicDifference.E3All
import PeriodicDifference.ThreeAll

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace AllOddAll

open Finset

variable {k : ℕ} {S : Finset ℕ}

/-- A common divisor of every element of `S` and of `k` is `1`, for a primitive `S`. -/
lemma dvd_one_of_prim (hP : PerSupport.Prim k S) {g : ℕ} (hS : ∀ j ∈ S, g ∣ j) (hk : g ∣ k) :
    g = 1 := by
  have h1 : g ∣ S.gcd id := Finset.dvd_gcd (fun j hj => hS j hj)
  have h2 : g ∣ Nat.gcd (S.gcd id) k := Nat.dvd_gcd h1 hk
  unfold PerSupport.Prim at hP
  rw [hP] at h2
  exact Nat.dvd_one.mp h2

/-- With only one element below `k/2`, the support is `{a, k/2, k − a}`. -/
lemma three_of_no_second {a : ℕ} (hsub : S ⊆ Icc 1 (k - 1)) (hpal : PerSupport.Pal k S)
    (hno : ¬ ∃ x ∈ S, 2 * x < k ∧ x ≠ a) :
    ∀ s ∈ S, s = a ∨ 2 * s = k ∨ s = k - a := by
  intro s hs
  have hs' := mem_Icc.mp (hsub hs)
  rcases Nat.lt_trichotomy (2 * s) k with h | h | h
  · left; by_contra hne; exact hno ⟨s, hs, h, hne⟩
  · right; left; exact h
  · right; right
    have hks := hpal s hs
    have hks' := mem_Icc.mp (hsub hks)
    by_contra hne
    exact hno ⟨k - s, hks, by omega, by omega⟩

/-- **`thm:alloddall`, granted Lemma A.**  Every primitive palindromic all-odd support at
even `k` with at least three elements, other than `(6, {1,3,5})`, carries a σ-bump. -/
theorem alloddall (hA : E3All.LemmaA) (hk : k % 2 = 0) (hsub : S ⊆ Icc 1 (k - 1))
    (hodd : ∀ j ∈ S, j % 2 = 1) (hpal : PerSupport.Pal k S) (hP : PerSupport.Prim k S)
    (h3 : 3 ≤ S.card) (h6 : ¬ (k = 6 ∧ S = {1, 3, 5})) :
    ∃ σ Q, BumpSat k S σ Q := by
  have hmem : ∀ j ∈ S, 0 < j ∧ j < k := by
    intro j hj; have := mem_Icc.mp (hsub hj); omega
  have hne : S.Nonempty := by
    rw [← Finset.card_pos]; omega
  -- supports containing `1`
  by_cases h1 : 1 ∈ S
  · exact AllOddOne.allodd_one hk hsub hodd hpal h1 h3 h6
  -- the table supports
  by_cases hT : (k, S) ∈ AllOddBase.tabKS
  · exact AllOddBase.base hT
  -- the least element
  obtain ⟨a, ha, hmin⟩ := S.exists_min_image id hne
  simp only [id] at hmin
  have hao := hodd a ha
  have ha1 : 1 < a := by
    have := (hmem a ha).1
    rcases Nat.lt_or_ge 1 a with h | h
    · exact h
    · exfalso; exact h1 (by have : a = 1 := by omega
                            exact this ▸ ha)
  have hb : Shadow.AllOddPal k S a := ⟨⟨hmem, hpal, ha, hmin⟩, hk, hodd⟩
  by_cases hsec : ∃ x ∈ S, 2 * x < k ∧ x ≠ a
  · obtain ⟨d, t, h⟩ := E3All.bumpSat_e3all hA hb hP h1 hsec hT
    exact ⟨a, _, h⟩
  -- one element below `k/2`: `S = {a, k/2, k − a}`
  have hthree := three_of_no_second hsub hpal hsec
  have hka := hpal a ha
  have h2a : 2 * a < k := by
    have := hmin (k - a) hka
    rcases Nat.lt_or_ge (2 * a) k with h | h
    · exact h
    · exfalso
      -- every element would be `k/2`, so `S` has one element
      have hall : ∀ s ∈ S, s = a := by
        intro s hs
        have := hmin s hs; have := hmin (k - s) (hpal s hs)
        have := hmem s hs; omega
      have : S ⊆ {a} := fun s hs => mem_singleton.mpr (hall s hs)
      have := Finset.card_le_card this
      simp at this; omega
  have hSeq : S = {a, k / 2, k - a} := by
    ext s
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hs
      rcases hthree s hs with h | h | h
      · left; exact h
      · right; left; omega
      · right; right; exact h
    · rintro (rfl | rfl | rfl)
      · exact ha
      · -- `k/2 ∈ S`: otherwise `S ⊆ {a, k − a}` has at most two elements
        by_contra hnot
        have : S ⊆ {a, k - a} := by
          intro s hs
          rcases hthree s hs with h | h | h
          · simp [h]
          · exfalso; exact hnot (by have : s = k / 2 := by omega
                                    exact this ▸ hs)
          · simp [h]
        have := Finset.card_le_card this
        have := Finset.card_le_two (a := a) (b := k - a)
        omega
      · exact hka
  have hmid : k / 2 ∈ S := by rw [hSeq]; simp
  have hk4 : k % 4 = 2 := by have := hodd _ hmid; omega
  have hcop : Nat.Coprime a (k / 2) := by
    apply dvd_one_of_prim hP
    · intro j hj
      rw [hSeq] at hj
      simp only [mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl | rfl
      · exact Nat.gcd_dvd_left _ _
      · exact Nat.gcd_dvd_right _ _
      · exact Nat.dvd_sub (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.div_dvd_of_dvd
          (Nat.dvd_of_mod_eq_zero hk))) (Nat.gcd_dvd_left _ _)
    · exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero hk))
  rw [hSeq] at hT ⊢
  by_cases hk26 : 26 ≤ k ∨ (14 ≤ k ∧ (a + k / 2) % 4 = 2)
  swap
  · -- `h = k/2 ≤ 11` and `3δ ≥ h`: the support is in `tab:allodd-base`
    have hak : a < k / 2 := by omega
    exfalso
    have hk26' : k < 26 := by omega
    interval_cases k <;> (try omega) <;> interval_cases a <;> (try omega) <;>
      first
      | exact absurd hcop (by decide)
      | exact hT (by decide)
  obtain ⟨d, h⟩ := ThreeAll.threeall k a hk4 hk26 hao ha1 (by omega) hcop
  exact ⟨a, _, h⟩

end AllOddAll
end Bump
end Trop
end PeriodicDifference
