/-
# `PeriodicDifference/NotAllOddShadow.lean` — `lem:nao-bfshadow`, the both-failing supports with `M ≥ 2`

Under the structure `BF k S a μ M` of `thm:nao-struct` (`μ` the paper's `b`) with `M ≥ 2`, `σ = a`
with the band carrier `Q = {a} ∪ 𝓑`, `𝓑 = {y ∉ S : a < y < k − a}` (`bandW`), is a σ-bump
(`BF.bumpSat_shadow`).  As in the paper: (N1) `mult_mem`, (N2) `free_odd`, (N3) `window`; a read `1`
at every index for `(z, {z} ∪ 𝓑)` with `z ∈ {a, k − a}` (`BF.oneRead`), and the reads `0` for
`(a, Q)` by the mirror (`r0_of_mirror`, `lem:nao-mirror`) from `z = k − a`.
-/
import PeriodicDifference.NotAllOddBF

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace NotAllOdd

open Finset

variable {k : ℕ} {S : Finset ℕ} {a μ M : ℕ}

/-- The set `𝓑` of free positions strictly between `a` and `k − a`. -/
def bandW (k : ℕ) (S : Finset ℕ) (a : ℕ) : Finset ℕ := (Ioo a (k - a)).filter (· ∉ S)

lemma mem_bandW {y : ℕ} : y ∈ bandW k S a ↔ a < y ∧ y < k - a ∧ y ∉ S := by
  simp [bandW, and_assoc]

/-- A multiple of `μ` is never strictly between two consecutive multiples. -/
lemma mul_ne_between {μ q r : ℕ} (h1 : μ * q < r) (h2 : r < μ * (q + 1)) (m : ℕ) :
    μ * m ≠ r := by
  intro h
  rcases Nat.lt_or_ge q m with hm | hm
  · have := Nat.mul_le_mul_left μ (show q + 1 ≤ m by omega); omega
  · have := Nat.mul_le_mul_left μ hm; omega

namespace BF

variable (H : BF k S a μ M)
include H

/-- (N2): an odd position whose offset from `a` is not a multiple of `μ` is free. -/
lemma free_odd {y : ℕ} (hy : y % 2 = 1) (hya : a ≤ y) (q : ℕ) (h1 : μ * q < y - a)
    (h2 : y - a < μ * (q + 1)) : y ∉ S := by
  intro hS
  obtain ⟨m, -, hm⟩ := H.odd_mem y hS hy
  exact mul_ne_between h1 h2 m (by omega)

/-- (N1): the multiples `μm`, `1 ≤ m ≤ M`, lie in `S` (mirrors of the core). -/
lemma mult_mem {m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ M) : μ * m ∈ S := by
  have h := H.pal _ (H.core (M - m) (by omega))
  have hk := H.hk
  have e : μ * (M - m) + μ * m = μ * M := by rw [← Nat.mul_add]; congr 1; omega
  rwa [show k - (2 * a + μ * (M - m)) = μ * m by omega] at h

/-- Every `s ∈ S` below `k − a` has an element of `S` in `(s, s + a]`. -/
lemma gap {s : ℕ} (hs : s ∈ S) (hsk : s < k - a) : ∃ y ∈ S, s < y ∧ y ≤ s + a := by
  have hk := H.hk
  have hax := H.amin s hs
  have haμ := H.a_lt
  have hμ2 := H.lt_2a
  have hμ0 : 0 < μ := by omega
  obtain ⟨t, r, hdm, hr⟩ : ∃ t r, μ * t + r = s ∧ r < μ :=
    ⟨s / μ, s % μ, Nat.div_add_mod s μ, Nat.mod_lt s hμ0⟩
  rcases Nat.lt_or_ge r a with hra | hra
  · have htM : t ≤ M := by
      have : μ * t < μ * (M + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
      exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left this)
    exact ⟨a + μ * t, H.ap_mem t htM, by omega, by omega⟩
  · have htM : t + 1 ≤ M := by
      have : μ * t < μ * M := by omega
      exact Nat.lt_of_mul_lt_mul_left this
    refine ⟨μ * (t + 1), H.mult_mem (by omega) htM, ?_, ?_⟩ <;>
      rw [Nat.mul_add, Nat.mul_one] <;> omega

/-- (N3): for `a < x ≤ k − a`, some element of `S` lies in `[x, x + a)`. -/
lemma window {x : ℕ} (hax : a < x) (hx : x ≤ k - a) : ∃ j ∈ S, x ≤ j ∧ j < x + a := by
  classical
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image (S.filter (fun y => y < x)) id
    ⟨a, Finset.mem_filter.mpr ⟨H.ha, hax⟩⟩
  rw [Finset.mem_filter] at hs
  obtain ⟨y, hyS, hsy, hys⟩ := H.gap hs.1 (by omega)
  refine ⟨y, hyS, ?_, by omega⟩
  by_contra hyx
  have := hmax y (Finset.mem_filter.mpr ⟨hyS, by omega⟩)
  simp only [id] at this
  omega

/-- **The reads `1`.**  For `z ∈ {a, k − a}` and `Q = {z} ∪ 𝓑` on `(0, k)`, every index has
a surviving tap reading `1`. -/
theorem oneRead (hM : 2 ≤ M) {z : ℕ} (hz : z = a ∨ z = k - a) {Q : Finset ℕ}
    (hQ : ∀ y, 0 < y → y < k → (y ∈ Q ↔ y ∈ bandW k S a ∨ y = z)) {i : ℕ} (hi0 : 0 < i)
    (hik : i < k) : R1 k S z Q i := by
  have hk := H.hk
  have haμ := H.a_lt
  have hμ2 := H.lt_2a
  have hao := H.hao
  have hμe := H.hμe
  have hP : μ * 2 ≤ μ * M := Nat.mul_le_mul_left μ hM
  have hS := H.sub
  have hW : ∀ y, y ∈ bandW k S a → y ∈ Q := fun y hy => by
    have := mem_bandW.mp hy; exact (hQ y (by omega) (by omega)).mpr (Or.inl hy)
  have hnz : ∀ y, z = y → a < y → y < k - a → False := by
    intro y e h1 h2; rcases hz with hz | hz <;> omega
  rcases Nat.lt_or_ge a i with hia | hia
  · -- `i > a`: the tap `k − a` reads the wrapped position `i − a`
    by_cases hWi : i - a ∈ bandW k S a
    · have hb := mem_bandW.mp hWi
      obtain ⟨j, hjS, hxj, hjx⟩ := H.window (x := i - a) hb.1 (by omega)
      have hjk := hS j hjS
      have hyz : i + (k - j) - k ≠ z := by
        intro e
        rcases hz with hz | hz
        · exact hb.2.2 (by rw [show i - a = j by omega]; exact hjS)
        · omega
      refine r1hi (H.pal j hjS) (by omega) (by omega) hyz ?_
      rw [hQ _ (by omega) (by omega), mem_bandW]
      rintro (⟨h1, -, -⟩ | h1)
      · omega
      · exact hyz h1
    by_cases hzi : i - a = z
    · -- `i = 2a`: the tap `k − μ` reads `2a − μ`
      have hi2a : i = 2 * a := by rcases hz with hz | hz <;> omega
      have hyz : i + (k - μ) - k ≠ z := by rcases hz with hz | hz <;> omega
      refine r1hi (H.pal μ H.hμ) (by omega) (by omega) hyz ?_
      rw [hQ _ (by omega) (by omega), mem_bandW]
      rintro (⟨h1, -, -⟩ | h1)
      · omega
      · exact hyz h1
    · refine r1hi (H.pal a H.ha) (by omega) (by omega) (by omega) ?_
      rw [show i + (k - a) - k = i - a by omega, hQ _ (by omega) (by omega)]
      rintro (h | h)
      · exact hWi h
      · exact hzi h
  · rcases Nat.lt_or_ge i a with hia' | hia'
    · rcases Nat.mod_two_eq_zero_or_one i with hie | hio
      · -- the tap `a` reads `i + a`
        refine r1lo H.ha (by omega) (by omega) (fun e => hnz _ e.symm (by omega) (by omega)) (hW _ ?_)
        exact mem_bandW.mpr ⟨by omega, by omega,
          H.free_odd (by omega) (by omega) 0 (by omega) (by omega)⟩
      · -- the tap `μ` reads `i + μ`
        refine r1lo H.hμ (by omega) (by omega) (fun e => hnz _ e.symm (by omega) (by omega)) (hW _ ?_)
        exact mem_bandW.mpr ⟨by omega, by omega,
          H.free_odd (by omega) (by omega) 0 (by omega) (by omega)⟩
    · -- `i = a`: the tap `2a` reads `3a`
      have hia2 : i = a := by omega
      subst hia2
      have h2a := H.core 0 (by omega)
      rw [Nat.mul_zero, Nat.add_zero] at h2a
      refine r1lo h2a (by omega) (by omega) (fun e => hnz _ e.symm (by omega) (by omega)) (hW _ ?_)
      exact mem_bandW.mpr ⟨by omega, by omega,
        H.free_odd (by omega) (by omega) 1 (by omega) (by omega)⟩

/-- **`lem:nao-bfshadow`.** -/
theorem bumpSat_shadow (hM : 2 ≤ M) : BumpSat k S a (insert a (bandW k S a)) where
  S_sub := H.sub
  σ_mem := H.ha
  B1 := by
    ext y
    simp only [mem_inter, mem_insert, mem_singleton, mem_bandW]
    constructor
    · rintro ⟨h1 | ⟨h0, -, h1⟩, h2⟩
      · exact h1
      · rcases h2 with rfl | h2
        · omega
        · exact absurd h2 h1
    · rintro rfl
      exact ⟨Or.inl rfl, Or.inr H.ha⟩
  B2 := fun i hi0 hik => by
    have hak := (H.sub a H.ha).2
    have hk := H.hk
    refine ⟨H.oneRead hM (Or.inl rfl) (fun y _ _ => by simp only [mem_insert]; tauto) hi0 hik,
      r0_of_mirror H.sub H.pal hak (Q' := insert (k - a) (bandW k S a)) ?_ hi0 hik
        (H.oneRead hM (Or.inr rfl) (fun y _ _ => by simp only [mem_insert]; tauto)
          (by omega) (by omega))⟩
    intro y hy0 hyk
    simp only [mem_insert, mem_bandW]
    have hsym : k - y ∈ S ↔ y ∈ S := ⟨fun h => by
      have := H.pal _ h; rwa [show k - (k - y) = y by omega] at this, H.pal y⟩
    rw [hsym]
    constructor
    · rintro (h | ⟨h1, h2, h3⟩)
      · left; omega
      · right; exact ⟨by omega, by omega, h3⟩
    · rintro (h | ⟨h1, h2, h3⟩)
      · left; omega
      · right; exact ⟨by omega, by omega, h3⟩

end BF

end NotAllOdd
end Bump
end Trop
end PeriodicDifference
