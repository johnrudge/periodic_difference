/-
# `PeriodicDifference/NotAllOddStruct.lean` — `lem:nao-endend` and `thm:nao-struct` at odd minimum

`Setup k S a μ` with `a = min S` odd and `μ = min S₀` (the paper's `b`) the least even
element.  The failures of the class-`c` parity carrier (missing reads `1`) are localised
(`loc0`, `loc1`):

* class `0`: at `i = a` (`E0`: `Cont 0 a`) or an odd index `i₀` of the inner range `(a, μ]` (`B0`);
* class `1`: at an odd `i₁ ≤ a` (`E1`) or an even index `i₁` of the inner range `(a, μ]` (`B1`).

`B0` empties `S₁ ∩ (i₀, i₀ + μ)` (`gapB0`), which kills `B0` against `B1` and against `E1`;
`E0` against `E1` forces the full support (`full_of_E0E1`, the proof of `lem:nao-endend`);
`E0` against `B1` gives the structure (`struct_E0B1`).
-/
import PeriodicDifference.NotAllOddBasic

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace NotAllOdd

open Parity EvenMin

variable {k : ℕ} {S : Finset ℕ} {a μ : ℕ}

/-- Class-`0` localisation. -/
theorem loc0 (H : Setup k S a μ) (hao : a % 2 = 1) {σ i : ℕ} (hσ : σ ∈ S) (hσe : σ % 2 = 0)
    (hi0 : 0 < i) (hik : i < k) (hno : ¬ OneRead k S σ 0 i) :
    Cont k S 0 i ∧ (i = a ∨ (i % 2 = 1 ∧ a < i ∧ i ≤ μ)) := by
  have hC := cont_of_noread hσ hno hi0
  refine ⟨hC, ?_⟩
  have hk2 := H.keven
  have hak := H.sub a H.ha
  have hμ := H.sub μ H.hb
  have hμe : μ % 2 = 0 := by have := H.bpar; omega
  have haμ := H.a_lt_b
  rcases lt_trichotomy i a with h | h | h
  · exfalso
    rcases Nat.mod_two_eq_zero_or_one i with hp | hp
    · have := hC (k - μ) (H.pal μ H.hb) (by omega) (by omega)
      have := H.le_kb this (by omega); omega
    · have := hC (k - a) (H.pal a H.ha) (by omega) (by omega)
      have := H.le_ka this; omega
  · exact Or.inl h
  · obtain ⟨h1, h2⟩ := paritydichotomy H hσe hik h hno
    exact Or.inr ⟨by omega, h, h1⟩

/-- Class-`1` localisation. -/
theorem loc1 (H : Setup k S a μ) (hao : a % 2 = 1) {σ i : ℕ} (hσ : σ ∈ S) (hσo : σ % 2 = 1)
    (hi0 : 0 < i) (hik : i < k) (hno : ¬ OneRead k S σ 1 i) :
    Cont k S 1 i ∧ ((i % 2 = 1 ∧ i ≤ a) ∨ (i % 2 = 0 ∧ a < i ∧ i ≤ μ)) := by
  have hC := cont_of_noread hσ hno hi0
  refine ⟨hC, ?_⟩
  have hk2 := H.keven
  have hak := H.sub a H.ha
  by_cases h : a < i
  · obtain ⟨h1, h2⟩ := paritydichotomy H hσo hik h hno
    exact Or.inr ⟨by omega, h, h1⟩
  · left
    rcases Nat.mod_two_eq_zero_or_one i with hp | hp
    · exfalso
      have := hC (k - a) (H.pal a H.ha) (by omega) (by omega)
      have := H.le_ka this; omega
    · exact ⟨hp, by omega⟩

/-- `B0` empties `S₁ ∩ (i₀, i₀ + μ)`. -/
theorem gapB0 (H : Setup k S a μ) (hao : a % 2 = 1) {i₀ : ℕ} (hC : Cont k S 0 i₀) (h1 : i₀ % 2 = 1)
    {s : ℕ} (hs : s ∈ S) (hso : s % 2 = 1) (hlo : i₀ < s) (hhi : s < i₀ + μ) : False := by
  have hk2 := H.keven
  have hsk := H.sub s hs
  have hμe : μ % 2 = 0 := by have := H.bpar; omega
  have := hC (k - s) (H.pal s hs) (by omega) (by omega)
  have := H.le_kb this (by omega)
  omega

/-- `B0` against `E1`. -/
theorem no_B0_E1 (H : Setup k S a μ) (hao : a % 2 = 1) {i₀ i₁ : ℕ} (hC0 : Cont k S 0 i₀) (h0o : i₀ % 2 = 1)
    (hai₀ : a < i₀) (hi₀ : i₀ ≤ μ) (hC1 : Cont k S 1 i₁) (h1o : i₁ % 2 = 1) (hi₁ : i₁ ≤ a) :
    False := by
  have hk2 := H.keven
  have hμe : μ % 2 = 0 := by have := H.bpar; omega
  have := H.b_le
  have hm := hC1 μ H.hb (by omega) (by omega)
  exact gapB0 H hao hC0 h0o hm (by omega) (by omega) (by omega)

/-- `B0` against `B1`. -/
theorem no_B0_B1 (H : Setup k S a μ) (hao : a % 2 = 1) {i₀ i₁ : ℕ} (hC0 : Cont k S 0 i₀)
    (h0o : i₀ % 2 = 1) (hai₀ : a < i₀) (hi₀ : i₀ ≤ μ) (hC1 : Cont k S 1 i₁) (h1e : i₁ % 2 = 0)
    (hai₁ : a < i₁) (hi₁ : i₁ ≤ μ) : False := by
  classical
  have hk2 := H.keven
  have hμe : μ % 2 = 0 := by have := H.bpar; omega
  have hbl := H.b_le
  have hbk := H.bk
  set F := S.filter (fun s => s % 2 = 1 ∧ s ≤ i₀) with hF
  have hne : F.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨H.ha, hao, by omega⟩⟩
  obtain ⟨hxS, hxo, hxi⟩ := Finset.mem_filter.mp (F.max'_mem hne)
  set x := F.max' hne
  have hx1 := hC1 x hxS (by omega) (by omega)
  have hgt : i₀ < i₁ + x := by
    by_contra hle
    have := F.le_max' (i₁ + x) (Finset.mem_filter.mpr ⟨hx1, by omega, by omega⟩)
    omega
  have hge : i₀ + μ ≤ i₁ + x := by
    by_contra hlt
    exact gapB0 H hao hC0 h0o hx1 (by omega) hgt (by omega)
  have ha1 := hC1 a H.ha (by omega) (by omega)
  exact gapB0 H hao hC0 h0o ha1 (by omega) (by omega) (by omega)

end NotAllOdd
end Bump
end Trop
end PeriodicDifference
