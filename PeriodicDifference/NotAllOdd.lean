/-
# `PeriodicDifference/NotAllOdd.lean` — `cor:nao-bothfailing` and `thm:notallodd`

Every primitive palindromic support at even order that is not all-odd and not the full
support carries a σ-bump.  Even minimum: `thm:nao-evenmin` (`EvenMin.evenmin_carrier`).  Odd
minimum: a parity carrier, or both fail for every `σ` and `cor:nao-bothfailing` applies — the
structure of `thm:nao-struct` (`bothfail_struct`), then `lem:nao-bfone` at `M = 1` and
`lem:nao-bfshadow` at `M ≥ 2`.
-/
import PeriodicDifference.NotAllOddOne
import PeriodicDifference.NotAllOddShadow
import PeriodicDifference.PerSupportDefs

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace NotAllOdd

open Parity EvenMin

variable {k : ℕ} {S : Finset ℕ} {a : ℕ}

/-- The structure with `M = 1` satisfies the hypotheses of `lem:nao-bfone`. -/
lemma BF.oneHyp {μ : ℕ} (H : BF k S a μ 1) : OneHyp k S a μ := by
  have hk := H.hk
  have haμ := H.a_lt
  have hμ2 := H.lt_2a
  refine
    { sub := H.sub, pal := H.pal, hk := by omega, hao := H.hao, hbe := H.hμe, hab := haμ
      hb2 := hμ2, ha := H.ha, hb := H.hμ, odd := ?_, even := ?_ }
  · intro s hs hso
    obtain ⟨m, hm, rfl⟩ := H.odd_mem s hs hso
    interval_cases m <;> simp
  · intro s hs hse
    have hsk := H.sub s hs
    have h1 := H.μmin s hs hse
    have h2 := H.μmin _ (H.pal s hs) (by have := H.keven; omega)
    omega

/-- **`cor:nao-bothfailing`.**  If both parity carriers fail for every `σ` of their class, `S`
has a σ-bump carrier at `σ = a`. -/
theorem bothfailing (hk2 : k % 2 = 0) (hS : ∀ j ∈ S, 0 < j ∧ j < k)
    (hpal : ∀ j ∈ S, k - j ∈ S) (hprim : ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ k → d = 1)
    (ha : a ∈ S) (hamin : ∀ s ∈ S, a ≤ s) (hao : a % 2 = 1)
    (heven : ∃ s ∈ S, s % 2 = 0) (hfull : ∃ y, 0 < y ∧ y < k ∧ y ∉ S)
    (F0 : ∀ σ ∈ S, σ % 2 = 0 → ¬ BumpSat k S σ (parQ k S σ 0))
    (F1 : ∀ σ ∈ S, σ % 2 = 1 → ¬ BumpSat k S σ (parQ k S σ 1)) :
    ∃ Q, BumpSat k S a Q := by
  obtain ⟨μ, M, H⟩ := bothfail_struct hk2 hS hpal hprim ha hamin hao heven hfull F0 F1
  rcases Nat.lt_or_ge M 2 with hM | hM
  · have hM1 : M = 1 := by have := H.M_pos; omega
    subst hM1
    exact ⟨_, H.oneHyp.bumpSat⟩
  · exact ⟨_, H.bumpSat_shadow hM⟩

/-- **`thm:notallodd`.**  Even `k`, `S ⊆ (0, k)` primitive, palindromic, not all-odd and not
the full support: `S` carries a σ-bump. -/
theorem notallodd (hk2 : k % 2 = 0) (hS : ∀ j ∈ S, 0 < j ∧ j < k)
    (hpal : ∀ j ∈ S, k - j ∈ S) (hprim : ∀ d, (∀ s ∈ S, d ∣ s) → d ∣ k → d = 1)
    (heven : ∃ s ∈ S, s % 2 = 0) (hfull : ∃ y, 0 < y ∧ y < k ∧ y ∉ S) :
    ∃ σ Q, BumpSat k S σ Q := by
  have hne : S.Nonempty := by obtain ⟨s, hs, -⟩ := heven; exact ⟨s, hs⟩
  have ha := S.min'_mem hne
  have hamin : ∀ s ∈ S, S.min' hne ≤ s := fun s hs => S.min'_le s hs
  rcases Nat.mod_two_eq_zero_or_one (S.min' hne) with hae | hao
  · obtain ⟨σ, -, c, hB⟩ := evenmin_carrier hk2 hS hpal hprim ha hamin hae
    exact ⟨σ, _, hB⟩
  · by_cases h0 : ∃ σ ∈ S, σ % 2 = 0 ∧ BumpSat k S σ (parQ k S σ 0)
    · obtain ⟨σ, -, -, hB⟩ := h0; exact ⟨σ, _, hB⟩
    by_cases h1 : ∃ σ ∈ S, σ % 2 = 1 ∧ BumpSat k S σ (parQ k S σ 1)
    · obtain ⟨σ, -, -, hB⟩ := h1; exact ⟨σ, _, hB⟩
    push_neg at h0 h1
    obtain ⟨Q, hQ⟩ := bothfailing hk2 hS hpal hprim ha hamin hao heven hfull h0 h1
    exact ⟨_, Q, hQ⟩

/-- `thm:notallodd` with the `PerSupport` predicates: `S ⊆ [1, k − 1]`, `Pal k S`,
`Prim k S`, some even element, `S ≠ [1, k − 1]`. -/
theorem notallodd' (hk2 : k % 2 = 0) (hsub : S ⊆ Finset.Icc 1 (k - 1))
    (hpal : PerSupport.Pal k S) (hprim : PerSupport.Prim k S)
    (heven : ∃ s ∈ S, s % 2 = 0) (hfull : S ≠ Finset.Icc 1 (k - 1)) :
    ∃ σ Q, BumpSat k S σ Q := by
  have hS : ∀ j ∈ S, 0 < j ∧ j < k := by
    intro j hj
    have := Finset.mem_Icc.mp (hsub hj)
    obtain ⟨s, hs, -⟩ := heven
    have := Finset.mem_Icc.mp (hsub hs)
    omega
  refine notallodd hk2 hS hpal ?_ heven ?_
  · intro d hd hdk
    have h1 : d ∣ Nat.gcd (S.gcd id) k := Nat.dvd_gcd (Finset.dvd_gcd fun y hy => hd y hy) hdk
    rw [hprim] at h1
    exact Nat.dvd_one.mp h1
  · by_contra h
    push_neg at h
    apply hfull
    ext y
    constructor
    · exact fun hy => hsub hy
    · intro hy
      have := Finset.mem_Icc.mp hy
      exact h y (by omega) (by omega)

end NotAllOdd
end Bump
end Trop
end PeriodicDifference
