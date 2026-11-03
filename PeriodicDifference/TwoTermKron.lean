/-
# `PeriodicDifference/TwoTermKron.lean` — the Kronecker step of `thm:twoterm`

With `ζ² − εζ + 1 = 0`, the number field `ℚ(ζ, η₁, …, η_K) ⊂ ℂ` has every conjugate of
`ε` in `[−2, 2]` (`embed_bound`), so `ζ` is a root of unity (`Kron.isRootOfUnity_of_conj_mem_Icc`).
-/
import PeriodicDifference.TwoTermGalois

namespace PeriodicDifference
namespace TwoTerm

open Polynomial Finset

lemma isIntegral_root_quad {ε ζ : ℂ} (hε : IsIntegral ℤ ε) (hζ : ζ ^ 2 - ε * ζ + 1 = 0) :
    IsIntegral ℤ ζ := by
  have hsub : IsIntegral (Algebra.adjoin ℤ ({ε} : Set ℂ)) ζ := by
    refine ⟨Polynomial.X ^ 2 -
      Polynomial.C ⟨ε, Algebra.self_mem_adjoin_singleton ℤ ε⟩ * Polynomial.X + 1, ?_, ?_⟩
    · monicity!
    · simp [Polynomial.eval₂_add, Polynomial.eval₂_sub]
      linear_combination hζ
  haveI : Algebra.IsIntegral ℤ (Algebra.adjoin ℤ ({ε} : Set ℂ)) :=
    Algebra.IsIntegral.adjoin (fun x hx => by rcases hx with rfl; exact hε)
  exact isIntegral_trans ζ hsub

/-- **The Kronecker step.** -/
theorem stage1 {K j p : ℕ} {η : Fin K → ℂ} {ε : ℂ} (hp : 0 < p)
    (hprod : ∏ i, (X - C (η i)) = chiP ℂ K j ε) (hηp : ∀ i, η i ^ p = 1)
    (hj0 : 0 < j) (hjK : 2 * j < K) (hcop : Nat.Coprime j K) (h3 : K ≠ 3 * j)
    {ζ : ℂ} (hζ : ζ ^ 2 - ε * ζ + 1 = 0) : ∃ n, 0 < n ∧ ζ ^ n = 1 := by
  have hεint := isIntegral_eps hp hprod hηp hj0 hjK
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  have hζint := isIntegral_root_quad hεint hζ
  set S : Set ℂ := insert ζ (Set.range η) with hS
  haveI : Finite S := ((Set.finite_range η).insert ζ).to_subtype
  haveI hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    rcases hx with rfl | ⟨i, rfl⟩
    · exact hζint.tower_top
    · exact (isIntegral_of_pow hp (hηp i)).tower_top
  set L := IntermediateField.adjoin ℚ S with hL
  haveI : NumberField L := ⟨⟩
  let ζ1 : L := ⟨ζ, IntermediateField.subset_adjoin ℚ S (Set.mem_insert ζ _)⟩
  let η1 : Fin K → L := fun i =>
    ⟨η i, IntermediateField.subset_adjoin ℚ S (Set.mem_insert_of_mem ζ ⟨i, rfl⟩)⟩
  let e1 : L := ζ1 + ζ1⁻¹
  have he1 : (e1 : ℂ) = ε := by
    show ζ + ζ⁻¹ = ε
    field_simp
    linear_combination hζ
  have hprod1 := prod_sub L hprod η1 (fun i => rfl) e1 he1
  have hint1 : IsIntegral ℤ e1 := by
    rw [← isIntegral_algebraMap_iff (A := L) (B := ℂ) (algebraMap L ℂ).injective]
    have : algebraMap L ℂ e1 = ε := he1
    rw [this]; exact hεint
  have hq1 : ζ1 ^ 2 - e1 * ζ1 + 1 = 0 := by
    apply (algebraMap L ℂ).injective
    have : algebraMap L ℂ e1 = ε := he1
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, this]
    exact hζ
  have hη1 : ∀ i, η1 i ^ p = 1 := by
    intro i
    apply (algebraMap L ℂ).injective
    simp only [map_pow, map_one]
    exact hηp i
  obtain ⟨n, hn, hpow⟩ := Kron.isRootOfUnity_of_conj_mem_Icc hint1 hq1 fun φ => by
    obtain ⟨r, hr, hr2, -⟩ := embed_bound hprod1 hp hη1 hj0 hjK hcop h3 φ
    exact ⟨r, hr, hr2⟩
  refine ⟨n, hn, ?_⟩
  have := congrArg (algebraMap L ℂ) hpow
  simpa using this

end TwoTerm
end PeriodicDifference
