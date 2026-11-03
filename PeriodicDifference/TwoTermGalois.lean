/-
# `PeriodicDifference/TwoTermGalois.lean` — conjugates of `ε` (field-theoretic part of `thm:twoterm`)

* `embed_bound`: in any field `L` where `χ_e` splits into roots of unity, every embedding
  `φ : L → ℂ` sends `e` to a real number in `[−2, 2]` that is at most `√2`;
* `exists_roots`: `χ_t` splits over `ℂ` into `K` linear factors.
-/
import PeriodicDifference.TwoTermBound
import PeriodicDifference.TwoTermSmall
import PeriodicDifference.Kronecker

namespace PeriodicDifference
namespace TwoTerm

open Polynomial Finset

lemma map_chiP {L L' : Type*} [Field L] [Field L'] (φ : L →+* L') (K j : ℕ) (t : L) :
    (chiP L K j t).map φ = chiP L' K j (φ t) := by
  simp [chiP, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

/-- **Every conjugate of `e` lies in `[−2, √2]`.** -/
theorem embed_bound {L : Type*} [Field L] {K j p : ℕ} {η : Fin K → L} {e : L}
    (hprod : ∏ i, (X - C (η i)) = chiP L K j e) (hp : 0 < p) (hη : ∀ i, η i ^ p = 1)
    (hj0 : 0 < j) (hjK : 2 * j < K) (hcop : Nat.Coprime j K) (h3 : K ≠ 3 * j)
    (φ : L →+* ℂ) : ∃ r : ℝ, φ e = r ∧ |r| ≤ 2 ∧ r ≤ Real.sqrt 2 := by
  have h := congrArg (Polynomial.map φ) hprod
  rw [Polynomial.map_prod, map_chiP] at h
  simp only [Polynomial.map_sub, map_X, map_C] at h
  refine conj_bound h (fun i => ?_) hj0 hjK hcop h3
  have : (φ (η i)) ^ p = 1 := by rw [← map_pow, hη i, map_one]
  exact Complex.norm_eq_one_of_pow_eq_one this hp.ne'

lemma natDegree_chiP {F : Type*} [Field F] {K j : ℕ} (hj0 : 0 < j) (hjK : 2 * j < K) (t : F) :
    (chiP F K j t).natDegree = K := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hN' : K < N := by exact_mod_cast hN
    rw [coeff_chiP, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  · rw [coeff_chiP, if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp

lemma monic_chiP {F : Type*} [Field F] {K j : ℕ} (hj0 : 0 < j) (hjK : 2 * j < K) (t : F) :
    (chiP F K j t).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, natDegree_chiP hj0 hjK, coeff_chiP, if_pos rfl,
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

lemma exists_fin_map {α : Type*} (s : Multiset α) :
    ∀ K, Multiset.card s = K → ∃ η : Fin K → α, univ.val.map η = s := by
  intro K hK
  subst hK
  refine ⟨fun i => s.toList.get (i.cast (by simp)), ?_⟩
  rw [Fin.univ_val_map]
  conv_rhs => rw [← Multiset.coe_toList s]
  congr 1
  apply List.ext_get (by simp)
  intro n h1 h2
  simp

lemma exists_roots {K j : ℕ} (hj0 : 0 < j) (hjK : 2 * j < K) (t : ℂ) :
    ∃ η : Fin K → ℂ, ∏ i, (X - C (η i)) = chiP ℂ K j t := by
  have hm := monic_chiP hj0 hjK t
  have hcard : Multiset.card (chiP ℂ K j t).roots = K := by
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_chiP hj0 hjK]
  obtain ⟨η, hη⟩ := exists_fin_map _ K hcard
  refine ⟨η, ?_⟩
  have := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm
    (by rw [IsAlgClosed.card_roots_eq_natDegree])
  rw [← hη, Multiset.map_map] at this
  exact this


/-! ## Subfields of `ℂ` -/

section Sub

variable {K j : ℕ} {η : Fin K → ℂ} {ε : ℂ}

/-- The factorisation descends to any subfield containing the roots and `ε`. -/
lemma prod_sub (L : IntermediateField ℚ ℂ) (hprod : ∏ i, (X - C (η i)) = chiP ℂ K j ε)
    (η' : Fin K → L) (hη' : ∀ i, (η' i : ℂ) = η i) (e : L) (he : (e : ℂ) = ε) :
    ∏ i, (X - C (η' i)) = chiP L K j e := by
  apply Polynomial.map_injective (algebraMap L ℂ) (algebraMap L ℂ).injective
  rw [Polynomial.map_prod, map_chiP]
  simp only [Polynomial.map_sub, map_X, map_C]
  have h1 : ∀ i, algebraMap L ℂ (η' i) = η i := hη'
  have h2 : algebraMap L ℂ e = ε := he
  simp only [h1, h2]
  exact hprod

lemma isIntegral_of_pow {z : ℂ} {p : ℕ} (hp : 0 < p) (hz : z ^ p = 1) : IsIntegral ℤ z :=
  IsIntegral.of_pow hp (by rw [hz]; exact isIntegral_one)

/-- `ε` is an algebraic integer: it is `±` an elementary symmetric function of the roots. -/
lemma isIntegral_eps {p : ℕ} (hp : 0 < p) (hprod : ∏ i, (X - C (η i)) = chiP ℂ K j ε)
    (hηp : ∀ i, η i ^ p = 1) (hj0 : 0 < j) (hjK : 2 * j < K) : IsIntegral ℤ ε := by
  have he := esymm_eq hprod (m := j) (by omega)
  rw [coeff_chiP, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos rfl] at he
  have hmem : (univ.val.map η).esymm j ∈ integralClosure ℤ ℂ := by
    unfold Multiset.esymm
    refine Subalgebra.multiset_sum_mem _ fun x hx => ?_
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hx
    refine Subalgebra.multiset_prod_mem _ fun y hy => ?_
    have hy' := Multiset.mem_of_le (Multiset.mem_powersetCard.mp hs).1 hy
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hy'
    exact isIntegral_of_pow hp (hηp i)
  have hε : ε = -(-1) ^ j * (univ.val.map η).esymm j := by
    rw [he, ← mul_assoc]
    have : ((-1 : ℂ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-ε) * this
  rw [hε]
  exact (IsIntegral.neg (IsIntegral.pow isIntegral_one.neg j)).mul hmem

end Sub

end TwoTerm
end PeriodicDifference
