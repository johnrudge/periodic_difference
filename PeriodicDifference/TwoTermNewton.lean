/-
# `PeriodicDifference/TwoTermNewton.lean` — power sums of the roots of `X^K + 1 − t (X^j + X^{K−j})`

Newton's identities (Mathlib's `MvPolynomial.psum_eq_mul_esymm_sub_sum`) for the sparse
polynomial `χ_t`: if `∏ᵢ (X − ηᵢ) = χ_t` then the power sums `p_r = Σ ηᵢ^r` obey
`p_k = t·p_{k−j} + t·p_{k−(K−j)} + j t [k = j] + (K−j) t [k = K−j] − K [k = K]`
(terms with negative index absent), for `1 ≤ k ≤ K` (`ps_rec`).
-/
import Mathlib

namespace PeriodicDifference
namespace TwoTerm

open Polynomial Finset

variable {F : Type*} [Field F]

/-- The power sums `p_r = Σᵢ ηᵢ^r`. -/
def ps {K : ℕ} (η : Fin K → F) (r : ℕ) : F := ∑ i, η i ^ r

/-- `χ_t = X^K + 1 − t (X^j + X^{K−j})` as a polynomial. -/
noncomputable def chiP (F : Type*) [Field F] (K j : ℕ) (t : F) : F[X] :=
  X ^ K + 1 - C t * (X ^ j + X ^ (K - j))

lemma coeff_chiP (K j : ℕ) (t : F) (d : ℕ) :
    (chiP F K j t).coeff d = (if d = K then 1 else 0) + (if d = 0 then 1 else 0) -
      t * ((if d = j then 1 else 0) + (if d = K - j then 1 else 0)) := by
  simp only [chiP, coeff_add, coeff_sub, coeff_X_pow, coeff_one, coeff_C_mul]

section

variable {K j : ℕ} {η : Fin K → F} {t : F}

lemma esymm_eq (hprod : ∏ i, (X - C (η i)) = chiP F K j t) {m : ℕ} (hm : m ≤ K) :
    (univ.val.map η).esymm m = (-1) ^ m * (chiP F K j t).coeff (K - m) := by
  have hcard : Multiset.card (univ.val.map η) = K := by simp
  have h := Multiset.prod_X_sub_C_coeff (univ.val.map η) (k := K - m) (by rw [hcard]; omega)
  rw [hcard, show K - (K - m) = m by omega, Multiset.map_map] at h
  have hp : ((univ.val.map ((fun a => X - C a) ∘ η))).prod = ∏ i, (X - C (η i)) := rfl
  rw [hp, hprod] at h
  rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- Newton's identity, evaluated at `η`. -/
lemma ps_newton {k : ℕ} (hk : 0 < k) :
    ps η k = (-1) ^ (k + 1) * k * (univ.val.map η).esymm k -
      ∑ a ∈ antidiagonal k with a.1 ∈ Set.Ioo 0 k,
        (-1) ^ a.1 * (univ.val.map η).esymm a.1 * ps η a.2 := by
  have h := congrArg (MvPolynomial.aeval η) (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin K) F k hk)
  simp only [map_sub, map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm] at h
  simpa [MvPolynomial.psum, ps] using h

/-- **The sparse Newton recursion.** -/
lemma ps_rec (hprod : ∏ i, (X - C (η i)) = chiP F K j t) (hj0 : 0 < j) (hjK : 2 * j < K)
    {k : ℕ} (hk : 0 < k) (hkK : k ≤ K) :
    ps η k = -(k : F) * (chiP F K j t).coeff (K - k) +
      t * ((if j < k then ps η (k - j) else 0) + (if K - j < k then ps η (k - (K - j)) else 0)) := by
  rw [ps_newton hk, esymm_eq hprod hkK]
  have hsum : ∑ a ∈ antidiagonal k with a.1 ∈ Set.Ioo 0 k,
      (-1) ^ a.1 * (univ.val.map η).esymm a.1 * ps η a.2
      = ∑ a ∈ Finset.Ioo 0 k, (chiP F K j t).coeff (K - a) * ps η (k - a) := by
    refine Finset.sum_nbij' Prod.fst (fun a => (a, k - a)) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp_all [Finset.mem_filter, Finset.mem_antidiagonal]
    · intro a ha
      simp_all [Finset.mem_filter, Finset.mem_antidiagonal]
      omega
    · intro a ha
      simp_all [Finset.mem_filter, Finset.mem_antidiagonal]
      ext <;> simp; omega
    · intro a _; rfl
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo] at ha
      rw [esymm_eq hprod (by omega), ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp only [neg_one_sq, one_pow, one_mul]
      congr 2; omega
  rw [hsum]
  have hterm : ∀ a ∈ Finset.Ioo 0 k, (chiP F K j t).coeff (K - a) * ps η (k - a)
      = -t * ((if a = j then ps η (k - j) else 0) + (if a = K - j then ps η (k - (K - j)) else 0)) := by
    intro a ha
    rw [Finset.mem_Ioo] at ha
    rw [coeff_chiP, if_neg (by omega), if_neg (by omega)]
    by_cases h1 : a = j
    · subst h1; rw [if_neg (by omega), if_pos (by omega), if_pos rfl, if_neg (by omega)]; ring
    · by_cases h2 : a = K - j
      · subst h2; rw [if_pos (by omega), if_neg (by omega), if_neg h1, if_pos rfl]; ring
      · rw [if_neg (by omega), if_neg (by omega), if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_Ioo]
  have hsg : ((-1 : F) ^ (k + 1)) * (-1) ^ k = -1 := by
    rw [← pow_add, show k + 1 + k = 2 * k + 1 by ring, pow_succ, pow_mul]; simp
  have e1 : (0 < j ∧ j < k) ↔ j < k := by omega
  have e2 : (0 < K - j ∧ K - j < k) ↔ K - j < k := by omega
  simp only [e1, e2]
  linear_combination ((k : F) * (chiP F K j t).coeff (K - k)) * hsg

/-- Below `K − j` only multiples of `j` survive: `p_{mj} = j t^m`. -/
lemma ps_low (hprod : ∏ i, (X - C (η i)) = chiP F K j t) (hj0 : 0 < j) (hjK : 2 * j < K) :
    ∀ r, 0 < r → r < K - j → ps η r = if j ∣ r then (j : F) * t ^ (r / j) else 0 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr hrK
    rw [ps_rec hprod hj0 hjK hr (by omega), coeff_chiP, if_neg (by omega), if_neg (by omega),
      if_neg (show ¬ K - j < r by omega)]
    by_cases hrj : r = j
    · subst hrj
      have e1 : K - r ≠ r := by omega
      simp only [e1, if_true, if_false, lt_irrefl, dvd_rfl, Nat.div_self hr, pow_one]
      ring
    · rw [if_neg (by omega), if_neg (by omega)]
      by_cases hlt : j < r
      · rw [if_pos hlt, ih (r - j) (by omega) (by omega) (by omega)]
        by_cases hd : j ∣ r
        · have hd' : j ∣ r - j := Nat.dvd_sub hd dvd_rfl
          rw [if_pos hd', if_pos hd]
          have : r / j = (r - j) / j + 1 := by
            rw [← Nat.add_div_right _ hj0]; congr 1; omega
          rw [this, pow_succ]; ring
        · have hd' : ¬ j ∣ r - j := fun h => hd (by
            have := Nat.dvd_add h (dvd_refl j); rwa [Nat.sub_add_cancel hlt.le] at this)
          rw [if_neg hd', if_neg hd]; ring
      · rw [if_neg hlt, if_neg (Nat.not_dvd_of_pos_of_lt hr (by omega))]; ring

lemma ps_j (hprod : ∏ i, (X - C (η i)) = chiP F K j t) (hj0 : 0 < j) (hjK : 2 * j < K) :
    ps η j = j * t := by
  rw [ps_low hprod hj0 hjK j hj0 (by omega), if_pos dvd_rfl, Nat.div_self hj0, pow_one]

lemma ps_Kj (hprod : ∏ i, (X - C (η i)) = chiP F K j t) (hj0 : 0 < j) (hjK : 2 * j < K) :
    ps η (K - j) = (K - j : ℕ) * t + t * ps η (K - 2 * j) := by
  rw [ps_rec hprod hj0 hjK (by omega) (by omega), coeff_chiP,
    show K - (K - j) = j by omega, if_neg (by omega), if_neg (by omega), if_pos rfl,
    if_neg (by omega), if_pos (by omega), if_neg (lt_irrefl _), show K - j - j = K - 2 * j by omega]
  ring

lemma ps_K (hprod : ∏ i, (X - C (η i)) = chiP F K j t) (hj0 : 0 < j) (hjK : 2 * j < K) :
    ps η K = -(K : F) + t * (ps η (K - j) + ps η j) := by
  rw [ps_rec hprod hj0 hjK (by omega) le_rfl, coeff_chiP, Nat.sub_self, if_neg (by omega),
    if_pos rfl, if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos (by omega),
    show K - (K - j) = j by omega]
  ring

/-- `j ≥ 2`, `gcd(j, K) = 1`: `p_K = K (t² − 1)`. -/
lemma ps_K_coprime (hprod : ∏ i, (X - C (η i)) = chiP F K j t) (hj2 : 2 ≤ j) (hjK : 2 * j < K)
    (hcop : Nat.Coprime j K) : ps η K = K * (t ^ 2 - 1) := by
  have hj0 : 0 < j := by omega
  have hnd : ¬ j ∣ K - 2 * j := by
    intro h
    have h2 : j ∣ K := by
      have := Nat.dvd_add h (Dvd.intro 2 rfl : j ∣ j * 2)
      rwa [show K - 2 * j + j * 2 = K by omega] at this
    have := Nat.Coprime.eq_one_of_dvd hcop h2
    omega
  rw [ps_K hprod hj0 hjK, ps_Kj hprod hj0 hjK, ps_j hprod hj0 hjK,
    ps_low hprod hj0 hjK (K - 2 * j) (by omega) (by omega), if_neg hnd]
  push_cast [show j ≤ K by omega]
  ring

/-- `j = 1`: `p_{K−2} = t^{K−2}` and `p_{K−1} = (K−1) t + t^{K−1}`. -/
lemma ps_one (hprod : ∏ i, (X - C (η i)) = chiP F K 1 t) (hK : 3 < K) :
    ps η (K - 2) = t ^ (K - 2) ∧ ps η (K - 1) = (K - 1 : ℕ) * t + t ^ (K - 1) := by
  have h2 := ps_low hprod one_pos (by omega) (K - 2) (by omega) (by omega)
  simp only [one_dvd, if_true, Nat.cast_one, one_mul, Nat.div_one] at h2
  refine ⟨h2, ?_⟩
  rw [ps_Kj hprod one_pos (by omega), show K - 2 * 1 = K - 2 by omega, h2,
    show K - 1 = (K - 2) + 1 by omega, pow_succ]
  ring

end

end TwoTerm
end PeriodicDifference
