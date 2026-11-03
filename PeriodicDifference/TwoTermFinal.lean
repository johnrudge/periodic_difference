/-
# `PeriodicDifference/TwoTermFinal.lean` — `thm:twoterm` in full (`TwoTerm.twoTerm`)

`twoTerm` follows from the linearisation (`TwoTermLinear.linear_periodic`, `root_pow_eq_one`)
and the spectral half `spectral`: for `0 < j`, `2j < K`, `gcd(j, K) = 1`, `K ≠ 3j` and
`ε ∈ (0, 1/2]`, the polynomial `χ_ε(z) = z^K + 1 − ε (z^j + z^{K−j})` has a root that is
not a `p`-th root of unity.

`stage2`: the cyclotomic conjugate.  With `ζ` of order `n₀` (`ζ² − εζ + 1 = 0`), the field
`ℚ(ω)`, `ω = e^{2πi/Q}`, `Q = p n₀`, contains `ζ` and every root of `χ_ε`; the embedding
`ω ↦ ω^a`, `a ≡ b (mod n₀)` with `ζ^b = e^{2πi/n₀}`, sends `ε = ζ + ζ⁻¹` to `2cos(2π/n₀)`,
which `embed_bound` caps at `√2`, so `n₀ ≤ 8`; and `small_order_absurd` rules out `n₀ ≤ 8`.
-/
import PeriodicDifference.TwoTermKron
import PeriodicDifference.TwoTermLinear

namespace PeriodicDifference
namespace TwoTerm

open Polynomial Finset Complex

/-- **The cyclotomic conjugate.** -/
theorem stage2 {K j p : ℕ} {η : Fin K → ℂ} {ε : ℝ} (hp : 0 < p)
    (hprod : ∏ i, (X - C (η i)) = chiP ℂ K j (ε : ℂ)) (hηp : ∀ i, η i ^ p = 1)
    (hj0 : 0 < j) (hjK : 2 * j < K) (hcop : Nat.Coprime j K) (h3 : K ≠ 3 * j)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    {ζ : ℂ} (hζ : ζ ^ 2 - ε * ζ + 1 = 0) {n : ℕ} (hn : 0 < n) (hζn : ζ ^ n = 1) : False := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hζn⟩
  set n0 := orderOf ζ with hn0def
  have hn0 : 0 < n0 := hfin.orderOf_pos
  have hprim : IsPrimitiveRoot ζ n0 := IsPrimitiveRoot.orderOf ζ
  rcases Nat.lt_or_ge n0 9 with h8 | h9
  · exact small_order_absurd hε0 hε1 hζ hn0 (by omega) (pow_orderOf_eq_one ζ)
  set ξ : ℂ := exp (2 * Real.pi * I / n0) with hξdef
  have hξ : IsPrimitiveRoot ξ n0 := Complex.isPrimitiveRoot_exp n0 hn0.ne'
  haveI : NeZero n0 := ⟨hn0.ne'⟩
  obtain ⟨b, -, hζb⟩ := hprim.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hbcop : b.Coprime n0 := (hprim.pow_iff_coprime hn0 b).mp (hζb ▸ hξ)
  set Q := p * n0 with hQdef
  have hQ : 0 < Q := Nat.mul_pos hp hn0
  haveI : NeZero Q := ⟨hQ.ne'⟩
  have hdvd : n0 ∣ Q := Dvd.intro_left p rfl
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hdvd (ZMod.unitOfCoprime b hbcop)
  set a := (u : ZMod Q).val with hadef
  have hacop : a.Coprime Q := ZMod.val_coe_unit_coprime u
  have hab : ζ ^ a = ξ := by
    rw [← hζb, ← pow_mod_orderOf, ← pow_mod_orderOf ζ b]
    congr 1
    have h1 := congrArg (fun v : (ZMod n0)ˣ => (v : ZMod n0)) hu
    simp only [ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply,
      ZMod.coe_unitOfCoprime] at h1
    rw [ZMod.cast_eq_val] at h1
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
  -- the cyclotomic field
  set ω : ℂ := exp (2 * Real.pi * I / Q) with hωdef
  have hω : IsPrimitiveRoot ω Q := Complex.isPrimitiveRoot_exp Q hQ.ne'
  have hωint : IsIntegral ℚ ω := (isIntegral_of_pow hQ hω.pow_eq_one).tower_top
  set L := IntermediateField.adjoin ℚ ({ω} : Set ℂ) with hL
  set pb := IntermediateField.adjoin.powerBasis hωint with hpb
  have hroot : aeval (ω ^ a) (minpoly ℚ pb.gen) = 0 := by
    have hg : pb.gen = IntermediateField.AdjoinSimple.gen ℚ ω := rfl
    rw [hg, IntermediateField.minpoly_gen, ← cyclotomic_eq_minpoly_rat hω hQ, aeval_def,
      eval₂_eq_eval_map, map_cyclotomic]
    exact (hω.pow_of_coprime a hacop).isRoot_cyclotomic hQ
  set σ := pb.lift (ω ^ a) hroot with hσdef
  have hσgen : σ pb.gen = ω ^ a := PowerBasis.lift_gen _ _ _
  have hmem : ∀ z : ℂ, z ^ Q = 1 → z ∈ L := by
    intro z hz
    obtain ⟨k, -, rfl⟩ := hω.eq_pow_of_pow_eq_one hz
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ω) k
  have hσ : ∀ (z : ℂ) (hz : z ^ Q = 1), σ ⟨z, hmem z hz⟩ = z ^ a := by
    intro z hz
    obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one hz
    have he : (⟨z, hmem z hz⟩ : L) = pb.gen ^ k := by
      apply Subtype.ext
      simp only [IntermediateField.coe_pow]
      rw [← hk]; rfl
    rw [he, map_pow, hσgen, ← hk, ← pow_mul, ← pow_mul, mul_comm]
  have hζQ : ζ ^ Q = 1 := by
    rw [hQdef, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hηQ : ∀ i, η i ^ Q = 1 := fun i => by rw [hQdef, pow_mul, hηp i, one_pow]
  let ζ2 : L := ⟨ζ, hmem ζ hζQ⟩
  let η2 : Fin K → L := fun i => ⟨η i, hmem (η i) (hηQ i)⟩
  let e2 : L := ζ2 + ζ2⁻¹
  have he2 : (e2 : ℂ) = ε := by
    show ζ + ζ⁻¹ = ε
    field_simp
    linear_combination hζ
  have hprod2 := prod_sub L hprod η2 (fun i => rfl) e2 he2
  have hη2 : ∀ i, η2 i ^ p = 1 := by
    intro i
    apply (algebraMap L ℂ).injective
    simp only [map_pow, map_one]
    exact hηp i
  obtain ⟨r, hr, -, hr2⟩ := embed_bound hprod2 hp hη2 hj0 hjK hcop h3 σ.toRingHom
  have hσe : σ e2 = ξ + ξ⁻¹ := by
    show σ (ζ2 + ζ2⁻¹) = _
    rw [map_add, map_inv₀, hσ ζ hζQ, hab]
  have hcos : ξ + ξ⁻¹ = ((2 * Real.cos (2 * Real.pi / n0) : ℝ) : ℂ) := by
    have harg : 2 * (Real.pi : ℂ) * I / n0 = ((2 * Real.pi / n0 : ℝ) : ℂ) * I := by push_cast; ring
    rw [hξdef, harg, ← Complex.exp_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_cos, Complex.two_cos, neg_mul]
  have : r = 2 * Real.cos (2 * Real.pi / n0) := by
    have h := hr
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
    rw [hσe, hcos] at h
    exact_mod_cast h.symm
  have := sqrt_two_lt_two_cos h9
  linarith

/-- **`thm:twoterm`, spectral half.** -/
theorem spectral {K j p : ℕ} {ε : ℝ} (hj0 : 0 < j) (hjK : 2 * j < K) (hcop : Nat.Coprime j K)
    (h3 : K ≠ 3 * j) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hp : 0 < p)
    (hroots : ∀ z : ℂ, chi K j ε z = 0 → z ^ p = 1) : False := by
  obtain ⟨η, hprod⟩ := exists_roots hj0 hjK (ε : ℂ)
  have hηp : ∀ i, η i ^ p = 1 := by
    intro i
    apply hroots
    have h : (chiP ℂ K j (ε : ℂ)).eval (η i) = 0 := by
      rw [← hprod, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    rw [eval_chiP] at h
    exact h
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, ζ ^ 2 - ε * ζ + 1 = 0 := by
    obtain ⟨z, hz⟩ := Complex.exists_root (f := C 1 * X ^ 2 + C (-(ε : ℂ)) * X + C 1)
      (by rw [degree_quadratic one_ne_zero]; norm_num)
    refine ⟨z, ?_⟩
    have := hz.eq_zero
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at this
    linear_combination this
  obtain ⟨n, hn, hζn⟩ := stage1 hp hprod hηp hj0 hjK hcop h3 hζ
  exact stage2 hp hprod hηp hj0 hjK hcop h3 hε0 hε1 hζ hn hζn

/-- **`thm:twoterm`**: no primitive two-term support other than `{K/3, 2K/3}` is globally
periodic. -/
theorem twoTerm {K : ℕ} {J : List ℕ} {co : ℕ → ℝ} {p j : ℕ} (h : Problem11.Admissible K J co)
    (hprim : Trop.Bump.PerSupport.Prim K (Problem11.supp J)) (hj0 : 0 < j) (hjK : 2 * j < K)
    (h3 : K ≠ 3 * j) (hs : Problem11.supp J = {j, K - j}) (hp : 0 < p) :
    ¬ Trop.GloballyPeriodic K J co p := by
  intro hg
  obtain ⟨ε, -, hε0, hε1, hlin⟩ := linear_periodic h hs hj0 hjK hg
  have hcop : Nat.Coprime j K := by
    show Nat.gcd j K = 1
    refine Problem11.eq_one_of_prim hprim (fun x hx => ?_) (Nat.gcd_dvd_right _ _)
    rw [hs] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Nat.gcd_dvd_left _ _
    · rw [Finset.mem_singleton.mp hx]
      exact Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  exact spectral hj0 hjK hcop h3 hε0 hε1 hp fun z hz => root_pow_eq_one hlin hz

end TwoTerm
end PeriodicDifference
