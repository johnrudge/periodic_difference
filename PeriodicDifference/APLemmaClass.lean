/-
# `PeriodicDifference/APLemmaClass.lean` — `thm:lemmaA`, Step D: the lattice classes of a direction

If `v = g u ∈ Λ(a,e)` (with the label facts (3.1)) then a unit `ε` with `ε ≡ lab(v)/g`
modulo `n₀ = N/g` gives `ε(a,e) ≡ (p + n₀s, q + n₀t) (mod N)` for some `0 ≤ s,t < g` ((D1) of
`B1_argument.txt`).  By unit invariance `Good k a e` follows from `Good` at that class
representative.  A class may instead be excluded: its lattice contains `m u` for some
`0 < m < g` (impossible when `g u` is a shortest vector), or `gcd(A,E,N) > 1` (impossible for
an admissible pair).  `ClassOK` collects the three alternatives.
-/
import PeriodicDifference.APLemmaLattice

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

/-- Lifting a unit modulo `n ∣ M` to a unit modulo `M`. -/
theorem exists_unit_lift {n M : ℕ} (hM : 0 < M) (hn : n ∣ M) {d : ℤ} (hd : IsCoprime d n) :
    ∃ ε : ℤ, IsCoprime ε M ∧ (n:ℤ) ∣ ε - d := by
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨α, β, hαβ⟩ := hd
  have hu : IsUnit (d : ZMod n) := by
    have : ((α*d + β*n : ℤ) : ZMod n) = 1 := by rw [hαβ]; simp
    push_cast at this
    have h' : (d : ZMod n) * (α : ZMod n) = 1 := by simpa [mul_comm] using this
    exact IsUnit.of_mul_eq_one _ h'
  obtain ⟨U, hU⟩ := ZMod.unitsMap_surjective hn hu.unit
  refine ⟨((U : ZMod M).val : ℤ), ?_, ?_⟩
  · rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact ZMod.val_coe_unit_coprime U
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h1 : (ZMod.cast (U : ZMod M) : ZMod n) = d := by
      have := congrArg (fun w : (ZMod n)ˣ => (w : ZMod n)) hU
      simpa [ZMod.unitsMap_def, ZMod.castHom_apply] using this
    push_cast
    rw [ZMod.natCast_val, h1, sub_self]

/-- The three ways a class `(p + n₀s, q + n₀t)` (`n₀ = 2k/g`) can be discharged. -/
def ClassOK (k : ℕ) (g p q s t : ℤ) : Prop :=
  Good k (p + (2*k/g)*s) (q + (2*k/g)*t) ∨
  (∃ m : ℤ, 0 < m ∧ m < g ∧ Mem (2*k) (p + (2*k/g)*s) (q + (2*k/g)*t) (m*p) (m*q)) ∨
  Int.gcd (Int.gcd (p + (2*k/g)*s) (q + (2*k/g)*t)) (2*k) ≠ 1

/-- Step D: Lemma A for `Λ(a,e) ∋ g u` from its `≤ g²` classes. -/
theorem good_of_class {k : ℕ} (hk : 0 < k) {a e x y z : ℤ} (hB : x*a + y*e + z*(2*k) = 1)
    {g p q : ℤ} (hg : 0 < g) (hgN : g ∣ 2*k) (hvm : Mem (2*k) a e (g*p) (g*q))
    (hgδ : g ∣ lab x y (g*p) (g*q))
    (hδ : ∀ ℓ : ℤ, 0 < ℓ → ℓ ∣ 2*k → ℓ ∣ lab x y (g*p) (g*q) → ℓ ∣ g)
    (hmin : ∀ m : ℤ, 0 < m → m < g → ¬ Mem (2*k) a e (m*p) (m*q))
    (hcls : ∀ s t : ℤ, 0 ≤ s → s < g → 0 ≤ t → t < g → ClassOK k g p q s t) :
    Good k a e := by
  set N : ℤ := 2*k with hN
  have hNpos : 0 < N := by positivity
  obtain ⟨n₀, hn₀⟩ := hgN
  have hn₀pos : 0 < n₀ := by
    by_contra h; push_neg at h; nlinarith
  have hdiv : N / g = n₀ := by rw [hn₀]; exact Int.mul_ediv_cancel_left _ hg.ne'
  obtain ⟨δ₁, hδ₁⟩ := hgδ
  have hcop : IsCoprime δ₁ n₀ := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    set c : ℤ := (Int.gcd δ₁ n₀ : ℤ) with hc
    have c1 : c ∣ δ₁ := Int.gcd_dvd_left _ _
    have c2 : c ∣ n₀ := Int.gcd_dvd_right _ _
    have cpos : 0 < c := Int.natCast_pos.2 (Int.gcd_pos_of_ne_zero_right _ hn₀pos.ne')
    have := hδ (g*c) (by positivity) (by rw [hn₀]; exact mul_dvd_mul_left g c2)
      (by rw [hδ₁]; exact mul_dvd_mul_left g c1)
    have hle := Int.le_of_dvd hg this
    have : c ≤ 1 := by nlinarith
    have : c = 1 := by omega
    exact_mod_cast (show ((Int.gcd δ₁ n₀ : ℕ) : ℤ) = 1 from this)
  -- a unit ε ≡ δ₁ (mod n₀)
  obtain ⟨ε, hε, hεd⟩ : ∃ ε : ℤ, IsCoprime ε N ∧ n₀ ∣ ε - δ₁ := by
    have h1 : n₀.toNat ∣ 2*k := by
      have : ((n₀.toNat : ℕ) : ℤ) ∣ ((2*k : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg hn₀pos.le]; push_cast; exact ⟨g, by rw [← hN, hn₀]; ring⟩
      exact_mod_cast this
    have h2 : IsCoprime δ₁ ((n₀.toNat : ℕ) : ℤ) := by rwa [Int.toNat_of_nonneg hn₀pos.le]
    obtain ⟨ε, h3, h4⟩ := exists_unit_lift (by omega) h1 h2
    refine ⟨ε, by simpa [hN] using h3, by rwa [Int.toNat_of_nonneg hn₀pos.le] at h4⟩
  obtain ⟨r, hr⟩ := hεd
  obtain ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ := mem_lab hB hvm
  -- ε a = p + n₀ K₁, ε e = q + n₀ K₂
  set K₁ := r*a - c₁; set K₂ := r*e - c₂
  have hK₁ : ε*a = p + n₀*K₁ := by
    have : g*(p - δ₁*a) = g*(n₀*c₁) := by
      rw [hδ₁] at h₁; rw [hn₀] at h₁; linear_combination h₁
    have := mul_left_cancel₀ hg.ne' this
    simp only [K₁]; linear_combination a*hr - this
  have hK₂ : ε*e = q + n₀*K₂ := by
    have : g*(q - δ₁*e) = g*(n₀*c₂) := by
      rw [hδ₁] at h₂; rw [hn₀] at h₂; linear_combination h₂
    have := mul_left_cancel₀ hg.ne' this
    simp only [K₂]; linear_combination e*hr - this
  set s := K₁ % g; set t := K₂ % g
  have hs : s + g*(K₁/g) = K₁ := Int.emod_add_mul_ediv K₁ g
  have ht : t + g*(K₂/g) = K₂ := Int.emod_add_mul_ediv K₂ g
  have hA : ε*a = (p + n₀*s) + N*(K₁/g) := by rw [hK₁, hn₀]; linear_combination -n₀ * hs
  have hE : ε*e = (q + n₀*t) + N*(K₂/g) := by rw [hK₂, hn₀]; linear_combination -n₀ * ht
  have hcl := hcls s t (Int.emod_nonneg _ hg.ne') (Int.emod_lt_of_pos _ hg)
    (Int.emod_nonneg _ hg.ne') (Int.emod_lt_of_pos _ hg)
  unfold ClassOK at hcl
  rw [← hN, hdiv] at hcl
  rcases hcl with h | ⟨m, hm0, hmg, hmem⟩ | h
  · refine good_of_unit_mul (ε := ε) ?_ ?_
    · rw [← Int.isCoprime_iff_gcd_eq_one]; exact hε
    · refine good_of_modEq ?_ ?_ h
      · rw [hA]; exact (Int.modEq_iff_dvd.2 ⟨-(K₁/g), by ring⟩)
      · rw [hE]; exact (Int.modEq_iff_dvd.2 ⟨-(K₂/g), by ring⟩)
  · exfalso; apply hmin m hm0 hmg
    obtain ⟨c, hc⟩ := hmem
    have : N ∣ ε*(m*p*e - m*q*a) :=
      ⟨c + m*p*(K₂/g) - m*q*(K₁/g), by linear_combination m*p*hE - m*q*hA + hc⟩
    exact hε.symm.dvd_of_dvd_mul_left this
  · exfalso; apply h
    set c : ℤ := (Int.gcd (Int.gcd (p + n₀*s) (q + n₀*t)) N : ℤ)
    have cA : c ∣ p + n₀*s := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
    have cE : c ∣ q + n₀*t := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
    have cN : c ∣ N := Int.gcd_dvd_right _ _
    have ca : c ∣ ε*a := by rw [hA]; exact dvd_add cA (dvd_mul_of_dvd_left cN _)
    have ce : c ∣ ε*e := by rw [hE]; exact dvd_add cE (dvd_mul_of_dvd_left cN _)
    have cε : c ∣ ε := by
      have : ε = x*(ε*a) + y*(ε*e) + z*ε*N := by linear_combination -ε * hB
      rw [this]
      exact dvd_add (dvd_add (dvd_mul_of_dvd_right ca _) (dvd_mul_of_dvd_right ce _))
        (dvd_mul_of_dvd_right cN _)
    have hu := IsCoprime.isUnit_of_dvd' hε cε cN
    rw [Int.isUnit_iff] at hu
    have : (0:ℤ) ≤ c := by positivity
    have : c = 1 := by omega
    exact_mod_cast (show ((Int.gcd (Int.gcd (p + n₀*s) (q + n₀*t)) N : ℕ) : ℤ) = 1 from this)

end APLemma
end Bump
end Trop
end PeriodicDifference
