/-
# `PeriodicDifference/APLemmaTailBand.lean` — `thm:lemmaA` for large `k`: Prop 4 (the band case)

Prop 4 of `tools/e3/lattice/proof.md` in rational arithmetic.  In the coordinates of `chordF`
(unit torus scaled by 4) the triangle `T₁` (the paper's `Δ₁`) is `{X < 2, Y < X, X + Y > 2}`;
we use the disc of radius `ρ = 207/500` about `C = (2 − γ, 1)` (the paper's incentre `O`),
`γ = 259/625` (inside `T₁`: `ρ < γ`, `2ρ² < (1 − γ)²`), and the band of lines at normal
distance `< b₄ = 51/250` from `C`.

* `jacOK_of_dvd` — `JacOK` passes to divisors;
* `exists_nn` — the complementary modulus `n_g` of (3.3) with `JacOK n_g J` from `JacOK (2k) J`;
* `band_chord` — among `J_g` consecutive lines meeting the band there is a good one, and its chord
  in the disc is a `ChordOK` witness longer than `J` lattice steps;
* `cert_band` — `Cert k g p q` from `JacOK g J_g`, `JacOK (2k) J` and the two inequalities
  `J_g² · 10⁶ < 10404 g²|u|²` (band, (4.2)) and `J² g²|u|² · 10⁶ < 129780 k²` (chord, (4.3)).
-/
import PeriodicDifference.APLemmaCert

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

theorem jacOK_of_dvd {n m J : ℕ} (h : JacOK n J) (hmn : m ∣ n) : JacOK m J := by
  intro X
  obtain ⟨i, hi, hc⟩ := h X
  refine ⟨i, hi, ?_⟩
  exact hc.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hmn)

/-- The modulus `n_g`: product of the primes of `2k` not dividing `g`. -/
theorem exists_nn {k J : ℕ} (hk : 0 < k) (hJ : JacOK (2*k) J) (g : ℤ) :
    ∃ nn : ℕ, JacOK nn J ∧ (nn:ℤ) ∣ 2*k ∧ IsCoprime (nn:ℤ) g ∧
      (∀ ℓ : ℕ, ℓ.Prime → (ℓ:ℤ) ∣ 2*k → (ℓ:ℤ) ∣ nn ∨ (ℓ:ℤ) ∣ g) := by
  classical
  set S : Finset ℕ := (Nat.primeFactors (2*k)).filter (fun ℓ : ℕ => ¬ (ℓ:ℤ) ∣ g)
  refine ⟨∏ ℓ ∈ S, ℓ, ?_, ?_, ?_, ?_⟩
  · refine jacOK_of_dvd hJ ?_
    exact (Finset.prod_dvd_prod_of_subset _ _ (fun ℓ : ℕ => ℓ) (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd _)
  · have : ∏ ℓ ∈ S, ℓ ∣ 2*k := (Finset.prod_dvd_prod_of_subset _ _ (fun ℓ : ℕ => ℓ)
      (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd _)
    exact_mod_cast this
  · push_cast
    refine IsCoprime.prod_left fun ℓ hℓ => ?_
    simp only [S, Finset.mem_filter, Nat.mem_primeFactors] at hℓ
    obtain ⟨⟨hp, -, -⟩, hng⟩ := hℓ
    exact (Int.isCoprime_iff_gcd_eq_one.2 (by
      have := Int.gcd_dvd_left (ℓ:ℤ) g
      rw [Int.natCast_dvd_natCast] at this
      rcases (Nat.dvd_prime hp).1 this with h | h
      · exact h
      · exfalso; apply hng; have := Int.gcd_dvd_right (ℓ:ℤ) g; rwa [h] at this))
  · intro ℓ hℓ hdvd
    by_cases hg : (ℓ:ℤ) ∣ g
    · exact Or.inr hg
    · left
      have hmem : ℓ ∈ S := by
        simp only [S, Finset.mem_filter, Nat.mem_primeFactors]
        exact ⟨⟨hℓ, by exact_mod_cast hdvd, by omega⟩, hg⟩
      have := Finset.dvd_prod_of_mem (fun ℓ : ℕ => ℓ) hmem
      exact_mod_cast this

/-- The disc of radius `207/500` about `(2 − 259/625, 1)` lies in the open triangle `T₁`. -/
theorem tri0_pos {X Y : ℚ} (h : (X - (2 - 259/625))^2 + (Y - 1)^2 < (207/500)^2) :
    0 < 2 - X ∧ 0 < X - Y ∧ 0 < X + Y - 2 := by
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [sq_nonneg (Y - 1), sq_nonneg (X - (2 - 259/625) - 207/500)]
  · nlinarith [sq_nonneg (X - (2 - 259/625) + (Y - 1)),
      sq_nonneg ((X - (2 - 259/625)) - (Y - 1) + 1 - 259/625)]
  · nlinarith [sq_nonneg (X - (2 - 259/625) - (Y - 1)),
      sq_nonneg ((X - (2 - 259/625)) + (Y - 1) + 1 - 259/625)]

/-- The distance identity along a geodesic: `|P(s) − C|² = 16 (s − s_F)² U + E²/U`. -/
theorem geo_dist (g p q j : ℤ) (s : ℚ) (hg : (g:ℚ) ≠ 0) (hU : (p:ℚ)^2 + q^2 ≠ 0) :
    (4*(-q*j/(g*(p^2+q^2)) + s*p) - 4*0 - (2 - 259/625))^2 +
      (4*(p*j/(g*(p^2+q^2)) + s*q) - 4*0 - 1)^2 =
    16*(s - (p*(2 - 259/625) + q*1)/(4*(p^2+q^2)))^2*(p^2+q^2) +
      (4*j/g + q*(2 - 259/625) - p*1)^2/(p^2+q^2) := by
  field_simp
  ring

set_option maxHeartbeats 2000000 in
/-- Prop 4: a good line of the band and its chord in the disc. -/
theorem band_chord {k : ℕ} {g p q : ℤ} {ng Jg J : ℕ} (hg : 0 < g) (hngg : (ng:ℤ) = g)
    (hJg : JacOK ng Jg) (hU : 0 < p^2+q^2)
    (hband : (Jg:ℤ)^2 * 10^6 < 10404 * (g^2*(p^2+q^2)))
    (hchord : (J:ℤ)^2 * (g^2*(p^2+q^2)) * 10^6 < 129780 * (k:ℤ)^2) :
    ∃ (j : ℤ) (s₀ s₁ : ℚ), IsCoprime j g ∧ ChordOK g p q j 0 0 0 s₀ s₁ ∧
      (J:ℚ) * g < 2*k*(s₁ - s₀) := by
  set U : ℚ := (p:ℚ)^2 + q^2 with hUdef
  have hUq : 0 < U := by have : (0:ℚ) < ((p^2+q^2 : ℤ) : ℚ) := by exact_mod_cast hU
                         push_cast at this; exact this
  have hgq : (0:ℚ) < g := by exact_mod_cast hg
  have hkpos : (0:ℚ) < k := by
    have : (0:ℤ) < (k:ℤ)^2 := by nlinarith [sq_nonneg ((J:ℤ)), sq_nonneg (g^2*(p^2+q^2))]
    have : (0:ℤ) < k := by
      rcases (show (k:ℤ) = 0 ∨ 0 < (k:ℤ) by omega) with h | h
      · rw [h] at this; norm_num at this
      · exact h
    exact_mod_cast this
  set τ : ℚ := g*(p*1 - q*(2 - 259/625))/4 with hτ
  set X0 : ℤ := ⌊τ - (Jg:ℚ)/2⌋ + 1 with hX0
  obtain ⟨i, hi, hcop⟩ := hJg X0
  set j : ℤ := X0 + i with hj
  have hjg : IsCoprime j g := by rw [← hngg]; exact hcop
  have hj1 : τ - (Jg:ℚ)/2 < j := by
    have := Int.lt_floor_add_one (τ - (Jg:ℚ)/2)
    have : (0:ℚ) ≤ i := by positivity
    push_cast [hj, hX0]; linarith
  have hj2 : (j:ℚ) ≤ τ + (Jg:ℚ)/2 := by
    have := Int.floor_le (τ - (Jg:ℚ)/2)
    have : (i:ℚ) + 1 ≤ Jg := by exact_mod_cast hi
    push_cast [hj, hX0]; linarith
  have hjt : ((j:ℚ) - τ)^2 ≤ (Jg:ℚ)^2/4 := by nlinarith
  set E : ℚ := 4*j/g + q*(2 - 259/625) - p*1 with hE
  have hE' : E = 4*((j:ℚ) - τ)/g := by rw [hE, hτ]; field_simp; ring
  have hband' : (Jg:ℚ)^2 * 10^6 < 10404 * ((g:ℚ)^2*U) := by
    have : ((Jg:ℤ)^2 * 10^6 : ℤ) < (10404 * (g^2*(p^2+q^2)) : ℤ) := hband
    rw [hUdef]; exact_mod_cast this
  have hEb : E^2/U < (204/1000)^2 := by
    rw [div_lt_iff₀ hUq, hE', div_pow]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  set Δ0 : ℚ := (J:ℚ)*g/(4*k) with hΔ0
  have hΔ0nn : 0 ≤ Δ0 := by positivity
  have hchord' : (J:ℚ)^2 * ((g:ℚ)^2*U) * 10^6 < 129780 * (k:ℚ)^2 := by
    have : ((J:ℤ)^2 * (g^2*(p^2+q^2)) * 10^6 : ℤ) < (129780 * (k:ℤ)^2 : ℤ) := hchord
    rw [hUdef]; exact_mod_cast this
  set F0 : ℚ := 16*Δ0^2*U + E^2/U - (207/500)^2 with hF0
  have h16 : 16*Δ0^2*U = (J:ℚ)^2*((g:ℚ)^2*U)/k^2 := by rw [hΔ0]; field_simp; ring
  have hF0neg : F0 < 0 := by
    have : (J:ℚ)^2*((g:ℚ)^2*U)/k^2 < 129780/10^6 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
    rw [hF0, h16]; nlinarith
  clear_value F0 Δ0 E j X0 τ U
  clear hcop hj1 hj2 hX0 hj hband hchord hband' hchord' h16
  obtain ⟨M, hM⟩ : ∃ M : ℚ, M = 16*U*(2*Δ0 + 1) := ⟨_, rfl⟩
  have hMpos : 0 < M := by rw [hM]; positivity
  have hden : 0 < 2*(M - F0) := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℚ, t = -F0/(2*(M - F0)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; exact div_pos (by linarith) hden
  have ht1 : t ≤ 1 := by rw [ht, div_le_iff₀ hden]; linarith
  have htM : t*M < -F0/2 := by
    have : t*(2*(M - F0)) = -F0 := by rw [ht, div_mul_cancel₀ _ hden.ne']
    have := mul_pos ht0 (neg_pos.mpr hF0neg)
    linarith
  set Δ : ℚ := Δ0 + t with hΔ
  have hFΔ : 16*Δ^2*U + E^2/U < (207/500)^2 := by
    have e : 16*Δ^2*U = 16*Δ0^2*U + 16*U*(2*Δ0*t + t^2) := by rw [hΔ]; ring
    have : 16*U*(2*Δ0*t + t^2) ≤ t*M := by
      have h1 : t^2 ≤ t := by nlinarith
      have h2 : 16*U*t^2 ≤ 16*U*t := by nlinarith
      rw [hM]; nlinarith
    rw [e]; linarith
  set sF : ℚ := (p*(2 - 259/625) + q*1)/(4*(p^2+q^2)) with hsF
  have hg0 : (g:ℚ) ≠ 0 := hgq.ne'
  have hU0 : (p:ℚ)^2 + q^2 ≠ 0 := by rw [← hUdef]; exact hUq.ne'
  have endpt : ∀ s : ℚ, (s - sF)^2 = Δ^2 →
      0 < (chordF g p q j 0 0 0 s).1 ∧ 0 < (chordF g p q j 0 0 0 s).2.1 ∧
      0 < (chordF g p q j 0 0 0 s).2.2 := by
    intro s hs
    have hd := geo_dist g p q j s hg0 hU0
    rw [← hsF, hs, ← hE] at hd
    have hin := tri0_pos (lt_of_eq_of_lt hd (by rw [← hUdef]; linarith))
    simp only [chordF, triF, Int.cast_zero]
    exact hin
  have e0 := endpt (sF - Δ) (by ring)
  have e1 := endpt (sF + Δ) (by ring)
  refine ⟨j, sF - Δ, sF + Δ, hjg, ⟨e0.1.le, e1.1.le, Or.inl e0.1, e0.2.1.le, e1.2.1.le,
    Or.inl e0.2.1, e0.2.2.le, e1.2.2.le, Or.inl e0.2.2⟩, ?_⟩
  have : (J:ℚ)*g = 4*k*Δ0 := by rw [hΔ0]; field_simp
  rw [this]; nlinarith

end APLemma
end Bump
end Trop
end PeriodicDifference
