/-
# `PeriodicDifference/APLemmaCert.lean` — `thm:lemmaA`, Step E: from a per-direction certificate to `Good`

`Cert k g p q` is what the finite data must supply for a direction `(g, u = (p,q))` at order
`k`: a Prop-5 chord (`good_of_chord`) or all lattice classes (`good_of_class`).
`good_of_cert`: for an admissible pair, the shortest vector `g u` of `Λ(a,e)` is normalised
(`p > 0` or `p = 0 < q`), primitive, `2 ∣ gq`, `g ∣ 2k`, satisfies Hermite's bound
`3 (g²|u|²)² ≤ 16k²`, and is not one of the eight zero directions (`zero_excluded`, §5 of
proof.md); so `Good k a e` follows from `Cert` at all such directions.
-/
import PeriodicDifference.APLemmaChord
import PeriodicDifference.APLemmaClass

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

/-- The eight directions with no admissible chord (§5 of proof.md). -/
def ZeroEntry (g p q : ℤ) : Prop :=
  (g = 1 ∧ p = 1 ∧ q = 0) ∨ (g = 1 ∧ p = 1 ∧ q = 2) ∨ (g = 2 ∧ p = 0 ∧ q = 1) ∨
  (g = 2 ∧ p = 1 ∧ q = 0) ∨ (g = 2 ∧ p = 1 ∧ q = 1) ∨ (g = 2 ∧ p = 1 ∧ q = -1) ∨
  (g = 2 ∧ p = 1 ∧ q = -2) ∨ (g = 4 ∧ p = 0 ∧ q = 1)

/-- The certificate for one direction at order `k`. -/
def Cert (k : ℕ) (g p q : ℤ) : Prop :=
  (∃ (j : ℤ) (t : ℕ) (m n : ℤ) (s₀ s₁ : ℚ) (nn J : ℕ), IsCoprime j g ∧
    ChordOK g p q j t m n s₀ s₁ ∧ JacOK nn J ∧ (nn:ℤ) ∣ 2*k ∧ IsCoprime (nn:ℤ) g ∧
    (∀ ℓ : ℕ, ℓ.Prime → (ℓ:ℤ) ∣ 2*k → (ℓ:ℤ) ∣ nn ∨ (ℓ:ℤ) ∣ g) ∧
    (J:ℚ) * g < 2*k*(s₁ - s₀)) ∨
  (∀ s t : ℤ, 0 ≤ s → s < g → 0 ≤ t → t < g → ClassOK k g p q s t)

/-- The hypotheses of `thm:lemmaA` on `(a, e = x − a)`. -/
structure Adm (k : ℕ) (a e : ℤ) : Prop where
  a_pos : 0 < a
  e_pos : 0 < e
  lt_half : 2*(a + e) < k
  a_odd : a % 2 = 1
  e_even : e % 2 = 0
  k_even : (k:ℤ) % 2 = 0
  ne3 : e ≠ 2*a
  cop : Int.gcd (Int.gcd a e) (2*k) = 1

/-- §5 of proof.md: none of the eight zero directions occurs. -/
theorem zero_excluded {k : ℕ} {a e g p q : ℤ} (h : Adm k a e) (hv : Mem (2*k) a e (g*p) (g*q))
    (hz : ZeroEntry g p q) : False := by
  obtain ⟨c, hc⟩ := hv
  replace hc : g*p*e - g*q*a = 2*((k:ℤ)*c) := by rw [hc]; ring
  have := h.a_pos; have := h.e_pos; have := h.lt_half; have := h.a_odd; have := h.e_even
  have := h.k_even; have := h.ne3
  have hk : (0:ℤ) < k := by omega
  rcases hz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases lt_trichotomy c 0 with hc0 | rfl | hc0 <;> first
      | omega
      | (have hc1 : c ≤ -1 := by omega
         have : (k:ℤ) * c ≤ -k := by nlinarith
         omega)
      | (have hc1 : 1 ≤ c := by omega
         have : (k:ℤ) ≤ k * c := by nlinarith
         omega)

/-- Step E: `Good k a e` from certificates at every direction that can be a shortest vector. -/
theorem good_of_cert {k : ℕ} {a e : ℤ} (h : Adm k a e)
    (hcert : ∀ g p q : ℤ, 0 < g → g ∣ 2*k → (0 < p ∨ (p = 0 ∧ 0 < q)) → IsCoprime p q →
      2 ∣ g*q → 3*(g^2*(p^2+q^2))^2 ≤ 16*k^2 → ¬ ZeroEntry g p q → Cert k g p q) :
    Good k a e := by
  have hk : 0 < k := by have := h.a_pos; have := h.e_pos; have := h.lt_half; omega
  set N : ℤ := 2*k with hN
  have hNpos : 0 < N := by positivity
  -- Bézout for gcd(a, e, N) = 1
  obtain ⟨x, y, z, hB⟩ : ∃ x y z : ℤ, x*a + y*e + z*N = 1 := by
    have h1 := Int.gcd_eq_gcd_ab (Int.gcd a e : ℤ) N
    have h2 := Int.gcd_eq_gcd_ab a e
    rw [h.cop] at h1
    refine ⟨Int.gcdA a e * Int.gcdA (Int.gcd a e : ℤ) N,
      Int.gcdB a e * Int.gcdA (Int.gcd a e : ℤ) N, Int.gcdB (Int.gcd a e : ℤ) N, ?_⟩
    push_cast at h1
    linear_combination -h1 - Int.gcdA (Int.gcd a e : ℤ) N * h2
  obtain ⟨v₁, v₂, w₁, w₂, hv, hw, hx, hmin, hH⟩ := exists_frame (a := a) (e := e) hNpos
  have hv0 : v₁ ≠ 0 ∨ v₂ ≠ 0 := by
    by_contra h0; push_neg at h0; rw [h0.1, h0.2] at hx; linarith
  -- normalise the sign of the shortest vector
  obtain ⟨V₁, V₂, W₁, W₂, hV, hW, hX, hmin', hH', hnorm⟩ : ∃ V₁ V₂ W₁ W₂ : ℤ,
      Mem N a e V₁ V₂ ∧ Mem N a e W₁ W₂ ∧ V₁*W₂ - V₂*W₁ = N ∧
      (∀ u₁ u₂, Mem N a e u₁ u₂ → (u₁ ≠ 0 ∨ u₂ ≠ 0) → V₁^2+V₂^2 ≤ u₁^2+u₂^2) ∧
      3*(V₁^2+V₂^2)^2 ≤ 4*N^2 ∧ (0 < V₁ ∨ (V₁ = 0 ∧ 0 < V₂)) := by
    by_cases hs : 0 < v₁ ∨ (v₁ = 0 ∧ 0 < v₂)
    · exact ⟨v₁, v₂, w₁, w₂, hv, hw, hx, hmin, hH, hs⟩
    · refine ⟨-v₁, -v₂, -w₁, -w₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa using Mem.smul (-1) hv
      · simpa using Mem.smul (-1) hw
      · linear_combination hx
      · intro u₁ u₂ hu hu0; simpa [neg_sq] using hmin u₁ u₂ hu hu0
      · simpa [neg_sq] using hH
      · push_neg at hs; omega
  have hV0 : V₁ ≠ 0 ∨ V₂ ≠ 0 := by
    rcases hnorm with h0 | ⟨_, h0⟩
    · exact Or.inl h0.ne'
    · exact Or.inr h0.ne'
  have gpos' : 0 < Int.gcd V₁ V₂ := by
    rcases hV0 with h0 | h0
    · exact Int.gcd_pos_of_ne_zero_left _ h0
    · exact Int.gcd_pos_of_ne_zero_right _ h0
  set g : ℤ := (Int.gcd V₁ V₂ : ℤ) with hg
  have gpos : 0 < g := Int.natCast_pos.2 gpos'
  set p := V₁ / g; set q := V₂ / g
  have hp : V₁ = g*p := (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)).symm
  have hq : V₂ = g*q := (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)).symm
  have hpq : IsCoprime p q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact Int.gcd_div_gcd_div_gcd gpos'
  have hnp : 0 < p ∨ (p = 0 ∧ 0 < q) := by
    rcases hnorm with h0 | ⟨h0, h1⟩
    · left; rw [hp] at h0; exact pos_of_mul_pos_right h0 gpos.le
    · right; rw [hp] at h0; rw [hq] at h1
      exact ⟨(mul_eq_zero.1 h0).resolve_left gpos.ne', pos_of_mul_pos_right h1 gpos.le⟩
  have heven : 2 ∣ g*q := by
    rw [← hq]
    obtain ⟨c, hc⟩ := hV
    have he : Even e := Int.even_iff.2 h.e_even
    have ha : ¬ Even a := by rw [Int.not_even_iff]; exact h.a_odd
    have : Even (V₂*a) := by
      have e1 : V₂*a = V₁*e - N*c := by linarith
      rw [e1]; refine Even.sub (he.mul_left _) ?_
      exact (even_two_mul (k:ℤ)).mul_right _
    rcases Int.even_mul.1 this with h0 | h0
    · exact even_iff_two_dvd.1 h0
    · exact absurd h0 ha
  have hherm : 3*(g^2*(p^2+q^2))^2 ≤ 16*k^2 := by
    have : V₁^2 + V₂^2 = g^2*(p^2+q^2) := by rw [hp, hq]; ring
    rw [← this]; nlinarith [hH']
  obtain ⟨hgN, hδ, hδ₀⟩ := frame_facts hB hNpos hV hW hX hmin'
  rw [← hg] at hgN hδ hδ₀
  rw [hp, hq] at hV hX hδ
  have hgδ : g ∣ lab x y (g*p) (g*q) := ⟨x*p + y*q, by simp only [lab]; ring⟩
  by_cases hz : ZeroEntry g p q
  · exact (zero_excluded h hV hz).elim
  rcases hcert g p q gpos hgN hnp hpq heven hherm hz with
    ⟨j, t, m, n, s₀, s₁, nn, J, hj, hc, hJ, hnn, hng, hcover, hlen⟩ | hcls
  · exact good_of_chord hk hB gpos hV hW hX hgδ hδ hδ₀ hj hc hJ hnn hng hcover hlen
  · refine good_of_class hk hB gpos hgN hV hgδ hδ ?_ hcls
    intro m hm0 hmg hmem
    have hm0' : m*p ≠ 0 ∨ m*q ≠ 0 := by
      rcases hnp with h0 | ⟨_, h0⟩
      · exact Or.inl (mul_ne_zero hm0.ne' h0.ne')
      · exact Or.inr (mul_ne_zero hm0.ne' h0.ne')
    have := hmin' _ _ hmem hm0'
    rw [hp, hq] at this
    have hU : 0 < p^2 + q^2 := by rcases hnp with h0 | ⟨_, h0⟩ <;> positivity
    have : (g^2 - m^2)*(p^2+q^2) ≤ 0 := by nlinarith
    have : g^2 - m^2 ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith
    nlinarith


end APLemma