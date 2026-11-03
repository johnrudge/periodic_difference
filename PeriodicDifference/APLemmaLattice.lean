/-
# `PeriodicDifference/APLemmaLattice.lean` — `thm:lemmaA`, stage 2: the lattice, labels, Hermite

`Λ = ℤ(a,e) + Nℤ²` (`N = 2k`, `gcd(a,e,N) = 1`, witnessed by `x a + y e + z N = 1`) is
described by its dual equation: `w ∈ Λ ↔ N ∣ w₁e − w₂a` (`Mem`).  The label of `w ∈ Λ` is the
*linear* form `lab w = x w₁ + y w₂`, and `w ≡ lab w · (a,e) (mod N)` (`mem_lab`).

* `good_of_point` — (2.1) of proof.md: a unit point of `Λ` in `R` gives `Good`.
* `exists_frame` — a shortest nonzero `v ∈ Λ` and `w ∈ Λ` with `v × w = N`, and Hermite's
  bound in dimension 2 in the integral form `3|v|⁴ ≤ 4N²` (Step A of `B1_argument.txt`).
-/
import PeriodicDifference.APLemmaBasic

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

/-- Membership in `Λ = ℤ(a,e) + Nℤ²`, by the dual equation. -/
def Mem (N a e w₁ w₂ : ℤ) : Prop := N ∣ w₁*e - w₂*a

/-- The label of a lattice point (linear, from the Bézout relation `x a + y e + z N = 1`). -/
def lab (x y w₁ w₂ : ℤ) : ℤ := x*w₁ + y*w₂

section
variable {N a e x y z : ℤ}

theorem mem_lab (hB : x*a + y*e + z*N = 1) {w₁ w₂ : ℤ} (h : Mem N a e w₁ w₂) :
    N ∣ w₁ - lab x y w₁ w₂ * a ∧ N ∣ w₂ - lab x y w₁ w₂ * e := by
  obtain ⟨c, hc⟩ := h
  unfold lab
  constructor
  · refine ⟨y*c + z*w₁, ?_⟩
    linear_combination -w₁ * hB + y * hc
  · refine ⟨-x*c + z*w₂, ?_⟩
    linear_combination -w₂ * hB - x * hc

theorem mem_of_mul (d : ℤ) : Mem N a e (d*a) (d*e) := ⟨0, by ring⟩

theorem Mem.add {u₁ u₂ w₁ w₂ : ℤ} (hu : Mem N a e u₁ u₂) (hw : Mem N a e w₁ w₂) :
    Mem N a e (u₁ + w₁) (u₂ + w₂) := by
  obtain ⟨c, hc⟩ := hu; obtain ⟨c', hc'⟩ := hw
  exact ⟨c + c', by linear_combination hc + hc'⟩

theorem Mem.smul {w₁ w₂ : ℤ} (t : ℤ) (hw : Mem N a e w₁ w₂) : Mem N a e (t*w₁) (t*w₂) := by
  obtain ⟨c, hc⟩ := hw
  exact ⟨t*c, by linear_combination t * hc⟩

theorem mem_N (s t : ℤ) : Mem N a e (N*s) (N*t) := ⟨s*e - t*a, by ring⟩

/-- Cross products of lattice points are divisible by `N`. -/
theorem cross_dvd (hB : x*a + y*e + z*N = 1) {u₁ u₂ w₁ w₂ : ℤ} (hu : Mem N a e u₁ u₂)
    (hw : Mem N a e w₁ w₂) : N ∣ u₁*w₂ - u₂*w₁ := by
  obtain ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ := mem_lab hB hu
  obtain ⟨⟨c₃, h₃⟩, ⟨c₄, h₄⟩⟩ := mem_lab hB hw
  set l := lab x y u₁ u₂; set l' := lab x y w₁ w₂
  refine ⟨c₁*w₂ - c₂*w₁ + l*a*c₄ - l*e*c₃, ?_⟩
  have e1 : u₁ = N*c₁ + l*a := by linarith
  have e2 : u₂ = N*c₂ + l*e := by linarith
  have e3 : w₁ = N*c₃ + l'*a := by linarith
  have e4 : w₂ = N*c₄ + l'*e := by linarith
  rw [e1, e2, e3, e4]; ring

/-- (2.1): a unit lattice point lying in `R` modulo `N = 2k` gives `Good`. -/
theorem good_of_point {k : ℕ} (hB : x*a + y*e + z*(2*k) = 1) {w₁ w₂ : ℤ}
    (hw : Mem (2*k) a e w₁ w₂) (hu : Int.gcd (lab x y w₁ w₂) (2*k) = 1)
    (hR : InR k (w₁ % (2*k)) (w₂ % (2*k))) : Good k a e := by
  obtain ⟨h1, h2⟩ := mem_lab hB hw
  refine good_of_inR hu ?_
  have e1 : (lab x y w₁ w₂ * a) % (2*k) = w₁ % (2*k) := (Int.modEq_iff_dvd.2 h1)
  have e2 : (lab x y w₁ w₂ * e) % (2*k) = w₂ % (2*k) := (Int.modEq_iff_dvd.2 h2)
  rw [e1, e2]; exact hR

/-- A shortest nonzero vector of `Λ` exists. -/
theorem exists_shortest (hN : 0 < N) : ∃ v₁ v₂ : ℤ, Mem N a e v₁ v₂ ∧ (v₁ ≠ 0 ∨ v₂ ≠ 0) ∧
    ∀ u₁ u₂, Mem N a e u₁ u₂ → (u₁ ≠ 0 ∨ u₂ ≠ 0) → v₁^2+v₂^2 ≤ u₁^2+u₂^2 := by
  classical
  have ex : ∃ n : ℕ, ∃ u₁ u₂ : ℤ, Mem N a e u₁ u₂ ∧ (u₁ ≠ 0 ∨ u₂ ≠ 0) ∧ u₁^2+u₂^2 = n :=
    ⟨(N^2).toNat, N, 0, by simpa using (mem_N (a := a) (e := e) (N := N) 1 0),
      Or.inl hN.ne', by rw [Int.toNat_of_nonneg (by positivity)]; ring⟩
  obtain ⟨v₁, v₂, hv, hv0, hn⟩ := Nat.find_spec ex
  refine ⟨v₁, v₂, hv, hv0, fun u₁ u₂ hu hu0 => ?_⟩
  have := Nat.find_min' ex ⟨u₁, u₂, hu, hu0, (Int.toNat_of_nonneg (by positivity)).symm⟩
  rw [hn]
  have h2 := Int.toNat_of_nonneg (show 0 ≤ u₁^2+u₂^2 by positivity)
  omega

/-- Step A: a shortest vector `v`, a partner `w ∈ Λ` with `v × w = N`, and Hermite's bound
`3|v|⁴ ≤ 4N²` (i.e. `|v|² ≤ (2/√3) det Λ`). -/
theorem exists_frame (hN : 0 < N) :
    ∃ v₁ v₂ w₁ w₂ : ℤ, Mem N a e v₁ v₂ ∧ Mem N a e w₁ w₂ ∧ v₁*w₂ - v₂*w₁ = N ∧
      (∀ u₁ u₂, Mem N a e u₁ u₂ → (u₁ ≠ 0 ∨ u₂ ≠ 0) → v₁^2+v₂^2 ≤ u₁^2+u₂^2) ∧
      3*(v₁^2+v₂^2)^2 ≤ 4*N^2 := by
  obtain ⟨v₁, v₂, hv, hv0, hmin⟩ := exists_shortest (a := a) (e := e) hN
  obtain ⟨φ, hφ⟩ := hv
  -- c = gcd(v₁, v₂, φ) = 1 by minimality
  set c : ℤ := (Int.gcd (Int.gcd v₁ v₂ : ℤ) φ : ℤ) with hc
  have hc1 : c ∣ v₁ := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
  have hc2 : c ∣ v₂ := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
  have hc3 : c ∣ φ := Int.gcd_dvd_right _ _
  obtain ⟨α₁, hα₁⟩ := hc1; obtain ⟨α₂, hα₂⟩ := hc2; obtain ⟨β, hβ⟩ := hc3
  have cpos : 0 < c := by
    rw [hc]; rcases hv0 with h | h
    · exact_mod_cast Int.gcd_pos_of_ne_zero_left _
        (by exact_mod_cast (Int.gcd_pos_of_ne_zero_left _ h).ne')
    · exact_mod_cast Int.gcd_pos_of_ne_zero_left _
        (by exact_mod_cast (Int.gcd_pos_of_ne_zero_right _ h).ne')
  have hαmem : Mem N a e α₁ α₂ := by
    refine ⟨β, ?_⟩
    have : c * (α₁*e - α₂*a) = c * (N*β) := by
      rw [hα₁, hα₂, hβ] at hφ; linear_combination hφ
    exact mul_left_cancel₀ cpos.ne' this
  have hα0 : α₁ ≠ 0 ∨ α₂ ≠ 0 := by
    rcases hv0 with h | h
    · left; rintro rfl; simp at hα₁; exact h hα₁
    · right; rintro rfl; simp at hα₂; exact h hα₂
  have c1 : c = 1 := by
    have := hmin α₁ α₂ hαmem hα0
    rw [hα₁, hα₂] at this
    have hp : 0 < α₁^2 + α₂^2 := by
      rcases hα0 with h | h <;> positivity
    have : (c^2 - 1) * (α₁^2+α₂^2) ≤ 0 := by nlinarith
    have : c^2 ≤ 1 := by nlinarith
    nlinarith
  -- Bézout: A v₁ + B v₂ + C φ = 1
  have hg : (Int.gcd (Int.gcd v₁ v₂ : ℤ) φ : ℤ) = 1 := by rw [← hc, c1]
  have b1 := Int.gcd_eq_gcd_ab (Int.gcd v₁ v₂ : ℤ) φ
  have b2 := Int.gcd_eq_gcd_ab v₁ v₂
  set A := Int.gcdA v₁ v₂ * Int.gcdA (Int.gcd v₁ v₂ : ℤ) φ
  set B := Int.gcdB v₁ v₂ * Int.gcdA (Int.gcd v₁ v₂ : ℤ) φ
  set C := Int.gcdB (Int.gcd v₁ v₂ : ℤ) φ
  have hABC : A*v₁ + B*v₂ + C*φ = 1 := by
    rw [hg] at b1; simp only [A, B, C]
    linear_combination -b1 - Int.gcdA (Int.gcd v₁ v₂ : ℤ) φ * b2
  -- the partner w₀ with v × w₀ = N
  set w₁ := -B*N + C*a; set w₂ := A*N + C*e
  have hw0 : Mem N a e w₁ w₂ := ⟨-B*e - A*a, by simp only [w₁, w₂]; ring⟩
  have hcross0 : v₁*w₂ - v₂*w₁ = N := by
    simp only [w₁, w₂]; linear_combination N * hABC + C * hφ
  -- reduce w₀ along v
  set n2 := v₁^2 + v₂^2
  have n2pos : 0 < n2 := by rcases hv0 with h | h <;> positivity
  set D := v₁*w₁ + v₂*w₂
  set t := -((2*D + n2) / (2*n2))
  have hdiv := Int.emod_add_mul_ediv (2*D + n2) (2*n2)
  have hr0 := Int.emod_nonneg (2*D + n2) (show 2*n2 ≠ 0 by positivity)
  have hr1 := Int.emod_lt_of_pos (2*D + n2) (show 0 < 2*n2 by positivity)
  set W₁ := w₁ + t*v₁; set W₂ := w₂ + t*v₂
  have hW : Mem N a e W₁ W₂ := hw0.add (Mem.smul t ⟨φ, hφ⟩)
  have hcross : v₁*W₂ - v₂*W₁ = N := by simp only [W₁, W₂]; linear_combination hcross0
  have hdot : v₁*W₁ + v₂*W₂ = D + t*n2 := by simp only [W₁, W₂, D, n2]; ring
  have hdot2 : (2*(v₁*W₁ + v₂*W₂))^2 ≤ n2^2 := by
    rw [hdot]
    have : 2*(D + t*n2) = (2*D + n2) % (2*n2) - n2 := by
      simp only [t]; linear_combination -hdiv
    rw [this]; nlinarith
  have hW0 : W₁ ≠ 0 ∨ W₂ ≠ 0 := by
    by_contra h; push_neg at h; rw [h.1, h.2] at hcross; linarith
  have hWmin := hmin W₁ W₂ hW hW0
  refine ⟨v₁, v₂, W₁, W₂, ⟨φ, hφ⟩, hW, hcross, hmin, ?_⟩
  have lag : (v₁*W₂ - v₂*W₁)^2 + (v₁*W₁ + v₂*W₂)^2 = n2 * (W₁^2+W₂^2) := by
    simp only [n2]; ring
  rw [hcross] at lag
  have h1 : n2*n2 ≤ n2*(W₁^2+W₂^2) := mul_le_mul_of_nonneg_left hWmin n2pos.le
  have h2 : 4*(v₁*W₁+v₂*W₂)^2 ≤ n2^2 := by
    have : (2*(v₁*W₁ + v₂*W₂))^2 = 4*(v₁*W₁+v₂*W₂)^2 := by ring
    linarith
  have h3 : n2^2 = n2*n2 := by ring
  show 3*n2^2 ≤ 4*N^2
  linarith


/-- The facts about a shortest vector `v = g u` used by Props 5 and Step D: `g ∣ N`;
a divisor of `N` and of `lab v` divides `g` ((3.1)); `lab w` is prime to `g` ((3.2)). -/
theorem frame_facts (hB : x*a + y*e + z*N = 1) (hN : 0 < N) {v₁ v₂ w₁ w₂ : ℤ}
    (hv : Mem N a e v₁ v₂) (hw : Mem N a e w₁ w₂) (hx : v₁*w₂ - v₂*w₁ = N)
    (hmin : ∀ u₁ u₂, Mem N a e u₁ u₂ → (u₁ ≠ 0 ∨ u₂ ≠ 0) → v₁^2+v₂^2 ≤ u₁^2+u₂^2) :
    ((Int.gcd v₁ v₂ : ℤ) ∣ N) ∧
    (∀ ℓ : ℤ, 0 < ℓ → ℓ ∣ N → ℓ ∣ lab x y v₁ v₂ → ℓ ∣ (Int.gcd v₁ v₂ : ℤ)) ∧
    IsCoprime (lab x y w₁ w₂) (Int.gcd v₁ v₂ : ℤ) := by
  set g : ℤ := (Int.gcd v₁ v₂ : ℤ) with hg
  obtain ⟨p, hp⟩ : g ∣ v₁ := Int.gcd_dvd_left _ _
  obtain ⟨q, hq⟩ : g ∣ v₂ := Int.gcd_dvd_right _ _
  have hv0 : v₁ ≠ 0 ∨ v₂ ≠ 0 := by
    by_contra h; push_neg at h; rw [h.1, h.2] at hx; linarith
  have gpos : 0 < g := by
    rcases hv0 with h | h
    · exact Int.natCast_pos.2 (Int.gcd_pos_of_ne_zero_left _ h)
    · exact Int.natCast_pos.2 (Int.gcd_pos_of_ne_zero_right _ h)
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    rcases hv0 with h | h
    · left; rintro rfl; simp at hp; exact h hp
    · right; rintro rfl; simp at hq; exact h hq
  have upos : 0 < p^2 + q^2 := by rcases hpq with h | h <;> positivity
  have hgN : g ∣ N := by
    -- h = gcd(N, g) gives a lattice vector h u, so h ≥ g
    set h : ℤ := (Int.gcd N g : ℤ) with hh
    have hb := Int.gcd_eq_gcd_ab N g
    have hmem : Mem N a e (h*p) (h*q) := by
      have e1 : h*p = N*(Int.gcdA N g * p) + Int.gcdB N g * v₁ := by
        rw [hh, hb, hp]; ring
      have e2 : h*q = N*(Int.gcdA N g * q) + Int.gcdB N g * v₂ := by
        rw [hh, hb, hq]; ring
      rw [e1, e2]; exact (mem_N _ _).add (Mem.smul _ hv)
    have hpos : 0 < h := Int.natCast_pos.2 (Int.gcd_pos_of_ne_zero_left _ hN.ne')
    have h0 : h*p ≠ 0 ∨ h*q ≠ 0 := by
      rcases hpq with h' | h'
      · left; exact mul_ne_zero hpos.ne' h'
      · right; exact mul_ne_zero hpos.ne' h'
    have := hmin _ _ hmem h0
    rw [hp, hq] at this
    have hle : h ≤ g := Int.le_of_dvd gpos (Int.gcd_dvd_right _ _)
    have hge : g ≤ h := by
      by_contra hlt; push_neg at hlt
      have : (h^2 - g^2) * (p^2+q^2) < 0 :=
        mul_neg_of_neg_of_pos (by nlinarith) upos
      nlinarith
    have : h = g := le_antisymm hle hge
    rw [← this]; exact Int.gcd_dvd_left _ _
  refine ⟨hgN, ?_, ?_⟩
  · intro ℓ _ hℓN hℓd
    obtain ⟨M, hM⟩ := hℓN
    obtain ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ := mem_lab hB hv
    obtain ⟨r, hr⟩ := hℓd
    have d1 : ℓ ∣ v₁ := ⟨r*a + M*c₁, by rw [hM, hr] at h₁; linear_combination h₁⟩
    have d2 : ℓ ∣ v₂ := ⟨r*e + M*c₂, by rw [hM, hr] at h₂; linear_combination h₂⟩
    exact Int.dvd_coe_gcd d1 d2
  · -- Cramer: N (a,e) = (a,e)×w · v + v×(a,e) · w, both coefficients divisible by N
    obtain ⟨A, hA⟩ := cross_dvd hB (mem_of_mul (N := N) (a := a) (e := e) 1) hw
    obtain ⟨B, hB'⟩ := cross_dvd hB (mem_of_mul (N := N) (a := a) (e := e) 1) hv
    have ea : a = A*v₁ - B*w₁ := by
      have : N*a = N*(A*v₁ - B*w₁) := by
        linear_combination -a * hx + v₁ * hA - w₁ * hB'
      exact mul_left_cancel₀ hN.ne' this
    have ee : e = A*v₂ - B*w₂ := by
      have : N*e = N*(A*v₂ - B*w₂) := by
        linear_combination -e * hx + v₂ * hA - w₂ * hB'
      exact mul_left_cancel₀ hN.ne' this
    obtain ⟨Ng, hNg⟩ := hgN
    refine ⟨-B, z*Ng + A*(x*p + y*q), ?_⟩
    unfold lab
    rw [ea, ee, hNg, hp, hq] at hB
    linear_combination hB

end

end APLemma
end Bump
end Trop
end PeriodicDifference
