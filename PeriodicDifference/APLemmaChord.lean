/-
# `PeriodicDifference/APLemmaChord.lean` — `thm:lemmaA`, stage 4: a chord of a good geodesic (Prop 5)

The four open triangles of `R` in the unit torus, scaled by 4 (`triF`, vertices as in
`chord_verify.py`'s `TV`), and their integral forms at scale `N = 2k` (`triZ`, `inR_of_triZ`).

A chord witness `(g, u = (p,q), j, t, (m,n), s₀, s₁)` (`ChordOK`, one row of `ct80.txt`) says
that the points `P₀ + s u`, `P₀ = j(−q,p)/(g|u|²)`, are in the closed triangle `T_t + (m,n)`
at `s = s₀, s₁` and not on the same edge, so the open segment lies in the open triangle
(`chord_pos`).  `good_of_chord` is Prop 5 (in the exact form of `B1_argument.txt`, Step B):
if `v = g u` and `w` frame `Λ` (`v × w = N`), the labels satisfy (3.1)–(3.2), and
`N(s₁ − s₀) > J g` with `JacOK n J` for an `n` covering the primes of `N` outside `g`,
then `Good k a e`.
-/
import PeriodicDifference.APLemmaLattice
import PeriodicDifference.APLemmaJac

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

/-- The affine functionals of the open triangle `T_t` (the paper's `Δ_t`; unit torus scaled by
4). -/
def triF (t : ℕ) (X Y : ℚ) : ℚ × ℚ × ℚ :=
  match t with
  | 0 => (2 - X, X - Y, X + Y - 2)
  | 1 => (4 - X, X - 2 - Y, X + Y - 4)
  | 2 => (X, Y - 2 - X, 4 - Y - X)
  | _ => (X - 2, Y - X, 6 - Y - X)

/-- The same functionals at scale `N`, integral: `triZ t A E N = N • triF t (4A/N) (4E/N)`. -/
def triZ (t : ℕ) (A E N : ℤ) : ℤ × ℤ × ℤ :=
  match t with
  | 0 => (2*N - 4*A, 4*A - 4*E, 4*A + 4*E - 2*N)
  | 1 => (4*N - 4*A, 4*A - 2*N - 4*E, 4*A + 4*E - 4*N)
  | 2 => (4*A, 4*E - 2*N - 4*A, 4*N - 4*E - 4*A)
  | _ => (4*A - 2*N, 4*E - 4*A, 6*N - 4*E - 4*A)

theorem triF_eq (t : ℕ) (A E N : ℤ) (hN : N ≠ 0) :
    triF t (4*(A:ℚ)/N) (4*(E:ℚ)/N) = (((triZ t A E N).1 : ℚ) / N,
      ((triZ t A E N).2.1 : ℚ) / N, ((triZ t A E N).2.2 : ℚ) / N) := by
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN
  rcases t with _ | _ | _ | t <;> simp only [triF, triZ, Prod.mk.injEq] <;> push_cast <;>
    refine ⟨?_, ?_, ?_⟩ <;> field_simp

theorem inR_of_triZ {k : ℕ} {t : ℕ} {A E : ℤ}
    (h : 0 < (triZ t A E (2*k)).1 ∧ 0 < (triZ t A E (2*k)).2.1 ∧ 0 < (triZ t A E (2*k)).2.2) :
    0 ≤ A ∧ A < 2*k ∧ 0 ≤ E ∧ E < 2*k ∧ InR k A E := by
  rcases t with _ | _ | _ | t <;> simp only [triZ] at h <;> simp only [InR, abs_lt] <;> omega

/-- The functionals along the parametrised geodesic `P₀ + s u`, translated by `(m, n)`. -/
def chordF (g p q j : ℤ) (t : ℕ) (m n : ℤ) (s : ℚ) : ℚ × ℚ × ℚ :=
  triF t (4*(-q*j/(g*(p^2+q^2)) + s*p) - 4*m) (4*(p*j/(g*(p^2+q^2)) + s*q) - 4*n)

/-- A chord witness: endpoints in the closed triangle, not both on one edge. -/
def ChordOK (g p q j : ℤ) (t : ℕ) (m n : ℤ) (s₀ s₁ : ℚ) : Prop :=
  0 ≤ (chordF g p q j t m n s₀).1 ∧ 0 ≤ (chordF g p q j t m n s₁).1 ∧
  (0 < (chordF g p q j t m n s₀).1 ∨ 0 < (chordF g p q j t m n s₁).1) ∧
  0 ≤ (chordF g p q j t m n s₀).2.1 ∧ 0 ≤ (chordF g p q j t m n s₁).2.1 ∧
  (0 < (chordF g p q j t m n s₀).2.1 ∨ 0 < (chordF g p q j t m n s₁).2.1) ∧
  0 ≤ (chordF g p q j t m n s₀).2.2 ∧ 0 ≤ (chordF g p q j t m n s₁).2.2 ∧
  (0 < (chordF g p q j t m n s₀).2.2 ∨ 0 < (chordF g p q j t m n s₁).2.2)

theorem chordF_interp (g p q j : ℤ) (t : ℕ) (m n : ℤ) (s₀ s₁ s : ℚ) :
    let F := chordF g p q j t m n
    (s₁ - s₀) * (F s).1 = (s₁ - s) * (F s₀).1 + (s - s₀) * (F s₁).1 ∧
    (s₁ - s₀) * (F s).2.1 = (s₁ - s) * (F s₀).2.1 + (s - s₀) * (F s₁).2.1 ∧
    (s₁ - s₀) * (F s).2.2 = (s₁ - s) * (F s₀).2.2 + (s - s₀) * (F s₁).2.2 := by
  rcases t with _ | _ | _ | t <;> simp only [chordF, triF] <;> refine ⟨?_, ?_, ?_⟩ <;> ring

theorem pos_of_interp {A B C s₀ s₁ s : ℚ} (h : (s₁ - s₀) * C = (s₁ - s) * A + (s - s₀) * B)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB' : 0 < A ∨ 0 < B) (h0 : s₀ < s) (h1 : s < s₁) :
    0 < C := by
  have hAB : 0 < A + B := by rcases hAB' with h | h <;> linarith
  have hpos : 0 < (s₁ - s) * A + (s - s₀) * B := by
    rcases lt_or_eq_of_le hA with hA' | hA'
    · have := mul_pos (sub_pos.2 h1) hA'
      have := mul_nonneg (sub_pos.2 h0).le hB
      linarith
    · have hB' : 0 < B := by linarith
      have := mul_pos (sub_pos.2 h0) hB'
      rw [← hA']; linarith
  rw [← h] at hpos
  exact pos_of_mul_pos_right hpos (sub_pos.2 (h0.trans h1)).le

theorem chord_pos {g p q j : ℤ} {t : ℕ} {m n : ℤ} {s₀ s₁ s : ℚ}
    (h : ChordOK g p q j t m n s₀ s₁) (h0 : s₀ < s) (h1 : s < s₁) :
    0 < (chordF g p q j t m n s).1 ∧ 0 < (chordF g p q j t m n s).2.1 ∧
    0 < (chordF g p q j t m n s).2.2 := by
  obtain ⟨i1, i2, i3⟩ := chordF_interp g p q j t m n s₀ s₁ s
  obtain ⟨a1, b1, c1, a2, b2, c2, a3, b3, c3⟩ := h
  exact ⟨pos_of_interp i1 a1 b1 c1 h0 h1, pos_of_interp i2 a2 b2 c2 h0 h1,
    pos_of_interp i3 a3 b3 c3 h0 h1⟩

/-- The lattice point `j w + i v` seen on the geodesic: `(jw + iv)/N = P₀ + s u`. -/
theorem chordF_point {g p q w₁ w₂ j m n N : ℤ} {t : ℕ} (hg : g ≠ 0)
    (hN : N = g*(p*w₂ - q*w₁)) (hN0 : N ≠ 0) (i : ℤ) :
    chordF g p q j t m n ((j*(p*w₁ + q*w₂) : ℤ) / (N*(p^2+q^2)) + i*g/N) =
      triF t (4*((j*w₁ + i*(g*p) - m*N : ℤ):ℚ)/N) (4*((j*w₂ + i*(g*q) - n*N : ℤ):ℚ)/N) := by
  have hpq : p*w₂ - q*w₁ ≠ 0 := by rintro h; rw [h] at hN; simp at hN; exact hN0 hN
  have hU : (p:ℚ)^2 + q^2 ≠ 0 := by
    intro h
    have h1 : (p:ℚ) = 0 := by nlinarith
    have h2 : (q:ℚ) = 0 := by nlinarith
    apply hpq; exact_mod_cast (by rw [h1, h2]; ring : (p:ℚ)*w₂ - q*w₁ = 0)
  have hg' : (g:ℚ) ≠ 0 := by exact_mod_cast hg
  have hpq' : (p:ℚ)*w₂ - q*w₁ ≠ 0 := by exact_mod_cast hpq
  have hNq : (N:ℚ) = g*(p*w₂ - q*w₁) := by exact_mod_cast hN
  unfold chordF
  congr 1
  · push_cast; rw [hNq]; field_simp; ring
  · push_cast; rw [hNq]; field_simp; ring

/-- Prop 5 (Step B of `B1_argument.txt`): a witnessed chord of a good geodesic, longer than
`J` lattice steps, carries a unit point of `Λ` in `R`. -/
theorem good_of_chord {k : ℕ} (hk : 0 < k) {a e x y z : ℤ} (hB : x*a + y*e + z*(2*k) = 1)
    {g p q w₁ w₂ : ℤ} (hg : 0 < g)
    (hvm : Mem (2*k) a e (g*p) (g*q)) (hwm : Mem (2*k) a e w₁ w₂)
    (hx : (g*p)*w₂ - (g*q)*w₁ = 2*k)
    (hgδ : g ∣ lab x y (g*p) (g*q))
    (hδ : ∀ ℓ : ℤ, 0 < ℓ → ℓ ∣ 2*k → ℓ ∣ lab x y (g*p) (g*q) → ℓ ∣ g)
    (hδ₀ : IsCoprime (lab x y w₁ w₂) g)
    {j : ℤ} (hj : IsCoprime j g) {t : ℕ} {m n : ℤ} {s₀ s₁ : ℚ}
    (hc : ChordOK g p q j t m n s₀ s₁)
    {nn J : ℕ} (hJ : JacOK nn J) (hnn : (nn:ℤ) ∣ 2*k) (hng : IsCoprime (nn:ℤ) g)
    (hcover : ∀ ℓ : ℕ, ℓ.Prime → (ℓ:ℤ) ∣ 2*k → (ℓ:ℤ) ∣ nn ∨ (ℓ:ℤ) ∣ g)
    (hlen : (J:ℚ) * g < 2*k*(s₁ - s₀)) : Good k a e := by
  set N : ℤ := 2*k with hNdef
  have hN : 0 < N := by positivity
  set δ := lab x y (g*p) (g*q)
  set δ₀ := lab x y w₁ w₂
  -- δ is prime to nn
  have hδn : IsCoprime δ (nn:ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    set c : ℤ := (Int.gcd δ nn : ℤ)
    have hc1 : c ∣ δ := Int.gcd_dvd_left _ _
    have hc2 : c ∣ (nn:ℤ) := Int.gcd_dvd_right _ _
    have hnn0 : (nn:ℤ) ≠ 0 := by rintro h; rw [h, zero_dvd_iff] at hnn; omega
    have hcpos : 0 < c := Int.natCast_pos.2 (Int.gcd_pos_of_ne_zero_right _ hnn0)
    have hcg := hδ c hcpos (hc2.trans hnn) hc1
    have hu := IsCoprime.isUnit_of_dvd' hng hc2 hcg
    rw [Int.isUnit_iff] at hu
    have : c = 1 := by omega
    simp only [c] at this; exact_mod_cast this
  -- the parameters of the lattice points on line j
  set σ₀ : ℚ := ((j*(p*w₁ + q*w₂) : ℤ) : ℚ) / (N*(p^2+q^2))
  have hNq : (0:ℚ) < N := by exact_mod_cast hN
  have hgq : (0:ℚ) < g := by exact_mod_cast hg
  set X : ℚ := (s₀ - σ₀) * N / g
  set i₀ : ℤ := ⌊X⌋ + 1
  obtain ⟨i', hi', hunit⟩ := exists_unit_on_line hJ hδn hgδ hj hδ₀ hcover i₀
  set i : ℤ := i₀ + i'
  have hsi0 : s₀ < σ₀ + i*g/N := by
    have h1 : X < i := by
      have := Int.lt_floor_add_one X
      have : (0:ℚ) ≤ i' := by positivity
      push_cast [i, i₀]; linarith
    have : (s₀ - σ₀) * N / g * g / N = s₀ - σ₀ := by field_simp
    have h2 : X * g / N < i * g / N := by
      apply div_lt_div_of_pos_right _ hNq; exact mul_lt_mul_of_pos_right h1 hgq
    rw [this] at h2; linarith
  have hsi1 : σ₀ + i*g/N < s₁ := by
    have h1 : (i:ℚ) ≤ X + J := by
      have := Int.floor_le X
      have : (i':ℚ) + 1 ≤ J := by exact_mod_cast hi'
      push_cast [i, i₀]; linarith
    have h2 : (i:ℚ) * g / N ≤ (X + J) * g / N := by
      apply div_le_div_of_nonneg_right _ hNq.le; exact mul_le_mul_of_nonneg_right h1 hgq.le
    have : (X + J) * g / N = (s₀ - σ₀) + J*g/N := by simp only [X]; field_simp
    have hNk : ((N:ℤ):ℚ) = 2*k := by simp only [N]; push_cast; ring
    have h3 : (J:ℚ)*g/N < s₁ - s₀ := by rw [div_lt_iff₀ hNq, hNk]; linarith
    linarith
  have hpos := chord_pos hc hsi0 hsi1
  have hxN : N = g*(p*w₂ - q*w₁) := by rw [← hx]; ring
  rw [chordF_point hg.ne' hxN hN.ne' i, triF_eq t _ _ N hN.ne'] at hpos
  obtain ⟨p1, p2, p3⟩ := hpos
  have z1 := (div_pos_iff_of_pos_right hNq).1 p1
  have z2 := (div_pos_iff_of_pos_right hNq).1 p2
  have z3 := (div_pos_iff_of_pos_right hNq).1 p3
  norm_cast at z1 z2 z3
  obtain ⟨A0, A1, E0, E1, hR⟩ := inR_of_triZ (k := k) ⟨z1, z2, z3⟩
  -- the lattice point W = j w + i v
  have hWm : Mem N a e (j*w₁ + i*(g*p)) (j*w₂ + i*(g*q)) :=
    (Mem.smul j hwm).add (Mem.smul i hvm)
  have hlab : lab x y (j*w₁ + i*(g*p)) (j*w₂ + i*(g*q)) = j*δ₀ + (i₀ + i')*δ := by
    simp only [lab, δ, δ₀, i]; ring
  refine good_of_point hB hWm ?_ ?_
  · rw [hlab, ← Int.isCoprime_iff_gcd_eq_one]; exact hunit
  · have e1 : (j*w₁ + i*(g*p)) % N = j*w₁ + i*(g*p) - m*N := by
      have := Int.emod_eq_of_lt A0 A1
      rwa [Int.sub_emod, Int.mul_emod_left, sub_zero, Int.emod_emod] at this
    have e2 : (j*w₂ + i*(g*q)) % N = j*w₂ + i*(g*q) - n*N := by
      have := Int.emod_eq_of_lt E0 E1
      rwa [Int.sub_emod, Int.mul_emod_left, sub_zero, Int.emod_emod] at this
    rw [e1, e2]; exact hR

end APLemma
end Bump
end Trop
end PeriodicDifference
