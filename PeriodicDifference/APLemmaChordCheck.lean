/-
# `PeriodicDifference/APLemmaChordCheck.lean` — integral decision procedure for chord witnesses

`chordCheck` evaluates the triangle functionals at the two endpoints `s = a/b` after scaling
by `D = g|u|²b > 0` (`chordZ`), so a row of `ct80.txt` is checked in `ℤ` by the kernel;
`chordOK_of_check` transfers it to `ChordOK`.
-/
import PeriodicDifference.APLemmaChord

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

/-- `triF` made homogeneous: `triH t (D X) (D Y) D = D • triF t X Y`. -/
def triH (t : ℕ) (X Y D : ℤ) : ℤ × ℤ × ℤ :=
  match t with
  | 0 => (2*D - X, X - Y, X + Y - 2*D)
  | 1 => (4*D - X, X - 2*D - Y, X + Y - 4*D)
  | 2 => (X, Y - 2*D - X, 4*D - Y - X)
  | _ => (X - 2*D, Y - X, 6*D - Y - X)

/-- The functionals of `chordF` at `s = a/b`, scaled by `g|u|²b`. -/
def chordZ (g p q j : ℤ) (t : ℕ) (m n a b : ℤ) : ℤ × ℤ × ℤ :=
  triH t (4*(-q*j*b + a*p*(g*(p^2+q^2))) - 4*m*(g*(p^2+q^2)*b))
    (4*(p*j*b + a*q*(g*(p^2+q^2))) - 4*n*(g*(p^2+q^2)*b)) (g*(p^2+q^2)*b)

theorem chordF_eq_Z {g p q j : ℤ} (t : ℕ) (m n a b : ℤ) (hg : 0 < g) (hU : 0 < p^2+q^2)
    (hb : 0 < b) :
    chordF g p q j t m n ((a:ℚ)/b) =
      (((chordZ g p q j t m n a b).1 : ℚ) / (g*(p^2+q^2)*b),
       ((chordZ g p q j t m n a b).2.1 : ℚ) / (g*(p^2+q^2)*b),
       ((chordZ g p q j t m n a b).2.2 : ℚ) / (g*(p^2+q^2)*b)) := by
  have hg' : (g:ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hU' : (p:ℚ)^2 + q^2 ≠ 0 := by exact_mod_cast hU.ne'
  have hb' : (b:ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  rcases t with _ | _ | _ | t <;> simp only [chordF, triF, chordZ, triH, Prod.mk.injEq] <;>
    push_cast <;> refine ⟨?_, ?_, ?_⟩ <;> field_simp

/-- Kernel check of one chord witness. -/
def chordCheck (g p q j : ℤ) (t : ℕ) (m n a₀ b₀ a₁ b₁ : ℤ) : Bool :=
  decide (0 < g) && decide (0 < p^2+q^2) && decide (0 < b₀) && decide (0 < b₁) &&
  (let A := chordZ g p q j t m n a₀ b₀
   let B := chordZ g p q j t m n a₁ b₁
   decide (0 ≤ A.1) && decide (0 ≤ B.1) && (decide (0 < A.1) || decide (0 < B.1)) &&
   decide (0 ≤ A.2.1) && decide (0 ≤ B.2.1) && (decide (0 < A.2.1) || decide (0 < B.2.1)) &&
   decide (0 ≤ A.2.2) && decide (0 ≤ B.2.2) && (decide (0 < A.2.2) || decide (0 < B.2.2)))

theorem chordOK_of_check {g p q j : ℤ} {t : ℕ} {m n a₀ b₀ a₁ b₁ : ℤ}
    (h : chordCheck g p q j t m n a₀ b₀ a₁ b₁ = true) :
    ChordOK g p q j t m n ((a₀:ℚ)/b₀) ((a₁:ℚ)/b₁) := by
  simp only [chordCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hg, hU⟩, hb₀⟩, hb₁⟩, h⟩ := h
  have D₀ : (0:ℚ) < g*(p^2+q^2)*b₀ := by
    have : (0:ℤ) < g*(p^2+q^2)*b₀ := by positivity
    exact_mod_cast this
  have D₁ : (0:ℚ) < g*(p^2+q^2)*b₁ := by
    have : (0:ℤ) < g*(p^2+q^2)*b₁ := by positivity
    exact_mod_cast this
  unfold ChordOK
  rw [chordF_eq_Z t m n a₀ b₀ hg hU hb₀, chordF_eq_Z t m n a₁ b₁ hg hU hb₁]
  simp only [div_nonneg_iff, div_pos_iff_of_pos_right D₀, div_pos_iff_of_pos_right D₁]
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, b1⟩, c1⟩, a2⟩, b2⟩, c2⟩, a3⟩, b3⟩, c3⟩ := h
  refine ⟨Or.inl ⟨by exact_mod_cast a1, D₀.le⟩, Or.inl ⟨by exact_mod_cast b1, D₁.le⟩,
    by exact_mod_cast c1, Or.inl ⟨by exact_mod_cast a2, D₀.le⟩,
    Or.inl ⟨by exact_mod_cast b2, D₁.le⟩, by exact_mod_cast c2,
    Or.inl ⟨by exact_mod_cast a3, D₀.le⟩, Or.inl ⟨by exact_mod_cast b3, D₁.le⟩,
    by exact_mod_cast c3⟩

end APLemma
end Bump
end Trop
end PeriodicDifference
