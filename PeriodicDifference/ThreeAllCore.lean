/-
# `PeriodicDifference/ThreeAllCore.lean` — the arithmetic core of `thm:allodd-threeall`

`k = 2h`, `S = {a, h, k − a}`.  At an index `i` of phase `c = d·i mod 2k`, the tap `j`
reads the position `p = i + j`: `1` at a wrapped pin (`p = k + h`, `p = 2k − a`), `0` at
an unwrapped pin (`p = h`, `p = k − a`), and `R k c (d·j)` at a free position (`V`).
The tap is deleted when `p ∈ {k, a, k + a}` (`T` says it is not).  With the phases
`da = 3h + δ`, `dh = h`, `d(k − a) = 3h − δ`, and the phase of `i` known at the seven
special indices, `core` is the case analysis of the paper's proof.
-/
import PeriodicDifference.HalfArc

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace ThreeAll

open HalfArc

/-- The tap reading position `p` is not deleted. -/
def T (h a p : ℕ) : Prop := p ≠ 2 * h ∧ p ≠ a ∧ p ≠ 2 * h + a

/-- The read of position `p` (below `4h`) whose free read is `r`. -/
def V (h a p : ℕ) (r : Prop) : Prop :=
  (p = 3 * h ∨ p = 4 * h - a) ∨ (p ≠ h ∧ p ≠ 2 * h - a ∧ p ≠ 3 * h ∧ p ≠ 4 * h - a ∧ r)

/-- The two clauses at an index, in linear form. -/
def Cl (h a δ i c : ℕ) : Prop :=
  ((T h a (i + a) ∧ V h a (i + a) (R (2 * h) c (3 * h + δ))) ∨
    (T h a (i + h) ∧ V h a (i + h) (R (2 * h) c h)) ∨
    (T h a (i + (2 * h - a)) ∧ V h a (i + (2 * h - a)) (R (2 * h) c (3 * h - δ)))) ∧
  ((T h a (i + a) ∧ ¬ V h a (i + a) (R (2 * h) c (3 * h + δ))) ∨
    (T h a (i + h) ∧ ¬ V h a (i + h) (R (2 * h) c h)) ∨
    (T h a (i + (2 * h - a)) ∧ ¬ V h a (i + (2 * h - a)) (R (2 * h) c (3 * h - δ))))

section
variable {h a δ i c : ℕ}

lemma V_free {h a p : ℕ} {r : Prop} (h1 : p ≠ h) (h2 : p ≠ 2 * h - a) (h3 : p ≠ 3 * h)
    (h4 : p ≠ 4 * h - a) : V h a p r ↔ r := by
  unfold V
  constructor
  · rintro (h | ⟨-, -, -, -, h⟩)
    · omega
    · exact h
  · intro hr; exact Or.inr ⟨h1, h2, h3, h4, hr⟩

/-- Three phases with gaps `2h − δ, 2δ, 2h − δ`: no half contains all three. -/
lemma gen_R (hβ3 : 3 * δ < h) (hδ : δ = 2 ∨ δ = 4) (hc : c < 4 * h) :
    (R (2 * h) c (3 * h + δ) ∨ R (2 * h) c h ∨ R (2 * h) c (3 * h - δ)) ∧
    (¬ R (2 * h) c (3 * h + δ) ∨ ¬ R (2 * h) c h ∨ ¬ R (2 * h) c (3 * h - δ)) := by
  unfold R
  rcases hδ with rfl | rfl <;> constructor <;> omega

/-- The generic index: every tap reads a free position. -/
lemma core_generic (hβ3 : 3 * δ < h) (ha3 : 3 ≤ a) (hah : a < h)
    (hδ : δ = 2 ∨ δ = 4) (hi0 : 0 < i) (hik : i < 2 * h) (hc : c < 4 * h)
    (n1 : i ≠ a) (n2 : i ≠ h) (n3 : i ≠ 2 * h - a) (n4 : i ≠ a + h) (n5 : i ≠ 2 * a)
    (n6 : i ≠ h - a) (n7 : i ≠ 2 * h - 2 * a) : Cl h a δ i c := by
  have t1 : T h a (i + a) := by unfold T; omega
  have t2 : T h a (i + h) := by unfold T; omega
  have t3 : T h a (i + (2 * h - a)) := by unfold T; omega
  unfold Cl
  rw [V_free (p := i + a) (by omega) (by omega) (by omega) (by omega),
    V_free (p := i + h) (by omega) (by omega) (by omega) (by omega),
    V_free (p := i + (2 * h - a)) (by omega) (by omega) (by omega) (by omega)]
  obtain ⟨g1, g2⟩ := gen_R hβ3 hδ hc
  refine ⟨?_, ?_⟩
  · rcases g1 with g | g | g
    · exact Or.inl ⟨t1, g⟩
    · exact Or.inr (Or.inl ⟨t2, g⟩)
    · exact Or.inr (Or.inr ⟨t3, g⟩)
  · rcases g2 with g | g | g
    · exact Or.inl ⟨t1, g⟩
    · exact Or.inr (Or.inl ⟨t2, g⟩)
    · exact Or.inr (Or.inr ⟨t3, g⟩)

/-- `i = a`, phase `3h + δ`. -/
lemma core_a (hβ3 : 3 * δ < h) (ha3 : 3 ≤ a) (hah : a < h) (hao : a % 2 = 1) (hho : h % 2 = 1)
    (hδ : δ = 2 ∨ δ = 4) : Cl h a δ a (3 * h + δ) := by
  unfold Cl T V R
  rcases hδ with rfl | rfl <;> constructor <;> omega

lemma core_h (hβ3 : 3 * δ < h) (ha3 : 3 ≤ a) (hah : a < h) (hao : a % 2 = 1) (hho : h % 2 = 1)
    (hδ : δ = 2 ∨ δ = 4) : Cl h a δ (h) (h) := by
  unfold Cl T V R
  rcases hδ with rfl | rfl <;> constructor <;> omega

lemma core_ka (hβ3 : 3 * δ < h) (ha3 : 3 ≤ a) (hah : a < h) (hao : a % 2 = 1) (hho : h % 2 = 1)
    (hδ : δ = 2 ∨ δ = 4) : Cl h a δ (2 * h - a) (3 * h - δ) := by
  unfold Cl T V R
  rcases hδ with rfl | rfl <;> constructor <;> omega

lemma core_ah (hβ3 : 3 * δ < h) (ha3 : 3 ≤ a) (hah : a < h) (hao : a % 2 = 1) (hho : h % 2 = 1)
    (hδ : δ = 2 ∨ δ = 4) : Cl h a δ (a + h) (δ) := by
  unfold Cl T V R
  rcases hδ with rfl | rfl <;> constructor <;> omega

lemma core_2a (hβ3 : 3 * δ < h) (ha3 : 3 ≤ a) (hah : a < h) (hao : a % 2 = 1) (hho : h % 2 = 1)
    (h3a : h ≠ 3 * a) (hδ : δ = 2 ∨ δ = 4) : Cl h a δ (2 * a) (2 * h + 2 * δ) := by
  unfold Cl T V R
  rcases hδ with rfl | rfl <;> constructor <;> omega

lemma core_e (hβ3 : 3 * δ < h) (ha3 : 3 ≤ a) (hah : a < h) (hao : a % 2 = 1) (hho : h % 2 = 1)
    (h3a : h ≠ 3 * a) (hδ : δ = 2 ∨ δ = 4) : Cl h a δ (h - a) (2 * h - δ) := by
  unfold Cl T V R
  rcases hδ with rfl | rfl <;> constructor <;> omega

lemma core_k2a (hβ3 : 3 * δ < h) (ha3 : 3 ≤ a) (hah : a < h) (hao : a % 2 = 1) (hho : h % 2 = 1)
    (hδ : δ = 2 ∨ δ = 4) : Cl h a δ (2 * h - 2 * a) (4 * h - 2 * δ) := by
  unfold Cl T V R
  rcases hδ with rfl | rfl <;> constructor <;> omega

/-- **The case analysis of `thm:allodd-threeall`.** -/
lemma core (hβ3 : 3 * δ < h) (ha3 : 3 ≤ a) (hah : a < h) (hao : a % 2 = 1) (hho : h % 2 = 1)
    (h3a : h ≠ 3 * a) (hδ : δ = 2 ∨ δ = 4) (hi0 : 0 < i) (hik : i < 2 * h) (hc : c < 4 * h)
    (c1 : i = a → c = 3 * h + δ) (c2 : i = h → c = h) (c3 : i = 2 * h - a → c = 3 * h - δ)
    (c4 : i = a + h → c = δ) (c5 : i = 2 * a → c = 2 * h + 2 * δ)
    (c6 : i = h - a → c = 2 * h - δ) (c7 : i = 2 * h - 2 * a → c = 4 * h - 2 * δ) :
    Cl h a δ i c := by
  by_cases n1 : i = a
  · rw [c1 n1, n1]; exact core_a hβ3 ha3 hah hao hho hδ
  by_cases n2 : i = h
  · rw [c2 n2, n2]; exact core_h hβ3 ha3 hah hao hho hδ
  by_cases n3 : i = 2 * h - a
  · rw [c3 n3, n3]; exact core_ka hβ3 ha3 hah hao hho hδ
  by_cases n4 : i = a + h
  · rw [c4 n4, n4]; exact core_ah hβ3 ha3 hah hao hho hδ
  by_cases n5 : i = 2 * a
  · rw [c5 n5, n5]; exact core_2a hβ3 ha3 hah hao hho h3a hδ
  by_cases n6 : i = h - a
  · rw [c6 n6, n6]; exact core_e hβ3 ha3 hah hao hho h3a hδ
  by_cases n7 : i = 2 * h - 2 * a
  · rw [c7 n7, n7]; exact core_k2a hβ3 ha3 hah hao hho hδ
  exact core_generic hβ3 ha3 hah hδ hi0 hik hc n1 n2 n3 n4 n5 n6 n7

end

end ThreeAll
end Bump
end Trop
end PeriodicDifference
