/-
# `PeriodicDifference/PerSupportDefs.lean` — palindromic and primitive supports

The light definitions about supports, with no carrier theory:

* `PerSupport.Pal k S` (palindromic: `x ∈ S → k − x ∈ S`) and `PerSupport.Prim k S` (primitive:
  `gcd(S ∪ {k}) = 1`), both decidable;
* `ShadowGen.Pal k S a`: a palindromic support inside `(0, k)` with minimum `a`, and
  `Shadow.AllOddPal k S a`, the same at even `k` with every element odd;
* `Shadow.GapLE k S a g`: every gap between consecutive elements of `S` is at most `g`.
-/
import Mathlib.Tactic

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace PerSupport

/-- Palindromic: `x ∈ S → k − x ∈ S`. -/
def Pal (k : ℕ) (S : Finset ℕ) : Prop := ∀ x ∈ S, k - x ∈ S
/-- Primitive: `gcd(S ∪ {k}) = 1`. -/
def Prim (k : ℕ) (S : Finset ℕ) : Prop := Nat.gcd (S.gcd id) k = 1

instance (k : ℕ) (S : Finset ℕ) : Decidable (Pal k S) := by unfold Pal; infer_instance
instance (k : ℕ) (S : Finset ℕ) : Decidable (Prim k S) := by unfold Prim; infer_instance

/-- A palindromic support inside `[1, k−1]` is its lower half together with the mirror of that half. -/
lemma pal_eq {k : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 (k - 1)) (hpal : Pal k S) :
    S = S.filter (· ≤ k / 2) ∪ (S.filter (· ≤ k / 2)).image (fun x => k - x) := by
  ext y
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  constructor
  · intro hy
    by_cases h : y ≤ k / 2
    · exact Or.inl ⟨hy, h⟩
    · have hb := Finset.mem_Icc.mp (hS hy)
      exact Or.inr ⟨k - y, ⟨hpal y hy, by omega⟩, by omega⟩
  · rintro (⟨hy, -⟩ | ⟨x, ⟨hx, -⟩, rfl⟩)
    · exact hy
    · exact hpal x hx

end PerSupport

namespace ShadowGen

/-- A palindromic support at order `k`, with minimum `a` (no parity assumption). -/
structure Pal (k : ℕ) (S : Finset ℕ) (a : ℕ) : Prop where
  mem : ∀ j ∈ S, 0 < j ∧ j < k
  pal : ∀ j ∈ S, k - j ∈ S
  a_mem : a ∈ S
  a_min : ∀ j ∈ S, a ≤ j

variable {k : ℕ} {S : Finset ℕ} {a : ℕ}

lemma Pal.a_pos (h : Pal k S a) : 0 < a := (h.mem a h.a_mem).1
lemma Pal.a_lt (h : Pal k S a) : a < k := (h.mem a h.a_mem).2
lemma Pal.k_pos (h : Pal k S a) : 0 < k := by have := h.a_lt; omega
lemma Pal.kma_mem (h : Pal k S a) : k - a ∈ S := h.pal a h.a_mem
/-- `max S = k − a`. -/
lemma Pal.le_kma (h : Pal k S a) {j : ℕ} (hj : j ∈ S) : j ≤ k - a := by
  have := h.a_min (k - j) (h.pal j hj); have := (h.mem j hj).2; omega
/-- If some element of `S` is not the middle `k/2`, then `2a < k`. -/
lemma Pal.two_a_lt (h : Pal k S a) {j : ℕ} (hj : j ∈ S) (hjk : 2 * j ≠ k) :
    2 * a < k := by
  have h1 := h.le_kma hj; have h2 := h.a_min j hj; have := (h.mem j hj).1; omega

end ShadowGen

namespace Shadow

/-- An all-odd palindromic support at even order `k`, with minimum `a`. -/
structure AllOddPal (k : ℕ) (S : Finset ℕ) (a : ℕ) : Prop extends ShadowGen.Pal k S a where
  even_k : k % 2 = 0
  odd : ∀ j ∈ S, j % 2 = 1

lemma AllOddPal.a_odd {k : ℕ} {S : Finset ℕ} {a : ℕ} (h : AllOddPal k S a) : a % 2 = 1 :=
  h.odd a h.a_mem

/-- `g` bounds every gap between consecutive elements of `S`: each element below
`max S = k − a` has a successor within `g`. -/
def GapLE (k : ℕ) (S : Finset ℕ) (a g : ℕ) : Prop :=
  ∀ x ∈ S, x < k - a → ∃ y ∈ S, x < y ∧ y ≤ x + g

end Shadow

end Bump
end Trop
end PeriodicDifference
