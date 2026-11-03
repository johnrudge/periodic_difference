/-
# `PeriodicDifference/APLemmaBasic.lean` — `thm:lemmaA`, stage 1: the predicate and the target region

`APLemma k a x` is the conclusion of the paper's `thm:lemmaA` (three-term progressions),
in the exact form shared with the other W1 files.  `Good k A E` is the same condition on an
integer pair `(A, E) = (a, x − a)` read modulo `2k`.

* `good_iff_of_modEq` — `Good` depends only on `(A, E)` modulo `2k`;
* `good_of_unit_mul` — unit invariance (`B1_argument.txt`, Step D);
* `good_of_inR` — Prop 1 of `tools/e3/lattice/proof.md` in the direction used, (1.1):
  if `(dA mod 2k, dE mod 2k)` lies in the open region `R = T1 ∪ T2 ∪ T3 ∪ T4` for a unit `d`,
  then `Good k A E`;
* `apLemma_of_good` — `Good k a (x − a)` gives `APLemma k a x`.
-/
import Mathlib

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

set_option linter.dupNamespace false

/-- The conclusion of `thm:lemmaA` (shared definition). -/
def APLemma (k a x : ℕ) : Prop :=
  ∃ d, Nat.Coprime d (2*k) ∧
    ((d*((2*a + 2*k - x) % (2*k))) % (2*k) < k ↔ d*a % (2*k) < k) ∧
    (d*x % (2*k) < k ↔ ¬ d*a % (2*k) < k)

/-- Integer form: a unit `d` (the paper's `ν`) with `H_d(A − E) = H_d(A) ≠ H_d(A + E)`. -/
def Good (k : ℕ) (A E : ℤ) : Prop :=
  ∃ d : ℤ, Int.gcd d (2*k) = 1 ∧
    ((d*(A-E)) % (2*k) < k ↔ (d*A) % (2*k) < k) ∧
    ((d*(A+E)) % (2*k) < k ↔ ¬ (d*A) % (2*k) < k)

theorem good_of_modEq {k : ℕ} {A E A' E' : ℤ} (hA : A ≡ A' [ZMOD 2*k])
    (hE : E ≡ E' [ZMOD 2*k]) (h : Good k A' E') : Good k A E := by
  obtain ⟨d, hd, h1, h2⟩ := h
  refine ⟨d, hd, ?_, ?_⟩
  · have e1 : d*(A-E) ≡ d*(A'-E') [ZMOD 2*k] := (Int.ModEq.sub hA hE).mul_left _
    have e2 : d*A ≡ d*A' [ZMOD 2*k] := hA.mul_left _
    rw [e1, e2]; exact h1
  · have e1 : d*(A+E) ≡ d*(A'+E') [ZMOD 2*k] := (Int.ModEq.add hA hE).mul_left _
    have e2 : d*A ≡ d*A' [ZMOD 2*k] := hA.mul_left _
    rw [e1, e2]; exact h2

/-- Unit invariance: if `d` works for `(εA, εE)` then `dε` works for `(A, E)`. -/
theorem good_of_unit_mul {k : ℕ} {A E ε : ℤ} (hε : Int.gcd ε (2*k) = 1)
    (h : Good k (ε*A) (ε*E)) : Good k A E := by
  obtain ⟨d, hd, h1, h2⟩ := h
  refine ⟨d*ε, ?_, ?_, ?_⟩
  · rw [← Int.isCoprime_iff_gcd_eq_one] at *
    exact IsCoprime.mul_left hd hε
  · have e1 : d*ε*(A-E) = d*(ε*A-ε*E) := by ring
    have e2 : d*ε*A = d*(ε*A) := by ring
    rw [e1, e2]; exact h1
  · have e1 : d*ε*(A+E) = d*(ε*A+ε*E) := by ring
    have e2 : d*ε*A = d*(ε*A) := by ring
    rw [e1, e2]; exact h2

/-- The open region `R` of proof.md §1 at `(A, E) ∈ [0, 2k)²`, doubled to stay integral. -/
def InR (k : ℤ) (A E : ℤ) : Prop :=
  (k < 2*A ∧ 2*A < 2*k ∧ |2*E - k| < 2*A - k) ∨
  (3*k < 2*A ∧ 2*A < 4*k ∧ |2*E - k| < 2*A - 3*k) ∨
  (0 < 2*A ∧ 2*A < k ∧ |2*E - 3*k| < k - 2*A) ∨
  (2*k < 2*A ∧ 2*A < 3*k ∧ |2*E - 3*k| < 3*k - 2*A)

/-- Prop 1, direction (1.1): a unit `d` putting `(dA, dE) mod 2k` in `R` gives `Good`. -/
theorem good_of_inR {k : ℕ} {A E d : ℤ} (hd : Int.gcd d (2*k) = 1)
    (hR : InR k ((d*A) % (2*k)) ((d*E) % (2*k))) : Good k A E := by
  refine ⟨d, hd, ?_⟩
  set r := (d*A) % (2*k) with hr
  set s := (d*E) % (2*k) with hs
  have hk : (0:ℤ) < 2*k := by
    rcases hR with h | h | h | h <;> (obtain ⟨h1, h2, -⟩ := h; omega)
  have r0 : 0 ≤ r := Int.emod_nonneg _ hk.ne'
  have r1 : r < 2*k := Int.emod_lt_of_pos _ hk
  have s0 : 0 ≤ s := Int.emod_nonneg _ hk.ne'
  have s1 : s < 2*k := Int.emod_lt_of_pos _ hk
  have em : ∀ t : ℤ, -(2*k) ≤ t → t < 4*k → t % (2*k) =
      if t < 0 then t + 2*k else if t < 2*k then t else t - 2*k := by
    intro t h1 h2
    split_ifs with h3 h4
    · rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
    · exact Int.emod_eq_of_lt (by omega) h4
    · rw [← Int.sub_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
  have hsub : (d*(A-E)) % (2*k) = (r - s) % (2*k) := by
    rw [mul_sub, Int.sub_emod]
  have hadd : (d*(A+E)) % (2*k) = (r + s) % (2*k) := by
    rw [mul_add, Int.add_emod]
  rw [hsub, hadd, em (r - s) (by omega) (by omega), em (r + s) (by omega) (by omega)]
  simp only [InR, abs_lt] at hR
  constructor <;> split_ifs <;> omega

/-- `Good k a (x − a)` gives the shared `APLemma k a x` (for `x ≤ 2a + 2k`). -/
theorem apLemma_of_good {k a x : ℕ} (hx : x ≤ 2*a + 2*k) (hk : 0 < k)
    (h : Good k a ((x:ℤ) - a)) : APLemma k a x := by
  obtain ⟨d, hd, h1, h2⟩ := h
  have hN : (0:ℤ) < 2*k := by positivity
  set d' : ℕ := (d % (2*k)).toNat with hd'
  have hdd : (d' : ℤ) = d % (2*k) := Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne')
  have key : ∀ y : ℤ, ((d' : ℤ) * y) % (2*k) = (d*y) % (2*k) := by
    intro y; rw [hdd, Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
  have cst : ∀ y : ℕ, (d' * y % (2*k) < k ↔ (d*(y:ℤ)) % (2*k) < k) := by
    intro y
    rw [← key]
    constructor <;> intro h <;> exact_mod_cast h
  refine ⟨d', ?_, ?_, ?_⟩
  · have : Int.gcd (d' : ℤ) (2*k) = 1 := by rw [hdd, Int.gcd_emod]; exact hd
    have h2k : ((2*k : ℕ) : ℤ) = 2*(k:ℤ) := by push_cast; ring
    rw [← h2k, Int.gcd_natCast_natCast] at this
    exact this
  · rw [cst a]
    have e : ((d' * ((2*a + 2*k - x) % (2*k)) % (2*k) : ℕ) : ℤ)
        = (d*((a:ℤ) - ((x:ℤ) - a))) % (2*k) := by
      push_cast [Nat.cast_sub hx]
      rw [← key, Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
      have : (2*(a:ℤ) + 2*k - x) = (a - (x - a)) + 2*k := by ring
      rw [this, mul_add, Int.add_mul_emod_self_right]
    rw [← h1, ← e]; constructor <;> intro h <;> exact_mod_cast h
  · rw [cst a, cst x, ← h2]
    have : (a:ℤ) + ((x:ℤ) - a) = x := by ring
    rw [this]

end APLemma
end Bump
end Trop
end PeriodicDifference
