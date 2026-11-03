/-
# `PeriodicDifference/ParityCarrier.lean` — the parity carrier

The paper's *parity carriers* are `Q = {σ} ∪ {free y : y ≡ c (mod 2)}` (`parQ`).  They
satisfy the pin condition (B1) automatically, so a parity carrier is a σ-bump carrier as soon
as every clause holds (`bumpSat_parQ`); the clauses are checked in `PeriodicDifference/EvenMin*.lean` and
`PeriodicDifference/NotAllOdd*.lean`.
-/
import PeriodicDifference.TapRead

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace Parity

variable {k : ℕ} {S : Finset ℕ} {σ c : ℕ}

/-- The parity carrier of class `c`: `σ` and the free positions `≡ c (mod 2)`. -/
def parQ (k : ℕ) (S : Finset ℕ) (σ c : ℕ) : Finset ℕ :=
  insert σ ((Finset.range k).filter (fun y => 0 < y ∧ y ∉ S ∧ y % 2 = c))

lemma mem_parQ {y : ℕ} : y ∈ parQ k S σ c ↔ y = σ ∨ (0 < y ∧ y < k ∧ y ∉ S ∧ y % 2 = c) := by
  simp only [parQ, Finset.mem_insert, Finset.mem_filter, Finset.mem_range]; tauto

/-- The clause of `def:bump` at index `i` for the carrier `Q`. -/
def Clause (k : ℕ) (S : Finset ℕ) (σ : ℕ) (Q : Finset ℕ) (i : ℕ) : Prop :=
  R1 k S σ Q i ∧ R0 k S σ Q i

/-- A parity carrier satisfies (B1); so it is a σ-bump carrier as soon as every clause holds. -/
theorem bumpSat_parQ (hS : ∀ j ∈ S, 0 < j ∧ j < k) (hσ : σ ∈ S)
    (hcl : ∀ i, 0 < i → i < k → Clause k S σ (parQ k S σ c) i) :
    BumpSat k S σ (parQ k S σ c) where
  S_sub := hS
  σ_mem := hσ
  B1 := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, mem_parQ]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact h1
      · exfalso; rcases h2 with rfl | h2; omega; exact h1.2.2.1 h2
    · rintro rfl; exact ⟨Or.inl rfl, Or.inr hσ⟩
  B2 := hcl

end Parity
end Bump
end Trop
end PeriodicDifference
