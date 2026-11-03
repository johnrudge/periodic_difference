/-
# `PeriodicDifference/TapRead.lean` — taps reading `1` and `0`

Clause `i` of `def:bump` asks for a surviving tap reading `1` (`R1`) and one reading `0`
(`R0`): a tap `j ∈ S` whose position `i + j` is not deleted (`(i + j) mod k ∉ {0, σ}`) and
lies in, resp. outside, the anti-periodic set `P` coded by `Q`.  Every carrier proof produces
these reads in one of three ways, all collected here:

* directly, from an unwrapped (`r1lo`, `r0lo`) or a wrapped (`r1hi`, `r0hi`) position;
* from a read `1` of the reflected carrier at the reflected index (`r0_of_mirror`,
  `lem:nao-mirror`);
* through the linear form of a read (`inP_lin`) and of the deletions (`del_lin`);
* through linear descriptions `Sp`, `Qp` of the support and the carrier and explicit witness
  taps (`Lin.Wit1`, `Lin.Wit0`, `Lin.bumpSat_of_lin`), which reduce each clause to `omega`.
-/
import PeriodicDifference.SigmaBump

namespace PeriodicDifference
namespace Trop
namespace Bump

variable {k : ℕ} {S : Finset ℕ} {σ : ℕ} {Q : Finset ℕ}

/-! ## The two reads -/

/-- A surviving tap at `i` reads `1`. -/
def R1 (k : ℕ) (S : Finset ℕ) (σ : ℕ) (Q : Finset ℕ) (i : ℕ) : Prop :=
  ∃ j ∈ S, (i + j) % k ≠ 0 ∧ (i + j) % k ≠ σ ∧ inP k Q (i + j)

/-- A surviving tap at `i` reads `0`. -/
def R0 (k : ℕ) (S : Finset ℕ) (σ : ℕ) (Q : Finset ℕ) (i : ℕ) : Prop :=
  ∃ j ∈ S, (i + j) % k ≠ 0 ∧ (i + j) % k ≠ σ ∧ ¬ inP k Q (i + j)

lemma r1lo {i j : ℕ} (hj : j ∈ S) (h0 : 0 < i + j) (hlt : i + j < k) (hne : i + j ≠ σ)
    (hQ : i + j ∈ Q) : R1 k S σ Q i :=
  ⟨j, hj, by rw [Nat.mod_eq_of_lt hlt]; omega, by rw [Nat.mod_eq_of_lt hlt]; exact hne,
    by rw [inP_of_lt _ hlt]; exact hQ⟩

lemma r0lo {i j : ℕ} (hj : j ∈ S) (h0 : 0 < i + j) (hlt : i + j < k) (hne : i + j ≠ σ)
    (hQ : i + j ∉ Q) : R0 k S σ Q i :=
  ⟨j, hj, by rw [Nat.mod_eq_of_lt hlt]; omega, by rw [Nat.mod_eq_of_lt hlt]; exact hne,
    by rw [inP_of_lt _ hlt]; exact hQ⟩

/-- The wrapped position `i + j = k + (i + j − k)` is not deleted when `i + j − k ∉ {0, σ}`. -/
lemma del_hi {i j : ℕ} (hlt : k < i + j) (h2 : i + j < 2 * k) (hne : i + j - k ≠ σ) :
    (i + j) % k ≠ 0 ∧ (i + j) % k ≠ σ := by
  have hsum : i + j = 1 * k + (i + j - k) := by omega
  rw [hsum, mod_qk_add_of_lt (by omega)]; omega

lemma r1hi {i j : ℕ} (hj : j ∈ S) (hlt : k < i + j) (h2 : i + j < 2 * k)
    (hne : i + j - k ≠ σ) (hQ : i + j - k ∉ Q) : R1 k S σ Q i :=
  ⟨j, hj, (del_hi hlt h2 hne).1, (del_hi hlt h2 hne).2,
    (inP_wrap (by omega) hlt.le h2).mpr hQ⟩

lemma r0hi {i j : ℕ} (hj : j ∈ S) (hlt : k < i + j) (h2 : i + j < 2 * k)
    (hne : i + j - k ≠ σ) (hQ : i + j - k ∈ Q) : R0 k S σ Q i :=
  ⟨j, hj, (del_hi hlt h2 hne).1, (del_hi hlt h2 hne).2,
    fun h => (inP_wrap (by omega) hlt.le h2).mp h hQ⟩

/-- **The mirror** (`lem:nao-mirror`).  For palindromic `S` and `Q'` the reflection of `Q`
through `y ↦ k − y`, a read `1` at the index `k − i` for `(k − σ, Q')` gives, through the tap
`k − j`, a read `0` at the index `i` for `(σ, Q)`. -/
lemma r0_of_mirror (hS : ∀ j ∈ S, 0 < j ∧ j < k) (hpal : ∀ j ∈ S, k - j ∈ S) (hσ : σ < k)
    {Q' : Finset ℕ} (hQ : ∀ y, 0 < y → y < k → (y ∈ Q' ↔ k - y ∈ Q)) {i : ℕ} (hi0 : 0 < i)
    (hik : i < k) (h : R1 k S (k - σ) Q' (k - i)) : R0 k S σ Q i := by
  obtain ⟨j, hj, hz, hs, hP⟩ := h
  have hjk := hS j hj
  have hk : 0 < k := by omega
  refine ⟨k - j, hpal j hj, ?_⟩
  rcases Nat.lt_or_ge (k - i + j) k with hlt | hge
  · -- `(k − i, j)` unwrapped, so `(i, k − j)` wrapped
    rw [Nat.mod_eq_of_lt hlt] at hz hs
    rw [inP_of_lt _ hlt, hQ _ (by omega) hlt, show k - (k - i + j) = i - j by omega] at hP
    have hsum : i + (k - j) = 1 * k + (i - j) := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hsum, mod_qk_add_of_lt (by omega)]; omega
    · rw [hsum, mod_qk_add_of_lt (by omega)]; omega
    · rw [hsum, inP_qk_add_of_lt hk _ 1 (by omega), wrap_iff, not_not]; exact hP
  · -- `(k − i, j)` wrapped, so `(i, k − j)` unwrapped
    have hne : k - i + j ≠ k := fun h => hz (by rw [h, Nat.mod_self])
    have hsum : k - i + j = 1 * k + (j - i) := by omega
    rw [hsum, mod_qk_add_of_lt (by omega)] at hz hs
    rw [hsum, inP_qk_add_of_lt hk _ 1 (by omega), wrap_iff, hQ _ (by omega) (by omega),
      show k - (j - i) = i + (k - j) by omega] at hP
    have hlt' : i + (k - j) < k := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.mod_eq_of_lt hlt']; omega
    · rw [Nat.mod_eq_of_lt hlt']; omega
    · rw [inP_of_lt _ hlt']; exact hP

/-! ## Linear forms -/

/-- A read of `n < 2k`, as a linear predicate in the position. -/
lemma inP_lin (hk : 0 < k) {n : ℕ} (hn : n < 2 * k) :
    inP k Q n ↔ (n < k ∧ n ∈ Q) ∨ (k ≤ n ∧ n - k ∉ Q) := by
  rcases Nat.lt_or_ge n k with h | h
  · rw [inP_of_lt Q h]; constructor
    · intro hh; exact Or.inl ⟨h, hh⟩
    · rintro (⟨-, hh⟩ | ⟨hh, -⟩); exact hh; omega
  · rw [inP_wrap hk h hn]; constructor
    · intro hh; exact Or.inr ⟨h, hh⟩
    · rintro (⟨hh, -⟩ | ⟨-, hh⟩); omega; exact hh

/-- The deletions of clause `i`, as linear conditions on `i + j < 2k`. -/
lemma del_lin {i j : ℕ} (h0 : 0 < i + j) (h2 : i + j < 2 * k) (hne : i + j ≠ k)
    (h3 : i + j ≠ σ) (h4 : i + j ≠ k + σ) : (i + j) % k ≠ 0 ∧ (i + j) % k ≠ σ := by
  rcases Nat.lt_or_ge (i + j) k with h | h
  · rw [Nat.mod_eq_of_lt h]; constructor <;> omega
  · have e : (i + j) % k = i + j - k := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [e]; constructor <;> omega

/-! ## Linear clauses with witness taps -/

namespace Lin

variable {Sp Qp : ℕ → Prop}

/-- The read `[n ∈ P]` at a position `n < 2k`, through the linear description of `Q`. -/
def Rd (Qp : ℕ → Prop) (k n : ℕ) : Prop := (n < k ∧ Qp n) ∨ (k ≤ n ∧ ¬ Qp (n - k))

/-- Tap `t` present, not deleted, reading `1` at index `i`. -/
def Wit1 (Sp Qp : ℕ → Prop) (k σ i t : ℕ) : Prop :=
  Sp t ∧ i + t ≠ k ∧ i + t ≠ σ ∧ i + t ≠ k + σ ∧ Rd Qp k (i + t)

/-- Tap `t` present, not deleted, reading `0` at index `i`. -/
def Wit0 (Sp Qp : ℕ → Prop) (k σ i t : ℕ) : Prop :=
  Sp t ∧ i + t ≠ k ∧ i + t ≠ σ ∧ i + t ≠ k + σ ∧ ¬ Rd Qp k (i + t)

lemma inP_rd (hk : 0 < k) (hQ : ∀ y, y < k → (y ∈ Q ↔ Qp y)) {n : ℕ} (hn : n < 2 * k) :
    inP k Q n ↔ Rd Qp k n := by
  rw [inP_lin hk hn, Rd]
  rcases Nat.lt_or_ge n k with h | h
  · rw [hQ n h]; constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, -⟩); exact Or.inl ⟨h1, h2⟩; omega
    · rintro (⟨h1, h2⟩ | ⟨h1, -⟩); exact Or.inl ⟨h1, h2⟩; omega
  · rw [hQ (n - k) (by omega)]; constructor
    · rintro (⟨h1, -⟩ | ⟨h1, h2⟩); omega; exact Or.inr ⟨h1, h2⟩
    · rintro (⟨h1, -⟩ | ⟨h1, h2⟩); omega; exact Or.inr ⟨h1, h2⟩

lemma of_wit1 (hS : ∀ y, y ∈ S ↔ Sp y) (hSb : ∀ y, Sp y → 0 < y ∧ y < k)
    (hQ : ∀ y, y < k → (y ∈ Q ↔ Qp y)) {i t : ℕ} (hi0 : 0 < i) (hik : i < k)
    (h : Wit1 Sp Qp k σ i t) : R1 k S σ Q i := by
  obtain ⟨hSt, h1, h2, h3, hr⟩ := h
  have ht := hSb t hSt
  have hd := del_lin (by omega) (by omega) h1 h2 h3
  exact ⟨t, (hS t).mpr hSt, hd.1, hd.2, (inP_rd (by omega) hQ (by omega)).mpr hr⟩

lemma of_wit0 (hS : ∀ y, y ∈ S ↔ Sp y) (hSb : ∀ y, Sp y → 0 < y ∧ y < k)
    (hQ : ∀ y, y < k → (y ∈ Q ↔ Qp y)) {i t : ℕ} (hi0 : 0 < i) (hik : i < k)
    (h : Wit0 Sp Qp k σ i t) : R0 k S σ Q i := by
  obtain ⟨hSt, h1, h2, h3, hr⟩ := h
  have ht := hSb t hSt
  have hd := del_lin (by omega) (by omega) h1 h2 h3
  exact ⟨t, (hS t).mpr hSt, hd.1, hd.2, by rw [inP_rd (by omega) hQ (by omega)]; exact hr⟩

/-- **The linear-clause criterion.**  Linear descriptions of `S` and `Q`, the pin
condition (B1) in linear form, and explicit witnesses at every index give `BumpSat`. -/
theorem bumpSat_of_lin (hS : ∀ y, y ∈ S ↔ Sp y) (hSb : ∀ y, Sp y → 0 < y ∧ y < k)
    (hQ : ∀ y, y < k → (y ∈ Q ↔ Qp y)) (hQb : ∀ y, y ∈ Q → y < k) (hσS : Sp σ) (hσQ : Qp σ)
    (hB1 : ∀ y, y < k → Qp y → y = σ ∨ (0 < y ∧ ¬ Sp y))
    (hw : ∀ i, 0 < i → i < k → (∃ t, Wit1 Sp Qp k σ i t) ∧ (∃ t, Wit0 Sp Qp k σ i t)) :
    BumpSat k S σ Q where
  S_sub := fun j hj => hSb j ((hS j).mp hj)
  σ_mem := (hS σ).mpr hσS
  B1 := by
    have hσk := hSb σ hσS
    ext y
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hyQ, hy⟩
      have hyk := hQb y hyQ
      rcases hB1 y hyk ((hQ y hyk).mp hyQ) with h | ⟨h1, h2⟩
      · exact h
      · exfalso; rcases hy with rfl | hy; omega; exact h2 ((hS y).mp hy)
    · intro hy; rw [hy]; exact ⟨(hQ σ hσk.2).mpr hσQ, Or.inr ((hS σ).mpr hσS)⟩
  B2 := fun i hi0 hik => by
    obtain ⟨⟨t1, h1⟩, ⟨t0, h0⟩⟩ := hw i hi0 hik
    exact ⟨of_wit1 hS hSb hQ hi0 hik h1, of_wit0 hS hSb hQ hi0 hik h0⟩

end Lin

end Bump
end Trop
end PeriodicDifference
