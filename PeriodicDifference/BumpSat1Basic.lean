/-
# `PeriodicDifference/BumpSat1Basic.lean` — witness criterion for `BumpSat` over an arbitrary support

Infrastructure for the carriers of supports containing `1` (`prop:allodd-one`, used by
`PeriodicDifference/AllOddOne.lean`, and the archived cone of an earlier version of the paper).  These
carriers have an explicit carrier `Q` but an **arbitrary** palindromic support `S`, so the
support is not described linearly: the taps are elements of `S` and only `Q` is described
by a predicate `Qp`, the case `Sp = (· ∈ S)` of `Lin.bumpSat_of_lin` (`PeriodicDifference/TapRead.lean`):

* `Wit1 S Qp k σ i t` / `Wit0 S Qp k σ i t` — tap `t ∈ S`, not deleted at index `i`
  (`i + t ∉ {k, σ, k + σ}`), reading `1` / `0`;
* `bumpSat_of_wit` — (B1) in linear form plus a pair of witnesses at every index gives
  `BumpSat k S σ Q`.

`Pal k S` is palindromy `j ∈ S → k − j ∈ S` on a support inside `(0, k)`.
-/
import PeriodicDifference.TapRead
import PeriodicDifference.PerSupportDefs

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace BumpSat1

open Lin (Rd)

variable {k : ℕ} {S Q : Finset ℕ} {σ : ℕ} {Qp : ℕ → Prop} {i : ℕ}

/-- Tap `t ∈ S` present, not deleted, reading `1` at index `i`. -/
def Wit1 (S : Finset ℕ) (Qp : ℕ → Prop) (k σ i t : ℕ) : Prop := Lin.Wit1 (· ∈ S) Qp k σ i t

/-- Tap `t ∈ S` present, not deleted, reading `0` at index `i`. -/
def Wit0 (S : Finset ℕ) (Qp : ℕ → Prop) (k σ i t : ℕ) : Prop := Lin.Wit0 (· ∈ S) Qp k σ i t

/-- **The witness criterion over an arbitrary support.**  A linear description of `Q`, the
pin condition (B1) in linear form, and a `1`-reading and a `0`-reading tap of `S` at every
index give `BumpSat k S σ Q`. -/
theorem bumpSat_of_wit (hSb : ∀ y ∈ S, 0 < y ∧ y < k)
    (hQ : ∀ y, y < k → (y ∈ Q ↔ Qp y)) (hQb : ∀ y, y ∈ Q → y < k) (hσS : σ ∈ S) (hσQ : Qp σ)
    (hB1 : ∀ y, y < k → Qp y → y = σ ∨ (0 < y ∧ y ∉ S))
    (hw : ∀ i, 0 < i → i < k → (∃ t, Wit1 S Qp k σ i t) ∧ (∃ t, Wit0 S Qp k σ i t)) :
    BumpSat k S σ Q :=
  Lin.bumpSat_of_lin (fun _ => Iff.rfl) hSb hQ hQb hσS hσQ hB1 hw

/-- Palindromy of a support inside `(0, k)`. -/
def Pal (k : ℕ) (S : Finset ℕ) : Prop := (∀ j ∈ S, 0 < j ∧ j < k) ∧ PerSupport.Pal k S

lemma Pal.bounds (h : Pal k S) : ∀ j ∈ S, 0 < j ∧ j < k := h.1

lemma Pal.mirror (h : Pal k S) {j : ℕ} (hj : j ∈ S) : k - j ∈ S := h.2 j hj

/-- The linear part of `Wit1`: tap `t` not deleted at `i` and reading `1`. -/
def L1 (Qp : ℕ → Prop) (k σ i t : ℕ) : Prop :=
  i + t ≠ k ∧ i + t ≠ σ ∧ i + t ≠ k + σ ∧ Rd Qp k (i + t)

/-- The linear part of `Wit0`: tap `t` not deleted at `i` and reading `0`. -/
def L0 (Qp : ℕ → Prop) (k σ i t : ℕ) : Prop :=
  i + t ≠ k ∧ i + t ≠ σ ∧ i + t ≠ k + σ ∧ ¬ Rd Qp k (i + t)

lemma w1 {t : ℕ} (ht : t ∈ S) (h : L1 Qp k σ i t) : ∃ t, Wit1 S Qp k σ i t := ⟨t, ht, h⟩

lemma w0 {t : ℕ} (ht : t ∈ S) (h : L0 Qp k σ i t) : ∃ t, Wit0 S Qp k σ i t := ⟨t, ht, h⟩

end BumpSat1
end Bump
end Trop
end PeriodicDifference
