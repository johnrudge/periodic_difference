/-
# `PeriodicDifference/OddRowsHandCore.lean` — the arc argument of `thm:odd-rowcarrier`, abstractly

This is the combinatorial heart of the hand proof of `thm:odd-rowcarrier`
(`paper/sections/oddk.tex`).  After folding (`PeriodicDifference/OddRowsHandFold.lean`) the carrier
becomes a pattern `γ : ℤ → Prop` of period `k = 2c + 1`, and (B2) at an index with
half-residue `s ∈ [-c, c] ∖ {0}` becomes `(∗)`: the reads `γ(s + a)` and `¬γ(s − a)`,
`1 ≤ a ≤ r`, at non-excluded residues (excluded: `0` and `1`) are not all equal.

Here `γ` is arbitrary, subject only to the properties the paper uses: the values forced
by (F1) (`fplus`, `fminus`), property (i) (`refl`), `γ(r + 1) = 1` (`p2`) and (iii) on
`A₊ = [r+1, c]` (`p3`).

* `run_arc` / `run_arc'`: a run of `r ≥ 2` consecutive residues on which `γ` is constant
  (off the excluded pair) lies in `[-r, 1]` or `[0, r]` — the four boundary pairs
  `(r, r+1)`, `(c, c+1)`, `(-r-1, -r)`, `(-1, 2)` and (iii) on `A±`.
* `core_const`: if `(∗)` fails at `s ≠ 0`, the two lists of `s` meet only in `0`.

Within `[-c - r, c + r]` a residue is `≡ 0, 1 (mod k)` exactly when it is `0` or `1`, so the
excluded set is written as `x ≠ 0 ∧ x ≠ 1` throughout.
-/
import PeriodicDifference.OddRows

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace Rows
namespace Hand

/-- The properties of the folded pattern `γ` used by the arc argument. -/
structure Folded (c r : ℤ) (γ : ℤ → Prop) : Prop where
  hr : 2 ≤ r
  hrc : r + 1 ≤ c
  /-- `γ` has period `k = 2c + 1` -/
  per : ∀ u, γ (u + (2 * c + 1)) ↔ γ u
  /-- `γ(u) = 0` on `F₊ = [2, r]` -/
  fplus : ∀ u, 2 ≤ u → u ≤ r → ¬ γ u
  /-- `γ(u) = 1` on `F₋ = [-r, -1]` -/
  fminus : ∀ u, -r ≤ u → u ≤ -1 → γ u
  /-- fact (i): `γ(-u) = 1 - γ(u)` for `2 ≤ u ≤ c` -/
  refl : ∀ u, 2 ≤ u → u ≤ c → (γ (-u) ↔ ¬ γ u)
  /-- `γ(r + 1) = 1` -/
  p2 : γ (r + 1)
  /-- (iii): both values on two consecutive residues of `A₊` -/
  p3 : ∀ u, r + 1 ≤ u → u + 1 ≤ c → (γ (u + 1) ↔ ¬ γ u)

/-- The failure of `(∗)` at `s`: every non-excluded read of the run `s + [1, r]` is `w`, and
every non-excluded read of the run `s − [1, r]` is `¬w` (i.e. `γ = ¬w` there). -/
def Const (r : ℤ) (γ : ℤ → Prop) (s : ℤ) (w : Prop) : Prop :=
  ∀ a, 1 ≤ a → a ≤ r →
    ((s + a ≠ 0 ∧ s + a ≠ 1) → (γ (s + a) ↔ w)) ∧
    ((s - a ≠ 0 ∧ s - a ≠ 1) → (γ (s - a) ↔ ¬ w))

variable {c r : ℤ} {γ : ℤ → Prop}

namespace Folded

variable (hF : Folded c r γ)
include hF

/-- Periodicity, with the shifted point named. -/
lemma per' (u v : ℤ) (h : v = u + (2 * c + 1)) : γ v ↔ γ u := by rw [h]; exact hF.per u

/-- Fact (i), with the reflected point named. -/
lemma refl' (u v : ℤ) (h : v = -u) (h1 : 2 ≤ u) (h2 : u ≤ c) : γ v ↔ ¬ γ u := by
  rw [h]; exact hF.refl u h1 h2

/-- Fact (ii) at `c`: `γ` changes value between `c` and `c + 1 ≡ -c`. -/
lemma step_c : γ (c + 1) ↔ ¬ γ c := by
  have h1 := hF.per' (-c) (c + 1) (by ring)
  have h2 := hF.refl c (by have := hF.hr; have := hF.hrc; omega) le_rfl
  rw [h1, h2]

/-- Fact (ii) at `-r`: `γ(-r-1) = 0`. -/
lemma neg_r_sub_one : ¬ γ (-r - 1) := by
  have := hF.refl' (r + 1) (-r - 1) (by ring) (by have := hF.hr; omega) hF.hrc
  rw [this]; exact not_not.mpr hF.p2

/-- (iii) on `A₋ = [-c, -r-1]`, from (iii) on `A₊` and (i). -/
lemma p3_neg (u : ℤ) (h1 : -c ≤ u) (h2 : u + 1 ≤ -r - 1) : γ (u + 1) ↔ ¬ γ u := by
  have hr := hF.hr
  have e0 := hF.refl' (-u) u (by ring) (by omega) (by omega)
  have e1 := hF.refl' (-u - 1) (u + 1) (by ring) (by omega) (by omega)
  have := hF.p3 (-u - 1) (by omega) (by omega)
  rw [show -u - 1 + 1 = -u by ring] at this
  rw [e0, e1]; tauto

/-- **The arc lemma**.  If `γ` is constant on the non-excluded elements of the
run `[m, m + r − 1]`, `m ∈ [-c, c]`, the run lies in `[-r, 1]` or in `[0, r]`: otherwise it
contains one of the boundary pairs `(r, r+1)`, `(c, c+1)`, `(-r-1, -r)`, `(-1, 2)`, or
two consecutive residues of `A₊` or `A₋`. -/
lemma run_arc {m : ℤ} (hm1 : -c ≤ m) (hm2 : m ≤ c) {w : Prop}
    (hc : ∀ x, m ≤ x → x ≤ m + r - 1 → x ≠ 0 → x ≠ 1 → (γ x ↔ w)) :
    (-r ≤ m ∧ m + r - 1 ≤ 1) ∨ (0 ≤ m ∧ m + r - 1 ≤ r) := by
  have hrc := hF.hrc
  have hr := hF.hr
  by_contra hno
  have hcases : (m ≤ r ∧ r + 1 ≤ m + r - 1) ∨ (m ≤ c ∧ c + 1 ≤ m + r - 1) ∨
      (m ≤ -r - 1 ∧ -r ≤ m + r - 1) ∨ (m ≤ -1 ∧ 2 ≤ m + r - 1) ∨
      (r + 1 ≤ m ∧ m + r - 1 ≤ c) ∨ (m + r - 1 ≤ -r - 1) := by omega
  rcases hcases with h | h | h | h | h | h
  · -- the boundary pair `(r, r + 1)`
    have a := hc r (by omega) (by omega) (by omega) (by omega)
    have b := hc (r + 1) (by omega) (by omega) (by omega) (by omega)
    have := hF.fplus r (by omega) le_rfl
    have := hF.p2
    tauto
  · -- the boundary pair `(c, c + 1)`
    have a := hc c (by omega) (by omega) (by omega) (by omega)
    have b := hc (c + 1) (by omega) (by omega) (by omega) (by omega)
    have := hF.step_c
    tauto
  · -- the boundary pair `(-r - 1, -r)`
    have a := hc (-r - 1) (by omega) (by omega) (by omega) (by omega)
    have b := hc (-r) (by omega) (by omega) (by omega) (by omega)
    have := hF.neg_r_sub_one
    have := hF.fminus (-r) le_rfl (by omega)
    tauto
  · -- the boundary pair `(-1, 2)` across the excluded pair
    have a := hc (-1) (by omega) (by omega) (by omega) (by omega)
    have b := hc 2 (by omega) (by omega) (by omega) (by omega)
    have := hF.fminus (-1) (by omega) le_rfl
    have := hF.fplus 2 le_rfl (by omega)
    tauto
  · -- inside `A₊`: (iii)
    have a := hc m le_rfl (by omega) (by omega) (by omega)
    have b := hc (m + 1) (by omega) (by omega) (by omega) (by omega)
    have := hF.p3 m (by omega) (by omega)
    tauto
  · -- inside `A₋`: (iii)
    have a := hc m le_rfl (by omega) (by omega) (by omega)
    have b := hc (m + 1) (by omega) (by omega) (by omega) (by omega)
    have := hF.p3_neg m hm1 (by omega)
    tauto

/-- The arc lemma for a run starting anywhere in `[-c - r, c + 1]` (shift by `k`). -/
lemma run_arc' {m : ℤ} (hm1 : -c - r ≤ m) (hm2 : m ≤ c + 1) {w : Prop}
    (hc : ∀ x, m ≤ x → x ≤ m + r - 1 → x ≠ 0 → x ≠ 1 → (γ x ↔ w)) :
    (-r ≤ m ∧ m + r - 1 ≤ 1) ∨ (0 ≤ m ∧ m + r - 1 ≤ r) := by
  have hrc := hF.hrc
  have hr := hF.hr
  rcases lt_or_ge c m with h | h
  · -- `m = c + 1 ≡ -c`
    exfalso
    have := hF.run_arc (m := m - (2 * c + 1)) (by omega) (by omega) (w := w)
      (fun x h1 h2 _ _ => by
        rw [← hF.per x]; exact hc _ (by omega) (by omega) (by omega) (by omega))
    omega
  rcases le_or_gt (-c) m with h' | h'
  · exact hF.run_arc h' h hc
  · -- `m < -c`: shift up by `k`
    exfalso
    have := hF.run_arc (m := m + (2 * c + 1)) (by omega) (by omega) (w := w)
      (fun x h1 h2 _ _ => by
        rw [hF.per' (x - (2 * c + 1)) x (by ring)]
        exact hc _ (by omega) (by omega) (by omega) (by omega))
    omega

omit hF in
/-- The plus run of a failing `s`, as a constancy statement. -/
lemma plus_run {s : ℤ} {w : Prop} (hC : Const r γ s w) :
    ∀ x, s + 1 ≤ x → x ≤ s + 1 + r - 1 → x ≠ 0 → x ≠ 1 → (γ x ↔ w) := by
  intro x h1 h2 h3 h4
  have := (hC (x - s) (by omega) (by omega)).1
  rw [show s + (x - s) = x by ring] at this
  exact this ⟨h3, h4⟩

omit hF in
/-- The minus run of a failing `s`, as a constancy statement. -/
lemma minus_run {s : ℤ} {w : Prop} (hC : Const r γ s w) :
    ∀ x, s - r ≤ x → x ≤ s - r + r - 1 → x ≠ 0 → x ≠ 1 → (γ x ↔ ¬ w) := by
  intro x h1 h2 h3 h4
  have := (hC (s - x) (by omega) (by omega)).2
  rw [show s - (s - x) = x by ring] at this
  exact this ⟨h3, h4⟩

/-- **The two lists of `s`.**  If `(∗)` fails at `s`, the plus run forces
`s ∈ [-r-1, 1-r] ∪ {-1, 0}` and the minus run forces `s ∈ {0, 1, 2} ∪ {r, r+1}`; as
`r ≥ 2` these meet only in `0`. -/
theorem core_const {s : ℤ} (hs1 : -c ≤ s) (hs2 : s ≤ c) (hs0 : s ≠ 0)
    (w : Prop) : ¬ Const r γ s w := by
  intro hC
  have hrc := hF.hrc
  have hr := hF.hr
  have hp := hF.run_arc' (m := s + 1) (by omega) (by omega) (plus_run hC)
  have hm := hF.run_arc' (m := s - r) (by omega) (by omega) (minus_run hC)
  omega

/-- `(∗)` at every `s ∈ [-c, c] ∖ {0}`, in witness form: for every target value `w` there is
a non-excluded read disagreeing with the constant pattern `w` / `¬w`. -/
theorem core {s : ℤ} (hs1 : -c ≤ s) (hs2 : s ≤ c) (hs0 : s ≠ 0) (w : Prop) :
    ∃ a, 1 ≤ a ∧ a ≤ r ∧
      ((s + a ≠ 0 ∧ s + a ≠ 1 ∧ ¬ (γ (s + a) ↔ w)) ∨
       (s - a ≠ 0 ∧ s - a ≠ 1 ∧ ¬ (γ (s - a) ↔ ¬ w))) := by
  have hn : ¬ Const r γ s w := hF.core_const hs1 hs2 hs0 w
  by_contra hno
  apply hn
  intro a h1 h2
  constructor
  · intro ⟨h3, h4⟩; by_contra h5; exact hno ⟨a, h1, h2, Or.inl ⟨h3, h4, h5⟩⟩
  · intro ⟨h3, h4⟩; by_contra h5; exact hno ⟨a, h1, h2, Or.inr ⟨h3, h4, h5⟩⟩

end Folded

end Hand
end Rows
end Bump
end Trop
end PeriodicDifference
