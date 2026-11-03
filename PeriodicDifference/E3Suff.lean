/-
# `PeriodicDifference/E3Suff.lean` — the even-index clauses with a unit multiplier
(`lem:allodd-windows`, `prop:allodd-e3bump`)

Let `k` be even, `S` all-odd and palindromic with `a = min S`, and `d` (the paper's `ν`) a
unit modulo `2k`.  Work with phases: `X = dS ⊂ ℤ/2k` (`X k d S`, the paper's `Φ`), `α = da`,
`U = (0, k)`, `V = (k, 2k)`.
A clause at an even index `i` reads only odd positions: with `σ = a`, the tap `j ∈ S`
is deleted exactly when `i + j = a + k` (`tap_del`); an undeleted tap reads `0` at an
unwrapped pin, `1` at a wrapped pin, and `H(d(i+j) + t)` at a free position
(`read_even`), where `H(z) = [z mod 2k < k]`; put `H_d(y) = H(d·y)` (the paper's `H_ν`).

The phases read at an even index `i` form the read set `d·i + X` (the paper's `φ + Φ`).  The
four ways a read set can be constant give the conditions `C_U`, `C_V` of
`CosetFail` (`cU_of_all0`, `cU_of_all1`, `cV_of_all0`, `cV_of_all1`); the deleted point
`α + k` weakens the all-`0` condition on its side, but a read set with a deleted tap other
than the read set at `2a` contains the wrapped pin read by the tap `k − a` (`del_window`), and
the read set at `2a` is saved by the point `y` of (Tb) (`window2a`).  Two failures, one at
`t = 0` and one at `t = k`, then give a coset of a nontrivial subgroup inside `X`
(`CosetFail.cosetfail`), which is impossible for a unit `d` and `S ⊂ (0, k)`
(`no_coset`, `lem:allodd-nocoset`).  `fullwindows` is `lem:allodd-windows`; `even_clauses` is
the even half of `prop:allodd-e3bump`, and `bumpSat_halfQ`, the proposition itself, combines it
with `HalfArc.odd_clause` into `BumpSat k S a (halfQ k S a d t)`.
-/
import PeriodicDifference.HalfArc
import PeriodicDifference.CosetFail

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace E3Suff

open Finset Shadow HalfArc

/-! ## The phase set `X = dS` (the paper's `Φ = νS`) -/

/-- The phase set `X = dS ⊂ ℤ/2k`. -/
def X (k d : ℕ) (S : Finset ℕ) : Finset ℕ := S.image (fun j => d * j % (2 * k))

lemma mem_X {k d : ℕ} {S : Finset ℕ} {z : ℕ} :
    z ∈ X k d S ↔ ∃ j ∈ S, d * j % (2 * k) = z := by
  simp [X]

section Unit

variable {k d : ℕ}

/-- A unit modulo `2k` is odd. -/
lemma odd_of_unit (hd : Nat.Coprime d (2 * k)) : d % 2 = 1 :=
  Nat.odd_iff.mp (Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 k) hd))

/-- Multiplication by a unit is injective on `[0, 2k)`. -/
lemma phase_inj (hd : Nat.Coprime d (2 * k)) {s s' : ℕ} (hs : s < 2 * k) (hs' : s' < 2 * k)
    (h : d * s % (2 * k) = d * s' % (2 * k)) : s = s' :=
  (Nat.ModEq.cancel_left_of_coprime hd.symm h).eq_of_lt_of_lt hs hs'

/-- **No coset in `X`.**  Since `d` is a unit and `S ⊂ (0, k)`, the phase set contains no
coset of a nontrivial subgroup of `ℤ/2k`: the preimage of the coset is a residue class
modulo `g ≤ k`, which meets `[k, 2k)`. -/
lemma no_coset {S : Finset ℕ} (hk : 0 < k) (hd : Nat.Coprime d (2 * k))
    (hS : ∀ j ∈ S, 0 < j ∧ j < k) {c g : ℕ} (hg : g ∣ 2 * k) (hg0 : 0 < g) (hgk : g < 2 * k)
    (hc : ∀ t, (c + t * g) % (2 * k) ∈ X k d S) : False := by
  obtain ⟨s₀, hs₀, hs₀c⟩ := mem_X.mp (hc 0)
  have hs₀k := hS s₀ hs₀
  have hgk' : g ≤ k := by
    obtain ⟨q, hq⟩ := hg
    rcases q with _ | _ | q
    · omega
    · omega
    · have : g * (q + 1 + 1) = g * q + 2 * g := by ring
      omega
  set q := (k - 1 - s₀) / g with hq
  have hdm := Nat.div_add_mod (k - 1 - s₀) g
  have hr := Nat.mod_lt (k - 1 - s₀) hg0
  rw [← hq] at hdm
  -- the point `s₁ = s₀ + (q+1) g` of the residue class lies in `[k, 2k)`
  obtain ⟨s', hs', hs'c⟩ := mem_X.mp (hc ((q + 1) * d))
  have hs'k := hS s' hs'
  have h1 : d * s₀ ≡ c [MOD 2 * k] := by
    simpa using hs₀c
  have h2 : d * (s₀ + g * q + g) ≡ c + (q + 1) * d * g [MOD 2 * k] := by
    have e : d * (s₀ + g * q + g) = d * s₀ + (q + 1) * d * g := by ring
    rw [e]; exact h1.add_right _
  have h3 : d * s' ≡ d * (s₀ + g * q + g) [MOD 2 * k] := by
    unfold Nat.ModEq
    rw [h2, hs'c]
  have := phase_inj hd (s := s') (s' := s₀ + g * q + g) (by omega) (by omega) h3
  omega

end Unit

section Phases

variable {k d : ℕ} {S : Finset ℕ} {a : ℕ}

/-- The elements of `X` are odd residues below `2k`. -/
lemma X_bounds (hb : AllOddPal k S a) (hd : d % 2 = 1) :
    ∀ x ∈ X k d S, x < 2 * k ∧ x % 2 = 1 := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := mem_X.mp hx
  have hk := hb.k_pos
  exact ⟨Nat.mod_lt _ (by omega), by rw [phase_parity hd]; exact hb.odd j hj⟩

/-- `X = k − X`, in the form used by `cosetfail`. -/
lemma X_sym (hb : AllOddPal k S a) (hd : d % 2 = 1) :
    ∀ x ∈ X k d S, ∀ y, y < 2 * k → (x + y) % (2 * k) = k → y ∈ X k d S := by
  intro x hx y hy hxy
  obtain ⟨j, hj, rfl⟩ := mem_X.mp hx
  have hk := hb.k_pos
  refine mem_X.mpr ⟨k - j, hb.pal j hj, ?_⟩
  have h := phase_k_sub hd hk (hb.mem j hj).2.le
  have h1 := Nat.mod_lt (d * (k - j)) (show 0 < 2 * k by omega)
  have h2 := Nat.mod_lt (d * j) (show 0 < 2 * k by omega)
  rcases CosetFail.mod_two_k_cases (k := k) (a := d * (k - j) % (2 * k) + d * j % (2 * k))
    (by omega) with ⟨_, e⟩ | ⟨_, e⟩ <;>
  rcases CosetFail.mod_two_k_cases (k := k) (a := d * j % (2 * k) + y) (by omega) with
    ⟨_, e'⟩ | ⟨_, e'⟩ <;> omega

/-- A tap at an even index never reads position `0`. -/
lemma tap_nz (hb : AllOddPal k S a) {i j : ℕ} (hik : i < k) (hie : i % 2 = 0) (hj : j ∈ S) :
    (i + j) % k ≠ 0 := by
  have hjk := hb.mem j hj
  have hjo := hb.odd j hj
  have hkev := hb.even_k
  intro h
  rcases Nat.lt_or_ge (i + j) k with h' | h'
  · rw [Nat.mod_eq_of_lt h'] at h; omega
  · rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)] at h; omega

/-- A tap at an even index is deleted (reads `a` modulo `k`) exactly when it reads
the wrapped position `a + k`. -/
lemma tap_del (hb : AllOddPal k S a) {i j : ℕ} (hi0 : 0 < i) (hik : i < k) (hj : j ∈ S) :
    (i + j) % k = a ↔ i + j = a + k := by
  have hjk := hb.mem j hj
  have hja := hb.a_min j hj
  rcases Nat.lt_or_ge (i + j) k with h' | h'
  · rw [Nat.mod_eq_of_lt h']; omega
  · rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)]; omega

/-- **The read at an even index.**  If the odd part of `Q` is `{a}` together with the
free odd positions `y` with `(dy + t) mod 2k < k`, then an undeleted tap `j ∈ S` at an
even index `i` reads `0` at an unwrapped pin, `1` at a wrapped pin, and
`[(d(i+j) + t) mod 2k < k]` at a free position. -/
lemma read_even (hb : AllOddPal k S a) (hd : d % 2 = 1) {t : ℕ} {Q : Finset ℕ}
    (hQ : ∀ y, y % 2 = 1 → 0 < y → y < k →
      (y ∈ Q ↔ y = a ∨ (y ∉ S ∧ (d * y + t) % (2 * k) < k)))
    {i j : ℕ} (hi0 : 0 < i) (hik : i < k) (hie : i % 2 = 0) (hj : j ∈ S)
    (hdel : i + j ≠ a + k) :
    inP k Q (i + j) ↔
      ((i + j) % k ∈ S ∧ k ≤ i + j) ∨ ((i + j) % k ∉ S ∧ (d * (i + j) + t) % (2 * k) < k) := by
  have hk := hb.k_pos
  have hkev := hb.even_k
  have hjk := hb.mem j hj
  have hjo := hb.odd j hj
  have hja := hb.a_min j hj
  rcases Nat.lt_or_ge (i + j) k with h | h
  · rw [inP_of_lt Q h, Nat.mod_eq_of_lt h, hQ _ (by omega) (by omega) h]
    have : i + j ≠ a := by omega
    constructor
    · rintro (h' | ⟨h1, h2⟩)
      · exact absurd h' this
      · exact Or.inr ⟨h1, h2⟩
    · rintro (⟨_, h'⟩ | ⟨h1, h2⟩)
      · omega
      · exact Or.inr ⟨h1, h2⟩
  · obtain ⟨m, hm⟩ : ∃ m, i + j = 1 * k + m := ⟨i + j - k, by omega⟩
    have hmk : m < k := by omega
    have hm0 : 0 < m := by omega
    have hma : m ≠ a := by omega
    rw [hm, inP_qk_add_of_lt hk Q 1 hmk, wrap_iff, mod_qk_add_of_lt hmk,
      hQ _ (by omega) hm0 hmk]
    have e : (d * (1 * k + m) + t) % (2 * k) = ((d * m + t) % (2 * k) + k) % (2 * k) := by
      rw [show d * (1 * k + m) + t = (d * m + t) + d * k by ring, Nat.add_mod, mul_k_mod hd hk]
    rw [e]
    have hf := flip_half (k := k) (Nat.mod_lt (d * m + t) (show 0 < 2 * k by omega))
    have : 1 * k + m ≥ k := by omega
    constructor
    · intro hn
      by_cases hmS : m ∈ S
      · exact Or.inl ⟨hmS, this⟩
      · refine Or.inr ⟨hmS, hf.mp fun h' => hn (Or.inr ⟨hmS, h'⟩)⟩
    · rintro (⟨h1, _⟩ | ⟨h1, h2⟩) hn
      · rcases hn with h' | ⟨h', _⟩
        · exact hma h'
        · exact h' h1
      · rcases hn with h' | ⟨_, h'⟩
        · exact hma h'
        · exact hf.mpr h2 h'


end Phases

/-! ## Read sets and the four failure types -/

section Windows

variable {k d : ℕ} {S : Finset ℕ} {a : ℕ}

/-- The odd part of `Q` is `{a}` together with the free odd positions of phase shift `t`. -/
def OddPart (k : ℕ) (S : Finset ℕ) (a d t : ℕ) (Q : Finset ℕ) : Prop :=
  ∀ y, y % 2 = 1 → 0 < y → y < k → (y ∈ Q ↔ y = a ∨ (y ∉ S ∧ (d * y + t) % (2 * k) < k))

/-- The clause of `BumpSat` (σ = a) at the index `i`. -/
def Clause (k : ℕ) (S : Finset ℕ) (a : ℕ) (Q : Finset ℕ) (i : ℕ) : Prop :=
  (∃ j ∈ S, (i + j) % k ≠ 0 ∧ (i + j) % k ≠ a ∧ inP k Q (i + j)) ∧
  (∃ j ∈ S, (i + j) % k ≠ 0 ∧ (i + j) % k ≠ a ∧ ¬ inP k Q (i + j))

lemma ph_shift_k (hk : 0 < k) (p : ℕ) :
    (d * p + k) % (2 * k) = (d * p % (2 * k) + k) % (2 * k) := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show k < 2 * k by omega)]

/-- The point of the read set read by the tap `j` at the index `i`. -/
lemma win (i j : ℕ) : (d * i % (2 * k) + d * j % (2 * k)) % (2 * k) = d * (i + j) % (2 * k) :=
  (phase_add i j).symm

/-- A phase of a position is in `X` exactly when the position is in `S`. -/
lemma ph_mem_X (hb : AllOddPal k S a) (hd : Nat.Coprime d (2 * k)) {p : ℕ} (hp : p < 2 * k) :
    d * p % (2 * k) ∈ X k d S ↔ p ∈ S := by
  constructor
  · intro h
    obtain ⟨s, hs, e⟩ := mem_X.mp h
    have := hb.mem s hs
    rw [← phase_inj hd (by omega) hp e]; exact hs
  · intro h; exact mem_X.mpr ⟨p, h, rfl⟩

/-- An index phase is even, nonzero and not `k`. -/
lemma rho_good (hb : AllOddPal k S a) (hd : Nat.Coprime d (2 * k)) {m : ℕ} (hm0 : 0 < m)
    (hm : m < 2 * k) (hmk : m ≠ k) (hme : m % 2 = 0) :
    d * m % (2 * k) % 2 = 0 ∧ 0 < d * m % (2 * k) ∧ d * m % (2 * k) ≠ k ∧
      d * m % (2 * k) < 2 * k := by
  have hk := hb.k_pos
  have hd1 := odd_of_unit hd
  refine ⟨by rw [phase_parity hd1]; exact hme, ?_, ?_, Nat.mod_lt _ (by omega)⟩
  · rcases Nat.eq_zero_or_pos (d * m % (2 * k)) with h | h
    · have := phase_inj hd (s := m) (s' := 0) hm (by omega) (by rw [h]; simp)
      omega
    · exact h
  · intro h
    have := phase_inj hd (s := m) (s' := k) hm (by omega) (by rw [h, mul_k_mod hd1 hk])
    omega

end Windows
/-! ## The four failure types -/

section Fail

variable {k d : ℕ} {S : Finset ℕ} {a : ℕ}

/-- Every undeleted tap at `i` reads `0`. -/
def All0 (k : ℕ) (S : Finset ℕ) (a : ℕ) (Q : Finset ℕ) (i : ℕ) : Prop :=
  ∀ j ∈ S, i + j ≠ a + k → ¬ inP k Q (i + j)

/-- Every undeleted tap at `i` reads `1`. -/
def All1 (k : ℕ) (S : Finset ℕ) (a : ℕ) (Q : Finset ℕ) (i : ℕ) : Prop :=
  ∀ j ∈ S, i + j ≠ a + k → inP k Q (i + j)

lemma fail_cases (hb : AllOddPal k S a) {Q : Finset ℕ} {i : ℕ} (hi0 : 0 < i) (hik : i < k)
    (hie : i % 2 = 0) (h : ¬ Clause k S a Q i) : All0 k S a Q i ∨ All1 k S a Q i := by
  by_contra hc
  push_neg at hc
  obtain ⟨h0, h1⟩ := hc
  unfold All0 at h0; unfold All1 at h1
  push_neg at h0 h1
  obtain ⟨j₁, hj₁, hd₁, hr₁⟩ := h0
  obtain ⟨j₀, hj₀, hd₀, hr₀⟩ := h1
  exact h ⟨⟨j₁, hj₁, tap_nz hb hik hie hj₁, fun e => hd₁ ((tap_del hb hi0 hik hj₁).mp e), hr₁⟩,
    ⟨j₀, hj₀, tap_nz hb hik hie hj₀, fun e => hd₀ ((tap_del hb hi0 hik hj₀).mp e), hr₀⟩⟩
/-- An unwrapped undeleted tap reading `0` on a free position of phase in the read half
is a pin. -/
lemma pin_of_not {p : ℕ} {P : Prop}
    (hr : ¬ ((p % k ∈ S ∧ k ≤ p) ∨ (p % k ∉ S ∧ P))) (hP : P) : p ∈ S := by
  rcases Nat.lt_or_ge p k with h | h
  · rw [Nat.mod_eq_of_lt h] at hr
    by_contra hn; exact hr (Or.inr ⟨hn, hP⟩)
  · by_cases hm : p % k ∈ S
    · exact (hr (Or.inl ⟨hm, h⟩)).elim
    · exact (hr (Or.inr ⟨hm, hP⟩)).elim

variable (hb : AllOddPal k S a) (hd : Nat.Coprime d (2 * k))
include hb hd

/-- All reads `0` at `t = 0` gives `C_U(d·i)`, unless the removed point lies in `U`. -/
lemma cU_of_all0 {Q : Finset ℕ} (hQ : OddPart k S a d 0 Q) {i : ℕ} (hi0 : 0 < i) (hik : i < k)
    (hie : i % 2 = 0) (hall : All0 k S a Q i)
    (hdel : ∀ j ∈ S, i + j = a + k → k ≤ d * (i + j) % (2 * k)) :
    CosetFail.CU k (X k d S) (d * i % (2 * k)) := by
  have hd1 := odd_of_unit hd
  intro x hx _ hz
  obtain ⟨j, hj, rfl⟩ := mem_X.mp hx
  have hjk := hb.mem j hj
  rw [win] at hz ⊢
  by_cases hdl : i + j = a + k
  · have := hdel j hj hdl; omega
  · have hr := hall j hj hdl
    rw [read_even hb hd1 hQ hi0 hik hie hj hdl, add_zero] at hr
    rw [ph_mem_X hb hd (by omega)]
    exact pin_of_not hr hz

/-- All reads `0` at `t = k` gives `C_V(d·i)`, unless the removed point lies in `V`. -/
lemma cV_of_all0 {Q : Finset ℕ} (hQ : OddPart k S a d k Q) {i : ℕ} (hi0 : 0 < i) (hik : i < k)
    (hie : i % 2 = 0) (hall : All0 k S a Q i)
    (hdel : ∀ j ∈ S, i + j = a + k → d * (i + j) % (2 * k) < k) :
    CosetFail.CV k (X k d S) (d * i % (2 * k)) := by
  have hk := hb.k_pos
  have hd1 := odd_of_unit hd
  intro x hx hz _
  obtain ⟨j, hj, rfl⟩ := mem_X.mp hx
  have hjk := hb.mem j hj
  rw [win] at hz ⊢
  by_cases hdl : i + j = a + k
  · have := hdel j hj hdl; omega
  · have hr := hall j hj hdl
    rw [read_even hb hd1 hQ hi0 hik hie hj hdl] at hr
    rw [ph_mem_X hb hd (by omega)]
    refine pin_of_not hr ?_
    rw [ph_shift_k hk]
    exact (flip_half (Nat.mod_lt _ (by omega))).mp (by omega)
/-- A wrapped undeleted tap reading `1` off the read half is a wrapped pin, whose phase
moved half way round is in `X`. -/
lemma wrapped_pin {p : ℕ} {P : Prop} (hp : p < 2 * k) (hr : (p % k ∈ S ∧ k ≤ p) ∨ (p % k ∉ S ∧ P))
    (hP : ¬ P) : d * (p + k) % (2 * k) ∈ X k d S := by
  have hk := hb.k_pos
  rcases hr with ⟨h1, h2⟩ | ⟨_, h2⟩
  · rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)] at h1
    rw [show p + k = (p - k) + 2 * k by omega, ph_add_2k, ph_mem_X hb hd (by omega)]
    exact h1
  · exact (hP h2).elim

omit hd in
/-- The removed point moved half way round is `α ∈ X`. -/
lemma del_mem {i j : ℕ} (h : i + j = a + k) : d * (i + j + k) % (2 * k) ∈ X k d S := by
  rw [h, show a + k + k = a + 2 * k by ring, ph_add_2k]
  exact mem_X.mpr ⟨a, hb.a_mem, rfl⟩

/-- All reads `1` at `t = 0` gives `C_U(d·(i + k))`. -/
lemma cU_of_all1 {Q : Finset ℕ} (hQ : OddPart k S a d 0 Q) {i : ℕ} (hi0 : 0 < i) (hik : i < k)
    (hie : i % 2 = 0) (hall : All1 k S a Q i) :
    CosetFail.CU k (X k d S) (d * (i + k) % (2 * k)) := by
  have hk := hb.k_pos
  have hd1 := odd_of_unit hd
  intro x hx _ hz
  obtain ⟨j, hj, rfl⟩ := mem_X.mp hx
  have hjk := hb.mem j hj
  rw [win, show i + k + j = i + j + k by ring] at hz ⊢
  by_cases hdl : i + j = a + k
  · exact del_mem hb hdl
  · have hr := hall j hj hdl
    rw [read_even hb hd1 hQ hi0 hik hie hj hdl, add_zero] at hr
    refine wrapped_pin hb hd (by omega) hr ?_
    intro h
    rw [ph_add_k hd1 hk] at hz
    exact (flip_half (Nat.mod_lt (d * (i + j)) (show 0 < 2 * k by omega))).mpr hz h

/-- All reads `1` at `t = k` gives `C_V(d·(i + k))`. -/
lemma cV_of_all1 {Q : Finset ℕ} (hQ : OddPart k S a d k Q) {i : ℕ} (hi0 : 0 < i) (hik : i < k)
    (hie : i % 2 = 0) (hall : All1 k S a Q i) :
    CosetFail.CV k (X k d S) (d * (i + k) % (2 * k)) := by
  have hk := hb.k_pos
  have hd1 := odd_of_unit hd
  intro x hx hz _
  obtain ⟨j, hj, rfl⟩ := mem_X.mp hx
  have hjk := hb.mem j hj
  rw [win, show i + k + j = i + j + k by ring] at hz ⊢
  by_cases hdl : i + j = a + k
  · exact del_mem hb hdl
  · have hr := hall j hj hdl
    rw [read_even hb hd1 hQ hi0 hik hie hj hdl] at hr
    refine wrapped_pin hb hd (by omega) hr ?_
    intro h
    rw [ph_add_k hd1 hk] at hz
    rw [ph_shift_k hk] at h
    omega

end Fail
/-! ## Read sets that cannot fail all-`0` -/

section NoFail

variable {k d : ℕ} {S : Finset ℕ} {a : ℕ}

/-- **R1.**  A read set with a deleted tap, other than the read set at `2a`, contains the wrapped
pin read by the tap `k − a`, which reads `1` at every `t`. -/
lemma del_window (hb : AllOddPal k S a) (hd : d % 2 = 1) {t : ℕ} {Q : Finset ℕ}
    (hQ : OddPart k S a d t Q) {i j₀ : ℕ} (hi0 : 0 < i) (hik : i < k) (hie : i % 2 = 0)
    (hj₀ : j₀ ∈ S) (hdel : i + j₀ = a + k) (hi2a : i ≠ 2 * a) : ¬ All0 k S a Q i := by
  intro hall
  have hka := hb.pal a hb.a_mem
  have ha := hb.mem a hb.a_mem
  have hj := hb.mem j₀ hj₀
  have hne : i + (k - a) ≠ a + k := by omega
  apply hall (k - a) hka hne
  rw [read_even hb hd hQ hi0 hik hie hka hne]
  left
  refine ⟨?_, by omega⟩
  rw [show i + (k - a) = 1 * k + (k - j₀) by omega, mod_qk_add_of_lt (by omega)]
  exact hb.pal j₀ hj₀

/-- The read set at `2a` does not fail all-`0` when the free position `2a + j` read by the tap
`j` reads `1`. -/
lemma window2a (hb : AllOddPal k S a) (hd : d % 2 = 1) {t : ℕ} {Q : Finset ℕ}
    (hQ : OddPart k S a d t Q) (h2a : 2 * a < k) {j : ℕ} (hj : j ∈ S) (hjk : j ≠ k - a)
    (hF : (2 * a + j) % k ∉ S) (hH : (d * (2 * a + j) + t) % (2 * k) < k) :
    ¬ All0 k S a Q (2 * a) := by
  intro hall
  have ha := hb.mem a hb.a_mem
  have hjb := hb.mem j hj
  have hne : 2 * a + j ≠ a + k := by omega
  apply hall j hj hne
  rw [read_even hb hd hQ (by omega) h2a (by omega) hj hne]
  exact Or.inr ⟨hF, hH⟩

end NoFail
/-! ## `lem:allodd-windows` and `prop:allodd-e3bump` -/

section Main

variable {k d : ℕ} {S : Finset ℕ} {a : ℕ}

/-- **A failure at `t = 0` gives `C_U(ρ)`** for an admissible `ρ` (the paper's `φ` or `φ + k`),
unless it is the all-`0` failure of the read set at `2a` with the removed point in `U` (excluded by
`hw`). -/
lemma fail0 (hb : AllOddPal k S a) (hd : Nat.Coprime d (2 * k))
    {Q : Finset ℕ} (hQ : OddPart k S a d 0 Q) {i : ℕ} (hi0 : 0 < i) (hik : i < k)
    (hie : i % 2 = 0) (hf : ¬ Clause k S a Q i)
    (hw : ¬ d * a % (2 * k) < k → i = 2 * a → ¬ All0 k S a Q i) :
    ∃ ρ, ρ % 2 = 0 ∧ 0 < ρ ∧ ρ ≠ k ∧ ρ < 2 * k ∧ CosetFail.CU k (X k d S) ρ := by
  have hk := hb.k_pos
  have hd1 := odd_of_unit hd
  rcases fail_cases hb hi0 hik hie hf with h0 | h1
  · obtain ⟨e1, e2, e3, e4⟩ := rho_good hb hd (m := i) hi0 (by omega) (by omega) hie
    refine ⟨_, e1, e2, e3, e4, cU_of_all0 hb hd hQ hi0 hik hie h0 ?_⟩
    intro j hj hdl
    by_contra hlt
    rw [hdl, ph_add_k hd1 hk] at hlt
    have hεa : ¬ d * a % (2 * k) < k :=
      (flip_half (Nat.mod_lt (d * a) (show 0 < 2 * k by omega))).mpr (by omega)
    by_cases hi : i = 2 * a
    · exact hw hεa hi h0
    · exact del_window hb hd1 hQ hi0 hik hie hj hdl hi h0
  · obtain ⟨e1, e2, e3, e4⟩ := rho_good hb hd (m := i + k) (by omega) (by omega) (by omega)
      (by have := hb.even_k; omega)
    exact ⟨_, e1, e2, e3, e4, cU_of_all1 hb hd hQ hi0 hik hie h1⟩

/-- **A failure at `t = k` gives `C_V(ρ')`** for an admissible `ρ'`, unless it is the
all-`0` failure of the read set at `2a` with the removed point in `V` (excluded by `hw`). -/
lemma failk (hb : AllOddPal k S a) (hd : Nat.Coprime d (2 * k))
    {Q : Finset ℕ} (hQ : OddPart k S a d k Q) {i : ℕ} (hi0 : 0 < i) (hik : i < k)
    (hie : i % 2 = 0) (hf : ¬ Clause k S a Q i)
    (hw : d * a % (2 * k) < k → i = 2 * a → ¬ All0 k S a Q i) :
    ∃ ρ, ρ % 2 = 0 ∧ 0 < ρ ∧ ρ ≠ k ∧ ρ < 2 * k ∧ CosetFail.CV k (X k d S) ρ := by
  have hk := hb.k_pos
  have hd1 := odd_of_unit hd
  rcases fail_cases hb hi0 hik hie hf with h0 | h1
  · obtain ⟨e1, e2, e3, e4⟩ := rho_good hb hd (m := i) hi0 (by omega) (by omega) hie
    refine ⟨_, e1, e2, e3, e4, cV_of_all0 hb hd hQ hi0 hik hie h0 ?_⟩
    intro j hj hdl
    by_contra hlt
    rw [hdl, ph_add_k hd1 hk] at hlt
    have hεa : d * a % (2 * k) < k := by
      by_contra hn
      exact hlt ((flip_half (Nat.mod_lt (d * a) (show 0 < 2 * k by omega))).mp hn)
    by_cases hi : i = 2 * a
    · exact hw hεa hi h0
    · exact del_window hb hd1 hQ hi0 hik hie hj hdl hi h0
  · obtain ⟨e1, e2, e3, e4⟩ := rho_good hb hd (m := i + k) (by omega) (by omega) (by omega)
      (by have := hb.even_k; omega)
    exact ⟨_, e1, e2, e3, e4, cV_of_all1 hb hd hQ hi0 hik hie h1⟩
/-- `X` meets both halves when `H_d` differs at `x` and `a`. -/
lemma meets (hb : AllOddPal k S a) (hd : d % 2 = 1) {x : ℕ} (hx : x ∈ S)
    (hxa : d * x % (2 * k) < k ↔ ¬ d * a % (2 * k) < k) :
    (∃ z ∈ X k d S, z < k) ∧ (∃ z ∈ X k d S, k < z) := by
  have hkev := hb.even_k
  have px := phase_parity (k := k) hd x
  have pa := phase_parity (k := k) hd a
  have ox := hb.odd x hx
  have oa := hb.odd a hb.a_mem
  have mx : d * x % (2 * k) ∈ X k d S := mem_X.mpr ⟨x, hx, rfl⟩
  have ma : d * a % (2 * k) ∈ X k d S := mem_X.mpr ⟨a, hb.a_mem, rfl⟩
  by_cases ha : d * a % (2 * k) < k
  · have : ¬ d * x % (2 * k) < k := fun h => hxa.mp h ha
    have hne : d * x % (2 * k) ≠ k := by intro h; omega
    exact ⟨⟨_, ma, ha⟩, ⟨_, mx, by omega⟩⟩
  · have hne : d * a % (2 * k) ≠ k := by intro h; omega
    exact ⟨⟨_, mx, hxa.mpr ha⟩, ⟨_, ma, by omega⟩⟩

/-- Two complementary failure conditions are impossible (`lem:allodd-cosetfail` + `no_coset`). -/
lemma no_pair (hb : AllOddPal k S a) (hd : Nat.Coprime d (2 * k)) {x : ℕ} (hx : x ∈ S)
    (hxa : d * x % (2 * k) < k ↔ ¬ d * a % (2 * k) < k)
    (hU : ∃ ρ, ρ % 2 = 0 ∧ 0 < ρ ∧ ρ ≠ k ∧ ρ < 2 * k ∧ CosetFail.CU k (X k d S) ρ)
    (hV : ∃ ρ, ρ % 2 = 0 ∧ 0 < ρ ∧ ρ ≠ k ∧ ρ < 2 * k ∧ CosetFail.CV k (X k d S) ρ) : False := by
  have hd1 := odd_of_unit hd
  obtain ⟨ρ, h1, h2, h3, h4, hCU⟩ := hU
  obtain ⟨ρ', h1', h2', h3', h4', hCV⟩ := hV
  obtain ⟨hXU, hXV⟩ := meets hb hd1 hx hxa
  obtain ⟨c, g, hg, hg0, hg2k, hc⟩ := CosetFail.cosetfail hb.even_k (X_bounds hb hd1)
    (X_sym hb hd1) hXU hXV h1 h2 h3 h4 h1' h2' h3' h4' hCU hCV
  exact no_coset hb.k_pos hd hb.mem hg hg0 hg2k hc

/-- **`lem:allodd-windows`.**  If `H_d` is non-constant on `S`, a failing even clause at
`t = 0` and a failing even clause at `t = k` cannot coexist, except when one of them is
the all-`0` failure of the read set at `2a` on the side of the removed point `α + k`. -/
theorem fullwindows (hb : AllOddPal k S a) (hd : Nat.Coprime d (2 * k)) {x : ℕ} (hx : x ∈ S)
    (hxa : d * x % (2 * k) < k ↔ ¬ d * a % (2 * k) < k)
    {Q₀ Q₁ : Finset ℕ} (hQ₀ : OddPart k S a d 0 Q₀) (hQ₁ : OddPart k S a d k Q₁)
    {i₀ i₁ : ℕ} (hi₀ : 0 < i₀) (hik₀ : i₀ < k) (hie₀ : i₀ % 2 = 0) (hf₀ : ¬ Clause k S a Q₀ i₀)
    (hi₁ : 0 < i₁) (hik₁ : i₁ < k) (hie₁ : i₁ % 2 = 0) (hf₁ : ¬ Clause k S a Q₁ i₁) :
    (i₀ = 2 * a ∧ All0 k S a Q₀ i₀ ∧ ¬ d * a % (2 * k) < k) ∨
      (i₁ = 2 * a ∧ All0 k S a Q₁ i₁ ∧ d * a % (2 * k) < k) := by
  by_contra h
  push_neg at h
  obtain ⟨h₀, h₁⟩ := h
  exact no_pair hb hd hx hxa
    (fail0 hb hd hQ₀ hi₀ hik₀ hie₀ hf₀ fun hε hi hall => hε (h₀ hi hall))
    (failk hb hd hQ₁ hi₁ hik₁ hie₁ hf₁ fun hε hi hall => absurd hε (not_lt.mpr (h₁ hi hall)))
/-- **`prop:allodd-e3bump`, even indices.**  Let `k` be even, `S` all-odd and palindromic
with `a = min S`, and `d` a unit modulo `2k` satisfying the three-point condition (T):
(Ta) some `x ∈ S` with `2x < k`, `x ≠ a` has `H_d(x) ≠ H_d(a)`, and (Tb) some free position
`y = 2a + j` read at the index `2a` (`j ∈ S ∖ {k − a}`, `(2a + j) mod k ∉ S`) has
`H_d(y) ≠ H_d(a)`.  Then for `t = 0` or `t = k`, every clause at an even index holds, for
every `Q` whose odd part is `{a}` together with the free odd positions `y` with
`(d·y + t) mod 2k < k`. -/
theorem even_clauses (hb : AllOddPal k S a) (hd : Nat.Coprime d (2 * k))
    (hx : ∃ x ∈ S, 2 * x < k ∧ x ≠ a ∧ (d * x % (2 * k) < k ↔ ¬ d * a % (2 * k) < k))
    (hy : ∃ j ∈ S, j ≠ k - a ∧ (2 * a + j) % k ∉ S ∧
      (d * (2 * a + j) % (2 * k) < k ↔ ¬ d * a % (2 * k) < k)) :
    ∃ t, (t = 0 ∨ t = k) ∧ ∀ Q, OddPart k S a d t Q →
      ∀ i, 0 < i → i < k → i % 2 = 0 → Clause k S a Q i := by
  have hk := hb.k_pos
  have hd1 := odd_of_unit hd
  obtain ⟨x, hxS, hx2, -, hxa⟩ := hx
  obtain ⟨j, hj, hjk, hF, hjy⟩ := hy
  have h2a := hb.two_a_lt hxS hx2.ne
  by_contra hc
  push_neg at hc
  obtain ⟨Q₀, hQ₀, i₀, hi₀, hik₀, hie₀, hf₀⟩ := hc 0 (Or.inl rfl)
  obtain ⟨Q₁, hQ₁, i₁, hi₁, hik₁, hie₁, hf₁⟩ := hc k (Or.inr rfl)
  refine no_pair hb hd hxS hxa (fail0 hb hd hQ₀ hi₀ hik₀ hie₀ hf₀ ?_)
    (failk hb hd hQ₁ hi₁ hik₁ hie₁ hf₁ ?_)
  · intro hε hi
    subst hi
    exact window2a hb hd1 hQ₀ h2a hj hjk hF (by rw [add_zero]; exact hjy.mpr hε)
  · intro hε hi
    subst hi
    refine window2a hb hd1 hQ₁ h2a hj hjk hF ?_
    rw [ph_shift_k hk]
    exact (flip_half (Nat.mod_lt _ (by omega))).mp fun h => hjy.mp h hε
/-- **`prop:allodd-e3bump`.**  With `t` from `even_clauses`, `halfQ k S a d t` satisfies
`BumpSat` with `σ = a`: the odd indices by `HalfArc.odd_clause` (`lem:allodd-oddhalf`), the
even ones by `even_clauses`. -/
theorem bumpSat_halfQ (hb : AllOddPal k S a) (hd : Nat.Coprime d (2 * k))
    (hx : ∃ x ∈ S, 2 * x < k ∧ x ≠ a ∧ (d * x % (2 * k) < k ↔ ¬ d * a % (2 * k) < k))
    (hy : ∃ j ∈ S, j ≠ k - a ∧ (2 * a + j) % k ∉ S ∧
      (d * (2 * a + j) % (2 * k) < k ↔ ¬ d * a % (2 * k) < k)) :
    ∃ t, (t = 0 ∨ t = k) ∧ BumpSat k S a (halfQ k S a d t) := by
  have hd1 := odd_of_unit hd
  have hao := hb.odd a hb.a_mem
  obtain ⟨t, ht, h⟩ := even_clauses hb hd hx hy
  obtain ⟨x, hxS, hx2, -, hxa⟩ := hx
  have h2a := hb.two_a_lt hxS hx2.ne
  refine ⟨t, ht, ⟨hb.mem, hb.a_mem, ?_, ?_⟩⟩
  · ext y
    simp only [Finset.mem_inter, halfQ, Finset.mem_insert, Finset.mem_filter, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h1 | ⟨_, h0, hS, _⟩, h2⟩
      · exact h1
      · rcases h2 with h2 | h2
        · exact absurd h2 h0
        · exact absurd h2 hS
    · rintro rfl
      exact ⟨Or.inl rfl, Or.inr hb.a_mem⟩
  · intro i hi0 hik
    rcases Nat.mod_two_eq_zero_or_one i with hie | hio
    · refine h _ ?_ i hi0 hik hie
      intro y hyo hy0 hyk
      simp only [halfQ, Finset.mem_insert, Finset.mem_filter, Finset.mem_range,
        if_neg (show ¬ y % 2 = 0 by omega)]
      constructor
      · rintro (h | ⟨_, _, h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hyk, by omega, h1, h2⟩
    · refine odd_clause hb hd1 hxS hb.a_mem hx2 h2a hxa ?_ hao hi0 hik hio
      intro y hye hy0 hyk
      simp only [halfQ, Finset.mem_insert, Finset.mem_filter, Finset.mem_range, if_pos hye,
        add_zero]
      constructor
      · rintro (h | ⟨_, _, _, h⟩)
        · omega
        · exact h
      · intro h
        exact Or.inr ⟨hyk, by omega, fun hS => by have := hb.odd y hS; omega, h⟩

end Main

end E3Suff
end Bump
end Trop
end PeriodicDifference
