/-
# `PeriodicDifference/HalfArc.lean` — the half-arc carrier and the odd indices (`lem:allodd-oddhalf`)

The paper's half-arc carrier (`def:allodd-halfarc`): for an odd multiplier `d` (the paper's
`ν`) and a shift `t ∈ {0, k}`, `Q(d;t)` (the paper's `Q(ν;t)`) is `a` together with every free
position `y` whose phase `d·y + t_y` lies in the lower half `[0, k)` of `ℤ/2k`, with `t_y = 0`
at even `y` and `t_y = t` at odd `y` (`halfQ k S a d t`).  This file proves
`lem:allodd-oddhalf`: every clause at an odd index holds, as soon as the half-pattern
`H_d(s) = [d·s mod 2k < k]` (the paper's `H_ν`) takes both values on the lower half of the
support.

The paper argues with the gaps of `dS` on the circle.  The proof here is local instead:
if `u, v ∈ S`, `2u, 2v < k`, have different half-patterns, then at every odd index the
four taps `u, k − u, v, k − v` (less the deleted tap `k − i`) already read both values.
After naming the residues `c = d·i`, `x = d·u`, `y = d·v` modulo `2k`, every read is a
linear condition on `c, x, y`, and the case analysis is `omega`'s.
-/
import PeriodicDifference.SigmaBump
import PeriodicDifference.PerSupportDefs

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace HalfArc

open Finset Shadow

/-! ## The carrier -/

/-- The half-arc carrier `Q(d;t)`, the paper's `Q(ν;t)` (`def:allodd-halfarc`): `a`, together with
every free position `y ∈ (0, k) ∖ S` whose phase `d·y + t_y` lies in `[0, k)` modulo `2k`, where
`t_y = 0` at even `y` and `t_y = t` at odd `y`. -/
def halfQ (k : ℕ) (S : Finset ℕ) (a d t : ℕ) : Finset ℕ :=
  insert a ((range k).filter (fun y => y ≠ 0 ∧ y ∉ S ∧
    (d * y + (if y % 2 = 0 then 0 else t)) % (2 * k) < k))

/-- The phase of a position under the multiplier `d`: `d·j mod 2k`. -/
def ph (k d j : ℕ) : ℕ := d * j % (2 * k)


/-! ## The four-tap core -/

section Core

/-- The read of a tap whose phase is `z` at an index of phase `c` (both below `2k`):
`(c + z) mod 2k < k`. -/
def R (k c z : ℕ) : Prop := (c + z < 2 * k ∧ c + z < k) ∨ (2 * k ≤ c + z ∧ c + z < 3 * k)

instance (k c z : ℕ) : Decidable (R k c z) :=
  inferInstanceAs (Decidable ((c + z < 2 * k ∧ c + z < k) ∨ (2 * k ≤ c + z ∧ c + z < 3 * k)))

set_option maxHeartbeats 4000000 in
/-- **The four-tap core.**  `x` is the least phase of `S` in the lower half and `y` the least
in the upper half, attained at the taps `u₀` and `v₀`; by palindromy the taps `k − u₀` and
`k − v₀` have phases `k − x` and `3k − y`, so `2x ≤ k` and `2y ≤ 3k`.  At an odd index
`i` of phase `c`, the only deleted tap is `k − i`, whose phase `z` has `c + z ≡ k`.  Unless
both least phases are the midpoints `k/2`, `3k/2`, the present taps among these four read
both values. -/
lemma core4 {k c i u₀ v₀ x y : ℕ} (hkev : k % 2 = 0) (hc : c < 2 * k) (hco : c % 2 = 1)
    (hu₀ : u₀ < k) (hv₀ : v₀ < k)
    (hx : x < k) (hx2 : 2 * x ≤ k) (hxo : x % 2 = 1)
    (hy : k < y) (hy2 : 2 * y ≤ 3 * k) (hyo : y % 2 = 1)
    (hdu : u₀ = k - i → x + c = k ∨ x + c = 3 * k)
    (hdu' : k - u₀ = k - i → (k - x) + c = k ∨ (k - x) + c = 3 * k)
    (hdv : v₀ = k - i → y + c = k ∨ y + c = 3 * k)
    (hdv' : k - v₀ = k - i → (3 * k - y) + c = k ∨ (3 * k - y) + c = 3 * k)
    (hnd : ¬ (2 * x = k ∧ 2 * y = 3 * k)) :
    ((u₀ ≠ k - i ∧ R k c x) ∨ (k - u₀ ≠ k - i ∧ R k c (k - x)) ∨
      (v₀ ≠ k - i ∧ R k c y) ∨ (k - v₀ ≠ k - i ∧ R k c (3 * k - y))) ∧
    ((u₀ ≠ k - i ∧ ¬ R k c x) ∨ (k - u₀ ≠ k - i ∧ ¬ R k c (k - x)) ∨
      (v₀ ≠ k - i ∧ ¬ R k c y) ∨ (k - v₀ ≠ k - i ∧ ¬ R k c (3 * k - y))) := by
  unfold R
  constructor <;> omega

/-- **The degenerate core.**  When every phase of `S` is a midpoint `k/2` or `3k/2`, the taps
`u, k − u` share one midpoint and `v, k − v` the other; at most one of the four is deleted. -/
lemma core_deg {k c i u v pu pv : ℕ} (hkev : k % 2 = 0) (hc : c < 2 * k)
    (hu2 : 2 * u < k) (hv2 : 2 * v < k)
    (hpu : 2 * pu = k ∨ 2 * pu = 3 * k) (hpv : 2 * pv = k ∨ 2 * pv = 3 * k) (hne : pu ≠ pv) :
    ((u ≠ k - i ∧ R k c pu) ∨ (k - u ≠ k - i ∧ R k c pu) ∨
      (v ≠ k - i ∧ R k c pv) ∨ (k - v ≠ k - i ∧ R k c pv)) ∧
    ((u ≠ k - i ∧ ¬ R k c pu) ∨ (k - u ≠ k - i ∧ ¬ R k c pu) ∨
      (v ≠ k - i ∧ ¬ R k c pv) ∨ (k - v ≠ k - i ∧ ¬ R k c pv)) := by
  unfold R
  constructor <;> omega

/-- From four taps and a disjunction of reads to the two clauses of an index. -/
lemma pick {S : Finset ℕ} {P : ℕ → Prop} {D : ℕ → Prop} {j₁ j₂ j₃ j₄ : ℕ}
    (h₁ : j₁ ∈ S) (h₂ : j₂ ∈ S) (h₃ : j₃ ∈ S) (h₄ : j₄ ∈ S)
    {r₁ r₂ r₃ r₄ : Prop} (hr₁ : D j₁ → (P j₁ ↔ r₁)) (hr₂ : D j₂ → (P j₂ ↔ r₂))
    (hr₃ : D j₃ → (P j₃ ↔ r₃)) (hr₄ : D j₄ → (P j₄ ↔ r₄))
    (K₁ : (D j₁ ∧ r₁) ∨ (D j₂ ∧ r₂) ∨ (D j₃ ∧ r₃) ∨ (D j₄ ∧ r₄))
    (K₂ : (D j₁ ∧ ¬ r₁) ∨ (D j₂ ∧ ¬ r₂) ∨ (D j₃ ∧ ¬ r₃) ∨ (D j₄ ∧ ¬ r₄)) :
    (∃ j ∈ S, D j ∧ P j) ∧ (∃ j ∈ S, D j ∧ ¬ P j) := by
  constructor
  · rcases K₁ with ⟨h, r⟩ | ⟨h, r⟩ | ⟨h, r⟩ | ⟨h, r⟩
    · exact ⟨_, h₁, h, (hr₁ h).mpr r⟩
    · exact ⟨_, h₂, h, (hr₂ h).mpr r⟩
    · exact ⟨_, h₃, h, (hr₃ h).mpr r⟩
    · exact ⟨_, h₄, h, (hr₄ h).mpr r⟩
  · rcases K₂ with ⟨h, r⟩ | ⟨h, r⟩ | ⟨h, r⟩ | ⟨h, r⟩
    · exact ⟨_, h₁, h, fun p => r ((hr₁ h).mp p)⟩
    · exact ⟨_, h₂, h, fun p => r ((hr₂ h).mp p)⟩
    · exact ⟨_, h₃, h, fun p => r ((hr₃ h).mp p)⟩
    · exact ⟨_, h₄, h, fun p => r ((hr₄ h).mp p)⟩

end Core

/-! ## Reads at an odd index -/

section Reads

variable {k d : ℕ}

/-- `R` is the lower-half test of the phase sum. -/
lemma R_iff {c z : ℕ} (hc : c < 2 * k) (hz : z < 2 * k) : R k c z ↔ (c + z) % (2 * k) < k := by
  unfold R
  rcases Nat.lt_or_ge (c + z) (2 * k) with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · have e : (c + z) % (2 * k) = c + z - 2 * k := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [e]; omega

/-- Moving half way round flips the half. -/
lemma flip_half {t : ℕ} (ht : t < 2 * k) : ¬ t < k ↔ (t + k) % (2 * k) < k := by
  rcases Nat.lt_or_ge (t + k) (2 * k) with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · have e : (t + k) % (2 * k) = t + k - 2 * k := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [e]; omega

/-- The phase of `y + z` is the sum of the phases, read by `R`. -/
lemma read_phase (hk : 0 < k) (y z : ℕ) :
    d * (y + z) % (2 * k) < k ↔ R k (d * y % (2 * k)) (d * z % (2 * k)) := by
  rw [R_iff (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)), phase_add]

/-- **The read at an odd index.**  If the even part of `Q` is the half-arc of `d` with shift
`0`, then a tap `j ∈ S` (odd, `0 < j < k`) at an odd index `i` with `i + j ≢ 0` reads the
lower-half test of the phase of `i + j`. -/
lemma read_odd (hk : 0 < k) (hkev : k % 2 = 0) (hd : d % 2 = 1) {Q : Finset ℕ}
    (hQ : ∀ y, y % 2 = 0 → 0 < y → y < k → (y ∈ Q ↔ d * y % (2 * k) < k))
    {i j : ℕ} (hi : i < k) (hio : i % 2 = 1) (hj : j < k) (hjo : j % 2 = 1)
    (h0 : (i + j) % k ≠ 0) :
    inP k Q (i + j) ↔ R k (ph k d i) (ph k d j) := by
  unfold ph
  rw [← read_phase hk]
  rcases Nat.lt_or_ge (i + j) k with h | h
  · have hm : (i + j) % k = i + j := Nat.mod_eq_of_lt h
    rw [inP_of_lt Q h, hQ _ (by omega) (by omega) h]
  · obtain ⟨m, hm⟩ : ∃ m, i + j = 1 * k + m := ⟨i + j - k, by omega⟩
    have hmk : m < k := by omega
    have hm0 : 0 < m := by
      by_contra hm0
      apply h0
      rw [hm, mod_qk_add_of_lt hmk]; omega
    rw [hm, inP_qk_add_of_lt hk Q 1 hmk, hQ _ (by omega) hm0 hmk, wrap_iff, one_mul,
      phase_add_k hd hk]
    exact flip_half (Nat.mod_lt (d * m) (show 0 < 2 * k by omega))

end Reads

/-! ## `lem:allodd-oddhalf` -/

section OddHalf

variable {k d : ℕ} {S : Finset ℕ} {a : ℕ}

/-- The phase of `k − j` complements the phase of `j` to `k` or `3k`. -/
lemma phase_pair (hd : d % 2 = 1) (hk : 0 < k) {j : ℕ} (hj : j ≤ k) :
    ph k d (k - j) + ph k d j = k ∨ ph k d (k - j) + ph k d j = 3 * k := by
  unfold ph
  have h := phase_k_sub hd hk hj
  have h1 := Nat.mod_lt (d * (k - j)) (show 0 < 2 * k by omega)
  have h2 := Nat.mod_lt (d * j) (show 0 < 2 * k by omega)
  rcases Nat.lt_or_ge (d * (k - j) % (2 * k) + d * j % (2 * k)) (2 * k) with h3 | h3
  · rw [Nat.mod_eq_of_lt h3] at h; omega
  · rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt (by omega)] at h; omega

set_option maxHeartbeats 1000000 in
/-- **`lem:allodd-oddhalf`.**  Let `S` be all-odd and palindromic at even `k`, `d` odd, and let
`u, v ∈ S` with `2u, 2v < k` lie in different halves under `d`.  If the even part of `Q`
is the half-arc of `d` with shift `0`, then at every odd index `i` some undeleted tap
reads `1` and some reads `0`, whatever the odd `σ`. -/
theorem odd_clause (hb : AllOddPal k S a) (hd : d % 2 = 1) {u v : ℕ} (hu : u ∈ S) (hv : v ∈ S)
    (hu2 : 2 * u < k) (hv2 : 2 * v < k)
    (huv : d * u % (2 * k) < k ↔ ¬ d * v % (2 * k) < k) {Q : Finset ℕ}
    (hQ : ∀ y, y % 2 = 0 → 0 < y → y < k → (y ∈ Q ↔ d * y % (2 * k) < k))
    {σ : ℕ} (hσ : σ % 2 = 1) {i : ℕ} (hi0 : 0 < i) (hik : i < k) (hio : i % 2 = 1) :
    (∃ j ∈ S, (i + j) % k ≠ 0 ∧ (i + j) % k ≠ σ ∧ inP k Q (i + j)) ∧
    (∃ j ∈ S, (i + j) % k ≠ 0 ∧ (i + j) % k ≠ σ ∧ ¬ inP k Q (i + j)) := by
  have hk := hb.k_pos
  have hkev := hb.even_k
  have hN : 0 < 2 * k := by omega
  have phlt : ∀ j, ph k d j < 2 * k := fun j => Nat.mod_lt _ hN
  have phodd : ∀ j ∈ S, ph k d j % 2 = 1 := by
    intro j hj; unfold ph; rw [phase_parity hd]; exact hb.odd j hj
  have nz : ∀ j ∈ S, j ≠ k - i → (i + j) % k ≠ 0 := by
    intro j hj hji h
    have hjk := hb.mem j hj
    rcases Nat.lt_or_ge (i + j) k with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at h; omega
    · rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)] at h; omega
  have nσ : ∀ j ∈ S, (i + j) % k ≠ σ := by
    intro j hj h
    have := mod_parity hkev (i + j)
    have := hb.odd j hj
    omega
  set c := ph k d i with hc
  -- the read of an undeleted tap
  have tapR : ∀ j ∈ S, j ≠ k - i → (inP k Q (i + j) ↔ R k c (ph k d j)) := by
    intro j hj hji
    have hjk := hb.mem j hj
    exact read_odd hk hkev hd hQ hik hio hjk.2 (hb.odd j hj) (nz j hj hji)
  -- the deleted tap `k − i` has phase complementary to `c`
  have hdel : ∀ j, j = k - i → ph k d j + c = k ∨ ph k d j + c = 3 * k := by
    intro j hj; subst hj; exact phase_pair hd hk hik.le
  -- it suffices to find taps `j ≠ k − i` reading both values
  suffices H : (∃ j ∈ S, j ≠ k - i ∧ inP k Q (i + j)) ∧ (∃ j ∈ S, j ≠ k - i ∧ ¬ inP k Q (i + j)) by
    obtain ⟨⟨j, hj, hji, r⟩, ⟨j', hj', hji', r'⟩⟩ := H
    exact ⟨⟨j, hj, nz j hj hji, nσ j hj, r⟩, ⟨j', hj', nz j' hj' hji', nσ j' hj', r'⟩⟩
  -- the least phases in each half
  have hlowne : (S.filter (fun j => ph k d j < k)).Nonempty := by
    by_cases h : ph k d u < k
    · exact ⟨u, mem_filter.mpr ⟨hu, h⟩⟩
    · exact ⟨v, mem_filter.mpr ⟨hv, by unfold ph; unfold ph at h; by_contra h'; exact h (huv.mpr h')⟩⟩
  have hhighne : (S.filter (fun j => ¬ ph k d j < k)).Nonempty := by
    by_cases h : ph k d u < k
    · exact ⟨v, mem_filter.mpr ⟨hv, by unfold ph; exact huv.mp h⟩⟩
    · exact ⟨u, mem_filter.mpr ⟨hu, h⟩⟩
  obtain ⟨u₀, hu₀f, hu₀min⟩ := exists_min_image _ (ph k d) hlowne
  obtain ⟨v₀, hv₀f, hv₀min⟩ := exists_min_image _ (ph k d) hhighne
  rw [mem_filter] at hu₀f hv₀f
  have hu₀k := hb.mem u₀ hu₀f.1
  have hv₀k := hb.mem v₀ hv₀f.1
  have hpu := phase_pair hd hk hu₀k.2.le
  have hpv := phase_pair hd hk hv₀k.2.le
  have hu₀o := phodd u₀ hu₀f.1
  have hv₀o := phodd v₀ hv₀f.1
  have hco : c % 2 = 1 := by rw [hc]; unfold ph; rw [phase_parity hd]; exact hio
  have hcl : c < 2 * k := phlt i
  have hku : ph k d (k - u₀) = k - ph k d u₀ := by
    have := phlt (k - u₀); omega
  have hkv : ph k d (k - v₀) = 3 * k - ph k d v₀ := by
    have := phlt (k - v₀); have := phlt v₀; have := hv₀f.2; omega
  have hx2 : 2 * ph k d u₀ ≤ k := by
    have := hu₀min (k - u₀) (mem_filter.mpr ⟨hb.pal u₀ hu₀f.1, by omega⟩); omega
  have hy2 : 2 * ph k d v₀ ≤ 3 * k := by
    have := phlt v₀
    have := hv₀min (k - v₀) (mem_filter.mpr ⟨hb.pal v₀ hv₀f.1, by omega⟩); omega
  have hyk : k < ph k d v₀ := by have := hv₀f.2; omega
  by_cases hnd : 2 * ph k d u₀ = k ∧ 2 * ph k d v₀ = 3 * k
  · -- every phase is a midpoint: use `u` and `v`
    have hmid : ∀ j ∈ S, 2 * ph k d j = k ∨ 2 * ph k d j = 3 * k := by
      intro j hj
      have hp := phase_pair hd hk (hb.mem j hj).2.le
      have hpk := hb.pal j hj
      have := phlt (k - j); have := phlt j
      by_cases hl : ph k d j < k
      · have h1 := hu₀min j (mem_filter.mpr ⟨hj, hl⟩)
        have h2 := hu₀min (k - j) (mem_filter.mpr ⟨hpk, by omega⟩)
        omega
      · have h1 := hv₀min j (mem_filter.mpr ⟨hj, hl⟩)
        have h2 := hv₀min (k - j) (mem_filter.mpr ⟨hpk, by omega⟩)
        omega
    have huk := hb.pal u hu
    have hvk := hb.pal v hv
    have hpu' := phase_pair hd hk (hb.mem u hu).2.le
    have hpv' := phase_pair hd hk (hb.mem v hv).2.le
    have hU := hmid u hu; have hV := hmid v hv
    have := phlt (k - u); have := phlt (k - v); have := phlt u; have := phlt v
    have eu : ph k d (k - u) = ph k d u := by omega
    have ev : ph k d (k - v) = ph k d v := by omega
    have hne : ph k d u ≠ ph k d v := by
      intro e; unfold ph at e; rw [e] at huv; exact iff_not_self huv
    have K := core_deg (i := i) (c := c) (u := u) (v := v) hkev hcl hu2 hv2 hU hV hne
    have t2 := tapR (k - u) huk
    have t4 := tapR (k - v) hvk
    rw [eu] at t2
    rw [ev] at t4
    exact pick hu huk hv hvk (tapR u hu) t2 (tapR v hv) t4 K.1 K.2
  · -- the generic case
    have K := core4 (i := i) (u₀ := u₀) (v₀ := v₀) hkev hcl hco hu₀k.2 hv₀k.2 hu₀f.2 hx2 hu₀o
      hyk hy2 hv₀o (fun h => hdel u₀ h) (fun h => by rw [← hku]; exact hdel _ h)
      (fun h => hdel v₀ h) (fun h => by rw [← hkv]; exact hdel _ h) hnd
    rw [← hku, ← hkv] at K
    exact pick hu₀f.1 (hb.pal u₀ hu₀f.1) hv₀f.1 (hb.pal v₀ hv₀f.1) (tapR u₀ hu₀f.1)
      (tapR (k - u₀) (hb.pal u₀ hu₀f.1)) (tapR v₀ hv₀f.1) (tapR (k - v₀) (hb.pal v₀ hv₀f.1))
      K.1 K.2

end OddHalf

end HalfArc
end Bump
end Trop
end PeriodicDifference
