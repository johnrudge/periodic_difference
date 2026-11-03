/-
# `PeriodicDifference/OddRows.lean` — block-preserving dilation of a σ-bump carrier

An earlier version of the paper claimed that a constant-minimum carrier `P ⊆ ℤ/2k` for `S`
is carried by any odd unit `d` modulo `2k` to a carrier `dP` for `dS`.  That is false
(2026-09-05): a tap `j` with `d·j mod 2k ≥ k` reads the *other* block of the anti-periodic
carrier.  What is true is the **block-preserving** case, and that is what this file
proves in the clause form `BumpSat` of `PeriodicDifference/SigmaBump.lean`:

  if `BumpSat k S σ Q`, `d·e ≡ 1 (mod 2k)` and `d·s mod 2k < k` for every `s ∈ S`, then
  `BumpSat k S' σ' Q'` with `S' = {d·s mod k}`, `σ' = d·σ mod k` and
  `Q' = (d·P) ∩ [0, k)`, where `P = {n < 2k : inP k Q n}`.

The proof is the relabelling `n ↦ d·n` of `ℤ/2k`: `inP k Q' n ↔ inP k Q (e·n mod 2k)`
(`inP_dilQ`), so the reads of clause `i'` at the dilated support are the reads of clause
`i = e·i' mod k` at the original one, all complemented when `e·i' mod 2k` lies in the
upper block — non-constancy survives either way — and the deletions correspond because
`d` is a unit modulo `k`.  The pin condition (B1) survives *because* every tap stays in
its block: `d·s mod 2k < k` means the read at `s' = d·s mod k` is the read at `s`, not
its complement.

Use (the odd orders): the residue of `thm:odd-nondil` at odd `k` is the family
`2μ·T_r = {2μj, k − 2μj : 1 ≤ j ≤ r}` with `rμ ≤ (k−1)/2`; dilating the base member
`2·T_r` by `d ≡ μ` moves every tap `2j` to `2μj < k` and every tap `k − 2j` to
`k − 2μj`, so the transport is block-preserving and one carrier per `(k, r)` suffices.
-/
import PeriodicDifference.TapRead

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace Dilate

/-! ## The dilated carrier -/

/-- `P ∩ [0, 2k)`: the anti-periodic set coded by `Q`, as a finset. -/
def Pset (k : ℕ) (Q : Finset ℕ) : Finset ℕ := (Finset.range (2 * k)).filter (inP k Q)

/-- `(d·P) ∩ [0, k)`: the bit set coding the dilated carrier. -/
def dilQ (k : ℕ) (Q : Finset ℕ) (d : ℕ) : Finset ℕ :=
  ((Pset k Q).image (fun x => d * x % (2 * k))).filter (fun x => x < k)

/-- The dilated support `{d·s mod k}`. -/
def dilS (k : ℕ) (S : Finset ℕ) (d : ℕ) : Finset ℕ := S.image (fun s => d * s % k)

variable {k : ℕ} {Q : Finset ℕ}

lemma mem_dilQ {d x : ℕ} :
    x ∈ dilQ k Q d ↔ x < k ∧ ∃ y, y < 2 * k ∧ inP k Q y ∧ d * y % (2 * k) = x := by
  simp only [dilQ, Pset, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨y, ⟨hy, hyP⟩, rfl⟩, hx⟩
    exact ⟨hx, y, hy, hyP, rfl⟩
  · rintro ⟨hx, y, hy, hyP, rfl⟩
    exact ⟨⟨y, ⟨hy, hyP⟩, rfl⟩, hx⟩

/-! ## Arithmetic of the unit `d` with inverse `e` modulo `2k` -/

section Unit

variable (hk : 0 < k) {d e : ℕ} (hde : d * e % (2 * k) = 1)
include hk hde

/-- `d·e ≡ 1 (mod 2k)`. -/
lemma de_modEq : d * e ≡ 1 [MOD 2 * k] := by
  unfold Nat.ModEq; rw [hde, Nat.mod_eq_of_lt (by omega)]

/-- Cancelling `d`: `d·a ≡ d·b (mod 2k) → a ≡ b (mod 2k)`. -/
lemma cancel_d {a b : ℕ} (h : d * a ≡ d * b [MOD 2 * k]) : a ≡ b [MOD 2 * k] := by
  have h1 : e * (d * a) ≡ e * (d * b) [MOD 2 * k] := h.mul_left e
  have h2 : e * (d * a) = (d * e) * a := by ring
  have h3 : e * (d * b) = (d * e) * b := by ring
  rw [h2, h3] at h1
  have h4 : (d * e) * a ≡ 1 * a [MOD 2 * k] := (de_modEq hk hde).mul_right a
  have h5 : (d * e) * b ≡ 1 * b [MOD 2 * k] := (de_modEq hk hde).mul_right b
  have := (h4.symm.trans h1).trans h5
  simpa using this

/-- `d · (e·m mod 2k) ≡ m (mod 2k)`. -/
lemma d_mul_e_mod (m : ℕ) : d * (e * m % (2 * k)) ≡ m [MOD 2 * k] := by
  have h1 : d * (e * m % (2 * k)) ≡ d * (e * m) [MOD 2 * k] :=
    (Nat.mod_modEq (e * m) (2 * k)).mul_left d
  have h2 : d * (e * m) = (d * e) * m := by ring
  have h3 : (d * e) * m ≡ 1 * m [MOD 2 * k] := (de_modEq hk hde).mul_right m
  rw [h2] at h1
  simpa using h1.trans h3

omit hk in
/-- `e` is odd. -/
lemma e_odd : e % 2 = 1 := by
  have h2 : 2 ∣ 2 * k := dvd_mul_right 2 k
  have h1 : d * e % 2 = 1 := by
    have := Nat.mod_mod_of_dvd (d * e) h2
    rw [hde] at this; omega
  rw [Nat.mul_mod] at h1
  rcases Nat.mod_two_eq_zero_or_one d with hd | hd <;>
    rcases Nat.mod_two_eq_zero_or_one e with he | he <;> simp [hd, he] at h1 ⊢

omit hk in
/-- `d` is odd. -/
lemma d_odd : d % 2 = 1 := by
  have h2 : 2 ∣ 2 * k := dvd_mul_right 2 k
  have h1 : d * e % 2 = 1 := by
    have := Nat.mod_mod_of_dvd (d * e) h2
    rw [hde] at this; omega
  rw [Nat.mul_mod] at h1
  rcases Nat.mod_two_eq_zero_or_one d with hd | hd <;>
    rcases Nat.mod_two_eq_zero_or_one e with he | he <;> simp [hd, he] at h1 ⊢

/-- `e · k ≡ k (mod 2k)`: the two blocks are swapped by `e` exactly as by `1`. -/
lemma e_mul_k_modEq : e * k ≡ k [MOD 2 * k] := by
  unfold Nat.ModEq; rw [mul_k_mod (e_odd hde) hk, Nat.mod_eq_of_lt (by omega)]

/-- `d · k mod 2k = k`. -/
lemma d_mul_k_mod : d * k % (2 * k) = k := mul_k_mod (d_odd hde) hk

end Unit

/-! ## `inP` on the dilated carrier -/

section InP

variable (hk : 0 < k) {d e : ℕ} (hde : d * e % (2 * k) = 1)
include hk hde

omit hde in
/-- `inP` depends only on the residue modulo `2k`. -/
lemma inP_mod_two_k (n : ℕ) : inP k Q n ↔ inP k Q (n % (2 * k)) := by
  have hn : n = (2 * (n / (2 * k))) * k + n % (2 * k) := by
    rw [show (2 * (n / (2 * k))) * k = 2 * k * (n / (2 * k)) by ring]
    exact (Nat.div_add_mod n (2 * k)).symm
  conv_lhs => rw [hn]
  rw [inP_qk_add hk Q]
  have : 2 * (n / (2 * k)) % 2 = 0 := Nat.mul_mod_right 2 _
  simp [this]

/-- Membership in `dilQ`, decoded: `x ∈ Q' ↔ inP k Q (e·x mod 2k)` for `x < k`. -/
lemma mem_dilQ_iff {x : ℕ} (hx : x < k) : x ∈ dilQ k Q d ↔ inP k Q (e * x % (2 * k)) := by
  rw [mem_dilQ]
  constructor
  · rintro ⟨-, y, hy, hyP, hdy⟩
    -- `y ≡ e·x (mod 2k)`
    have h1 : d * y ≡ d * (e * x % (2 * k)) [MOD 2 * k] := by
      have := d_mul_e_mod hk hde x
      unfold Nat.ModEq at this ⊢
      rw [hdy, this, Nat.mod_eq_of_lt (by omega)]
    have h2 := cancel_d hk hde h1
    unfold Nat.ModEq at h2
    rw [Nat.mod_eq_of_lt hy, Nat.mod_mod] at h2
    rwa [h2] at hyP
  · intro h
    refine ⟨hx, e * x % (2 * k), Nat.mod_lt _ (by omega), h, ?_⟩
    have := d_mul_e_mod hk hde x
    unfold Nat.ModEq at this
    rw [this, Nat.mod_eq_of_lt (by omega)]

/-- **The relabelling.**  `inP k Q' n ↔ inP k Q (e·n mod 2k)`. -/
lemma inP_dilQ (n : ℕ) : inP k (dilQ k Q d) n ↔ inP k Q (e * n % (2 * k)) := by
  rw [inP_mod_two_k hk (Q := dilQ k Q d) n]
  set m := n % (2 * k) with hm
  have hm2 : m < 2 * k := Nat.mod_lt _ (by omega)
  have hen : e * n % (2 * k) = e * m % (2 * k) := ((Nat.mod_modEq n (2 * k)).mul_left e).symm
  rw [hen]
  rcases Nat.lt_or_ge m k with hlt | hge
  · rw [inP_of_lt _ hlt, mem_dilQ_iff hk hde hlt]
  · -- the wrapped block: `m ∈ P' ↔ m − k ∉ Q'`
    rw [inP_wrap hk hge hm2, mem_dilQ_iff hk hde (by omega)]
    -- `e·(m − k) ≡ e·m + k (mod 2k)`, and `inP` flips across `k`
    have h1 : e * (m - k) + e * k = e * m := by rw [← Nat.mul_add]; congr 1; omega
    have h2 : e * (m - k) + k ≡ e * m [MOD 2 * k] := by
      have := (e_mul_k_modEq hk hde).add_left (e * (m - k))
      rw [h1] at this; exact this.symm
    have h3 : inP k Q (e * m % (2 * k)) ↔ inP k Q (e * (m - k) % (2 * k) + k) := by
      rw [inP_mod_two_k hk (n := e * (m - k) % (2 * k) + k)]
      have : (e * (m - k) % (2 * k) + k) % (2 * k) = e * m % (2 * k) := by
        have h4 : e * (m - k) % (2 * k) + k ≡ e * (m - k) + k [MOD 2 * k] :=
          (Nat.mod_modEq _ _).add_right k
        exact h4.trans h2
      rw [this]
    rw [h3, inP_add_k hk]

end InP

/-! ## The transport theorem -/

/-- **Block-preserving dilation** (the unit dilation used in the proof of `thm:oddk`) — the
block-preserving case of the dilation transport.  If `d·e ≡ 1 (mod 2k)` and every tap of
`S` stays in the lower block under `d`, then the σ-bump carrier `Q` for `(S, σ)` is carried
to the σ-bump carrier `dilQ k Q d` for `(dilS k S d, d·σ mod k)`. -/
theorem bumpSat_dilate {S : Finset ℕ} {σ : ℕ} (h : BumpSat k S σ Q) {d e : ℕ}
    (hde : d * e % (2 * k) = 1) (hblock : ∀ s ∈ S, d * s % (2 * k) < k) :
    BumpSat k (dilS k S d) (d * σ % k) (dilQ k Q d) := by
  have hk := h.k_pos
  have hk2 : 0 < 2 * k := by omega
  -- a dilated tap, read in both moduli
  have hmod : ∀ s ∈ S, d * s % k = d * s % (2 * k) := by
    intro s hs
    have := hblock s hs
    have h2 : d * s % (2 * k) % k = d * s % k := Nat.mod_mod_of_dvd _ (dvd_mul_left k 2)
    rw [← h2, Nat.mod_eq_of_lt this]
  -- `e·(d·s mod 2k) ≡ s (mod 2k)` for `s < 2k`
  have hback : ∀ s, s < 2 * k → e * (d * s % (2 * k)) % (2 * k) = s := by
    intro s hs
    have h1 : d * (e * (d * s % (2 * k)) % (2 * k)) ≡ d * s % (2 * k) [MOD 2 * k] :=
      d_mul_e_mod hk hde (d * s % (2 * k))
    have h2 : d * (e * (d * s % (2 * k)) % (2 * k)) ≡ d * s [MOD 2 * k] :=
      h1.trans (Nat.mod_modEq _ _)
    have h3 := cancel_d hk hde h2
    unfold Nat.ModEq at h3
    rw [Nat.mod_mod, Nat.mod_eq_of_lt hs] at h3
    exact h3
  -- a dilated tap is a nonzero residue below `k`
  have hpos : ∀ s ∈ S, 0 < d * s % k := by
    intro s hs
    have hs' := h.S_sub s hs
    by_contra h0
    have h0' : d * s % k = 0 := by omega
    have : d * s % (2 * k) = 0 ∨ d * s % (2 * k) = k := by
      have hb := hblock s hs
      have := hmod s hs
      omega
    rcases this with h1 | h1
    · have := hback s (by omega); rw [h1] at this; simp at this; omega
    · -- `d·s ≡ k`: then `s ≡ e·k ≡ k`, impossible for `s < k`
      have := hback s (by omega)
      rw [h1] at this
      have hek := e_mul_k_modEq hk hde
      unfold Nat.ModEq at hek
      rw [hek, Nat.mod_eq_of_lt (by omega)] at this
      omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- S_sub
    intro j hj
    rw [dilS, Finset.mem_image] at hj
    obtain ⟨s, hs, rfl⟩ := hj
    exact ⟨hpos s hs, Nat.mod_lt _ hk⟩
  · -- σ ∈ S'
    rw [dilS, Finset.mem_image]; exact ⟨σ, h.σ_mem, rfl⟩
  · -- (B1)
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, dilS,
      Finset.mem_image]
    constructor
    · rintro ⟨hxQ, hx0 | ⟨s, hs, rfl⟩⟩
      · -- `0 ∈ Q'` is impossible
        exfalso
        rw [hx0, mem_dilQ_iff hk hde hk] at hxQ
        simp only [Nat.mul_zero, Nat.zero_mod] at hxQ
        rw [inP_of_lt _ hk] at hxQ
        exact h.zero_not_mem_Q hxQ
      · -- a pinned position reads its own bit: `s ∈ Q ↔ s = σ`
        have hs' := h.S_sub s hs
        rw [mem_dilQ_iff hk hde (Nat.mod_lt _ hk), hmod s hs, hback s (by omega),
          inP_of_lt _ hs'.2] at hxQ
        rw [h.eq_σ_of_mem hs hxQ]
    · rintro rfl
      refine ⟨?_, Or.inr ⟨σ, h.σ_mem, rfl⟩⟩
      have hσ := h.S_sub σ h.σ_mem
      rw [mem_dilQ_iff hk hde (Nat.mod_lt _ hk), hmod σ h.σ_mem, hback σ (by omega),
        inP_of_lt _ hσ.2]
      exact h.σ_mem_Q
  · -- (B2)
    intro i' hi'0 hi'k
    -- the original index: `ĩ = e·i' mod 2k`, `i = ĩ mod k`
    set ĩ := e * i' % (2 * k) with hĩ
    have hĩ2 : ĩ < 2 * k := Nat.mod_lt _ hk2
    have hdĩ : d * ĩ % (2 * k) = i' := by
      have := d_mul_e_mod hk hde i'
      unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt (by omega)]
    -- `i = ĩ` or `ĩ − k`, whichever lies below `k`
    set i := if ĩ < k then ĩ else ĩ - k with hi
    have hik : i < k := by rw [hi]; split_ifs <;> omega
    have hĩi : ĩ = i ∨ ĩ = i + k := by rw [hi]; split_ifs <;> omega
    have hi0 : 0 < i := by
      by_contra h0
      have h0' : i = 0 := by omega
      -- then `ĩ ∈ {0, k}`, and `d·ĩ mod 2k ∈ {0, k}`, but it is `i' ∈ (0, k)`
      rcases hĩi with h1 | h1
      · rw [h1, h0'] at hdĩ; simp at hdĩ; omega
      · rw [h1, h0', Nat.zero_add, d_mul_k_mod hk hde] at hdĩ
        omega
    -- the reads of clause `i'` are the reads of clause `i`, all complemented when `ĩ ≥ k`
    have hread : ∀ j ∈ S, inP k (dilQ k Q d) (i' + d * j % k) ↔
        (inP k Q (i + j) ↔ ĩ < k) := by
      intro j hj
      have hjk := h.S_sub j hj
      rw [inP_dilQ hk hde]
      -- `e·(i' + d·j mod k) ≡ ĩ + j (mod 2k)`
      have h1 : e * (i' + d * j % k) ≡ ĩ + j [MOD 2 * k] := by
        have ha : e * i' ≡ ĩ [MOD 2 * k] := (Nat.mod_modEq _ _).symm
        have hb : e * (d * j % k) ≡ j [MOD 2 * k] := by
          rw [hmod j hj]
          have := hback j (by omega)
          unfold Nat.ModEq; rw [this, Nat.mod_eq_of_lt (by omega)]
        have := ha.add hb
        rwa [← Nat.mul_add] at this
      unfold Nat.ModEq at h1
      rw [h1, ← inP_mod_two_k hk]
      rcases hĩi with h2 | h2
      · rw [h2]; simp [hik]
      · rw [h2, show i + k + j = (i + j) + k by ring, inP_add_k hk]
        have : ¬ (i + k < k) := by omega
        simp [this]
    -- deletions correspond
    have hdel : ∀ j ∈ S, ((i' + d * j % k) % k ≠ 0 ↔ (i + j) % k ≠ 0) ∧
        ((i' + d * j % k) % k ≠ d * σ % k ↔ (i + j) % k ≠ σ) := by
      intro j hj
      have hjk := h.S_sub j hj
      have hσk := h.S_sub σ h.σ_mem
      -- `i' + d·j ≡ d·(i + j) (mod k)`
      have hsum : (i' + d * j % k) % k = d * (i + j) % k := by
        have h1 : i' ≡ d * i [MOD k] := by
          have h2 : d * ĩ ≡ i' [MOD 2 * k] := by unfold Nat.ModEq; rw [hdĩ, Nat.mod_eq_of_lt (by omega)]
          have h3 : d * ĩ ≡ i' [MOD k] := Nat.ModEq.of_mul_left 2 h2
          have h4 : ĩ ≡ i [MOD k] := by
            rcases hĩi with h5 | h5
            · rw [h5]
            · rw [h5]; exact Nat.ModEq.symm (Nat.modEq_iff_dvd' (by omega) |>.mpr ⟨1, by omega⟩)
          exact (h3.symm.trans (h4.mul_left d))
        have h5 : d * j % k ≡ d * j [MOD k] := Nat.mod_modEq _ _
        have := h1.add h5
        unfold Nat.ModEq at this
        rw [this]; congr 1; ring
      -- `d·x mod k = d·y mod k ↔ x ≡ y (mod k)`, as `d` is a unit mod `k`
      have hunit : ∀ x y, d * x % k = d * y % k → x % k = y % k := by
        intro x y hxy
        have h1 : d * x ≡ d * y [MOD k] := hxy
        have h2 : e * (d * x) ≡ e * (d * y) [MOD k] := h1.mul_left e
        have h3 : e * (d * x) = (d * e) * x := by ring
        have h4 : e * (d * y) = (d * e) * y := by ring
        rw [h3, h4] at h2
        have hde' : d * e ≡ 1 [MOD k] := Nat.ModEq.of_mul_left 2 (de_modEq hk hde)
        have := ((hde'.mul_right x).symm.trans h2).trans (hde'.mul_right y)
        simpa using this
      constructor
      · rw [hsum]
        constructor
        · intro hne heq
          apply hne
          rw [Nat.mul_mod, heq]; simp
        · intro hne heq
          apply hne
          have := hunit (i + j) 0 (by rw [heq]; simp)
          simpa using this
      · rw [hsum]
        constructor
        · intro hne heq
          apply hne
          have h1 : (i + j) ≡ σ [MOD k] := by
            unfold Nat.ModEq; rw [heq, Nat.mod_eq_of_lt hσk.2]
          exact h1.mul_left d
        · intro hne heq
          apply hne
          have := hunit (i + j) σ heq
          rwa [Nat.mod_eq_of_lt hσk.2] at this
    obtain ⟨⟨j1, hj1, hj1z, hj1σ, hj1r⟩, ⟨j0, hj0, hj0z, hj0σ, hj0r⟩⟩ := h.B2 i hi0 hik
    have m1 : d * j1 % k ∈ dilS k S d := Finset.mem_image.mpr ⟨j1, hj1, rfl⟩
    have m0 : d * j0 % k ∈ dilS k S d := Finset.mem_image.mpr ⟨j0, hj0, rfl⟩
    rcases Nat.lt_or_ge ĩ k with hlt | hge
    · refine ⟨⟨d * j1 % k, m1, (hdel j1 hj1).1.mpr hj1z, (hdel j1 hj1).2.mpr hj1σ, ?_⟩,
        ⟨d * j0 % k, m0, (hdel j0 hj0).1.mpr hj0z, (hdel j0 hj0).2.mpr hj0σ, ?_⟩⟩
      · rw [hread j1 hj1]; exact ⟨fun _ => hlt, fun _ => hj1r⟩
      · rw [hread j0 hj0]; intro hh; exact hj0r (hh.mpr hlt)
    · refine ⟨⟨d * j0 % k, m0, (hdel j0 hj0).1.mpr hj0z, (hdel j0 hj0).2.mpr hj0σ, ?_⟩,
        ⟨d * j1 % k, m1, (hdel j1 hj1).1.mpr hj1z, (hdel j1 hj1).2.mpr hj1σ, ?_⟩⟩
      · rw [hread j0 hj0]; exact ⟨fun hh => absurd hh hj0r, fun hh => absurd hh (not_lt.mpr hge)⟩
      · rw [hread j1 hj1]; intro hh; exact absurd (hh.mp hj1r) (not_lt.mpr hge)

end Dilate

/-! ## The interval carrier at odd order: the base member `2·T_r` (`thm:odd-rowcarrier`)

At odd `k = 2c + 1` the dilated intervals are `2μ·T_r`, `rμ ≤ c` (`eq:odd-prog`); by
`bumpSat_dilate` it suffices to exhibit a carrier at the base member
`S_r = {2j, k − 2j : 1 ≤ j ≤ r}` — the even numbers `2, …, 2r` and the odd numbers
`k − 2r, …, k − 2`.  The paper's carrier is given folded onto `ℤ/k` (`lem:odd-fold`):
`γ(u) = [u ≡ r + 1 (mod 2)]` and `γ(−u) = 1 − γ(u)` for `r < u ≤ c`.  Unfolded, it is `σ = 2`
together with the free positions `y` with `y/2 ≡ r + 1` (`y` even) or `(k − y)/2 ≡ r + 1`
(`y` odd) modulo `2` (`foldQ`); the proof is `PeriodicDifference/OddRowsHand*.lean`. -/

namespace Rows

/-- The base member `S_r = {2j, k − 2j : 1 ≤ j ≤ r}`. -/
def rowS (k r : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 r).image (fun j => 2 * j)) ∪ ((Finset.Icc 1 r).image (fun j => k - 2 * j))

/-- The pattern of `thm:odd-rowcarrier` on the free positions, as a linear predicate. -/
def foldPat (k r y : ℕ) : Prop :=
  (y % 2 = 0 ∧ (y / 2) % 2 = (r + 1) % 2) ∨ (y % 2 = 1 ∧ ((k - y) / 2) % 2 = (r + 1) % 2)

instance (k r y : ℕ) : Decidable (foldPat k r y) := by unfold foldPat; infer_instance

/-- The interval carrier: `σ = 2` and the free positions of the pattern. -/
def foldQ (k r : ℕ) : Finset ℕ :=
  insert 2 ((Finset.range k).filter (fun y => 0 < y ∧ y ∉ rowS k r ∧ foldPat k r y))

variable {k r : ℕ}

/-- Membership in `S_r` as a linear predicate (for `2r + 3 ≤ k`, `k` odd). -/
lemma mem_rowS (hk : k % 2 = 1) (hrk : 2 * r + 3 ≤ k) {y : ℕ} :
    y ∈ rowS k r ↔ (y % 2 = 0 ∧ 2 ≤ y ∧ y ≤ 2 * r) ∨ (y % 2 = 1 ∧ k - 2 * r ≤ y ∧ y ≤ k - 2) := by
  simp only [rowS, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  · rintro (h | h)
    · exact Or.inl ⟨y / 2, by omega, by omega⟩
    · exact Or.inr ⟨(k - y) / 2, by omega, by omega⟩

lemma mem_foldQ (hk : k % 2 = 1) (hrk : 2 * r + 3 ≤ k) {y : ℕ} :
    y ∈ foldQ k r ↔ y = 2 ∨ (0 < y ∧ y < k ∧
      ¬ ((y % 2 = 0 ∧ 2 ≤ y ∧ y ≤ 2 * r) ∨ (y % 2 = 1 ∧ k - 2 * r ≤ y ∧ y ≤ k - 2)) ∧
      foldPat k r y) := by
  simp only [foldQ, Finset.mem_insert, Finset.mem_filter, Finset.mem_range, mem_rowS hk hrk]
  tauto

/-- `S_r` as a linear predicate. -/
def Slin (k r y : ℕ) : Prop :=
  (y % 2 = 0 ∧ 2 ≤ y ∧ y ≤ 2 * r) ∨ (y % 2 = 1 ∧ k - 2 * r ≤ y ∧ y ≤ k - 2)

lemma mem_rowS' (hk : k % 2 = 1) (hrk : 2 * r + 3 ≤ k) {y : ℕ} : y ∈ rowS k r ↔ Slin k r y :=
  mem_rowS hk hrk

end Rows

end Bump
end Trop
end PeriodicDifference
