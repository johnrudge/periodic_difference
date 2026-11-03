/-
# `PeriodicDifference/E3AllDefs.lean` — definitions and generic lemmas for `thm:allodd-e3all`

Phases: `H_d(y) = [d·y mod 2k < k]` (the paper's `H_ν`, with the multiplier `d` the paper's `ν`).
The progression statement at `(k; a, x)` asks for a unit `d` modulo `2k` with
`H_d(2a − x) = H_d(a) ≠ H_d(x)`; the residue `2a − x mod 2k` is encoded as `(2a + 2k − x) mod 2k`
(exact for `x ≤ 2a + 2k`, in particular for `x < k`).  `APLemma k a x` is that statement;
`LemmaA` is `thm:lemmaA` at every order `k > 90`, taken as an explicit hypothesis (it is
formalised separately).

Contents: the witness predicate and its Boolean search (`apSearch`, sound by `apB_sound`); the
lifting step (`lift`: the statement at `(m; a, x)` gives it at `(gm; ga, gx)`, units modulo `2m`
lifting to units modulo `2gm`); the three-point condition (T) (`E3`, exactly the hypotheses `hx`,
`hy` of `E3Suff.bumpSat_halfQ`); the table of the 59 primitive progression failures at orders `≤ 90`
(`PF`); the depth-first enumeration of all-blocked lower halves (`gen`) with its completeness lemma
(`gen_complete`).
-/
import PeriodicDifference.E3Suff
import PeriodicDifference.AllOddBase
import PeriodicDifference.PerSupportDefs

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace E3All

open Finset

/-! ## The progression statement -/

/-- `d` witnesses the progression statement at `(k; a, x)`: a unit with
`H_d(2a − x) = H_d(a) ≠ H_d(x)`, where `2a − x` is read as `(2a + 2k − x) mod 2k`. -/
def APWit (k a x d : ℕ) : Prop :=
  Nat.Coprime d (2 * k) ∧ ((d * ((2 * a + 2 * k - x) % (2 * k))) % (2 * k) < k ↔
    d * a % (2 * k) < k) ∧ (d * x % (2 * k) < k ↔ ¬ d * a % (2 * k) < k)

/-- The progression statement at `(k; a, x)`. -/
def APLemma (k a x : ℕ) : Prop :=
  ∃ d, Nat.Coprime d (2 * k) ∧ ((d * ((2 * a + 2 * k - x) % (2 * k))) % (2 * k) < k ↔
    d * a % (2 * k) < k) ∧ (d * x % (2 * k) < k ↔ ¬ d * a % (2 * k) < k)

/-- `thm:lemmaA` (Lemma A) at every even order `k > 90`: the hypothesis of this module. -/
def LemmaA : Prop :=
  ∀ k a x, 90 < k → k % 2 = 0 → a < x → 2 * x < k → x % 2 = 1 → a % 2 = 1 → x ≠ 3 * a →
    Nat.gcd (Nat.gcd a x) k = 1 → APLemma k a x

/-- Boolean form of `APWit`. -/
def apB (k a x d : ℕ) : Bool :=
  Nat.gcd d (2 * k) == 1 &&
    (decide ((d * ((2 * a + 2 * k - x) % (2 * k))) % (2 * k) < k) ==
      decide (d * a % (2 * k) < k)) &&
    (decide (d * x % (2 * k) < k) != decide (d * a % (2 * k) < k))

/-- Search for a witness among `d < 2k`. -/
def apSearch (k a x : ℕ) : Bool := (List.range (2 * k)).any (apB k a x)

lemma apB_sound {k a x d : ℕ} (h : apB k a x d = true) : APWit k a x d := by
  simp only [apB, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_decide] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  constructor
  · intro hx ha; exact h3 (by simp [hx, ha])
  · intro hn; by_contra hx; exact h3 (by simp [hx, hn])

lemma apSearch_sound {k a x : ℕ} (h : apSearch k a x = true) : APLemma k a x := by
  obtain ⟨d, -, hd⟩ := List.any_eq_true.mp h
  exact ⟨d, apB_sound hd⟩

/-! ## Phases -/

/-- Adding `k` flips the half, for odd `d`. -/
lemma eps_add_k {k d : ℕ} (hd : d % 2 = 1) (hk : 0 < k) (y : ℕ) :
    d * (y + k) % (2 * k) < k ↔ ¬ d * y % (2 * k) < k := by
  obtain ⟨q, rfl⟩ : ∃ q, d = 2 * q + 1 := ⟨d / 2, by omega⟩
  have e : (2 * q + 1) * (y + k) = ((2 * q + 1) * y + k) + 2 * k * q := by ring
  rw [e, Nat.add_mul_mod_self_left, Nat.add_mod, Nat.mod_eq_of_lt (show k < 2 * k by omega)]
  exact (HalfArc.flip_half (Nat.mod_lt _ (by omega))).symm

/-- The phase of an odd position is odd. -/
lemma phase_odd {k d y : ℕ} (hd : d % 2 = 1) (hy : y % 2 = 1) : d * y % (2 * k) % 2 = 1 := by
  rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 2 k), Nat.mul_mod, hd, hy]

/-! ## Lifting -/

/-- A unit modulo `n` lifts to a unit modulo any multiple `N` of `n`. -/
lemma unit_lift {n N d : ℕ} (hN : 0 < N) (hnN : n ∣ N) (hd : Nat.Coprime d n) :
    ∃ D, Nat.Coprime D N ∧ D % n = d % n := by
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hnN (ZMod.unitOfCoprime d hd)
  refine ⟨(v : ZMod N).val, ZMod.val_coe_unit_coprime v, ?_⟩
  have h1 := congrArg (fun w : (ZMod n)ˣ => (w : ZMod n)) hv
  simp only [ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime] at h1
  rw [← ZMod.natCast_eq_natCast_iff', ← h1, ZMod.castHom_apply, ZMod.natCast_val]


/-- `H_D(g·p)` at order `gm` is `H_d(p)` at order `m` when `D ≡ d mod 2m`. -/
lemma eps_scale {m g d D : ℕ} (hg : 0 < g) (hD : D % (2 * m) = d % (2 * m)) (p : ℕ) :
    D * (g * p) % (2 * (g * m)) < g * m ↔ d * p % (2 * m) < m := by
  rw [show D * (g * p) = g * (D * p) by ring, show 2 * (g * m) = g * (2 * m) by ring,
    Nat.mul_mod_mul_left, Nat.mul_mod, hD, ← Nat.mul_mod, Nat.mul_lt_mul_left hg]

/-- **Lifting.** The progression statement at `(m; a, x)` gives it at `(gm; ga, gx)`. -/
lemma lift {m a x g d : ℕ} (hm : 0 < m) (hg : 0 < g) (h : APWit m a x d) :
    APLemma (g * m) (g * a) (g * x) := by
  obtain ⟨hd, h1, h2⟩ := h
  obtain ⟨D, hD, hDd⟩ := unit_lift (n := 2 * m) (N := 2 * (g * m)) (by positivity)
    ⟨g, by ring⟩ hd
  refine ⟨D, hD, ?_, ?_⟩
  · have e : (2 * (g * a) + 2 * (g * m) - g * x) % (2 * (g * m)) =
        g * ((2 * a + 2 * m - x) % (2 * m)) := by
      rw [show 2 * (g * a) + 2 * (g * m) - g * x = g * (2 * a + 2 * m - x) by
        rw [Nat.mul_sub]; ring_nf, show 2 * (g * m) = g * (2 * m) by ring,
        Nat.mul_mod_mul_left]
    rw [e, eps_scale hg hDd, eps_scale hg hDd]
    exact h1
  · rw [eps_scale hg hDd, eps_scale hg hDd]
    exact h2

/-! ## The three-point condition (T) and the progression route -/

open Shadow in
/-- The three-point condition (T) (`def:allodd-e3`) for the unit `d`: (Ta) and (Tb) are
exactly the hypotheses `hx`, `hy` of `E3Suff.bumpSat_halfQ`. -/
def E3 (k : ℕ) (S : Finset ℕ) (a d : ℕ) : Prop :=
  Nat.Coprime d (2 * k) ∧
    (∃ x ∈ S, 2 * x < k ∧ x ≠ a ∧ (d * x % (2 * k) < k ↔ ¬ d * a % (2 * k) < k)) ∧
    (∃ j ∈ S, j ≠ k - a ∧ (2 * a + j) % k ∉ S ∧
      (d * (2 * a + j) % (2 * k) < k ↔ ¬ d * a % (2 * k) < k))

instance (k : ℕ) (S : Finset ℕ) (a d : ℕ) : Decidable (E3 k S a d) := by
  unfold E3; infer_instance

open Shadow in
/-- **`lem:allodd-aproute`, first part.** If `x ∈ L ∖ {a}` has `x − 2a ∉ S`, then `j = k − x` is a
free tap at the index `2a` (`y = 2a + k − x ∈ Q_{2a}`), and every witness of the
progression statement at `(k; a, x)` satisfies (T). -/
lemma aproute1 {k a x d : ℕ} {S : Finset ℕ} (hb : AllOddPal k S a) (hx : x ∈ S)
    (hx2 : 2 * x < k) (hxa : x ≠ a) (h2a : x - 2 * a ∉ S) (hw : APWit k a x d) :
    E3 k S a d := by
  obtain ⟨hd, h1, h2⟩ := hw
  have hd1 : d % 2 = 1 := E3Suff.odd_of_unit hd
  have ha := hb.mem a hb.a_mem
  have hao := hb.odd a hb.a_mem
  have hxo := hb.odd x hx
  have hax : a < x := lt_of_le_of_ne (hb.a_min x hx) (Ne.symm hxa)
  refine ⟨hd, ⟨x, hx, hx2, hxa, h2⟩, k - x, hb.pal x hx, by omega, ?_, ?_⟩
  · rcases Nat.lt_or_ge x (2 * a) with hlt | hge
    · rw [show 2 * a + (k - x) = (2 * a - x) + k * 1 by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
      intro hm
      have := hb.a_min _ hm
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      intro hm
      have := hb.pal _ hm
      rw [show k - (2 * a + (k - x)) = x - 2 * a by omega] at this
      exact h2a this
  · have e : (2 * a + 2 * k - x) = (2 * a + (k - x)) + k := by omega
    rw [Nat.mul_mod_mod, e, eps_add_k hd1 (by omega)] at h1
    tauto

/-! ## The primitive progression failures at orders `≤ 90` -/

/-- The 59 primitive failures `(m, a, x)` (`x ≠ 3a`) of the progression statement at orders
`m ≤ 90` (`tools/e3/shrink/b2_primitive_ap_failures.csv`). -/
def PF : List (ℕ × ℕ × ℕ) :=
  [(12, 1, 5), (12, 3, 5), (16, 1, 5), (16, 1, 7), (16, 3, 7), (20, 1, 7), (20, 3, 5), (20, 7,
    9), (22, 1, 5), (22, 1, 9), (22, 5, 7), (24, 1, 5), (24, 1, 11), (24, 3, 7), (24, 5, 7),
    (24, 5, 9), (24, 7, 9), (28, 1, 7), (28, 3, 13), (28, 7, 9), (30, 1, 11), (30, 1, 13), (30,
    7, 13), (36, 1, 7), (36, 1, 15), (36, 1, 17), (36, 5, 11), (36, 5, 13), (36, 7, 17), (36,
    11, 15), (40, 1, 5), (40, 1, 15), (40, 3, 15), (40, 5, 17), (40, 7, 19), (40, 9, 13), (40,
    15, 19), (42, 1, 5), (42, 1, 9), (42, 1, 17), (42, 3, 19), (42, 5, 7), (42, 11, 15), (42,
    11, 19), (42, 13, 15), (48, 3, 11), (48, 15, 23), (60, 1, 23), (60, 11, 13), (60, 13, 27),
    (60, 19, 21), (70, 1, 17), (70, 3, 25), (70, 9, 13), (70, 13, 15), (90, 1, 33), (90, 17,
    21), (90, 19, 41), (90, 23, 39)]

/-- At even order `m`, every primitive pair outside `PF` (with `x ≠ 3a`) has a witness.
(Odd orders are skipped: at `m = 15` there are primitive failures, irrelevant here.) -/
def pfCheck (m : ℕ) : Bool :=
  m % 2 == 1 || (List.range m).all fun x => (List.range x).all fun a =>
    !(a % 2 == 1 && x % 2 == 1 && decide (2 * x < m) && x != 3 * a &&
        Nat.gcd (Nat.gcd a x) m == 1) || PF.contains (m, a, x) || apSearch m a x

lemma pf_sound {m a x : ℕ} (h : pfCheck m = true) (hme : m % 2 = 0) (hax : a < x) (h2x : 2 * x < m)
    (hxo : x % 2 = 1) (hao : a % 2 = 1) (h3 : x ≠ 3 * a) (hg : Nat.gcd (Nat.gcd a x) m = 1)
    (hn : PF.contains (m, a, x) = false) : APLemma m a x := by
  simp only [pfCheck, hme, Bool.or_eq_true, beq_iff_eq, zero_ne_one, false_or] at h
  have h1 := List.all_eq_true.mp h x (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 a (List.mem_range.mpr hax)
  rw [hn] at h2
  have hc : (a % 2 == 1 && x % 2 == 1 && decide (2 * x < m) && x != 3 * a &&
      Nat.gcd (Nat.gcd a x) m == 1) = true := by
    simp [hao, hxo, h2x, h3, hg]
  rw [hc] at h2
  exact apSearch_sound (by simpa using h2)

/-- **The lift of a failure.**  Given Lemma A above `90` and the tables below it, a failure
of the progression statement at `(k; a, x)` with `k > 90`, `x ≠ 3a` is the lift of a
primitive failure `(k/g; a/g, x/g) ∈ PF`, `g = gcd(a, x, k)`. -/
lemma pf_of_fail (hA : LemmaA) (hpf : ∀ m ≤ 90, pfCheck m = true) {k a x : ℕ} (hk : 90 < k)
    (he : k % 2 = 0) (hax : a < x) (h2x : 2 * x < k) (hxo : x % 2 = 1) (hao : a % 2 = 1)
    (h3 : x ≠ 3 * a) (hf : ¬ APLemma k a x) :
    PF.contains (k / Nat.gcd (Nat.gcd a x) k, a / Nat.gcd (Nat.gcd a x) k,
      x / Nat.gcd (Nat.gcd a x) k) = true := by
  generalize hgdef : Nat.gcd (Nat.gcd a x) k = g
  have hga : g ∣ a := hgdef ▸ (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgx : g ∣ x := hgdef ▸ (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hgk : g ∣ k := hgdef ▸ Nat.gcd_dvd_right _ _
  have hg0 : 0 < g := Nat.pos_of_ne_zero (by intro h0; rw [h0] at hgk; simp at hgk; omega)
  obtain ⟨a', rfl⟩ := hga
  obtain ⟨x', rfl⟩ := hgx
  obtain ⟨m, rfl⟩ := hgk
  simp only [Nat.mul_div_cancel_left _ hg0]
  have hgo : g % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one g with h | h
    · rw [Nat.mul_mod, h] at hao; simp at hao
    · exact h
  have hao' : a' % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one a' with h | h
    · rw [Nat.mul_mod, h] at hao; simp at hao
    · exact h
  have hxo' : x' % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one x' with h | h
    · rw [Nat.mul_mod, h] at hxo; simp at hxo
    · exact h
  have hme : m % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · exact h
    · rw [Nat.mul_mod, h, hgo] at he; simp at he
  have hax' : a' < x' := Nat.lt_of_mul_lt_mul_left hax
  have h2x' : 2 * x' < m := Nat.lt_of_mul_lt_mul_left (a := g) (by linarith)
  have h3' : x' ≠ 3 * a' := by rintro rfl; exact h3 (by ring)
  have hg' : Nat.gcd (Nat.gcd a' x') m = 1 := by
    rw [Nat.gcd_mul_left, Nat.gcd_mul_left] at hgdef
    exact (Nat.mul_eq_left hg0.ne').mp hgdef
  by_contra hn
  have hAP : APLemma m a' x' := by
    rcases Nat.lt_or_ge 90 m with h90 | h90
    · exact hA m a' x' h90 hme hax' h2x' hxo' hao' h3' hg'
    · exact pf_sound (hpf m h90) hme hax' h2x' hxo' hao' h3' hg' (by simpa using hn)
  obtain ⟨d, hd⟩ := hAP
  exact hf (lift (by omega) hg0 hd)

/-! ## All-blocked lower halves: the enumeration -/

/-- Depth-first enumeration of lower halves: the candidates `x` (increasing) are each left
out, or admitted when `(a, x) ∈ F` (a progression failure) or `x − 2a` is already present. -/
def gen (a : ℕ) (F : List (ℕ × ℕ)) : List ℕ → Finset ℕ → List (Finset ℕ)
  | [], L => [L]
  | x :: xs, L => gen a F xs L ++
      (if F.contains (a, x) || decide (x - 2 * a ∈ L) then gen a F xs (insert x L) else [])

/-- Every all-blocked set is enumerated. -/
lemma gen_complete (a : ℕ) (F : List (ℕ × ℕ)) : ∀ (cs : List ℕ) (L0 T : Finset ℕ),
    cs.Pairwise (· < ·) → (∀ x ∈ T, x ∈ cs) →
    (∀ x ∈ T, F.contains (a, x) = true ∨ x - 2 * a ∈ L0 ∪ T) → (∀ x ∈ T, x - 2 * a < x) →
    L0 ∪ T ∈ gen a F cs L0
  | [], L0, T, _, hT, _, _ => by
    have : T = ∅ := Finset.eq_empty_of_forall_notMem (fun x hx => by simpa using hT x hx)
    subst this; simp [gen]
  | x :: xs, L0, T, hp, hT, hadm, hlt => by
    rw [List.pairwise_cons] at hp
    simp only [gen, List.mem_append]
    by_cases hxT : x ∈ T
    · right
      have hc : (F.contains (a, x) || decide (x - 2 * a ∈ L0)) = true := by
        rcases hadm x hxT with h | h
        · rw [h]; rfl
        · rcases Finset.mem_union.mp h with h | h
          · simp [h]
          · exfalso
            rcases List.mem_cons.mp (hT _ h) with h' | h'
            · have := hlt x hxT; omega
            · have := hp.1 _ h'; have := hlt x hxT; omega
      rw [if_pos hc]
      have e : L0 ∪ T = insert x L0 ∪ T.erase x := by
        ext y; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
        by_cases hy : y = x
        · subst hy; simp [hxT]
        · simp [hy]
      rw [e]
      refine gen_complete a F xs _ _ hp.2 ?_ ?_ ?_
      · intro y hy
        rcases List.mem_cons.mp (hT y (Finset.mem_of_mem_erase hy)) with h | h
        · exact absurd h (Finset.ne_of_mem_erase hy)
        · exact h
      · intro y hy; rw [← e]; exact hadm y (Finset.mem_of_mem_erase hy)
      · intro y hy; exact hlt y (Finset.mem_of_mem_erase hy)
    · left
      refine gen_complete a F xs _ _ hp.2 ?_ hadm hlt
      intro y hy
      rcases List.mem_cons.mp (hT y hy) with h | h
      · exact absurd (h ▸ hy) hxT
      · exact h

/-- The odd candidates `a < x < k/2`, increasing. -/
def cands (k a : ℕ) : List ℕ := (List.range k).filter (fun x => a < x && 2 * x < k && x % 2 == 1)

lemma cands_pairwise (k a : ℕ) : (cands k a).Pairwise (· < ·) :=
  List.Pairwise.filter _ (List.pairwise_lt_range)

/-- The support spanned by a lower half, with or without the middle element `k/2`. -/
def spanM (k : ℕ) (L : Finset ℕ) (mid : Bool) : Finset ℕ :=
  L ∪ L.image (fun x => k - x) ∪ (if mid then {k / 2} else ∅)

/-- The obligation at one enumerated lower half: the support it spans is one of the supports
of `tab:allodd-base`, or it satisfies (T) with some `d ∈ D`. -/
def LeafOK (k a : ℕ) (D : List ℕ) (L : Finset ℕ) : Prop :=
  ∀ mid ∈ [false, true], (mid = true → (k / 2) % 2 = 1) → 2 ≤ L.card →
    PerSupport.Prim k (spanM k L mid) →
      (k, spanM k L mid) ∈ AllOddBase.tabKS ∨ ∃ d ∈ D, E3 k (spanM k L mid) a d

instance (k a : ℕ) (D : List ℕ) (L : Finset ℕ) : Decidable (LeafOK k a D L) := by
  unfold LeafOK; infer_instance

/-- The base-case check at order `k` with failure table `FT` and multipliers `D`. -/
def BaseCheck (k : ℕ) (FT : List (ℕ × ℕ)) (D : List ℕ) : Prop :=
  ∀ a ∈ (List.range k).filter (fun a => 3 ≤ a && 2 * a < k && a % 2 == 1),
    ∀ L ∈ gen a FT (cands k a) {a}, LeafOK k a D L

instance (k : ℕ) (FT : List (ℕ × ℕ)) (D : List ℕ) : Decidable (BaseCheck k FT D) := by
  unfold BaseCheck; infer_instance

/-- Every odd pair `a < x < k/2` outside `FT` has a witness. -/
def ftCheck (k : ℕ) (FT : List (ℕ × ℕ)) : Bool :=
  (List.range k).all fun x => (List.range x).all fun a =>
    !(a % 2 == 1 && x % 2 == 1 && decide (2 * x < k)) || FT.contains (a, x) || apSearch k a x

lemma ft_sound {k a x : ℕ} {FT : List (ℕ × ℕ)} (h : ftCheck k FT = true) (hax : a < x)
    (h2x : 2 * x < k) (hxo : x % 2 = 1) (hao : a % 2 = 1) (hn : FT.contains (a, x) = false) :
    APLemma k a x := by
  have h1 := List.all_eq_true.mp h x (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 a (List.mem_range.mpr hax)
  rw [hn] at h2
  have hc : (a % 2 == 1 && x % 2 == 1 && decide (2 * x < k)) = true := by simp [hao, hxo, h2x]
  rw [hc] at h2
  exact apSearch_sound (by simpa using h2)

/-- A row of the base data: the order `k`, its failure table `F_k` and the multipliers `D_k`. -/
abbrev BaseRow := ℕ × List (ℕ × ℕ) × List ℕ

/-- Both checks of one row. -/
def rowCheck (r : BaseRow) : Bool := ftCheck r.1 r.2.1 && decide (BaseCheck r.1 r.2.1 r.2.2)

/-! ## From the checks to (T) at one order -/

open Shadow in
/-- An all-odd palindromic support is spanned by its lower half, with `k/2` when present. -/
lemma span_eq {k a : ℕ} {S : Finset ℕ} (hb : AllOddPal k S a) :
    S = spanM k (S.filter (fun y => 2 * y < k)) (decide (k / 2 ∈ S)) := by
  have hke := hb.even_k
  ext s
  simp only [spanM, Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  constructor
  · intro hs
    have hm := hb.mem s hs
    rcases lt_trichotomy (2 * s) k with h | h | h
    · exact Or.inl (Or.inl ⟨hs, h⟩)
    · right; rw [if_pos (by simp [show k / 2 = s by omega, hs])]; simp; omega
    · exact Or.inl (Or.inr ⟨k - s, ⟨hb.pal s hs, by omega⟩, by omega⟩)
  · rintro ((⟨hs, -⟩ | ⟨y, ⟨hy, -⟩, rfl⟩) | h)
    · exact hs
    · exact hb.pal y hy
    · by_cases hm : k / 2 ∈ S
      · rw [if_pos (by simp [hm])] at h; rw [Finset.mem_singleton.mp h]; exact hm
      · rw [if_neg (by simp [hm])] at h; simp at h

open Shadow in
/-- **The base case at one order.**  The two checks give (T) for every primitive all-odd
palindromic `S` with `1 ∉ S` and at least two elements below `k/2`, other than the supports of
`tab:allodd-base`. -/
theorem e3_of_checks {k : ℕ} {FT : List (ℕ × ℕ)} {D : List ℕ} (hft : ftCheck k FT = true)
    (hbc : BaseCheck k FT D) {S : Finset ℕ} {a : ℕ} (hb : AllOddPal k S a)
    (hP : PerSupport.Prim k S) (h1 : 1 ∉ S) (hL : ∃ x ∈ S, 2 * x < k ∧ x ≠ a) :
    (k, S) ∈ AllOddBase.tabKS ∨ ∃ d, E3 k S a d := by
  have hke := hb.even_k
  have hk := hb.k_pos
  have ha := hb.mem a hb.a_mem
  have hao := hb.odd a hb.a_mem
  obtain ⟨x₀, hx₀, hx₀2, hx₀a⟩ := hL
  have h2a := hb.two_a_lt hx₀ hx₀2.ne
  by_cases hne : ∃ x ∈ S, 2 * x < k ∧ x ≠ a ∧ FT.contains (a, x) = false ∧ x - 2 * a ∉ S
  · obtain ⟨x, hx, hx2, hxa, hF, h2⟩ := hne
    have hax : a < x := lt_of_le_of_ne (hb.a_min x hx) (Ne.symm hxa)
    obtain ⟨d, hd⟩ := ft_sound hft hax hx2 (hb.odd x hx) hao hF
    exact Or.inr ⟨d, aproute1 hb hx hx2 hxa h2 hd⟩
  push_neg at hne
  set L := S.filter (fun y => 2 * y < k) with hLdef
  have haL : a ∈ L := Finset.mem_filter.mpr ⟨hb.a_mem, h2a⟩
  have hgen : ({a} : Finset ℕ) ∪ L.erase a ∈ gen a FT (cands k a) {a} := by
    refine gen_complete a FT _ _ _ (cands_pairwise k a) ?_ ?_ ?_
    · intro y hy
      have hyL := Finset.mem_of_mem_erase hy
      have hyS := (Finset.mem_filter.mp hyL).1
      have := hb.a_min y hyS
      have := Finset.ne_of_mem_erase hy
      have := hb.odd y hyS
      have := (Finset.mem_filter.mp hyL).2
      simp only [cands, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq]
      refine ⟨by omega, ⟨by omega, (Finset.mem_filter.mp hyL).2⟩, by omega⟩
    · intro y hy
      have hyL := Finset.mem_of_mem_erase hy
      have hyS := (Finset.mem_filter.mp hyL).1
      by_cases hF : FT.contains (a, y) = true
      · exact Or.inl hF
      · right
        have hm := hne y hyS (Finset.mem_filter.mp hyL).2 (Finset.ne_of_mem_erase hy)
          (by simpa using hF)
        rw [Finset.mem_union, Finset.mem_singleton]
        by_cases hya : y - 2 * a = a
        · exact Or.inl hya
        · right
          refine Finset.mem_erase.mpr ⟨hya, Finset.mem_filter.mpr ⟨hm, ?_⟩⟩
          have := (Finset.mem_filter.mp hyL).2
          omega
    · intro y hy
      have := hb.mem y (Finset.mem_filter.mp (Finset.mem_of_mem_erase hy)).1
      omega
  rw [Finset.singleton_union, Finset.insert_erase haL] at hgen
  have ha3 : a ∈ (List.range k).filter (fun a => 3 ≤ a && 2 * a < k && a % 2 == 1) := by
    have : a ≠ 1 := fun h => h1 (h ▸ hb.a_mem)
    simp only [List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq]
    exact ⟨by omega, ⟨by omega, h2a⟩, hao⟩
  have hleaf := hbc a ha3 L hgen (decide (k / 2 ∈ S)) (by by_cases h : k / 2 ∈ S <;> simp [h])
    (by intro h; have := hb.odd _ (of_decide_eq_true h); exact this)
    (by
      have hxL : x₀ ∈ L := Finset.mem_filter.mpr ⟨hx₀, hx₀2⟩
      have : ({a, x₀} : Finset ℕ) ⊆ L := by
        intro y hy; rcases Finset.mem_insert.mp hy with rfl | hy
        · exact haL
        · rw [Finset.mem_singleton.mp hy]; exact hxL
      have hc := Finset.card_le_card this
      rw [Finset.card_pair (Ne.symm hx₀a)] at hc
      exact hc)
  rw [← span_eq hb] at hleaf
  rcases hleaf hP with h | ⟨d, -, hd⟩
  · exact Or.inl h
  · exact Or.inr ⟨d, hd⟩

end E3All
end Bump
end Trop
end PeriodicDifference
