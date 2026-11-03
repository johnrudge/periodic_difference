/-
# `PeriodicDifference/E3All.lean` — the three-point condition (`thm:allodd-e3all`)

`lem:allodd-aproute` (`aproute1` in `E3AllDefs`, `aproute2` here), `lem:allodd-nofail`
(`nofail`) and `thm:allodd-e3all` (`e3all`), with Lemma A (`thm:lemmaA`) at every even order
`k > 90` as the explicit hypothesis `hA : LemmaA`.  The corollary `bumpSat_e3all` feeds
`E3Suff.bumpSat_halfQ` (`prop:allodd-e3bump`): every such support carries the half-arc carrier
`halfQ k S a d t`, `t ∈ {0, k}`.

Route for `k > 90`, as in the paper: if some `x ∈ L ∖ {a}` has a progression witness and
`x − 2a ∉ S`, `aproute1`.  Otherwise, unless `(k, a) = (120, 15)`, `lem:allodd-nofail` gives a
witness for every `x ∈ L ∖ {a, 3a}` (a failure would be the lift of a primitive failure at an order
`≤ 90`, `pf_of_fail`, and then primitivity forces `ell k a = k`, which the ratio classes of the
failure table exclude, `lift_count`); so `L` is the chain `a, 3a, 5a, …` (`aproute2`), and Lemma A
at `(k; 1, 2m + 3)`, scaled by `a⁻¹`, gives the three-point condition (T).  At `(k, a) = (120, 15)`
the lower half lies in `{15, 35, 45, 51}`, and contains `35` and `51` by primitivity; the unit `11`
satisfies (T) (`e3_120`).  The orders `k ≤ 90` are the base check `base_e3`
(`PeriodicDifference/E3AllBase.lean`), whose exceptions are the supports of `tab:allodd-base`.
-/
import PeriodicDifference.E3AllBase
import PeriodicDifference.E3AllLift
import PeriodicDifference.E3AllPF0
import PeriodicDifference.E3AllPF1
import PeriodicDifference.E3AllPF2
import PeriodicDifference.E3AllPF3
import PeriodicDifference.E3AllPF4
import PeriodicDifference.E3AllPF5

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace E3All

open Finset Shadow

/-- The failure table is complete at every even order `≤ 90`. -/
theorem pf_all : ∀ m ≤ 90, pfCheck m = true := by
  intro m hm
  rcases Nat.lt_or_ge m 50 with h | h
  · exact List.all_eq_true.mp pf_0 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  rcases Nat.lt_or_ge m 62 with h' | h'
  · exact List.all_eq_true.mp pf_1 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  rcases Nat.lt_or_ge m 72 with h'' | h''
  · exact List.all_eq_true.mp pf_2 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  rcases Nat.lt_or_ge m 80 with h3 | h3
  · exact List.all_eq_true.mp pf_3 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  rcases Nat.lt_or_ge m 86 with h4 | h4
  · exact List.all_eq_true.mp pf_4 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact List.all_eq_true.mp pf_5 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

/-- An odd common divisor of `k` and of the lower half of a primitive all-odd palindromic `S`
is `1`. -/
lemma prim_dvd {k a e : ℕ} {S : Finset ℕ} (hb : AllOddPal k S a) (hP : PerSupport.Prim k S)
    (he : ∀ y ∈ S, 2 * y < k → e ∣ y) (heo : e % 2 = 1) (hek : e ∣ k) : e = 1 := by
  have hall : ∀ y ∈ S, e ∣ y := by
    intro y hy
    have hm := hb.mem y hy
    rcases lt_trichotomy (2 * y) k with h | h | h
    · exact he y hy h
    · have hc : Nat.Coprime e 2 :=
        Nat.coprime_comm.mp (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))
      exact hc.dvd_of_dvd_mul_left (by rw [h]; exact hek)
    · have := he (k - y) (hb.pal y hy) (by omega)
      have h2 := Nat.dvd_sub hek this
      rwa [Nat.sub_sub_self hm.2.le] at h2
  have h1 : e ∣ Nat.gcd (S.gcd id) k := Nat.dvd_gcd (Finset.dvd_gcd fun y hy => hall y hy) hek
  rw [hP] at h1
  exact Nat.dvd_one.mp h1

/-- **`lem:allodd-aproute`, second part.**  If every `x ∈ L ∖ {a}` has `x − 2a ∈ S`, then
`gcd(a, k) = 1` and `L ⊇ {a, 3a, …, (2m+1)a}` with `m ≥ 1`, `2(2m+1)a < k`, and
`(2m+3)a ∉ S`. -/
lemma aproute2 {k a : ℕ} {S : Finset ℕ} (hb : AllOddPal k S a) (hP : PerSupport.Prim k S)
    (h1 : 1 ∉ S) (hall : ∀ x ∈ S, 2 * x < k → x ≠ a → x - 2 * a ∈ S)
    (hL : ∃ x ∈ S, 2 * x < k ∧ x ≠ a) :
    Nat.Coprime a k ∧ ∃ m, 1 ≤ m ∧ 2 * ((2 * m + 1) * a) < k ∧
      (∀ i ≤ m, (2 * i + 1) * a ∈ S) ∧ (2 * m + 3) * a ∉ S := by
  have ha := hb.mem a hb.a_mem
  have hao := hb.odd a hb.a_mem
  have ha3 : 3 ≤ a := by
    have : a ≠ 1 := fun h => h1 (h ▸ hb.a_mem)
    omega
  have hmod : ∀ y, y ∈ S → 2 * y < k → y % (2 * a) = a := by
    intro y
    induction y using Nat.strong_induction_on with
    | _ y ih =>
      intro hy hy2
      by_cases hya : y = a
      · subst hya; exact Nat.mod_eq_of_lt (by omega)
      · have h := hall y hy hy2 hya
        have hpos := (hb.mem _ h).1
        have := ih (y - 2 * a) (by omega) h (by omega)
        rw [show y = (y - 2 * a) + 2 * a by omega, Nat.add_mod_right]
        exact this
  have hdiv : ∀ y ∈ S, 2 * y < k → a ∣ y := by
    intro y hy hy2
    have h := Nat.div_add_mod y (2 * a)
    rw [hmod y hy hy2] at h
    exact ⟨2 * (y / (2 * a)) + 1, by linarith⟩
  have hcop : Nat.Coprime a k := by
    refine prim_dvd hb hP (fun y hy hy2 => (Nat.gcd_dvd_left a k).trans (hdiv y hy hy2)) ?_
      (Nat.gcd_dvd_right a k)
    rcases Nat.mod_two_eq_zero_or_one (Nat.gcd a k) with h | h
    · have := (Nat.dvd_of_mod_eq_zero h).trans (Nat.gcd_dvd_left a k); omega
    · exact h
  refine ⟨hcop, ?_⟩
  obtain ⟨x₀, hx₀, hx₀2, hx₀a⟩ := hL
  set L := S.filter (fun y => 2 * y < k) with hLdef
  have hx₀L : x₀ ∈ L := Finset.mem_filter.mpr ⟨hx₀, hx₀2⟩
  set M := L.max' ⟨x₀, hx₀L⟩ with hMdef
  have hML : M ∈ L := L.max'_mem _
  have hMS := (Finset.mem_filter.mp hML).1
  have hM2 := (Finset.mem_filter.mp hML).2
  have hx₀M : x₀ ≤ M := L.le_max' x₀ hx₀L
  have hx₀gt : a < x₀ := lt_of_le_of_ne (hb.a_min x₀ hx₀) (Ne.symm hx₀a)
  have hMe := Nat.div_add_mod M (2 * a)
  rw [hmod M hMS hM2] at hMe
  set m := M / (2 * a) with hmdef
  have hMm : (2 * m + 1) * a = M := by rw [← hMe]; ring
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hMe; omega
    · exact h
  have hchain : ∀ j i, i + j = m → (2 * i + 1) * a ∈ S := by
    intro j
    induction j with
    | zero => intro i hi; rw [show i = m by omega, hMm]; exact hMS
    | succ j ih =>
      intro i hi
      have h := ih (i + 1) (by omega)
      have hle : (2 * (i + 1) + 1) * a ≤ M := by
        rw [← hMm]; exact Nat.mul_le_mul_right _ (by omega)
      have e : (2 * (i + 1) + 1) * a = (2 * i + 1) * a + 2 * a := by ring
      have h' := hall _ h (by omega) (by rw [e]; nlinarith)
      rwa [e, Nat.add_sub_cancel] at h'
  refine ⟨m, hm1, by rw [hMm]; exact hM2, fun i hi => hchain (m - i) i (by omega), ?_⟩
  intro hy
  have e : (2 * m + 3) * a = M + 2 * a := by rw [← hMm]; ring
  rw [e] at hy
  have hyk := (hb.mem _ hy).2
  have hak : ¬ a ∣ k := fun h => by have := Nat.Coprime.eq_one_of_dvd hcop h; omega
  rcases lt_trichotomy (2 * (M + 2 * a)) k with h | h | h
  · have := L.le_max' _ (Finset.mem_filter.mpr ⟨hy, h⟩); omega
  · exact hak ⟨2 * (2 * m + 3), by rw [← h, ← e]; ring⟩
  · have hz := hdiv (k - (M + 2 * a)) (hb.pal _ hy) (by omega)
    have hyd : a ∣ M + 2 * a := ⟨2 * m + 3, by rw [← e]; ring⟩
    have := Nat.dvd_add hz hyd
    rw [Nat.sub_add_cancel hyk.le] at this
    exact hak this

/-- The order `k / g` of a lifted failure is admissible for `a`. -/
lemma adm_of_fail (hA : LemmaA) {k a x : ℕ} (hk : 90 < k) (he : k % 2 = 0) (hax : a < x)
    (h2x : 2 * x < k) (hxo : x % 2 = 1) (hao : a % 2 = 1) (h3 : x ≠ 3 * a)
    (hf : ¬ APLemma k a x) :
    k / Nat.gcd (Nat.gcd a x) k ∈ admL k a ∧
      k / (k / Nat.gcd (Nat.gcd a x) k) = Nat.gcd (Nat.gcd a x) k := by
  have hPF := pf_of_fail hA pf_all hk he hax h2x hxo hao h3 hf
  have hgk : Nat.gcd (Nat.gcd a x) k ∣ k := Nat.gcd_dvd_right _ _
  have hga : Nat.gcd (Nat.gcd a x) k ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hkk := Nat.div_div_self hgk (by omega)
  refine ⟨?_, hkk⟩
  simp only [admL, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq]
  refine ⟨_, ⟨List.contains_iff_mem.mp hPF, ?_, ?_⟩, rfl⟩
  · exact Nat.mod_eq_zero_of_dvd (Nat.div_dvd_of_dvd hgk)
  · simp only [hkk]; exact (Nat.mul_div_cancel' hga).symm

/-- Negation flips the half for odd phases: `H_c(2k − y) ≠ H_c(y)` for odd `c`, `y`. -/
lemma eps_neg {k c y : ℕ} (he : k % 2 = 0) (hk : 0 < k) (hc : c % 2 = 1) (hy : y % 2 = 1)
    (hyk : y < 2 * k) :
    c * (2 * k - y) % (2 * k) < k ↔ ¬ c * y % (2 * k) < k := by
  have hu := phase_odd (k := k) hc (show (2 * k - y) % 2 = 1 by omega)
  have hr := phase_odd (k := k) hc hy
  have hu2 := Nat.mod_lt (c * (2 * k - y)) (show 0 < 2 * k by omega)
  have hr2 := Nat.mod_lt (c * y) (show 0 < 2 * k by omega)
  have hsum : (c * (2 * k - y) % (2 * k) + c * y % (2 * k)) % (2 * k) = 0 := by
    rw [← Nat.add_mod, ← Nat.mul_add, Nat.sub_add_cancel hyk.le, Nat.mul_comm,
      Nat.mul_mod_right]
  obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hsum
  have ht1 : t = 1 := by
    rcases t with _ | _ | t
    · omega
    · rfl
    · nlinarith
  subst ht1
  omega

/-- **`lem:allodd-nofail`.**  At even `k > 90`, `(k, a) ≠ (120, 15)`: if every `x ∈ L ∖ {a}` with a
progression witness has `x − 2a ∈ S`, then every `x ∈ L ∖ {a, 3a}` has a witness. -/
lemma nofail (hA : LemmaA) {k a : ℕ} {S : Finset ℕ} (h90 : 90 < k) (h120 : ¬ (k = 120 ∧ a = 15))
    (hb : AllOddPal k S a) (hP : PerSupport.Prim k S)
    (hc1 : ∀ x ∈ S, 2 * x < k → x ≠ a → APLemma k a x → x - 2 * a ∈ S) :
    ∀ x ∈ S, 2 * x < k → x ≠ a → x ≠ 3 * a → APLemma k a x := by
  intro x hx hx2 hxa h3
  by_contra hf
  have he := hb.even_k
  have hao := hb.odd a hb.a_mem
  have h2a := hb.two_a_lt hx hx2.ne
  have hax : a < x := lt_of_le_of_ne (hb.a_min x hx) (Ne.symm hxa)
  obtain ⟨hmx, hkx⟩ := adm_of_fail hA h90 he hax hx2 (hb.odd x hx) hao h3 hf
  obtain ⟨e, hke⟩ := ell_dvd_k (k := k) (a := a)
  have hediv : ∀ m ∈ admL k a, e ∣ k / m := by
    intro m hm
    obtain ⟨r, hr⟩ := dvd_foldr_lcm hm
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · have := (mem_admL hm).1; rw [h, Nat.mod_zero] at this; omega
      · exact h
    have hr' : ell k a = m * r := hr
    have : k / m = r * e := by
      rw [hke, hr', mul_assoc, Nat.mul_div_cancel_left _ hm0]
    rw [this]; exact dvd_mul_left e r
  have hea : e ∣ a := by
    obtain ⟨-, a', ha'⟩ := mem_admL hmx
    rw [ha']; exact (hediv _ hmx).trans (dvd_mul_right _ _)
  have hey : ∀ y, y ∈ S → 2 * y < k → e ∣ y := by
    intro y
    induction y using Nat.strong_induction_on with
    | _ y ih =>
      intro hy hy2
      by_cases hya : y = a
      · rw [hya]; exact hea
      have hay : a < y := lt_of_le_of_ne (hb.a_min y hy) (Ne.symm hya)
      by_cases hAP : APLemma k a y
      · have h := hc1 y hy hy2 hya hAP
        have hpos := (hb.mem _ h).1
        have := ih (y - 2 * a) (by omega) h (by omega)
        rw [show y = (y - 2 * a) + 2 * a by omega]
        exact Nat.dvd_add this (hea.mul_left 2)
      by_cases hy3 : y = 3 * a
      · rw [hy3]; exact hea.mul_left 3
      obtain ⟨hmy, hky⟩ := adm_of_fail hA h90 he hay hy2 (hb.odd y hy) hao hy3 hAP
      have := hediv _ hmy
      rw [hky] at this
      exact this.trans ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
  have heo : e % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one e with h | h
    · have := (Nat.dvd_of_mod_eq_zero h).trans hea; omega
    · exact h
  have he1 := prim_dvd hb hP hey heo ⟨ell k a, hke.trans (mul_comm _ _)⟩
  rw [he1, mul_one] at hke
  exact h120 (lift_count (List.contains_iff_mem.mp (pf_of_fail hA pf_all h90 he hax hx2
    (hb.odd x hx) hao h3 hf)) h90
    (Nat.mod_eq_zero_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)))
    (by simp only [hkx]; exact (Nat.mul_div_cancel'
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))).symm) hke.symm)

/-- The lifted failures `(120; 15, y)`, `y ≠ 45`: only `y = 35` (from `(24; 3, 7)`) and `y = 51`
(from `(40; 5, 17)`). -/
def fail120 : Bool :=
  (List.range 60).all fun y => !PF.contains (120 / Nat.gcd (Nat.gcd 15 y) 120,
    15 / Nat.gcd (Nat.gcd 15 y) 120, y / Nat.gcd (Nat.gcd 15 y) 120) || y == 35 || y == 51

theorem fail120_true : fail120 = true := by decide +kernel

/-- **`thm:allodd-e3all` at `(k, a) = (120, 15)`.**  If route (i) of `lem:allodd-aproute` is
available for no `x`, the lower half lies in `{15, 35, 45, 51}` and contains `35` and `51`, and the
unit `11` satisfies (T). -/
lemma e3_120 (hA : LemmaA) {k a : ℕ} {S : Finset ℕ} (hka : k = 120 ∧ a = 15)
    (hb : AllOddPal k S a) (hP : PerSupport.Prim k S)
    (hc1 : ∀ x ∈ S, 2 * x < k → x ≠ a → APLemma k a x → x - 2 * a ∈ S) : ∃ d, E3 k S a d := by
  obtain ⟨rfl, rfl⟩ := hka
  have hL : ∀ y, y ∈ S → 2 * y < 120 → y = 15 ∨ y = 35 ∨ y = 45 ∨ y = 51 := by
    intro y
    induction y using Nat.strong_induction_on with
    | _ y ih =>
      intro hy hy2
      by_cases hya : y = 15
      · exact Or.inl hya
      by_cases hy3 : y = 45
      · exact Or.inr (Or.inr (Or.inl hy3))
      have hay : 15 < y := lt_of_le_of_ne (hb.a_min y hy) (Ne.symm hya)
      by_cases hAP : APLemma 120 15 y
      · have h := hc1 y hy hy2 hya hAP
        have hpos := (hb.mem _ h).1
        have := ih (y - 2 * 15) (by omega) h (by omega)
        omega
      · have hPF := pf_of_fail hA pf_all (by norm_num) (by norm_num) hay hy2 (hb.odd y hy)
          (by norm_num) (by omega) hAP
        have hc := List.all_eq_true.mp fail120_true y (List.mem_range.mpr (by omega))
        simp only [hPF, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hc
        omega
  have h35 : 35 ∈ S := by
    by_contra h
    have := prim_dvd (e := 3) hb hP (fun y hy hy2 => by
      rcases hL y hy hy2 with rfl | rfl | rfl | rfl
      · norm_num
      · exact absurd hy h
      · norm_num
      · norm_num) (by norm_num) (by norm_num)
    omega
  have h51 : 51 ∈ S := by
    by_contra h
    have := prim_dvd (e := 5) hb hP (fun y hy hy2 => by
      rcases hL y hy hy2 with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · exact absurd hy h) (by norm_num) (by norm_num)
    omega
  refine ⟨11, by norm_num, ⟨51, h51, by norm_num, by norm_num, by decide⟩, ?_⟩
  by_cases h45 : 45 ∈ S
  · refine ⟨85, by simpa using hb.pal 35 h35, by norm_num, ?_, by decide⟩
    intro h115
    have := hb.a_min _ (hb.pal _ (show (2 * 15 + 85) % 120 ∈ S from h115))
    norm_num at this
  · exact ⟨15, hb.a_mem, by norm_num, by simpa using h45, by decide⟩

/-- **`thm:allodd-e3all`.**  Given Lemma A above `90`: every primitive palindromic all-odd `S`
at even `k` with `1 ∉ S` and at least two elements below `k/2`, not one of the supports of
`tab:allodd-base`, has a unit `d` satisfying the three-point condition (T) (`E3`). -/
theorem e3all (hA : LemmaA) {k a : ℕ} {S : Finset ℕ} (hb : AllOddPal k S a)
    (hP : PerSupport.Prim k S) (h1 : 1 ∉ S) (hL : ∃ x ∈ S, 2 * x < k ∧ x ≠ a)
    (hT : (k, S) ∉ AllOddBase.tabKS) : ∃ d, E3 k S a d := by
  by_cases hbase : k ≤ 90
  · exact (base_e3 hbase hb hP h1 hL).resolve_left hT
  have h90 : 90 < k := by omega
  have he := hb.even_k
  have hao := hb.odd a hb.a_mem
  have ha3 : 3 ≤ a := by
    have : a ≠ 1 := fun h => h1 (h ▸ hb.a_mem)
    have := hb.mem a hb.a_mem
    omega
  by_cases hc1 : ∃ x ∈ S, 2 * x < k ∧ x ≠ a ∧ APLemma k a x ∧ x - 2 * a ∉ S
  · obtain ⟨x, hx, hx2, hxa, ⟨d, hd⟩, h2⟩ := hc1
    exact ⟨d, aproute1 hb hx hx2 hxa h2 hd⟩
  push_neg at hc1
  by_cases h120 : k = 120 ∧ a = 15
  · exact e3_120 hA h120 hb hP hc1
  have hnf := nofail hA h90 h120 hb hP hc1
  have hall : ∀ x ∈ S, 2 * x < k → x ≠ a → x - 2 * a ∈ S := by
    intro x hx hx2 hxa
    by_cases h3 : x = 3 * a
    · rw [h3, show 3 * a - 2 * a = a by omega]; exact hb.a_mem
    · exact hc1 x hx hx2 hxa (hnf x hx hx2 hxa h3)
  obtain ⟨hcop, m, hm, hM, hchain, hnot⟩ := aproute2 hb hP h1 hall hL
  have h3M : 3 * a ≤ (2 * m + 1) * a := Nat.mul_le_mul_right _ (by omega)
  have h6 : 6 * (2 * m + 1) < k := by nlinarith
  -- Lemma A at `(k; 1, 2m + 3)`
  obtain ⟨c, hc, hc1', hc2'⟩ := hA k 1 (2 * m + 3) h90 he (by omega) (by omega) (by omega)
    rfl (by omega) (by simp)
  have hco : c % 2 = 1 := E3Suff.odd_of_unit hc
  rw [mul_one] at hc1' hc2'
  rw [show (2 * 1 + 2 * k - (2 * m + 3)) % (2 * k) = 2 * k - (2 * m + 1) by
    rw [Nat.mod_eq_of_lt (by omega)]; omega, eps_neg he (by omega) hco (by omega) (by omega)]
    at hc1'
  -- scale by `a⁻¹`
  have hcop2 : Nat.Coprime a (2 * k) :=
    Nat.Coprime.mul_right (Nat.coprime_comm.mp
      (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))) hcop
  obtain ⟨a', -, ha'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop2 (by omega)
  have hscale : ∀ n, c * a' * (n * a) % (2 * k) = c * n % (2 * k) := by
    intro n
    rw [show c * a' * (n * a) = c * n * (a * a') by ring, Nat.mul_mod, ha', mul_one,
      Nat.mod_mod]
  have hda : c * a' * a % (2 * k) = c % (2 * k) := by simpa using hscale 1
  have hd : Nat.Coprime (c * a') (2 * k) :=
    Nat.Coprime.mul_left hc (Nat.coprime_of_mul_modEq_one a (by
      rw [Nat.ModEq, mul_comm, ha', Nat.mod_eq_of_lt (by omega)]))
  refine ⟨c * a', hd, ⟨(2 * m + 1) * a, hchain m le_rfl, hM, by omega, ?_⟩,
    ⟨(2 * m + 1) * a, hchain m le_rfl, by omega, ?_, ?_⟩⟩
  · rw [hscale, hda]; rw [mul_one] at hc1'; tauto
  · rw [show 2 * a + (2 * m + 1) * a = (2 * m + 3) * a by ring, Nat.mod_eq_of_lt (by nlinarith)]
    exact hnot
  · rw [show 2 * a + (2 * m + 1) * a = (2 * m + 3) * a by ring, hscale, hda]; exact hc2'

/-- **The corollary** (`thm:allodd-e3all` with `prop:allodd-e3bump`).  Every primitive
palindromic all-odd `S` at even `k` with `1 ∉ S` and at least two elements below `k/2`, not in
`tab:allodd-base`, carries a half-arc carrier `halfQ k S a d t` with `σ = a = min S`. -/
theorem bumpSat_e3all (hA : LemmaA) {k a : ℕ} {S : Finset ℕ}
    (hb : AllOddPal k S a) (hP : PerSupport.Prim k S) (h1 : 1 ∉ S)
    (hL : ∃ x ∈ S, 2 * x < k ∧ x ≠ a) (hT : (k, S) ∉ AllOddBase.tabKS) :
    ∃ d t, BumpSat k S a (HalfArc.halfQ k S a d t) := by
  obtain ⟨d, hd, hx, hy⟩ := e3all hA hb hP h1 hL hT
  obtain ⟨t, -, h⟩ := E3Suff.bumpSat_halfQ hb hd hx hy
  exact ⟨d, t, h⟩

end E3All
end Bump
end Trop
end PeriodicDifference
