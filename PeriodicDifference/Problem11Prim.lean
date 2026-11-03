/-
# `PeriodicDifference/Problem11Prim.lean` — the case walk of `thm:main` on primitive supports

Every primitive admissible globally periodic equation is a member (`TropMember`):
`|S| = 0`; `|S| = 1` (`K = 2`, `thm:order2`); `|S| = 2` (`thm:twoterm`, `TwoTerm.twoTerm`, and the
survivor `K = 3`, `thm:order3`); `|S| ≥ 3`: full support (`FS.not_globallyPeriodic`), odd `K`
(`thm:oddk`, `Trop.OddK.oddk_trop`), `(6, {1,3,5})` (`prop:order6cert`, `order6_135`), other
even `K` (`bump_even`, from Lemma A `lemmaA`, and `thm:sigmabump`).
-/
import PeriodicDifference.Problem11Small
import PeriodicDifference.Order6Cert
import PeriodicDifference.OddK
import PeriodicDifference.FullSupport
import PeriodicDifference.TwoTermFinal
import PeriodicDifference.AllOddAll
import PeriodicDifference.NotAllOdd
import PeriodicDifference.APLemmaMain

namespace PeriodicDifference
namespace Problem11

open Trop
open Trop.Bump.PerSupport (Pal Prim)

variable {K : ℕ} {J : List ℕ} {co : ℕ → ℝ}

/-- **Lemma A** (`thm:lemmaA`) at every even order `k > 90`, in the form `E3All.LemmaA`
(`APLemma.aplemma`). -/
theorem lemmaA : Trop.Bump.E3All.LemmaA := by
  intro k a x hk hke hax hxk hx ha h3 hcop
  exact Trop.Bump.APLemma.aplemma hk hke ha hx hax hxk h3 hcop

/-- **Every primitive support at even order other than the full one and `(6, {1,3,5})` carries a
σ-bump**: supports with an even element by `NotAllOdd.notallodd'`, all-odd supports by
`AllOddAll.alloddall` (from Lemma A). -/
theorem bump_even {k : ℕ} (hk : k % 2 = 0) {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc 1 (k - 1)) (hpal : Pal k S) (hprim : Prim k S) (hcard : 3 ≤ S.card)
    (hne : S ≠ Finset.Icc 1 (k - 1)) (h6 : ¬ (k = 6 ∧ S = {1, 3, 5})) :
    ∃ σ Q, Trop.Bump.BumpSat k S σ Q := by
  by_cases hev : ∃ s ∈ S, s % 2 = 0
  · exact Trop.Bump.NotAllOdd.notallodd' hk hsub hpal hprim hev hne
  · have hodd : ∀ j ∈ S, j % 2 = 1 := by
      intro j hj
      by_contra h
      exact hev ⟨j, hj, by omega⟩
    exact Trop.Bump.AllOddAll.alloddall lemmaA hk hsub hodd hpal hprim hcard h6

lemma supp_JS : ∀ j ∈ J, j = 0 ∨ j ∈ supp J := by
  intro j hj
  by_cases h0 : j = 0
  · exact Or.inl h0
  · exact Or.inr (mem_supp.mpr ⟨h0, hj⟩)

lemma supp_SJ : ∀ j ∈ supp J, j ∈ J := fun _ hj => (mem_supp.mp hj).2

/-- `|S| ≥ 3`: no primitive admissible equation is periodic. -/
theorem big_case (h : Admissible K J co) (hprim : Prim K (supp J)) (hcard : 3 ≤ (supp J).card)
    {p : ℕ} (hp : 0 < p) (hg : GloballyPeriodic K J co p) : False := by
  have hsub := h.supp_sub
  by_cases hne : supp J = Finset.Icc 1 (K - 1)
  · have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    obtain ⟨k', rfl⟩ : ∃ k', K = k' + 1 := ⟨K - 1, by omega⟩
    refine Trop.FS.not_globallyPeriodic (by omega) (fun j hj => ?_) (fun j hj1 hj2 => ?_)
      h.pos hp hg
    · have := h.lt j hj; omega
    · have hm : j ∈ supp J := by rw [hne, Finset.mem_Icc]; omega
      exact (mem_supp.mp hm).2
  by_cases hodd : K % 2 = 1
  · exact Trop.OddK.oddk_trop hodd hsub h.pal_supp hprim hcard hne supp_JS supp_SJ h.pos hp hg
  by_cases h6 : K = 6 ∧ supp J = {1, 3, 5}
  · obtain ⟨rfl, hs⟩ := h6
    exact order6_135 h hs hp hg
  obtain ⟨σ, Q, hbs⟩ := bump_even (by omega) hsub h.pal_supp hprim hcard hne h6
  exact Trop.Bump.not_globallyPeriodic_of_bumpSat hbs supp_JS supp_SJ h.pos hp hg

/-- `|S| = 2` with `S = {j, K − j}`, `2j < K`. -/
theorem pair_case (h : Admissible K J co) (hprim : Prim K (supp J))
    {j : ℕ} (hj0 : 0 < j) (hjK : 2 * j < K) (hs : supp J = {j, K - j})
    {p : ℕ} (hp : 0 < p) (hg : GloballyPeriodic K J co p) : TropMember K J co := by
  by_cases h3 : K = 3 * j
  · have hj1 : j = 1 := by
      refine eq_one_of_prim hprim (fun x hx => ?_) ⟨3, by rw [h3]; ring⟩
      rw [hs] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact dvd_refl _
      · rw [Finset.mem_singleton.mp hx, h3]; exact ⟨2, by omega⟩
    subst hj1
    have hK : K = 3 := by omega
    subst hK
    have hs' : supp J = {1, 2} := hs
    exact Or.inr (Or.inr ⟨1, rfl, hs', order3_case h hs' hp hg⟩)
  · exact (TwoTerm.twoTerm h hprim hj0 hjK h3 hs hp hg).elim

/-- **The primitive case walk.** -/
theorem prim_member (h : Admissible K J co) (hprim : Prim K (supp J))
    {p : ℕ} (hp : 0 < p) (hg : GloballyPeriodic K J co p) : TropMember K J co := by
  have hsub := h.supp_sub
  have hpal := h.pal_supp
  rcases Nat.lt_or_ge (supp J).card 3 with hc | hc
  swap
  · exact (big_case h hprim hc hp hg).elim
  interval_cases hcard : (supp J).card
  · exact Or.inl (Finset.card_eq_zero.mp hcard)
  · obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hcard
    have hsm : s ∈ supp J := hs ▸ Finset.mem_singleton_self s
    have hb := Finset.mem_Icc.mp (hsub hsm)
    have hKs : K - s = s := by have := hpal s hsm; rw [hs] at this; simpa using this
    have hs1 : s = 1 := by
      refine eq_one_of_prim hprim (fun x hx => ?_) ⟨2, by omega⟩
      rw [hs, Finset.mem_singleton] at hx; rw [hx]
    subst hs1
    have hK : K = 2 := by omega
    subst hK
    exact Or.inr (Or.inl ⟨1, rfl, hs, order2_case h hs hp hg⟩)
  · obtain ⟨s, t, hst, hs⟩ := Finset.card_eq_two.mp hcard
    have hsm : s ∈ supp J := by rw [hs]; simp
    have htm : t ∈ supp J := by rw [hs]; simp
    have hbs := Finset.mem_Icc.mp (hsub hsm)
    have hbt := Finset.mem_Icc.mp (hsub htm)
    have h1 := hpal s hsm
    have h2 := hpal t htm
    rw [hs, Finset.mem_insert, Finset.mem_singleton] at h1 h2
    have hsum : s + t = K := by omega
    rcases Nat.lt_or_gt_of_ne hst with hlt | hlt
    · refine pair_case h hprim (j := s) (by omega) (by omega) ?_ hp hg
      rw [hs, show K - s = t by omega]
    · refine pair_case h hprim (j := t) (by omega) (by omega) ?_ hp hg
      rw [hs, show K - t = s by omega, Finset.pair_comm]

end Problem11
end PeriodicDifference
