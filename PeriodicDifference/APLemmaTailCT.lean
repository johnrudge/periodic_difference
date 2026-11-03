/-
# `PeriodicDifference/APLemmaTailCT.lean` — the resonant case for every `k` (Prop 5 with the chord table)

The chord table `CT` (`ct80.txt`, directions with `g²|u|² ≤ 6400`) has worst ratio
`g / (2σ) ≤ 169.9` (`ct_ratio`, kernel-checked), so every entry is certified at order `k`
as soon as `JacOK (2k) J` and `1699 J < 10 k` (`cert_ct`).
-/
import PeriodicDifference.APLemmaTables
import PeriodicDifference.APLemmaTailBand

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ct_ratio : CT.all (fun ge => ge.2.all fun e =>
    decide (10*(ge.1:ℤ)*(e.b₀*e.b₁) ≤ 3398*(e.a₁*e.b₀ - e.a₀*e.b₁))) = true := by
  decide +kernel

/-- The resonant case: every table direction is certified once `1699 J < 10 k`. -/
theorem cert_ct {k J : ℕ} (hk : 0 < k) (hJ : JacOK (2*k) J) (hkJ : 1699*J < 10*k) :
    ∀ g p q : ℤ, 0 < g → g ∣ 2*k → (0 < p ∨ (p = 0 ∧ 0 < q)) → IsCoprime p q →
      2 ∣ g*q → g^2*(p^2+q^2) ≤ 6400 → ¬ ZeroEntry g p q → Cert k g p q := by
  intro g p q hg hgk hn hpq h2 hX hz
  obtain ⟨ge, hge, e, he, hge1, hp', hq'⟩ := exists_entry ct_complete hg hn hpq h2 hX hz
  obtain ⟨hc, hj⟩ := ceCheck_sound (hCT_all ge hge e he)
  have hrat := ct_ratio
  simp only [List.all_eq_true, decide_eq_true_eq] at hrat
  have hr := hrat ge hge e he
  have hb := hCT_all ge hge e he
  simp only [ceCheck, chordCheck, Bool.and_eq_true, decide_eq_true_eq] at hb
  have hb₀ : 0 < e.b₀ := hb.1.1.1.2
  have hb₁ : 0 < e.b₁ := hb.1.1.2
  obtain ⟨nn, hJac, hnn, hng, hcov⟩ := exists_nn hk hJ g
  rw [← hp', ← hq', ← hge1]
  rw [← hge1] at hng hcov
  left
  refine ⟨e.j, e.t, e.m, e.n, _, _, nn, J, hj, hc, hJac, hnn, hng, hcov, ?_⟩
  have hb₀' : (0:ℚ) < e.b₀ := by exact_mod_cast hb₀
  have hb₁' : (0:ℚ) < e.b₁ := by exact_mod_cast hb₁
  have hσ : (0:ℤ) < e.a₁*e.b₀ - e.a₀*e.b₁ := by
    have : (0:ℤ) < 10*(ge.1:ℤ)*(e.b₀*e.b₁) := by
      have : (0:ℤ) < ge.1 := by rw [hge1]; exact hg
      positivity
    linarith
  have h3 : ((J:ℤ)*ge.1*(e.b₀*e.b₁) : ℤ) < 2*k*(e.a₁*e.b₀ - e.a₀*e.b₁) := by
    have hJ0 : (0:ℤ) ≤ J := by positivity
    have : (10:ℤ)*(J*ge.1*(e.b₀*e.b₁)) ≤ J*(3398*(e.a₁*e.b₀ - e.a₀*e.b₁)) := by
      have := mul_le_mul_of_nonneg_left hr hJ0; linarith
    have hk' : (1699:ℤ)*J < 10*k := by exact_mod_cast hkJ
    nlinarith
  have h3' : (((J:ℤ)*ge.1*(e.b₀*e.b₁) : ℤ) : ℚ) < ((2*k*(e.a₁*e.b₀ - e.a₀*e.b₁) : ℤ) : ℚ) := by
    exact_mod_cast h3
  rw [div_sub_div _ _ hb₁'.ne' hb₀'.ne', mul_div_assoc', lt_div_iff₀ (by positivity)]
  push_cast at h3' ⊢
  linarith

end APLemma
end Bump
end Trop
end PeriodicDifference
