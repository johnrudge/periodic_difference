/-
# `PeriodicDifference/APLemmaTailMain.lean` — `prop:lemmaA-tail` at one order, from two Jacobsthal bounds

At an even order `k` with `JacOK (2k) J`, `178 J² ≤ 10 k` and `1699 J < 10 k`
(`good_of_jac`), for a shortest vector `g u` of `Λ(a, e)`:
* `g²|u|² ≤ 6400`: the chord table (`cert_ct`), needing `1699 J < 10 k`;
* `g²|u|² > 6400`: `prop:lemmaA-band` (`band_chord`), needing `J_g ≤ 8` or `J_g < 0.102 g`
  (`JacG`, `cor:lemmaA-jac`(b)) and `178 J² ≤ 10 k` (with Hermite's bound
  `3 (g²|u|²)² ≤ 16 k²`).

Every even `k > 2730` satisfies both bounds (`cor:lemmaA-jac`(a), `APLemmaTailFinal`); so do
890 of the orders `92 ≤ k ≤ 2730`, with `J` from the table (C2) (`APLemmaFinite`).
-/
import PeriodicDifference.APLemmaTailCT

namespace PeriodicDifference
namespace Trop
namespace Bump
namespace APLemma

/-- A Jacobsthal bound for `2k` good enough for (4.3): `17.8 J² ≤ k`. -/
def JacTail : Prop :=
  ∀ k : ℕ, 2730 < k → k % 2 = 0 → ∃ J : ℕ, JacOK (2*k) J ∧ 178*J^2 ≤ 10*k

/-- A Jacobsthal bound for `g` good enough for (4.2) outside the chord table. -/
def JacG : Prop :=
  ∀ g : ℕ, 0 < g → ∃ Jg : ℕ, JacOK g Jg ∧ (Jg ≤ 8 ∨ 1000*Jg < 102*g)

/-- Prop 4 as a certificate. -/
theorem cert_band {k J Jg ng : ℕ} {g p q : ℤ} (hk : 0 < k) (hg : 0 < g) (hngg : (ng:ℤ) = g)
    (hJg : JacOK ng Jg) (hJ : JacOK (2*k) J) (hU : 0 < p^2+q^2)
    (hband : (Jg:ℤ)^2 * 10^6 < 10404 * (g^2*(p^2+q^2)))
    (hchord : (J:ℤ)^2 * (g^2*(p^2+q^2)) * 10^6 < 129780 * (k:ℤ)^2) : Cert k g p q := by
  obtain ⟨j, s₀, s₁, hj, hc, hlen⟩ := band_chord hg hngg hJg hU hband hchord
  obtain ⟨nn, hJac, hnn, hng, hcov⟩ := exists_nn hk hJ g
  exact Or.inl ⟨j, 0, 0, 0, s₀, s₁, nn, J, hj, hc, hJac, hnn, hng, hcov, hlen⟩

/-- `thm:lemmaA` at every even order `k > 2730` (`prop:lemmaA-tail`); proved as `tailHyp` in
`PeriodicDifference/APLemmaTailFinal.lean`. -/
def TailHyp : Prop :=
  ∀ k : ℕ, 2730 < k → k % 2 = 0 → ∀ a e : ℤ, Adm k a e → Good k a e

/-- **`prop:lemmaA-tail` at one order.**  If `J(2k) ≤ J` with `178 J² ≤ 10 k` and
`1699 J < 10 k`, every admissible pair at order `k` has a witness. -/
theorem good_of_jac (hG : JacG) {k J : ℕ} (hJ : JacOK (2*k) J) (hJk : 178*J^2 ≤ 10*k)
    (hkJ : 1699*J < 10*k) {a e : ℤ} (hadm : Adm k a e) : Good k a e := by
  have hk0 : 0 < k := by omega
  apply good_of_cert hadm
  intro g p q hg hgk hn hpq h2 hH hz
  rcases le_or_gt (g^2*(p^2+q^2)) 6400 with hX | hX
  · exact cert_ct hk0 hJ hkJ g p q hg hgk hn hpq h2 hX hz
  · have hU : 0 < p^2 + q^2 := by rcases hn with h0 | ⟨_, h0⟩ <;> positivity
    obtain ⟨Jg, hJg, hJg'⟩ := hG g.toNat (by omega)
    refine cert_band hk0 hg (Int.toNat_of_nonneg hg.le) hJg hJ hU ?_ ?_
    · rcases hJg' with h8 | h8
      · have : (Jg:ℤ) ≤ 8 := by exact_mod_cast h8
        have : (Jg:ℤ)^2 ≤ 64 := by nlinarith [Int.natCast_nonneg Jg]
        nlinarith
      · have h8' : (1000:ℤ)*Jg < 102*g := by
          have := Int.toNat_of_nonneg hg.le
          have h' : ((1000*Jg : ℕ) : ℤ) < ((102*g.toNat : ℕ) : ℤ) := by exact_mod_cast h8
          push_cast at h'; rw [this] at h'; exact h'
        have hJ0 : (0:ℤ) ≤ Jg := by positivity
        have : (Jg:ℤ)^2 * 10^6 < 10404 * g^2 := by nlinarith
        nlinarith
    · -- (4.3) from Hermite and `178 J² ≤ 10 k`
      set L : ℤ := g^2*(p^2+q^2) with hL
      have hL0 : 0 ≤ L := by positivity
      have hJk' : (178:ℤ)*J^2 ≤ 10*k := by exact_mod_cast hJk
      have hkz : (0:ℤ) < k := by exact_mod_cast hk0
      have hx0 : (0:ℤ) ≤ (J:ℤ)^2 := by positivity
      have hsq : ((J:ℤ)^2 * L * 10^6)^2 < (129780 * (k:ℤ)^2)^2 := by
        have e1 : ((J:ℤ)^2 * L * 10^6)^2 = ((J:ℤ)^2)^2 * L^2 * 10^12 := by ring
        have a1 : (178*(J:ℤ)^2)^2 ≤ (10*k)^2 := by
          exact pow_le_pow_left₀ (by positivity) hJk' 2
        have a2 : ((J:ℤ)^2)^2 * (3*L^2) ≤ ((J:ℤ)^2)^2 * (16*k^2) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
        have a3 : ((J:ℤ)^2)^2 * (16*k^2) * 31684 ≤ (100*k^2) * (16*k^2) := by
          have := mul_le_mul_of_nonneg_right a1 (show (0:ℤ) ≤ 16*k^2 by positivity)
          nlinarith
        have hk4 : (0:ℤ) < k^4 := by positivity
        nlinarith
      have hR : (0:ℤ) ≤ 129780 * (k:ℤ)^2 := by positivity
      exact lt_of_pow_lt_pow_left₀ 2 hR hsq

end APLemma
end Bump
end Trop
end PeriodicDifference
