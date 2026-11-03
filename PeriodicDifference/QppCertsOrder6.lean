/-
# `PeriodicDifference/QppCertsOrder6.lean` — the order-6 tied-carrier certificate

One certificate `Cert6.cert θ` for the support `{1, 3, 5}` at order 6, for both `θ`
(`prop:order6cert`, `tab:trop-cert`; used in `PeriodicDifference/Order6Cert.lean`): the exponent window
`E0 = (−1, 0, −1, 0, 0, −1)` returns after `q = 15` steps, the affine pair `(V, W)` drifts by
`W`, and the same word serves both `θ` — when `θ = 1` the constant slot `0` attains the minimum
at three steps of the period but is never the designated slot, and its weak margins hold.  With
its `decide` check and the instantiated non-periodicity theorems (Theorem Q″,
`not_tropPeriodic_of_certPP` and `not_globallyPeriodic_of_certPP`, `PeriodicDifference/TropicalQpp.lean`)
for every slot list with the certificate's members.
-/

import PeriodicDifference.TropicalQpp

namespace PeriodicDifference
namespace Trop
namespace Cert6

/-- `k = 6`, `S = {1, 3, 5}`, with the constant slot iff `θ`; carrier period `q = 15`. -/
def cert (θ : Bool) : CertPP :=
  { k := 6, J := if θ then [0,1,3,5] else [1,3,5], q := 15,
    E0 := [-1,0,-1,0,0,-1],
    V := [-1,-1,0,0,0,1], W := [0,-1,-1,0,-1,1],
    sg := [5,1,5,1,3,5,1,5,5,3,5,1,5,1,3] }

set_option maxRecDepth 100000 in
theorem ok (θ : Bool) : (cert θ).ok = true := by cases θ <;> decide

/-- The certificate for the min-plus map: for both `θ`, no power `T^p`, `p ≥ 1`, of the
min-plus map of `(6, {1, 3, 5}, θ)` is the identity. -/
theorem not_tropPeriodic (θ : Bool) {J : List ℕ} (hJ : ∀ j, j ∈ J ↔ j ∈ (cert θ).J) {p : ℕ}
    (hp : 0 < p) : ¬ TropPeriodic 6 J p :=
  not_tropPeriodic_of_certPP (k := 5) rfl (ok θ) (by cases θ <;> decide)
    (by cases θ <;> decide) hJ hp

theorem no_periodic (θ : Bool) {J : List ℕ} (hJ : ∀ j, j ∈ J ↔ j ∈ (cert θ).J) {co : ℕ → ℝ}
    (hco : ∀ j ∈ J, 0 < co j) {p : ℕ} (hp : 0 < p) : ¬ GloballyPeriodic 6 J co p :=
  not_globallyPeriodic_of_certPP (k := 5) rfl (ok θ) (by cases θ <;> decide)
    (by cases θ <;> decide) hJ hco hp

end Cert6
end Trop
end PeriodicDifference
