import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PathForms
open TorusFields WeightedResponses
def pathFormAboutSiteStatement : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ Y : TorusSite n, ∃ co : TorusBond n → OrientedPlaquette n → ℝ,
    (∀ c : TorusBond n, ∑ p : OrientedPlaquette n, |co c p| ≤ K * (1 + (supDist c.1 Y : ℝ)) ^ 2) ∧
    (∀ (c : TorusBond n) (p : OrientedPlaquette n), co c p ≠ 0 → supDist p.1.1 Y ≤ supDist c.1 Y + 1) ∧
    ∀ (A : TorusBond n → ℝ) (p : TorusPlaquette n),
      WeightedResponses.curl (fun c => ∑ p' : OrientedPlaquette n, co c p' * WeightedResponses.curl A p'.1) p =
        WeightedResponses.curl A p
end YangMills.Construction.PathForms
end
