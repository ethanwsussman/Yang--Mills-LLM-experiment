import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.FamiliesOfCriticalBranches
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Conventions
namespace Tower
def CriticalBranchData.pushForward {L n k j : ℕ} (hL : 0 < L) (hj : j ≤ k)
    (b : CriticalBranchData L n k) : CriticalBranchData L (scaledExponent n k j) j where
  energy l := transportTotalScalar (scaleEdge hL hj l) (b.energy l)
  prolong i := transportTotalFunValued (scaleEdge hL hj (i + 1)) (scaleEdge hL hj i)
    (b.prolong i)
def ScaledBranchIsCriticalStatement : Prop :=
  ∀ (L n k j : ℕ) (hL : 0 < L) (hj : j ≤ k), IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ j →
    ∀ b : CriticalBranchData L n k, b.IsCritical → (b.pushForward hL hj).IsCritical
end Tower
end YangMills.Construction
end
