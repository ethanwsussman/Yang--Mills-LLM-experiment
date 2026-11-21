import YangMills.Construction.ClusterExpansionOfAStep.ConstantsOfTheColdChain
import YangMills.Construction.ClusterExpansionOfAStep.MatchingClasses
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace StepFrames
variable {n : ℕ}
def ColdNearSite (s : ℝ) (m : ℕ) (y : TorusFields.TorusSite n) (V : TorusFields.TorusField n) : Prop :=
  ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν →
    (∀ d ∈ TorusLumps.plaquetteOffsets μ ν, TorusFields.OffsetInBox m (a + d)) →
    TorusFields.curvature V (y + TorusFields.siteOfInt a) μ ν < s
def continuousOn_frameCoord_of_cold : Prop :=
  ∀ (p : TorusLumps.StepParameters) (δ lam ρA σA cg : ℝ) (N : ℕ → ℝ), p.Admissible →
    ColdChain.ColdChainConstants p.coupling δ p.side lam ρA σA cg N →
    p.threshold ≤ σA → ∀ (t m n : ℕ) [NeZero n], 16 ≤ m → 64 ≤ n → ∀ e ∈ StepCosts.chartBonds p.side n,
      (4 * m + 5 < n → ContinuousOn
        (fun V : TorusFields.TorusField n =>
          ((StepCosts.frameCoord p ρA t m V e : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]))
        {V | ColdNearSite p.threshold m (TorusLumps.parentBlock p.side e.1) V}) ∧
      (¬ 4 * m + 5 < n → ContinuousOn
        (fun V : TorusFields.TorusField n =>
          ((StepCosts.frameCoord p ρA t m V e : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]))
        {V | TorusFields.IsCold p.threshold V})
end StepFrames
end YangMills.Construction
end
