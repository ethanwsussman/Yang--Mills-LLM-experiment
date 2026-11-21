import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps WeightedResponses CyclicFormula
def freeCumulantValueStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S =>
    ∀ μ : Measure (LevelChain Λ.stepParams.side S.data.windowLevel (S.data.period Λ.stepParams.side)),
    IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling S.data.windowLevel (S.data.period Λ.stepParams.side)) μ →
    jointCumulant μ (fun i => S.observableAt S.data.windowLevel (S.data.period Λ.stepParams.side) i) =
      3 * (if Λ.k = 2 then 1 / 2 else 1) * ∑ σ ∈ unorientedCyclicOrders Λ.k,
        ∑ p : Fin Λ.k → OrientedPlaquette
          (fineSide Λ.stepParams.side S.data.windowLevel (S.data.period Λ.stepParams.side)),
        (∏ i, S.weight i _ (p i).1) * ∏ c : Fin Λ.k, torusCurvatureProjection (p (σ c)) (p (σ (c + 1))) ∧
    |jointCumulant μ (fun i => S.observableAt S.data.windowLevel (S.data.period Λ.stepParams.side) i)| ≤ C 0 ∧
    |jointCumulant μ (fun i => S.observableAt S.data.windowLevel (S.data.period Λ.stepParams.side) i) -
        S.latticeCycleSumAt S.data.scaleLevel| ≤
      C 0 * (Λ.stepParams.side : ℝ) ^ (-(4 * ((S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ)))) ∧
    (X₀ ≤ S.scaleCoupling →
      |jointCumulant μ (fun i => S.observableAt S.data.windowLevel (S.data.period Λ.stepParams.side) i) -
        S.latticeCycleSumAt S.data.scaleLevel| ≤ C 0 * S.scaleCoupling⁻¹) ∧
    |S.latticeCycleSumAt S.data.scaleLevel| ≤ C 0 ∧
    |S.latticeCycleSumAt S.data.scaleLevel - S.cyclicLimit| ≤
      C 0 * (Λ.stepParams.side : ℝ) ^ (-(S.data.scaleLevel : ℝ))
end YangMills.Construction.MomentLaw
end
