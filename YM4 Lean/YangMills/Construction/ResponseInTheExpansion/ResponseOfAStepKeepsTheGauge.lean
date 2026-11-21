import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open StepSettings TorusFields TorusLumps StepGas BlockAverages RenormalizationStepParameters ClusterExpansionOfAStep
def StepResponseGaugeInvariant : Prop :=
  HoldsAtEveryStep fun _ S P => S.IsWellPosed → ∀ hL : CoarseLabelFacts S,
    (∀ n [NeZero n], S.params.n₀ ≤ n → ∀ (y : TorusSite n) (g : TorusSite n → UnitQuaternion) (V : TorusField n), IsCold S.params.threshold V →
      ∀ w : PlaquetteWeight (fineSide S.params.side (S.depth + 1) n), P.coldStep n y (gaugeTransform g V) w = P.coldStep n y V w) ∧
    ∀ n [NeZero n], IsBlockTorusSide S.params n → ∀ (y : TorusSite n) (g : TorusSite n → UnitQuaternion) (V : TorusField n)
      (Y : Finset (TorusSite n)) (ω : Y → (coarseLabelSpace S hL).Ω),
      IsLiveState S.params S.nextCoupling (coarseWeightExpansion S) V Y ω → ∀ w : PlaquetteWeight (fineSide S.params.side (S.depth + 1) n),
      P.hullStep n y (gaugeTransform g V) Y ((coarseLabelSpace S hL).act Y g ω) w = P.hullStep n y V Y ω w
end YangMills.Construction.WeightedResponses
end
