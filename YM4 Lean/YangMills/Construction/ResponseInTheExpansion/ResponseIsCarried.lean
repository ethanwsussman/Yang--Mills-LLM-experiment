import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace WeightedResponses
open StepSettings TorusFields TorusLumps StepGas BlockAverages RenormalizationStepParameters ClusterExpansionOfAStep
def StepResponseIsometryInvariant : Prop :=
  HoldsAtEveryStep fun _ S P => ∀ hL : CoarseLabelFacts S, S.IsSymmetricWeight →
    (∀ (n : ℕ) [NeZero n], IsBlockTorusSide S.params n → ∀ (y : TorusSite n) (V : TorusField n) (Y : Finset (TorusSite n)),
      IsHullState S.params (clusterRange S.nextCoupling) V Y →
      Integrable (fun ω : Y → (coarseLabelSpace S hL).Ω =>
          P.hullStep n y V Y ω (constOneWeight _) * coarseWeightExpansion S n V Y ω)
        (Measure.pi fun _ : Y => (coarseLabelSpace S hL).μ)) ∧
    (∀ (n : ℕ) [NeZero n], IsBlockTorusSide S.params n → ∀ (g : TorusIsometry) (y : TorusSite n) (V V' : TorusField n),
      g.Transports V V' →
      responseMass S.params (S.depth + 1) S.nextCoupling (coarseLabelSpace S hL) (coarseWeightExpansion S) P.hullStep n (g.mapSite y) V' =
        responseMass S.params (S.depth + 1) S.nextCoupling (coarseLabelSpace S hL) (coarseWeightExpansion S) P.hullStep n y V) ∧
    ∀ (n : ℕ) [NeZero n], S.params.n₀ ≤ n → ∀ (g : TorusIsometry) (y : TorusSite n) (V V' : TorusField n),
      IsCold S.params.threshold V → g.Transports V V' →
      P.coldStep n (g.mapSite y) V' (constOneWeight _) = P.coldStep n y V (constOneWeight _)
end WeightedResponses
end YangMills.Construction
end
