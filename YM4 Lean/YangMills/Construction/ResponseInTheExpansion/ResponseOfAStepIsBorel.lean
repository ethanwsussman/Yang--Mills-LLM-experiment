import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open StepSettings StepCosts TorusFields TorusLumps StepGas RenormalizationStepParameters ClusterExpansionOfAStep
def StepResponseMeasurable : Prop :=
  HoldsAtEveryStep fun _ S P => S.IsWellPosed → ∀ hL : CoarseLabelFacts S,
    (∀ n [NeZero n], S.params.n₀ ≤ n → ∀ (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState S n) (y : TorusSite n)
      (w : PlaquetteWeight (fineSide S.params.side (S.depth + 1) n)) (bad : Finset (TorusBond (n * S.params.side)))
      (Yt : Finset (TorusSite (n * S.params.side))) (b : BaseChoice S.params.side n),
      Measurable fun p : TorusField (n * S.params.side) × (q.unlabelled Yt → S.labels.Ω) =>
        caseTerm S C V q (caseResponse P V y w) bad Yt b p.1 p.2) ∧
    (∀ n [NeZero n], S.params.n₀ ≤ n → ∀ (y : TorusSite n) (w : PlaquetteWeight (fineSide S.params.side (S.depth + 1) n)),
      (open Classical in Measurable fun V : TorusField n => if IsCold S.params.threshold V then P.coldStep n y V w else 0)) ∧
    ∀ n [NeZero n], IsBlockTorusSide S.params n → ∀ (y : TorusSite n) (Y : Finset (TorusSite n))
      (w : PlaquetteWeight (fineSide S.params.side (S.depth + 1) n)),
      (open Classical in Measurable fun p : TorusField n × (Y → (coarseLabelSpace S hL).Ω) =>
        if IsLiveState S.params S.nextCoupling (coarseWeightExpansion S) p.1 Y p.2 then P.hullStep n y p.1 Y p.2 w else 0)
end YangMills.Construction.WeightedResponses
end
