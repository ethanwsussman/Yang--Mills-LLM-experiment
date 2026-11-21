import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open StepSettings TorusFields TorusLumps StepGas RenormalizationStepParameters ClusterExpansionOfAStep
def StepResponseTranslationInvariant : Prop :=
  HoldsAtEveryStep fun _ S P => S.IsWellPosed → ∀ _hL : CoarseLabelFacts S,
    (∀ n [NeZero n], S.params.n₀ ≤ n → ∀ (y : TorusSite n) (v : Fin 4 → ℤ) (V : TorusField n), IsCold S.params.threshold V →
      ∀ w : PlaquetteWeight (fineSide S.params.side (S.depth + 1) n),
      P.coldStep n y (TorusFields.translate (siteOfInt fun i => (S.params.side : ℤ) * v i) V)
          (translateWeight (fineTranslate S.params.side (S.depth + 1) n fun i => (S.params.side : ℤ) * v i) w) =
        P.coldStep n (y + siteOfInt fun i => (S.params.side : ℤ) * v i) V w) ∧
    ∀ n [NeZero n], IsBlockTorusSide S.params n → ∀ (y : TorusSite n) (v : Fin 4 → ℤ) (V : TorusField n)
      (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel S.labels.Ω S.params.side),
      IsLiveState S.params S.nextCoupling (coarseWeightExpansion S) V Y ω → ∀ w : PlaquetteWeight (fineSide S.params.side (S.depth + 1) n),
      P.hullStep n y (TorusFields.translate (siteOfInt fun i => (S.params.side : ℤ) * v i) V)
          (translateSet (siteOfInt fun i => (S.params.side : ℤ) * v i) Y)
          (translateLabel (siteOfInt fun i => (S.params.side : ℤ) * v i) Y ω)
          (translateWeight (fineTranslate S.params.side (S.depth + 1) n fun i => (S.params.side : ℤ) * v i) w) =
        P.hullStep n (y + siteOfInt fun i => (S.params.side : ℤ) * v i) V Y ω w
end YangMills.Construction.WeightedResponses
end
