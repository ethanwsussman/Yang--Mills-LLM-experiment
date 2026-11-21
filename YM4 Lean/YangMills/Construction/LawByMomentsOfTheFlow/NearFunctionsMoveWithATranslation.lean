import YangMills.Construction.HullsInEveryVolume.HullDefs
import YangMills.Construction.LawByMomentsOfTheFlow.NearlyLocalFunctionsOfTheCases
import YangMills.Construction.LawByMomentsOfTheFlow.TranslationsOfTheCases
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
def nearlyLocalTranslateStatement : Prop :=
  HullTrees.EventuallyInParameters fun Tb _ y => ∀ (g β : ℝ) (K m : ℕ)
    (T : WeightedResponses.StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n],
    HullTrees.HullChainAtLevel Tb y g β K m T (u + 1) n → ∀ (w : Fin 4 → ℤ)
      (o : TorusFields.TorusSite (n * (Tb.stepParameters y).side)) (R : ℕ) (B : ℝ)
      (F : WeightedResponses.CaseFunction (T.stage u).toStepSetup n),
      IsNearlyLocalCaseFunction (T.stage u).toStepSetup o R B F →
      IsNearlyLocalCaseFunction (T.stage u).toStepSetup
        (o + TorusFields.siteOfInt fun i =>
          ((Tb.stepParameters y).side : ℤ) * (((Tb.stepParameters y).side : ℤ) * w i)) R B
        (translateCaseFunction (fun i => ((Tb.stepParameters y).side : ℤ) * w i) F)
end YangMills.Construction.MomentLaw
end
