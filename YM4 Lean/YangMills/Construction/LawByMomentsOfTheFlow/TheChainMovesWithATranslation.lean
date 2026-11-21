import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import YangMills.Construction.LawByMomentsOfTheFlow.TranslationsOfTheCases
import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def chainTranslationStatement : Prop :=
  HullTrees.EventuallyInParameters fun Tb _ y => ∀ (g β : ℝ) (K m : ℕ)
    (T : WeightedResponses.StageTower (Tb.stepParameters y)) (t d n : ℕ) [NeZero n],
    HullTrees.HullChainAtLevel Tb y g β K m T (t + d) n → ∀ w : Fin 4 → ℤ,
      (∀ rule : ChainNoise.NoiseRule (Tb.stepParameters y), rule.IsAdmissible T →
        ∀ p : TorusFields.TorusField (WeightedResponses.fineSide (Tb.stepParameters y).side (t + d) n) ×
            ChainNoise.ChainNoise (Tb.stepParameters y) (t + d) n,
          rule.chain T (t + d) n
              (ChainNoise.pairTranslate (Tb.stepParameters y) (t + d) n
                (fun i => ((Tb.stepParameters y).side : ℤ) * w i) p).1
              (ChainNoise.pairTranslate (Tb.stepParameters y) (t + d) n
                (fun i => ((Tb.stepParameters y).side : ℤ) * w i) p).2 =
            translateSample (t + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * w i)
              (rule.chain T (t + d) n p.1 p.2)) ∧
      (∀ x : WeightedResponses.MarkedSample (Tb.stepParameters y) (t + d) n,
        WeightedResponses.stageState T (t + d) n
            (translateSample (t + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * w i) x) =
          translateStageState T (t + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * w i)
            (WeightedResponses.stageState T (t + d) n x)) ∧
      (∀ x : WeightedResponses.MarkedSample (Tb.stepParameters y) (t + d) n,
        translateSample (t + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * -w i)
          (translateSample (t + d) n (fun i => ((Tb.stepParameters y).side : ℤ) * w i) x) = x) ∧
      Measurable (translateSample (ℓ := Tb.stepParameters y) (t + d) n
        fun i => ((Tb.stepParameters y).side : ℤ) * w i) ∧
      @Measurable _ _ (ResponseInTheExpansion.upperSigma T t d n) (ResponseInTheExpansion.upperSigma T t d n)
        (translateSample (t + d) n fun i => ((Tb.stepParameters y).side : ℤ) * w i)
end YangMills.Construction.MomentLaw
end
