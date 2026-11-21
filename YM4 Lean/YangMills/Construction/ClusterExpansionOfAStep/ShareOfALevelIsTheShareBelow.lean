import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.ShareEvaluation
open YangMills.Construction.TorusFields YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepCosts
def LevelShareEqMinimalSiteShare : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ (t n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ W : TorusField (n * T.side),
    IsCold T.threshold W → ∀ y : TorusSite (n * T.side),
      levelShare T.coupling T.side t Finset.univ y W =
        minimalSiteShare (F := torusFrame T.side t n) T.coupling
          (torusSiteInFrame (torusFrame T.side t n) (torusFrame T.side t n).depth y)
          (readAtLevel (torusFrame T.side t n) (torusFrame T.side t n).depth W)
end YangMills.Construction.ShareEvaluation
end
