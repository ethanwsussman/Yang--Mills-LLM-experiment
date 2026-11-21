import YangMills.Construction.LimitsOfLatticeFamilies.IsometriesTranslationsAndEnlargedSupports
import YangMills.Construction.LimitsOfLatticeFamilies.TranslationModulusInTheSharpNorm
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
open ModelSpace
def ShiftDifferenceBounds : Prop :=
  ∀ (s : Conventions.StandingParameters) (M : BlockScale s) (Y : ModelSpace)
    (f : c1CompactSupp s Y univ) (a b : Y.Carrier s),
    ENNReal.ofReal (TestFunctions.uniformNorm (ModelSpace.shift a f.1 - ModelSpace.shift b f.1)) ≤
      gradSup f * ((ModelSpace.norm s Y (a - b)).toNNReal : ℝ≥0∞) ∧
    ENNReal.ofReal (lipNumber s Y (ModelSpace.shift a f.1 - ModelSpace.shift b f.1)) ≤
      gradOscillation f (ModelSpace.norm s Y (a - b)).toNNReal ∧
    ENNReal.ofReal (sharpNorm s M Y (ModelSpace.shift a f.1 - ModelSpace.shift b f.1)) ≤
      sharpTranslationModulus M f (ModelSpace.norm s Y (a - b)).toNNReal
end YangMills.Construction.LatticeLimits
end
