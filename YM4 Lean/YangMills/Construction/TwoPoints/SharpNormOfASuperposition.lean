import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def IsBddLipschitz (F : AmbientSpace → ℂ) : Prop :=
  TestFunctions.IsBoundedFun F ∧ TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 F
def SharpNormSuperpositionBound.Statement : Prop :=
  ∀ sc : FixedScale,
    (∀ F G : AmbientSpace → ℂ, IsBddLipschitz F → IsBddLipschitz G →
      IsBddLipschitz (F + G) ∧ sc.sharpNorm (F + G) ≤ sc.sharpNorm F + sc.sharpNorm G) ∧
    (∀ (a : ℂ) (F : AmbientSpace → ℂ), IsBddLipschitz F →
      IsBddLipschitz (a • F) ∧ sc.sharpNorm (a • F) = ‖a‖ * sc.sharpNorm F) ∧
    ∀ (Z : Set AmbientSpace) (w : AmbientSpace → ℂ) (F : AmbientSpace → AmbientSpace → ℂ) (A : ℝ),
      MeasurableSet Z → Bornology.IsBounded Z → Measurable w → (∃ C : ℝ, ∀ z ∈ Z, ‖w z‖ ≤ C) →
      Continuous (Function.uncurry F) → (∀ z ∈ Z, IsBddLipschitz (F z)) →
      (∀ z ∈ Z, sc.sharpNorm (F z) ≤ A) →
      IsBddLipschitz (fun x => setIntegralOf Z fun z => w z * F z x) ∧
        sc.sharpNorm (fun x => setIntegralOf Z fun z => w z * F z x) ≤
          (∫ z in Z, ‖w z‖) * A
end YangMills.Construction.TwoPoints
end
