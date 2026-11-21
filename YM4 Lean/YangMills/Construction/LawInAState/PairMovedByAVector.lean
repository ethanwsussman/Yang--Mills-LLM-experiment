import YangMills.Construction.LawInAState.HatsSumToTheFreeKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open InfiniteLattice (AmbientSpace)
def localizedPairTranslateStatement : Prop :=
  ∀ (c s : AmbientSpace) (d Λ : ℝ) (f h : AmbientSpace → ℝ), IsLocalizedLipschitzPair c d Λ f h →
    IsLocalizedLipschitzPair (c + s) d Λ (fun x => f (x - s)) (fun x => h (x - s)) ∧
    TestFunctions.inverseEighthKernel (fun x => f (x - s)) (fun x => h (x - s)) =
      TestFunctions.inverseEighthKernel f h
end YangMills.Construction.StateLaws
end
