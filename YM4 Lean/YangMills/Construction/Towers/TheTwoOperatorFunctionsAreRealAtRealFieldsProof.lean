import YangMills.Construction.Towers.ConfigurationsNearOneHaveSmallIterates
import YangMills.Construction.Towers.FieldsAndTheirValues
import YangMills.Construction.Towers.TheBackgroundKernelAndTheCovariantLaplacianAreFormed
import YangMills.Construction.Towers.TheEntriesOfTheBackgroundKernelAreRealAtRealData
import YangMills.Construction.Towers.TheIteratedMapsKeepRealFunctions
import YangMills.Construction.Towers.TheThreeKernelsAreRealAtRealConfigurations
import YangMills.Construction.Towers.TheTwoOperatorFunctionsAreRealAtRealFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RealOperatorFunctions
open YangMills.Construction.PeriodicOperators
private theorem im_tsum_mul_of_im_eq_zero {α : Type} (f g : α → ℂ) (hf : ∀ a, (f a).im = 0)
    (hg : ∀ a, (g a).im = 0) : (∑' a, f a * g a).im = 0 := by
  have h : (fun a => f a * g a) = fun a => (((f a * g a).re : ℝ) : ℂ) := by
    funext a
    apply Complex.ext
    · simp
    · simp [Complex.mul_im, hf a, hg a]
  rw [h, ← Complex.ofReal_tsum]
  exact Complex.ofReal_im _
theorem operatorFunctionsRealOnCompactFields_holds
    (hSmall : SmallIterates.SmallIteratesNearOne)
    (hValues : FieldValues.FieldsAndValuesClaim)
    (hIterated : IteratesPreserveRealFields.Holds)
    (hFormed : HessianLaplacian.HessianKernelAndLaplacianExist)
    (hEntries : RealBackgroundKernel.RawHessianKernelReal)
    (hKernels : KernelsRealAtGroupFields) :
    OperatorFunctionsRealOnCompactFields := by
  intro L hL hStd k hk
  obtain ⟨ρ, hρ, hBelow⟩ := (hSmall L hL hStd k hk).2
  refine ⟨ρ, hρ, fun ζ hζ hReal => ?_⟩
  have hConf : FieldValueFunctions.gaugeFieldOfCoeffs hL (ζ.pauliCoeffs hL) = ζ.gaugeField :=
    ((hValues L hL k).1 ζ).2.2.2.2.2
  have hU : ζ.gaugeField ∈ smallIterateFields L k := hConf ▸ hBelow _ hζ
  have hG : ζ.gaugeField ∈ fieldSpace L k 0 := (hIterated L hStd k hk).1 _ hReal.1
  obtain ⟨hD, hA, hQ, -, -⟩ := hKernels L hStd k hk _ hU hG
  have hY := hEntries L hStd k hk _ hU hG _ hReal.2.1 _ hReal.2.2
  have hX := ((hFormed L hStd k hk _ hU).1 _ ζ.2.1.2 _ ζ.2.2.2).2.2.2.2
  refine ⟨?_, ?_⟩
  · rintro (i' | c') (i | c)
    · change (hessianKernel ζ.gaugeField _ _ i' i).im = 0
      rw [hX]
      simp [HessianLaplacian.symmHessianKernel, swapKernel, hY]
    · exact hQ c i'
    · exact hQ c' i
    · rfl
  · rintro (i' | c') (i | c)
    · exact im_tsum_mul_of_im_eq_zero _ _ (fun a => hD a i') (fun a => hD a i)
    · exact hA c i'
    · exact hA c' i
    · rfl
end YangMills.Construction.Tower.FullSpace.RealOperatorFunctions
end
