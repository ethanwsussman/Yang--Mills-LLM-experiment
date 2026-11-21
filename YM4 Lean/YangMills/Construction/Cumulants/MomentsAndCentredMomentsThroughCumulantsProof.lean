import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.Cumulants.MomentsAndCentredMomentsThroughCumulants
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Cumulants
open YangMills.Construction.Probability (complexExpectation)
theorem complexExpectation_ofReal {𝒳 : Type} [MeasurableSpace 𝒳] (ν : Measure 𝒳) (f : 𝒳 → ℝ) :
    (complexExpectation ν fun ω => (f ω : ℂ)) = ((∫ ω, f ω ∂ν : ℝ) : ℂ) :=
  integral_complex_ofReal
theorem momentsViaCumulants_holds (hRel : Cumulants.CumulantMomentRelations) :
    Cumulants.MomentsViaCumulants := by
  intro 𝒳 _ ν _ q x hx
  obtain ⟨-, -, -, -, hMom, hCen, -⟩ := hRel 𝒳 ν q x hx
  refine ⟨?_, ?_⟩
  · rw [← hMom, complexExpectation_ofReal]
  · rw [← hCen, ← complexExpectation_ofReal]
    refine congrArg (complexExpectation ν) (funext fun ω => ?_)
    simp only [complexExpectation_ofReal]
    push_cast
    rfl
end YangMills.Construction.Cumulants
