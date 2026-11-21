import YangMills.Construction.SummableBoundsOfTheFlow.DecayOfTheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsAtTheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheContoursAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheEnergyAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheGapAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheHaarDensityAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.Interpolation
namespace YangMills.Construction.Interpolation
theorem interpolationKernelBoundsStatement_holds (hD : SummableBounds.interpolatedFrameDecayStatement)
    (hE : EnergyKernelBounds) (hC : contourKernelDerivBound)
    (hG : gapKernelBounds) (hH : haarDensityKernelBounds) :
    interpolationKernelBoundsStatement := by
  obtain ⟨Cz, -, hD⟩ := hD
  obtain ⟨D₁, p₁, hE⟩ := hE
  obtain ⟨D₂, p₂, hC⟩ := hC
  obtain ⟨D₃, p₃, hG⟩ := hG
  obtain ⟨D₄, p₄, hH⟩ := hH
  refine ⟨fun T k => 16 ^ k * |T.chainParams.Kk k| + 1, fun T l j => D₁ T l j + D₂ T l j + D₃ T l j + D₄ T l j,
    fun T k => by positivity, fun T l j => ?_, ?_⟩
  · have := p₁ T l j; have := p₂ T l j; have := p₃ T l j; have := p₄ T l j
    positivity
  refine EventuallyInParameters.mono (EventuallyInParameters.and hD (EventuallyInParameters.and hE
    (EventuallyInParameters.and hC (EventuallyInParameters.and hG hH)))) ?_
  rintro T ⟨gD, gE, gC, gG, gH⟩ x t F V s η hx hF hV hs hs' hη
  have hsum : ∀ l j, D₁ (rateParameters T) l j ≤ D₁ (rateParameters T) l j + D₂ (rateParameters T) l j +
      D₃ (rateParameters T) l j + D₄ (rateParameters T) l j ∧
      D₂ (rateParameters T) l j ≤ D₁ (rateParameters T) l j + D₂ (rateParameters T) l j +
      D₃ (rateParameters T) l j + D₄ (rateParameters T) l j ∧
      D₃ (rateParameters T) l j ≤ D₁ (rateParameters T) l j + D₂ (rateParameters T) l j +
      D₃ (rateParameters T) l j + D₄ (rateParameters T) l j ∧
      D₄ (rateParameters T) l j ≤ D₁ (rateParameters T) l j + D₂ (rateParameters T) l j +
      D₃ (rateParameters T) l j + D₄ (rateParameters T) l j := by
    intro l j
    have a₁ := p₁ (rateParameters T) l j
    have a₂ := p₂ (rateParameters T) l j
    have a₃ := p₃ (rateParameters T) l j
    have a₄ := p₄ (rateParameters T) l j
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  refine ⟨fun b hb => ((gD x t F V s hx hF hV hs hs' b hb).2.1), fun b hb k c X hk hX => ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans ((gD x t F V s hx hF hV hs hs' b hb).2.2 k c X hk hX) ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have : (16 : ℝ) ^ k * T.chainParams.Kk k ≤ 16 ^ k * |T.chainParams.Kk k| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    show 16 ^ k * T.chainParams.Kk k ≤ 16 ^ k * |(rateParameters T).chainParams.Kk k| + 1
    have e : (rateParameters T).chainParams = T.chainParams := rfl
    rw [e]
    linarith
  · intro l j b u c X hl hu hX
    obtain ⟨g₁, g₂⟩ := gE x t F V s η hx hF hV hs hs' hη l j b u c X hl hu hX
    refine ⟨g₁, ?_⟩
    rw [Finset.empty_union]
    exact le_trans g₂ (mul_le_mul_of_nonneg_right (hsum l j).1 (Real.exp_pos _).le)
  · intro c₀ l j b u c X hl hu hX
    obtain ⟨g₁, g₂⟩ := gC x t F V s η hx hF hV hs hs' hη c₀ l j b u c X hl hu hX
    exact ⟨g₁, le_trans g₂ (mul_le_mul_of_nonneg_right (hsum l j).2.1 (Real.exp_pos _).le)⟩
  · intro c₀ l j b u c X hl hu hX
    obtain ⟨g₁, g₂⟩ := gG x t F V s η hx hF hV hs hs' hη c₀ l j b u c X hl hu hX
    exact ⟨g₁, le_trans g₂ (mul_le_mul_of_nonneg_right (hsum l j).2.2.1 (Real.exp_pos _).le)⟩
  · intro b₀ l j b u c X hl hu hX
    obtain ⟨g₁, g₂⟩ := gH x t F V s η hx hF hV hs hs' hη b₀ l j b u c X hl hu hX
    exact ⟨g₁, le_trans g₂ (mul_le_mul_of_nonneg_right (hsum l j).2.2.2 (Real.exp_pos _).le)⟩
end YangMills.Construction.Interpolation
end
