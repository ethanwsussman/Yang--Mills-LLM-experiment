import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.DensityNearTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionDensityBoundsForm
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionDensityOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivativeOfTheExpansionDensity
import YangMills.Construction.ColdStepAtMirrorFrames.TransportOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem stepDensity_deriv_bounds (hJ : EventuallyInParametersCombines) (hN : stepDensityNearFrameStatement)
    (hD : stepDensityThirdDerivStatement) (hC : stepDensityIsLocalStatement)
    (hT : expansionTransportStatement) : stepDensityDerivBoundsStatement := by
  refine hJ.2 _ _ (fun T _ H => ?_) (hJ.1 _ _ hN (hJ.1 _ _ hD (hJ.1 _ _ hC hT)))
  obtain ⟨hN, hD, hC, hT⟩ := H
  intro t x f hx hf
  refine ⟨fun F hF Y V k c X hV h1 h3 hX => ?_, hC t x f hx hf⟩
  obtain hk | hk : k ≤ 2 ∨ k = 3 := by omega
  · have hnear := (hN t x f hx hf F hF Y V hV).2 k c X h1 hk hX
    have hlow : |bondDeriv (expansionAtFrameFamily T false x f F Y) V c X| ≤
        2⁻¹ ^ 6 * T.E / torusDecayFactor T.L T.decayRate (bondSpan Y c) :=
      (hT t x f F V hx hf hF hV false).1.lowDeriv Y k c X h1 hk hX
    have hne : k ≠ 3 := by omega
    have htri := abs_sub_abs_le_abs_sub (bondDeriv (stepDensityFamily T x f F Y) V c X)
      (bondDeriv (expansionAtFrameFamily T false x f F Y) V c X)
    beta_reduce
    rw [if_neg hne]
    linarith
  · subst hk
    have h := hD t x f hx hf F hF Y V c X hV hX
    beta_reduce
    rw [if_pos rfl]
    exact h
end YangMills.Construction.ColdStepAtMirrorFrames
end
