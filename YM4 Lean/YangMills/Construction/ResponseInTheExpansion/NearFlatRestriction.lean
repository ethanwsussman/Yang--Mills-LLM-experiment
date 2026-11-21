import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtANearFlatTop
import YangMills.Construction.ResponseInTheExpansion.FamilyAtANearFlatTop

set_option autoImplicit false

namespace YangMills.Construction.NearFlatRestriction

open BlockAverages ColdStepAtMirrorFrames LinearResponse ResponseInTheExpansion

theorem regularFamily_on_torus {L t n₀ : ℕ} {σ δ E E₃ : ℝ} {f : LocalFamily}
    (hf : IsRegularFamily L t n₀ σ δ E E₃ f) (F : BlockFrame) :
    IsRegularOnTorus L t n₀ σ δ E E₃ f F where
  smooth := hf.smooth F
  gauge_invariant := hf.gauge_invariant F
  decay := hf.decay F
  locality := fun hF y W W' r k h X => hf.locality F F hF hF y y W W' r k h X

theorem centredExpansionNearUniformTopAt_of_family {T : StepParameters} {R : ℕ}
    (h : FamilyNearUniformTopAt T R) : CentredExpansionNearUniformTopAt T R := by
  intro t x f F V hx hf hF
  exact h t x f F V hx (regularFamily_on_torus hf F) hF

theorem centredExpansionNearUniformTop_of_family (hj : EventuallyInParametersCombines)
    (h : familyNearUniformTopStatement) : CentredExpansionNearUniformTop := by
  exact hj.2 _ _ (fun _ _ ⟨R, hR, hF⟩ =>
    ⟨R, hR, centredExpansionNearUniformTopAt_of_family hF⟩) h

end YangMills.Construction.NearFlatRestriction
