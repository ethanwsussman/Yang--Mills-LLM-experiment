import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentsCompareOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.TermsBetweenCompareOnTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.FamilyNorms YangMills.Construction.Interpolation
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem cellExponentsCloseEventually_holds (hb : InterpolatedTermsCloseOnTwoTori)
    (hends : interpolationAtEndpoints) (hj : EventuallyInParametersCombines) :
    CellExponentsCloseEventually := by
  refine hj.2 _ _ ?_ hb
  intro T hT hc t x f F F' V V' Y Y' r e φ hxy hrow htop htop' hcold hcold' hag hr hbm hcm star
  have hf : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f :=
    ⟨hrow.smooth, hrow.gauge_invariant, hrow.translation_invariant, hrow.decay, hrow.locality⟩
  have hs0 : 0 ≤ segmentEnd star := by
    simp only [segmentEnd]
    split_ifs <;> norm_num
  have hs1 : segmentEnd star ≤ 1 := by
    simp only [segmentEnd]
    split_ifs <;> norm_num
  have hj1 : Function.Injective (fun k : ↥(bondsNearCell F Y r) => k.1) := Subtype.val_injective
  have hj2 : Function.Injective (fun k : ↥(bondsNearCell F Y r) => (e k).1) :=
    fun a b h => e.injective (Subtype.ext h)
  have ends := fun {G : BlockFrame} (W : G.GaugeField G.top) =>
    hends G star T.a T.chainParams.ρA 0 x 0 (frameRadius x) W
  have eE : ∀ {G : BlockFrame} (W : G.GaugeField G.top) (z : G.Cell),
      interpolatedBlockExponent (segmentEnd star) T.a T.chainParams.ρA x (frameRadius x) z W =
        cellExponent star T.a T.chainParams.ρA x (frameRadius x) z W := by
    intro G W z
    funext η
    exact (ends W).2.2.2.2.1 z η
  have eR : ∀ {G : BlockFrame} (W : G.GaugeField G.top) (z : G.Cell) (η : StepVariable (finiteCells G)),
      interpolatedBlockExpansion (segmentEnd star) T.a T.chainParams.ρA (frameRadius x) f z η W =
        cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f z η W := by
    intro G W z η
    unfold interpolatedBlockExpansion cellCentredExpansion
    exact Finset.sum_congr rfl fun y _ => (ends W).2.2.2.1 f y η
  have key : ∀ z : {z // z ∈ cellsNearCell F Y r}, ∃ o : Fin 4 → ℤ, z.1 = Y + siteOfCoords F.top o ∧
      (φ z).1 = Y' + siteOfCoords F'.top o ∧ _ := fun z => by
    obtain ⟨o, ho, h1, h2⟩ := hcm z
    refine ⟨o, h1, h2, ?_⟩
    have := hc t x (segmentEnd star) f F F' V V' Y Y' r ↥(bondsNearCell F Y r) (fun k => k.1) (fun k => (e k).1) o
      ⟨hxy, ⟨hs0, hs1⟩, hf, htop, htop', hcold, hcold', hag, hr, hj1, hj2,
        (fun i => by
          obtain ⟨g, u, k, hu, hg, e1, e2⟩ := hbm i
          exact ⟨g, u, k, hu, hg, e1, e2⟩), ho⟩
    exact this
  refine ⟨fun z ξ hξ => ?_, fun z ξ hξ => ?_⟩
  · obtain ⟨o, h1, h2, h3⟩ := key z
    have := h3.1 ξ hξ
    rw [← h1, ← h2, eE, eE] at this
    exact this
  · obtain ⟨o, h1, h2, h3⟩ := key z
    have := h3.2 ξ hξ
    rw [← h1, ← h2] at this
    simp only [eR] at this
    exact this
end YangMills.Construction.ColdStepAtMirrorFrames
end
