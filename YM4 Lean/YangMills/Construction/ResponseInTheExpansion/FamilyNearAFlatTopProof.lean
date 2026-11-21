import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionNearAFlatTopProof
import YangMills.Construction.ResponseInTheExpansion.FamilyAtANearFlatTop
import YangMills.Construction.ResponseInTheExpansion.FamilyNearAFlatTopForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace ResponseInTheExpansion
namespace NearUniformTopProof
open BlockOffsets
variable {F : BlockFrame}
theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hper : ∀ i, F.period F.top i ≠ 0)
    (V : F.GaugeField F.top) {s : ℝ} (hV : IsSmallCurvature s V)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), IsSmallCurvature s (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearFlatExpansion.eventually_isSmallCurvature_leftTranslate <;> assumption
theorem isSmallCurvature_gaugeTransform {s : ℝ} (γ : F.Cell → UnitQuaternion) (V : F.GaugeField F.top)
    (hV : IsSmallCurvature s V) : IsSmallCurvature s (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearFlatExpansion.isSmallCurvature_gaugeTransform <;> assumption
theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) : ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X‖ = ‖X‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
theorem nearUniformTopResponse_of_family (hAx : AxialGaugeBondBound) (hG : GaugeCovarianceOfFrame)
    (hends : interpolationAtEndpoints) {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {R : ℕ} (hd : T.IsOrdered) (hR : 4 * R + 8 ≤ T.n₀)
    (hfb : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFramesControlledAt T t x)
    (hft : FrameBoundsForParameters T) (hbody : FamilyNearUniformTopAt T R) : NearUniformTopResponse T := by
  classical
  intro t x f F V hx hf hF hV w
  obtain ⟨hFL, _, n, hsn, hnn⟩ := id hF
  have hLp : 0 < T.L := hd.odd_L.pos
  have hlow : IsCubicTorusAbove T.L t T.n₀ F :=
    ⟨hFL, by assumption, n, hsn, hnn.trans (Nat.le_mul_of_pos_right n hLp)⟩
  have hs : ∀ i, 2 * R + 2 < F.extent i := fun i => by rw [hsn i]; omega
  have hperN : ∀ i, F.period F.top i ≠ 0 := fun i => by
    rw [period_top]
    have := hs i
    omega
  have hσ := hd.σ_pos
  obtain ⟨Cf, C, _, _, _, _, _, _, _, _, _, _, _, _, _, hFH⟩ := hft
  have hs0 : 0 ≤ segmentEnd w := by unfold segmentEnd; split_ifs <;> norm_num
  have hs1 : segmentEnd w ≤ 1 := by unfold segmentEnd; split_ifs <;> norm_num
  have hturn : ∀ (γ : F.Cell → UnitQuaternion) (V₁ : F.GaugeField F.top),
      IsSmallCurvature (5 / 4 * T.σ) V₁ →
      ∀ (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ T.σ / 64) → ∀ y : F.Site F.depth,
      centredExpansion w T.a T.chainParams.ρA (frameRadius x) f y (adjointStepVariable γ η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V₁) =
        centredExpansion w T.a T.chainParams.ρA (frameRadius x) f y η V₁ := by
    intro γ V₁ hV₁ η hη y
    have hsm := (hFH t x F V₁ hx hF hV₁).2.1 w
    have hcov : ∀ b ∈ chordBonds (finiteCells F),
        stepFrame w T.a T.chainParams.ρA (frameRadius x) b (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V₁) =
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame w T.a T.chainParams.ρA (frameRadius x) b V₁) :=
      fun b hb => Subtype.ext (hsm.gauge_covariant b hb γ)
    have h1 := hG.1 F (fun b V' => stepFrame w T.a T.chainParams.ρA (frameRadius x) b V') V₁ γ η
      (by rw [hFL]; exact hd.odd_L) (fun i => by have := hs i; omega) hcov
    have hbet := ((hfb t x hx).single F V₁ (segmentEnd w) hF hV₁ hs0 hs1).2
    obtain ⟨_, _, h3, -⟩ := hends F w T.a T.chainParams.ρA 0 0 0 (frameRadius x) V₁
    have hcold : IsSmallCurvature T.σ (fieldAboveFrame w T.a T.chainParams.ρA (frameRadius x) V₁ η) := by
      have := hbet.small_curvature_nearby η hη
      rw [h3 η] at this
      exact fun p hp => (this p hp).trans (by linarith)
    show subtractTrivial f F y
        (fieldAboveFrame w T.a T.chainParams.ρA (frameRadius x) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V₁) (adjointStepVariable γ η)) =
      subtractTrivial f F y (fieldAboveFrame w T.a T.chainParams.ρA (frameRadius x) V₁ η)
    have h2 : fieldAboveFrame w T.a T.chainParams.ρA (frameRadius x) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V₁)
        (adjointStepVariable γ η) =
        _root_.YangMills.Construction.BlockAverages.gaugeTransform (fun x' => γ (enclosingCell x'))
          (fieldAboveFrame w T.a T.chainParams.ρA (frameRadius x) V₁ η) := h1
    rw [h2]
    show f F y _ - _ = f F y _ - _
    rw [hf.gauge_invariant hlow y _ _ hcold]
  have hblock : ∀ (γ : F.Cell → UnitQuaternion) (V₁ : F.GaugeField F.top),
      IsSmallCurvature (5 / 4 * T.σ) V₁ →
      ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ T.σ / 64) →
      cellCentredExpansion w T.a T.chainParams.ρA (frameRadius x) f Y (adjointStepVariable γ η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V₁) =
        cellCentredExpansion w T.a T.chainParams.ρA (frameRadius x) f Y η V₁ := fun γ V₁ hV₁ Y η hη => by
    unfold cellCentredExpansion
    exact Finset.sum_congr rfl fun y _ => hturn γ V₁ hV₁ η hη y
  have hnear : ∀ Y : F.Cell,
      IsNearUniformAbout (5 / 4 * T.σ) R (_root_.YangMills.Construction.BlockAverages.gaugeTransform (axialGaugeHolonomy V Y) V) Y := by
    intro Y r b hr hb
    have := hAx F V Y (5 / 4 * T.σ) r (fun i => by have := hs i; omega) (by positivity) hV b hb
    exact this
  have hV' : ∀ Y : F.Cell, IsSmallCurvature (5 / 4 * T.σ) (_root_.YangMills.Construction.BlockAverages.gaugeTransform (axialGaugeHolonomy V Y) V) :=
    fun Y => _root_.YangMills.Construction.ResponseInTheExpansion.NearUniformTopProof.isSmallCurvature_gaugeTransform _ V hV
  have hfull := fun Y =>
    hbody t x f F (_root_.YangMills.Construction.BlockAverages.gaugeTransform (axialGaugeHolonomy V Y) V) hx hf hF (hV' Y) w Y (hnear Y)
  have hball : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ < T.ballRadius) →
      ∀ b, ‖adjointStepVariable (axialGaugeHolonomy V Y) η b‖ < T.ballRadius := fun Y η hη b => by
    rw [hG.2.2 F _ η b]
    exact hη b
  have hcarry : ∀ {k : ℕ} (Y : F.Cell) (η : StepVariable (finiteCells F)) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ < T.ballRadius) → AreUnitVectors X →
      bondDeriv (cellCentredExpansion w T.a T.chainParams.ρA (frameRadius x) f Y η) V c X =
        bondDeriv (cellCentredExpansion w T.a T.chainParams.ρA (frameRadius x) f Y
            (adjointStepVariable (axialGaugeHolonomy V Y) η))
          (_root_.YangMills.Construction.BlockAverages.gaugeTransform (axialGaugeHolonomy V Y) V) c (axialGaugeRotated V Y c X) := by
    intro k Y η c X hη hX
    refine hG.2.1 F F.top k _ _ V (axialGaugeHolonomy V Y) c X ?_
    refine (eventually_isSmallCurvature_leftTranslate hperN V hV c X hX).mono fun τ hτ => ?_
    exact hblock _ _ hτ Y η fun b => (hη b).le
  refine ⟨fun Y η hη => ?_, fun Y η c X hη hX hc => ?_, fun Y η c X hη hX hc => ?_⟩
  · have e := hblock (axialGaugeHolonomy V Y) V hV Y η fun b => (hη b).le
    rw [← e]
    exact (hfull Y).1 _ (hball Y η hη)
  · rw [hcarry Y η c X hη hX]
    exact (hfull Y).2.1 _ c _ (hball Y η hη) (fun l => by
      show ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction _ _‖ = 1
      rw [norm_adjointAction]
      exact hX l) hc
  · rw [hcarry Y η c X hη hX]
    exact (hfull Y).2.2 _ c _ (hball Y η hη) (fun l => by
      show ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction _ _‖ = 1
      rw [norm_adjointAction]
      exact hX l) hc
end NearUniformTopProof
open NearUniformTopProof
theorem nearUniformTopResponseStatement_holds (hAx : AxialGaugeBondBound) (hG : GaugeCovarianceOfFrame)
    (hends : interpolationAtEndpoints) (hfb : interpolatedFramesControlled)
    (hft : FrameBoundsEventually) (hN : familyNearUniformTopStatement)
    (hj : EventuallyInParametersCombines) : nearUniformTopResponseStatement := by
  refine hj.2 _ _ (fun T hd h => ?_) (hj.1 _ _ hN (hj.1 _ _ hfb hft))
  obtain ⟨⟨R, hR, hb⟩, h1, h2⟩ := h
  exact nearUniformTopResponse_of_family hAx hG hends hd hR h1 h2 hb
end ResponseInTheExpansion
end YangMills.Construction
end
