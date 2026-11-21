import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ColdStepAtMirrorFrames.MovingTheChartCoordinates
import YangMills.Construction.ResponseInTheExpansion.FramesMoveWithTheTop
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import YangMills.Construction.SummableBoundsOfTheFlow.TheFramesBetween
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace ResponseInTheExpansion
namespace MirrorFrames
structure MirrorFrameConditions (T : StepParameters) : Prop where
  odd_L : Odd T.L
  σ_pos : 0 < T.σ
  chart_bound : T.Ct * T.σ + T.σ / 64 ≤ 1 / (64 * (T.L : ℝ))
  curvature_bound : 3 / 4 * T.σ ≤ T.chainParams.σA
theorem eventually_mirrorFrameConditions : EventuallyInParameters MirrorFrameConditions := by
  intro a ha
  refine ⟨2 ^ 40, fun L hL hL₀ c hc => ⟨0, fun Ct hCt => ?_⟩⟩
  have hσA := hc.positivity.2.2.2.1
  have hLp : (0 : ℝ) < L := by
    have : 0 < L := lt_of_lt_of_le (by norm_num) hL₀
    exact_mod_cast this
  refine ⟨1, one_pos, fun κ hκ0 hκ => ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun m _ => ?_⟩⟩⟩
  refine ⟨min c.σA (1 / (64 * L * (Ct + 1))), ?_, fun σ hσ0 hσ p _ => ?_⟩
  · exact lt_min hσA (by positivity)
  have h1 : σ ≤ c.σA := hσ.trans (min_le_left _ _)
  have h2 : σ ≤ 1 / (64 * L * (Ct + 1)) := hσ.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at h2
  have hLσ := mul_pos hLp hσ0
  have hCσ : 0 ≤ Ct * σ := by positivity
  refine ⟨0, fun Cs _ E _ => ⟨0, fun n₀ _ => ⟨0, fun CE _ => ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩
  refine ⟨hL, hσ0, ?_, ?_⟩
  · show Ct * σ + σ / 64 ≤ 1 / (64 * (L : ℝ))
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hCσ hLp.le]
  · show 3 / 4 * σ ≤ c.σA
    linarith
end MirrorFrames
open MirrorFrames in
theorem framesEquivariant_holds (hJ : EventuallyInParametersCombines) (hF : interpolatedFramesStatement)
    (hE : interpolationAtEndpoints) (hM : ChartShiftLipschitz) :
    framesEquivariantStatement := by
  obtain ⟨Cq, Cz, Cr, h⟩ := hF
  refine hJ.2 _ _ (fun T _ hT t x hx F V hFt hV => ?_) (hJ.1 _ _ h eventually_mirrorFrameConditions)
  obtain ⟨hT, hfl⟩ := hT
  have one := ((hT t x hx).one_torus F V 1 hFt hV zero_le_one le_rfl).small
  have hend : segmentEnd false = 1 := by simp [segmentEnd]
  have hfr : ∀ (W : F.GaugeField F.top) (b : F.Site F.depth × Fin 4),
      interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b W =
        stepFrame false T.a T.chainParams.ρA (frameRadius x) b W :=
    fun W b => by
      have := (hE F false T.a T.chainParams.ρA T.chainParams.lam x 0 (frameRadius x) W).1 b
      rwa [hend] at this
  have hab : ∀ η, interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V η =
      coordsAboveFrame false T.a T.chainParams.ρA (frameRadius x) V η :=
    fun η => by
      have := (hE F false T.a T.chainParams.ρA T.chainParams.lam x 0 (frameRadius x) V).2.1 η
      rwa [hend] at this
  refine ⟨fun γ b hb => Subtype.ext ?_, fun g b hb => ?_, fun η hη => ⟨fun q hq => ?_, ?_⟩⟩
  · have e := one.gauge_covariant b hb γ
    rw [hfr, hfr] at e
    exact e
  · have e := one.translation_invariant b hb g
    rw [hfr, hfr] at e
    exact e
  · have h1 := one.small_curvature_nearby η hη q hq
    have h2 := (hE F false T.a T.chainParams.ρA T.chainParams.lam x 0 (frameRadius x) V).2.2.1 η
    rw [hend] at h2
    rwa [h2] at h1
  · have hρ : 0 ≤ T.ballRadius := by
      have := hfl.σ_pos
      unfold StepParameters.ballRadius
      positivity
    have hodd : Odd F.blockSide := by
      rw [hFt.1]
      exact hfl.odd_L
    have hc := (hM F V (fun z i => interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) (z, i) V) η
      T.ballRadius hodd hη hρ).1
    rw [← hab]
    refine ⟨fun b hb => ?_, fun p hp => ?_⟩
    · have h1 := one.norm_le b hb
      have h2 := hc b.1 b.2
      have h3 := hfl.chart_bound
      calc ‖interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V η b.1 b.2‖
          ≤ ‖interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b V‖ + ‖stepCoordinates η b.1 b.2‖ :=
            norm_add_le _ _
        _ ≤ T.Ct * T.σ + T.ballRadius := add_le_add h1 h2
        _ ≤ 1 / (64 * (T.L : ℝ)) := h3
    · exact lt_of_lt_of_le (one.small_curvature_nearby η hη p hp) hfl.curvature_bound
end ResponseInTheExpansion
end YangMills.Construction
end
