import YangMills.Construction.ColdStepAtMirrorFrames.AxialGaugeOfATop
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAreSmallProof
import YangMills.Construction.SummableBoundsOfTheFlow.TopOrderNearTheBlockProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace BlockMeans
namespace GaugeCovariance
variable {F : BlockFrame}
theorem isSmallCurvature_gaugeTransform {j : ℕ} {s : ℝ} (g : F.Site j → UnitQuaternion) {A : F.GaugeField j}
    (h : IsSmallCurvature s A) : IsSmallCurvature s (_root_.YangMills.Construction.BlockAverages.gaugeTransform g A) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SmallFrames.isSmallCurvature_gaugeTransform <;> assumption
theorem eventually_isSmallCurvature_leftTranslate {j k : ℕ} {r : ℝ} (hper : ∀ i, F.period j i ≠ 0)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) {V : F.GaugeField j}
    (hV : IsSmallCurvature r V) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ),
      IsSmallCurvature r (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) := by apply _root_.YangMills.Construction.Interpolation.TopOrderNearBlock.eventually_isSmallCurvature_leftTranslate <;> assumption
theorem interpolatedBlockExpansion_gauge_covariance_at (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hσ : 0 < T.σ) (hL : Odd T.L)
    (hn : 2 ≤ T.n₀) {s C : ℝ} {t k m : ℕ} {e : ℕ → ℝ} {f : LocalFamily} (F : BlockFrame)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (γ : F.Cell → UnitQuaternion)
    (hR : GaugeCovarianceOfFrame) (hA : AxialGaugeBondBound)
    (hB : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      InterpolatedFrameSmall s T.a T.chainParams.ρA T.chainParams.δ₂ C T.σ m V')
    (hd : HasBoundedDerivatives T.L t T.n₀ T.σ T.decayRate k e f) (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hη : ∀ b, ‖η b‖ ≤ T.ballRadius) :
    IsSmallCurvature (5 / 4 * T.σ) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) ∧
    (∀ R : ℕ, (∀ i, 2 * R + 2 < F.extent i) →
      IsNearUniformAbout (5 / 4 * T.σ) R (_root_.YangMills.Construction.BlockAverages.gaugeTransform (axialGaugeHolonomy V Y) V) Y) ∧
    bondDeriv (interpolatedBlockExpansion s T.a T.chainParams.ρA m f Y η) V c X =
      bondDeriv (interpolatedBlockExpansion s T.a T.chainParams.ρA m f Y (adjointStepVariable γ η))
        (gaugeTransform γ V) c fun l => _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (c l).1) (X l) := by
  obtain ⟨hFL, hFt, n, hside, hnn⟩ := hF
  have hLpos : 0 < T.L := hL.pos
  have hlow : IsCubicTorusAbove T.L t T.n₀ F :=
    ⟨hFL, hFt, n, hside, hnn.trans (Nat.le_mul_of_pos_right n hLpos)⟩
  have hper : ∀ i, F.period F.top i ≠ 0 := fun i => by
    simp only [BlockFrame.period, Nat.sub_self, pow_zero, mul_one, hside i]
    omega
  have h2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside i]
    omega
  have hodd : Odd F.blockSide := hFL ▸ hL
  refine ⟨_root_.YangMills.Construction.BlockMeans.GaugeCovariance.isSmallCurvature_gaugeTransform γ hV, fun R hRs r b hr hb => ?_, ?_⟩
  · exact hA F V Y (5 / 4 * T.σ) r (fun i => by have := hRs i; omega) (by positivity) hV b hb
  · refine hR.2.1 F F.top k _ _ V γ c X ?_
    filter_upwards [eventually_isSmallCurvature_leftTranslate hper c X hV] with τ hτ
    have hs := hB _ hτ
    unfold interpolatedBlockExpansion
    refine Finset.sum_congr rfl fun y _ => ?_
    have hfield : interpolatedField s T.a T.chainParams.ρA m
        (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) (adjointStepVariable γ η) =
        _root_.YangMills.Construction.BlockAverages.gaugeTransform (fun z => γ (enclosingCell z))
          (interpolatedField s T.a T.chainParams.ρA m
            (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) η) :=
      hR.1 F (fun b W => interpolatedFrame s T.a T.chainParams.ρA m b W) _ γ η hodd h2
        fun b hb => Subtype.ext (hs.gauge_covariant b hb γ)
    have hcold : IsSmallCurvature T.σ
        (interpolatedField s T.a T.chainParams.ρA m
          (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) η) :=
      fun p hp => ((hs.small_curvature_nearby η hη) p hp).trans (by linarith)
    simp only [interpolatedExpansion, ColdStepAtMirrorFrames.subtractTrivial]
    rw [hfield, hd.gauge_invariant F hlow y _ _ hcold]
end GaugeCovariance
open GaugeCovariance in
theorem interpolatedBlockExpansionGaugeCovariance_holds (hF : interpolatedFramesStatement)
    (hR : GaugeCovarianceOfFrame) (hA : AxialGaugeBondBound) : interpolatedBlockExpansionGaugeCovariance := by
  obtain ⟨Cq, Cz, Cr, hT⟩ := hF
  intro a ha
  obtain ⟨L₀, h1⟩ := hT a ha
  refine ⟨L₀, fun L hL hL₀ c hc => ?_⟩
  obtain ⟨Ct₀, h2⟩ := h1 L hL hL₀ c hc
  refine ⟨Ct₀, fun Ct hCt => ?_⟩
  obtain ⟨κ₀, hκ₀, h3⟩ := h2 Ct hCt
  refine ⟨κ₀, hκ₀, fun κ hκ hκ' => ?_⟩
  obtain ⟨η₀, hη₀, h4⟩ := h3 κ hκ hκ'
  refine ⟨η₀, hη₀, fun η₃ a1 a2 a3 => ?_⟩
  obtain ⟨N₀, h5⟩ := h4 η₃ a1 a2 a3
  refine ⟨N₀, fun nss hn => ?_⟩
  obtain ⟨σ₀, hσ₀, h6⟩ := h5 nss hn
  refine ⟨σ₀, hσ₀, fun σ hσ hσ' p hp => ?_⟩
  obtain ⟨C₀, h7⟩ := h6 σ hσ hσ' p hp
  refine ⟨C₀, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₀, h8⟩ := h7 Cs hCs E hE
  refine ⟨max m₀ 2, fun n₀ hn₀ => ?_⟩
  obtain ⟨C₁, h9⟩ := h8 n₀ (le_trans (le_max_left _ _) hn₀)
  refine ⟨C₁, fun CE hCE => ?_⟩
  obtain ⟨y₀, h10⟩ := h9 CE hCE
  refine ⟨y₀, fun y₁ hy => ?_⟩
  have hT' := h10 y₁ hy
  intro x t k e f F V s η Y c X γ hx hd hFt hV hs0 hs1 hη
  exact interpolatedBlockExpansion_gauge_covariance_at _ hσ hL (le_trans (le_max_right _ _) hn₀) F V η Y c X γ hR hA
    (fun V' hV' => (((hT' t x hx).one_torus F V' s hFt hV' hs0 hs1).small)) hd hFt hV hη
end BlockMeans
end YangMills.Construction
end
