import YangMills.Construction.Continuum.SharpNormOfATestFunctionAndNeighbourhoodsOfDisjointCompactSetsProof
import YangMills.Construction.SystemsWithFiveBounds.OnePointOfALimitAtNumbers
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open TestFunctions
open BoundsOnEverySide (unitMassBumps)
open TorusMetric (euclidNormVec)
private theorem euclidNormVec_le_two_mul_norm (v : Fin 4 → ℝ) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
private theorem isLipschitzFor_of_contDiff {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) : IsLipschitzFor euclidDistR4 f := by apply _root_.YangMills.Construction.Continuum.SeparatedFourTuples.SharpNormAndThickenings.isLipschitzFor_of_contDiff <;> assumption
private theorem unitMassBumps_nonempty : unitMassBumps.Nonempty := by
  let b : ContDiffBump (0 : Fin 4 → ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, ⟨b.contDiff_normed, b.hasCompactSupport_normed, subset_univ _⟩, ?_,
    b.integral_normed⟩
  rw [b.tsupport_normed_eq]
  intro y hy
  have hdist : dist y 0 ≤ 1 / 2 := hy
  have hnorm : ‖y‖ ≤ 1 / 2 := by simpa using hdist
  have hcmp := euclidNormVec_le_two_mul_norm (y - 0)
  rw [sub_zero] at hcmp
  show euclidNormVec (y - 0) ≤ 1
  rw [sub_zero]
  linarith
theorem onePointLimitWithConstants_holds : OnePointLimitWithConstants := by
  intro F N B K β ρ ν hd hρ hν
  have hpoint : ∀ (R : ℝ) (f : InfiniteLattice.AmbientSpace → ℝ) (z : ℝ), 0 < R →
      IsLipschitzFor euclidDistR4 f → (∃ x, tsupport f ⊆ closedBallR4 x R) →
      Tendsto (fun k => (∫ U, InfiniteLattice.smearedEnergy f U ∂ρ k) -
        ∫ U, InfiniteLattice.smearedEnergy f U ∂ν k) atTop (𝓝 z) →
        |z| ≤ N.onePointConst R * sharpNormR4 F.M f := by
    intro R f z hR hLip hball hlim
    exact le_of_tendsto hlim.abs (Eventually.of_forall fun k =>
      B.mean_sub_le (K k) (β k) (hd k) (ρ k) (hρ k) (ν k) (hν k) R hR f hLip hball)
  refine ⟨hpoint, fun c hc => ?_⟩
  have hC0 : 0 ≤ N.onePointConst 1 := B.admissible_constants.onePointConst_nonneg 1 one_pos
  have heach : ∀ f ∈ unitMassBumps, |c| ≤ N.onePointConst 1 * sharpNormR4 F.M f := fun f hf =>
    hpoint 1 f c one_pos (isLipschitzFor_of_contDiff hf.1.1 hf.1.2.1) ⟨0, hf.2.1⟩ (hc f hf)
  unfold unitBallBound
  rcases hC0.eq_or_lt with h0 | hC
  · obtain ⟨f, hf⟩ := unitMassBumps_nonempty
    have := heach f hf
    rw [← h0, zero_mul] at this
    rw [← h0, zero_mul]
    exact this
  · have hle : |c| / N.onePointConst 1 ≤ sInf (sharpNormR4 F.M '' unitMassBumps) := by
      refine le_csInf (unitMassBumps_nonempty.image _) ?_
      rintro _ ⟨f, hf, rfl⟩
      rw [div_le_iff₀' hC]
      exact heach f hf
    rw [div_le_iff₀' hC] at hle
    exact hle
end YangMills.Construction.SystemsWithFiveBounds
end
