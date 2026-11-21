import YangMills.Construction.GeneralTorus.ScaledDistanceEstimates
import YangMills.Construction.Torus.CellsThatMeetAreNearProof
import YangMills.Construction.Torus.LowerBoundsOfTheWeightedLengthProof
import YangMills.Construction.Torus.PartitionsAndLatticesOfATorusProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory Filter Topology YangMills.Construction.TorusMetric
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.GeneralTorus.InfIntegral
section Cubes
variable {S : ℝ}
theorem norm_apply_le_torusSupNorm (x : Torus4 S) (μ : Fin 4) : ‖x μ‖ ≤ torusSupNorm x := by apply _root_.YangMills.Construction.SequenceGeometryProof.norm_apply_le_torusSupNorm <;> assumption
theorem torusSupNorm_le {c : ℝ} (x : Torus4 S) (h : ∀ μ, ‖x μ‖ ≤ c) : torusSupNorm x ≤ c := by apply _root_.YangMills.Construction.GeneralTorus.ScaledDistanceUpper.torusSupNorm_le <;> assumption
theorem isClosed_supCube (σ : ℝ) (z : Torus4 S) : IsClosed (supCube σ z) := by apply _root_.YangMills.Construction.GeneralTorus.CubePartitions.isClosed_supCube <;> assumption
theorem continuous_pointAt (s : LiftedSegment) : Continuous (s.pointAt S) := by apply _root_.YangMills.Construction.Weighted.WeightedLengthProof.continuous_pointAt <;> assumption
theorem measurableSet_segmentsSupport (Γ : List LiftedSegment) :
    MeasurableSet (segmentsSupport S Γ) := by apply _root_.YangMills.Construction.GeneralTorus.WeightedLengthBounds.measurableSet_segmentsSupport <;> assumption
theorem volume_image_le_of_lipschitzOn [Fact (0 < S)] (f : Torus4 S → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (E : Set (Torus4 S))
    (hf : ∀ x ∈ E, ∀ x' ∈ E, |f x - f x'| ≤ κ * torusL1Norm (x - x')) :
    volume (f '' E) ≤ ENNReal.ofReal κ * Weighted.l1LengthMeasure S E := by
  have hemb : MeasurableEmbedding (WithLp.ofLp : Weighted.TorusL1 S → Torus4 S) :=
    (PiLp.homeomorph 1 fun _ : Fin 4 => AddCircle S).toMeasurableEquiv.measurableEmbedding
  have happly : Weighted.l1LengthMeasure S E =
      (μH[1] : Measure (Weighted.TorusL1 S)) (WithLp.ofLp ⁻¹' E) :=
    hemb.map_apply _ _
  have hlip : LipschitzOnWith κ.toNNReal (fun p : Weighted.TorusL1 S => f p.ofLp)
      (WithLp.ofLp ⁻¹' E) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp p' hp' => ?_
    have h : dist p p' = torusL1Norm (p.ofLp - p'.ofLp) := by
      rw [dist_eq_norm, ← Weighted.norm_toLp_eq_torusL1Norm, WithLp.toLp_sub]
    rw [Real.dist_eq, Real.coe_toNNReal _ hκ, h]
    exact hf _ hp _ hp'
  have himg : f '' E = (fun p : Weighted.TorusL1 S => f p.ofLp) '' (WithLp.ofLp ⁻¹' E) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨WithLp.toLp 1 x, by simpa using hx, by simp⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.ofLp, hp, rfl⟩
  have h := hlip.hausdorffMeasure_image_le (d := 1) zero_le_one
  rw [← himg, hausdorffMeasure_real, ENNReal.rpow_one, ← happly] at h
  exact h
theorem volume_image_le_setLIntegral [Fact (0 < S)] (f : Torus4 S → ℝ)
    (w : Torus4 S → ℝ≥0∞) (P : ℕ → Set (Torus4 S)) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hP : ∀ n, MeasurableSet (P n)) (hw : ∀ n, ∀ y ∈ P n, ENNReal.ofReal (c n) ≤ w y)
    (hf : ∀ n, ∀ p ∈ P n, ∀ q ∈ P n, |f p - f q| ≤ c n * torusL1Norm (p - q))
    {E : Set (Torus4 S)} (hE : MeasurableSet E) (hcov : E ⊆ ⋃ n, P n) :
    volume (f '' E) ≤ ∫⁻ y in E, w y ∂(Weighted.l1LengthMeasure S) := by
  let A : ℕ → Set (Torus4 S) := fun n => disjointed P n ∩ E
  have hAP : ∀ n, A n ⊆ P n := fun n => inter_subset_left.trans (disjointed_subset P n)
  have hAm : ∀ n, MeasurableSet (A n) := fun n => (MeasurableSet.disjointed hP n).inter hE
  have hdis : Pairwise (Function.onFun Disjoint A) := fun i j hij =>
    (disjoint_disjointed P hij).mono inter_subset_left inter_subset_left
  have hun : ⋃ n, A n = E := by
    rw [← iUnion_inter, iUnion_disjointed]
    exact inter_eq_right.mpr hcov
  calc volume (f '' E) = volume (⋃ n, f '' A n) := by rw [← image_iUnion, hun]
    _ ≤ ∑' n, volume (f '' A n) := measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ y in A n, w y ∂(Weighted.l1LengthMeasure S) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        refine (volume_image_le_of_lipschitzOn f (c n) (hc n) (A n)
          fun p hp q hq => hf n p (hAP n hp) q (hAP n hq)).trans ?_
        rw [← setLIntegral_const]
        exact setLIntegral_mono' (hAm n) fun y hy => hw n y (hAP n hy)
    _ = ∫⁻ y in ⋃ n, A n, w y ∂(Weighted.l1LengthMeasure S) := (lintegral_iUnion hAm hdis _).symm
    _ = ∫⁻ y in E, w y ∂(Weighted.l1LengthMeasure S) := by rw [hun]
end Cubes
theorem levelSpacing_pos (D : ScaleData) (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
variable {D : ScaleData} (B : SeparatedChain D)
def gridCube (D : ScaleData) (m : ℕ) (k : Fin 4 → ℤ) : Set D.Space :=
  supCube (D.levelSpacing m) (torusProj D.torusSide fun μ => D.levelSpacing m * (k μ : ℝ))
end YangMills.Construction.GeneralTorus.InfIntegral
end
