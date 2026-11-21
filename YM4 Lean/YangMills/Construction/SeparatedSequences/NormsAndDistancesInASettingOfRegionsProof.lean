import YangMills.Construction.SeparatedSequences.ClassGeometryInASettingOfRegionsProof
import YangMills.Construction.SeparatedSequences.ClassGeometryInASettingOfTheTorusOfLevelSideProof
import YangMills.Construction.SeparatedSequences.DivergencesInASettingOfRegionsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Pointwise
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SeparatedClasses.EvaluationOfNorms
open SingleSequence
section EvaluationMaps
variable (s : SequenceData) (𝒮 : RegionSequence.NestedRegions)
theorem Lreal_pos : 0 < s.Lreal := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.Lreal_pos <;> assumption
theorem unitScale_pos : 0 < s.unitScale := pow_pos (Lreal_pos s) _
theorem unitScale_eq_zpow :
    s.unitScale = s.Lreal ^ ((s.data.cutoff : ℤ) - (s.data.t : ℤ)) := by apply _root_.YangMills.Construction.SeparatedClasses.BlockGeometryOfClass.unitScale_eq_zpow <;> assumption
theorem unitTorusSide_eq :
    s.unitTorusSide = s.unitScale * PeriodicLattice.torusSide s.data.L s.data.m := by apply _root_.YangMills.Construction.SeparatedClasses.BlockGeometryOfClass.unitTorusSide_eq <;> assumption
def torusHomeomorph : s.data.Point ≃ₜ 𝒮.Point :=
  Homeomorph.piCongrRight fun _ =>
    AddCircle.homeomorphAddCircle _ _ s.torusSide_ne_zero 𝒮.side_pos.ne'
theorem toTorus_eq (x : s.data.Point) : s.toTorus 𝒮.side x = torusHomeomorph s 𝒮 x := by
  unfold SequenceData.toTorus
  rw [dif_pos 𝒮.side_pos.ne']
  rfl
theorem toTorus_eq_homeomorph : s.toTorus 𝒮.side = torusHomeomorph s 𝒮 :=
  funext (toTorus_eq s 𝒮)
variable {s 𝒮}
theorem torusHomeomorph_torusProj (hs : s.IsNestedRegions 𝒮) (v : Fin 4 → ℝ) :
    torusHomeomorph s 𝒮 (TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m) v) =
      Torus.torusProj 4 𝒮.side (s.unitScale • v) := by
  funext μ
  have hℓ := s.torusSide_ne_zero
  have hc := (unitScale_pos s).ne'
  show AddCircle.homeomorphAddCircle _ _ hℓ 𝒮.side_pos.ne' ((v μ : ℝ) : AddCircle _) = _
  rw [AddCircle.homeomorphAddCircle_apply_mk]
  show _ = ((s.unitScale * v μ : ℝ) : AddCircle 𝒮.side)
  congr 1
  rw [hs.side_eq, unitTorusSide_eq]
  field_simp
theorem supNormVec_eq_norm (v : Fin 4 → ℝ) : TorusMetric.supNormVec v = ‖v‖ := by apply _root_.YangMills.Construction.LevelUnitFacts.supNormVec_eq_norm <;> assumption
end EvaluationMaps
section Pairing
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions} {σ : s.data.BareSite ≃ 𝒮.FineSite}
  {β : s.data.BareBond ≃ 𝒮.FineBond}
theorem bondInner_eq (hs : s.IsNestedRegions 𝒮) (f g : s.data.BondFn) :
    s.data.bondInner f g = RegionSequence.NestedRegions.bondInner (f ∘ β.symm) (g ∘ β.symm) := by apply _root_.YangMills.Construction.SeparatedClasses.RegionDivergences.bondInner_eq_transport <;> assumption
end Pairing
section Segments
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions}
theorem pointAt_scaleSegmentDir (hs : s.IsNestedRegions 𝒮) (g : TorusMetric.LiftedSegment) (τ : ℝ) :
    Torus.TorusSegment.pointAt 𝒮.side (s.scaleSegmentDir g) τ =
      torusHomeomorph s 𝒮 (g.pointAt (PeriodicLattice.torusSide s.data.L s.data.m) τ) := by
  rw [TorusMetric.LiftedSegment.pointAt, torusHomeomorph_torusProj hs]
  show Torus.torusProj 4 𝒮.side (s.unitScale • g.tail + τ • (s.unitScale • g.displacement)) = _
  rw [smul_add, smul_comm τ s.unitScale g.displacement]
theorem segment_length_mul_volume (hs : s.IsNestedRegions 𝒮) (g : TorusMetric.LiftedSegment)
    (X : Set s.data.Point) :
    (s.scaleSegmentDir g).lOneLength *
        (volume {τ ∈ Icc (0 : ℝ) 1 |
          Torus.TorusSegment.pointAt 𝒮.side (s.scaleSegmentDir g) τ ∈
            torusHomeomorph s 𝒮 '' X}).toReal =
      s.unitScale * (TorusMetric.l1NormVec g.displacement * (volume (Icc (0 : ℝ) 1 ∩
        g.pointAt (PeriodicLattice.torusSide s.data.L s.data.m) ⁻¹' X)).toReal) := by
  have hset : {τ ∈ Icc (0 : ℝ) 1 |
      Torus.TorusSegment.pointAt 𝒮.side (s.scaleSegmentDir g) τ ∈ torusHomeomorph s 𝒮 '' X} =
      Icc (0 : ℝ) 1 ∩ g.pointAt (PeriodicLattice.torusSide s.data.L s.data.m) ⁻¹' X := by
    ext τ
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, pointAt_scaleSegmentDir hs,
      (torusHomeomorph s 𝒮).injective.mem_set_image]
  have hlen : (s.scaleSegmentDir g).lOneLength = s.unitScale * TorusMetric.l1NormVec g.displacement := by
    show ∑ μ, |s.unitScale * g.displacement μ| = s.unitScale * ∑ μ, |g.displacement μ|
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by rw [abs_mul, abs_of_pos (unitScale_pos s)]
  rw [hset, hlen, mul_assoc]
theorem lengthWithin_image (hs : s.IsNestedRegions 𝒮) (Γ : List TorusMetric.LiftedSegment)
    (X : Set s.data.Point) :
    Torus.lengthWithin (Γ.map s.scaleSegmentDir) (torusHomeomorph s 𝒮 '' X) =
      s.unitScale * TorusMetric.pathLengthIn (PeriodicLattice.torusSide s.data.L s.data.m) Γ X := by
  induction Γ with
  | nil => simp [Torus.lengthWithin, TorusMetric.pathLengthIn]
  | cons g Γ ih =>
    simp only [Torus.lengthWithin, TorusMetric.pathLengthIn, List.map_cons, List.sum_cons] at ih ⊢
    rw [segment_length_mul_volume hs, ih, mul_add]
theorem segmentUnion_map (hs : s.IsNestedRegions 𝒮) (Γ : List TorusMetric.LiftedSegment) :
    Torus.segmentUnion 𝒮.side (Γ.map s.scaleSegmentDir) =
      torusHomeomorph s 𝒮 '' TorusMetric.segmentsSupport (PeriodicLattice.torusSide s.data.L s.data.m) Γ := by
  ext p
  simp only [Torus.segmentUnion, TorusMetric.segmentsSupport, TorusMetric.LiftedSegment.support,
    mem_ofPred_eq, List.mem_map, mem_image, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, τ, hτ, rfl⟩
    exact ⟨_, ⟨g, hg, τ, hτ, rfl⟩, (pointAt_scaleSegmentDir hs g τ).symm⟩
  · rintro ⟨_, ⟨g, hg, τ, hτ, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, τ, hτ, (pointAt_scaleSegmentDir hs g τ).symm⟩
theorem scaleSegmentDir_surjective : Function.Surjective s.scaleSegmentDir := by apply _root_.YangMills.Construction.SeparatedClasses.BlockGeometryOfClass.scaleSegmentDir_surjective <;> assumption
theorem lengthWithin_nonneg {S : ℝ} (Γ : List (Torus.TorusSegment 4))
    (X : Set (Torus.PeriodicTorus 4 S)) : 0 ≤ Torus.lengthWithin Γ X := by apply _root_.YangMills.Construction.SeparatedClasses.BlockGeometryOfClass.lengthWithin_nonneg <;> assumption
theorem exists_treeGraph_through (x y : s.data.Point) :
    ∃ Γ : List TorusMetric.LiftedSegment,
      TorusMetric.IsTreeGraph (PeriodicLattice.torusSide s.data.L s.data.m) Γ ∧
      x ∈ TorusMetric.segmentsSupport (PeriodicLattice.torusSide s.data.L s.data.m) Γ ∧
      y ∈ TorusMetric.segmentsSupport (PeriodicLattice.torusSide s.data.L s.data.m) Γ := by apply _root_.YangMills.Construction.SeparatedClasses.BlockGeometryOfClass.exists_isTreeGraph_mem <;> assumption
theorem scale_eq_coarseMesh (hs : s.IsNestedRegions 𝒮) (n : ℕ) :
    𝒮.scale n = Conventions.LeveledParameters.coarseMesh s.data.toLeveledParameters n := by apply _root_.YangMills.Construction.SeparatedClasses.NestedGeometryOfClass.scale_eq_coarseMesh <;> assumption
theorem ξ_eq_levelMesh (hs : s.IsNestedRegions 𝒮) :
    𝒮.ξ = s.data.scales.levelMesh s.data.L 0 := by
  rw [hs.ξ_eq]
  unfold SequenceData.mesh Torus.unitSpacing SeparatedSequences.ScaleData.levelMesh
  simp
theorem chainWeight_map (hs : s.IsNestedRegions 𝒮) (hg : s.NestedGeometry 𝒮)
    (Γ : List TorusMetric.LiftedSegment) :
    𝒮.chainWeight (Γ.map s.scaleSegmentDir) = s.data.chainLength s.Ω Γ := by
  have hin : ∀ r, s.data.scales.toUnits s.data.L r = s.unitScale * r := by
    intro r
    rw [unitScale_eq_zpow]
    rfl
  have hun : ∀ i : ℕ, s.data.scales.levelMesh s.data.L i = 𝒮.scale i := fun i =>
    (scale_eq_coarseMesh hs i).symm
  have hmem : SeparatedSequences.truncatedMember s.data.scales s.Ω 1 = s.Ω 1 := by
    by_cases h1 : 1 ≤ s.data.t
    · exact if_pos h1
    · have he : s.Ω 1 = ∅ := s.Ω_mem.2.2 1 (by omega)
      rw [he]
      exact if_neg h1
  have hone : (𝒮.Ω 1)ᶜ =
      torusHomeomorph s 𝒮 '' (SeparatedSequences.truncatedMember s.data.scales s.Ω 1)ᶜ := by
    rw [hmem, hs.Ω_eq, SequenceData.regionOn, toTorus_eq_homeomorph,
      image_compl_eq (torusHomeomorph s 𝒮).bijective]
  have hlay : ∀ n, 𝒮.shellOf n = torusHomeomorph s 𝒮 '' s.data.layerAt s.Ω n := fun n => by
    rw [← hg.layers n, toTorus_eq_homeomorph]
  show _ = SeparatedSequences.layerWeightedLength s.data.scales s.Ω Γ
  rw [RegionSequence.NestedRegions.chainWeight, SeparatedSequences.layerWeightedLength, hs.s_eq,
    hone, lengthWithin_image hs, hin, ξ_eq_levelMesh hs]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hlay n, lengthWithin_image hs, hin, hun]
theorem chainLength_nonneg (hs : s.IsNestedRegions 𝒮) (hg : s.NestedGeometry 𝒮)
    (Γ : List TorusMetric.LiftedSegment) : 0 ≤ s.data.chainLength s.Ω Γ := by
  have hsp : ∀ i : ℕ, 0 ≤ (𝒮.scale i)⁻¹ := fun i => by
    rw [scale_eq_coarseMesh hs]
    exact inv_nonneg.mpr (zpow_pos (Lreal_pos s) _).le
  rw [← chainWeight_map hs hg, RegionSequence.NestedRegions.chainWeight]
  refine add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (hsp _) (lengthWithin_nonneg _ _))
    (mul_nonneg (inv_nonneg.mpr 𝒮.ξ_pos.le) (lengthWithin_nonneg _ _))
theorem weightedDist_set_eq (hs : s.IsNestedRegions 𝒮) (x y : s.data.Point) :
    {r | ∃ Γ : List (Torus.TorusSegment 4),
      IsConnected (Torus.segmentUnion 𝒮.side Γ) ∧
      torusHomeomorph s 𝒮 x ∈ Torus.segmentUnion 𝒮.side Γ ∧
      torusHomeomorph s 𝒮 y ∈ Torus.segmentUnion 𝒮.side Γ ∧ r = 𝒮.chainWeight Γ} =
    (fun Γ => 𝒮.chainWeight (Γ.map s.scaleSegmentDir)) ''
      {Γ | TorusMetric.IsTreeGraph (PeriodicLattice.torusSide s.data.L s.data.m) Γ ∧
        x ∈ TorusMetric.segmentsSupport (PeriodicLattice.torusSide s.data.L s.data.m) Γ ∧
        y ∈ TorusMetric.segmentsSupport (PeriodicLattice.torusSide s.data.L s.data.m) Γ} := by
  ext r
  constructor
  · rintro ⟨Γ', hc, hx, hy, rfl⟩
    obtain ⟨Γ, rfl⟩ := (List.map_surjective_iff.2 (scaleSegmentDir_surjective (s := s))) Γ'
    rw [segmentUnion_map hs] at hc hx hy
    rw [(torusHomeomorph s 𝒮).injective.mem_set_image] at hx hy
    exact ⟨Γ, ⟨(torusHomeomorph s 𝒮).isConnected_image.1 hc, hx, hy⟩, rfl⟩
  · rintro ⟨Γ, ⟨hc, hx, hy⟩, rfl⟩
    refine ⟨Γ.map s.scaleSegmentDir, ?_, ?_, ?_, rfl⟩
    · rw [segmentUnion_map hs]
      exact (torusHomeomorph s 𝒮).isConnected_image.2 hc
    · rw [segmentUnion_map hs, (torusHomeomorph s 𝒮).injective.mem_set_image]
      exact hx
    · rw [segmentUnion_map hs, (torusHomeomorph s 𝒮).injective.mem_set_image]
      exact hy
theorem weightedDist_nonneg (hs : s.IsNestedRegions 𝒮) (hg : s.NestedGeometry 𝒮)
    (x y : s.data.Point) :
    0 ≤ 𝒮.weightedDist (torusHomeomorph s 𝒮 x) (torusHomeomorph s 𝒮 y) := by
  rw [RegionSequence.NestedRegions.weightedDist, weightedDist_set_eq hs]
  refine Real.sInf_nonneg ?_
  rintro _ ⟨Γ, -, rfl⟩
  show 0 ≤ 𝒮.chainWeight (Γ.map s.scaleSegmentDir)
  rw [chainWeight_map hs hg]
  exact chainLength_nonneg hs hg Γ
end Segments
section Apexes
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions} {σ : s.data.BareSite ≃ 𝒮.FineSite}
  {β : s.data.BareBond ≃ 𝒮.FineBond}
end Apexes
end YangMills.Construction.SeparatedClasses.EvaluationOfNorms
end
