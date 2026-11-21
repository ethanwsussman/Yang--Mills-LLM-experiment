import YangMills.Construction.Geometry.SegmentDeterminesEndpoints
import YangMills.Construction.Lattice.LengthOfAUnionOfEdges
import YangMills.Construction.Lattice.LiftsOfCubesVerticesAndEdgesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.EdgeUnionLength
open LevelUnitPartition
variable (S : LevelUnitPartition)
theorem L_pos : 0 < S.params.L := by
  have := S.params.isAdmissible.2
  omega
theorem side_pos_real : (0 : ℝ) < (S.side : ℝ) := by apply _root_.YangMills.Construction.PeriodicLattice.CubeLifts.side_cast_pos <;> assumption
theorem l1NormVec_smul_coordVec {a : ℝ} (ha : 0 ≤ a) (ν : Fin 4) :
    TorusMetric.l1NormVec (a • coordVec ν) = a := by
  unfold TorusMetric.l1NormVec
  rw [Finset.sum_eq_single ν]
  · simp [coordVec, abs_of_nonneg ha]
  · intro μ _ h
    simp [coordVec, h]
  · simp
theorem edgeSegment_displacement (w : Fin 4 → ℝ) (ν : Fin 4) :
    (S.edgeSegment w ν).displacement = (S.side : ℝ) • coordVec ν := by
  simp [edgeSegment, TorusMetric.LiftedSegment.displacement]
theorem l1NormVec_edgeSegment_displacement (w : Fin 4 → ℝ) (ν : Fin 4) :
    TorusMetric.l1NormVec (S.edgeSegment w ν).displacement = (S.side : ℝ) := by
  rw [edgeSegment_displacement]
  exact l1NormVec_smul_coordVec (side_pos_real S).le ν
theorem edgeSegmentSet_eq (w : Fin 4 → ℝ) (ν : Fin 4) :
    S.edgeSegmentSet w ν = segmentBetween w (w + (S.side : ℝ) • coordVec ν) := by
  have hM := side_pos_real S
  ext x
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    refine ⟨t / (S.side : ℝ), by positivity, (div_le_one hM).2 h1, ?_⟩
    rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hM.ne']
  · rintro ⟨s, h0, h1, rfl⟩
    refine ⟨s * (S.side : ℝ), by positivity, mul_le_of_le_one_left hM.le h1, ?_⟩
    rw [add_sub_cancel_left, smul_smul]
theorem isSegmentEndpoint_iff (hseg : Segment.SegmentDeterminesEndpoints) (a b z : Fin 4 → ℝ) :
    IsSegmentEndpoint (segmentBetween a b) z ↔ z = a ∨ z = b := by
  constructor
  · rintro ⟨x, x', h, hz⟩
    rcases hseg a b x x' h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rwa [h1, h2] at hz
    · rw [h1, h2] at hz
      exact hz.symm
  · intro h
    exact ⟨a, b, rfl, h⟩
theorem segmentBetween_self (z : Fin 4 → ℝ) : segmentBetween z z = {z} := by
  ext u
  constructor
  · rintro ⟨t, _, _, rfl⟩
    simp
  · intro h
    rw [mem_singleton_iff] at h
    subst h
    exact ⟨0, le_rfl, zero_le_one, by simp⟩
theorem proj_apply (v : Fin 4 → ℝ) (μ : Fin 4) :
    S.proj v μ =
      ((meshSize S.params.L (levelDepth S.params.K S.level) * v μ : ℝ) :
        AddCircle (torusSide S.params.L S.params.m)) := rfl
theorem scaled_side_le_half_torusSide :
    |meshSize S.params.L (levelDepth S.params.K S.level) * (S.side : ℝ)| ≤
      |torusSide S.params.L S.params.m| / 2 := by
  have hL : (1 : ℝ) ≤ (S.params.L : ℝ) := by exact_mod_cast L_pos S
  have hL0 : (S.params.L : ℝ) ≠ 0 := by linarith
  have hexp : (S.sideExponent : ℤ) - levelDepth S.params.K S.level ≤ (S.params.m : ℕ) := by
    have := S.inRange.2
    simp only [levelDepth]
    omega
  have hmain : meshSize S.params.L (levelDepth S.params.K S.level) * (S.side : ℝ) =
      (S.params.L : ℝ) ^ ((S.sideExponent : ℤ) - levelDepth S.params.K S.level) := by
    simp only [meshSize, LevelUnitPartition.side, Nat.cast_pow]
    rw [← zpow_natCast, ← zpow_add₀ hL0]
    congr 1
    ring
  have hle : (S.params.L : ℝ) ^ ((S.sideExponent : ℤ) - levelDepth S.params.K S.level) ≤
      (S.params.L : ℝ) ^ (((S.params.m : ℕ) : ℤ)) := zpow_le_zpow_right₀ hL hexp
  have hpos : (0 : ℝ) ≤ (S.params.L : ℝ) ^ ((S.sideExponent : ℤ) - levelDepth S.params.K S.level) :=
    by positivity
  rw [hmain, abs_of_nonneg hpos, torusSide, abs_of_nonneg (by positivity)]
  rw [zpow_natCast] at hle
  linarith
theorem levelL1Norm_proj_edge (ν : Fin 4) :
    S.levelL1Norm (S.proj ((S.side : ℝ) • coordVec ν)) = (S.side : ℝ) := by
  have hL : (0 : ℝ) < (S.params.L : ℝ) := by exact_mod_cast L_pos S
  have hside : torusSide S.params.L S.params.m ≠ 0 := by
    simp only [torusSide]
    positivity
  have hsum : ∑ μ, ‖S.proj ((S.side : ℝ) • coordVec ν) μ‖ =
      meshSize S.params.L (levelDepth S.params.K S.level) * (S.side : ℝ) := by
    rw [Finset.sum_eq_single ν]
    · rw [proj_apply]
      have hv : ((S.side : ℝ) • coordVec ν) ν = (S.side : ℝ) := by
        simp [coordVec]
      rw [hv, (AddCircle.norm_coe_eq_abs_iff _ hside).2 (scaled_side_le_half_torusSide S)]
      apply abs_of_nonneg
      have := side_pos_real S
      simp only [meshSize]
      positivity
    · intro μ _ h
      rw [proj_apply]
      have hv : ((S.side : ℝ) • coordVec ν) μ = 0 := by
        simp [coordVec, h]
      rw [hv]
      simp
    · simp
  unfold levelL1Norm
  rw [TorusMetric.torusL1Norm_eq_sum_norm, hsum]
  simp only [toLevelUnits, meshSize]
  rw [← mul_assoc, ← zpow_add₀ hL.ne', add_neg_cancel, zpow_zero, one_mul]
theorem levelL1Norm_proj_zero : S.levelL1Norm (S.proj 0) = 0 := by
  have hsum : ∑ μ, ‖S.proj 0 μ‖ = 0 := by
    refine Finset.sum_eq_zero fun μ _ => ?_
    rw [proj_apply]
    simp
  unfold levelL1Norm
  rw [TorusMetric.torusL1Norm_eq_sum_norm, hsum]
  simp [toLevelUnits]
theorem pathLength_edgeSegments (l : List ((Fin 4 → ℝ) × Fin 4)) :
    TorusMetric.pathLength (S.edgeSegments l) = (S.side : ℝ) * (l.length : ℝ) := by
  induction l with
  | nil => simp [TorusMetric.pathLength, edgeSegments]
  | cons p l ih =>
    have step : TorusMetric.pathLength (S.edgeSegments (p :: l)) =
        TorusMetric.l1NormVec (S.edgeSegment p.1 p.2).displacement +
          TorusMetric.pathLength (S.edgeSegments l) := by
      simp [TorusMetric.pathLength, edgeSegments]
    rw [step, ih, l1NormVec_edgeSegment_displacement, List.length_cons]
    push_cast
    ring
theorem length_eq_ncard_of_enumeratesEdges {𝒜 : Set (Set S.Points)}
    {l : List ((Fin 4 → ℝ) × Fin 4)} (h : S.EnumeratesEdges 𝒜 l) : l.length = 𝒜.ncard := by
  classical
  obtain ⟨_, hnd, hmem⟩ := h
  have h𝒜 : 𝒜 = ((l.map fun p => S.edgeAt p.1 p.2).toFinset : Set (Set S.Points)) := by
    ext e
    rw [hmem e]
    simp
  rw [h𝒜, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]
theorem exists_enumeratesEdges {𝒜 : Set (Set S.Points)} (hfin : 𝒜.Finite)
    (hE : ∀ e ∈ 𝒜, ∃ p : (Fin 4 → ℝ) × Fin 4,
      p.1 ∈ S.vertexSet ∧ e = S.edgeAt p.1 p.2) : ∃ l, S.EnumeratesEdges 𝒜 l := by
  classical
  choose! f hf using hE
  have hg : (hfin.toFinset.toList.map f).map (fun p => S.edgeAt p.1 p.2) =
      hfin.toFinset.toList := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id hfin.toFinset.toList]
    refine List.map_congr_left fun e he => ?_
    have he' : e ∈ 𝒜 := by simpa using he
    exact ((hf e he').2).symm
  refine ⟨hfin.toFinset.toList.map f, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
    exact (hf e (by simpa using he)).1
  · rw [hg]
    exact Finset.nodup_toList _
  · intro e
    rw [hg]
    simp
theorem edgeUnionLength_holds (hC : CubeLifts.Statement)
    (hseg : Segment.SegmentDeterminesEndpoints) : EdgeUnionLength := by
  intro S
  obtain ⟨hT, -, -, hV, -, -⟩ := hC.2.2 S
  obtain ⟨-, -, -, -, -, -, hlift, -⟩ := hT
  obtain ⟨-, -, hedge, -⟩ := hV
  have hL : S.params.L ≠ 0 := (L_pos S).ne'
  refine ⟨fun w _ ν => ?_, fun 𝒜 hfin hE _ => ⟨?_, fun l hl => ?_⟩, fun x => ?_⟩
  · have hlif : S.IsSegmentLift (S.edgeAt w ν) (S.edgeSegmentSet w ν) :=
      ⟨⟨_, _, edgeSegmentSet_eq S w ν⟩, rfl⟩
    refine ⟨⟨_, hlif⟩, hlif, fun z => ?_, edgeSegment_displacement S w ν,
      l1NormVec_edgeSegment_displacement S w ν, ?_⟩
    · rw [edgeSegmentSet_eq]
      exact isSegmentEndpoint_iff hseg _ _ z
    · rw [edgeSegment_displacement]
      exact levelL1Norm_proj_edge S ν
  · refine exists_enumeratesEdges S hfin fun e he => ?_
    obtain ⟨w, hw, ν, rfl⟩ := (hedge e).1 (hE e he)
    exact ⟨(w, ν), hw, rfl⟩
  · rw [pathLength_edgeSegments, length_eq_ncard_of_enumeratesEdges S hl]
  · have hpt : ∀ z, S.IsPointLift x z →
        S.IsSegmentLift {x} (segmentBetween z z) := fun z hz => by
      have hproj : S.proj z = x :=
        (levelProj_eq_iff_isLevelLift hL _ _ _ x z).2 hz
      exact ⟨⟨z, z, rfl⟩, by rw [segmentBetween_self, image_singleton, hproj]⟩
    obtain ⟨z₀, hz₀⟩ := hlift x
    refine ⟨⟨_, hpt z₀ hz₀⟩, ⟨z₀, hz₀⟩, fun z hz => ⟨hpt z hz, fun u => ?_, ?_,
      levelL1Norm_proj_zero S⟩⟩
    · rw [isSegmentEndpoint_iff hseg, or_self]
    · simp [TorusMetric.pathLength, degenerateSegment, TorusMetric.LiftedSegment.displacement,
        TorusMetric.l1NormVec]
end YangMills.Construction.PeriodicLattice.EdgeUnionLength
