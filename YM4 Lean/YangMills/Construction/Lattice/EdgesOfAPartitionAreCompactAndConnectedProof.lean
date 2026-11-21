import YangMills.Construction.Lattice.EdgesOfAPartitionAreCompactAndConnected
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.PeriodicLattice.LevelUnitPartitionEdges
variable (S : LevelUnitPartition)
theorem continuous_proj : Continuous S.proj := by
  unfold LevelUnitPartition.proj levelProj TorusMetric.torusProj
  refine continuous_pi fun μ => ?_
  exact (AddCircle.continuous_mk' _).comp ((continuous_apply μ).comp (continuous_const_smul _))
theorem edgeAt_eq_image (w : Fin 4 → ℝ) (ν : Fin 4) :
    S.edgeAt w ν =
      (fun t : ℝ => S.proj (w + t • coordVec ν)) '' Icc 0 (S.side : ℝ) := by
  ext x
  constructor
  · rintro ⟨_, ⟨t, h0, hM, rfl⟩, rfl⟩
    exact ⟨t, ⟨h0, hM⟩, rfl⟩
  · rintro ⟨t, ⟨h0, hM⟩, rfl⟩
    exact ⟨_, ⟨t, h0, hM, rfl⟩, rfl⟩
theorem continuous_proj_line (w : Fin 4 → ℝ) (ν : Fin 4) :
    Continuous fun t : ℝ => S.proj (w + t • coordVec ν) :=
  (continuous_proj S).comp
    (continuous_const.add (continuous_id.smul continuous_const))
theorem side_nonneg : (0 : ℝ) ≤ (S.side : ℝ) := Nat.cast_nonneg _
theorem levelUnitPartitionEdgesCompactConnected_holds :
    LevelUnitPartitionEdgesCompactConnected := by
  intro S e he
  obtain ⟨Δ, -, y, -, c, -, ε, ν, -, -, rfl⟩ := he
  rw [show S.edgeAt (c + ((S.side : ℝ) / 2) • ε) ν = _ from edgeAt_eq_image S _ ν]
  refine ⟨isCompact_Icc.image (continuous_proj_line S _ ν),
    (isConnected_Icc (side_nonneg S)).image _ (continuous_proj_line S _ ν).continuousOn, ?_⟩
  rintro v ⟨w, -, ν', he, hv⟩
  rw [← edgeAt_eq_image S _ ν] at he ⊢
  rw [he]
  rcases hv with rfl | rfl
  · exact ⟨w, ⟨0, le_rfl, side_nonneg S, by simp⟩, rfl⟩
  · exact ⟨_, ⟨_, side_nonneg S, le_rfl, rfl⟩, rfl⟩
end YangMills.Construction.PeriodicLattice.LevelUnitPartitionEdges
