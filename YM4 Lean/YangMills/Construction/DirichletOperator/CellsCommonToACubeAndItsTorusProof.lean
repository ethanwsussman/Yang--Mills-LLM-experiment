import YangMills.Construction.DirichletOperator.CellsCarriedToTheLocalTorusProof
import YangMills.Construction.DirichletOperator.CellsOfACube
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PartitionCubes.SharedCellsProof
section Lengths
variable {S : ℝ}
theorem exists_lift_abs_eq_norm (p : Torus.PeriodicTorus 4 S) :
    ∃ v : Fin 4 → ℝ, Torus.torusProj 4 S v = p ∧ ∀ μ, |v μ| = ‖p μ‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.exists_lift_abs_eq_norm <;> assumption
theorem supNorm_eq_norm (p : Torus.PeriodicTorus 4 S) : Torus.supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem mem_cubeAt_iff {y p : Torus.PeriodicTorus 4 S} {σ : ℝ} :
    p ∈ Torus.cubeAt y σ ↔ ‖p - y‖ ≤ σ / 2 := by apply _root_.YangMills.Construction.PartitionCubes.CellsTransferProof.mem_cubeAt_iff <;> assumption
theorem mem_interior_cubeAt (y : Torus.PeriodicTorus 4 S) {σ : ℝ} (hσ : 0 < σ) :
    y ∈ interior (Torus.cubeAt y σ) := by apply _root_.YangMills.Construction.PartitionCubes.CellsTransferProof.mem_interior_cubeAt <;> assumption
end Lengths
section Centres
variable (R : RegionSequence.NestedRegions)
theorem scale_pos (j : ℕ) : 0 < R.scale j := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem scale_zero : R.scale 0 = R.ξ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.scale_zero <;> assumption
theorem Ω_antitone {a b : ℕ} (h : a ≤ b) : R.Ω b ⊆ R.Ω a := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusBonds.regions_antitone <;> assumption
theorem side_mem_zmultiples_scale {j : ℕ} (hj : j ≤ R.s) :
    ∃ c : ℤ, R.side = (c : ℝ) * R.scale j := by
  obtain ⟨k, hk⟩ := R.side_mem_zmultiples
  have e : Torus.scaleSpacing R.L R.ξ (R.s : ℤ) = (R.L : ℝ) ^ (R.s - j) * R.scale j := by
    change R.scale R.s = _
    rw [RegionSequence.NestedRegions.scale_eq_pow_mul, RegionSequence.NestedRegions.scale_eq_pow_mul,
      ← mul_assoc, ← pow_add, Nat.sub_add_cancel hj]
  refine ⟨k * (2 * (R.L : ℤ) ^ (R.s - j)), ?_⟩
  rw [hk, e]
  push_cast
  ring
structure CentreData (y : R.Point) (j : ℕ) : Prop where
  level_eq : R.level y = j
  cellOf_eq : R.cellOf y = Torus.cubeAt y (R.scale j)
  cellOf_subset : R.cellOf y ⊆ R.Ω j
variable {R}
theorem centreData_of_mem (C : RegionSequence.ShellCells R) {y : R.Point} {j : ℕ}
    (hy : y ∈ R.centresAt j) : CentreData R y j := by
  have hj : j ≤ R.s := by
    by_contra h
    rw [R.centresAt_eq_empty_of_lt (by omega)] at hy
    exact hy
  have hset : {n | y ∈ Torus.shellSites R.L R.ξ R.Ω n}.Nonempty := ⟨j, hy⟩
  have hiy : y ∈ R.centresAt (R.level y) := Nat.sInf_mem hset
  have hij : R.level y ≤ j := Nat.sInf_le hy
  have his : R.level y ≤ R.s := hij.trans hj
  have hcell : R.cellOf y = Torus.cubeAt y (R.scale (R.level y)) := rfl
  have hmem : R.cellOf y ∈ {Q ∈ R.cubePartitionAt (R.level y) |
      Q ⊆ R.Ω (R.level y) ∧ ¬ Q ⊆ R.Ω (R.level y + 1)} := by
    rw [C.shellCubes_eq _ his]
    exact ⟨y, hiy, rfl⟩
  have hint : y ∈ interior (R.cellOf y) := by
    rw [hcell]
    exact mem_interior_cubeAt y (scale_pos R _)
  have hnot : y ∉ R.Ω (R.level y + 1) := fun h =>
    Set.disjoint_left.1 (C.interior_disjoint_next _ his _ hmem) hint h
  have hsubj := C.cellOf_subset j hj y hy
  have hyj : y ∈ R.Ω j := (hsubj.2 (hsubj.1 (interior_subset hint))).1
  have hii : R.level y = j := by
    by_contra hne
    exact hnot (Ω_antitone R (by omega) hyj)
  refine ⟨hii, ?_, fun p hp => (hsubj.2 (hsubj.1 hp)).1⟩
  rw [hcell, hii]
theorem mem_cellOf_self (C : RegionSequence.ShellCells R) {y : R.Point} {j : ℕ}
    (hy : y ∈ R.centresAt j) : y ∈ R.cellOf y := by
  rw [(centreData_of_mem C hy).cellOf_eq, mem_cubeAt_iff, sub_self, norm_zero]
  have := scale_pos R j
  positivity
end Centres
variable {N : RegionSequence.NestedRegions} {M : ℕ}
structure FirstTypeData (Q : LevelCube N M) : Prop where
  embed_injOn : InjOn Q.system.embed Q.strictPts
  embed_lattice : ∀ j : ℕ, j ≤ Q.level ∨ (j = Q.level + 1 ∧ Q.level < N.s) →
    ∀ x ∈ (Torus.spacingLattice 4 N.side (N.scale j) : Set N.Point), x ∈ Q.strictPts →
      Q.system.embed x ∈ Torus.spacingLattice 4 Q.system.setting.side (N.scale j)
  scale_eq : ∀ j, Q.system.setting.scale j = N.scale j
  top_eq : Q.system.setting.s = Q.level + 1
  Ω_eq_univ : ∀ j ≤ Q.level, Q.system.setting.Ω j = univ
  cells : RegionSequence.ShellCells N
  localCells : RegionSequence.ShellCells Q.system.setting
  centre_level : ∀ y ∈ N.allCentres, (N.cellOf y ∩ Q.thicken (5 / 6)).Nonempty →
    y ∈ N.centresAt Q.level ∨ y ∈ N.centresAt (Q.level + 1)
  cellOf_subset : ∀ y ∈ N.allCentres, (N.cellOf y ∩ Q.thicken (5 / 6)).Nonempty →
    N.cellOf y ⊆ Q.strictPts
  cellOf_image : ∀ y ∈ N.allCentres, (N.cellOf y ∩ Q.thicken (5 / 6)).Nonempty →
    ∃ y' ∈ Q.system.setting.allCentres,
      Q.system.embed '' N.cellOf y = Q.system.setting.cellOf y' ∧
        Q.system.setting.level y' = N.level y
variable {Q : LevelCube N M}
theorem mapBond_source (hsite : ∀ x : N.FineSite, (x : N.Point) ∈ Q.strictPts →
      Q.system.embed x ∈ Torus.spacingLattice 4 Q.system.setting.side Q.system.setting.ξ)
    (b : N.FineBond) (hb : (b.source : N.Point) ∈ Q.strictPts) :
    ((Q.system.mapBond b).source : Q.system.setting.Point) =
      Q.system.embed (b.source : N.Point) :=
  Classical.epsilon_spec
    (p := fun y : Q.system.setting.FineSite =>
      (y : Q.system.setting.Point) = Q.system.embed (b.source : N.Point))
    ⟨⟨_, hsite b.source hb⟩, rfl⟩
end YangMills.Construction.PartitionCubes.SharedCellsProof
