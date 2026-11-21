import YangMills.Construction.DirichletOperator.OperatorsComparingACubeWithTheTorus
import YangMills.Construction.RegionSequence.GaugeProjectionsProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.CubeTorusComparison
open YangMills.Construction.CubeTorus (torusSetting)
noncomputable section
namespace YangMills.Construction.ProjTransferCommutator
theorem finite_spacingLattice {σ S : ℝ} (K : ℤ) (hK : K ≠ 0) (hS : S = K * σ) :
    (spacingLattice 4 S σ : Set (PeriodicTorus 4 S)).Finite := by apply _root_.YangMills.Construction.RegionSequence.GaugeProjections.spacingLattice_finite <;> assumption
section Counting
variable (𝒮 : NestedRegions)
theorem scaleSpacing_pos (n : ℤ) : 0 < scaleSpacing 𝒮.L 𝒮.ξ n := by apply _root_.YangMills.Construction.PartitionCubes.FirstTypeMaps.scaleSpacing_pos <;> assumption
theorem exists_side_eq_mul :
    ∃ k : ℤ, 0 < k ∧ 𝒮.side = (k : ℝ) * (2 * ((𝒮.L : ℝ) ^ 𝒮.s * 𝒮.ξ)) := by apply _root_.YangMills.Construction.RegionSequence.GaugeProjections.side_eq_int_mul <;> assumption
instance instFiniteFineSite : Finite 𝒮.FineSite := by
  obtain ⟨k, hk, hside⟩ := exists_side_eq_mul 𝒮
  have hne : k * 2 * (𝒮.L : ℤ) ^ 𝒮.s ≠ 0 := by
    have : (𝒮.L : ℤ) ≠ 0 := by
      have := 𝒮.thirteen_le_L
      omega
    positivity
  refine (finite_spacingLattice (k * 2 * (𝒮.L : ℤ) ^ 𝒮.s) hne ?_).to_subtype
  rw [hside]
  push_cast
  ring
theorem mem_spacingLattice_of_mem_scale (n : ℕ) {y : 𝒮.Point}
    (hy : y ∈ spacingLattice 4 𝒮.side (𝒮.scale n)) :
    y ∈ spacingLattice 4 𝒮.side 𝒮.ξ := by apply _root_.YangMills.Construction.RegionSequence.GaugeProjections.mem_spacingLattice_of_scale <;> assumption
instance instFiniteAllCentres : Finite 𝒮.allCentres := by
  have hf : (spacingLattice 4 𝒮.side 𝒮.ξ : Set 𝒮.Point).Finite :=
    Set.finite_coe_iff.1 (instFiniteFineSite 𝒮)
  refine (hf.subset ?_).to_subtype
  rintro y ⟨n, _, hy⟩
  exact mem_spacingLattice_of_mem_scale 𝒮 n hy.2.1
end Counting
section Pairings
variable {𝒮 : NestedRegions}
theorem innerSum_comm (a b : 𝒮.FineSite → ℝ) : innerSum a b = innerSum b a := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.innerSum_comm <;> assumption
theorem levelScale_pos (y : 𝒮.Point) : 0 < 𝒮.levelScale y := scaleSpacing_pos 𝒮 _
end Pairings
section Linearity
variable {𝒮 : NestedRegions}
end Linearity
section Cube
variable {𝒮 : NestedRegions} {M : ℕ} (Q : LevelCube 𝒮 M)
variable {Q}
end Cube
end YangMills.Construction.ProjTransferCommutator
