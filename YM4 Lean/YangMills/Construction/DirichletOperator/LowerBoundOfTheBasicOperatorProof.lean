import YangMills.Construction.DirichletOperator.BoundsOnTheApproximateInverse
import YangMills.Construction.DirichletOperator.BoundsOnTheOperatorsOfASeparatedSequenceProof
import YangMills.Construction.DirichletOperator.ExistenceAndExpansionOfThePropagatorProof
import YangMills.Construction.DirichletOperator.WeightedDistanceOutOfACubeProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.Propagator YangMills.Construction.PropagatorThresholds YangMills.Construction.RemainderEstimates YangMills.Construction.Weighted
noncomputable section
namespace YangMills.Construction.BaseOperatorCoercivity
theorem finite_fineSite (𝒯 : NestedRegions) : Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineSite <;> assumption
theorem finite_fineBond (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineBond <;> assumption
theorem allCentres_subset_spacingLattice (𝒯 : NestedRegions) {y : 𝒯.Point} (hy : y ∈ 𝒯.allCentres) :
    y ∈ spacingLattice 4 𝒯.side 𝒯.ξ := by
  obtain ⟨n, -, -, ⟨a, rfl⟩, -⟩ := hy
  refine ⟨fun μ => a μ * ((𝒯.L ^ n : ℕ) : ℤ), ?_⟩
  funext μ
  simp only [torusProj, scaleSpacing]
  push_cast
  congr 1
  simp only [zpow_natCast]
  ring
section Pairing
variable {𝒮 : NestedRegions} [Fintype 𝒮.FineBond]
theorem bondInner_eq_sum (A A' : 𝒮.FineBond → ℝ) :
    bondInner A A' = 𝒮.ξ ^ 4 * ∑ b, A b * A' b := by
  rw [bondInner, finsum_eq_sum_of_fintype]
theorem bondInner_comm (A A' : 𝒮.FineBond → ℝ) : bondInner A A' = bondInner A' A := by
  simp only [bondInner_eq_sum, mul_comm (A _)]
theorem bondInner_sub_left (A A' B : 𝒮.FineBond → ℝ) :
    bondInner (A - A') B = bondInner A B - bondInner A' B := by
  simp only [bondInner_eq_sum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]
theorem eq_zero_of_bondInner_self {A : 𝒮.FineBond → ℝ} (h : bondInner A A = 0) : A = 0 := by apply _root_.YangMills.Construction.PropagatorProof.eq_zero_of_bondInner_self <;> assumption
theorem ltwoBond_nonneg (A : 𝒮.FineBond → ℝ) : 0 ≤ ltwoBond A := Real.sqrt_nonneg _
def toEuclidean (A : 𝒮.FineBond → ℝ) : EuclideanSpace ℝ 𝒮.FineBond :=
  WithLp.toLp 2 fun b => 𝒮.ξ ^ 2 * A b
end Pairing
theorem weightedDist_comm (𝒮 : NestedRegions) (y y' : 𝒮.Point) :
    𝒮.weightedDist y y' = 𝒮.weightedDist y' y := by apply _root_.YangMills.Construction.PartitionCubes.WeightedDistFromCube.weightedDist_comm <;> assumption
theorem levelScale_pos (𝒮 : NestedRegions) (y : 𝒮.Point) : 0 < 𝒮.levelScale y := by apply _root_.YangMills.Construction.RegionSequence.OperatorEstimates.levelScale_pos <;> assumption
theorem levelScale_le_one {𝒮 : NestedRegions} (hξ : 𝒮.ξ = unitSpacing 𝒮.L 𝒮.s) {y : 𝒮.Point}
    (hy : y ∈ 𝒮.allCentres) : 𝒮.levelScale y ≤ 1 := by
  obtain ⟨n, hn, hyn⟩ := hy
  have hidx : shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y ≤ n := Nat.sInf_le hyn
  have hL : (1 : ℝ) ≤ 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 1 ≤ 𝒮.L)
  have hL₀ : (0 : ℝ) < 𝒮.L := by linarith
  show scaleSpacing 𝒮.L 𝒮.ξ (shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y) ≤ 1
  generalize shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y = i at hidx
  rw [scaleSpacing, hξ, unitSpacing, ← zpow_add₀ hL₀.ne']
  exact zpow_le_one_of_nonpos₀ hL (by omega)
end YangMills.Construction.BaseOperatorCoercivity
