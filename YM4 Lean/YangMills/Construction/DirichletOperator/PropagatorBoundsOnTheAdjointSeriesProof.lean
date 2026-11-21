import YangMills.Construction.Torus.BoundOnTheScaledRemainderBlocksProof
import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.PropagatorBoundsForDivergenceSourcesProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes Weighted
namespace AdjointNeumannBounds
theorem finite_fineBond (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineBond <;> assumption
section Norms
variable {𝒮 : NestedRegions}
theorem supBond_nonneg (f : 𝒮.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem abs_le_supBond (f : 𝒮.FineBond → ℝ) (b : 𝒮.FineBond) : |f b| ≤ supBond f := by
  have := finite_fineBond 𝒮
  exact le_ciSup (f := fun b => ‖f b‖) (Set.finite_range _).bddAbove b
theorem supBond_le (f : 𝒮.FineBond → ℝ) {c : ℝ} (hc : 0 ≤ c) (h : ∀ b, |f b| ≤ c) :
    supBond f ≤ c :=
  Real.iSup_le h hc
theorem supSite_nonneg (f : 𝒮.FineSite → ℝ) : 0 ≤ supSite f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem abs_le_supSite (f : 𝒮.FineSite → ℝ) (x : 𝒮.FineSite) : |f x| ≤ supSite f := by apply _root_.YangMills.Construction.DivSourceEstimate.abs_le_supSite <;> assumption
theorem supTensor_nonneg {r : ℕ} (J : 𝒮.Tensor r) : 0 ≤ supTensor J :=
  Real.iSup_nonneg fun _ => supBond_nonneg _
theorem ltwoTensor_nonneg {r : ℕ} (J : 𝒮.Tensor r) : 0 ≤ ltwoTensor J := by apply _root_.YangMills.Construction.CornerGreen.ltwoTensor_nonneg' <;> assumption
end Norms
theorem supNorm_add_le {S : ℝ} (p q : PeriodicTorus 4 S) :
    supNorm (p + q) ≤ supNorm p + supNorm q := by apply _root_.YangMills.Construction.PartitionCubes.PartitionFnSupport.torusSupNorm_add_le <;> assumption
section Distance
variable (𝒯 : NestedRegions)
theorem weightedDist_nonneg (y y' : 𝒯.Point) : 0 ≤ 𝒯.weightedDist y y' := by apply _root_.YangMills.Construction.DivSourceEstimate.weightedDist_nonneg <;> assumption
theorem weightedDist_comm (y y' : 𝒯.Point) :
    𝒯.weightedDist y y' = 𝒯.weightedDist y' y := by apply _root_.YangMills.Construction.PartitionCubes.WeightedDistFromCube.weightedDist_comm <;> assumption
theorem levelScale_pos (y : 𝒯.Point) : 0 < 𝒯.levelScale y := by apply _root_.YangMills.Construction.RegionSequence.OperatorEstimates.levelScale_pos <;> assumption
theorem ξ_le_levelScale (y : 𝒯.Point) : 𝒯.ξ ≤ 𝒯.levelScale y := by apply _root_.YangMills.Construction.DivSourceEstimate.ξ_le_levelScale <;> assumption
theorem levelScale_le_one (hξ : 𝒯.ξ = unitSpacing 𝒯.L 𝒯.s) {y : 𝒯.Point} (hy : y ∈ 𝒯.allCentres) :
    𝒯.levelScale y ≤ 1 := by apply _root_.YangMills.Construction.BaseOperatorCoercivity.levelScale_le_one <;> assumption
end Distance
section Estimates
variable {𝒮 : NestedRegions} {M R₁ : ℕ}
theorem wideCell_subset_outerCube (y : 𝒮.Point) :
    Propagator.wideCell y ⊆ ApproxInverseScales.outerCube y := by apply _root_.YangMills.Construction.DivSourceEstimate.wideCell_subset_outerCube <;> assumption
variable (c : ApproxInverseBounds.Constants) {κ : ℝ}
end Estimates
section Terms
variable {𝒮 : NestedRegions} {M R₁ : ℕ}
theorem cellOf_subset_Ω_zero (hc : CellStructure.CellFacts 𝒮) {y : 𝒮.Point}
    (hy : y ∈ 𝒮.allCentres) : 𝒮.cellOf y ⊆ 𝒮.Ω 0 := by
  intro p hp
  rw [← hc.union_eq]
  exact mem_iUnion₂.2 ⟨y, hy, hp⟩
theorem exists_near_cell (hc : CellStructure.CellFacts 𝒮) (hbp : CellStructure.AnchorFacts 𝒮)
    (hd : CubeGeometry.WeightedDistComparisons 𝒮 M) (y : 𝒮.allCentres) {b : 𝒮.FineBond}
    (hb : b ∈ 𝒮.bonds) (ht : (b.source : 𝒮.Point) ∈ Propagator.wideCell (y : 𝒮.Point)) :
    ∃ z : 𝒮.allCentres, AnchoredIn (𝒮.cellOf z) b ∧ 𝒮.weightedDist y z ≤ 3 * 4 * (𝒮.L : ℝ) := by
  obtain ⟨hx, hlen, -⟩ := hbp.anchor_spec b hb
  obtain ⟨z, hz, hint, -⟩ := hc.fine_site (𝒮.anchor b) hx
  have hcent : 𝒮.centreOfSite (𝒮.anchor b) ∈ 𝒮.allCentres ∧
      ((𝒮.anchor b : 𝒮.FineSite) : 𝒮.Point) ∈ 𝒮.cellOf (𝒮.centreOfSite (𝒮.anchor b)) :=
    Classical.epsilon_spec (p := fun y => y ∈ 𝒮.allCentres ∧
      ((𝒮.anchor b : 𝒮.FineSite) : 𝒮.Point) ∈ 𝒮.cellOf y) ⟨z, hz, interior_subset hint⟩
  obtain ⟨m, -, hym⟩ := y.2
  have hnear : ((𝒮.anchor b : 𝒮.FineSite) : 𝒮.Point) ∈
      cubeHalfSide (y : 𝒮.Point) (2 * 𝒮.levelScale y) := by
    show supNorm (((𝒮.anchor b : 𝒮.FineSite) : 𝒮.Point) - (y : 𝒮.Point)) ≤
      2 * (2 * 𝒮.levelScale y) / 2
    have e : ((𝒮.anchor b : 𝒮.FineSite) : 𝒮.Point) - (y : 𝒮.Point) =
        (((𝒮.anchor b : 𝒮.FineSite) : 𝒮.Point) - (b.source : 𝒮.Point)) +
          ((b.source : 𝒮.Point) - (y : 𝒮.Point)) := by abel
    have h₁ : supNorm ((b.source : 𝒮.Point) - (y : 𝒮.Point)) ≤ 2 * 𝒮.levelScale y / 2 := ht
    have h₂ := ξ_le_levelScale 𝒮 (y : 𝒮.Point)
    have h₃ := supNorm_add_le (((𝒮.anchor b : 𝒮.FineSite) : 𝒮.Point) - (b.source : 𝒮.Point))
      ((b.source : 𝒮.Point) - (y : 𝒮.Point))
    rw [e]
    linarith
  exact ⟨⟨_, hcent.1⟩, hcent.2, hd.centre_near m y hym _ hnear hx⟩
theorem holderSite_nonneg (α : ℝ) {lam : ℝ} (hlam : 0 < lam) (ζ : 𝒮.FineSite → ℝ) :
    0 ≤ holderSite α lam ζ := by apply _root_.YangMills.Construction.CornerGreen.holderSite_nonneg_of_pos <;> assumption
end Terms
def plainConst (L : ℕ) (κ B : ℝ) : ℝ :=
  (L : ℝ) * separatedSumConst 4 L (κ / 8) * |B| + separatedSumConst 4 L (κ / 8) * |B|
def holderConst (L : ℕ) (κ B P C : ℝ) : ℝ :=
  (|P| + 2 * |C| * ((L : ℝ) * separatedSumConst 4 L (κ / 8) * |B|) * (L : ℝ) *
      separatedSumConst 4 L (κ / 8)) +
    2 * ((L : ℝ) * separatedSumConst 4 L (κ / 8) * |B| *
      ((L : ℝ) * Real.exp (3 * κ * (L : ℝ))))
end AdjointNeumannBounds
end YangMills.Construction
