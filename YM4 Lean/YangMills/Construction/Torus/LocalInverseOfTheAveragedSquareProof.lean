import YangMills.Construction.Torus.DistanceAveragesWholePairMatricesAndNormsProof
import YangMills.Construction.Torus.FloorsOfTheAveragedSquareExpansionProof
import YangMills.Construction.Torus.GeometryOfCovers
import YangMills.Construction.Torus.LocalInverseOfTheAveragedSquare
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted.AvgSquareInverse
section Compression
variable {S : Type*} (X : Set S)
open Classical in
def extendByZero : (↥X → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun v := fun y => if h : y ∈ X then v ⟨y, h⟩ else 0
  map_add' v v' := by
    ext y
    by_cases h : y ∈ X <;> simp [h]
  map_smul' c v := by
    ext y
    by_cases h : y ∈ X <;> simp [h]
end Compression
section Matrices
end Matrices
section Numbers
theorem lowerBoundConst_pos : 0 < lowerBoundConst 4 := by apply _root_.YangMills.Construction.Weighted.ExpansionFloors.lowerBoundConst_pos <;> assumption
theorem greenDecayRate_pos {L : ℕ} (hL : 3 ≤ L) : 0 < greenDecayRate 4 L := by apply _root_.YangMills.Construction.Weighted.AvgGreenSqBounds.greenDecayRate_pos <;> assumption
theorem upperBoundConst_pos {L : ℕ} (hL : 3 ≤ L) : 0 < upperBoundConst 4 L := by apply _root_.YangMills.Construction.Weighted.ExpansionFloors.upperBoundConst_pos <;> assumption
end Numbers
section Sites
variable {D : TorusData} (B : SeparatedChain D)
theorem scale_pos (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem siteScale_pos (y : D.Space) : 0 < B.siteScale y := scale_pos _
theorem allSites_finite : Finite ↥B.allSites := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.allSites_finite <;> assumption
theorem weightedDistance_nonneg (x x' : D.Space) : 0 ≤ B.weightedDistance x x' := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.weightedDistance_nonneg <;> assumption
theorem bareInner_comm (f g : D.BareSite → ℝ) : B.bareInner f g = B.bareInner g f := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.bareInner_comm <;> assumption
def invScaleOn (W : Set D.Space) : Module.End ℝ ↥(B.layerSpaceOn W) :=
  (B.mulOp fun y => (B.siteScale y)⁻¹).restrict fun w hw y hy => by
    change (B.siteScale y)⁻¹ * w y = 0
    rw [hw y hy, mul_zero]
end Sites
end YangMills.Construction.Weighted.AvgSquareInverse
