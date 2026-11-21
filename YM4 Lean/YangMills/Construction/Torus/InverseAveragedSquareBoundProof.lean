import YangMills.Construction.Torus.FloorsOfTheAveragedSquareExpansionProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.Weighted
namespace InverseAvgGreenSq
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem lowerBoundConst_pos : 0 < lowerBoundConst 4 := by apply _root_.YangMills.Construction.Weighted.ExpansionFloors.lowerBoundConst_pos <;> assumption
theorem greenDecayRate_pos {L : ℕ} (hL : 3 ≤ L) : 0 < greenDecayRate 4 L := by apply _root_.YangMills.Construction.Weighted.AvgGreenSqBounds.greenDecayRate_pos <;> assumption
theorem upperBoundConst_pos {L : ℕ} (hL : 3 ≤ L) : 0 < upperBoundConst 4 L := by apply _root_.YangMills.Construction.Weighted.ExpansionFloors.upperBoundConst_pos <;> assumption
variable {D : TorusData} (B : SeparatedChain D)
theorem allSites_finite (hs : ∀ n, ∀ y ∈ B.layerSites n, B.BlockDescription n y) :
    B.allSites.Finite := by apply _root_.YangMills.Construction.Weighted.AvgGreenSqBounds.allSites_finite <;> assumption
theorem weightedDistance_nonneg (x x' : D.Space) : 0 ≤ B.weightedDistance x x' := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.weightedDistance_nonneg <;> assumption
end InverseAvgGreenSq
end YangMills.Construction.Weighted
