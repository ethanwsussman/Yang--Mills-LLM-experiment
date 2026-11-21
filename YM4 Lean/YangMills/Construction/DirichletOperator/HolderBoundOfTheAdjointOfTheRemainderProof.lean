import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.BlockNumbersOfTheAdjointTermsProof
import YangMills.Construction.DirichletOperator.PropagatorBoundsForSourcesInFormsProof
import YangMills.Construction.DirichletOperator.RegularityOfTheLocalOperatorsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RemainderAdjHolder
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes RemainderEstimates
open CubeOperators (cutoffSize)
theorem finite_fineBond (R : NestedRegions) : Finite R.FineBond := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.finite_fineBond <;> assumption
variable {R : NestedRegions}
theorem holderBond_nonneg (α lam : ℝ) (f : R.FineBond → ℝ) :
    0 ≤ holderBond α lam f := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.holderBond_nonneg <;> assumption
theorem supBond_nonneg (f : R.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
variable {M : ℕ}
end YangMills.Construction.RemainderAdjHolder
