import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.GreenOperatorOfACubeAgainstSourcesAtItsCellsProof
import YangMills.Construction.DirichletOperator.SourcesOfATermOfACubeAtTheCells
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.CubeOperators (cutoffSize)
open YangMills.Construction.CubeTorus (levelSpacing)
open YangMills.Construction.ApproxInverseScales
open YangMills.Construction.CellSources (termAtCell)
noncomputable section
namespace YangMills.Construction.ApproxInverseTerms
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
section Seminorms
variable {𝒯 : NestedRegions}
theorem supBond_nonneg (f : 𝒯.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem fwdDiff_add (ν : Fin 4) (A B : 𝒯.FineBond → ℝ) :
    fwdDiff ν (A + B) = fwdDiff ν A + fwdDiff ν B := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.fwdDiff_add <;> assumption
theorem holderBond_le_holderTensor (α lam : ℝ) (g : 𝒯.FineSite → ℝ) (A : 𝒯.FineBond → ℝ) (ν : Fin 4) :
    holderBond α lam (smulSiteBond g (fwdDiff ν A)) ≤
      holderTensor α lam (smulSiteTensor g (nablaOne A)) :=
  le_ciSup (f := fun κ : Fin 1 → Fin 4 =>
    holderBond α lam (smulSiteTensor g (nablaOne A) κ))
    (Set.finite_range _).bddAbove (fun _ => ν)
end Seminorms
end YangMills.Construction.ApproxInverseTerms
