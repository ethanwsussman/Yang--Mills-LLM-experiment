import YangMills.Construction.DirichletOperator.TermsOfTheRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CubeAdjointGreen
open YangMills.Construction.Dirichlet YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.RemainderEstimates
variable (𝒮 : NestedRegions) (M : ℕ)
def SupBound (L : ℕ) (C : ℝ) : Prop :=
  ∀ y y' : 𝒮.allCentres, ∀ Q ∈ PartitionCubes.active 𝒮 M,
    (Q.supp ∩ doubledCube (y : 𝒮.Point)).Nonempty →
    ∀ A ∈ 𝒮.oneForms, cellCutBond (y' : 𝒮.Point) A = A →
      supBond (cellCutBond (y : 𝒮.Point) (cutoffGreenDefectAdj Q A)) ≤
        C * (M : ℝ)⁻¹ * RemainderEstimates.expWeight L (y : 𝒮.Point) y' * supBond A
end YangMills.Construction.CubeAdjointGreen
