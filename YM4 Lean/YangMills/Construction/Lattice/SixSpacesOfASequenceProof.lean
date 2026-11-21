import YangMills.Construction.Lattice.CommutatorsOfTheDirichletOperatorsWithFunctionsProof
import YangMills.Construction.Lattice.DirichletFormLaplacianWithItsBoundaryTermProof
import YangMills.Construction.Lattice.FactsOfTheFormExtensionProof
import YangMills.Construction.Lattice.WeightedFunctionSpacesAndTensors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences.WeightedSpaces
open Set TorusMetric PeriodicLattice PeriodicLattice.DirichletOperators
open BaseParameters
theorem finsum_eq_finsum_subtype_of_vanish {ι M : Type} [AddCommMonoid M] (X : Set ι) (F : ι → M)
    (h : ∀ i, i ∉ X → F i = 0) : ∑ᶠ i, F i = ∑ᶠ i : ↥X, F i := by
  rw [finsum_set_coe_eq_finsum_mem, finsum_mem_def]
  refine finsum_congr fun i => ?_
  by_cases hi : i ∈ X
  · rw [indicator_of_mem hi]
  · rw [indicator_of_notMem hi, h i hi]
theorem two_le_L (D : BaseParameters) : 2 ≤ D.L := by
  have := D.three_le_L
  omega
theorem levelMeshRatio_pos (D : BaseParameters) (n : ℕ) : 0 < D.levelMeshRatio n := by apply _root_.YangMills.Construction.SeparatedSequences.OneExtensionProof.levelMeshRatio_pos <;> assumption
section Levels
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus)
variable {D Ω}
theorem mem_fineBlock_self {n : ℕ} (y : D.LatticeSite n) :
    (y : D.Torus) ∈ fineBlock (D := D) y := by apply _root_.YangMills.Construction.SeparatedSequences.DirichletCommutators.mem_fineBlock_self <;> assumption
end Levels
section Spaces
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus) (φ : BondFrame)
end Spaces
end YangMills.Construction.SeparatedSequences.WeightedSpaces
end
