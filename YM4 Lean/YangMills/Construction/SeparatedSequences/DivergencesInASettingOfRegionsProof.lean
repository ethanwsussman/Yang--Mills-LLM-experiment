import YangMills.Construction.RegionSequence.CellsAndAdjoints
import YangMills.Construction.RegionSequence.GradientAdjointsOnTorus
import YangMills.Construction.SeparatedSequences.ClassExpansionsInASettingOfRegionsProof
import YangMills.Construction.SeparatedSequences.PropertiesOfTheOperatorsOfASequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses.RegionDivergences
open Set PeriodicLattice.DirichletOperators
open SingleSequence SingleSequence.SequenceData RegionSequence.NestedRegions
section Transport
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions} {σ : s.data.BareSite ≃ 𝒮.FineSite}
  {β : s.data.BareBond ≃ 𝒮.FineBond}
theorem bondInner_eq_transport (hS : s.IsNestedRegions 𝒮) (A B : s.data.BondFn) :
    s.data.bondInner A B = bondInner (A ∘ β.symm) (B ∘ β.symm) := by
  have hξ : 𝒮.ξ = PeriodicLattice.finestMeshInLevelUnits s.data.L s.data.t := hS.ξ_eq
  simp only [ClassData.bondInner, latticeInner, RegionSequence.NestedRegions.bondInner, hξ]
  congr 1
  exact (finsum_comp_equiv β.symm (f := fun x => A x * B x)).symm
end Transport
section Nested
variable {𝒮 : RegionSequence.NestedRegions}
theorem bondInner_comm (A B : 𝒮.FineBond → ℝ) : bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
end Nested
end YangMills.Construction.SeparatedClasses.RegionDivergences
end
