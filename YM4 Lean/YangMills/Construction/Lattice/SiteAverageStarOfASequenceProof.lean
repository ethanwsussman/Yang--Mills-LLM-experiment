import YangMills.Construction.Lattice.LatticesAndCubesOfOrder
import YangMills.Construction.Lattice.SymmetryOfTheDirichletSiteOperatorsProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.SeparatedSequences.BaseParameters
noncomputable section
namespace YangMills.Construction.SeparatedSequences
namespace AverageZeroAdjoint
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus)
theorem levelSite_eq (hP : D.FineSitesPartitionIntoBlocks Ω) {n : ℕ}
    (y : D.LatticeSite n) (hn : n ≤ D.t) (hy : y ∈ D.layerSites Ω n)
    (hmem : (y : D.Torus) ∈ D.allLayerPoints Ω) :
    D.levelSite Ω ⟨(y : D.Torus), hmem⟩ = ⟨n, y⟩ := by apply _root_.YangMills.Construction.SeparatedSequences.DirichletCommutators.levelSite_of_mem_layerSites <;> assumption
open Classical in
def siteIndicator (x₀ : BareSite D.L D.m D.K) : ZeroForms D.L D.m D.K :=
  fun x => if x = x₀ then 1 else 0
end AverageZeroAdjoint
end YangMills.Construction.SeparatedSequences
end
