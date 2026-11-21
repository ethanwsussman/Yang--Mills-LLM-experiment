import YangMills.Construction.Lattice.DifferenceOperatorsOfTheBareLattice
import YangMills.Construction.Lattice.ExistenceOfTheOperatorsOfASeparatedSequence
import YangMills.Construction.Lattice.IntertwiningOfTheAveragesWithTheDifferenceProof
import YangMills.Construction.Lattice.KernelOfTheSiteAverageOfASequence
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.SeparatedSequences.BaseParameters YangMills.Construction.RealInnerForms
noncomputable section
namespace YangMills.Construction.SeparatedSequences.AverageKernel
variable {S : SequenceDatum}
theorem mem_layerSites_iff (hc : LatticeCubeStatement) {n : ℕ} (hn : n ≤ S.t)
    (y : S.LatticeSite n) :
    y ∈ S.layerSites S.region n ↔
      (y : S.Torus) ∈ S.memberAt S.region n ∧ (y : S.Torus) ∉ S.memberAt S.region (n + 1) := by apply _root_.YangMills.Construction.AveragesDifference.mem_layerSites_iff <;> assumption
theorem levelSite_eq (hc : LatticeCubeStatement) {n : ℕ} (hn : n ≤ S.t)
    {y : S.LatticeSite n} (hy : y ∈ S.layerSites S.region n)
    (h : (y : S.Torus) ∈ S.allLayerPoints S.region) : S.levelSite S.region ⟨y, h⟩ = ⟨n, y⟩ := by apply _root_.YangMills.Construction.AveragesDifference.levelSite_eq <;> assumption
theorem interiorBonds_subset_framedBonds (φ : BondFrame) :
    interiorBonds S.K (S.region 0) ⊆ framedBonds S.K (S.region 0) φ := by
  intro b hb
  cases φ with
  | interior => exact hb
  | star => exact Or.inl hb.1
end YangMills.Construction.SeparatedSequences.AverageKernel
end
