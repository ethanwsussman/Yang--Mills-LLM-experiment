import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.WilsonSpecificationOnObservablesVersionsAndTrivialMeasures
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ChessboardSetup
variable (D : ChessboardSetup)
def positiveLinksOn (S : Set AmbientSpace) : Set D.Link :=
  InfiniteLattice.positiveLinksWithin D.mesh S
theorem mem_positiveLinksOn_iff {S : Set AmbientSpace} {e : D.Link} :
    e ∈ D.positiveLinksOn S ↔ e ∈ InfiniteLattice.positiveLinkSet D.mesh ∧
      (e.initial : AmbientSpace) ∈ S ∧ (e.terminal : AmbientSpace) ∈ S :=
  Iff.rfl
def wilsonKernelAt (E : Finset D.Link)
    (hE : (E : Set D.Link) ⊆ InfiniteLattice.positiveLinkSet D.mesh)
    (A : D.GaugeField → ℂ) (ξ : D.GaugeField) : ℂ :=
  GibbsAtFixedSpacing.wilsonLinkKernel D.β E
    (InfiniteLattice.hasNoOppositePairs_of_subset_positiveLinks D.mesh_pos hE) A ξ
def periodicStates : Set (Measure D.GaugeField) :=
  InfiniteLattice.periodicGibbsSet D.L D.K D.β
end ChessboardSetup
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def baseCell : Set AmbientSpace := g.cell 0
theorem baseCell_eq : g.baseCell = {x | ∀ μ, x μ - g.origin μ ∈ Icc 0 g.cellSide} := by
  simp [baseCell, cell]
def fundamentalBlock : Set AmbientSpace := g.block 0
theorem fundamentalBlock_eq :
    g.fundamentalBlock =
      {x | ∀ μ, x μ - g.origin μ ∈ Icc 0 (PeriodicLattice.torusSide D.L D.m)} := by
  simp [fundamentalBlock, block]
theorem fundamentalBlock_mem_blocks : g.fundamentalBlock ∈ g.blocks := ⟨0, rfl⟩
def fundamentalBlockInterior : Set AmbientSpace := interior g.fundamentalBlock
end ReflectionGrid
end ChessboardTori
end YangMills.Construction
end
