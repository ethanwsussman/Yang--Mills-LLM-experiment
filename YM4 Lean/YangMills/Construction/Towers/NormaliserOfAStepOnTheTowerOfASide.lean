import YangMills.Construction.OneLoopLaw.CoefficientOfAFunctional
import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open PeriodicOperators.Tempered
def topVertexEquivUnit (L m k : ℕ) : Vertex L m k k ≃+ Vertex L m 0 0 :=
  AddEquiv.addSubgroupCongr (OneLoopLaw.FunctionalStiffness.sublattice_levelDepth_self L m k)
theorem topVertexEquivUnit_unitStep (L m k : ℕ) (μ : Fin 4) :
    topVertexEquivUnit L m k (PeriodicLattice.unitStep L m (PeriodicLattice.levelDepth k k) μ) =
      PeriodicLattice.unitStep L m (PeriodicLattice.levelDepth 0 0) μ := by
  refine Subtype.ext ?_
  simp [topVertexEquivUnit, PeriodicLattice.unitStep, PeriodicLattice.meshSize]
def topEdgeEquivUnit (L m k : ℕ) : Edge L m k k ≃ UnitEdge L m :=
  edgeEquivOfVertexEquiv (topVertexEquivUnit L m k) (topVertexEquivUnit_unitStep L m k)
def sideStepNormaliser (L m i : ℕ) : (Edge L m (i + 1) (i + 1) → Matrices.ComplexMatrix2) → ℝ :=
  logNormaliserRatio L m (i + 1) i
def stepNormaliserFamily (L i : ℕ) : FieldFamily L :=
  fun m U => sideStepNormaliser L m i (U ∘ topEdgeEquivUnit L m (i + 1))
end YangMills.Construction.Tower
end
