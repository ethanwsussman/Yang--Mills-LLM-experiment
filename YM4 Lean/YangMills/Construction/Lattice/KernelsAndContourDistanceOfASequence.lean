import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.Matrices
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction.SeparatedSequences.BaseParameters
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus) (φ : BondFrame)
def pointMesh (y : ↥(D.allLayerPoints Ω)) : ℝ := D.levelMeshRatio (D.levelSite Ω y).1
variable {D Ω φ}
variable (D Ω φ)
variable {D Ω φ}
variable (D Ω φ)
end YangMills.Construction.SeparatedSequences.BaseParameters
end
