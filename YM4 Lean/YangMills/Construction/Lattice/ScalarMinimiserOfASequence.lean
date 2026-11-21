import YangMills.Construction.Lattice.DirichletOperatorsOfASeparatedSequence
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice.DirichletOperators
noncomputable section
namespace YangMills.Construction
namespace SeparatedSequences
namespace BaseParameters
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus)
def averagedZeroGreen : Module.End ℝ (D.CoarseZeroForms Ω) :=
  D.averageZero Ω ∘ₗ D.zeroGreen Ω ∘ₗ D.averageZeroAdjoint Ω
def zeroFormExtension : D.CoarseZeroForms Ω →ₗ[ℝ] ↥(zeroFormsOn D.K (Ω 0)) :=
  D.zeroGreen Ω ∘ₗ D.averageZeroAdjoint Ω ∘ₗ Ring.inverse (D.averagedZeroGreen Ω)
end BaseParameters
end SeparatedSequences
end YangMills.Construction
end
