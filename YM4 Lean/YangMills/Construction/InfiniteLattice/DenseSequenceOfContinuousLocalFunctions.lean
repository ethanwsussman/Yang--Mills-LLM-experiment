import YangMills.Construction.InfiniteLattice.AlgebraOfLocalFunctionsAndContinuousFunctions
import YangMills.Construction.InfiniteLattice.UnitSpacingLatticeData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def CylinderFunctionsHaveDenseSequence : Prop :=
  ∀ D : FixedSpacing.Params,
    ∃ F : ℕ+ → GaugeField D.mesh → ℂ,
      (∀ k, F k ∈ cylinderAlgebra D.mesh) ∧
      ∀ H : ContinuousGaugeFunctions D.mesh, ∀ ε : ℝ, 0 < ε →
        ∃ k, observableSupNorm (fun U => H U - F k U) < ε
end YangMills.Construction.InfiniteLattice
