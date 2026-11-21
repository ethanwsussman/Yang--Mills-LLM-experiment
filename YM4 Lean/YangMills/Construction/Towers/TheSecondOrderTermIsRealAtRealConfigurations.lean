import YangMills.Construction.Towers.CovariantAveragesAsDifferentials
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def QuadraticTermHermitianAtRealFields : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ U ∈ smallIterateFields L k, U ∈ fieldSpace L k 0 →
      ∀ B ∈ edgeFormSpace (meshAt L k 0), ∀ B' ∈ edgeFormSpace (meshAt L k 0),
        ∀ e, AsDifferentials.complexQuadraticTerm L k U B B' e ∈
          Matrices.ComplexMatrix2.hermitianTraceless
end YangMills.Construction.Tower.FullSpace
end
