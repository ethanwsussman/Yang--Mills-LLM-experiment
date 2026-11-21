import YangMills.Construction.Lattice.ActionOfIsometriesAndAlgebrasOfAGridDatum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GridSymmetries
def PullbackContinuity : Prop :=
  ∀ (L : ℕ) (κ : ℤ) (d : CellGrid L κ) (g : d.GridSymmetry),
    Continuous g.pullback ∧
      ∀ F : d.GaugeConfig → ℂ, Measurable F → (∃ C : ℝ, ∀ U, ‖F U‖ ≤ C) →
        Measurable (g.actOnObservables F) ∧ ∃ C : ℝ, ∀ U, ‖g.actOnObservables F U‖ ≤ C
end YangMills.Construction.GridSymmetries
end
