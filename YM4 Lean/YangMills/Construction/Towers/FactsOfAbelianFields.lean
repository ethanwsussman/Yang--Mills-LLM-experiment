import YangMills.Construction.Towers.PropertiesOfAbelianFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldFacts
open UnitLatticeL2 AbelianFieldDensity
def AllFacts : Prop :=
  FourierCoeffsUnique ∧ ChargeAlgebra ∧
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z →
    FormsChargeDecomposition (meshAt L 0 0) ∧ KernelLocality L ∧ LinearFieldAngles L ∧
    ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      AbelianOperators θ ∧ ChargeSymmetries θ ∧ CovariantShifts θ ∧
      FaceVariables θ ∧ HessianQuadraticForm θ ∧ SpectralLowerBounds θ ∧
      ActionDerivative θ
end YangMills.Construction.Tower.AbelianFieldFacts
end
