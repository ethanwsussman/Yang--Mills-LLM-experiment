import YangMills.Construction.Towers.PartialSumsOfTheGaugeFixingFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LastPartialHessianFormula : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 1 ≤ k →
    IsSmoothingFibreNhd L m k (smoothingFibreNhd L m k) ∧
      EventuallyNearIdentity (fieldSpace L m k k) fun W =>
        ∀ B : LinearMap.ker (topConstraintMap L m k W),
          partialFibreHessian L m k k (smoothingFibreNhd L m k) W (chainBottom W) B =
            augmentedHessianValue W B
end YangMills.Construction.Tower
end
