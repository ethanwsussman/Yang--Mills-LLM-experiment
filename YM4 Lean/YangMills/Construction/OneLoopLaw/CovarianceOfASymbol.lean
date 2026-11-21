import YangMills.Construction.OneLoopLaw.KernelsAndTensorFormOfASymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.SymbolCovariance
def SymbolCovarianceClaim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (F : PeriodicOperators.Tempered.FieldFamily L) (δ : ℝ) (π : PeriodicOperators.Tempered.SymbolArray) (e : ℕ → ℝ),
      PeriodicOperators.Tempered.IsLatticeFunctional L F → PeriodicOperators.Tempered.IsTemperedWitness L F δ π e →
        TemperedStiffness.PermutationCovariant δ π ∧ TemperedStiffness.ReflectionCovariant δ π
end YangMills.Construction.OneLoopLaw.SymbolCovariance
end
