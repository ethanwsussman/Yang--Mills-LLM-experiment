import YangMills.Construction.PeriodicOperators.TemperedFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw
def MemberFirstDerivativeVanishes : Prop :=
  ∀ L n : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∀ f : (PeriodicOperators.Tempered.UnitEdge L n → Matrices.ComplexMatrix2) → ℝ,
      PeriodicOperators.Tempered.IsAdmissibleMember f →
      ∀ B ∈ Tower.edgeFormSpace L n 0 0,
        Tower.leftDeriv (k := 0) (j := 0) f (PeriodicOperators.Tempered.identityField L n) B = 0
end YangMills.Construction.OneLoopLaw
end
