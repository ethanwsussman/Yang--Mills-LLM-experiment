import YangMills.Construction.PeriodicOperators.TemperedFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.GaugeDirectionHessian
def HessianKillsGaugeDirections : Prop :=
  ∀ L n : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∀ F : PeriodicOperators.Tempered.FieldFamily L,
    PeriodicOperators.Tempered.IsAdmissibleMember (F n) →
    ∀ l : Tower.Vertex L n 0 0 → Matrices.ComplexMatrix2,
    (∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) →
    ∀ B' ∈ Tower.complexEdgeForms L n 0 0,
      PeriodicOperators.Tempered.complexHessian F n
        (Tower.covDiff (k := 0) (j := 0) (PeriodicOperators.Tempered.identityField L n) l) B' = 0
end YangMills.Construction.OneLoopLaw.GaugeDirectionHessian
end
