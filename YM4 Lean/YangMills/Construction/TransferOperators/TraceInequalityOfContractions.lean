import YangMills.Construction.Matrices.HilbertSchmidtOperatorsTraceClassAndTraceOnG
import YangMills.Construction.TransferOperators.CubicToriAndProductsOfOperatorsOnPowersOfG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open SpinHarmonics
namespace TransferOperators
def interleavedProd {M : Type*} [Monoid M] {s : ℕ} (X : Fin s → M) (A : M) : M :=
  (List.ofFn fun j => X j * A).prod
def FiniteDimTraceBound (s : ℕ) : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (A : Module.End ℂ W) (X : Fin s → Module.End ℂ W),
    LinearMap.IsSymmetric A →
    (∀ x : W, 0 ≤ (inner ℂ x (A x) : ℂ).re ∧ (inner ℂ x (A x) : ℂ).im = 0) →
    (∀ j, ‖LinearMap.toContinuousLinearMap (X j)‖ ≤ 1) →
    ‖linearMapTrace (interleavedProd X A)‖ ≤ (linearMapTrace (A ^ s)).re ∧
      (linearMapTrace (A ^ s)).im = 0
def traceExpansionTerm {J : Type} [Finite J] {s : ℕ}
    (X : Fin s → HaarL2 J →L[ℂ] HaarL2 J)
    (A : HaarL2 J →L[ℂ] HaarL2 J)
    (a : Fin s → PeterWeylIndex J × PeterWeylIndex J) : ℂ :=
  ∏ j, peterWeylEntry (X j) (a j).1 (a j).2 * peterWeylEntry A (a j).2 (a (finRotate s j)).1
def HaarL2TraceBound (s : ℕ) : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (A : HaarL2 J →L[ℂ] HaarL2 J)
    (X : Fin s → HaarL2 J →L[ℂ] HaarL2 J),
    IsPositiveOp A →
    Summable (fun p : PeterWeylIndex J × PeterWeylIndex J => ‖peterWeylEntry A p.1 p.2‖) →
    (∀ j, ‖X j‖ ≤ 1) →
    TraceSummablePW (interleavedProd X A) ∧
      Summable (fun a : Fin s → PeterWeylIndex J × PeterWeylIndex J => ‖traceExpansionTerm X A a‖) ∧
      tracePW (interleavedProd X A) = ∑' a, traceExpansionTerm X A a ∧
      TraceSummablePW (A ^ s) ∧
      ‖tracePW (interleavedProd X A)‖ ≤ (tracePW (A ^ s)).re ∧
      (tracePW (A ^ s)).im = 0
def ContractionTraceBound.Statement : Prop :=
  ∀ s : ℕ, 1 ≤ s → FiniteDimTraceBound s ∧ HaarL2TraceBound s
end TransferOperators
end YangMills.Construction
end
