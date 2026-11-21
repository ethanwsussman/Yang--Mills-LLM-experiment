import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import YangMills.Construction.Towers.CovariantAveragesAsDifferentials
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels
def QuadraticTermIsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ W ∈ Tower.FullSpace.smallIterateFields L k,
    ∀ A ∈ Tower.AsDifferentials.boundedSubmodule
        (Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0)),
    ∀ A' ∈ Tower.AsDifferentials.boundedSubmodule
        (Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0)),
    ∀ D ∈ Tower.AsDifferentials.boundedSubmodule
        (Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0)),
    ∀ D' ∈ Tower.AsDifferentials.boundedSubmodule
        (Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0)),
    ∀ e : PeriodicOperators.PosEdge L k k,
      (∀ f : PeriodicOperators.PosEdge L k 0,
        TorusMetric.supNormVec (f.1.initial.1 - e.1.initial.1) ≤ 3 →
          A f.1 = D f.1 ∧ A' f.1 = D' f.1) →
      Tower.FullSpace.AsDifferentials.complexQuadraticTerm L k W A A' e =
        Tower.FullSpace.AsDifferentials.complexQuadraticTerm L k W D D' e
end YangMills.Construction.LocalKernels
