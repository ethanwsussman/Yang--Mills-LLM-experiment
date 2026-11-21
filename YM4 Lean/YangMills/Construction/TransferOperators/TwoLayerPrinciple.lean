import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import YangMills.Construction.TransferOperators.ConditioningOnAllBondsButOneBlockOfOneLayer
import YangMills.Construction.TransferOperators.TransferOperatorOfACubicTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.TransferOperators
def Stack.ofConsecutive (i : ℤ) : Stack where
  lower := i
  upper := i + 1
  lower_lt_upper := by omega
def TwoLevelPrinciple.Statement : Prop :=
  ∀ (β : ℝ), 0 < β → ∀ (μ : Fin 4) (ν : Measure (GaugeField 1)), IsPeriodicGibbs β ν →
    ∀ (B : Block μ) (i : ℤ)
      (Y : C((B.links → Matrices.ComplexMatrix2.specialUnitary) ×
        (B.links → Matrices.ComplexMatrix2.specialUnitary), ℝ)),
      (∀ (g : B.vertices → Matrices.ComplexMatrix2.specialUnitary)
        (u u' : B.links → Matrices.ComplexMatrix2.specialUnitary),
        Y (gaugeAct B.links_subset_linksWithin g u,
          gaugeAct B.links_subset_linksWithin g u') = Y (u, u')) →
      (∀ u u' : B.links → Matrices.ComplexMatrix2.specialUnitary, Y (u, u') = -Y (u', u)) →
      stateEval ν (fun U => Y ((Stack.ofConsecutive i).blockValues B U i,
        (Stack.ofConsecutive i).blockValues B U (i + 1))) = 0
end YangMills.Construction.TransferOperators
end
