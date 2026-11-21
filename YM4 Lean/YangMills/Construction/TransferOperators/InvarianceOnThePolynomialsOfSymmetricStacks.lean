import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import YangMills.Construction.TransferOperators.ReflectionInALinkMirrorSymmetricStacksAndTheReversal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransferOperators
open MeasureTheory YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics YangMills.Construction.NormalFamilies
def IsPolynomialInLinkVariables (B : Set (PositiveLink 1)) (F : GaugeField 1 → ℂ) : Prop :=
  ∃ P : (B → YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary) → ℂ,
    IsEntryPolynomial P ∧ ∀ U : GaugeField 1, F U = P fun c => U c.1.1
def centeredStackGaugePolys {μ : Fin 4} (i k : ℤ) (hk : 1 ≤ k) :
    Set (GaugeField 1 → ℂ) :=
  {F | IsGaugeInvariantFunction F ∧ (∀ U, (F U).im = 0) ∧
    ∃ (v : Set (SliceSite μ)) (_ : Finite v), (linksWithin v).Nonempty ∧
      IsPolynomialInLinkVariables ((centeredStack i k hk).linksOver v) F}
def CenteredStackReflectionInvarianceStatement : Prop :=
  ∀ (μ : Fin 4) (β : ℝ), 0 < β → ∀ ν : Measure (GaugeField 1), IsPeriodicGibbs β ν →
    ∀ i : ℤ,
      (∀ (k : ℤ) (hk : 1 ≤ k),
        centeredStackClass μ i k hk = centeredStackGaugePolys (μ := μ) i k hk) ∧
      ∀ P : NormalLevelPair 1, P.normal = YangMills.Construction.PeriodicLattice.coordVec μ →
        P.level = (i : ℝ) + 1 / 2 →
        ∀ (k : ℤ) (hk : 1 ≤ k), ∀ X ∈ centeredStackClass μ i k hk,
          stateEval ν X = stateEval ν (P.reflectObservable X)
end YangMills.Construction.TransferOperators
end
