import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace AxialFunctionFacts
structure AtLevel (L n k i : ℕ) : Prop where
  meanContourHolonomy_trivial : ∀ y : Vertex L n k (i + 1),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
      PeriodicLattice.meanContourHolonomy (trivialField L n k i) y x = 1
  smoothingStep_trivial :
    smoothingStep L n k i (trivialField L n k i) = trivialField L n k (i + 1)
  isAxialGaugeAt_trivial : IsAxialGaugeAt L n k i (trivialField L n k i)
  analytic_near_identity : ∃ U : Set (Edge L n k i → Matrices.ComplexMatrix2), IsOpenNhdOfOne U ∧
    U ⊆ axialFunctionDomain L n k i ∧ IsAnalyticFieldFunction U (axialFunction L n k i)
  nonneg : EventuallyNearIdentity (fieldSpace L n k i) fun V => 0 ≤ axialFunction L n k i V
  eq_zero_iff : EventuallyNearIdentity (fieldSpace L n k i) fun V =>
    axialFunction L n k i V = 0 ↔ IsAxialGaugeAt L n k i V
  leftGradient_eq_zero : EventuallyNearIdentity (fieldSpace L n k i) fun V =>
    IsAxialGaugeAt L n k i V →
      leftGradient (fieldSpace L n k i) (fun W => (axialFunction L n k i W : ℂ)) V = 0
  leftSecondDeriv_eq : EventuallyNearIdentity (fieldSpace L n k i) fun V =>
    IsAxialGaugeAt L n k i V →
      ∀ B ∈ edgeFormSpace L n k i, leftSecondDeriv (axialFunction L n k i) V B B =
        traceFinsumNorm (contourLogDeriv L n k i V B) ^ 2
  deriv_deriv_along_curve : EventuallyNearIdentity (fieldSpace L n k i) fun V =>
    IsAxialGaugeAt L n k i V → ∀ B ∈ edgeFormSpace L n k i,
      ∀ (I : Set ℝ) (γ : ℝ → Edge L n k i → Matrices.ComplexMatrix2),
        (fieldCurveData L n k i).IsTwiceDiffCurve I γ → γ 0 = V →
          (fieldCurveData L n k i).tangent γ = B →
            deriv (deriv fun t => axialFunction L n k i (γ t)) 0 =
              traceFinsumNorm (contourLogDeriv L n k i V B) ^ 2
  contourLogDeriv_trivial : ∀ B ∈ edgeFormSpace L n k i,
    contourLogDeriv L n k i (trivialField L n k i) B = fineOnlyContourAverage L n k i B
def statement : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k → AtLevel L n k i
end AxialFunctionFacts
end Tower
end YangMills.Construction
end
