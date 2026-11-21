import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace ContourLogDerivAlongCurves
def Statement : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    EventuallyNearIdentity (fieldSpace L n k i) fun V =>
      ∀ (I : Set ℝ) (γ : ℝ → Edge L n k i → Matrices.ComplexMatrix2),
        IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ → γ 0 = V →
          ∀ x : FineOnlyVertex L n k i,
            HasDerivAt
              (fun t => Complex.I⁻¹ •
                Matrices.ComplexMatrix2.logSeries
                  (PeriodicLattice.meanContourHolonomy (γ t) (cubeCentre x) x.1))
              (contourLogDeriv L n k i V (curveTangent γ) x) 0 ∧
            contourLogDeriv L n k i V (curveTangent γ) x ∈ Matrices.ComplexMatrix2.hermitianTraceless
end ContourLogDerivAlongCurves
end Tower
end YangMills.Construction
end
