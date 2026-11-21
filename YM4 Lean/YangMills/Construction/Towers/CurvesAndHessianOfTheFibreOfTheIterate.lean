import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
def FibreCurvesAndHessian : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L m k k) fun W =>
      chainBottom W ∈ fieldSpace L m k 0 ∧
      (fieldCurveData L m k 0).IsCriticalOn (smoothingIterFibre (smoothingFibreNhd L m k) W)
        (plaquetteAction L m k) (chainBottom W) ∧
      (fieldCurveData L m k 0).IsHessianFormAt (S := LinearMap.ker (topConstraintMap L m k W))
        (fun B => (B.1.1 : Edge L m k 0 → Matrices.ComplexMatrix2))
        (smoothingIterFibre (smoothingFibreNhd L m k) W)
        (plaquetteAction L m k) (chainBottom W) (fibreRestrictedHessian L m k W) ∧
      (∀ B : LinearMap.ker (topConstraintMap L m k W),
        ∃ (I : Set ℝ) (γ : ℝ → Edge L m k 0 → Matrices.ComplexMatrix2),
          (fieldCurveData L m k 0).IsTwiceDiffCurve I γ ∧
            MapsTo γ I (smoothingIterFibre (smoothingFibreNhd L m k) W) ∧ γ 0 = chainBottom W ∧
            (fieldCurveData L m k 0).tangent γ = B.1.1) ∧
      ∀ (I : Set ℝ) (γ : ℝ → Edge L m k 0 → Matrices.ComplexMatrix2),
        (fieldCurveData L m k 0).IsTwiceDiffCurve I γ →
        MapsTo γ I (smoothingIterFibre (smoothingFibreNhd L m k) W) → γ 0 = chainBottom W →
        ∃ B : LinearMap.ker (topConstraintMap L m k W),
          (fieldCurveData L m k 0).tangent γ = B.1.1
end YangMills.Construction.Tower
end
