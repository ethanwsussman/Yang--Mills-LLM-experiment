import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
def LeftChartCurveAction.Statement : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∀ U ∈ fieldSpace L n k 0, ∀ (I : Set ℝ) (γ : ℝ → Edge L n k 0 → Matrices.ComplexMatrix2),
      (fieldCurveData L n k 0).IsTwiceDiffCurve I γ → γ 0 = U →
      ∀ B : edgeFormSpace L n k 0, (fieldCurveData L n k 0).tangent γ = B →
      ∃ (X : ℝ → edgeFormSpace L n k 0) (ξ : edgeFormSpace L n k 0),
        (∀ᶠ t in 𝓝 (0 : ℝ), γ t =
          PeriodicLattice.expTwist (X t : Edge L n k 0 → Matrices.ComplexMatrix2) U) ∧
        Tendsto X (𝓝 0) (𝓝 0) ∧
        ((fun t : ℝ => edgeFormNorm ((X t - t • B - (t ^ 2 / 2) • ξ : edgeFormSpace L n k 0) :
            Edge L n k 0 → Matrices.ComplexMatrix2)) =o[𝓝 0] fun t : ℝ => t ^ 2) ∧
        ((deriv (deriv fun t => plaquetteAction L n k (γ t)) 0 : ℝ) : ℂ) =
          ((leftSecondDeriv (plaquetteAction L n k) U
              (B : Edge L n k 0 → Matrices.ComplexMatrix2) B : ℝ) : ℂ) +
            edgeFormPairing
              (leftGradient (fieldSpace L n k 0) (fun V => (plaquetteAction L n k V : ℂ)) U) ξ
end YangMills.Construction.Tower
end
