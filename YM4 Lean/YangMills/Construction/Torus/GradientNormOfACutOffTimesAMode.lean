import YangMills.Construction.Torus.CutOffsOnAProductOfOpenSetsOfFourSpace
import YangMills.Construction.Torus.GradientNormOfAFunctionOfOnePoint
import YangMills.Construction.Torus.PeriodBoxModesCoefficientsAndPartialSums
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints
def CutoffTimesModeGradNorm : Prop :=
  ∀ (s : Conventions.StandingParameters) (ρ : ℝ), 0 < ρ →
    ∀ (A : Set (Pt s .euclidean)) (χ : Pt s .euclidean → ℝ) (κ : Fin 4 → ℤ), IsOpen A →
      asFunctionOnOnePoint χ ∈ testFns (singletonTuples A) →
      ofSinglePoint (fun x => (χ x : ℂ) * Torus.FourierBox.fourierMode (4 * ρ) κ x) ∈
          testFns (singletonTuples A) ∧
        closedSupport (ofSinglePoint fun x => (χ x : ℂ) * Torus.FourierBox.fourierMode (4 * ρ) κ x) ⊆
          closedSupport (asFunctionOnOnePoint χ) ∧
        c1GradNorm (fun x => (χ x : ℂ) * Torus.FourierBox.fourierMode (4 * ρ) κ x) ≤
          c1GradNorm (fun x => (χ x : ℂ)) *
            ENNReal.ofReal (1 + Torus.FourierBox.euclidNormInt κ / bumpScale ρ)
end YangMills.Construction.AmbientPoints
