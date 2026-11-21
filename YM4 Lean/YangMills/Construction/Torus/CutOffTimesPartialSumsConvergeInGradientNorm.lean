import YangMills.Construction.Torus.GradientNormOfAFunctionOfOnePoint
import YangMills.Construction.Torus.PeriodBoxModesCoefficientsAndPartialSums
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import YangMills.Construction.Torus.TestFunctionsAndDistributionsOnOpenSetsOfTuples
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.AmbientPoints
def CutoffTimesFourierSumsConverge : Prop :=
  ∀ (s : Conventions.StandingParameters) (P : ℝ), 0 < P →
    ∀ (χ : Pt s .euclidean → ℝ) (h : Pt s .euclidean → ℂ),
      asFunctionOnOnePoint χ ∈ testFns (Torus.FourierBox.fundamentalBoxPow s 1 P) →
      ofSinglePoint h ∈ testFns (Torus.FourierBox.fundamentalBoxPow s 1 P) →
      Tendsto
        (fun t : ℕ+ => c1GradNorm fun x : Pt s .euclidean =>
          (χ x : ℂ) * Torus.FourierBox.fourierPartialSum (n := 1) P (ofSinglePoint h) t x - (χ x : ℂ) * h x)
        atTop (𝓝 0)
end YangMills.Construction.AmbientPoints
