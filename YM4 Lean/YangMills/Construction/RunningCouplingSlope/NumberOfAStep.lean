import YangMills.Construction.ColdStepAtMirrorFrames.ChainOfConstantCurvature
import YangMills.Construction.RunningCouplingSlope.TotalOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
def fluxCurvature (l n : ℕ) : ℝ := 2 * Real.pi * l / (n : ℝ) ^ 2
def constantCurvatureField (L t l n : ℕ) (X : BlockAverages.imaginaryQuaternions) :
    TorusFields.TorusField n :=
  ColdStepAtMirrorFrames.restrictToTorus n
    (ColdStepAtMirrorFrames.constantCurvatureChain (TorusFields.torusFrame L t n) X 0 1 l
      (TorusFields.torusFrame L t n).top)
def curvatureQuotient (a ρ : ℝ) (L t l n : ℕ) (X : BlockAverages.imaginaryQuaternions) : ℝ :=
  2 / ((n : ℝ) ^ 4 * fluxCurvature l n ^ 2) *
    SlopeCoefficient.stepGaugeTotal a ρ L t n (constantCurvatureField L t l n X)
def IsStepCoefficient (a : ℝ) (L t : ℕ) (b : ℝ) : Prop :=
  ∀ (ρ : ℝ) (l : ℕ) (X : BlockAverages.imaginaryQuaternions), 0 < ρ → ρ ≤ 1 → 1 ≤ l → ‖X‖ = 1 →
    Filter.Tendsto (fun n : ℕ => curvatureQuotient a ρ L t l n X) Filter.atTop (𝓝 b)
def AreStepCoefficients (a : ℝ) (L : ℕ) (b : ℕ → ℝ) : Prop := ∀ t, IsStepCoefficient a L t (b t)
end YangMills.Construction.RunningCouplingSlope
end
