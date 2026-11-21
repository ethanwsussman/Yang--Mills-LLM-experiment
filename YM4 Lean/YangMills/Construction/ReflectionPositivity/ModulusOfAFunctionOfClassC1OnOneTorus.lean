import YangMills.Construction.ReflectionPositivity.OneTorusAllCutoffsPointsAndTheClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.TorusCutoffs
variable {s : Conventions.StandingParameters}
def gradOscillation (f : s.Torus → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ (x : s.Torus) (x' : s.Torus) (_ : torusDist x x' ≤ δ),
    ENNReal.ofReal (TorusMetric.euclidNormVec (grad f x - grad f x'))
namespace TorusData
variable (D : TorusData)
def c1ModulusExt (f : D.Torus → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  max (gradSupNorm f * ENNReal.ofReal δ) (ENNReal.ofReal (40 * D.sharpScale) * gradOscillation f δ)
def c1Modulus (f : D.Torus → ℝ) (δ : ℝ) : ℝ := (D.c1ModulusExt f δ).toReal
end TorusData
end YangMills.Construction.ReflectionPositivity.TorusCutoffs
end
