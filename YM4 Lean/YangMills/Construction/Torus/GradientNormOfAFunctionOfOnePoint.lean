import YangMills.Construction.Torus.FunctionsOfSeveralPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.Conventions (StandingParameters)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints
variable {s : StandingParameters} {E : Ambient}
def ofSinglePoint (g : Pt s E → ℂ) : Tuple s E 1 → ℂ := fun y => g (y 0)
def IsCnAtPoint (ν : ℕ∞) (g : Pt s E → ℂ) : Prop :=
  IsCn ν (ofSinglePoint g)
def basisMultiIndex (μ : Fin 4) : YangMills.Construction.PowerSeries.MultiIndex (4 * 1) :=
  Pi.single (Fin.cast (by norm_num) μ) 1
theorem basisMultiIndex_order (μ : Fin 4) : (basisMultiIndex μ).order = 1 := by
  simp [basisMultiIndex, YangMills.Construction.PowerSeries.MultiIndex.order,
    Finset.sum_pi_single']
def partialAt (μ : Fin 4) (g : Pt s E → ℂ) : Pt s E → ℂ :=
  fun x => multiDeriv (basisMultiIndex μ) (ofSinglePoint g) fun _ => x
def gradient (g : Pt s E → ℂ) : Pt s E → Fin 4 → ℂ :=
  fun x μ => partialAt μ g x
def gradNorm (g : Pt s E → ℂ) : Pt s E → ℝ :=
  fun x => Real.sqrt (∑ μ, ‖gradient g x μ‖ ^ 2)
def gradSupNorm (g : Pt s E → ℂ) : ℝ≥0∞ := ⨆ x, ENNReal.ofReal (gradNorm g x)
def c1GradNorm (g : Pt s E → ℂ) : ℝ≥0∞ :=
  max (tupleSupNorm (ofSinglePoint g)) (gradSupNorm g)
theorem tupleSupNorm_ofSinglePoint (g : Pt s E → ℂ) :
    tupleSupNorm (ofSinglePoint g) = ⨆ x, ENNReal.ofReal ‖g x‖ :=
  (Equiv.funUnique (Fin 1) (Pt s E)).iSup_congr fun _ => rfl
end YangMills.Construction.AmbientPoints
