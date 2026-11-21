import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints
variable {s : Conventions.StandingParameters} {E : Ambient}
variable (s) in
def ambientSharpNorm (M : Set.Ici (1 : ℝ)) : (E : Ambient) → (Pt s E → ℝ) → ℝ
  | .euclidean, f => TestFunctions.sharpNormR4 (M : ℝ) f
  | .torus, f => TestFunctions.sharpNormTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (M : ℝ) f
end YangMills.Construction.AmbientPoints
