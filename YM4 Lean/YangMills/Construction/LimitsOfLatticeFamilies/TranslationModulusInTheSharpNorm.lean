import YangMills.Construction.LimitsOfLatticeFamilies.SpacesOfFunctionsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
abbrev BlockScale (p : Conventions.StandingParameters) : Type := {M : ℕ // IsBlockScale p M}
namespace ModelSpace
variable (p : Conventions.StandingParameters)
def lipNumber : (X : ModelSpace) → (X.Carrier p → ℝ) → ℝ
  | ModelSpace.euclidean, g => TestFunctions.lipConstR4 g
  | ModelSpace.torus, g => TestFunctions.lipConstTorus g
def sharpNorm (M : BlockScale p) : (X : ModelSpace) → (X.Carrier p → ℝ) → ℝ
  | ModelSpace.euclidean, g => TestFunctions.sharpNormR4 (M.1 : ℝ) g
  | ModelSpace.torus, g => TestFunctions.sharpNormTorus (M.1 : ℝ) g
theorem lipNumber_eq_bestLipschitzConstant (X : ModelSpace) (g : X.Carrier p → ℝ) :
    lipNumber p X g = TestFunctions.bestLipschitzConstant (ModelSpace.dist p X) g := by
  cases X <;> rfl
theorem sharpNorm_eq_max (M : BlockScale p) (X : ModelSpace) (g : X.Carrier p → ℝ) :
    sharpNorm p M X g =
      max (TestFunctions.uniformNorm g) (40 * (M.1 : ℝ) * lipNumber p X g) := by
  cases X <;> rfl
variable {p} {X : ModelSpace}
def gradSup (g : c1CompactSupp p X univ) : ℝ≥0∞ :=
  ⨆ x : X.Carrier p, ENNReal.ofReal (TorusMetric.euclidNormVec (ModelSpace.grad p X g.1 x))
def gradOscillation (g : c1CompactSupp p X univ) (r : ℝ≥0) : ℝ≥0∞ :=
  ⨆ (x : X.Carrier p) (y : X.Carrier p) (_ : ModelSpace.dist p X x y ≤ r),
    ENNReal.ofReal (TorusMetric.euclidNormVec (ModelSpace.grad p X g.1 x - ModelSpace.grad p X g.1 y))
def sharpTranslationModulus (M : BlockScale p) (g : c1CompactSupp p X univ) (r : ℝ≥0) : ℝ≥0∞ :=
  max (gradSup g * r) (40 * (M.1 : ℝ≥0∞) * gradOscillation g r)
end ModelSpace
end YangMills.Construction.LatticeLimits
end
