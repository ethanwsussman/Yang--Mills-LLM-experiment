import YangMills.Construction.ReflectionPositivity.FunctionsOfClassC1AndSupports
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
abbrev ScaleParam : Type := Set.Ici (1 : ℝ)
section SharpNorm
variable (D : MirrorData) {𝕜 : Type*} [RCLike 𝕜]
def normSharp (M : ScaleParam) : (E : Ambient) → (E.Point D → 𝕜) → ℝ
  | torus, f => TestFunctions.sharpNormTorus (M : ℝ) f
  | euclidean, f => TestFunctions.sharpNormR4 (M : ℝ) f
end SharpNorm
section Modulus
variable {D : MirrorData} {𝕜 : Type*} [RCLike 𝕜] {E : Ambient}
def vecLength (v : Fin 4 → 𝕜) : ℝ := Real.sqrt (∑ μ, ‖v μ‖ ^ 2)
def gradSup (f : compactC1 D 𝕜 E) : ℝ≥0∞ :=
  ⨆ x : E.Point D, ENNReal.ofReal (vecLength (grad D E f.1 x))
def gradOsc (f : compactC1 D 𝕜 E) (δ : ℝ≥0) : ℝ≥0∞ :=
  ⨆ (x : E.Point D) (y : E.Point D) (_ : metric D E x y ≤ δ),
    ENNReal.ofReal (vecLength (grad D E f.1 x - grad D E f.1 y))
def smoothModulus (M : ScaleParam) (f : compactC1 D 𝕜 E) (δ : ℝ≥0) : ℝ :=
  max ((gradSup f).toReal * δ) (40 * (M : ℝ) * (gradOsc f δ).toReal)
end Modulus
end YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
end
