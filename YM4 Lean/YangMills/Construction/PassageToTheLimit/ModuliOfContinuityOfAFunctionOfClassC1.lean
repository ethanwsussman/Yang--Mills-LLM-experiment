import YangMills.Construction.PassageToTheLimit.SpaceTestFunctionsTranslationsReflectionsPositions
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
namespace Ambient
variable {s : Conventions.StandingParameters} {E : Ambient}
def gradModulus (f : E.c1Compact s) (δ : ℝ≥0) : ℝ≥0∞ :=
  ⨆ (x : E.Carrier s) (y : E.Carrier s) (_ : E.pointDist s x y ≤ δ),
    ENNReal.ofReal (TorusMetric.euclidNormVec (E.grad s f.1 x - E.grad s f.1 y))
def continuityModulus (M : SharpParameter) (f : E.c1Compact s) (δ : ℝ≥0) : ℝ≥0∞ :=
  max (E.gradSup s f.1 * δ) (ENNReal.ofReal (40 * (M : ℝ)) * gradModulus f δ)
end Ambient
end LimitSpaces
end YangMills.Construction
