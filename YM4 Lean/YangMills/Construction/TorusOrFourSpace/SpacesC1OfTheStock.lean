import YangMills.Construction.TorusOrFourSpace.BoxesStockOfSupportsAndFamilyOfTuples
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNorm
import YangMills.Construction.TorusOrFourSpace.StandingSignsOfTheSupportAdaptedFamily
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.C1OfStock
open Kind VectorClasses
variable (D : Params) (E : Kind)
def MemIffSupportSubset (Q : Set (Kind.Pt D E)) : Prop :=
  (∀ f ∈ c1Set D E, f ∈ c1VanishingOutside D E Q ↔ supportQ D E f ⊆ Q) ∧
  ∀ f ∈ c1VanishingOutside D E Q,
    IsCompactQ D E (supportQ D E f) ∧
    (∀ y, y ∉ Q → f y = 0) ∧
    (∀ y, y ∉ Q → gradVec D E f y = 0) ∧
    SupportAdapted.c1EuclidNorm D E f < ∞
def SharpNormBound (Q : Set (Kind.Pt D E)) : Prop :=
  IsNormOn D E (c1VanishingOutside D E Q) (sharpNormQ D E) ∧
  ∀ f ∈ c1VanishingOutside D E Q,
    sharpNormQ D E f ≤ ENNReal.ofReal (40 * D.M) * SupportAdapted.c1EuclidNorm D E f
def Holds : Prop :=
  ∀ (D : Params) (E : Kind), ∀ Q ∈ supportStock D E,
    MemIffSupportSubset D E Q ∧ SharpNormBound D E Q
end YangMills.Construction.PeriodicSpace.C1OfStock
