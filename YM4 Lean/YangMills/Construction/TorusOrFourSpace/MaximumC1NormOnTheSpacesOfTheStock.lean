import YangMills.Construction.TorusOrFourSpace.ChoicesOfDenseSetsComponentsAndTheirFamily
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNorm
import YangMills.Construction.TorusOrFourSpace.StandingSignsOfTheSupportAdaptedFamily
import YangMills.Construction.TorusOrFourSpace.StockOfSupportsAndTheCountableFamily
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.MaxC1Norm
open Kind VectorClasses
variable (D : Params) (E : Kind)
def NormComparison (Q : Set (E.Pt D)) : Prop :=
  ∀ f ∈ c1VanishingOutside D E Q,
    SupportAdapted.c1MaxNorm D E f ≤ SupportAdapted.c1EuclidNorm D E f ∧
    SupportAdapted.c1EuclidNorm D E f ≤ 2 * SupportAdapted.c1MaxNorm D E f ∧
    sharpNormQ D E f ≤ ENNReal.ofReal (80 * D.M) * SupportAdapted.c1MaxNorm D E f
def SeparableBanachSameDense (Q : Set (E.Pt D)) : Prop :=
  IsNormOn D E (c1VanishingOutside D E Q) (SupportAdapted.c1MaxNorm D E) ∧
  IsSeparableBanachWrt D E (SupportAdapted.c1MaxNorm D E) (c1VanishingOutside D E Q) ∧
  ∀ A, A ⊆ c1VanishingOutside D E Q →
    (IsDenseWrt D E (SupportAdapted.c1MaxNorm D E) (c1VanishingOutside D E Q) A ↔
      IsDenseWrt D E (SupportAdapted.c1EuclidNorm D E) (c1VanishingOutside D E Q) A)
def IsMaxNormChoice (C : supportStock D E → Set (E.Pt D → ℝ)) : Prop :=
  ∀ Q, C Q ⊆ c1VanishingOutside D E Q ∧
    IsDenseWrt D E (SupportAdapted.c1MaxNorm D E) (c1VanishingOutside D E Q) (C Q)
def CountableFamilyMaxNorm (Q : Set (E.Pt D)) : Prop :=
  c1VanishingOutside D E Q = c1SupportedIn D E Q ∧
  (∀ f ∈ c1VanishingOutside D E Q, ∀ y, y ∉ Q → gradVec D E f y = 0) ∧
  IsSeparableBanachWrt D E (SupportAdapted.c1MaxNorm D E) (c1VanishingOutside D E Q) ∧
  ∀ A, A ⊆ c1VanishingOutside D E Q →
    IsDenseWrt D E (SupportAdapted.c1MaxNorm D E) (c1VanishingOutside D E Q) A →
    IsDenseWrt D E (sharpNormQ D E) (c1VanishingOutside D E Q) A
def Claim : Prop :=
  ∀ (D : Params) (E : Kind),
    (∀ Q ∈ supportStock D E,
      NormComparison D E Q ∧ SeparableBanachSameDense D E Q ∧
        CountableFamilyMaxNorm D E Q) ∧
    ∀ C : supportStock D E → Set (E.Pt D → ℝ),
      IsDenseChoice D E C ↔ IsMaxNormChoice D E C
end YangMills.Construction.PeriodicSpace.MaxC1Norm
