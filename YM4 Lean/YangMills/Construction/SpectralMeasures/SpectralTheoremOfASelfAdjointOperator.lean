import YangMills.Construction.HilbertSpaces.FormsOperatorsAndFamiliesInAHilbertSpace
import YangMills.Construction.SpectralMeasures.BorelFunctionOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanBorel
open YangMills.Construction.FormsOperators (IsExtendedBy IsSelfAdj Commutes UnitaryMap
  addConst ofCLM)
open YangMills.Construction.SpectralTheory (UnboundedOp)
section SelfAdjoint
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def IsBoundedInverse (R : H →L[ℂ] H) (B : UnboundedOp H) : Prop :=
  (∀ ψ, ∃ h : R ψ ∈ B.domain, B ⟨R ψ, h⟩ = ψ) ∧ ∀ χ : B.domain, R (B χ) = χ
def resolventAtI (A : UnboundedOp H) : H →L[ℂ] H :=
  Classical.epsilon fun R => IsBoundedInverse R (addConst A Complex.I)
def IsCayleyTransform (A : UnboundedOp H) (U : UnitaryMap H H) : Prop :=
  ∀ ψ, (∃ h : resolventAtI A ψ ∈ A.domain,
      U ψ = addConst A (-Complex.I) ⟨resolventAtI A ψ, h⟩) ∧
    U ψ = ψ - (2 * Complex.I) • resolventAtI A ψ
def IsSpectralIntegralOp {n : ℕ} (A : UnboundedOp H) (E : BorelSubset n → H →L[ℂ] H)
    (f : Space n → ℂ) : Prop :=
  ∃ h : (A.domain : Set H) = sqIntegrableDomain E f,
    ∀ χ : A.domain, A χ = spectralIntegral E f ⟨χ, h ▸ χ.2⟩
def IsSpectralResolution (A : UnboundedOp H) (E : BorelSubset 1 → H →L[ℂ] H) : Prop :=
  IsPVM E ∧ IsSpectralIntegralOp A E lineCoord
def spectralResolution (A : UnboundedOp H) : BorelSubset 1 → H →L[ℂ] H :=
  Classical.epsilon (IsSpectralResolution A)
end SelfAdjoint
namespace SelfAdjoint
def SpectralTheorem : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : UnboundedOp H),
    IsSelfAdj A →
    Function.Bijective (addConst A Complex.I).toFun ∧
    Function.Bijective (addConst A (-Complex.I)).toFun ∧
    (∀ χ : A.domain,
      ‖addConst A Complex.I χ‖ ^ 2 = ‖A χ‖ ^ 2 + ‖(χ : H)‖ ^ 2 ∧
      ‖addConst A (-Complex.I) χ‖ ^ 2 = ‖A χ‖ ^ 2 + ‖(χ : H)‖ ^ 2) ∧
    IsBoundedInverse (resolventAtI A) (addConst A Complex.I) ∧
    Function.Injective (resolventAtI A) ∧
    (∃ U : UnitaryMap H H, IsCayleyTransform A U) ∧
    (∀ A' : UnboundedOp H, IsSelfAdj A' → IsExtendedBy A A' → A' = A) ∧
    (∃! E : BorelSubset 1 → H →L[ℂ] H, IsSpectralResolution A E) ∧
    IsSpectralResolution A (spectralResolution A) ∧
    (∀ B : H →L[ℂ] H, Commutes B (resolventAtI A) →
      ∀ Δ, Commutes B (spectralResolution A Δ)) ∧
    ∀ T : H →L[ℂ] H, A = ofCLM T → ∀ B : H →L[ℂ] H, Commutes B T →
      ∀ Δ, Commutes B (spectralResolution A Δ)
end SelfAdjoint
end YangMills.Construction.EuclideanBorel
