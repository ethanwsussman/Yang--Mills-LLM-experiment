import YangMills.Construction.HilbertSpace.FormsAndOperators
import YangMills.Construction.SpectralTheory.JointSpectralMeasureOnSpace
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.SpectralTheorem
open YangMills.Construction.BorelSpectral YangMills.Construction.HilbertSpaceBasics
open YangMills.Construction.JointSpectral (dirac)
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
abbrev RealLineSet : Set (Fin 1 → ℝ) := univ
def coordVar (y : RealLineSet) : ℂ := ((y.1 0 : ℝ) : ℂ)
def IsSpectralIntegralOf (A : UnboundedOp H) (E : SpectralMeasure Y H) (g : Y → ℂ) : Prop :=
  (∀ ψ, ψ ∈ A.domain ↔ ψ ∈ E.integralDom g) ∧
    ∀ ψ : A.domain, A ψ = E.integralApply g ψ
def spectralIntegralOp (E : SpectralMeasure Y H) (g : Y → ℂ) : UnboundedOp H :=
  Classical.epsilon fun A => IsSpectralIntegralOf A E g
def IsSpectralMeasureFor (E : SpectralMeasure RealLineSet H) (A : UnboundedOp H) : Prop :=
  IsSpectralIntegralOf A E coordVar
def spectralMeasure (A : UnboundedOp H) : SpectralMeasure RealLineSet H :=
  haveI : Nonempty (SpectralMeasure RealLineSet H) :=
    ⟨dirac le_rfl MeasurableSet.univ ⟨0, mem_univ _⟩⟩
  Classical.epsilon fun E => IsSpectralMeasureFor E A
def IsBoundedInverse (R : H →L[ℂ] H) (B : UnboundedOp H) : Prop :=
  (∀ χ, ∃ h : R χ ∈ B.domain, B ⟨R χ, h⟩ = χ) ∧ ∀ ψ : B.domain, R (B ψ) = ψ
def pushforwardToLine (E : SpectralMeasure Y H) (g : Y → ℝ) (hg : Measurable g) :
    SpectralMeasure RealLineSet H :=
  E.pushforward le_rfl MeasurableSet.univ (fun y => ⟨fun _ => g y, mem_univ _⟩)
    (Measurable.subtype_mk (measurable_pi_iff.mpr fun _ => hg))
def IntegralsAgree {n' : ℕ} {Y' : Set (Fin n' → ℝ)} (E : SpectralMeasure Y H) (g : Y → ℂ)
    (E' : SpectralMeasure Y' H) (g' : Y' → ℂ) : Prop :=
  E.integralDom g = E'.integralDom g' ∧
    ∀ ψ ∈ E.integralDom g, E.integralApply g ψ = E'.integralApply g' ψ
def negHalfLine : BorelSubsets ℝ := ⟨Iio 0, measurableSet_Iio⟩
def SpectralTheoremHolds : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : UnboundedOp H),
    IsSelfAdjointOp A →
    (∀ ψ : A.domain,
      ‖A ψ + Complex.I • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 ∧
      ‖A ψ - Complex.I • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2) ∧
    Function.Bijective (addConst A Complex.I).toFun ∧
    Function.Bijective (addConst A (-Complex.I)).toFun ∧
    (∃ R R' : H →L[ℂ] H, IsBoundedInverse R (addConst A Complex.I) ∧
      IsBoundedInverse R' (addConst A (-Complex.I)) ∧ ‖R‖ ≤ 1 ∧ (∀ χ, R χ = 0 → χ = 0) ∧
      range R = (A.domain : Set H) ∧ star R = R' ∧
      R - star R = (-2 * Complex.I) • (star R * R) ∧
      R - star R = (-2 * Complex.I) • (R * star R)) ∧
    (∃! E : SpectralMeasure RealLineSet H, IsSpectralMeasureFor E A) ∧
    IsSpectralMeasureFor (spectralMeasure A) A ∧
    (∀ (n : ℕ) (Y : Set (Fin n → ℝ)) (E : SpectralMeasure Y H) (g : Y → ℝ)
      (hg : Measurable g), IsSpectralIntegralOf A E (fun y => ((g y : ℝ) : ℂ)) →
        spectralMeasure A = pushforwardToLine E g hg ∧
        ∀ f : ℝ → ℂ, Measurable f →
          IntegralsAgree (spectralMeasure A) (fun y => f (y.1 0)) E (fun y => f (g y))) ∧
    (IsNonnegOp A ↔ spectralMeasure A (realLineSet negHalfLine) = 0) ∧
    ∀ (B : H →L[ℂ] H) (γ γ' : ℝ), A = ofBounded B → γ < γ' →
      IsGE B ((γ : ℂ) • (1 : H →L[ℂ] H)) → IsGE ((γ' : ℂ) • (1 : H →L[ℂ] H)) B →
        spectralMeasure A = JointSpectral.jointMeasureOnSpace le_rfl (fun _ : Fin 1 => B) ∧
        (spectralMeasure A).IsCarriedBy (realLineSet ⟨Icc γ γ', measurableSet_Icc⟩)
end YangMills.Construction.SpectralTheorem
