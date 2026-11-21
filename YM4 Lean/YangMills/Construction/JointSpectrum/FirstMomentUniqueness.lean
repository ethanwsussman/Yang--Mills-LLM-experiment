import YangMills.Construction.JointSpectrum.SpectralIntegral
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open JointSpectrum JointSpectrum.SpectralIntegral
namespace JointSpectrum.FirstMoments
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : Type*} [Fintype J] [Nonempty J]
def IsDiagonalMeasure (E' : ProjectionValuedMeasure J H) (ψ : H)
    (ρ : Measure (SpectralDomain J)) : Prop :=
  IsFiniteMeasure ρ ∧ ∀ T, inner ℂ ψ (E'.E T ψ) = ((ρ.real T.1 : ℝ) : ℂ)
def HasFirstMoments (S : CommutingFamily H J) (E' : ProjectionValuedMeasure J H) : Prop :=
  ∀ (ψ : H) (ρ : Measure (SpectralDomain J)), IsDiagonalMeasure E' ψ ρ →
    inner ℂ ψ (S.A ψ) = ∫ p, (((p.1 : ℝ) : ℂ)) ∂ρ ∧
    ∀ α, inner ℂ ψ ((S.B α : H →L[ℂ] H) ψ) = ∫ p, ((p.2 α : ℂ)) ∂ρ
def EqJointSpectralMeasure (S : CommutingFamily H J) (E' : ProjectionValuedMeasure J H) : Prop :=
  ∀ (Δ : {Δ : Set (SpectralDomain J) // MeasurableSet Δ}) (ψ : H),
    E'.E Δ ψ = jointSpectralMeasure S Δ.1 ψ
def FirstMomentUniquenessStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : Type) [Fintype J] [Nonempty J] (S : CommutingFamily H J),
    (∃ E : ProjectionValuedMeasure J H, EqJointSpectralMeasure S E ∧ HasFirstMoments S E) ∧
    ∀ E' : ProjectionValuedMeasure J H, HasFirstMoments S E' → EqJointSpectralMeasure S E'
end JointSpectrum.FirstMoments
end YangMills.Construction
