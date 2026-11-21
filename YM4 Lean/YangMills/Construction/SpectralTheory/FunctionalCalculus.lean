import YangMills.Construction.SpectralTheory.IntegralAndPushforward
import Mathlib
set_option autoImplicit false
open Set
open scoped NNReal
noncomputable section
namespace YangMills.Construction
namespace SpectralTheory
def nonnegReals : BorelSets 1 :=
  ⟨{x | 0 ≤ x 0}, measurableSet_le measurable_const (measurable_pi_apply 0)⟩
def coordFun {n : ℕ} (r : Fin n) (x : Fin n → ℝ) : ℂ :=
  (x r : ℂ)
theorem measurable_coordFun {n : ℕ} (r : Fin n) : Measurable (coordFun r) :=
  Complex.measurable_ofReal.comp (measurable_pi_apply r)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def HasSpectralResolution (A : UnboundedOperator H) (F : ProjectionMeasure 1 H) : Prop :=
  A = F.functionalCalculus (coordFun 0)
def IsSpectralProjection (A : UnboundedOperator H) (P : H →L[ℂ] H) : Prop :=
  ∃ F : ProjectionMeasure 1 H, HasSpectralResolution A F ∧ ∃ Δ : BorelSets 1, P = F Δ
namespace ProjectionMeasure
def expIMulOp (F : ProjectionMeasure 1 H) (u : ℝ) : UnboundedOperator H :=
  F.functionalCalculus fun x => Complex.exp (Complex.I * u * x 0)
def absValueOp (F : ProjectionMeasure 1 H) : UnboundedOperator H :=
  F.functionalCalculus fun x => ((|x 0| : ℝ) : ℂ)
def expNegMulOp (F : ProjectionMeasure 1 H) (t : ℝ≥0) : UnboundedOperator H :=
  F.functionalCalculusOn nonnegReals fun x => Complex.exp (-(t : ℂ) * (x.1 0 : ℝ))
def coordinateOp {n : ℕ} [NeZero n] (E : ProjectionMeasure n H) (r : Fin n) :
    UnboundedOperator H :=
  E.functionalCalculus (coordFun r)
end ProjectionMeasure
def opKernel (A : UnboundedOperator H) : Set H :=
  {ψ | ∃ h : ψ ∈ A.domain, A ⟨ψ, h⟩ = 0}
def IsPositiveOp (A : UnboundedOperator H) : Prop :=
  ∃ F : ProjectionMeasure 1 H, HasSpectralResolution A F ∧ F.IsConcentratedOn nonnegReals
def StronglyCommute {ι : Type*} (A : ι → UnboundedOperator H) : Prop :=
  (∀ i, ∃ F : ProjectionMeasure 1 H, HasSpectralResolution (A i) F) ∧
    ∀ i j, i ≠ j → ∀ P Q : H →L[ℂ] H,
      IsSpectralProjection (A i) P → IsSpectralProjection (A j) Q → Commute P Q
def IsJointSpectralMeasure {n : ℕ} [NeZero n] (E : ProjectionMeasure n H)
    (A : Fin n → UnboundedOperator H) : Prop :=
  ∀ r, A r = E.coordinateOp r
def IsJointSpectrum {n : ℕ} [NeZero n] (S : Set (Fin n → ℝ)) (A : Fin n → UnboundedOperator H) : Prop :=
  ∃ E : ProjectionMeasure n H, IsJointSpectralMeasure E A ∧ S = E.support
end SpectralTheory
end YangMills.Construction
