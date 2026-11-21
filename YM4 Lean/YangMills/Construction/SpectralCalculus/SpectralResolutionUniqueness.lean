import YangMills.Construction.SpectralCalculus.JointSpectralMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal
noncomputable section
namespace YangMills.Construction.SpectralCalculus
section PartialOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def partialOfCLM [CompleteSpace H] (B : H →L[ℂ] H) : PartialOperator H :=
  (B : H →ₗ[ℂ] H).toPMap ⊤
def compDomain [CompleteSpace H] (A B : PartialOperator H) : Submodule ℂ H :=
  (A.domain.comap B.toFun).map B.domain.subtype
def partialComp [CompleteSpace H] (A B : PartialOperator H) : PartialOperator H :=
  A.comp (B.domRestrict (compDomain A B)) (by
    rintro ⟨x, hx, hxB⟩
    obtain ⟨y, hy, rfl⟩ := hx
    exact hy)
end PartialOperators
def fstCylinderSet (S : MeasurableSubtype ℝ) : MeasurableSubtype SpectralPlane :=
  ⟨(((↑) : ℝ≥0 → ℝ) ⁻¹' S.1) ×ˢ univ, (measurable_coe_nnreal_real S.2).prod MeasurableSet.univ⟩
def SpectralResolutionUniqueness : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (∀ μ ν : ProjValuedMeasure H,
      μ.spectralIntegral coordSnd = ν.spectralIntegral coordSnd →
        (∀ S : MeasurableSubtype ℝ, μ (cylinderSet S) = ν (cylinderSet S)) ∧
        ∀ F : ℝ → ℂ, Measurable F →
          μ.spectralIntegral (fun p => F p.2) = ν.spectralIntegral fun p => F p.2) ∧
    (∀ (A : PartialOperator H) (μ : ProjValuedMeasure H), IsSpectralIntegralSnd μ A →
      (∀ S : MeasurableSubtype ℝ, spectralProjection A S = μ (cylinderSet S)) ∧
      ∀ F : ℝ → ℂ, Measurable F → functionalCalculus F A = μ.spectralIntegral fun p => F p.2) ∧
    ∀ μ : ProjValuedMeasure H,
      HasSpectralResolution (μ.spectralIntegral coordFst) ∧
      HasSpectralResolution (μ.spectralIntegral coordSnd) ∧
      (∀ S : MeasurableSubtype ℝ,
        spectralProjection (μ.spectralIntegral coordFst) S = μ (fstCylinderSet S) ∧
        spectralProjection (μ.spectralIntegral coordSnd) S = μ (cylinderSet S)) ∧
      (∀ F : ℝ → ℂ, Measurable F →
        functionalCalculus F (μ.spectralIntegral coordFst) =
            μ.spectralIntegral (fun p => F (p.1 : ℝ)) ∧
        functionalCalculus F (μ.spectralIntegral coordSnd) = μ.spectralIntegral fun p => F p.2) ∧
      CommuteSpectrally (μ.spectralIntegral coordFst) (μ.spectralIntegral coordSnd) ∧
      ∀ (T : ℝ≥0 → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H), IsCommutingSemigroupGroup T U →
        IsJointSpectralPVM T U μ →
        (∀ t, partialOfCLM (T t) =
          expNegMul t (μ.spectralIntegral coordFst)) ∧
        (∀ s, partialOfCLM (U s) =
          expIMul s (μ.spectralIntegral coordSnd)) ∧
        ∀ t s, partialComp (expNegMul t (μ.spectralIntegral coordFst))
            (expIMul s (μ.spectralIntegral coordSnd)) =
          μ.spectralIntegral (spectralCharacter t s)
end YangMills.Construction.SpectralCalculus
end
