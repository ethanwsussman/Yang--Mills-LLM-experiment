import YangMills.Construction.HilbertSpace.CommutingSemigroupGroupPairs
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder NNReal
noncomputable section
namespace YangMills.Construction.SpectralCalculus
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def HasSpectralTransform (T : ℝ≥0 → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H) (u v : H)
    (μ : ComplexMeasure SpectralPlane) : Prop :=
  ∀ (t : ℝ≥0) (s : ℝ), inner ℂ u (T t (U s v)) = laplaceFourier μ t s
def pairSpectralMeasure (T : ℝ≥0 → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H) (u v : H) :
    ComplexMeasure SpectralPlane :=
  Classical.epsilon (HasSpectralTransform T U u v)
def IsJointSpectralPVM (T : ℝ≥0 → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H)
    (P : ProjValuedMeasure H) : Prop :=
  ∀ (t : ℝ≥0) (s : ℝ), P.IsBoundedSpectralIntegral (spectralCharacter t s) (T t * U s)
def expNegTwoMul (t : ℝ≥0) (p : SpectralPlane) : ℂ :=
  Complex.exp ((-2 * (t : ℝ) * (p.1 : ℝ) : ℝ) : ℂ)
structure JointSpectralProperties (T : ℝ≥0 → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H) : Prop where
  hasSpectralTransform : ∀ u v, HasSpectralTransform T U u v (pairSpectralMeasure T U u v)
  eq_of_hasSpectralTransform : ∀ u v (μ : ComplexMeasure SpectralPlane),
    HasSpectralTransform T U u v μ → μ = pairSpectralMeasure T U u v
  add_left : ∀ u₁ u₂ v, pairSpectralMeasure T U (u₁ + u₂) v =
    pairSpectralMeasure T U u₁ v + pairSpectralMeasure T U u₂ v
  smul_left : ∀ (a : ℂ) u v, pairSpectralMeasure T U (a • u) v =
    conj a • pairSpectralMeasure T U u v
  add_right : ∀ u v₁ v₂, pairSpectralMeasure T U u (v₁ + v₂) =
    pairSpectralMeasure T U u v₁ + pairSpectralMeasure T U u v₂
  smul_right : ∀ (a : ℂ) u v, pairSpectralMeasure T U u (a • v) =
    a • pairSpectralMeasure T U u v
  conj_symm : ∀ u v, pairSpectralMeasure T U v u = conjMeasure (pairSpectralMeasure T U u v)
  nonneg : ∀ v (B : MeasurableSubtype SpectralPlane), 0 ≤ pairSpectralMeasure T U v v B.1
  mass : ∀ v, pairSpectralMeasure T U v v univ = ((‖v‖ ^ 2 : ℝ) : ℂ)
  norm_sq_le : ∀ u v (B : MeasurableSubtype SpectralPlane),
    ‖pairSpectralMeasure T U u v B.1‖ ^ 2 ≤
      (pairSpectralMeasure T U u u B.1).re * (pairSpectralMeasure T U v v B.1).re
  variation_le : ∀ u v, (pairSpectralMeasure T U u v).variation.real univ ≤ ‖u‖ * ‖v‖
  right_eq_density : ∀ u v (t : ℝ≥0) (s : ℝ), pairSpectralMeasure T U u (T t (U s v)) =
    withDensityComplex (spectralCharacter t s) (pairSpectralMeasure T U u v)
  both_eq_density : ∀ v (t : ℝ≥0), pairSpectralMeasure T U (T t v) (T t v) =
    withDensityComplex (expNegTwoMul t) (pairSpectralMeasure T U v v)
  existsUnique_pvm : ∃! P : ProjValuedMeasure H, IsJointSpectralPVM T U P
  inner_pvm : ∀ P : ProjValuedMeasure H, IsJointSpectralPVM T U P →
    ∀ u v (B : MeasurableSubtype SpectralPlane),
      inner ℂ u (P B v) = pairSpectralMeasure T U u v B.1
end
def JointSpectralTheorem : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : ℝ≥0 → H →L[ℂ] H) (U : ℝ → H →L[ℂ] H),
    IsCommutingSemigroupGroup T U → JointSpectralProperties T U
end YangMills.Construction.SpectralCalculus
end
