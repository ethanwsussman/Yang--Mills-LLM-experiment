import YangMills.Construction.EuclideanBorel.RepresentationSpectralMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanBorel
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
structure IsStarClosedFamilyOn (X : BorelSubset n) (M : Set (Space n → ℂ)) : Prop where
  eq_zero_off : ∀ f ∈ M, ∀ x, x ∉ X.1 → f x = 0
  indicator_one_mem : X.1.indicator (fun _ => (1 : ℂ)) ∈ M
  mul_mem : ∀ f ∈ M, ∀ g ∈ M, (fun x => f x * g x) ∈ M
  star_mem : ∀ f ∈ M, (fun x => conj (f x)) ∈ M
def SeparatesSupportedMeasures (X : BorelSubset n) (M : Set (Space n → ℂ)) : Prop :=
  ∀ ν : BorelSubset n → ℂ, IsFiniteCombinationMeasure ν → IsSupportedOn ν X →
    (∀ f ∈ M, complexIntegral ν f = 0) → IsZeroMeasure ν
structure IsStarHomOnFamily (X : BorelSubset n) (M : Set (Space n → ℂ))
    (π : M → H →L[ℂ] H) : Prop where
  map_indicator_one : ∀ h : M, h.1 = X.1.indicator (fun _ => (1 : ℂ)) → π h = 1
  map_mul : ∀ f g h : M, h.1 = (fun x => f.1 x * g.1 x) → π h = π f * π g
  map_star : ∀ f h : M, h.1 = (fun x => conj (f.1 x)) → ∀ v w : H,
    ⟪v, π f w⟫_ℂ = ⟪π h v, w⟫_ℂ
def HasSupportedDiagonalMeasures (X : BorelSubset n) (M : Set (Space n → ℂ))
    (π : M → H →L[ℂ] H) : Prop :=
  ∀ v : H, ∃ μ : Measure (Space n), IsFiniteMeasure μ ∧
    IsSupportedOn (fun A => ((μ.real A.1 : ℝ) : ℂ)) X ∧
    ∀ f : M, ⟪v, π f v⟫_ℂ = ∫ x, f.1 x ∂μ
def IsPVMRepresenting (X : BorelSubset n) (M : Set (Space n → ℂ))
    (π : M → H →L[ℂ] H) (P : BorelSubset n → H →L[ℂ] H) : Prop :=
  IsPVM P ∧ IsSupportedOnPVM P X ∧
    ∀ f : M, SpectralIntegralIs P f.1 (π f)
end Operators
def PVMOfDiagonalMeasuresTheorem : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (X : BorelSubset n) (M : Set (Space n → ℂ)) (π : M → H →L[ℂ] H),
      (∀ f ∈ M, IsBoundedMeasurableFn f) →
      IsStarClosedFamilyOn X M →
      SeparatesSupportedMeasures X M →
      IsStarHomOnFamily X M π →
      HasSupportedDiagonalMeasures X M π →
      (∃! P : BorelSubset n → H →L[ℂ] H, IsPVMRepresenting X M π P) ∧
      ∀ P : BorelSubset n → H →L[ℂ] H, IsPVMRepresenting X M π P →
        ∀ T : H →L[ℂ] H, (∀ f : M, T * π f = π f * T) → ∀ A, T * P A = P A * T
end YangMills.Construction.EuclideanBorel
