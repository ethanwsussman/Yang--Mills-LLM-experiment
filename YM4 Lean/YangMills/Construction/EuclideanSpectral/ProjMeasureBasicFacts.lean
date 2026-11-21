import YangMills.Construction.HilbertSpace.EuclideanProjectionMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace EuclideanSpectral
namespace ProjMeasure
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
  [NeZero n]
def IsFiniteMeasureRep {n : ℕ} (m : BorelSubset n → ℂ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsFiniteMeasure μ ∧ ∀ B : BorelSubset n, m B = ((μ.real B.1 : ℝ) : ℂ)
def diagMeasure (E : ProjMeasure H n) (ψ : H) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  Classical.epsilon (IsFiniteMeasureRep (E.diag ψ))
def IsWeakIntegralOp (E : ProjMeasure H n) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (A : H →ₗ[ℂ] H) : Prop :=
  ∀ ψ : H, inner ℂ ψ (A ψ) = ∫ x, f x ∂(E.diagMeasure ψ)
end ProjMeasure
open ProjMeasure
def ProjMeasureBasicFacts : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) [NeZero n]
    (E : ProjMeasure H n),
    ((∀ A : H →ₗ[ℂ] H, (∀ ψ : H, inner ℂ ψ (A ψ) = 0) → A = 0) ∧
      ∀ (U : H →ₗ[ℂ] H) (hU : IsUnitaryMap U) (φ ψ : H),
        inner ℂ (U φ) (U ψ) = inner ℂ φ ψ ∧ inner ℂ (hU.inv φ) ψ = inner ℂ φ (U ψ)) ∧
    (∀ p : H →ₗ[ℂ] H, IsOrthProj p →
      (∀ ψ : H, ((‖p ψ‖ ^ 2 : ℝ) : ℂ) = inner ℂ ψ (p ψ) ∧ (inner ℂ ψ (p ψ)).re ≤ ‖ψ‖ ^ 2) ∧
      ∀ (U : H →ₗ[ℂ] H) (hU : IsUnitaryMap U),
        IsOrthProj (hU.inv ∘ₗ p ∘ₗ U)) ∧
    (∀ ψ : H, IsFiniteMeasureRep (E.diag ψ) (E.diagMeasure ψ) ∧
      (∀ B : BorelSubset n, E.diag ψ B = ((‖E B ψ‖ ^ 2 : ℝ) : ℂ)) ∧
      E.diag ψ (BorelSubset.univ n) = ((‖ψ‖ ^ 2 : ℝ) : ℂ)) ∧
    (∀ (φ ψ : H) (z : ℂ) (B : BorelSubset n),
      E.diag (z • ψ) B = ((‖z‖ ^ 2 : ℝ) : ℂ) * E.diag ψ B ∧
      (E.diagMeasure (φ + ψ)).real B.1 ≤
        2 * (E.diagMeasure φ).real B.1 + 2 * (E.diagMeasure ψ).real B.1) ∧
    (E ⟨∅, MeasurableSet.empty⟩ = 0 ∧
      (∀ B B' : BorelSubset n, Disjoint B.1 B'.1 → E ⟨B.1 ∪ B'.1, B.2.union B'.2⟩ = E B + E B') ∧
      ∀ B B' : BorelSubset n, E B ∘ₗ E B' = E ⟨B.1 ∩ B'.1, B.2.inter B'.2⟩) ∧
    ((∀ B : BorelSubset n, E.IsNull B ↔ ∀ ψ : H, E.diag ψ B = 0) ∧
      (∀ B B' : BorelSubset n, B'.1 ⊆ B.1 → E.IsNull B → E.IsNull B') ∧
      ∀ (ι : Type) [Countable ι] (B : ι → BorelSubset n), (∀ i, E.IsNull (B i)) →
        E.IsNull ⟨⋃ i, (B i).1, MeasurableSet.iUnion fun i => (B i).2⟩) ∧
    ∀ f : EuclideanSpace ℝ (Fin n) → ℂ, Measurable f → (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
      (∃! A : H →ₗ[ℂ] H, E.IsWeakIntegralOp f A) ∧
      ∀ A : H →ₗ[ℂ] H, E.IsWeakIntegralOp f A →
        ∀ ψ : H, ‖A ψ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(E.diagMeasure ψ)
end EuclideanSpectral
end YangMills.Construction
