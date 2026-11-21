import YangMills.Construction.HilbertSpace.SemidefiniteFormHilbertSpace
import YangMills.Construction.HilbertSpaces.CompletionExtensionDecompositionAndForms
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction
namespace ProjectionMeasures
open OneLoopNotation ComplexHilbert HilbertToolkit
section Completions
variable {V : Type} [AddCommGroup V] [Module ℂ V]
abbrev FormQuotientCompletion (q : V → V → ℂ) : Type := FormCompletion.FormHilbertSpace q
def quotientClass (q : V → V → ℂ) (F : V) : FormQuotientCompletion q :=
  FormCompletion.classVec q F
end Completions
section Projections
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
structure IsOrthProjection [CompleteSpace H] (A : BddOp H) : Prop where
  adjoint_self : adjointOp A = A
  idempotent : A = A ^ 2
end Projections
abbrev FourBorelSet : Type := {S : Set (Fin 4 → ℝ) // MeasurableSet S}
def FourBorelSet.univ : FourBorelSet := ⟨Set.univ, MeasurableSet.univ⟩
def FourBorelSet.iUnion (S : ℕ → FourBorelSet) : FourBorelSet :=
  ⟨⋃ n, (S n).1, MeasurableSet.iUnion fun n => (S n).2⟩
def FourBorelSet.compl (S : FourBorelSet) : FourBorelSet := ⟨S.1ᶜ, S.2.compl⟩
structure HasMeasureDecomposition (μ : FourBorelSet → ℂ) {r : ℕ} (c : Fin r → ℂ)
    (ν : Fin r → Measure (Fin 4 → ℝ)) : Prop where
  length_pos : 0 < r
  isFinite : ∀ n, IsFiniteMeasure (ν n)
  apply_eq : ∀ S : FourBorelSet, μ S = ∑ n, c n * ((ν n S.1).toReal : ℂ)
def IsFinComplexMeasure (μ : FourBorelSet → ℂ) : Prop :=
  ∃ (r : ℕ) (c : Fin r → ℂ) (ν : Fin r → Measure (Fin 4 → ℝ)), HasMeasureDecomposition μ c ν
def IsBddMeasurableFun (u : (Fin 4 → ℝ) → ℂ) : Prop :=
  Measurable u ∧ ∃ B : ℝ, ∀ p, ‖u p‖ ≤ B
def IsDecompIntegral (μ : FourBorelSet → ℂ) (u : (Fin 4 → ℝ) → ℂ) (z : ℂ) : Prop :=
  ∃ (r : ℕ) (c : Fin r → ℂ) (ν : Fin r → Measure (Fin 4 → ℝ)),
    HasMeasureDecomposition μ c ν ∧ z = ∑ n, c n * ∫ p, u p ∂(ν n)
def complexMeasureIntegral (μ : FourBorelSet → ℂ) (u : (Fin 4 → ℝ) → ℂ) : ℂ :=
  Classical.epsilon (IsDecompIntegral μ u)
section Measures
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
structure IsPVM [CompleteSpace H] (E : FourBorelSet → BddOp H) : Prop where
  isProj : ∀ S, IsOrthProjection (E S)
  univ_eq : E FourBorelSet.univ = idOp H
  sigma_additive : ∀ (ψ : H) (S : ℕ → FourBorelSet),
    Pairwise (fun k l => Disjoint (S k).1 (S l).1) →
      HasSum (fun k => ⟪ψ, E (S k) ψ⟫_ℂ) ⟪ψ, E (FourBorelSet.iUnion S) ψ⟫_ℂ
def IsSupportedOn [CompleteSpace H] (E : FourBorelSet → BddOp H) (S : FourBorelSet) : Prop :=
  E S.compl = 0
def spectralScalarMeasure [CompleteSpace H] (E : FourBorelSet → BddOp H) (ψ ψ' : H)
    (S : FourBorelSet) : ℂ :=
  ⟪ψ, E S ψ'⟫_ℂ
end Measures
section WeakIntegrals
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {P : Type} [TopologicalSpace P] [MeasureSpace P]
structure HasWeakIntegrandData [CompleteSpace H] (C : Set P) (Ξ : P → H) (φ : P → ℂ) : Prop where
  measurableSet : MeasurableSet C
  norm_bdd : ∃ B : ℝ, ∀ x ∈ C, ‖Ξ x‖ ≤ B
  continuousOn_inner : ∀ ψ : H, ContinuousOn (fun x => ⟪ψ, Ξ x⟫_ℂ) C
  integrableOn : IntegrableOn φ C
def HasWeakIntegral [CompleteSpace H] (C : Set P) (Ξ : P → H) (φ : P → ℂ) (v : H) : Prop :=
  ∀ ψ : H, ⟪ψ, v⟫_ℂ = ∫ x in C, φ x * ⟪ψ, Ξ x⟫_ℂ
def weakInt [CompleteSpace H] (C : Set P) (Ξ : P → H) (φ : P → ℂ) : H :=
  Classical.epsilon (HasWeakIntegral C Ξ φ)
end WeakIntegrals
end ProjectionMeasures
end YangMills.Construction
