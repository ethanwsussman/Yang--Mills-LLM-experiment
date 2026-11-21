import YangMills.Construction.Towers.FormsOnTowers
import YangMills.Construction.Towers.FunctionsOfFiniteBondSets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower.FullSpace
namespace UniqueValue
variable {L k j : ℕ}
def perturbedTuple (F : Finset (Edge L k j)) (X X' U : Edge L k j → Matrices.ComplexMatrix2)
    (s t : ℂ) : F → Matrices.ComplexMatrix2 :=
  fun e => Matrices.ComplexMatrix2.matExp (Complex.I • (s • X e + t • X' e)) * U e
def AgreeAlongPerturbations (𝕜 : Type) [NormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {E : Type}
    (U X X' : Edge L k j → Matrices.ComplexMatrix2)
    (F₁ : Finset (Edge L k j)) (O₁ : Set (F₁ → Matrices.ComplexMatrix2))
    (f₁ : (F₁ → Matrices.ComplexMatrix2) → E)
    (F₂ : Finset (Edge L k j)) (O₂ : Set (F₂ → Matrices.ComplexMatrix2))
    (f₂ : (F₂ → Matrices.ComplexMatrix2) → E) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ s t : 𝕜, ‖s‖ < ε → ‖t‖ < ε →
    perturbedTuple F₁ X X' U (algebraMap 𝕜 ℂ s) (algebraMap 𝕜 ℂ t) ∈ O₁ ∧
    perturbedTuple F₂ X X' U (algebraMap 𝕜 ℂ s) (algebraMap 𝕜 ℂ t) ∈ O₂ ∧
    f₁ (perturbedTuple F₁ X X' U (algebraMap 𝕜 ℂ s) (algebraMap 𝕜 ℂ t)) =
      f₂ (perturbedTuple F₂ X X' U (algebraMap 𝕜 ℂ s) (algebraMap 𝕜 ℂ t))
def PresentationsAgreeAlongPerturbations (L k j : ℕ) (𝕜 : Type) [NormedField 𝕜]
    [NormedAlgebra 𝕜 ℂ] (𝒢 : Set Matrices.ComplexMatrix2)
    (IsDirection : (Edge L k j → Matrices.ComplexMatrix2) → Prop) (E : Type) : Prop :=
  ∀ 𝔇 : Set (Edge L k j → Matrices.ComplexMatrix2), IsFinitelyOpen 𝒢 𝔇 →
    ∀ (h : (Edge L k j → Matrices.ComplexMatrix2) → E) (U : Edge L k j → Matrices.ComplexMatrix2),
    U ∈ 𝔇 →
    ∀ (F₁ : Finset (Edge L k j)) (O₁ : Set (F₁ → Matrices.ComplexMatrix2))
      (f₁ : (F₁ → Matrices.ComplexMatrix2) → E)
      (F₂ : Finset (Edge L k j)) (O₂ : Set (F₂ → Matrices.ComplexMatrix2))
      (f₂ : (F₂ → Matrices.ComplexMatrix2) → E),
      IsLocalPresentation 𝒢 𝔇 h U F₁ O₁ f₁ → IsLocalPresentation 𝒢 𝔇 h U F₂ O₂ f₂ →
      ∀ X X' : Edge L k j → Matrices.ComplexMatrix2, IsDirection X → IsDirection X' →
        AgreeAlongPerturbations 𝕜 U X X' F₁ O₁ f₁ F₂ O₂ f₂
def IsComplexTangent (X : Edge L k j → Matrices.ComplexMatrix2) : Prop :=
  ∀ e : Edge L k j, e.IsPositivelyOriented → X e ∈ Matrices.ComplexMatrix2.traceless
def supBall (L k j : ℕ) (𝒢 : Set Matrices.ComplexMatrix2) (ε : ℝ) :
    Set (Edge L k j → Matrices.ComplexMatrix2) :=
  {V | V ∈ fieldsValuedIn L k j 𝒢 ∧ supDistOne V < ENNReal.ofReal ε}
def pointwiseBall (L k j : ℕ) (𝒢 : Set Matrices.ComplexMatrix2) (ε : ℝ) :
    Set (Edge L k j → Matrices.ComplexMatrix2) :=
  {V | V ∈ fieldsValuedIn L k j 𝒢 ∧
    ∀ e : Edge L k j, Matrices.ComplexMatrix2.operatorNorm (V e - 1) < ε}
def NearIdentitySetsFinitelyOpen (L k j : ℕ) (𝒢 : Set Matrices.ComplexMatrix2) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    IsFinitelyOpen 𝒢 (fieldsValuedIn L k j 𝒢) ∧
    IsFinitelyOpen 𝒢 (supBall L k j 𝒢 ε) ∧
    IsFinitelyOpen 𝒢 (pointwiseBall L k j 𝒢 ε)
def PresentationsAgreeAndBallsOpen : Prop :=
  ∀ L k j : ℕ, Odd L → 13 ≤ L → j ≤ k →
    (PresentationsAgreeAlongPerturbations L k j ℝ PeriodicLattice.compactGaugeGroup
        (fun X => X ∈ edgeFormSpace (meshAt L k j)) ℂ ∧
      PresentationsAgreeAlongPerturbations L k j ℝ PeriodicLattice.compactGaugeGroup
        (fun X => X ∈ edgeFormSpace (meshAt L k j)) Matrices.ComplexMatrix2 ∧
      PresentationsAgreeAlongPerturbations L k j ℂ PeriodicLattice.complexGaugeGroup
        IsComplexTangent ℂ ∧
      PresentationsAgreeAlongPerturbations L k j ℂ PeriodicLattice.complexGaugeGroup
        IsComplexTangent Matrices.ComplexMatrix2) ∧
    NearIdentitySetsFinitelyOpen L k j PeriodicLattice.compactGaugeGroup ∧
    NearIdentitySetsFinitelyOpen L k j PeriodicLattice.complexGaugeGroup
end UniqueValue
end Tower.FullSpace
end YangMills.Construction
end
