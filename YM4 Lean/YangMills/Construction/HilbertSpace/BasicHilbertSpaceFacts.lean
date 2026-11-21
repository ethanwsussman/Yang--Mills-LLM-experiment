import YangMills.Construction.HilbertSpace.UnitaryConjugation
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.HilbertSpace.BasicFacts
variable (𝒦 𝒦' : Type) [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦]
  [NormedAddCommGroup 𝒦'] [InnerProductSpace ℂ 𝒦']
def ExtendsFromDense : Prop :=
  ∀ (𝒟 : Submodule ℂ 𝒦) (C : ℝ) (B₀ : 𝒟 →ₗ[ℂ] 𝒦'), Dense (𝒟 : Set 𝒦) → 0 ≤ C →
    (∀ ψ : 𝒟, ‖B₀ ψ‖ ≤ C * ‖(ψ : 𝒦)‖) →
    ∃ B : 𝒦 →L[ℂ] 𝒦', (∀ ψ : 𝒟, B ψ = B₀ ψ) ∧ ‖B‖ ≤ C ∧
      (∀ B' : 𝒦 →L[ℂ] 𝒦', (∀ ψ : 𝒟, B' ψ = B₀ ψ) → B' = B) ∧
      ((∀ ψ : 𝒟, ‖B₀ ψ‖ = ‖(ψ : 𝒦)‖) → Dense (Set.range B₀) →
        OperatorTransport.IsUnitaryMap (B : 𝒦 →ₗ[ℂ] 𝒦'))
def EqOnDenseEq : Prop :=
  ∀ (S : Set 𝒦) (B B' : 𝒦 →L[ℂ] 𝒦'), Dense S → (∀ ψ ∈ S, B ψ = B' ψ) → B = B'
def FormPolarization : Prop :=
  ∀ b : 𝒦 → 𝒦 → ℂ, HilbertSpaceBasics.IsSesquilinear b → ∀ φ ψ : 𝒦,
    b φ ψ = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
      Complex.I ^ k * b (ψ + Complex.I ^ k • φ) (ψ + Complex.I ^ k • φ)
def EqZeroOfInnerSelfApply : Prop :=
  ∀ B : 𝒦 →L[ℂ] 𝒦, (∀ ψ, ⟪ψ, B ψ⟫_ℂ = 0) → B = 0
def NormPreservingPreservesInner : Prop :=
  ∀ B : 𝒦 →ₗ[ℂ] 𝒦', (∀ ψ, ‖B ψ‖ = ‖ψ‖) → ∀ φ ψ, ⟪B φ, B ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ
def AdjointUnique : Prop :=
  ∀ B B' B'' : 𝒦 →L[ℂ] 𝒦, OperatorTransport.IsBoundedAdjoint B' B →
    OperatorTransport.IsBoundedAdjoint B'' B → B' = B''
def RieszRepresentation : Prop :=
  ∀ (l : 𝒦 →ₗ[ℂ] ℂ) (C' : ℝ), 0 ≤ C' → (∀ φ, ‖l φ‖ ≤ C' * ‖φ‖) →
    ∃ χ : 𝒦, ∀ φ, l φ = ⟪χ, φ⟫_ℂ
def BoundedFormRepresentation : Prop :=
  ∀ (b : 𝒦 → 𝒦 → ℂ) (C : ℝ), HilbertSpaceBasics.IsSesquilinear b → 0 ≤ C →
    (∀ φ ψ, ‖b φ ψ‖ ≤ C * ‖φ‖ * ‖ψ‖) →
    ∃ B : 𝒦 →L[ℂ] 𝒦, (∀ φ ψ, b φ ψ = ⟪φ, B ψ⟫_ℂ) ∧ ‖B‖ ≤ C ∧
      (∀ B' : 𝒦 →L[ℂ] 𝒦, (∀ φ ψ, b φ ψ = ⟪φ, B' ψ⟫_ℂ) → B' = B) ∧
      ((∀ φ ψ, b ψ φ = conj (b φ ψ)) → OperatorTransport.IsSelfAdjointCLM B)
def CLMBanachAlgebra : Prop :=
  CompleteSpace (𝒦 →L[ℂ] 𝒦) ∧ ∀ B B' : 𝒦 →L[ℂ] 𝒦, ‖B * B'‖ ≤ ‖B‖ * ‖B'‖
def UnitaryBasicProps : Prop :=
  ∀ (V : 𝒦 →ₗ[ℂ] 𝒦') (hV : OperatorTransport.IsUnitaryMap V),
    (∃ B : 𝒦 →L[ℂ] 𝒦', (B : 𝒦 →ₗ[ℂ] 𝒦') = V) ∧
    (∃ B : 𝒦' →L[ℂ] 𝒦, (B : 𝒦' →ₗ[ℂ] 𝒦) = hV.inv) ∧
    OperatorTransport.IsUnitaryMap hV.inv ∧
    ∀ (φ' : 𝒦') (ψ : 𝒦), ⟪φ', V ψ⟫_ℂ = ⟪hV.inv φ', ψ⟫_ℂ
def UnitaryInvIsAdjoint : Prop :=
  ∀ (V : 𝒦 →ₗ[ℂ] 𝒦) (hV : OperatorTransport.IsUnitaryMap V),
    ∃ B B' : 𝒦 →L[ℂ] 𝒦, (B : 𝒦 →ₗ[ℂ] 𝒦) = V ∧ (B' : 𝒦 →ₗ[ℂ] 𝒦) = hV.inv ∧
      OperatorTransport.IsBoundedAdjoint B' B
def SelfAdjointNotionsAgree [CompleteSpace 𝒦] : Prop :=
  ∀ B : 𝒦 →L[ℂ] 𝒦, OperatorTransport.IsSelfAdjointCLM B ↔
    OperatorTransport.IsSelfAdjointUnbounded (HilbertSpaceBasics.ofBounded B)
def BasicHilbertSpaceFacts : Prop :=
  ∀ (𝒦 𝒦' : Type) [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
    [NormedAddCommGroup 𝒦'] [InnerProductSpace ℂ 𝒦'] [CompleteSpace 𝒦'],
    ExtendsFromDense 𝒦 𝒦' ∧ EqOnDenseEq 𝒦 𝒦' ∧
    FormPolarization 𝒦 ∧ EqZeroOfInnerSelfApply 𝒦 ∧
    NormPreservingPreservesInner 𝒦 𝒦' ∧ AdjointUnique 𝒦 ∧
    RieszRepresentation 𝒦 ∧ BoundedFormRepresentation 𝒦 ∧
    CLMBanachAlgebra 𝒦 ∧ UnitaryBasicProps 𝒦 𝒦' ∧
    UnitaryInvIsAdjoint 𝒦 ∧ SelfAdjointNotionsAgree 𝒦
end YangMills.Construction.HilbertSpace.BasicFacts
