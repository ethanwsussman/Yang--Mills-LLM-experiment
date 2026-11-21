import YangMills.Construction.LimitsOfLatticeFamilies.TensorsOfSeparatedTuplesAndCentredFunctionals
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits.TensorRelations
open ModelSpace
variable {s : Conventions.StandingParameters} {Y : ModelSpace}
def RespectsTensorRelations {q : ℕ} {ρ : ℝ≥0∞} (Ψ : TupleFunctional (sepTuplesIn s Y q ρ)) :
    Prop :=
  ∀ (T : Type) [Fintype T] (f : T → sepTuplesIn s Y q ρ) (c : T → ℂ),
    ∑ t, c t • cTensor s Y (f t).1 = 0 → ∑ t, c t * (Ψ (f t) : ℂ) = 0
def IsLinearFormOf {q : ℕ} {ρ : ℝ≥0∞} (Ψ : TupleFunctional (sepTuplesIn s Y q ρ))
    (Λ : sepTensors s Y q ρ →ₗ[ℂ] ℂ) : Prop :=
  ∀ (f : FunTuple s Y q) (hf : f ∈ sepTuplesIn s Y q ρ),
    Λ ⟨cTensor s Y f, cTensor_mem hf⟩ = (Ψ ⟨f, hf⟩ : ℂ)
def Claim : Prop :=
  ∀ (s : Conventions.StandingParameters) (Y : ModelSpace) (q : ℕ) (ρ : ℝ≥0∞), 1 ≤ q → 0 < ρ →
    (∀ Ψ : TupleFunctional (sepTuplesIn s Y q ρ), IsMultilinearSep Ψ →
      RespectsTensorRelations Ψ ∧ ∃! Λ, IsLinearFormOf Ψ Λ) ∧
    ∀ Ψ : FunctionalSeq s Y ρ, IsMultilinearSeq Ψ →
      IsMultilinearSep (centredSum Ψ q) ∧ ∃! Λ, IsCentredLinearForm Ψ q Λ
end YangMills.Construction.LatticeLimits.TensorRelations
end
