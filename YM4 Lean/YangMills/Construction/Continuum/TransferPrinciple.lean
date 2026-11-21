import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces
variable {n : ℕ}
def IsBoundedByWeighted (c : ℝ) (k : ℕ) (T : flatSchwartzSet n → ℂ) : Prop :=
  ∀ φ : flatSchwartzSet n, ENNReal.ofReal ‖T φ‖ ≤ ENNReal.ofReal c * weightedSeminorm k φ.1
def EqOnSmoothTensors (T₁ T₂ : flatSchwartzSet n → ℂ) : Prop :=
  ∀ X : SepTupleOfCard n, HasSmoothComponents Set.univ X.1 →
    ∀ h : tensorProdComplex X.1 ∈ flatSchwartzSet n, T₁ ⟨_, h⟩ = T₂ ⟨_, h⟩
def DensityTransfer.Statement : Prop :=
  (∀ n k : ℕ, 0 < n → 0 < k → ∀ T₁ T₂ : flatSchwartzSet n → ℂ,
    IsCLinearOnFlat T₁ → IsCLinearOnFlat T₂ →
    (∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧
      IsBoundedByWeighted c₁ k T₁ ∧ IsBoundedByWeighted c₂ k T₂) →
    EqOnSmoothTensors T₁ T₂ → T₁ = T₂) ∧
  (∀ n k k' : ℕ, 0 < n → 0 < k → 0 < k' → ∀ (T₁ T₂ : flatSchwartzSet n → ℂ) (c₁ c₂ : ℝ),
    IsCLinearOnFlat T₁ → IsCLinearOnFlat T₂ → 0 ≤ c₁ → 0 ≤ c₂ →
    IsBoundedByWeighted c₁ k T₁ → IsBoundedByWeighted c₂ k' T₂ →
    IsBoundedByWeighted c₁ (max k k') T₁ ∧ IsBoundedByWeighted c₂ (max k k') T₂)
end YangMills.Construction.TestSpaces
