import YangMills.Construction.TorusOrFourSpace.DiagonalExtractionDefs
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndSetsAtPositiveDistance
import YangMills.Construction.TorusOrFourSpace.TuplesInABallAndLipschitzClasses
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SeparatedTupleFacts
open Kind
variable (D : Params) (E : Kind)
def HasFiniteBallRadius {n : ℕ} (f : FnTuple D E n) : Prop :=
  ∃ ρ : ℝ≥0∞, 0 < ρ ∧ ρ < ∞ ∧ f ∈ sepC1TuplesInBall D E n ρ
def SupportGapPosAndTopIff {n : ℕ}
    (f : FnTuple D E n) : Prop :=
  supportGap D E f ∈ Set.Ioc (0 : ℝ≥0∞) ∞ ∧
    (supportGap D E f = ∞ ↔ {i | (supportQ D E (f i)).Nonempty}.Subsingleton)
def SupportGapTopImpliesZero {n : ℕ} (f : FnTuple D E n) : Prop :=
  supportGap D E f = ∞ →
    (∃ i, f i = 0) ∧
      ∀ (ρ : ℝ≥0∞), 0 < ρ → ∀ hf : f ∈ sepC1TuplesInBall D E n ρ,
        ∀ Ψ : sepC1TuplesInBall D E n ρ → ℝ,
          IsMultilinearOn D E (sepC1TuplesInBall D E n ρ) Ψ → Ψ ⟨f, hf⟩ = 0
def SeparatedTupleBasics : Prop :=
  ∀ (D : Params) (E : Kind) (n : ℕ), 2 ≤ n →
    ∀ f : FnTuple D E n, DiagonalLimits.IsSepTuple D E f →
      HasFiniteBallRadius D E f ∧
        SupportGapPosAndTopIff D E f ∧
          SupportGapTopImpliesZero D E f
end YangMills.Construction.PeriodicSpace.SeparatedTupleFacts
