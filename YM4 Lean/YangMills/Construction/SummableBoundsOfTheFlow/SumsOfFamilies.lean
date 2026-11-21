import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace FamilyNorms
open TorusLumps
def normBoundedFamilyClosureStatement : Prop :=
  ∀ ℓ : StepParameters,
    (∀ (ε ε₃ ε' ε₃' : ℝ) (h : LocalDensity), ε ≤ ε' → ε₃ ≤ ε₃' → IsNormBoundedFamily ℓ ε ε₃ h →
      IsNormBoundedFamily ℓ ε' ε₃' h) ∧
    (∀ (ε ε₃ ε' ε₃' : ℝ) (h h' : LocalDensity), IsNormBoundedFamily ℓ ε ε₃ h →
      IsNormBoundedFamily ℓ ε' ε₃' h' → IsNormBoundedFamily ℓ (ε + ε') (ε₃ + ε₃') (h + h')) ∧
    (∀ (c ε ε₃ : ℝ) (h : LocalDensity), IsNormBoundedFamily ℓ ε ε₃ h →
      IsNormBoundedFamily ℓ (|c| * ε) (|c| * ε₃) (c • h)) ∧
    ∀ ε ε₃ : ℝ, 0 ≤ ε → 0 ≤ ε₃ → IsNormBoundedFamily ℓ ε ε₃ 0
end FamilyNorms
end YangMills.Construction
end
