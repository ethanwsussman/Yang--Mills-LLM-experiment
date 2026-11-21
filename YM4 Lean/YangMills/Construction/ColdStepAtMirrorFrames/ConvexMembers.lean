import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def IsConvexClassMember (ρ m κ : ℝ) (d : ι → ι → ℝ) (P : BondField ι → ℝ) : Prop :=
  ∃ (Φ : BondField ι → ℝ) (K : ι → ι → ℝ), (∀ η, (∀ b, ‖η b‖ < ρ) → Φ η = P η) ∧
    IsUniformlyConvexDecaying ρ m κ d Φ K ∧
    ∀ (b : ι) (e : BondVector), |bondPartialDeriv Φ b 0 e| ≤ Real.sqrt m * ‖e‖
def restrictToSupport (Λ : Finset ι) (η : BondField ι) : BondField ι :=
  fun b => if b ∈ Λ then η b else 0
end ColdStepAtMirrorFrames
end YangMills.Construction
end
