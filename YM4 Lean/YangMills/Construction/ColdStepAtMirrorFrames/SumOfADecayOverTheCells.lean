import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def ExpDecaySumBounded : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ S : ℝ, 0 < S ∧ ∀ (F : BlockFrame) (j : ℕ) (y : F.Site j) (A : Finset (F.Site j)),
    ∑ z ∈ A, Real.exp (-(γ * siteSupDist y z)) ≤ S
end ColdStepAtMirrorFrames
end YangMills.Construction
end
