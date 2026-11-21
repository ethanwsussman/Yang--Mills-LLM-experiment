import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def MollifierTranslatesDisjoint.Statement : Prop :=
  (∃ j : ℕ → AmbientSpace → ℂ, IsMollifierSeq j) ∧
    ∀ ξ : AmbientSpace, ξ ≠ 0 → ∀ j : ℕ → AmbientSpace → ℂ, IsMollifierSeq j →
      ∀ n : ℕ, 2 / euclidNorm ξ ≤ (n : ℝ) →
        j n ∈ compactC1Real ∧ translateFun ξ (j n) ∈ compactC1Real ∧
          DisjointSupports (j n) (translateFun ξ (j n))
end YangMills.Construction.TwoPoints
end
