import YangMills.Construction.TwoPoints.ThreePropertiesOfAForm
import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
def MollifierLimitSymmetric.Statement : Prop :=
  ∀ (F : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ), IsDisjointForm S →
    IsAdmissibleForm F S →
    ∀ K : AmbientSpace → ℝ,
      (∀ v : AmbientSpace, v ≠ 0 → ∀ ρ : ℕ → AmbientSpace → ℂ, IsMollifierSeq ρ →
        Tendsto (fun n : ℕ => S (ρ n) (translateFun v (ρ n))) atTop (𝓝 (K v))) →
      ∀ v : AmbientSpace, v ≠ 0 → K (-v) = K v ∧ ∀ w ∈ hyperoctahedralPerms, K (w v) = K v
end YangMills.Construction.TwoPoints
end
