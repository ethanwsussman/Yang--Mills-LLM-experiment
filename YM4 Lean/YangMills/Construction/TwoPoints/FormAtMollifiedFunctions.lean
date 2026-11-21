import YangMills.Construction.TwoPoints.ThreePropertiesOfAForm
import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
def MollifiedFormLimit.Statement : Prop :=
  ∀ F : FixedScale, ∀ S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ, IsDisjointForm S →
    IsAdmissibleForm F S →
    ∀ f ∈ compactC1Complex, ∀ h ∈ compactC1Complex, DisjointSupports f h →
      ∀ ρ : ℕ → AmbientSpace → ℂ, IsMollifierSeq ρ →
        (∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          DisjointSupports (convolve (ρ n) f) (convolve (ρ n) h)) ∧
        Tendsto (fun n : ℕ => complexifyForm S (convolve (ρ n) f) (convolve (ρ n) h)) atTop
          (𝓝 (complexifyForm S f h))
end YangMills.Construction.TwoPoints
end
