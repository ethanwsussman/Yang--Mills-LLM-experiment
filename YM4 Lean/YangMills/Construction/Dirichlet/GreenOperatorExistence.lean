import YangMills.Construction.Dirichlet.LatticeCalculus
import YangMills.Construction.Dirichlet.Parameters
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
noncomputable section
namespace YangMills.Construction.Dirichlet.GreenExistence
variable {d L : ℕ} {S aMinus aPlus : ℝ}
structure GreenOperatorProperties (𝒮 : BlockSetting d L aMinus aPlus S) : Prop where
  shell_sum_le_innerSum : ∀ f : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f →
    min 4 aMinus * ∑ n ∈ Finset.range (𝒮.t + 1),
        (𝒮.scaleAt n ^ 2)⁻¹ * siteNormOn (shell 𝒮.Ω n) f ^ 2 ≤ innerSum f (𝒮.fullOperator f)
  innerSum_fullOperator_pos : ∀ f : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f → f ≠ 0 →
    0 < innerSum f (𝒮.fullOperator f)
  existsUnique_preimage : ∀ f : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f →
    ∃! g : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) g ∧ 𝒮.fullOperator g = f
  innerSum_fullGreen_comm : ∀ f g : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f →
    VanishesOff (𝒮.Ω 0) g → innerSum (𝒮.fullGreen f) g = innerSum f (𝒮.fullGreen g)
  innerSum_fullGreen_pos : ∀ f : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff (𝒮.Ω 0) f → f ≠ 0 →
    0 < innerSum f (𝒮.fullGreen f)
def GreenOperatorExists : Prop :=
  ∀ (d L : ℕ) (aMinus aPlus : ℝ), Parameters d L aMinus aPlus →
    ∀ (S : ℝ) (𝒮 : BlockSetting d L aMinus aPlus S), GreenOperatorProperties 𝒮
end YangMills.Construction.Dirichlet.GreenExistence
