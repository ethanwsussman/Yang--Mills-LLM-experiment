import YangMills.Construction.Dirichlet.LatticeCalculus
import YangMills.Construction.Dirichlet.Parameters
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.Dirichlet.GreenLinearity
variable {d L : ℕ} {S aMinus aPlus : ℝ}
structure BlockGreenFacts (𝒮 : BlockSetting d L aMinus aPlus S) (W : Set (PeriodicTorus d S))
    (E : Set (LatticeBond d S 𝒮.ξ)) : Prop where
  vanishesOff : ∀ f : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff W (𝒮.blockGreen W E f)
  blockOperator_blockGreen : ∀ f : LatticeSite d S 𝒮.ξ → ℝ,
    𝒮.blockOperator W E (𝒮.blockGreen W E f) = restrictTo W f
  eq_of_blockOperator : ∀ f g : LatticeSite d S 𝒮.ξ → ℝ, VanishesOff W g →
    𝒮.blockOperator W E g = restrictTo W f → 𝒮.blockGreen W E f = g
  map_add : ∀ f g : LatticeSite d S 𝒮.ξ → ℝ,
    𝒮.blockGreen W E (f + g) = 𝒮.blockGreen W E f + 𝒮.blockGreen W E g
  map_smul : ∀ (r : ℝ) (f : LatticeSite d S 𝒮.ξ → ℝ),
    𝒮.blockGreen W E (r • f) = r • 𝒮.blockGreen W E f
def BlockGreenLinear : Prop :=
  ∀ (d L : ℕ) (aMinus aPlus : ℝ), Parameters d L aMinus aPlus →
    ∀ (S : ℝ) (𝒮 : BlockSetting d L aMinus aPlus S) (W : Set (PeriodicTorus d S))
      (E : Set (LatticeBond d S 𝒮.ξ)), 𝒮.IsCellUnion W → IsBoundaryRule (𝒮.Ω 0) W E →
        BlockGreenFacts 𝒮 W E
end YangMills.Construction.Dirichlet.GreenLinearity
