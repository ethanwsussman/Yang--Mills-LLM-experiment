import YangMills.Construction.Towers.ParametrixOfTheExpansionInTheFlux
import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MagneticWeyl
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open FluxExpansion in
def FluxExpansionBrackets : Prop :=
  ∀ (N' : ℕ) [NeZero N'] (s : ℝ), 0 < s →
    ∀ σ₁ : AmbientSpace → Matrix (Fin N') (Fin N') ℂ, IsWeylSymbol σ₁ →
    ∀ q : AmbientSpace,
      poissonBracket (termZero N' s) (baseSymbolMatrix N') q = 0 ∧
      poissonBracket (termOne s σ₁) (baseSymbolMatrix N') q + poissonBracket (termZero N' s) σ₁ q = 0 ∧
      secondPoissonBracket (termZero N' s) (baseSymbolMatrix N') q =
        (shiftedInverseSecondDeriv s 0 q * baseSymbolSecondDeriv 1 q +
            shiftedInverseSecondDeriv s 1 q * baseSymbolSecondDeriv 0 q) •
          (1 : Matrix (Fin N') (Fin N') ℂ)
end YangMills.Construction.Tower.MagneticWeyl
end
