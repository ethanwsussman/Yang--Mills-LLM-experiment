import YangMills.Construction.Towers.ParametrixOfTheExpansionInTheFlux
import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice (AmbientSpace)
noncomputable section
namespace YangMills.Construction.Tower.MagneticWeyl
open FluxExpansion in
def ApproxInverseRemainder : Prop :=
  ∀ (N' : ℕ) [NeZero N'] (z : ℝ), 0 < z → ∀ σ₁ σ₂ : AmbientSpace → Matrix (Fin N') (Fin N') ℂ,
    IsWeylSymbol σ₁ → IsWeylSymbol σ₂ → ∃ K : ℝ, 0 ≤ K ∧ ∀ s φ : ℝ, z ≤ s → |φ| ≤ 1 →
      ∀ σr : AmbientSpace → Matrix (Fin N') (Fin N') ℂ, IsWeylSymbol σr →
        IsWeylSymbol (approxInverse s φ σ₁ σ₂) ∧
        ∃ e : AmbientSpace → Matrix (Fin N') (Fin N') ℂ, IsWeylSymbol e ∧
          moyalProduct φ (approxInverse s φ σ₁ σ₂)
              (fun q => (baseSymbolMatrix N' q + (φ : ℂ) • σ₁ q + (φ : ℂ) ^ 2 • σ₂ q + σr q) +
                (s : ℂ) • (1 : Matrix (Fin N') (Fin N') ℂ)) =
            (fun q => 1 + e q) ∧
          weightedCoeffNorm 0 e ≤ K * (|φ| ^ 3 + weightedCoeffNorm 3 σr) / s
end YangMills.Construction.Tower.MagneticWeyl
end
