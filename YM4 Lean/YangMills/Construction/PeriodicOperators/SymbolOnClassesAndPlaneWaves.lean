import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymbolOnQuotients
structure Properties (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ) : Prop where
  fourierSymbol_congr_mkQuot : ∀ κ, SymbolSummableAt I I' T κ → ∀ i₁' i₂' i₁ i₂,
    I'.mkQuot 1 i₁' = I'.mkQuot 1 i₂' → I.mkQuot 1 i₁ = I.mkQuot 1 i₂ →
      fourierSymbol I I' T κ i₁' i₁ = fourierSymbol I I' T κ i₂' i₂
  quotSymbol_mkQuot : ∀ κ, SymbolSummableAt I I' T κ → ∀ i' i,
    quotSymbol I I' T κ (I'.mkQuot 1 i') (I.mkQuot 1 i) = fourierSymbol I I' T κ i' i
  applyKernel_blochWave : ∀ κ, SymbolSummableAt I I' T κ → ∀ (φ : I.UnitQuot → ℂ) i',
    ApplySummableAt T (blochWave I κ φ) i' ∧
      applyKernel T (blochWave I κ φ) i' =
        blochWave I' κ (applyKernel (quotSymbol I I' T κ) φ) i'
def Claim : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    ∀ T : I'.Carrier → I.Carrier → ℂ, IsPeriodicKernel I I' T → Properties I I' T
end YangMills.Construction.PeriodicOperators.SymbolOnQuotients
end
