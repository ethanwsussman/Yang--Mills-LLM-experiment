import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.Periodized
structure Properties (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ) : Prop where
  summable : ∀ s, 0 < s → ∀ a b, PeriodizationSummableAt I I' T s a b
  depends_quot : ∀ s, 0 < s → ∀ a₁ a₂ b₁ b₂,
    I'.mkQuot s a₁ = I'.mkQuot s a₂ → I.mkQuot s b₁ = I.mkQuot s b₂ →
      periodization I I' T s a₁ b₁ = periodization I I' T s a₂ b₂
  matrix_entries : ∀ s, 0 < s → ∀ a b,
    periodicMatrix I I' T s (I'.mkQuot s a) (I.mkQuot s b) = periodization I I' T s a b
  acts_by_symbol : ∀ s, 0 < s → ∀ k ∈ dualLattice s, ∀ (φ : I.UnitQuot → ℂ)
    (g : I.QuotMod s → ℂ), (∀ b, g (I.mkQuot s b) = blochWave I (toComplexVec k) φ b) →
      ∀ a, applyKernel (periodicMatrix I I' T s) g (I'.mkQuot s a) =
        blochWave I' (toComplexVec k)
          (applyKernel (quotSymbol I I' T (toComplexVec k)) φ) a
def Claim : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    ∀ (T : I'.Carrier → I.Carrier → ℂ) (δ : ℝ),
      IsPeriodicKernel I I' T → IsDecayRate I I' T δ → Properties I I' T
end YangMills.Construction.PeriodicOperators.Periodized
end
