import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
structure AreKernelsWithRate (I I' I'' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ)
    (S : I.Carrier → I''.Carrier → ℂ) (δ : ℝ) : Prop where
  mid_periodic : IsPeriodic I
  target_periodic : IsPeriodic I'
  source_periodic : IsPeriodic I''
  left_kernel : IsPeriodicKernel I I' T
  left_rate : IsDecayRate I I' T δ
  right_kernel : IsPeriodicKernel I'' I S
  right_rate : IsDecayRate I'' I S δ
structure PairsWithId (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ) : Prop where
  exists_rate : ∃ δ, IsDecayRate I I' T δ
  withRate : ∀ δ, IsDecayRate I I' T δ → AreKernelsWithRate I I' I T (idKernel I) δ
  common_bound : ∀ δ C, IsDecayRate I I' T δ → 0 < C → ExpDecay I I' T C δ →
    ExpDecay I I' T (max C 1) δ ∧ ExpDecay I I (idKernel I) (max C 1) δ
def IdKernelFacts.Claim : Prop :=
  ∀ I : PeriodicData, IsPeriodic I →
    IsPeriodicKernel I I (idKernel I) ∧
    (∀ δ : ℝ, 0 < δ → IsDecayRate I I (idKernel I) δ) ∧
    SymbolSummableOn I I (idKernel I) Set.univ ∧
    (∀ (κ : Fin 4 → ℂ) (ι' ι : I.Carrier), fourierSymbol I I (idKernel I) κ ι' ι =
      quotOne I (I.mkQuot 1 ι') (I.mkQuot 1 ι)) ∧
    (∀ κ : Fin 4 → ℂ, quotSymbol I I (idKernel I) κ = quotOne I) ∧
    (∀ I' : PeriodicData, IsPeriodic I' → ∀ T : I'.Carrier → I.Carrier → ℂ,
      IsPeriodicKernel I I' T → PairsWithId I I' T) ∧
    PairsWithId I I (idKernel I) ∧
    ∀ δ : ℝ, 0 < δ →
      AreKernelsWithRate I I I (idKernel I) (idKernel I) δ
end YangMills.Construction.PeriodicOperators
end
