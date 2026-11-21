import YangMills.Construction.Towers.CoercivityOfTheFreeOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.RootedSandwiches
open StripSymbols (openStripInterior linCombKernel)
abbrev addScalar (I : PeriodicData) (X : I.Carrier → I.Carrier → ℂ) (τ : ℝ) :
    I.Carrier → I.Carrier → ℂ :=
  linCombKernel 1 (τ : ℂ) X (idKernel I)
structure RootedPair (I J : PeriodicData) (N Ni K X : I.Carrier → I.Carrier → ℂ)
    (A : J.Carrier → I.Carrier → ℂ) (At : I.Carrier → J.Carrier → ℂ) (r a B c cC : ℝ) : Prop where
  source_periodic : IsPeriodic I
  target_periodic : IsPeriodic J
  K_finiteRange : IsPeriodicKernel I I K ∧ IsFiniteRange I I K
  X_finiteRange : IsPeriodicKernel I I X ∧ IsFiniteRange I I X
  A_finiteRange : IsPeriodicKernel I J A ∧ IsFiniteRange I J A
  At_finiteRange : IsPeriodicKernel J I At ∧ IsFiniteRange J I At
  N_periodic : IsPeriodicKernel I I N
  Ni_periodic : IsPeriodicKernel I I Ni
  N_summable : SymbolSummableOn I I N (openStripInterior (1 / 8))
  Ni_summable : SymbolSummableOn I I Ni (openStripInterior (1 / 8))
  N_holomorphic :
    QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (1 / 8)) (symbolHom I I N)
  Ni_holomorphic :
    QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (1 / 8)) (symbolHom I I Ni)
  inverse_pair : ∀ κ ∈ openStripInterior (1 / 8),
    (symbolHom I I Ni κ).comp (symbolHom I I N κ) = LinearMap.id ∧
      (symbolHom I I N κ).comp (symbolHom I I Ni κ) = LinearMap.id
  N_norm_le : ∀ κ ∈ openStripInterior (1 / 8), quotHomNorm (symbolHom I I N κ) ≤ ENNReal.ofReal r
  A_norm_le : ∀ κ ∈ openStripInterior (1 / 8),
    quotHomNorm (symbolHom I J A κ) ≤ ENNReal.ofReal a ∧
      quotHomNorm (symbolHom J I At κ) ≤ ENNReal.ofReal a
  sandwich_norm_le : ∀ κ ∈ openStripInterior (1 / 8),
    quotHomNorm ((symbolHom I I N κ).comp ((symbolHom I I X κ).comp (symbolHom I I N κ))) ≤
        ENNReal.ofReal B ∧
      quotHomNorm ((symbolHom I I N κ).comp ((symbolHom I I K κ).comp (symbolHom I I N κ))) ≤
        ENNReal.ofReal B ∧
      quotHomNorm ((symbolHom I I N κ).comp (symbolHom I I N κ)) ≤ ENNReal.ofReal B
  N_selfAdjoint : ∀ κ ∈ realDualPoints, IsSelfAdjointQuotHom (symbolHom I I N κ)
  K_nonneg : ∀ κ ∈ realDualPoints, LoewnerLE (scalarQuotHom I 0) (symbolHom I I K κ)
  X_lower_bound : ∀ κ ∈ realDualPoints,
    LoewnerLE ((c : ℂ) • (symbolHom I I K κ + scalarQuotHom I 1)) (symbolHom I I X κ)
  X_upper_bound : ∀ κ ∈ realDualPoints,
    LoewnerLE (symbolHom I I X κ) (symbolHom I I K κ + scalarQuotHom I 1)
  N_sandwich_eq_one : ∀ κ ∈ realDualPoints,
    (symbolHom I I N κ).comp ((symbolHom I I K κ + scalarQuotHom I 1).comp (symbolHom I I N κ)) =
      LinearMap.id
  At_adjoint : ∀ κ ∈ realDualPoints, IsAdjointQuotHom (symbolHom I J A κ) (symbolHom J I At κ)
  A_sandwich_lower : ∀ κ ∈ realDualPoints, LoewnerLE (scalarQuotHom J cC)
    ((symbolHom I J A κ).comp
      (((symbolHom I I N κ).comp (symbolHom I I N κ)).comp (symbolHom J I At κ)))
structure SandwichInvertibility (I J : PeriodicData) (N K X : I.Carrier → I.Carrier → ℂ)
    (A : J.Carrier → I.Carrier → ℂ) (At : I.Carrier → J.Carrier → ℂ) (D : Set (Fin 4 → ℂ))
    (C t τ : ℝ) : Prop where
  interp_invertible : ∀ κ ∈ D,
    IsInvertibleQuotHom ((symbolHom I I N κ).comp
      (((t : ℂ) • symbolHom I I X κ + ((1 - t : ℝ) : ℂ) • symbolHom I I K κ +
        scalarQuotHom I 1).comp (symbolHom I I N κ))) ∧
    quotHomNorm (quotHomInverse ((symbolHom I I N κ).comp
      (((t : ℂ) • symbolHom I I X κ + ((1 - t : ℝ) : ℂ) • symbolHom I I K κ +
        scalarQuotHom I 1).comp (symbolHom I I N κ)))) ≤ ENNReal.ofReal C
  shift_invertible : ∀ κ ∈ D,
    IsInvertibleQuotHom ((symbolHom I I N κ).comp
      ((symbolHom I I X κ + scalarQuotHom I τ).comp (symbolHom I I N κ))) ∧
    quotHomNorm (quotHomInverse ((symbolHom I I N κ).comp
      ((symbolHom I I X κ + scalarQuotHom I τ).comp (symbolHom I I N κ)))) ≤ ENNReal.ofReal C
  symbol_invertible_real : SymbolInvertibleOnReals I (addScalar I X τ)
  shifted_invertible : ∀ κ ∈ D, IsInvertibleQuotHom (symbolHom I I X κ + scalarQuotHom I τ)
  inverse_isPeriodic : IsPeriodicKernel I I (periodicInverse I (addScalar I X τ))
  inverse_summable : SymbolSummableOn I I (periodicInverse I (addScalar I X τ)) D
  inverse_symbol_eq : ∀ κ ∈ D,
    symbolHom I I (periodicInverse I (addScalar I X τ)) κ =
      quotHomInverse (symbolHom I I X κ + scalarQuotHom I τ)
  avg_invertible : ∀ κ ∈ D,
    IsInvertibleQuotHom ((symbolHom I J A κ).comp
      ((quotHomInverse (symbolHom I I X κ + scalarQuotHom I τ)).comp (symbolHom J I At κ))) ∧
    quotHomNorm (quotHomInverse ((symbolHom I J A κ).comp
      ((quotHomInverse (symbolHom I I X κ + scalarQuotHom I τ)).comp (symbolHom J I At κ)))) ≤
      ENNReal.ofReal C
def SandwichBounds : Prop :=
  ∀ r a B c cC : ℝ, 0 ≤ r → 0 ≤ a → 0 ≤ B → 0 < c → c ≤ 1 → 0 < cC →
    ∃ δ ∈ Ioc (0 : ℝ) (1 / 32), ∃ C : ℝ, 1 ≤ C ∧
      ∀ (I J : PeriodicData) (N Ni K X : I.Carrier → I.Carrier → ℂ) (A : J.Carrier → I.Carrier → ℂ)
        (At : I.Carrier → J.Carrier → ℂ), RootedPair I J N Ni K X A At r a B c cC →
          ∀ t ∈ Icc (0 : ℝ) 1, ∀ τ ∈ Icc (0 : ℝ) 1,
            SandwichInvertibility I J N K X A At (imStrip (2 * δ)) C t τ
end YangMills.Construction.PeriodicOperators.RootedSandwiches
end
