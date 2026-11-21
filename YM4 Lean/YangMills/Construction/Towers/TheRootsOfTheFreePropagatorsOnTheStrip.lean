import YangMills.Construction.Towers.CoercivityOfTheFreeOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResolventRootsOnStrip
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.StripSymbols (openStripInterior)
open YangMills.Construction.Tower.FreeResolvents
structure SqrtFacts (I : PeriodicData) (M : ℝ → (Fin 4 → ℂ) → QuotHom I I)
    (N Ni G K : I.Carrier → I.Carrier → ℂ) : Prop where
  sqrt_periodic : IsPeriodicKernel I I N
  invSqrt_periodic : IsPeriodicKernel I I Ni
  sqrt_summable : SymbolSummableOn I I N (openStripInterior (1 / 8))
  invSqrt_summable : SymbolSummableOn I I Ni (openStripInterior (1 / 8))
  sqrt_symbol : ∀ κ ∈ openStripInterior (1 / 8), symbolHom I I N κ = M (-(1 / 2)) κ
  invSqrt_symbol : ∀ κ ∈ openStripInterior (1 / 8), symbolHom I I Ni κ = M (1 / 2) κ
  sqrt_holomorphicOn : QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (1 / 8)) (symbolHom I I N)
  invSqrt_holomorphicOn :
    QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (1 / 8)) (symbolHom I I Ni)
  invSqrt_inverse : ∀ κ ∈ openStripInterior (1 / 8),
    (symbolHom I I Ni κ).comp (symbolHom I I N κ) = LinearMap.id ∧
      (symbolHom I I N κ).comp (symbolHom I I Ni κ) = LinearMap.id
  resolvent_eq_sq : ∀ κ ∈ openStripInterior (1 / 8), SymbolSummableAt I I G κ ∧
    symbolHom I I G κ = (symbolHom I I N κ).comp (symbolHom I I N κ)
  sqrt_conj_add_one : ∀ κ ∈ openStripInterior (1 / 8),
    (symbolHom I I N κ).comp ((symbolHom I I K κ + scalarQuotHom I 1).comp (symbolHom I I N κ)) =
      LinearMap.id
  sqrt_selfAdjoint : ∀ κ ∈ realDualPoints, IsSelfAdjointQuotHom (symbolHom I I N κ)
def ResolventRootsHold : Prop :=
  ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    SqrtFacts (colourEdges L k 0) (edgePowMatrix L k) (edgeResolventSqrt L k)
      (edgeResolventInvSqrt L k) (edgeResolvent L k) (trivialRescaledOperators L k).K ∧
    SqrtFacts (colourVertices L k 0) (vertexPowMatrix L k) (vertexResolventSqrt L k)
      (vertexResolventInvSqrt L k) (vertexResolvent L k) (trivialRescaledOperators L k).Delta
end YangMills.Construction.Tower.ResolventRootsOnStrip
end
