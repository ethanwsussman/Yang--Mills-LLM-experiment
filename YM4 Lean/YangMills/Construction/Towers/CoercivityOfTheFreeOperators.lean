import YangMills.Construction.Towers.TheFreePropagatorsAsOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
section QuotientMaps
variable {I I' : PeriodicData}
def IsAdjointQuotHom (M : QuotHom I I') (A : QuotHom I' I) : Prop :=
  ∀ (f : I.UnitQuot → ℂ) (g : I'.UnitQuot → ℂ),
    wInner (I'.quotWeight 1) g (M f) = wInner (I.quotWeight 1) (A g) f
def quotHomAdjoint (M : QuotHom I I') : QuotHom I' I :=
  Classical.epsilon (IsAdjointQuotHom M)
def IsSelfAdjointQuotHom (M : QuotHom I I) : Prop :=
  ∀ f g : I.UnitQuot → ℂ,
    wInner (I.quotWeight 1) (M f) g = wInner (I.quotWeight 1) f (M g)
structure LoewnerLE (M M' : QuotHom I I) : Prop where
  isSelfAdjoint_left : IsSelfAdjointQuotHom M
  isSelfAdjoint_right : IsSelfAdjointQuotHom M'
  im_eq_zero : ∀ f : I.UnitQuot → ℂ, (wInner (I.quotWeight 1) f ((M' - M) f)).im = 0
  re_nonneg : ∀ f : I.UnitQuot → ℂ, 0 ≤ (wInner (I.quotWeight 1) f ((M' - M) f)).re
def scalarQuotHom (I : PeriodicData) (c : ℝ) : QuotHom I I := (c : ℂ) • LinearMap.id
end QuotientMaps
structure SymbolIsMatrixAt (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ) (κ : Fin 4 → ℂ) :
    Prop where
  summable : SymbolSummableAt I I' T κ
  factorsThroughQuot : FactorsThroughQuot (P := I) (Q := I') (fourierSymbol I I' T κ)
  carrierEntry_eq : ∀ ι' ι, carrierEntry (symbolHom I I' T κ) ι' ι = fourierSymbol I I' T κ ι' ι
end PeriodicOperators
namespace Tower
namespace FreeCoercivity
open PeriodicOperators
open FreeResolvents
abbrev vertexIndex (L k : ℕ) : PeriodicData := colourVertices L k 0
abbrev edgeIndex (L k : ℕ) : PeriodicData := colourEdges L k 0
abbrev topVertexIndex (L k : ℕ) : PeriodicData := colourVertices L k k
abbrev topEdgeIndex (L k : ℕ) : PeriodicData := colourEdges L k k
def IsFiniteRangeEntire (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ) : Prop :=
  IsPeriodicKernel I I' T ∧ IsFiniteRange I I' T ∧ SymbolSummableOn I I' T univ
structure FiniteRangeOperators (L k : ℕ) : Prop where
  K : IsFiniteRangeEntire (edgeIndex L k) (edgeIndex L k) (trivialRescaledOperators L k).K
  Delta : IsFiniteRangeEntire (vertexIndex L k) (vertexIndex L k)
    (trivialRescaledOperators L k).Delta
  Xi : IsFiniteRangeEntire (edgeIndex L k) (edgeIndex L k) (trivialRescaledOperators L k).Xi
  Y : IsFiniteRangeEntire (vertexIndex L k) (vertexIndex L k) (trivialRescaledOperators L k).Y
  Q : IsFiniteRangeEntire (edgeIndex L k) (topEdgeIndex L k) (trivialRescaledOperators L k).Q
  R : IsFiniteRangeEntire (vertexIndex L k) (topVertexIndex L k) (trivialRescaledOperators L k).R
  Qt : IsFiniteRangeEntire (topEdgeIndex L k) (edgeIndex L k) (trivialRescaledOperators L k).Qt
  Rt : IsFiniteRangeEntire (topVertexIndex L k) (vertexIndex L k)
    (trivialRescaledOperators L k).Rt
structure SymbolMatricesAt (L k : ℕ) (κ : Fin 4 → ℂ) : Prop where
  K : SymbolIsMatrixAt (edgeIndex L k) (edgeIndex L k) (trivialRescaledOperators L k).K κ
  Delta : SymbolIsMatrixAt (vertexIndex L k) (vertexIndex L k)
    (trivialRescaledOperators L k).Delta κ
  Xi : SymbolIsMatrixAt (edgeIndex L k) (edgeIndex L k) (trivialRescaledOperators L k).Xi κ
  Y : SymbolIsMatrixAt (vertexIndex L k) (vertexIndex L k) (trivialRescaledOperators L k).Y κ
  Q : SymbolIsMatrixAt (edgeIndex L k) (topEdgeIndex L k) (trivialRescaledOperators L k).Q κ
  R : SymbolIsMatrixAt (vertexIndex L k) (topVertexIndex L k) (trivialRescaledOperators L k).R κ
  Qt : SymbolIsMatrixAt (topEdgeIndex L k) (edgeIndex L k) (trivialRescaledOperators L k).Qt κ
  Rt : SymbolIsMatrixAt (topVertexIndex L k) (vertexIndex L k)
    (trivialRescaledOperators L k).Rt κ
  G : SymbolIsMatrixAt (edgeIndex L k) (edgeIndex L k) (edgeResolvent L k) κ
  g : SymbolIsMatrixAt (vertexIndex L k) (vertexIndex L k) (vertexResolvent L k) κ
def edgeSymbolAddOne (L k : ℕ) (κ : Fin 4 → ℂ) : QuotHom (edgeIndex L k) (edgeIndex L k) :=
  symbolHom (edgeIndex L k) (edgeIndex L k) (trivialRescaledOperators L k).K κ +
    scalarQuotHom (edgeIndex L k) 1
def vertexSymbolAddOne (L k : ℕ) (κ : Fin 4 → ℂ) : QuotHom (vertexIndex L k) (vertexIndex L k) :=
  symbolHom (vertexIndex L k) (vertexIndex L k) (trivialRescaledOperators L k).Delta κ +
    scalarQuotHom (vertexIndex L k) 1
def edgeResolventConjugate (L k : ℕ) (κ : Fin 4 → ℂ) :
    QuotHom (topEdgeIndex L k) (topEdgeIndex L k) :=
  (symbolHom (edgeIndex L k) (topEdgeIndex L k) (trivialRescaledOperators L k).Q κ).comp
    ((symbolHom (edgeIndex L k) (edgeIndex L k) (edgeResolvent L k) κ).comp
      (quotHomAdjoint (symbolHom (edgeIndex L k) (topEdgeIndex L k)
        (trivialRescaledOperators L k).Q κ)))
def vertexResolventConjugate (L k : ℕ) (κ : Fin 4 → ℂ) :
    QuotHom (topVertexIndex L k) (topVertexIndex L k) :=
  (symbolHom (vertexIndex L k) (topVertexIndex L k) (trivialRescaledOperators L k).R κ).comp
    ((symbolHom (vertexIndex L k) (vertexIndex L k) (vertexResolvent L k) κ).comp
      (quotHomAdjoint (symbolHom (vertexIndex L k) (topVertexIndex L k)
        (trivialRescaledOperators L k).R κ)))
structure CoercivityAt (L k : ℕ) (cXi cY cC : ℝ) (κ : Fin 4 → ℂ) : Prop where
  Xi_lower : LoewnerLE ((cXi : ℂ) • edgeSymbolAddOne L k κ)
    (symbolHom (edgeIndex L k) (edgeIndex L k) (trivialRescaledOperators L k).Xi κ)
  Xi_upper : LoewnerLE (symbolHom (edgeIndex L k) (edgeIndex L k) (trivialRescaledOperators L k).Xi κ)
    (edgeSymbolAddOne L k κ)
  Y_lower : LoewnerLE ((cY : ℂ) • vertexSymbolAddOne L k κ)
    (symbolHom (vertexIndex L k) (vertexIndex L k) (trivialRescaledOperators L k).Y κ)
  Y_upper : LoewnerLE
    (symbolHom (vertexIndex L k) (vertexIndex L k) (trivialRescaledOperators L k).Y κ)
    (vertexSymbolAddOne L k κ)
  edge_lower : LoewnerLE (scalarQuotHom (topEdgeIndex L k) cC) (edgeResolventConjugate L k κ)
  vertex_lower : LoewnerLE (scalarQuotHom (topVertexIndex L k) cC) (vertexResolventConjugate L k κ)
def FreeOperatorsCoercive : Prop :=
  ∃ cXi ∈ Ioc (0 : ℝ) 1, ∃ cY ∈ Ioc (0 : ℝ) 1, ∃ cC ∈ Ioc (0 : ℝ) 1,
    ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
      FiniteRangeOperators L k ∧
      IsPeriodicKernel (edgeIndex L k) (edgeIndex L k) (edgeResolvent L k) ∧
      IsPeriodicKernel (vertexIndex L k) (vertexIndex L k) (vertexResolvent L k) ∧
      ∀ κ ∈ realDualPoints, SymbolMatricesAt L k κ ∧ CoercivityAt L k cXi cY cC κ
end FreeCoercivity
end Tower
end YangMills.Construction
end
