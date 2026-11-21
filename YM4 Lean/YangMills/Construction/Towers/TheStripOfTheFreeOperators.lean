import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperators
import YangMills.Construction.Towers.TheFreePropagatorsAsOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FreeStrip
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FreeResolvents
abbrev vertices (L k : ℕ) : PeriodicData := colourVertices L k 0
abbrev edges (L k : ℕ) : PeriodicData := colourEdges L k 0
abbrev faces (L k : ℕ) : PeriodicData := colourFaces L k 0
abbrev topVertices (L k : ℕ) : PeriodicData := colourVertices L k k
abbrev topEdges (L k : ℕ) : PeriodicData := colourEdges L k k
def vertexDiff (L k : ℕ) : (edges L k).Carrier → (vertices L k).Carrier → ℂ :=
  FullSpace.scaledVertexCoboundaryKernel L k 0
def edgeDiff (L k : ℕ) : (faces L k).Carrier → (edges L k).Carrier → ℂ :=
  FullSpace.scaledEdgeCoboundaryKernel L k 0
def vertexDiffT (L k : ℕ) : (vertices L k).Carrier → (edges L k).Carrier → ℂ :=
  kernelTranspose (vertices L k) (edges L k) (vertexDiff L k)
def edgeDiffT (L k : ℕ) : (edges L k).Carrier → (faces L k).Carrier → ℂ :=
  kernelTranspose (edges L k) (faces L k) (edgeDiff L k)
def edgeAvg (L k : ℕ) : (topEdges L k).Carrier → (edges L k).Carrier → ℂ :=
  (trivialRescaledOperators L k).Q
def vertexAvg (L k : ℕ) : (topVertices L k).Carrier → (vertices L k).Carrier → ℂ :=
  (trivialRescaledOperators L k).R
def edgeAvgT (L k : ℕ) : (edges L k).Carrier → (topEdges L k).Carrier → ℂ :=
  (trivialRescaledOperators L k).Qt
def vertexAvgT (L k : ℕ) : (vertices L k).Carrier → (topVertices L k).Carrier → ℂ :=
  (trivialRescaledOperators L k).Rt
def edgeOpK (L k : ℕ) : (edges L k).Carrier → (edges L k).Carrier → ℂ :=
  (trivialRescaledOperators L k).K
def vertexOpDelta (L k : ℕ) : (vertices L k).Carrier → (vertices L k).Carrier → ℂ :=
  (trivialRescaledOperators L k).Delta
def edgeOpXi (L k : ℕ) : (edges L k).Carrier → (edges L k).Carrier → ℂ :=
  (trivialRescaledOperators L k).Xi
def vertexOpY (L k : ℕ) : (vertices L k).Carrier → (vertices L k).Carrier → ℂ :=
  (trivialRescaledOperators L k).Y
def addScalar (I : PeriodicData) (τ : ℝ) (A : I.Carrier → I.Carrier → ℂ) :
    I.Carrier → I.Carrier → ℂ :=
  fun ι' ι => A ι' ι + (τ : ℂ) * idKernel I ι' ι
def interpPlusOne (I : PeriodicData) (t : ℝ) (A B : I.Carrier → I.Carrier → ℂ) :
    I.Carrier → I.Carrier → ℂ :=
  fun ι' ι => (t : ℂ) * A ι' ι + ((1 - t : ℝ) : ℂ) * B ι' ι + idKernel I ι' ι
def symbolAddScalar (I : PeriodicData) (τ : ℝ) (A : I.Carrier → I.Carrier → ℂ) (κ : Fin 4 → ℂ) :
    QuotHom I I :=
  symbolHom I I A κ + (τ : ℂ) • LinearMap.id
def SymbolBoundedOn (I I' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ) (D : Set (Fin 4 → ℂ))
    (C : ℝ) : Prop :=
  SymbolSummableOn I I' T D ∧ ∀ κ ∈ D, quotHomNorm (symbolHom I I' T κ) ≤ ENNReal.ofReal C
def CompSymbolBoundedOn (I I' I'' : PeriodicData) (T : I'.Carrier → I.Carrier → ℂ)
    (S : I.Carrier → I''.Carrier → ℂ) (D : Set (Fin 4 → ℂ)) (C : ℝ) : Prop :=
  (∀ ι' ι'', CompSummableAt T S ι' ι'') ∧ SymbolBoundedOn I'' I' (compKernel T S) D C
def SymbolInvertibleOn (I : PeriodicData) (T : I.Carrier → I.Carrier → ℂ) (D : Set (Fin 4 → ℂ))
    (C : ℝ) : Prop :=
  SymbolSummableOn I I T D ∧ ∀ κ ∈ D, IsInvertibleQuotHom (symbolHom I I T κ) ∧
    quotHomNorm (quotHomInverse (symbolHom I I T κ)) ≤ ENNReal.ofReal C
def TripleCompSymbolInvertibleOn (I J : PeriodicData) (T : I.Carrier → J.Carrier → ℂ)
    (A : J.Carrier → J.Carrier → ℂ) (S : J.Carrier → I.Carrier → ℂ) (D : Set (Fin 4 → ℂ))
    (C : ℝ) : Prop :=
  (∀ ι' ι, CompSummableAt T A ι' ι) ∧ (∀ ι' ι, CompSummableAt (compKernel T A) S ι' ι) ∧
    SymbolInvertibleOn I (compKernel (compKernel T A) S) D C
structure AddScalarInvertibleOn (I : PeriodicData) (A : I.Carrier → I.Carrier → ℂ) (τ : ℝ)
    (D : Set (Fin 4 → ℂ)) : Prop where
  periodic : IsPeriodicKernel I I (addScalar I τ A)
  symbol : ∀ κ ∈ D, SymbolSummableAt I I A κ ∧ SymbolSummableAt I I (addScalar I τ A) κ ∧
    symbolHom I I (addScalar I τ A) κ = symbolAddScalar I τ A κ
  invertible_on_reals : SymbolInvertibleOnReals I (addScalar I τ A)
  inverse_periodic : IsPeriodicKernel I I (periodicInverse I (addScalar I τ A))
  matrix_invertible : ∀ κ ∈ D, IsInvertibleQuotHom (symbolAddScalar I τ A κ)
  inverse_summable : SymbolSummableOn I I (periodicInverse I (addScalar I τ A)) D
  inverse_symbol : ∀ κ ∈ D, symbolHom I I (periodicInverse I (addScalar I τ A)) κ =
    quotHomInverse (symbolAddScalar I τ A κ)
structure BoundedSymbols (L k : ℕ) (D : Set (Fin 4 → ℂ)) (C : ℝ) : Prop where
  edge_sqrt : SymbolBoundedOn (edges L k) (edges L k) (edgeResolventSqrt L k) D C
  edge_sqrt_eq : ∀ κ ∈ D,
    symbolHom (edges L k) (edges L k) (edgeResolventSqrt L k) κ = edgePowMatrix L k (-(1 / 2)) κ
  vertex_sqrt : SymbolBoundedOn (vertices L k) (vertices L k) (vertexResolventSqrt L k) D C
  vertex_sqrt_eq : ∀ κ ∈ D,
    symbolHom (vertices L k) (vertices L k) (vertexResolventSqrt L k) κ =
      vertexPowMatrix L k (-(1 / 2)) κ
  diff_edge_sqrt : CompSymbolBoundedOn (edges L k) (faces L k) (edges L k)
    (edgeDiff L k) (edgeResolventSqrt L k) D C
  diffT_edge_sqrt : CompSymbolBoundedOn (edges L k) (vertices L k) (edges L k)
    (vertexDiffT L k) (edgeResolventSqrt L k) D C
  edge_sqrt_diff : CompSymbolBoundedOn (edges L k) (edges L k) (vertices L k)
    (edgeResolventSqrt L k) (vertexDiff L k) D C
  edge_sqrt_diffT : CompSymbolBoundedOn (edges L k) (edges L k) (faces L k)
    (edgeResolventSqrt L k) (edgeDiffT L k) D C
  diff_vertex_sqrt : CompSymbolBoundedOn (vertices L k) (edges L k) (vertices L k)
    (vertexDiff L k) (vertexResolventSqrt L k) D C
  vertex_sqrt_diffT : CompSymbolBoundedOn (vertices L k) (vertices L k) (edges L k)
    (vertexResolventSqrt L k) (vertexDiffT L k) D C
  edge_avg : SymbolBoundedOn (edges L k) (topEdges L k) (edgeAvg L k) D C
  vertex_avg : SymbolBoundedOn (vertices L k) (topVertices L k) (vertexAvg L k) D C
  edge_avgT : SymbolBoundedOn (topEdges L k) (edges L k) (edgeAvgT L k) D C
  vertex_avgT : SymbolBoundedOn (topVertices L k) (vertices L k) (vertexAvgT L k) D C
structure InvertibleSymbols (L k : ℕ) (D : Set (Fin 4 → ℂ)) (C t τ : ℝ) : Prop where
  edge_interp : TripleCompSymbolInvertibleOn (edges L k) (edges L k) (edgeResolventSqrt L k)
    (interpPlusOne (edges L k) t (edgeOpXi L k) (edgeOpK L k))
    (edgeResolventSqrt L k) D C
  edge_add : TripleCompSymbolInvertibleOn (edges L k) (edges L k) (edgeResolventSqrt L k)
    (addScalar (edges L k) τ (edgeOpXi L k)) (edgeResolventSqrt L k) D C
  vertex_interp : TripleCompSymbolInvertibleOn (vertices L k) (vertices L k)
    (vertexResolventSqrt L k)
    (interpPlusOne (vertices L k) t (vertexOpY L k) (vertexOpDelta L k))
    (vertexResolventSqrt L k) D C
  vertex_add : TripleCompSymbolInvertibleOn (vertices L k) (vertices L k) (vertexResolventSqrt L k)
    (addScalar (vertices L k) τ (vertexOpY L k)) (vertexResolventSqrt L k) D C
  edge_avg : TripleCompSymbolInvertibleOn (topEdges L k) (edges L k) (edgeAvg L k)
    (periodicInverse (edges L k) (addScalar (edges L k) τ (edgeOpXi L k)))
    (edgeAvgT L k) D C
  vertex_avg : TripleCompSymbolInvertibleOn (topVertices L k) (vertices L k) (vertexAvg L k)
    (periodicInverse (vertices L k) (addScalar (vertices L k) τ (vertexOpY L k)))
    (vertexAvgT L k) D C
  edge_inverse : AddScalarInvertibleOn (edges L k) (edgeOpXi L k) τ D
  vertex_inverse : AddScalarInvertibleOn (vertices L k) (vertexOpY L k) τ D
def StripBounds (L k : ℕ) (δ C : ℝ) : Prop :=
  BoundedSymbols L k (imStrip (2 * δ)) C ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ τ ∈ Icc (0 : ℝ) 1, InvertibleSymbols L k (imStrip (2 * δ)) C t τ
def FreeStripEstimate : Prop :=
  ∃ δ ∈ Ioc (0 : ℝ) (1 / 32), ∃ C : ℝ, 1 ≤ C ∧
    ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
      ∀ k : ℕ, 1 ≤ k → StripBounds L k δ C
end FreeStrip
end Tower
end YangMills.Construction
end
