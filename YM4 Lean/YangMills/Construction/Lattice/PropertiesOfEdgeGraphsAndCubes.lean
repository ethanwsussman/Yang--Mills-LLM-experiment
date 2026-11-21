import YangMills.Construction.Lattice.PartitionInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.EdgeGraphCubeProperties
variable (S : LevelUnitPartition)
def centreLattice : Set (Fin 4 → ℝ) :=
  {c | ∀ μ, ∃ a : ℤ, c μ = (S.side : ℝ) * (a : ℝ)}
def IsCubeCentredAt (Δ : Set S.Points) (x : S.Points) : Prop :=
  ∃ y : Site S.params.L S.params.m S.index, (y : S.Points) = x ∧ Δ = cubeAround y
def signedStep (ν : Fin 4) (σ : ℝ) : Fin 4 → ℝ := (σ * (S.side : ℝ)) • coordVec ν
def projectedBox (c : Fin 4 → ℝ) : Set S.Points := S.proj '' S.closedBox c
def neighbourCubes (Δ : Set S.Points) : Set (Set S.Points) :=
  {Δ' | Δ' ∈ S.cubes ∧ CubesShareFace S.index Δ Δ'}
def HasEndpoints (e : Set S.Points) (a b : S.Points) : Prop :=
  a ≠ b ∧ S.IsEdgeEndpoint e a ∧ S.IsEdgeEndpoint e b
def LinkedByChain (W : Set S.Points) (A : Set (Set S.Points)) (x x' : S.Points) : Prop :=
  ∃ c : List S.Points, (∀ u ∈ c, u ∈ W) ∧
    c.IsChain (fun a b => ∃ e ∈ A, HasEndpoints S e a b) ∧
    c.head? = some x ∧ c.getLast? = some x'
def MeetsGraphAtVertices (Γ : Set S.Points) : Prop :=
  (∀ Δ ∈ S.cubes, CubeIntersects Δ Γ ↔ ∃ v, S.IsCornerOf v Δ ∧ v ∈ S.graphVertices Γ) ∧
    ∀ Y, IsPartitionRegion S.index Y → ((Y ∩ Γ).Nonempty ↔ ∃ v ∈ S.graphVertices Γ, v ∈ Y)
def VertexCornerIncidence (X : Set S.Points) : Prop :=
  (∀ v, S.IsVertex v → ∀ Δ ∈ S.cubes, (v ∈ Δ ↔ S.IsCornerOf v Δ)) ∧
    (∀ v, S.IsVertex v → (v ∈ X ↔ ∃ Δ ∈ partitionCubesIn S.index X, S.IsCornerOf v Δ)) ∧
    (∀ v, S.IsVertex v → (S.cubesContaining v).ncard = 16) ∧
    (∀ w ∈ S.vertexSet, S.cubesContaining (S.proj w) =
      {Δ | ∃ ε, LevelUnitPartition.IsSigns ε ∧
        IsCubeCentredAt S Δ (S.proj (w - ((S.side : ℝ) / 2) • ε))}) ∧
    ∀ Δ ∈ S.cubes, {v | S.IsCornerOf v Δ}.ncard = 16
def CubeNeighbours : Prop :=
  (∀ c ∈ centreLattice S, ∀ Δ Δ', IsCubeCentredAt S Δ (S.proj c) → Δ' ∈ S.cubes →
    CubesShareFace S.index Δ Δ' →
      ∃ (ν : Fin 4) (σ : ℝ), (σ = 1 ∨ σ = -1) ∧
        IsCubeCentredAt S Δ' (S.proj (c + signedStep S ν σ))) ∧
    ∀ Δ ∈ S.cubes, (neighbourCubes S Δ).encard ≤ 8
def CubeNeighboursOfWideTorus : Prop :=
  (3 * (S.side : ℝ) ≤ sideInLevelUnits S.params.L S.params.m S.params.K S.level ↔
    S.sideExponent + S.level + 1 ≤ (S.params.m : ℕ) + (S.params.K : ℕ)) ∧
  (3 * (S.side : ℝ) ≤ sideInLevelUnits S.params.L S.params.m S.params.K S.level →
    (∀ c ∈ centreLattice S, ∀ (ν ν' : Fin 4) (σ σ' : ℝ), (σ = 1 ∨ σ = -1) → (σ' = 1 ∨ σ' = -1) →
      ∀ Δ, IsCubeCentredAt S Δ (S.proj (c + signedStep S ν σ)) →
        IsCubeCentredAt S Δ (S.proj (c + signedStep S ν' σ')) → ν = ν' ∧ σ = σ') ∧
    (∀ c ∈ centreLattice S, ∀ (ν : Fin 4) (σ : ℝ), (σ = 1 ∨ σ = -1) →
      projectedBox S c ∩ projectedBox S (c + signedStep S ν σ) = S.facetAt c ν σ ∧
        S.facetAt c ν σ = S.facetAt (c + signedStep S ν σ) ν (-σ)) ∧
    ∀ Δ ∈ S.cubes, (neighbourCubes S Δ).encard = 8)
def ConnectedGraphVertexCubeBounds : Prop :=
  ∀ (e : ℕ) (Γ' : Set S.Points), S.IsGlobalEdgeGraph Γ' → IsConnected Γ' →
    (S.graphEdges Γ').encard = e →
      (S.graphVertices Γ').encard ≤ (e : ℕ∞) + 1 ∧
        {Δ | Δ ∈ S.cubes ∧ CubeIntersects Δ Γ'}.encard ≤ 16 * ((e : ℕ∞) + 1)
def ShortestTreeVertexCount (X Γ : Set S.Points) : Prop :=
  ∀ G : Set (Set S.Points), G.Finite → (∀ Y ∈ G, IsPartitionRegion S.index Y) →
    IsSpanningEdgeTree S.index X G Γ →
    (∀ Γ', IsSpanningEdgeTree S.index X G Γ' →
      graphLength S.side S.index Γ ≤ graphLength S.side S.index Γ') →
    (S.graphVertices Γ).encard = (S.graphEdges Γ).encard + 1
def EdgeEndpointFacts (X : Set S.Points) : Prop :=
  (∀ w ∈ S.vertexSet, ∀ w' ∈ S.vertexSet, ∀ ν ν' : Fin 4,
    S.edgeAt w ν = S.edgeAt w' ν' → ν = ν' ∧ S.proj w = S.proj w') ∧
    (∀ e, S.IsEdge e → {v | S.IsEdgeEndpoint e v}.ncard = 2) ∧
    (∀ e e', S.IsEdge e → S.IsEdge e' → e ≠ e' →
      ∀ x, x ∈ e → x ∈ e' → S.IsEdgeEndpoint e x ∧ S.IsEdgeEndpoint e' x) ∧
    (∀ (Γ' : Set S.Points) (A : Set (Set S.Points)), S.IsGlobalEdgeGraph Γ' → A.Finite → A.Nonempty →
      (∀ a ∈ A, S.IsEdge a) → Γ' = ⋃₀ A →
        S.graphEdges Γ' = A ∧ edgeCount S.index Γ' = A.ncard) ∧
    (∀ v, S.IsVertex v → S.graphEdges {v} = ∅) ∧
    ∀ e, S.IsEdge e → (e ⊆ X ↔ ∃ Δ ∈ partitionCubesIn S.index X, S.IsEdgeOf e Δ)
def VertexAdjacencyAndConnectivity : Prop :=
  (∀ w ∈ S.vertexSet, {v | S.Adjacent (S.proj w) v} =
    {v | ∃ (ν : Fin 4) (σ : ℝ), (σ = 1 ∨ σ = -1) ∧ v = S.proj (w + signedStep S ν σ)}) ∧
    (∀ v, S.IsVertex v → {v' | S.Adjacent v v'}.encard ≤ 8 ∧ ¬S.Adjacent v v) ∧
    (∀ A : Set (Set S.Points), A.Finite → A.Nonempty → (∀ a ∈ A, S.IsEdge a) →
      S.IsGlobalEdgeGraph (⋃₀ A) ∧
        (IsConnected (⋃₀ A) ↔
          ∀ v ∈ S.graphVertices (⋃₀ A), ∀ v' ∈ S.graphVertices (⋃₀ A),
            LinkedByChain S (S.graphVertices (⋃₀ A)) (S.graphEdges (⋃₀ A)) v v')) ∧
    ∀ Γ', S.IsGlobalEdgeTree Γ' → S.IsConnectedVertices (S.graphVertices Γ')
def EdgeNumbering : Prop :=
  ∀ (W : Set S.Points) (q : ℕ) (A : Set (Set S.Points)), W.Finite → W.ncard = q → 1 ≤ q →
    (∀ v ∈ W, S.IsVertex v) →
    (∀ a ∈ A, S.IsEdge a ∧ ∀ v, S.IsEdgeEndpoint a v → v ∈ W) →
    (∀ v ∈ W, ∀ v' ∈ W, LinkedByChain S W A v v') →
    ∀ F ∈ W, ∃ v : ℕ → S.Points, v 1 = F ∧ BijOn v (Icc 1 q) W ∧
      ∃ a : ℕ → Set S.Points,
        (∀ k, 2 ≤ k → k ≤ q →
          a k ∈ A ∧ ∃ l, 1 ≤ l ∧ l < k ∧ HasEndpoints S (a k) (v k) (v l)) ∧
        InjOn a (Icc 2 q) ∧
        (2 ≤ q → IsConnected (⋃ k ∈ Icc 2 q, a k) ∧ W ⊆ ⋃ k ∈ Icc 2 q, a k)
end YangMills.Construction.PeriodicLattice.EdgeGraphCubeProperties
end
