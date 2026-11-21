import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Graphs
def MultigraphPathConnected {α β : Type} (G : Graph α β) : Prop :=
  ∀ x ∈ G.vertexSet, ∀ y ∈ G.vertexSet, ∃ (n : ℕ) (p : ℕ → α),
    p 0 = x ∧ p n = y ∧ ∀ i < n, G.Adj (p i) (p (i + 1))
def ExistsClosedWalkThroughAllVertices : Prop :=
  ∀ (α β : Type) (G : Graph α β), G.vertexSet.Finite → G.edgeSet.Finite → G.Loopless →
    MultigraphPathConnected G → ∀ E : ℕ, G.edgeSet.ncard = E → ∀ r ∈ G.vertexSet,
      G.vertexSet.ncard ≤ E + 1 ∧
      ∃ u : ℕ → α, u 0 = r ∧ u (2 * E) = r ∧ (∀ t ≤ 2 * E, u t ∈ G.vertexSet) ∧
        (∀ v ∈ G.vertexSet, ∃ t ≤ 2 * E, u t = v) ∧
        ∀ t : ℕ, 1 ≤ t → t ≤ 2 * E → G.Adj (u (t - 1)) (u t)
end YangMills.Construction.Graphs
