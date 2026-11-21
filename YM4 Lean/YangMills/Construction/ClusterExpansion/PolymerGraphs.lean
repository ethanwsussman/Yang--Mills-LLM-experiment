import Mathlib
set_option autoImplicit false
open scoped Classical
noncomputable section
universe u v
namespace YangMills.Construction.ClusterExpansion
namespace SymGraph
variable {V : Type v} [Fintype V]
def edgePairs (V : Type v) [Fintype V] : Finset (Sym2 V) :=
  Finset.univ.filter fun e => ¬ e.IsDiag
def graphSet (V : Type v) [Fintype V] : Finset (Finset (Sym2 V)) :=
  (edgePairs V).powerset
def IsWalk (k : Finset (Sym2 V)) (a b : V) (m : ℕ) (r : Fin (m + 1) → V) : Prop :=
  r 0 = a ∧ r (Fin.last m) = b ∧ ∀ l : Fin m, s(r l.castSucc, r l.succ) ∈ k
def reachableSet (k : Finset (Sym2 V)) (b : V) : Finset V :=
  Finset.univ.filter fun a => ∃ (m : ℕ) (r : Fin (m + 1) → V), IsWalk k b a m r
def IsConnected (k : Finset (Sym2 V)) : Prop :=
  ∀ b : V, reachableSet k b = Finset.univ
def connectedSet (V : Type v) [Fintype V] : Finset (Finset (Sym2 V)) :=
  (graphSet V).filter IsConnected
def IsPartition (B : Finset (Finset V)) : Prop :=
  (∀ b ∈ B, b.Nonempty) ∧ (B : Set (Finset V)).PairwiseDisjoint id ∧ B.biUnion id = Finset.univ
def partitions (V : Type v) [Fintype V] : Finset (Finset (Finset V)) :=
  Finset.univ.filter IsPartition
end SymGraph
structure PolymerRelation (P : Type u) [Fintype P] where
  Related : P → P → Prop
  refl : ∀ X, Related X X
  symm : ∀ X Y, Related X Y ↔ Related Y X
namespace PolymerRelation
variable {P : Type u} [Fintype P] (S : PolymerRelation P)
def zetaFactor (X Y : P) : ℝ :=
  1 - if S.Related X Y then 1 else 0
theorem zetaFactor_comm (X Y : P) : S.zetaFactor X Y = S.zetaFactor Y X := by
  simp only [zetaFactor, S.symm X Y]
variable {V : Type v} [Fintype V]
def edgeFactor (X : V → P) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun i j => S.zetaFactor (X i) (X j) - 1, fun i j => by simp only [S.zetaFactor_comm (X i)]⟩
def graphWeight (k : Finset (Sym2 V)) (X : V → P) : ℝ :=
  ∏ e ∈ k, S.edgeFactor X e
def ursellFunction (X : V → P) : ℝ :=
  ∑ k ∈ SymGraph.connectedSet V, S.graphWeight k X
end PolymerRelation
end YangMills.Construction.ClusterExpansion
