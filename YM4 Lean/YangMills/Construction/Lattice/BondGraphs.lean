import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
namespace YangMills.Construction.PeriodicLattice
structure MultiLevelBondSet (L m K : ℕ) where
  edges : Finset (Σ j : ℕ, BondAtLevel L m K j)
  edges_level_le : ∀ e ∈ edges, e.1 ≤ K
namespace MultiLevelBondSet
variable {L m K : ℕ}
def vertices (T : MultiLevelBondSet L m K) : Set (FourTorus L m) :=
  {x | ∃ e ∈ T.edges, x = (e.2.source : FourTorus L m) ∨ x = (e.2.target : FourTorus L m)}
def ContainsEdge (T : MultiLevelBondSet L m K) (x y : FourTorus L m) : Prop :=
  ∃ e ∈ T.edges, (e.2.source : FourTorus L m) = x ∧ (e.2.target : FourTorus L m) = y
def Adjacent (T : MultiLevelBondSet L m K) (x y : FourTorus L m) : Prop :=
  T.ContainsEdge x y ∨ T.ContainsEdge y x
def IsWalkBetween (T : MultiLevelBondSet L m K) (x y : FourTorus L m) {p : ℕ}
    (w : Fin (p + 1) → FourTorus L m) : Prop :=
  (∀ i, w i ∈ T.vertices) ∧ w 0 = x ∧ w (Fin.last p) = y ∧
    ∀ i : Fin p, T.Adjacent (w i.castSucc) (w i.succ)
def IsWalk (T : MultiLevelBondSet L m K) {p : ℕ} (w : Fin (p + 1) → FourTorus L m) : Prop :=
  T.IsWalkBetween (w 0) (w (Fin.last p)) w
def IsCycle (T : MultiLevelBondSet L m K) {p : ℕ} (w : Fin (p + 1) → FourTorus L m) : Prop :=
  T.IsWalk w ∧ 3 ≤ p ∧ w (Fin.last p) = w 0 ∧ Function.Injective fun i : Fin p => w i.castSucc
def IsAcyclic (T : MultiLevelBondSet L m K) : Prop :=
  ∀ (p : ℕ) (w : Fin (p + 1) → FourTorus L m), ¬T.IsCycle w
def Reachable (T : MultiLevelBondSet L m K) (x y : FourTorus L m) : Prop :=
  ∃ (p : ℕ) (w : Fin (p + 1) → FourTorus L m), T.IsWalkBetween x y w
def componentOf (T : MultiLevelBondSet L m K) (x : FourTorus L m) : Set (FourTorus L m) :=
  {y | y ∈ T.vertices ∧ T.Reachable x y}
def components (T : MultiLevelBondSet L m K) : Set (Set (FourTorus L m)) :=
  {C | ∃ x ∈ T.vertices, C = T.componentOf x}
end MultiLevelBondSet
end YangMills.Construction.PeriodicLattice
