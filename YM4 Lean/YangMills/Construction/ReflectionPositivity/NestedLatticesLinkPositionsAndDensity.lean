import YangMills.Construction.ReflectionPositivity.OneTorusAllCutoffsPointsAndTheClassC1
import YangMills.Construction.ReflectionPositivity.UnionOfTheLatticesAndLinkPositionsOfAllCutoffs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.NestedRefinement
variable (s : Conventions.StandingParameters)
def MonotoneInRefinement : Prop :=
  ∀ k k' : ℕ+, k ≤ k' →
    (EveryCutoff.sublatticeAt s k : Set s.Torus) ⊆ EveryCutoff.sublatticeAt s k' ∧
      EveryCutoff.linkLevelsAt s k ⊆ EveryCutoff.linkLevelsAt s k'
def LatticePointPersists : Prop :=
  ∀ (v : s.Torus) (Kv : ℕ+), v ∈ EveryCutoff.sublatticeAt s Kv →
    ∀ k : ℕ+, Kv ≤ k → v ∈ EveryCutoff.sublatticeAt s k
def LinkLevelPersists : Prop :=
  ∀ (c : ℝ) (Kc : ℕ+), c ∈ EveryCutoff.linkLevelsAt s Kc →
    ∀ k : ℕ+, Kc ≤ k → c ∈ EveryCutoff.linkLevelsAt s k
def UnionIsAddSubgroup : Prop :=
  ∃ G : AddSubgroup s.Torus, (G : Set s.Torus) = EveryCutoff.unionOfSublattices s
def UnionIsDense : Prop :=
  ∀ (x : s.Torus) (ε : ℝ), 0 < ε →
    ∃ y ∈ EveryCutoff.unionOfSublattices s, TorusCutoffs.torusDist x y < ε
def LinkLevelsAreDense : Prop :=
  Dense (EveryCutoff.allLinkLevels s)
def NestedAndDense : Prop :=
  ∀ s : Conventions.StandingParameters,
    (MonotoneInRefinement s ∧ LatticePointPersists s ∧
      LinkLevelPersists s) ∧
    (UnionIsAddSubgroup s ∧ UnionIsDense s) ∧
    LinkLevelsAreDense s
end YangMills.Construction.ReflectionPositivity.NestedRefinement
end
