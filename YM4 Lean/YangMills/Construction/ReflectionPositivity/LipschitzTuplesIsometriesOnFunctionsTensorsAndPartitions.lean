import YangMills.Construction.ReflectionPositivity.SeparatedTuplesAndFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
variable (D : MirrorData) (E : Ambient)
def IsLipschitzDisjointList (X : FnList D E) : Prop :=
  (∀ f ∈ X, TestFunctions.IsLipschitzFor (metric D E) f ∧
      MetricNotions.IsCompactWrt (metric D E) (closedSupport D E f)) ∧
    X.Pairwise fun f g => Disjoint (closedSupport D E f) (closedSupport D E g)
section Joining
variable {D E} {𝕜 : Type*} [RCLike 𝕜]
def HaveDisjointSupports (X Y : List (E.Point D → 𝕜)) : Prop :=
  (append X Y).Pairwise fun f g => Disjoint (closedSupport D E f) (closedSupport D E g)
end Joining
def IsIsometryOf : (E : Ambient) → (E.Point D → E.Point D) → Prop
  | torus, r => PeriodicLattice.IsTorusIsometry (L := D.L) (m := D.m) r
  | euclidean, r => InfiniteLattice.IsSpaceIsometry r
structure IsometryEquiv where
  toEquiv : E.Point D ≃ E.Point D
  isometric : IsIsometryOf D E toEquiv
namespace IsometryEquiv
variable {D E} (r : IsometryEquiv D E) {α : Type*}
def mapFn (f : E.Point D → α) : E.Point D → α := f ∘ r.toEquiv.symm
def mapList (X : List (E.Point D → α)) : List (E.Point D → α) := X.map r.mapFn
end IsometryEquiv
end YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
