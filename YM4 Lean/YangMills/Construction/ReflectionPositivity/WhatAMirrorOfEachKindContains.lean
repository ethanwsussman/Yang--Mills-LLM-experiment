import YangMills.Construction.ReflectionPositivity.AxisMirrorData
import Mathlib
import YangMills.Construction.ReflectionPositivity.PositionsAndKindsOfMirrors
import YangMills.Construction.ReflectionPositivity.ReflectionsHyperplanesMirrorsAndOpenSides
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
variable {D : MirrorData} {E : Ambient}
def siteToPoint : {E : Ambient} → E.Site D → E.Point D
  | torus, x => (x : PeriodicLattice.Site D.L D.m (D.K : ℕ)).1
  | euclidean, x => (x : InfiniteLattice.LatticePoint D.mesh).1
def addVec : {E : Ambient} → E.Point D → (Fin 4 → ℝ) → E.Point D
  | torus, x, v => D.shift x v
  | euclidean, x, v =>
      let y : Fin 4 → ℝ := x
      (y + v : Fin 4 → ℝ)
def linkStart : {E : Ambient} → E.Bond D → E.Point D
  | torus, b => siteToPoint (E := torus) (b : PeriodicLattice.Bond D.L D.m (D.K : ℕ)).source
  | euclidean, b => siteToPoint (E := euclidean) (b : InfiniteLattice.Link D.mesh).initial
def linkEnd : {E : Ambient} → E.Bond D → E.Point D
  | torus, b => siteToPoint (E := torus) (b : PeriodicLattice.Bond D.L D.m (D.K : ℕ)).target
  | euclidean, b => siteToPoint (E := euclidean) (b : InfiniteLattice.Link D.mesh).terminal
def plaquetteLowAxis : {E : Ambient} → E.Plaquette D → Fin 4
  | torus, p => (p : PeriodicLattice.Plaquette D.L D.m (D.K : ℕ)).firstAxis
  | euclidean, p => (p : InfiniteLattice.ElementaryPlaquette D.mesh).lowAxis
def plaquetteHighAxis : {E : Ambient} → E.Plaquette D → Fin 4
  | torus, p => (p : PeriodicLattice.Plaquette D.L D.m (D.K : ℕ)).secondAxis
  | euclidean, p => (p : InfiniteLattice.ElementaryPlaquette D.mesh).highAxis
def plaquetteVertices : {E : Ambient} → E.Plaquette D → Set (E.Point D)
  | torus, p => Subtype.val '' (p : PeriodicLattice.Plaquette D.L D.m (D.K : ℕ)).vertices
  | euclidean, p =>
      let q : InfiniteLattice.ElementaryPlaquette D.mesh := p
      Subtype.val '' ({q.corner, q.corner + InfiniteLattice.axisStep D.mesh q.lowAxis,
        q.corner + InfiniteLattice.axisStep D.mesh q.lowAxis + InfiniteLattice.axisStep D.mesh q.highAxis,
        q.corner + InfiniteLattice.axisStep D.mesh q.highAxis} : Set (InfiniteLattice.LatticePoint D.mesh))
def IsSignedStep (b : E.Bond D) (ν : Fin 4) (ε : ℝ) : Prop :=
  (ε = 1 ∨ ε = -1) ∧
    linkEnd b = addVec (linkStart b) ((ε * D.mesh) • PeriodicLattice.coordVec ν)
def HasAxis (b : E.Bond D) (ν : Fin 4) : Prop := ∃ ε : ℝ, IsSignedStep b ν ε
def IsParallelToAxis (b : E.Bond D) (ν : Fin 4) : Prop := HasAxis b ν
def IsOrthogonalToAxis (b : E.Bond D) (μ : Fin 4) : Prop := ∃ ν : Fin 4, HasAxis b ν ∧ μ ≠ ν
def PlaquetteIsOrthogonalToAxis (p : E.Plaquette D) (μ : Fin 4) : Prop :=
  μ ∉ ({plaquetteLowAxis p, plaquetteHighAxis p} : Set (Fin 4))
def LiesWithin (b : E.Bond D) (Z : Set (E.Point D)) : Prop := linkStart b ∈ Z ∧ linkEnd b ∈ Z
def PlaquetteLiesWithin (p : E.Plaquette D) (Z : Set (E.Point D)) : Prop := plaquetteVertices p ⊆ Z
def axisAndSign (b : E.Bond D) : Fin 4 × ℝ := Classical.epsilon fun q => IsSignedStep b q.1 q.2
def pointAlong (b : E.Bond D) (τ : ℝ) : E.Point D :=
  addVec (linkStart b) ((τ * (axisAndSign b).2 * D.mesh) • PeriodicLattice.coordVec (axisAndSign b).1)
def linkSegment (b : E.Bond D) : Set (E.Point D) := pointAlong b '' Icc 0 1
def linkMidpoint (b : E.Bond D) : E.Point D := pointAlong b (1 / 2)
def Traverses (b : E.Bond D) (Z : Set (E.Point D)) : Prop :=
  (linkSegment b ∩ Z).Nonempty ∧ linkStart b ∉ Z ∧ linkEnd b ∉ Z
def BisectsLink (Z : Set (E.Point D)) (b : E.Bond D) : Prop :=
  linkMidpoint b ∈ Z ∧ ∀ p ∈ linkSegment b, p ∈ Z → p = linkMidpoint b
end YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
end
end

noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
namespace Ambient
variable (D : MirrorData) (E : Ambient)
def SiteLevelContents (μ : Fin 4) (c : ℝ) : Prop :=
  (∃ x : E.Site D, siteToPoint x ∈ levelSet D μ c E) ∧
    ∀ x : E.Site D, siteToPoint x ∈ levelSet D μ c E →
      (∀ b : E.Bond D, IsOrthogonalToAxis b μ →
        (linkStart b = siteToPoint x ∨ linkEnd b = siteToPoint x) →
          LiesWithin b (levelSet D μ c E)) ∧
      ∀ p : E.Plaquette D, PlaquetteIsOrthogonalToAxis p μ → siteToPoint x ∈ plaquetteVertices p →
        PlaquetteLiesWithin p (levelSet D μ c E)
def LinkLevelContents (μ : Fin 4) (c : ℝ) : Prop :=
  (∀ x : E.Site D, siteToPoint x ∉ levelSet D μ c E) ∧
    ∀ b : E.Bond D, IsParallelToAxis b μ → Traverses b (levelSet D μ c E) →
      BisectsLink (levelSet D μ c E) b
end Ambient
def LevelContents : Prop :=
  ∀ (D : MirrorData) (E : Ambient) (μ : Fin 4) (c : ℝ),
    (c ∈ siteLevels D.mesh → Ambient.SiteLevelContents D E μ c) ∧
      (c ∈ linkLevels D.mesh → Ambient.LinkLevelContents D E μ c)
end YangMills.Construction.ReflectionPositivity.AxisMirror
