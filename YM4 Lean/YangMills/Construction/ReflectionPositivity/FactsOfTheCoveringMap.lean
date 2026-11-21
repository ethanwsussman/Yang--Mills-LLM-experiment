import YangMills.Construction.Lattice.AxialGauges
import YangMills.Construction.ReflectionPositivity.AxisMirrorData
import Mathlib
set_option autoImplicit false
open Set Function
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity.AxisMirror
def intLattice (α : ℝ) : Set (Fin 4 → ℝ) := range (intCombination α)
def frameAffine (R : PeriodicLattice.SignedFrame) (v : Fin 4 → ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  R.actOnVector y + v
namespace MirrorData
variable (D : MirrorData)
def slabImage (μ : Fin 4) (A : Set ℝ) : Set D.Torus :=
  D.projection '' coordSet μ fun t => t ∈ A
def descended (s' : (Fin 4 → ℝ) → Fin 4 → ℝ) : D.Torus → D.Torus :=
  Classical.epsilon (D.Induces s')
def cellsPerSide (j : ℤ) : ℝ := 2 * (D.L : ℝ) ^ ((D.m : ℤ) + j)
def ProjectionAdditive : Prop :=
  Surjective D.projection ∧
    (∀ x : D.Torus, ∃ y, D.projection y = x ∧ ∀ μ, y μ ∈ Ico 0 D.side) ∧
    (∀ y y', D.projection y = D.projection y' ↔ y - y' ∈ intLattice D.side) ∧
    (∀ y v, D.shift (D.projection y) v = D.projection (y + v)) ∧
    (∀ (x x' : D.Torus) (v : Fin 4 → ℝ), x' - x = D.projection v ↔ x' = D.shift x v) ∧
    ∀ (x : D.Torus) (v v' : Fin 4 → ℝ),
      D.shift (D.shift x v) v' = D.shift x (v + v')
def ProjectionMetric : Prop :=
  (∀ y y', IsLeast (range fun n : Fin 4 → ℤ =>
        TorusMetric.euclidNormVec (y - y' + intCombination D.side n))
      (TorusMetric.torusEuclidNorm (D.projection y - D.projection y'))) ∧
    (∀ y y', TorusMetric.torusEuclidNorm (D.projection y - D.projection y') ≤
      TorusMetric.euclidNormVec (y - y')) ∧
    (∀ (y : Fin 4 → ℝ) (x' : D.Torus), ∃ y'', D.projection y'' = x' ∧
      TorusMetric.euclidNormVec (y - y'') = TorusMetric.torusEuclidNorm (D.projection y - x')) ∧
    (∀ x x' : D.Torus,
      TorusMetric.torusEuclidNorm (x - x') = TorusMetric.torusEuclidNorm (x' - x)) ∧
    (∀ x x' : D.Torus, TorusMetric.torusEuclidNorm (x - x') = 0 → x = x') ∧
    ∀ x x' x'' : D.Torus,
      TorusMetric.torusEuclidNorm (x - x'') ≤
        TorusMetric.torusEuclidNorm (x - x') + TorusMetric.torusEuclidNorm (x' - x'')
def ProjectionSlabs : Prop :=
  ∀ (μ : Fin 4) (A B : Set ℝ),
    (∀ y, D.projection y ∈ D.slabImage μ A ↔ y μ ∈ D.periodize A) ∧
      (Disjoint (D.slabImage μ A) (D.slabImage μ B) ↔ D.periodize A ∩ B = ∅) ∧
      (D.periodize A = D.periodize B → D.slabImage μ A = D.slabImage μ B) ∧
      ∀ v : Fin 4 → ℝ, D.shiftSet (D.slabImage μ A) v = D.slabImage μ (translateSet A (v μ))
def ProjectionSites (j : ℤ) : Prop :=
  (∃ N : ℕ, 0 < N ∧ (N : ℝ) = D.cellsPerSide j ∧
      D.side = D.cellsPerSide j * PeriodicLattice.meshSize D.L j) ∧
    (∀ n : ℤ, ∃ n' : ℤ, D.side * n = PeriodicLattice.meshSize D.L j * n') ∧
    ((PeriodicLattice.sublattice D.L D.m j : Set D.Torus) =
      D.projection '' intLattice (PeriodicLattice.meshSize D.L j)) ∧
    (∀ y, D.projection y ∈ PeriodicLattice.sublattice D.L D.m j ↔
      y ∈ intLattice (PeriodicLattice.meshSize D.L j)) ∧
    (∀ (x : PeriodicLattice.Site D.L D.m j) (w : Fin 4 → ℤ),
      D.shift x (intCombination (PeriodicLattice.meshSize D.L j) w) ∈
        PeriodicLattice.sublattice D.L D.m j) ∧
    (∀ (x : PeriodicLattice.Site D.L D.m j) (w w' : Fin 4 → ℤ),
      D.shift x (intCombination (PeriodicLattice.meshSize D.L j) w) =
          D.shift x (intCombination (PeriodicLattice.meshSize D.L j) w') ↔
        ∃ n : Fin 4 → ℤ, ∀ μ, ((w μ - w' μ : ℤ) : ℝ) = D.cellsPerSide j * n μ) ∧
    (∀ x x' : PeriodicLattice.Site D.L D.m j,
      (∃ b : PeriodicLattice.Bond D.L D.m j, b.source = x ∧ b.target = x') ↔
        ∃ (ε : ℝ) (ν : Fin 4), (ε = 1 ∨ ε = -1) ∧ (x' : D.Torus) =
          D.shift x ((ε * PeriodicLattice.meshSize D.L j) • PeriodicLattice.coordVec ν)) ∧
    ∀ b : PeriodicLattice.Bond D.L D.m j, b.IsPositivelyOriented ↔ ∃ ν : Fin 4,
      (b.target : D.Torus) =
        D.shift b.source (PeriodicLattice.meshSize D.L j • PeriodicLattice.coordVec ν)
def ProjectionSitesAtFinest : Prop :=
  PeriodicLattice.meshSize D.L (D.K : ℕ) = D.mesh ∧
    PeriodicLattice.sublattice D.L D.m (D.K : ℕ) = D.torusSublattice ∧
    (D.L : ℝ) ^ ((D.m : ℤ) + ((D.K : ℕ) : ℤ)) = D.halfSideCount
def ProjectionDescends (R : PeriodicLattice.SignedFrame) (v : Fin 4 → ℝ) : Prop :=
  (∃ (ς : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤˣ), ∀ ν,
    R.actOnVector (PeriodicLattice.coordVec ν) =
      (((ε ν : ℤ) : ℝ)) • PeriodicLattice.coordVec (ς ν)) ∧
  Bijective (frameAffine R v) ∧
    (∀ y y', TorusMetric.euclidNormVec (frameAffine R v y - frameAffine R v y') =
      TorusMetric.euclidNormVec (y - y')) ∧
    (∃ R' : PeriodicLattice.SignedFrame,
      (LeftInverse R'.actOnVector R.actOnVector ∧
        RightInverse R'.actOnVector R.actOnVector) ∧
      LeftInverse (fun y => R'.actOnVector y - R'.actOnVector v) (frameAffine R v) ∧
      RightInverse (fun y => R'.actOnVector y - R'.actOnVector v) (frameAffine R v) ∧
      LeftInverse (D.descended fun y => R'.actOnVector y - R'.actOnVector v)
        (D.descended (frameAffine R v)) ∧
      RightInverse (D.descended fun y => R'.actOnVector y - R'.actOnVector v)
        (D.descended (frameAffine R v))) ∧
    (∃! s, D.Induces (frameAffine R v) s) ∧
    D.Induces (frameAffine R v) (D.descended (frameAffine R v)) ∧
    Bijective (D.descended (frameAffine R v)) ∧
    (∀ x x' : D.Torus, TorusMetric.torusEuclidNorm
        (D.descended (frameAffine R v) x - D.descended (frameAffine R v) x') =
      TorusMetric.torusEuclidNorm (x - x')) ∧
    (∀ Z : Set (Fin 4 → ℝ), D.descended (frameAffine R v) '' (D.projection '' Z) =
      D.projection '' (frameAffine R v '' Z)) ∧
    (∀ (x : D.Torus) (v' : Fin 4 → ℝ), D.descended (frameAffine R v) (D.shift x v') =
      D.shift (D.descended (frameAffine R v) x) (R.actOnVector v')) ∧
    ∀ (R' : PeriodicLattice.SignedFrame) (v' : Fin 4 → ℝ),
      (∃ (R'' : PeriodicLattice.SignedFrame) (v'' : Fin 4 → ℝ),
        frameAffine R v ∘ frameAffine R' v' = frameAffine R'' v'') ∧
      D.Induces (frameAffine R v ∘ frameAffine R' v')
        (D.descended (frameAffine R v) ∘ D.descended (frameAffine R' v'))
end MirrorData
def ProjectionFacts : Prop :=
  ∀ D : MirrorData, D.ProjectionAdditive ∧ D.ProjectionMetric ∧ D.ProjectionSlabs ∧
    (∀ j : ℤ, -(D.m : ℤ) ≤ j → D.ProjectionSites j) ∧ D.ProjectionSitesAtFinest ∧
    ∀ (R : PeriodicLattice.SignedFrame) (v : Fin 4 → ℝ), D.ProjectionDescends R v
end ReflectionPositivity.AxisMirror
end YangMills.Construction
