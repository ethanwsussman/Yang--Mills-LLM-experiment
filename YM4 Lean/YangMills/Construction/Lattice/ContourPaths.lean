import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ} {j j' : ℤ}
def IsBlockOffset (y : Site L m j) (x : Site L m j') (n : Fin 4 → ℤ) : Prop :=
  (x : FourTorus L m) - (y : FourTorus L m) =
      ∑ μ, pointOnAxis L m μ ((n μ : ℝ) * meshSize L j') ∧
    ∀ μ, 2 * |n μ| ≤ (L : ℤ) - 1
def blockOffset (y : Site L m j) (x : Site L m j') : Fin 4 → ℤ :=
  Classical.epsilon (IsBlockOffset y x)
def offsetAxes (y : Site L m j) (x : Site L m j') : Finset (Fin 4) :=
  Finset.univ.filter fun μ => blockOffset y x μ ≠ 0
abbrev AxisOrdering (y : Site L m j) (x : Site L m j') : Type :=
  Fin (offsetAxes y x).card ≃ offsetAxes y x
def stepsThroughAxes (n : Fin 4 → ℤ) (x : Site L m j') : List (Fin 4) → List (Bond L m j')
  | [] => []
  | μ :: l => flowAlong x μ (n μ) ++ stepsThroughAxes n (x + n μ • unitStep L m j' μ) l
def orderedContour (y : Site L m j) (x : Site L m j') (σ : AxisOrdering y x) :
    List (Bond L m j') :=
  stepsThroughAxes (blockOffset y x) (y.toSublattice j')
    ((List.finRange _).map fun i => ((σ i : offsetAxes y x) : Fin 4))
def contourSet (y : Site L m j) (x : Site L m j') : Set (List (Bond L m j')) :=
  Set.range (orderedContour y x)
def shiftAcross (c : Bond L m j) (x : Site L m j') : Site L m j' :=
  x + (c.target - c.source).toSublattice j'
def crossingPath (c : Bond L m j) (x : Site L m j') : List (Bond L m j') :=
  axialPath x (shiftAcross c x)
def parallelTransport (U : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) :
    Matrices.ComplexMatrix2 :=
  pathHolonomy U (axialPath (c.source.toSublattice j') (c.target.toSublattice j'))
end PeriodicLattice
end YangMills.Construction
