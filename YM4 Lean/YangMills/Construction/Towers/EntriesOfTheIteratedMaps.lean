import YangMills.Construction.Towers.BondsOnWhichTheAveragesDepend
import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
namespace IteratedKernelEntries
open Tower.SupportOfMeans.Unbounded (supportEdges)
open PeriodicOperators FieldValueFunctions
def edgesNear (L k : ℕ) (x : InfiniteLattice.AmbientSpace) (r : ℝ) : Set (Edge L k 0) :=
  {b | ∀ i, |(b.initial : InfiniteLattice.AmbientSpace) i - x i| < r ∧
    |(b.terminal : InfiniteLattice.AmbientSpace) i - x i| < r}
def driftKernel (L k : ℕ) (U : Edge L k 0 → Matrices.ComplexMatrix2) :
    KernelMatrix (Fin 3 × PositiveEdge (meshAt L k 0)) (Fin 3 × Vertex L k k) :=
  (edgePauliCoordinates L k 0).kernel (vertexCoordinate (Vertex L k k)) (iterContourLogDrift L k U k)
def driftKernelFn (L k : ℕ) (hL : 0 < L) :
    ((fieldPeriodicData L k hL).Carrier → ℂ) →
      (colourVertices L k k).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  fun f => driftKernel L k (FieldValueFunctions.gaugeFieldOfCoeffs hL f)
end IteratedKernelEntries
open Tower.SupportOfMeans.Unbounded (supportEdges)
open PeriodicOperators FieldValueFunctions IteratedKernelEntries
def IteratedKernelEntries.Claim : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ (y : Vertex L k k) (a' : Fin 3),
        (∀ ι, HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
          (backgroundCoords L k hL (edgesNear L k y 2))
          fun f => driftKernelFn L k hL f (a', y) ι) ∧
        (∀ ι, HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
          (backgroundCoords L k hL (edgesNear L k y 2))
          fun f => averageKernelFn L k hL f (a', y) ι) ∧
        ∀ (a : Fin 3) (x : Vertex L k 0),
          (x : InfiniteLattice.AmbientSpace) ∉ cubeOfOrder L (meshAt L k 0) k y →
          ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
            averageKernelFn L k hL f (a', y) (a, x) = 0) ∧
      ∀ (c : PositiveEdge (meshAt L k k)) (a' : Fin 3),
        (∀ ι, HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
          (backgroundCoords L k hL (edgesNear L k c.1.initial 3))
          fun f => covariantAverageFn L k hL f (a', c) ι) ∧
        ∀ (a : Fin 3) (b : PositiveEdge (meshAt L k 0)), b.1 ∉ supportEdges c.1 →
          ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
            covariantAverageFn L k hL f (a', c) (a, b) = 0
end YangMills.Construction.Tower.FullSpace
end
