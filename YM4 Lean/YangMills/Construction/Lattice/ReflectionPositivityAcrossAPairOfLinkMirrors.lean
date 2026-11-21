import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import YangMills.Construction.Lattice.ReflectionPositivityAndChessboardEstimateOfAGridDatum
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.MirrorPositivity
variable {L : ℕ} {κ : ℤ}
def reflectedPairing (d : CellGrid L κ) (β : ℝ) (θ : d.Space → d.Space)
    (F' F : d.GaugeConfig → ℂ) : ℂ :=
  d.gibbsMean β fun U =>
    starRingEnd ℂ ((d.symmetryOfMap θ).actOnObservables F' U) * F U
def PositiveOnHalf (d : CellGrid L κ) (β : ℝ) (θ : d.Space → d.Space) (H : Set d.Space) : Prop :=
  (∀ b : d.DirectedEdge, b.LiesIn H ↔ b ∈ d.edgesWithin H) ∧
  ∃ hH : IsOpen H,
    d.localAlgebra ⟨H, hH⟩ =
      {F | BoxTorus.IsBoundedBorelOfEdges {b : d.DirectedEdge | b.LiesIn H} F} ∧
    ∀ F ∈ d.localAlgebra ⟨H, hH⟩, ∀ F' ∈ d.localAlgebra ⟨H, hH⟩,
      0 ≤ reflectedPairing d β θ F F ∧
      ‖reflectedPairing d β θ F' F‖ ^ 2 ≤
        (reflectedPairing d β θ F' F').re * (reflectedPairing d β θ F F).re
def PositiveAcrossMirrorPair (d : CellGrid L κ) (β : ℝ) (μ : Fin 4) (c : ℝ) : Prop :=
  (∃! θ : d.Space → d.Space, d.IsInducedMap θ (InfiniteLattice.coordinateReflection μ c)) ∧
  ∀ θ : d.Space → d.Space, d.IsInducedMap θ (InfiniteLattice.coordinateReflection μ c) →
    BoxTorus.IsDistPreserving θ ∧
    θ '' (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) =
      (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) ∧
    PositiveOnHalf d β θ (BoxTorus.slab d.sideLengths μ c (c + 1 / 2 * d.sideLengths μ)) ∧
    PositiveOnHalf d β θ (BoxTorus.slab d.sideLengths μ (c - 1 / 2 * d.sideLengths μ) c)
def ReflectionPositivityAcrossMirrors : Prop :=
  ∀ (L : ℕ) (κ : ℤ) (d : CellGrid L κ) (β : ℝ), 0 < β →
    (∀ (μ : Fin 4) (c : ℝ), (∃ z : ℤ, c = PeriodicLattice.meshSize L κ * ((z : ℝ) + 1 / 2)) →
      PositiveAcrossMirrorPair d β μ c) ∧
    d.IsReflectionPositiveAcrossFaces β
end YangMills.Construction.MirrorPositivity
end
