import YangMills.Construction.BoundsOnEverySide.OnePointOfALimitOverTheBounds
import YangMills.Construction.SystemsWithFiveBounds.BoundsAtNumbers
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open TestFunctions (IsLipschitzFor euclidDistR4 closedBallR4 sharpNormR4)
open BoundsOnEverySide (unitMassBumps)
open InfiniteLattice (GaugeField AmbientSpace smearedEnergy)
def unitBallBound (M : ℝ) (N : BoundConstants) : ℝ :=
  N.onePointConst 1 * sInf (sharpNormR4 M '' unitMassBumps)
def OnePointLimitWithConstants : Prop :=
  ∀ (F : StatedSideFamily) (N : BoundConstants), BoundsHoldAt F N → ∀ (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ)
    (ρ ν : ∀ n, Measure (GaugeField (PeriodicLattice.meshSize F.L (((K n : ℕ+) : ℕ) : ℤ)))),
    (∀ n, F.IsFirstPassage (K n) (β n)) → (∀ n, ρ n ∈ F.stateSet F.L (K n) (β n)) →
    (∀ n, ν n ∈ F.stateSet F.L (K n) (β n)) →
    (∀ (R : ℝ) (f : AmbientSpace → ℝ) (z : ℝ), 0 < R → IsLipschitzFor euclidDistR4 f →
      (∃ x, tsupport f ⊆ closedBallR4 x R) →
      Tendsto (fun n => (∫ U, smearedEnergy f U ∂ρ n) - ∫ U, smearedEnergy f U ∂ν n) atTop (𝓝 z) →
        |z| ≤ N.onePointConst R * sharpNormR4 F.M f) ∧
    ∀ c : ℝ, (∀ f ∈ unitMassBumps,
      Tendsto (fun n => (∫ U, smearedEnergy f U ∂ρ n) - ∫ U, smearedEnergy f U ∂ν n) atTop (𝓝 c)) →
        |c| ≤ unitBallBound F.M N
end YangMills.Construction.SystemsWithFiveBounds
end
