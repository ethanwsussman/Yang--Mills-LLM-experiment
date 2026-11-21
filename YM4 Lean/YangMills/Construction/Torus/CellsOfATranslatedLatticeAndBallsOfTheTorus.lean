import YangMills.Construction.Torus.CellOfAPointOfTheTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric TestFunctions
namespace TorusMeasure
namespace TranslatedLatticeCells
variable (s : Conventions.StandingParameters)
def cellLattice (a : ℝ) : Set s.Torus :=
  proj s '' {x | ∃ k : Fin 4 → ℤ, ∀ μ, x μ = a * (k μ : ℝ)}
def DistanceProperties : Prop :=
  (∀ u w z : s.Torus, pointDist w u = pointDist u w ∧
    pointDist u w ≤ pointDist u z + pointDist z w) ∧
  ∀ x : Fin 4 → ℝ, pointNorm (proj s x) ≤ euclidNormVec x
def ClosedWrapBallProperties : Prop :=
  ∀ (p : s.Torus) (r : ℝ), 0 < r →
    closedWrapBall p r = {u | pointDist u p ≤ r} ∧
    (∀ x : Fin 4 → ℝ, IsLift s p x →
      closedWrapBall p r = proj s '' closedBallR4 x r ∧
      volumeR4 (closedBallR4 x r) = ENNReal.ofReal (omega4 * r ^ 4)) ∧
    @IsClosed _ (euclidTopology s) (closedWrapBall p r) ∧
    IsMeasurableTorusSet (closedWrapBall p r) ∧
    torusVolume (closedWrapBall p r) ≤ omega4 * r ^ 4 ∧
    (r < PeriodicLattice.torusSide s.L s.m / 2 →
      closedWrapBall p r = closedBallTorus (ℓ := PeriodicLattice.torusSide s.L s.m) p r)
def LipschitzBoundedMeasurable : Prop :=
  ∀ f : s.Torus → ℝ, IsLipschitzFor pointDist f → IsBoundedFun f ∧ IsMeasurableFun f
def CellProperties (a : ℝ) : Prop :=
  ∀ z : s.Torus, z ∈ torusCell a z ∧ IsMeasurableTorusSet (torusCell a z) ∧
    torusVolume (torusCell a z) = a ^ 4 ∧
    ∀ u ∈ torusCell a z, pointDist u z ≤ a
def LatticeCellPartition (a : ℝ) (m : ℤ) : Prop :=
  (∃ H : AddSubgroup s.Torus, (H : Set s.Torus) = cellLattice s a) ∧
  (cellLattice s a).Finite ∧ ((cellLattice s a).ncard : ℤ) = m ^ 4 ∧
  ∀ v : s.Torus, (cellLattice s a).PairwiseDisjoint (fun y => torusCell a (y + v)) ∧
    ⋃ y ∈ cellLattice s a, torusCell a (y + v) = univ
def LatticePointCountInBall (a : ℝ) : Prop :=
  ∀ (v p : s.Torus) (r : ℝ), 0 < r →
    a ^ 4 * ({y | y ∈ cellLattice s a ∧ pointDist (y + v) p ≤ r}.ncard : ℝ) ≤
      omega4 * (r + a) ^ 4
def RiemannSumApprox (a : ℝ) : Prop :=
  ∀ (v p : s.Torus) (r : ℝ) (f : s.Torus → ℝ), 0 < r → IsLipschitzFor pointDist f →
    (∀ u, u ∉ {u | pointDist u p ≤ r} → f u = 0) →
    |a ^ 4 * (∑ᶠ y ∈ cellLattice s a, f (y + v)) - torusIntegral f| ≤
      omega4 * a * (r + 2 * a) ^ 4 * lipConstTorus (ℓ := PeriodicLattice.torusSide s.L s.m) f
def CellsAndBallsStatement : Prop :=
  ∀ s : Conventions.StandingParameters,
    DistanceProperties s ∧ ClosedWrapBallProperties s ∧ LipschitzBoundedMeasurable s ∧
    ∀ (a : ℝ) (m : ℤ), 0 < a → PeriodicLattice.torusSide s.L s.m / a = m →
      CellProperties s a ∧ LatticeCellPartition s a m ∧ LatticePointCountInBall s a ∧
        RiemannSumApprox s a
end TranslatedLatticeCells
end TorusMeasure
end YangMills.Construction
end
