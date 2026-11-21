import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import YangMills.Construction.Towers.IteratedAveragesOfSmallRegularFields
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.IteratedSmallFieldMeans (HolomorphicInEntries smallFormBall)
def MeanExpansionsLocal.Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ n k : ℕ, 0 < n → 1 ≤ k →
    (∀ c : Edge L n k k, ∀ w ∈ smallFormBall L n k ρ, ∀ w' ∈ smallFormBall L n k ρ,
      ∀ B ∈ complexEdgeForms L n k 0, ∀ B' ∈ complexEdgeForms L n k 0,
        EqOn w w' (edgesOverEdge c) → EqOn B B' (edgesOverEdge c) →
          meanCovariant (remainderGaugeField w) k B c =
            meanCovariant (remainderGaugeField w') k B' c) ∧
    (∀ y : Vertex L n k k, ∀ w ∈ smallFormBall L n k ρ, ∀ w' ∈ smallFormBall L n k ρ,
      ∀ f f' : Vertex L n k 0 → Matrices.ComplexMatrix2,
        (∀ x, f x ∈ PeriodicLattice.complexLieAlgebra) → (∀ x, f' x ∈ PeriodicLattice.complexLieAlgebra) →
        (∀ x : Vertex L n k 0, (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k y →
          f x = f' x) →
        EqOn w w' (PeriodicLattice.bondsInside (PeriodicLattice.refinedBlock k y)) →
          composedCubeAverage (quietPoint (remainderGaugeField w)) k f y =
            composedCubeAverage (quietPoint (remainderGaugeField w')) k f' y) ∧
    ∀ m < k, ∀ c : Edge L n k (m + 1), ∀ w ∈ smallFormBall L n k ρ, ∀ w' ∈ smallFormBall L n k ρ,
      EqOn w w' (PeriodicLattice.bondsInside
        (PeriodicLattice.refinedBlock (m + 1) c.source ∪ PeriodicLattice.refinedBlock (m + 1) c.target)) →
        meanRadius (meanIterate (remainderGaugeField w) m) c =
          meanRadius (meanIterate (remainderGaugeField w') m) c
end YangMills.Construction.RunningCouplingSlope
end
