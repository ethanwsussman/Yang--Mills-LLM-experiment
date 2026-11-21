import YangMills.Construction.Towers.CovariantLinearAverages
import YangMills.Construction.Towers.ExpansionOfAStepInTheLeftChart
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower
section Expansion
variable {L n k : ℕ}
def iterLogRatio (U : Edge L n k 0 → ComplexMatrix2) (c : PositiveEdge L n k k)
    (B : Edge L n k 0 → ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries
    (PeriodicLattice.complexBlockFieldAtLevel k (PeriodicLattice.expTwist B U) c *
      (PeriodicLattice.complexBlockFieldAtLevel k U c)⁻¹)
abbrev IterBilinearForm (L n k : ℕ) : Type :=
  edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0 →ₗ[ℝ] PositiveEdge L n k k → ComplexMatrix2
def IsIterQuadraticExpansion (U : Edge L n k 0 → ComplexMatrix2)
    (q : IterBilinearForm L n k) : Prop :=
  (∀ B B' : edgeFormSpace L n k 0, q B B' = q B' B) ∧
    ∀ c : PositiveEdge L n k k, ∃ C : ℝ, ∀ᶠ B : edgeFormSpace L n k 0 in 𝓝 0,
      ComplexMatrix2.operatorNorm (iterLogRatio U c B - complexIterDeriv L n k k U B c -
        (1 / 2 : ℝ) • q B B c) ≤ C * edgeFormNorm (B : Edge L n k 0 → ComplexMatrix2) ^ 3
def iterQuadraticTerm (U : Edge L n k 0 → ComplexMatrix2) : IterBilinearForm L n k :=
  Classical.epsilon (IsIterQuadraticExpansion U)
def CovariantIterEqRealIterAt (V : Edge L n k 0 → ComplexMatrix2) : Prop :=
  ∀ c : PositiveEdge L n k k,
    PeriodicLattice.complexBlockFieldAtLevel k V c = smoothingIter L n k k V c
def IterLogRatioAnalytic (U : Edge L n k 0 → ComplexMatrix2) : Prop :=
  U ∈ smallIterateFields L n k ∧ CovariantIterEqRealIterAt U ∧
    (∀ᶠ B : edgeFormSpace L n k 0 in 𝓝 0,
      PeriodicLattice.expTwist (B : Edge L n k 0 → ComplexMatrix2) U ∈ smallIterateFields L n k ∧
      CovariantIterEqRealIterAt (PeriodicLattice.expTwist (B : Edge L n k 0 → ComplexMatrix2) U) ∧
      ∀ c : PositiveEdge L n k k,
        PeriodicLattice.complexBlockFieldAtLevel k
            (PeriodicLattice.expTwist (B : Edge L n k 0 → ComplexMatrix2) U) c *
          (PeriodicLattice.complexBlockFieldAtLevel k U c)⁻¹ ∈ ComplexMatrix2.logBall) ∧
    ∀ c : PositiveEdge L n k k,
      IsAnalyticNearZero (iterLogRatio U c) ∧ iterLogRatio U c 0 = 0
def IterDerivIsLinearTaylorTerm (U : Edge L n k 0 → ComplexMatrix2) : Prop :=
  ∀ (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k k),
    taylorCoeffAtZero 1 (iterLogRatio U c) B =
        deriv (fun t : ℝ => iterLogRatio U c ((t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2))) 0 ∧
      deriv (fun t : ℝ => iterLogRatio U c ((t : ℂ) • (B : Edge L n k 0 → ComplexMatrix2))) 0 =
        complexIterDeriv L n k k U B c
def IterHasUniqueQuadraticExpansion (U : Edge L n k 0 → ComplexMatrix2) : Prop :=
  (∃! q : IterBilinearForm L n k, IsIterQuadraticExpansion U q) ∧
    IsIterQuadraticExpansion U (iterQuadraticTerm U) ∧
    ∀ q : IterBilinearForm L n k, IsIterQuadraticExpansion U q →
      ∀ (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k k),
        (1 / 2 : ℝ) • q B B c = taylorCoeffAtZero 2 (iterLogRatio U c) B
end Expansion
def IterLeftChartExpansion : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
      IterLogRatioAnalytic U ∧
        IterDerivIsLinearTaylorTerm U ∧
        IterHasUniqueQuadraticExpansion U
end Tower
end YangMills.Construction
end
