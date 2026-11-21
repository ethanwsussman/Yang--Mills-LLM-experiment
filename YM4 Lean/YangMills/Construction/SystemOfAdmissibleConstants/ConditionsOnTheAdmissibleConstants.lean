import YangMills.Construction.BoundsOnEverySide.TheBoundsOnEverySide
import YangMills.Construction.InfiniteLattice.GeneratingFunctionsAndConnectedFunctionsOfAMeasureAndOfATorus
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.SystemOfAdmissibleConstants.NumbersOfTheSystem
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
open MeasureTheory TestFunctions
open InfiniteLattice (AmbientSpace periodicGibbsSet smearedEnergyCumulant smearedEnergy)
def TorusClusterBound (L : ℕ) (M : ℝ) (K : ℕ+) (β A b : ℝ) : Prop :=
  ∀ m : ℕ+, ∀ n : ℕ, 2 ≤ n → ∀ d : ℝ, 0 < d →
    ∀ f : Fin n → PeriodicLattice.FourTorus L m → ℝ, (∀ i, IsLipschitzFor euclidDistTorus (f i)) →
      HasSeparatedSupportsTorus f d →
        ‖PeriodicLattice.torusUrsellFunction L m K β f‖ ≤
          cumulantBound L A b n d (PeriodicLattice.torusSide L m) * ∏ i, sharpNormTorus M (f i)
def BallClusterBoundOnTori (L : ℕ) (M : ℝ) (K : ℕ+) (β A b : ℝ) : Prop :=
  ∀ m : ℕ+, ∀ n : ℕ, 2 ≤ n → ∀ R d : ℝ, 0 < R → 0 < d →
    ∀ f : Fin n → PeriodicLattice.FourTorus L m → ℝ, (∀ i, IsLipschitzFor euclidDistTorus (f i)) →
      (∀ i, ∃ x, tsupport (f i) ⊆ closedBallTorus x R) → HasSeparatedSupportsTorus f d →
        ‖PeriodicLattice.torusUrsellFunction L m K β f‖ ≤
          cumulantBound L A b n d R * ∏ i, sharpNormTorus M (f i)
def BallClusterBoundInStates (L : ℕ) (M : ℝ) (K : ℕ+) (β A b : ℝ) : Prop :=
  ∀ ν ∈ periodicGibbsSet L K β, ∀ n : ℕ, 2 ≤ n → ∀ R d : ℝ, 0 < R → 0 < d →
    ∀ f : Fin n → AmbientSpace → ℝ, (∀ i, IsLipschitzFor euclidDistR4 (f i)) →
      (∀ i, ∃ x, tsupport (f i) ⊆ closedBallR4 x R) → HasSeparatedSupportsR4 f d →
        ‖smearedEnergyCumulant ν f‖ ≤ cumulantBound L A b n d R * ∏ i, sharpNormR4 M (f i)
def MeanGapInStates (L : ℕ) (M : ℝ) (K : ℕ+) (β A b : ℝ) : Prop :=
  ∀ ν ∈ periodicGibbsSet L K β, ∀ ν' ∈ periodicGibbsSet L K β, ∀ R : ℝ, 0 < R →
    ∀ f : AmbientSpace → ℝ, IsLipschitzFor euclidDistR4 f → (∃ x, tsupport f ⊆ closedBallR4 x R) →
      |(∫ U, smearedEnergy f U ∂ν) - ∫ U, smearedEnergy f U ∂ν'| ≤
        onePointBound L A b R * sharpNormR4 M f
def MeanGapToTori (L : ℕ) (M : ℝ) (K : ℕ+) (β A b : ℝ) : Prop :=
  ∀ ν ∈ periodicGibbsSet L K β, ∀ m : ℕ+, ∀ R : ℝ, 0 < R → 4 * R ≤ PeriodicLattice.torusSide L m →
    ∀ f : AmbientSpace → ℝ, IsLipschitzFor euclidDistR4 f → (∃ x, tsupport f ⊆ closedBallR4 x R) →
      |(∫ U, smearedEnergy f U ∂ν) - BoundsOnEverySide.torusMean L m K β f| ≤
        onePointBound L A b R * sharpNormR4 M f
structure ClusterConditions (L : ℕ) (M : ℝ) (IsFirstPassage : ℕ+ → ℝ → Prop) (A b : ℝ) : Prop where
  torus : ∀ K β, IsFirstPassage K β → TorusClusterBound L M K β A b
  ballOnTori : ∀ K β, IsFirstPassage K β → BallClusterBoundOnTori L M K β A b
  ballInStates : ∀ K β, IsFirstPassage K β → BallClusterBoundInStates L M K β A b
  meanGapInStates : ∀ K β, IsFirstPassage K β → MeanGapInStates L M K β A b
  meanGapToTori : ∀ K β, IsFirstPassage K β → MeanGapToTori L M K β A b
end YangMills.Construction.AdmissibleConstants
end
