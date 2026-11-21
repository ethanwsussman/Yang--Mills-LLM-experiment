import YangMills.Construction.InfiniteLattice.GeneratingFunctionsAndConnectedFunctionsOfAMeasureAndOfATorus
import YangMills.Construction.InfiniteLattice.StatesAtOneSpacing
import YangMills.Construction.Torus.FunctionalsOnATorusAndFamiliesUnderABoundFunctionOnTorusOrFourSpace
import YangMills.Construction.Torus.LipschitzTuplesSeparationConcatenationAndTransport
import Mathlib
set_option autoImplicit false
open YangMills.Construction.TorusFunctionals YangMills.Construction.AmbientPoints
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.CouplingFlow
def TorusUrsellBound (M : ℕ) (s : YangMills.Construction.Conventions.StandingParameters) (β : ℝ)
    (n : ℕ) (d C : ℝ) : Prop :=
  ∀ f ∈ lipSeparatedTuples s .torus n, ENNReal.ofReal d ≤ supportSeparation f →
    ‖YangMills.Construction.PeriodicLattice.torusUrsellFunction s.L s.m s.K β f‖ ≤
      C * ∏ i, sharpNormAt s .torus M (f i)
def TorusBallUrsellBound (M : ℕ) (s : YangMills.Construction.Conventions.StandingParameters) (β : ℝ)
    (n : ℕ) (d R C : ℝ) : Prop :=
  16 * (n : ℝ) * (R + 1) ≤ s.side →
    ∀ f ∈ lipSeparatedTuples s .torus n, IsSupportedInBalls R f →
      ENNReal.ofReal d ≤ supportSeparation f →
        ‖YangMills.Construction.PeriodicLattice.torusUrsellFunction s.L s.m s.K β f‖ ≤
          C * ∏ i, sharpNormAt s .torus M (f i)
def StateBallUrsellBound (M : ℕ) (s : YangMills.Construction.Conventions.StandingParameters) (β : ℝ)
    (n : ℕ) (d R C : ℝ) : Prop :=
  ∀ ν ∈ YangMills.Construction.InfiniteLattice.periodicGibbsStates s.L s.K β,
    ∀ f ∈ lipSeparatedTuples s .euclidean n, IsSupportedInBalls R f →
      ENNReal.ofReal d ≤ supportSeparation f →
        ‖YangMills.Construction.InfiniteLattice.ursellFunction ν.1 n f‖ ≤
          C * ∏ i, sharpNormAt s .euclidean M (f i)
def OnePointDiffBound (M : ℕ) (s : YangMills.Construction.Conventions.StandingParameters) (β : ℝ)
    (R C : ℝ) : Prop :=
  ∀ ν ∈ YangMills.Construction.InfiniteLattice.periodicGibbsStates s.L s.K β,
    ∀ ν' ∈ YangMills.Construction.InfiniteLattice.periodicGibbsStates s.L s.K β,
      ∀ f : Pt s .euclidean → ℝ,
        YangMills.Construction.TestFunctions.IsLipschitzFor (pointDist s .euclidean) f →
        (∃ B, IsClosedBallRadius s .euclidean R B ∧ tsupport f ⊆ B) →
          |(∫ U, YangMills.Construction.InfiniteLattice.smearedEnergy f U ∂ν.1) -
              ∫ U, YangMills.Construction.InfiniteLattice.smearedEnergy f U ∂ν'.1| ≤
            C * sharpNormAt s .euclidean M f
structure ConstantFamilies where
  torusConst : ℕ → ℝ → ℝ → ℝ
  supConst : ℕ → ℝ → ℝ → ℝ
  starConst : ℕ → ℝ → ℝ → ℝ
  onePointConst : ℝ → ℝ
structure FamilyBoundsHold (L M : ℕ) (sides : Set ℝ) (IsDatum : ℕ+ → ℝ → Prop) (N : ConstantFamilies) :
    Prop where
  torus : ∀ s : YangMills.Construction.Conventions.StandingParameters, s.L = L → s.side ∈ sides →
    ∀ β, IsDatum s.K β → ∀ n, 2 ≤ n →
    ∀ d, 0 < d → TorusUrsellBound M s β n d (N.torusConst n d s.side)
  torusBall : ∀ s : YangMills.Construction.Conventions.StandingParameters, s.L = L → s.side ∈ sides →
    ∀ β, IsDatum s.K β → ∀ n, 2 ≤ n →
    ∀ d R, 0 < d → 0 < R → TorusBallUrsellBound M s β n d R (N.supConst n d R)
  stateBall : ∀ s : YangMills.Construction.Conventions.StandingParameters, s.L = L →
    ∀ β, IsDatum s.K β → ∀ n, 2 ≤ n →
    ∀ d R, 0 < d → 0 < R → StateBallUrsellBound M s β n d R (N.starConst n d R)
  onePoint : ∀ s : YangMills.Construction.Conventions.StandingParameters, s.L = L →
    ∀ β, IsDatum s.K β → ∀ R, 0 < R → OnePointDiffBound M s β R (N.onePointConst R)
end YangMills.Construction.CouplingFlow
end
