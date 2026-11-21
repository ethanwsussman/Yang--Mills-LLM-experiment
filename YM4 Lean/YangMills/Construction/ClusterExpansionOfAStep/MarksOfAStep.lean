import YangMills.Construction.ClusterExpansionOfAStep.HullsOfHotLumps
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace StepMarks
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts
variable {n : ℕ}
def IsStepSituation (ℓ : StepParameters) [NeZero n] (r' : ℕ) (V : TorusField n)
    (S C : Finset (TorusSite n)) (s : ℝ) : Prop :=
  (IsBlockTorusSide ℓ n ∧ S = Finset.univ \ thickening lumpRange (torusHotSites ℓ V) ∧
      C = minimalHull ℓ r' V ∧ s = ℓ.threshold) ∨
    (ℓ.n₀ ≤ n ∧ IsCold (9 / 8 * ℓ.threshold) V ∧ S = Finset.univ ∧ C = ∅ ∧
      s = 9 / 8 * ℓ.threshold)
structure RangesAdmissible (r r' : ℕ) : Prop where
  le_succ : r ≤ r' + 1
  large : 2 ^ 16 ≤ r'
  frame_radius : 16 ≤ r / 2 ^ 11
def minimizerCoord (a ρ : ℝ) (L t : ℕ) (S : Finset (TorusSite n)) (V : TorusField n)
    (b : TorusBond (n * L)) : imaginaryQuaternions :=
  minimizingBondCoordinate a ρ (cellsOfSites (torusFrame L t n) S)
    (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth b.1, b.2)
    (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
def frameDeviation (ℓ : StepParameters) (ρA : ℝ) (t m₀ : ℕ) (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (b : TorusBond (n * ℓ.side)) : imaginaryQuaternions :=
  chartCoord ℓ V W b - frameCoord ℓ ρA t m₀ V b
def goodMark (ℓ : StepParameters) (ρA : ℝ) (p : ℝ → ℝ) (t m₀ : ℕ) (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (b : TorusBond (n * ℓ.side)) : ℝ :=
  cutoffFactor (ℓ.threshold / 64) p ‖(frameDeviation ℓ ρA t m₀ V W b : ℍ[ℝ])‖
def IsRangeSuppressed (q : ℝ → ℝ) : Prop :=
  ∃ K C c : ℝ, 0 < c ∧ ∀ x : ℝ, 1 ≤ x → |q x| ≤ K * x ^ C * Real.exp (-(c * clusterRange x))
def frameGap (N₀ δ σ x : ℝ) : ℝ :=
  N₀ * (2 * σ) * Real.exp (-(δ * ((clusterRange x / 2 ^ 11 : ℕ) : ℝ)))
end StepMarks
end YangMills.Construction
end
