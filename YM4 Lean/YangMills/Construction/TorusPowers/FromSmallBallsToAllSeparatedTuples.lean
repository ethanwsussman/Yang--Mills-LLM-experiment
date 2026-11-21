import YangMills.Construction.ToriAtArbitraryCouplings.TheSeparationAtEveryLength
import YangMills.Construction.TorusPowers.PowersLiftsDistancesAndTopology
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TorusPowers
open AmbientPoints (Pt separatedTuples)
variable {P : Conventions.StandingParameters} {n : ℕ}
def smallBallConstant (M : ℝ) (p : ℕ) : ℝ := (2 * (p : ℝ)) ^ 4 * (1 + 10 * (p : ℝ) * M)
def torusTupleGap (f : Fin n → Pt P .torus → ℝ) : ℝ≥0∞ :=
  (ToriAtArbitraryCouplings.TorusSide.ofStandingParameters P).gapAllLengths .torus (List.ofFn f)
def SupportsInClosedBalls (R : ℝ) (f : Fin n → Pt P .torus → ℝ) : Prop :=
  ∀ i, ∃ x : Pt P .torus,
    tsupport (f i) ⊆ TestFunctions.closedBallTorus (ℓ := PeriodicLattice.torusSide P.L P.m) x R
def BoundedOnSmallBallTuples (M d c : ℝ) (p : ℕ) (Ψ : separatedTuples P .torus n → ℝ) : Prop :=
  ∀ u : separatedTuples P .torus n, ENNReal.ofReal d ≤ torusTupleGap u.1 →
    SupportsInClosedBalls (PeriodicLattice.torusSide P.L P.m / p) u.1 →
      |Ψ u| ≤ c * ∏ i, TestFunctions.sharpNormTorus M (u.1 i)
def SmallBallsToSeparatedTuples : Prop :=
  ∀ (P : Conventions.StandingParameters), 8 * 105 ^ 4 ≤ P.L → ∀ (M : ℝ), IsPowerOfL P M →
    ∀ (n : ℕ), 2 ≤ n → ∀ (d c : ℝ), 0 < d → 0 ≤ c → ∀ (p : ℕ), 3 ≤ p →
      ∀ Ψ : separatedTuples P .torus n → ℝ,
        AmbientPoints.IsTupleMultilinear Ψ → BoundedOnSmallBallTuples M d c p Ψ →
          (∀ h : separatedTuples P .torus n, ENNReal.ofReal d ≤ torusTupleGap h.1 →
            |Ψ h| ≤ smallBallConstant M p ^ n * c * ∏ i, TestFunctions.sharpNormTorus M (h.1 i)) ∧
          1 ≤ smallBallConstant M p
end YangMills.Construction.TorusPowers
end
