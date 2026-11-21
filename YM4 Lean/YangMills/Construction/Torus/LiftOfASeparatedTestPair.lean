import YangMills.Construction.TestFunctions.SeparatedBumpPairs
import YangMills.Construction.Torus.LiftsOfBallsFunctionsAndTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TestFunctions
def IsPairLift {L m : ℕ} (d ϑ : ℝ) (f h : PeriodicLattice.FourTorus L m → ℝ)
    (f' h' : (Fin 4 → ℝ) → ℝ) : Prop :=
  0 < ϑ ∧ ϑ ≤ 1 ∧ 0 < d ∧ 40 * d ≤ PeriodicLattice.torusSide L m ∧
    (f, h) ∈ separatedPairsFourTorus L m d ϑ ∧ IsTupleLift ![f, h] ![f', h']
end YangMills.Construction.TestFunctions
