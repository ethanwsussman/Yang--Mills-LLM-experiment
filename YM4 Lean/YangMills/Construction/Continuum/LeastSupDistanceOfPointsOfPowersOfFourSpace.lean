import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MinSeparation
open ConfigSpace
def LipschitzContinuousProp (n : ℕ) : Prop :=
  (∀ x : Config n, minSeparation x ≠ ⊤) ∧
  (∀ x y : Config n,
    |(minSeparation x).toReal - (minSeparation y).toReal| ≤ 2 * coordSupNorm (x - y)) ∧
  Continuous fun x : Config n => (minSeparation x).toReal
def ZeroSetProp (n : ℕ) : Prop :=
  diagonalSet n = {x | minSeparation x = 0} ∧ IsClosed (diagonalSet n)
def ComplementProp (n : ℕ) : Prop :=
  (diagonalSet n)ᶜ = TestFunctions.injectiveTuples (Fin 4 → ℝ) n ∧
  IsOpen (TestFunctions.injectiveTuples (Fin 4 → ℝ) n)
def mainClaim : Prop :=
  (∀ n : ℕ, 2 ≤ n →
    LipschitzContinuousProp n ∧ ZeroSetProp n ∧ ComplementProp n) ∧
  ZeroSetProp 1 ∧ ComplementProp 1
end YangMills.Construction.MinSeparation
end
