import YangMills.Construction.TestSpaces.PointsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction
namespace TestSpaces
def upperHalfSpace : Set (Fin 4 → ℝ) := {u | u 3 > 0}
def distinctLocus (n : ℕ) : Set (PointTuple n) := TestFunctions.injectiveTuples (Fin 4 → ℝ) n
def positiveTimeLocus (n : ℕ) : Set (PointTuple n) :=
  {x | x ∈ TestFunctions.injectiveTuples (Fin 4 → ℝ) n ∧ ∀ i, timeCoord x i > 0}
def negativeTimeLocus (n : ℕ) : Set (PointTuple n) :=
  {x | x ∈ TestFunctions.injectiveTuples (Fin 4 → ℝ) n ∧ ∀ i, -timeCoord x i > 0}
section InfiniteOrderVanishing
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
def VanishesToInfiniteOrderAt (f : PointTuple n → F) (x : PointTuple n) : Prop :=
  ContDiff ℝ ∞ f ∧ f x = 0 ∧ ∀ α : MultiIdx4 n, multiDeriv α f x = 0
def VanishesToInfiniteOrderOff (f : PointTuple n → F) (U : Set (PointTuple n)) : Prop :=
  ContDiff ℝ ∞ f ∧ IsOpen U ∧ ∀ x ∈ Uᶜ, VanishesToInfiniteOrderAt f x
end InfiniteOrderVanishing
end TestSpaces
end YangMills.Construction
