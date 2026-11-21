import YangMills.Construction.Continuum.EuclideanMotionsAndOperationsOnFunctionsAndTuples
import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TestSpaces
def increasingTimes (q : ℕ) : Set (PointTuple q) := {x | StrictMono (timeCoord x)}
def increasingPositiveTimes (q : ℕ) : Set (PointTuple q) :=
  {x | x ∈ increasingTimes q ∧ ∀ h : 0 < q, 0 < timeCoord x ⟨0, h⟩}
theorem continuous_timeCoord_apply {q : ℕ} (i : Fin q) :
    Continuous fun x : PointTuple q => timeCoord x i :=
  (continuous_apply 3).comp (continuous_apply i)
theorem isOpen_increasingTimes (q : ℕ) : IsOpen (increasingTimes q) := by
  have hEq : increasingTimes q =
      ⋂ i : Fin q, ⋂ j : Fin q, {x : PointTuple q | i < j → timeCoord x i < timeCoord x j} := by
    ext x
    simp [increasingTimes, StrictMono]
  rw [hEq]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  by_cases hlt : i < j
  · simpa [hlt] using isOpen_lt (continuous_timeCoord_apply i) (continuous_timeCoord_apply j)
  · simp [hlt]
theorem isOpen_increasingPositiveTimes (q : ℕ) : IsOpen (increasingPositiveTimes q) := by
  by_cases hq : 0 < q
  · have hEq : increasingPositiveTimes q =
        increasingTimes q ∩ {x | 0 < timeCoord x ⟨0, hq⟩} := by
      ext x
      simp [increasingPositiveTimes, hq]
    rw [hEq]
    exact (isOpen_increasingTimes q).inter
      (isOpen_lt continuous_const (continuous_timeCoord_apply _))
  · have hEq : increasingPositiveTimes q = increasingTimes q := by
      ext x
      simp [increasingPositiveTimes, hq]
    rw [hEq]
    exact isOpen_increasingTimes q
theorem increasingTimes_subset_distinctLocus (q : ℕ) :
    increasingTimes q ⊆ distinctLocus q := by
  intro x hx i j hij
  have hinj : Function.Injective (timeCoord x) := StrictMono.injective hx
  exact hinj (congrFun hij 3)
theorem increasingPositiveTimes_subset_positiveTimeLocus (q : ℕ) :
    increasingPositiveTimes q ⊆ positiveTimeLocus q := by
  intro x hx
  refine ⟨increasingTimes_subset_distinctLocus q hx.1, fun i => ?_⟩
  have hq : 0 < q := i.pos
  have hfirst : 0 < timeCoord x ⟨0, hq⟩ := hx.2 hq
  have hmono : timeCoord x ⟨0, hq⟩ ≤ timeCoord x i :=
    StrictMono.monotone hx.1 (Fin.mk_le_of_le_val (Nat.zero_le _))
  exact lt_of_lt_of_le hfirst hmono
def schwartzOnIncreasingPositiveTimes (q : ℕ) : Set (PointTuple q → ℂ) :=
  {φ | φ ∈ schwartzSet q ∧ ∀ x, x ∉ increasingPositiveTimes q → φ x = 0}
def succComponent (Φ : (q : ℕ) → Motions.TensorVal ℂ q) (q : ℕ) :
    PointTuple (q + 1) → ℂ := Φ (q + 1)
def IsIncreasingPositiveTimeSeq (Φ : (q : ℕ) → Motions.TensorVal ℂ q) : Prop :=
  {q : ℕ | succComponent Φ q ≠ 0}.Finite ∧
    ∀ q : ℕ, succComponent Φ q ∈ schwartzOnIncreasingPositiveTimes (q + 1)
def rotatePermute {q : ℕ} (R : Matrix.orthogonalGroup (Fin 4) ℝ) (σ : Equiv.Perm (Fin q))
    (x : PointTuple q) : PointTuple q :=
  fun i => (R : Matrix (Fin 4) (Fin 4) ℝ).mulVec (x (σ i))
end YangMills.Construction.TestSpaces
