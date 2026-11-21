import Reconstruction.Continuum.OrderedTimes
import YangMills.Construction.Continuum.TensorBoundsIntegrationBoundsAndDensity
import YangMills.Construction.Continuum.SchwartzTestsAndMollifiers
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.TestSpaces.OrderedApprox
def IsOrderedTensorCombination {q : ℕ} (O : Set (Fin 4 → ℝ)) (ψ : PointTuple q → ℂ) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℂ) (F : Fin m → Fin q → (Fin 4 → ℝ) → ℝ),
    (∀ i, F i ∈ WightmanReconstruction.smoothDisjointTuples O q ∧
      WightmanReconstruction.IsTimeOrdered (F i)) ∧
      ψ = TestSpaceFacts.tensorCombination c F
def CompactlySupportedApprox (q k : ℕ) : Prop :=
  ∀ f ∈ schwartzOnIncreasingPositiveTimes q, ∃ g : ℕ → PointTuple q → ℂ,
    (∀ n, g n ∈ (smoothCompactSupp (increasingPositiveTimes q) : Set (PointTuple q → ℂ))) ∧
      Tendsto (fun n => weightedSeminorm k (f - g n)) atTop (𝓝 0)
def TensorApprox {q : ℕ} (V : Set (PointTuple q)) (O : Set (Fin 4 → ℝ)) (k : ℕ) : Prop :=
  ∀ f ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ)), ∃ K : Set (PointTuple q),
    IsCompact K ∧ K ⊆ V ∧ ∃ g : ℕ → PointTuple q → ℂ,
      (∀ n, tsupport (g n) ⊆ K ∧ IsOrderedTensorCombination O (g n)) ∧
        Tendsto (fun n => weightedSeminorm k (f - g n)) atTop (𝓝 0)
def Statement : Prop :=
  ∀ q k : ℕ, 0 < q → 0 < k →
    CompactlySupportedApprox q k ∧
      TensorApprox (increasingTimes q) Set.univ k ∧
        TensorApprox (increasingPositiveTimes q) upperHalfSpace k
end YangMills.Construction.TestSpaces.OrderedApprox
