import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import Mathlib
noncomputable section
namespace YangMills.Construction.TestSpaces
def ApproxByTensorSums {n : ℕ} (V : Set (PointTuple n)) (O : Set (Fin 4 → ℝ)) (k : ℕ) : Prop :=
  ∀ φ ∈ (smoothCompactSupp V : Set (PointTuple n → ℂ)), ∀ ε : ℝ, 0 < ε →
    ∃ (m : ℕ) (c : Fin m → ℂ) (f : Fin m → Fin n → (Fin 4 → ℝ) → ℝ),
      0 < m ∧ (∀ i, f i ∈ disjointSupportTuples O n ∧ HasSmoothComponents O (f i)) ∧
      weightedSeminorm k (φ - fun x => ∑ i, c i * ((tensorProd (f i) x : ℝ) : ℂ)) ≤ ENNReal.ofReal ε ∧
      ((∀ x, (φ x).im = 0) → ∀ i, (c i).im = 0)
def TensorSumsApproxBumps : Prop :=
  ∀ n k : ℕ, 0 < n → 0 < k →
    ApproxByTensorSums (distinctLocus n) Set.univ k ∧
      ApproxByTensorSums (positiveTimeLocus n) upperHalfSpace k
end YangMills.Construction.TestSpaces
