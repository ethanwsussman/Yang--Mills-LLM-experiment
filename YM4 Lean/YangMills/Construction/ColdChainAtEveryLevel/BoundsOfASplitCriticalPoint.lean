import YangMills.Construction.ColdChainAtEveryLevel.CriticalPointOnTheSlice
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
structure SliceCriticalPointLocalBounds (a θ K s : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (U : ChainChart F) : Prop where
  colder : IsCold S F.depth (s / 8) (chartField (referenceFieldChain S V) U F.depth)
  quartic : ∀ (j : ℕ) (x : F.Site 0) (ρ : ℝ), j < F.top → 1 ≤ ρ → ρ ≤ (F.blockSide : ℝ) ^ (F.top - j) →
    localQuarticSum S (referenceFieldChain S V) U j x ρ ≤
      (K * s) ^ 4 * (ρ / (F.blockSide : ℝ) ^ (F.top - j)) ^ (4 * θ)
  curvature_and_misfits : ∀ (x : F.Site 0) (ρ : ℝ), 1 ≤ ρ → ρ ≤ (F.blockSide : ℝ) ^ F.top →
    localCurvatureSum S (referenceFieldChain S V) U x ρ ≤
        (K * s) ^ 2 * (ρ / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) ∧
      localMisfitSum S (referenceFieldChain S V) U V x ρ ≤
        (K * s) ^ 2 * (ρ / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ)
  misfits_on_cells : ∀ (j : ℕ) (z : F.Cell), j < F.top →
    cellMisfitSum S (referenceFieldChain S V) U V j 4 z ≤
        (K * s * (4 / (F.blockSide : ℝ) ^ 2) ^ (F.top - 1 - j)) ^ 4 ∧
      cellMisfitSum S (referenceFieldChain S V) U V j 2 z ≤
        (K * s * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j)) ^ 2
def splitCriticalPointBoundsStatement : Prop :=
  ∀ a θ δ A : ℝ, 0 < a → 0 < θ → θ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 8 → 0 < A →
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ ρ K₁ : ℝ, 0 < ρ → 0 < K₁ → ∃ s₀ K₂ : ℝ, 0 < s₀ ∧ 0 < K₂ ∧
      ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F →
        1024 ≤ m → IsOrthantRegular S m →
        ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ s₀ → IsCold S F.top s V →
          ∀ U : ChainChart F, IsSliceCriticalPoint a θ δ A ρ K₁ s S V U →
            SliceCriticalPointLocalBounds a θ K₂ s S V U
end BlockAverages
end YangMills.Construction
end
