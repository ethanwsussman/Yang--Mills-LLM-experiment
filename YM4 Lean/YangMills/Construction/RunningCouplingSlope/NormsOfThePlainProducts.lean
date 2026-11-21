import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import YangMills.Construction.Towers.AveragesAreContractions
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def MeanKernelNormBounds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ C : ℝ, 0 < ρ ∧ 1 ≤ C ∧
    ∀ n k : ℕ, 0 < n → 1 ≤ k →
    ∀ (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) (t : ℝ), 0 ≤ t → t ≤ ρ →
      (∀ j < k, meanIterate U j ∈ Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup) →
      (∀ j < k, ∀ b, Matrices.ComplexMatrix2.operatorNorm (meanIterate U j b - 1) ≤
        20 * Tower.meshAt L k j * t) →
      Tower.SmoothingContraction.TorusOpNormLE (Tower.finestMesh L k) (Tower.meshAt L k k)
        (meanKernelQ L n k U) C ∧
      Tower.SmoothingContraction.TorusOpNormLE (Tower.finestMesh L k) (Tower.meshAt L k k)
        (meanKernelR L n k U) C ∧
      ∀ s m : ℕ, s + m = k →
        Tower.SmoothingContraction.TorusOpNormLE (Tower.meshAt L k s) (Tower.meshAt L k k)
          (meanKernelFrom L n k U s m) C
end YangMills.Construction.RunningCouplingSlope
end
