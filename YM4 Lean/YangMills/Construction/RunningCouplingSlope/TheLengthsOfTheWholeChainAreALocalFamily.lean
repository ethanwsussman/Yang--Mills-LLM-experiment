import YangMills.Construction.RunningCouplingSlope.HessianOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.MatricesOfTheWholeChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower Conventions
def NoiseRadiusMatrixIsLocal : Prop :=
  ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ M θ : ℝ, 0 < M ∧ 0 < θ ∧ ∀ᶠ n in atTop,
      ∀ [Fintype (NoiseIndex L n k)] [DecidableEq (NoiseIndex L n k)],
        IsUnit (Matrix.det (noiseRadiusMatrix (0 : LevelTriple L n k))) ∧
        ‖(noiseRadiusMatrix (0 : LevelTriple L n k))⁻¹‖ ≤ M ∧
        ∀ (y y' : Vertex L n k k) (τ τ' : LevelTriple L n k),
          TripleSupportedInCell y τ → TripleSupportedInCell y' τ' →
          tripleNormSq τ ≤ 1 → tripleNormSq τ' ≤ 1 →
          IsLocalAlongCellPair noiseIndexCell (fun s t => noiseRadiusMatrix (s • τ + t • τ')) y y' M θ
end YangMills.Construction.RunningCouplingSlope
end
