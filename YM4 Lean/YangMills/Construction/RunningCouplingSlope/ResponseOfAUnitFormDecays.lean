import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.CriticalBranchResponse
def UnitFormResponseDecays : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧
    ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n → ∀ v : Fin 4 → ℤ,
      (∀ b : Edge L n k 0,
        Matrices.ComplexMatrix2.operatorNorm
            ((periodicResponse L n k (pauliUnitForm L n k v) : Edge L n k 0 → Matrices.ComplexMatrix2) b) ≤
          C * Real.exp (-(θ * cellDist (fineVertexCell b.source) (cellOfCoords L n k v)))) ∧
      (∀ p : Face L n k 0,
        Matrices.ComplexMatrix2.operatorNorm (scaledEdgeCoboundary
            (periodicResponse L n k (pauliUnitForm L n k v) : Edge L n k 0 → Matrices.ComplexMatrix2) p) ≤
          C * Real.exp (-(θ * cellDist (fineVertexCell p.origin) (cellOfCoords L n k v)))) ∧
      ∀ b : Edge L n k 0, ∃ x : ℝ,
        (periodicResponse L n k (pauliUnitForm L n k v) : Edge L n k 0 → Matrices.ComplexMatrix2) b =
          (x : ℂ) • Matrices.ComplexMatrix2.pauliFamily 2
end YangMills.Construction.RunningCouplingSlope
end
