import YangMills.Construction.RunningCouplingSlope.TriplesOfTheChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def ChainFunctionEntriesAnalytic : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ (N : ℕ) (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k),
      (∀ᶠ w in 𝓝 (0 : Fin N → ℝ),
        ∃ q : QuadraticForm ℝ (LevelForms L n k), ∀ ξ,
          q ξ = gaugedRightValue a (expMove (e w).1 (unitPoint L n k)) (e w).2.1 (e w).2.2 ξ) ∧
      (∀ ξ : LevelForms L n k, AnalyticAt ℝ (fun w =>
        gaugedRightValue a (expMove (e w).1 (unitPoint L n k)) (e w).2.1 (e w).2.2 ξ) 0) ∧
      (∀ (ξ : LevelForms L n k) (C : edgeFormSpace L n k k), AnalyticAt ℝ (fun w =>
        (edgeFormPairing (C : Edge L n k k → Matrices.ComplexMatrix2)
          (shiftedGaugeMap (expMove (e w).1 (unitPoint L n k)) ξ :
            Edge L n k k → Matrices.ComplexMatrix2)).re) 0) ∧
      (∀ x y : vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k, AnalyticAt ℝ (fun w =>
        (traceFinsumPairing (x.1 : Vertex L n k 0 → Matrices.ComplexMatrix2)
          ((ghostBlockOperator (expMove (e w).1 (unitPoint L n k)) y).1 :
            Vertex L n k 0 → Matrices.ComplexMatrix2)).re +
        (traceFinsumPairing (x.2 : Vertex L n k k → Matrices.ComplexMatrix2)
          ((ghostBlockOperator (expMove (e w).1 (unitPoint L n k)) y).2 :
            Vertex L n k k → Matrices.ComplexMatrix2)).re) 0) ∧
      AnalyticAt ℝ (fun w => logRadiusSum (expMove (e w).1 (unitPoint L n k))) 0
end YangMills.Construction.RunningCouplingSlope
end
