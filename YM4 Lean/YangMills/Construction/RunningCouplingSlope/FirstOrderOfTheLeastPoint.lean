import YangMills.Construction.RunningCouplingSlope.TriplesOfTheChain
import YangMills.Construction.Towers.SignsOfTheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
open Tower.CriticalBranchResponse
variable {L n k : ℕ}
def linearChain (ξ : LevelForms L n k) : (j : ℕ) → Tower.Edge L n k j → Matrices.ComplexMatrix2
  | 0 => ξ.1
  | j + 1 =>
    if h : j < k then
      Tower.crossingSmoothing L n k j (linearChain ξ j) + (ξ.2 ⟨j, h⟩ : Tower.Edge L n k (j + 1) → Matrices.ComplexMatrix2)
    else 0
def IsLinearConstraintAdjoint (T : Tower.edgeFormSpace L n k k →ₗ[ℝ] LevelForms L n k) : Prop :=
  ∀ (μ : Tower.edgeFormSpace L n k k) (ξ : LevelForms L n k), levelPairing (formValues (T μ)) (formValues ξ) =
    (Tower.edgeFormPairing (μ : Tower.Edge L n k k → Matrices.ComplexMatrix2) (linearChain ξ k)).re
def linearConstraintAdjoint (L n k : ℕ) : Tower.edgeFormSpace L n k k →ₗ[ℝ] LevelForms L n k :=
  Classical.epsilon IsLinearConstraintAdjoint
def IsFirstVariation (a : ℝ) (B : Tower.edgeFormSpace L n k k) (t : LevelTriple L n k) : Prop :=
  ∃ (N : ℕ) (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) (c : ℝ → Fin N → ℝ),
    c 0 = 0 ∧ HasDerivAt c (e.symm t) 0 ∧ ∀ᶠ s in 𝓝 (0 : ℝ),
      IsMinimizerOver a
          (PeriodicLattice.expTwist (s • (B : Tower.Edge L n k k → Matrices.ComplexMatrix2)) fun _ => 1)
          (expMove (e (c s)).1 (unitPoint L n k)) ∧
        IsLevelGradient (chainAction a) (expMove (e (c s)).1 (unitPoint L n k)) (e (c s)).2.1 ∧
        IsTopMultiplier (expMove (e (c s)).1 (unitPoint L n k)) (e (c s)).2.1 (e (c s)).2.2
def MinimizerFirstVariation : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ B : Tower.edgeFormSpace L n k k,
      (∃ t, IsFirstVariation a B t) ∧
      ∀ t : LevelTriple L n k, IsFirstVariation a B t →
        t.2.1 = linearConstraintAdjoint L n k t.2.2 ∧
        (∀ i, t.1.2 i = a⁻¹ • (linearConstraintAdjoint L n k t.2.2).2 i) ∧
        ∃ (G : Tower.edgeFormSpace L n k k) (l : Tower.vertexFunctionSpace L n k 0),
          (G : Tower.Edge L n k k → Matrices.ComplexMatrix2) = linearChain (0, t.1.2) k ∧
          (t.2.2 : Tower.Edge L n k k → Matrices.ComplexMatrix2) =
            periodicDefect L n k ((B : Tower.Edge L n k k → Matrices.ComplexMatrix2) - G) ∧
          (t.1.1 : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) =
            (meshScaledResponse L n k ((B : Tower.Edge L n k k → Matrices.ComplexMatrix2) - G) :
                Tower.Edge L n k 0 → Matrices.ComplexMatrix2) +
              Tower.vertexCoboundary (l : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)
end YangMills.Construction.RunningCouplingSlope
end
