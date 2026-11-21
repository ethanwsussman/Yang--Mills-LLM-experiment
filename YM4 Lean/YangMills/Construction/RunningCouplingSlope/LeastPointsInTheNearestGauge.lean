import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
variable {L n k : ℕ}
def distanceGaugeVariation (U : Edge L n k 0 → Matrices.ComplexMatrix2)
    (κ : Vertex L n k 0 → Matrices.ComplexMatrix2) : ℝ :=
  ∑ᶠ b : PositiveEdge L n k 0, (Matrices.ComplexMatrix2.halfTrace (Complex.I • κ b.1.source * U b.1 -
    U b.1 * Complex.I • κ b.1.target)).re
def NearestGaugeMinimizerExists : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ (B : edgeFormSpace L n k k) (ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      ∃ ξ : LevelForms L n k,
        (∀ b, Matrices.ComplexMatrix2.operatorNorm ((ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2) b) < ε) ∧
        (∀ (i : Fin k) (b : Edge L n k ((i : ℕ) + 1)),
          Matrices.ComplexMatrix2.operatorNorm
            ((ξ.2 i : Edge L n k ((i : ℕ) + 1) → Matrices.ComplexMatrix2) b) < ε) ∧
        IsMinimizerOver a
          (PeriodicLattice.expTwist (s • (B : Edge L n k k → Matrices.ComplexMatrix2)) fun _ => 1)
          (expMove ξ (unitPoint L n k)) ∧
        ∀ κ ∈ topVanishingGauges L n k,
          distanceGaugeVariation (expMove ξ (unitPoint L n k)).fine
            (κ : Vertex L n k 0 → Matrices.ComplexMatrix2) = 0
end YangMills.Construction.RunningCouplingSlope
end
