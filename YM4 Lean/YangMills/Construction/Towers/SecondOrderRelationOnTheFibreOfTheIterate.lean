import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import YangMills.Construction.Towers.ExpansionOfTheIterateInTheLeftChart
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
def FibreSecondOrderRelation : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k k) fun W =>
      ∀ (X : ℝ → edgeFormSpace L n k 0) (B ξ : edgeFormSpace L n k 0),
        complexIterDeriv L n k k (chainBottom W) B = 0 →
        Tendsto X (𝓝 0) (𝓝 0) →
        ((fun t : ℝ => edgeFormNorm ((X t - t • B - (t ^ 2 / 2) • ξ : edgeFormSpace L n k 0) :
            Edge L n k 0 → Matrices.ComplexMatrix2)) =o[𝓝 0] fun t : ℝ => t ^ 2) →
        (∀ᶠ t in 𝓝 (0 : ℝ), smoothingIter L n k k
          (PeriodicLattice.expTwist (X t : Edge L n k 0 → Matrices.ComplexMatrix2)
            (chainBottom W)) = W) →
        ∀ c : PositiveEdge L n k k, complexIterDeriv L n k k (chainBottom W) ξ c =
          -iterQuadraticTerm (chainBottom W) B B c
end YangMills.Construction.Tower
end
