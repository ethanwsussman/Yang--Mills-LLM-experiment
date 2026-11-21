import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.AngleSphereAndPlaquetteBound
import YangMills.Construction.Lattice.AxialGauges
import YangMills.Construction.Lattice.BoxesOfOrder
import YangMills.Construction.Lattice.BoxesWithShellFreeBondsAndTrees
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open CollaredBox
def PotentialBoundOnRegularBox (c : ℝ) : Prop :=
  0 < c ∧
    ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ k : ℕ, k ≤ K →
      ∀ (M : ℕ) (P : Set (SiteAtLevel L m K k)) (B ε : ℝ)
        (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (r : SignedFrame),
        1 ≤ M → IsSiteBox (levelDepth K k) P → (∀ μ, coordCount μ P ≤ 100 * M) →
        IsSiteBox (levelDepth K k) (thickening P) → 0 ≤ B → 0 ≤ ε →
        IsGaugeFieldWithin (thickening P) V →
        (∀ p : PlaquetteAtLevel L m K k, p.LiesIn (thickening P) →
          Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy V p - 1) ≤
            B * (M : ℝ) ^ 5 * ε) →
        (∀ b ∈ rotatedAxialBoxTree r (levelDepth K k) P, V b = 1) →
        ∀ b : BondAtLevel L m K k, b.LiesIn P →
          Matrices.ComplexMatrix2.groupAngle (V b) ≤ c * B * (M : ℝ) ^ 6 * ε
def potentialBoundConstant : ℝ := Classical.epsilon PotentialBoundOnRegularBox
end YangMills.Construction.PeriodicLattice
end
