import YangMills.Construction.Lattice.GaugeFunctionalOneStepEstimates
import YangMills.Construction.Lattice.NumbersOfTheStraightenedAverage
import YangMills.Construction.Lattice.TowersOverSetsOfSites
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def orderKGaugeFactor (L : ℕ) : ℝ := 2 + 32 * recursionStepConstant L
def orderKCurvatureThreshold (L : ℕ) : ℝ :=
  min (straightenedCurvatureThreshold L)
    ((L : ℝ) ^ 2 / (4 * recursionStepConstant L * orderKGaugeFactor L))
def orderKGaugeRadius (L : ℕ) : ℝ :=
  min (straightenedRadius L / 4)
    (min ((L : ℝ) ^ 2 / (80 * recursionStepConstant L))
      (min (recursionStepAngle L / 8)
        (min (recursionStepRadius / orderKGaugeFactor L) (stepBondRadius L / 32))))
def orderKGaugeConstant (L : ℕ) : ℝ :=
  orderKGaugeFactor L * (16 * recursionStepConstant L * (L : ℝ)⁻¹ + 1)
def composedBlockAverage (U₀ : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (θ : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    (n : ℕ) → SiteAtLevel L m K n → Matrices.ComplexMatrix2
  | 0 => θ
  | n + 1 => covariantBlockAverage (iteratedAverage .centred n U₀) (composedBlockAverage U₀ θ n)
def ancestorSite (j : ℕ) (x : SiteAtLevel L m K 0) : SiteAtLevel L m K j :=
  Classical.epsilon fun z : SiteAtLevel L m K j => x ∈ blockSitesAtLevel 0 z
def ancestorTransport (U₀ : BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
    (x : SiteAtLevel L m K 0) : ℕ → Matrices.ComplexMatrix2
  | 0 => 1
  | n + 1 => contourHolonomy AveragingScheme.centred (iteratedAverage .centred n U₀)
      (ancestorSite (n + 1) x : SiteAtLevel L m K (n + 1)) (ancestorSite n x : SiteAtLevel L m K n) *
    ancestorTransport U₀ x n
end YangMills.Construction.PeriodicLattice
