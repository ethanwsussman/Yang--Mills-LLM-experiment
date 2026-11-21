import YangMills.Construction.Lattice.BlockAveraging
import YangMills.Construction.Thresholds.DegreeFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def nearIdentityIndicator (ε : ℝ) (w : Matrices.ComplexMatrix2) : ℝ :=
  open Classical in if Matrices.ComplexMatrix2.operatorNorm (w - 1) < ε then 1 else 0
def traceDeficit (w : Matrices.ComplexMatrix2) : ℝ :=
  1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace w).re
def axialNormalizer (x ε : ℝ) : ℝ :=
  ∫ u : Matrices.ComplexMatrix2.specialUnitary,
    nearIdentityIndicator ε (u : Matrices.ComplexMatrix2) *
      Real.exp (-x * traceDeficit (u : Matrices.ComplexMatrix2)) ∂Matrices.ComplexMatrix2.haarProb
def blockSitesExceptCenter (K k : ℕ) (y : SiteAtLevel L m K (k + 1)) :
    Set (SiteAtLevel L m K k) :=
  {z | z ∈ sitesInBlock (levelDepth K k) y ∧ (z : FourTorus L m) ≠ y}
def HasOffCenterContours (K k : ℕ) (Q : Set (SiteAtLevel L m K (k + 1)))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  ∀ y ∈ Q, ∀ z ∈ blockSitesExceptCenter K k y, HasContourMean V y z
def axialGaugeFactor (A₀ : ℝ) (p₀ : ℕ) (x : ℕ → ℝ) (K k : ℕ)
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (Q : Set (SiteAtLevel L m K (k + 1))) : ℝ :=
  open Classical in
  if HasOffCenterContours K k Q V then
    ∏ᶠ y ∈ Q, ∏ᶠ z ∈ blockSitesExceptCenter K k y,
      nearIdentityIndicator (Thresholds.epsThreshold A₀ p₀ x k) (meanContourHolonomy V y z) /
          axialNormalizer (x k) (Thresholds.epsThreshold A₀ p₀ x k) *
        Real.exp (-x k * traceDeficit (meanContourHolonomy V y z))
  else 0
def axialGaugeFunction (K k : ℕ) (Q : Set (SiteAtLevel L m K (k + 1)))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : ℝ :=
  ∑ᶠ y ∈ Q, ∑ᶠ z ∈ blockSitesExceptCenter K k y, traceDeficit (meanContourHolonomy V y z)
end PeriodicLattice
end YangMills.Construction
