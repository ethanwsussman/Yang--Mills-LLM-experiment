import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BondsWithinSiteSets
import YangMills.Construction.Lattice.BoxesOfOrder
import YangMills.Construction.Lattice.CoordinateCombs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m K n : ℕ}
def combTransport (W : BondAtLevel L m K n → ComplexMatrix2) (y x : SiteAtLevel L m K n) :
    ComplexMatrix2 :=
  pathHolonomy W (coordinateComb y x)
def offsetNormBefore (y x : SiteAtLevel L m K n) (ν : Fin 4) : ℝ :=
  ∑ μ ∈ Finset.Iio ν, ((|chartOffset y x μ| : ℤ) : ℝ)
def offsetL1Norm (y x : SiteAtLevel L m K n) : ℝ :=
  ∑ μ, ((|chartOffset y x μ| : ℤ) : ℝ)
def CombTransportOnBox.Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n ≤ K →
    ∀ (Y : Set (SiteAtLevel L m K n)) (s : ℕ) (y : SiteAtLevel L m K n)
      (W : BondAtLevel L m K n → ComplexMatrix2) (ϖ : ℝ),
      IsSiteBox (levelDepth K n) Y → (∀ μ, coordCount μ Y ≤ s + 1) → y ∈ Y →
      IsGaugeFieldWithin Y W → 0 ≤ ϖ →
      (∀ p : PlaquetteAtLevel L m K n, p.LiesIn Y →
        ComplexMatrix2.operatorNorm (plaquetteHolonomy W p - 1) ≤ ϖ) →
      combTransport W y y = 1 ∧
      (∀ (x : SiteAtLevel L m K n) (ν : Fin 4), (Bond.forwardFrom x ν).LiesIn Y →
        ComplexMatrix2.operatorNorm
            (gaugeTransform (combTransport W y) W (Bond.forwardFrom x ν) - 1) ≤
            ϖ * offsetNormBefore y x ν ∧
          ϖ * offsetNormBefore y x ν ≤ min (3 * (s : ℝ)) (offsetL1Norm y x) * ϖ) ∧
      (3 * (s : ℝ) * ϖ < 2 → ∃ a : LieBondFieldWithin Y, IsCompactValued a ∧
        (∀ v ∈ (bondsWithin Y).bonds,
          gaugeTransform (combTransport W y) W v =
            ComplexMatrix2.matExp (Complex.I • (a.eval v : ComplexMatrix2))) ∧
        supOperatorNorm a ≤ 3 * Real.pi / 2 * s * ϖ) ∧
      ∀ (Γ₁ Γ₂ : List (BondAtLevel L m K n)) (z z' : SiteAtLevel L m K n),
        IsBondPathFromTo Γ₁ z z' → IsBondPathFromTo Γ₂ z z' →
        (∀ v ∈ Γ₁, v.LiesIn Y) → (∀ v ∈ Γ₂, v.LiesIn Y) →
        ComplexMatrix2.operatorNorm (pathHolonomy W Γ₁ - pathHolonomy W Γ₂) ≤
          3 * (s : ℝ) * ϖ * ((Γ₁.length : ℝ) + Γ₂.length)
end YangMills.Construction.PeriodicLattice
