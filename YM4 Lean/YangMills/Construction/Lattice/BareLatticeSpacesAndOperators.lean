import YangMills.Construction.Lattice.CovariantSiteOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.Bare
open Set YangMills.Construction.Matrices
variable {L m : ℕ} {j : ℤ}
def siteSpace (X : Set (FourTorus L m)) : Set (Site L m j → ComplexMatrix2) :=
  {f | IsSiteField complexLieAlgebra f ∧ zeroExtendSiteField X f = f}
def bondFormSpace (X : Set (FourTorus L m)) : Set (Bond L m j → ComplexMatrix2) :=
  {A | IsBondForm complexLieAlgebra A ∧ (bondsInside X).indicator A = A}
def siteInnerOn (X : Set (FourTorus L m)) (ξ : ℝ) (f g : Site L m j → ComplexMatrix2) : ℂ :=
  siteInner ξ (zeroExtendSiteField X f) (zeroExtendSiteField X g)
def bondFormInnerOn (X : Set (FourTorus L m)) (ξ : ℝ) (A B : Bond L m j → ComplexMatrix2) : ℂ :=
  bondFormInner ξ ((bondsInside X).indicator A) ((bondsInside X).indicator B)
def transposeWith {V W : Type*} [Nonempty V] (𝒱 : Set V) (p : V → V → ℂ) (q : W → W → ℂ)
    (T : V → W) (w : W) : V :=
  Classical.epsilon fun v => v ∈ 𝒱 ∧ ∀ u ∈ 𝒱, p v u = q w (T u)
abbrev IsComplexGaugeFieldInside (X : Set (FourTorus L m)) (U : Bond L m j → ComplexMatrix2) :
    Prop :=
  IsGaugeField complexGaugeGroup (bondsInside X) U
def covGradientInside (X : Set (FourTorus L m)) (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    (f : Site L m j → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  (bondsInside X).indicator (covGradient X ξ U f)
def covGradientTranspose (X : Set (FourTorus L m)) (ξ : ℝ) (U A : Bond L m j → ComplexMatrix2) :
    Site L m j → ComplexMatrix2 :=
  transposeWith (siteSpace X) (siteInnerOn X ξ) (bondFormInnerOn X ξ)
    (covGradientInside X ξ U) A
def bondsInsideFrom (X : Set (FourTorus L m)) (x : Site L m j) : Set (Bond L m j) :=
  {b | b ∈ bondsInside X ∧ b.source = x}
def degreeInside (X : Set (FourTorus L m)) (x : Site L m j) : ℕ := (bondsInsideFrom X x).ncard
def dirichletCovLaplacian (X : Set (FourTorus L m)) (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    (f : Site L m j → ComplexMatrix2) : Site L m j → ComplexMatrix2 :=
  (sitesIn X).indicator fun x => (((ξ⁻¹) ^ 2 : ℝ) : ℂ) •
    ((8 : ℂ) • f x - ∑ᶠ (b : Bond L m j) (_ : b ∈ bondsInsideFrom X x),
      ComplexMatrix2.conjugateBy (U b) (f b.target))
end YangMills.Construction.PeriodicLattice.Bare
