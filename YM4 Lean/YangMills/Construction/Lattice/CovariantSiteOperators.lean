import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
open Set
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def zeroExtendSiteField (X : Set (FourTorus L m)) (f : Site L m j → ComplexMatrix2) :
    Site L m j → ComplexMatrix2 :=
  (sitesIn X).indicator f
def zeroExtendBondForm (X : Set (FourTorus L m)) (A : Bond L m j → ComplexMatrix2) :
    Bond L m j → ComplexMatrix2 :=
  (bondsMeeting X).indicator A
def bondFormOfPositive (a : Bond L m j → ComplexMatrix2) (b : Bond L m j) : ComplexMatrix2 :=
  open Classical in if b.IsPositivelyOriented then a b else -a b.opposite
def covGradient (X : Set (FourTorus L m)) (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    (f : Site L m j → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  zeroExtendBondForm X (bondFormOfPositive fun b =>
    covDeriv ξ U b.axis (zeroExtendSiteField X f) b.source)
def covDivergence (X : Set (FourTorus L m)) (ξ : ℝ) (U A : Bond L m j → ComplexMatrix2) :
    Site L m j → ComplexMatrix2 :=
  Classical.epsilon fun B => IsSiteField complexLieAlgebra B ∧ zeroExtendSiteField X B = B ∧
    ∀ f, IsSiteField complexLieAlgebra f →
      siteInner ξ B (zeroExtendSiteField X f) =
        bondFormInner ξ (zeroExtendBondForm X A) (covGradient X ξ U f)
def covLaplacian (X : Set (FourTorus L m)) (ξ : ℝ) (U : Bond L m j → ComplexMatrix2)
    (f : Site L m j → ComplexMatrix2) : Site L m j → ComplexMatrix2 :=
  covDivergence X ξ U (covGradient X ξ U f)
def conjugateBondForm (u : Site L m j → ComplexMatrix2) (A : Bond L m j → ComplexMatrix2) :
    Bond L m j → ComplexMatrix2 :=
  bondFormOfPositive fun b => ComplexMatrix2.conjugateBy (u b.source) (A b)
end YangMills.Construction.PeriodicLattice
