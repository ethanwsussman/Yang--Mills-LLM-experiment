import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K : ℕ} {j : ℤ}
abbrev LieBondFunction (L m : ℕ) (j : ℤ) : Type :=
  PositivelyOrientedBond L m j → ↥Matrices.ComplexMatrix2.traceless
namespace LieBondFunction
open Classical in
def onBond (a : LieBondFunction L m j) (b : Bond L m j) : ↥Matrices.ComplexMatrix2.traceless :=
  if hb : b.IsPositivelyOriented then a ⟨b, hb⟩
  else if hr : b.opposite.IsPositivelyOriented then -a ⟨b.opposite, hr⟩
  else 0
def twist (a : LieBondFunction L m j) (W : Bond L m j → Matrices.ComplexMatrix2) :
    Bond L m j → Matrices.ComplexMatrix2 :=
  expTwist (fun b => (a.onBond b : Matrices.ComplexMatrix2)) W
def IsCompactValued (a : LieBondFunction L m j) : Prop :=
  ∀ b, (a b : Matrices.ComplexMatrix2) ∈ compactLieAlgebra
end LieBondFunction
def bareTwist (k : ℕ) (A U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  expTwist (fun b => ((finestMeshInLevelUnits L k : ℝ) : ℂ) • A b) U
def supOfOperatorNorms {ι : Type*} (f : ι → Matrices.ComplexMatrix2) : ℝ :=
  ⨆ i, Matrices.ComplexMatrix2.operatorNorm (f i)
def bondFormC1Norm (k : ℕ) (U₀ A : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : ℝ :=
  max (supOfOperatorNorms A)
    (⨆ x : SiteAtLevel L m K 0, covDerivNorm (finestMeshInLevelUnits L k) U₀ A x)
def matrixCovExteriorDerivTranspose (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2)
    (X : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2) :
    Bond L m j → Matrices.ComplexMatrix2 :=
  Classical.epsilon fun B => IsBondForm univ B ∧ ∀ A, IsBondForm univ A →
    bondFormInner ξ B A = plaquetteFormInner ξ X (covExteriorDeriv ξ U A)
def covDerivAdjointComponent (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2) (ν : Fin 4)
    (f : Site L m j → Matrices.ComplexMatrix2) (x : Site L m j) : Matrices.ComplexMatrix2 :=
  ((ξ⁻¹ : ℝ) : ℂ) •
    (Matrices.ComplexMatrix2.conjugateBy (U (Bond.forwardFrom (x - unitStep L m j ν) ν))⁻¹
      (f (x - unitStep L m j ν)) - f x)
def bondFormDivergenceSum (ξ : ℝ) (U A : Bond L m j → Matrices.ComplexMatrix2)
    (x : Site L m j) : Matrices.ComplexMatrix2 :=
  ∑ μ : Fin 4, covDerivAdjointComponent ξ U μ (bondFormComponent A μ) x
def plaquetteFormDivergenceSum (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2)
    (X : Fin 4 → Fin 4 → Site L m j → Matrices.ComplexMatrix2) (μ : Fin 4) (x : Site L m j) :
    Matrices.ComplexMatrix2 :=
  ∑ ν ∈ Finset.Iio μ, covDerivAdjointComponent ξ U ν (X ν μ) x -
    ∑ ν ∈ Finset.Ioi μ, covDerivAdjointComponent ξ U ν (X μ ν) x
def halfTracePairing (X Y : Matrices.ComplexMatrix2) : ℂ :=
  Matrices.ComplexMatrix2.halfTrace (X * Y)
end PeriodicLattice
end YangMills.Construction
