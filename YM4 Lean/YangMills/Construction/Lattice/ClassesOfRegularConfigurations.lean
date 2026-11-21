import YangMills.Construction.Lattice.ElementsAndLocalScales
import YangMills.Construction.Lattice.TowersAndMinimalConfigurations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m : ℕ}
section
variable {K : ℕ}
def coboundaryAt (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (X : PlaquetteAtLevel L m K 0 → ComplexMatrix2) (x : SiteAtLevel L m K 0) (μ : Fin 4) :
    ComplexMatrix2 :=
  (∑ ν ∈ Finset.Iio μ,
    (ComplexMatrix2.conjugateBy (U (Bond.forwardFrom (x - unitStep L m (levelDepth K 0) ν) ν))⁻¹
        (plaquetteFormOf X ν μ (x - unitStep L m (levelDepth K 0) ν)) -
      plaquetteFormOf X ν μ x)) -
  ∑ ν ∈ Finset.Ioi μ,
    (ComplexMatrix2.conjugateBy (U (Bond.forwardFrom (x - unitStep L m (levelDepth K 0) ν) ν))⁻¹
        (plaquetteFormOf X μ ν (x - unitStep L m (levelDepth K 0) ν)) -
      plaquetteFormOf X μ ν x)
def transposeDerivAt (η : ℝ) (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (X : PlaquetteAtLevel L m K 0 → ComplexMatrix2) (x : SiteAtLevel L m K 0) (μ : Fin 4) :
    ComplexMatrix2 :=
  ((η⁻¹ : ℝ) : ℂ) • coboundaryAt U X x μ
end
def transposeRegularSet (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (r : ℕ → ℝ) :
    Set (BondAtLevel L m K 0 → ComplexMatrix2) :=
  {U | U ∈ gaugeFieldsInside K (Ω 0) ∧
    (∀ p : PlaquetteAtLevel L m K 0, (CorneredObject.ofPlaquette p).LiesIn (Ω 0) →
      ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) <
        r ((CorneredObject.ofPlaquette p).localLevel k Ω) * finestMeshInLevelUnits L k ^ 2 *
          ((CorneredObject.ofPlaquette p).localMesh k Ω)⁻¹ ^ 2) ∧
    ∀ (x : SiteAtLevel L m K 0) (μ : Fin 4), IsFullBondIn (Ω 0) (Bond.forwardFrom x μ) →
      ComplexMatrix2.operatorNorm
          (transposeDerivAt (finestMeshInLevelUnits L k) U (plaquetteHolonomy U) x μ) <
        r ((CorneredObject.ofBond (Bond.forwardFrom x μ)).localLevel k Ω) *
          finestMeshInLevelUnits L k ^ 2 *
          ((CorneredObject.ofBond (Bond.forwardFrom x μ)).localMesh k Ω)⁻¹ ^ 3}
def transposeRegularSetConst (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (r : ℝ) :
    Set (BondAtLevel L m K 0 → ComplexMatrix2) :=
  transposeRegularSet K k Ω fun _ => r
end YangMills.Construction.PeriodicLattice
