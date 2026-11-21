import YangMills.Construction.Lattice.LieValuedBondFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice
def curvatureDivergence {L m K : ℕ} (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    BondAtLevel L m K 0 → ComplexMatrix2 :=
  matrixCovExteriorDerivTranspose (finestMeshInLevelUnits L k) U
    (plaquetteFormOf (plaquetteHolonomy U))
def smallCurvatureConfigs (L m K k : ℕ) (r : ℝ) : Set (BondAtLevel L m K 0 → ComplexMatrix2) :=
  {U | U ∈ gaugeFieldsAtLevel L m K 0 ∧
    (∀ p : PlaquetteAtLevel L m K 0,
      ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) <
        r * finestMeshInLevelUnits L k ^ 2) ∧
    ∀ b : BondAtLevel L m K 0,
      ComplexMatrix2.operatorNorm (curvatureDivergence k U b) < r * finestMeshInLevelUnits L k ^ 2}
end PeriodicLattice
end YangMills.Construction
