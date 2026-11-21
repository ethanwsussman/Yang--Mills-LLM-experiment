import YangMills.Construction.Lattice.CovariantSiteOperators
import YangMills.Construction.Lattice.LieValuedBondFunctions
import YangMills.Construction.Lattice.WeightedWilsonActions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
namespace PeriodicLattice
variable {L m K : ℕ}
def IsBareFormEnergyData (K k : ℕ) (U₀ : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  k ≤ K ∧ U₀ ∈ gaugeFieldsAtLevel L m K 0
abbrev bareCovGradient (k : ℕ) (U₀ : BondAtLevel L m K 0 → ComplexMatrix2)
    (f : SiteAtLevel L m K 0 → ComplexMatrix2) : BondAtLevel L m K 0 → ComplexMatrix2 :=
  covGradient Set.univ (finestMeshInLevelUnits L k) U₀ f
abbrev bareCovExteriorDeriv (k : ℕ) (U₀ A : BondAtLevel L m K 0 → ComplexMatrix2) :
    Fin 4 → Fin 4 → SiteAtLevel L m K 0 → ComplexMatrix2 :=
  covExteriorDeriv (finestMeshInLevelUnits L k) U₀ A
abbrev bareCovDivergence (k : ℕ) (U₀ A : BondAtLevel L m K 0 → ComplexMatrix2) :
    SiteAtLevel L m K 0 → ComplexMatrix2 :=
  covDivergence Set.univ (finestMeshInLevelUnits L k) U₀ A
abbrev bareCovExteriorDerivAdjoint (k : ℕ) (U₀ : BondAtLevel L m K 0 → ComplexMatrix2)
    (X : Fin 4 → Fin 4 → SiteAtLevel L m K 0 → ComplexMatrix2) :
    BondAtLevel L m K 0 → ComplexMatrix2 :=
  covExteriorDerivAdjoint (finestMeshInLevelUnits L k) U₀ X
def bareFormEnergy (k : ℕ) (U₀ A : BondAtLevel L m K 0 → ComplexMatrix2) : ℂ :=
  totalEnergy (bareTwist k A U₀)
def IsBareFormEnergyGradient (k : ℕ) (U₀ A B : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  IsBondForm complexLieAlgebra B ∧ ∀ δA : BondAtLevel L m K 0 → ComplexMatrix2,
    IsBondForm complexLieAlgebra δA →
      HasDerivAt (fun t : ℝ => bareFormEnergy k U₀ (A + (t : ℂ) • δA))
        (bondFormInner (finestMeshInLevelUnits L k) B δA) 0
def bareFormEnergyGradient (k : ℕ) (U₀ A : BondAtLevel L m K 0 → ComplexMatrix2) :
    BondAtLevel L m K 0 → ComplexMatrix2 :=
  Classical.epsilon (IsBareFormEnergyGradient k U₀ A)
end PeriodicLattice
end YangMills.Construction
