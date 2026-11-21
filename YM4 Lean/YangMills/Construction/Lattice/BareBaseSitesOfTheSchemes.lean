import YangMills.Construction.Averaging.OneStepToolboxData
import YangMills.Construction.Lattice.LowestBlockSite
import YangMills.Construction.Lattice.OneStepSchemes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def SchemeFinestBaseSites : Prop :=
  ∀ (d N L K m : ℕ) (G : Submonoid Matrices.ComplexMatrix2),
    Averaging.OneStep.Parameters d N L K m G →
    ∀ j : ℕ, j ≤ K → ∀ y : SiteAtLevel L m K j,
      (finestBaseSite .centred K j y : FourTorus L m) = (y : FourTorus L m) ∧
      (finestBaseSite .cornered K j y : FourTorus L m) = (lowestBlockSite j y : FourTorus L m)
end PeriodicLattice
end YangMills.Construction
