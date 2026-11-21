import YangMills.Construction.Lattice.AveragingOperatorsOfASeparatedSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice
namespace SeparatedSequences
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
abbrev covGradAt (W : FineBond L m S → Matrices.ComplexMatrix2)
    (l : SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) :
    BondAtLevel L m S.levels 0 → Matrices.ComplexMatrix2 :=
  Bare.covGradientInside (Ω 0) (S.finestMesh L) W l
abbrev dirichletLapAt (W : FineBond L m S → Matrices.ComplexMatrix2)
    (l : SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) :
    SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2 :=
  Bare.dirichletCovLaplacian (Ω 0) (S.finestMesh L) W l
def layerValueOnTops (W : FineBond L m S → Matrices.ComplexMatrix2)
    (l : SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2) :
    ↥(layerPoints S Ω) → Matrices.ComplexMatrix2 :=
  fun y => layerSiteValue S Ω W l y
def weightSmul (a : ↥(layerPoints S Ω) → ℂ) (μ : ↥(layerPoints S Ω) → Matrices.ComplexMatrix2) :
    ↥(layerPoints S Ω) → Matrices.ComplexMatrix2 :=
  fun y => a y • μ y
end SeparatedSequences
end YangMills.Construction
end
