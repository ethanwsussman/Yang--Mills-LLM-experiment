import YangMills.Construction.Lattice.ConfigurationAndWeightsOnTheTops
import YangMills.Construction.Lattice.PairedSpacesOfASequenceAndTheirTransposes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice Matrices
namespace SeparatedSequences
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def layerValueAdjoint (W : FineBond L m S → ComplexMatrix2) :
    (↥(layerPoints S Ω) → ComplexMatrix2) → SiteAtLevel L m S.levels 0 → ComplexMatrix2 :=
  PairedFunctionSpace.transpose (bareSitePaired S Ω) (topPaired S Ω) (layerValueOnTops S Ω W)
abbrev covDivAt (W A : FineBond L m S → ComplexMatrix2) : SiteAtLevel L m S.levels 0 → ComplexMatrix2 :=
  Bare.covGradientTranspose (Ω 0) (S.finestMesh L) W A
def weightedLaplacian (W : FineBond L m S → ComplexMatrix2) (a : ↥(layerPoints S Ω) → ℂ)
    (u : SiteAtLevel L m S.levels 0 → ComplexMatrix2) : SiteAtLevel L m S.levels 0 → ComplexMatrix2 :=
  dirichletLapAt S Ω W u +
    layerValueAdjoint S Ω W (weightSmul S Ω a (layerValueOnTops S Ω W u))
end SeparatedSequences
end YangMills.Construction
end
