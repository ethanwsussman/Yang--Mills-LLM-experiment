import YangMills.Construction.Lattice.BareLatticeSpacesAndOperators
import YangMills.Construction.Lattice.ExpansionPairingAndSchemeOperators
import YangMills.Construction.Lattice.PairingOfFunctionsOnTheTops
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice
namespace SeparatedSequences
structure PairedFunctionSpace where
  Carrier : Type
  [nonempty : Nonempty Carrier]
  members : Set Carrier
  pairing : Carrier → Carrier → ℂ
attribute [instance] PairedFunctionSpace.nonempty
def PairedFunctionSpace.transpose (P Q : PairedFunctionSpace) (T : P.Carrier → Q.Carrier) :
    Q.Carrier → P.Carrier :=
  Bare.transposeWith P.members P.pairing Q.pairing T
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def bareSitePaired : PairedFunctionSpace where
  Carrier := SiteAtLevel L m S.levels 0 → Matrices.ComplexMatrix2
  members := Bare.siteSpace (Ω 0)
  pairing := Bare.siteInnerOn (Ω 0) (S.finestMesh L)
def bareFormPaired : PairedFunctionSpace where
  Carrier := BondAtLevel L m S.levels 0 → Matrices.ComplexMatrix2
  members := Bare.bondFormSpace (Ω 0)
  pairing := Bare.bondFormInnerOn (Ω 0) (S.finestMesh L)
def topPaired : PairedFunctionSpace where
  Carrier := ↥(layerPoints S Ω) → Matrices.ComplexMatrix2
  members := {μ | ∀ y, μ y ∈ complexLieAlgebra}
  pairing := topPointPairing S Ω
def expansionPaired : PairedFunctionSpace where
  Carrier := LeveledBond L m S.levels → Matrices.ComplexMatrix2
  members := outwardFields S Ω
  pairing := outwardPairing S Ω
end SeparatedSequences
end YangMills.Construction
