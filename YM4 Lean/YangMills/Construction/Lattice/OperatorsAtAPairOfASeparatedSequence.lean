import YangMills.Construction.Lattice.ExpansionPairingAndSchemeOperators
import Mathlib
import YangMills.Construction.Lattice.AveragingOperatorsOfASeparatedSequence
import YangMills.Construction.Lattice.PairedSpacesOfASequenceAndTheirTransposes
set_option autoImplicit false

section
open Set MeasureTheory
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
section DeterminingSet
variable {L m K : ℕ}
open Classical in
def fieldOnBonds (B : Set (LeveledBond L m K)) (r : LeveledBond L m K → Matrices.ComplexMatrix2) :
    LeveledBond L m K → Matrices.ComplexMatrix2 :=
  fun q => if q ∈ positiveLeveledBonds B then r q
    else if q ∈ B ∧ q.flip ∈ positiveLeveledBonds B then -r q.flip else 0
end DeterminingSet
end YangMills.Construction.PeriodicLattice
end
end

open YangMills.Construction.PeriodicLattice
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.SeparatedSequences
variable {L m : ℕ} (S : ScaleData) (Ω : ℕ → Set (FourTorus L m))
def topWeight (y : ↥(layerPoints S Ω)) : ℂ :=
  ((Lattice.averagingMassCoefficient L (layerLevel S Ω y) * (layerPointMesh S Ω y ^ 2)⁻¹ : ℝ) : ℂ)
open Classical in
def interiorOutwardExtend
    (r : PositiveLevelBonds S (BondKinds.interiorOutwardSet S Ω) → Matrices.ComplexMatrix2) :
    LeveledBond L m S.levels → Matrices.ComplexMatrix2 :=
  fieldOnBonds (BondKinds.interiorOutwardSet S Ω) fun q =>
    if h : q ∈ positiveLeveledBonds (BondKinds.interiorOutwardSet S Ω) then r ⟨q, h⟩ else 0
def quadraticPart (F : (FineBond L m S → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2)
    (A : FineBond L m S → Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  (1 / 2 : ℂ) • iteratedDeriv 2 (fun s : ℂ => F (s • A)) 0
def straightenedAverageAt {T : Set (Σ j : ℕ, BondAtLevel L m S.levels j)}
    (U : FineBond L m S → Matrices.ComplexMatrix2) (q : PositiveLevelBonds S T)
    (A : FineBond L m S → Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  (twistedStraightenedAverage q.1.2 U A q.1.1 (blockPairTopBond q.1.2 q.2.2) : Matrices.ComplexMatrix2)
def quadraticExpansionValue (U A : FineBond L m S → Matrices.ComplexMatrix2)
    (q : PositiveLevelBonds S (BondKinds.interiorOutwardSet S Ω)) : Matrices.ComplexMatrix2 :=
  (((S.levelMesh L q.1.1)⁻¹ : ℝ) : ℂ) •
    quadraticPart S (straightenedAverageAt S U q) (levelUnitForm S q.1.1 A)
def quadraticExpansions (U A : FineBond L m S → Matrices.ComplexMatrix2) :
    LeveledBond L m S.levels → Matrices.ComplexMatrix2 :=
  interiorOutwardExtend S Ω (quadraticExpansionValue S Ω U A)
section Operators
variable [∀ (n : ℕ) (c : BondAtLevel L m S.levels (n + 1)),
  Fintype (PositiveBondsOf (doubleBlockSymmetricSet c))]
def rowAverage (U A : FineBond L m S → Matrices.ComplexMatrix2) :
    LeveledBond L m S.levels → Matrices.ComplexMatrix2 :=
  interiorOutwardExtend S Ω (interiorOutwardExpansions S Ω U A)
def rowAverageTranspose (U : FineBond L m S → Matrices.ComplexMatrix2) :
    (LeveledBond L m S.levels → Matrices.ComplexMatrix2) → FineBond L m S → Matrices.ComplexMatrix2 :=
  PairedFunctionSpace.transpose (bareFormPaired S Ω) (expansionPaired S Ω) (rowAverage S Ω U)
end Operators
end YangMills.Construction.SeparatedSequences
end
