import YangMills.Construction.Lattice.OneStepCovarianceAndDomains
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
def fourCornerBlockSites (p : PlaquetteAtLevel L m K (n + 1)) : Set (SiteAtLevel L m K n) :=
  sitesIn (refinedBlockUnion 1 p.vertices)
def firstEdge (p : PlaquetteAtLevel L m K (n + 1)) : BondAtLevel L m K (n + 1) :=
  Bond.forwardFrom p.origin p.firstAxis
def secondEdge (p : PlaquetteAtLevel L m K (n + 1)) : BondAtLevel L m K (n + 1) :=
  Bond.forwardFrom (p.origin + unitStep L m (levelDepth K (n + 1)) p.firstAxis) p.secondAxis
def thirdEdge (p : PlaquetteAtLevel L m K (n + 1)) : BondAtLevel L m K (n + 1) :=
  Bond.forwardFrom (p.origin + unitStep L m (levelDepth K (n + 1)) p.secondAxis) p.firstAxis
def fourthEdge (p : PlaquetteAtLevel L m K (n + 1)) : BondAtLevel L m K (n + 1) :=
  Bond.forwardFrom p.origin p.secondAxis
def LieBondField.matrixValues {P : SymmetricBondSet L m K n} (a : LieBondField P) :
    BondAtLevel L m K n → Matrices.ComplexMatrix2 :=
  fun v => (a.eval v : Matrices.ComplexMatrix2)
def LieBondField.restrictToDoubleBlock {P : SymmetricBondSet L m K n} (c : BondAtLevel L m K (n + 1))
    (a : LieBondField P) : LieBondField (doubleBlockSymmetricSet c) :=
  fun v => a.eval v.1
def linearSchemeAverage (s : AveragingScheme) (A : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (c : BondAtLevel L m K (n + 1)) : Matrices.ComplexMatrix2 :=
  inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source, (contourFormMean s A c.source x +
    bondFormSumAlong A (crossingPath c x) - contourFormMean s A c.target (shiftAcross c x))
def restrictedSchemeAverage (s : AveragingScheme) {P : SymmetricBondSet L m K n}
    (a : LieBondField P) (c : BondAtLevel L m K (n + 1)) : Matrices.ComplexMatrix2 :=
  schemeBlockAverage s (expBondField c (LieBondField.restrictToDoubleBlock c a)) c
def plaquetteAverageHolonomy (s : AveragingScheme) {P : SymmetricBondSet L m K n}
    (a : LieBondField P) (p : PlaquetteAtLevel L m K (n + 1)) : Matrices.ComplexMatrix2 :=
  restrictedSchemeAverage s a (firstEdge p) *
    restrictedSchemeAverage s a (secondEdge p) *
    (restrictedSchemeAverage s a (thirdEdge p))⁻¹ *
    (restrictedSchemeAverage s a (fourthEdge p))⁻¹
def plaquetteLinearAverage (s : AveragingScheme) {P : SymmetricBondSet L m K n}
    (a : LieBondField P) (p : PlaquetteAtLevel L m K (n + 1)) : Matrices.ComplexMatrix2 :=
  linearSchemeAverage s
      (LieBondField.matrixValues (LieBondField.restrictToDoubleBlock (firstEdge p) a))
      (firstEdge p) +
    linearSchemeAverage s
      (LieBondField.matrixValues (LieBondField.restrictToDoubleBlock (secondEdge p) a))
      (secondEdge p) -
    linearSchemeAverage s
      (LieBondField.matrixValues (LieBondField.restrictToDoubleBlock (thirdEdge p) a))
      (thirdEdge p) -
    linearSchemeAverage s
      (LieBondField.matrixValues (LieBondField.restrictToDoubleBlock (fourthEdge p) a))
      (fourthEdge p)
end YangMills.Construction.PeriodicLattice
