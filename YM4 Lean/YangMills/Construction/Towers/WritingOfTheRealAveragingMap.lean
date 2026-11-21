import YangMills.Construction.Towers.CovariantLinearAverages
import YangMills.Construction.Towers.PolydiscsOfDoubleBlocks
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.CompactPresentation
open YangMills.Construction.Tower.BondSetFields
open YangMills.Construction.Tower.DoubleBlockPolydisc
variable {L k j : ℕ}
def reindexPositive {c : Edge L k (j + 1)} {S : Finset (Edge L k j)}
    (hS : (S : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    (w : S → Matrices.ComplexMatrix2) :
    DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c → Matrices.ComplexMatrix2 :=
  fun e => w ⟨e.1, Finset.mem_coe.mp (hS.symm ▸ e.2)⟩
def smoothingAtValues (c : Edge L k (j + 1))
    (v : DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c → Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2 :=
  complexSmoothing L (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c v) c
def smoothingOfRestriction (c : Edge L k (j + 1)) (W : Edge L k j → Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2 :=
  smoothingAtValues c (Tower.BondSetFields.readPositive InfiniteLattice.Link.IsPositivelyOriented
    (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c)
    (Tower.BondSetFields.restrictTo (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) W))
def compactPolydiscImage (r : ℝ) (c : Edge L k (j + 1)) :
    Set (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c → Matrices.ComplexMatrix2) :=
  DoubleBlockPolydisc.positiveImage InfiniteLattice.Link.IsPositivelyOriented
    (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c)
    {W | W ∈ nearIdentityPolydisc L k j r c ∧ IsFieldOn PeriodicLattice.compactGaugeGroup
      (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) W}
def compactPolydiscOn {c : Edge L k (j + 1)} {S : Finset (Edge L k j)}
    (hS : (S : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    (r : ℝ) : Set (S → Matrices.ComplexMatrix2) :=
  reindexPositive hS ⁻¹' compactPolydiscImage r c
def smoothingOn {c : Edge L k (j + 1)} {S : Finset (Edge L k j)}
    (hS : (S : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    (w : S → Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  smoothingAtValues c (reindexPositive hS w)
def smoothingAt (c : Edge L k (j + 1)) (W : Edge L k j → Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2 :=
  smoothingMap L k j W c
def HasPolydiscPresentation (D : Set (Edge L k j → Matrices.ComplexMatrix2))
    (U : Edge L k j → Matrices.ComplexMatrix2) (c : Edge L k (j + 1)) : Prop :=
  (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c).Finite ∧
    (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c).Nonempty ∧
    ∀ (S : Finset (Edge L k j))
      (hS : (S : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c),
      Matrices.ComplexMatrix2.IsRelativelyOpen (Matrices.specialUnitaryPower S)
        (compactPolydiscOn hS (Tower.polydiscRadius L)) ∧
      Matrices.EmbeddedSubmanifold.DifferentiableOnOpen (Matrices.specialUnitaryPower S)
        (compactPolydiscOn hS (Tower.polydiscRadius L)) (smoothingOn hS) ∧
      IsLocalPresentation PeriodicLattice.compactGaugeGroup D (smoothingAt c) U S
        (compactPolydiscOn hS (Tower.polydiscRadius L)) (smoothingOn hS)
def twistedPoint (S : Finset (Edge L k j)) (U X : Edge L k j → Matrices.ComplexMatrix2) :
    S → Matrices.ComplexMatrix2 :=
  fun e => Matrices.ComplexMatrix2.matExp (Complex.I • X e) * U e
structure DerivAgrees (D : Set (Edge L k j → Matrices.ComplexMatrix2))
    (U : Edge L k j → Matrices.ComplexMatrix2) (c : Edge L k (j + 1))
    (B : Edge L k j → Matrices.ComplexMatrix2) : Prop where
  presentation_value : ∀ (S : Finset (Edge L k j)) (O : Set (S → Matrices.ComplexMatrix2))
    (f : (S → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2),
      IsLocalPresentation PeriodicLattice.compactGaugeGroup D (smoothingAt c) U S O f →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
        twistedPoint S U ((t : ℂ) • B) ∈ O ∧
          f (twistedPoint S U ((t : ℂ) • B)) =
            smoothingOfRestriction c (expTwist ((t : ℂ) • B) U)
  presentation_deriv : ∀ (S : Finset (Edge L k j)) (O : Set (S → Matrices.ComplexMatrix2))
    (f : (S → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2),
      IsLocalPresentation PeriodicLattice.compactGaugeGroup D (smoothingAt c) U S O f →
      Tower.logDirectionalDeriv ℝ (fun X => f (twistedPoint S U X)) (smoothingAt c U) B =
        Tower.logDirectionalDeriv ℂ (fun X => smoothingOfRestriction c (expTwist X U))
          (smoothingOfRestriction c U) B
  holomorphic_deriv :
    Tower.logDirectionalDeriv ℂ (fun X => smoothingOfRestriction c (expTwist X U))
        (smoothingOfRestriction c U) B =
      complexSmoothingDeriv U B c
  leftDifferential_eq : leftDifferential D (smoothingMap L k j) U B c = complexSmoothingDeriv U B c
def PresentationTheorem : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    ∀ c : Edge L k (j + 1), InfiniteLattice.Link.IsPositivelyOriented c →
    ∀ D : Set (Edge L k j → Matrices.ComplexMatrix2), D ⊆ smoothingDomain L k j →
    ∀ U ∈ D, (∀ e : Edge L k j,
        Matrices.ComplexMatrix2.operatorNorm (U e - 1) < Tower.polydiscRadius L) →
      HasPolydiscPresentation D U c ∧
        (IsFinitelyOpen PeriodicLattice.compactGaugeGroup D →
          ∀ B ∈ edgeFormSpace (Tower.meshAt L k j), DerivAgrees D U c B)
end YangMills.Construction.Tower.FullSpace.CompactPresentation
end
