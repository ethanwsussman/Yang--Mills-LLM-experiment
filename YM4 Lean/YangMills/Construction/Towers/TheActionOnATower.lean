import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
namespace ActionFacts
variable {L n k : ℕ}
def edgeEntryCoordinates (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    PositiveEdge L n k 0 × Fin 2 × Fin 2 × Bool → ℝ
  | (e, r, c, false) => (U e r c).re
  | (e, r, c, true) => (U e r c).im
def IsPolynomialInEdgeEntries (F : (Edge L n k 0 → Matrices.ComplexMatrix2) → ℝ) : Prop :=
  ∃ P : MvPolynomial (PositiveEdge L n k 0 × Fin 2 × Fin 2 × Bool) ℝ,
    ∀ U ∈ fieldSpace L n k 0, F U = MvPolynomial.eval (edgeEntryCoordinates U) P
def HolonomyExpansionAtIdentity (L n k : ℕ) : Prop :=
  ∃ C ε : ℝ, 0 < ε ∧ ∀ A ∈ edgeFormSpace L n k 0, edgeFormNorm A < ε → ∀ p : Face L n k 0,
    ∃ R : Matrices.ComplexMatrix2, Matrices.ComplexMatrix2.operatorNorm R ≤ C * edgeFormNorm A ^ 2 ∧
      PeriodicLattice.plaquetteHolonomy
          (PeriodicLattice.expTwist A PeriodicLattice.trivialGaugeField) p =
        Matrices.ComplexMatrix2.matExp (Complex.I • edgeCoboundary A p + R)
def ActionTaylorExpansion (L n k : ℕ) : Prop :=
  ∃ C ε : ℝ, 0 < ε ∧ ∀ A ∈ edgeFormSpace L n k 0, edgeFormNorm A < ε →
    |plaquetteAction L n k (PeriodicLattice.expTwist A PeriodicLattice.trivialGaugeField) -
        1 / 2 * traceFinsumNorm (edgeCoboundary A) ^ 2| ≤ C * edgeFormNorm A ^ 3
end ActionFacts
open ActionFacts in
def ActionFacts.Statement : Prop :=
  ∀ L k n : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    (IsPolynomialInEdgeEntries (plaquetteAction L n k) ∧
      (∀ U ∈ fieldSpace L n k 0, 0 ≤ plaquetteAction L n k U) ∧
      plaquetteAction L n k PeriodicLattice.trivialGaugeField = 0) ∧
    (∀ U ∈ fieldSpace L n k 0, ∀ g ∈ gaugeGroupAt L n k 0,
      plaquetteAction L n k (PeriodicLattice.gaugeTransform g U) = plaquetteAction L n k U) ∧
    (∀ U ∈ fieldSpace L n k 0, ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
      IsDistancePreserving f → MapsSublatticeOnto k 0 f →
        plaquetteAction L n k (pushField f U) = plaquetteAction L n k U) ∧
    (HolonomyExpansionAtIdentity L n k ∧
      ActionTaylorExpansion L n k ∧
      leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
        PeriodicLattice.trivialGaugeField = 0 ∧
      ∀ A ∈ edgeFormSpace L n k 0,
        leftSecondDeriv (plaquetteAction L n k) PeriodicLattice.trivialGaugeField A A =
          traceFinsumNorm (edgeCoboundary A) ^ 2)
end YangMills.Construction.Tower
end
