import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import YangMills.Construction.Towers.TransportsAroundAPlaquette
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FaceTermDerivatives
def expProduct (Y : Fin 4 → Matrices.ComplexMatrix2) (t : ℂ) : Matrices.ComplexMatrix2 :=
  Matrices.ComplexMatrix2.matExp ((Complex.I * t) • Y 0) *
    Matrices.ComplexMatrix2.matExp ((Complex.I * t) • Y 1) *
    Matrices.ComplexMatrix2.matExp ((Complex.I * t) • Y 2) *
    Matrices.ComplexMatrix2.matExp ((Complex.I * t) • Y 3)
def commutatorSum (Y : Fin 4 → Matrices.ComplexMatrix2) : Matrices.ComplexMatrix2 :=
  ∑ a : Fin 4, ∑ b ∈ Finset.Ioi a, (Y a * Y b - Y b * Y a)
def firstDerivExpr (Y : Fin 4 → Matrices.ComplexMatrix2) (W : Matrices.ComplexMatrix2) : ℂ :=
  -(Complex.I / 2) * Matrices.ComplexMatrix2.fullTrace ((∑ a, Y a) * W)
def secondDerivExpr (Y : Fin 4 → Matrices.ComplexMatrix2) (W : Matrices.ComplexMatrix2) : ℂ :=
  (1 / 2) * Matrices.ComplexMatrix2.fullTrace W *
      Matrices.ComplexMatrix2.halfTrace ((∑ a, Y a) * ∑ a, Y a) +
    (1 / 4) * Matrices.ComplexMatrix2.fullTrace (commutatorSum Y * (W - W⁻¹))
def HoldsAtFace {L n k j : ℕ} (U B : Edge L n k j → Matrices.ComplexMatrix2) (p : Face L n k j) :
    Prop :=
  (∀ t : ℂ, PeriodicLattice.plaquetteHolonomy (PeriodicLattice.expTwist (t • B) U) p =
    expProduct (transportedForm U B p) t * PeriodicLattice.plaquetteHolonomy U p) ∧
  HasDerivAt (fun t : ℂ => complexFaceTerm (PeriodicLattice.expTwist (t • B) U) p)
    (firstDerivExpr (transportedForm U B p) (PeriodicLattice.plaquetteHolonomy U p)) 0 ∧
  HasDerivAt (deriv fun t : ℂ => complexFaceTerm (PeriodicLattice.expTwist (t • B) U) p)
    (secondDerivExpr (transportedForm U B p) (PeriodicLattice.plaquetteHolonomy U p)) 0
def HoldsOnPeriodicLevel (L n k j : ℕ) : Prop :=
  ∀ B ∈ complexEdgeForms L n k j,
    (∀ U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ p : Face L n k j, HoldsAtFace U B p) ∧
      (∑ᶠ p : Face L n k j, secondDerivExpr (transportedForm U B p)
        (PeriodicLattice.plaquetteHolonomy U p)) = complexActionHessian U B B ∧
      (∑ᶠ p : Face L n k j, firstDerivExpr (transportedForm U B p)
        (PeriodicLattice.plaquetteHolonomy U p)) = complexActionDeriv U B) ∧
    complexActionHessian (fun _ => 1) B B =
      traceFinsumPairing (edgeCoboundary B) (edgeCoboundary B)
def HoldsAtFullSpaceFace {L k j : ℕ} (U B : FullSpace.Edge L k j → Matrices.ComplexMatrix2)
    (p : FullSpace.Face L k j) : Prop :=
  (∀ t : ℂ, FullSpace.faceVariable (FullSpace.expTwist (t • B) U) p =
    expProduct (FullSpace.transportedForm U B p) t * FullSpace.faceVariable U p) ∧
  HasDerivAt (fun t : ℂ => FullSpace.complexFaceTerm (FullSpace.expTwist (t • B) U) p)
    (firstDerivExpr (FullSpace.transportedForm U B p) (FullSpace.faceVariable U p)) 0 ∧
  HasDerivAt (deriv fun t : ℂ => FullSpace.complexFaceTerm (FullSpace.expTwist (t • B) U) p)
    (secondDerivExpr (FullSpace.transportedForm U B p) (FullSpace.faceVariable U p)) 0
def HoldsOnFullSpaceLevel (L k j : ℕ) : Prop :=
  ∀ B ∈ FullSpace.complexEdgeForms (meshAt L k j),
    (∀ U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
      ∀ p : FullSpace.Face L k j, HoldsAtFullSpaceFace U B p) ∧
    (FullSpace.HasFiniteEdgeSupport B →
      (∀ U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
        (∑ᶠ p : FullSpace.Face L k j, secondDerivExpr (FullSpace.transportedForm U B p)
          (FullSpace.faceVariable U p)) = FullSpace.complexActionHessian U B B ∧
        (∑ᶠ p : FullSpace.Face L k j, firstDerivExpr (FullSpace.transportedForm U B p)
          (FullSpace.faceVariable U p)) = FullSpace.complexActionDeriv U B) ∧
      FullSpace.complexActionHessian (fun _ => 1) B B =
        traceFinsumPairing (FullSpace.edgeCoboundary B) (FullSpace.edgeCoboundary B))
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    (∀ n : ℕ, 0 < n → HoldsOnPeriodicLevel L n k j) ∧ HoldsOnFullSpaceLevel L k j
end FaceTermDerivatives
end Tower
end YangMills.Construction
end
