import YangMills.Construction.Lattice.IdentitiesOfComplexForms
import YangMills.Construction.Lattice.IsometryCovarianceOfTheOneStepOperations
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ComplexTransport
open Matrices
variable {L m : ℕ} {j j' : ℤ}
structure ComplexConstraintData (V : Bond L m j' → ComplexMatrix2) (Γ : Set (Bond L m j)) :
    Prop where
  defined : ComplexConstraintDefined V Γ
  pivot_invertible : ∀ c ∈ Γ, PivotCoeffInvertible V c
structure StepOperationsTransport (σ : FourTorus L m ≃ FourTorus L m) {K k : ℕ}
    (V : BondAtLevel L m K k → ComplexMatrix2) (Γ : Set (BondAtLevel L m K (k + 1))) : Prop where
  linearized_comm : ∀ A : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra A →
    ∀ c' ∈ orientedImage σ Γ,
      linearizedConstraint (transportGaugeField σ V) (twistedTransportForm σ V A) c' =
        twistedTransportForm σ (complexBlockAverage V) (linearizedConstraint V A) c'
  map_comm : ∀ B : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra B →
    ∀ c ∈ Γ, ∀ c', IsOrientedImage σ c c' → ConstraintMapDefined V B c →
      ConstraintMapDefined (transportGaugeField σ V) (twistedTransportForm σ V B) c' →
      constraintMap (transportGaugeField σ V) (twistedTransportForm σ V B) c' =
        twistedFormValue σ (complexBlockAverage V) (constraintMap V B) c'
  eliminate_comm : ∀ A : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra A →
    eliminate (transportGaugeField σ V) (orientedImage σ Γ)
        (twistedTransportForm σ V A) =
      twistedTransportForm σ V (eliminate V Γ A)
  lift_comm : ∀ ν : ↥Γ → ComplexMatrix2, (∀ c, ν c ∈ complexLieAlgebra) →
    pivotCorrectionLift (transportGaugeField σ V) (orientedImage σ Γ)
        (twistedTransportCoarse σ (complexBlockAverage V) ν) =
      twistedTransportSupportForm σ V (pivotCorrectionLift V Γ ν)
  correction_comm :
    ∀ᶠ B in 𝓝[(supportForms (levelDepth K k) Γ :
        Set (SupportBond (levelDepth K k) Γ → ComplexMatrix2))] 0,
      linearizingCorrection (transportGaugeField σ V) (orientedImage σ Γ)
          (twistedTransportSupportForm σ V B) =
        twistedTransportCoarse σ (complexBlockAverage V) (linearizingCorrection V Γ B)
  correction_holomorphic :
    IsHolomorphicAtZero (fun B : SupportBond (levelDepth K k) Γ → ComplexMatrix2 =>
      linearizingCorrection (transportGaugeField σ V) (orientedImage σ Γ)
        (twistedTransportSupportForm σ V B)) ∧
    IsHolomorphicAtZero (fun B : SupportBond (levelDepth K k) Γ → ComplexMatrix2 =>
      twistedTransportCoarse σ (complexBlockAverage V) (linearizingCorrection V Γ B))
  change_comm :
    ∀ᶠ B in 𝓝[(supportForms (levelDepth K k) Γ :
        Set (SupportBond (levelDepth K k) Γ → ComplexMatrix2))] 0,
      linearizingChange (transportGaugeField σ V) (orientedImage σ Γ)
          (twistedTransportSupportForm σ V B) =
        twistedTransportSupportForm σ V (linearizingChange V Γ B)
  change_holomorphic :
    IsHolomorphicAtZero (fun B : SupportBond (levelDepth K k) Γ → ComplexMatrix2 =>
      linearizingChange (transportGaugeField σ V) (orientedImage σ Γ)
        (twistedTransportSupportForm σ V B)) ∧
    IsHolomorphicAtZero (fun B : SupportBond (levelDepth K k) Γ → ComplexMatrix2 =>
      twistedTransportSupportForm σ V (linearizingChange V Γ B))
  pivotCoeff_conj : ∀ c ∈ Γ, ∀ c', IsOrientedImage σ c c' → ∀ X : ↥ComplexMatrix2.traceless,
    ∃ Y : ↥ComplexMatrix2.traceless, (Y : ComplexMatrix2) = pivotCoeff V c X ∧
      pivotCoeff (transportGaugeField σ V) c'
          (twistedLinkMap σ V (pivot c) X : ↥ComplexMatrix2.traceless) =
        (twistedLinkMap σ (complexBlockAverage V) c Y : ↥ComplexMatrix2.traceless)
  weight_eq : ∀ c ∈ Γ, ∀ c', IsOrientedImage σ c c' →
    eliminationWeight (transportGaugeField σ V) c' = eliminationWeight V c
  bilinear_comm : ∀ B₁ B₂ : BondAtLevel L m K k → ComplexMatrix2, IsBondForm complexLieAlgebra B₁ →
    IsBondForm complexLieAlgebra B₂ → ∀ c' ∈ orientedImage σ Γ,
      constraintBilinear (transportGaugeField σ V)
          (twistedTransportForm σ V B₁) (twistedTransportForm σ V B₂) c' =
        twistedFormValue σ (complexBlockAverage V) (constraintBilinear V B₁ B₂) c'
def definedPoints (σ : FourTorus L m ≃ FourTorus L m) (j' : ℤ) (Γ : Set (Bond L m j))
    (κ : Type) : Set (SupportBond j' Γ ⊕ κ → ComplexMatrix2) :=
  {p | p ∈ GroupLieProduct (SupportBond j' Γ) κ ∧
    ComplexConstraintData (gaugeFieldOfPoint (doubleBlockSupport j' Γ) p) Γ ∧
    ComplexConstraintData
      (transportGaugeField σ (gaugeFieldOfPoint (doubleBlockSupport j' Γ) p))
      (orientedImage σ Γ)}
abbrev supportGaugeField {Γ : Set (Bond L m j)} {κ : Type}
    (p : SupportBond j' Γ ⊕ κ → ComplexMatrix2) : Bond L m j' → ComplexMatrix2 :=
  gaugeFieldOfPoint (doubleBlockSupport j' Γ) p
structure StepSidesHolomorphic (σ : FourTorus L m ≃ FourTorus L m) {K k : ℕ}
    (Γ : Set (BondAtLevel L m K (k + 1))) : Prop where
  linearized_sides : ∀ c' ∈ orientedImage σ Γ,
    BothHolomorphicToTraceless
      (definedPoints σ (levelDepth K k) Γ (SupportBond (levelDepth K k) Γ))
      (fun p => linearizedConstraint (transportGaugeField σ (supportGaugeField p))
        (twistedTransportForm σ (supportGaugeField p) (extendForm (algebraPartOfPoint p))) c')
      (fun p => twistedTransportForm σ (complexBlockAverage (supportGaugeField p))
        (linearizedConstraint (supportGaugeField p) (extendForm (algebraPartOfPoint p))) c')
  map_sides : ∀ c ∈ Γ, ∀ c', IsOrientedImage σ c c' →
    BothHolomorphicToTraceless
      {p | p ∈ definedPoints σ (levelDepth K k) Γ (SupportBond (levelDepth K k) Γ) ∧
        ConstraintMapDefined (supportGaugeField p) (extendForm (algebraPartOfPoint p)) c ∧
        ConstraintMapDefined (transportGaugeField σ (supportGaugeField p))
          (twistedTransportForm σ (supportGaugeField p) (extendForm (algebraPartOfPoint p))) c'}
      (fun p => constraintMap (transportGaugeField σ (supportGaugeField p))
        (twistedTransportForm σ (supportGaugeField p) (extendForm (algebraPartOfPoint p))) c')
      (fun p => twistedFormValue σ (complexBlockAverage (supportGaugeField p))
        (constraintMap (supportGaugeField p) (extendForm (algebraPartOfPoint p))) c')
  eliminate_sides : ∀ b' : SupportBond (levelDepth K k) (orientedImage σ Γ),
    BothHolomorphicToTraceless
      (definedPoints σ (levelDepth K k) Γ (SupportBond (levelDepth K k) Γ))
      (fun p => eliminate (transportGaugeField σ (supportGaugeField p))
        (orientedImage σ Γ)
        (twistedTransportForm σ (supportGaugeField p) (extendForm (algebraPartOfPoint p))) b'.1)
      (fun p => twistedTransportForm σ (supportGaugeField p)
        (eliminate (supportGaugeField p) Γ (extendForm (algebraPartOfPoint p))) b'.1)
  lift_sides : ∀ b' : SupportBond (levelDepth K k) (orientedImage σ Γ),
    BothHolomorphicToTraceless
      (definedPoints σ (levelDepth K k) Γ ↥Γ)
      (fun p => pivotCorrectionLift (transportGaugeField σ (supportGaugeField p))
        (orientedImage σ Γ)
        (twistedTransportCoarse σ (complexBlockAverage (supportGaugeField p))
          (algebraPartOfPoint p)) b')
      (fun p => twistedTransportSupportForm σ (supportGaugeField p)
        (pivotCorrectionLift (supportGaugeField p) Γ (algebraPartOfPoint p)) b')
  bilinear_sides : ∀ c' ∈ orientedImage σ Γ,
    BothHolomorphicToTraceless
      (definedPoints σ (levelDepth K k) Γ
        (SupportBond (levelDepth K k) Γ ⊕ SupportBond (levelDepth K k) Γ))
      (fun p => constraintBilinear
        (transportGaugeField σ (supportGaugeField p))
        (twistedTransportForm σ (supportGaugeField p) (extendForm (firstAlgebraPart p)))
        (twistedTransportForm σ (supportGaugeField p) (extendForm (secondAlgebraPart p))) c')
      (fun p => twistedFormValue σ (complexBlockAverage (supportGaugeField p))
        (constraintBilinear (supportGaugeField p)
          (extendForm (firstAlgebraPart p)) (extendForm (secondAlgebraPart p))) c')
end YangMills.Construction.PeriodicLattice.ComplexTransport
