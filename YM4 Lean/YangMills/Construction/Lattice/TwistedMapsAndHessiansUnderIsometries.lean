import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.Lattice.CurrentOnPart
import YangMills.Construction.Lattice.HessianOfTheActionOfARegion
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import YangMills.Construction.Lattice.LandauGaugeRelativeToABackground
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ} {j : ℤ}
def bondSetTransport (σ : FourTorus L m ≃ FourTorus L m) (S : Set (Bond L m j)) : Set (Bond L m j) :=
  bondImage σ '' S
def complexFormsOn (S : Set (Bond L m j)) : Set (Bond L m j → Matrices.ComplexMatrix2) :=
  {A | IsBondForm complexLieAlgebra A ∧ S.indicator A = A}
def realFormsOn (S : Set (Bond L m j)) : Set (Bond L m j → Matrices.ComplexMatrix2) :=
  {A | IsRealBondFormOn S A}
def realFormOfPositiveValues (S : Set (Bond L m j))
    (a : PositiveBondOf S → Matrices.ComplexMatrix2.LieElement) :
    Bond L m j → Matrices.ComplexMatrix2 :=
  open Classical in
  bondFormOfPositive fun b => if h : b ∈ S ∧ b.IsPositivelyOriented then (a ⟨b, h⟩).toMatrix else 0
def currentDomain (S : Set (Bond L m j)) : Set (Bond L m j) :=
  {b | ∀ p ∈ plaquettesThrough b, p.BondsWithin S}
structure IsTwistedTransportOn (σ : FourTorus L m ≃ FourTorus L m) (S : Set (Bond L m j))
    (V : Bond L m j → Matrices.ComplexMatrix2) : Prop where
  transport_expTwist : ∀ A ∈ complexFormsOn S, ∀ e ∈ bondSetTransport σ S,
    transportGaugeField σ (expTwist A V) e =
      expTwist (twistedTransportForm σ V A) (transportGaugeField σ V) e
  map_add : ∀ A ∈ complexFormsOn S, ∀ B ∈ complexFormsOn S,
    twistedTransportForm σ V (A + B) =
      twistedTransportForm σ V A + twistedTransportForm σ V B
  map_smul : ∀ (c : ℂ), ∀ A ∈ complexFormsOn S,
    twistedTransportForm σ V (c • A) = c • twistedTransportForm σ V A
  bijOn : BijOn (twistedTransportForm σ V) (complexFormsOn S)
    (complexFormsOn (bondSetTransport σ S))
  inner_eq : ∀ ξ : ℝ, 0 < ξ → ∀ A ∈ complexFormsOn S, ∀ B ∈ complexFormsOn S,
    bondFormInner ξ (twistedTransportForm σ V A) (twistedTransportForm σ V B) =
      bondFormInner ξ A B
  currentDomain_image : currentDomain (bondSetTransport σ S) =
    bondSetTransport σ (currentDomain S)
  current_transport : ∀ ξ : ℝ, 0 < ξ → ∀ e ∈ currentDomain (bondSetTransport σ S),
    yangMillsCurrent ξ (extendByOne (bondSetTransport σ S) (transportGaugeField σ V)) e =
      twistedTransportForm σ V (yangMillsCurrent ξ (extendByOne S V)) e
structure IsRealTwistedTransportOn (σ : FourTorus L m ≃ FourTorus L m) (S : Set (Bond L m j))
    (V : Bond L m j → Matrices.ComplexMatrix2) : Prop where
  bijOn : BijOn (twistedTransportForm σ V) (realFormsOn S)
    (realFormsOn (bondSetTransport σ S))
  inner_eq : ∀ ξ : ℝ, 0 < ξ → ∀ A ∈ realFormsOn S, ∀ B ∈ realFormsOn S,
    bondFormInner ξ (twistedTransportForm σ V A) (twistedTransportForm σ V B) =
      bondFormInner ξ A B
  operatorNorm_eq : ∀ A ∈ realFormsOn S, ∀ b ∈ S,
    Matrices.ComplexMatrix2.operatorNorm (twistedTransportForm σ V A (bondImage σ b)) =
      Matrices.ComplexMatrix2.operatorNorm (A b)
  measurePreserving : ∃ (_ : Fintype (PositiveBondOf S))
      (_ : Fintype (PositiveBondOf (bondSetTransport σ S)))
      (T : (PositiveBondOf S → Matrices.ComplexMatrix2.LieElement) →
        PositiveBondOf (bondSetTransport σ S) → Matrices.ComplexMatrix2.LieElement),
    MeasurePreserving T (Measure.pi fun _ => Matrices.ComplexMatrix2.lieLebesgue)
        (Measure.pi fun _ => Matrices.ComplexMatrix2.lieLebesgue) ∧
      ∀ a, realFormOfPositiveValues (bondSetTransport σ S) (T a) =
        twistedTransportForm σ V (realFormOfPositiveValues S a)
structure HessiansInvariant (σ : FourTorus L m ≃ FourTorus L m) (K : ℕ) (Ω : Set (FourTorus L m))
    (S : Set (BondAtLevel L m K 0)) : Prop where
  wilson : ∀ ξ : ℝ, 0 < ξ → ∀ V, IsGaugeField compactGaugeGroup S V → ∀ A ∈ realFormsOn S,
    wilsonHessian ξ K (σ '' Ω) (transportGaugeField σ V)
        (twistedTransportForm σ V A) =
      wilsonHessian ξ K Ω V A
  regionEnergy : ∀ (k : ℕ) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2),
    IsGaugeField complexGaugeGroup S U →
    ∀ A₁ ∈ complexFormsOn S, ∀ A₂ ∈ complexFormsOn S,
      regionEnergyHessian k (σ '' Ω) (transportGaugeField σ U)
          (twistedTransportForm σ U A₁) (twistedTransportForm σ U A₂) =
        regionEnergyHessian k Ω U A₁ A₂
def TwistedTransportIsometryInvariance : Prop :=
  ∀ (L m : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m),
    Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i →
    ((IsTorusTranslation σ ∨ ∃ π : Equiv.Perm (Fin 4), HasLinearPart σ (π, 1)) →
      ∀ j : ℤ, -(m : ℤ) < j → i ≤ j → ∀ b : Bond L m j, b.IsPositivelyOriented →
        (bondImage σ b).IsPositivelyOriented) ∧
    (∀ j : ℤ, i ≤ j → ∀ S : Set (Bond L m j), IsReversalClosed S →
      ∀ U : Bond L m j → Matrices.ComplexMatrix2,
      (IsGaugeField compactGaugeGroup S U →
        IsGaugeField compactGaugeGroup (bondSetTransport σ S) (transportGaugeField σ U)) ∧
      (IsGaugeField complexGaugeGroup S U →
        IsGaugeField complexGaugeGroup (bondSetTransport σ S) (transportGaugeField σ U))) ∧
    (∀ j : ℤ, -(m : ℤ) < j → i ≤ j → ∀ S : Set (Bond L m j), IsReversalClosed S →
      (∀ A ∈ complexFormsOn S,
        twistedTransportForm σ trivialGaugeField A = transportForm σ A) ∧
      ((∀ b : Bond L m j, b.IsPositivelyOriented → (bondImage σ b).IsPositivelyOriented) →
        ∀ V : Bond L m j → Matrices.ComplexMatrix2, ∀ A ∈ complexFormsOn S,
          twistedTransportForm σ V A = transportForm σ A) ∧
      (∀ V : Bond L m j → Matrices.ComplexMatrix2,
        IsGaugeField complexGaugeGroup S V → IsTwistedTransportOn σ S V) ∧
      (∀ V : Bond L m j → Matrices.ComplexMatrix2,
        IsGaugeField compactGaugeGroup S V → IsRealTwistedTransportOn σ S V)) ∧
    (∀ K : ℕ, -(m : ℤ) < levelDepth K 0 → i ≤ levelDepth K 0 → ∀ i' : ℤ, i ≤ i' →
      i' ≤ levelDepth K 0 →
      ∀ Ω : Set (FourTorus L m), IsPartitionRegion i' Ω → ∀ S : Set (BondAtLevel L m K 0),
        IsReversalClosed S → bondsInside Ω ⊆ S → HessiansInvariant σ K Ω S)
end YangMills.Construction.PeriodicLattice
end
