import YangMills.Construction.InfiniteLattice.ConnectedCorrelations
import YangMills.Construction.InfiniteLattice.RepresentativeOfATupleAtACutoff
import YangMills.Construction.LimitTheorem.FunctionalDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.LimitTheorem
namespace CutoffRepresentatives
open InfiniteLattice CutoffLattice
open TestSpaces (SepTuple SepTupleOfCard sepRestrict)
def MomentsAndCumulantsAt (L K : ℕ) (μ : Measure (FieldsAt L K)) : Prop :=
  (∀ (k : ℕ) (X : SepTupleOfCard k),
    ((∫ U, CutoffRepresentative.centredProduct L K μ ⟨k, X⟩ U ∂μ : ℝ) : ℂ) = centeredMoment μ X.1 ∧
      centeredMoment μ X.1 = ursellPartitionSum μ X.1) ∧
  (∀ X : SepTupleOfCard 0, ursellPartitionSum μ X.1 = 1) ∧
  (∀ X : SepTupleOfCard 1, ursellPartitionSum μ X.1 = 0) ∧
  ∀ (m : ℕ), 2 ≤ m → ∀ X : SepTupleOfCard m,
    ursellFunction μ m X.1 =
      ∑ P ∈ ClusterExpansion.SymGraph.partitions (Fin m),
        (-1 : ℂ) ^ (P.card - 1) * ((P.card - 1).factorial : ℂ) *
          ∏ J ∈ P, centeredMoment μ (sepRestrict X J).1
def UrsellTendsto (L : ℕ) (K : ℕ+ → ℕ+)
    (μ : ∀ j, Measure (FieldsAt L (K j))) (S : CumulantFamily) : Prop :=
  ∀ (m : ℕ) (hm : 2 ≤ m) (X : SepTupleOfCard m),
    Tendsto (fun j => ursellFunction (μ j) m X.1) atTop (𝓝 ((S m hm X : ℝ) : ℂ))
def RepresentativesTendsto (L : ℕ) (K : ℕ+ → ℕ+)
    (μ : ∀ j, Measure (FieldsAt L (K j))) (S : CumulantFamily) : Prop :=
  ∀ X : SepTuple,
    Tendsto (fun j => ∫ U, CutoffRepresentative.centredProduct L (K j) (μ j) X U ∂μ j) atTop
      (𝓝 (evalOnMap (centredOf S) X))
def CentredSymmetriesAndCumulants (S : CumulantFamily) : Prop :=
  ((centredOf S).IsPermInvariant ↔ IsFamilySymmetric S) ∧
  (∀ g : Motions.RigidMotion,
    IsMotionInvariant (centredOf S) g ↔ IsFamilyInvariant S g) ∧
  (∀ X : SepTupleOfCard 1, connectedFn (centredOf S) X = 0) ∧
  HasCumulants (centredOf S) S
end CutoffRepresentatives
open CutoffRepresentatives in
def CutoffRepresentatives.IdentificationsHold : Prop :=
  ∀ (L : ℕ), Conventions.IsAdmissibleBlockingFactor L → ∀ (K : ℕ+ → ℕ+)
    (μ : ∀ j, Measure (CutoffLattice.FieldsAt L (K j))), (∀ j, IsProbabilityMeasure (μ j)) →
    ∀ S : CumulantFamily,
      (∀ j, MomentsAndCumulantsAt L (K j) (μ j)) ∧
      (UrsellTendsto L K μ S ↔ RepresentativesTendsto L K μ S) ∧
      CentredSymmetriesAndCumulants S
end YangMills.Construction.LimitTheorem
end
