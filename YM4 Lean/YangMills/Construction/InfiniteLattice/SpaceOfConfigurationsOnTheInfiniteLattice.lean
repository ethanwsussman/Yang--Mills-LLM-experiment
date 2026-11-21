import YangMills.Construction.InfiniteLattice.LatticeOfACutoffAndTheVariablesOfASetOfBonds
import YangMills.Construction.InfiniteLattice.PeriodicExtensionsAndTheirWeakLimitPoints
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.GaugeFieldSpace
open YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def IsBoundedBorel {X : Type*} [TopologicalSpace X] (g : X → ℝ) : Prop :=
  Measurable[borel X] g ∧ ∃ C : ℝ, ∀ x, |g x| ≤ C
def AgreesOnAndOff (S : Set (Link a)) (V : LinkVariables S) (U W : GaugeField a) : Prop :=
  (∀ e : S, W e = V e) ∧ ∀ e ∈ CutoffLattice.positiveLinks a \ S, W e = U e
def ProductStructure (a : ℝ) : Prop :=
  (CutoffLattice.positiveLinks a).Countable ∧ (CutoffLattice.positiveLinks a).Infinite ∧
    (∀ e : Link a, Xor (e ∈ CutoffLattice.positiveLinks a)
      (e.opposite ∈ CutoffLattice.positiveLinks a)) ∧
    IsHomeomorph (CutoffLattice.valuesOnPositive :
      GaugeField a → CutoffLattice.positiveLinks a → Matrices.ComplexMatrix2.specialUnitary) ∧
    CompactSpace (GaugeField a) ∧ TopologicalSpace.MetrizableSpace (GaugeField a)
def FiniteLinkSplicing (a : ℝ) : Prop :=
  ∀ (S : Set (Link a)) [Finite S], S ⊆ CutoffLattice.positiveLinks a →
    (∀ (V : LinkVariables S) (U : GaugeField a), ∃! W, AgreesOnAndOff S V U W) ∧
    (∀ c : LinkVariables S × GaugeField a → GaugeField a,
      (∀ V U, AgreesOnAndOff S V U (c (V, U))) → Continuous c) ∧
    ∀ F : GaugeField a → ℝ,
      (CutoffLattice.DependsOnlyOn F S ↔
        ∃ g : LinkVariables S → ℝ, ∀ U, F U = g (restrictField U S)) ∧
      (CutoffLattice.DependsOnlyOn F S →
        (∃! g : LinkVariables S → ℝ, ∀ U, F U = g (restrictField U S)) ∧
        ∀ g : LinkVariables S → ℝ, (∀ U, F U = g (restrictField U S)) →
          (Continuous F ↔ Continuous g) ∧
          (Measurable[borel (GaugeField a)] F ↔ Measurable[borel (LinkVariables S)] g))
def FaceEnergyProperties (a : ℝ) : Prop :=
  ∀ p : ElementaryPlaquette a,
    Continuous (fun U : GaugeField a => faceEnergy U p) ∧
    (∀ U : GaugeField a, faceEnergy U p ∈ Set.Icc (0 : ℝ) 2) ∧
    CutoffLattice.DependsOnlyOn (fun U : GaugeField a => faceEnergy U p)
      {PeriodicExtensions.firstEdge p, PeriodicExtensions.secondEdge p,
        PeriodicExtensions.thirdEdge p, PeriodicExtensions.fourthEdge p}
def ExistsDenseLocalSequence (a : ℝ) : Prop :=
  ∃ F : ℕ+ → C(GaugeField a, ℝ),
    (∀ (H : C(GaugeField a, ℝ)) (ε : ℝ), 0 < ε →
      ∃ k, CutoffLattice.supNorm (H - F k) < ε) ∧
    ∀ k, ∃ S : Set (Link a), S.Finite ∧ CutoffLattice.DependsOnlyOn (F k) S
def FiniteLinkFubini (a : ℝ) : Prop :=
  ∀ (S : Set (Link a)) [Finite S], S ⊆ CutoffLattice.positiveLinks a →
    ∀ Φ : LinkVariables S × GaugeField a → ℝ, IsBoundedBorel Φ →
      (∀ U, IsBoundedBorel fun V => Φ (V, U)) ∧
      (∀ V, IsBoundedBorel fun U => Φ (V, U)) ∧
      IsBoundedBorel (fun U => ∫ V, Φ (V, U) ∂LinkVariables.haarMeasure S) ∧
      (∀ U, |∫ V, Φ (V, U) ∂LinkVariables.haarMeasure S| ≤ TestFunctions.uniformNorm Φ) ∧
      (Continuous Φ → Continuous fun U => ∫ V, Φ (V, U) ∂LinkVariables.haarMeasure S) ∧
      ∀ ν : Measure (GaugeField a), IsProbabilityMeasure ν →
        IsBoundedBorel (fun V => ∫ U, Φ (V, U) ∂ν) ∧
        ∫ U, (∫ V, Φ (V, U) ∂LinkVariables.haarMeasure S) ∂ν =
          ∫ V, (∫ U, Φ (V, U) ∂ν) ∂LinkVariables.haarMeasure S
def Statement : Prop :=
  ∀ d : CutoffLinks.CutoffData,
    ProductStructure d.spacing ∧ FiniteLinkSplicing d.spacing ∧ FaceEnergyProperties d.spacing ∧
      ExistsDenseLocalSequence d.spacing ∧ FiniteLinkFubini d.spacing
end YangMills.Construction.InfiniteLattice.GaugeFieldSpace
