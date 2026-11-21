import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import YangMills.Construction.Lattice.ImagesOfBondsAndPlaquettesUnderLatticeIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
namespace LinkWindow
variable (W : LinkWindow a)
def traceBoltzmannWeight (β : ℝ) (U : GaugeField a) : ℝ :=
  Real.exp (β * ∑ᶠ p ∈ facesMeeting (W.links : Set (Link a)),
    (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
      (faceHolonomy U p : Matrices.ComplexMatrix2)).re)
def conditionalExpectationTrace (ha : 0 < a) (β : ℝ) (F : GaugeField a → ℂ)
    (U : GaugeField a) : ℂ :=
  (∫ V, F (W.glue ha V U) * (W.traceBoltzmannWeight β (W.glue ha V U) : ℂ) ∂W.haarProd) /
    ((∫ V, W.traceBoltzmannWeight β (W.glue ha V U) ∂W.haarProd : ℝ) : ℂ)
def ConditionalExpectationWellDefined (ha : 0 < a) (β : ℝ) (F : GaugeField a → ℂ)
    (U : GaugeField a) : Prop :=
  Integrable (fun V => F (W.glue ha V U) * (W.localWeight β (W.glue ha V U) : ℂ)) W.haarProd ∧
    Integrable (fun V => W.localWeight β (W.glue ha V U)) W.haarProd ∧
    ∫ V, W.localWeight β (W.glue ha V U) ∂W.haarProd ≠ 0
end LinkWindow
def linksInside (a : ℝ) (S : Set AmbientSpace) : Set (Link a) :=
  {b | b ∈ positiveLinks a ∧ LinksLieIn {b} S}
def GaugeFieldsAreLinkFamilies (ha : 0 < a) : Prop :=
  IsHomeomorph (restrictToPositive (a := a)) ∧
    IsProbabilityMeasure (gaugeFieldHaarMeasure ha) ∧
    ∀ W : LinkWindow a, Continuous fun q : W.Assignments × GaugeField a => W.glue ha q.1 q.2
def PlaquetteProperties (a : ℝ) : Prop :=
  (∀ (p : ElementaryPlaquette a) (U : GaugeField a), faceEnergy U p ∈ Icc (0 : ℝ) 2) ∧
  (∀ (p : ElementaryPlaquette a) (U : GaugeField a) (e₀ e₁ e₂ e₃ : Link a),
    ({e₀.initial, e₁.initial, e₂.initial, e₃.initial} : Set (LatticePoint a)) = p.cornerSet →
    e₀.terminal = e₁.initial → e₁.terminal = e₂.initial → e₂.terminal = e₃.initial →
    e₃.terminal = e₀.initial →
    (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
      ((U e₀ * U e₁ * U e₂ * U e₃ : Matrices.ComplexMatrix2.specialUnitary) :
        Matrices.ComplexMatrix2)).re =
      (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
        (faceHolonomy U p : Matrices.ComplexMatrix2)).re) ∧
  (∀ (p : ElementaryPlaquette a) (e : Link a),
    e ∈ p.linkSet ↔ e.IsPositivelyOriented ∧ e.initial ∈ p.cornerSet ∧ e.terminal ∈ p.cornerSet) ∧
  (∀ (p : ElementaryPlaquette a), ∀ x ∈ p.cornerSet, ∃ e ∈ p.linkSet, x = e.initial ∨ x = e.terminal) ∧
  (∀ p : ElementaryPlaquette a,
    (fun U : GaugeField a => (faceEnergy U p : ℂ)) ∈ continuousLocalFunctions a ∧
      DependsOnlyOn p.linkSet fun U : GaugeField a => (faceEnergy U p : ℂ)) ∧
  (∀ W : LinkWindow a, (facesMeeting (W.links : Set (Link a))).Finite)
def SpecificationProperties (ha : 0 < a) (β : ℝ) : Prop :=
  ∀ W : LinkWindow a,
    (∀ F : GaugeField a → ℂ, IsBoundedObservable F → ∀ U,
      W.ConditionalExpectationWellDefined ha β F U ∧
        W.conditionalExpectationTrace ha β F U = W.conditionalExpectation ha β F U) ∧
    (∀ U : GaugeField a, W.traceBoltzmannWeight β U =
      Real.exp (β * ((facesMeeting (W.links : Set (Link a))).ncard : ℝ)) *
        W.localWeight β U) ∧
    (∀ F H : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable H →
      W.conditionalExpectation ha β (F + H) =
        W.conditionalExpectation ha β F + W.conditionalExpectation ha β H) ∧
    (∀ (c : ℂ) (F : GaugeField a → ℂ), IsBoundedObservable F →
      W.conditionalExpectation ha β (c • F) = c • W.conditionalExpectation ha β F) ∧
    (∀ F : GaugeField a → ℂ, IsBoundedObservable F → (∀ U, 0 ≤ F U) →
      ∀ U, 0 ≤ W.conditionalExpectation ha β F U) ∧
    (W.conditionalExpectation ha β (fun _ => 1) = fun _ => 1) ∧
    (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      IsBoundedObservable (W.conditionalExpectation ha β F) ∧
        Measurable[W.exteriorSigma] (W.conditionalExpectation ha β F) ∧
        observableSupNorm (W.conditionalExpectation ha β F) ≤ observableSupNorm F) ∧
    (∀ F H : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable H →
      Measurable[W.exteriorSigma] H →
      W.conditionalExpectation ha β (F * H) = H * W.conditionalExpectation ha β F) ∧
    (∀ (F : GaugeField a → ℂ) (Fs : ℕ → GaugeField a → ℂ), IsBoundedObservable F →
      (∀ n, IsBoundedObservable (Fs n)) → (∀ U, Tendsto (fun n => Fs n U) atTop (𝓝 (F U))) →
      BddAbove (range fun n => observableSupNorm (Fs n)) →
      (∀ U, Tendsto (fun n => W.conditionalExpectation ha β (Fs n) U) atTop
        (𝓝 (W.conditionalExpectation ha β F U))) ∧
      BddAbove (range fun n => observableSupNorm (W.conditionalExpectation ha β (Fs n)))) ∧
    (∀ F ∈ continuousLocalFunctions a,
      W.conditionalExpectation ha β F ∈ continuousLocalFunctions a) ∧
    (∀ ν : Measure (GaugeField a), IsProbabilityMeasure ν →
      ∃ ν' : Measure (GaugeField a), IsProbabilityMeasure ν' ∧
        (∀ E : Set (GaugeField a), MeasurableSet E →
          ((ν' E).toReal : ℂ) =
            stateEval ν (W.conditionalExpectation ha β (E.indicator 1))) ∧
        ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
          stateEval ν' F = stateEval ν (W.conditionalExpectation ha β F))
def LocalFunctionProperties (a : ℝ) : Prop :=
  (∀ F ∈ continuousLocalFunctions a, ∀ H ∈ continuousLocalFunctions a,
    F + H ∈ continuousLocalFunctions a ∧ F * H ∈ continuousLocalFunctions a) ∧
  (∀ (c : ℂ), ∀ F ∈ continuousLocalFunctions a, c • F ∈ continuousLocalFunctions a) ∧
  (∀ c : ℂ, (fun _ => c) ∈ continuousLocalFunctions a) ∧
  (∀ F ∈ continuousLocalFunctions a,
    (fun U => conj (F U)) ∈ continuousLocalFunctions a) ∧
  (∀ (f : C(GaugeField a, ℂ)) (ε : ℝ), 0 < ε →
    ∃ F ∈ continuousLocalFunctions a, ∀ U, ‖f U - F U‖ < ε) ∧
  (∀ ν ν' : Measure (GaugeField a), IsProbabilityMeasure ν → IsProbabilityMeasure ν' →
    (∀ F ∈ continuousLocalFunctions a, stateEval ν F = stateEval ν' F) → ν = ν') ∧
  (∀ (F : GaugeField a → ℂ) (L₁ L₂ : Set (Link a)), IsBoundedObservable F →
    IsLocalObservable F → IsLinkSet L₁ → IsLinkSet L₂ → DependsOnlyOn L₁ F →
    DependsOnlyOn L₂ F → DependsOnlyOn (L₁ ∩ L₂) F) ∧
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F → IsLocalObservable F →
    DependsOnlyOn (observableSupport F) F ∧
      IsLinkSet (observableSupport F) ∧ (observableSupport F).Finite ∧
      ∀ M : Set (Link a), IsLinkSet M → M.Finite → DependsOnlyOn M F →
        observableSupport F ⊆ M)
def GaugeTransformProperties (a : ℝ) : Prop :=
  ∀ g g' : GaugeTransform a,
    (∀ (U : GaugeField a) (e : Link a), g.act U e.opposite = (g.act U e)⁻¹) ∧
    (∀ (U : GaugeField a) (p : ElementaryPlaquette a), faceHolonomy (g.act U) p =
      g.toFun p.corner * faceHolonomy U p * (g.toFun p.corner)⁻¹) ∧
    (∀ p : ElementaryPlaquette a, g.pullback (fun U : GaugeField a => faceEnergy U p) =
      fun U : GaugeField a => faceEnergy U p) ∧
    (∀ U : GaugeField a, (g * g').act U = g.act (g'.act U)) ∧
    IsHomeomorph g.act ∧
    ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      IsBoundedObservable (g.pullback F) ∧
        (g * g').pullback F = g'.pullback (g.pullback F)
def PeriodicMeasuresCubicInvariance (ha : 0 < a) (β : ℝ) : Prop :=
  (∀ Q : AddSubgroup (LatticePoint a), Q.FiniteIndex → ∀ v : LatticePoint a, Q.index • v ∈ Q) ∧
  ∀ ν ∈ periodicGibbsClass ha β, ∃ k : ℕ, 1 ≤ k ∧
    ∀ v : LatticePoint a, IsSymmetricUnder ν (shift (k • v))
def MeasurableIffDependsOnly (a : ℝ) : Prop :=
  (∀ (M : Set (Link a)) (F : GaugeField a → ℂ), IsLinkSet M → IsBoundedObservable F →
    (Measurable[linkSigma M] F ↔ DependsOnlyOn M F)) ∧
  (∀ S : Set AmbientSpace, (regionSigma S : MeasurableSpace (GaugeField a)) =
    linkSigma (linksInside a S)) ∧
  (∀ S : Set AmbientSpace, regionObservables a S =
    {F | IsBoundedObservable F ∧ DependsOnlyOn (linksInside a S) F}) ∧
  ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    (IsLocalObservable F ↔ ∃ M : Set (Link a), IsLinkSet M ∧ M.Finite ∧ DependsOnlyOn M F)
def LatticeSymmetryProperties (a : ℝ) : Prop :=
  ∀ r r' : LatticeSymmetry a,
    BijOn (fun e => (r.linkMap e).orientedRepresentative) (positiveLinks a) (positiveLinks a) ∧
    (∀ e ∈ positiveLinks a, (r.linkMap (r'.linkMap e).orientedRepresentative).orientedRepresentative =
      ((r.comp r').linkMap e).orientedRepresentative) ∧
    (∀ M : Set (Link a), IsLinkSet M →
      r.linkImage (r'.linkImage M) = (r.comp r').linkImage M) ∧
    (∀ (M : Set (Link a)) (F : GaugeField a → ℂ), IsLinkSet M → IsBoundedObservable F →
      DependsOnlyOn M F →
      DependsOnlyOn (r.linkImage M) (r.actOn F)) ∧
    r.actOn '' continuousLocalFunctions a = continuousLocalFunctions a ∧
    (∀ F : GaugeField a → ℂ, IsBoundedObservable F → IsLocalObservable F →
      observableSupport (r.actOn F) = r.linkImage (observableSupport F)) ∧
    ∀ ν : Measure (GaugeField a), IsProbabilityMeasure ν →
      IsProbabilityMeasure (ν.map r.pullbackField) ∧
      (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        stateEval (ν.map r.pullbackField) F = stateEval ν (r.actOn F)) ∧
      (IsSymmetricUnder ν r ↔ ∀ F ∈ continuousLocalFunctions a,
        stateEval ν (r.actOn F) = stateEval ν F)
def FiniteHaarIntegralsBounded (a : ℝ) : Prop :=
  ∀ (S : Type) [Finite S] (Φ : (S → Matrices.ComplexMatrix2.specialUnitary) × GaugeField a → ℂ),
    Measurable[borel ((S → Matrices.ComplexMatrix2.specialUnitary) × GaugeField a)] Φ →
    (∃ C : ℝ, ∀ q, ‖Φ q‖ ≤ C) →
    IsBoundedObservable (fun U => ∫ g, Φ (g, U) ∂Matrices.ComplexMatrix2.haarPi S) ∧
      observableSupNorm (fun U => ∫ g, Φ (g, U) ∂Matrices.ComplexMatrix2.haarPi S) ≤ ⨆ q, ‖Φ q‖ ∧
      (Continuous Φ → Continuous fun U => ∫ g, Φ (g, U) ∂Matrices.ComplexMatrix2.haarPi S)
end InfiniteLattice
end YangMills.Construction
