import YangMills.Construction.Continuum.ComplexComponentsOfSeparatedTuples
import YangMills.Construction.InfiniteLattice.ObservablesAndIsometriesAtOneSpacing
import YangMills.Construction.InfiniteLattice.ReflectionFormOfAPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.RepresentativeOfATupleAtACutoff
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CutoffRepresentative
def SymmetryTransportsFacesAndSmearedEnergies {a : ℝ} (g : LatticeSymmetry a) : Prop :=
  (∀ p : ElementaryPlaquette a, ∃! q : ElementaryPlaquette a, q.cornerSet = g.pointMap '' p.cornerSet) ∧
  (∀ ρ : ElementaryPlaquette a → ElementaryPlaquette a,
    (∀ p, (ρ p).cornerSet = g.pointMap '' p.cornerSet) →
    Function.Bijective ρ ∧
    (∀ p, (ρ p).center = g.toFun p.center) ∧
    ∀ p, g.actOn (fun A : GaugeField a => faceEnergy A p) =
      fun A : GaugeField a => faceEnergy A (ρ p)) ∧
  (∀ f : AmbientSpace → ℝ, IsBoundedBorelCompactlySupported f →
    g.actOn (smearedEnergy f) =
      (smearedEnergy (g.pushforwardFun f) : GaugeField a → ℝ)) ∧
  ∀ f : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported f →
    g.actOn (smearedEnergy f) =
      (smearedEnergy (g.pushforwardFun f) : GaugeField a → ℂ)
def CentredProductRealSymmetricMultilinear (L K : ℕ)
    (ν : Measure (CutoffLattice.FieldsAt L K)) : Prop :=
  (∀ (X : SeparatedTuples.SepTuple) (A : CutoffLattice.FieldsAt L K),
    (centredProductLinear L K ν (SeparatedTuples.basisVec X) A).im = 0) ∧
  (∀ X Y : SeparatedTuples.SepTuple, X.1.Perm Y.1 →
    centredProduct L K ν (TupleLists.ofList X) = centredProduct L K ν (TupleLists.ofList Y)) ∧
  ∀ (n : ℕ) (X X' X'' : TestSpaces.SepTupleOfCard n) (i : Fin n) (c' c'' : ℝ),
    (∀ j, j ≠ i → X.1 j = X'.1 j ∧ X.1 j = X''.1 j) →
    X.1 i = c' • X'.1 i + c'' • X''.1 i →
    centredProduct L K ν ⟨n, X⟩ =
      c' • centredProduct L K ν ⟨n, X'⟩ + c'' • centredProduct L K ν ⟨n, X''⟩
def CentredProductMulConjSingle (L K : ℕ)
    (ν : Measure (CutoffLattice.FieldsAt L K)) : Prop :=
  (∀ Φ Ψ : SeparatedTuples.FormalSpan, R4TupleForms.FormalMulDefined Φ Ψ →
    centredProductLinear L K ν (SeparatedTuples.formalMul Φ Ψ) =
      centredProductLinear L K ν Φ * centredProductLinear L K ν Ψ) ∧
  (∀ (Φ : SeparatedTuples.FormalSpan) (A : CutoffLattice.FieldsAt L K),
    conj (centredProductLinear L K ν Φ A) =
      centredProductLinear L K ν (SeparatedTuples.conjugation Φ) A) ∧
  ∀ (f : ComplexTestFunctions.ComplexValued) (hf : ComplexTestFunctions.IsC1cComplex f)
    (A : CutoffLattice.FieldsAt L K),
    centredProductLinear L K ν (ComplexTupleComponents.singleSpan f hf) A =
      ComplexTupleComponents.complexObservable f A - ∫ B, ComplexTupleComponents.complexObservable f B ∂ν
def CentredProductCalculus : Prop :=
  ∀ s : Conventions.StandingParameters, ∀ ν : Measure (CutoffLattice.FieldsAt s.L s.K),
    IsProbabilityMeasure ν →
    (∀ g : LatticeSymmetry (CutoffLattice.spacingAt s.L s.K),
      SymmetryTransportsFacesAndSmearedEnergies g) ∧
    CentredProductRealSymmetricMultilinear s.L s.K ν ∧
    CentredProductMulConjSingle s.L s.K ν ∧
    (∀ g : LatticeSymmetry (CutoffLattice.spacingAt s.L s.K), IsSymmetricUnder ν g →
      ∀ Φ : SeparatedTuples.FormalSpan,
      g.actOn (centredProductLinear s.L s.K ν Φ) =
        centredProductLinear s.L s.K ν (SeparatedTuples.pushSpan g.toFun Φ)) ∧
    ∀ (t : halfSpacingTimes (CutoffLattice.spacingAt s.L s.K)) (δ : ℝ),
      CutoffLattice.spacingAt s.L s.K / 2 < δ →
      ∀ Φ ∈ SeparatedTuples.spanIn {x : AmbientSpace | (t : ℝ) + δ ≤ x timeAxis},
        centredProductLinear s.L s.K ν Φ ∈ localObsAbove t
end YangMills.Construction.InfiniteLattice.CutoffRepresentative
end
