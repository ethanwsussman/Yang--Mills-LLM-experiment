import YangMills.Construction.InfiniteLattice.CoveringOfTheLatticeOfACutoff
import YangMills.Construction.InfiniteLattice.PeriodicExtensionsOfTheLatticeOfACutoff
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set InfiniteLattice
namespace CutoffLinks
namespace CutoffData
variable (d : CutoffData)
def periodLattice : Set AmbientSpace := range (TestFunctions.latticeTranslate d.side)
def periodInvariantFields : Set (GaugeField d.spacing) :=
  {U' | ∀ (b : Link d.spacing) (v : LatticePoint d.spacing), (v : AmbientSpace) ∈ d.periodLattice →
    U' (CutoffLattice.translateLink b v) = U' b}
def sideAtExp (q : ℕ+) : d.sideSet := ⟨PeriodicLattice.torusSide d.L q, q, q.pos, rfl⟩
abbrev periodizedAtExp (q : ℕ+) : Measure (GaugeField d.spacing) :=
  (d.withSide (d.sideAtExp q)).periodizedWilsonMeasure
def IsWeakLimitAlongExps (ν : d.FieldProb) : Prop :=
  ∃ (i : ℕ → ℕ+) (ρ : ℕ → d.FieldProb), StrictMono i ∧
    (∀ j, (ρ j).1 = d.periodizedAtExp (i j)) ∧
      d.TendstoWeaklyComplex ρ ν
def IsClusterAlongExps (ν : d.FieldProb) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ F : Fin n → C(GaugeField d.spacing, ℂ), ∀ ε : ℝ, 0 < ε → ∀ i₀ : ℕ+,
    ∃ i : ℕ+, i₀ ≤ i ∧ ∀ s : Fin n,
      ‖(∫ U, F s U ∂d.periodizedAtExp i) - ν.expect (F s)‖ < ε
def IsSubseqWeakLimit (ν : d.FieldProb) : Prop :=
  ∃ (φ : ℕ → ℕ) (ρ : ℕ → d.FieldProb), StrictMono φ ∧
    (∀ j, (ρ j).1 = d.periodizedAtExp (φ j).succPNat) ∧
      d.TendstoWeaklyComplex ρ ν
end CutoffData
def LiftImageAndPeriodizedLimits : Prop :=
  ∀ d : CutoffData,
    ((∀ b : Link d.spacing, ∀ v ∈ d.periodLattice, ∃ b' : Link d.spacing,
        (b'.initial : AmbientSpace) = (b.initial : AmbientSpace) + v ∧
          (b'.terminal : AmbientSpace) = (b.terminal : AmbientSpace) + v) ∧
      Function.Injective d.liftField ∧
      range d.liftField = d.periodInvariantFields ∧
      d.periodInvariantFields = periodicFields d.L d.m ((d.K : ℕ) : ℤ) ∧
      IsClosed d.periodInvariantFields ∧
      d.periodizedWilsonMeasure d.periodInvariantFields = 1) ∧
    (∀ ν : d.FieldProb,
      (ν ∈ d.torusWeakLimits ↔ d.IsWeakLimitAlongExps ν) ∧
        (ν ∈ d.torusWeakLimits ↔ d.IsClusterAlongExps ν)) ∧
    ((∀ (U : d.PeriodicFields) (b : Link d.spacing),
        d.liftField U b = U.linkValue (d.projLink b)) ∧
      BijOn d.liftField univ (periodicFields d.L d.m ((d.K : ℕ) : ℤ)) ∧
      IsProbabilityMeasure d.periodizedWilsonMeasure ∧
      (∀ E : Set (GaugeField d.spacing), MeasurableSet E →
        d.periodizedWilsonMeasure E =
          PeriodicLattice.wilsonGibbsMeasure d.L d.m d.K d.coupling
            {U | ∃ h : U ∈ PeriodicLattice.compactGaugeFields d.L d.m ((d.K : ℕ) : ℤ),
              d.liftField ⟨U, h⟩ ∈ E}) ∧
      {ν | d.IsSubseqWeakLimit ν} = d.torusWeakLimits ∧
      {ν | d.IsClusterAlongExps ν} = d.torusWeakLimits)
end CutoffLinks
end YangMills.Construction
end
