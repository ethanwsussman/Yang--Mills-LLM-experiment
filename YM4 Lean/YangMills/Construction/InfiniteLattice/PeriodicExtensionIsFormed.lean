import YangMills.Construction.InfiniteLattice.CoveringPeriodicExtensionsAndTheTwoSetsOfStates
import YangMills.Construction.Lattice.ToriLatticesNormsAndFunctionsOfFinitelyManyVariables
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.LiftFormation
open YangMills.Construction.InfiniteLattice YangMills.Construction.CutoffLattice
variable (L m K : ℕ)
abbrev TorusGaugeFields : Type := PeriodicLattice.CompactGaugeField L m (K : ℤ)
def liftMap (U : TorusGaugeFields L m K) : FieldsAt L K :=
  pullbackField L m K U.1
def torusWilson (β : ℝ) : Measure (TorusGaugeFields L m K) :=
  (PeriodicLattice.wilsonGibbsMeasure L m K β).comap fun U : TorusGaugeFields L m K => U.1
def LinkImages : Prop :=
  (∀ b : Link (spacingAt L K),
    ((projectLink L m (K : ℤ) b).source : PeriodicLattice.FourTorus L m) = torusCover L m b.initial ∧
      ((projectLink L m (K : ℤ) b).target : PeriodicLattice.FourTorus L m) = torusCover L m b.terminal ∧
      projectLink L m (K : ℤ) b.opposite = (projectLink L m (K : ℤ) b).opposite) ∧
    ∀ (U : TorusGaugeFields L m K) (b : Link (spacingAt L K)),
      ((liftMap L m K U b : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
        U.1 (projectLink L m (K : ℤ) b)
def PushforwardIntegral (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (β : ℝ) : Prop :=
  ∀ F : FieldsAt L K → E, Measurable F → (∃ C : ℝ, ∀ U, ‖F U‖ ≤ C) →
    Measurable (F ∘ liftMap L m K) ∧
      (∃ C : ℝ, ∀ U, ‖(F ∘ liftMap L m K) U‖ ≤ C) ∧
      integralAgainst (periodizedMeasure L m K β) F =
        ∫ U, (F ∘ liftMap L m K) U ∂torusWilson L m K β
def MeasuresAndPushforward (β : ℝ) : Prop :=
  IsProbabilityMeasure (torusWilson L m K β) ∧
    (torusWilson L m K β).map (fun U : TorusGaugeFields L m K => U.1) =
      PeriodicLattice.wilsonGibbsMeasure L m K β ∧
    (torusWilson L m K β).map (liftMap L m K) = periodizedMeasure L m K β ∧
    IsProbabilityMeasure (periodizedMeasure L m K β) ∧
    PushforwardIntegral L m K ℝ β ∧ PushforwardIntegral L m K ℂ β
def Statement : Prop :=
  ∀ s : Conventions.StandingParameters, ∀ β : ℝ, 0 < β →
    LinkImages s.L s.m s.K ∧
      Continuous (liftMap s.L s.m s.K) ∧
      MeasuresAndPushforward s.L s.m s.K β
end YangMills.Construction.LiftFormation
