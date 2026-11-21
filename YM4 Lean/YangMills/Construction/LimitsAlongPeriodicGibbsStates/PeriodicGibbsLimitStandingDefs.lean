import YangMills.Construction.GrowingTori.DefinitionsForSequencesOfGrowingTori
import YangMills.Construction.InfiniteLattice.LimitsAlongTheCutoffs
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.Parameters.NumbersOfTheConstruction
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicGibbsLimits
open ParameterChoice FlowConstants InfiniteLattice
structure LimitParameters where
  constants : ParameterChoice.DerivedConstants
  external : ParameterChoice.ExternalConstants
  constants_admissible : ParameterChoice.AdmissibleConstants constants external
  choice : ParameterChoice.FullChoice
  admissible : Conventions.IsAdmissibleBlockingFactor choice.L
  order : ParameterChoice.ChoiceOrderConditions constants external choice
  sourceRadius :
    ParameterChoice.SourceRadiusFloors constants external choice.toChoiceUpToCoupling choice.ϱ
  shapeConst_eq : constants.ϑ₀ = TwoPoints.Shapes.shapeConst
  shape_eq : choice.ϑ = constants.ϑ₀
  activityKind : PeriodicLattice.ActivityDomainKind
namespace LimitParameters
variable (D : LimitParameters)
abbrev L : ℕ := D.choice.L
def toGrowthParameters : GrowingTori.GrowthParameters where
  constants := D.constants
  choice := D.choice
  admissible :=
    { factor_admissible := D.admissible
      M_eq_pow := D.order.admissible.M_power
      exponent_lowerBound := D.order.admissible.exponentLowerBound
      c₂_nonneg := D.order.admissible.c₂_nonneg
      Cβ_nonneg := D.order.ranges.Cβ_nonneg
      CPrime_pos := D.order.ranges.CPrime_pos
      γ_pos := D.order.ranges.γ_pos
      γH_pos := D.order.ranges.γH_pos
      γH_le_ceiling :=
        GrowingTori.highThresholdCeiling_of_couplingConstraints D.order.couplings
      γJ_pos := D.order.thresholds.γJ_pos
      γJ_le_γH := D.order.thresholds.γJ_le_γH
      gap_lowerBound := D.order.admissible.gapLowerBound }
  activityKind := D.activityKind
end LimitParameters
structure LimitData extends LimitParameters where
  g : ℝ
  g_pos : 0 < g
  g_le : g ≤ choice.γJ
structure CutoffSequence (D : LimitData) where
  point : ℕ+ → GrowingTori.FirstPassagePoint D.toGrowthParameters D.g
  cutoff_tend : CutoffLimits.CutoffsTendToTop fun j => (point j).K
namespace CutoffSequence
variable {D : LimitData} (Q : CutoffSequence D)
abbrev K (j : ℕ+) : ℕ+ := (Q.point j).K
abbrev β (j : ℕ+) : ℝ := (Q.point j).β
abbrev spacing (j : ℕ+) : ℝ := PeriodicLattice.meshSize D.L ((Q.K j : ℕ) : ℤ)
abbrev Fields (j : ℕ+) : Type := InfiniteLattice.GaugeField (Q.spacing j)
abbrev states (j : ℕ+) : Set (Measure (Q.Fields j)) :=
  InfiniteLattice.periodicGibbsSet D.L (Q.K j) (Q.β j)
end CutoffSequence
def complexObservable {a : ℝ} (f : InfiniteLattice.AmbientSpace → ℂ)
    (U : InfiniteLattice.GaugeField a) : ℂ :=
  ((InfiniteLattice.smearedEnergy (fun x => (f x).re) U : ℝ) : ℂ) +
    Complex.I * ((InfiniteLattice.smearedEnergy (fun x => (f x).im) U : ℝ) : ℂ)
end YangMills.Construction.PeriodicGibbsLimits
end
