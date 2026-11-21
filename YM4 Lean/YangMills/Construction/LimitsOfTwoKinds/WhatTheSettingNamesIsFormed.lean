import YangMills.Construction.Parameters.OrderOfChoice
import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LimitsOfTwoKinds
namespace SettingWellDefined
open ParameterChoice FlowConstants AmbientPoints
open ReflectionPositivity.AxisMirror (Ambient)
structure CouplingsAndSidesWellDefined (T : DerivedConstants) (c : ChoiceUpToCoupling)
    (γJ g : ℝ) : Prop where
  windowLowerEnd_pos : 0 < windowLowerEnd T c g
  windowLowerEnd_lt : windowLowerEnd T c g < g
  le_upper : g ≤ γJ
  upper_le_γH : γJ ≤ c.γH
  γH_lt_one : c.γH < 1
  referenceTorusSide_mem_torusSides : referenceTorusSide T c g ∈ PeriodicLattice.torusSides c.L
  referenceTorusSide_mem_admissible : referenceTorusSide T c g ∈ admissibleTorusSides T c g
structure PassageDataPositive (T : DerivedConstants) (c : ChoiceUpToCoupling) (g : ℝ) :
    Prop where
  passageLevel_pos : 0 < passageLevel T c g
  pos_of_passageLevel_le : ∀ β : ℝ, passageLevel T c g ≤ β → 0 < β
  pos_of_mem_firstPassageWindow : ∀ (x : ℝ → ℕ → ℝ) (D : ℝ → ℕ∞) (K : ℕ) (β : ℝ),
    β ∈ firstPassageWindow T c x D g K → 0 < β
def BoundedReal {s : Conventions.StandingParameters} {E : Ambient} (f : Pt s E → ℝ) : Prop :=
  ∃ C : ℝ, ∀ x, |f x| ≤ C
structure TestFunctionsBoundedLipschitz (s : Conventions.StandingParameters) (E : Ambient) :
    Prop where
  c1CompactlySupported : ∀ f ∈ c1CompactlySupportedIn (univ : Set (Pt s E)),
    BoundedReal f ∧ TestFunctions.IsLipschitzFor (pointDist s E) f
  tuple_components : ∀ (n : ℕ), ∀ X ∈ separatedTuples s E n, ∀ i,
    BoundedReal (X i) ∧ TestFunctions.IsLipschitzFor (pointDist s E) (X i)
  bounded_of_lipschitz_torus : ∀ f : Pt s .torus → ℝ,
    TestFunctions.IsLipschitzFor (pointDist s .torus) f → BoundedReal f
def SubtuplesSeparated (s : Conventions.StandingParameters) (E : Ambient) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ X ∈ separatedTuples s E n, ∀ J : Finset (Fin n), J.Nonempty →
    restrictTuple X J ∈ separatedTuples s E J.card
end SettingWellDefined
open ParameterChoice SettingWellDefined in
open ReflectionPositivity.AxisMirror (Ambient) in
def SettingWellDefined.Statement : Prop :=
  (∀ (T : DerivedConstants) (N : ExternalConstants) (c : ChoiceUpToCoupling) (ϱ γJ g : ℝ),
    ChosenUpToCoupling T N c → SourceAndCorrelationThresholds T N c ϱ γJ →
      0 < g → g ≤ γJ →
        CouplingsAndSidesWellDefined T c γJ g ∧ PassageDataPositive T c g) ∧
  ∀ (s : Conventions.StandingParameters) (E : Ambient),
    TestFunctionsBoundedLipschitz s E ∧ SubtuplesSeparated s E
end YangMills.Construction.LimitsOfTwoKinds
end
