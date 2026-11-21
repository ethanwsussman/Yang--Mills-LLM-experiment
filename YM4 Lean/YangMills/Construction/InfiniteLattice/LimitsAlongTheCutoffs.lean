import YangMills.Construction.InfiniteLattice.ConnectedCorrelations
import YangMills.Construction.InfiniteLattice.PeriodicExtensionsStatesAndTorusFunctionalsAtOneSpacing
import YangMills.Construction.Lattice.RemaindersOfTheFlowOfTheConstruction
import YangMills.Construction.Parameters.OrderOfChoice
import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.CutoffLimits
open ParameterChoice FlowConstants InfiniteLattice AmbientPoints
structure Setting where
  constants : ParameterChoice.DerivedConstants
  external : ParameterChoice.ExternalConstants
  choice : ParameterChoice.FullChoice
  admissible : Conventions.IsAdmissibleBlockingFactor choice.L
  chosen : ParameterChoice.ChosenUpToCoupling constants external choice.toChoiceUpToCoupling
  activityKind : PeriodicLattice.ActivityDomainKind
  g : ℝ
  g_pos : 0 < g
  g_le : g ≤ choice.γH
namespace Setting
variable (D : Setting)
abbrev L : ℕ := D.choice.L
abbrev upToCoupling : ParameterChoice.ChoiceUpToCoupling := D.choice.toChoiceUpToCoupling
abbrev sharpWidth : ℝ := FlowConstants.widthSharp D.constants D.upToCoupling
abbrev remainders : InfiniteLattice.CutoffRemainders D.choice :=
  PeriodicLattice.CubesOfStep.constructionRemainders D.constants D.choice D.activityKind
abbrev window (K : ℕ) : Set ℝ :=
  FlowConstants.flowFirstPassageWindow D.constants D.choice K D.activityKind (D.remainders K) D.g
theorem sharpWidth_pos : 0 < D.sharpWidth := by
  have hr := D.chosen.ranges
  have hp : 0 < D.upToCoupling.γ ^ (D.upToCoupling.κ₀ - 8) :=
    Real.rpow_pos_of_pos hr.γ_pos _
  have hC := mul_pos hr.CPrime_pos hp
  have hβ := hr.Cβ_nonneg
  show 0 < FlowConstants.widthSharp D.constants D.upToCoupling
  unfold FlowConstants.widthSharp FlowConstants.flowError
  exact add_pos_of_nonneg_of_pos hβ hC
def euclideanParams : Conventions.StandingParameters := ⟨D.L, D.admissible, 1, 1⟩
abbrev SepTuples (n : ℕ) : Set (Fin n → AmbientPoints.Pt D.euclideanParams .euclidean → ℝ) :=
  AmbientPoints.separatedTuples D.euclideanParams .euclidean n
abbrev AllSepTuples : Set (AmbientPoints.FunctionTuple D.euclideanParams .euclidean) :=
  AmbientPoints.allSeparatedTuples D.euclideanParams .euclidean
end Setting
def CutoffsTendToTop (K : ℕ+ → ℕ+) : Prop :=
  ∀ t : ℝ, {j : ℕ+ | ¬ t ≤ ((K j : ℕ) : ℝ)}.Finite
structure PassageData (D : Setting) where
  K : ℕ+ → ℕ+
  β : ℕ+ → ℝ
  mem_window : ∀ j, β j ∈ D.window (K j)
namespace PassageData
variable {D : Setting} (Q : PassageData D)
theorem passageLevel_le (j : ℕ+) :
    FlowConstants.passageLevel D.constants D.upToCoupling D.g ≤ Q.β j :=
  (Q.mem_window j).1
theorem β_pos (j : ℕ+) : 0 < Q.β j :=
  (FlowConstants.passageLevel_pos D.g_pos D.sharpWidth_pos).trans_le (Q.passageLevel_le j)
def latticeAt (j : ℕ+) : FixedSpacing.Setup where
  L := D.L
  admissible := D.admissible
  level := Q.K j
  m := 1
  β := Q.β j
  β_pos := Q.β_pos j
abbrev Fields (j : ℕ+) : Type := (Q.latticeAt j).Fields
abbrev torusLimits (j : ℕ+) : Set (Measure (Q.Fields j)) := (Q.latticeAt j).torusLimits
end PassageData
structure PassageSequence (D : Setting) extends PassageData D where
  cutoff_tend : CutoffsTendToTop K
def TendsAlong {E : Type*} [SeminormedAddCommGroup E] (J : Set ℕ+) (t : J → E) (t₀ : E) :
    Prop :=
  ∀ ε : ℝ, 0 < ε → {j : J | ¬ ‖t j - t₀‖ ≤ ε}.Finite
def centredMoment {a : ℝ} (ν' ν : Measure (InfiniteLattice.GaugeField a)) {k : ℕ}
    (f : Fin k → InfiniteLattice.AmbientSpace → ℝ) : ℂ :=
  Probability.complexExpectation ν' fun U =>
    ∏ i, (((InfiniteLattice.smearedEnergy (f i) U : ℝ) : ℂ) -
      Probability.complexExpectation ν fun V => ((InfiniteLattice.smearedEnergy (f i) V : ℝ) : ℂ))
variable {D : Setting}
variable (D) in
abbrev RealFamily : Type := (n : ℕ) → 2 ≤ n → D.SepTuples n → ℝ
def blockFactor (S : RealFamily D) {n : ℕ} (f : D.SepTuples n)
    (I : Finset (Fin n)) : ℝ :=
  if h : 2 ≤ I.card then S I.card h (AmbientPoints.restrictSeparated f I) else 0
def centred (S : RealFamily D) (X : D.AllSepTuples) : ℝ :=
  ∑ π ∈ SetPartition.singletonFree X.1.1,
    ∏ I ∈ π.parts, blockFactor S ⟨X.1.2, X.2⟩ I
def IsVolumeFirstLimitWith (Q : PassageSequence D) (S : RealFamily D)
    (J : Set ℕ+) (ν : ∀ j : J, Measure (Q.Fields j)) : Prop :=
  J.Infinite ∧ (∀ j : J, ν j ∈ Q.torusLimits j) ∧
    ∀ (n : ℕ) (hn : 2 ≤ n) (X : D.SepTuples n), TendsAlong J
      (fun j => InfiniteLattice.ursellFunction (ν j) n X.1) ((S n hn X : ℝ) : ℂ)
end YangMills.Construction.CutoffLimits
end
