import YangMills.Construction.LawByMomentsOfTheFlow.TestFunctionsAcrossTheLevels
import YangMills.Construction.ResponseInTheExpansion.LevelsOfAFlow
import YangMills.Construction.ResponseInTheExpansion.SupportsAlongTheLevels
import YangMills.Construction.ResponseInTheExpansion.TorusBoundOfTheFlow
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps RenormalizationStepParameters StepSettings StepReturn WeightedResponses LevelTestFunctions TestFunctions
def supDist (x y : EuclideanFourSpace) : ℝ := ⨆ a : Fin 4, |x a - y a|
structure IsSupTestFamily {k : ℕ} (R d : ℝ) (φ : Fin k → EuclideanFourSpace → ℝ) : Prop where
  abs_le_one : ∀ i x, |φ i x| ≤ 1
  lipschitz : ∀ i x y, |φ i x - φ i y| ≤ supDist x y
  hasCompactSupport : ∀ i, HasCompactSupport (φ i)
  abs_coord_le : ∀ i, ∀ x ∈ tsupport (φ i), ∀ a, |x a| ≤ R
  le_supDist : ∀ i j, i ≠ j → ∀ x ∈ tsupport (φ i), ∀ y ∈ tsupport (φ j), d ≤ supDist x y
variable {k : ℕ}
instance (P : LevelData k) (L : ℕ) [NeZero L] : NeZero (P.period L) :=
  ⟨mul_ne_zero two_ne_zero (pow_ne_zero _ (NeZero.ne L))⟩
def jointCumulant {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Fin k → Ω → ℝ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin k)), (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) *
    ∏ J ∈ π.parts, ∫ ω, ∏ i ∈ J, X i ω ∂μ
structure _root_.YangMills.Construction.LevelTestFunctions.LevelData.SupAdmissible
    (P : LevelData k) (L : ℕ) (R d : ℝ) : Prop where
  isSupTestFamily : IsSupTestFamily R d P.fn
  scaleLevel_le : P.scaleLevel ≤ P.windowLevel
  support_small : 2 * R * (L : ℝ) ^ P.scaleLevel ≤ (P.period L : ℝ) / 4 * (L : ℝ) ^ P.windowLevel
  center_mem_lattice : ∃ z : Fin 4 → ℤ, ∀ a, P.center a = (z a : ℝ) / (L : ℝ) ^ P.windowLevel
  exists_ne_zero : ∀ i, ∃ p : OrientedPlaquette (P.period L * L ^ P.windowLevel), P.testWeight L i _ p.1 ≠ 0
structure MomentParameters where
  table : ParameterAssignment
  response : ResponseParameters
  floor : ℝ
  g : ℝ
  k : ℕ
  [k_ne : NeZero k]
  R : ℝ
  d : ℝ
attribute [instance] MomentParameters.k_ne
abbrev MomentParameters.stepParams (Λ : MomentParameters) : TorusLumps.StepParameters := Λ.table.stepParameters Λ.floor
structure MomentPoint (Λ : MomentParameters) where
  data : LevelData Λ.k
  β : ℝ
  tower : StageTower Λ.stepParams
  resp : ∀ t, ResponseSetup (tower.stage t).toStepSetup
  labelFacts : ∀ c : ChainStage Λ.stepParams, ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup
  initial : ResponseInTheExpansion.StageWithResponse Λ.stepParams
  supAdmissible : data.SupAdmissible Λ.stepParams.side Λ.R Λ.d
  side_le : Λ.stepParams.side * Λ.stepParams.n₀ ≤ data.period Λ.stepParams.side
  window_le : couplingWindowTop Λ.stepParams Λ.g ≤ β
  passage : IsFirstPassage Λ.stepParams (couplingWindowTop Λ.stepParams Λ.g) β data.windowLevel
  isInitial : ResponseInTheExpansion.IsInitialStage Λ.table Λ.floor β initial
  onFlow : ResponseInTheExpansion.StagesOnFlowUpTo Λ.table Λ.response Λ.floor β labelFacts initial data.windowLevel
  startsAtWilson : ResponseInTheExpansion.StageTower.StartsAtWilson tower β
  isCutoff : ColdStepAtMirrorFrames.IsCutoff (Λ.stepParams.threshold / 64) tower.base.barrierFn
  marksMeasurable : tower.MarksMeasurable
  stage_eq : ∀ t ≤ data.windowLevel, (⟨tower.stage t, resp t⟩ : ResponseInTheExpansion.StageWithResponse Λ.stepParams) =
    ResponseInTheExpansion.flowStages Λ.table Λ.floor β labelFacts initial t
  cold_zero : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (W : TorusField n) (h : PlaquetteWeight n)
    (h' : PlaquetteWeight (fineSide Λ.stepParams.side (tower.stage 0).depth n)), HEq h h' →
      (resp 0).cold n y W h' = siteResponse y W h
  hull_zero : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (W : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → (tower.stage 0).labels.Ω) (h : PlaquetteWeight n)
    (h' : PlaquetteWeight (fineSide Λ.stepParams.side (tower.stage 0).depth n)), HEq h h' →
      (resp 0).hull n y W Y ω h' = siteResponse y W h
def ForAllParameters (Q : MomentParameters → Prop) : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : ChainParameters → ℝ) (C₀ : ℝ), (∀ c, 0 < rt₀ c) ∧ ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ Tb : ParameterAssignment, Tb.coupling = a → Tb.side = L → Tb.Admissible → Tb.ColdStepHolds →
      Tb.HoldsFrom ColdRegimeEstimatesAt →
      Tb.rt ≤ rt₀ Tb.toChainParameters → C₀ ≤ Tb.derivBound → ∀ Kr : ResponseParameters,
      (∀ y : ℝ, Kr.Admissible (Tb.stepParameters y)) →
      ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ExpansionReturnsAt (Tb.stepParameters y) →
        (∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β)) →
        ∀ g : ℝ, 0 < g → y ≤ (g ^ 2)⁻¹ → ∀ (k : ℕ) [NeZero k], 2 ≤ k → k ≤ 8 → ∀ R d : ℝ, 0 < d →
          Q ⟨Tb, Kr, y, g, k, R, d⟩
def ForAllPoints (Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop) : Prop :=
  ForAllParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, Q Λ C c X₀ S
namespace MomentPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
def coupling (u : ℕ) : ℝ := (couplingFlow Λ.stepParams S.β u).1
def scaleCoupling : ℝ := S.coupling S.data.scaleLevel
open Classical in
def lastSeparated : ℕ := Nat.findGreatest (S.data.SeparatedBelow Λ.stepParams S.β) S.data.scaleLevel
abbrev levelSide (u : ℕ) : ℕ := S.data.sideAt Λ.stepParams.side u
def range : ℕ := clusterRange S.scaleCoupling
def rangeSq : ℕ := S.range ^ 2
def logIndex : ℕ := ⌈4 * Real.log S.scaleCoupling⌉₊
def coeff (j : ℕ) : ℝ := (S.resp j).coeff
def weight (i : Fin Λ.k) (m : ℕ) : PlaquetteWeight m := S.data.testWeight Λ.stepParams.side i m
def law (u n : ℕ) [NeZero n] : Measure (MarkedSample Λ.stepParams u n) := markedSampleLaw S.tower S.β u n
def supportAt (u n : ℕ) [NeZero n] (i : Fin Λ.k) : Finset (TorusSite n) :=
  ResponseInTheExpansion.weightSupportSites Λ.stepParams.side u n (S.weight i (fineSide Λ.stepParams.side u n))
def supportTotal (u n : ℕ) [NeZero n] (i : Fin Λ.k) (q : StageState S.tower u n) : ℝ :=
  ResponseInTheExpansion.supportResponseTotal (S.resp u) (S.weight i _) q.1 q.2.1 q.2.2
def state (u n : ℕ) [NeZero n] (w : MarkedSample Λ.stepParams u n) : StageState S.tower u n := stageState S.tower u n w
def meanScore (u n : ℕ) [NeZero n] (i : Fin Λ.k) (q : StageState S.tower u n) : ℝ :=
  ResponseInTheExpansion.meanSiteScore (S.resp u).score (S.supportAt u n i) q.2.1 q.2.2
def kappa (u n : ℕ) [NeZero n] (i : Fin Λ.k) : ℝ :=
  ∑ y ∈ S.supportAt u n i, (S.resp u).cold n y (trivialField n) (S.weight i _)
open Classical in
def separationError (Cn : ℝ) (t' : ℕ) (B : Finset (Fin Λ.k)) : ℝ :=
  Cn * ∑ u ∈ Finset.range t', (∑ i ∈ B, ((S.data.supportSites Λ.stepParams.side u i).card : ℝ)) ^ 2 *
    Real.exp (-(Λ.stepParams.rt * (S.data.separation Λ.stepParams.side u : ℝ) / 2 ^ 8)) *
    ∏ i ∈ B, (4 * (Λ.response.C₀ * ((S.data.supportSites Λ.stepParams.side u i).card : ℝ)))
def originSite (u n : ℕ) : TorusSite n := fun a =>
  ((round (S.data.center a * (Λ.stepParams.side : ℝ) ^ S.data.windowLevel / (Λ.stepParams.side : ℝ) ^ u) : ℤ) : ZMod n)
def radius : ℕ := sInf {b : ℕ | ∀ u, S.lastSeparated ≤ u → u ≤ S.data.windowLevel → ∀ (i : Fin Λ.k),
  ∀ y ∈ S.data.supportSites Λ.stepParams.side u i, S.data.distFromCenter Λ.stepParams.side u y ≤ b}
end MomentPoint
end YangMills.Construction.MomentLaw
end
