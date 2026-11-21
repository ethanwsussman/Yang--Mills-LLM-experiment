import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAStep
import YangMills.Construction.ResponseInTheExpansion.ExpansionOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.ScoresOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace WeightedResponses
variable {n : ℕ}
structure ResponseSetup (R : StepSettings.StepSetup) where
  responseParams : ResponseParameters
  coeff : ℝ
  score : R.labels.Ω → ℝ
  cold : ColdResponse R.params.side R.depth
  hull : HullResponse R.params.side R.depth R.labels.Ω
  siteRemainder : TorusLumps.LocalDensity
  totalRemainder : TorusLumps.LocalDensity
structure ResponseSetup.IsAdmissible {R : StepSettings.StepSetup} (A : ResponseSetup R) : Prop where
  params_admissible : A.responseParams.Admissible R.params
  price : PriceBoundsScore R.params R.coupling R.labels R.clusterFactor R.siteDensity A.score
  bounds : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score
    A.cold A.hull A.siteRemainder A.totalRemainder
  abs_coeff_le : |A.coeff| ≤ 2
abbrev CaseFunction (R : StepSettings.StepSetup) (n : ℕ) : Type :=
  (W : TorusFields.TorusField (n * R.params.side)) → (Yt : Finset (TorusFields.TorusSite (n * R.params.side))) →
    (Yt → R.labels.Ω) → Finset (TorusFields.TorusBond (n * R.params.side)) → StepCosts.BaseChoice R.params.side n → ℝ
section Mean
variable (R : StepSettings.StepSetup) [NeZero n]
def caseTerm (C : Finset (TorusFields.TorusSite n)) (V : TorusFields.TorusField n) (q : StepSettings.CoarseState R n)
    (F : CaseFunction R n) (bad : Finset (TorusFields.TorusBond (n * R.params.side)))
    (Yt : Finset (TorusFields.TorusSite (n * R.params.side))) (b : StepCosts.BaseChoice R.params.side n)
    (W : TorusFields.TorusField (n * R.params.side)) (ν : q.unlabelled Yt → R.labels.Ω) : ℝ :=
  open Classical in
  if TorusLumps.IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
      StepSettings.coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
    F (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b *
      StepSettings.stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b
  else 0
def caseIntegral (C : Finset (TorusFields.TorusSite n)) (V : TorusFields.TorusField n)
    (q : StepSettings.CoarseState R n) (F : CaseFunction R n) : ℝ :=
  ∑ bad ∈ (StepSettings.markedBonds R C).powerset, ∑ Yt : Finset (TorusFields.TorusSite (n * R.params.side)),
    ∑ b : StepCosts.BaseChoice R.params.side n,
    ∫ W, ∫ ν : q.unlabelled Yt → R.labels.Ω, caseTerm R C V q F bad Yt b W ν
      ∂(Measure.pi fun _ => R.labels.μ) ∂(TorusFields.fieldHaar (n * R.params.side))
def caseMean (C : Finset (TorusFields.TorusSite n)) (V : TorusFields.TorusField n)
    (q : StepSettings.CoarseState R n) (F : CaseFunction R n) : ℝ :=
  caseIntegral R C V q F / StepSettings.coarseStateWeight R C V q
def CaseIntegrable (C : Finset (TorusFields.TorusSite n)) (V : TorusFields.TorusField n)
    (q : StepSettings.CoarseState R n) (F : CaseFunction R n) : Prop :=
  ∀ bad ∈ (StepSettings.markedBonds R C).powerset, ∀ (Yt : Finset (TorusFields.TorusSite (n * R.params.side)))
    (b : StepCosts.BaseChoice R.params.side n),
    Integrable (fun p : TorusFields.TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
        caseTerm R C V q F bad Yt b p.1 p.2)
      ((TorusFields.fieldHaar (n * R.params.side)).prod (Measure.pi fun _ => R.labels.μ))
end Mean
section Response
variable {R : StepSettings.StepSetup} (A : ResponseSetup R) [NeZero n]
def blockBondScores (W : TorusFields.TorusField (n * R.params.side)) (V : TorusFields.TorusField n)
    (b : StepCosts.BaseChoice R.params.side n) (Y : TorusFields.TorusSite n) : ℝ :=
  ∑ i : Fin 4, (bondScore R.params R.coupling W V b (Y, i) +
    bondScore R.params R.coupling W V b (Y - TorusFields.unitStep n i, i))
def caseResponse (V : TorusFields.TorusField n) (Y : TorusFields.TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) : CaseFunction R n :=
  fun W Yt ωt _ b =>
    ∑ y ∈ TorusLumps.sitesInBlocks R.params.side {Y}, A.hull (n * R.params.side) y W Yt ωt h +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h * blockBondScores W V b Y
end Response
def ResponseSetup.coldStep {R : StepSettings.StepSetup} (A : ResponseSetup R) :
    ColdResponse R.params.side (R.depth + 1) :=
  fun n _ Y V h => caseMean R ∅ V (StepGas.emptyCoarseState R) (caseResponse A V Y h)
def ResponseSetup.hullStep {R : StepSettings.StepSetup} (A : ResponseSetup R) :
    HullResponse R.params.side (R.depth + 1) (TorusLumps.CoarseLabel R.labels.Ω R.params.side) :=
  fun n _ Y V Y' ω' h => caseMean R (StepSettings.hotCoreSites R V) V ⟨Y', ω'⟩ (caseResponse A V Y h)
def coarseLabelScore {Ω : Type} {L : ℕ} (s₁ : ℝ) (s : Ω → ℝ) : TorusLumps.CoarseLabel Ω L → ℝ
  | Sum.inl _ => s₁
  | Sum.inr st => s₁ + ∑ o : TorusLumps.BlockOffset L, Sum.elim (fun _ => 0) s (st.siteLabel o)
end WeightedResponses
end YangMills.Construction
end
