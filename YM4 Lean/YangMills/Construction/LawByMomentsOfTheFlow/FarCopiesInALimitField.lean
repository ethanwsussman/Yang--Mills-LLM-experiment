import YangMills.Construction.FreeEnergiesOfTheFlow.ProductsOnATowerDefs
import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldOfThePoint
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.ResponseInTheExpansion.FunctionsOfTheCases
import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
structure IsQuasiLocalCaseFunction {n : ℕ} [NeZero n] (R : StepSettings.StepSetup) (o : TorusFields.TorusSite (n * R.params.side))
    (Rr a : ℕ) (Sz : ℝ) (A : Finset (TorusFields.TorusSite (n * R.params.side)))
    (sz : R.labels.Ω → ℝ) (F : WeightedResponses.CaseFunction R n) : Prop where
  mem_ball : ∀ y ∈ A, y ∈ ResponseInTheExpansion.supBall o (Rr : ℝ)
  weight_measurable : Measurable sz
  weight_nonneg : ∀ w, 0 ≤ sz w
  weight_gauge : ∀ (Y : Finset (TorusFields.TorusSite (n * R.params.side))) (g : TorusFields.TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion)
    (ω : Y → R.labels.Ω) (y : Y), sz (R.labels.act Y g ω y) = sz (ω y)
  abs_le : ∀ W Yt ωt bad b, |F W Yt ωt bad b| ≤ Sz * (1 + ∑ y ∈ A, WeightedResponses.siteScore sz Yt ωt y) ^ a
  measurable : ∀ (Yt : Finset (TorusFields.TorusSite (n * R.params.side))) (bad : Finset (TorusFields.TorusBond (n * R.params.side)))
    (b : StepCosts.BaseChoice R.params.side n),
    Measurable fun p : TorusFields.TorusField (n * R.params.side) × (Yt → R.labels.Ω) => F p.1 Yt p.2 bad b
  gaugeInvariant : WeightedResponses.IsGaugeInvariantCase F
  sub_le_of_agree : ∀ (m : ℕ), (TorusLumps.clusterRange R.coupling : ℝ) / 64 ≤ m → ∀ W W' Yt Yt' ωt ωt' bad bad' b b',
    WeightedResponses.IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
    WeightedResponses.IsLiveState R.params R.coupling R.labelWeight W' Yt' ωt' →
    (∀ c : TorusFields.TorusBond (n * R.params.side), c.1 ∈ ResponseInTheExpansion.supBall o ((Rr : ℝ) + m) →
      c.1 + TorusFields.unitStep (n * R.params.side) c.2 ∈ ResponseInTheExpansion.supBall o ((Rr : ℝ) + m) →
      W c.1 c.2 = W' c.1 c.2 ∧ (c ∈ bad ↔ c ∈ bad')) →
    (∀ y ∈ ResponseInTheExpansion.supBall o ((Rr : ℝ) + m), (y ∈ Yt ↔ y ∈ Yt') ∧
      ∀ (hy : y ∈ Yt) (hy' : y ∈ Yt'), ωt ⟨y, hy⟩ = ωt' ⟨y, hy'⟩) →
    (∀ c, (TorusFields.supDist (TorusLumps.toTorusSite (F := TorusLumps.stepBlockFrame R.params.side n) (j := 1) n c)
      (TorusLumps.parentBlock R.params.side o) : ℝ) ≤ Rr → b c = b' c) →
    |F W Yt ωt bad b - F W' Yt' ωt' bad' b'| ≤
      Sz * (1 + ∑ y ∈ A, WeightedResponses.siteScore sz Yt ωt y) ^ a * Real.exp (-(R.params.decayRate * (m : ℝ)))
def supportWeightOfSample {ℓ : TorusLumps.StepParameters} (T : WeightedResponses.StageTower ℓ) (u n : ℕ) [NeZero n]
    (A : Finset (TorusFields.TorusSite (n * ℓ.side))) (sz : (T.stage u).labels.Ω → ℝ)
    (x : WeightedResponses.MarkedSample ℓ (u + 1) n) : ℝ :=
  1 + ∑ y ∈ A, WeightedResponses.siteScore sz (WeightedResponses.stageState T u (n * ℓ.side) x.1).2.1
    (WeightedResponses.stageState T u (n * ℓ.side) x.1).2.2 y
def IsMeasurableAbove {Λ : MomentParameters} (S : MomentPoint Λ) (v : ℕ)
    (g : WeightedResponses.MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side) → ℝ) : Prop :=
  ∀ (d : ℕ) (h : v + d = S.data.windowLevel), @Measurable _ _ (ResponseInTheExpansion.upperSigma S.tower v d (S.data.period Λ.stepParams.side)) _
    fun w : WeightedResponses.MarkedSample Λ.stepParams (v + d) (S.data.period Λ.stepParams.side) => g (h ▸ w)
def farCopiesConditionalStatement : Prop :=
  ForAllHullParameters fun Λ => ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S) (u : ℕ) (hu : ∀ i, u + 1 ≤ (F.points i).data.windowLevel)
    (Φ : ∀ i, TorusFields.TorusField ((F.points i).sideAtLevel (u + 1)) →
      WeightedResponses.CaseFunction ((F.points i).tower.stage u).toStepSetup ((F.points i).sideAtLevel (u + 1)))
    (Rr a : ℕ) (Sz : ℝ) (A : ∀ i, Finset (TorusFields.TorusSite ((F.points i).sideAtLevel (u + 1) * Λ.stepParams.side)))
    (o : ∀ i, TorusFields.TorusSite ((F.points i).sideAtLevel (u + 1) * Λ.stepParams.side))
    (sz : ∀ i, ((F.points i).tower.stage u).labels.Ω → ℝ) (jX jE jR : F.Index),
    (∀ i V, IsQuasiLocalCaseFunction ((F.points i).tower.stage u).toStepSetup (o i) Rr a Sz (A i) (sz i) (Φ i V)) →
    (∀ i, Measurable (FreeEnergies.caseLift (F.points i).tower u _ (Φ i))) →
    (∀ i, ∀ᵐ x ∂(WeightedResponses.markedSampleLaw (F.points i).tower (F.points i).β (u + 1) ((F.points i).sideAtLevel (u + 1))),
      FreeEnergies.CaseIntegrableAtSample (F.points i).tower u _ (Φ i) x) →
    (∃ C : ℝ, ∀ i, ∫⁻ x, ENNReal.ofReal (supportWeightOfSample (F.points i).tower u _ (A i) (sz i) x)
      ∂(WeightedResponses.markedSampleLaw (F.points i).tower (F.points i).β (u + 1) ((F.points i).sideAtLevel (u + 1))) ≤ ENNReal.ofReal C) →
    (∀ i w, F.observables jX (F.points i) w =
      FreeEnergies.caseLift (F.points i).tower u _ (Φ i) ((F.points i).sampleAtLevel (u + 1) (hu i) w)) →
    (∀ i w, F.observables jE (F.points i) w =
      FreeEnergies.caseMeanAtSample (F.points i).tower u _ (Φ i) ((F.points i).sampleAtLevel (u + 1) (hu i) w)) →
    (∃ C : ℝ, ∀ i w, |F.observables jR (F.points i) w| ≤ C) →
    (∀ i, IsMeasurableAbove (F.points i) (u + 1) (F.observables jR (F.points i))) →
    F.condMean (fun v => v (jR, 0) * v (jX, 0)) =ᵐ[F.law] F.condMean (fun v => v (jR, 0) * v (jE, 0))
end YangMills.Construction.MomentLaw
end
