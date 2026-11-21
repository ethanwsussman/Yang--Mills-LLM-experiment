import YangMills.Construction.FreeEnergiesOfTheFlow.MeanScoresOverTheGasProof
import YangMills.Construction.ResponseInTheExpansion.FarVariablesSplitInASettingProof
import YangMills.Construction.ResponseInTheExpansion.GasResponseReadsItsSite
import YangMills.Construction.ResponseInTheExpansion.ResponseInTwoSettingsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open Dobrushin StepSettings StepGas RenormalizationStepParameters TorusLumps TorusFields WeightedResponses BlockAverages LumpContours
  ColdStepAtMirrorFrames
section
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem inBalls_of_chartDensity_ne_zero {s : ChartSetting R n} {η : FreeCoords s.free}
    (h : chartDensity s η ≠ 0) : s.InBalls η := by apply _root_.YangMills.SharedProofs.p4538 <;> assumption
private theorem isLiveState_of_isAdmissible
    (hexp : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hpos : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side))) {s : ChartSetting R n}
    (hs : s.IsAdmissible) (η : FreeCoords s.free) (hη : s.InBalls η) :
    IsLiveState R.params R.coupling R.labelWeight (s.field η) s.support s.labelling := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSupports.isLiveState_of_inBalls <;> assumption
private theorem chartResponse_congr (A : ResponseSetup R) (hA : A.IsAdmissible)
    (hexp : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (hpos : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side))) {s : ChartSetting R n}
    (hs : s.IsAdmissible) (y : TorusSite (n * R.params.side))
    {w w' : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))}
    (hagree : ∀ p, IsPlaquetteAt R.params.side R.depth y p → w p = w' p)
    (hcold : A.cold (n * R.params.side) y (trivialField (n * R.params.side)) w =
      A.cold (n * R.params.side) y (trivialField (n * R.params.side)) w') :
    chartResponse A s y w = chartResponse A s y w' := by
  unfold chartResponse weightedMean
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  by_cases hd : chartDensity s η = 0
  · simp [hd]
  · have hl := isLiveState_of_isAdmissible hexp hside hpos hs η (inBalls_of_chartDensity_ne_zero hd)
    have hq := hA.bounds.hull_reads (n * R.params.side) hside y _ _ _ hl w w' hagree
    simp only [centeredHullResponse, hq, hcold]
private theorem ae_isAdmissible_gibbsLaw (G : GasGround R n) {z : G.GasSpin → ℝ}
    (hw : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight z) :
    ∀ᵐ σ ∂G.gibbsLaw ∅, G.pairConstraint.IsAdmissible σ := by apply _root_.YangMills.SharedProofs.p77920 <;> assumption
private theorem allVacant_isAdmissible (G : GasGround R n) : G.pairConstraint.IsAdmissible G.allVacant :=
  fun i j _ => G.pairConstraint.vacant_compatible i j _
private theorem configSetting_allVacant (G : GasGround R n) : configSetting G G.allVacant = G.groundSetting := by
  have e : G.familyOf G.allVacant = GasFamily.empty := by
    funext θ
    unfold GasGround.familyOf GasFamily.empty GasGround.allVacant
    by_cases hθ : G.IsGasSupport θ
    · simp [hθ]
    · simp [hθ]
  unfold configSetting GasGround.groundSetting
  rw [e]
abbrev _root_.YangMills.DeltaSharedProofs.p176 := @configSetting_allVacant
end
theorem gasResponseShift_local_of_settings (hCf : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting)
    (hW : ClusterExpansionOfAStep.GasIsActivityBounded) : WeightedResponses.gasResponseShift_local := by
  obtain ⟨r₃, p₃, g₃⟩ := hW
  refine ⟨r₃, p₃, fun T hT hrt K => ?_⟩
  obtain ⟨y₃, G₃⟩ := g₃ T hT hrt
  obtain ⟨y₇, G₇⟩ := hCf T hT
  refine ⟨max (max y₃ y₇) (max T.floorMin (200 * T.B)), fun y hy R A _ hAt => ?_⟩
  intro n _ hn V hV z w w' hagree
  have ha := (le_max_left _ _).trans hy
  have hb := (le_max_right _ _).trans hy
  have hy3 : y₃ ≤ y := (le_max_left _ _).trans ha
  have hy7 : y₇ ≤ y := (le_max_right _ _).trans ha
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans hb
  have hyB : 200 * T.B ≤ y := (le_max_right _ _).trans hb
  have hR := hAt.onFamily
  have hx : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAt.abs_sub_le).2
    have h2 := hR.le_coupling
    linarith
  have hadm : R.params.Admissible := hR.params_eq ▸ hT.fits y hy0
  have hexp : R.HasExpansions := hR.isStep.1
  have hL : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hnL : R.params.n₀ ≤ n * R.params.side := hn.trans (Nat.le_mul_of_pos_right _ hL)
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have htriv : IsCold R.params.threshold (trivialField (n * R.params.side)) := by
    intro x μ ν _
    simp [curvature, holonomy_trivialField, hadm.σ_pos]
  have hpos : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side)) :=
    hexp.1.positive (n * R.params.side) hnL _ htriv
  have hA := hAt.admissible
  have hcold : A.cold (n * R.params.side) z (trivialField (n * R.params.side)) w =
      A.cold (n * R.params.side) z (trivialField (n * R.params.side)) w' :=
    hA.bounds.cold_reads (n * R.params.side) hnL z _ htriv w w' hagree
  have hG : (coldCaseGround R V).IsAdmissibleGround := Or.inl ⟨hn, hV, rfl, rfl, rfl⟩
  have hw : (coldCaseGround R V).pairConstraint.IsActivityBounded ((coldCaseGround R V).referenceMeasure ∅)
      (coldCaseGround R V).weight ((coldCaseGround R V).spinActivity T.gasRate) :=
    G₃ y hy3 R hR hx n (coldCaseGround R V) hG _
  have hset := G₇ y hy7 R hR hx n (coldCaseGround R V) hG
  have reads : ∀ s : ChartSetting R n, s.IsAdmissible → chartResponse A s z w = chartResponse A s z w' :=
    fun s hs => chartResponse_congr A hA hexp.2 hside hpos hs z hagree hcold
  unfold gasResponseShift
  have e1 : (coldCaseGround R V).expectation ∅
        (fun σ => chartResponse A (configSetting (coldCaseGround R V) σ) z w) =
      (coldCaseGround R V).expectation ∅
        (fun σ => chartResponse A (configSetting (coldCaseGround R V) σ) z w') := by
    refine integral_congr_ae ?_
    filter_upwards [ae_isAdmissible_gibbsLaw (coldCaseGround R V) hw] with σ hσ
    exact reads _ (hset σ hσ)
  have e2 : (coldCaseGround R V).groundSetting.IsAdmissible := by
    rw [← configSetting_allVacant]
    exact hset _ (allVacant_isAdmissible _)
  rw [e1, reads _ e2]
end YangMills.Construction.ResponseInTheExpansion
end
