import YangMills.Construction.LawByMomentsOfTheFlow.FormsAtTheCutAreOfTheFarClass
import YangMills.Construction.LawByMomentsOfTheFlow.MeanAtTheCutOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.StatesOfAPointAreLive
import YangMills.Construction.ResponseInTheExpansion.BoundedFunctionsOfTheCasesAreIntegrable
import YangMills.Construction.ResponseInTheExpansion.LevelsFormStates
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepSettings StepCosts WeightedResponses ResponseInTheExpansion BlockAverages LevelTestFunctions
namespace CaseFormsQuasiLocal
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem levelSide_isBlockTorusSide {u n : ℕ} (hn : n = S.levelSide (u + 1)) (hu : u + 1 ≤ S.data.windowLevel)
    (h4 : 4096 ≤ Λ.stepParams.n₀) :
    IsBlockTorusSide Λ.stepParams n ∧ n * Λ.stepParams.side = S.levelSide u := by
  have hLpos : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ := S.side_le
  have hm : S.data.sideExponent ≠ 0 := by
    intro h0
    unfold LevelData.period at hn₀
    rw [h0, pow_zero] at hn₀
    nlinarith
  have e : n = S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (u + 1)) := hn
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [e]
    unfold LevelData.period
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ hm) _) _
  · rw [e]
    exact hn₀.trans (Nat.le_mul_of_pos_right _ (pow_pos hLpos _))
  · show n * Λ.stepParams.side = S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - u)
    have e1 : S.data.windowLevel - u = (S.data.windowLevel - (u + 1)) + 1 := by omega
    rw [e, e1, pow_succ]
    ring
private theorem mem_supBall_of_le {N : ℕ} [NeZero N] (o y : TorusSite N) {r r' : ℝ} (h : r ≤ r') (hy : y ∈ supBall o r) :
    y ∈ supBall o r' := by
  simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact hy.trans h
private theorem isQuasiLocal_of_cutoffMean {d n : ℕ} [NeZero n] {B : Finset (Fin Λ.k)} {Sz : ℝ}
    (hSz : ∀ W Yt ωt bad b, |S.goodCaseForms (S.lastSeparated + d) d n B W Yt ωt bad b| ≤ Sz)
    (hBor : ∀ Y, Measurable fun W => S.cutoffMean d (n * Λ.stepParams.side) B W Y)
    (hG : ∀ (g : TorusSite (n * Λ.stepParams.side) → UnitQuaternion) W Y,
      S.cutoffMean d (n * Λ.stepParams.side) B (gaugeTransform g W) Y = S.cutoffMean d (n * Λ.stepParams.side) B W Y)
    (hLoc : ∀ W W' Y Y', (∀ c : TorusBond (n * Λ.stepParams.side),
        c.1 ∈ supBall (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (8 * S.rangeSq) →
        c.1 + TorusFields.unitStep (n * Λ.stepParams.side) c.2 ∈
          supBall (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (8 * S.rangeSq) →
        W c.1 c.2 = W' c.1 c.2) →
      Y ∩ supBall (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (8 * S.rangeSq) =
        Y' ∩ supBall (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (8 * S.rangeSq) →
      S.cutoffMean d (n * Λ.stepParams.side) B W Y = S.cutoffMean d (n * Λ.stepParams.side) B W' Y') :
    IsQuasiLocalCaseFunction (S.tower.stage (S.lastSeparated + d)).toStepSetup
      (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) (8 * S.rangeSq + 2) 0 Sz ∅ (fun _ => 0)
      (S.goodCaseForms (S.lastSeparated + d) d n B) := by
  classical
  have hS0 : 0 ≤ Sz := (abs_nonneg _).trans
    (hSz (trivialField _) ∅ (fun y => absurd y.2 (Finset.notMem_empty _)) ∅ (fun _ => 0))
  refine
    { mem_ball := fun y hy => absurd hy (Finset.notMem_empty _)
      weight_measurable := measurable_const
      weight_nonneg := fun _ => le_rfl
      weight_gauge := fun _ _ _ _ => rfl
      abs_le := fun W Yt ωt bad b => by simpa using hSz W Yt ωt bad b
      measurable := fun Yt bad b => (hBor Yt).comp measurable_fst
      gaugeInvariant := fun W Yt ωt bad b g _ _ _ => hG g W Yt
      sub_le_of_agree := ?_ }
  intro m _ W W' Yt Yt' ωt ωt' bad bad' b b' _ _ hW hY _
  have hr : ((8 * S.rangeSq : ℕ) : ℝ) ≤ ((8 * S.rangeSq + 2 : ℕ) : ℝ) + m := by
    push_cast
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have hr' : (8 * (S.rangeSq : ℝ)) ≤ ((8 * S.rangeSq + 2 : ℕ) : ℝ) + m := by
    have := hr
    push_cast at this ⊢
    linarith
  have e : S.cutoffMean d (n * Λ.stepParams.side) B W Yt = S.cutoffMean d (n * Λ.stepParams.side) B W' Yt' := by
    refine hLoc W W' Yt Yt'
      (fun c h1 h2 => (hW c (mem_supBall_of_le _ _ hr' h1) (mem_supBall_of_le _ _ hr' h2)).1) ?_
    ext y
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨a, c⟩
      exact ⟨((hY y (mem_supBall_of_le _ _ hr' c)).1).1 a, c⟩
    · rintro ⟨a, c⟩
      exact ⟨((hY y (mem_supBall_of_le _ _ hr' c)).1).2 a, c⟩
  have e' : S.goodCaseForms (S.lastSeparated + d) d n B W Yt ωt bad b =
      S.goodCaseForms (S.lastSeparated + d) d n B W' Yt' ωt' bad' b' := e
  rw [e', sub_self, abs_zero]
  have : (0 : ℝ) ≤ Real.exp (-((S.tower.stage (S.lastSeparated + d)).toStepSetup.params.decayRate * (m : ℝ))) :=
    (Real.exp_pos _).le
  simpa using mul_nonneg hS0 this
end CaseFormsQuasiLocal
open CaseFormsQuasiLocal in
theorem caseFormsQuasiLocalStatement_holds (hM : cutoffMeanBoundsStatement) (hLive : liveStatesStatement)
    (hBI : boundedCaseFunctionIntegrableStatement) (hLv : StagesAreWellPosed) :
    caseFormsQuasiLocalStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, p₁, P₁⟩ := hM a ha
  obtain ⟨L₂, r₂, C₂, p₂, P₂⟩ := hLive a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (p₁ c) (p₂ c),
    fun L hodd hLe Tb hTa hTL hDr hCold hHalf hrt hCder => ?_⟩
  simp only [max_le_iff] at hLe hCder
  simp only [le_min_iff] at hrt
  have Q₁ := P₁ L hodd hLe.1 Tb hTa hTL hDr hCold hHalf hrt.1 hCder.1
  have Q₂ := P₂ L hodd hLe.2 Tb hTa hTL hDr hCold hHalf hrt.2 hCder.2
  obtain ⟨y₈, V₁⟩ := hLv Tb hDr
  refine fun Kr hfit => ?_
  obtain ⟨y₁, R₁⟩ := Q₁ Kr hfit
  obtain ⟨y₂, R₂⟩ := Q₂ Kr hfit
  refine ⟨max y₁ (max y₂ y₈), fun y hy hRet hWil g hg hgy k _ hk2 hk8 Rd dd hdd => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨e1, e2, e8⟩ := hy
  obtain ⟨Cm, cm, Xm, hc, hXy, Mn⟩ := R₁ y e1 hRet hWil g hg hgy k hk2 hk8 Rd dd hdd
  obtain ⟨Cl, cl, Xl, -, -, Lv⟩ := R₂ y e2 hRet hWil g hg hgy k hk2 hk8 Rd dd hdd
  refine ⟨Cm, cm, Xm, hc, hXy, fun S hx u d n _ hn hu hut hd B Sz hSz => ?_⟩
  subst hut
  obtain ⟨hbs, hside⟩ := levelSide_isBlockTorusSide S hn hu hDr.n₀_ge
  obtain ⟨-, -, hMB⟩ := Mn S hx d (n * (Tb.stepParameters y).side) hd hside
  obtain ⟨-, -, -, hBor, hG, hLoc⟩ := hMB B
  refine ⟨isQuasiLocal_of_cutoffMean S hSz hBor hG hLoc, ?_⟩
  have hforms : (S.tower.stage (S.lastSeparated + d)).toStepSetup.IsWellPosed := by
    have hFo := V₁ y e8 Kr S.β S.labelFacts S.initial S.isInitial S.data.windowLevel S.onFlow
      (S.lastSeparated + d) (by omega)
    have pack : ∀ z : StageWithResponse (Tb.stepParameters y),
        z = flowStages Tb y S.β S.labelFacts S.initial (S.lastSeparated + d) → z.1.toStepSetup.IsWellPosed := by
      rintro _ rfl
      exact hFo
    exact pack ⟨S.tower.stage (S.lastSeparated + d), S.resp (S.lastSeparated + d)⟩
      (S.stage_eq (S.lastSeparated + d) (by omega))
  refine (Lv S (S.lastSeparated + d + 1) hu n hbs).mono fun x hx' => ?_
  have h3 : 0 < coarseWeightExpansion (S.tower.stage (S.lastSeparated + d)).toStepSetup n
      (stageState S.tower (S.lastSeparated + d + 1) n x).1 (stageState S.tower (S.lastSeparated + d + 1) n x).2.1
      (stageState S.tower (S.lastSeparated + d + 1) n x).2.2 := hx'.2
  unfold coarseWeightExpansion at h3
  rw [dif_neg (NeZero.ne _)] at h3
  have hfin : coarseStateMass (S.tower.stage (S.lastSeparated + d)).toStepSetup
      (hotCoreSites (S.tower.stage (S.lastSeparated + d)).toStepSetup x.2.2.1) x.2.2.1
      (stageState S.tower (S.lastSeparated + d + 1) n x).2 ≠ ⊤ := by
    intro h
    have h4 : 0 < coarseStateWeight (S.tower.stage (S.lastSeparated + d)).toStepSetup
        (hotCoreSites (S.tower.stage (S.lastSeparated + d)).toStepSetup x.2.2.1) x.2.2.1
        (stageState S.tower (S.lastSeparated + d + 1) n x).2 := h3
    unfold coarseStateWeight at h4
    rw [h] at h4
    simp at h4
  have hn₀ : (Tb.stepParameters y).n₀ ≤ n := by
    have h5 := hbs.2
    have hLpos : 0 < (Tb.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne _)
    exact (Nat.le_mul_of_pos_left _ hLpos).trans h5
  exact hBI _ hforms n hn₀ _ _ _ hfin (S.goodCaseForms (S.lastSeparated + d) d n B) Sz
    (fun Yt bad b => (hBor Yt).comp measurable_fst) hSz
end YangMills.Construction.MomentLaw
end
