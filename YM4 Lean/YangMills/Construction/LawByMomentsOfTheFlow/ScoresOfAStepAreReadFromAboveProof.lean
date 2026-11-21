import YangMills.Construction.FreeEnergiesOfTheFlow.CompletedObservablesAreBounded
import YangMills.Construction.LawByMomentsOfTheFlow.ScoresOfAStepAreReadFromAbove
import YangMills.Construction.ResponseInTheExpansion.StatesAreReadFromAbove
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusLumps TorusFields WeightedResponses ResponseInTheExpansion FreeEnergies LevelTestFunctions StepSettings
section Samples
variable {ℓ : StepParameters}
private theorem stageState_fst (T : StageTower ℓ) : ∀ (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s n),
    (stageState T s n u).1 = topField ℓ s n u
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private theorem fst_cast_succ {a b n : ℕ} (h : a = b) (h' : a + 1 = b + 1) (w : MarkedSample ℓ (a + 1) n) :
    (h' ▸ w : MarkedSample ℓ (b + 1) n).1 = (h ▸ w.1 : MarkedSample ℓ b (n * ℓ.side)) := by
  subst h
  rfl
private theorem cast_cast_eq {a b c n : ℕ} (h₁ : a = b) (h₂ : b = c) (h₃ : a = c) (w : MarkedSample ℓ a n) :
    (h₂ ▸ (h₁ ▸ w : MarkedSample ℓ b n) : MarkedSample ℓ c n) = h₃ ▸ w := by
  subst h₁
  subst h₂
  rfl
private theorem sourceTerm_measurable_base (hStates : upperSigmaDeterminesStatesStatement)
    (hBound : completedObservablesBounded)
    (hadm : ℓ.Admissible) (T : StageTower ℓ) (coef : ℕ → ℝ) (v c n : ℕ) [NeZero n]
    (g : PlaquetteWeight (fineSide ℓ.side (v + c + 1) n)) :
    Measurable[upperSigma T v (c + 1) n] (sourceTerm T coef (v + c) n g) := by
  have hq := (hStates ℓ hadm T v c (n * ℓ.side)).2
  let mX : MeasurableSpace (MarkedSample ℓ (v + c + 1) n) := upperSigma T v (c + 1) n
  have hfst : @Measurable _ _ mX (upperSigma T v c (n * ℓ.side))
      (fun u : MarkedSample ℓ (v + c + 1) n => u.1) :=
    (comap_measurable _).mono le_sup_left le_rfl
  have hsnd : @Measurable _ _ mX inferInstance (fun u : MarkedSample ℓ (v + c + 1) n => u.2) :=
    (comap_measurable _).mono le_sup_right le_rfl
  have htop : @Measurable _ _ mX inferInstance
      (fun u : MarkedSample ℓ (v + c + 1) n => topField ℓ (v + c) (n * ℓ.side) u.1) := by
    have hfun : (fun u : MarkedSample ℓ (v + c + 1) n => topField ℓ (v + c) (n * ℓ.side) u.1) =
        fun u => (stageState T (v + c) (n * ℓ.side) u.1).1 := by
      funext u
      exact (stageState_fst T _ _ _).symm
    rw [hfun]
    exact measurable_fst.comp (hq.comp hfst)
  have hJ : Measurable fun p : TorusField (n * ℓ.side) × StepOutcome ℓ n =>
      stepSourceTerm ℓ (T.stage (v + c)).coupling (coef (v + c)) (v + c) g p.1 p.2 :=
    (hBound ℓ hadm T coef (v + c) n).2.2 (T.stage (v + c)).coupling (coef (v + c)) g
  have hP : @Measurable _ (TorusField (n * ℓ.side) × StepOutcome ℓ n) mX _
      (fun u : MarkedSample ℓ (v + c + 1) n => (topField ℓ (v + c) (n * ℓ.side) u.1, u.2)) :=
    htop.prodMk hsnd
  have hR : @Measurable _ _ mX _ (fun u : MarkedSample ℓ (v + c + 1) n =>
      stepSourceTerm ℓ (T.stage (v + c)).coupling (coef (v + c)) (v + c) g
        (topField ℓ (v + c) (n * ℓ.side) u.1) u.2) :=
    @Measurable.comp _ _ _ mX _ _
      (fun p : TorusField (n * ℓ.side) × StepOutcome ℓ n =>
        stepSourceTerm ℓ (T.stage (v + c)).coupling (coef (v + c)) (v + c) g p.1 p.2)
      (fun u : MarkedSample ℓ (v + c + 1) n => (topField ℓ (v + c) (n * ℓ.side) u.1, u.2)) hJ hP
  exact hR
private theorem sourceTerm_measurable_upperSigma (hStates : upperSigmaDeterminesStatesStatement)
    (hBound : completedObservablesBounded)
    (hadm : ℓ.Admissible) (T : StageTower ℓ) (coef : ℕ → ℝ) (v c e : ℕ) :
    ∀ (D n : ℕ) [NeZero n] (hD : v + D = v + c + 1 + e)
      (g : PlaquetteWeight (fineSide ℓ.side (v + c + 1) (fineSide ℓ.side e n))),
      Measurable[upperSigma T v D n] fun w : MarkedSample ℓ (v + D) n =>
        sourceTerm T coef (v + c) (fineSide ℓ.side e n) g (sampleBelow ℓ (v + c + 1) e n (hD ▸ w)) := by
  induction e with
  | zero =>
    intro D n _ hD g
    obtain rfl : D = c + 1 := by omega
    exact sourceTerm_measurable_base hStates hBound hadm T coef v c n g
  | succ e ih =>
    intro D n _ hD g
    obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    have hD' : v + D' = v + c + 1 + e := by omega
    have ih' := ih D' (n * ℓ.side) hD' g
    have hfst : @Measurable _ _ (upperSigma T v (D' + 1) n) (upperSigma T v D' (n * ℓ.side))
        (fun u : MarkedSample ℓ (v + D' + 1) n => u.1) :=
      (comap_measurable _).mono le_sup_left le_rfl
    have hfun : (fun w : MarkedSample ℓ (v + (D' + 1)) n =>
          sourceTerm T coef (v + c) (fineSide ℓ.side (e + 1) n) g
            (sampleBelow ℓ (v + c + 1) (e + 1) n (hD ▸ w))) =
        fun w : MarkedSample ℓ (v + D' + 1) n =>
          sourceTerm T coef (v + c) (fineSide ℓ.side e (n * ℓ.side)) g
            (sampleBelow ℓ (v + c + 1) e (n * ℓ.side) (hD' ▸ w.1)) := by
      funext w
      exact congrArg (fun x => sourceTerm T coef (v + c) (fineSide ℓ.side e (n * ℓ.side)) g
        (sampleBelow ℓ (v + c + 1) e (n * ℓ.side) x)) (fst_cast_succ hD' hD w)
    rw [hfun]
    exact ih'.comp hfst
end Samples
private theorem centredStepScore_measurableAbove (hStates : upperSigmaDeterminesStatesStatement)
    (hBound : completedObservablesBounded)
    {Λ : MomentParameters} (hadm : Λ.stepParams.Admissible) (S : MomentPoint Λ) (v j : ℕ) (i : Fin Λ.k)
    (hvj : v ≤ j) :
    IsMeasurableAbove S v (centredStepScore j i S) := by
  intro d h
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hvj
  by_cases hj : v + c + 1 ≤ S.data.windowLevel
  · have hD : v + d = v + c + 1 + (S.data.windowLevel - (v + c + 1)) := by omega
    have key := sourceTerm_measurable_upperSigma hStates hBound hadm S.tower S.coeff v c
      (S.data.windowLevel - (v + c + 1)) d (S.data.period Λ.stepParams.side) hD (S.weight i _)
    have hfun : (fun w : MarkedSample Λ.stepParams (v + d) (S.data.period Λ.stepParams.side) =>
          centredStepScore (v + c) i S (h ▸ w)) =
        fun w => sourceTerm S.tower S.coeff (v + c) (S.sideAtLevel (v + c + 1)) (S.weight i _)
            (sampleBelow Λ.stepParams (v + c + 1) (S.data.windowLevel - (v + c + 1))
              (S.data.period Λ.stepParams.side) (hD ▸ w)) -
          stepMeanShift (n := S.sideAtLevel (v + c + 1)) (S.resp (v + c)) (S.weight i _) := by
      funext w
      simp only [centredStepScore, dif_pos hj, MomentPoint.sampleAtLevel]
      rw [cast_cast_eq h (Nat.add_sub_of_le hj).symm hD w]
    rw [hfun]
    exact key.sub_const _
  · have hfun : (fun w : MarkedSample Λ.stepParams (v + d) (S.data.period Λ.stepParams.side) =>
          centredStepScore (v + c) i S (h ▸ w)) = fun _ => 0 := by
      funext w
      simp only [centredStepScore, dif_neg hj]
    rw [hfun]
    exact measurable_const
theorem stepScoreMeasurableAbove_holds (hStates : upperSigmaDeterminesStatesStatement)
    (hBound : completedObservablesBounded) : stepScoreMeasurableAboveStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ d₁ _ _ _ _ Kr _
  refine ⟨Tb.floorMin, ?_⟩
  intro y hy _ _ g _ _ k _ _ _ R d _
  exact ⟨fun _ => 0, 1, y, one_pos, le_rfl, fun S v j i hvj =>
    centredStepScore_measurableAbove hStates hBound (Λ := ⟨Tb, Kr, y, g, k, R, d⟩) (d₁.fits y hy) S v j i hvj⟩
end YangMills.Construction.MomentLaw
end
