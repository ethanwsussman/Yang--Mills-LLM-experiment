import YangMills.Construction.CellOfTheFlow.TheLowerSumReadsItsCellProof
import YangMills.Construction.ResponseInTheExpansion.ComparisonFromBoundsOfAMoveProof
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfAStepFallsByHalfProof
import YangMills.Construction.ResponseInTheExpansion.FluctuationsOverAColdBoxAreBorel
import YangMills.Construction.ResponseInTheExpansion.RowSumsOfTheFunctionals
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheLocalChainProof
import YangMills.Construction.ResponseInTheExpansion.StatesAreReadFromAbove
import YangMills.Construction.ResponseInTheExpansion.TheCovarianceOfAStepIsBounded
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsAGaussianChain
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsASumOverTheLevels
import YangMills.Construction.ResponseInTheExpansion.TheFlowHasATower
import YangMills.Construction.ResponseInTheExpansion.TheLocalEventIsLikely
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours WeightedResponses TorusLumps TorusFields RenormalizationStepParameters StepSettings StepMarks StepReturn
  ClusterExpansionOfAStep MarkedIntegrals StepCosts
namespace ResponseInTheExpansion
open Classical
section Casts
variable {ℓ : StepParameters}
private def castD {s s' : ℕ} (h : s = s') (n : ℕ) (u : MarkedSample ℓ s n) : MarkedSample ℓ s' n := h ▸ u
private theorem castD_fst {s s' : ℕ} (h : s = s') (n : ℕ) (u : MarkedSample ℓ (s + 1) n) :
    (castD (congrArg (· + 1) h) n u).1 = castD h (n * ℓ.side) u.1 := by
  subst h; rfl
private theorem topField_castD {s s' : ℕ} (h : s = s') (n : ℕ) (u : MarkedSample ℓ s n) :
    topField ℓ s' n (castD h n u) = topField ℓ s n u := by
  subst h; rfl
end Casts
section Levels
variable {ℓ : StepParameters} (T : StageTower ℓ) (k : ℕ) (nn ρ₀ ρA : ℝ)
private def levelTerm (j : ℕ) : (d n : ℕ) → [NeZero n] → MarkedSample ℓ (k + d) n → TorusSite (fineSide ℓ.side d n) →
    (TorusSite n → UnitQuaternion) → TorusPlaquette (fineSide ℓ.side d n) → imaginaryQuaternions
  | 0, _, _, _, _, _, _ => 0
  | d + 1, n, _, u, o, g, p =>
    if d = j then
      ∑ b : TorusBond (n * ℓ.side), adjointTransport ℓ.coupling ρA ℓ.side k d (n * ℓ.side) (curlFunctional p) b •
        deviationInGauge T (k + d) g
          (supBall (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀)) u.2.2.1
          (topField ℓ (k + d) (n * ℓ.side) u.1) b
    else levelTerm j d (n * ℓ.side) u.1 o
      (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ (topField ℓ (k + d) (n * ℓ.side) u.1) x) p
private theorem levelTerm_of_lt {j d : ℕ} (h : j < d) (n : ℕ) [NeZero n] (u : MarkedSample ℓ (k + (d + 1)) n)
    (o : TorusSite (fineSide ℓ.side (d + 1) n)) (g : TorusSite n → UnitQuaternion) (p : TorusPlaquette (fineSide ℓ.side (d + 1) n)) :
    levelTerm T k nn ρ₀ ρA j (d + 1) n u o g p = levelTerm T k nn ρ₀ ρA j d (n * ℓ.side) u.1 o
      (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ (topField ℓ (k + d) (n * ℓ.side) u.1) x) p := by
  rw [levelTerm, if_neg (by omega)]
private theorem fluctuationSum_eq : ∀ (d n : ℕ) [NeZero n] (u : MarkedSample ℓ (k + d) n)
    (o : TorusSite (fineSide ℓ.side d n)) (g : TorusSite n → UnitQuaternion) (p : TorusPlaquette (fineSide ℓ.side d n)),
    levelFluctuationSum T k nn ρ₀ ρA d n u o g p = ∑ j ∈ Finset.range d, levelTerm T k nn ρ₀ ρA j d n u o g p := by
  intro d
  induction d with
  | zero =>
    intro n _ u o g p
    simp [levelFluctuationSum]
  | succ d ih =>
    intro n _ u o g p
    rw [levelFluctuationSum]
    refine (congrArg (· + _) (ih (n * ℓ.side) u.1 o _ p)).trans ?_
    rw [Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [levelTerm_of_lt T k nn ρ₀ ρA (Finset.mem_range.1 hj)]
    · rw [levelTerm, if_pos rfl]
private def wAt (a : ℕ) : (e n : ℕ) → MarkedSample ℓ (k + (a + e)) n → MarkedSample ℓ (k + a) (fineSide ℓ.side e n)
  | 0, _, u => u
  | e + 1, n, u => wAt a e (n * ℓ.side) u.1
private def gAt (a : ℕ) : (e n : ℕ) → MarkedSample ℓ (k + (a + e)) n → (TorusSite n → UnitQuaternion) →
    TorusSite (fineSide ℓ.side e n) → UnitQuaternion
  | 0, _, _, g => g
  | e + 1, n, u, g => gAt a e (n * ℓ.side) u.1
      (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ (topField ℓ (k + (a + e)) (n * ℓ.side) u.1) x)
private def oAt (a : ℕ) : (e n : ℕ) → TorusSite (fineSide ℓ.side (a + e) n) → TorusSite (fineSide ℓ.side e n)
  | 0, n, o => siteAbove ℓ.side a n o
  | e + 1, n, o => oAt a e (n * ℓ.side) o
private def lAt (j : ℕ) : (e n : ℕ) → [NeZero n] → TorusPlaquette (fineSide ℓ.side (j + 1 + e) n) →
    TorusBond (fineSide ℓ.side e n * ℓ.side) → ℝ
  | 0, n, _, p => adjointTransport ℓ.coupling ρA ℓ.side k j (n * ℓ.side) (curlFunctional p)
  | e + 1, n, _, p => lAt j e (n * ℓ.side) p
private theorem levelTerm_eq (j : ℕ) : ∀ (e n : ℕ) [NeZero n] (w : MarkedSample ℓ (k + (j + 1 + e)) n)
    (o : TorusSite (fineSide ℓ.side (j + 1 + e) n)) (g : TorusSite n → UnitQuaternion)
    (p : TorusPlaquette (fineSide ℓ.side (j + 1 + e) n)),
    levelTerm T k nn ρ₀ ρA j (j + 1 + e) n w o g p =
      ∑ b : TorusBond (fineSide ℓ.side e n * ℓ.side), lAt k ρA j e n p b •
        deviationInGauge T (k + j) (gAt k (j + 1) e n w g)
          (supBall (oAt (j + 1) e n o) (ballRadius ℓ.side nn ρ₀ (j + 1) - 3 * ρ₀))
          (wAt k (j + 1) e n w).2.2.1
          (topField ℓ (k + j) (fineSide ℓ.side e n * ℓ.side) (wAt k (j + 1) e n w).1) b := by
  intro e
  induction e with
  | zero =>
    intro n _ w o g p
    show levelTerm T k nn ρ₀ ρA j (j + 1) n w o g p = _
    rw [levelTerm, if_pos rfl]
    rfl
  | succ e ih =>
    intro n _ w o g p
    show levelTerm T k nn ρ₀ ρA j (j + 1 + e + 1) n w o g p = _
    rw [levelTerm_of_lt T k nn ρ₀ ρA (by omega)]
    exact ih (n * ℓ.side) w.1 o _ p
end Levels
section Events
variable {ℓ : StepParameters} (T : StageTower ℓ) (k : ℕ) (m : ℝ)
private def missAt (j : ℕ) : (d n : ℕ) → [NeZero n] → MarkedSample ℓ (k + d) n → TorusSite (fineSide ℓ.side d n) → Prop
  | 0, _, _, _, _ => True
  | d + 1, n, _, u, o =>
    if d = j then
      FreeCoresAvoid (T.stage (k + d)).toStepSetup (stageState T (k + d) (n * ℓ.side) u.1).2.1 u.2.2.2
        (hotCoreSites (T.stage (k + d)).toStepSetup u.2.2.1) (supBall (siteAbove ℓ.side (d + 1) n o) m)
    else missAt j d (n * ℓ.side) u.1 o
private def coldAt (j : ℕ) : (d n : ℕ) → [NeZero n] → MarkedSample ℓ (k + d) n → TorusSite (fineSide ℓ.side d n) → Prop
  | 0, _, _, _, _ => True
  | d + 1, n, _, u, o =>
    if d = j then IsColdOnBall ℓ.threshold u.2.2.1 (siteAbove ℓ.side (d + 1) n o) m
    else coldAt j d (n * ℓ.side) u.1 o
private theorem stepsMiss_iff : ∀ (d n : ℕ) [NeZero n] (u : MarkedSample ℓ (k + d) n) (o : TorusSite (fineSide ℓ.side d n)),
    StepsAvoidOrigin T k m d n u o ↔ ∀ j < d, missAt T k m j d n u o := by
  intro d
  induction d with
  | zero =>
    intro n _ u o
    simp [StepsAvoidOrigin]
  | succ d ih =>
    intro n _ u o
    have hi := ih (n * ℓ.side) u.1 o
    rw [StepsAvoidOrigin]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rw [missAt]
      split_ifs with hd
      · subst hd; exact h2
      · exact hi.1 h1 j (by omega)
    · intro h
      refine ⟨hi.2 fun j hj => ?_, ?_⟩
      · have := h j (by omega)
        rwa [missAt, if_neg (by omega)] at this
      · have := h d (by omega)
        rwa [missAt, if_pos rfl] at this
private theorem missAt_eq (j : ℕ) : ∀ (e n : ℕ) [NeZero n] (w : MarkedSample ℓ (k + (j + 1 + e)) n)
    (o : TorusSite (fineSide ℓ.side (j + 1 + e) n)),
    missAt T k m j (j + 1 + e) n w o ↔
      StepAvoids T (k + j) m (oAt (j + 1) e n o) (wAt k (j + 1) e n w) := by
  intro e
  induction e with
  | zero =>
    intro n _ w o
    show missAt T k m j (j + 1) n w o ↔ _
    rw [missAt, if_pos rfl]
    rfl
  | succ e ih =>
    intro n _ w o
    show missAt T k m j (j + 1 + e + 1) n w o ↔ _
    rw [missAt, if_neg (by omega)]
    exact ih (n * ℓ.side) w.1 o
private theorem coldAt_eq (j : ℕ) : ∀ (e n : ℕ) [NeZero n] (w : MarkedSample ℓ (k + (j + 1 + e)) n)
    (o : TorusSite (fineSide ℓ.side (j + 1 + e) n)),
    coldAt k m j (j + 1 + e) n w o ↔
      IsColdOnBall ℓ.threshold (wAt k (j + 1) e n w).2.2.1 (oAt (j + 1) e n o) m := by
  intro e
  induction e with
  | zero =>
    intro n _ w o
    show coldAt k m j (j + 1) n w o ↔ _
    rw [coldAt, if_pos rfl]
    rfl
  | succ e ih =>
    intro n _ w o
    show coldAt k m j (j + 1 + e + 1) n w o ↔ _
    rw [coldAt, if_neg (by omega)]
    exact ih (n * ℓ.side) w.1 o
end Events
section Covariances
variable {ℓ : StepParameters} (k : ℕ) (nn ρ₀ ρA : ℝ)
private def cutOf {n : ℕ} [NeZero n] (Z : Finset (TorusSite n)) (h : TorusBond (n * ℓ.side) → ℝ) :
    TorusBond (n * ℓ.side) → ℝ :=
  fun b => if parentBlock ℓ.side b.1 ∈ Z then h b else 0
private def levelCov (j : ℕ) : (d n : ℕ) → [NeZero n] → TorusPlaquette (fineSide ℓ.side d n) →
    TorusPlaquette (fineSide ℓ.side d n) → ℝ
  | 0, _, _, _, _ => 0
  | d + 1, n, _, p, p' =>
    if d = j then stepCovariance ℓ.coupling ℓ.side (k + d) n
      (adjointTransport ℓ.coupling ρA ℓ.side k d (n * ℓ.side) (curlFunctional p))
      (adjointTransport ℓ.coupling ρA ℓ.side k d (n * ℓ.side) (curlFunctional p'))
    else levelCov j d (n * ℓ.side) p p'
private def levelCovCut (j : ℕ) : (d n : ℕ) → [NeZero n] → TorusSite (fineSide ℓ.side d n) →
    TorusPlaquette (fineSide ℓ.side d n) → TorusPlaquette (fineSide ℓ.side d n) → ℝ
  | 0, _, _, _, _, _ => 0
  | d + 1, n, _, o, p, p' =>
    if d = j then stepCovariance ℓ.coupling ℓ.side (k + d) n
      (cutOf (supBall (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀))
        (adjointTransport ℓ.coupling ρA ℓ.side k d (n * ℓ.side) (curlFunctional p)))
      (cutOf (supBall (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀))
        (adjointTransport ℓ.coupling ρA ℓ.side k d (n * ℓ.side) (curlFunctional p')))
    else levelCovCut j d (n * ℓ.side) o p p'
private theorem stepsCovariance_eq : ∀ (d n : ℕ) [NeZero n] (p p' : TorusPlaquette (fineSide ℓ.side d n)),
    accumulatedCovariance ℓ.coupling ρA ℓ.side k d n (curlFunctional p) (curlFunctional p') =
      ∑ j ∈ Finset.range d, levelCov k ρA j d n p p' := by
  intro d
  induction d with
  | zero =>
    intro n _ p p'
    simp [accumulatedCovariance]
  | succ d ih =>
    intro n _ p p'
    rw [accumulatedCovariance]
    refine (congrArg (· + _) (ih (n * ℓ.side) p p')).trans ?_
    rw [Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      have : j < d := Finset.mem_range.1 hj
      rw [levelCov, if_neg (by omega)]
    · rw [levelCov, if_pos rfl]
      rfl
private theorem levelCov_eq (j : ℕ) : ∀ (e n : ℕ) [NeZero n] (p p' : TorusPlaquette (fineSide ℓ.side (j + 1 + e) n)),
    levelCov k ρA j (j + 1 + e) n p p' =
      stepCovariance ℓ.coupling ℓ.side (k + j) (fineSide ℓ.side e n) (lAt k ρA j e n p) (lAt k ρA j e n p') := by
  intro e
  induction e with
  | zero =>
    intro n _ p p'
    show levelCov k ρA j (j + 1) n p p' = _
    rw [levelCov, if_pos rfl]
    rfl
  | succ e ih =>
    intro n _ p p'
    show levelCov k ρA j (j + 1 + e + 1) n p p' = _
    rw [levelCov, if_neg (by omega)]
    exact ih (n * ℓ.side) p p'
private theorem levelCovCut_eq (j : ℕ) : ∀ (e n : ℕ) [NeZero n] (o : TorusSite (fineSide ℓ.side (j + 1 + e) n))
    (p p' : TorusPlaquette (fineSide ℓ.side (j + 1 + e) n)),
    levelCovCut k nn ρ₀ ρA j (j + 1 + e) n o p p' =
      stepCovariance ℓ.coupling ℓ.side (k + j) (fineSide ℓ.side e n)
        (cutOf (supBall (oAt (j + 1) e n o) (ballRadius ℓ.side nn ρ₀ (j + 1) - 3 * ρ₀)) (lAt k ρA j e n p))
        (cutOf (supBall (oAt (j + 1) e n o) (ballRadius ℓ.side nn ρ₀ (j + 1) - 3 * ρ₀)) (lAt k ρA j e n p')) := by
  intro e
  induction e with
  | zero =>
    intro n _ o p p'
    show levelCovCut k nn ρ₀ ρA j (j + 1) n o p p' = _
    rw [levelCovCut, if_pos rfl]
    rfl
  | succ e ih =>
    intro n _ o p p'
    show levelCovCut k nn ρ₀ ρA j (j + 1 + e + 1) n o p p' = _
    rw [levelCovCut, if_neg (by omega)]
    exact ih (n * ℓ.side) o p p'
end Covariances
section Clear
variable {ℓ : StepParameters} (T : StageTower ℓ) (m : ℝ)
private def Down (t n : ℕ) [NeZero n] (u : MarkedSample ℓ (t + 1) n) : Prop :=
  ∀ o : TorusSite n, Disjoint (stageState T (t + 1) n u).2.1 (supBall o m) →
    IsColdOnBall ℓ.threshold u.2.2.1 o m ∧ (StepAvoids T t m o u →
      (∀ o' : TorusSite (n * ℓ.side), parentBlock ℓ.side o' = o →
        Disjoint (stageState T t (n * ℓ.side) u.1).2.1 (supBall o' m)) ∧
      ∀ b ∈ chartBondsInBlocks ℓ.side (supBall o m),
        b ∉ (show Finset (TorusBond (n * ℓ.side)) from u.2.2.2) ∧
        ‖(stepDeviation T t u.2.2.1 (topField ℓ t (n * ℓ.side) u.1) b : Quaternion ℝ)‖ < ℓ.threshold / 64)
private def AllDown (s : ℕ) : (d n : ℕ) → [NeZero n] → MarkedSample ℓ (s + d) n → Prop
  | 0, _, _, _ => True
  | d + 1, n, _, u => Down T m (s + d) n u ∧ AllDown s d (n * ℓ.side) u.1
private theorem allDown_at (k j : ℕ) : ∀ (e n : ℕ) [NeZero n] (w : MarkedSample ℓ (k + (j + 1 + e)) n),
    AllDown T m k (j + 1 + e) n w → Down T m (k + j) (fineSide ℓ.side e n) (wAt k (j + 1) e n w) := by
  intro e
  induction e with
  | zero =>
    intro n _ w h
    exact h.1
  | succ e ih =>
    intro n _ w h
    exact ih (n * ℓ.side) w.1 h.2
private theorem yOff (k a : ℕ) : ∀ (e n : ℕ) [NeZero n] (w : MarkedSample ℓ (k + (a + e)) n)
    (o : TorusSite (fineSide ℓ.side (a + e) n)), AllDown T m k (a + e) n w →
    Disjoint (stageState T (k + (a + e)) n w).2.1 (supBall (siteAbove ℓ.side (a + e) n o) m) →
    (∀ j, a ≤ j → j < a + e → missAt T k m j (a + e) n w o) →
    Disjoint (stageState T (k + a) (fineSide ℓ.side e n) (wAt k a e n w)).2.1 (supBall (oAt a e n o) m) := by
  intro e
  induction e with
  | zero =>
    intro n _ w o _ h _
    exact h
  | succ e ih =>
    intro n _ w o hA hD hM
    obtain ⟨hd, hA'⟩ := hA
    have hm : StepAvoids T (k + (a + e)) m (siteAbove ℓ.side (a + e + 1) n o) w := by
      have h' : missAt T k m (a + e) (a + e + 1) n w o := hM (a + e) (by omega) (by omega)
      rwa [missAt, if_pos rfl] at h'
    have h1 := ((hd _ hD).2 hm).1 (siteAbove ℓ.side (a + e) (n * ℓ.side) o) rfl
    refine ih (n * ℓ.side) w.1 o hA' h1 fun j h2 h3 => ?_
    have h' : missAt T k m j (a + e + 1) n w o := hM j h2 (by omega)
    rwa [missAt, if_neg (by omega)] at h'
private theorem yOffTop (s : ℕ) : ∀ (d n : ℕ) [NeZero n] (w : MarkedSample ℓ (s + d) n)
    (o : TorusSite (fineSide ℓ.side d n)), AllDown T m s d n w →
    Disjoint (stageState T (s + d) n w).2.1 (supBall (siteAbove ℓ.side d n o) m) →
    StepsAvoidOrigin T s m d n w o →
    Disjoint (stageState T s (fineSide ℓ.side d n) (sampleBelow ℓ s d n w)).2.1 (supBall o m) := by
  intro d
  induction d with
  | zero =>
    intro n _ w o _ h _
    exact h
  | succ d ih =>
    intro n _ w o hA hD hS
    obtain ⟨hd, hA'⟩ := hA
    obtain ⟨hS', hm⟩ := hS
    have h1 := ((hd _ hD).2 hm).1 (siteAbove ℓ.side d (n * ℓ.side) o) rfl
    exact ih (n * ℓ.side) w.1 o hA' h1 hS'
end Clear
section EvaluationMaps
variable {ℓ : StepParameters} {Ω₀ : Type} [MeasurableSpace Ω₀]
private theorem top_of_state (T : StageTower ℓ) : ∀ (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s n),
    (stageState T s n u).1 = topField ℓ s n u
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl
private def Up (T : StageTower ℓ) (t d n : ℕ) [NeZero n] {s : ℕ} (hs : s = t + d)
    (π : Ω₀ → MarkedSample ℓ s n) : Prop :=
  @Measurable _ _ _ (upperSigma T t d n) fun ω => castD hs n (π ω)
variable {T : StageTower ℓ} {t : ℕ}
private theorem Up.fst {d n : ℕ} [NeZero n] {s : ℕ} {hs : s + 1 = t + (d + 1)}
    {π : Ω₀ → MarkedSample ℓ (s + 1) n} (h : Up T t (d + 1) n hs π) :
    Up T t d (n * ℓ.side) (Nat.succ.inj hs) fun ω => (π ω).1 := by
  have hs' : s = t + d := Nat.succ.inj hs
  subst hs'
  have h1 : @Measurable _ _ (upperSigma T t (d + 1) n) (upperSigma T t d (n * ℓ.side))
      (fun u : MarkedSample ℓ (t + d + 1) n => u.1) :=
    (comap_measurable _).mono le_sup_left le_rfl
  exact h1.comp h
private theorem Up.snd {d n : ℕ} [NeZero n] {s : ℕ} {hs : s + 1 = t + (d + 1)}
    {π : Ω₀ → MarkedSample ℓ (s + 1) n} (h : Up T t (d + 1) n hs π) :
    Measurable fun ω => (π ω).2 := by
  have hs' : s = t + d := Nat.succ.inj hs
  subst hs'
  have h1 : @Measurable _ _ (upperSigma T t (d + 1) n) _ (fun u : MarkedSample ℓ (t + d + 1) n => u.2) :=
    (comap_measurable _).mono le_sup_right le_rfl
  exact h1.comp h
private theorem Up.state {d n : ℕ} [NeZero n] {s : ℕ} {hs : s = t + d} {π : Ω₀ → MarkedSample ℓ s n}
    (h : Up T t d n hs π) (hS : Measurable[upperSigma T t d n] (stageState T (t + d) n)) :
    Measurable fun ω => stageState T s n (π ω) := by
  subst hs
  exact hS.comp h
private theorem Up.top {d n : ℕ} [NeZero n] {s : ℕ} {hs : s = t + d} {π : Ω₀ → MarkedSample ℓ s n}
    (h : Up T t d n hs π) (hS : Measurable[upperSigma T t d n] (stageState T (t + d) n)) :
    Measurable fun ω => topField ℓ s n (π ω) := by
  have h1 := measurable_fst.comp (h.state hS)
  have e : (Prod.fst ∘ fun ω => stageState T s n (π ω)) = fun ω => topField ℓ s n (π ω) :=
    funext fun ω => top_of_state T s n (π ω)
  rwa [e] at h1
private theorem Up.down (e : ℕ) : ∀ (M N : ℕ) [NeZero N] {s : ℕ} (hs : s = t + e) (hs' : s + M = t + (e + M))
    (π : Ω₀ → MarkedSample ℓ (s + M) N), Up T t (e + M) N hs' π →
    Up T t e (fineSide ℓ.side M N) hs fun ω => sampleBelow ℓ s M N (π ω) := by
  intro M
  induction M with
  | zero =>
    intro N _ s hs hs' π h
    exact h
  | succ M ih =>
    intro N _ s hs hs' π h
    exact ih (N * ℓ.side) hs (Nat.succ.inj hs') (fun ω => (π ω).1) (Up.fst (hs := hs') h)
end EvaluationMaps
section OnASet
variable {Ω₀ : Type} [MeasurableSpace Ω₀]
private def MO (C : Set Ω₀) (f : Ω₀ → ℝ) : Prop := Measurable (C.indicator f)
variable {C : Set Ω₀}
private theorem MO.congr {f g : Ω₀ → ℝ} (h : MO C f) (hfg : ∀ ω ∈ C, f ω = g ω) : MO C g := by
  have : C.indicator f = C.indicator g := by
    funext ω
    by_cases hω : ω ∈ C
    · simp [hω, hfg ω hω]
    · simp [hω]
  unfold MO
  rw [← this]
  exact h
private theorem MO.add {f g : Ω₀ → ℝ} (hf : MO C f) (hg : MO C g) : MO C (fun ω => f ω + g ω) := by
  have : C.indicator (fun ω => f ω + g ω) = fun ω => C.indicator f ω + C.indicator g ω := by
    funext ω
    by_cases hω : ω ∈ C <;> simp [hω]
  unfold MO
  rw [this]
  exact Measurable.add hf hg
private theorem MO.mul {f g : Ω₀ → ℝ} (hf : MO C f) (hg : MO C g) : MO C (fun ω => f ω * g ω) := by
  have : C.indicator (fun ω => f ω * g ω) = fun ω => C.indicator f ω * C.indicator g ω := by
    funext ω
    by_cases hω : ω ∈ C <;> simp [hω]
  unfold MO
  rw [this]
  exact Measurable.mul hf hg
private theorem MO.const (hC : MeasurableSet C) (c : ℝ) : MO C (fun _ => c) :=
  measurable_const.indicator hC
private theorem MO.of_measurable (hC : MeasurableSet C) {f : Ω₀ → ℝ} (hf : Measurable f) : MO C f :=
  hf.indicator hC
private theorem MO.sum {κ : Type} (hC : MeasurableSet C) (S : Finset κ) {f : κ → Ω₀ → ℝ}
    (hf : ∀ i ∈ S, MO C (f i)) : MO C (fun ω => ∑ i ∈ S, f i ω) := by
  induction S using Finset.induction_on with
  | empty => simpa using MO.const hC 0
  | insert a S ha ih =>
    have h1 := hf a (Finset.mem_insert_self _ _)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    simpa only [Finset.sum_insert ha] using h1.add h2
private theorem MO.prod {κ : Type} (hC : MeasurableSet C) (S : Finset κ) {f : κ → Ω₀ → ℝ}
    (hf : ∀ i ∈ S, MO C (f i)) : MO C (fun ω => ∏ i ∈ S, f i ω) := by
  induction S using Finset.induction_on with
  | empty => simpa using MO.const hC 1
  | insert a S ha ih =>
    have h1 := hf a (Finset.mem_insert_self _ _)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    simpa only [Finset.prod_insert ha] using h1.mul h2
end OnASet
section Components
private theorem imaginaryComponent_add (c : Fin 3) (X Y : imaginaryQuaternions) :
    imaginaryComponent c (X + Y) = imaginaryComponent c X + imaginaryComponent c Y := by
  fin_cases c <;> simp [imaginaryComponent]
private theorem imaginaryComponent_zero (c : Fin 3) : imaginaryComponent c (0 : imaginaryQuaternions) = 0 := by
  fin_cases c <;> rfl
private theorem imaginaryComponent_smul (c : Fin 3) (r : ℝ) (X : imaginaryQuaternions) :
    imaginaryComponent c (r • X) = r * imaginaryComponent c X := by
  fin_cases c <;> simp [imaginaryComponent]
private theorem imaginaryComponent_sum {κ : Type} (c : Fin 3) (S : Finset κ) (f : κ → imaginaryQuaternions) :
    imaginaryComponent c (∑ i ∈ S, f i) = ∑ i ∈ S, imaginaryComponent c (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [imaginaryComponent_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, imaginaryComponent_add, ih]
abbrev _root_.YangMills.SharedProofs.p4562 := @imaginaryComponent_sum
private theorem abs_imaginaryComponent_le (c : Fin 3) (X : imaginaryQuaternions) :
    |imaginaryComponent c X| ≤ ‖(X : Quaternion ℝ)‖ := by apply _root_.YangMills.SharedProofs.p13926 <;> assumption
end Components
section Terms
variable {ℓ : StepParameters} {Ω₀ : Type} [MeasurableSpace Ω₀]
open scoped Quaternion
private def adjQ (c : Fin 3) (q w : ℍ[ℝ]) : ℝ := ![(q * w * star q).imI, (q * w * star q).imJ, (q * w * star q).imK] c
private theorem imaginaryComponent_adjoint (c : Fin 3) (g : UnitQuaternion) (X : imaginaryQuaternions) :
    imaginaryComponent c (ColdStepAtMirrorFrames.adjointAction g X) = adjQ c (g : ℍ[ℝ]) (X : ℍ[ℝ]) := by
  fin_cases c <;> rfl
private theorem measurable_adj {G : Ω₀ → UnitQuaternion} (hG : Measurable G) {X : Ω₀ → ℍ[ℝ]}
    (hX : MeasurableQuaternion X) (c : Fin 3) : Measurable fun ξ => adjQ c (G ξ : ℍ[ℝ]) (X ξ) := by
  have hc : ∀ f : ℍ[ℝ] → ℝ, Continuous f → Measurable fun ξ => f (G ξ : ℍ[ℝ]) :=
    fun f hf => (hf.comp continuous_subtype_val).measurable.comp hG
  have g0 := hc _ Quaternion.continuous_re
  have g1 := hc _ Quaternion.continuous_imI
  have g2 := hc _ Quaternion.continuous_imJ
  have g3 := hc _ Quaternion.continuous_imK
  obtain ⟨x0, x1, x2, x3⟩ := hX
  fin_cases c <;> simp only [adjQ, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star] <;> measurability
private theorem measurable_pathHolonomy {F : BlockFrame} {j : ℕ} (X : Ω₀ → F.GaugeField j)
    (hX : ∀ x i, Measurable fun a => X a x i) (x : F.Site j) (l : List PathStep) :
    Measurable fun a => pathHolonomy (X a) x l := by
  induction l generalizing x with
  | nil => exact measurable_const
  | cons st r ih =>
    simp only [pathHolonomy]
    refine Measurable.mul ?_ (ih _)
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      exact (hX _ _).inv
    · simp only [linkValue, if_true]
      exact hX _ _
abbrev _root_.YangMills.SharedProofs.p6492 := @measurable_pathHolonomy
private theorem measurable_readAtLevel (F : BlockFrame) (j : ℕ) {n : ℕ} {W : Ω₀ → TorusField n} (hW : Measurable W)
    (x : F.Site j) (i : Fin 4) : Measurable fun a => readAtLevel F j (W a) x i :=
  (measurable_pi_apply i).comp ((measurable_pi_apply _).comp hW)
private theorem measurable_blockTreeGauge {n : ℕ} {W : Ω₀ → TorusField (n * ℓ.side)} (hW : Measurable W)
    (x : TorusSite (n * ℓ.side)) : Measurable fun a => blockTreeGauge ℓ (W a) x := by
  unfold blockTreeGauge axialGauge
  exact measurable_pathHolonomy _ (fun x i => measurable_readAtLevel _ _ hW x i) _ _
private theorem measurable_axialGaugeAt {n : ℕ} {V : Ω₀ → TorusField n} (hV : Measurable V) (o z : TorusSite n) :
    Measurable fun a => axialGaugeAt ℓ (V a) o z := by
  unfold axialGaugeAt ColdStepAtMirrorFrames.axialGaugeHolonomy
  exact measurable_pathHolonomy _ (fun x i => measurable_readAtLevel _ _ hV x i) _ _
private theorem measurable_curvature {n : ℕ} {V : Ω₀ → TorusField n} (hV : Measurable V) (x : TorusSite n)
    (μ ν : Fin 4) : Measurable fun a => curvature (V a) x μ ν := by
  have hc : Measurable fun g : UnitQuaternion => ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1‖ :=
    ((continuous_subtype_val.sub continuous_const).norm).measurable
  have hp : Measurable fun a => holonomy (V a) x μ ν := by
    have h : ∀ (y : TorusSite n) (i : Fin 4), Measurable fun a => V a y i :=
      fun y i => (measurable_pi_apply i).comp ((measurable_pi_apply y).comp hV)
    unfold holonomy
    exact (((h _ _).mul (h _ _)).mul (h _ _).inv).mul (h _ _).inv
  exact hc.comp hp
abbrev _root_.YangMills.SharedProofs.p35643 := @measurable_curvature
private theorem measurable_liftGauge {n : ℕ} {g : Ω₀ → TorusSite n → UnitQuaternion} (hg : Measurable g)
    {W : Ω₀ → TorusField (n * ℓ.side)} (hW : Measurable W) :
    Measurable fun a => fun x : TorusSite (n * ℓ.side) => g a (parentBlock ℓ.side x) * blockTreeGauge ℓ (W a) x :=
  measurable_pi_lambda _ fun x => ((measurable_pi_apply _).comp hg).mul (measurable_blockTreeGauge hW x)
private theorem term_MO (T : StageTower ℓ) (t : ℕ) {n : ℕ} [NeZero n] {C : Set Ω₀} (hC : MeasurableSet C)
    (V : Ω₀ → TorusField n) (W : Ω₀ → TorusField (n * ℓ.side)) {g : Ω₀ → TorusSite n → UnitQuaternion}
    (hg : Measurable g) (l : TorusBond (n * ℓ.side) → ℝ) (Z : Finset (TorusSite n)) (c : Fin 3)
    (X : TorusBond (n * ℓ.side) → Ω₀ → ℍ[ℝ])
    (hX : ∀ b, parentBlock ℓ.side b.1 ∈ Z → b ∈ chartBonds ℓ.side n → MeasurableQuaternion (X b))
    (hXe : ∀ ω ∈ C, ∀ b, parentBlock ℓ.side b.1 ∈ Z → b ∈ chartBonds ℓ.side n →
      X b ω = (frameDeviation ℓ (T.stage t).anchorRadius t (T.stage t).toStepSetup.frameReach (V ω) (W ω) b : ℍ[ℝ])) :
    MO C fun ω => imaginaryComponent c (∑ b, l b • deviationInGauge T t (g ω) Z (V ω) (W ω) b) := by
  have e : (fun ω => imaginaryComponent c (∑ b, l b • deviationInGauge T t (g ω) Z (V ω) (W ω) b)) =
      fun ω => ∑ b, l b * imaginaryComponent c (deviationInGauge T t (g ω) Z (V ω) (W ω) b) := by
    funext ω
    rw [imaginaryComponent_sum]
    exact Finset.sum_congr rfl fun b _ => imaginaryComponent_smul _ _ _
  rw [e]
  refine MO.sum hC _ fun b _ => ?_
  by_cases hb : parentBlock ℓ.side b.1 ∈ Z ∧ b ∈ chartBonds ℓ.side n
  · have hm : Measurable fun ω => l b * adjQ c (g ω (parentBlock ℓ.side b.1) : ℍ[ℝ]) (X b ω) :=
      (measurable_adj ((measurable_pi_apply _).comp hg) (hX b hb.1 hb.2) c).const_mul _
    refine (MO.of_measurable hC hm).congr fun ω hω => ?_
    unfold deviationInGauge
    rw [if_pos hb, imaginaryComponent_adjoint, hXe ω hω b hb.1 hb.2]
  · have : ∀ ω, deviationInGauge T t (g ω) Z (V ω) (W ω) b = 0 := fun ω => by
      unfold deviationInGauge
      rw [if_neg hb]
    refine (MO.const hC 0).congr fun ω _ => ?_
    rw [this, imaginaryComponent_zero, mul_zero]
end Terms
section EvaluationOfTheLevels
variable {ℓ : StepParameters} {Ω₀ : Type} [MeasurableSpace Ω₀]
open scoped Quaternion
private theorem measurableSet_fst' {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
private theorem measurableSet_of_fibres {X : Type} [Countable X] (f : Ω₀ → X)
    (hf : ∀ x, MeasurableSet {ω | f ω = x}) (P : X → Prop) : MeasurableSet {ω | P (f ω)} := by
  have e : {ω | P (f ω)} = ⋃ x : {x // P x}, {ω | f ω = x.1} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Subtype.exists, exists_prop, exists_eq_right']
  rw [e]
  exact MeasurableSet.iUnion fun x => hf x.1
abbrev _root_.YangMills.SharedProofs.p67002 := @measurableSet_of_fibres
private theorem fibres_pair {X X' : Type} {f : Ω₀ → X} {f' : Ω₀ → X'} (hf : ∀ x, MeasurableSet {ω | f ω = x})
    (hf' : ∀ x, MeasurableSet {ω | f' ω = x}) : ∀ x : X × X', MeasurableSet {ω | (f ω, f' ω) = x} := by apply _root_.YangMills.SharedProofs.p66564 <;> assumption
private theorem freeCores_meas (hH : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a}) (R : StepSetup) {n : ℕ} [NeZero n]
    {Yf : Ω₀ → Finset (TorusSite (n * R.params.side))} {bf : Ω₀ → Finset (TorusBond (n * R.params.side))}
    {Vf : Ω₀ → TorusField n}
    (hY : ∀ y, MeasurableSet {ω | Yf ω = y}) (hb : ∀ y, MeasurableSet {ω | bf ω = y}) (hV : Measurable Vf)
    (Z : Finset (TorusSite n)) : MeasurableSet {ω | FreeCoresAvoid R (Yf ω) (bf ω) (hotCoreSites R (Vf ω)) Z} := by
  have hC : ∀ a, MeasurableSet {ω | hotCoreSites R (Vf ω) = a} := fun a => hV (hH R n a)
  exact measurableSet_of_fibres (fun ω => (Yf ω, bf ω, hotCoreSites R (Vf ω)))
    (fibres_pair hY (fibres_pair hb hC)) (fun x => FreeCoresAvoid R x.1 x.2.1 x.2.2 Z)
variable {T : StageTower ℓ} {t : ℕ}
private theorem Up.setFibres {d n : ℕ} [NeZero n] {s : ℕ} {hs : s = t + d} {π : Ω₀ → MarkedSample ℓ s n}
    (h : Up T t d n hs π) (hS : Measurable[upperSigma T t d n] (stageState T (t + d) n))
    (y : Finset (TorusSite n)) : MeasurableSet {ω | (stageState T s n (π ω)).2.1 = y} := by
  have h1 := (measurable_snd.comp (h.state hS)) (measurableSet_fst' y)
  exact h1
private theorem Up.badFibres {d n : ℕ} [NeZero n] {s : ℕ} {hs : s + 1 = t + (d + 1)}
    {π : Ω₀ → MarkedSample ℓ (s + 1) n} (h : Up T t (d + 1) n hs π) (y : Finset (TorusBond (n * ℓ.side))) :
    MeasurableSet {ω | (show Finset (TorusBond (n * ℓ.side)) from (π ω).2.2.2) = y} := by
  have h1 : Measurable fun ω => (π ω).2.2.2 := measurable_snd.comp (measurable_snd.comp h.snd)
  have hs1 : MeasurableSet ({y} : Set (BondSet (n * ℓ.side))) := MeasurableSpace.measurableSet_top
  exact h1 hs1
private theorem Up.fieldAbove {d n : ℕ} [NeZero n] {s : ℕ} {hs : s + 1 = t + (d + 1)}
    {π : Ω₀ → MarkedSample ℓ (s + 1) n} (h : Up T t (d + 1) n hs π) : Measurable fun ω => (π ω).2.2.1 :=
  measurable_fst.comp (measurable_snd.comp h.snd)
variable (T)
private theorem stepsMiss_meas
    (hS : ∀ (t d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (stageState T (t + d) n))
    (hH : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (m : ℝ) (e : ℕ) (s : ℕ) (hs : s = t + e) : ∀ (d n : ℕ) [NeZero n] (π : Ω₀ → MarkedSample ℓ (s + d) n)
    (hs' : s + d = t + (e + d)) (o : TorusSite (fineSide ℓ.side d n)), Up T t (e + d) n hs' π →
    MeasurableSet {ω | StepsAvoidOrigin T s m d n (π ω) o} := by
  intro d
  induction d with
  | zero =>
    intro n _ π hs' o _
    simp [StepsAvoidOrigin]
  | succ d ih =>
    intro n _ π hs' o h
    have h1 := Up.fst (hs := hs') h
    have e1 : {ω | StepsAvoidOrigin T s m (d + 1) n (π ω) o} =
        {ω | StepsAvoidOrigin T s m d (n * ℓ.side) (π ω).1 o} ∩
          {ω | FreeCoresAvoid (T.stage (s + d)).toStepSetup (stageState T (s + d) (n * ℓ.side) (π ω).1).2.1
            (π ω).2.2.2 (hotCoreSites (T.stage (s + d)).toStepSetup (π ω).2.2.1)
            (supBall (siteAbove ℓ.side (d + 1) n o) m)} := rfl
    rw [e1]
    refine (ih (n * ℓ.side) _ (Nat.succ.inj hs') o h1).inter ?_
    exact freeCores_meas hH _ (fun y => h1.setFibres (hS _ _ _) y) (fun y => (Up.badFibres (hs := hs') h y))
      (Up.fieldAbove (hs := hs') h) _
private theorem missAt_meas
    (hS : ∀ (t d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (stageState T (t + d) n))
    (hH : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    (m : ℝ) (k a : ℕ) : ∀ (e n : ℕ) [NeZero n] (π : Ω₀ → MarkedSample ℓ (k + (a + e)) n)
    (hs : k + (a + e) = k + a + e) (o : TorusSite (fineSide ℓ.side (a + e) n)), Up T (k + a) e n hs π →
    MeasurableSet {ω | ∀ j, a ≤ j → j < a + e → missAt T k m j (a + e) n (π ω) o} := by
  intro e
  induction e with
  | zero =>
    intro n _ π hs o _
    have : {ω | ∀ j, a ≤ j → j < a + 0 → missAt T k m j (a + 0) n (π ω) o} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro j h1 h2
      omega
    rw [this]
    exact MeasurableSet.univ
  | succ e ih =>
    intro n _ π hs o h
    have h1 := Up.fst (hs := hs) h
    have e1 : {ω | ∀ j, a ≤ j → j < a + (e + 1) → missAt T k m j (a + (e + 1)) n (π ω) o} =
        {ω | ∀ j, a ≤ j → j < a + e → missAt T k m j (a + e) (n * ℓ.side) (π ω).1 o} ∩
          {ω | FreeCoresAvoid (T.stage (k + (a + e))).toStepSetup
            (stageState T (k + (a + e)) (n * ℓ.side) (π ω).1).2.1 (π ω).2.2.2
            (hotCoreSites (T.stage (k + (a + e))).toStepSetup (π ω).2.2.1)
            (supBall (siteAbove ℓ.side (a + e + 1) n o) m)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · intro hω
        refine ⟨fun j h2 h3 => ?_, ?_⟩
        · have h' : missAt T k m j (a + e + 1) n (π ω) o := hω j h2 (by omega)
          rwa [missAt, if_neg (by omega)] at h'
        · have h' : missAt T k m (a + e) (a + e + 1) n (π ω) o := hω (a + e) (by omega) (by omega)
          rwa [missAt, if_pos rfl] at h'
      · rintro ⟨h2, h3⟩ j h4 h5
        show missAt T k m j (a + e + 1) n (π ω) o
        rw [missAt]
        split_ifs with h6
        · subst h6; exact h3
        · exact h2 j h4 (by omega)
    rw [e1]
    refine (ih (n * ℓ.side) _ (Nat.succ.inj hs) o h1).inter ?_
    exact freeCores_meas hH _ (fun y => h1.setFibres (hS _ _ _) y) (fun y => (Up.badFibres (hs := hs) h y))
      (Up.fieldAbove (hs := hs) h) _
private theorem isCold_meas {n : ℕ} [NeZero n] {V : Ω₀ → TorusField n} (hV : Measurable V) (σ : ℝ)
    (o : TorusSite n) (m : ℝ) : MeasurableSet {ω | IsColdOnBall σ (V ω) o m} := by
  have e : {ω | IsColdOnBall σ (V ω) o m} =
      ⋂ p ∈ plaquettesIn (supBall o m), {ω | curvature (V ω) p.1 p.2.1 p.2.2 < σ} := by
    ext ω
    simp [IsColdOnBall]
  rw [e]
  exact Finset.measurableSet_biInter _ fun p _ => measurableSet_lt (measurable_curvature hV _ _ _) measurable_const
private theorem coldAt_meas
    (hS : ∀ (t d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (stageState T (t + d) n))
    (m : ℝ) (k a : ℕ) : ∀ (e n : ℕ) [NeZero n] (π : Ω₀ → MarkedSample ℓ (k + (a + e)) n)
    (hs : k + (a + e) = k + a + e) (o : TorusSite (fineSide ℓ.side (a + e) n)), Up T (k + a) e n hs π →
    MeasurableSet {ω | ∀ j, a ≤ j → j < a + e → coldAt k m j (a + e) n (π ω) o} := by
  intro e
  induction e with
  | zero =>
    intro n _ π hs o _
    have : {ω | ∀ j, a ≤ j → j < a + 0 → coldAt k m j (a + 0) n (π ω) o} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro j h1 h2
      omega
    rw [this]
    exact MeasurableSet.univ
  | succ e ih =>
    intro n _ π hs o h
    have h1 := Up.fst (hs := hs) h
    have e1 : {ω | ∀ j, a ≤ j → j < a + (e + 1) → coldAt k m j (a + (e + 1)) n (π ω) o} =
        {ω | ∀ j, a ≤ j → j < a + e → coldAt k m j (a + e) (n * ℓ.side) (π ω).1 o} ∩
          {ω | IsColdOnBall ℓ.threshold (π ω).2.2.1 (siteAbove ℓ.side (a + e + 1) n o) m} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · intro hω
        refine ⟨fun j h2 h3 => ?_, ?_⟩
        · have h' : coldAt k m j (a + e + 1) n (π ω) o := hω j h2 (by omega)
          rwa [coldAt, if_neg (by omega)] at h'
        · have h' : coldAt k m (a + e) (a + e + 1) n (π ω) o := hω (a + e) (by omega) (by omega)
          rwa [coldAt, if_pos rfl] at h'
      · rintro ⟨h2, h3⟩ j h4 h5
        show coldAt k m j (a + e + 1) n (π ω) o
        rw [coldAt]
        split_ifs with h6
        · subst h6; exact h3
        · exact h2 j h4 (by omega)
    rw [e1]
    exact (ih (n * ℓ.side) _ (Nat.succ.inj hs) o h1).inter (isCold_meas (Up.fieldAbove (hs := hs) h) _ _ _)
end EvaluationOfTheLevels
section LevelsAreRead
variable {ℓ : StepParameters} {Ω₀ : Type} [MeasurableSpace Ω₀]
open scoped Quaternion
private theorem levelTerm_zero (T : StageTower ℓ) (k : ℕ) (nn ρ₀ ρA : ℝ) (j : ℕ) : ∀ (d n : ℕ) [NeZero n], d ≤ j →
    ∀ (u : MarkedSample ℓ (k + d) n) (o : TorusSite (fineSide ℓ.side d n)) (g : TorusSite n → UnitQuaternion)
      (p : TorusPlaquette (fineSide ℓ.side d n)),
    levelTerm T k nn ρ₀ ρA j d n u o g p = 0 := by
  intro d
  induction d with
  | zero =>
    intro n _ _ u o g p
    rfl
  | succ d ih =>
    intro n _ h u o g p
    by_cases hd : d = j
    · omega
    · rw [levelTerm, if_neg hd]
      exact ih (n * ℓ.side) (by omega) _ _ _ _
private theorem mq_comp {Ξ : Type} [MeasurableSpace Ξ] {ψ : Ξ → ℍ[ℝ]} (h : MeasurableQuaternion ψ) {f : Ω₀ → Ξ}
    (hf : Measurable f) : MeasurableQuaternion fun ω => ψ (f ω) :=
  ⟨h.1.comp hf, h.2.1.comp hf, h.2.2.1.comp hf, h.2.2.2.comp hf⟩
private theorem level_MO (T : StageTower ℓ) (k : ℕ) (nn ρ₀ ρA m : ℝ) (N M₂ : ℕ)
    (hS : ∀ (t d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (stageState T (t + d) n))
    (hB : ∀ (d n : ℕ) [NeZero n] (o' : TorusSite n) (b : TorusBond (n * ℓ.side)), N ≤ n → ℓ.side ∣ n → d < M₂ →
      parentBlock ℓ.side b.1 ∈ supBall o' (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀) → b ∈ chartBonds ℓ.side n →
      MeasurableQuaternion fun p : TorusField n × TorusField (n * ℓ.side) =>
        if IsColdOnBall ℓ.threshold p.1 o' m then (stepDeviation T (k + d) p.1 p.2 b : ℍ[ℝ]) else 0)
    (a : ℕ) : ∀ (e n : ℕ) [NeZero n], N ≤ n → ℓ.side ∣ n → a + e ≤ M₂ →
    ∀ (π : Ω₀ → MarkedSample ℓ (k + (a + e)) n)
    (hs : k + (a + e) = k + a + e) (g : Ω₀ → TorusSite n → UnitQuaternion) (o : TorusSite (fineSide ℓ.side (a + e) n))
    (p : TorusPlaquette (fineSide ℓ.side (a + e) n)) (c : Fin 3) (C : Set Ω₀), MeasurableSet C → Up T (k + a) e n hs π →
    Measurable g → (∀ ω ∈ C, ∀ j, a ≤ j → j < a + e → coldAt k m j (a + e) n (π ω) o) →
    ∀ j, a ≤ j → MO C fun ω => imaginaryComponent c (levelTerm T k nn ρ₀ ρA j (a + e) n (π ω) o (g ω) p) := by
  intro e
  induction e with
  | zero =>
    intro n _ _ _ _ π hs g o p c C hC _ _ _ j hj
    refine (MO.const hC 0).congr fun ω _ => ?_
    rw [levelTerm_zero T k nn ρ₀ ρA j (a + 0) n (by omega), imaginaryComponent_zero]
  | succ e ih =>
    intro n _ hN hL hM π hs g o p c C hC hπ hg hcold j hj
    have h1 := Up.fst (hs := hs) hπ
    have hV : Measurable fun ω => (π ω).2.2.1 := Up.fieldAbove (hs := hs) hπ
    have hW : Measurable fun ω => topField ℓ (k + (a + e)) (n * ℓ.side) (π ω).1 := h1.top (hS _ _ _)
    have hpos : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
    by_cases hj' : a + e = j
    · subst hj'
      have hval : ∀ ω, levelTerm T k nn ρ₀ ρA (a + e) (a + e + 1) n (π ω) o (g ω) p =
          ∑ b : TorusBond (n * ℓ.side), adjointTransport ℓ.coupling ρA ℓ.side k (a + e) (n * ℓ.side) (curlFunctional p) b •
            deviationInGauge T (k + (a + e)) (g ω)
              (supBall (siteAbove ℓ.side (a + e + 1) n o) (ballRadius ℓ.side nn ρ₀ (a + e + 1) - 3 * ρ₀))
              (π ω).2.2.1 (topField ℓ (k + (a + e)) (n * ℓ.side) (π ω).1) b := fun ω => by
        rw [levelTerm, if_pos rfl]
      refine MO.congr ?_ (fun ω _ => (congrArg (imaginaryComponent c) (hval ω)).symm)
      set o₁ := siteAbove ℓ.side (a + e + 1) n o with ho₁
      refine term_MO T (k + (a + e)) hC (fun ω => (π ω).2.2.1)
        (fun ω => topField ℓ (k + (a + e)) (n * ℓ.side) (π ω).1) hg _ _ c
        (fun b ω => (fun p : TorusField n × TorusField (n * ℓ.side) => if IsColdOnBall ℓ.threshold p.1 o₁ m then
          (stepDeviation T (k + (a + e)) p.1 p.2 b : ℍ[ℝ]) else 0)
            ((π ω).2.2.1, topField ℓ (k + (a + e)) (n * ℓ.side) (π ω).1))
        ?_ ?_
      · intro b hb hb'
        exact mq_comp (hB (a + e) n o₁ b hN hL (by omega) hb hb') (hV.prodMk hW)
      · intro ω hω b _ _
        have h2 : coldAt k m (a + e) (a + e + 1) n (π ω) o := hcold ω hω (a + e) (by omega) (by omega)
        rw [coldAt, if_pos rfl] at h2
        show (if IsColdOnBall ℓ.threshold (π ω).2.2.1 o₁ m then _ else _) = _
        rw [if_pos h2]
        rfl
    · have hval : ∀ ω, levelTerm T k nn ρ₀ ρA j (a + e + 1) n (π ω) o (g ω) p =
          levelTerm T k nn ρ₀ ρA j (a + e) (n * ℓ.side) (π ω).1 o
            (fun x => g ω (parentBlock ℓ.side x) *
              blockTreeGauge ℓ (topField ℓ (k + (a + e)) (n * ℓ.side) (π ω).1) x) p := fun ω => by
        rw [levelTerm, if_neg hj']
      refine MO.congr ?_ (fun ω _ => (congrArg (imaginaryComponent c) (hval ω)).symm)
      refine ih (n * ℓ.side) (hN.trans (Nat.le_mul_of_pos_right n hpos)) (Dvd.intro_left n rfl) (by omega) _
        (Nat.succ.inj hs) _ o p c C hC h1 (measurable_liftGauge hg hW) ?_ j hj
      intro ω hω i h2 h3
      have h' : coldAt k m i (a + e + 1) n (π ω) o := hcold ω hω i h2 (by omega)
      rwa [coldAt, if_neg (by omega)] at h'
private theorem measurable_gaugeTransform {n : ℕ} {g : Ω₀ → TorusSite n → UnitQuaternion} (hg : Measurable g)
    {V : Ω₀ → TorusField n} (hV : Measurable V) (b : TorusBond n) :
    Measurable fun ω => gaugeTransform (g ω) (V ω) b := by
  have h : ∀ y : TorusSite n, Measurable fun ω => g ω y := fun y => (measurable_pi_apply y).comp hg
  have hv : Measurable fun ω => V ω b.1 b.2 := (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hV)
  unfold gaugeTransform
  exact ((h _).mul hv).mul (h _).inv
abbrev _root_.YangMills.SharedProofs.p20103 := @measurable_gaugeTransform
private theorem measurable_component
    (hlog : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])))
    (c : Fin 3) {G : Ω₀ → UnitQuaternion} (hG : Measurable G) :
    Measurable fun ω => imaginaryComponent c (minimalLog (G ω)) := by
  obtain ⟨-, h1, h2, h3⟩ := hlog
  fin_cases c
  · exact h1.comp hG
  · exact h2.comp hG
  · exact h3.comp hG
abbrev _root_.YangMills.SharedProofs.p57079 := @measurable_component
private theorem measurable_topLogForm
    (hlog : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])))
    {n : ℕ} [NeZero n] {V : Ω₀ → TorusField n} (hV : Measurable V) (o : TorusSite n) (r s : ℝ) (c : Fin 3)
    (b : TorusBond n) : Measurable fun ω => imaginaryComponent c (topLogForm ℓ (V ω) o r s b) := by
  have hset : MeasurableSet {ω | b.1 ∈ supBall o r ∧ ∀ z ∈ supBall o r, ∀ μ ν : Fin 4, curvature (V ω) z μ ν ≤ s} := by
    have e : {ω | b.1 ∈ supBall o r ∧ ∀ z ∈ supBall o r, ∀ μ ν : Fin 4, curvature (V ω) z μ ν ≤ s} =
        {_ω | b.1 ∈ supBall o r} ∩
          ⋂ z ∈ supBall o r, ⋂ μ : Fin 4, ⋂ ν : Fin 4, {ω | curvature (V ω) z μ ν ≤ s} := by
      ext ω
      simp
    rw [e]
    refine (MeasurableSet.const _).inter (Finset.measurableSet_biInter _ fun z _ => ?_)
    exact MeasurableSet.iInter fun μ => MeasurableSet.iInter fun ν =>
      measurableSet_le (measurable_curvature hV _ _ _) measurable_const
  have hg : Measurable fun ω => axialGaugeAt ℓ (V ω) o :=
    measurable_pi_lambda _ fun z => measurable_axialGaugeAt hV o z
  have hl := measurable_component hlog c (measurable_gaugeTransform hg hV b)
  have e : (fun ω => imaginaryComponent c (topLogForm ℓ (V ω) o r s b)) =
      fun ω => if b.1 ∈ supBall o r ∧ ∀ z ∈ supBall o r, ∀ μ ν : Fin 4, curvature (V ω) z μ ν ≤ s then
        imaginaryComponent c (minimalLog (gaugeTransform (axialGaugeAt ℓ (V ω) o) (V ω) b)) else 0 := by
    funext ω
    unfold topLogForm
    split_ifs
    · rfl
    · exact imaginaryComponent_zero c
  rw [e]
  exact Measurable.ite hset hl measurable_const
end LevelsAreRead
section Casting
variable {ℓ : StepParameters}
private theorem measurable_castD {s s' : ℕ} (h : s = s') (n : ℕ) : Measurable (castD (ℓ := ℓ) h n) := by
  subst h
  exact measurable_id
private theorem sampleBelow_castD {s s' : ℕ} (h : s = s') (d n : ℕ) (u : MarkedSample ℓ (s + d) n) :
    sampleBelow ℓ s' d n (castD (congrArg (· + d) h) n u) = castD h (fineSide ℓ.side d n) (sampleBelow ℓ s d n u) := by
  subst h
  rfl
private theorem stageState_set_castD (T : StageTower ℓ) {s s' : ℕ} (h : s = s') (n : ℕ) [NeZero n]
    (u : MarkedSample ℓ s n) : (stageState T s' n (castD h n u)).2.1 = (stageState T s n u).2.1 := by
  subst h
  rfl
private theorem freeCores_castD (T : StageTower ℓ) {s s' : ℕ} (h : s = s') (n : ℕ) [NeZero n]
    (u : MarkedSample ℓ (s + 1) n) (Z : Finset (TorusSite n)) :
    FreeCoresAvoid (T.stage s').toStepSetup (stageState T s' (n * ℓ.side) (castD (congrArg (· + 1) h) n u).1).2.1
        (castD (congrArg (· + 1) h) n u).2.2.2
        (hotCoreSites (T.stage s').toStepSetup (castD (congrArg (· + 1) h) n u).2.2.1) Z ↔
      FreeCoresAvoid (T.stage s).toStepSetup (stageState T s (n * ℓ.side) u.1).2.1 u.2.2.2
        (hotCoreSites (T.stage s).toStepSetup u.2.2.1) Z := by
  subst h
  rfl
private theorem stepsMiss_castD (T : StageTower ℓ) {s s' : ℕ} (h : s = s') (m : ℝ) (d n : ℕ) [NeZero n]
    (u : MarkedSample ℓ (s + d) n) (o : TorusSite (fineSide ℓ.side d n)) :
    StepsAvoidOrigin T s' m d n (castD (congrArg (· + d) h) n u) o ↔ StepsAvoidOrigin T s m d n u o := by
  subst h
  rfl
private theorem siteAbove_oAt (a : ℕ) : ∀ (e n : ℕ) (o : TorusSite (fineSide ℓ.side (a + e) n)),
    siteAbove ℓ.side e n (oAt a e n o) = siteAbove ℓ.side (a + e) n o := by
  intro e
  induction e with
  | zero =>
    intro n o
    rfl
  | succ e ih =>
    intro n o
    show parentBlock ℓ.side (siteAbove ℓ.side e (n * ℓ.side) (oAt a e (n * ℓ.side) o)) =
      parentBlock ℓ.side (siteAbove ℓ.side (a + e) (n * ℓ.side) o)
    rw [ih (n * ℓ.side) o]
private theorem stepsMiss_levels (T : StageTower ℓ) (k a : ℕ) (m : ℝ) : ∀ (e n : ℕ) [NeZero n]
    (w : MarkedSample ℓ (k + (a + e)) n) (hs : k + (a + e) = k + a + e) (o : TorusSite (fineSide ℓ.side (a + e) n)),
    StepsAvoidOrigin T (k + a) m e n (castD hs n w) (oAt a e n o) ↔
      ∀ j, a ≤ j → j < a + e → missAt T k m j (a + e) n w o := by
  intro e
  induction e with
  | zero =>
    intro n _ w hs o
    simp only [StepsAvoidOrigin, true_iff]
    intro j h1 h2
    omega
  | succ e ih =>
    intro n _ w hs o
    have hs' : k + (a + e) = k + a + e := Nat.succ.inj hs
    have hi := ih (n * ℓ.side) w.1 hs' o
    have hfst : (castD hs n w).1 = castD hs' (n * ℓ.side) w.1 := castD_fst hs' n w
    have hfc := freeCores_castD T hs' n w (supBall (siteAbove ℓ.side (e + 1) n (oAt a (e + 1) n o)) m)
    have ho : siteAbove ℓ.side (e + 1) n (oAt a (e + 1) n o) = siteAbove ℓ.side (a + e + 1) n o :=
      siteAbove_oAt a (e + 1) n o
    rw [ho] at hfc
    have e1 : StepsAvoidOrigin T (k + a) m (e + 1) n (castD hs n w) (oAt a (e + 1) n o) ↔
        StepsAvoidOrigin T (k + a) m e (n * ℓ.side) (castD hs n w).1 (oAt a e (n * ℓ.side) o) ∧
          FreeCoresAvoid (T.stage (k + a + e)).toStepSetup
            (stageState T (k + a + e) (n * ℓ.side) (castD hs n w).1).2.1
            (castD hs n w).2.2.2 (hotCoreSites (T.stage (k + a + e)).toStepSetup (castD hs n w).2.2.1)
            (supBall (siteAbove ℓ.side (e + 1) n (oAt a (e + 1) n o)) m) := Iff.rfl
    rw [ho] at e1
    have hA : StepsAvoidOrigin T (k + a) m e (n * ℓ.side) (castD hs n w).1 (oAt a e (n * ℓ.side) o) ↔
        ∀ j, a ≤ j → j < a + e → missAt T k m j (a + e) (n * ℓ.side) w.1 o := by
      rw [hfst]
      exact hi
    refine e1.trans ((and_congr hA hfc).trans ?_)
    · constructor
      · rintro ⟨h2, h3⟩ j h4 h5
        show missAt T k m j (a + e + 1) n w o
        rw [missAt]
        split_ifs with h6
        · subst h6; exact h3
        · exact h2 j h4 (by omega)
      · intro hω
        refine ⟨fun j h2 h3 => ?_, ?_⟩
        · have h' : missAt T k m j (a + e + 1) n w o := hω j h2 (by omega)
          rwa [missAt, if_neg (by omega)] at h'
        · have h' : missAt T k m (a + e) (a + e + 1) n w o := hω (a + e) (by omega) (by omega)
          rwa [missAt, if_pos rfl] at h'
end Casting
section TheChain
variable {ℓ : StepParameters}
private def vOf (k N M : ℕ) (u : MarkedSample ℓ (k + M + M) N) : MarkedSample ℓ (k + M) (fineSide ℓ.side M N) :=
  sampleBelow ℓ (k + M) M N u
private def gOf (k N M : ℕ) [NeZero N] (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N)))
    (u : MarkedSample ℓ (k + M + M) N) : TorusSite (fineSide ℓ.side M N) → UnitQuaternion :=
  axialGaugeAt ℓ (topField ℓ (k + M) (fineSide ℓ.side M N) (vOf k N M u)) (siteAbove ℓ.side M (fineSide ℓ.side M N) o)
private def zetaOf (T : StageTower ℓ) (k N M : ℕ) [NeZero N] (nn ρ₀ ρA : ℝ)
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N)))
    (p : TorusPlaquette (fineSide ℓ.side M (fineSide ℓ.side M N))) (c : Fin 3)
    (j : ℕ) (u : MarkedSample ℓ (k + M + M) N) : ℝ :=
  imaginaryComponent c (levelTerm T k nn ρ₀ ρA j M (fineSide ℓ.side M N) (vOf k N M u) o (gOf k N M o u) p)
private def topOf (k N M : ℕ) [NeZero N] (nn ρ₀ ρA s₀ : ℝ)
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N)))
    (p : TorusPlaquette (fineSide ℓ.side M (fineSide ℓ.side M N))) (c : Fin 3)
    (u : MarkedSample ℓ (k + M + M) N) : ℝ :=
  imaginaryComponent c (∑ b : TorusBond (fineSide ℓ.side M N),
    adjointTransport ℓ.coupling ρA ℓ.side k M (fineSide ℓ.side M N) (curlFunctional p) b •
    topLogForm ℓ (topField ℓ (k + M) (fineSide ℓ.side M N) (vOf k N M u)) (siteAbove ℓ.side M (fineSide ℓ.side M N) o)
      (ballRadius ℓ.side nn ρ₀ M) s₀ b)
private def TopOK (T : StageTower ℓ) (k N M : ℕ) [NeZero N] (m : ℝ)
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) (u : MarkedSample ℓ (k + M + M) N) : Prop :=
  Disjoint (stageState T (k + M + M) N u).2.1
      (supBall (siteAbove ℓ.side M N (siteAbove ℓ.side M (fineSide ℓ.side M N) o)) m) ∧
    StepsAvoidOrigin T (k + M) m M N u (siteAbove ℓ.side M (fineSide ℓ.side M N) o)
private def chi (T : StageTower ℓ) (k N M : ℕ) [NeZero N] (m : ℝ)
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) (a : ℕ) : Set (MarkedSample ℓ (k + M + M) N) :=
  {u | TopOK T k N M m o u ∧ ∀ j, a ≤ j → j < M → missAt T k m j M (fineSide ℓ.side M N) (vOf k N M u) o}
private def coldSet (k N M : ℕ) [NeZero N] (m : ℝ) (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) (a : ℕ) :
    Set (MarkedSample ℓ (k + M + M) N) :=
  {u | ∀ j, a ≤ j → j < M → coldAt k m j M (fineSide ℓ.side M N) (vOf k N M u) o}
private def Good (T : StageTower ℓ) (k N M : ℕ) [NeZero N] (m : ℝ) (u : MarkedSample ℓ (k + M + M) N) : Prop :=
  AllDown T m (k + M) M N u ∧ AllDown T m k M (fineSide ℓ.side M N) (vOf k N M u)
private theorem chi_zero (T : StageTower ℓ) (k N M : ℕ) [NeZero N] (m : ℝ)
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) :
    chi T k N M m o 0 = {u | IsLocalEvent T k M m N u o} := by
  ext u
  simp only [chi, TopOK, IsLocalEvent, Set.mem_setOf_eq, and_assoc, Nat.zero_le, forall_true_left, vOf]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact (stepsMiss_iff T k m M (fineSide ℓ.side M N) _ o).symm
private theorem chi_mono (T : StageTower ℓ) (k N M : ℕ) [NeZero N] (m : ℝ)
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) {a b : ℕ} (h : a ≤ b) :
    chi T k N M m o a ⊆ chi T k N M m o b :=
  fun _ hu => ⟨hu.1, fun j h1 h2 => hu.2 j (h.trans h1) h2⟩
private theorem chi_off (T : StageTower ℓ) (k N a e : ℕ) [NeZero N] (m : ℝ)
    (o : TorusSite (fineSide ℓ.side (a + e) (fineSide ℓ.side (a + e) N)))
    (u : MarkedSample ℓ (k + (a + e) + (a + e)) N)
    (hu : u ∈ chi T k N (a + e) m o a) (hG : Good T k N (a + e) m u) :
    Disjoint (stageState T (k + a) (fineSide ℓ.side e (fineSide ℓ.side (a + e) N))
      (wAt k a e (fineSide ℓ.side (a + e) N) (vOf k N (a + e) u))).2.1 (supBall (oAt a e _ o) m) := by
  have h1 := yOffTop T m (k + (a + e)) (a + e) N u (siteAbove ℓ.side (a + e) (fineSide ℓ.side (a + e) N) o)
    hG.1 hu.1.1 hu.1.2
  exact yOff T m k a e (fineSide ℓ.side (a + e) N) (vOf k N (a + e) u) o hG.2 h1 hu.2
private theorem chi_cold (T : StageTower ℓ) (k N j e : ℕ) [NeZero N] (m : ℝ)
    (o : TorusSite (fineSide ℓ.side (j + 1 + e) (fineSide ℓ.side (j + 1 + e) N)))
    (u : MarkedSample ℓ (k + (j + 1 + e) + (j + 1 + e)) N)
    (hu : u ∈ chi T k N (j + 1 + e) m o (j + 1)) (hG : Good T k N (j + 1 + e) m u) :
    coldAt k m j (j + 1 + e) (fineSide ℓ.side (j + 1 + e) N) (vOf k N (j + 1 + e) u) o :=
  (coldAt_eq k m j e _ _ o).2
    ((allDown_at T m k j e _ _ hG.2 _ (chi_off T k N (j + 1) e m o u hu hG)).1)
private theorem chi_subset_cold (T : StageTower ℓ) (k N M : ℕ) [NeZero N] (m : ℝ)
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) (a : ℕ) (u : MarkedSample ℓ (k + M + M) N)
    (hu : u ∈ chi T k N M m o a) (hG : Good T k N M m u) : u ∈ coldSet k N M m o a := by
  intro j h1 h2
  obtain ⟨e, rfl⟩ : ∃ e, M = j + 1 + e := ⟨M - (j + 1), by omega⟩
  exact chi_cold T k N j e m o u (chi_mono T k N _ m o (by omega) hu) hG
private theorem chi_eta (T : StageTower ℓ) (k N j e : ℕ) [NeZero N] (m : ℝ)
    (o : TorusSite (fineSide ℓ.side (j + 1 + e) (fineSide ℓ.side (j + 1 + e) N)))
    (u : MarkedSample ℓ (k + (j + 1 + e) + (j + 1 + e)) N)
    (hu : u ∈ chi T k N (j + 1 + e) m o j) (hG : Good T k N (j + 1 + e) m u) :
    ∀ b ∈ chartBondsInBlocks ℓ.side (supBall (oAt (j + 1) e _ o) m),
      ‖(stepDeviation T (k + j) (wAt k (j + 1) e _ (vOf k N (j + 1 + e) u)).2.2.1
        (topField ℓ (k + j) _ (wAt k (j + 1) e _ (vOf k N (j + 1 + e) u)).1) b : Quaternion ℝ)‖ <
        ℓ.threshold / 64 := by
  intro b hb
  have hoff := chi_off T k N (j + 1) e m o u (chi_mono T k N _ m o (Nat.le_succ j) hu) hG
  have hm := (missAt_eq T k m j e _ _ o).1 (hu.2 j le_rfl (by omega))
  exact (((allDown_at T m k j e _ _ hG.2 _ hoff).2 hm).2 b hb).2
end TheChain
section Sizes
variable {ℓ : StepParameters}
open scoped Quaternion
private theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
private theorem norm_adjoint (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ‖(ColdStepAtMirrorFrames.adjointAction g X : ℍ[ℝ])‖ = ‖(X : ℍ[ℝ])‖ := by apply _root_.YangMills.SharedProofs.p17728 <;> assumption
private theorem norm_deviationInGauge (T : StageTower ℓ) (t : ℕ) {n : ℕ} [NeZero n] (g : TorusSite n → UnitQuaternion)
    (Z : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * ℓ.side)) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ b ∈ chartBondsInBlocks ℓ.side Z, ‖(stepDeviation T t V W b : ℍ[ℝ])‖ ≤ B) (b : TorusBond (n * ℓ.side)) :
    ‖(deviationInGauge T t g Z V W b : ℍ[ℝ])‖ ≤ B := by
  unfold deviationInGauge
  split_ifs with hb
  · rw [norm_adjoint]
    exact h b (Finset.mem_filter.2 ⟨hb.2, hb.1⟩)
  · simpa using hB
private theorem term_le (T : StageTower ℓ) (t : ℕ) {n : ℕ} [NeZero n] (g : TorusSite n → UnitQuaternion)
    (Z : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * ℓ.side)) (l : TorusBond (n * ℓ.side) → ℝ)
    (c : Fin 3) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ b ∈ chartBondsInBlocks ℓ.side Z, ‖(stepDeviation T t V W b : ℍ[ℝ])‖ ≤ B) :
    |imaginaryComponent c (∑ b, l b • deviationInGauge T t g Z V W b)| ≤ (∑ b, |l b|) * B := by
  rw [imaginaryComponent_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [imaginaryComponent_smul, abs_mul]
  exact mul_le_mul_of_nonneg_left
    ((abs_imaginaryComponent_le c _).trans (norm_deviationInGauge T t g Z V W B hB h b)) (abs_nonneg _)
private theorem lAt_expansion (k : ℕ) (ρA : ℝ) (j : ℕ) (n₀ : ℕ) (R : ℝ)
    (hRow : ∀ (n : ℕ) [NeZero n], n₀ ≤ n →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide ℓ.side j n))),
      ∑ b, |adjointTransport ℓ.coupling ρA ℓ.side k j n (curlFunctional p) b| ≤ R) :
    ∀ (e n : ℕ) [NeZero n], n₀ ≤ n →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide ℓ.side (j + 1 + e) n))),
      ∑ b, |lAt k ρA j e n p b| ≤ R := by
  intro e
  induction e with
  | zero =>
    intro n _ hn p hp
    have hpos : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
    exact hRow (n * ℓ.side) (hn.trans (Nat.le_mul_of_pos_right n hpos)) p hp
  | succ e ih =>
    intro n _ hn p hp
    have hpos : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
    exact ih (n * ℓ.side) (hn.trans (Nat.le_mul_of_pos_right n hpos)) p hp
private theorem lAt_far (k : ℕ) (nn ρ₀ ρA : ℝ) (j : ℕ) (n₀ : ℕ) (E : ℝ)
    (hFar : ∀ (n : ℕ) [NeZero n], n₀ ≤ n → ∀ (o : TorusSite (fineSide ℓ.side (j + 1) n)),
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide ℓ.side (j + 1) n))), p.1 ∈ supBall o (19 * nn) →
      ∑ b ∈ (Finset.univ : Finset (TorusBond (n * ℓ.side))).filter (fun b => parentBlock ℓ.side b.1 ∉ supBall
          (siteAbove ℓ.side (j + 1) n o) (ballRadius ℓ.side nn ρ₀ (j + 1) - 3 * ρ₀)),
        |adjointTransport ℓ.coupling ρA ℓ.side k j (n * ℓ.side) (curlFunctional p) b| ≤ E) :
    ∀ (e n : ℕ) [NeZero n], n₀ ≤ n → ∀ (o : TorusSite (fineSide ℓ.side (j + 1 + e) n)),
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide ℓ.side (j + 1 + e) n))),
      p.1 ∈ supBall o (19 * nn) →
      ∑ b, |lAt k ρA j e n p b - cutOf (supBall (oAt (j + 1) e n o) (ballRadius ℓ.side nn ρ₀ (j + 1) - 3 * ρ₀))
        (lAt k ρA j e n p) b| ≤ E := by
  intro e
  induction e with
  | zero =>
    intro n _ hn o p hp hb
    change ∑ b : TorusBond (n * ℓ.side), |adjointTransport ℓ.coupling ρA ℓ.side k j (n * ℓ.side) (curlFunctional p) b -
      cutOf (supBall (siteAbove ℓ.side (j + 1) n o) (ballRadius ℓ.side nn ρ₀ (j + 1) - 3 * ρ₀))
        (adjointTransport ℓ.coupling ρA ℓ.side k j (n * ℓ.side) (curlFunctional p)) b| ≤ E
    refine le_trans (le_of_eq ?_) (hFar n hn o p hp hb)
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold cutOf
    by_cases h : parentBlock ℓ.side b.1 ∈
        supBall (siteAbove ℓ.side (j + 1) n o) (ballRadius ℓ.side nn ρ₀ (j + 1) - 3 * ρ₀)
    · simp [h]
    · simp [h]
  | succ e ih =>
    intro n _ hn o p hp hb
    have hpos : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
    exact ih (n * ℓ.side) (hn.trans (Nat.le_mul_of_pos_right n hpos)) o p hp hb
private theorem cut_sum_abs_le {n : ℕ} [NeZero n] (Z : Finset (TorusSite n)) (h : TorusBond (n * ℓ.side) → ℝ) :
    ∑ b, |cutOf Z h b| ≤ ∑ b, |h b| := by
  refine Finset.sum_le_sum fun b _ => ?_
  unfold cutOf
  split_ifs
  · exact le_rfl
  · simpa using abs_nonneg (h b)
private theorem stepCovariance_sub_left (a : ℝ) (L u n : ℕ) [NeZero L] [NeZero n] (h₁ h₂ h' : TorusBond (n * L) → ℝ) :
    stepCovariance a L u n (fun b => h₁ b - h₂ b) h' = stepCovariance a L u n h₁ h' - stepCovariance a L u n h₂ h' := by
  unfold stepCovariance
  simp only
  rw [← sub_dotProduct]
  congr 1
  funext b
  simp only [Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp
private theorem stepCovariance_sub_right (a : ℝ) (L u n : ℕ) [NeZero L] [NeZero n] (h h₁ h₂ : TorusBond (n * L) → ℝ) :
    stepCovariance a L u n h (fun b => h₁ b - h₂ b) = stepCovariance a L u n h h₁ - stepCovariance a L u n h h₂ := by
  unfold stepCovariance
  simp only
  rw [← dotProduct_sub, ← Matrix.mulVec_sub]
  congr 2
  funext b
  simp only [Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp
private theorem cov_near (a : ℝ) (L u n : ℕ) [NeZero L] [NeZero n] (C : ℝ) (hC : 0 ≤ C) (R E : ℝ) (hR : 0 ≤ R)
    (hb : ∀ h h' : TorusBond (n * L) → ℝ, |stepCovariance a L u n h h'| ≤ C * (∑ b, |h b|) * ∑ b, |h' b|)
    (l₁ l₂ c₁ c₂ : TorusBond (n * L) → ℝ) (h₁ : ∑ b, |l₁ b| ≤ R) (h₂ : ∑ b, |c₂ b| ≤ R)
    (f₁ : ∑ b, |l₁ b - c₁ b| ≤ E) (f₂ : ∑ b, |l₂ b - c₂ b| ≤ E) :
    |stepCovariance a L u n c₁ c₂ - stepCovariance a L u n l₁ l₂| ≤ 2 * C * R * E := by
  have hE : 0 ≤ E := (Finset.sum_nonneg fun b _ => abs_nonneg _).trans f₁
  have e : stepCovariance a L u n c₁ c₂ - stepCovariance a L u n l₁ l₂ =
      -(stepCovariance a L u n (fun b => l₁ b - c₁ b) c₂ + stepCovariance a L u n l₁ (fun b => l₂ b - c₂ b)) := by
    rw [stepCovariance_sub_left, stepCovariance_sub_right]
    ring
  rw [e, abs_neg]
  have t1 : |stepCovariance a L u n (fun b => l₁ b - c₁ b) c₂| ≤ C * R * E := by
    refine (hb _ _).trans ?_
    calc C * (∑ b, |l₁ b - c₁ b|) * ∑ b, |c₂ b| ≤ C * E * R :=
          mul_le_mul (mul_le_mul_of_nonneg_left f₁ hC) h₂ (Finset.sum_nonneg fun b _ => abs_nonneg _) (by positivity)
      _ = _ := by ring
  have t2 : |stepCovariance a L u n l₁ (fun b => l₂ b - c₂ b)| ≤ C * R * E := by
    refine (hb _ _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left h₁ hC) f₂ (Finset.sum_nonneg fun b _ => abs_nonneg _) (by positivity)
  have := abs_add_le (stepCovariance a L u n (fun b => l₁ b - c₁ b) c₂)
    (stepCovariance a L u n l₁ (fun b => l₂ b - c₂ b))
  linarith
end Sizes
section Near
variable {ℓ : StepParameters} {Ω₀ : Type} [MeasurableSpace Ω₀]
open scoped Quaternion
private theorem le_finsetSupNonneg {α : Type} (S : Finset α) (f : α → ℝ) {i : α} (hi : i ∈ S) :
    f i ≤ finsetSupNonneg S f :=
  Finset.le_fold_max _ |>.2 (Or.inr ⟨i, hi, le_rfl⟩)
private theorem finsetSupNonneg_nonneg {α : Type} (S : Finset α) (f : α → ℝ) : 0 ≤ finsetSupNonneg S f :=
  Finset.le_fold_max _ |>.2 (Or.inl le_rfl)
private theorem finsetSupNonneg_le {α : Type} (S : Finset α) (f : α → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i ∈ S, f i ≤ c) : finsetSupNonneg S f ≤ c :=
  Finset.fold_max_le _ |>.2 ⟨hc, h⟩
private theorem measurable_finsetSupNonneg {α : Type} (S : Finset α) {F : α → Ω₀ → ℝ}
    (hF : ∀ i ∈ S, Measurable (F i)) : Measurable fun ω => finsetSupNonneg S fun i => F i ω := by
  classical
  unfold finsetSupNonneg
  induction S using Finset.induction_on with
  | empty => simpa using measurable_const
  | insert a S ha ih =>
    simp only [Finset.fold_insert ha]
    exact (hF a (Finset.mem_insert_self _ _)).max (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))
private def nearBall {n : ℕ} [NeZero n] (g : TorusSite n → UnitQuaternion) (V : TorusField n) (o : TorusSite n)
    (r : ℝ) : ℝ :=
  max (finsetSupNonneg (Finset.univ.filter fun b : TorusBond n => b.1 ∈ supBall o r)
    fun b => ‖(minimalLog (gaugeTransform g V b) : ℍ[ℝ])‖) (maxCurvatureOnBall V o r)
private theorem isNearIdentity_nearBall {n : ℕ} [NeZero n] (g : TorusSite n → UnitQuaternion) (V : TorusField n)
    (o : TorusSite n) (r : ℝ) : IsNearIdentity g V o r (nearBall g V o r) where
  log_le b hb := (le_finsetSupNonneg _ (fun b => ‖(minimalLog (gaugeTransform g V b) : ℍ[ℝ])‖)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)).trans (le_max_left _ _)
  curvature_le p hp :=
    (le_finsetSupNonneg _ (fun p : TorusPlaquette n => curvature V p.1 p.2.1 p.2.2) hp).trans (le_max_right _ _)
private theorem nearBall_nonneg {n : ℕ} [NeZero n] (g : TorusSite n → UnitQuaternion) (V : TorusField n)
    (o : TorusSite n) (r : ℝ) : 0 ≤ nearBall g V o r := (finsetSupNonneg_nonneg _ _).trans (le_max_left _ _)
private theorem curvature_le_two {n : ℕ} (V : TorusField n) (x : TorusSite n) (μ ν : Fin 4) :
    curvature V x μ ν ≤ 2 := by
  unfold curvature
  have h := norm_sub_le ((holonomy V x μ ν : UnitQuaternion) : ℍ[ℝ]) 1
  rw [norm_unitQuaternion, norm_one] at h
  linarith
abbrev _root_.YangMills.SharedProofs.p28884 := @curvature_le_two
private theorem nearBall_le {n : ℕ} [NeZero n] (g : TorusSite n → UnitQuaternion) (V : TorusField n)
    (o : TorusSite n) (r : ℝ) : nearBall g V o r ≤ 4 := by
  refine max_le (finsetSupNonneg_le _ _ (by norm_num) fun b _ => ?_)
    (finsetSupNonneg_le _ _ (by norm_num) fun p _ => ?_)
  · exact (GaugeFixing.norm_minimalLog_le_pi _).trans Real.pi_le_four
  · exact (curvature_le_two _ _ _ _).trans (by norm_num)
private theorem measurable_nearBall
    (hlog : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])))
    {n : ℕ} [NeZero n] {g : Ω₀ → TorusSite n → UnitQuaternion} (hg : Measurable g) {V : Ω₀ → TorusField n}
    (hV : Measurable V) (o : TorusSite n) (r : ℝ) : Measurable fun ω => nearBall (g ω) (V ω) o r := by
  refine Measurable.max (measurable_finsetSupNonneg _ fun b _ => ?_)
    (measurable_finsetSupNonneg _ fun p _ => measurable_curvature hV _ _ _)
  have hG := measurable_gaugeTransform hg hV b
  obtain ⟨h0, h1, h2, h3⟩ := hlog
  have e : (fun ω => ‖(minimalLog (gaugeTransform (g ω) (V ω) b) : ℍ[ℝ])‖) =
      fun ω => Real.sqrt ((minimalLog (gaugeTransform (g ω) (V ω) b) : ℍ[ℝ]).re ^ 2 +
        (minimalLog (gaugeTransform (g ω) (V ω) b) : ℍ[ℝ]).imI ^ 2 +
        (minimalLog (gaugeTransform (g ω) (V ω) b) : ℍ[ℝ]).imJ ^ 2 +
        (minimalLog (gaugeTransform (g ω) (V ω) b) : ℍ[ℝ]).imK ^ 2) := by
    funext ω
    rw [← Quaternion.normSq_def', Quaternion.normSq_eq_norm_mul_self, Real.sqrt_mul_self (norm_nonneg _)]
  rw [e]
  exact ((((h0.comp hG).pow_const 2).add ((h1.comp hG).pow_const 2)).add ((h2.comp hG).pow_const 2)).add
    ((h3.comp hG).pow_const 2) |>.sqrt
end Near
section AtALevel
variable {ℓ : StepParameters} {Ω₀ : Type} [MeasurableSpace Ω₀]
private theorem gAt_read (T : StageTower ℓ) (k a : ℕ)
    (hS : ∀ (t d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (stageState T (t + d) n)) :
    ∀ (e n : ℕ) [NeZero n] (π : Ω₀ → MarkedSample ℓ (k + (a + e)) n) (hs : k + (a + e) = k + a + e)
      (g : Ω₀ → TorusSite n → UnitQuaternion), Up T (k + a) e n hs π → Measurable g →
      Measurable fun ω => gAt k a e n (π ω) (g ω) := by
  intro e
  induction e with
  | zero =>
    intro n _ π hs g _ hg
    exact hg
  | succ e ih =>
    intro n _ π hs g h hg
    have h1 := Up.fst (hs := hs) h
    exact ih (n * ℓ.side) (fun ω => (π ω).1) (Nat.succ.inj hs) _ h1 (measurable_liftGauge hg (h1.top (hS _ _ _)))
private theorem wAt_top_read (T : StageTower ℓ) (k a : ℕ)
    (hS : ∀ (t d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (stageState T (t + d) n)) :
    ∀ (e n : ℕ) [NeZero n] (π : Ω₀ → MarkedSample ℓ (k + (a + e)) n) (hs : k + (a + e) = k + a + e),
      Up T (k + a) e n hs π →
      Measurable fun ω => topField ℓ (k + a) (fineSide ℓ.side e n) (wAt k a e n (π ω)) := by
  intro e
  induction e with
  | zero =>
    intro n _ π hs h
    exact h.top (hS _ _ _)
  | succ e ih =>
    intro n _ π hs h
    exact ih (n * ℓ.side) (fun ω => (π ω).1) (Nat.succ.inj hs) (Up.fst (hs := hs) h)
private def nearDef (k N a e : ℕ) [NeZero N] (nn ρ₀ : ℝ) : (M : ℕ) → a + e = M →
    TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N)) → MarkedSample ℓ (k + M + M) N → ℝ
  | _, rfl, o, u => nearBall (gAt k a e (fineSide ℓ.side (a + e) N) (vOf k N (a + e) u) (gOf k N (a + e) o u))
      (topField ℓ (k + a) _ (wAt k a e (fineSide ℓ.side (a + e) N) (vOf k N (a + e) u))) (oAt a e _ o)
      (ballRadius ℓ.side nn ρ₀ a)
private def sFam (k N M : ℕ) [NeZero N] (nn ρ₀ : ℝ) (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N)))
    (a : ℕ) (u : MarkedSample ℓ (k + M + M) N) : ℝ :=
  if h : a ≤ M then nearDef k N a (M - a) nn ρ₀ M (by omega) o u else 0
private theorem nearDef_congr (k N a : ℕ) [NeZero N] (nn ρ₀ : ℝ) {e e' M : ℕ} (he : e = e') (h : a + e = M)
    (h' : a + e' = M) (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) (u : MarkedSample ℓ (k + M + M) N) :
    nearDef k N a e nn ρ₀ M h o u = nearDef k N a e' nn ρ₀ M h' o u := by
  subst he
  rfl
private theorem sFam_eq (k N a e : ℕ) [NeZero N] (nn ρ₀ : ℝ)
    (o : TorusSite (fineSide ℓ.side (a + e) (fineSide ℓ.side (a + e) N)))
    (u : MarkedSample ℓ (k + (a + e) + (a + e)) N) :
    sFam k N (a + e) nn ρ₀ o a u = nearDef k N a e nn ρ₀ (a + e) rfl o u := by
  unfold sFam
  rw [dif_pos (by omega)]
  exact nearDef_congr k N a nn ρ₀ (by omega) _ _ o u
private theorem nearDef_bounds (k N a e : ℕ) [NeZero N] (nn ρ₀ : ℝ) : ∀ (M : ℕ) (h : a + e = M)
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) (u : MarkedSample ℓ (k + M + M) N),
    0 ≤ nearDef k N a e nn ρ₀ M h o u ∧ nearDef k N a e nn ρ₀ M h o u ≤ 4 := by
  rintro _ rfl o u
  exact ⟨nearBall_nonneg _ _ _ _, nearBall_le _ _ _ _⟩
private theorem sFam_nonneg (k N M : ℕ) [NeZero N] (nn ρ₀ : ℝ)
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) (a : ℕ)
    (u : MarkedSample ℓ (k + M + M) N) : 0 ≤ sFam k N M nn ρ₀ o a u := by
  unfold sFam
  split_ifs with h
  · exact (nearDef_bounds k N a (M - a) nn ρ₀ M _ o u).1
  · exact le_rfl
private theorem sFam_le (k N M : ℕ) [NeZero N] (nn ρ₀ : ℝ) (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N)))
    (a : ℕ) (u : MarkedSample ℓ (k + M + M) N) : sFam k N M nn ρ₀ o a u ≤ 4 := by
  unfold sFam
  split_ifs with h
  · exact (nearDef_bounds k N a (M - a) nn ρ₀ M _ o u).2
  · norm_num
end AtALevel
section Numbers
private theorem couplingLargeEnough (P B A c n₀ : ℝ) (hc : 0 < c) (hA : 0 < A) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    1 ≤ x ∧ (1 / 2 : ℝ) ^ chainDepth x ≤ x ^ (-P) ∧
    A * Real.exp (-(c * logCubeScale x)) * ((chainDepth x : ℝ) + 1) * 4 ^ chainDepth x ≤ x ^ (-P) ∧
    2 * B * (chainDepth x : ℝ) ≤ 3 / 4 * x ∧ logCubeScale x ≤ x ∧
    20 * x ^ ((1 : ℝ) / 90) + logCubeScale x ≤ localBoxRadius x / 8 ∧ n₀ ≤ localBoxRadius x := by
  have h3 : ∀ᶠ t : ℝ in Filter.atTop, t ^ 3 ≤ (1 / 64) * Real.exp (1 / 20 * t) := by
    have := (isLittleO_pow_exp_pos_mul_atTop 3 (show (0 : ℝ) < 1 / 20 by norm_num)).bound
      (show (0 : ℝ) < 1 / 64 by norm_num)
    filter_upwards [this, Filter.eventually_ge_atTop 0] with t ht h0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos (Real.exp_pos _)] at ht
    exact ht
  have h1 : ∀ᶠ t : ℝ in Filter.atTop, (1 : ℝ) ≤ (1 / 64) * Real.exp (1 / 20 * t) := by
    have := (Real.tendsto_exp_atTop.comp
      (Filter.tendsto_id.const_mul_atTop (show (0 : ℝ) < 1 / 20 by norm_num))).eventually_ge_atTop 64
    filter_upwards [this] with t ht
    simp only [Function.comp, id] at ht
    linarith
  have h90 : ∀ᶠ t : ℝ in Filter.atTop, Real.exp (1 / 90 * t) ≤ (1 / 1280) * Real.exp (1 / 20 * t) := by
    filter_upwards [Filter.eventually_ge_atTop (180 / 7 * Real.log 1280)] with t ht
    have e : Real.exp (1 / 20 * t) = Real.exp (1 / 90 * t) * Real.exp (7 / 180 * t) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : (1280 : ℝ) ≤ Real.exp (7 / 180 * t) := by
      rw [← Real.log_le_iff_le_exp (by norm_num)]
      linarith
    rw [e]
    have := Real.exp_pos (1 / 90 * t)
    nlinarith
  have hn : ∀ᶠ t : ℝ in Filter.atTop, n₀ + 1 ≤ Real.exp (1 / 20 * t) :=
    (Real.tendsto_exp_atTop.comp
      (Filter.tendsto_id.const_mul_atTop (show (0 : ℝ) < 1 / 20 by norm_num))).eventually_ge_atTop _
  have hB : ∀ᶠ t : ℝ in Filter.atTop, 2 * |B| * t ^ 2 ≤ 3 / 4 * Real.exp t := by
    have := (isLittleO_pow_exp_pos_mul_atTop 2 (show (0 : ℝ) < 1 by norm_num)).bound
      (show (0 : ℝ) < 3 / 4 / (2 * |B| + 1) by positivity)
    filter_upwards [this, Filter.eventually_ge_atTop 0] with t ht h0
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos (Real.exp_pos _)] at ht
    have hq : 0 < 2 * |B| + 1 := by positivity
    have h5 : (2 * |B| + 1) * t ^ 2 ≤ 3 / 4 * Real.exp t := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hq] at ht
      linarith
    have h6 : 2 * |B| * t ^ 2 ≤ (2 * |B| + 1) * t ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    linarith
  have hpoly : ∀ᶠ t : ℝ in Filter.atTop,
      Real.log A + c + 4 * t ^ 2 + P * t + t ≤ c * t ^ 3 ∧ P * t ≤ (t ^ 2 - 1) / 2 ∧ 1 ≤ t := by
    have ht : ∀ᶠ t : ℝ in Filter.atTop, (|Real.log A| + c + 5 + |P| + 1) / c + 2 * |P| + 2 ≤ t :=
      Filter.eventually_ge_atTop _
    filter_upwards [ht] with t h
    have hq : 0 ≤ (|Real.log A| + c + 5 + |P| + 1) / c := by positivity
    have ht1 : 1 ≤ t := by
      have := abs_nonneg P
      linarith
    have ht2 : (|Real.log A| + c + 5 + |P| + 1) ≤ c * t := by
      have h1' : (|Real.log A| + c + 5 + |P| + 1) / c ≤ t := by
        have := abs_nonneg P
        linarith
      rwa [div_le_iff₀ hc, mul_comm] at h1'
    have hP : P ≤ |P| := le_abs_self P
    have hlA : Real.log A ≤ |Real.log A| := le_abs_self _
    refine ⟨?_, ?_, ht1⟩
    · have h2 : 1 ≤ t ^ 2 := by nlinarith
      have h3' : t ≤ t ^ 2 := by nlinarith
      have h4 : (|Real.log A| + c + 5 + |P| + 1) * t ^ 2 ≤ c * t * t ^ 2 :=
        mul_le_mul_of_nonneg_right ht2 (by positivity)
      have h5 : c * t * t ^ 2 = c * t ^ 3 := by ring
      have a1 : 0 ≤ |Real.log A| := abs_nonneg _
      have a2 : 0 ≤ |P| := abs_nonneg _
      have h6 : P * t ≤ |P| * t ^ 2 := by nlinarith
      nlinarith
    · have a2 : 0 ≤ |P| := abs_nonneg _
      have h6 : 2 * |P| + 2 ≤ t := by
        have : 0 ≤ (|Real.log A| + c + 5 + |P| + 1) / c := hq
        linarith
      nlinarith
  have hall := ((((h3.and h1).and h90).and hn).and hB).and hpoly
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1 hall
  refine ⟨Real.exp t₀, fun x hx => ?_⟩
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have htx : t₀ ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  obtain ⟨⟨⟨⟨⟨a3, a1⟩, a90⟩, an⟩, aB⟩, p1, p2, p3⟩ := ht₀ _ htx
  set t := Real.log x with ht
  have hxe : Real.exp t = x := Real.exp_log hx0
  have hx1 : 1 ≤ x := by
    rw [← hxe]
    exact Real.one_le_exp (by linarith)
  have hD1 : (chainDepth x : ℝ) ≤ t ^ 2 := Nat.floor_le (by positivity)
  have hD2 : t ^ 2 - 1 < chainDepth x := by
    have := Nat.lt_floor_add_one (t ^ 2)
    unfold chainDepth
    linarith
  have hS1 : logCubeScale x ≤ t ^ 3 := Nat.floor_le (by positivity)
  have hS2 : t ^ 3 - 1 < logCubeScale x := by
    have := Nat.lt_floor_add_one (t ^ 3)
    unfold logCubeScale
    linarith
  have hpow : ∀ r : ℝ, x ^ r = Real.exp (r * t) := fun r => by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  have hm2 : x ^ ((1 : ℝ) / 20) - 1 < localBoxRadius x := by
    have := Nat.lt_floor_add_one (x ^ ((1 : ℝ) / 20))
    unfold localBoxRadius
    linarith
  have hm3 : Real.exp (1 / 20 * t) = x ^ ((1 : ℝ) / 20) := (hpow _).symm
  refine ⟨hx1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpow, one_div, inv_pow, ← Real.exp_log (show (0 : ℝ) < 2 ^ chainDepth x by positivity), ← Real.exp_neg,
      Real.log_pow]
    apply Real.exp_le_exp.2
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hD0 : (0 : ℝ) ≤ chainDepth x := by positivity
    have : (chainDepth x : ℝ) * (1 / 2) ≤ (chainDepth x : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hl2 hD0
    linarith
  · rw [hpow]
    have hM1 : (chainDepth x : ℝ) + 1 ≤ Real.exp (t ^ 2) := by
      have := Real.add_one_le_exp (t ^ 2)
      linarith
    have h4 : (4 : ℝ) ^ chainDepth x ≤ Real.exp (3 * t ^ 2) := by
      rw [← Real.exp_log (show (0 : ℝ) < 4 ^ chainDepth x by positivity), Real.log_pow]
      apply Real.exp_le_exp.2
      have hl4 : Real.log 4 ≤ 3 := by
        have e : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        have := Real.log_two_lt_d9
        linarith
      have hD0 : (0 : ℝ) ≤ chainDepth x := by positivity
      have := mul_le_mul hD1 hl4 (Real.log_nonneg (by norm_num)) (by positivity)
      linarith
    have hE : Real.exp (-(c * logCubeScale x)) ≤ Real.exp (-(c * (t ^ 3 - 1))) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hS2.le hc.le
      linarith
    calc A * Real.exp (-(c * logCubeScale x)) * ((chainDepth x : ℝ) + 1) * 4 ^ chainDepth x
        ≤ A * Real.exp (-(c * (t ^ 3 - 1))) * Real.exp (t ^ 2) * Real.exp (3 * t ^ 2) := by
          gcongr
      _ = Real.exp (Real.log A + -(c * (t ^ 3 - 1)) + t ^ 2 + 3 * t ^ 2) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hA]
      _ ≤ Real.exp (-P * t) := by
          apply Real.exp_le_exp.2
          nlinarith
  · have h0 : 2 * B * (chainDepth x : ℝ) ≤ 2 * |B| * t ^ 2 := by
      have : B ≤ |B| := le_abs_self B
      have a1 : 0 ≤ |B| := abs_nonneg B
      nlinarith
    rw [hxe] at aB
    linarith
  · have hEle : Real.exp (1 / 20 * t) ≤ Real.exp t := Real.exp_le_exp.2 (by linarith)
    rw [hxe] at hEle
    have h0 := Real.exp_pos (1 / 20 * t)
    linarith
  · have e90 : x ^ ((1 : ℝ) / 90) = Real.exp (1 / 90 * t) := hpow _
    rw [e90]
    rw [hm3] at a3 a1 a90 an
    linarith
  · rw [hm3] at an
    linarith
end Numbers
section Transport
variable {ℓ : StepParameters}
private theorem heq_fst {s s' n : ℕ} (h : s = s') (w : MarkedSample ℓ (s + 1) n) (w' : MarkedSample ℓ (s' + 1) n)
    (hw : HEq w w') : HEq w.1 w'.1 := by
  subst h
  rw [eq_of_heq hw]
private theorem wAt_heq (k a : ℕ) : ∀ (e n : ℕ) (w : MarkedSample ℓ (k + (a + e)) n)
    (w' : MarkedSample ℓ (k + a + e) n), HEq w w' → wAt k a e n w = sampleBelow ℓ (k + a) e n w' := by
  intro e
  induction e with
  | zero =>
    intro n w w' h
    exact eq_of_heq h
  | succ e ih =>
    intro n w w' h
    exact ih (n * ℓ.side) w.1 w'.1 (heq_fst (s := k + (a + e)) (s' := k + a + e) (by omega) w w' h)
private theorem below_heq (k a e : ℕ) : ∀ (M N : ℕ) (u : MarkedSample ℓ (k + (a + e) + M) N)
    (u' : MarkedSample ℓ (k + a + (e + M)) N), HEq u u' →
    HEq (wAt k a e (fineSide ℓ.side M N) (sampleBelow ℓ (k + (a + e)) M N u))
      (sampleBelow ℓ (k + a) (e + M) N u') := by
  intro M
  induction M with
  | zero =>
    intro N u u' h
    exact heq_of_eq (wAt_heq k a e N u u' h)
  | succ M ih =>
    intro N u u' h
    exact ih (N * ℓ.side) u.1 u'.1 (heq_fst (s := k + (a + e) + M) (s' := k + a + (e + M)) (by omega) u u' h)
private theorem fineSide_add (L e M N : ℕ) : fineSide L (e + M) N = fineSide L e (fineSide L M N) := by
  rw [fineSide_eq, fineSide_eq, fineSide_eq, pow_add]
  ring
end Transport
section Pull
variable {Ω : Type} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
private theorem integral_mul_near_condExp [IsProbabilityMeasure μ] {𝔽 : MeasurableSpace Ω} (h𝔽 : 𝔽 ≤ mΩ)
    {F Y E : Ω → ℝ} {w c : ℝ} {B : Set Ω}
    (hF : Integrable F μ) (hY : AEStronglyMeasurable[𝔽] Y μ) (hYb : ∀ᵐ ω ∂μ, |Y ω| ≤ c)
    (hY0 : ∀ᵐ ω ∂μ, ω ∉ B → Y ω = 0) (hE : ∀ᵐ ω ∂μ, ω ∈ B → |(μ[F | 𝔽]) ω - w| ≤ E ω)
    (hYE : Integrable (fun ω => |Y ω| * E ω) μ) :
    |∫ ω, F ω * Y ω ∂μ - w * ∫ ω, Y ω ∂μ| ≤ ∫ ω, |Y ω| * E ω ∂μ := by
  have hYm : @AEStronglyMeasurable _ _ _ mΩ mΩ Y μ := by
    obtain ⟨g, hg, hgY⟩ := hY
    exact ⟨g, hg.mono h𝔽, hgY⟩
  have hYb' : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ c := by simpa using hYb
  have hYi : Integrable Y μ := Integrable.of_bound hYm c hYb'
  have hYF : Integrable (Y * F) μ := hF.bdd_mul hYm hYb'
  have hce := condExp_mul_of_aestronglyMeasurable_left hY hYF hF
  have hint : ∫ ω, (μ[Y * F | 𝔽]) ω ∂μ = ∫ ω, (Y * F) ω ∂μ := integral_condExp h𝔽
  have hYc : Integrable (Y * (μ[F | 𝔽])) μ := (integrable_condExp (m := 𝔽)).bdd_mul hYm hYb'
  have e1 : ∫ ω, F ω * Y ω ∂μ = ∫ ω, (Y * (μ[F | 𝔽])) ω ∂μ := by
    rw [← integral_congr_ae hce, hint]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp [mul_comm])
  have e2 : ∫ ω, (Y * (μ[F | 𝔽])) ω ∂μ - w * ∫ ω, Y ω ∂μ = ∫ ω, Y ω * ((μ[F | 𝔽]) ω - w) ∂μ := by
    rw [← integral_const_mul, ← integral_sub hYc (hYi.const_mul w)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [Pi.mul_apply]; ring)
  rw [e1, e2]
  refine (abs_integral_le_integral_abs).trans (integral_mono_ae ?_ hYE ?_)
  · exact (hYc.sub (hYi.const_mul w)).abs.congr (Filter.Eventually.of_forall fun ω => by
      simp only [Pi.sub_apply, Pi.mul_apply]
      congr 1
      ring)
  · filter_upwards [hY0, hE] with ω h0 h1
    by_cases hω : ω ∈ B
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h1 hω) (abs_nonneg _)
    · simp [h0 hω]
end Pull
section Marginals
variable {ℓ : StepParameters} {T : StageTower ℓ} {β : ℝ}
private theorem below_ae (hfst : ∀ (s n : ℕ) [NeZero n],
      (markedSampleLaw T β (s + 1) n).map (fun u : MarkedSample ℓ (s + 1) n => u.1) =
        markedSampleLaw T β s (n * ℓ.side))
    (s : ℕ) : ∀ (d n : ℕ) [NeZero n] (P : MarkedSample ℓ s (fineSide ℓ.side d n) → Prop),
    (∀ᵐ w ∂(markedSampleLaw T β s (fineSide ℓ.side d n)), P w) →
    ∀ᵐ u ∂(markedSampleLaw T β (s + d) n), P (sampleBelow ℓ s d n u) := by
  intro d
  induction d with
  | zero =>
    intro n _ P h
    exact h
  | succ d ih =>
    intro n _ P h
    have h1 := ih (n * ℓ.side) P h
    rw [← hfst (s + d) n] at h1
    exact ae_of_ae_map measurable_fst.aemeasurable h1
private theorem allDown_ae (hfst : ∀ (s n : ℕ) [NeZero n],
      (markedSampleLaw T β (s + 1) n).map (fun u : MarkedSample ℓ (s + 1) n => u.1) =
        markedSampleLaw T β s (n * ℓ.side))
    (m : ℝ) (s N₀ : ℕ) (d₀ : ℕ) (hD : ∀ t, s ≤ t → t < s + d₀ → ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ℓ.side ∣ n →
      ∀ᵐ u ∂(markedSampleLaw T β (t + 1) n), Down T m t n u) :
    ∀ (d n : ℕ) [NeZero n], d ≤ d₀ → N₀ ≤ n → ℓ.side ∣ n →
      ∀ᵐ u ∂(markedSampleLaw T β (s + d) n), AllDown T m s d n u := by
  intro d
  induction d with
  | zero =>
    intro n _ _ _ _
    exact Filter.Eventually.of_forall fun _ => trivial
  | succ d ih =>
    intro n _ hd hn hL
    have hpos : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
    have h1 := ih (n * ℓ.side) (by omega) (hn.trans (Nat.le_mul_of_pos_right n hpos)) (Dvd.intro_left n rfl)
    rw [← hfst (s + d) n] at h1
    have h2 := ae_of_ae_map measurable_fst.aemeasurable h1
    filter_upwards [hD (s + d) (by omega) (by omega) n hn hL, h2] with u a b
    exact ⟨a, b⟩
end Marginals
section Reads
variable {ℓ : StepParameters} {Ω₀ : Type} [MeasurableSpace Ω₀]
open scoped Quaternion
private theorem vOf_up {T : StageTower ℓ} {k N a e : ℕ} [NeZero N]
    {π₀ : Ω₀ → MarkedSample ℓ (k + (a + e) + (a + e)) N} (hh : k + (a + e) + (a + e) = k + a + (e + (a + e)))
    (h : Up T (k + a) (e + (a + e)) N hh π₀) (hs : k + (a + e) = k + a + e) :
    Up T (k + a) e (fineSide ℓ.side (a + e) N) hs fun ω => vOf k N (a + e) (π₀ ω) :=
  Up.down e (a + e) N hs hh π₀ h
private theorem chi_read (T : StageTower ℓ)
    (hS : ∀ (t d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (stageState T (t + d) n))
    (hH : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
      MeasurableSet {V : TorusField n | hotCoreSites R V = a})
    {k N a e : ℕ} [NeZero N] (m : ℝ) (o : TorusSite (fineSide ℓ.side (a + e) (fineSide ℓ.side (a + e) N)))
    {π₀ : Ω₀ → MarkedSample ℓ (k + (a + e) + (a + e)) N} (hh : k + (a + e) + (a + e) = k + a + (e + (a + e)))
    (h : Up T (k + a) (e + (a + e)) N hh π₀) : MeasurableSet {ω | π₀ ω ∈ chi T k N (a + e) m o a} := by
  have hs : k + (a + e) = k + a + e := by omega
  have h1 : MeasurableSet {ω | Disjoint (stageState T (k + (a + e) + (a + e)) N (π₀ ω)).2.1
      (supBall (siteAbove ℓ.side (a + e) N (siteAbove ℓ.side (a + e) (fineSide ℓ.side (a + e) N) o)) m)} :=
    measurableSet_of_fibres (fun ω => (stageState T (k + (a + e) + (a + e)) N (π₀ ω)).2.1)
      (fun y => h.setFibres (hS _ _ _) y) (fun y => Disjoint y _)
  have h2 := stepsMiss_meas T hS hH m e (k + (a + e)) hs (a + e) N π₀ hh
    (siteAbove ℓ.side (a + e) (fineSide ℓ.side (a + e) N) o) h
  have h3 := missAt_meas T hS hH m k a e _ (fun ω => vOf k N (a + e) (π₀ ω)) hs o (vOf_up hh h hs)
  have e1 : {ω | π₀ ω ∈ chi T k N (a + e) m o a} =
      ({ω | Disjoint (stageState T (k + (a + e) + (a + e)) N (π₀ ω)).2.1
        (supBall (siteAbove ℓ.side (a + e) N (siteAbove ℓ.side (a + e) (fineSide ℓ.side (a + e) N) o)) m)} ∩
      {ω | StepsAvoidOrigin T (k + (a + e)) m (a + e) N (π₀ ω)
        (siteAbove ℓ.side (a + e) (fineSide ℓ.side (a + e) N) o)}) ∩
      {ω | ∀ j, a ≤ j → j < a + e → missAt T k m j (a + e) (fineSide ℓ.side (a + e) N) (vOf k N (a + e) (π₀ ω)) o} :=
    rfl
  rw [e1]
  exact (h1.inter h2).inter h3
private theorem cold_read (T : StageTower ℓ)
    (hS : ∀ (t d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (stageState T (t + d) n))
    {k N a e : ℕ} [NeZero N] (m : ℝ) (o : TorusSite (fineSide ℓ.side (a + e) (fineSide ℓ.side (a + e) N)))
    {π₀ : Ω₀ → MarkedSample ℓ (k + (a + e) + (a + e)) N} (hh : k + (a + e) + (a + e) = k + a + (e + (a + e)))
    (h : Up T (k + a) (e + (a + e)) N hh π₀) : MeasurableSet {ω | π₀ ω ∈ coldSet k N (a + e) m o a} := by
  have hs : k + (a + e) = k + a + e := by omega
  exact coldAt_meas T hS m k a e _ (fun ω => vOf k N (a + e) (π₀ ω)) hs o (vOf_up hh h hs)
private theorem gOf_read (T : StageTower ℓ)
    (hS : ∀ (t d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (stageState T (t + d) n))
    {k N a e : ℕ} [NeZero N] (o : TorusSite (fineSide ℓ.side (a + e) (fineSide ℓ.side (a + e) N)))
    {π₀ : Ω₀ → MarkedSample ℓ (k + (a + e) + (a + e)) N} (hh : k + (a + e) + (a + e) = k + a + (e + (a + e)))
    (h : Up T (k + a) (e + (a + e)) N hh π₀) : Measurable fun ω => gOf k N (a + e) o (π₀ ω) := by
  have hs : k + (a + e) = k + a + e := by omega
  have hV := (vOf_up hh h hs).top (hS _ _ _)
  exact measurable_pi_lambda _ fun z => measurable_axialGaugeAt hV _ z
private theorem zeta_read (T : StageTower ℓ) (nn ρ₀ ρA m : ℝ)
    (hS : ∀ (t d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (stageState T (t + d) n))
    {k N a e : ℕ} [NeZero N]
    (hB : ∀ (d n : ℕ) [NeZero n] (o' : TorusSite n) (b : TorusBond (n * ℓ.side)), N ≤ n → ℓ.side ∣ n → d < a + e →
      parentBlock ℓ.side b.1 ∈ supBall o' (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀) → b ∈ chartBonds ℓ.side n →
      MeasurableQuaternion fun p : TorusField n × TorusField (n * ℓ.side) =>
        if IsColdOnBall ℓ.threshold p.1 o' m then (stepDeviation T (k + d) p.1 p.2 b : ℍ[ℝ]) else 0)
    (hL : ℓ.side ∣ N) (o : TorusSite (fineSide ℓ.side (a + e) (fineSide ℓ.side (a + e) N)))
    (p : TorusPlaquette (fineSide ℓ.side (a + e) (fineSide ℓ.side (a + e) N))) (c : Fin 3)
    {π₀ : Ω₀ → MarkedSample ℓ (k + (a + e) + (a + e)) N} (hh : k + (a + e) + (a + e) = k + a + (e + (a + e)))
    (h : Up T (k + a) (e + (a + e)) N hh π₀) {C : Set Ω₀} (hC : MeasurableSet C)
    (hcold : ∀ ω ∈ C, π₀ ω ∈ coldSet k N (a + e) m o a) (j : ℕ) (hj : a ≤ j) :
    MO C fun ω => zetaOf T k N (a + e) nn ρ₀ ρA o p c j (π₀ ω) := by
  have hs : k + (a + e) = k + a + e := by omega
  have hpos : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
  have hN : N ≤ fineSide ℓ.side (a + e) N := by
    rw [fineSide_eq]
    exact Nat.le_mul_of_pos_right N (pow_pos hpos _)
  have hL' : ℓ.side ∣ fineSide ℓ.side (a + e) N := by
    rw [fineSide_eq]
    exact hL.mul_right _
  exact level_MO T k nn ρ₀ ρA m N (a + e) hS hB a e (fineSide ℓ.side (a + e) N) hN hL' le_rfl
    (fun ω => vOf k N (a + e) (π₀ ω)) hs (fun ω => gOf k N (a + e) o (π₀ ω)) o p c C hC (vOf_up hh h hs)
    (gOf_read T hS o hh h) (fun ω hω => hcold ω hω) j hj
private theorem top_read (T : StageTower ℓ) (nn ρ₀ ρA s₀ : ℝ)
    (hS : ∀ (t d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (stageState T (t + d) n))
    (hlog : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])))
    {k N a e : ℕ} [NeZero N] (o : TorusSite (fineSide ℓ.side (a + e) (fineSide ℓ.side (a + e) N)))
    (p : TorusPlaquette (fineSide ℓ.side (a + e) (fineSide ℓ.side (a + e) N))) (c : Fin 3)
    {π₀ : Ω₀ → MarkedSample ℓ (k + (a + e) + (a + e)) N} (hh : k + (a + e) + (a + e) = k + a + (e + (a + e)))
    (h : Up T (k + a) (e + (a + e)) N hh π₀) :
    Measurable fun ω => topOf k N (a + e) nn ρ₀ ρA s₀ o p c (π₀ ω) := by
  have hs : k + (a + e) = k + a + e := by omega
  have hV := (vOf_up hh h hs).top (hS _ _ _)
  have e1 : (fun ω => topOf k N (a + e) nn ρ₀ ρA s₀ o p c (π₀ ω)) = fun ω => ∑ b : TorusBond (fineSide ℓ.side (a + e) N),
      adjointTransport ℓ.coupling ρA ℓ.side k (a + e) (fineSide ℓ.side (a + e) N) (curlFunctional p) b *
        imaginaryComponent c (topLogForm ℓ
          (topField ℓ (k + (a + e)) (fineSide ℓ.side (a + e) N) (vOf k N (a + e) (π₀ ω)))
          (siteAbove ℓ.side (a + e) (fineSide ℓ.side (a + e) N) o) (ballRadius ℓ.side nn ρ₀ (a + e)) s₀ b) := by
    funext ω
    unfold topOf
    rw [imaginaryComponent_sum]
    exact Finset.sum_congr rfl fun b _ => imaginaryComponent_smul _ _ _
  rw [e1]
  exact Finset.measurable_fun_sum _ fun b _ => (measurable_topLogForm hlog hV _ _ _ c b).const_mul _
private theorem near_read (T : StageTower ℓ) (nn ρ₀ : ℝ)
    (hS : ∀ (t d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (stageState T (t + d) n))
    (hlog : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])))
    {k N a e : ℕ} [NeZero N] (o : TorusSite (fineSide ℓ.side (a + e) (fineSide ℓ.side (a + e) N)))
    {π₀ : Ω₀ → MarkedSample ℓ (k + (a + e) + (a + e)) N} (hh : k + (a + e) + (a + e) = k + a + (e + (a + e)))
    (h : Up T (k + a) (e + (a + e)) N hh π₀) :
    Measurable fun ω => nearDef k N a e nn ρ₀ (a + e) rfl o (π₀ ω) := by
  have hs : k + (a + e) = k + a + e := by omega
  have hv := vOf_up hh h hs
  exact measurable_nearBall hlog (gAt_read T k a hS e _ _ hs _ hv (gOf_read T hS o hh h))
    (wAt_top_read T k a hS e _ _ hs hv) _ _
end Reads
section Facts
variable {ℓ : StepParameters}
open scoped Quaternion
private theorem curvature_sum (hSum : curvatureLevelSumStatement) (T : StageTower ℓ) (ρA : ℝ)
    (hρ : ∀ j, (T.stage j).anchorRadius = ρA) (k N M : ℕ) [NeZero N] (nn x : ℝ)
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N)))
    (p : TorusPlaquette (fineSide ℓ.side M (fineSide ℓ.side M N))) (c : Fin 3)
    (u : MarkedSample ℓ (k + M + M) N) :
    ∑ j ∈ Finset.Ico 0 M, zetaOf T k N M nn (logCubeScale x) ρA o p c j u +
        topOf k N M nn (logCubeScale x) ρA (x ^ (-(1 / 4 : ℝ))) o p c u =
      imaginaryComponent c (sampledCurvature T k M nn x N u o p) := by
  have h := hSum ℓ T ρA hρ k nn (logCubeScale x) M (fineSide ℓ.side M N) (vOf k N M u) o
    (topLogForm ℓ (topField ℓ (k + M) (fineSide ℓ.side M N) (vOf k N M u))
      (siteAbove ℓ.side M (fineSide ℓ.side M N) o)
      (ballRadius ℓ.side nn (logCubeScale x) M) (x ^ (-(1 / 4 : ℝ)))) (gOf k N M o u) p
  have e : sampledCurvature T k M nn x N u o p =
      lieFormCurl (descendedForm T k nn (logCubeScale x) M (fineSide ℓ.side M N) (vOf k N M u) o
        (topLogForm ℓ (topField ℓ (k + M) (fineSide ℓ.side M N) (vOf k N M u))
          (siteAbove ℓ.side M (fineSide ℓ.side M N) o)
          (ballRadius ℓ.side nn (logCubeScale x) M) (x ^ (-(1 / 4 : ℝ)))) (gOf k N M o u)) p := rfl
  rw [e, h, fluctuationSum_eq, imaginaryComponent_add, imaginaryComponent_sum, Nat.Ico_zero_eq_range]
  rfl
private theorem chi_step (T : StageTower ℓ) (k N M : ℕ) [NeZero N] (m : ℝ)
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) {j : ℕ} (hj : j < M) (u : MarkedSample ℓ (k + M + M) N) :
    u ∈ chi T k N M m o j ↔ u ∈ chi T k N M m o (j + 1) ∧
      missAt T k m j M (fineSide ℓ.side M N) (vOf k N M u) o := by
  constructor
  · intro h
    exact ⟨chi_mono T k N M m o (Nat.le_succ j) h, h.2 j le_rfl hj⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1.1, fun i hi hi' => ?_⟩
    rcases Nat.eq_or_lt_of_le hi with rfl | h
    · exact h2
    · exact h1.2 i h hi'
private theorem chi_of_ge (T : StageTower ℓ) (k N M : ℕ) [NeZero N] (m : ℝ)
    (o : TorusSite (fineSide ℓ.side M (fineSide ℓ.side M N))) {a : ℕ} (ha : M ≤ a) :
    chi T k N M m o a = chi T k N M m o M := by
  ext u
  constructor
  · exact fun h => ⟨h.1, fun j h1 h2 => by omega⟩
  · exact fun h => ⟨h.1, fun j h1 h2 => by omega⟩
private theorem term_cut (T : StageTower ℓ) (t : ℕ) {n : ℕ} [NeZero n] (g : TorusSite n → UnitQuaternion)
    (Z : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * ℓ.side)) (l : TorusBond (n * ℓ.side) → ℝ) :
    ∑ b, cutOf Z l b • deviationInGauge T t g Z V W b = ∑ b, l b • deviationInGauge T t g Z V W b := by
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold cutOf
  by_cases h : parentBlock ℓ.side b.1 ∈ Z
  · rw [if_pos h]
  · have : deviationInGauge T t g Z V W b = 0 := by
      unfold deviationInGauge
      rw [if_neg fun h' => h h'.1]
    rw [if_neg h, this, zero_smul, smul_zero]
private theorem zeta_eq (T : StageTower ℓ) (k N j e : ℕ) [NeZero N] (nn ρ₀ ρA : ℝ)
    (o : TorusSite (fineSide ℓ.side (j + 1 + e) (fineSide ℓ.side (j + 1 + e) N)))
    (p : TorusPlaquette (fineSide ℓ.side (j + 1 + e) (fineSide ℓ.side (j + 1 + e) N))) (c : Fin 3)
    (u : MarkedSample ℓ (k + (j + 1 + e) + (j + 1 + e)) N) :
    zetaOf T k N (j + 1 + e) nn ρ₀ ρA o p c j u = imaginaryComponent c
      (∑ b : TorusBond (fineSide ℓ.side e (fineSide ℓ.side (j + 1 + e) N) * ℓ.side),
      cutOf (supBall (oAt (j + 1) e _ o) (ballRadius ℓ.side nn ρ₀ (j + 1) - 3 * ρ₀))
          (lAt k ρA j e (fineSide ℓ.side (j + 1 + e) N) p) b •
        deviationInGauge T (k + j) (gAt k (j + 1) e _ (vOf k N (j + 1 + e) u) (gOf k N (j + 1 + e) o u))
          (supBall (oAt (j + 1) e _ o) (ballRadius ℓ.side nn ρ₀ (j + 1) - 3 * ρ₀))
          (wAt k (j + 1) e _ (vOf k N (j + 1 + e) u)).2.2.1
          (topField ℓ (k + j) _ (wAt k (j + 1) e _ (vOf k N (j + 1 + e) u)).1) b) := by
  unfold zetaOf
  rw [levelTerm_eq, term_cut]
private theorem comap_castD_heq {s s' n : ℕ} (h : s = s') (m : MeasurableSpace (MarkedSample ℓ s' n)) :
    HEq (m.comap (castD h n)) m := by
  subst h
  exact heq_of_eq MeasurableSpace.comap_id
end Facts
section TheStep
variable (Tb : ParameterAssignment) (y : ℝ)
private def StepLaw (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ) (j r : ℕ)
    {S B : ℕ} [NeZero B]
    (z : MarkedSample (Tb.stepParameters y) S N → MarkedSample (Tb.stepParameters y) (k + j + 1) B)
    (𝔽 : MeasurableSpace (MarkedSample (Tb.stepParameters y) S N)) (o : TorusSite B)
    (g : MarkedSample (Tb.stepParameters y) S N → TorusSite B → UnitQuaternion)
    (s : MarkedSample (Tb.stepParameters y) S N → ℝ)
    (l : Fin r → TorusBond (B * (Tb.stepParameters y).side) → ℝ) (e : Fin r → Fin 3) (C c : ℝ) : Prop :=
  Integrable (Set.indicator
      {u' | Disjoint (stageState T (k + j + 1) _ (z u')).2.1
          (supBall o (localBlockSide (Tb.stepParameters y) β k)) ∧
        StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) o (z u')}
      (fun u' => ∏ i, imaginaryComponent (e i) (∑ b, l i b • deviationInGauge T (k + j) (g u')
        (supBall o (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
          3 * localLogScale (Tb.stepParameters y) β k))
        (topField (Tb.stepParameters y) (k + j + 1) _ (z u'))
        (topField (Tb.stepParameters y) (k + j) _ (z u').1) b)))
    (markedSampleLaw T β S N) ∧
  ∀ᵐ u ∂(markedSampleLaw T β S N),
    Disjoint (stageState T (k + j + 1) _ (z u)).2.1 (supBall o (localBlockSide (Tb.stepParameters y) β k)) →
    IsNearIdentity (g u) (topField (Tb.stepParameters y) (k + j + 1) _ (z u)) o
      (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1)) (s u) →
    |((markedSampleLaw T β S N)[Set.indicator
          {u' | Disjoint (stageState T (k + j + 1) _ (z u')).2.1
              (supBall o (localBlockSide (Tb.stepParameters y) β k)) ∧
            StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) o (z u')}
          (fun u' => ∏ i, imaginaryComponent (e i) (∑ b, l i b • deviationInGauge T (k + j) (g u')
            (supBall o (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
              3 * localLogScale (Tb.stepParameters y) β k))
            (topField (Tb.stepParameters y) (k + j + 1) _ (z u'))
            (topField (Tb.stepParameters y) (k + j) _ (z u').1) b)) | 𝔽]) u -
      flowCouplings (Tb.stepParameters y) β (k + j) ^ (-(r : ℝ) / 2) * wickPairingSum fun i i' =>
        if e i = e i' then stepCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side (k + j) B
          (l i) (l i') else 0| ≤
      C * (1 / 2 : ℝ) ^ j * (flowCouplings (Tb.stepParameters y) β k ^ (-((r : ℝ) + 1) / 2) +
        flowCouplings (Tb.stepParameters y) β k ^ (-(r : ℝ) / 2) * s u) +
        Real.exp (-(c * localLogScale (Tb.stepParameters y) β k))
private theorem step_at (r : ℕ) (C c x₀ : ℝ)
    (hr : ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ) (j d' : ℕ)
      (o : TorusSite (fineSide (Tb.stepParameters y).side d' N))
      (g : MarkedSample (Tb.stepParameters y) (k + j + 1 + d') N →
        TorusSite (fineSide (Tb.stepParameters y).side d' N) → UnitQuaternion)
      (s : MarkedSample (Tb.stepParameters y) (k + j + 1 + d') N → ℝ)
      (l : Fin r → TorusBond (fineSide (Tb.stepParameters y).side d' N * (Tb.stepParameters y).side) → ℝ)
      (e : Fin r → Fin 3),
      IsLocalChainAbove Tb y T β k (fineSide (Tb.stepParameters y).side d' N) nn x₀ →
      (Tb.stepParameters y).side ∣ fineSide (Tb.stepParameters y).side d' N →
      j < localChainDepth (Tb.stepParameters y) β k →
      j + 1 + d' ≤ 2 * localChainDepth (Tb.stepParameters y) β k →
      Measurable[upperSigma T (k + j + 1) d' N] g → Measurable[upperSigma T (k + j + 1) d' N] s → (∀ u, 0 ≤ s u) →
      (∀ i, ∑ b, |l i b| ≤ 4 * (1 / 2 : ℝ) ^ j) →
      (∀ i b, parentBlock (Tb.stepParameters y).side b.1 ∉ supBall o
          (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
            3 * localLogScale (Tb.stepParameters y) β k) →
        l i b = 0) →
      StepLaw Tb y T β k N nn j r (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N)
        (upperSigma T (k + j + 1) d' N) o g s l e C c)
    (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ) (j d' : ℕ) {S B : ℕ} [NeZero B]
    (hS : k + j + 1 + d' = S) (hB : fineSide (Tb.stepParameters y).side d' N = B)
    (z : MarkedSample (Tb.stepParameters y) S N → MarkedSample (Tb.stepParameters y) (k + j + 1) B)
    (hz : ∀ (u : MarkedSample (Tb.stepParameters y) S N) (u' : MarkedSample (Tb.stepParameters y) (k + j + 1 + d') N),
      HEq u u' → HEq (z u) (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N u'))
    (𝔽 : MeasurableSpace (MarkedSample (Tb.stepParameters y) S N)) (h𝔽 : HEq 𝔽 (upperSigma T (k + j + 1) d' N))
    (o : TorusSite B)
    (g : MarkedSample (Tb.stepParameters y) S N → TorusSite B → UnitQuaternion)
    (s : MarkedSample (Tb.stepParameters y) S N → ℝ)
    (l : Fin r → TorusBond (B * (Tb.stepParameters y).side) → ℝ) (e : Fin r → Fin 3)
    (h1 : IsLocalChainAbove Tb y T β k B nn x₀) (h2 : (Tb.stepParameters y).side ∣ B)
    (h3 : j < localChainDepth (Tb.stepParameters y) β k)
    (h4 : j + 1 + d' ≤ 2 * localChainDepth (Tb.stepParameters y) β k) (h5 : Measurable[𝔽] g)
    (h6 : Measurable[𝔽] s) (h7 : ∀ u, 0 ≤ s u)
    (h8 : ∀ i, ∑ b, |l i b| ≤ 4 * (1 / 2 : ℝ) ^ j)
    (h9 : ∀ i b, parentBlock (Tb.stepParameters y).side b.1 ∉ supBall o
        (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
          3 * localLogScale (Tb.stepParameters y) β k) →
        l i b = 0) :
    StepLaw Tb y T β k N nn j r z 𝔽 o g s l e C c := by
  subst hS
  subst hB
  have hz' : z = sampleBelow (Tb.stepParameters y) (k + j + 1) d' N := funext fun u => eq_of_heq (hz u u HEq.rfl)
  subst hz'
  have h𝔽' := eq_of_heq h𝔽
  subst h𝔽'
  exact hr T β k N nn j d' o g s l e h1 h2 h3 h4 h5 h6 h7 h8 h9
end TheStep
section TheCore
variable (Tb : ParameterAssignment) (y : ℝ)
private theorem up_id {T : StageTower (Tb.stepParameters y)}
    (hup : ∀ (t d n : ℕ) [NeZero n], upperSigma T t d n ≤ markedSampleMeasurableSpace (Tb.stepParameters y) (t + d) n)
    {t d N s : ℕ} [NeZero N] (hs : s = t + d) :
    Up T t d N hs (id : MarkedSample (Tb.stepParameters y) s N → MarkedSample (Tb.stepParameters y) s N) := by
  subst hs
  exact (measurable_id (α := MarkedSample (Tb.stepParameters y) (t + d) N)).mono le_rfl (hup t d N)
private structure ChainInputs (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ) (M : ℕ)
    (ρ₀ m : ℝ) : Prop where
  prob : ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (markedSampleLaw T β s n)
  fst : ∀ (s n : ℕ) [NeZero n],
    (markedSampleLaw T β (s + 1) n).map (fun u : MarkedSample (Tb.stepParameters y) (s + 1) n => u.1) =
      markedSampleLaw T β s (n * (Tb.stepParameters y).side)
  S : ∀ (t d n : ℕ) [NeZero n], Measurable[upperSigma T t d n] (stageState T (t + d) n)
  up : ∀ (t d n : ℕ) [NeZero n], upperSigma T t d n ≤ markedSampleMeasurableSpace (Tb.stepParameters y) (t + d) n
  H : ∀ (R : StepSetup) (n : ℕ) [NeZero n] (a : Finset (TorusSite n)),
    MeasurableSet {V : TorusField n | hotCoreSites R V = a}
  log : MeasurableQuaternion (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : Quaternion ℝ))
  Bor : ∀ (d n : ℕ) [NeZero n] (o' : TorusSite n) (b : TorusBond (n * (Tb.stepParameters y).side)), N ≤ n →
    (Tb.stepParameters y).side ∣ n → d < M →
    parentBlock (Tb.stepParameters y).side b.1 ∈
      supBall o' (ballRadius (Tb.stepParameters y).side nn ρ₀ (d + 1) - 3 * ρ₀) →
    b ∈ chartBonds (Tb.stepParameters y).side n →
    MeasurableQuaternion fun p : TorusField n × TorusField (n * (Tb.stepParameters y).side) =>
      if IsColdOnBall (Tb.stepParameters y).threshold p.1 o' m then
        (stepDeviation T (k + d) p.1 p.2 b : Quaternion ℝ) else 0
  down : ∀ t, k ≤ t → t < k + 2 * M → ∀ (n : ℕ) [NeZero n], N ≤ n → (Tb.stepParameters y).side ∣ n →
    ∀ᵐ u ∂(markedSampleLaw T β (t + 1) n), Down T m t n u
  LN : (Tb.stepParameters y).side ∣ N
private theorem ChainInputs.good {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k N : ℕ} [NeZero N] {nn : ℝ}
    {M : ℕ} {ρ₀ m : ℝ} (c : ChainInputs Tb y T β k N nn M ρ₀ m) :
    ∀ᵐ u ∂(markedSampleLaw T β (k + M + M) N), Good T k N M m u := by
  have h1 := allDown_ae c.fst m (k + M) N M
    (fun t h1 h2 n _ hn hL => c.down t (by omega) (by omega) n hn hL) M N le_rfl le_rfl c.LN
  have hpos : 0 < (Tb.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne (Tb.stepParameters y).side)
  have hN : N ≤ fineSide (Tb.stepParameters y).side M N := by
    rw [fineSide_eq]
    exact Nat.le_mul_of_pos_right N (pow_pos hpos _)
  have hLd : (Tb.stepParameters y).side ∣ fineSide (Tb.stepParameters y).side M N := by
    rw [fineSide_eq]
    exact c.LN.mul_right _
  have h2 := allDown_ae c.fst m k N M (fun t h1 h2 n _ hn hL => c.down t h1 (by omega) n hn hL) M
    (fineSide (Tb.stepParameters y).side M N) le_rfl hN hLd
  have h3 := below_ae c.fst (k + M) M N _ h2
  filter_upwards [h1, h3] with u a b
  exact ⟨a, b⟩
private theorem ChainInputs.chi_meas {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k N : ℕ} [NeZero N] {nn : ℝ}
    {M : ℕ} {ρ₀ m : ℝ} (c : ChainInputs Tb y T β k N nn M ρ₀ m)
    (o : TorusSite (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N))) (a : ℕ) :
    MeasurableSet (chi T k N M m o a) := by
  have key : ∀ a, a ≤ M → MeasurableSet (chi T k N M m o a) := by
    intro a ha
    obtain ⟨e, rfl⟩ : ∃ e, M = a + e := ⟨M - a, by omega⟩
    have hh : k + (a + e) + (a + e) = k + a + (e + (a + e)) := by omega
    exact chi_read T c.S c.H m o hh (up_id Tb y c.up (N := N) hh)
  by_cases ha : a ≤ M
  · exact key a ha
  · rw [chi_of_ge T k N M m o (a := a) (by omega)]
    exact key M le_rfl
private theorem ChainInputs.zeta_meas {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k N : ℕ} [NeZero N] {nn : ℝ}
    {M : ℕ} {ρ₀ m : ℝ} (c : ChainInputs Tb y T β k N nn M ρ₀ m) (ρA : ℝ)
    (o : TorusSite (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (p : TorusPlaquette (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (cc : Fin 3) {u₀ : ℕ} (hu : u₀ ≤ M) :
    AEStronglyMeasurable ((chi T k N M m o u₀).indicator (zetaOf T k N M nn ρ₀ ρA o p cc u₀))
      (markedSampleLaw T β (k + M + M) N) := by
  have hG := ChainInputs.good Tb y c
  obtain ⟨e, rfl⟩ : ∃ e, M = u₀ + e := ⟨M - u₀, by omega⟩
  have hh : k + (u₀ + e) + (u₀ + e) = k + u₀ + (e + (u₀ + e)) := by omega
  have hU := up_id Tb y c.up (N := N) hh
  have hCm : MeasurableSet (chi T k N (u₀ + e) m o u₀ ∩ coldSet k N (u₀ + e) m o u₀) :=
    (chi_read T c.S c.H m o hh hU).inter (cold_read T c.S m o hh hU)
  have hM := zeta_read T nn ρ₀ ρA m c.S c.Bor c.LN o p cc hh hU hCm (fun ω hω => hω.2) u₀ le_rfl
  refine (Measurable.aestronglyMeasurable hM).congr ?_
  filter_upwards [hG] with u hu'
  by_cases h1 : u ∈ chi T k N (u₀ + e) m o u₀
  · have h2 := chi_subset_cold T k N _ m o u₀ u h1 hu'
    have h3 : u ∈ chi T k N (u₀ + e) m o u₀ ∩ coldSet k N (u₀ + e) m o u₀ := ⟨h1, h2⟩
    simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h3, id]
  · have h3 : u ∉ chi T k N (u₀ + e) m o u₀ ∩ coldSet k N (u₀ + e) m o u₀ := fun h => h1 h.1
    simp only [Set.indicator_of_notMem h1, Set.indicator_of_notMem h3]
private theorem ChainInputs.top_meas {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k N : ℕ} [NeZero N] {nn : ℝ}
    {M : ℕ} {ρ₀ m : ℝ} (c : ChainInputs Tb y T β k N nn M ρ₀ m) (ρA s₀ : ℝ)
    (o : TorusSite (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (p : TorusPlaquette (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (cc : Fin 3) :
    Measurable (topOf k N M nn ρ₀ ρA s₀ o p cc) := by
  obtain ⟨e, rfl⟩ : ∃ e, M = 0 + e := ⟨M, by omega⟩
  have hh : k + (0 + e) + (0 + e) = k + 0 + (e + (0 + e)) := by omega
  exact top_read T nn ρ₀ ρA s₀ c.S c.log o p cc hh (up_id Tb y c.up (N := N) hh)
private theorem ChainInputs.s_meas {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k N : ℕ} [NeZero N] {nn : ℝ}
    {M : ℕ} {ρ₀ m : ℝ} (c : ChainInputs Tb y T β k N nn M ρ₀ m)
    (o : TorusSite (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N))) (a : ℕ) :
    Measurable (sFam k N M nn ρ₀ o a) := by
  by_cases ha : a ≤ M
  · obtain ⟨e, rfl⟩ : ∃ e, M = a + e := ⟨M - a, by omega⟩
    have hh : k + (a + e) + (a + e) = k + a + (e + (a + e)) := by omega
    have e1 : sFam k N (a + e) nn ρ₀ o a = fun u => nearDef k N a e nn ρ₀ (a + e) rfl o u :=
      funext fun u => sFam_eq k N a e nn ρ₀ o u
    rw [e1]
    exact near_read T nn ρ₀ c.S c.log o hh (up_id Tb y c.up (N := N) hh)
  · have e1 : sFam k N M nn ρ₀ o a = fun _ => 0 := funext fun u => by
      unfold sFam
      rw [dif_neg ha]
    rw [e1]
    exact measurable_const
end TheCore
section TheStepOfTheChain
variable (Tb : ParameterAssignment) (y : ℝ)
private def zFam (T : StageTower (Tb.stepParameters y)) (k N M : ℕ) [NeZero N] (nn ρ₀ ρA : ℝ) {q : ℕ}
    (o : TorusSite (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (p : Fin q → TorusPlaquette (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (ec : Fin q → Fin 3) (j : ℕ) (i : Fin q) : MarkedSample (Tb.stepParameters y) (k + M + M) N → ℝ :=
  zetaOf T k N M nn ρ₀ ρA o (p i) (ec i) j
private def tFam (k N M : ℕ) [NeZero N] (nn ρ₀ ρA s₀ : ℝ) {q : ℕ}
    (o : TorusSite (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (p : Fin q → TorusPlaquette (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (ec : Fin q → Fin 3) (i : Fin q) : MarkedSample (Tb.stepParameters y) (k + M + M) N → ℝ :=
  topOf k N M nn ρ₀ ρA s₀ o (p i) (ec i)
private def gFam (k N M : ℕ) [NeZero N] (ρA : ℝ) {q : ℕ}
    (p : Fin q → TorusPlaquette (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (ec : Fin q → Fin 3) (j : ℕ) (i i' : Fin q) : ℝ :=
  if ec i = ec i' then levelCov k ρA j M (fineSide (Tb.stepParameters y).side M N) (p i) (p i') else 0
private def gcFam (k N M : ℕ) [NeZero N] (nn ρ₀ ρA : ℝ) {q : ℕ}
    (o : TorusSite (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (p : Fin q → TorusPlaquette (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (ec : Fin q → Fin 3) (j : ℕ) (i i' : Fin q) : ℝ :=
  if ec i = ec i' then levelCovCut k nn ρ₀ ρA j M (fineSide (Tb.stepParameters y).side M N) o (p i) (p i') else 0
private theorem stepMomentBound {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k N : ℕ} [NeZero N] {nn : ℝ}
    {j e q r : ℕ}
    (c : ChainInputs Tb y T β k N nn (j + 1 + e) (localLogScale (Tb.stepParameters y) β k)
      (localBlockSide (Tb.stepParameters y) β k : ℝ))
    (ρA s₀ K X ε Bd Cc cc xr Xsj : ℝ)
    (o : TorusSite (fineSide (Tb.stepParameters y).side (j + 1 + e)
      (fineSide (Tb.stepParameters y).side (j + 1 + e) N)))
    (p : Fin q → TorusPlaquette (fineSide (Tb.stepParameters y).side (j + 1 + e)
      (fineSide (Tb.stepParameters y).side (j + 1 + e) N))) (ec : Fin q → Fin 3)
    (f : Fin r → Fin q) (S : Finset (Fin q))
    (hr : ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ) (j d' : ℕ)
      (o : TorusSite (fineSide (Tb.stepParameters y).side d' N))
      (g : MarkedSample (Tb.stepParameters y) (k + j + 1 + d') N →
        TorusSite (fineSide (Tb.stepParameters y).side d' N) → UnitQuaternion)
      (s : MarkedSample (Tb.stepParameters y) (k + j + 1 + d') N → ℝ)
      (l : Fin r → TorusBond (fineSide (Tb.stepParameters y).side d' N * (Tb.stepParameters y).side) → ℝ)
      (e : Fin r → Fin 3),
      IsLocalChainAbove Tb y T β k (fineSide (Tb.stepParameters y).side d' N) nn xr →
      (Tb.stepParameters y).side ∣ fineSide (Tb.stepParameters y).side d' N →
      j < localChainDepth (Tb.stepParameters y) β k →
      j + 1 + d' ≤ 2 * localChainDepth (Tb.stepParameters y) β k →
      Measurable[upperSigma T (k + j + 1) d' N] g → Measurable[upperSigma T (k + j + 1) d' N] s → (∀ u, 0 ≤ s u) →
      (∀ i, ∑ b, |l i b| ≤ 4 * (1 / 2 : ℝ) ^ j) →
      (∀ i b, parentBlock (Tb.stepParameters y).side b.1 ∉ supBall o
          (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
            3 * localLogScale (Tb.stepParameters y) β k) →
        l i b = 0) →
      StepLaw Tb y T β k N nn j r (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N)
        (upperSigma T (k + j + 1) d' N) o g s l e Cc cc)
    (hloc : IsLocalChainAbove Tb y T β k
      (fineSide (Tb.stepParameters y).side e (fineSide (Tb.stepParameters y).side (j + 1 + e) N)) nn xr)
    (hM : j + 1 + e = localChainDepth (Tb.stepParameters y) β k)
    (hrow : ∀ i, ∑ b, |lAt k ρA j e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (p i) b| ≤
      4 * (1 / 2 : ℝ) ^ j)
    (hGb : ∀ᵐ u ∂(markedSampleLaw T β (k + (j + 1 + e) + (j + 1 + e)) N),
      u ∈ chi T k N (j + 1 + e) (localBlockSide (Tb.stepParameters y) β k : ℝ) o (j + 1) → ∀ i,
        |tailSum (j + 1 + e)
          (zFam Tb y T k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA o p ec)
          (tFam Tb y k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA s₀ o p ec) (j + 1) i u| ≤ Bd)
    (hBd : 0 ≤ Bd) (hK0 : 0 ≤ K) (hCK : Cc ≤ K)
    (hε : Real.exp (-(cc * localLogScale (Tb.stepParameters y) β k)) ≤ ε)
    (hXs : Xsj = flowCouplings (Tb.stepParameters y) β (k + j) ^ (-(1 / 2 : ℝ)))
    (hxj : 0 ≤ flowCouplings (Tb.stepParameters y) β (k + j))
    (hX : X = flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ)))
    (hx : 0 < flowCouplings (Tb.stepParameters y) β k) :
    |∫ ω, (chi T k N (j + 1 + e) (localBlockSide (Tb.stepParameters y) β k : ℝ) o j).indicator (fun ω =>
        (∏ a, zFam Tb y T k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA o p ec j (f a) ω) *
          ∏ i ∈ S, tailSum (j + 1 + e)
            (zFam Tb y T k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA o p ec)
            (tFam Tb y k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA s₀ o p ec) (j + 1) i ω) ω
          ∂(markedSampleLaw T β (k + (j + 1 + e) + (j + 1 + e)) N) -
      Xsj ^ r * wickPairingSum (fun a b =>
          gcFam Tb y k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA o p ec j (f a) (f b)) *
        ∫ ω, (chi T k N (j + 1 + e) (localBlockSide (Tb.stepParameters y) β k : ℝ) o (j + 1)).indicator (fun ω =>
          ∏ i ∈ S, tailSum (j + 1 + e)
            (zFam Tb y T k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA o p ec)
            (tFam Tb y k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA s₀ o p ec) (j + 1) i ω) ω
          ∂(markedSampleLaw T β (k + (j + 1 + e) + (j + 1 + e)) N)| ≤
      ∫ ω, (chi T k N (j + 1 + e) (localBlockSide (Tb.stepParameters y) β k : ℝ) o (j + 1)).indicator (fun ω =>
        |∏ i ∈ S, tailSum (j + 1 + e)
            (zFam Tb y T k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA o p ec)
            (tFam Tb y k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA s₀ o p ec) (j + 1) i ω| *
          (K * (1 / 2 : ℝ) ^ j * (X ^ (r + 1) + X ^ r *
            sFam k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) o (j + 1) ω) + ε)) ω
        ∂(markedSampleLaw T β (k + (j + 1 + e) + (j + 1 + e)) N) := by
  have hprob := c.prob (k + (j + 1 + e) + (j + 1 + e)) N
  have hG := ChainInputs.good Tb y c
  have hh : k + (j + 1 + e) + (j + 1 + e) = k + (j + 1) + (e + (j + 1 + e)) := by omega
  have hs : k + (j + 1 + e) = k + (j + 1) + e := by omega
  set m : ℝ := (localBlockSide (Tb.stepParameters y) β k : ℝ) with hm
  set ρ₀ := localLogScale (Tb.stepParameters y) β k with hρ₀
  set μ := markedSampleLaw T β (k + (j + 1 + e) + (j + 1 + e)) N with hμ
  let 𝔽 : MeasurableSpace (MarkedSample (Tb.stepParameters y) (k + (j + 1 + e) + (j + 1 + e)) N) :=
    MeasurableSpace.comap (castD hh N) (upperSigma T (k + (j + 1)) (e + (j + 1 + e)) N)
  have h𝔽le : 𝔽 ≤ markedSampleMeasurableSpace (Tb.stepParameters y) (k + (j + 1 + e) + (j + 1 + e)) N :=
    (MeasurableSpace.comap_mono (c.up _ _ _)).trans (measurable_castD hh N).comap_le
  have hUp : @Up (Tb.stepParameters y) _ 𝔽 T (k + (j + 1)) (e + (j + 1 + e)) N _ _ hh id := comap_measurable _
  have hUv : @Up (Tb.stepParameters y) _ 𝔽 T (k + (j + 1)) e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) _ _ hs
      (fun ω => vOf k N (j + 1 + e) ω) :=
    @vOf_up (Tb.stepParameters y) _ 𝔽 T k N (j + 1) e _ id hh hUp hs
  have hg : Measurable[𝔽] fun u => gAt k (j + 1) e (fineSide (Tb.stepParameters y).side (j + 1 + e) N)
      (vOf k N (j + 1 + e) u) (gOf k N (j + 1 + e) o u) :=
    @gAt_read (Tb.stepParameters y) _ 𝔽 T k (j + 1) c.S e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) _ _ hs
      _ hUv (@gOf_read (Tb.stepParameters y) _ 𝔽 T c.S k N (j + 1) e _ o id hh hUp)
  have hsm : Measurable[𝔽] (sFam k N (j + 1 + e) nn ρ₀ o (j + 1)) := by
    have e1 : sFam k N (j + 1 + e) nn ρ₀ o (j + 1) = fun u => nearDef k N (j + 1) e nn ρ₀ (j + 1 + e) rfl o u :=
      funext fun u => sFam_eq k N (j + 1) e nn ρ₀ o u
    rw [e1]
    exact @near_read (Tb.stepParameters y) _ 𝔽 T nn ρ₀ c.S c.log k N (j + 1) e _ o id hh hUp
  set oo := oAt (j + 1) e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) o with hoo
  set R := ballRadius (Tb.stepParameters y).side nn ρ₀ (j + 1) - 3 * ρ₀ with hR
  let l : Fin r → TorusBond (fineSide (Tb.stepParameters y).side e
      (fineSide (Tb.stepParameters y).side (j + 1 + e) N) * (Tb.stepParameters y).side) → ℝ := fun a =>
    cutOf (supBall oo R) (lAt k ρA j e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (p (f a)))
  have hLB : (Tb.stepParameters y).side ∣
      fineSide (Tb.stepParameters y).side e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) := by
    rw [fineSide_eq, fineSide_eq]
    exact (c.LN.mul_right _).mul_right _
  have hSL := step_at Tb y r Cc cc xr hr T β k N nn j (e + (j + 1 + e)) (S := k + (j + 1 + e) + (j + 1 + e))
    (B := fineSide (Tb.stepParameters y).side e (fineSide (Tb.stepParameters y).side (j + 1 + e) N)) (by omega)
    (fineSide_add _ _ _ _)
    (fun u => wAt k (j + 1) e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u))
    (fun u u' h => below_heq k (j + 1) e (j + 1 + e) N u u' h) 𝔽 (comap_castD_heq hh _) oo
    (fun u => gAt k (j + 1) e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u)
      (gOf k N (j + 1 + e) o u))
    (sFam k N (j + 1 + e) nn ρ₀ o (j + 1)) l (fun a => ec (f a)) hloc hLB (by omega) (by omega) hg hsm
    (fun u => sFam_nonneg _ _ _ _ _ _ _ _)
    (fun a => (cut_sum_abs_le _ _).trans (hrow (f a)))
    (fun a b hb => by
      show cutOf (supBall oo R) _ b = 0
      unfold cutOf
      rw [if_neg hb])
  obtain ⟨hFi, hae⟩ := hSL
  set A₁ := chi T k N (j + 1 + e) m o (j + 1) with hA₁
  set A₀ := chi T k N (j + 1 + e) m o j with hA₀
  set Z := zFam Tb y T k N (j + 1 + e) nn ρ₀ ρA o p ec with hZ
  set Tp := tFam Tb y k N (j + 1 + e) nn ρ₀ ρA s₀ o p ec with hTp
  set Q : MarkedSample (Tb.stepParameters y) (k + (j + 1 + e) + (j + 1 + e)) N → ℝ :=
    fun ω => ∏ i ∈ S, tailSum (j + 1 + e) Z Tp (j + 1) i ω with hQ
  set E : MarkedSample (Tb.stepParameters y) (k + (j + 1 + e) + (j + 1 + e)) N → ℝ := fun ω =>
    K * (1 / 2 : ℝ) ^ j * (X ^ (r + 1) + X ^ r * sFam k N (j + 1 + e) nn ρ₀ o (j + 1) ω) + ε with hE
  have hFY : ∀ᵐ u ∂μ, A₀.indicator (fun ω => (∏ a, Z j (f a) ω) * Q ω) u =
      (Set.indicator {u' | Disjoint (stageState T (k + j + 1) _ (wAt k (j + 1) e
              (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u'))).2.1
            (supBall oo (localBlockSide (Tb.stepParameters y) β k)) ∧
          StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) oo
            (wAt k (j + 1) e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u'))}
        (fun u' => ∏ i, imaginaryComponent (ec (f i)) (∑ b, l i b • deviationInGauge T (k + j)
          (gAt k (j + 1) e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u')
            (gOf k N (j + 1 + e) o u'))
          (supBall oo (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
            3 * localLogScale (Tb.stepParameters y) β k))
          (topField (Tb.stepParameters y) (k + j + 1) _ (wAt k (j + 1) e
            (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u')))
          (topField (Tb.stepParameters y) (k + j) _ (wAt k (j + 1) e
            (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u')).1) b)) u) *
        A₁.indicator Q u := by
    filter_upwards [hG] with u hGu
    by_cases h1 : u ∈ A₁
    · have hd := chi_off T k N (j + 1) e m o u h1 hGu
      by_cases h2 : missAt T k m j (j + 1 + e) (fineSide (Tb.stepParameters y).side (j + 1 + e) N)
          (vOf k N (j + 1 + e) u) o
      · have hu0 : u ∈ A₀ := (chi_step T k N _ m o (by omega) u).2 ⟨h1, h2⟩
        have hmem : u ∈ {u' | Disjoint (stageState T (k + j + 1) _ (wAt k (j + 1) e
              (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u'))).2.1
            (supBall oo (localBlockSide (Tb.stepParameters y) β k)) ∧
          StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) oo
            (wAt k (j + 1) e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u'))} :=
          ⟨hd, (missAt_eq T k m j e _ _ o).1 h2⟩
        rw [Set.indicator_of_mem hu0, Set.indicator_of_mem h1, Set.indicator_of_mem hmem]
        congr 1
        exact Finset.prod_congr rfl fun a _ => zeta_eq T k N j e nn ρ₀ ρA o (p (f a)) (ec (f a)) u
      · have hu0 : u ∉ A₀ := fun h => h2 ((chi_step T k N _ m o (by omega) u).1 h).2
        have hmem : u ∉ {u' | Disjoint (stageState T (k + j + 1) _ (wAt k (j + 1) e
              (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u'))).2.1
            (supBall oo (localBlockSide (Tb.stepParameters y) β k)) ∧
          StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) oo
            (wAt k (j + 1) e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u'))} :=
          fun h => h2 ((missAt_eq T k m j e _ _ o).2 h.2)
        rw [Set.indicator_of_notMem hu0, Set.indicator_of_notMem hmem, zero_mul]
    · have hu0 : u ∉ A₀ := fun h => h1 (chi_mono T k N _ m o (Nat.le_succ j) h)
      rw [Set.indicator_of_notMem hu0, Set.indicator_of_notMem h1, mul_zero]
  have hCm : @MeasurableSet _ 𝔽 (A₁ ∩ coldSet k N (j + 1 + e) m o (j + 1)) :=
    @MeasurableSet.inter _ 𝔽 _ _ (@chi_read (Tb.stepParameters y) _ 𝔽 T c.S c.H k N (j + 1) e _ m o id hh hUp)
      (@cold_read (Tb.stepParameters y) _ 𝔽 T c.S k N (j + 1) e _ m o id hh hUp)
  have hMO : @MO _ 𝔽 (A₁ ∩ coldSet k N (j + 1 + e) m o (j + 1)) Q := by
    refine @MO.prod _ 𝔽 _ _ hCm S (fun i ω => tailSum (j + 1 + e) Z Tp (j + 1) i ω) fun i _ => ?_
    refine @MO.add _ 𝔽 _ (fun ω => ∑ u ∈ Finset.Ico (j + 1) (j + 1 + e), Z u i ω) (Tp i)
      (@MO.sum _ 𝔽 _ _ hCm _ (fun u ω => Z u i ω) fun u hu => ?_)
      (@MO.of_measurable _ 𝔽 _ hCm _ (@top_read (Tb.stepParameters y) _ 𝔽 T nn ρ₀ ρA s₀ c.S c.log k N (j + 1) e _ o
        (p i) (ec i) id hh hUp))
    exact @zeta_read (Tb.stepParameters y) _ 𝔽 T nn ρ₀ ρA m c.S k N (j + 1) e _ c.Bor c.LN o (p i) (ec i) id hh hUp _
      hCm (fun ω hω => hω.2) u (Finset.mem_Ico.1 hu).1
  have hYm : AEStronglyMeasurable[𝔽] (A₁.indicator Q) μ := by
    refine ⟨(A₁ ∩ coldSet k N (j + 1 + e) m o (j + 1)).indicator Q, Measurable.stronglyMeasurable hMO, ?_⟩
    filter_upwards [hG] with u hGu
    by_cases h1 : u ∈ A₁
    · have h3 : u ∈ A₁ ∩ coldSet k N (j + 1 + e) m o (j + 1) := ⟨h1, chi_subset_cold T k N _ m o _ u h1 hGu⟩
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h3]
    · have h3 : u ∉ A₁ ∩ coldSet k N (j + 1 + e) m o (j + 1) := fun h => h1 h.1
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h3]
  have hYb : ∀ᵐ u ∂μ, |A₁.indicator Q u| ≤ (Bd + 1) ^ q := by
    filter_upwards [hGb] with u hu
    by_cases h1 : u ∈ A₁
    · rw [Set.indicator_of_mem h1, hQ]
      simp only []
      rw [Finset.abs_prod]
      have hb1 : (1 : ℝ) ≤ Bd + 1 := by linarith
      calc ∏ i ∈ S, |tailSum (j + 1 + e) Z Tp (j + 1) i u| ≤ ∏ _i ∈ S, (Bd + 1) :=
            Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => (hu h1 i).trans (by linarith)
        _ = (Bd + 1) ^ S.card := by simp
        _ ≤ (Bd + 1) ^ q := pow_le_pow_right₀ hb1 (by simpa using Finset.card_le_univ S)
    · rw [Set.indicator_of_notMem h1, abs_zero]
      positivity
  have hY0 : ∀ᵐ u ∂μ, u ∉ A₁ → A₁.indicator Q u = 0 :=
    Filter.Eventually.of_forall fun u hu => Set.indicator_of_notMem hu _
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le.trans hε
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact Real.rpow_nonneg hx.le _
  have hXpow : ∀ n : ℕ, flowCouplings (Tb.stepParameters y) β k ^ (-(n : ℝ) / 2) = X ^ n := by
    intro n
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hXpow1 : flowCouplings (Tb.stepParameters y) β k ^ (-((r : ℝ) + 1) / 2) = X ^ (r + 1) := by
    have := hXpow (r + 1)
    rwa [Nat.cast_add, Nat.cast_one] at this
  have hXjpow : flowCouplings (Tb.stepParameters y) β (k + j) ^ (-(r : ℝ) / 2) = Xsj ^ r := by
    rw [hXs, ← Real.rpow_natCast, ← Real.rpow_mul hxj]
    congr 1
    ring
  have hwick : (fun i i' : Fin r => if ec (f i) = ec (f i') then
        stepCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side (k + j)
          (fineSide (Tb.stepParameters y).side e (fineSide (Tb.stepParameters y).side (j + 1 + e) N)) (l i) (l i')
        else 0) =
      fun a b => gcFam Tb y k N (j + 1 + e) nn ρ₀ ρA o p ec j (f a) (f b) := by
    funext a b
    unfold gcFam
    rw [levelCovCut_eq]
  have hEb : ∀ᵐ u ∂μ, u ∈ A₁ → |(μ[Set.indicator {u' | Disjoint (stageState T (k + j + 1) _ (wAt k (j + 1) e
              (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u'))).2.1
            (supBall oo (localBlockSide (Tb.stepParameters y) β k)) ∧
          StepAvoids T (k + j) (localBlockSide (Tb.stepParameters y) β k) oo
            (wAt k (j + 1) e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u'))}
        (fun u' => ∏ i, imaginaryComponent (ec (f i)) (∑ b, l i b • deviationInGauge T (k + j)
          (gAt k (j + 1) e (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u')
            (gOf k N (j + 1 + e) o u'))
          (supBall oo (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
            3 * localLogScale (Tb.stepParameters y) β k))
          (topField (Tb.stepParameters y) (k + j + 1) _ (wAt k (j + 1) e
            (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u')))
          (topField (Tb.stepParameters y) (k + j) _ (wAt k (j + 1) e
            (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u')).1) b)) | 𝔽]) u -
      Xsj ^ r * wickPairingSum (fun a b => gcFam Tb y k N (j + 1 + e) nn ρ₀ ρA o p ec j (f a) (f b))| ≤ E u := by
    filter_upwards [hae, hG] with u a1 a2 hu
    have hd := chi_off T k N (j + 1) e m o u hu a2
    have hn : IsNearIdentity (gAt k (j + 1) e (fineSide (Tb.stepParameters y).side (j + 1 + e) N)
          (vOf k N (j + 1 + e) u) (gOf k N (j + 1 + e) o u))
        (topField (Tb.stepParameters y) (k + j + 1) _ (wAt k (j + 1) e
          (fineSide (Tb.stepParameters y).side (j + 1 + e) N) (vOf k N (j + 1 + e) u))) oo
        (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1))
        (sFam k N (j + 1 + e) nn ρ₀ o (j + 1) u) := by
      rw [sFam_eq]
      exact isNearIdentity_nearBall _ _ _ _
    have b := a1 hd hn
    rw [hXjpow, hwick, hXpow1, hXpow] at b
    refine b.trans ?_
    have hs0 := sFam_nonneg k N (j + 1 + e) nn ρ₀ o (j + 1) u
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
    have hw : 0 ≤ (1 / 2 : ℝ) ^ j * (X ^ (r + 1) + X ^ r * sFam k N (j + 1 + e) nn ρ₀ o (j + 1) u) := by positivity
    have : Cc * ((1 / 2 : ℝ) ^ j * (X ^ (r + 1) + X ^ r * sFam k N (j + 1 + e) nn ρ₀ o (j + 1) u)) ≤
        K * ((1 / 2 : ℝ) ^ j * (X ^ (r + 1) + X ^ r * sFam k N (j + 1 + e) nn ρ₀ o (j + 1) u)) :=
      mul_le_mul_of_nonneg_right hCK hw
    simp only [hE]
    nlinarith
  have hYi : Integrable (A₁.indicator Q) μ := by
    have hYm' : @AEStronglyMeasurable _ _ _
        (markedSampleMeasurableSpace (Tb.stepParameters y) (k + (j + 1 + e) + (j + 1 + e)) N)
        (markedSampleMeasurableSpace (Tb.stepParameters y) (k + (j + 1 + e) + (j + 1 + e)) N) (A₁.indicator Q) μ := by
      obtain ⟨g, hg', hgY⟩ := hYm
      exact ⟨g, hg'.mono h𝔽le, hgY⟩
    exact Integrable.of_bound hYm' _ (by simpa using hYb)
  have hEm : @Measurable _ _ (markedSampleMeasurableSpace (Tb.stepParameters y) (k + (j + 1 + e) + (j + 1 + e)) N)
      _ E := by
    have h1 := ChainInputs.s_meas Tb y c o (j + 1)
    exact (((h1.const_mul _).const_add _).const_mul _).add_const _
  have hEle : ∀ u, ‖E u‖ ≤ K * (1 / 2 : ℝ) ^ j * (X ^ (r + 1) + X ^ r * 4) + ε := by
    intro u
    have hs0 := sFam_nonneg k N (j + 1 + e) nn ρ₀ o (j + 1) u
    have hs4 := sFam_le k N (j + 1 + e) nn ρ₀ o (j + 1) u
    have hXr : 0 ≤ X ^ r := by positivity
    have hp : (0 : ℝ) ≤ K * (1 / 2 : ℝ) ^ j := by positivity
    have h1 : X ^ r * sFam k N (j + 1 + e) nn ρ₀ o (j + 1) u ≤ X ^ r * 4 := mul_le_mul_of_nonneg_left hs4 hXr
    have h2 : 0 ≤ X ^ r * sFam k N (j + 1 + e) nn ρ₀ o (j + 1) u := by positivity
    have h0 : 0 ≤ E u := by simp only [hE]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    simp only [hE]
    have := mul_le_mul_of_nonneg_left (add_le_add_left h1 (X ^ (r + 1))) hp
    linarith
  have hYE : Integrable (fun ω => |A₁.indicator Q ω| * E ω) μ :=
    hYi.abs.mul_bdd hEm.aestronglyMeasurable (Filter.Eventually.of_forall hEle)
  have hpull := @integral_mul_near_condExp _
    (markedSampleMeasurableSpace (Tb.stepParameters y) (k + (j + 1 + e) + (j + 1 + e)) N) _ hprob 𝔽 h𝔽le _ _ _ _ _ _
    hFi hYm hYb hY0 hEb hYE
  have e1 : ∫ ω, A₀.indicator (fun ω => (∏ a, Z j (f a) ω) * Q ω) ω ∂μ = _ := integral_congr_ae hFY
  rw [e1]
  have e3 : ∫ ω, A₁.indicator (fun ω => |Q ω| * E ω) ω ∂μ = ∫ ω, |A₁.indicator Q ω| * E ω ∂μ := by
    congr 1
    funext ω
    by_cases h1 : ω ∈ A₁
    · simp [h1]
    · simp [h1]
  rw [e3]
  exact hpull
end TheStepOfTheChain
section TheSizes
variable {ℓ : StepParameters}
open scoped Quaternion
private theorem ae_castD {T : StageTower ℓ} {β : ℝ} {s s' n : ℕ} [NeZero n] (h : s = s')
    {P : MarkedSample ℓ s' n → Prop}
    (hP : ∀ᵐ v ∂(markedSampleLaw T β s' n), P v) : ∀ᵐ u ∂(markedSampleLaw T β s n), P (castD h n u) := by
  subst h
  exact hP
private theorem integral_castD {T : StageTower ℓ} {β : ℝ} {s s' n : ℕ} [NeZero n] (h : s = s')
    (f : MarkedSample ℓ s' n → ℝ) :
    ∫ u, f (castD h n u) ∂(markedSampleLaw T β s n) = ∫ v, f v ∂(markedSampleLaw T β s' n) := by
  subst h
  rfl
private theorem integrable_castD {T : StageTower ℓ} {β : ℝ} {s s' n : ℕ} [NeZero n] (h : s = s')
    {f : MarkedSample ℓ s' n → ℝ}
    (hf : Integrable f (markedSampleLaw T β s' n)) :
    Integrable (fun u => f (castD h n u)) (markedSampleLaw T β s n) := by
  subst h
  exact hf
private theorem small_bottom (T : StageTower ℓ) (k a : ℕ) (nn ρ₀ s : ℝ) : ∀ (e n : ℕ) [NeZero n]
    (w : MarkedSample ℓ (k + (a + e)) n) (hs : k + (a + e) = k + a + e) (o : TorusSite (fineSide ℓ.side e n))
    (g : TorusSite n → UnitQuaternion),
    IsGaugeSmallAlong T (k + a) nn ρ₀ s e n (castD hs n w) o g →
    ∀ b : TorusBond (fineSide ℓ.side e n), b.1 ∈ supBall o (ballRadius ℓ.side nn ρ₀ 0) →
      ‖(minimalLog (gaugeTransform (gAt k a e n w g)
        (topField ℓ (k + a) (fineSide ℓ.side e n) (wAt k a e n w)) b) : ℍ[ℝ])‖ ≤ s := by
  intro e
  induction e with
  | zero =>
    intro n _ w hs o g h b hb
    exact h b hb
  | succ e ih =>
    intro n _ w hs o g h b hb
    have hs' : k + (a + e) = k + a + e := Nat.succ.inj hs
    obtain ⟨-, -, h3⟩ := h
    have hfst : (castD hs n w).1 = castD hs' (n * ℓ.side) w.1 := castD_fst hs' n w
    rw [hfst, topField_castD hs'] at h3
    exact ih (n * ℓ.side) w.1 hs' o _ h3 b hb
private theorem widenedStageSum_nonneg (T : StageTower ℓ) (t : ℕ) (nn ρ₀ : ℝ) : ∀ (d n : ℕ) [NeZero n]
    (u : MarkedSample ℓ (t + d) n) (o : TorusSite (fineSide ℓ.side d n)), 0 ≤ widenedStageSum T t nn ρ₀ d n u o := by apply _root_.YangMills.SharedProofs.p61945 <;> assumption
private theorem plaquettesIn_ball {n : ℕ} [NeZero n] (o : TorusSite n) {r r' : ℝ} (h : r ≤ r') :
    plaquettesIn (supBall o r) ⊆ plaquettesIn (supBall o r') := by apply _root_.YangMills.SharedProofs.p58549 <;> assumption
private theorem maxCurvatureOnBall_mono {n : ℕ} [NeZero n] (V : TorusField n) (o : TorusSite n) {r r' : ℝ}
    (h : r ≤ r') : maxCurvatureOnBall V o r ≤ maxCurvatureOnBall V o r' :=
  finsetSupNonneg_le _ _ (finsetSupNonneg_nonneg _ _) fun p hp =>
    le_finsetSupNonneg _ (fun p : TorusPlaquette n => curvature V p.1 p.2.1 p.2.2) (plaquettesIn_ball o h hp)
private theorem widenedStageMax_bottom (k a : ℕ) (nn ρ₀ : ℝ) : ∀ (e n : ℕ) [NeZero n]
    (w : MarkedSample ℓ (k + (a + e)) n) (hs : k + (a + e) = k + a + e) (o : TorusSite (fineSide ℓ.side e n)),
    maxCurvatureOnBall (topField ℓ (k + a) (fineSide ℓ.side e n) (wAt k a e n w)) o
        (ballRadius ℓ.side nn ρ₀ 0 + 1) ≤
      widenedStageMax (k + a) nn ρ₀ e n (castD hs n w) o := by
  intro e
  induction e with
  | zero =>
    intro n _ w hs o
    exact le_rfl
  | succ e ih =>
    intro n _ w hs o
    have hs' : k + (a + e) = k + a + e := Nat.succ.inj hs
    have hfst : (castD hs n w).1 = castD hs' (n * ℓ.side) w.1 := castD_fst hs' n w
    show _ ≤ max _ (widenedStageMax (k + a) nn ρ₀ e (n * ℓ.side) (castD hs n w).1 o)
    rw [hfst]
    exact (ih (n * ℓ.side) w.1 hs' o).trans (le_max_right _ _)
private theorem widenedSize_facts (T : StageTower ℓ) (C₁ c : ℝ) (hC₁ : 0 < C₁) (M t : ℕ) (nn ρ₀ : ℝ)
    (hρ : 0 ≤ ρ₀) (d n : ℕ) [NeZero n]
    (u : MarkedSample ℓ (t + d) n) (o : TorusSite (fineSide ℓ.side d n)) :
    0 ≤ widenedChainSize T C₁ c M t nn ρ₀ d n u o ∧ widenedChainSize T C₁ c M t nn ρ₀ d n u o ≤ 1 ∧
      (widenedChainSize T C₁ c M t nn ρ₀ d n u o < 1 →
        widenedStageMax t nn ρ₀ d n u o ≤ widenedChainSize T C₁ c M t nn ρ₀ d n u o / C₁) := by
  have h1 : 0 ≤ ρ₀ * maxCurvatureOnBall (topField ℓ (t + d) n u) (siteAbove ℓ.side d n o)
      (ballRadius ℓ.side nn ρ₀ d + 1) :=
    mul_nonneg hρ (finsetSupNonneg_nonneg _ _)
  have h2 := widenedStageSum_nonneg T t nn ρ₀ d n u o
  have h3 : 0 ≤ widenedStageMax t nn ρ₀ d n u o := by
    clear h1 h2
    induction d with
    | zero => exact finsetSupNonneg_nonneg _ _
    | succ d ih => exact (finsetSupNonneg_nonneg _ _).trans (le_max_left _ _)
  have h4 : (0 : ℝ) ≤ (M : ℝ) * Real.exp (-(c * ρ₀)) := by positivity
  unfold widenedChainSize
  refine ⟨le_min zero_le_one (by positivity), min_le_left _ _, fun h => ?_⟩
  have h5 := (min_lt_iff.1 h).resolve_left (lt_irrefl 1)
  rw [min_eq_right h5.le, le_div_iff₀ hC₁]
  nlinarith
private theorem nearBall_le_of (n : ℕ) [NeZero n] (g : TorusSite n → UnitQuaternion) (V : TorusField n)
    (o : TorusSite n) (r A : ℝ) (hA : 0 ≤ A)
    (h1 : ∀ b : TorusBond n, b.1 ∈ supBall o r → ‖(minimalLog (gaugeTransform g V b) : ℍ[ℝ])‖ ≤ A)
    (h2 : maxCurvatureOnBall V o r ≤ A) : nearBall g V o r ≤ A :=
  max_le (finsetSupNonneg_le _ _ hA fun b hb => h1 b (Finset.mem_filter.1 hb).2) h2
private theorem le_of_rat_gt {A w : ℝ} (hw : w < 1) (h : ∀ q : ℚ, w < q → (q : ℝ) < 1 → A ≤ q) : A ≤ w := by
  by_contra hc
  rw [not_le] at hc
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (lt_min hc hw)
  have h3 := h q h1 (lt_of_lt_of_le h2 (min_le_right _ _))
  have h4 : (q : ℝ) < A := lt_of_lt_of_le h2 (min_le_left _ _)
  linarith
end TheSizes
section SizeMoment
variable (Tb : ParameterAssignment) (y : ℝ)
open scoped Quaternion
private theorem chi_iff_local {ℓ : StepParameters} (T : StageTower ℓ) (k N a e : ℕ) [NeZero N] (m : ℝ)
    (o : TorusSite (fineSide ℓ.side (a + e) (fineSide ℓ.side (a + e) N)))
    (hh : k + (a + e) + (a + e) = k + a + e + (a + e)) (u : MarkedSample ℓ (k + (a + e) + (a + e)) N) :
    u ∈ chi T k N (a + e) m o a ↔
      IsLocalEventFrom T (k + a) e (a + e) m N (castD hh N u) (oAt a e (fineSide ℓ.side (a + e) N) o) := by
  have hs : k + (a + e) = k + a + e := by omega
  have e0 := siteAbove_oAt a e (fineSide ℓ.side (a + e) N) o
  have e1 := stageState_set_castD T hh N u
  have e2 := stepsMiss_castD T hs m (a + e) N u (siteAbove ℓ.side (a + e) (fineSide ℓ.side (a + e) N) o)
  have e3 := sampleBelow_castD hs (a + e) N u
  have e4 := stepsMiss_levels T k a m e (fineSide ℓ.side (a + e) N) (vOf k N (a + e) u) hs o
  unfold IsLocalEventFrom
  rw [e0, e1]
  have e2' : StepsAvoidOrigin T (k + a + e) m (a + e) N (castD hh N u)
      (siteAbove ℓ.side (a + e) (fineSide ℓ.side (a + e) N) o) ↔ StepsAvoidOrigin T (k + (a + e)) m (a + e) N u
      (siteAbove ℓ.side (a + e) (fineSide ℓ.side (a + e) N) o) := e2
  have e3' : sampleBelow ℓ (k + a + e) (a + e) N (castD hh N u) = castD hs _ (vOf k N (a + e) u) := e3
  rw [e2', e3', e4]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
private def SizeConditions (C₁ c : ℝ) (Q : ℕ) (Cq : ℝ) (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ)
    [NeZero N] (nn : ℝ) (t d d' : ℕ)
    (o : TorusSite (fineSide (Tb.stepParameters y).side d (fineSide (Tb.stepParameters y).side d' N))) : Prop :=
  (∀ s : ℝ, s < 1 → ∀ᵐ u ∂(markedSampleLaw T β (t + d + d') N),
    IsLocalEventFrom T t d d' (localBlockSide (Tb.stepParameters y) β k) N u o →
    widenedChainSize T C₁ c (localChainDepth (Tb.stepParameters y) β k) t
        (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k)) (localLogScale (Tb.stepParameters y) β k) d
        (fineSide (Tb.stepParameters y).side d' N)
        (sampleBelow (Tb.stepParameters y) (t + d) d' N u) o ≤ s →
    IsGaugeSmallAlong T t (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k)) (localLogScale (Tb.stepParameters y) β k)
      s d (fineSide (Tb.stepParameters y).side d' N)
      (sampleBelow (Tb.stepParameters y) (t + d) d' N u) o
      (axialGaugeAt (Tb.stepParameters y) (topField (Tb.stepParameters y) (t + d)
          (fineSide (Tb.stepParameters y).side d' N) (sampleBelow (Tb.stepParameters y) (t + d) d' N u))
        (siteAbove (Tb.stepParameters y).side d (fineSide (Tb.stepParameters y).side d' N) o))) ∧
  (Integrable (Set.indicator {u | IsLocalEventFrom T t d d' (localBlockSide (Tb.stepParameters y) β k) N u o}
      (fun u => widenedChainSize T C₁ c (localChainDepth (Tb.stepParameters y) β k) t
        (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k)) (localLogScale (Tb.stepParameters y) β k) d
        (fineSide (Tb.stepParameters y).side d' N) (sampleBelow (Tb.stepParameters y) (t + d) d' N u) o ^ Q))
      (markedSampleLaw T β (t + d + d') N) ∧
    ∫ u, Set.indicator {u | IsLocalEventFrom T t d d' (localBlockSide (Tb.stepParameters y) β k) N u o}
      (fun u => widenedChainSize T C₁ c (localChainDepth (Tb.stepParameters y) β k) t
        (nn / ((Tb.stepParameters y).side : ℝ) ^ (t - k)) (localLogScale (Tb.stepParameters y) β k) d
        (fineSide (Tb.stepParameters y).side d' N) (sampleBelow (Tb.stepParameters y) (t + d) d' N u) o ^ Q) u
      ∂(markedSampleLaw T β (t + d + d') N) ≤
    (Cq * flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ) + 2 / 1000)) ^ Q)
private theorem near_le {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k N : ℕ} [NeZero N] {nn : ℝ} {a e Q : ℕ}
    (C₁ c Cq : ℝ) (hC₁ : 0 < C₁)
    (o : TorusSite (fineSide (Tb.stepParameters y).side (a + e) (fineSide (Tb.stepParameters y).side (a + e) N)))
    (hρ : 0 ≤ localLogScale (Tb.stepParameters y) β k)
    (hz : SizeConditions Tb y C₁ c Q Cq T β k N nn (k + a) e (a + e) (oAt a e _ o))
    (hh : k + (a + e) + (a + e) = k + a + e + (a + e)) :
    ∀ᵐ u ∂(markedSampleLaw T β (k + (a + e) + (a + e)) N),
      u ∈ chi T k N (a + e) (localBlockSide (Tb.stepParameters y) β k : ℝ) o a →
      sFam k N (a + e) nn (localLogScale (Tb.stepParameters y) β k) o a u ≤ (4 + 1 / C₁) *
        widenedChainSize T C₁ c (localChainDepth (Tb.stepParameters y) β k) (k + a)
          (nn / ((Tb.stepParameters y).side : ℝ) ^ (k + a - k)) (localLogScale (Tb.stepParameters y) β k) e
          (fineSide (Tb.stepParameters y).side (a + e) N)
          (sampleBelow (Tb.stepParameters y) (k + a + e) (a + e) N (castD hh N u)) (oAt a e _ o) := by
  have hs : k + (a + e) = k + a + e := by omega
  have hall : ∀ᵐ v ∂(markedSampleLaw T β (k + a + e + (a + e)) N), ∀ q : ℚ, (q : ℝ) < 1 →
      IsLocalEventFrom T (k + a) e (a + e) (localBlockSide (Tb.stepParameters y) β k) N v (oAt a e _ o) →
      widenedChainSize T C₁ c (localChainDepth (Tb.stepParameters y) β k) (k + a)
        (nn / ((Tb.stepParameters y).side : ℝ) ^ (k + a - k)) (localLogScale (Tb.stepParameters y) β k) e
        (fineSide (Tb.stepParameters y).side (a + e) N) (sampleBelow (Tb.stepParameters y) (k + a + e) (a + e) N v)
        (oAt a e _ o) ≤ q →
      IsGaugeSmallAlong T (k + a) (nn / ((Tb.stepParameters y).side : ℝ) ^ (k + a - k))
        (localLogScale (Tb.stepParameters y) β k) q e (fineSide (Tb.stepParameters y).side (a + e) N)
        (sampleBelow (Tb.stepParameters y) (k + a + e) (a + e) N v) (oAt a e _ o)
        (axialGaugeAt (Tb.stepParameters y) (topField (Tb.stepParameters y) (k + a + e)
            (fineSide (Tb.stepParameters y).side (a + e) N)
            (sampleBelow (Tb.stepParameters y) (k + a + e) (a + e) N v))
          (siteAbove (Tb.stepParameters y).side e (fineSide (Tb.stepParameters y).side (a + e) N) (oAt a e _ o))) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : (q : ℝ) < 1
    · filter_upwards [hz.1 q hq] with v hv _ using hv
    · exact Filter.Eventually.of_forall fun _ h => absurd h hq
  filter_upwards [ae_castD hh hall] with u hu hchi
  have hloc := (chi_iff_local T k N a e _ o hh u).1 hchi
  set w := widenedChainSize T C₁ c (localChainDepth (Tb.stepParameters y) β k) (k + a)
      (nn / ((Tb.stepParameters y).side : ℝ) ^ (k + a - k)) (localLogScale (Tb.stepParameters y) β k) e
      (fineSide (Tb.stepParameters y).side (a + e) N)
      (sampleBelow (Tb.stepParameters y) (k + a + e) (a + e) N (castD hh N u)) (oAt a e _ o) with hw
  obtain ⟨hw0, hw1, hw2⟩ := widenedSize_facts T C₁ c hC₁ (localChainDepth (Tb.stepParameters y) β k) (k + a)
    (nn / ((Tb.stepParameters y).side : ℝ) ^ (k + a - k))
    (localLogScale (Tb.stepParameters y) β k) hρ e (fineSide (Tb.stepParameters y).side (a + e) N)
    (sampleBelow (Tb.stepParameters y) (k + a + e) (a + e) N (castD hh N u)) (oAt a e _ o)
  rw [← hw] at hw0 hw1 hw2
  have hS₀ : 1 ≤ 4 + 1 / C₁ := by
    have : 0 < 1 / C₁ := by positivity
    linarith
  rw [sFam_eq]
  have hdb : sampleBelow (Tb.stepParameters y) (k + a + e) (a + e) N (castD hh N u) =
      castD hs _ (vOf k N (a + e) u) :=
    sampleBelow_castD hs (a + e) N u
  have hradius : ballRadius (Tb.stepParameters y).side (nn / ((Tb.stepParameters y).side : ℝ) ^ (k + a - k))
        (localLogScale (Tb.stepParameters y) β k) 0 =
      ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) a := by
    unfold ballRadius
    rw [Nat.add_sub_cancel_left]
    simp
    ring
  by_cases h1 : w < 1
  · have hlogs : ∀ b : TorusBond (fineSide (Tb.stepParameters y).side e
          (fineSide (Tb.stepParameters y).side (a + e) N)),
        b.1 ∈ supBall (oAt a e _ o) (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) a) →
        ‖(minimalLog (gaugeTransform (gAt k a e _ (vOf k N (a + e) u) (gOf k N (a + e) o u))
          (topField (Tb.stepParameters y) (k + a) _ (wAt k a e _ (vOf k N (a + e) u))) b) : ℍ[ℝ])‖ ≤ w := by
      intro b hb
      refine le_of_rat_gt h1 fun q h2 h3 => ?_
      have h4 := hu q h3 hloc h2.le
      rw [hdb, topField_castD hs, siteAbove_oAt a e] at h4
      rw [← hradius] at hb
      exact small_bottom T k a _ _ _ e _ _ hs _ _ h4 b hb
    have hcurv : maxCurvatureOnBall (topField (Tb.stepParameters y) (k + a) _ (wAt k a e _ (vOf k N (a + e) u)))
        (oAt a e _ o) (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) a) ≤
          w / C₁ := by
      have h5 := widenedStageMax_bottom k a (nn / ((Tb.stepParameters y).side : ℝ) ^ (k + a - k))
        (localLogScale (Tb.stepParameters y) β k) e _ (vOf k N (a + e) u) hs (oAt a e _ o)
      rw [← hdb] at h5
      have h6 := hw2 h1
      have h7 := maxCurvatureOnBall_mono (topField (Tb.stepParameters y) (k + a) _ (wAt k a e _ (vOf k N (a + e) u)))
        (oAt a e _ o)
        (show ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) a ≤
            ballRadius (Tb.stepParameters y).side (nn / ((Tb.stepParameters y).side : ℝ) ^ (k + a - k))
              (localLogScale (Tb.stepParameters y) β k) 0 + 1 by
          rw [hradius]; linarith)
      linarith
    refine nearBall_le_of _ _ _ _ _ _ (by positivity) (fun b hb => (hlogs b hb).trans ?_) (hcurv.trans ?_)
    · nlinarith
    · have : w / C₁ = (1 / C₁) * w := by ring
      rw [this]
      have h8 : 0 ≤ 4 * w := by positivity
      nlinarith
  · have hw' : w = 1 := le_antisymm hw1 (not_lt.1 h1)
    rw [hw', mul_one]
    have h9 := nearBall_le (gAt k a e _ (vOf k N (a + e) u) (gOf k N (a + e) o u))
      (topField (Tb.stepParameters y) (k + a) _ (wAt k a e _ (vOf k N (a + e) u))) (oAt a e _ o)
      (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) a)
    have : 0 < 1 / C₁ := by positivity
    exact h9.trans (by linarith)
end SizeMoment
section Fields
variable (Tb : ParameterAssignment) (y : ℝ)
open scoped Quaternion
private theorem s_moment {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k N : ℕ} [NeZero N] {nn : ℝ}
    {a e Q : ℕ} (C₁ c Cq : ℝ) (hC₁ : 0 < C₁)
    (cB : ChainInputs Tb y T β k N nn (a + e) (localLogScale (Tb.stepParameters y) β k)
      (localBlockSide (Tb.stepParameters y) β k : ℝ))
    (o : TorusSite (fineSide (Tb.stepParameters y).side (a + e) (fineSide (Tb.stepParameters y).side (a + e) N)))
    (hρ : 0 ≤ localLogScale (Tb.stepParameters y) β k)
    (hz : SizeConditions Tb y C₁ c Q Cq T β k N nn (k + a) e (a + e) (oAt a e _ o)) :
    ∫ ω, (chi T k N (a + e) (localBlockSide (Tb.stepParameters y) β k : ℝ) o a).indicator
        (fun ω => sFam k N (a + e) nn (localLogScale (Tb.stepParameters y) β k) o a ω ^ Q) ω
        ∂(markedSampleLaw T β (k + (a + e) + (a + e)) N) ≤
      (4 + 1 / C₁) ^ Q * (Cq * flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ) + 2 / 1000)) ^ Q := by
  have hh : k + (a + e) + (a + e) = k + a + e + (a + e) := by omega
  have hprob := cB.prob (k + (a + e) + (a + e)) N
  have hle := near_le Tb y C₁ c Cq hC₁ o hρ hz hh
  set A := chi T k N (a + e) (localBlockSide (Tb.stepParameters y) β k : ℝ) o a with hA
  have hAm := ChainInputs.chi_meas Tb y cB o a
  set s := sFam k N (a + e) nn (localLogScale (Tb.stepParameters y) β k) o a with hs
  set f : MarkedSample (Tb.stepParameters y) (k + (a + e) + (a + e)) N → ℝ := fun u =>
    widenedChainSize T C₁ c (localChainDepth (Tb.stepParameters y) β k) (k + a)
      (nn / ((Tb.stepParameters y).side : ℝ) ^ (k + a - k)) (localLogScale (Tb.stepParameters y) β k) e
      (fineSide (Tb.stepParameters y).side (a + e) N)
      (sampleBelow (Tb.stepParameters y) (k + a + e) (a + e) N (castD hh N u)) (oAt a e _ o) with hf
  have hpt : ∀ u, A.indicator (fun u => f u ^ Q) u =
      (Set.indicator {v | IsLocalEventFrom T (k + a) e (a + e) (localBlockSide (Tb.stepParameters y) β k) N v
          (oAt a e _ o)}
        (fun v => widenedChainSize T C₁ c (localChainDepth (Tb.stepParameters y) β k) (k + a)
          (nn / ((Tb.stepParameters y).side : ℝ) ^ (k + a - k)) (localLogScale (Tb.stepParameters y) β k) e
          (fineSide (Tb.stepParameters y).side (a + e) N)
          (sampleBelow (Tb.stepParameters y) (k + a + e) (a + e) N v) (oAt a e _ o) ^ Q)) (castD hh N u) := by
    intro u
    by_cases h1 : u ∈ A
    · have h2 := (chi_iff_local T k N a e _ o hh u).1 h1
      have hm : castD hh N u ∈ {v | IsLocalEventFrom T (k + a) e (a + e) (localBlockSide (Tb.stepParameters y) β k)
          N v (oAt a e _ o)} := h2
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem hm]
    · have h2 : ¬ IsLocalEventFrom T (k + a) e (a + e) (localBlockSide (Tb.stepParameters y) β k) N (castD hh N u)
          (oAt a e _ o) :=
        fun h => h1 ((chi_iff_local T k N a e _ o hh u).2 h)
      have hm : castD hh N u ∉ {v | IsLocalEventFrom T (k + a) e (a + e) (localBlockSide (Tb.stepParameters y) β k)
          N v (oAt a e _ o)} := h2
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem hm]
  have hint : Integrable (A.indicator fun u => f u ^ Q) (markedSampleLaw T β (k + (a + e) + (a + e)) N) := by
    have := integrable_castD hh hz.2.1
    exact this.congr (Filter.Eventually.of_forall fun u => (hpt u).symm)
  have hval : ∫ u, A.indicator (fun u => f u ^ Q) u ∂(markedSampleLaw T β (k + (a + e) + (a + e)) N) ≤
      (Cq * flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ) + 2 / 1000)) ^ Q := by
    have e1 : ∫ u, A.indicator (fun u => f u ^ Q) u ∂(markedSampleLaw T β (k + (a + e) + (a + e)) N) = _ :=
      (integral_congr_ae (Filter.Eventually.of_forall hpt)).trans (integral_castD hh _)
    rw [e1]
    exact hz.2.2
  have hsI : Integrable (A.indicator fun ω => s ω ^ Q) (markedSampleLaw T β (k + (a + e) + (a + e)) N) := by
    refine Integrable.of_bound (((ChainInputs.s_meas Tb y cB o a).pow_const Q).indicator hAm).aestronglyMeasurable
      ((4 : ℝ) ^ Q) (Filter.Eventually.of_forall fun u => ?_)
    by_cases h1 : u ∈ A
    · rw [Set.indicator_of_mem h1, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sFam_nonneg _ _ _ _ _ _ _ _) Q)]
      exact pow_le_pow_left₀ (sFam_nonneg _ _ _ _ _ _ _ _) (sFam_le _ _ _ _ _ _ _ _) Q
    · rw [Set.indicator_of_notMem h1]
      simp
  calc ∫ ω, A.indicator (fun ω => s ω ^ Q) ω ∂(markedSampleLaw T β (k + (a + e) + (a + e)) N)
      ≤ ∫ ω, (4 + 1 / C₁) ^ Q * A.indicator (fun u => f u ^ Q) ω
          ∂(markedSampleLaw T β (k + (a + e) + (a + e)) N) := by
        refine integral_mono_ae hsI (hint.const_mul _) ?_
        filter_upwards [hle] with u hu
        by_cases h1 : u ∈ A
        · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1, ← mul_pow]
          exact pow_le_pow_left₀ (sFam_nonneg _ _ _ _ _ _ _ _) (hu h1) Q
        · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1, mul_zero]
    _ = (4 + 1 / C₁) ^ Q * ∫ ω, A.indicator (fun u => f u ^ Q) ω
          ∂(markedSampleLaw T β (k + (a + e) + (a + e)) N) :=
        integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hval (by positivity)
private theorem stage_anchorRadius (T : StageTower (Tb.stepParameters y)) :
    ∀ j, (T.stage j).anchorRadius = T.base.anchorRadius
  | 0 => rfl
  | j + 1 => by
    show ((T.stage j).next _ _ _ _).anchorRadius = _
    exact stage_anchorRadius T j
private theorem couplings_near (β : ℝ) (k d : ℕ) (hrun : FlowHasExpansionAt (Tb.stepParameters y) β)
    (hy : ∀ j ≤ k + d, (Tb.stepParameters y).y₁ ≤ flowCouplings (Tb.stepParameters y) β j) :
    |flowCouplings (Tb.stepParameters y) β (k + d) - flowCouplings (Tb.stepParameters y) β k| ≤
      2 * |(Tb.stepParameters y).B| * d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := ih fun j hj => hy j (by omega)
    have h2 : |flowCouplings (Tb.stepParameters y) β (k + d + 1) - flowCouplings (Tb.stepParameters y) β (k + d)| ≤
        2 * (Tb.stepParameters y).B :=
      (hrun (k + d)).2 fun j hj => hy j (by omega)
    have h3 := abs_sub_le (flowCouplings (Tb.stepParameters y) β (k + d + 1))
      (flowCouplings (Tb.stepParameters y) β (k + d)) (flowCouplings (Tb.stepParameters y) β k)
    have h4 : (Tb.stepParameters y).B ≤ |(Tb.stepParameters y).B| := le_abs_self _
    show |flowCouplings (Tb.stepParameters y) β (k + d + 1) - flowCouplings (Tb.stepParameters y) β k| ≤ _
    push_cast
    nlinarith
end Fields
section Assembly
variable (Tb : ParameterAssignment) (y : ℝ)
open scoped Quaternion
private theorem side_le (N d : ℕ) : N ≤ fineSide (Tb.stepParameters y).side d N := by
  have hpos : 0 < (Tb.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne (Tb.stepParameters y).side)
  rw [fineSide_eq]
  exact Nat.le_mul_of_pos_right N (pow_pos hpos _)
private theorem side_dvd {N : ℕ} (h : (Tb.stepParameters y).side ∣ N) (d : ℕ) :
    (Tb.stepParameters y).side ∣ fineSide (Tb.stepParameters y).side d N := by
  rw [fineSide_eq]
  exact h.mul_right _
private theorem gam_le {k N : ℕ} [NeZero N] {M q : ℕ} (ρA C₇ : ℝ)
    (p : Fin q → TorusPlaquette (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (ec : Fin q → Fin 3)
    (hp : ∀ i, p i ∈ plaquettesIn Finset.univ)
    (hRow : ∀ (d n : ℕ) [NeZero n], (Tb.stepParameters y).n₀ ≤ n →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (Tb.stepParameters y).side d n))),
      ∑ b, |adjointTransport (Tb.stepParameters y).coupling ρA (Tb.stepParameters y).side k d n (curlFunctional p) b| ≤
        4 * (1 / 2 : ℝ) ^ d)
    (hcov : ∀ (u n : ℕ) [NeZero n] (h h' : TorusBond (n * (Tb.stepParameters y).side) → ℝ),
      (Tb.stepParameters y).n₀ ≤ n → (Tb.stepParameters y).side ∣ n →
      |stepCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side u n h h'| ≤
        C₇ * (∑ b, |h b|) * ∑ b, |h' b|)
    (hN : (Tb.stepParameters y).n₀ ≤ N) (hLN : (Tb.stepParameters y).side ∣ N) {u : ℕ} (hu : u < M) (i i' : Fin q) :
    |gFam Tb y k N M ρA p ec u i i'| ≤ 16 * |C₇| * (1 / 4 : ℝ) ^ u := by
  obtain ⟨e, rfl⟩ : ∃ e, M = u + 1 + e := ⟨M - (u + 1), by omega⟩
  have hp4 : (0 : ℝ) ≤ 16 * |C₇| * (1 / 4 : ℝ) ^ u := by positivity
  unfold gFam
  split_ifs
  · rw [levelCov_eq]
    have hn : (Tb.stepParameters y).n₀ ≤ (fineSide (Tb.stepParameters y).side (u + 1 + e) N) :=
      hN.trans (side_le Tb y N _)
    have r1 := lAt_expansion k ρA u (Tb.stepParameters y).n₀ _ (hRow u) e
      (fineSide (Tb.stepParameters y).side (u + 1 + e) N) hn (p i) (hp i)
    have r2 := lAt_expansion k ρA u (Tb.stepParameters y).n₀ _ (hRow u) e
      (fineSide (Tb.stepParameters y).side (u + 1 + e) N) hn (p i') (hp i')
    have h1 := hcov (k + u) (fineSide (Tb.stepParameters y).side e (fineSide (Tb.stepParameters y).side (u + 1 + e) N))
      (lAt k ρA u e (fineSide (Tb.stepParameters y).side (u + 1 + e) N) (p i))
      (lAt k ρA u e (fineSide (Tb.stepParameters y).side (u + 1 + e) N) (p i'))
      (hn.trans (side_le Tb y _ _)) (side_dvd Tb y (side_dvd Tb y hLN _) _)
    have h0 : ∀ (g : TorusBond (fineSide (Tb.stepParameters y).side e
        (fineSide (Tb.stepParameters y).side (u + 1 + e) N) * (Tb.stepParameters y).side) → ℝ),
        0 ≤ ∑ b, |g b| := fun g =>
      Finset.sum_nonneg fun b _ => abs_nonneg _
    have hq : (1 / 4 : ℝ) ^ u = (1 / 2 : ℝ) ^ u * (1 / 2 : ℝ) ^ u := by
      rw [← mul_pow]; norm_num
    calc _ ≤ C₇ * (∑ b, |lAt k ρA u e (fineSide (Tb.stepParameters y).side (u + 1 + e) N) (p i) b|) *
            ∑ b, |lAt k ρA u e (fineSide (Tb.stepParameters y).side (u + 1 + e) N) (p i') b| := h1
      _ ≤ |C₇| * (∑ b, |lAt k ρA u e (fineSide (Tb.stepParameters y).side (u + 1 + e) N) (p i) b|) *
            ∑ b, |lAt k ρA u e (fineSide (Tb.stepParameters y).side (u + 1 + e) N) (p i') b| := by
          apply mul_le_mul_of_nonneg_right _ (h0 _)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (h0 _)
      _ ≤ |C₇| * (4 * (1 / 2 : ℝ) ^ u) * (4 * (1 / 2 : ℝ) ^ u) :=
          mul_le_mul (mul_le_mul_of_nonneg_left r1 (abs_nonneg _)) r2 (h0 _) (by positivity)
      _ = 16 * |C₇| * (1 / 4 : ℝ) ^ u := by rw [hq]; ring
  · simpa using hp4
private theorem gamc_near {k N : ℕ} [NeZero N] {M q : ℕ} (nn ρ₀ ρA C₇ E : ℝ)
    (o : TorusSite (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (p : Fin q → TorusPlaquette (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (ec : Fin q → Fin 3)
    (hp : ∀ i, p i ∈ plaquettesIn Finset.univ ∧ (p i).1 ∈ supBall o (19 * nn))
    (hRow : ∀ (d n : ℕ) [NeZero n], (Tb.stepParameters y).n₀ ≤ n →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (Tb.stepParameters y).side d n))),
      ∑ b, |adjointTransport (Tb.stepParameters y).coupling ρA (Tb.stepParameters y).side k d n (curlFunctional p) b| ≤
        4 * (1 / 2 : ℝ) ^ d)
    (hFar : ∀ (d n : ℕ) [NeZero n], (Tb.stepParameters y).n₀ ≤ n → d < M →
      ∀ (o : TorusSite (fineSide (Tb.stepParameters y).side (d + 1) n)),
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (Tb.stepParameters y).side (d + 1) n))),
      p.1 ∈ supBall o (19 * nn) →
      ∑ b ∈ (Finset.univ : Finset (TorusBond (n * (Tb.stepParameters y).side))).filter
          (fun b => parentBlock (Tb.stepParameters y).side b.1 ∉ supBall
            (siteAbove (Tb.stepParameters y).side (d + 1) n o)
            (ballRadius (Tb.stepParameters y).side nn ρ₀ (d + 1) - 3 * ρ₀)),
        |adjointTransport (Tb.stepParameters y).coupling ρA (Tb.stepParameters y).side k d
          (n * (Tb.stepParameters y).side) (curlFunctional p) b| ≤ E)
    (hcov : ∀ (u n : ℕ) [NeZero n] (h h' : TorusBond (n * (Tb.stepParameters y).side) → ℝ),
      (Tb.stepParameters y).n₀ ≤ n → (Tb.stepParameters y).side ∣ n →
      |stepCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side u n h h'| ≤
        C₇ * (∑ b, |h b|) * ∑ b, |h' b|)
    (hN : (Tb.stepParameters y).n₀ ≤ N) (hLN : (Tb.stepParameters y).side ∣ N) {u : ℕ} (hu : u < M) (i i' : Fin q) :
    |gcFam Tb y k N M nn ρ₀ ρA o p ec u i i' - gFam Tb y k N M ρA p ec u i i'| ≤ 2 * |C₇| * 4 * E := by
  obtain ⟨e, rfl⟩ : ∃ e, M = u + 1 + e := ⟨M - (u + 1), by omega⟩
  have hn : (Tb.stepParameters y).n₀ ≤ (fineSide (Tb.stepParameters y).side (u + 1 + e) N) :=
    hN.trans (side_le Tb y N _)
  have hfar := lAt_far k nn ρ₀ ρA u (Tb.stepParameters y).n₀ E
    (fun n _ h o' p' hp' hb => hFar u n h (by omega) o' p' hp' hb)
  have f1 := hfar e (fineSide (Tb.stepParameters y).side (u + 1 + e) N) hn o (p i) (hp i).1 (hp i).2
  have f2 := hfar e (fineSide (Tb.stepParameters y).side (u + 1 + e) N) hn o (p i') (hp i').1 (hp i').2
  have hE : 0 ≤ E := (Finset.sum_nonneg fun b _ => abs_nonneg _).trans f1
  have hp4 : (0 : ℝ) ≤ 2 * |C₇| * 4 * E := by positivity
  unfold gcFam gFam
  split_ifs
  · rw [levelCov_eq, levelCovCut_eq]
    have hhalf : (1 / 2 : ℝ) ^ u ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have r1 := (lAt_expansion k ρA u (Tb.stepParameters y).n₀ _ (hRow u) e
      (fineSide (Tb.stepParameters y).side (u + 1 + e) N) hn (p i) (hp i).1).trans
        (show 4 * (1 / 2 : ℝ) ^ u ≤ 4 by linarith)
    have r2 := (lAt_expansion k ρA u (Tb.stepParameters y).n₀ _ (hRow u) e
      (fineSide (Tb.stepParameters y).side (u + 1 + e) N) hn (p i') (hp i').1).trans
        (show 4 * (1 / 2 : ℝ) ^ u ≤ 4 by linarith)
    refine cov_near (Tb.stepParameters y).coupling (Tb.stepParameters y).side (k + u)
      (fineSide (Tb.stepParameters y).side e (fineSide (Tb.stepParameters y).side (u + 1 + e) N)) |C₇| (abs_nonneg _)
      4 E (by norm_num) ?_ _ _ _ _ r1 ((cut_sum_abs_le _ _).trans r2) f1 f2
    intro h h'
    refine (hcov (k + u) (fineSide (Tb.stepParameters y).side e (fineSide (Tb.stepParameters y).side (u + 1 + e) N))
      h h' (hn.trans (side_le Tb y _ _)) (side_dvd Tb y (side_dvd Tb y hLN _) _)).trans ?_
    have h0 : ∀ (g : TorusBond (fineSide (Tb.stepParameters y).side e
        (fineSide (Tb.stepParameters y).side (u + 1 + e) N) * (Tb.stepParameters y).side) → ℝ),
        0 ≤ ∑ b, |g b| := fun g =>
      Finset.sum_nonneg fun b _ => abs_nonneg _
    apply mul_le_mul_of_nonneg_right _ (h0 _)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (h0 _)
  · simpa using hp4
private theorem zeta_le {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k N : ℕ} [NeZero N] {nn : ℝ} {M q : ℕ}
    (ρ₀ ρA m : ℝ)
    (hσ : 0 ≤ (Tb.stepParameters y).threshold)
    (o : TorusSite (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (p : Fin q → TorusPlaquette (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (ec : Fin q → Fin 3)
    (hp : ∀ i, p i ∈ plaquettesIn Finset.univ)
    (hRow : ∀ (d n : ℕ) [NeZero n], (Tb.stepParameters y).n₀ ≤ n →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (Tb.stepParameters y).side d n))),
      ∑ b, |adjointTransport (Tb.stepParameters y).coupling ρA (Tb.stepParameters y).side k d n (curlFunctional p) b| ≤
        4 * (1 / 2 : ℝ) ^ d)
    (hN : (Tb.stepParameters y).n₀ ≤ N)
    (hR : ∀ d, ballRadius (Tb.stepParameters y).side nn ρ₀ (d + 1) - 3 * ρ₀ ≤ m) {u : ℕ} (hu : u < M) (i : Fin q)
    (ω : MarkedSample (Tb.stepParameters y) (k + M + M) N) (hG : Good T k N M m ω) (hω : ω ∈ chi T k N M m o u) :
    |zFam Tb y T k N M nn ρ₀ ρA o p ec u i ω| ≤ 4 * (1 / 2 : ℝ) ^ u * ((Tb.stepParameters y).threshold / 64) := by
  obtain ⟨e, rfl⟩ : ∃ e, M = u + 1 + e := ⟨M - (u + 1), by omega⟩
  have hn : (Tb.stepParameters y).n₀ ≤ fineSide (Tb.stepParameters y).side (u + 1 + e) N :=
    hN.trans (side_le Tb y N _)
  unfold zFam
  rw [zeta_eq]
  refine (term_le T (k + u) _ _ _ _ _ (ec i) ((Tb.stepParameters y).threshold / 64) (by positivity) ?_).trans ?_
  · intro b hb
    have hb' := Finset.mem_filter.1 hb
    have hin : b ∈ chartBondsInBlocks (Tb.stepParameters y).side (supBall (oAt (u + 1) e _ o) m) := by
      refine Finset.mem_filter.2 ⟨hb'.1, ?_⟩
      have h2 := Finset.mem_filter.1 hb'.2
      exact Finset.mem_filter.2 ⟨h2.1, h2.2.trans (hR u)⟩
    exact (chi_eta T k N u e m o ω hω hG b hin).le
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (cut_sum_abs_le _ _).trans (lAt_expansion k ρA u (Tb.stepParameters y).n₀ _ (hRow u) e _ hn (p i) (hp i))
private theorem top_le {k N : ℕ} [NeZero N] {M q : ℕ} (nn ρ₀ ρA s₀ : ℝ)
    (o : TorusSite (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (p : Fin q → TorusPlaquette (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (ec : Fin q → Fin 3)
    (hp : ∀ i, p i ∈ plaquettesIn Finset.univ)
    (hRow : ∀ (d n : ℕ) [NeZero n], (Tb.stepParameters y).n₀ ≤ n →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (Tb.stepParameters y).side d n))),
      ∑ b, |adjointTransport (Tb.stepParameters y).coupling ρA (Tb.stepParameters y).side k d n (curlFunctional p) b| ≤
        4 * (1 / 2 : ℝ) ^ d)
    (hN : (Tb.stepParameters y).n₀ ≤ N) (i : Fin q) (ω : MarkedSample (Tb.stepParameters y) (k + M + M) N) :
    |tFam Tb y k N M nn ρ₀ ρA s₀ o p ec i ω| ≤ 4 * (1 / 2 : ℝ) ^ M * 4 := by
  unfold tFam topOf
  rw [imaginaryComponent_sum]
  have hb : ∀ b : TorusBond (fineSide (Tb.stepParameters y).side M N),
      |imaginaryComponent (ec i) (adjointTransport (Tb.stepParameters y).coupling ρA (Tb.stepParameters y).side k M
          (fineSide (Tb.stepParameters y).side M N) (curlFunctional (p i)) b •
        topLogForm (Tb.stepParameters y) (topField (Tb.stepParameters y) (k + M) (fineSide (Tb.stepParameters y).side M N)
            (vOf k N M ω))
          (siteAbove (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N) o)
          (ballRadius (Tb.stepParameters y).side nn ρ₀ M) s₀ b)| ≤
      |adjointTransport (Tb.stepParameters y).coupling ρA (Tb.stepParameters y).side k M
        (fineSide (Tb.stepParameters y).side M N) (curlFunctional (p i)) b| * 4 := by
    intro b
    rw [imaginaryComponent_smul, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (abs_imaginaryComponent_le _ _).trans ?_
    unfold topLogForm
    split_ifs
    · exact (GaugeFixing.norm_minimalLog_le_pi _).trans Real.pi_le_four
    · simp
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun b _ => hb b).trans ?_)
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hRow M _ (hN.trans (side_le Tb y N _)) _ (hp i)) (by norm_num)
end Assembly
section Data
variable (Tb : ParameterAssignment) (y : ℝ)
open scoped Quaternion
private theorem sq_rpow_half {x : ℝ} (hx : 0 < x) : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by apply _root_.YangMills.Construction.WeightedResponses.GradientMoves.rpow_neg_half_sq <;> assumption
private theorem scales {β : ℝ} {k M : ℕ} (hx : 1 ≤ flowCouplings (Tb.stepParameters y) β k)
    (hrun : FlowHasExpansionAt (Tb.stepParameters y) β)
    (hy : ∀ j ≤ k + M, (Tb.stepParameters y).y₁ ≤ flowCouplings (Tb.stepParameters y) β j)
    (hB : 2 * |(Tb.stepParameters y).B| * (M : ℝ) ≤ 3 / 4 * flowCouplings (Tb.stepParameters y) β k)
    {u : ℕ} (hu : u < M) :
    0 < flowCouplings (Tb.stepParameters y) β (k + u) ∧
      flowCouplings (Tb.stepParameters y) β (k + u) ^ (-(1 / 2 : ℝ)) ≤
        2 * flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ)) ∧
      |(flowCouplings (Tb.stepParameters y) β (k + u) ^ (-(1 / 2 : ℝ))) ^ 2 -
          (flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ))) ^ 2| ≤
        8 * |(Tb.stepParameters y).B| * (u : ℝ) * (flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ))) ^ 4 := by
  set x := flowCouplings (Tb.stepParameters y) β k with hxd
  set xu := flowCouplings (Tb.stepParameters y) β (k + u) with hxu
  have hx0 : 0 < x := by linarith
  have h1 : |xu - x| ≤ 2 * |(Tb.stepParameters y).B| * u := couplings_near Tb y β k u hrun fun j hj => hy j (by omega)
  have h2 : 2 * |(Tb.stepParameters y).B| * (u : ℝ) ≤ 2 * |(Tb.stepParameters y).B| * (M : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hu.le) (by positivity)
  have h3 : x / 4 ≤ xu := by
    have := (abs_le.1 h1).1
    linarith
  have hxu0 : 0 < xu := by linarith
  have e1 := sq_rpow_half hx0
  have e2 := sq_rpow_half hxu0
  refine ⟨hxu0, ?_, ?_⟩
  · have hb : (xu ^ (-(1 / 2 : ℝ))) ^ 2 ≤ (2 * x ^ (-(1 / 2 : ℝ))) ^ 2 := by
      rw [mul_pow, e1, e2]
      rw [inv_le_comm₀ hxu0 (by positivity)]
      have : (2 ^ 2 * x⁻¹)⁻¹ = x / 4 := by
        field_simp
        norm_num
      rw [this]
      exact h3
    exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hxu0.le _) (by positivity) (by norm_num)).1 hb
  · have e4 : (x ^ (-(1 / 2 : ℝ))) ^ 4 = x⁻¹ * x⁻¹ := by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, e1]
    rw [e1, e2, e4]
    have e5 : xu⁻¹ - x⁻¹ = (x - xu) * (xu⁻¹ * x⁻¹) := by
      field_simp
    rw [e5, abs_mul, abs_of_nonneg (show 0 ≤ xu⁻¹ * x⁻¹ by positivity), abs_sub_comm]
    have h4 : xu⁻¹ ≤ 4 * x⁻¹ := by
      rw [inv_le_comm₀ hxu0 (by positivity)]
      have : (4 * x⁻¹)⁻¹ = x / 4 := by
        field_simp
      rw [this]
      exact h3
    have h5 : 0 ≤ x⁻¹ := by positivity
    calc |xu - x| * (xu⁻¹ * x⁻¹) ≤ (2 * |(Tb.stepParameters y).B| * u) * (4 * x⁻¹ * x⁻¹) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_right h4 h5) (by positivity) (by positivity)
      _ = _ := by ring
private theorem gaussianChainData {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k N : ℕ} [NeZero N] {nn : ℝ}
    {M q : ℕ}
    (hM : M = localChainDepth (Tb.stepParameters y) β k)
    (cB : ChainInputs Tb y T β k N nn M (localLogScale (Tb.stepParameters y) β k)
      (localBlockSide (Tb.stepParameters y) β k : ℝ))
    (o : TorusSite (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (p : Fin q → TorusPlaquette (fineSide (Tb.stepParameters y).side M (fineSide (Tb.stepParameters y).side M N)))
    (ec : Fin q → Fin 3)
    (hp : ∀ i, p i ∈ plaquettesIn Finset.univ ∧ (p i).1 ∈ supBall o (19 * nn))
    (ρA s₀ K ε C₇ E C₁ c₃ Cq : ℝ) (Cf cf xf : ℕ → ℝ) (hσ : 0 ≤ (Tb.stepParameters y).threshold) (hC₁ : 0 < C₁)
    (hx : 1 ≤ flowCouplings (Tb.stepParameters y) β k) (hρ : 0 ≤ localLogScale (Tb.stepParameters y) β k)
    (hrun : FlowHasExpansionAt (Tb.stepParameters y) β)
    (hy : ∀ j ≤ k + 2 * M, (Tb.stepParameters y).y₁ ≤ flowCouplings (Tb.stepParameters y) β j)
    (hB2 : 2 * |(Tb.stepParameters y).B| * (M : ℝ) ≤ 3 / 4 * flowCouplings (Tb.stepParameters y) β k)
    (hRow : ∀ (d n : ℕ) [NeZero n], (Tb.stepParameters y).n₀ ≤ n →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (Tb.stepParameters y).side d n))),
      ∑ b, |adjointTransport (Tb.stepParameters y).coupling ρA (Tb.stepParameters y).side k d n (curlFunctional p) b| ≤
        4 * (1 / 2 : ℝ) ^ d)
    (hFar : ∀ (d n : ℕ) [NeZero n], (Tb.stepParameters y).n₀ ≤ n → d < M →
      ∀ (o : TorusSite (fineSide (Tb.stepParameters y).side (d + 1) n)),
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide (Tb.stepParameters y).side (d + 1) n))),
      p.1 ∈ supBall o (19 * nn) →
      ∑ b ∈ (Finset.univ : Finset (TorusBond (n * (Tb.stepParameters y).side))).filter
          (fun b => parentBlock (Tb.stepParameters y).side b.1 ∉ supBall
            (siteAbove (Tb.stepParameters y).side (d + 1) n o)
            (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (d + 1) -
              3 * localLogScale (Tb.stepParameters y) β k)),
        |adjointTransport (Tb.stepParameters y).coupling ρA (Tb.stepParameters y).side k d
          (n * (Tb.stepParameters y).side) (curlFunctional p) b| ≤ E)
    (hcov : ∀ (u n : ℕ) [NeZero n] (h h' : TorusBond (n * (Tb.stepParameters y).side) → ℝ),
      (Tb.stepParameters y).n₀ ≤ n → (Tb.stepParameters y).side ∣ n →
      |stepCovariance (Tb.stepParameters y).coupling (Tb.stepParameters y).side u n h h'| ≤
        C₇ * (∑ b, |h b|) * ∑ b, |h' b|)
    (hN : (Tb.stepParameters y).n₀ ≤ N)
    (hR : ∀ d, ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (d + 1) -
      3 * localLogScale (Tb.stepParameters y) β k ≤ (localBlockSide (Tb.stepParameters y) β k : ℝ))
    (hLike : (markedSampleLaw T β (k + M + M) N).real
      (chi T k N M (localBlockSide (Tb.stepParameters y) β k : ℝ) o 0)ᶜ ≤ ε)
    (hK1 : 16 ≤ K) (hKC : 16 * |C₇| ≤ K) (hKσ : (Tb.stepParameters y).threshold ≤ K)
    (hKB : 8 * |(Tb.stepParameters y).B| ≤ K)
    (hKq : (4 + 1 / C₁) * |Cq| ≤ K) (hEε : 2 * |C₇| * 4 * E ≤ ε) (hε0 : 0 ≤ ε)
    (hsM : (1 / 2 : ℝ) ^ M ≤ (flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ))) ^ (4 * q + 4))
    (hsε : ε * ((M : ℝ) + 1) * 4 ^ M ≤ (flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ))) ^ (4 * q + 4))
    (hSz : ∀ (t d d' : ℕ) (o' : TorusSite (fineSide (Tb.stepParameters y).side d
        (fineSide (Tb.stepParameters y).side d' N))),
      k ≤ t → t + d = k + localChainDepth (Tb.stepParameters y) β k →
      d' = localChainDepth (Tb.stepParameters y) β k → SizeConditions Tb y C₁ c₃ (2 * q + 2) Cq T β k N nn t d d' o')
    (hr : ∀ r, 1 ≤ r → r ≤ 2 * q + 2 → ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N]
      (nn : ℝ) (j d' : ℕ)
      (o : TorusSite (fineSide (Tb.stepParameters y).side d' N))
      (g : MarkedSample (Tb.stepParameters y) (k + j + 1 + d') N →
        TorusSite (fineSide (Tb.stepParameters y).side d' N) → UnitQuaternion)
      (s : MarkedSample (Tb.stepParameters y) (k + j + 1 + d') N → ℝ)
      (l : Fin r → TorusBond (fineSide (Tb.stepParameters y).side d' N * (Tb.stepParameters y).side) → ℝ)
      (e : Fin r → Fin 3),
      IsLocalChainAbove Tb y T β k (fineSide (Tb.stepParameters y).side d' N) nn (xf r) →
      (Tb.stepParameters y).side ∣ fineSide (Tb.stepParameters y).side d' N →
      j < localChainDepth (Tb.stepParameters y) β k →
      j + 1 + d' ≤ 2 * localChainDepth (Tb.stepParameters y) β k →
      Measurable[upperSigma T (k + j + 1) d' N] g → Measurable[upperSigma T (k + j + 1) d' N] s → (∀ u, 0 ≤ s u) →
      (∀ i, ∑ b, |l i b| ≤ 4 * (1 / 2 : ℝ) ^ j) →
      (∀ i b, parentBlock (Tb.stepParameters y).side b.1 ∉ supBall o
          (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
            3 * localLogScale (Tb.stepParameters y) β k) →
        l i b = 0) →
      StepLaw Tb y T β k N nn j r (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N)
        (upperSigma T (k + j + 1) d' N) o g s l e (Cf r) (cf r))
    (hlocF : ∀ r, 1 ≤ r → r ≤ 2 * q + 2 → ∀ n, N ≤ n → IsLocalChainAbove Tb y T β k n nn (xf r))
    (hCK : ∀ r, 1 ≤ r → r ≤ 2 * q + 2 → Cf r ≤ K)
    (hεr : ∀ r, 1 ≤ r → r ≤ 2 * q + 2 → Real.exp (-(cf r * localLogScale (Tb.stepParameters y) β k)) ≤ ε) :
    IsGaussianChain (markedSampleLaw T β (k + M + M) N) K (flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ)))
      (flowCouplings (Tb.stepParameters y) β k ^ (2 / 1000 : ℝ)) ε M
      (chi T k N M (localBlockSide (Tb.stepParameters y) β k : ℝ) o)
      (fun u => flowCouplings (Tb.stepParameters y) β (k + u) ^ (-(1 / 2 : ℝ)))
      (gFam Tb y k N M ρA p ec) (gcFam Tb y k N M nn (localLogScale (Tb.stepParameters y) β k) ρA o p ec)
      (zFam Tb y T k N M nn (localLogScale (Tb.stepParameters y) β k) ρA o p ec)
      (tFam Tb y k N M nn (localLogScale (Tb.stepParameters y) β k) ρA s₀ o p ec)
      (sFam k N M nn (localLogScale (Tb.stepParameters y) β k) o) := by
  have hx0 : 0 < flowCouplings (Tb.stepParameters y) β k := by linarith
  have hX0 : 0 < flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hK0 : 0 ≤ K := by linarith
  have hGood := ChainInputs.good Tb y cB
  have hsc : ∀ {u : ℕ}, u < M → _ := fun {u} hu => scales Tb y hx hrun (fun j hj => hy j (by omega)) hB2 hu
  have hzle : ∀ u < M, ∀ i, ∀ᵐ ω ∂(markedSampleLaw T β (k + M + M) N),
      ω ∈ chi T k N M (localBlockSide (Tb.stepParameters y) β k : ℝ) o u →
        |zFam Tb y T k N M nn (localLogScale (Tb.stepParameters y) β k) ρA o p ec u i ω| ≤ K * (1 / 2 : ℝ) ^ u := by
    intro u hu i
    filter_upwards [hGood] with ω hG hω
    refine (zeta_le Tb y (β := β) _ ρA _ hσ o p ec (fun i => (hp i).1) hRow hN hR hu i ω hG hω).trans ?_
    have hp2 : (0 : ℝ) < (1 / 2 : ℝ) ^ u := by positivity
    have : 4 * ((Tb.stepParameters y).threshold / 64) ≤ K := by linarith
    nlinarith
  refine
    { isProbability := cB.prob _ _
      one_le_K := by linarith
      X_pos := hX0
      X_le_one := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
      one_le_Y := Real.one_le_rpow hx (by norm_num)
      ε_nonneg := hε0
      scale_nonneg := fun u hu => Real.rpow_nonneg (hsc hu).1.le _
      scale_le := fun u hu => (hsc hu).2.1
      scale_sq_near := fun u hu => ?_
      cov_le := fun u hu i i' => (gam_le Tb y ρA C₇ p ec (fun i => (hp i).1) hRow hcov hN cB.LN hu i i').trans
        (mul_le_mul_of_nonneg_right hKC (by positivity))
      stepCov_near := fun u hu i i' =>
        (gamc_near Tb y nn _ ρA C₇ E o p ec hp hRow hFar hcov hN cB.LN hu i i').trans hEε
      event_measurable := fun j => ChainInputs.chi_meas Tb y cB o j
      event_mono := fun j => chi_mono T k N M _ o (Nat.le_succ j)
      measure_compl_le := hLike
      var_aesm := fun u hu i => ChainInputs.zeta_meas Tb y cB ρA o (p i) (ec i) hu.le
      top_aesm := fun i => ((ChainInputs.top_meas Tb y cB ρA s₀ o (p i) (ec i)).indicator
        (ChainInputs.chi_meas Tb y cB o M)).aestronglyMeasurable
      var_le := hzle
      top_le := fun i => Filter.Eventually.of_forall fun ω _ =>
        (top_le Tb y nn _ ρA s₀ o p ec (fun i => (hp i).1) hRow hN i ω).trans ?_
      size_aesm := fun j _ =>
        ((ChainInputs.s_meas Tb y cB o j).indicator (ChainInputs.chi_meas Tb y cB o j)).aestronglyMeasurable
      size_nonneg := fun j ω => sFam_nonneg _ _ _ _ _ _ _ _
      size_le := fun j ω => (sFam_le _ _ _ _ _ _ _ _).trans (by linarith)
      size_moment := fun j hj => ?_
      small_depth := hsM
      small_error := hsε
      step_moment := fun j hj r hr1 hr2 f S => ?_ }
  · obtain ⟨-, -, h3⟩ := hsc hu
    refine h3.trans ?_
    have h4 : 0 ≤ (flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ))) ^ 4 := by positivity
    apply mul_le_mul_of_nonneg_right _ h4
    have h5 : (0 : ℝ) ≤ u := by positivity
    nlinarith [abs_nonneg (Tb.stepParameters y).B]
  · have hp2 : (0 : ℝ) < (1 / 2 : ℝ) ^ M := by positivity
    nlinarith
  · obtain ⟨e, rfl⟩ : ∃ e, M = j + e := ⟨M - j, by omega⟩
    have h1 := s_moment Tb y C₁ c₃ Cq hC₁ cB o hρ
      (hSz (k + j) e (j + e) (oAt j e _ o) (by omega) (by omega) hM)
    refine h1.trans ?_
    have hz : flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ) + 2 / 1000) =
        flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ)) *
          flowCouplings (Tb.stepParameters y) β k ^ (2 / 1000 : ℝ) := Real.rpow_add hx0 _ _
    rw [hz, ← mul_pow]
    set z := flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ)) *
      flowCouplings (Tb.stepParameters y) β k ^ (2 / 1000 : ℝ) with hzd
    have hz0 : 0 ≤ z := by positivity
    have hS0 : 0 < 4 + 1 / C₁ := by positivity
    have hev : Even (2 * q + 2) := ⟨q + 1, by omega⟩
    rw [← hev.pow_abs]
    have e2 : K * flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ)) *
        flowCouplings (Tb.stepParameters y) β k ^ (2 / 1000 : ℝ) = K * z := by rw [hzd]; ring
    rw [e2]
    apply pow_le_pow_left₀ (abs_nonneg _)
    rw [abs_mul, abs_mul, abs_of_pos hS0, abs_of_nonneg hz0, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hKq hz0
  · obtain ⟨e, rfl⟩ : ∃ e, M = j + 1 + e := ⟨M - (j + 1), by omega⟩
    have hn : (Tb.stepParameters y).n₀ ≤ fineSide (Tb.stepParameters y).side (j + 1 + e) N :=
      hN.trans (side_le Tb y N _)
    have hGb : ∀ᵐ u ∂(markedSampleLaw T β (k + (j + 1 + e) + (j + 1 + e)) N),
        u ∈ chi T k N (j + 1 + e) (localBlockSide (Tb.stepParameters y) β k : ℝ) o (j + 1) → ∀ i,
          |tailSum (j + 1 + e) (zFam Tb y T k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA o p ec)
            (tFam Tb y k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA s₀ o p ec) (j + 1) i u| ≤
            3 * K := by
      have H1 : ∀ᵐ ω ∂(markedSampleLaw T β (k + (j + 1 + e) + (j + 1 + e)) N), ∀ (u : ℕ) (i : Fin q),
          u < j + 1 + e →
          ω ∈ chi T k N (j + 1 + e) (localBlockSide (Tb.stepParameters y) β k : ℝ) o u →
            |zFam Tb y T k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA o p ec u i ω| ≤
              K * (1 / 2 : ℝ) ^ u := by
        rw [ae_all_iff]
        intro u
        rw [ae_all_iff]
        intro i
        by_cases hu : u < j + 1 + e
        · filter_upwards [hzle u hu i] with ω hω _ using hω
        · exact Filter.Eventually.of_forall fun _ h' => absurd h' hu
      filter_upwards [H1] with ω h1 hω i
      unfold tailSum
      have hs : ∑ u ∈ Finset.Ico (j + 1) (j + 1 + e),
          |zFam Tb y T k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA o p ec u i ω| ≤
          ∑ u ∈ Finset.Ico (j + 1) (j + 1 + e), K * (1 / 2 : ℝ) ^ u := by
        refine Finset.sum_le_sum fun u hu => ?_
        obtain ⟨a1, a2⟩ := Finset.mem_Ico.1 hu
        exact h1 u i a2 (chi_mono T k N _ _ o a1 hω)
      rw [← Finset.mul_sum] at hs
      have hgeo : ∑ u ∈ Finset.Ico (j + 1) (j + 1 + e), (1 / 2 : ℝ) ^ u ≤ 2 := by
        have h2 : ∑ u ∈ Finset.Ico (j + 1) (j + 1 + e), (1 / 2 : ℝ) ^ u ≤
            ∑ u ∈ Finset.range (j + 1 + e), (1 / 2 : ℝ) ^ u := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro u hu
            exact Finset.mem_range.2 (Finset.mem_Ico.1 hu).2
          · intro u _ _
            positivity
        exact h2.trans (sum_geometric_two_le _)
      have ht := top_le Tb y nn (localLogScale (Tb.stepParameters y) β k) ρA s₀ o p ec (fun i => (hp i).1) hRow hN i ω
      have hp1 : (1 / 2 : ℝ) ^ (j + 1 + e) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hz2 : K * ∑ u ∈ Finset.Ico (j + 1) (j + 1 + e), (1 / 2 : ℝ) ^ u ≤ K * 2 :=
        mul_le_mul_of_nonneg_left hgeo hK0
      calc _ ≤ ∑ u ∈ Finset.Ico (j + 1) (j + 1 + e),
              |zFam Tb y T k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA o p ec u i ω| +
            |tFam Tb y k N (j + 1 + e) nn (localLogScale (Tb.stepParameters y) β k) ρA s₀ o p ec i ω| :=
            (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl)
        _ ≤ 3 * K := by linarith
    exact stepMomentBound Tb y cB ρA s₀ K _ ε (3 * K) (Cf r) (cf r) (xf r) _ o p ec f S (hr r hr1 hr2)
      (hlocF r hr1 hr2 _ ((side_le Tb y N _).trans (side_le Tb y _ _))) hM
      (fun i => lAt_expansion k ρA j (Tb.stepParameters y).n₀ _ (hRow j) e _ hn (p i) (hp i).1) hGb (by positivity) hK0
      (hCK r hr1 hr2) (hεr r hr1 hr2) rfl (hsc hj).1.le rfl hx0
end Data
section Final
variable (Tb : ParameterAssignment) (y : ℝ)
private theorem gaussianChain_of_curvatureMoments (m1 : stepCurvatureMomentsAt Tb y) (m2 : transportedCurlFunctionalBoundsAt Tb y)
    (m3 : localChainSizeAt Tb y) (m4 : descentKeepsBallClearAt Tb y)
    (m5 : ∃ c x₀ : ℝ, 0 < c ∧ ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k e N : ℕ) [NeZero N] (nn : ℝ)
      (o : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))),
      N = 2 * (Tb.stepParameters y).side ^ e → IsLocalChainAbove Tb y T β k N nn x₀ →
      MeasureTheory.Measure.real (markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
          chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
        {u | ¬ IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
          (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o} ≤
        Real.exp (-(c * (couplingFlow (Tb.stepParameters y) β k).1)))
    (m6 : coldBallDeviationMeasurableAt Tb y) (m7 : stepCovarianceBoundedAt Tb y)
    (hfit : (Tb.stepParameters y).Admissible)
    (hJ : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side)
    (hrunAll : ∀ β, (Tb.stepParameters y).y₁ ≤ β → FlowHasExpansionAt (Tb.stepParameters y) β)
    (hSum : curvatureLevelSumStatement) (hC2 : upperSigmaDeterminesStatesStatement)
    (hC5 : chainMeasurabilityStatement) :
    ∀ q : ℕ, ∃ K x₀ : ℝ, ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ)
    (o : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
      (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)))
    (p : Fin q → TorusPlaquette (fineSide (Tb.stepParameters y).side
      (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
      (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)))
    (e : Fin q → Fin 3) (w : ℕ),
    N = 2 * (Tb.stepParameters y).side ^ (w + 1) → IsLocalChainAbove Tb y T β k N nn x₀ →
    (∀ j, p j ∈ plaquettesIn Finset.univ ∧ (p j).1 ∈ supBall o (19 * nn)) →
    ∃ (ε : ℝ) (A : ℕ → Set (MarkedSample (Tb.stepParameters y)
        (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
          chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))
      (Xs : ℕ → ℝ) (Gam Gamc : ℕ → Fin q → Fin q → ℝ)
      (ζ : ℕ → Fin q → MarkedSample (Tb.stepParameters y) (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N → ℝ)
      (top : Fin q → MarkedSample (Tb.stepParameters y) (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N → ℝ)
      (s : ℕ → MarkedSample (Tb.stepParameters y) (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N → ℝ),
      IsGaussianChain (markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
          chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
        K ((couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ)))
        ((couplingFlow (Tb.stepParameters y) β k).1 ^ (2 / 1000 : ℝ)) ε
        (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) A Xs Gam Gamc ζ top s ∧
      A 0 = {u | IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o} ∧
      (∀ u i, tailSum (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) ζ top 0 i u =
        imaginaryComponent (e i) (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) nn
          (couplingFlow (Tb.stepParameters y) β k).1 N u o (p i))) ∧
      ∀ i i', ∑ u ∈ Finset.range (chainDepth (couplingFlow (Tb.stepParameters y) β k).1), Gam u i i' =
        if e i = e i' then accumulatedCovariance Tb.coupling Tb.ρA (Tb.stepParameters y).side k
          (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
          (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
          (curlFunctional (p i)) (curlFunctional (p i')) else 0 := by
  intro q
  obtain ⟨hrow, c₂, x₂, hc₂, hfar⟩ := m2
  obtain ⟨C₁, c₃, hC₁, hc₃, hsz⟩ := m3
  obtain ⟨Cq, x₃, hszq⟩ := hsz (2 * q + 2)
  obtain ⟨x₄, hod⟩ := m4
  obtain ⟨c₅, x₅, hc₅, hlike⟩ := m5
  obtain ⟨x₆, hfb⟩ := m6
  obtain ⟨C₇, hcb⟩ := m7
  have hall : ∀ r : ℕ, ∃ C c x₀ : ℝ, 0 < c ∧ (1 ≤ r → ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ)
      [NeZero N] (nn : ℝ) (j d' : ℕ)
      (o : TorusSite (fineSide (Tb.stepParameters y).side d' N))
      (g : MarkedSample (Tb.stepParameters y) (k + j + 1 + d') N →
        TorusSite (fineSide (Tb.stepParameters y).side d' N) → UnitQuaternion)
      (s : MarkedSample (Tb.stepParameters y) (k + j + 1 + d') N → ℝ)
      (l : Fin r → TorusBond (fineSide (Tb.stepParameters y).side d' N * (Tb.stepParameters y).side) → ℝ)
      (e : Fin r → Fin 3),
      IsLocalChainAbove Tb y T β k (fineSide (Tb.stepParameters y).side d' N) nn x₀ →
      (Tb.stepParameters y).side ∣ fineSide (Tb.stepParameters y).side d' N →
      j < localChainDepth (Tb.stepParameters y) β k →
      j + 1 + d' ≤ 2 * localChainDepth (Tb.stepParameters y) β k →
      Measurable[upperSigma T (k + j + 1) d' N] g → Measurable[upperSigma T (k + j + 1) d' N] s → (∀ u, 0 ≤ s u) →
      (∀ i, ∑ b, |l i b| ≤ 4 * (1 / 2 : ℝ) ^ j) →
      (∀ i b, parentBlock (Tb.stepParameters y).side b.1 ∉ supBall o
          (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
            3 * localLogScale (Tb.stepParameters y) β k) →
        l i b = 0) →
      StepLaw Tb y T β k N nn j r (sampleBelow (Tb.stepParameters y) (k + j + 1) d' N)
        (upperSigma T (k + j + 1) d' N) o g s l e C c) := by
    intro r
    by_cases hr : 1 ≤ r
    · obtain ⟨C, c, x₀, hc, h⟩ := m1 r hr
      exact ⟨C, c, x₀, hc, fun _ T β k N _ nn j d' o g s l e h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
        h T β k N nn j d' o g s l e h1 h2 h3 h4 h5 h6 h7 h8 h9⟩
    · exact ⟨0, 1, 0, one_pos, fun h => absurd h hr⟩
  choose Cf cf xf hcf hf using hall
  set Q := 2 * q + 2 with hQ
  set KC := ∑ r ∈ Finset.range (Q + 1), |Cf r| with hKC
  set xF := ∑ r ∈ Finset.range (Q + 1), |xf r| with hxF
  set cinv := ∑ r ∈ Finset.range (Q + 1), (cf r)⁻¹ with hcinv
  have hcinv0 : 0 ≤ cinv := Finset.sum_nonneg fun r _ => (inv_pos.2 (hcf r)).le
  have hCfK : ∀ r, r ≤ Q → Cf r ≤ KC := fun r hr =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun r => |Cf r|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega)))
  have hxfF : ∀ r, r ≤ Q → xf r ≤ xF := fun r hr =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun r => |xf r|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega)))
  have hcmin : ∀ r, r ≤ Q → (1 + cinv)⁻¹ ≤ cf r := by
    intro r hr
    have h1 : (cf r)⁻¹ ≤ cinv := Finset.single_le_sum (f := fun r => (cf r)⁻¹)
      (fun r _ => (inv_pos.2 (hcf r)).le) (Finset.mem_range.2 (by omega))
    rw [inv_le_comm₀ (by positivity) (hcf r)]
    linarith
  set c₀ := min ((1 + cinv)⁻¹) (min c₂ c₅) with hc₀
  have hc₀pos : 0 < c₀ := lt_min (by positivity) (lt_min hc₂ hc₅)
  set Aε := 1 + 8 * |C₇| with hAε
  have hAε0 : 0 < Aε := by positivity
  obtain ⟨x₇, hnum⟩ := couplingLargeEnough ((2 * q + 2 : ℕ) : ℝ) |(Tb.stepParameters y).B| Aε c₀
    ((Tb.stepParameters y).n₀ : ℝ) hc₀pos hAε0
  refine ⟨16 + 16 * |C₇| + |(Tb.stepParameters y).threshold| + 8 * |(Tb.stepParameters y).B| +
    (4 + 1 / C₁) * |Cq| + KC,
    max x₇ (max x₂ (max x₃ (max x₄ (max x₅ (max x₆ xF))))), ?_⟩
  intro T β k N _ nn o p ec w hw hloc hp
  have hfl := hloc.floor_le
  have f7 : x₇ ≤ (couplingFlow (Tb.stepParameters y) β k).1 := (le_max_left _ _).trans hfl
  have f2 : x₂ ≤ (couplingFlow (Tb.stepParameters y) β k).1 := ((le_max_left _ _).trans (le_max_right _ _)).trans hfl
  have f3 : x₃ ≤ (couplingFlow (Tb.stepParameters y) β k).1 :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hfl
  have f4 : x₄ ≤ (couplingFlow (Tb.stepParameters y) β k).1 :=
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hfl
  have f5 : x₅ ≤ (couplingFlow (Tb.stepParameters y) β k).1 :=
    (((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans hfl
  have f6 : x₆ ≤ (couplingFlow (Tb.stepParameters y) β k).1 :=
    ((((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans hfl
  have fF : xF ≤ (couplingFlow (Tb.stepParameters y) β k).1 :=
    ((((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans hfl
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hnum _ f7
  have hLN : (Tb.stepParameters y).side ∣ N := ⟨2 * (Tb.stepParameters y).side ^ w, by rw [hw]; ring⟩
  have hlocAt : ∀ (x₁ : ℝ), x₁ ≤ (couplingFlow (Tb.stepParameters y) β k).1 → ∀ n, N ≤ n →
      IsLocalChainAbove Tb y T β k n nn x₁ := by
    intro x₁ h1 n hn
    exact { hloc with
      floor_le := h1
      side_ge := hloc.side_ge.trans (by exact_mod_cast hn) }
  have hρ : 0 ≤ localLogScale (Tb.stepParameters y) β k := Nat.cast_nonneg _
  have hnn := hloc.one_le
  have hRadius : ∀ d, ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (d + 1) -
      3 * localLogScale (Tb.stepParameters y) β k ≤ (localBlockSide (Tb.stepParameters y) β k : ℝ) / 8 := by
    intro d
    have hL1 : (1 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) ^ (d + 1) := by
      have : 1 ≤ (Tb.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne (Tb.stepParameters y).side)
      exact one_le_pow₀ (by exact_mod_cast this)
    have h1 : 20 * nn / ((Tb.stepParameters y).side : ℝ) ^ (d + 1) ≤ 20 * nn := div_le_self (by linarith) hL1
    have h2 : 20 * nn ≤ 20 * (couplingFlow (Tb.stepParameters y) β k).1 ^ ((1 : ℝ) / 90) := by
      linarith [hloc.le_rpow]
    have h3 : logCubeScale (couplingFlow (Tb.stepParameters y) β k).1 = localLogScale (Tb.stepParameters y) β k := rfl
    have h4 : localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1 =
      (localBlockSide (Tb.stepParameters y) β k : ℝ) := rfl
    rw [h3, h4] at n6
    unfold ballRadius
    linarith
  have hm0 : (0 : ℝ) ≤ (localBlockSide (Tb.stepParameters y) β k : ℝ) := Nat.cast_nonneg _
  have hN : (Tb.stepParameters y).n₀ ≤ N := by
    have h1 := hloc.side_ge
    have h2 : (0 : ℝ) ≤ localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1 := by
      unfold localBoxRadius
      positivity
    have h3 : ((Tb.stepParameters y).n₀ : ℝ) ≤ N := by nlinarith
    exact_mod_cast h3
  have cB : ChainInputs Tb y T β k N nn (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
      (localLogScale (Tb.stepParameters y) β k) (localBlockSide (Tb.stepParameters y) β k : ℝ) :=
    { prob := fun s n _ =>
        (hC5.2.2 (Tb.stepParameters y) hfit hJ T hloc.cutoff hloc.measurable β s n).1
      fst := fun s n _ => (hC5.2.2 (Tb.stepParameters y) hfit hJ T hloc.cutoff hloc.measurable β s n).2
      S := fun t d n _ => (hC2 (Tb.stepParameters y) hfit T t d n).2
      up := fun t d n _ => (hC2 (Tb.stepParameters y) hfit T t d n).1
      H := hC5.1
      log := hC5.2.1
      Bor := fun d n _ o' b hn hL hd hb hc => hfb T β k n nn d o' b (hlocAt x₆ f6 n hn) hL (by
          have : d < localChainDepth (Tb.stepParameters y) β k := hd
          omega)
        (Finset.mem_filter.2 ⟨hc, by
          have h2 := Finset.mem_filter.1 hb
          exact Finset.mem_filter.2 ⟨h2.1, h2.2.trans (hRadius d)⟩⟩)
      down := fun t h1 h2 n _ hn hL => by
        obtain ⟨j, rfl⟩ : ∃ j, t = k + j := ⟨t - k, by omega⟩
        have hj : j < 2 * localChainDepth (Tb.stepParameters y) β k := by
          have : j < 2 * chainDepth (couplingFlow (Tb.stepParameters y) β k).1 := by omega
          exact this
        have h3 : ∀ o' : TorusSite n, _ := fun o' => hod T β k n nn j o' (hlocAt x₄ f4 n hn) hL hj
        exact (ae_all_iff.2 h3)
      LN := hLN }
  have hρAll : ∀ j, (T.stage j).anchorRadius = Tb.ρA := by
    intro j
    rw [stage_anchorRadius Tb y T j]
    have h1 := (hloc.onFamily.onFamily 0 (Nat.zero_le _)).anchorRadius_eq
    rw [← h1]
    exact (stage_anchorRadius Tb y T 0).symm
  have hexp0 : 0 < Real.exp (-(c₀ * localLogScale (Tb.stepParameters y) β k)) := Real.exp_pos _
  have hexpc : ∀ c', c₀ ≤ c' → Real.exp (-(c' * localLogScale (Tb.stepParameters y) β k)) ≤
      Real.exp (-(c₀ * localLogScale (Tb.stepParameters y) β k)) := by
    intro c' h
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right h hρ
    linarith
  have hA1 : 1 ≤ Aε := by
    have := abs_nonneg C₇
    rw [hAε]
    linarith
  have hle1 : ∀ z, z ≤ Real.exp (-(c₀ * localLogScale (Tb.stepParameters y) β k)) →
      z ≤ Aε * Real.exp (-(c₀ * localLogScale (Tb.stepParameters y) β k)) :=
    fun z h => h.trans (le_mul_of_one_le_left hexp0.le hA1)
  have hKC0 : 0 ≤ KC := Finset.sum_nonneg fun r _ => abs_nonneg _
  have hS0 : 0 ≤ (4 + 1 / C₁) * |Cq| := by positivity
  have a1 := abs_nonneg C₇
  have a2 := abs_nonneg (Tb.stepParameters y).threshold
  have a3 := abs_nonneg (Tb.stepParameters y).B
  have a4 := le_abs_self (Tb.stepParameters y).threshold
  have hXpow : ((couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ))) ^ (4 * q + 4) =
      (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(((2 * q + 2 : ℕ) : ℝ))) := by
    have hx0 : 0 ≤ (couplingFlow (Tb.stepParameters y) β k).1 := by linarith
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    congr 1
    push_cast
    ring
  refine ⟨Aε * Real.exp (-(c₀ * localLogScale (Tb.stepParameters y) β k)),
    chi T k N _ (localBlockSide (Tb.stepParameters y) β k : ℝ) o,
    fun u => flowCouplings (Tb.stepParameters y) β (k + u) ^ (-(1 / 2 : ℝ)), gFam Tb y k N _ Tb.ρA p ec,
    gcFam Tb y k N _ nn (localLogScale (Tb.stepParameters y) β k) Tb.ρA o p ec,
    zFam Tb y T k N _ nn (localLogScale (Tb.stepParameters y) β k) Tb.ρA o p ec,
    tFam Tb y k N _ nn (localLogScale (Tb.stepParameters y) β k) Tb.ρA
      ((couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 4 : ℝ))) o p ec,
    sFam k N _ nn (localLogScale (Tb.stepParameters y) β k) o, ?_, chi_zero T k N _ _ o, ?_, ?_⟩
  · refine gaussianChainData Tb y rfl cB o p ec hp Tb.ρA ((couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 4 : ℝ)))
      _ _ C₇ (Real.exp (-(c₂ * localLogScale (Tb.stepParameters y) β k))) C₁ c₃ Cq Cf cf xf hfit.σ_pos.le hC₁ n1 hρ
      (hrunAll β (hloc.coupling_ge 0 (Nat.zero_le _))) hloc.coupling_ge n4
      (fun d n _ hn p hp => (hrow k d n hn p hp).2)
      (fun d n _ hn hd o' p' hp' hb => hfar _ nn k d n f2 (by linarith) hn hd o' p' hp' hb)
      (fun u n _ h h' a b => hcb u n h h' a b) hN (fun d => (hRadius d).trans (by linarith)) ?_
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) ?_ (by positivity) ?_ ?_ ?_
      (fun r h1 _ => hf r h1) (fun r h1 h2 n hn => hlocAt (xf r) ((hxfF r h2).trans fF) n hn)
      (fun r h1 h2 => (hCfK r h2).trans (by linarith))
      (fun r h1 h2 => hle1 _ (hexpc _ ((min_le_left _ _).trans (hcmin r h2))))
    · have h := hlike T β k (w + 1) N nn o hw (hlocAt x₅ f5 N le_rfl)
      have e0 : chi T k N (localChainDepth (Tb.stepParameters y) β k) (localBlockSide (Tb.stepParameters y) β k : ℝ) o 0 =
          {u | IsLocalEvent T k (localChainDepth (Tb.stepParameters y) β k)
            (localBlockSide (Tb.stepParameters y) β k : ℝ) N u o} := chi_zero T k N _ _ o
      have h' : (markedSampleLaw T β (k + localChainDepth (Tb.stepParameters y) β k +
            localChainDepth (Tb.stepParameters y) β k) N).real
          (chi T k N (localChainDepth (Tb.stepParameters y) β k) (localBlockSide (Tb.stepParameters y) β k : ℝ) o 0)ᶜ ≤
            Real.exp (-(c₅ * (couplingFlow (Tb.stepParameters y) β k).1)) := by
        rw [e0]
        exact h
      refine h'.trans (hle1 _ ?_)
      refine le_trans ?_ (hexpc c₅ ((min_le_right _ _).trans (min_le_right _ _)))
      apply Real.exp_le_exp.2
      have h3 : logCubeScale (couplingFlow (Tb.stepParameters y) β k).1 = localLogScale (Tb.stepParameters y) β k := rfl
      rw [h3] at n5
      have := mul_le_mul_of_nonneg_left n5 hc₅.le
      linarith
    · have h1 := hexpc c₂ ((min_le_right _ _).trans (min_le_left _ _))
      have h2 : 2 * |C₇| * 4 * Real.exp (-(c₂ * localLogScale (Tb.stepParameters y) β k)) ≤
          8 * |C₇| * Real.exp (-(c₀ * localLogScale (Tb.stepParameters y) β k)) := by
        have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 8 * |C₇| by positivity)
        linarith
      rw [hAε]
      nlinarith
    · exact n2.trans (le_of_eq hXpow.symm)
    · exact n3.trans (le_of_eq hXpow.symm)
    · intro t d d' o' h1 h2 h3
      have := hszq T β k N nn t d d' o' (hlocAt x₃ f3 N le_rfl) hLN h1 h2 h3
      exact ⟨this.1, this.2.1⟩
  · intro u i
    exact curvature_sum hSum T Tb.ρA hρAll k N _ nn _ o (p i) (ec i) u
  · intro i i'
    unfold gFam
    by_cases h : ec i = ec i'
    · simp only [if_pos h]
      exact (stepsCovariance_eq k Tb.ρA _ _ (p i) (p i')).symm
    · simp [h]
end Final
section ParameterChoices
private theorem holdsOnParams_and {P Q : ParameterAssignment → ℝ → Prop} (hP : HoldsOnParameterFamilies P)
    (hQ : HoldsOnParameterFamilies Q) : HoldsOnParameterFamilies fun T y => P T y ∧ Q T y := by apply _root_.YangMills.SharedProofs.p24215 <;> assumption
private theorem holdsOnParams_expansionReturns :
    HoldsOnParameterFamilies fun T y => ExpansionReturnsAt (T.stepParameters y) := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ T _ _ _ _ _ _ _
  exact ⟨0, fun y _ hR _ => hR⟩
private theorem holdsOnParams_derivBound (C₀ : ℝ) : HoldsOnParameterFamilies fun T _ => C₀ ≤ T.derivBound := by
  intro a _
  refine ⟨0, fun _ => 1, C₀, fun _ => one_pos, ?_⟩
  intro L _ _ T _ _ _ _ _ _ h
  exact ⟨0, fun _ _ _ _ => h⟩
end ParameterChoices
theorem curvatureGaussianChain (hMS : stepCurvatureMomentsStatement)
    (hSum : curvatureLevelSumStatement) (hRS : transportedCurlFunctionalBoundsStatement)
    (hSZ : localChainSizeStatement) (hOD : descentKeepsBallClearStatement)
    (hLE : localEventLikelyStatement) (hFB : coldBallDeviationMeasurableStatement)
    (hCB : stepCovarianceBoundedStatement) (hTW : TowerAlongFlowStatement)
    (hScaleFlow : FlowWhereExpansionReturns) (hC2 : upperSigmaDeterminesStatesStatement)
    (hC5 : chainMeasurabilityStatement) : curvatureGaussianChainStatement := by
  obtain ⟨C₀, hR⟩ := hScaleFlow
  have big := holdsOnParams_and hMS (holdsOnParams_and hRS (holdsOnParams_and hSZ (holdsOnParams_and hOD
    (holdsOnParams_and hLE (holdsOnParams_and hFB (holdsOnParams_and hCB
    (holdsOnParams_and hTW (holdsOnParams_and (holdsOnParams_derivBound C₀) holdsOnParams_expansionReturns))))))))
  intro a ha
  obtain ⟨L₀, r, C, hr, h⟩ := big a ha
  refine ⟨L₀, r, C, hr, fun L hL hLL T e1 e2 d1 d2 d3 d4 d5 => ?_⟩
  obtain ⟨y₀, hy⟩ := h L hL hLL T e1 e2 d1 d2 d3 d4 d5
  refine ⟨y₀, fun y hy₀ hRR hW => ?_⟩
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10⟩ := hy y hy₀ hRR hW
  exact gaussianChain_of_curvatureMoments T y m1 m2 m3 m4 m5 m6 m7 m8.1 m8.2.1 (fun β hβ => ((hR _ m8.1 m9 m10).2 β hβ).1)
    hSum hC2 hC5
end ResponseInTheExpansion
end YangMills.Construction
end
