import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfTheLawOfASettingProof
import YangMills.Construction.ColdStepAtMirrorFrames.MomentsOfAConvexMeasure
import YangMills.Construction.LawByMomentsOfTheFlow.ColdDensityOfAGoodStateProof
import YangMills.Construction.LawByMomentsOfTheFlow.SlopesOfTheMeansOfForms
import Mathlib
import YangMills.Construction.LawByMomentsOfTheFlow.FluctuationsOfTheGaussianChain
import YangMills.Construction.LawByMomentsOfTheFlow.SlopesOfThePotentialOfAGoodState
import YangMills.Construction.ResponseInTheExpansion.TheHessianOfAStepIsDefinite
import YangMills.Construction.SummableBoundsOfTheFlow.RimMomentsOfALaw
set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def goodStateColdLawStatement : Prop :=
  ForAllPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling → ∀ (d n : ℕ) [NeZero n], d < S.logIndex →
    n = S.levelSide (S.lastSeparated + d + 1) →
    (fluctuationCov Λ.stepParams.coupling Λ.stepParams.side 1 (S.lastSeparated + d) n).PosSemidef ∧
    (∀ q : ℕ, 1 ≤ q →
      weightedCurvatureNorm (fluctuationGaussian Λ.stepParams.coupling Λ.stepParams.side 1 (S.lastSeparated + d) n)
        (fun _ => 1) (q : ENNReal) (fun ζ => extendFluctuation ζ) ≤ ENNReal.ofReal (C q)) ∧
    ∀ (V : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n)),
      S.IsGoodConfig (S.lastSeparated + d + 1) n V Y →
    ∃ (ρ : ℝ) (p : ℝ → ℝ)
      (Ψ : ColdStepAtMirrorFrames.BondField (ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n) → ℝ),
      0 < ρ ∧ ColdStepAtMirrorFrames.IsCutoff ρ p ∧ ContDiff ℝ 1 Ψ ∧
      (∀ Φ : ColourForm (n * Λ.stepParams.side) → ℝ,
        coldExpectation (S.tower.stage (S.lastSeparated + d)).toStepSetup
            (S.smoothedField (S.lastSeparated + d + 1) n V)
            (fun η => Φ (freeCoordForm (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
              (S.smoothedField (S.lastSeparated + d + 1) n V)) η)) =
          ∫ k, Φ (chartColourForm k) ∂ConvexObservables.normalizedBallLaw (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ) ∧
      (∀ q : ℕ, 1 ≤ q →
        weightedCurvatureNorm (ConvexObservables.normalizedBallLaw (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ)
            (fun _ => 1) (q : ENNReal) (fun k => chartColourForm k) ≤
          ENNReal.ofReal (C q * S.scaleCoupling ^ (-(1 / 2) : ℝ))) ∧
      ∀ j : Fin 3 × ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n,
        eLpNorm (fun k => MomentMethod.driftCoord
            (fluctuationCov Λ.stepParams.coupling Λ.stepParams.side (S.coupling (S.lastSeparated + d))
              (S.lastSeparated + d) n) p Ψ k j) 2
            (ConvexObservables.normalizedBallLaw (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ) ≤
          ENNReal.ofReal (C 0 * S.scaleCoupling⁻¹ * (1 + (1 + (TorusFields.supDist
            (TorusLumps.toTorusSite (n * Λ.stepParams.side) j.2.1.1)
            (S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side)) : ℝ) + (S.range : ℝ)) *
            S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature (S.lastSeparated + d + 1) n V))
end YangMills.Construction.MomentLaw
end

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction
open StepSettings StepGas TorusFields TorusLumps RenormalizationStepParameters StepCosts TopLevelSites BlockAverages ColdStepAtMirrorFrames
  ConvexObservables Estimates WeightedResponses ResponseInTheExpansion ClusterExpansionOfAStep MomentMethod
namespace MomentLaw
namespace GoodStateColdLaw
private theorem coordNorm_toImaginary (z : EuclideanSpace ℝ (Fin 3)) : coordNorm z = ‖z‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
section Parameters
private theorem forAllParameters_mono {Q Q' : MomentParameters → Prop} (h : ForAllParameters Q) (f : ∀ Λ, Q Λ → Q' Λ) :
    ForAllParameters Q' := by apply _root_.YangMills.SharedProofs.p9549 <;> assumption
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁) (h₂ : ForAllParameters Q₂) :
    ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_of_holdsOnAllParameters {P : ParameterAssignment → ℝ → Prop} (h : HoldsOnParameterFamilies P) :
    ForAllParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p27928 <;> assumption
private theorem forAllParameters_admissible : ForAllParameters fun Λ => Λ.table.Admissible := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD _ _ _ _ _ _
  exact ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => hD⟩
abbrev _root_.YangMills.SharedProofs.p23915 := @forAllParameters_admissible
private theorem forAllParameters_settings (hCv : SettingsUniformlyConvex) (hConf : GasConfigIsAdmissibleSetting) :
    ForAllParameters fun Λ => ∃ Cc : ℝ, 0 < Cc ∧ 200 * Λ.table.B ≤ Λ.floor ∧ 0 ≤ Λ.floor ∧
      (∀ R : StepSetup, R.OnParameters Λ.table Λ.floor → ∀ (n : ℕ) [NeZero n], Λ.table.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
        s.HasFullDecay s.potential Λ.table.lam Cc) ∧
      (∀ R : StepSetup, R.OnParameters Λ.table Λ.floor → R.nextCoupling ≤ 1.01 * R.coupling → ∀ (n : ℕ) [NeZero n] (G : GasGround R n),
        G.IsAdmissibleGround → ∀ σ : G.Config, G.pairConstraint.IsAdmissible σ → (G.settingOf (G.familyOf σ)).IsAdmissible) := by
  obtain ⟨rt₀, hrt₀, HM⟩ := hCv
  intro a _
  refine ⟨1, rt₀, 0, hrt₀, ?_⟩
  intro L _ hL Tb _ hTL hD _ _ hrt _ _ _
  obtain ⟨Cc, y₁, hCc, Y₁⟩ := HM Tb hD hrt
  obtain ⟨y₂, Y₂⟩ := hConf Tb hD
  refine ⟨max (max y₁ y₂) (max (200 * Tb.B) 0), fun y hy _ _ g _ _ k _ _ _ R d _ => ?_⟩
  have hy₁ : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hy₂ : y₂ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy₃ : 200 * Tb.B ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hy₄ : 0 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
  refine ⟨Cc, hCc, hy₃, hy₄, ?_, ?_⟩
  · intro R hR n _ hn s hs
    exact (Y₁ y hy₁ R hR n hn s hs).1
  · intro R hR hx n _ G hG σ hσ
    exact Y₂ y hy₂ R hR hx n G hG σ hσ
end Parameters
section Relabel
variable {L u m : ℕ} [NeZero L] [NeZero m]
private abbrev torusBondInFrame (L u m : ℕ) (c : TorusBond (m * L)) :
    (torusFrame L u m).Site (torusFrame L u m).depth × Fin 4 :=
  (torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth c.1, c.2)
private theorem torusBondInFrame_injective (c c' : TorusBond (m * L)) (h : torusBondInFrame L u m c = torusBondInFrame L u m c') :
    c = c' := by
  have hp : ∀ i, (torusFrame L u m).period (torusFrame L u m).depth i = m * L := fun i => by
    simp [BlockFrame.period, torusFrame, BlockFrame.top]
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  have e := congrArg (toTorusSite (m * L)) h1
  simp only [torusBondInFrame] at e
  rw [toTorusSite_torusSiteInFrame hp, toTorusSite_torusSiteInFrame hp] at e
  exact Prod.ext e h2
abbrev _root_.YangMills.DeltaSharedProofs.p500956 := @torusBondInFrame_injective
private theorem torusBondInFrame_mem_chordBonds (hodd : Odd L) (h2 : 2 ≤ m) {c : TorusBond (m * L)}
    (hc : c ∈ StepCosts.chartBonds L m) :
    torusBondInFrame L u m c ∈ BlockAverages.chordBonds (finiteCells (torusFrame L u m)) := by
  classical
  have hs : ¬ IsAxialTreeBond (F := stepBlockFrame L m) (torusSiteInFrame (stepBlockFrame L m) 0 c.1, c.2) := by
    simpa [StepCosts.chartBonds] using hc
  have : NeZero (m * (stepBlockFrame L m).blockSide) := inferInstanceAs (NeZero (m * L))
  have : NeZero (m * (torusFrame L u m).blockSide) := inferInstanceAs (NeZero (m * L))
  have t1 := isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame L m) (fun _ => rfl) hodd h2 c.1 c.2
  have t2 := isAxialTreeBond_torusSiteInFrame_iff (F := torusFrame L u m) (fun _ => rfl) hodd h2 c.1 c.2
  have hnt : ¬ IsAxialTreeBond (torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth c.1, c.2) := fun h =>
    hs (t1.2 (t2.1 h))
  have := mem_chordBonds_of_parentBlock (F := torusFrame L u m) (S := Finset.univ) (fun _ => rfl) hodd h2 c.1 c.2 hnt
    (Finset.mem_univ _) (Finset.mem_univ _)
  rwa [cellsOfSites_univ (fun _ => rfl)] at this
abbrev _root_.YangMills.DeltaSharedProofs.p363 := @torusBondInFrame_mem_chordBonds
private theorem torusBondInFrame_toTorusSite (b : (torusFrame L u m).Site (torusFrame L u m).depth × Fin 4) :
    torusBondInFrame L u m (toTorusSite (m * L) b.1, b.2) = b := by
  have hp : ∀ i, (torusFrame L u m).period (torusFrame L u m).depth i = m * L := fun i => by
    simp [BlockFrame.period, torusFrame, BlockFrame.top]
  refine Prod.ext ?_ rfl
  funext k
  have h : ∀ (P Q : ℕ) (hPQ : P = Q) (a : ZMod P), (((((a.cast : ℤ) : ZMod Q)).cast : ℤ) : ZMod P) = a := by
    intro P Q h a
    subst h
    simp
  exact h _ _ (hp k) (b.1 k)
abbrev _root_.YangMills.DeltaSharedProofs.p501604 := @torusBondInFrame_toTorusSite
private theorem toTorusSite_mem_chartBonds (hodd : Odd L) (h2 : 2 ≤ m) (b : ChartBondIndex L u m) :
    (toTorusSite (m * L) b.1.1, b.1.2) ∈ StepCosts.chartBonds L m := by
  classical
  have : NeZero (m * (stepBlockFrame L m).blockSide) := inferInstanceAs (NeZero (m * L))
  have : NeZero (m * (torusFrame L u m).blockSide) := inferInstanceAs (NeZero (m * L))
  have hb : ¬ IsAxialTreeBond b.1 := (Finset.mem_filter.mp b.2).2
  have e := torusBondInFrame_toTorusSite (L := L) (u := u) (m := m) b.1
  have t1 := isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame L m) (fun _ => rfl) hodd h2 (toTorusSite (m * L) b.1.1) b.1.2
  have t2 := isAxialTreeBond_torusSiteInFrame_iff (F := torusFrame L u m) (fun _ => rfl) hodd h2 (toTorusSite (m * L) b.1.1) b.1.2
  have : ¬ IsAxialTreeBond (F := stepBlockFrame L m)
      (torusSiteInFrame (stepBlockFrame L m) 0 (toTorusSite (m * L) b.1.1), b.1.2) := fun h => by
    apply hb
    have h4 : IsAxialTreeBond (torusBondInFrame L u m (toTorusSite (m * L) b.1.1, b.1.2)) := t2.2 (t1.1 h)
    rwa [e] at h4
  simpa [StepCosts.chartBonds] using this
abbrev _root_.YangMills.SharedProofs.p28920 := @toTorusSite_mem_chartBonds
private def chartBondsEquiv (hodd : Odd L) (h2 : 2 ≤ m) : ↥(StepCosts.chartBonds L m) ≃ ChartBondIndex L u m where
  toFun b := ⟨torusBondInFrame L u m b.1, torusBondInFrame_mem_chordBonds hodd h2 b.2⟩
  invFun c := ⟨(toTorusSite (m * L) c.1.1, c.1.2), toTorusSite_mem_chartBonds hodd h2 c⟩
  left_inv b := by
    apply Subtype.ext
    exact torusBondInFrame_injective (L := L) (u := u) (m := m) _ _ (torusBondInFrame_toTorusSite _)
  right_inv c := by
    apply Subtype.ext
    exact torusBondInFrame_toTorusSite _
end Relabel
section Free
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem markAt_emptyCoarseState (y : TorusSite n) : (emptyCoarseState R : CoarseState R n).markAt y = none := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TrivialFieldGround.markAt_empty <;> assumption
private theorem fieldAt_empty (b : TorusBond (n * R.params.side)) : (GasFamily.empty : GasFamily R n).fieldAt b = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.fieldAt_empty <;> assumption
private theorem mem_free_coldSetting (V : TorusField n) (b : TorusBond (n * R.params.side)) :
    b ∈ (coldSettingOver R V).free ↔ b ∈ StepCosts.chartBonds R.params.side n := by
  classical
  show b ∈ ((coldGroundOver R V).freeBonds.filter fun b => (GasFamily.empty : GasFamily R n).fieldAt b = Sum.inl ()) ↔ _
  simp only [Finset.mem_filter, GasGround.freeBonds, markedBonds, fieldAt_empty, and_true, GasGround.IsRecorded]
  simp [coldGroundOver, markAt_emptyCoarseState]
abbrev _root_.YangMills.SharedProofs.p28439 := @mem_free_coldSetting
end Free
section Bounds
variable {Ω : Type} [MeasurableSpace Ω]
private theorem eLpNorm_le_of_integral_pow {μ : Measure Ω} {f : Ω → ℝ} {Q : ℕ} (hQ : Q ≠ 0)
    (hf : AEStronglyMeasurable f μ) (hI : Integrable (fun x => |f x| ^ Q) μ) {K : ℝ} (hK : ∫ x, |f x| ^ Q ∂μ ≤ K) :
    eLpNorm f (Q : ENNReal) μ ≤ ENNReal.ofReal (K ^ ((Q : ℝ)⁻¹)) := by
  have hQ0 : (Q : ENNReal) ≠ 0 := by exact_mod_cast hQ
  have hQt : (Q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top Q
  have hr : (Q : ENNReal).toReal = (Q : ℝ) := ENNReal.toReal_natCast Q
  have hm : MemLp f (Q : ENNReal) μ := by
    refine (integrable_norm_rpow_iff hf hQ0 hQt).1 ?_
    rw [hr]
    simpa [Real.rpow_natCast] using hI
  rw [hm.eLpNorm_eq_integral_rpow_norm hQ0 hQt, hr]
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ?_ ?_ (by positivity))
  · exact integral_nonneg fun x => by positivity
  · simpa [Real.rpow_natCast] using hK
private theorem eLpNorm_weighted_sum_le {κ : Type} [Fintype κ] {μ : Measure Ω} (c F : κ → ℝ) (f : κ → Ω → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hF : ∀ i, 0 ≤ F i) (hm : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : ∀ i, eLpNorm (f i) 2 μ ≤ ENNReal.ofReal (F i)) :
    eLpNorm (fun ω => ∑ i, c i * f i ω) 2 μ ≤ ENNReal.ofReal (∑ i, c i * F i) := by
  classical
  have e : (fun ω => ∑ i, c i * f i ω) = ∑ i, (c i) • f i := by
    funext ω
    simp [Finset.sum_apply]
  rw [e]
  refine (eLpNorm_sum_le (fun i _ => (hm i).const_smul _) (by norm_num)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hc i) (hF i)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [eLpNorm_const_smul, ENNReal.ofReal_mul (hc i)]
  refine mul_le_mul' ?_ (h i)
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hc i)]
variable {n : ℕ} [NeZero n]
private theorem curlNorm_eq_norm (X : ColourForm n) (p : TorusPlaquette n) :
    curlNorm X p = ‖(WithLp.toLp 2 fun e => curl (X e) p : EuclideanSpace ℝ (Fin 3))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [curlNorm]
private theorem curlNorm_le_sum_abs (X : ColourForm n) (p : TorusPlaquette n) : curlNorm X p ≤ ∑ e, |curl (X e) p| := by
  rw [curlNorm_eq_norm, EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  simp only [Fin.sum_univ_three, sq_abs]
  nlinarith [abs_nonneg (curl (X 0) p), abs_nonneg (curl (X 1) p), abs_nonneg (curl (X 2) p),
    sq_abs (curl (X 0) p), sq_abs (curl (X 1) p), sq_abs (curl (X 2) p),
    mul_nonneg (abs_nonneg (curl (X 0) p)) (abs_nonneg (curl (X 1) p)),
    mul_nonneg (abs_nonneg (curl (X 0) p)) (abs_nonneg (curl (X 2) p)),
    mul_nonneg (abs_nonneg (curl (X 1) p)) (abs_nonneg (curl (X 2) p))]
abbrev _root_.YangMills.SharedProofs.p49135 := @curlNorm_le_sum_abs
private theorem weightedCurvatureNorm_le_of_bonds {μ : Measure Ω} {q : ENNReal} (hq : 1 ≤ q) {X : Ω → ColourForm n} {V : ℝ}
    (hV : 0 ≤ V) (hm : ∀ e c, AEStronglyMeasurable (fun w => X w e c) μ)
    (hb : ∀ e c, eLpNorm (fun w => X w e c) q μ ≤ ENNReal.ofReal V) :
    weightedCurvatureNorm μ (fun _ => 1) q X ≤ ENNReal.ofReal (12 * V) := by
  refine iSup_le fun p => ?_
  simp only [ENNReal.ofReal_one, one_mul]
  have e0 : ∀ e, (fun w => curl (X w e) p.1) =
      (((fun w => X w e (p.1.1, p.1.2.1)) + (fun w => X w e (p.1.1 + TorusFields.unitStep n p.1.2.1, p.1.2.2))) -
        (fun w => X w e (p.1.1 + TorusFields.unitStep n p.1.2.2, p.1.2.1))) - (fun w => X w e (p.1.1, p.1.2.2)) := fun e => rfl
  have hE : ∀ e, eLpNorm (fun w => curl (X w e) p.1) q μ ≤ 4 * ENNReal.ofReal V := fun e => by
    rw [e0]
    have s1 := eLpNorm_sub_le (((hm e (p.1.1, p.1.2.1)).add (hm e (p.1.1 + TorusFields.unitStep n p.1.2.1, p.1.2.2))).sub
      (hm e (p.1.1 + TorusFields.unitStep n p.1.2.2, p.1.2.1))) (hm e (p.1.1, p.1.2.2)) hq
    have s2 := eLpNorm_sub_le ((hm e (p.1.1, p.1.2.1)).add (hm e (p.1.1 + TorusFields.unitStep n p.1.2.1, p.1.2.2)))
      (hm e (p.1.1 + TorusFields.unitStep n p.1.2.2, p.1.2.1)) hq
    have s3 := eLpNorm_add_le (hm e (p.1.1, p.1.2.1)) (hm e (p.1.1 + TorusFields.unitStep n p.1.2.1, p.1.2.2)) hq
    refine s1.trans ((add_le_add (s2.trans (add_le_add s3 (hb _ _))) (hb _ _)).trans ?_)
    refine (add_le_add (add_le_add (add_le_add (hb _ _) (hb _ _)) le_rfl) le_rfl).trans ?_
    exact le_of_eq (by ring)
  have hmc : ∀ e, AEStronglyMeasurable (fun w => curl (X w e) p.1) μ := fun e => by
    rw [e0]
    exact (((hm e (p.1.1, p.1.2.1)).add (hm e (p.1.1 + TorusFields.unitStep n p.1.2.1, p.1.2.2))).sub
      (hm e (p.1.1 + TorusFields.unitStep n p.1.2.2, p.1.2.1))).sub (hm e (p.1.1, p.1.2.2))
  have hma : ∀ e, AEStronglyMeasurable (fun w => |curl (X w e) p.1|) μ := fun e => (hmc e).norm
  have ha : ∀ e, eLpNorm (fun w => |curl (X w e) p.1|) q μ ≤ 4 * ENNReal.ofReal V := fun e =>
    (le_of_eq (eLpNorm_norm (p := q) (μ := μ) (fun w => curl (X w e) p.1))).trans (hE e)
  calc eLpNorm (fun w => curlNorm (X w) p.1) q μ
      ≤ eLpNorm ((((fun w => |curl (X w 0) p.1|) + fun w => |curl (X w 1) p.1|) +
          fun w => |curl (X w 2) p.1|)) q μ := by
        refine eLpNorm_mono_real fun w => ?_
        have e1 : 0 ≤ curlNorm (X w) p.1 := Real.sqrt_nonneg _
        rw [Real.norm_of_nonneg e1]
        have := curlNorm_le_sum_abs (X w) p.1
        rw [Fin.sum_univ_three] at this
        exact this
    _ ≤ _ := by
        have s1 := eLpNorm_add_le ((hma 0).add (hma 1)) (hma 2) hq
        have s2 := eLpNorm_add_le (hma 0) (hma 1) hq
        refine s1.trans ((add_le_add (s2.trans (add_le_add (ha 0) (ha 1))) (ha 2)).trans ?_)
        rw [ENNReal.ofReal_mul (by norm_num)]
        have : ENNReal.ofReal 12 = 12 := by norm_num
        rw [this]
        exact le_of_eq (by ring)
end Bounds
section Maps
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
private def reindexBonds : BondField κ →L[ℝ] BondField ι :=
  ContinuousLinearMap.pi fun b => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => BondVector) (e b)
@[simp] private theorem reindexBonds_apply (k : BondField κ) (b : ι) : reindexBonds e k b = k (e b) := rfl
private theorem reindexBonds_bondVariation (c : κ) (x : BondVector) :
    reindexBonds e (ColdStepAtMirrorFrames.bondVariation c x) = ColdStepAtMirrorFrames.bondVariation (e.symm c) x := by
  funext b
  simp only [reindexBonds_apply, ColdStepAtMirrorFrames.bondVariation, Pi.single_apply]
  by_cases h : e b = c
  · have : b = e.symm c := by rw [← h]; simp
    simp [h, this]
  · have : b ≠ e.symm c := fun h' => h (by rw [h']; simp)
    simp [h, this]
private theorem measurePreserving_piCongrLeft_bonds :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : κ => BondVector) e) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : κ => BondVector) e
private theorem reindexBonds_piCongrLeft (η : BondField ι) :
    reindexBonds e ((MeasurableEquiv.piCongrLeft (fun _ : κ => BondVector) e) η) = η := by
  funext b
  rw [reindexBonds_apply, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
private theorem integral_reindexBonds (H : BondField ι → ℝ) : ∫ η, H η = ∫ k, H (reindexBonds e k) := by
  have h := (measurePreserving_piCongrLeft_bonds e).integral_comp' (fun k => H (reindexBonds e k))
  simp only [reindexBonds_piCongrLeft] at h
  exact h
private theorem integrable_reindexBonds {H : BondField ι → ℝ} (hH : Integrable H) :
    Integrable (fun k => H (reindexBonds e k)) := by
  have h := (measurePreserving_piCongrLeft_bonds e).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (g := fun k => H (reindexBonds e k))
  refine h.1 ?_
  have e1 : ((fun k => H (reindexBonds e k)) ∘ (MeasurableEquiv.piCongrLeft (fun _ : κ => BondVector) e)) = H := by
    funext η
    simp only [Function.comp, reindexBonds_piCongrLeft]
  rw [e1]
  exact hH
private theorem ballDensity_reindexBonds (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) (k : BondField κ) :
    ballDensity r (fun k' => Ψ (reindexBonds e k')) k = ballDensity r Ψ (reindexBonds e k) := by
  unfold ballDensity radialWeightProd
  congr 1
  exact (Equiv.prod_comp e fun c => r ‖k c‖).symm
private theorem ballExpectation_reindexBonds (r : ℝ → ℝ) (Ψ f : BondField ι → ℝ) :
    ballExpectation r Ψ f = ballExpectation r (fun k => Ψ (reindexBonds e k)) (fun k => f (reindexBonds e k)) := by
  unfold ballExpectation
  rw [integral_reindexBonds e (fun η => f η * ballDensity r Ψ η), integral_reindexBonds e (fun η => ballDensity r Ψ η)]
  simp only [ballDensity_reindexBonds]
end Maps
section Calculus
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem ballDensity_cutoffFactor_max (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) :
    ballDensity (fun u => cutoffFactor ρ p (max u 0)) Ψ = ballDensity (cutoffFactor ρ p) Ψ := by
  funext η
  unfold ballDensity radialWeightProd
  congr 1
  exact Finset.prod_congr rfl fun b _ => by
    show cutoffFactor ρ p (max ‖η b‖ 0) = _
    rw [max_eq_left (norm_nonneg _)]
private theorem update_add_smul_eq (ζ : BondField ι) (b : ι) (X : BondVector) (τ : ℝ) :
    Function.update ζ b (ζ b + τ • X) = ζ + τ • ColdStepAtMirrorFrames.bondVariation b X := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ConvexLaw.update_add_smul_eq_add_bondVariation <;> assumption
private theorem deriv_line_of_eventuallyEq {Ψ u : BondField ι → ℝ} (hΨ : Differentiable ℝ Ψ) {ζ w : BondField ι}
    (h : Ψ =ᶠ[nhds ζ] u) : deriv (fun σ : ℝ => u (ζ + σ • w)) 0 = fderiv ℝ Ψ ζ w := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ConvexLaw.deriv_line_eq_fderiv_of_eventuallyEq <;> assumption
private theorem abs_bondPartialDeriv_le {G : BondField ι → ℝ} {η : BondField ι} {b : ι} {B : ℝ}
    (h : ∀ X : BondVector, ‖X‖ = 1 → |fderiv ℝ G η (ColdStepAtMirrorFrames.bondVariation b X)| ≤ B) (e : BondVector) :
    |bondPartialDeriv G b η e| ≤ B * ‖e‖ := by
  unfold bondPartialDeriv
  by_cases he : e = 0
  · subst he
    simp [ColdStepAtMirrorFrames.bondVariation]
  have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr he
  set X := ‖e‖⁻¹ • e with hX
  have u1 : ‖X‖ = 1 := by
    rw [hX, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have e1 : ColdStepAtMirrorFrames.bondVariation b e = ‖e‖ • ColdStepAtMirrorFrames.bondVariation b X := by
    funext c
    by_cases hc : c = b
    · subst hc
      simp [ColdStepAtMirrorFrames.bondVariation, hX, smul_smul, mul_inv_cancel₀ hn]
    · simp [ColdStepAtMirrorFrames.bondVariation, Pi.single_eq_of_ne hc]
  rw [e1, map_smul, smul_eq_mul, abs_mul, abs_norm, mul_comm]
  exact mul_le_mul_of_nonneg_right (h X u1) (norm_nonneg _)
private theorem abs_apply_le_of_basis_three (f : BondVector →L[ℝ] ℝ) {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ i : Fin 3, |f (EuclideanSpace.single i 1)| ≤ A) (v : BondVector) : |f v| ≤ 3 * A * ‖v‖ := by
  have e : v = ∑ i : Fin 3, v i • EuclideanSpace.single i (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
    simpa using this.symm
  have h1 : f v = ∑ i : Fin 3, v i * f (EuclideanSpace.single i 1) := by
    conv_lhs => rw [e]
    simp [map_sum]
  rw [h1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h2 : ∀ i : Fin 3, |v i * f (EuclideanSpace.single i 1)| ≤ ‖v‖ * A := fun i => by
    rw [abs_mul]
    exact mul_le_mul (by simpa using PiLp.norm_apply_le v i) (h i) (abs_nonneg _) (norm_nonneg _)
  refine (Finset.sum_le_sum fun i _ => h2 i).trans (le_of_eq ?_)
  simp
  ring
end Calculus
section Chart
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def freeBondsEquiv (u : ℕ) (V : TorusField n) (hodd : Odd R.params.side) (h2 : 2 ≤ n) :
    ↥(coldSettingOver R V).free ≃ ChartBondIndex R.params.side u n :=
  (Equiv.subtypeEquivRight (mem_free_coldSetting V)).trans (chartBondsEquiv hodd h2)
private theorem freeBondsEquiv_val (u : ℕ) (V : TorusField n) (hodd : Odd R.params.side) (h2 : 2 ≤ n)
    (b : ↥(coldSettingOver R V).free) : (freeBondsEquiv u V hodd h2 b).1 = torusBondInFrame R.params.side u n b.1 := rfl
private theorem chartFreeCoords_eq_reindex (u : ℕ) (V : TorusField n) (hodd : Odd R.params.side) (h2 : 2 ≤ n)
    (k : BondField (ChartBondIndex R.params.side u n)) : chartFreeCoords R u V k = reindexBonds (freeBondsEquiv u V hodd h2) k := by
  classical
  funext b
  unfold chartFreeCoords
  rw [reindexBonds_apply, Finset.sum_eq_single (freeBondsEquiv u V hodd h2 b)]
  · exact if_pos (freeBondsEquiv_val u V hodd h2 b).symm
  · intro c _ hne
    rw [if_neg]
    intro h
    exact hne (Subtype.ext h.symm)
  · simp
private theorem freeCoordForm_reindex (u : ℕ) (V : TorusField n) (hodd : Odd R.params.side) (h2 : 2 ≤ n)
    (k : BondField (ChartBondIndex R.params.side u n)) :
    freeCoordForm (coldSettingOver R V) (reindexBonds (freeBondsEquiv u V hodd h2) k) = chartColourForm k := by
  classical
  funext e c
  unfold freeCoordForm chartColourForm extendChart
  by_cases hb : c ∈ (coldSettingOver R V).free
  · rw [dif_pos hb, Finset.sum_eq_single (freeBondsEquiv u V hodd h2 ⟨c, hb⟩)]
    · exact (if_pos (freeBondsEquiv_val u V hodd h2 ⟨c, hb⟩).symm).symm
    · intro b _ hne
      rw [if_neg]
      intro h
      exact hne (Subtype.ext h.symm)
    · simp
  · rw [dif_neg hb]
    refine (Finset.sum_eq_zero fun b _ => ?_).symm
    rw [if_neg]
    intro h
    apply hb
    have h1 := ((freeBondsEquiv u V hodd h2).symm b).2
    have h3 : torusBondInFrame R.params.side u n ((freeBondsEquiv u V hodd h2).symm b).1 = b.1 := by
      rw [← freeBondsEquiv_val u V hodd h2]
      simp
    have h4 := torusBondInFrame_injective (L := R.params.side) (u := u) (m := n) _ _ (h3.trans h.symm)
    rwa [h4] at h1
private theorem chartLaw_exists (hCM : ChartPotentialConvex) (hMo : GaussianMomentBound)
    (hW : FreeBondWeightsSummable) (hRc : CutoffFactorIsRadialCutoff) (hLw : normalizedBallLawIsProbabilityStatement)
    (u : ℕ) (V : TorusField n) (hodd : Odd R.params.side) (h2 : 2 ≤ n) {lam Cc A Cr : ℝ} {p₀ : ℝ → ℝ} (hp₀ : R.barrierFn = p₀)
    (hσ : 0 < R.params.threshold) (hrt : 0 < R.params.rt) (hx : 1 ≤ R.coupling) (hlam : 0 < lam) (hC : 0 ≤ Cc)
    (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hfull : (coldSettingOver R V).HasFullDecay (coldSettingOver R V).potential lam Cc)
    (hA : 3 * A ≤ Real.sqrt (R.coupling * lam / 8))
    (h0 : ∀ j : Fin 3 × ChartBondIndex R.params.side u n, |fderiv ℝ (chartPotential R u V) 0 (unitVariation j)| ≤ A)
    (hCr : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x κ : ℝ) (d : ι → ι → ℝ) (Ψ : BondField ι → ℝ)
        (K : ι → ι → ℝ), 1 ≤ x → 0 ≤ κ → IsPseudoMetricOnBonds d →
        IsUniformlyConvexDecaying R.ballRadius (x * (lam / 2) / 4) κ d Ψ K →
        (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ R.params.bondWeightBound) →
        (∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * (lam / 2) / 4) * ‖e‖) →
        (∀ η : BondField ι, (∀ b, ‖η b‖ < R.ballRadius) → ∀ (b : ι) (e : BondVector),
          |bondPartialDeriv Ψ b η e| ≤ Cc * x * ‖e‖) →
        ∀ b : ι, Integrable (fun η => |iteratedDeriv 1 p₀ ‖η b‖| ^ 2 * ballDensity (cutoffFactor R.ballRadius p₀) Ψ η) ∧
          ballExpectation (cutoffFactor R.ballRadius p₀) Ψ (fun η => |iteratedDeriv 1 p₀ ‖η b‖| ^ 2) ≤ Cr * (x ^ 0)⁻¹) :
    ∃ Ψ : BondField (ChartBondIndex R.params.side u n) → ℝ, ContDiff ℝ 1 Ψ ∧
      (∀ Φ : ColourForm (n * R.params.side) → ℝ, coldExpectation R V (fun η => Φ (freeCoordForm (coldSettingOver R V) η)) =
        ∫ k, Φ (chartColourForm k) ∂normalizedBallLaw (cutoffFactor R.ballRadius R.barrierFn) Ψ) ∧
      (∀ k, (∀ b, ‖k b‖ < R.ballRadius) → fderiv ℝ Ψ k = fderiv ℝ (chartPotential R u V) k) ∧
      (∀ (q : ℕ) (c : ChartBondIndex R.params.side u n),
        ∫ k, ‖k c‖ ^ (2 * q) ∂normalizedBallLaw (cutoffFactor R.ballRadius R.barrierFn) Ψ ≤
        (∏ i ∈ Finset.range q, (4 * (i : ℝ) + 8 * R.params.bondWeightBound)) / (R.coupling * lam / 8) ^ q) ∧
      ∀ c : ChartBondIndex R.params.side u n,
        Integrable (fun k => |deriv R.barrierFn ‖k c‖| ^ 2) (normalizedBallLaw (cutoffFactor R.ballRadius R.barrierFn) Ψ) ∧
        ∫ k, |deriv R.barrierFn ‖k c‖| ^ 2 ∂normalizedBallLaw (cutoffFactor R.ballRadius R.barrierFn) Ψ ≤ Cr := by
  classical
  subst hp₀
  set s := coldSettingOver R V with hs
  have hρ : 0 < R.ballRadius := by
    unfold StepSettings.StepSetup.ballRadius
    positivity
  have hx0 : 0 < R.coupling := by linarith
  obtain ⟨Ψf, K, hgerm, hconv, -, -⟩ := hCM R lam Cc hσ hrt hx0 hlam n s s.potential hfull
  set e := freeBondsEquiv (R := R) u V hodd h2 with he
  have hcf : ∀ k, chartFreeCoords R u V k = reindexBonds e k := chartFreeCoords_eq_reindex u V hodd h2
  set Ψ : BondField (ChartBondIndex R.params.side u n) → ℝ := fun k => Ψf (reindexBonds e k) with hΨ
  have hΨ3 : ContDiff ℝ 3 Ψ := hconv.smooth.comp (reindexBonds e).contDiff
  have hΨd : Differentiable ℝ Ψf := hconv.smooth.differentiable (by norm_num)
  have hin : ∀ η : BondField s.free, (∀ b, ‖η b‖ ≤ R.ballRadius) → s.InBalls η := fun η h b => by
    rw [coordNorm_toImaginary]
    exact h b
  have hopen : ∀ η : BondField s.free, (∀ b, ‖η b‖ < R.ballRadius) → s.InBalls η := fun η h => hin η fun b => (h b).le
  have hd : IsPseudoMetricOnBonds s.bondDist := by
    refine ⟨fun b => ?_, fun b b' => ?_, fun b b' b'' => ?_⟩
    · simp [ChartSetting.bondDist, bondBlockDist, supDist_self]
    · simp only [ChartSetting.bondDist, bondBlockDist]
      rw [supDist_comm]
    · simp only [ChartSetting.bondDist, bondBlockDist]
      exact_mod_cast supDist_triangle _ _ _
  have hderiv : ∀ k : BondField (ChartBondIndex R.params.side u n), (∀ b, ‖k b‖ ≤ R.ballRadius) →
      fderiv ℝ Ψ k = fderiv ℝ (chartPotential R u V) k := by
    intro k hk
    refine Filter.EventuallyEq.fderiv_eq ?_
    have h1 := hgerm (reindexBonds e k) (hin _ fun b => hk _)
    have h3 := ((reindexBonds e).continuous.tendsto k).eventually h1
    filter_upwards [h3] with k' hk'
    show Ψf (reindexBonds e k') = s.potential (chartFreeCoords R u V k')
    rw [hcf]
    exact hk'
  have hfd : ∀ k v : BondField (ChartBondIndex R.params.side u n),
      fderiv ℝ Ψ k v = fderiv ℝ Ψf (reindexBonds e k) (reindexBonds e v) := fun k v => by
    have h1 : HasFDerivAt Ψ ((fderiv ℝ Ψf (reindexBonds e k)).comp (reindexBonds e)) k :=
      (hΨd (reindexBonds e k)).hasFDerivAt.comp k (reindexBonds e).hasFDerivAt
    rw [h1.fderiv]
    rfl
  have hdens : ∀ η, chartDensity s η = ballDensity (cutoffFactor R.ballRadius R.barrierFn) Ψf η := by
    intro η
    have e1 : s.cutoffProduct η = radialWeightProd (cutoffFactor R.ballRadius R.barrierFn) η := by
      unfold ChartSetting.cutoffProduct radialWeightProd
      exact Finset.prod_congr rfl fun b _ => by rw [coordNorm_toImaginary]
    unfold chartDensity ballDensity
    rw [e1]
    by_cases hz : ∀ b, ‖η b‖ < R.ballRadius
    · rw [(hgerm η (hopen η hz)).eq_of_nhds]
    · push Not at hz
      obtain ⟨b, hb⟩ := hz
      have h0' : radialWeightProd (cutoffFactor R.ballRadius R.barrierFn) η = 0 := by
        unfold radialWeightProd
        exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mpr hb])
      rw [h0']
      simp
  obtain ⟨hprob, hmean, hint, hae, hmeas, hnn, hI, hZ, -, -, -⟩ := hLw _ R.ballRadius R.barrierFn Ψ hρ hcut hΨ3.continuous
  set m := R.coupling * lam / 8 with hm
  have hm0 : 0 < m := by positivity
  have hs0 : ∀ (b : s.free) (v : BondVector), |bondPartialDeriv Ψf b 0 v| ≤ Real.sqrt m * ‖v‖ := by
    intro b v
    have ha : ∀ i : Fin 3,
        |fderiv ℝ Ψf 0 (ColdStepAtMirrorFrames.bondVariation b (EuclideanSpace.single i 1))| ≤ A := by
      intro i
      have h1 := h0 (i, e b)
      rw [← hderiv 0 (fun c => by simpa using hρ.le), hfd, map_zero] at h1
      have h3 : reindexBonds e (unitVariation (i, e b)) =
          ColdStepAtMirrorFrames.bondVariation b (EuclideanSpace.single i 1) := by
        have := reindexBonds_bondVariation e (e b) (EuclideanSpace.single i 1)
        simpa [unitVariation] using this
      rwa [h3] at h1
    have hA0 : 0 ≤ A := (abs_nonneg _).trans (ha 0)
    have h3 := abs_apply_le_of_basis_three
      ((fderiv ℝ Ψf 0).comp (ContinuousLinearMap.single ℝ (fun _ : s.free => BondVector) b)) hA0 (fun i => ha i) v
    exact le_trans h3 (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hsl : ∀ η : BondField s.free, (∀ b, ‖η b‖ < R.ballRadius) → ∀ (b : s.free) (v : BondVector),
      |bondPartialDeriv Ψf b η v| ≤ Cc * R.coupling * ‖v‖ := by
    intro η hη b v
    refine abs_bondPartialDeriv_le (fun X hX => ?_) v
    have h1 := hfull.firstDeriv_le η (hopen η hη) b X hX
    rw [← deriv_line_of_eventuallyEq hΨd (hgerm η (hopen η hη))]
    simpa only [update_add_smul_eq] using h1
  have hrim : IsRadialCutoff R.ballRadius (fun u => cutoffFactor R.ballRadius R.barrierFn (max u 0)) :=
    hRc R.ballRadius R.barrierFn hρ hcut
  have hmom : ∀ (q : ℕ) (c : ChartBondIndex R.params.side u n),
      ∫ k, ‖k c‖ ^ (2 * q) ∂normalizedBallLaw (cutoffFactor R.ballRadius R.barrierFn) Ψ ≤
      (∏ i ∈ Finset.range q, (4 * (i : ℝ) + 8 * R.params.bondWeightBound)) / m ^ q := by
    intro q c
    rw [hmean]
    have h1 := hMo s.free R.ballRadius m R.params.rt R.params.bondWeightBound s.bondDist Ψf K _ hρ hm0 hrt.le hrim hd hconv
      (fun b₀ => hW R hrt n s b₀) hs0 q (e.symm c)
    have h2 : ballExpectation (fun u => cutoffFactor R.ballRadius R.barrierFn (max u 0)) Ψf
          (fun η => ‖η (e.symm c)‖ ^ (2 * q)) =
        ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψ (fun k => ‖k c‖ ^ (2 * q)) := by
      have h3 : ballExpectation (fun u => cutoffFactor R.ballRadius R.barrierFn (max u 0)) Ψf
            (fun η => ‖η (e.symm c)‖ ^ (2 * q)) =
          ballExpectation (cutoffFactor R.ballRadius R.barrierFn) Ψf (fun η => ‖η (e.symm c)‖ ^ (2 * q)) := by
        unfold ballExpectation
        rw [ballDensity_cutoffFactor_max]
      rw [h3, ballExpectation_reindexBonds e]
      simp only [reindexBonds_apply, Equiv.apply_symm_apply]
      rfl
    rwa [h2] at h1
  have hrm : ∀ c : ChartBondIndex R.params.side u n,
      Integrable (fun k => |deriv R.barrierFn ‖k c‖| ^ 2) (normalizedBallLaw (cutoffFactor R.ballRadius R.barrierFn) Ψ) ∧
      ∫ k, |deriv R.barrierFn ‖k c‖| ^ 2 ∂normalizedBallLaw (cutoffFactor R.ballRadius R.barrierFn) Ψ ≤ Cr := by
    intro c
    have e8 : R.coupling * (lam / 2) / 4 = m := by
      rw [hm]
      ring
    obtain ⟨h2, h3⟩ := hCr s.free R.coupling R.params.rt s.bondDist Ψf K hx hrt.le hd (by rw [e8]; exact hconv)
      (fun b₀ => hW R hrt n s b₀) (fun b v => by rw [e8]; exact hs0 b v) hsl (e.symm c)
    simp only [iteratedDeriv_one] at h2 h3
    constructor
    · rw [hint]
      refine (integrable_reindexBonds e h2).congr (ae_of_all _ fun k => ?_)
      simp only [reindexBonds_apply, Equiv.apply_symm_apply]
      rw [← ballDensity_reindexBonds e]
    · rw [hmean]
      rw [ballExpectation_reindexBonds e] at h3
      simp only [reindexBonds_apply, Equiv.apply_symm_apply, pow_zero, inv_one, mul_one] at h3
      exact h3
  refine ⟨Ψ, hΨ3.of_le (by norm_num), ?_, fun k hk => hderiv k fun b => (hk b).le, hmom, hrm⟩
  intro Φ
  rw [hmean]
  unfold coldExpectation weightedMean ballExpectation
  rw [integral_reindexBonds e (fun η => Φ (freeCoordForm s η) * chartDensity s η),
    integral_reindexBonds e (fun η => chartDensity s η)]
  have hf : ∀ k : BondField (ChartBondIndex R.params.side u n), freeCoordForm s (reindexBonds e k) = chartColourForm k :=
    freeCoordForm_reindex u V hodd h2
  simp only [hdens, ← ballDensity_reindexBonds e, hf]
  rfl
end Chart
section Gauss
private def bilinearPair {κ : Type} [Fintype κ] (Bm : κ → κ → ℝ) (u v : κ → ℝ) : ℝ := ∑ b, ∑ b', u b * Bm b b' * v b'
private theorem eLpNorm_id_gaussianReal_scale (v : NNReal) (q : ENNReal) :
    eLpNorm id q (gaussianReal 0 v) = ENNReal.ofReal (Real.sqrt v) * eLpNorm id q (gaussianReal 0 1) := by
  have h := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt v)
  have h' : Measure.map (fun x => Real.sqrt v * x) (gaussianReal 0 1) = gaussianReal 0 v := by
    rw [h]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt v.2]
  rw [← h', eLpNorm_map_measure (measurable_id.aestronglyMeasurable) (by fun_prop)]
  have : (id ∘ fun x : ℝ => Real.sqrt v * x) = (Real.sqrt v) • (id : ℝ → ℝ) := by
    funext x
    simp
  rw [this, eLpNorm_const_smul]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
private theorem eLpNorm_coord_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι] {Sg : Matrix ι ι ℝ}
    (hp : Sg.PosSemidef) (i : ι) (q : ENNReal) :
    eLpNorm (fun η : EuclideanSpace ℝ ι => η i) q (multivariateGaussian 0 Sg) =
      ENNReal.ofReal (Real.sqrt (Sg i i)) * eLpNorm id q (gaussianReal 0 1) := by
  have h := measurePreserving_eval_multivariateGaussian (μ := 0) hp (i := i)
  have h0 : ((0 : EuclideanSpace ℝ ι)).ofLp i = 0 := rfl
  rw [h0] at h
  have e := eLpNorm_comp_measurePreserving (p := q) (g := (id : ℝ → ℝ)) measurable_id.aestronglyMeasurable h
  have e' : eLpNorm (fun η : EuclideanSpace ℝ ι => η i) q (multivariateGaussian 0 Sg) =
      eLpNorm id q (gaussianReal 0 (Sg i i).toNNReal) := e
  rw [e', eLpNorm_id_gaussianReal_scale, Real.coe_toNNReal _ (hp.diag_nonneg)]
abbrev _root_.YangMills.SharedProofs.p91446 := @eLpNorm_coord_multivariateGaussian
private theorem quadForm_blockDiagonal {κ : Type} [Fintype κ] [DecidableEq (Fin 3 × κ)]
    (Sg : Matrix (Fin 3 × κ) (Fin 3 × κ) ℝ) (σ : κ → κ → ℝ)
    (hS : ∀ e e' b b', Sg (e, b) (e', b') = if e = e' then σ b b' else 0) (y : Fin 3 × κ → ℝ) :
    y ⬝ᵥ Sg.mulVec y = ∑ e, bilinearPair σ (fun b => y (e, b)) (fun b => y (e, b)) := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, hS, bilinearPair, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 : ∀ z, (∑ w, if e = z then y (e, b) * (σ b w * y (z, w)) else 0) =
      if e = z then ∑ w, y (e, b) * (σ b w * y (z, w)) else 0 := fun z => by
    split_ifs <;> simp
  simp only [h2, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun w _ => by ring
abbrev _root_.YangMills.DeltaSharedProofs.p502266 := @quadForm_blockDiagonal
variable {a : ℝ} {L : ℕ} [NeZero L]
open Classical in
private theorem fluctuationCov_posSemidef {u n : ℕ} (hH : (trivialHessian a L u n).PosDef) :
    (fluctuationCov a L 1 u n).PosSemidef := by
  have hinv : ((trivialHessian a L u n)⁻¹).PosSemidef := hH.posSemidef.inv
  refine .of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext ⟨e, b⟩ ⟨e', b'⟩
    have hs := congrFun (congrFun hinv.isHermitian.eq b) b'
    simp only [Matrix.conjTranspose_apply, star_trivial] at hs
    simp only [Matrix.conjTranspose_apply, fluctuationCov, star_trivial, eq_comm (a := e')]
    rw [hs]
  · have hq := quadForm_blockDiagonal (κ := ChartBondIndex L u n) (fluctuationCov a L 1 u n)
      (fun b b' => (1 : ℝ)⁻¹ * (trivialHessian a L u n)⁻¹ b b') (fun e e' b b' => by simp [fluctuationCov]) x
    rw [star_trivial, hq]
    refine Finset.sum_nonneg fun e _ => ?_
    have := hinv.dotProduct_mulVec_nonneg (fun b => x (e, b))
    rw [star_trivial] at this
    have e1 : bilinearPair (fun b b' => (1 : ℝ)⁻¹ * (trivialHessian a L u n)⁻¹ b b') (fun b => x (e, b)) (fun b => x (e, b)) =
        (fun b => x (e, b)) ⬝ᵥ (trivialHessian a L u n)⁻¹.mulVec (fun b => x (e, b)) := by
      simp only [bilinearPair, dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
    rw [e1]
    exact this
abbrev _root_.YangMills.SharedProofs.p20571 := @fluctuationCov_posSemidef
variable {u m : ℕ} [NeZero m]
private theorem extendFluctuation_cases (e : Fin 3) (c : TorusBond (m * L)) :
    (∀ η : StepFluctuation L u m, extendFluctuation η e c = 0) ∨
      ∃ b : ChartBondIndex L u m, ∀ η : StepFluctuation L u m, extendFluctuation η e c = η (e, b) := by
  by_cases h : ∃ b : ChartBondIndex L u m, (torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth c.1, c.2) = b.1
  · obtain ⟨b, hb⟩ := h
    refine Or.inr ⟨b, fun η => ?_⟩
    simp only [extendFluctuation, extendChart]
    rw [Finset.sum_eq_single b]
    · rw [if_pos hb]
    · intro b' _ hne
      rw [if_neg]
      intro h'
      exact hne (Subtype.ext (h'.symm.trans hb))
    · simp
  · refine Or.inl fun η => ?_
    simp only [extendFluctuation, extendChart]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    exact fun h' => h ⟨b, h'⟩
abbrev _root_.YangMills.SharedProofs.p34049 := @extendFluctuation_cases
private theorem chartColourForm_cases (e : Fin 3) (c : TorusBond (m * L)) :
    (∀ k : BondField (ChartBondIndex L u m), chartColourForm k e c = 0) ∨
      ∃ b : ChartBondIndex L u m, ∀ k : BondField (ChartBondIndex L u m), chartColourForm k e c = k b e := by
  by_cases h : ∃ b : ChartBondIndex L u m, (torusSiteInFrame (torusFrame L u m) (torusFrame L u m).depth c.1, c.2) = b.1
  · obtain ⟨b, hb⟩ := h
    refine Or.inr ⟨b, fun k => ?_⟩
    simp only [chartColourForm, extendChart]
    rw [Finset.sum_eq_single b]
    · rw [if_pos hb]
    · intro b' _ hne
      rw [if_neg]
      intro h'
      exact hne (Subtype.ext (h'.symm.trans hb))
    · simp
  · refine Or.inl fun k => ?_
    simp only [chartColourForm, extendChart]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    exact fun h' => h ⟨b, h'⟩
private theorem eLpNorm_fluctuation_coord_le {lam : ℝ} {q : ENNReal} (hq : q ≠ ⊤) (hH : (trivialHessian a L u m).PosDef)
    (hb : ∀ b, (trivialHessian a L u m)⁻¹ b b ≤ 2 / lam) (i : Fin 3 × ChartBondIndex L u m) :
    eLpNorm (fun η : StepFluctuation L u m => η i) q (fluctuationGaussian a L 1 u m) ≤
      ENNReal.ofReal (Real.sqrt (2 / lam) * (eLpNorm id q (gaussianReal 0 1)).toReal) := by
  classical
  have hp := fluctuationCov_posSemidef (a := a) (L := L) (u := u) (n := m) hH
  have hfin : eLpNorm id q (gaussianReal 0 1) ≠ ⊤ := (memLp_id_gaussianReal' q hq).2.ne
  unfold fluctuationGaussian
  rw [eLpNorm_coord_multivariateGaussian hp, ENNReal.ofReal_mul (Real.sqrt_nonneg _), ENNReal.ofReal_toReal hfin]
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)) _
  obtain ⟨e, b⟩ := i
  simpa [fluctuationCov] using hb b
private theorem weightedCurvatureNorm_fluctuation_le {lam : ℝ} {q : ENNReal} (hq1 : 1 ≤ q) (hqt : q ≠ ⊤)
    (hH : (trivialHessian a L u m).PosDef) (hb : ∀ b, (trivialHessian a L u m)⁻¹ b b ≤ 2 / lam) :
    weightedCurvatureNorm (fluctuationGaussian a L 1 u m) (fun _ => 1) q extendFluctuation ≤
      ENNReal.ofReal (12 * (Real.sqrt (2 / lam) * (eLpNorm id q (gaussianReal 0 1)).toReal)) := by
  have hV : 0 ≤ Real.sqrt (2 / lam) * (eLpNorm id q (gaussianReal 0 1)).toReal := by positivity
  refine weightedCurvatureNorm_le_of_bonds hq1 hV (fun e c => ?_) (fun e c => ?_)
  · rcases extendFluctuation_cases (L := L) (u := u) (m := m) e c with h0 | ⟨b, h1⟩
    · have : (fun η : StepFluctuation L u m => extendFluctuation η e c) = 0 := funext h0
      rw [this]
      exact aestronglyMeasurable_zero
    · have : (fun η : StepFluctuation L u m => extendFluctuation η e c) = fun η => η (e, b) := funext h1
      rw [this]
      exact (EuclideanSpace.proj (𝕜 := ℝ) (e, b)).continuous.aestronglyMeasurable
  · rcases extendFluctuation_cases (L := L) (u := u) (m := m) e c with h0 | ⟨b, h1⟩
    · have : (fun η : StepFluctuation L u m => extendFluctuation η e c) = 0 := funext h0
      rw [this]
      simp
    · have : (fun η : StepFluctuation L u m => extendFluctuation η e c) = fun η => η (e, b) := funext h1
      rw [this]
      exact eLpNorm_fluctuation_coord_le hqt hH hb _
end Gauss
section Roots
variable {Ω : Type} [MeasurableSpace Ω]
private theorem eLpNorm_two_le_sqrt {μ : Measure Ω} {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hI : Integrable (fun x => f x ^ 2) μ) {K : ℝ} (hK : ∫ x, f x ^ 2 ∂μ ≤ K) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt K) := by
  have h := eLpNorm_le_of_integral_pow (Q := 2) (by norm_num) hf (by simpa [sq_abs] using hI) (by simpa [sq_abs] using hK)
  rw [Nat.cast_ofNat] at h
  have e : K ^ (((2 : ℕ) : ℝ)⁻¹) = Real.sqrt K := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rwa [e] at h
private theorem rpow_div_pow_inv (A x : ℝ) (hA : 0 ≤ A) (hx : 0 < x) (q : ℕ) (hq : 1 ≤ q) :
    (A / x ^ q) ^ (((2 * q : ℕ) : ℝ)⁻¹) = A ^ (((2 * q : ℕ) : ℝ)⁻¹) * x ^ (-(1 / 2) : ℝ) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    have : 0 < q := hq
    positivity
  rw [Real.div_rpow hA (by positivity), ← Real.rpow_natCast x q, ← Real.rpow_mul hx.le, div_eq_mul_inv,
    ← Real.rpow_neg hx.le]
  congr 2
  push_cast
  field_simp
private theorem sqrt_div_sq_eq {M xs l : ℝ} (hM : 0 ≤ M) (hx : 0 < xs) (hl : 0 < l) :
    Real.sqrt (M / (xs * (l / 16)) ^ 2) = Real.sqrt M * (16 / l) * xs⁻¹ := by
  rw [Real.sqrt_div hM, Real.sqrt_sq (by positivity)]
  field_simp
private theorem sqrt_div_eq {M xs l : ℝ} (hM : 0 ≤ M) (hx : 0 < xs) (hl : 0 < l) :
    Real.sqrt (M / (xs * (l / 16))) = Real.sqrt (M * (16 / l)) * (xs⁻¹ * xs ^ ((1 : ℝ) / 2)) := by
  have e : M / (xs * (l / 16)) = M * (16 / l) / xs := by
    field_simp
  rw [e, Real.sqrt_div (by positivity), ← Real.sqrt_eq_rpow]
  have h := Real.mul_self_sqrt hx.le
  have e2 : (Real.sqrt xs)⁻¹ = xs⁻¹ * Real.sqrt xs := by
    calc (Real.sqrt xs)⁻¹ = (Real.sqrt xs * Real.sqrt xs)⁻¹ * Real.sqrt xs := by field_simp
      _ = _ := by rw [h]
  rw [div_eq_mul_inv, e2]
variable {κ : Type} [Fintype κ]
private theorem integrable_norm_pow_of_ball {μ : Measure (BondField κ)} [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hae : ∀ᵐ k ∂μ, ∀ b, ‖k b‖ < ρ) (c : κ) (Q : ℕ) : Integrable (fun k : BondField κ => ‖k c‖ ^ Q) μ := by
  have hc : Continuous fun k : BondField κ => ‖k c‖ ^ Q := by fun_prop
  refine Integrable.mono' (integrable_const (ρ ^ Q)) hc.aestronglyMeasurable (hae.mono fun k hk => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hk c).le Q
private theorem eLpNorm_cutoffDeriv_le {μ : Measure (BondField κ)} (p : ℝ → ℝ) (b : κ) {Cr : ℝ}
    (h : Integrable (fun k : BondField κ => |deriv p ‖k b‖| ^ 2) μ ∧ ∫ k, |deriv p ‖k b‖| ^ 2 ∂μ ≤ Cr) :
    eLpNorm (fun k : BondField κ => |deriv p ‖k b‖|) 2 μ ≤ ENNReal.ofReal (Real.sqrt Cr) := by
  have hc : Continuous fun k : BondField κ => ‖k b‖ := by fun_prop
  have hm : AEStronglyMeasurable (fun k : BondField κ => |deriv p ‖k b‖|) μ :=
    (((measurable_deriv p).comp hc.measurable).norm).aestronglyMeasurable
  exact eLpNorm_two_le_sqrt (f := fun k : BondField κ => |deriv p ‖k b‖|) hm h.1 h.2
private theorem eLpNorm_norm_le_of_moment {μ : Measure (BondField κ)} [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hae : ∀ᵐ k ∂μ, ∀ b, ‖k b‖ < ρ) (c : κ) {Q : ℕ} (hQ : Q ≠ 0) {K : ℝ} (hK : ∫ k, ‖k c‖ ^ Q ∂μ ≤ K) :
    eLpNorm (fun k : BondField κ => ‖k c‖) (Q : ENNReal) μ ≤ ENNReal.ofReal (K ^ ((Q : ℝ)⁻¹)) := by
  have hc : Continuous fun k : BondField κ => ‖k c‖ := by fun_prop
  refine eLpNorm_le_of_integral_pow hQ hc.aestronglyMeasurable ?_ ?_
  · simpa using integrable_norm_pow_of_ball hρ hae c Q
  · simpa using hK
end Roots
section Small
private theorem settingOf_familyOf_allVacant {R : StepSetup} {n : ℕ} [NeZero n] (G : GasGround R n) :
    G.settingOf (G.familyOf G.allVacant) = G.groundSetting := by apply _root_.YangMills.SharedProofs.p14309 <;> assumption
private theorem mul_rpow_neg_quarter_lt (x σ : ℝ) (hσ : 0 < σ) (hx : (64 / σ + 1) ^ 4 ≤ x) :
    64 * x ^ (-(1 / 4) : ℝ) < 9 / 8 * σ := by apply _root_.YangMills.SharedProofs.p21801 <;> assumption
private theorem log_le_two_mul_sqrt (x : ℝ) (hx : 0 < x) : Real.log x ≤ 2 * x ^ ((1 : ℝ) / 2) := by
  have hs : 0 < x ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx _
  have h1 := Real.log_le_sub_one_of_pos hs
  rw [Real.log_rpow hx] at h1
  linarith
abbrev _root_.YangMills.SharedProofs.p12056 := @log_le_two_mul_sqrt
private theorem abs_cutoffRadialDeriv_le (p : ℝ → ℝ) (e v : BondVector) :
    |cutoffRadialDeriv p e v| ≤ |deriv p ‖e‖| * ‖v‖ := by
  unfold cutoffRadialDeriv
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  by_cases he : ‖e‖ = 0
  · rw [he, div_zero, abs_zero]
    positivity
  have hp : 0 < ‖e‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
  have := abs_real_inner_le_norm e v
  linarith [mul_comm ‖e‖ ‖v‖]
private theorem half_le_of_abs_sub_le_log {xs x cn : ℝ} (hx2 : 2 ≤ xs) (hcn : 0 ≤ cn) (hxn : 16 * cn ^ 2 ≤ xs)
    (hnear : |x - xs| ≤ cn * Real.log xs) : xs / 2 ≤ x := by
  have hx0 : 0 < xs := by linarith
  have hh0 : 0 < xs ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
  have hhh : xs ^ ((1 : ℝ) / 2) * xs ^ ((1 : ℝ) / 2) = xs := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hfloor : cn * Real.log xs ≤ xs / 2 := by
    have h1 := log_le_two_mul_sqrt xs hx0
    have h2 : 4 * cn ≤ xs ^ ((1 : ℝ) / 2) := by
      by_contra hc'
      push Not at hc'
      nlinarith
    nlinarith
  have := (abs_le.1 (le_trans hnear hfloor)).1
  linarith
abbrev _root_.YangMills.SharedProofs.p65497 := @half_le_of_abs_sub_le_log
private theorem drift_constant_le {c0 xs h K₁ K₂ sr D v r Sw SG : ℝ} (hc0 : 0 ≤ c0) (hx : 0 < xs) (hh : 0 < h)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hsr : 0 ≤ sr) (hD : 0 ≤ D) (hv : 0 ≤ v) (hr : 0 ≤ r) (hSw : Sw ≤ c0) (hSw0 : 0 ≤ Sw)
    (hSG : SG ≤ c0 * xs⁻¹) :
    c0 * xs⁻¹ + c0 * Sw * (K₂ * xs⁻¹) + c0 * (D * v) * Sw * (K₁ * (xs⁻¹ * h)) + SG * sr ≤
      (c0 * (1 + c0 * K₂ + sr) + c0 ^ 2 * K₁) * xs⁻¹ * (1 + (D + r) * h * v) := by
  have e1 : c0 * Sw * (K₂ * xs⁻¹) ≤ c0 * c0 * (K₂ * xs⁻¹) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSw hc0) (by positivity)
  have e2 : c0 * (D * v) * Sw * (K₁ * (xs⁻¹ * h)) ≤ c0 * (D * v) * c0 * (K₁ * (xs⁻¹ * h)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSw (by positivity)) (by positivity)
  have e3 : SG * sr ≤ c0 * xs⁻¹ * sr := mul_le_mul_of_nonneg_right hSG hsr
  have e4 : c0 * xs⁻¹ + c0 * c0 * (K₂ * xs⁻¹) + c0 * (D * v) * c0 * (K₁ * (xs⁻¹ * h)) + c0 * xs⁻¹ * sr ≤
      (c0 * (1 + c0 * K₂ + sr) + c0 ^ 2 * K₁) * xs⁻¹ * (1 + (D + r) * h * v) := by
    have t1 : 0 ≤ c0 * (1 + c0 * K₂ + sr) * xs⁻¹ * ((D + r) * h * v) := by positivity
    have t2 : 0 ≤ c0 ^ 2 * K₁ * xs⁻¹ := by positivity
    have t3 : 0 ≤ c0 ^ 2 * K₁ * xs⁻¹ * (r * h * v) := by positivity
    nlinarith
  linarith
end Small
section Requirements
variable {ι : Type} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 400000 in
private theorem eLpNorm_driftCoord_le {μ : Measure (BondField ι)} [IsProbabilityMeasure μ] {ρ : ℝ}
    (hae : ∀ᵐ k ∂μ, ∀ b, ‖k b‖ < ρ) (p : ℝ → ℝ) (Ψ U : BondField ι → ℝ)
    (G : Matrix (Fin 3 × ι) (Fin 3 × ι) ℝ) (j : Fin 3 × ι) (w : ι → ℝ) (hw0 : ∀ b, 0 ≤ w b) {c0 xs Dv F1 F2 F3 : ℝ}
    (hc0 : 0 ≤ c0) (hx : 0 < xs) (hDv : 0 ≤ Dv) (hF1 : 0 ≤ F1) (hF2 : 0 ≤ F2) (hF3 : 0 ≤ F3)
    (hder : ∀ k : BondField ι, (∀ b, ‖k b‖ < ρ) → fderiv ℝ Ψ k = fderiv ℝ U k)
    (hbd : ∀ k : BondField ι, (∀ b, ‖k b‖ < ρ) → |∑ i, G j i * fderiv ℝ U k (unitVariation i) - k j.2 j.1| ≤
      c0 * xs⁻¹ * (1 + xs * ∑ b, w b * (‖k b‖ ^ 2 + Dv * ‖k b‖)))
    (h1 : ∀ b, eLpNorm (fun k : BondField ι => ‖k b‖ ^ 2) 2 μ ≤ ENNReal.ofReal F1)
    (h2 : ∀ b, eLpNorm (fun k : BondField ι => ‖k b‖) 2 μ ≤ ENNReal.ofReal F2)
    (h3 : ∀ b, eLpNorm (fun k : BondField ι => |deriv p ‖k b‖|) 2 μ ≤ ENNReal.ofReal F3) :
    eLpNorm (fun k => driftCoord G p Ψ k j) 2 μ ≤
      ENNReal.ofReal (c0 * xs⁻¹ + c0 * (∑ b, w b) * F1 + c0 * Dv * (∑ b, w b) * F2 + (∑ i, |G j i|) * F3) := by
  classical
  have hmc : ∀ b, Continuous fun k : BondField ι => ‖k b‖ := fun b => by fun_prop
  have hmd : ∀ b, AEStronglyMeasurable (fun k : BondField ι => |deriv p ‖k b‖|) μ := fun b =>
    (((measurable_deriv p).comp (hmc b).measurable).norm).aestronglyMeasurable
  set f0 : BondField ι → ℝ := fun _ => c0 * xs⁻¹ with hf0
  set f1 : BondField ι → ℝ := fun k => ∑ b, (c0 * w b) * ‖k b‖ ^ 2 with hf1
  set f2 : BondField ι → ℝ := fun k => ∑ b, (c0 * Dv * w b) * ‖k b‖ with hf2
  set f3 : BondField ι → ℝ := fun k => ∑ i : Fin 3 × ι, |G j i| * |deriv p ‖k i.2‖| with hf3
  have t0 : eLpNorm f0 2 μ ≤ ENNReal.ofReal (c0 * xs⁻¹) := by
    have hn : 0 ≤ c0 * xs⁻¹ := by positivity
    have := eLpNorm_two_le_sqrt (μ := μ) (f := f0) aestronglyMeasurable_const
      (by simp only [hf0]; exact integrable_const _) (K := (c0 * xs⁻¹) ^ 2) (by simp [hf0])
    rwa [Real.sqrt_sq hn] at this
  have hm1 : ∀ b, AEStronglyMeasurable (fun k : BondField ι => ‖k b‖ ^ 2) μ := fun b =>
    ((hmc b).pow 2).aestronglyMeasurable
  have t1 : eLpNorm f1 2 μ ≤ ENNReal.ofReal (∑ b, (c0 * w b) * F1) := by
    have := eLpNorm_weighted_sum_le (μ := μ) (fun b => c0 * w b) (fun _ => F1) (fun (b : ι) (k : BondField ι) => ‖k b‖ ^ 2)
      (fun b => mul_nonneg hc0 (hw0 b)) (fun _ => hF1) hm1 h1
    exact this
  have t2 : eLpNorm f2 2 μ ≤ ENNReal.ofReal (∑ b, (c0 * Dv * w b) * F2) := by
    have := eLpNorm_weighted_sum_le (μ := μ) (fun b => c0 * Dv * w b) (fun _ => F2) (fun (b : ι) (k : BondField ι) => ‖k b‖)
      (fun b => mul_nonneg (mul_nonneg hc0 hDv) (hw0 b)) (fun _ => hF2) (fun b => (hmc b).aestronglyMeasurable) h2
    exact this
  have t3 : eLpNorm f3 2 μ ≤ ENNReal.ofReal (∑ i : Fin 3 × ι, |G j i| * F3) := by
    have := eLpNorm_weighted_sum_le (μ := μ) (fun i : Fin 3 × ι => |G j i|) (fun _ => F3)
      (fun (i : Fin 3 × ι) (k : BondField ι) => |deriv p ‖k i.2‖|) (fun _ => abs_nonneg _) (fun _ => hF3)
      (fun i => hmd i.2) (fun i => h3 i.2)
    exact this
  have m0 : AEStronglyMeasurable f0 μ := aestronglyMeasurable_const
  have m1 : AEStronglyMeasurable f1 μ :=
    (Finset.aestronglyMeasurable_fun_sum _ fun b _ => (((hmc b).pow 2).aestronglyMeasurable.const_mul _))
  have m2 : AEStronglyMeasurable f2 μ :=
    (Finset.aestronglyMeasurable_fun_sum _ fun b _ => ((hmc b).aestronglyMeasurable.const_mul _))
  have m3 : AEStronglyMeasurable f3 μ :=
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ => ((hmd i.2).const_mul _))
  have hpt : ∀ᵐ k ∂μ, ‖driftCoord G p Ψ k j‖ ≤ (((f0 + f1) + f2) + f3) k := by
    filter_upwards [hae] with k hk
    have e1 : driftCoord G p Ψ k j = (∑ i, G j i * fderiv ℝ U k (unitVariation i) - k j.2 j.1) +
        ∑ i, G j i * cutoffRadialDeriv p (k i.2) (EuclideanSpace.single i.1 1) := by
      unfold driftCoord MomentMethod.gradientCoord
      rw [hder k hk]
      simp only [mul_add, Finset.sum_add_distrib]
      ring
    have e2 : |∑ i, G j i * cutoffRadialDeriv p (k i.2) (EuclideanSpace.single i.1 1)| ≤ f3 k := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := abs_cutoffRadialDeriv_le p (k i.2) (EuclideanSpace.single i.1 1)
      simpa using this
    have e3 : c0 * xs⁻¹ * (1 + xs * ∑ b, w b * (‖k b‖ ^ 2 + Dv * ‖k b‖)) = f0 k + f1 k + f2 k := by
      simp only [hf0, hf1, hf2, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      have hxx : xs⁻¹ * xs = 1 := inv_mul_cancel₀ hx.ne'
      have : ∀ b, c0 * xs⁻¹ * (xs * (w b * ‖k b‖ ^ 2)) = c0 * w b * ‖k b‖ ^ 2 := fun b => by
        calc _ = c0 * (xs⁻¹ * xs) * (w b * ‖k b‖ ^ 2) := by ring
          _ = _ := by rw [hxx]; ring
      have h' : ∀ b, c0 * xs⁻¹ * (xs * (w b * (Dv * ‖k b‖))) = c0 * Dv * w b * ‖k b‖ := fun b => by
        calc _ = c0 * (xs⁻¹ * xs) * (w b * (Dv * ‖k b‖)) := by ring
          _ = _ := by rw [hxx]; ring
      simp only [this, h']
      ring
    rw [e1, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    have := hbd k hk
    rw [e3] at this
    show _ ≤ f0 k + f1 k + f2 k + f3 k
    linarith
  refine (eLpNorm_mono_ae_real hpt).trans ?_
  refine (eLpNorm_add_le ((m0.add m1).add m2) m3 (by norm_num)).trans ?_
  refine (add_le_add (eLpNorm_add_le (m0.add m1) m2 (by norm_num)) t3).trans ?_
  refine (add_le_add (add_le_add (eLpNorm_add_le m0 m1 (by norm_num)) t2) le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add t0 t1) le_rfl) le_rfl).trans ?_
  have n0 : 0 ≤ c0 * xs⁻¹ := by positivity
  have n1 : 0 ≤ ∑ b, (c0 * w b) * F1 := Finset.sum_nonneg fun b _ => mul_nonneg (mul_nonneg hc0 (hw0 b)) hF1
  have n2 : 0 ≤ ∑ b, (c0 * Dv * w b) * F2 :=
    Finset.sum_nonneg fun b _ => mul_nonneg (mul_nonneg (mul_nonneg hc0 hDv) (hw0 b)) hF2
  have n3 : 0 ≤ ∑ i : Fin 3 × ι, |G j i| * F3 := Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) hF3
  rw [← ENNReal.ofReal_add n0 n1, ← ENNReal.ofReal_add (add_nonneg n0 n1) n2,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg n0 n1) n2) n3]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
end Requirements
section ChartCurvature
variable {L u m : ℕ} [NeZero L] [NeZero m]
private theorem weightedCurvatureNorm_chartColourForm_le {μ : Measure (BondField (ChartBondIndex L u m))}
    [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hae : ∀ᵐ k ∂μ, ∀ b, ‖k b‖ < ρ) {q : ℕ} (hq : 1 ≤ q) {K : ℝ}
    (hK : ∀ c, ∫ k, ‖k c‖ ^ (2 * q) ∂μ ≤ K) (hK0 : 0 ≤ K) :
    weightedCurvatureNorm μ (fun _ => 1) (q : ENNReal) (fun k => chartColourForm k) ≤
      ENNReal.ofReal (12 * K ^ (((2 * q : ℕ) : ℝ)⁻¹)) := by
  have hq1 : (1 : ENNReal) ≤ (q : ENNReal) := by exact_mod_cast hq
  refine weightedCurvatureNorm_le_of_bonds hq1 (by positivity) (fun e c => ?_) (fun e c => ?_)
  · rcases chartColourForm_cases (L := L) (u := u) (m := m) e c with h0 | ⟨b, h1⟩
    · have : (fun k : BondField (ChartBondIndex L u m) => chartColourForm k e c) = 0 := funext h0
      rw [this]
      exact aestronglyMeasurable_zero
    · have : (fun k : BondField (ChartBondIndex L u m) => chartColourForm k e c) = fun k => k b e := funext h1
      rw [this]
      have hc : Continuous fun k : BondField (ChartBondIndex L u m) => k b e :=
        (EuclideanSpace.proj (𝕜 := ℝ) e).continuous.comp (continuous_apply b)
      exact hc.aestronglyMeasurable
  · rcases chartColourForm_cases (L := L) (u := u) (m := m) e c with h0 | ⟨b, h1⟩
    · have : (fun k : BondField (ChartBondIndex L u m) => chartColourForm k e c) = 0 := funext h0
      rw [this]
      simp
    · have : (fun k : BondField (ChartBondIndex L u m) => chartColourForm k e c) = fun k => k b e := funext h1
      rw [this]
      have hc : Continuous fun k : BondField (ChartBondIndex L u m) => ‖k b‖ := by fun_prop
      have s1 : eLpNorm (fun k : BondField (ChartBondIndex L u m) => k b e) (q : ENNReal) μ ≤
          eLpNorm (fun k : BondField (ChartBondIndex L u m) => ‖k b‖) (q : ENNReal) μ :=
        eLpNorm_mono_real fun k => by simpa using PiLp.norm_apply_le (k b) e
      have s2 : eLpNorm (fun k : BondField (ChartBondIndex L u m) => ‖k b‖) (q : ENNReal) μ ≤
          eLpNorm (fun k : BondField (ChartBondIndex L u m) => ‖k b‖) ((2 * q : ℕ) : ENNReal) μ :=
        eLpNorm_le_eLpNorm_of_exponent_le (by exact_mod_cast (by omega : q ≤ 2 * q)) hc.aestronglyMeasurable
      exact s1.trans (s2.trans (eLpNorm_norm_le_of_moment hρ hae b (by omega) (hK b)))
end ChartCurvature
end GoodStateColdLaw
set_option maxHeartbeats 2000000 in
open GoodStateColdLaw in
theorem goodStateColdLaw (hSl : potentialGradientBoundsStatement)
    (hFl : gaussianChainFluctuationsStatement) (hHess : stepHessianPosDefStatement)
    (hCutS : goodConfigCutoffStatement) (hWin : scaleWindowStatement)
    (hCv : SettingsUniformlyConvex) (hConf : GasConfigIsAdmissibleSetting)
    (hCM : ChartPotentialConvex) (hMo : GaussianMomentBound)
    (hRm : cutoffDerivMomentsStatement) (hW : FreeBondWeightsSummable)
    (hRc : CutoffFactorIsRadialCutoff) (hLw : normalizedBallLawIsProbabilityStatement) : goodStateColdLawStatement := by
  unfold potentialGradientBoundsStatement ForAllPoints at hSl
  unfold gaussianChainFluctuationsStatement ForAllPoints at hFl
  unfold goodConfigCutoffStatement ForAllPoints at hCutS
  unfold scaleWindowStatement ForAllPoints at hWin
  unfold goodStateColdLawStatement ForAllPoints
  refine forAllParameters_mono (forAllParameters_and forAllParameters_admissible
    (forAllParameters_and (forAllParameters_of_holdsOnAllParameters hHess) (forAllParameters_and (forAllParameters_settings hCv hConf)
    (forAllParameters_and hSl (forAllParameters_and hFl (forAllParameters_and hCutS hWin)))))) ?_
  rintro Λ ⟨hD, hH, ⟨Cc, hCc, hB, hy0, hFull, hSet⟩, ⟨Cs, _, Xs, _, hys, hsl⟩, ⟨_, cf, Xf, _, _, hfl⟩,
    ⟨_, _, Xc, _, hyc, hcutS⟩, ⟨Cw, _, Xw, _, _, hwin⟩⟩
  have hlam : 0 < Λ.table.lam := hD.chain.2.2.1
  have hσ : 0 < Λ.stepParams.threshold := hD.σ_pos
  have hrt : 0 < Λ.stepParams.rt := hD.rt_pos
  have hρ0 : 0 < Λ.stepParams.threshold / 64 := by positivity
  have hcutT : IsCutoff (Λ.stepParams.threshold / 64) Λ.table.cutoff := hD.cut
  have hW0 : 0 ≤ Λ.stepParams.bondWeightBound := by
    unfold TorusLumps.StepParameters.bondWeightBound TorusLumps.StepParameters.blockBondBound
    positivity
  obtain ⟨Cr, hCr0, hCr⟩ := hRm (Λ.stepParams.threshold / 64) Λ.table.cutoff (Λ.table.lam / 2) Cc Λ.stepParams.bondWeightBound hρ0 hcutT
    (by positivity) hCc.le hW0 1 2 0 le_rfl (by norm_num)
  set lam := Λ.table.lam with hlamd
  set Mq : ℕ → ℝ := fun q => ∏ i ∈ Finset.range q, (4 * (i : ℝ) + 8 * Λ.stepParams.bondWeightBound) with hMqd
  have hMq : ∀ q, 0 ≤ Mq q := fun q => Finset.prod_nonneg fun i _ => by positivity
  set c0 := |Cs 0| with hc0
  set cn := |Cw 0| with hcn
  set K₁ := Real.sqrt (Mq 1 * (16 / lam)) with hK₁
  set K₂ := Real.sqrt (Mq 2) * (16 / lam) with hK₂
  set Kd := c0 * (1 + c0 * K₂ + Real.sqrt Cr) + c0 ^ 2 * K₁ with hKd
  set Cq : ℕ → ℝ := fun q => if q = 0 then Kd else
    max (12 * (Real.sqrt (2 / lam) * (eLpNorm id (q : ENNReal) (gaussianReal 0 1)).toReal))
      (12 * (Mq q * (16 / lam) ^ q) ^ (((2 * q : ℕ) : ℝ)⁻¹)) with hCqd
  refine ⟨Cq, 1, max (max (max Xs Xc) (max Xw 2))
      (max ((64 / Λ.stepParams.threshold + 1) ^ 4) (max (16 * cn ^ 2) (16 * (3 * c0) ^ 2 / lam))),
    one_pos, le_trans hys (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))), ?_⟩
  intro S hx d n _ hd hn
  have hxs : Xs ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxc : Xc ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxw : Xw ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hx2 : 2 ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hx64 : (64 / Λ.stepParams.threshold + 1) ^ 4 ≤ S.scaleCoupling := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxn : 16 * cn ^ 2 ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hxa : 16 * (3 * c0) ^ 2 / lam ≤ S.scaleCoupling :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hx0 : 0 < S.scaleCoupling := by linarith
  obtain ⟨-, -, -, -, -, hKle, hwn⟩ := hwin S hxw
  have hnear := (hwn (S.lastSeparated + d) (by omega) (by omega)).1
  have hcn0 : 0 ≤ cn := abs_nonneg _
  have hlog0 : 0 ≤ Real.log S.scaleCoupling := Real.log_nonneg (by linarith)
  have hnear' : |S.coupling (S.lastSeparated + d) - S.scaleCoupling| ≤ cn * Real.log S.scaleCoupling :=
    le_trans hnear (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0)
  have hhalf : S.scaleCoupling / 2 ≤ S.coupling (S.lastSeparated + d) := half_le_of_abs_sub_le_log hx2 hcn0 hxn hnear'
  have hh0 : 0 < S.scaleCoupling ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
  have hK : S.lastSeparated + d ≤ S.data.windowLevel := by omega
  have hstand : StageOnFlow Λ.table Λ.response Λ.floor S.β (S.lastSeparated + d)
      ⟨S.tower.stage (S.lastSeparated + d), S.resp (S.lastSeparated + d)⟩ := by
    have h := S.onFlow (S.lastSeparated + d) hK
    rwa [← S.stage_eq (S.lastSeparated + d) hK] at h
  have hon : (S.tower.stage (S.lastSeparated + d)).toStepSetup.OnParameters Λ.table Λ.floor := hstand.onFamily.onFamily
  have hmv : |(S.tower.stage (S.lastSeparated + d)).toStepSetup.nextCoupling -
      (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling| ≤ 2 * Λ.table.B := hstand.onFamily.abs_sub_le
  have hxx : (S.tower.stage (S.lastSeparated + d)).toStepSetup.nextCoupling ≤
      1.01 * (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling := by
    have h1 := (abs_le.mp hmv).2
    have h2 := hon.le_coupling
    linarith only [h1, h2, hB, hy0]
  have hRx : (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling = S.coupling (S.lastSeparated + d) :=
    hstand.coupling_eq
  have hLge : 2 ^ 40 ≤ Λ.stepParams.side := hD.L_ge
  have hside : Λ.table.n₀ ≤ n := by
    have h1 : Λ.stepParams.side * Λ.stepParams.n₀ ≤ S.data.period Λ.stepParams.side := S.side_le
    have h2 : S.data.period Λ.stepParams.side ≤ n := by
      rw [hn]
      exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
    have h3 : Λ.stepParams.n₀ ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.le_mul_of_pos_left _ (by omega)
    exact h3.trans (h1.trans h2)
  have hn₀ : 4096 ≤ Λ.table.n₀ := hD.n₀_ge
  have h64 : 64 ≤ n := by omega
  have h2n : 2 ≤ n := by omega
  have hHn : (trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n).PosDef := hH (S.lastSeparated + d) n hside
  refine ⟨fluctuationCov_posSemidef hHn, ?_, ?_⟩
  · intro q hq
    have hq0 : q ≠ 0 := by omega
    have hdiag : ∀ b, (trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ b b ≤ 2 / lam := fun b => by
      have h1 := (hfl S).2 (S.lastSeparated + d) n h64 b b
      have h2 := le_abs_self ((trivialHessian Λ.stepParams.coupling Λ.stepParams.side (S.lastSeparated + d) n)⁻¹ b b)
      refine h2.trans (h1.trans (le_of_eq ?_))
      simp only [supDist_self]
      simp
      rfl
    refine (weightedCurvatureNorm_fluctuation_le (lam := lam) (by exact_mod_cast hq) (ENNReal.natCast_ne_top q) hHn hdiag).trans
      (ENNReal.ofReal_le_ofReal ?_)
    simp only [hCqd, if_neg hq0]
    exact le_max_left _ _
  intro V Y hg
  have hcold : IsCold (9 / 8 * Λ.stepParams.threshold) (S.smoothedField (S.lastSeparated + d + 1) n V) := by
    intro z μ ν hμ
    obtain ⟨-, -, h3, -⟩ := hcutS S
      (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx |> fun h => h)
      (S.lastSeparated + d + 1) (by omega) (by omega) n hn V Y hg
    have h4 := h3 1 zero_le_one le_rfl z μ ν hμ
    have h5 := mul_rpow_neg_quarter_lt S.scaleCoupling Λ.stepParams.threshold hσ hx64
    have h6 := hg.curvature_le
    exact lt_of_le_of_lt (h4.trans (by linarith only [h6])) h5
  have hgr : (coldGroundOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
      (S.smoothedField (S.lastSeparated + d + 1) n V)).IsAdmissibleGround :=
    Or.inl ⟨hside, hcold, rfl, rfl, rfl⟩
  have hset : (coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
      (S.smoothedField (S.lastSeparated + d + 1) n V)).IsAdmissible := by
    have h := hSet _ hon hxx n _ hgr (GasGround.allVacant _) (fun i j _ => GasGround.pairConstraint _ |>.vacant_compatible i j _)
    have e : (coldGroundOver (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.smoothedField (S.lastSeparated + d + 1) n V)).settingOf
        ((coldGroundOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
          (S.smoothedField (S.lastSeparated + d + 1) n V)).familyOf (GasGround.allVacant _)) =
        (coldGroundOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
          (S.smoothedField (S.lastSeparated + d + 1) n V)).groundSetting := settingOf_familyOf_allVacant _
    rwa [e] at h
  have hfull := hFull _ hon n hside _ hset
  obtain ⟨h0, hj⟩ := hsl S hxs d n hd hn V Y hg
  have hRx1 : 1 ≤ (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling := by
    rw [hRx]
    linarith
  have hmge : S.scaleCoupling * (lam / 16) ≤ (S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling * lam / 8 := by
    rw [hRx]
    have := mul_le_mul_of_nonneg_right hhalf (by positivity : 0 ≤ lam / 8)
    linarith
  have hA : 3 * c0 ≤ Real.sqrt ((S.tower.stage (S.lastSeparated + d)).toStepSetup.coupling * lam / 8) := by
    refine Real.le_sqrt_of_sq_le (le_trans ?_ hmge)
    have h1 := (div_le_iff₀ hlam).1 hxa
    linarith
  have hcutR : IsCutoff (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius
      (S.tower.stage (S.lastSeparated + d)).toStepSetup.barrierFn := by
    have e : (S.tower.stage (S.lastSeparated + d)).toStepSetup.barrierFn = Λ.table.cutoff := hon.barrierFn_eq
    rw [e]
    exact hcutT
  obtain ⟨Ψ, hC1, hrepr, hder, hmom, hrm⟩ := chartLaw_exists hCM hMo hW hRc hLw (S.lastSeparated + d)
    (S.smoothedField (S.lastSeparated + d + 1) n V)
    (R := (S.tower.stage (S.lastSeparated + d)).toStepSetup) (lam := lam) (Cc := Cc) (A := c0) (Cr := Cr) hD.L_odd h2n
    hon.barrierFn_eq hσ hrt hRx1 hlam hCc.le hcutR hfull hA (fun j => (h0 j).trans (le_abs_self _)) hCr
  have hρR : 0 < (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius := hρ0
  obtain ⟨hprob, -, hint, hae, -, -, -, -, -, -, -⟩ := hLw _ _ _ Ψ hρR hcutR hC1.continuous
  refine ⟨_, _, Ψ, hρR, hcutR, hC1, hrepr, ?_, ?_⟩
  · intro q hq
    have hq0 : q ≠ 0 := by omega
    have hm₀ : 0 < S.scaleCoupling * (lam / 16) := by positivity
    have hA0 : 0 ≤ Mq q * (16 / lam) ^ q := mul_nonneg (hMq q) (by positivity)
    have hK : ∀ c, ∫ k, ‖k c‖ ^ (2 * q) ∂normalizedBallLaw (cutoffFactor (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius
        (S.tower.stage (S.lastSeparated + d)).toStepSetup.barrierFn) Ψ ≤ (Mq q * (16 / lam) ^ q) / S.scaleCoupling ^ q := by
      intro c
      refine (hmom q c).trans ?_
      have e : (Mq q * (16 / lam) ^ q) / S.scaleCoupling ^ q = Mq q / (S.scaleCoupling * (lam / 16)) ^ q := by
        have e1 : 16 / lam = (lam / 16)⁻¹ := by rw [inv_div]
        rw [e1, inv_pow, mul_pow]
        field_simp
      rw [e]
      exact div_le_div_of_nonneg_left (hMq q) (pow_pos hm₀ q) (pow_le_pow_left₀ hm₀.le hmge q)
    have h1 := weightedCurvatureNorm_chartColourForm_le (L := Λ.stepParams.side) (u := S.lastSeparated + d) (m := n) hρR hae hq hK
      (div_nonneg hA0 (by positivity))
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [rpow_div_pow_inv _ _ hA0 hx0 q hq]
    simp only [hCqd, if_neg hq0]
    have hp : 0 ≤ S.scaleCoupling ^ (-(1 / 2) : ℝ) := by positivity
    calc 12 * ((Mq q * (16 / lam) ^ q) ^ (((2 * q : ℕ) : ℝ)⁻¹) * S.scaleCoupling ^ (-(1 / 2) : ℝ))
        = (12 * (Mq q * (16 / lam) ^ q) ^ (((2 * q : ℕ) : ℝ)⁻¹)) * S.scaleCoupling ^ (-(1 / 2) : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hp
  · intro j
    obtain ⟨w, hw0, hwsum, hGs, hbd⟩ := hj j
    have hSw0 : 0 ≤ ∑ b, w b := Finset.sum_nonneg fun b _ => hw0 b
    have hC0 : 0 ≤ Cs 0 := hSw0.trans hwsum
    have hCe : Cs 0 = c0 := (abs_of_nonneg hC0).symm
    rw [hCe] at hwsum hGs hbd
    have hc00 : 0 ≤ c0 := abs_nonneg _
    have hv : 0 ≤ S.localCurvature (S.lastSeparated + d + 1) n V := Real.iSup_nonneg fun _ => norm_nonneg _
    have hm₀ : 0 < S.scaleCoupling * (lam / 16) := by positivity
    have hmr : ∀ (Q : ℕ) (b : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n),
        Integrable (fun k : BondField (ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n) => ‖k b‖ ^ Q)
        (normalizedBallLaw (cutoffFactor (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius
          (S.tower.stage (S.lastSeparated + d)).toStepSetup.barrierFn) Ψ) :=
      fun Q b => integrable_norm_pow_of_ball hρR hae b Q
    have hcn' : ∀ b : ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n,
        Continuous fun k : BondField (ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n) => ‖k b‖ :=
      fun b => by fun_prop
    have f1 : ∀ b, eLpNorm (fun k : BondField (ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n) => ‖k b‖ ^ 2) 2
        (normalizedBallLaw (cutoffFactor (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius
          (S.tower.stage (S.lastSeparated + d)).toStepSetup.barrierFn) Ψ) ≤ ENNReal.ofReal (K₂ * S.scaleCoupling⁻¹) := by
      intro b
      have e4 : ∀ k : BondField (ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n), (‖k b‖ ^ 2) ^ 2 = ‖k b‖ ^ (2 * 2) :=
        fun k => (pow_mul _ 2 2).symm
      have h1 := eLpNorm_two_le_sqrt (f := fun k : BondField (ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n) => ‖k b‖ ^ 2)
        ((hcn' b).pow 2).aestronglyMeasurable
        (by simpa only [e4] using hmr (2 * 2) b) (K := Mq 2 / (S.scaleCoupling * (lam / 16)) ^ 2) (by
          simp only [e4]
          refine (hmom 2 b).trans ?_
          exact div_le_div_of_nonneg_left (hMq 2) (pow_pos hm₀ 2) (pow_le_pow_left₀ hm₀.le hmge 2))
      rwa [sqrt_div_sq_eq (hMq 2) hx0 hlam] at h1
    have f2 : ∀ b, eLpNorm (fun k : BondField (ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n) => ‖k b‖) 2
        (normalizedBallLaw (cutoffFactor (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius
          (S.tower.stage (S.lastSeparated + d)).toStepSetup.barrierFn) Ψ) ≤
        ENNReal.ofReal (K₁ * (S.scaleCoupling⁻¹ * S.scaleCoupling ^ ((1 : ℝ) / 2))) := by
      intro b
      have h1 := eLpNorm_two_le_sqrt (f := fun k : BondField (ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n) => ‖k b‖)
        (hcn' b).aestronglyMeasurable (hmr 2 b) (K := Mq 1 / (S.scaleCoupling * (lam / 16))) (by
          have h3 := hmom 1 b
          simp only [mul_one, pow_one] at h3
          refine h3.trans ?_
          exact div_le_div_of_nonneg_left (hMq 1) hm₀ hmge)
      rwa [sqrt_div_eq (hMq 1) hx0 hlam] at h1
    have f3 : ∀ b, eLpNorm (fun k : BondField (ChartBondIndex Λ.stepParams.side (S.lastSeparated + d) n) =>
        |deriv (S.tower.stage (S.lastSeparated + d)).toStepSetup.barrierFn ‖k b‖|) 2
        (normalizedBallLaw (cutoffFactor (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius
          (S.tower.stage (S.lastSeparated + d)).toStepSetup.barrierFn) Ψ) ≤ ENNReal.ofReal (Real.sqrt Cr) := fun b =>
      eLpNorm_cutoffDeriv_le _ b (hrm b)
    have hmain := eLpNorm_driftCoord_le hae (S.tower.stage (S.lastSeparated + d)).toStepSetup.barrierFn Ψ
      (chartPotential (S.tower.stage (S.lastSeparated + d)).toStepSetup (S.lastSeparated + d)
        (S.smoothedField (S.lastSeparated + d + 1) n V)) _ j w hw0 hc00 hx0
      (mul_nonneg (by positivity) hv) (by positivity) (by positivity) (Real.sqrt_nonneg _) hder hbd f1 f2 f3
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    have hq : Cq 0 = Kd := by simp [hCqd]
    rw [hq]
    exact drift_constant_le hc00 hx0 hh0 (Real.sqrt_nonneg _) (by positivity) (Real.sqrt_nonneg _) (by positivity) hv
      (Nat.cast_nonneg _) hwsum hSw0 hGs
end MomentLaw
end YangMills.Construction
end
