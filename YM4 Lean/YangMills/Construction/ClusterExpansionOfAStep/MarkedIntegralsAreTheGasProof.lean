import YangMills.Construction.ClusterExpansionOfAStep.ColdGroundOfTheFlatFieldProof
import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.ConfigurationsOfTheGasAreSettings
import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.ImageAtAGroundIsTheSumOverTheGas
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsSmoothOffItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreTheGas
import YangMills.Construction.ClusterExpansionOfAStep.MassOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames Dobrushin StepSettings StepGas StepCosts TorusFields
  TorusLumps MarkedIntegrals RenormalizationStepParameters
namespace ClusterExpansionOfAStep
namespace ColdGasIdentity
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem sum_powerset_prod_complement_eq_one {B : Type} [DecidableEq B] (M : Finset B) (m : B → ℝ) :
    ∑ bad ∈ M.powerset, ∏ b ∈ M, (if b ∈ bad then 1 - m b else m b) = 1 := by
  have h := Finset.prod_add (fun b => 1 - m b) m M
  have h1 : ∏ i ∈ M, ((1 - m i) + m i) = 1 := Finset.prod_eq_one fun i _ => by ring
  rw [h1] at h
  refine Eq.trans ?_ h.symm
  refine Finset.sum_congr rfl fun t ht => ?_
  have hsub := Finset.mem_powerset.mp ht
  rw [← Finset.prod_sdiff hsub, mul_comm]
  congr 1
  · exact Finset.prod_congr rfl fun b hb => by simp [hb]
  · exact Finset.prod_congr rfl fun b hb => by simp [(Finset.mem_sdiff.mp hb).2]
theorem sum_powerset_avoiding_eq_prod {B : Type} [DecidableEq B] (M : Finset B) (P : B → Prop) [DecidablePred P]
    (m : B → ℝ) :
    ∑ bad ∈ M.powerset, (if ∀ c ∈ bad, ¬ P c then ∏ b ∈ M, (if b ∈ bad then 1 - m b else m b) else 0) =
      ∏ b ∈ M.filter P, m b := by
  set MO := M.filter fun b => ¬ P b with hMO
  have e1 : M.powerset.filter (fun bad => ∀ c ∈ bad, ¬ P c) = MO.powerset := by
    ext bad
    simp only [Finset.mem_filter, Finset.mem_powerset, hMO]
    constructor
    · rintro ⟨h1, h2⟩ c hc
      exact Finset.mem_filter.mpr ⟨h1 hc, h2 c hc⟩
    · intro h
      exact ⟨fun c hc => (Finset.mem_filter.mp (h hc)).1, fun c hc => (Finset.mem_filter.mp (h hc)).2⟩
  rw [← Finset.sum_filter, e1]
  have e2 : ∀ bad ∈ MO.powerset, ∏ b ∈ M, (if b ∈ bad then 1 - m b else m b) =
      (∏ b ∈ M.filter P, m b) * ∏ b ∈ MO, (if b ∈ bad then 1 - m b else m b) := by
    intro bad hbad
    rw [← Finset.prod_filter_mul_prod_filter_not M P]
    congr 1
    refine Finset.prod_congr rfl fun b hb => ?_
    rw [if_neg fun h => (Finset.mem_filter.mp (Finset.mem_powerset.mp hbad h)).2 (Finset.mem_filter.mp hb).2]
  rw [Finset.sum_congr rfl e2, ← Finset.mul_sum, sum_powerset_prod_complement_eq_one, mul_one]
theorem lintegral_pi_reindex {S Ω : Type} [DecidableEq S] [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    {Y Y' : Finset S} (e : Y' = Y) (lab : (Y' → Ω) → (Y → Ω)) (h : ∀ ν z, lab ν z = ν ⟨z.1, e ▸ z.2⟩)
    (f : (Y → Ω) → ℝ≥0∞) :
    ∫⁻ ν, f (lab ν) ∂Measure.pi (fun _ : Y' => μ) = ∫⁻ ω, f ω ∂Measure.pi (fun _ : Y => μ) := by
  subst e
  have : lab = id := by
    funext ν z
    exact h ν z
  rw [this]
  rfl
theorem measurable_bondMark (hR : R.IsWellPosed) (V : TorusField n) (b : TorusBond (n * R.params.side)) :
    Measurable fun W : TorusField (n * R.params.side) => bondMark R V W b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.measurable_bondMark <;> assumption
section Cold
variable (R)
theorem markAt_empty (y : TorusSite n) : (emptyCoarseState R (n := n)).markAt y = none := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TrivialFieldGround.markAt_empty <;> assumption
theorem fieldWithStoredLinks_empty (W : TorusField (n * R.params.side)) :
    (emptyCoarseState R (n := n)).fieldWithStoredLinks W = W := by
  funext x i
  unfold CoarseState.fieldWithStoredLinks
  rw [markAt_empty]
theorem labelAt_empty (z : TorusSite (n * R.params.side)) :
    (emptyCoarseState R (n := n)).labelAt z = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TrivialFieldGround.labelAt_empty <;> assumption
theorem unlabelled_empty (Yt : Finset (TorusSite (n * R.params.side))) :
    (emptyCoarseState R (n := n)).unlabelled Yt = Yt := by
  classical
  unfold CoarseState.unlabelled
  simp [labelAt_empty]
theorem fillLabels_empty {Yt : Finset (TorusSite (n * R.params.side))}
    (ν : (emptyCoarseState R (n := n)).unlabelled Yt → R.labels.Ω) (z : Yt) :
    (emptyCoarseState R (n := n)).fillLabels Yt ν z = ν ⟨z.1, (unlabelled_empty R Yt).symm ▸ z.2⟩ := by
  unfold CoarseState.fillLabels
  split
  · rename_i a heq
    rw [labelAt_empty] at heq
    cases heq
  · rfl
theorem coarseStateOf_empty (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    coarseStateOf R (∅ : Finset (TorusSite n)) W Yt ωt bad b = emptyCoarseState R := by
  classical
  have h1 : attachedSites R.params.side R.range bad Yt (∅ : Finset (TorusSite n)) = ∅ := by
    unfold attachedSites
    simp [sitesInBlocks]
  have h2 : storedBlocks R.params.side R.range bad Yt (∅ : Finset (TorusSite n)) = ∅ := by
    unfold storedBlocks coreBlocks
    rw [h1]
    simp [thickening]
  have h3 : coarseHull R.params.side R.range R.nextRange bad Yt (∅ : Finset (TorusSite n)) = ∅ := by
    unfold coarseHull
    rw [h2]
    simp [thickening]
  unfold coarseStateOf emptyCoarseState
  have key : ∀ (Y : Finset (TorusSite n)) (f : Y → CoarseLabel R.labels.Ω R.params.side), Y = ∅ →
      (⟨Y, f⟩ : CoarseState R n) = ⟨∅, fun z => absurd z.2 (Finset.notMem_empty _)⟩ := by
    rintro Y f rfl
    congr 1
    funext z
    exact absurd z.2 (Finset.notMem_empty _)
  exact key _ _ h3
def unitFunctional (n : ℕ) : CaseFunctional R n := fun _ _ _ _ _ => 1
theorem isCaseFunctional_unitFunctional : IsCaseFunctional (unitFunctional R (n := n)) :=
  ⟨fun _ _ _ => measurable_const, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
theorem caseIntegral_coldCase (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    (coldCaseGround R V).caseIntegral (unitFunctional R n) bad Yt b =
      ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R ∅ V bad Yt b W ωt ∂(Measure.pi fun _ => R.labels.μ)
        ∂(fieldHaar (n * R.params.side)) := by
  classical
  unfold GasGround.caseIntegral
  refine lintegral_congr fun W => ?_
  have e : ∀ ν : (coldCaseGround R V).state.unlabelled Yt → R.labels.Ω,
      (coldCaseGround R V).caseIntegrand (unitFunctional R n) bad Yt b W ν =
      configurationWeight R ∅ V bad Yt b W ((emptyCoarseState R).fillLabels Yt ν) := by
    intro ν
    unfold GasGround.caseIntegrand configurationWeight
    simp only [unitFunctional, one_mul]
    change (if IsHullState R.params R.range ((emptyCoarseState R).fieldWithStoredLinks W) Yt ∧
        coarseStateOf R ∅ ((emptyCoarseState R).fieldWithStoredLinks W) Yt
          ((emptyCoarseState R).fillLabels Yt ν) bad b = emptyCoarseState R then
        ENNReal.ofReal (stepWeight R ∅ V ((emptyCoarseState R).fieldWithStoredLinks W) Yt
          ((emptyCoarseState R).fillLabels Yt ν) bad b)
      else 0) = _
    rw [fieldWithStoredLinks_empty]
    by_cases h : IsHullState R.params R.range W Yt
    · rw [if_pos ⟨h, coarseStateOf_empty R W Yt _ bad b⟩, if_pos h]
    · rw [if_neg fun c => h c.1, if_neg h]
  simp only [e]
  exact lintegral_pi_reindex R.labels.μ (unlabelled_empty R Yt) _ (fillLabels_empty R) _
theorem recordedBad_coldCase (V : TorusField n) : (coldCaseGround R V).recordedBad = ∅ := by
  classical
  unfold GasGround.recordedBad
  have : ∀ y, (coldCaseGround R V).state.markAt y = none := fun y => markAt_empty R y
  simp [this]
theorem recordedSites_coldCase (V : TorusField n) : (coldCaseGround R V).recordedSites = ∅ := by
  classical
  unfold GasGround.recordedSites
  have : ∀ z, (coldCaseGround R V).state.labelAt z = Sum.inl () := fun z => labelAt_empty R z
  simp [this]
open Classical in
theorem caseAvoids_coldCase_iff (V : TorusField n) (A : Finset (TorusSite n))
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) :
    (coldCaseGround R V).CaseAvoids A bad Yt ↔
      (∀ c ∈ bad, parentBlock R.params.side c.1 ∉ A) ∧ Disjoint Yt (sitesInBlocks R.params.side A) := by
  unfold GasGround.CaseAvoids
  rw [recordedBad_coldCase, recordedSites_coldCase]
  simp only [Finset.notMem_empty, not_false_eq_true, forall_const]
  refine and_congr Iff.rfl ?_
  rw [Finset.disjoint_left]
  refine forall₂_congr fun z _ => ?_
  unfold sitesInBlocks
  simp
theorem baseLaw_nonneg (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    0 ≤ baseLaw (R := R) W b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SmoothOffHull.baseLaw_nonneg_of_field <;> assumption
theorem averagedKernel_eq_sum (W : TorusField (n * R.params.side)) (V : TorusField n) :
    averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) =
      ∑ b : BaseChoice R.params.side n, baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c := by
  classical
  unfold averagedKernel baseLaw
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
variable {R}
theorem bondMark_bounds (hR : R.IsWellPosed) (V : TorusField n) (W : TorusField (n * R.params.side))
    (b : TorusBond (n * R.params.side)) : 0 ≤ bondMark R V W b ∧ bondMark R V W b ≤ 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.bondMark_nonneg_le_one <;> assumption
theorem markProduct_nonneg (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (bad : Finset (TorusBond (n * R.params.side))) :
    0 ≤ markProduct R C V W bad := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.markProduct_nonneg <;> assumption
theorem prod_bondKernel_nonneg (hk : BondKernelProperties) (W : TorusField (n * R.params.side)) (V : TorusField n)
    (b : BaseChoice R.params.side n) :
    0 ≤ ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c :=
  Finset.prod_nonneg fun c _ => (hk.2 R.params R.coupling n _ _ b c).1.le
theorem lintegral_configurationWeight (hk : BondKernelProperties) (hR : R.IsWellPosed) (C : Finset (TorusSite n))
    (V : TorusField n) (W : TorusField (n * R.params.side)) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R C V bad Yt b W ωt ∂(Measure.pi fun _ => R.labels.μ) =
      (open Classical in if IsHullState R.params R.range W Yt then
          ∫⁻ ωt, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt)
            ∂(Measure.pi fun _ : Yt => R.labels.μ) else 0) *
        ENNReal.ofReal (baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
          bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
            (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) *
        ENNReal.ofReal (markProduct R C V W bad) := by
  classical
  by_cases hh : IsHullState R.params R.range W Yt
  · simp only [configurationWeight, if_pos hh]
    have hnn : ∀ ωt, 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt :=
      fun ωt => hR.hasExpansions.2.nonneg _ hside W Yt ωt hh
    have hκ := mul_nonneg (baseLaw_nonneg (R := R) W b) (prod_bondKernel_nonneg hk W V b)
    have he : ∀ ωt, ENNReal.ofReal (stepWeight R C V W Yt ωt bad b) =
        ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt) *
          (ENNReal.ofReal (baseLaw (R := R) W b * ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
            bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
              (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) *
          ENNReal.ofReal (markProduct R C V W bad)) := by
      intro ωt
      rw [← ENNReal.ofReal_mul hκ, ← ENNReal.ofReal_mul (hnn ωt)]
      unfold stepWeight
      congr 1
      ring
    simp_rw [he]
    rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top), mul_assoc]
  · simp only [configurationWeight, if_neg hh, lintegral_zero, zero_mul]
open Classical in
def avoidingHullMass (R : StepSetup) [NeZero n] (A : Finset (TorusSite n)) (W : TorusField (n * R.params.side)) :
    ℝ≥0∞ :=
  ∑ Y ∈ Finset.univ.filter
      (fun Y : Finset (TorusSite (n * R.params.side)) =>
        IsHullState R.params R.range W Y ∧ Disjoint Y (sitesInBlocks R.params.side A)),
    ∫⁻ ω, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Y ω) ∂(Measure.pi fun _ : Y => R.labels.μ)
def blockMarks (R : StepSetup) [NeZero n] (A : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) : ℝ :=
  ∏ b ∈ chartBondsInBlocks R.params.side A, bondMark R V W b
theorem markedBonds_empty : markedBonds R (∅ : Finset (TorusSite n)) = chartBonds R.params.side n := by
  classical
  unfold markedBonds
  simp
theorem sum_markProduct_avoiding (hR : R.IsWellPosed) (A : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) :
    (open Classical in ∑ bad ∈ (markedBonds R (∅ : Finset (TorusSite n))).powerset,
      if ∀ c ∈ bad, parentBlock R.params.side c.1 ∉ A then ENNReal.ofReal (markProduct R ∅ V W bad) else 0) =
      ENNReal.ofReal (blockMarks R A V W) := by
  classical
  have h := sum_powerset_avoiding_eq_prod (markedBonds R (∅ : Finset (TorusSite n)))
    (fun b => parentBlock R.params.side b.1 ∈ A) (fun b => bondMark R V W b)
  have e : blockMarks R A V W = ∏ b ∈ (markedBonds R (∅ : Finset (TorusSite n))).filter
      (fun b => parentBlock R.params.side b.1 ∈ A), bondMark R V W b := by
    unfold blockMarks chartBondsInBlocks
    rw [markedBonds_empty]
  rw [e, ← h, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun bad _ => ?_
    split_ifs
    · rfl
    · simp
  · intro bad _
    split_ifs
    · exact markProduct_nonneg hR _ V W bad
    · exact le_rfl
open Classical in
theorem sum_coldCase (hk : BondKernelProperties) (hR : R.IsWellPosed)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (A : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side)) :
    ∑ bad ∈ (markedBonds R (∅ : Finset (TorusSite n))).powerset, ∑ Yt : Finset (TorusSite (n * R.params.side)),
      (if (coldCaseGround R V).CaseAvoids A bad Yt then ∑ b : BaseChoice R.params.side n,
        ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R ∅ V bad Yt b W ωt
          ∂(Measure.pi fun _ => R.labels.μ) else 0) =
      avoidingHullMass R A W * ENNReal.ofReal (averagedKernel R.params R.coupling
        (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) * blockMarks R A V W) := by
  set D : Finset (TorusSite (n * R.params.side)) → ℝ≥0∞ := fun Yt => if IsHullState R.params R.range W Yt then
    ∫⁻ ωt, ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt ωt)
      ∂(Measure.pi fun _ : Yt => R.labels.μ) else 0 with hD
  set K : BaseChoice R.params.side n → ℝ≥0∞ := fun b => ENNReal.ofReal (baseLaw (R := R) W b *
    ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) with hK
  set M : Finset (TorusBond (n * R.params.side)) → ℝ≥0∞ := fun bad => ENNReal.ofReal (markProduct R ∅ V W bad)
    with hMk
  have h1 : ∀ bad Yt, (if (coldCaseGround R V).CaseAvoids A bad Yt then ∑ b : BaseChoice R.params.side n,
      ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R ∅ V bad Yt b W ωt ∂(Measure.pi fun _ => R.labels.μ) else 0) =
      (if Disjoint Yt (sitesInBlocks R.params.side A) then D Yt else 0) * (∑ b, K b) *
        (if ∀ c ∈ bad, parentBlock R.params.side c.1 ∉ A then M bad else 0) := by
    intro bad Yt
    have e : ∀ b : BaseChoice R.params.side n, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R ∅ V bad Yt b W ωt
        ∂(Measure.pi fun _ => R.labels.μ) = D Yt * K b * M bad :=
      fun b => lintegral_configurationWeight hk hR ∅ V W hside bad Yt b
    by_cases ho : (coldCaseGround R V).CaseAvoids A bad Yt
    · obtain ⟨o1, o2⟩ := (caseAvoids_coldCase_iff R V A bad Yt).mp ho
      rw [if_pos ho, if_pos o1, if_pos o2]
      simp only [e]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    · rw [if_neg ho]
      by_cases o1 : ∀ c ∈ bad, parentBlock R.params.side c.1 ∉ A
      · have o2 : ¬ Disjoint Yt (sitesInBlocks R.params.side A) :=
          fun h => ho ((caseAvoids_coldCase_iff R V A bad Yt).mpr ⟨o1, h⟩)
        rw [if_neg o2, zero_mul, zero_mul]
      · rw [if_neg o1, mul_zero]
  simp only [h1]
  have hY : ∑ Yt : Finset (TorusSite (n * R.params.side)),
      (if Disjoint Yt (sitesInBlocks R.params.side A) then D Yt else 0) = avoidingHullMass R A W := by
    unfold avoidingHullMass
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    simp only [hD]
    by_cases a : IsHullState R.params R.range W Yt
    · by_cases b : Disjoint Yt (sitesInBlocks R.params.side A)
      · rw [if_pos b, if_pos a, if_pos ⟨a, b⟩]
      · rw [if_neg b, if_neg fun h => b h.2]
    · by_cases b : Disjoint Yt (sitesInBlocks R.params.side A)
      · rw [if_pos b, if_neg a, if_neg fun h => a h.1]
      · rw [if_neg b, if_neg fun h => a h.1]
  have hS : ∑ b, K b = ENNReal.ofReal (averagedKernel R.params R.coupling
      (readAtLevel (stepBlockFrame R.params.side n) 0 W) (readAtLevel (stepBlockFrame R.params.side n) 1 V)) := by
    rw [averagedKernel_eq_sum R, ENNReal.ofReal_sum_of_nonneg]
    exact fun b _ => mul_nonneg (baseLaw_nonneg R W b) (prod_bondKernel_nonneg hk W V b)
  have hM0 : 0 ≤ averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
      (readAtLevel (stepBlockFrame R.params.side n) 1 V) := by
    rw [averagedKernel_eq_sum R]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (baseLaw_nonneg R W b) (prod_bondKernel_nonneg hk W V b)
  simp_rw [← Finset.sum_mul]
  rw [hY, hS, ← Finset.mul_sum, sum_markProduct_avoiding hR A V W, ENNReal.ofReal_mul hM0, mul_assoc]
theorem caseMass_coldCase (hk : BondKernelProperties) (hw : ConfigurationWeightMeasurable) (hR : R.IsWellPosed)
    (hn : R.params.n₀ ≤ n) (hside : IsBlockTorusSide R.params (n * R.params.side)) (A : Finset (TorusSite n))
    (V : TorusField n) :
    (coldCaseGround R V).caseMass A (unitFunctional R n) =
      ∫⁻ W, avoidingHullMass R A W * ENNReal.ofReal (averagedKernel R.params R.coupling
        (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) * blockMarks R A V W) ∂fieldHaar (n * R.params.side) := by
  classical
  have hm : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
      (b : BaseChoice R.params.side n), Measurable fun W : TorusField (n * R.params.side) =>
      ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R ∅ V bad Yt b W ωt ∂(Measure.pi fun _ => R.labels.μ) :=
    fun bad Yt b => (hw R hR n hn ∅ V bad Yt b).lintegral_prod_right'
  have hmi : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))),
      Measurable fun W : TorusField (n * R.params.side) =>
        (if (coldCaseGround R V).CaseAvoids A bad Yt then ∑ b : BaseChoice R.params.side n,
        ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R ∅ V bad Yt b W ωt
          ∂(Measure.pi fun _ => R.labels.μ) else 0) := by
    intro bad Yt
    split_ifs
    · exact Finset.measurable_sum _ fun b _ => hm bad Yt b
    · exact measurable_const
  unfold GasGround.caseMass
  simp only [caseIntegral_coldCase]
  have h1 : ∀ (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))),
      (if (coldCaseGround R V).CaseAvoids A bad Yt then ∑ b : BaseChoice R.params.side n,
        ∫⁻ W, ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R ∅ V bad Yt b W ωt ∂(Measure.pi fun _ => R.labels.μ)
          ∂(fieldHaar (n * R.params.side)) else 0) =
      ∫⁻ W, (if (coldCaseGround R V).CaseAvoids A bad Yt then ∑ b : BaseChoice R.params.side n,
        ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R ∅ V bad Yt b W ωt ∂(Measure.pi fun _ => R.labels.μ) else 0)
          ∂(fieldHaar (n * R.params.side)) := by
    intro bad Yt
    split_ifs
    · exact (lintegral_finsetSum _ fun b _ => hm bad Yt b).symm
    · simp
  simp only [h1]
  have h2 : ∀ bad : Finset (TorusBond (n * R.params.side)), ∑ Yt : Finset (TorusSite (n * R.params.side)),
      ∫⁻ W, (if (coldCaseGround R V).CaseAvoids A bad Yt then ∑ b : BaseChoice R.params.side n,
        ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R ∅ V bad Yt b W ωt ∂(Measure.pi fun _ => R.labels.μ) else 0)
          ∂(fieldHaar (n * R.params.side)) =
      ∫⁻ W, ∑ Yt : Finset (TorusSite (n * R.params.side)),
        (if (coldCaseGround R V).CaseAvoids A bad Yt then ∑ b : BaseChoice R.params.side n,
        ∫⁻ ωt : Yt → R.labels.Ω, configurationWeight R ∅ V bad Yt b W ωt ∂(Measure.pi fun _ => R.labels.μ) else 0)
          ∂(fieldHaar (n * R.params.side)) :=
    fun bad => (lintegral_finsetSum _ fun Yt _ => hmi bad Yt).symm
  simp only [h2]
  rw [← lintegral_finsetSum _ fun bad _ => Finset.measurable_sum _ fun Yt _ => hmi bad Yt]
  exact lintegral_congr fun W => sum_coldCase hk hR hside A V W
theorem avoidingHullMass_ne_top (hR : R.IsWellPosed) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (A : Finset (TorusSite n)) (W : TorusField (n * R.params.side)) : avoidingHullMass R A W ≠ ⊤ := by
  classical
  have hsum := hR.hasExpansions.2.sum (n * R.params.side) hside W
  have hle : avoidingHullMass R A W ≤ ENNReal.ofReal (R.functional (n * R.params.side) W) := by
    rw [← hsum]
    unfold avoidingHullMass
    refine Finset.sum_le_sum_of_subset fun Y hY => ?_
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hY).2.1⟩
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
theorem measurable_avoidingHullMass (hR : R.IsWellPosed) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (A : Finset (TorusSite n)) : Measurable (avoidingHullMass R A) := by
  classical
  have e : avoidingHullMass R A = fun W => ∑ Y : Finset (TorusSite (n * R.params.side)),
      if Disjoint Y (sitesInBlocks R.params.side A) then
      ∫⁻ ω, ENNReal.ofReal (if IsHullState R.params (clusterRange R.coupling) W Y then
          R.labelWeight (n * R.params.side) W Y ω else 0)
        ∂(Measure.pi fun _ : Y => R.labels.μ) else 0 := by
    funext W
    unfold avoidingHullMass
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases a : IsHullState R.params R.range W Y
    · have a' : IsHullState R.params (clusterRange R.coupling) W Y := a
      simp only [if_pos a']
      by_cases b : Disjoint Y (sitesInBlocks R.params.side A)
      · rw [if_pos b, if_pos ⟨a, b⟩]
      · rw [if_neg b, if_neg fun h => b h.2]
    · have a' : ¬ IsHullState R.params (clusterRange R.coupling) W Y := a
      simp only [if_neg a', ENNReal.ofReal_zero, lintegral_zero, ite_self]
      rw [if_neg fun h => a h.1]
  rw [e]
  refine Finset.measurable_sum _ fun Y _ => ?_
  split_ifs
  · exact (ENNReal.measurable_ofReal.comp
      ((hR.hasExpansions.2.borel (n * R.params.side) hside Y).1)).lintegral_prod_right'
  · exact measurable_const
theorem measurable_averagedKernel (hKb : BondKernelBorel) (V : TorusField n) :
    Measurable fun W : TorusField (n * R.params.side) =>
      averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := hKb R.params R.coupling n
  have h8 : Measurable fun W : TorusField (n * R.params.side) => (W, V) := measurable_prodMk_right
  have h9 := h7.comp h8
  simp only [Function.comp_def] at h9
  exact h9
theorem partitionFunction_ne_zero_ne_top (G : GasGround R n) (A : Finset (TorusSite n))
    (hp : IsProbabilityMeasure (G.gibbsLaw A)) :
    G.partitionFunction A ≠ 0 ∧ G.partitionFunction A ≠ ⊤ := by
  have h1 : G.gibbsLaw A Set.univ = (G.partitionFunction A)⁻¹ * G.partitionFunction A := by
    unfold GasGround.gibbsLaw GasGround.gibbsLawOff PairConstraint.gibbsLaw GasGround.partitionFunction
      GasGround.referenceMeasure
    rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, smul_eq_mul, Measure.restrict_univ]
  rw [measure_univ] at h1
  constructor
  · intro h
    rw [h] at h1
    simp at h1
  · intro h
    rw [h] at h1
    simp at h1
theorem markedIntegral_eq_caseMass (hk : BondKernelProperties) (hKb : BondKernelBorel)
    (hw : ConfigurationWeightMeasurable) (hR : R.IsWellPosed) (hn : R.params.n₀ ≤ n)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (A : Finset (TorusSite n)) (V : TorusField n) :
    R.markedIntegral A V = ((coldCaseGround R V).caseMass A (unitFunctional R n)).toReal := by
  classical
  rw [caseMass_coldCase hk hw hR hn hside A V]
  unfold StepSetup.markedIntegral
  have hM0 : ∀ W : TorusField (n * R.params.side),
      0 ≤ averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) := by
    intro W
    rw [averagedKernel_eq_sum R]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (baseLaw_nonneg R W b) (prod_bondKernel_nonneg hk W V b)
  have hQ0 : ∀ W : TorusField (n * R.params.side), 0 ≤ blockMarks R A V W := fun W =>
    Finset.prod_nonneg fun b _ => (bondMark_bounds hR V W b).1
  have hf : (fun W : TorusField (n * R.params.side) => R.avoidingPart A W *
      averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) *
      ∏ b ∈ chartBondsInBlocks R.params.side A, R.bondMark V W b) = fun W => (avoidingHullMass R A W).toReal *
      (averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (readAtLevel (stepBlockFrame R.params.side n) 1 V) * blockMarks R A V W) := by
    funext W
    rw [mul_assoc]
    rfl
  rw [hf, integral_eq_lintegral_of_nonneg_ae]
  · congr 1
    refine lintegral_congr fun W => ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (avoidingHullMass_ne_top hR hside A W)]
  · exact Filter.Eventually.of_forall fun W =>
      mul_nonneg ENNReal.toReal_nonneg (mul_nonneg (hM0 W) (hQ0 W))
  · refine Measurable.aestronglyMeasurable ?_
    refine (measurable_avoidingHullMass hR hside A).ennreal_toReal.mul (Measurable.mul ?_ ?_)
    · exact measurable_averagedKernel hKb V
    · exact Finset.measurable_prod _ fun b _ => measurable_bondMark hR V b
theorem gasIntegrand_unitFunctional (V : TorusField n) (hfin : ∀ σ, (coldCaseGround R V).pairConstraint.IsAdmissible σ →
    settingMass ((coldCaseGround R V).settingOf ((coldCaseGround R V).familyOf σ)) ≠ ⊤) :
    (coldCaseGround R V).gasIntegrand (unitFunctional R n) =
      (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight := by
  classical
  funext σ
  by_cases h : (coldCaseGround R V).pairConstraint.IsAdmissible σ
  · have e1 : (coldCaseGround R V).gasIntegrand (unitFunctional R n) σ =
        ((coldCaseGround R V).settingOf ((coldCaseGround R V).familyOf σ)).settingIntegral (unitFunctional R n)
          ((coldCaseGround R V).badBondsOf σ) :=
      if_pos h
    have e2 : (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight σ =
        ENNReal.ofReal ((coldCaseGround R V).weight σ) := if_pos h
    have e3 : (coldCaseGround R V).weight σ =
        (settingMass ((coldCaseGround R V).settingOf ((coldCaseGround R V).familyOf σ))).toReal :=
      if_pos h
    rw [e1, e2, e3, ENNReal.ofReal_toReal (hfin σ h)]
    unfold ChartSetting.settingIntegral settingMass
    simp only [unitFunctional, one_mul]
  · have e1 : (coldCaseGround R V).gasIntegrand (unitFunctional R n) σ = 0 := if_neg h
    have e2 : (coldCaseGround R V).pairConstraint.weightDensity (coldCaseGround R V).weight σ = 0 := if_neg h
    rw [e1, e2]
end Cold
end ColdGasIdentity
open ColdGasIdentity in
theorem markedIntegralEqPartition_holds (hM : CaseMassEqGasMass)
    (hC : GasColumnsSmall) (hCf : GasConfigIsAdmissibleSetting)
    (hMs : SettingMassEqIntegral) (hw : ConfigurationWeightMeasurable) (hk : BondKernelProperties)
    (hKb : BondKernelBorel) (hf1 : CouplingFloorExists) : MarkedIntegralEqPartition := by
  classical
  obtain ⟨a₂, ha₂, hC⟩ := hC
  obtain ⟨a₃, ha₃, hMs⟩ := hMs
  refine ⟨fun c => min (a₂ c) (a₃ c), fun c => lt_min (ha₂ c) (ha₃ c), fun T hT hrt => ?_⟩
  obtain ⟨y₁, hM⟩ := hM T hT
  obtain ⟨y₂, hC⟩ := hC T hT (hrt.trans (min_le_left _ _))
  obtain ⟨y₃, hCf⟩ := hCf T hT
  obtain ⟨y₄, hMs⟩ := hMs T hT (hrt.trans (min_le_right _ _))
  obtain ⟨y₅, hf1⟩ := hf1 1 (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 16) T.rt one_pos
  refine ⟨max 1 (max y₁ (max y₂ (max y₃ (max y₄ (max y₅ T.floorMin))))), fun y hy R hR hA hxx n _ hn V hV => ?_⟩
  have b₀ : (1 : ℝ) ≤ y := le_trans (by simp) hy
  have b₁ : y₁ ≤ y := le_trans (by simp) hy
  have b₂ : y₂ ≤ y := le_trans (by simp) hy
  have b₃ : y₃ ≤ y := le_trans (by simp) hy
  have b₄ : y₄ ≤ y := le_trans (by simp) hy
  have b₅ : y₅ ≤ y := le_trans (by simp) hy
  have b₆ : T.floorMin ≤ y := le_trans (by simp) hy
  have hx := hR.le_coupling
  have hfit : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y b₆
  have eL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have en₀ : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have eσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hrange := (hf1 R.coupling (b₅.trans hx)).1
  have er : R.nextRange = R.range := by
    show clusterRange R.nextCoupling = clusterRange R.coupling
    rw [hxx]
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      show R.params.threshold / 64 = T.threshold / 64
      rw [eσ]
    rw [e, hR.barrierFn_eq]
    exact hT.cut
  have hrr : R.range = clusterRange R.coupling := rfl
  have hform : R.IsWellPosed :=
    { hasExpansions := hR.isStep.1
      admissible := hfit
      isCutoff := hcut
      range_le := by omega
      nextRange_le := by omega
      nextRange_ge := by omega
      range_ge_side := by
        rw [eL]
        omega
      range_ge_base := by
        rw [en₀]
        omega
      coupling_pos := by linarith
      functional_spec := hA }
  have hn' : R.params.n₀ ≤ n := en₀ ▸ hn
  have hV' : IsCold (9 / 8 * R.params.threshold) V := eσ ▸ hV
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn'⟩
  have hx1 : R.nextCoupling ≤ 1.01 * R.coupling := by
    rw [hxx]
    linarith
  have hG : (coldCaseGround R V).IsAdmissibleGround := Or.inl ⟨hn', hV', rfl, rfl, rfl⟩
  have hset : ∀ σ, (coldCaseGround R V).pairConstraint.IsAdmissible σ →
      ((coldCaseGround R V).settingOf ((coldCaseGround R V).familyOf σ)).IsAdmissible :=
    fun σ hσ => hCf y b₃ R hR hx1 n _ hG σ hσ
  have hmass : ∀ σ, (coldCaseGround R V).pairConstraint.IsAdmissible σ →
      settingMass ((coldCaseGround R V).settingOf ((coldCaseGround R V).familyOf σ)) ≠ ⊤ := fun σ hσ => by
    rw [(hMs y b₄ R hR n hn _ (hset σ hσ)).2.2]
    exact ENNReal.ofReal_ne_top
  have hone := gasIntegrand_unitFunctional V hmass
  have hpos : ∀ A, (coldCaseGround R V).partitionFunction A ≠ 0 ∧ (coldCaseGround R V).partitionFunction A ≠ ⊤ := by
    intro A
    obtain ⟨hw', hs⟩ := hC y b₂ R hR hx1 n (coldCaseGround R V) hG (fun j => j.1.Touches A)
    exact partitionFunction_ne_zero_ne_top _ A hs.isProbabilityMeasure
  have hB : Measurable ((coldCaseGround R V).gasIntegrand (unitFunctional R n)) := by
    obtain ⟨hw', -⟩ := hC y b₂ R hR hx1 n (coldCaseGround R V) hG (fun _ => False)
    rw [hone]
    exact hw'.measurable_weightDensity
  have hD : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side)) := by
    have hσ := hfit.σ_pos
    have hnn : R.params.n₀ ≤ n * R.params.side :=
      hn'.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne _)))
    refine hR.isStep.1.1.positive _ hnn _ fun x μ ν _ => ?_
    simpa [curvature, holonomy_trivialField] using hσ
  have hZ : ∀ A, R.markedIntegral A V = R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
      ((coldCaseGround R V).partitionFunction A).toReal := by
    intro A
    rw [markedIntegral_eq_caseMass hk hKb hw hform hn' hside A V,
      hM y b₁ R hR hx1 n _ hG A (unitFunctional R n) (isCaseFunctional_unitFunctional R) hB]
    have e1 : ∏ X ∈ chainComponents R.nextRange (coldCaseGround R V).state.1,
        coarseFactor (coldCaseGround R V).coarse (coldCaseGround R V).state X = 1 := by
      have : chainComponents R.nextRange (coldCaseGround R V).state.1 = ∅ := by
        show chainComponents R.nextRange (∅ : Finset (TorusSite n)) = ∅
        unfold chainComponents
        simp
      rw [this, Finset.prod_empty]
    have e2 : (coldCaseGround R V).gasMass A (unitFunctional R n) = (coldCaseGround R V).partitionFunction A := by
      unfold GasGround.gasMass GasGround.partitionFunction
      rw [hone]
    rw [e1, e2, ENNReal.ofReal_one, mul_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le]
  refine ⟨hZ, fun Y => ?_⟩
  have hcold : 0 < (coldCaseGround R V).coldWeight := by
    have ha : (coldCaseGround R V).pairConstraint.IsAdmissible (coldCaseGround R V).allVacant := fun i j _ => Or.inl rfl
    have h1 := hMs y b₄ R hR n hn _ (hset _ ha)
    have e : (coldCaseGround R V).coldWeight =
        (settingMass ((coldCaseGround R V).settingOf ((coldCaseGround R V).familyOf
          (coldCaseGround R V).allVacant))).toReal := if_pos ha
    rw [e, h1.2.2, ENNReal.toReal_ofReal h1.2.1.le]
    exact h1.2.1
  have hP : ∀ A, 0 < ((coldCaseGround R V).partitionFunction A).toReal :=
    fun A => ENNReal.toReal_pos (hpos A).1 (hpos A).2
  show _ = R.blockDensity n Y V
  unfold StepSetup.blockDensity
  rw [dif_neg (NeZero.ne n)]
  unfold GasGround.blockDensity StepSetup.blockDensityAt
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show Real.log ((coldCaseGround R V).xi _) - Real.log ((coldCaseGround R V).xi _) =
    Real.log (R.markedIntegral _ V) - Real.log (R.markedIntegral _ V)
  unfold GasGround.xi
  rw [hZ, hZ, Real.log_div (hP _).ne' hcold.ne', Real.log_div (hP _).ne' hcold.ne',
    Real.log_mul hD.ne' (hP _).ne', Real.log_mul hD.ne' (hP _).ne']
  ring
end ClusterExpansionOfAStep
end YangMills.Construction
end
