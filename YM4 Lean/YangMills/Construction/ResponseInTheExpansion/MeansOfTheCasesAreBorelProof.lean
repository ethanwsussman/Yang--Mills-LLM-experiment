import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.MeansOfTheCasesAreBorel
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepSettings StepCosts StepGas StateMeasurability BlockAverages ColdStepAtMirrorFrames ColdChain RenormalizationStepParameters StepFrames
namespace CaseMeanMeasurability
section Hull
variable {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
theorem measurableSet_torusHotLumps_pred (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (P : Finset (Finset (TorusSite n)) → Prop) :
    MeasurableSet {W : TorusField n | P (torusHotLumps ℓ W)} := by apply _root_.YangMills.Construction.CoarseMeasurability.measurableSet_of_torusHotLumps <;> assumption
theorem measurableSet_isHullState (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (r : ℕ) (Y : Finset (TorusSite n)) :
    MeasurableSet {W : TorusField n | IsHullState ℓ r W Y} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.measurableSet_setOf_isHullState <;> assumption
end Hull
section State
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
def labelsWithDefault (q : CoarseState R n) (Yt S : Finset (TorusSite (n * R.params.side))) (d : Yt → R.labels.Ω)
    (ν : S → R.labels.Ω) : Yt → R.labels.Ω := fun z =>
  getOrDefault (q.labelAt z) (if h : (z : TorusSite (n * R.params.side)) ∈ S then ν ⟨z, h⟩ else d z)
theorem fillLabels_eq_labelsWithDefault (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side)))
    (d : Yt → R.labels.Ω) (ν : q.unlabelled Yt → R.labels.Ω) :
    q.fillLabels Yt ν = labelsWithDefault q Yt (q.unlabelled Yt) d ν := by
  classical
  funext z
  unfold CoarseState.fillLabels labelsWithDefault
  split
  · rename_i a hz
    simp [hz, getOrDefault]
  · rename_i u hz
    have hm : (z : TorusSite (n * R.params.side)) ∈ q.unlabelled Yt := Finset.mem_filter.mpr ⟨z.2, by rw [hz]⟩
    simp [hz, getOrDefault, hm]
variable {α : Type} [MeasurableSpace α] {Y : Finset (TorusSite n)}
theorem measurableSet_unlabelled_eq {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    (Yt S : Finset (TorusSite (n * R.params.side))) :
    MeasurableSet {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S} := by apply _root_.YangMills.Construction.CoarseMeasurability.measurableSet_unlabelled_eq <;> assumption
theorem measurable_labelsWithDefault {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    (Yt S : Finset (TorusSite (n * R.params.side))) (d : Yt → R.labels.Ω) {β : Type} [MeasurableSpace β]
    {f : β → α} (hf : Measurable f) {g : β → S → R.labels.Ω} (hg : Measurable g) :
    Measurable fun x => labelsWithDefault (⟨Y, ω (f x)⟩ : CoarseState R n) Yt S d (g x) := by
  classical
  refine measurable_pi_iff.mpr fun z => ?_
  unfold labelsWithDefault
  have h1 : Measurable fun x =>
      CoarseState.labelAt (⟨Y, ω (f x)⟩ : CoarseState R n) (z : TorusSite (n * R.params.side)) :=
    (measurable_labelAt (R := R) Y _).comp (hω.comp hf)
  have h2 : Measurable fun x => if h : (z : TorusSite (n * R.params.side)) ∈ S then g x ⟨z, h⟩ else d z := by
    by_cases h : (z : TorusSite (n * R.params.side)) ∈ S
    · simp only [dif_pos h]
      exact (measurable_pi_apply _).comp hg
    · simp only [dif_neg h]
      exact measurable_const
  exact measurable_getOrDefault.comp (h1.prodMk h2)
theorem measurableSet_coarseStateOf_eq [StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side)]
    (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (Yt : Finset (TorusSite (n * R.params.side))) (Y : Finset (TorusSite n))
    {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    {W : α → TorusField (n * R.params.side)} (hW : Measurable W) {lab : α → Yt → R.labels.Ω}
    (hlab : Measurable lab) :
    MeasurableSet {a | coarseStateOf R C (W a) Yt (lab a) bad b = (⟨Y, ω a⟩ : CoarseState R n)} := by apply _root_.YangMills.Construction.CoarseMeasurability.measurableSet_coarseStateOf_eq <;> assumption
theorem measurableQuaternion_comp {Ξ Ξ' : Type} [MeasurableSpace Ξ] [MeasurableSpace Ξ'] {f : Ξ → ℍ[ℝ]}
    (hf : MeasurableQuaternion f) {g : Ξ' → Ξ} (hg : Measurable g) : MeasurableQuaternion fun x => f (g x) :=
  ⟨hf.1.comp hg, hf.2.1.comp hg, hf.2.2.1.comp hg, hf.2.2.2.comp hg⟩
theorem measurable_markProduct (hcut : IsCutoff R.ballRadius R.barrierFn) (hch : ChartCoordMeasurable)
    (C : Finset (TorusSite n)) {v : α → TorusField n} (hv : Measurable v)
    {W : α → TorusField (n * R.params.side)} (hW : Measurable W) (bad : Finset (TorusBond (n * R.params.side)))
    (hf : ∀ b ∈ markedBonds R C, MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun a => markProduct R C (v a) (W a) bad := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_markProduct <;> assumption
theorem measurable_baseLaw (hK : BondKernelBorel) (b : BaseChoice R.params.side n) :
    Measurable fun W : TorusField (n * R.params.side) => baseLaw (R := R) W b := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_baseLaw <;> assumption
open Classical in
def caseIntegrand (H : TorusField n → CaseFunction R n) (C : Finset (TorusSite n))
    (bad : Finset (TorusBond (n * R.params.side))) (Yt S : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (d : Yt → R.labels.Ω) (v : α → TorusField n)
    (ω : α → Y → CoarseLabel R.labels.Ω R.params.side)
    (p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω)) : ℝ :=
  if IsHullState R.params R.range
      (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt ∧
      coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩ then
    H (v p.1.1) (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b *
      stepWeight R C (v p.1.1) (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b
  else 0
theorem measurable_caseIntegrand (hK : BondKernelBorel) (hch : ChartCoordMeasurable)
    (hexp : R.HasExpansions) (hfit : R.params.Admissible) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hblock : IsBlockTorusSide R.params (n * R.params.side))
    [StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side)] (H : TorusField n → CaseFunction R n)
    (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt S : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (d : Yt → R.labels.Ω)
    (hH : open Classical in Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.2.1 Yt p.2.2 then H p.1 p.2.1 Yt p.2.2 bad b else 0)
    {v : α → TorusField n} (hv : Measurable v)
    {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    (hf : ∀ b ∈ markedBonds R C, MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable (caseIntegrand H C bad Yt S b d v ω) := by
  classical
  have hA : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) => p.1.1 :=
    measurable_fst.comp measurable_fst
  have hWq : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) =>
      CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2 :=
    (measurable_fieldWithStoredLinks (R := R) Y).comp ((hω.comp hA).prodMk (measurable_snd.comp measurable_fst))
  have hlab : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) =>
      labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2 :=
    measurable_labelsWithDefault hω Yt S d hA measurable_snd
  have hv' : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) => v p.1.1 :=
    hv.comp hA
  have hT1 : MeasurableSet {p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) |
      IsHullState R.params R.range
        (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt} :=
    hWq (measurableSet_isHullState hfit hblock.1 R.range Yt)
  have hT2 : MeasurableSet {p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) |
      coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩} :=
    measurableSet_coarseStateOf_eq C bad b Yt Y (hω.comp hA) hWq hlab
  have hDq := ((hexp.2.borel (n * R.params.side) hblock Yt).1).comp (hWq.prodMk hlab)
  have hB := (measurable_baseLaw (R := R) hK b).comp hWq
  have hker : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) =>
      ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4, bondKernel R.params R.coupling
        (readAtLevel (stepBlockFrame R.params.side n) 0
          (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2))
        (readAtLevel (stepBlockFrame R.params.side n) 1 (v p.1.1)) b c := by
    refine Finset.measurable_fun_prod _ fun c _ => ?_
    obtain ⟨_, _, _, _, _, h6, _⟩ := hK R.params R.coupling n
    have h7 := (h6 b c).comp (hWq.prodMk hv')
    exact h7
  have hf' : ∀ b' ∈ markedBonds R C, MeasurableQuaternion
      fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) =>
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v p.1.1) b' : imaginaryQuaternions) : ℍ[ℝ]) := by
    intro b' hb'
    have h := measurableQuaternion_comp (hf b' hb') hA
    exact h
  have hM : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) =>
      markProduct R C (v p.1.1) (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) bad := by
    exact measurable_markProduct
      (v := fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) => v p.1.1) hcut hch C hv' hWq bad hf'
  have hHc := hH.comp (hv'.prodMk (hWq.prodMk hlab))
  have e : caseIntegrand H C bad Yt S b d v ω = fun p =>
      if IsHullState R.params R.range
          (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt ∧
        coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
          (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩ then
      (if IsLiveState R.params R.coupling R.labelWeight
          (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
          (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) then
        H (v p.1.1) (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
          (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b else 0) *
      ((if IsHullState R.params (clusterRange R.coupling)
          (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt then
          R.labelWeight (n * R.params.side)
            (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
            (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) else 0) *
        baseLaw (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) b *
        (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4, bondKernel R.params R.coupling
          (readAtLevel (stepBlockFrame R.params.side n) 0
            (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2))
          (readAtLevel (stepBlockFrame R.params.side n) 1 (v p.1.1)) b c) *
        markProduct R C (v p.1.1) (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) bad)
      else 0 := by
    funext p
    unfold caseIntegrand
    by_cases h : IsHullState R.params R.range
        (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt ∧
      coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩
    · rw [if_pos h, if_pos h, if_pos (show IsHullState R.params (clusterRange R.coupling) _ Yt from h.1)]
      by_cases hl : IsLiveState R.params R.coupling R.labelWeight
          (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
          (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2)
      · rw [if_pos hl]
        rfl
      · rw [if_neg hl, zero_mul]
        have hd : R.labelWeight (n * R.params.side)
            (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
            (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) = 0 :=
          le_antisymm (not_lt.mp fun hp => hl ⟨h.1, hp⟩) (hexp.2.nonneg (n * R.params.side) hblock _ _ _ h.1)
        unfold stepWeight
        rw [hd]
        ring
    · rw [if_neg h, if_neg h]
  rw [e]
  exact Measurable.ite (hT1.inter hT2) (hHc.mul (((hDq.mul hB).mul hker).mul hM)) measurable_const
theorem integral_unlabelled_eq (q : CoarseState R n) (Yt S : Finset (TorusSite (n * R.params.side)))
    (d : Yt → R.labels.Ω) (e : q.unlabelled Yt = S) (G : (Yt → R.labels.Ω) → ℝ) :
    ∫ ν : q.unlabelled Yt → R.labels.Ω, G (q.fillLabels Yt ν) ∂(Measure.pi fun _ => R.labels.μ) =
      ∫ ν : S → R.labels.Ω, G (labelsWithDefault q Yt S d ν) ∂(Measure.pi fun _ => R.labels.μ) := by
  subst e
  refine integral_congr_ae (Filter.Eventually.of_forall fun ν => ?_)
  simp only [fillLabels_eq_labelsWithDefault q Yt d ν]
theorem measurable_integral_caseTerm (hK : BondKernelBorel) (hch : ChartCoordMeasurable)
    (hexp : R.HasExpansions) (hfit : R.params.Admissible) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hblock : IsBlockTorusSide R.params (n * R.params.side))
    [StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side)] (H : TorusField n → CaseFunction R n)
    (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hH : open Classical in Measurable fun p : TorusField n × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.2.1 Yt p.2.2 then H p.1 p.2.1 Yt p.2.2 bad b else 0)
    {v : α → TorusField n} (hv : Measurable v)
    {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    (hf : ∀ b ∈ markedBonds R C, MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun a => ∫ W, ∫ ν : CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt → R.labels.Ω,
      caseTerm R C (v a) ⟨Y, ω a⟩ (H (v a)) bad Yt b W ν
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  by_cases hne : Nonempty (Yt → R.labels.Ω)
  · obtain ⟨d⟩ := hne
    refine measurable_of_countable_cover (fun S : Finset (TorusSite (n * R.params.side)) =>
      {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S})
      (fun S => measurableSet_unlabelled_eq hω Yt S) (fun a => ⟨_, rfl⟩) fun S => ?_
    have hsub : Measurable
        (Subtype.val : {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S} → α) :=
      measurable_subtype_coe
    have hi := measurable_caseIntegrand hK hch hexp hfit hcut hblock H C bad Yt S b d hH
      (hv.comp hsub) (hω.comp hsub) (fun b' hb' => by
        have h := measurableQuaternion_comp (hf b' hb') hsub
        exact h)
    have h1 := ((hi.stronglyMeasurable.integral_prod_right'
      (ν := Measure.pi fun _ : S => R.labels.μ)).integral_prod_right'
      (ν := fieldHaar (n * R.params.side))).measurable
    convert h1 using 2 with x
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    exact integral_unlabelled_eq _ Yt S d x.2 fun l =>
      if IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) Yt ∧
          coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) Yt l bad b =
            ⟨Y, ω x⟩ then
        H (v x) (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) Yt l bad b *
          stepWeight R C (v x) (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) Yt l bad b
      else 0
  · have hemp : ∀ a, IsEmpty (CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt → R.labels.Ω) := fun a =>
      ⟨fun ν => hne ⟨CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν⟩⟩
    have e : (fun a => ∫ W, ∫ ν : CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt → R.labels.Ω,
      caseTerm R C (v a) ⟨Y, ω a⟩ (H (v a)) bad Yt b W ν
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) = fun _ => 0 := by
      funext a
      have := hemp a
      simp [Measure.eq_zero_of_isEmpty
        (Measure.pi fun _ : CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt => R.labels.μ)]
    rw [e]
    exact measurable_const
end State
section Cold
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem measurableQuaternion_of_continuousOn {s : Set (TorusField n)} {f : TorusField n → ℍ[ℝ]}
    (hf : ContinuousOn f s) {α : Type} [MeasurableSpace α] {v : α → TorusField n} (hv : Measurable v)
    (hs : ∀ a, v a ∈ s) : MeasurableQuaternion fun a => f (v a) := by apply _root_.YangMills.Construction.CoarseMeasurability.measurableQuaternion_of_continuousOn <;> assumption
theorem coldNearSite_of_not_mem_hotCoreSites (hfit : R.params.Admissible) (hLn : R.params.side ∣ n)
    (hm : R.frameReach ≤ 2 * R.nextRange) {V : TorusField n} {y : TorusSite n} (hy : y ∉ hotCoreSites R V) :
    ColdNearSite R.params.threshold R.frameReach y V := by apply _root_.YangMills.Construction.CoarseMeasurability.coldNearSite_of_not_mem_hotCoreSites <;> assumption
theorem isCold_of_not_mem_hotCoreSites_of_small (hfit : R.params.Admissible) (hLn : R.params.side ∣ n)
    (hsm : n ≤ 4 * R.nextRange) {V : TorusField n} {y : TorusSite n} (hy : y ∉ hotCoreSites R V) :
    IsCold R.params.threshold V := by apply _root_.YangMills.Construction.CoarseMeasurability.isCold_of_not_mem_hotCoreSites_of_small <;> assumption
end Cold
theorem caseMean_measurable (hK : BondKernelBorel) (hch : ChartCoordMeasurable)
    (hfr : continuousOn_frameCoord_of_cold) (hlb : CoarseLabelMeasureByShapes)
    (hImg : CoarseWeightExpansionMeasurable) : caseMeanMeasurableStatement := by
  classical
  intro T hT
  obtain ⟨yI, HI⟩ := hImg T hT
  refine ⟨yI, fun y hyI R hOn hS n _ hn Y H hH => ?_⟩
  have hfit := hS.admissible
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hL0) hn.2
  have hblock : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  have : StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side) :=
    (hlb R.labels.Ω R.labels.μ R.params.side).2.1 inferInstance
  have hr40 : 2 ^ 40 ≤ R.range := le_trans (Nat.le_mul_of_pos_right _ hL0) hS.range_ge_side
  have hr' : 2 ^ 16 ≤ R.nextRange := hS.nextRange_ge
  have hab := hS.range_le
  have hm16 : 16 ≤ R.frameReach := by
    unfold StepSetup.frameReach
    norm_num at hr40 ⊢
    omega
  have hmr : R.frameReach ≤ R.range / 2 ^ 11 := le_refl _
  have hm : R.frameReach ≤ 2 * R.nextRange := by
    norm_num at hr' hmr
    omega
  have n64 : 64 ≤ n := le_trans (by have := hfit.n₀_ge; omega) hn₀
  have ha : R.params.coupling = T.coupling := by rw [hOn.params_eq]; rfl
  have hLT : R.params.side = T.side := by rw [hOn.params_eq]; rfl
  have hσ : R.params.threshold = T.threshold := by rw [hOn.params_eq]; rfl
  have hchain : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [ha, hLT, hOn.anchorRadius_eq]
    exact hT.chain
  have hσA : R.params.threshold ≤ T.σA := by
    rw [hσ]
    linarith [hT.σ_le, hT.σ_pos]
  have hcont : ∀ (C : Finset (TorusSite n)), ∀ b ∈ markedBonds R C,
      ContinuousOn (fun V : TorusField n =>
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ]))
        {V | hotCoreSites R V = C} := by
    intro C b hb
    have hb' := Finset.mem_filter.mp hb
    obtain ⟨h1, h2⟩ := hfr R.params T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N hfit hchain hσA R.depth R.frameReach n
      hm16 n64 b hb'.1
    by_cases hs : 4 * R.frameReach + 5 < n
    · refine (h1 hs).mono fun V hV => ?_
      have hV' : hotCoreSites R V = C := hV
      exact coldNearSite_of_not_mem_hotCoreSites hfit hn.1 hm (by rw [hV']; exact hb'.2)
    · refine (h2 hs).mono fun V hV => ?_
      have hV' : hotCoreSites R V = C := hV
      have hsm : n ≤ 4 * R.nextRange := by
        norm_num at hr' hmr
        omega
      exact isCold_of_not_mem_hotCoreSites_of_small hfit hn.1 hsm (y := parentBlock R.params.side b.1)
        (by rw [hV']; exact hb'.2)
  have hden := HI y hyI R hOn hS n hn Y
  refine measurable_of_countable_cover (fun C : Finset (TorusSite n) =>
    {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C})
    (fun C => measurable_fst (measurableSet_torusHotLumps_pred hfit hn.1 fun H =>
      thickening (2 * R.nextRange) (H.biUnion id) = C))
    (fun p => ⟨_, rfl⟩) fun C => ?_
  have hv : Measurable fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) |
      hotCoreSites R p.1 = C} => a.1.1 :=
    measurable_fst.comp measurable_subtype_coe
  have hω : Measurable fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) |
      hotCoreSites R p.1 = C} => a.1.2 :=
    measurable_snd.comp measurable_subtype_coe
  have hfq : ∀ b ∈ markedBonds R C, MeasurableQuaternion
      fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C} =>
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach a.1.1 b : imaginaryQuaternions) : ℍ[ℝ]) := by
    intro b hb
    exact measurableQuaternion_of_continuousOn (hcont C b hb) hv fun a => a.2
  have hint : Measurable fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) |
      hotCoreSites R p.1 = C} =>
      caseIntegral R C a.1.1 (⟨Y, a.1.2⟩ : CoarseState R n) (H a.1.1) := by
    unfold caseIntegral
    refine Finset.measurable_fun_sum _ fun bad _ => Finset.measurable_fun_sum _ fun Yt _ =>
      Finset.measurable_fun_sum _ fun b _ => ?_
    exact measurable_integral_caseTerm hK hch hS.hasExpansions hfit hS.isCutoff hblock H C bad Yt b
      (hH Yt bad b) hv hω hfq
  have hd : Measurable fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) |
      hotCoreSites R p.1 = C} =>
      if IsHullState R.params R.nextRange a.1.1 Y then coarseWeightExpansion R n a.1.1 Y a.1.2 else 0 :=
    Measurable.comp (g := fun p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) =>
      if IsHullState R.params R.nextRange p.1 Y then coarseWeightExpansion R n p.1 Y p.2 else 0)
      (f := fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C} =>
        a.1) hden measurable_subtype_coe
  have e : (fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C} =>
      if IsHullState R.params R.nextRange a.1.1 Y then
        caseMean R (hotCoreSites R a.1.1) a.1.1 ⟨Y, a.1.2⟩ (H a.1.1) else 0) =
      fun a => if IsHullState R.params R.nextRange a.1.1 Y then
        caseIntegral R C a.1.1 (⟨Y, a.1.2⟩ : CoarseState R n) (H a.1.1) /
          (if IsHullState R.params R.nextRange a.1.1 Y then coarseWeightExpansion R n a.1.1 Y a.1.2 else 0) else 0 := by
    funext a
    have hC : hotCoreSites R a.1.1 = C := a.2
    by_cases hh : IsHullState R.params R.nextRange a.1.1 Y
    · rw [if_pos hh, if_pos hh, if_pos hh]
      unfold caseMean coarseWeightExpansion
      rw [dif_neg (NeZero.ne n), hC]
    · rw [if_neg hh, if_neg hh]
  have hfin : Measurable fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) |
      hotCoreSites R p.1 = C} =>
      if IsHullState R.params R.nextRange a.1.1 Y then
        caseIntegral R C a.1.1 (⟨Y, a.1.2⟩ : CoarseState R n) (H a.1.1) /
          (if IsHullState R.params R.nextRange a.1.1 Y then coarseWeightExpansion R n a.1.1 Y a.1.2 else 0) else 0 :=
    Measurable.ite (hv (measurableSet_isHullState hfit hn.1 R.nextRange Y)) (Measurable.div hint hd)
      measurable_const
  exact Eq.mp (congrArg Measurable e.symm) hfin
end CaseMeanMeasurability
end YangMills.Construction.WeightedResponses
end
