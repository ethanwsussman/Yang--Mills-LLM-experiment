import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStepIsBorel
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepSettings YangMills.Construction.StepGas YangMills.Construction.StepCosts YangMills.Construction.StepFrames YangMills.Construction.StateMeasurability YangMills.Construction.RenormalizationStepParameters YangMills.Construction.ColdChain YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace StepResponse
section Hull
variable {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
private theorem measurableSet_of_torusHotLumps (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (P : Finset (Finset (TorusSite n)) → Prop) :
    MeasurableSet {W : TorusField n | P (torusHotLumps ℓ W)} := by apply _root_.YangMills.Construction.CoarseMeasurability.measurableSet_of_torusHotLumps <;> assumption
private theorem measurableSet_isHullState (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (r : ℕ)
    (Y : Finset (TorusSite n)) :
    MeasurableSet {W : TorusField n | IsHullState ℓ r W Y} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.measurableSet_setOf_isHullState <;> assumption
end Hull
section State
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
private def labelsWithDefault (q : CoarseState R n) (Yt S : Finset (TorusSite (n * R.params.side)))
    (d : Yt → R.labels.Ω) (ν : S → R.labels.Ω) : Yt → R.labels.Ω := fun z =>
  getOrDefault (q.labelAt z) (if h : (z : TorusSite (n * R.params.side)) ∈ S then ν ⟨z, h⟩ else d z)
private theorem fillLabels_eq (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side)))
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
private theorem measurableSet_unlabelled_eq {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    (Yt S : Finset (TorusSite (n * R.params.side))) :
    MeasurableSet {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S} := by apply _root_.YangMills.Construction.CoarseMeasurability.measurableSet_unlabelled_eq <;> assumption
private theorem measurable_labelsWithDefault {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
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
private theorem measurableSet_coarseStateOf_eq [StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side)]
    (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (Yt : Finset (TorusSite (n * R.params.side))) (Y : Finset (TorusSite n))
    {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    {W : α → TorusField (n * R.params.side)} (hW : Measurable W) {lab : α → Yt → R.labels.Ω}
    (hlab : Measurable lab) :
    MeasurableSet {a | coarseStateOf R C (W a) Yt (lab a) bad b = (⟨Y, ω a⟩ : CoarseState R n)} := by apply _root_.YangMills.Construction.CoarseMeasurability.measurableSet_coarseStateOf_eq <;> assumption
private theorem measurableQuaternion_comp {Ξ Ξ' : Type} [MeasurableSpace Ξ] [MeasurableSpace Ξ'] {f : Ξ → ℍ[ℝ]}
    (hf : MeasurableQuaternion f) {g : Ξ' → Ξ} (hg : Measurable g) : MeasurableQuaternion fun x => f (g x) :=
  ⟨hf.1.comp hg, hf.2.1.comp hg, hf.2.2.1.comp hg, hf.2.2.2.comp hg⟩
private theorem measurable_markProduct (hcut : IsCutoff R.ballRadius R.barrierFn) (hch : ChartCoordMeasurable)
    (C : Finset (TorusSite n)) {v : α → TorusField n} (hv : Measurable v)
    {W : α → TorusField (n * R.params.side)} (hW : Measurable W) (bad : Finset (TorusBond (n * R.params.side)))
    (hf : ∀ b ∈ markedBonds R C, MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun a => markProduct R C (v a) (W a) bad := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_markProduct <;> assumption
private theorem measurable_baseLaw (hK : BondKernelBorel) (b : BaseChoice R.params.side n) :
    Measurable fun W : TorusField (n * R.params.side) => baseLaw (R := R) W b := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_baseLaw <;> assumption
open Classical in
private def weightedIntegrand (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt S : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (d : Yt → R.labels.Ω)
    (v : α → TorusField n) (ω : α → Y → CoarseLabel R.labels.Ω R.params.side)
    (G : α → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ)
    (p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω)) : ℝ :=
  if IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt ∧
      coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩ then
    G p.1.1 (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2)
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) *
      stepWeight R C (v p.1.1) (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b
  else 0
private theorem measurableSet_isLiveState (hrow : R.HasExpansions) (hfit : R.params.Admissible)
    (hblock : IsBlockTorusSide R.params (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) :
    MeasurableSet {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} := by
  classical
  have h1 : MeasurableSet {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
      IsHullState R.params R.range p.1 Yt} :=
    measurable_fst (measurableSet_isHullState hfit hblock.1 R.range Yt)
  have h2 := measurableSet_lt (measurable_const (a := (0 : ℝ))) ((hrow.2.borel (n * R.params.side) hblock Yt).1)
  have e : {p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
        IsLiveState R.params R.coupling R.labelWeight p.1 Yt p.2} =
      {p | IsHullState R.params R.range p.1 Yt} ∩ {p | 0 < if IsHullState R.params (clusterRange R.coupling) p.1 Yt
        then R.labelWeight (n * R.params.side) p.1 Yt p.2 else 0} := by
    ext p
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      show 0 < if IsHullState R.params (clusterRange R.coupling) p.1 Yt
        then R.labelWeight (n * R.params.side) p.1 Yt p.2 else 0
      rw [if_pos h.1]
      exact h.2
    · rintro ⟨h1, h2⟩
      have h2' : 0 < if IsHullState R.params (clusterRange R.coupling) p.1 Yt
          then R.labelWeight (n * R.params.side) p.1 Yt p.2 else 0 := h2
      have h1' : IsHullState R.params (clusterRange R.coupling) p.1 Yt := h1
      rw [if_pos h1'] at h2'
      exact ⟨h1', h2'⟩
  rw [e]
  exact h1.inter h2
open Classical in
private theorem measurable_weightedIntegrand (hK : BondKernelBorel) (hch : ChartCoordMeasurable)
    (hrow : R.HasExpansions) (hfit : R.params.Admissible) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hblock : IsBlockTorusSide R.params (n * R.params.side))
    [StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side)]
    (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt S : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (d : Yt → R.labels.Ω)
    {v : α → TorusField n} (hv : Measurable v)
    {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    (hf : ∀ b ∈ markedBonds R C, MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ]))
    {G : α → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ}
    (hG : Measurable fun p : α × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.2.1 Yt p.2.2 then G p.1 p.2.1 p.2.2 else 0) :
    Measurable (weightedIntegrand C bad Yt S b d v ω G) := by
  have hA : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) => p.1.1 :=
    measurable_fst.comp measurable_fst
  have hWq : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) =>
      CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2 :=
    (measurable_fieldWithStoredLinks (R := R) Y).comp ((hω.comp hA).prodMk (measurable_snd.comp measurable_fst))
  have hlab : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) =>
      labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2 :=
    measurable_labelsWithDefault hω Yt S d hA measurable_snd
  have hv' : Measurable fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) => v p.1.1 := hv.comp hA
  have hT1 : MeasurableSet {p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) |
      IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt} :=
    hWq (measurableSet_isHullState hfit hblock.1 R.range Yt)
  have hT2 : MeasurableSet {p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) |
      coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩} :=
    measurableSet_coarseStateOf_eq C bad b Yt Y (hω.comp hA) hWq hlab
  have hDq := ((hrow.2.borel (n * R.params.side) hblock Yt).1).comp (hWq.prodMk hlab)
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
  have hGc := hG.comp (hA.prodMk (hWq.prodMk hlab))
  have e : weightedIntegrand C bad Yt S b d v ω G = fun p =>
      if IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt ∧
        coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
          (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩ then
      (if IsLiveState R.params R.coupling R.labelWeight
          (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
          (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) then
          G p.1.1 (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2)
            (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) else 0) *
        ((if IsHullState R.params (clusterRange R.coupling)
            (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt then
          R.labelWeight (n * R.params.side) (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
            (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) else 0) *
        baseLaw (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) b *
        (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4, bondKernel R.params R.coupling
          (readAtLevel (stepBlockFrame R.params.side n) 0
            (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2))
          (readAtLevel (stepBlockFrame R.params.side n) 1 (v p.1.1)) b c) *
        markProduct R C (v p.1.1) (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) bad)
      else 0 := by
    funext p
    unfold weightedIntegrand
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
      · have h0 : R.labelWeight (n * R.params.side)
            (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
            (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) = 0 :=
          le_antisymm (not_lt.mp fun hp => hl ⟨h.1, hp⟩) (hrow.2.nonneg _ hblock _ _ _ h.1)
        rw [if_neg hl, zero_mul]
        unfold stepWeight
        rw [h0]
        ring
    · rw [if_neg h, if_neg h]
  rw [e]
  exact Measurable.ite (hT1.inter hT2) (hGc.mul (((hDq.mul hB).mul hker).mul hM)) measurable_const
private theorem measurable_massTerm (hK : BondKernelBorel) (hch : ChartCoordMeasurable)
    (hrow : R.HasExpansions) (hfit : R.params.Admissible) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hblock : IsBlockTorusSide R.params (n * R.params.side))
    [StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side)]
    (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    {v : α → TorusField n} (hv : Measurable v)
    {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    (hf : ∀ b ∈ markedBonds R C, MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun a => ∫⁻ W, ∫⁻ ν : CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt → R.labels.Ω,
      (open Classical in
        if IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt ∧
          coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt
            (CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν) bad b = ⟨Y, ω a⟩ then
          ENNReal.ofReal (stepWeight R C (v a) (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt
            (CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν) bad b) else 0)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_massTerm <;> assumption
private theorem integral_unlabelled (q : CoarseState R n) (Yt S : Finset (TorusSite (n * R.params.side)))
    (d : Yt → R.labels.Ω) (e : q.unlabelled Yt = S) (G : (Yt → R.labels.Ω) → ℝ) :
    ∫ ν : q.unlabelled Yt → R.labels.Ω, G (q.fillLabels Yt ν) ∂(Measure.pi fun _ => R.labels.μ) =
      ∫ ν : S → R.labels.Ω, G (labelsWithDefault q Yt S d ν) ∂(Measure.pi fun _ => R.labels.μ) := by
  subst e
  refine integral_congr_ae (Filter.Eventually.of_forall fun ν => ?_)
  simp only [fillLabels_eq q Yt d ν]
open Classical in
private theorem measurable_caseTermIntegral (hK : BondKernelBorel) (hch : ChartCoordMeasurable)
    (hrow : R.HasExpansions) (hfit : R.params.Admissible) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hblock : IsBlockTorusSide R.params (n * R.params.side))
    [StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side)]
    (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    {v : α → TorusField n} (hv : Measurable v)
    {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    (hf : ∀ b ∈ markedBonds R C, MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ]))
    {F : α → CaseFunction R n}
    (hF : Measurable fun p : α × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.2.1 Yt p.2.2 then F p.1 p.2.1 Yt p.2.2 bad b else 0) :
    Measurable fun a => ∫ W, ∫ ν : CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt → R.labels.Ω,
      caseTerm R C (v a) ⟨Y, ω a⟩ (F a) bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ)
        ∂(fieldHaar (n * R.params.side)) := by
  by_cases hne : Nonempty (Yt → R.labels.Ω)
  · obtain ⟨d⟩ := hne
    refine measurable_of_countable_cover (fun S : Finset (TorusSite (n * R.params.side)) =>
      {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S})
      (fun S => measurableSet_unlabelled_eq hω Yt S) (fun a => ⟨_, rfl⟩) fun S => ?_
    have hsub : Measurable
        (Subtype.val : {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S} → α) :=
      measurable_subtype_coe
    have hm : Measurable fun p : {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S} ×
        TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        (((p.1 : α), p.2) : α × TorusField (n * R.params.side) × (Yt → R.labels.Ω)) :=
      (hsub.comp measurable_fst).prodMk measurable_snd
    have hF' : Measurable fun p : {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S} ×
        TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        if IsLiveState R.params R.coupling R.labelWeight p.2.1 Yt p.2.2 then F p.1.1 p.2.1 Yt p.2.2 bad b
        else 0 := by
      have h := hF.comp hm
      exact h
    have hf' : ∀ b' ∈ markedBonds R C, MeasurableQuaternion
        fun a : {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S} =>
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach ((v ∘ Subtype.val) a) b' :
            imaginaryQuaternions) : ℍ[ℝ]) := fun b' hb' => by
      have h := measurableQuaternion_comp (hf b' hb') hsub
      exact h
    have hi := measurable_weightedIntegrand
      (α := {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S})
      hK hch hrow hfit hcut hblock C bad Yt S b d (hv.comp hsub) (hω.comp hsub) hf'
      (G := fun a W l => F a.1 W Yt l bad b) hF'
    have h1 := (hi.stronglyMeasurable.integral_prod_right'
      (ν := Measure.pi fun _ : S => R.labels.μ)).integral_prod_right' (ν := fieldHaar (n * R.params.side))
    have e : (fun x : {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S} =>
        ∫ W, ∫ ν : CoarseState.unlabelled (⟨Y, ω x.1⟩ : CoarseState R n) Yt → R.labels.Ω,
          caseTerm R C (v x.1) ⟨Y, ω x.1⟩ (F x.1) bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ)
            ∂(fieldHaar (n * R.params.side))) =
        fun x => ∫ W, ∫ ν : S → R.labels.Ω, weightedIntegrand C bad Yt S b d (v ∘ Subtype.val) (ω ∘ Subtype.val)
          (fun a W l => F a.1 W Yt l bad b) ((x, W), ν) ∂(Measure.pi fun _ => R.labels.μ)
            ∂(fieldHaar (n * R.params.side)) := by
      funext x
      refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
      simp only [caseTerm, weightedIntegrand, Function.comp]
      exact integral_unlabelled _ Yt S d x.2 fun l =>
        if IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) Yt ∧
            coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) Yt l bad b =
              ⟨Y, ω x⟩ then
          F x (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) Yt l bad b *
            stepWeight R C (v x) (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) Yt l bad b
        else 0
    exact show Measurable fun x : {a | CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt = S} =>
        ∫ W, ∫ ν : CoarseState.unlabelled (⟨Y, ω x.1⟩ : CoarseState R n) Yt → R.labels.Ω,
          caseTerm R C (v x.1) ⟨Y, ω x.1⟩ (F x.1) bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ)
            ∂(fieldHaar (n * R.params.side)) from by
      rw [e]
      exact h1.measurable
  · have hemp : ∀ a, IsEmpty (CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt → R.labels.Ω) := fun a =>
      ⟨fun ν => hne ⟨CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν⟩⟩
    have e : (fun a => ∫ W, ∫ ν : CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt → R.labels.Ω,
      caseTerm R C (v a) ⟨Y, ω a⟩ (F a) bad Yt b W ν ∂(Measure.pi fun _ => R.labels.μ)
        ∂(fieldHaar (n * R.params.side))) = fun _ => 0 := by
      funext a
      have := hemp a
      simp [Measure.eq_zero_of_isEmpty
        (Measure.pi fun _ : CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt => R.labels.μ)]
    rw [e]
    exact measurable_const
open Classical in
private theorem measurable_caseResponse (hsc : BondScoreProperties) {A : ResponseSetup R} (hA : A.IsAdmissible)
    (hrow : R.HasExpansions) (hfit : R.params.Admissible) (hblock : IsBlockTorusSide R.params (n * R.params.side))
    {v : α → TorusField n} (hv : Measurable v) (y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable fun p : α × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.2.1 Yt p.2.2 then
        caseResponse A (v p.1) y h p.2.1 Yt p.2.2 bad b else 0 := by
  have hS : MeasurableSet {p : α × TorusField (n * R.params.side) × (Yt → R.labels.Ω) |
      IsLiveState R.params R.coupling R.labelWeight p.2.1 Yt p.2.2} :=
    measurable_snd (measurableSet_isLiveState hrow hfit hblock Yt)
  have hQ : ∀ z, Measurable fun p : α × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.2.1 Yt p.2.2 then
        A.hull (n * R.params.side) z p.2.1 Yt p.2.2 h else 0 := fun z =>
    (hA.bounds.hull_borel (n * R.params.side) hblock z Yt h).comp measurable_snd
  have hg : Measurable fun p : α × TorusField (n * R.params.side) × (Yt → R.labels.Ω) => (p.2.1, v p.1) :=
    (measurable_fst.comp measurable_snd).prodMk (hv.comp measurable_fst)
  have hs : Measurable fun p : α × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      blockBondScores p.2.1 (v p.1) b y := by
    unfold blockBondScores
    refine Finset.measurable_sum _ fun i _ => ?_
    have h1 := ((hsc R.params hfit R.coupling n b (y, i)).2.2.2.2).comp hg
    have h2 := ((hsc R.params hfit R.coupling n b (y - TorusFields.unitStep n i, i)).2.2.2.2).comp hg
    exact h1.add h2
  have e : (fun p : α × TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      if IsLiveState R.params R.coupling R.labelWeight p.2.1 Yt p.2.2 then
        caseResponse A (v p.1) y h p.2.1 Yt p.2.2 bad b else 0) =
      fun p => (∑ z ∈ sitesInBlocks R.params.side {y},
          if IsLiveState R.params R.coupling R.labelWeight p.2.1 Yt p.2.2 then
            A.hull (n * R.params.side) z p.2.1 Yt p.2.2 h else 0) +
        if IsLiveState R.params R.coupling R.labelWeight p.2.1 Yt p.2.2 then
          R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n y h *
            blockBondScores p.2.1 (v p.1) b y else 0 := by
    funext p
    by_cases hl : IsLiveState R.params R.coupling R.labelWeight p.2.1 Yt p.2.2
    · simp only [if_pos hl]
      rfl
    · simp only [if_neg hl, Finset.sum_const_zero, add_zero]
  rw [e]
  exact (Finset.measurable_sum _ fun z _ => hQ z).add (Measurable.ite hS (hs.const_mul _) measurable_const)
end State
section Cold
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem measurableQuaternion_of_continuousOn {s : Set (TorusField n)} {f : TorusField n → ℍ[ℝ]}
    (hf : ContinuousOn f s) {α : Type} [MeasurableSpace α] {v : α → TorusField n} (hv : Measurable v)
    (hs : ∀ a, v a ∈ s) : MeasurableQuaternion fun a => f (v a) := by apply _root_.YangMills.Construction.CoarseMeasurability.measurableQuaternion_of_continuousOn <;> assumption
private theorem coldNearSite_of_not_mem (hfit : R.params.Admissible) (hLn : R.params.side ∣ n)
    (hm : R.frameReach ≤ 2 * R.nextRange) {V : TorusField n} {y : TorusSite n} (hy : y ∉ hotCoreSites R V) :
    ColdNearSite R.params.threshold R.frameReach y V := by apply _root_.YangMills.Construction.CoarseMeasurability.coldNearSite_of_not_mem_hotCoreSites <;> assumption
private theorem isCold_of_small (hfit : R.params.Admissible) (hLn : R.params.side ∣ n)
    (hsm : n ≤ 4 * R.nextRange) {V : TorusField n} {y : TorusSite n} (hy : y ∉ hotCoreSites R V) :
    IsCold R.params.threshold V := by apply _root_.YangMills.Construction.CoarseMeasurability.isCold_of_not_mem_hotCoreSites_of_small <;> assumption
end Cold
private theorem measurableSet_isCold (s : ℝ) {n : ℕ} [NeZero n] :
    MeasurableSet {W : TorusField n | IsCold s W} := by
  have e : {W : TorusField n | IsCold s W} =
      ⋂ (x : TorusSite n) (μ : Fin 4) (ν : Fin 4) (_ : μ < ν), {W : TorusField n | curvature W x μ ν < s} := by
    ext W
    simp [TorusFields.IsCold]
  rw [e]
  exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun μ => MeasurableSet.iInter fun ν =>
    MeasurableSet.iInter fun _ => measurableSet_lt (continuous_curvature x μ ν).measurable measurable_const
end StepResponse
open StepResponse in
theorem stepResponseMeasurable_of_bondKernelBorel (hK : BondKernelBorel) (hch : ChartCoordMeasurable)
    (hfr : continuousOn_frameCoord_of_cold) (hlb : CoarseLabelMeasureByShapes)
    (hsc : BondScoreProperties) : StepResponseMeasurable := by
  classical
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ K => ⟨0, fun y _ R A _ hAt hS hL => ?_⟩⟩
  have hOn := hAt.onFamily
  have hresp := hAt.admissible
  have hfit := hS.admissible
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
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
  have ha : R.params.coupling = T.coupling := by rw [hOn.params_eq]; rfl
  have hLT : R.params.side = T.side := by rw [hOn.params_eq]; rfl
  have hσ : R.params.threshold = T.threshold := by rw [hOn.params_eq]; rfl
  have hchain : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [ha, hLT, hOn.anchorRadius_eq]
    exact hT.chain
  have hσA : R.params.threshold ≤ T.σA := by
    rw [hσ]
    linarith [hT.σ_le, hT.σ_pos]
  have hblockOf : ∀ {n : ℕ}, R.params.n₀ ≤ n → IsBlockTorusSide R.params (n * R.params.side) := fun hn =>
    ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  refine ⟨fun n _ hn C V q y' h bad Yt b => ?_, fun n _ hn y' h => ?_, fun n _ hn y' Y h => ?_⟩
  · by_cases hne : Nonempty (Yt → R.labels.Ω)
    · obtain ⟨d⟩ := hne
      have hi := measurable_weightedIntegrand (α := Unit) (Y := q.1) hK hch hS.hasExpansions hfit hS.isCutoff
        (hblockOf hn) C bad Yt (q.unlabelled Yt) b d (v := fun _ => V) measurable_const (ω := fun _ => q.2)
        measurable_const (fun b' _ => ⟨measurable_const, measurable_const, measurable_const, measurable_const⟩)
        (G := fun _ W l => caseResponse A V y' h W Yt l bad b)
        (measurable_caseResponse hsc hresp hS.hasExpansions hfit (hblockOf hn) (v := fun _ : Unit => V)
          measurable_const y' h bad Yt b)
      have hf : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
          (((), p.1), p.2) :=
        (measurable_const.prodMk measurable_fst).prodMk measurable_snd
      have e : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
          caseTerm R C V q (caseResponse A V y' h) bad Yt b p.1 p.2) =
          (weightedIntegrand (Y := q.1) C bad Yt (q.unlabelled Yt) b d (fun _ : Unit => V) (fun _ => q.2)
            fun _ W l => caseResponse A V y' h W Yt l bad b) ∘ fun p => (((), p.1), p.2) := by
        funext p
        simp only [Function.comp, weightedIntegrand, caseTerm]
        simp only [fillLabels_eq q Yt d p.2]
      rw [e]
      exact hi.comp hf
    · have : IsEmpty (TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω)) :=
        ⟨fun p => hne ⟨q.fillLabels Yt p.2⟩⟩
      intro s _
      rw [Set.eq_empty_of_isEmpty (_ ⁻¹' s)]
      exact MeasurableSet.empty
  · have n64 : 64 ≤ n := le_trans (by have := hfit.n₀_ge; omega) hn
    have hcold : MeasurableSet {W : TorusField n | IsCold R.params.threshold W} := measurableSet_isCold _
    refine measurable_of_countable_cover
      (fun c : Bool => {W : TorusField n | decide (IsCold R.params.threshold W) = c})
      (fun c => ?_) (fun W => ⟨_, rfl⟩) fun c => ?_
    · cases c
      · have e : {W : TorusField n | decide (IsCold R.params.threshold W) = false} =
            {W : TorusField n | IsCold R.params.threshold W}ᶜ := by
          ext W
          simp
        show MeasurableSet {W : TorusField n | decide (IsCold R.params.threshold W) = false}
        rw [e]
        exact hcold.compl
      · have e : {W : TorusField n | decide (IsCold R.params.threshold W) = true} =
            {W : TorusField n | IsCold R.params.threshold W} := by
          ext W
          simp
        show MeasurableSet {W : TorusField n | decide (IsCold R.params.threshold W) = true}
        rw [e]
        exact hcold
    · cases c
      · have e : (fun W : {W : TorusField n | decide (IsCold R.params.threshold W) = false} =>
            if IsCold R.params.threshold W.1 then A.coldStep n y' W.1 h else 0) = fun _ => 0 := by
          funext W
          have hW : ¬ IsCold R.params.threshold W.1 := of_decide_eq_false W.2
          rw [if_neg hW]
        rw [e]
        exact measurable_const
      · have hmem : ∀ W : {W : TorusField n | decide (IsCold R.params.threshold W) = true},
            IsCold R.params.threshold W.1 := fun W => of_decide_eq_true W.2
        have hv : Measurable fun W : {W : TorusField n | decide (IsCold R.params.threshold W) = true} => W.1 :=
          measurable_subtype_coe
        have hcont : ∀ b ∈ markedBonds R (∅ : Finset (TorusSite n)),
            ContinuousOn (fun V : TorusField n =>
              ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ]))
              {V | IsCold R.params.threshold V} := by
          intro b hb
          have hb' := Finset.mem_filter.mp hb
          obtain ⟨h1, h2⟩ := hfr R.params T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N hfit hchain hσA R.depth
            R.frameReach n hm16 n64 b hb'.1
          by_cases hs : 4 * R.frameReach + 5 < n
          · exact (h1 hs).mono fun V hV a μ ν hlt _ => hV _ μ ν hlt
          · exact h2 hs
        have hfq : ∀ b ∈ markedBonds R (∅ : Finset (TorusSite n)), MeasurableQuaternion fun W :
            {W : TorusField n | decide (IsCold R.params.threshold W) = true} =>
            ((frameCoord R.params R.anchorRadius R.depth R.frameReach W.1 b : imaginaryQuaternions) : ℍ[ℝ]) :=
          fun b hb => measurableQuaternion_of_continuousOn (hcont b hb) hv hmem
        have hω : Measurable fun _ : {W : TorusField n | decide (IsCold R.params.threshold W) = true} =>
            (emptyCoarseState R (n := n)).2 := measurable_const
        have hmass : Measurable fun W : {W : TorusField n | decide (IsCold R.params.threshold W) = true} =>
            coarseStateMass R ∅ W.1 (emptyCoarseState R) := by
          unfold coarseStateMass
          refine Finset.measurable_fun_sum _ fun bad _ => Finset.measurable_fun_sum _ fun Yt _ =>
            Finset.measurable_fun_sum _ fun b _ => ?_
          exact measurable_massTerm (Y := ∅) hK hch hS.hasExpansions hfit hS.isCutoff (hblockOf hn) ∅ bad Yt b
            hv hω hfq
        have hint : Measurable fun W : {W : TorusField n | decide (IsCold R.params.threshold W) = true} =>
            caseIntegral R ∅ W.1 (emptyCoarseState R) (caseResponse A W.1 y' h) := by
          unfold caseIntegral
          refine Finset.measurable_sum _ fun bad _ => Finset.measurable_sum _ fun Yt _ =>
            Finset.measurable_sum _ fun b _ => ?_
          exact measurable_caseTermIntegral (Y := ∅) hK hch hS.hasExpansions hfit hS.isCutoff (hblockOf hn) ∅
            bad Yt b hv hω hfq (F := fun W => caseResponse A W.1 y' h)
            (measurable_caseResponse hsc hresp hS.hasExpansions hfit (hblockOf hn) hv y' h bad Yt b)
        have e : (fun W : {W : TorusField n | decide (IsCold R.params.threshold W) = true} =>
            if IsCold R.params.threshold W.1 then A.coldStep n y' W.1 h else 0) =
            fun W => caseIntegral R ∅ W.1 (emptyCoarseState R) (caseResponse A W.1 y' h) /
              (coarseStateMass R ∅ W.1 (emptyCoarseState R)).toReal := by
          funext W
          rw [if_pos (hmem W)]
          rfl
        rw [e]
        exact hint.div (ENNReal.measurable_toReal.comp hmass)
  · have hn₀ : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hL0) hn.2
    have n64 : 64 ≤ n := le_trans (by have := hfit.n₀_ge; omega) hn₀
    have hcont : ∀ (C : Finset (TorusSite n)), ∀ b ∈ markedBonds R C,
        ContinuousOn (fun V : TorusField n =>
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ]))
          {V | hotCoreSites R V = C} := by
      intro C b hb
      have hb' := Finset.mem_filter.mp hb
      obtain ⟨h1, h2⟩ := hfr R.params T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N hfit hchain hσA R.depth
        R.frameReach n hm16 n64 b hb'.1
      by_cases hs : 4 * R.frameReach + 5 < n
      · refine (h1 hs).mono fun V hV => ?_
        have hV' : hotCoreSites R V = C := hV
        exact coldNearSite_of_not_mem hfit hn.1 hm (by rw [hV']; exact hb'.2)
      · refine (h2 hs).mono fun V hV => ?_
        have hV' : hotCoreSites R V = C := hV
        have hsm : n ≤ 4 * R.nextRange := by
          norm_num at hr' hmr
          omega
        exact isCold_of_small hfit hn.1 hsm (y := parentBlock R.params.side b.1) (by rw [hV']; exact hb'.2)
    show Measurable fun p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) =>
      if IsLiveState R.params R.nextCoupling (coarseWeightExpansion R) p.1 Y p.2 then
        A.hullStep n y' p.1 Y p.2 h else 0
    refine measurable_of_countable_cover (fun C : Finset (TorusSite n) =>
      {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C})
      (fun C => measurable_fst (measurableSet_of_torusHotLumps hfit hn.1 fun H =>
        thickening (2 * R.nextRange) (H.biUnion id) = C))
      (fun p => ⟨_, rfl⟩) fun C => ?_
    have hv : Measurable fun a :
        {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C} => a.1.1 :=
      measurable_fst.comp measurable_subtype_coe
    have hω : Measurable fun a :
        {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C} => a.1.2 :=
      measurable_snd.comp measurable_subtype_coe
    have hfq : ∀ b ∈ markedBonds R C, MeasurableQuaternion
        fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C} =>
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach a.1.1 b : imaginaryQuaternions) : ℍ[ℝ]) := by
      intro b hb
      exact measurableQuaternion_of_continuousOn (hcont C b hb) hv fun a => a.2
    have hmass : Measurable fun a :
        {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C} =>
        coarseStateMass R C a.1.1 (⟨Y, a.1.2⟩ : CoarseState R n) := by
      unfold coarseStateMass
      refine Finset.measurable_fun_sum _ fun bad _ => Finset.measurable_fun_sum _ fun Yt _ =>
        Finset.measurable_fun_sum _ fun b _ => ?_
      exact measurable_massTerm hK hch hS.hasExpansions hfit hS.isCutoff (hblockOf hn₀) C bad Yt b hv hω hfq
    have hint : Measurable fun a :
        {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C} =>
        caseIntegral R C a.1.1 (⟨Y, a.1.2⟩ : CoarseState R n) (caseResponse A a.1.1 y' h) := by
      unfold caseIntegral
      refine Finset.measurable_sum _ fun bad _ => Finset.measurable_sum _ fun Yt _ =>
        Finset.measurable_sum _ fun b _ => ?_
      exact measurable_caseTermIntegral hK hch hS.hasExpansions hfit hS.isCutoff (hblockOf hn₀) C bad Yt b
        hv hω hfq (F := fun a => caseResponse A a.1.1 y' h)
        (measurable_caseResponse hsc hresp hS.hasExpansions hfit (hblockOf hn₀) hv y' h bad Yt b)
    have e : (fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C} =>
        if IsLiveState R.params R.nextCoupling (coarseWeightExpansion R) a.1.1 Y a.1.2 then
          A.hullStep n y' a.1.1 Y a.1.2 h else 0) =
        fun a => if IsHullState R.params R.nextRange a.1.1 Y ∧
            0 < (coarseStateMass R C a.1.1 (⟨Y, a.1.2⟩ : CoarseState R n)).toReal then
          caseIntegral R C a.1.1 (⟨Y, a.1.2⟩ : CoarseState R n) (caseResponse A a.1.1 y' h) /
            (coarseStateMass R C a.1.1 (⟨Y, a.1.2⟩ : CoarseState R n)).toReal else 0 := by
      funext a
      have hC : hotCoreSites R a.1.1 = C := a.2
      have h2 : coarseWeightExpansion R n a.1.1 Y a.1.2 =
          (coarseStateMass R C a.1.1 (⟨Y, a.1.2⟩ : CoarseState R n)).toReal := by
        unfold coarseWeightExpansion
        rw [dif_neg (NeZero.ne n)]
        show coarseStateWeight R (hotCoreSites R a.1.1) a.1.1 ⟨Y, a.1.2⟩ = _
        rw [hC]
        rfl
      have h3 : IsLiveState R.params R.nextCoupling (coarseWeightExpansion R) a.1.1 Y a.1.2 ↔
          IsHullState R.params R.nextRange a.1.1 Y ∧
            0 < (coarseStateMass R C a.1.1 (⟨Y, a.1.2⟩ : CoarseState R n)).toReal := by
        unfold IsLiveState
        rw [h2]
        rfl
      by_cases hl : IsLiveState R.params R.nextCoupling (coarseWeightExpansion R) a.1.1 Y a.1.2
      · rw [if_pos hl, if_pos (h3.mp hl)]
        show caseIntegral R (hotCoreSites R a.1.1) a.1.1 _ _ /
          coarseStateWeight R (hotCoreSites R a.1.1) a.1.1 _ = _
        rw [hC]
        rfl
      · rw [if_neg hl, if_neg fun h' => hl (h3.mpr h')]
    rw [e]
    have hreal := ENNReal.measurable_toReal.comp hmass
    exact Measurable.ite ((hv (measurableSet_isHullState hfit hn.1 R.nextRange Y)).inter
      (measurableSet_lt measurable_const hreal)) (hint.div hreal) measurable_const
end YangMills.Construction.WeightedResponses
end
