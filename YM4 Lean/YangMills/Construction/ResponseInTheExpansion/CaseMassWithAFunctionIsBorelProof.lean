import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.CaseMassWithAFunctionIsBorelForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps StepSettings StepCosts StateMeasurability ColdStepAtMirrorFrames BlockAverages ColdChain
  StepFrames
namespace MassMeasurability
section Hull
variable {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
theorem measurableSet_of_torusHotLumps (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (P : Finset (Finset (TorusSite n)) → Prop) :
    MeasurableSet {W : TorusField n | P (torusHotLumps ℓ W)} := by apply _root_.YangMills.Construction.CoarseMeasurability.measurableSet_of_torusHotLumps <;> assumption
theorem measurableSet_isHullState (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (r : ℕ) (Y : Finset (TorusSite n)) :
    MeasurableSet {W : TorusField n | IsHullState ℓ r W Y} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.measurableSet_setOf_isHullState <;> assumption
end Hull
section State
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
def labelsWithDefault (q : CoarseState R n) (Yt S : Finset (TorusSite (n * R.params.side)))
    (d : Yt → R.labels.Ω) (ν : S → R.labels.Ω) : Yt → R.labels.Ω := fun z =>
  getOrDefault (q.labelAt z) (if h : (z : TorusSite (n * R.params.side)) ∈ S then ν ⟨z, h⟩ else d z)
omit [NeZero n] in
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
omit [NeZero n] in
theorem lintegral_unlabelled_eq (q : CoarseState R n) (Yt S : Finset (TorusSite (n * R.params.side)))
    (d : Yt → R.labels.Ω) (e : q.unlabelled Yt = S) (G : (Yt → R.labels.Ω) → ℝ≥0∞) :
    ∫⁻ ν : q.unlabelled Yt → R.labels.Ω, G (q.fillLabels Yt ν) ∂(Measure.pi fun _ => R.labels.μ) =
      ∫⁻ ν : S → R.labels.Ω, G (labelsWithDefault q Yt S d ν) ∂(Measure.pi fun _ => R.labels.μ) := by
  subst e
  refine lintegral_congr fun ν => ?_
  rw [fillLabels_eq_labelsWithDefault q Yt d ν]
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
theorem measurable_baseLaw_apply (hK : BondKernelBorel) (b : BaseChoice R.params.side n) :
    Measurable fun W : TorusField (n * R.params.side) => baseLaw (R := R) W b := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_baseLaw <;> assumption
open Classical in
def massIntegrand (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt S : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (d : Yt → R.labels.Ω)
    (v : α → TorusField n) (ω : α → Y → CoarseLabel R.labels.Ω R.params.side)
    (Gf : α → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ≥0∞)
    (p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω)) : ℝ≥0∞ :=
  if IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt ∧
      coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩ then
    ENNReal.ofReal (stepWeight R C (v p.1.1)
      (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
      (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b) *
      Gf p.1.1 (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2)
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2)
  else 0
theorem measurable_massIntegrand (hK : BondKernelBorel) (hch : ChartCoordMeasurable)
    (hexp : R.HasExpansions) (hfit : R.params.Admissible) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hblock : IsBlockTorusSide R.params (n * R.params.side))
    [StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side)]
    (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt S : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (d : Yt → R.labels.Ω)
    {v : α → TorusField n} (hv : Measurable v)
    {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    {Gf : α → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ≥0∞}
    (hG : Measurable fun p : α × TorusField (n * R.params.side) × (Yt → R.labels.Ω) => Gf p.1 p.2.1 p.2.2)
    (hf : ∀ b ∈ markedBonds R C, MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable (massIntegrand C bad Yt S b d v ω Gf) := by
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
      IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt} :=
    hWq (measurableSet_isHullState hfit hblock.1 R.range Yt)
  have hT2 : MeasurableSet {p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) |
      coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩} :=
    measurableSet_coarseStateOf_eq C bad b Yt Y (hω.comp hA) hWq hlab
  have hDq := ((hexp.2.borel (n * R.params.side) hblock Yt).1).comp (hWq.prodMk hlab)
  have hB := (measurable_baseLaw_apply (R := R) hK b).comp hWq
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
      (v := fun p : (α × TorusField (n * R.params.side)) × (S → R.labels.Ω) => v p.1.1)
      hcut hch C hv' hWq bad hf'
  have e : massIntegrand C bad Yt S b d v ω Gf = fun p =>
      if IsHullState R.params R.range
          (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt ∧
        coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
          (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩ then
      ENNReal.ofReal ((if IsHullState R.params (clusterRange R.coupling)
            (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt then
          R.labelWeight (n * R.params.side)
            (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
            (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) else 0) *
        baseLaw (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) b *
        (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4, bondKernel R.params R.coupling
          (readAtLevel (stepBlockFrame R.params.side n) 0
            (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2))
          (readAtLevel (stepBlockFrame R.params.side n) 1 (v p.1.1)) b c) *
        markProduct R C (v p.1.1)
          (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) bad) *
        Gf p.1.1 (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2)
          (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2)
      else 0 := by
    funext p
    unfold massIntegrand
    by_cases h : IsHullState R.params R.range
        (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt ∧
      coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω p.1.1⟩ : CoarseState R n) p.1.2) Yt
        (labelsWithDefault (⟨Y, ω p.1.1⟩ : CoarseState R n) Yt S d p.2) bad b = ⟨Y, ω p.1.1⟩
    · rw [if_pos h, if_pos h, if_pos (show IsHullState R.params (clusterRange R.coupling) _ Yt from h.1)]
      rfl
    · rw [if_neg h, if_neg h]
  rw [e]
  exact Measurable.ite (hT1.inter hT2)
    ((ENNReal.measurable_ofReal.comp (((hDq.mul hB).mul hker).mul hM)).mul
      (hG.comp (hA.prodMk (hWq.prodMk hlab)))) measurable_const
theorem measurable_lintegral_massIntegrand (hK : BondKernelBorel) (hch : ChartCoordMeasurable)
    (hexp : R.HasExpansions) (hfit : R.params.Admissible) (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hblock : IsBlockTorusSide R.params (n * R.params.side))
    [StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side)]
    (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    {v : α → TorusField n} (hv : Measurable v)
    {ω : α → Y → CoarseLabel R.labels.Ω R.params.side} (hω : Measurable ω)
    {Gf : α → TorusField (n * R.params.side) → (Yt → R.labels.Ω) → ℝ≥0∞}
    (hG : Measurable fun p : α × TorusField (n * R.params.side) × (Yt → R.labels.Ω) => Gf p.1 p.2.1 p.2.2)
    (hf : ∀ b ∈ markedBonds R C, MeasurableQuaternion fun a =>
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach (v a) b : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun a => ∫⁻ W, ∫⁻ ν : CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt → R.labels.Ω,
      (open Classical in
        if IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt ∧
          coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt
            (CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν) bad b = ⟨Y, ω a⟩ then
          ENNReal.ofReal (stepWeight R C (v a) (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt
            (CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν) bad b) *
            Gf a (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W)
              (CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν) else 0)
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
    have hi := measurable_massIntegrand hK hch hexp hfit hcut hblock C bad Yt S b d
      (hv.comp hsub) (hω.comp hsub) (Gf := fun a => Gf a.1)
      (hG.comp ((hsub.comp measurable_fst).prodMk measurable_snd)) (fun b' hb' => by
        have h := measurableQuaternion_comp (hf b' hb') hsub
        exact h)
    have h1 := (hi.lintegral_prod_right' (ν := Measure.pi fun _ : S => R.labels.μ)).lintegral_prod_right'
      (ν := fieldHaar (n * R.params.side))
    convert h1 using 2 with x
    refine lintegral_congr fun W => ?_
    exact lintegral_unlabelled_eq _ Yt S d x.2 fun l =>
      if IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) Yt ∧
          coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) Yt l bad b =
            ⟨Y, ω x⟩ then
        ENNReal.ofReal (stepWeight R C (v x) (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W)
          Yt l bad b) *
          Gf x (CoarseState.fieldWithStoredLinks (⟨Y, ω x⟩ : CoarseState R n) W) l
      else 0
  · have hemp : ∀ a, IsEmpty (CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt → R.labels.Ω) :=
      fun a => ⟨fun ν => hne ⟨CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν⟩⟩
    have e : (fun a => ∫⁻ W, ∫⁻ ν : CoarseState.unlabelled (⟨Y, ω a⟩ : CoarseState R n) Yt → R.labels.Ω,
      (open Classical in
        if IsHullState R.params R.range (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt ∧
          coarseStateOf R C (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt
            (CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν) bad b = ⟨Y, ω a⟩ then
          ENNReal.ofReal (stepWeight R C (v a) (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W) Yt
            (CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν) bad b) *
            Gf a (CoarseState.fieldWithStoredLinks (⟨Y, ω a⟩ : CoarseState R n) W)
              (CoarseState.fillLabels (⟨Y, ω a⟩ : CoarseState R n) Yt ν) else 0)
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
theorem configurationMassMeasurability (hK : BondKernelBorel) (hch : ChartCoordMeasurable)
    (hfr : continuousOn_frameCoord_of_cold) (hlb : CoarseLabelMeasureByShapes) :
    ConfigurationMassMeasurability := by
  classical
  intro T hT y R htab hwp n _ hn
  have hfit := hwp.admissible
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn₀ : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hL0) hn.2
  have hblock : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  have : StandardBorelSpace (CoarseLabel R.labels.Ω R.params.side) :=
    (hlb R.labels.Ω R.labels.μ R.params.side).2.1 inferInstance
  have hr40 : 2 ^ 40 ≤ R.range := le_trans (Nat.le_mul_of_pos_right _ hL0) hwp.range_ge_side
  have hr' : 2 ^ 16 ≤ R.nextRange := hwp.nextRange_ge
  have hab := hwp.range_le
  have hm16 : 16 ≤ R.frameReach := by
    unfold StepSetup.frameReach
    norm_num at hr40 ⊢
    omega
  have hmr : R.frameReach ≤ R.range / 2 ^ 11 := le_refl _
  have hm : R.frameReach ≤ 2 * R.nextRange := by
    norm_num at hr' hmr
    omega
  have n64 : 64 ≤ n := le_trans (by have := hfit.n₀_ge; omega) hn₀
  have ha : R.params.coupling = T.coupling := by rw [htab.params_eq]; rfl
  have hLT : R.params.side = T.side := by rw [htab.params_eq]; rfl
  have hσ : R.params.threshold = T.threshold := by rw [htab.params_eq]; rfl
  have hchain : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [ha, hLT, htab.anchorRadius_eq]
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
  have hCset : ∀ C : Finset (TorusSite n), MeasurableSet {V : TorusField n | hotCoreSites R V = C} := fun C =>
    measurableSet_of_torusHotLumps hfit hn.1 fun H => thickening (2 * R.nextRange) (H.biUnion id) = C
  have hlo' : ∀ (Yt : Finset (TorusSite (n * R.params.side))) (q : CoarseState R n),
      Measurable fun ν : q.unlabelled Yt → R.labels.Ω => q.fillLabels Yt ν := by
    intro Yt q
    by_cases hne : Nonempty (Yt → R.labels.Ω)
    · obtain ⟨d⟩ := hne
      have e : (fun ν : q.unlabelled Yt → R.labels.Ω => q.fillLabels Yt ν) =
          fun ν => labelsWithDefault (⟨q.1, (fun (_ : Unit) => q.2) ()⟩ : CoarseState R n) Yt
            (q.unlabelled Yt) d ν := by
        funext ν
        exact fillLabels_eq_labelsWithDefault q Yt d ν
      rw [e]
      exact measurable_labelsWithDefault (ω := fun _ : Unit => q.2) measurable_const Yt (q.unlabelled Yt) d
        (f := fun _ => ()) measurable_const measurable_id
    · have : IsEmpty (q.unlabelled Yt → R.labels.Ω) := ⟨fun ν => hne ⟨q.fillLabels Yt ν⟩⟩
      exact measurable_of_empty _
  refine ⟨hCset, fun Y => measurableSet_isHullState hfit hn.1 R.nextRange Y, hlo',
    fun bad Yt b G hG Y => ?_, fun C bad Yt b q => ?_⟩
  · refine measurable_of_countable_cover (fun C : Finset (TorusSite n) =>
      {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) | hotCoreSites R p.1 = C})
      (fun C => measurable_fst (hCset C)) (fun p => ⟨_, rfl⟩) fun C => ?_
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
    have hmass := measurable_lintegral_massIntegrand hK hch hwp.hasExpansions hfit hwp.isCutoff hblock C bad Yt b
      hv hω (Gf := fun a => G a.1.1) (hG.comp ((hv.comp measurable_fst).prodMk measurable_snd)) hfq
    have e : (fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) |
          hotCoreSites R p.1 = C} =>
        configurationMassWith R (hotCoreSites R a.1.1) a.1.1 bad Yt b (G a.1.1) ⟨Y, a.1.2⟩) =
        fun a => configurationMassWith R C a.1.1 bad Yt b (G a.1.1) ⟨Y, a.1.2⟩ := by
      funext a
      rw [show hotCoreSites R a.1.1 = C from a.2]
    show Measurable fun a : {p : TorusField n × (Y → CoarseLabel R.labels.Ω R.params.side) |
        hotCoreSites R p.1 = C} =>
      configurationMassWith R (hotCoreSites R a.1.1) a.1.1 bad Yt b (G a.1.1) ⟨Y, a.1.2⟩
    rw [e]
    exact hmass
  · by_cases hne : Nonempty (Yt → R.labels.Ω)
    · obtain ⟨d⟩ := hne
      have hfo : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
          q.fieldWithStoredLinks p.1 :=
        (measurable_fieldWithStoredLinks (R := R) q.1).comp (measurable_const.prodMk measurable_fst)
      have hlo : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
          q.fillLabels Yt p.2 :=
        (hlo' Yt q).comp measurable_snd
      exact (hfo (measurableSet_isHullState hfit hblock.1 R.range Yt)).inter
        (measurableSet_coarseStateOf_eq C bad b Yt q.1
          (ω := fun _ : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) => q.2)
          measurable_const hfo hlo)
    · have : IsEmpty (TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω)) :=
        ⟨fun p => hne ⟨q.fillLabels Yt p.2⟩⟩
      exact Subsingleton.measurableSet
end MassMeasurability
end YangMills.Construction.ResponseInTheExpansion
end
