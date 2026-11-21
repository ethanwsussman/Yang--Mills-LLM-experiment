import YangMills.Construction.Lattice.GeometryOfASeparatedSequenceProof
import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsInTheFineCaseProof
import YangMills.Construction.Torus.AveragingOperatorAndMatricesProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Weighted.WeightedDistBounds
import YangMills.Construction.Weighted.WeightedLengthLipBounds
import Mathlib
set_option autoImplicit false
open Set MeasureTheory Filter Topology YangMills.Construction.TorusMetric
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.Weighted.DistBounds
section Metric
set_option linter.unusedSectionVars false
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
def slowSet (f : X → ℝ) (c : ℝ≥0) (j : ℕ) : Set X :=
  {x | ∀ x', dist x' x < 1 / ((j : ℝ) + 1) → |f x' - f x| ≤ c * dist x' x}
theorem isClosed_slowSet {f : X → ℝ} (hf : Continuous f) (c : ℝ≥0) (j : ℕ) :
    IsClosed (slowSet f c j) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' : ¬ ∀ x', dist x' x < 1 / ((j : ℝ) + 1) → |f x' - f x| ≤ c * dist x' x := hx
  push Not at hx'
  obtain ⟨x', hd, hlt⟩ := hx'
  have h₁ : ∀ᶠ z in 𝓝 x, dist x' z < 1 / ((j : ℝ) + 1) :=
    (continuous_const.dist continuous_id).continuousAt.eventually_lt continuousAt_const hd
  have h₂ : ∀ᶠ z in 𝓝 x, (c : ℝ) * dist x' z < |f x' - f z| :=
    (continuous_const.mul (continuous_const.dist continuous_id)).continuousAt.eventually_lt
      ((continuous_const.sub hf).abs.continuousAt) hlt
  filter_upwards [h₁, h₂] with z hz hz' hmem
  exact absurd (hmem x' hz) (not_le.2 hz')
theorem volume_image_le_mul_hausdorff {f : X → ℝ} (hf : Continuous f) (c : ℝ≥0) {F : Set X}
    (hF : MeasurableSet F) (hslow : F ⊆ ⋃ j, slowSet f c j) :
    volume (f '' F) ≤ c * (μH[1] : Measure X) F := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have : F = ∅ := Set.eq_empty_of_isEmpty F
    simp [this]
  let u : ℕ → X := TopologicalSpace.denseSeq X
  have hu : DenseRange u := TopologicalSpace.denseRange_denseSeq X
  let Q : ℕ → Set X := fun m =>
    F ∩ slowSet f c m.unpair.1 ∩ Metric.ball (u m.unpair.2) (1 / (2 * ((m.unpair.1 : ℝ) + 1)))
  have hQm : ∀ m, MeasurableSet (Q m) := fun m =>
    (hF.inter (isClosed_slowSet hf c _).measurableSet).inter Metric.isOpen_ball.measurableSet
  have hQu : ⋃ m, Q m = F := by
    apply Subset.antisymm
    · exact iUnion_subset fun m => inter_subset_left.trans inter_subset_left
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.1 (hslow hx)
      have hr : (0 : ℝ) < 1 / (2 * ((j : ℝ) + 1)) := by positivity
      obtain ⟨i, hi⟩ := hu.exists_dist_lt x hr
      refine mem_iUnion.2 ⟨Nat.pair j i, ?_⟩
      simp only [Q, Nat.unpair_pair]
      exact ⟨⟨hx, hj⟩, by simpa [Metric.mem_ball] using hi⟩
  have hlip : ∀ m, LipschitzOnWith c f (Q m) := by
    intro m
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx x' hx'
    have hd : dist x x' < 1 / ((m.unpair.1 : ℝ) + 1) := by
      have h₁ := hx.2
      have h₂ := hx'.2
      rw [Metric.mem_ball] at h₁ h₂
      have h₃ := dist_triangle_right x x' (u m.unpair.2)
      have h₄ : 1 / ((m.unpair.1 : ℝ) + 1) =
          1 / (2 * ((m.unpair.1 : ℝ) + 1)) + 1 / (2 * ((m.unpair.1 : ℝ) + 1)) := by
        field_simp
        norm_num
      linarith
    have := hx'.1.2 x hd
    rwa [Real.dist_eq]
  have hdis : Pairwise (Function.onFun Disjoint (disjointed Q)) := disjoint_disjointed Q
  have hdm : ∀ m, MeasurableSet (disjointed Q m) := fun m => MeasurableSet.disjointed hQm m
  have hun : ⋃ m, disjointed Q m = F := by rw [iUnion_disjointed, hQu]
  calc volume (f '' F) = volume (⋃ m, f '' disjointed Q m) := by
        rw [← image_iUnion, hun]
    _ ≤ ∑' m : ℕ, volume (f '' disjointed Q m) := measure_iUnion_le _
    _ ≤ ∑' m : ℕ, (c : ℝ≥0∞) * (μH[1] : Measure X) (disjointed Q m) := by
        refine ENNReal.tsum_le_tsum fun m => ?_
        have h := ((hlip m).mono (disjointed_subset Q m)).hausdorffMeasure_image_le
          (d := 1) zero_le_one
        simpa [hausdorffMeasure_real] using h
    _ = c * (μH[1] : Measure X) F := by
        rw [ENNReal.tsum_mul_left, ← measure_iUnion hdis hdm, hun]
theorem volume_image_le_setLIntegral {f : X → ℝ} (hf : Continuous f) {E : Set X}
    (hE : MeasurableSet E) (hfin : (μH[1] : Measure X) E ≠ ⊤) (g : X → ℝ≥0∞)
    (hbig : ∀ x ∈ E, ∃ c : ℝ≥0, g x < c)
    (hg : ∀ x ∈ E, ∀ c : ℝ≥0, g x < c → x ∈ ⋃ j, slowSet f c j) :
    volume (f '' E) ≤ ∫⁻ x in E, g x ∂(μH[1] : Measure X) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ (δ : ℝ≥0∞) * (μH[1] : Measure X) E ≤ ε := by
    by_cases h0 : (μH[1] : Measure X) E = 0
    · exact ⟨1, one_pos, by simp [h0]⟩
    · refine ⟨ε / ((μH[1] : Measure X) E).toNNReal, div_pos hε
        (ENNReal.toNNReal_pos h0 hfin), ?_⟩
      have h1 : ((μH[1] : Measure X) E) = (((μH[1] : Measure X) E).toNNReal : ℝ≥0∞) :=
        (ENNReal.coe_toNNReal hfin).symm
      rw [h1, ← ENNReal.coe_mul, ENNReal.toNNReal_coe, div_mul_cancel₀ _
        (ENNReal.toNNReal_pos h0 hfin).ne']
  let T : ℕ → Set X := fun k => E ∩ ⋃ j, slowSet f (k * δ) j
  have hTm : ∀ k, MeasurableSet (T k) := fun k =>
    hE.inter (MeasurableSet.iUnion fun j => (isClosed_slowSet hf _ j).measurableSet)
  have hTu : ⋃ k, T k = E := by
    apply Subset.antisymm (iUnion_subset fun k => inter_subset_left)
    intro x hx
    obtain ⟨c, hc⟩ := hbig x hx
    obtain ⟨k, hk⟩ := exists_nat_gt (c / δ)
    refine mem_iUnion.2 ⟨k, hx, hg x hx _ (hc.trans ?_)⟩
    rw [div_lt_iff₀ hδ] at hk
    exact_mod_cast hk
  have hdis : Pairwise (Function.onFun Disjoint (disjointed T)) := disjoint_disjointed T
  have hdm : ∀ k, MeasurableSet (disjointed T k) := fun k => MeasurableSet.disjointed hTm k
  have hun : ⋃ k, disjointed T k = E := by rw [iUnion_disjointed, hTu]
  have hsub : ∀ k, disjointed T k ⊆ E := fun k =>
    (disjointed_subset T k).trans inter_subset_left
  have hstep : ∀ k, ∀ x ∈ disjointed T k, ((k * δ : ℝ≥0) : ℝ≥0∞) ≤ g x + δ := by
    intro k x hx
    cases k with
    | zero => simp
    | succ k =>
      by_contra hlt
      rw [not_le] at hlt
      have hgx : g x < ((k * δ : ℝ≥0) : ℝ≥0∞) := by
        have h₃ : (((k + 1 : ℕ) * δ : ℝ≥0) : ℝ≥0∞) = ((k * δ : ℝ≥0) : ℝ≥0∞) + δ := by
          push_cast
          ring
        rw [h₃] at hlt
        exact lt_of_add_lt_add_right hlt
      have hxk : x ∈ T k := ⟨hsub _ hx, hg x (hsub _ hx) _ hgx⟩
      rw [disjointed_eq_inter_compl] at hx
      exact (mem_iInter₂.1 hx.2 k (Nat.lt_succ_self k)) hxk
  calc volume (f '' E) = volume (⋃ k, f '' disjointed T k) := by rw [← image_iUnion, hun]
    _ ≤ ∑' k : ℕ, volume (f '' disjointed T k) := measure_iUnion_le _
    _ ≤ ∑' k : ℕ, ((k * δ : ℝ≥0) : ℝ≥0∞) * (μH[1] : Measure X) (disjointed T k) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        refine volume_image_le_mul_hausdorff hf _ (hdm k) ?_
        exact (disjointed_subset T k).trans inter_subset_right
    _ ≤ ∑' k : ℕ, ∫⁻ x in disjointed T k, (g x + δ) ∂(μH[1] : Measure X) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        calc ((k * δ : ℝ≥0) : ℝ≥0∞) * (μH[1] : Measure X) (disjointed T k)
            = ∫⁻ _ in disjointed T k, ((k * δ : ℝ≥0) : ℝ≥0∞) ∂(μH[1] : Measure X) := by
              simp
          _ ≤ _ := setLIntegral_mono' (hdm k) (hstep k)
    _ = ∫⁻ x in E, (g x + δ) ∂(μH[1] : Measure X) := by
        rw [← lintegral_iUnion hdm hdis, hun]
    _ = (∫⁻ x in E, g x ∂(μH[1] : Measure X)) + δ * (μH[1] : Measure X) E := by
        rw [lintegral_add_right _ measurable_const]
        simp
    _ ≤ _ := by gcongr
end Metric
section TorusSegments
variable {S : ℝ}
theorem torusProj_sub (a b : Fin 4 → ℝ) :
    torusProj S a - torusProj S b = torusProj S (a - b) := by apply _root_.YangMills.SharedProofs.p13492 <;> assumption
theorem torusProj_surjective (x : Torus4 S) : ∃ a : Fin 4 → ℝ, torusProj S a = x := by
  choose b hb _ using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  exact ⟨b, funext hb⟩
theorem torusL1Norm_torusProj_le (a : Fin 4 → ℝ) :
    torusL1Norm (torusProj S a) ≤ l1NormVec a := by
  rw [torusL1Norm_eq_sum_norm]
  exact Finset.sum_le_sum fun μ _ => addCircle_norm_coe_le_abs _
theorem l1NormVec_nonneg (a : Fin 4 → ℝ) : 0 ≤ l1NormVec a :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem l1NormVec_smul (u : ℝ) (a : Fin 4 → ℝ) : l1NormVec (u • a) = |u| * l1NormVec a := by
  simp [l1NormVec, abs_mul, Finset.mul_sum]
theorem pointAt_sub_pointAt (s : LiftedSegment) (u u' : ℝ) :
    s.pointAt S u - s.pointAt S u' = torusProj S ((u - u') • s.displacement) := by
  rw [LiftedSegment.pointAt, LiftedSegment.pointAt, torusProj_sub]
  congr 1
  funext μ
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem pointAt_zero (s : LiftedSegment) : s.pointAt S 0 = torusProj S s.tail := by
  simp [LiftedSegment.pointAt]
theorem pointAt_one (s : LiftedSegment) : s.pointAt S 1 = torusProj S s.head := by
  simp [LiftedSegment.pointAt, LiftedSegment.displacement]
variable [Fact (0 < S)]
theorem continuous_pointAt (s : LiftedSegment) : Continuous (s.pointAt S) := by
  refine continuous_pi fun μ => ?_
  have : Continuous fun u : ℝ => (s.tail + u • s.displacement) μ := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  exact (AddCircle.continuous_mk' S).comp this
theorem segmentsSupport_cons (s : LiftedSegment) (Γ : List LiftedSegment) :
    segmentsSupport S (s :: Γ) = s.support S ∪ segmentsSupport S Γ := by
  simp only [segmentsSupport, List.mem_cons, iUnion_iUnion_eq_or_left]
theorem segmentsSupport_singleton (s : LiftedSegment) : segmentsSupport S [s] = s.support S := by
  rw [segmentsSupport_cons]
  simp [segmentsSupport]
theorem isCompact_image_Icc (s : LiftedSegment) (a b : ℝ) : IsCompact (s.pointAt S '' Icc a b) :=
  isCompact_Icc.image (continuous_pointAt s)
theorem measurableSet_segmentsSupport (Γ : List LiftedSegment) :
    MeasurableSet (segmentsSupport S Γ) := by
  induction Γ with
  | nil => simp [segmentsSupport]
  | cons s Γ ih =>
    rw [segmentsSupport_cons]
    exact (isCompact_image_Icc s 0 1).measurableSet.union ih
theorem isTreeGraph_singleton (s : LiftedSegment) : IsTreeGraph S [s] := by
  rw [IsTreeGraph, segmentsSupport_singleton]
  exact (isConnected_Icc zero_le_one).image _ (continuous_pointAt s).continuousOn
theorem dist_toLp_toLp (x x' : Torus4 S) :
    dist (WithLp.toLp 1 x : TorusL1 S) (WithLp.toLp 1 x') = torusL1Norm (x - x') := by
  rw [dist_eq_norm, ← WithLp.toLp_sub, norm_toLp_eq_torusL1Norm]
theorem dist_eq_torusL1Norm (p q : TorusL1 S) : dist p q = torusL1Norm (p.ofLp - q.ofLp) := by
  have := dist_toLp_toLp (S := S) p.ofLp q.ofLp
  simpa using this
theorem measurableEmbedding_ofLp :
    MeasurableEmbedding (WithLp.ofLp : TorusL1 S → Torus4 S) :=
  (PiLp.homeomorph 1 fun _ : Fin 4 => AddCircle S).toMeasurableEquiv.measurableEmbedding
theorem l1LengthMeasure_apply (A : Set (Torus4 S)) :
    l1LengthMeasure S A = (μH[1] : Measure (TorusL1 S)) (WithLp.ofLp ⁻¹' A) :=
  measurableEmbedding_ofLp.map_apply _ _
theorem l1LengthMeasure_singleton (p : Torus4 S) : l1LengthMeasure S {p} = 0 := by
  rw [l1LengthMeasure_apply]
  have : (WithLp.ofLp ⁻¹' {p} : Set (TorusL1 S)) = {WithLp.toLp 1 p} := by
    ext q
    constructor
    · intro h
      have h' : q.ofLp = p := h
      simp [← h']
    · rintro rfl
      rfl
  rw [this]
  have := Measure.nullSingletonClass_hausdorff (TorusL1 S) one_pos
  exact measure_singleton _
theorem l1LengthMeasure_image_Icc_le (s : LiftedSegment) {a b : ℝ} :
    l1LengthMeasure S (s.pointAt S '' Icc a b) ≤
      ENNReal.ofReal (l1NormVec s.displacement * (b - a)) := by
  have hK : 0 ≤ l1NormVec s.displacement := l1NormVec_nonneg _
  have hlip : LipschitzWith (l1NormVec s.displacement).toNNReal
      (fun u : ℝ => (WithLp.toLp 1 (s.pointAt S u) : TorusL1 S)) := by
    refine LipschitzWith.of_dist_le_mul fun u u' => ?_
    rw [dist_toLp_toLp, pointAt_sub_pointAt, Real.dist_eq, Real.coe_toNNReal _ hK]
    refine (torusL1Norm_torusProj_le _).trans ?_
    rw [l1NormVec_smul, mul_comm]
  have himg : (WithLp.ofLp ⁻¹' (s.pointAt S '' Icc a b) : Set (TorusL1 S)) =
      (fun u : ℝ => (WithLp.toLp 1 (s.pointAt S u) : TorusL1 S)) '' Icc a b := by
    ext q
    constructor
    · rintro ⟨u, hu, h⟩
      exact ⟨u, hu, by simp [h]⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
  rw [l1LengthMeasure_apply, himg]
  have h := (hlip.lipschitzOnWith (s := Icc a b)).hausdorffMeasure_image_le
    (d := 1) zero_le_one
  refine h.trans ?_
  rw [hausdorffMeasure_real, Real.volume_Icc, ENNReal.rpow_one, ENNReal.ofReal_mul hK]
  exact le_rfl
theorem l1LengthMeasure_segmentsSupport_ne_top (Γ : List LiftedSegment) :
    l1LengthMeasure S (segmentsSupport S Γ) ≠ ⊤ := by
  induction Γ with
  | nil => simp [segmentsSupport]
  | cons s Γ ih =>
    rw [segmentsSupport_cons]
    refine ne_top_of_le_ne_top ?_ (measure_union_le _ _)
    exact ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (l1LengthMeasure_image_Icc_le s), ih⟩
theorem LipschitzL1.exists_lipschitzWith_ofLp {f : Torus4 S → ℝ} (hf : LipschitzL1 f) :
    ∃ C : ℝ≥0, LipschitzWith C fun p : TorusL1 S => f p.ofLp := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, LipschitzWith.of_dist_le_mul fun p q => ?_⟩
  rw [dist_eq_torusL1Norm, Real.dist_eq]
  exact hC _ _
theorem LipschitzL1.continuous {f : Torus4 S → ℝ} (hf : LipschitzL1 f) : Continuous f := by
  obtain ⟨C, hC⟩ := LipschitzL1.exists_lipschitzWith_ofLp hf
  have h := hC.continuous.comp (PiLp.continuous_toLp 1 fun _ : Fin 4 => AddCircle S)
  exact h
theorem localLip_le {f : Torus4 S → ℝ} {C : ℝ≥0}
    (hC : ∀ x x', |f x' - f x| ≤ C * torusL1Norm (x' - x)) (x : Torus4 S) :
    localLip f x ≤ C := by
  refine limsup_le_of_le (h := Eventually.of_forall fun x' => ?_)
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hn : 0 ≤ torusL1Norm (x' - x) := by
    rw [torusL1Norm_eq_sum_norm]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  rcases hn.eq_or_lt with h0 | h0
  · simp [← h0]
  · exact (div_le_iff₀ h0).2 (hC x x')
theorem toLp_mem_slowSet_of_localLip_lt (f : Torus4 S → ℝ) (x : Torus4 S) (c : ℝ≥0)
    (h : localLip f x < c) :
    (WithLp.toLp 1 x : TorusL1 S) ∈ ⋃ j, slowSet (fun p : TorusL1 S => f p.ofLp) c j := by
  have h₁ := eventually_lt_of_limsup_lt h
  rw [eventually_nhdsWithin_iff] at h₁
  have h₂ : ∀ᶠ p in 𝓝 (WithLp.toLp 1 x : TorusL1 S), p.ofLp ∈ ({x}ᶜ : Set (Torus4 S)) →
      ENNReal.ofReal (|f p.ofLp - f x| / torusL1Norm (p.ofLp - x)) < c :=
    ((PiLp.continuous_ofLp 1 fun _ : Fin 4 => AddCircle S).tendsto
      (WithLp.toLp 1 x : TorusL1 S)).eventually h₁
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 h₂
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  refine mem_iUnion.2 ⟨j, fun p hp => ?_⟩
  have hlt := hball (hp.trans hj)
  have hd : dist p (WithLp.toLp 1 x : TorusL1 S) = torusL1Norm (p.ofLp - x) := by
    rw [dist_eq_torusL1Norm]
  simp only [WithLp.ofLp_toLp]
  rw [hd]
  by_cases hpx : p.ofLp = x
  · rw [← hd, hpx]
    simp only [sub_self, abs_zero]
    positivity
  · have hpos : 0 < torusL1Norm (p.ofLp - x) := by
      rw [← hd]
      refine dist_pos.2 fun h => hpx ?_
      rw [h]
    have h₃ := hlt hpx
    have h₄ : |f p.ofLp - f x| / torusL1Norm (p.ofLp - x) < c := by
      rwa [ENNReal.ofReal_lt_coe_iff (by positivity)] at h₃
    exact ((div_lt_iff₀ hpos).1 h₄).le
theorem abs_sub_le_setLIntegral_localLip {f : Torus4 S → ℝ} (hf : LipschitzL1 f)
    {Γ : List LiftedSegment} (hΓ : IsTreeGraph S Γ) {x x' : Torus4 S}
    (hx : x ∈ segmentsSupport S Γ) (hx' : x' ∈ segmentsSupport S Γ) :
    ENNReal.ofReal |f x - f x'| ≤
      setLIntegralL1 (segmentsSupport S Γ) (localLip f) := by
  obtain ⟨C, hC⟩ := hf
  have hf' : LipschitzL1 f := ⟨C, hC⟩
  have hint : setLIntegralL1 (segmentsSupport S Γ) (localLip f) =
      ∫⁻ p in (WithLp.ofLp ⁻¹' segmentsSupport S Γ : Set (TorusL1 S)), localLip f p.ofLp
        ∂(μH[1] : Measure (TorusL1 S)) :=
    by
      unfold setLIntegralL1 l1LengthMeasure
      rw [Measure.restrict_map measurableEmbedding_ofLp.measurable
        (measurableSet_segmentsSupport Γ), measurableEmbedding_ofLp.lintegral_map]
  have hcont := LipschitzL1.continuous hf'
  have hmeas : MeasurableSet (WithLp.ofLp ⁻¹' segmentsSupport S Γ : Set (TorusL1 S)) :=
    measurableEmbedding_ofLp.measurable (measurableSet_segmentsSupport Γ)
  have hfin : (μH[1] : Measure (TorusL1 S)) (WithLp.ofLp ⁻¹' segmentsSupport S Γ) ≠ ⊤ := by
    rw [← l1LengthMeasure_apply]
    exact l1LengthMeasure_segmentsSupport_ne_top Γ
  have hcont' : Continuous fun p : TorusL1 S => f p.ofLp :=
    hcont.comp (PiLp.continuous_ofLp 1 fun _ : Fin 4 => AddCircle S)
  have himg : (fun p : TorusL1 S => f p.ofLp) '' (WithLp.ofLp ⁻¹' segmentsSupport S Γ) =
      f '' segmentsSupport S Γ := by
    ext r
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.ofLp, hp, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨WithLp.toLp 1 z, hz, rfl⟩
  have hmain := volume_image_le_setLIntegral hcont' hmeas hfin
    (fun p => localLip f p.ofLp)
    (fun p _ => ⟨C + 1, lt_of_le_of_lt (localLip_le hC p.ofLp) (by
      exact_mod_cast lt_add_one C)⟩)
    (fun p _ c hc => by simpa using toLp_mem_slowSet_of_localLip_lt f p.ofLp c hc)
  rw [himg] at hmain
  rw [hint]
  refine le_trans ?_ hmain
  have hsub : uIcc (f x) (f x') ⊆ f '' segmentsSupport S Γ :=
    (hΓ.image f hcont.continuousOn).isPreconnected.ordConnected.uIcc_subset
      ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
  refine le_trans (le_of_eq ?_) (measure_mono hsub)
  rw [uIcc, Real.volume_Icc, max_sub_min_eq_abs']
end TorusSegments
section Density
theorem one_le_L (D : TorusData) : (1 : ℝ) ≤ D.L := by
  have := D.blocking.three_le_factor
  exact_mod_cast (by omega : 1 ≤ D.L)
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem scale_mono (D : TorusData) {m n : ℕ} (h : m ≤ n) : D.scale m ≤ D.scale n :=
  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_L D) h) D.bareSpacing_pos.le
theorem scale_succ (D : TorusData) (n : ℕ) : D.scale (n + 1) = D.L * D.scale n := by
  simp only [TorusData.scale]
  ring
theorem scale_inv_anti (D : TorusData) {m n : ℕ} (h : m ≤ n) : (D.scale n)⁻¹ ≤ (D.scale m)⁻¹ :=
  inv_anti₀ (scale_pos D m) (scale_mono D h)
variable {D : TorusData} (B : SeparatedChain D)
theorem stage_anti {m k : ℕ} (h : m ≤ k) : B.stage k ⊆ B.stage m := by
  induction k, h using Nat.le_induction with
  | base => exact Subset.rfl
  | succ k _ ih =>
    refine Subset.trans ?_ ih
    by_cases hk : k < D.top
    · exact B.decreasing k hk
    · rw [B.empty_above (k + 1) (by omega)]
      exact empty_subset _
theorem weightDensity_term_nonneg (n : ℕ) (x : D.Space) :
    0 ≤ (D.scale n)⁻¹ * (B.layer n).indicator (fun _ => (1 : ℝ)) x :=
  mul_nonneg (inv_nonneg.2 (scale_pos D n).le) (indicator_nonneg (fun _ _ => zero_le_one) x)
theorem inv_scale_le_weightDensity (n : ℕ) (x : D.Space) (hx : x ∉ B.stage (n + 1)) :
    (D.scale n)⁻¹ ≤ B.weightDensity x := by
  have hlast : 0 ≤ (D.scale 0)⁻¹ * (B.stage 1)ᶜ.indicator (fun _ => (1 : ℝ)) x :=
    mul_nonneg (inv_nonneg.2 (scale_pos D 0).le) (indicator_nonneg (fun _ _ => zero_le_one) x)
  by_cases h1 : x ∈ B.stage 1
  · classical
    have htop : 1 ≤ D.top := by
      by_contra hlt
      rw [B.empty_above 1 (by omega)] at h1
      exact h1
    let P : ℕ → Prop := fun m => x ∈ B.stage m
    let m := Nat.findGreatest P D.top
    have hm : x ∈ B.stage m := Nat.findGreatest_spec (P := P) htop h1
    have hm1 : 1 ≤ m := Nat.le_findGreatest htop h1
    have hmt : m ≤ D.top := Nat.findGreatest_le _
    have hnext : x ∉ B.stage (m + 1) := by
      by_cases hlt : m < D.top
      · exact Nat.findGreatest_is_greatest (P := P) (Nat.lt_succ_self m) hlt
      · rw [B.empty_above (m + 1) (by omega)]
        exact notMem_empty x
    have hmn : m ≤ n := by
      by_contra hlt
      exact hx (stage_anti B (by omega) hm)
    have hlayer : x ∈ B.layer m := by
      unfold SeparatedChain.layer
      split_ifs with h h'
      · exact subset_closure ⟨hm, hnext⟩
      · exact hm
      · omega
    have hsum : (D.scale m)⁻¹ * (B.layer m).indicator (fun _ => (1 : ℝ)) x ≤
        ∑ k ∈ Finset.Icc 1 D.top, (D.scale k)⁻¹ * (B.layer k).indicator (fun _ => (1 : ℝ)) x :=
      Finset.single_le_sum (f := fun k => (D.scale k)⁻¹ *
        (B.layer k).indicator (fun _ => (1 : ℝ)) x) (fun k _ => weightDensity_term_nonneg B k x)
        (Finset.mem_Icc.2 ⟨hm1, hmt⟩)
    rw [indicator_of_mem hlayer, mul_one] at hsum
    unfold SeparatedChain.weightDensity
    have := scale_inv_anti D hmn
    linarith
  · have hsum : 0 ≤ ∑ k ∈ Finset.Icc 1 D.top, (D.scale k)⁻¹ *
        (B.layer k).indicator (fun _ => (1 : ℝ)) x :=
      Finset.sum_nonneg fun k _ => weightDensity_term_nonneg B k x
    unfold SeparatedChain.weightDensity
    rw [indicator_of_mem (mem_compl h1), mul_one]
    have := scale_inv_anti D (Nat.zero_le n)
    linarith
theorem pathLengthIn_nonneg {S : ℝ} (Γ : List LiftedSegment) (A : Set (Torus4 S)) :
    0 ≤ pathLengthIn S Γ A := by
  refine List.sum_nonneg ?_
  intro r hr
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hr
  exact mul_nonneg (l1NormVec_nonneg _) ENNReal.toReal_nonneg
theorem weightedLength_nonneg (Γ : List LiftedSegment) : 0 ≤ B.weightedLength Γ := by
  refine add_nonneg (Finset.sum_nonneg fun n _ => ?_) ?_
  · exact mul_nonneg (inv_nonneg.2 (scale_pos D n).le) (pathLengthIn_nonneg _ _)
  · exact mul_nonneg (inv_nonneg.2 (scale_pos D 0).le) (pathLengthIn_nonneg _ _)
theorem weightedDistance_le_weightedLength_singleton (s : LiftedSegment) {p q : D.Space}
    (hp : p ∈ s.support D.side) (hq : q ∈ s.support D.side) :
    B.weightedDistance p q ≤ B.weightedLength [s] := by
  refine csInf_le ⟨0, ?_⟩ ⟨[s], isTreeGraph_singleton s, ?_, ?_, rfl⟩
  · rintro r ⟨Γ, -, -, -, rfl⟩
    exact weightedLength_nonneg B Γ
  · rwa [segmentsSupport_singleton]
  · rwa [segmentsSupport_singleton]
theorem weightedDistance_comm (x x' : D.Space) :
    B.weightedDistance x x' = B.weightedDistance x' x := by
  unfold SeparatedChain.weightedDistance
  congr 1
  ext r
  constructor
  · rintro ⟨Γ, h, a, b, e⟩
    exact ⟨Γ, h, b, a, e⟩
  · rintro ⟨Γ, h, a, b, e⟩
    exact ⟨Γ, h, b, a, e⟩
theorem exists_liftedSegment_mem_support (x x' : D.Space) :
    ∃ s : LiftedSegment, x ∈ s.support D.side ∧ x' ∈ s.support D.side := by
  obtain ⟨a, rfl⟩ := torusProj_surjective x
  obtain ⟨b, rfl⟩ := torusProj_surjective x'
  exact ⟨⟨a, b⟩, ⟨0, by simp, pointAt_zero _⟩, ⟨1, by simp, pointAt_one _⟩⟩
end Density
section Chains
variable (hW : WeightedLengthAndLip) (G : GivenChain)
include hW
theorem abs_sub_le_weightedDistance {f : G.data.Space → ℝ} (hf : LipschitzL1 f) {τ : ℝ}
    (hτ : 0 ≤ τ)
    (hb : ∀ z, localLip f z ≤ ENNReal.ofReal (τ * G.chain.weightDensity z))
    (x x' : G.data.Space) : |f x - f x'| ≤ τ * G.chain.weightedDistance x x' := by
  have key : ∀ Γ : List LiftedSegment, IsTreeGraph G.data.side Γ →
      x ∈ segmentsSupport G.data.side Γ →
      x' ∈ segmentsSupport G.data.side Γ → |f x - f x'| ≤ τ * G.chain.weightedLength Γ := by
    intro Γ hΓ hx hx'
    have hnn : 0 ≤ τ * G.chain.weightedLength Γ :=
      mul_nonneg hτ (weightedLength_nonneg _ Γ)
    rw [← ENNReal.ofReal_le_ofReal_iff hnn]
    calc ENNReal.ofReal |f x - f x'|
        ≤ setLIntegralL1 (segmentsSupport G.data.side Γ) (localLip f) :=
          abs_sub_le_setLIntegral_localLip hf hΓ hx hx'
      _ ≤ setLIntegralL1 (segmentsSupport G.data.side Γ)
            (fun z => ENNReal.ofReal τ * ENNReal.ofReal (G.chain.weightDensity z)) := by
          refine lintegral_mono fun z => ?_
          refine (hb z).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul hτ]
      _ = ENNReal.ofReal τ * setLIntegralL1 (segmentsSupport G.data.side Γ)
            (fun z => ENNReal.ofReal (G.chain.weightDensity z)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal τ * ENNReal.ofReal (G.chain.weightedLength Γ) := by
          gcongr
          exact ((hW G).1 Γ).1
      _ = ENNReal.ofReal (τ * G.chain.weightedLength Γ) := (ENNReal.ofReal_mul hτ).symm
  obtain ⟨s, hs, hs'⟩ := exists_liftedSegment_mem_support (D := G.data) x x'
  have hne : {r | ∃ Γ : List LiftedSegment, IsTreeGraph G.data.side Γ ∧
      x ∈ segmentsSupport G.data.side Γ ∧
      x' ∈ segmentsSupport G.data.side Γ ∧ r = G.chain.weightedLength Γ}.Nonempty :=
    ⟨_, [s], isTreeGraph_singleton s, by rwa [segmentsSupport_singleton],
      by rwa [segmentsSupport_singleton], rfl⟩
  rcases hτ.eq_or_lt with h0 | hpos
  · have := key [s] (isTreeGraph_singleton s) (by rwa [segmentsSupport_singleton])
      (by rwa [segmentsSupport_singleton])
    rw [← h0] at this ⊢
    simpa using this
  · rw [← div_le_iff₀' hpos]
    refine le_csInf hne ?_
    rintro r ⟨Γ, hΓ, hx, hx', rfl⟩
    rw [div_le_iff₀' hpos]
    exact key Γ hΓ hx hx'
theorem weightedLength_singleton_le (s : LiftedSegment)
    (hs : l1NormVec s.displacement < G.data.side) {a c₁ c₂ : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h₁ : ∀ u, 0 ≤ u → u < a → G.chain.weightDensity (s.pointAt G.data.side u) = c₁)
    (h₂ : ∀ u, a < u → u ≤ 1 → G.chain.weightDensity (s.pointAt G.data.side u) = c₂) :
    G.chain.weightedLength [s] ≤ l1NormVec s.displacement * (c₁ * a + c₂ * (1 - a)) := by
  have hv := l1NormVec_nonneg s.displacement
  have hnn : 0 ≤ l1NormVec s.displacement * (c₁ * a + c₂ * (1 - a)) :=
    mul_nonneg hv (add_nonneg (mul_nonneg hc₁ ha₀) (mul_nonneg hc₂ (by linarith)))
  rw [← ENNReal.ofReal_le_ofReal_iff hnn]
  have heq := ((hW G).1 [s]).2 (by simpa using hs) (by simp)
  have hcar : segmentsSupport G.data.side [s] =
      s.pointAt G.data.side '' Icc 0 a ∪ s.pointAt G.data.side '' Icc a 1 := by
    rw [segmentsSupport_singleton, LiftedSegment.support, ← image_union,
      Icc_union_Icc_eq_Icc ha₀ ha₁]
  have hint : ∀ (K : Set G.data.Space) (c : ℝ), MeasurableSet K →
      (∀ z ∈ K, z ≠ s.pointAt G.data.side a → G.chain.weightDensity z = c) →
      setLIntegralL1 K (fun z => ENNReal.ofReal (G.chain.weightDensity z)) ≤
        ENNReal.ofReal c * l1LengthMeasure G.data.side K := by
    intro K c hK hz
    calc setLIntegralL1 K (fun z => ENNReal.ofReal (G.chain.weightDensity z))
        ≤ ∫⁻ _ in K, ENNReal.ofReal c ∂(l1LengthMeasure G.data.side) := by
          refine lintegral_mono_ae ((ae_restrict_iff' hK).2 ?_)
          have hnull : ∀ᵐ z ∂(l1LengthMeasure G.data.side), z ≠ s.pointAt G.data.side a :=
            compl_mem_ae_iff.2 (l1LengthMeasure_singleton _)
          filter_upwards [hnull] with z hzp hzK
          rw [hz z hzK hzp]
      _ = ENNReal.ofReal c * l1LengthMeasure G.data.side K := by simp
  have hK₁ := hint _ c₁ (isCompact_image_Icc s 0 a).measurableSet (by
    rintro _ ⟨u, hu, rfl⟩ hne
    exact h₁ u hu.1 (lt_of_le_of_ne hu.2 fun h => hne (by rw [h])))
  have hK₂ := hint _ c₂ (isCompact_image_Icc s a 1).measurableSet (by
    rintro _ ⟨u, hu, rfl⟩ hne
    exact h₂ u (lt_of_le_of_ne hu.1 fun h => hne (by rw [h])) hu.2)
  rw [heq, hcar]
  calc setLIntegralL1 (s.pointAt G.data.side '' Icc 0 a ∪ s.pointAt G.data.side '' Icc a 1)
        (fun z => ENNReal.ofReal (G.chain.weightDensity z))
      ≤ setLIntegralL1 (s.pointAt G.data.side '' Icc 0 a)
          (fun z => ENNReal.ofReal (G.chain.weightDensity z)) +
        setLIntegralL1 (s.pointAt G.data.side '' Icc a 1)
          (fun z => ENNReal.ofReal (G.chain.weightDensity z)) :=
        lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal c₁ * ENNReal.ofReal (l1NormVec s.displacement * (a - 0)) +
        ENNReal.ofReal c₂ * ENNReal.ofReal (l1NormVec s.displacement * (1 - a)) := by
        refine add_le_add (hK₁.trans ?_) (hK₂.trans ?_)
        · gcongr
          exact l1LengthMeasure_image_Icc_le s
        · gcongr
          exact l1LengthMeasure_image_Icc_le s
    _ = ENNReal.ofReal (l1NormVec s.displacement * (c₁ * a + c₂ * (1 - a))) := by
        rw [← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₂,
          ← ENNReal.ofReal_add (mul_nonneg hc₁ (mul_nonneg hv (by linarith)))
            (mul_nonneg hc₂ (mul_nonneg hv (by linarith)))]
        congr 1
        ring
end Chains
section Cubes
variable {S : ℝ}
theorem torusSupNorm_le_of_norm_le {x : Torus4 S} {r : ℝ} (h : ∀ μ, ‖x μ‖ ≤ r) :
    torusSupNorm x ≤ r := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_le_of_forall <;> assumption
theorem norm_apply_le_torusSupNorm (x : Torus4 S) (μ : Fin 4) : ‖x μ‖ ≤ torusSupNorm x := by apply _root_.YangMills.Construction.SequenceGeometryProof.norm_apply_le_torusSupNorm <;> assumption
theorem setSupDist_le {A A' : Set (Torus4 S)} {a a' : Torus4 S} (ha : a ∈ A) (ha' : a' ∈ A') :
    setSupDist A A' ≤ ENNReal.ofReal (torusSupNorm (a - a')) :=
  iInf₂_le_of_le a ha (iInf₂_le a' ha')
theorem torusProj_add (a b : Fin 4 → ℝ) : torusProj S (a + b) = torusProj S a + torusProj S b := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
variable {D : TorusData}
theorem mem_interior_cubeAround {σ : ℝ} {y z : D.Space} (h : ∀ μ, ‖(z - y) μ‖ < σ / 2) :
    z ∈ interior (D.cubeAround σ y) := by
  have hopen : IsOpen {z : D.Space | ∀ μ, ‖(z - y) μ‖ < σ / 2} := by
    have : {z : D.Space | ∀ μ, ‖(z - y) μ‖ < σ / 2} =
        ⋂ μ, {z : D.Space | ‖(z - y) μ‖ < σ / 2} := by
      ext z
      simp
    rw [this]
    refine isOpen_iInter_of_finite fun μ => isOpen_lt ?_ continuous_const
    exact ((continuous_apply μ).comp (continuous_id.sub continuous_const)).norm
  refine interior_maximal (fun w hw => ?_) hopen h
  have hw' : ∀ μ, ‖(w - y) μ‖ < σ / 2 := hw
  exact torusSupNorm_le_of_norm_le fun μ => (hw' μ).le
end Cubes
section Sites
variable {D : TorusData} (B : SeparatedChain D)
theorem level_spec {y : D.Space} (hy : y ∈ B.allSites) :
    y ∈ B.layerSites (B.level y) ∧ B.level y ≤ D.top := by
  obtain ⟨n, hn, hyn⟩ := mem_iUnion₂.1 hy
  have hne : {n | y ∈ B.layerSites n}.Nonempty := ⟨n, hyn⟩
  refine ⟨Nat.sInf_mem hne, (Nat.sInf_le hyn).trans ?_⟩
  have := Finset.mem_range.1 hn
  omega
theorem siteScale_pos (y : D.Space) : 0 < B.siteScale y := scale_pos D _
theorem bareScale_eq (x : D.BareSite) : B.bareScale x = D.scale (B.bareLevel x) := rfl
end Sites
section ChainBounds
open YangMills.Construction.Weighted.GivenChainGeneral
variable (G : GivenChain)
theorem blockCenter_spec (hblocks : BlockPartition G.chain) {x : G.data.BareSite}
    (hx : x ∈ G.data.bareSites (G.chain.stage 0)) :
    G.chain.blockCenter x ∈ G.chain.allSites ∧
      x ∈ G.chain.block (G.chain.blockCenter x) := by
  rw [← hblocks.iUnion_block] at hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
  exact Classical.epsilon_spec (p := fun y => y ∈ G.chain.allSites ∧ x ∈ G.chain.block y)
    ⟨y, hy, hxy⟩
theorem mem_layer_bareLevel (hblocks : BlockPartition G.chain)
    (hlayers : ShellsAndCubes G.chain) {x : G.data.BareSite}
    (hx : x ∈ G.data.bareSites (G.chain.stage 0)) :
    (x : G.data.Space) ∈ G.chain.layer (G.chain.bareLevel x) ∧
      G.chain.bareLevel x ≤ G.data.top := by
  obtain ⟨hy, hxy⟩ := blockCenter_spec G hblocks hx
  obtain ⟨hyl, hle⟩ := level_spec G.chain hy
  refine ⟨?_, hle⟩
  rw [SeparatedChain.bareLevel, hlayers.layer_eq_iUnion _ hle]
  exact mem_iUnion₂.2 ⟨_, hyl, hxy⟩
theorem bareLevel_le_succ (hblocks : BlockPartition G.chain)
    (hlayers : ShellsAndCubes G.chain) {x x' : G.data.BareSite}
    (hx : x ∈ G.data.bareSites (G.chain.stage 0))
    (hx' : x' ∈ G.data.bareSites (G.chain.stage 0))
    (hd : torusSupNorm ((x : G.data.Space) - (x' : G.data.Space)) ≤ G.data.scale 0) :
    G.chain.bareLevel x' ≤ G.chain.bareLevel x + 1 := by
  by_contra hlt
  obtain ⟨hxl, hxt⟩ := mem_layer_bareLevel G hblocks hlayers hx
  obtain ⟨hxl', hxt'⟩ := mem_layer_bareLevel G hblocks hlayers hx'
  set n := G.chain.bareLevel x
  set n' := G.chain.bareLevel x'
  have hcompl := (hlayers.layer_subset_diff n hxt hxl).2
  have hmem := stage_anti G.chain (show n + 1 + 1 ≤ n' by omega)
    (hlayers.layer_subset_diff n' hxt' hxl').1
  have hsep := G.chain.separated (n + 1) (by omega)
  have hle : setSupDist (G.data.closedComplement (G.chain.stage (n + 1)))
      (G.chain.stage (n + 1 + 1)) ≤ ENNReal.ofReal (G.data.scale 0) :=
    (setSupDist_le hcompl hmem).trans (ENNReal.ofReal_le_ofReal hd)
  have hlt' := (ENNReal.ofReal_lt_ofReal_iff (scale_pos G.data 0)).1 (hsep.trans_le hle)
  have hL := one_le_L G.data
  have hgap : (1 : ℝ) ≤ G.data.gapNumber := hL.trans (by exact_mod_cast G.data.le_gapNumber)
  have hblock : (1 : ℝ) ≤ G.data.blockNumber :=
    hL.trans (by exact_mod_cast G.data.le_blockNumber)
  have hmono := scale_mono G.data (Nat.zero_le (n + 1))
  have hpos := scale_pos G.data (n + 1)
  have : G.data.scale (n + 1) ≤
      (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) * G.data.scale (n + 1) :=
    le_mul_of_one_le_left hpos.le (one_le_mul_of_one_le_of_one_le hgap hblock)
  linarith
variable (hW : WeightedLengthAndLip) (hS : GivenChainGeneralFacts)
include hS in
theorem two_mul_scale_lt_side {n : ℕ} (hn : n ≤ G.data.top) :
    2 * G.data.scale n < G.data.side := by
  have h := ((hS G).1.side_ge n hn).1
  have hL : (3 : ℝ) ≤ G.data.L := by
    exact_mod_cast G.data.blocking.three_le_factor
  have hM : (3 : ℝ) ≤ G.data.blockNumber := hL.trans (by exact_mod_cast G.data.le_blockNumber)
  have hpos := scale_pos G.data n
  nlinarith
include hW hS
theorem weightedDistance_blockCenter_le {y : G.data.Space} (hy : y ∈ G.chain.allSites)
    {x : G.data.BareSite} (hx : x ∈ G.chain.block y) :
    G.chain.weightedDistance (x : G.data.Space) y ≤ 1 / 2 * 4 := by
  set ξ := G.chain.siteScale y with hξ
  have hξpos : 0 < ξ := siteScale_pos _ _
  have hcube : torusSupNorm ((x : G.data.Space) - y) ≤ ξ / 2 := hx
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (((x : G.data.Space) - y) μ)
  have hcov : torusProj G.data.side b = (x : G.data.Space) - y := funext hb
  have hbμ : ∀ μ, |b μ| ≤ ξ / 2 := fun μ => by
    rw [hb' μ]
    exact (norm_apply_le_torusSupNorm _ μ).trans hcube
  have hL1 : l1NormVec b ≤ 2 * ξ := by
    calc l1NormVec b ≤ ∑ _μ : Fin 4, ξ / 2 := Finset.sum_le_sum fun μ _ => hbμ μ
      _ = 2 * ξ := by
        simp
        ring
  obtain ⟨z, hz⟩ := torusProj_surjective y
  let s : LiftedSegment := ⟨z, z + b⟩
  have hvec : s.displacement = b := by simp [s, LiftedSegment.displacement]
  have hs : l1NormVec s.displacement < G.data.side := by
    rw [hvec]
    exact hL1.trans_lt (two_mul_scale_lt_side G hS (level_spec G.chain hy).2)
  have hp0 : s.pointAt G.data.side 0 = y := by rw [pointAt_zero]; exact hz
  have hp1 : s.pointAt G.data.side 1 = (x : G.data.Space) := by
    rw [pointAt_one]
    change torusProj G.data.side (z + b) = _
    rw [torusProj_add, hz, hcov]
    abel
  have hdens : ∀ u, 0 ≤ u → u < 1 →
      G.chain.weightDensity (s.pointAt G.data.side u) = ξ⁻¹ := by
    intro u hu₀ hu₁
    refine (hW G).2.1 y hy _ (mem_interior_cubeAround fun μ => ?_)
    have hsub : s.pointAt G.data.side u - y = torusProj G.data.side ((u - 0) • b) := by
      rw [← hp0, pointAt_sub_pointAt, hvec]
    rw [hsub]
    refine (addCircle_norm_coe_le_abs _).trans_lt ?_
    simp only [sub_zero, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hu₀]
    have := hbμ μ
    nlinarith
  have hw := weightedLength_singleton_le hW G s hs zero_le_one le_rfl
    (inv_nonneg.2 hξpos.le) le_rfl hdens (fun u h h' => absurd h (not_lt.2 h'))
  have hdist := weightedDistance_le_weightedLength_singleton G.chain s
    (p := (x : G.data.Space)) (q := y) ⟨1, by simp, hp1⟩ ⟨0, by simp, hp0⟩
  refine hdist.trans (hw.trans ?_)
  rw [hvec]
  have hξ' : ξ⁻¹ * ξ = 1 := inv_mul_cancel₀ hξpos.ne'
  nlinarith
theorem weightedDistance_bond_le {x x' : G.data.BareSite}
    (hx : x ∈ G.data.bareSites (G.chain.stage 0))
    (hx' : x' ∈ G.data.bareSites (G.chain.stage 0)) {μ : Fin 4}
    (hstep : (x' : G.data.Space) - x = G.data.unitStep μ) :
    G.chain.weightedDistance (x : G.data.Space) x' ≤
      1 / 2 * G.data.scale 0 *
        ((G.chain.bareScale x)⁻¹ + (G.chain.bareScale x')⁻¹) := by
  have hblocks := (hS G).2.2.2.2.1
  set ξ₀ := G.data.scale 0 with hξ₀
  have hpos : 0 < ξ₀ := scale_pos _ _
  let b : Fin 4 → ℝ := Pi.single μ ξ₀
  have hbν : ∀ ν, |b ν| ≤ ξ₀ := fun ν => by
    by_cases h : ν = μ
    · subst h
      simp [b, abs_of_pos hpos]
    · simp [b, Pi.single_eq_of_ne h, hpos.le]
  have hL1 : l1NormVec b = ξ₀ := by
    unfold l1NormVec
    rw [Finset.sum_eq_single μ]
    · simp [b, abs_of_pos hpos]
    · intro ν _ h
      simp [b, Pi.single_eq_of_ne h]
    · simp
  obtain ⟨z, hz⟩ := torusProj_surjective (x : G.data.Space)
  let s : LiftedSegment := ⟨z, z + b⟩
  have hvec : s.displacement = b := by simp [s, LiftedSegment.displacement]
  have hs : l1NormVec s.displacement < G.data.side := by
    rw [hvec, hL1]
    have := two_mul_scale_lt_side G hS (Nat.zero_le G.data.top)
    linarith
  have hcovb : torusProj G.data.side b = G.data.unitStep μ := rfl
  have hp0 : s.pointAt G.data.side 0 = (x : G.data.Space) := by rw [pointAt_zero]; exact hz
  have hp1 : s.pointAt G.data.side 1 = (x' : G.data.Space) := by
    rw [pointAt_one]
    change torusProj G.data.side (z + b) = _
    rw [torusProj_add, hz, hcovb, ← hstep]
    abel
  have hnear : ∀ (p : G.data.BareSite), p ∈ G.data.bareSites (G.chain.stage 0) →
      ∀ w : G.data.Space, (∀ ν, ‖(w - (p : G.data.Space)) ν‖ < ξ₀ / 2) →
      G.chain.weightDensity w = (G.chain.bareScale p)⁻¹ := by
    intro p hp w hw
    exact (hW G).2.1 _ (blockCenter_spec G hblocks hp).1 w
      (interior_mono (hblocks.cubeAround_subset p hp) (mem_interior_cubeAround hw))
  have hsmall : ∀ (t : ℝ), |t| < 1 / 2 → ∀ ν,
      ‖(torusProj G.data.side (t • b)) ν‖ < ξ₀ / 2 := by
    intro t ht ν
    refine (addCircle_norm_coe_le_abs _).trans_lt ?_
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    have h1 := hbν ν
    have h3 := abs_nonneg t
    nlinarith
  have hw := weightedLength_singleton_le hW G s hs (a := 1 / 2) (by norm_num) (by norm_num)
    (inv_nonneg.2 (siteScale_pos G.chain _).le)
    (inv_nonneg.2 (siteScale_pos G.chain _).le)
    (fun u hu₀ hu₁ => hnear x hx _ fun ν => by
      rw [← hp0, pointAt_sub_pointAt, hvec]
      refine hsmall _ ?_ ν
      rw [sub_zero, abs_of_nonneg hu₀]
      exact hu₁)
    (fun u hu₀ hu₁ => hnear x' hx' _ fun ν => by
      rw [← hp1, pointAt_sub_pointAt, hvec]
      refine hsmall _ ?_ ν
      rw [abs_of_nonpos (by linarith)]
      linarith)
  have hdist := weightedDistance_le_weightedLength_singleton G.chain s
    (p := (x : G.data.Space)) (q := (x' : G.data.Space)) ⟨0, by simp, hp0⟩ ⟨1, by simp, hp1⟩
  refine hdist.trans (hw.trans (le_of_eq ?_))
  rw [hvec, hL1]
  simp only [SeparatedChain.bareScale]
  ring
theorem bareLevel_bond_le {x x' : G.data.BareSite}
    (hx : x ∈ G.data.bareSites (G.chain.stage 0))
    (hx' : x' ∈ G.data.bareSites (G.chain.stage 0)) {μ : Fin 4}
    (hstep : (x' : G.data.Space) - x = G.data.unitStep μ) :
    G.chain.bareLevel x' ≤ G.chain.bareLevel x + 1 ∧
      G.chain.bareLevel x ≤ G.chain.bareLevel x' + 1 := by
  have hblocks := (hS G).2.2.2.2.1
  have hlayers := (hS G).2.2.1
  have hpos : 0 < G.data.scale 0 := scale_pos _ _
  have hnorm : ∀ ν, ‖(G.data.unitStep μ) ν‖ ≤ G.data.scale 0 := by
    intro ν
    refine (addCircle_norm_coe_le_abs _).trans ?_
    by_cases h : ν = μ
    · subst h
      simp [abs_of_pos hpos]
    · simp [Pi.single_eq_of_ne h, hpos.le]
  refine ⟨bareLevel_le_succ G hblocks hlayers hx hx' ?_,
    bareLevel_le_succ G hblocks hlayers hx' hx ?_⟩
  · refine torusSupNorm_le_of_norm_le fun ν => ?_
    have : ((x : G.data.Space) - (x' : G.data.Space)) = -G.data.unitStep μ := by
      rw [← hstep]; abel
    rw [this]
    simpa using hnorm ν
  · refine torusSupNorm_le_of_norm_le fun ν => ?_
    rw [hstep]
    exact hnorm ν
omit hW hS in
theorem bond_scale_bound (D : TorusData) {n n' : ℕ} (h : n ≤ n' + 1) :
    1 / 2 * D.scale 0 * ((D.scale n)⁻¹ + (D.scale n')⁻¹) ≤
      min 1 ((D.L : ℝ) * D.scale 0 * (D.scale n)⁻¹) := by
  have hL := one_le_L D
  have h0 := scale_pos D 0
  have hn := scale_pos D n
  have hn' := scale_pos D n'
  have h₁ : D.scale 0 * (D.scale n)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hn).2 (scale_mono D (Nat.zero_le n))
  have h₂ : D.scale 0 * (D.scale n')⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hn').2 (scale_mono D (Nat.zero_le n'))
  have h₃ : (D.scale n')⁻¹ ≤ (D.L : ℝ) * (D.scale n)⁻¹ := by
    have hle : D.scale n ≤ D.L * D.scale n' := by
      rw [← scale_succ]
      exact scale_mono D h
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hn' hn]
    linarith
  have h₄ : (D.scale n)⁻¹ ≤ (D.L : ℝ) * (D.scale n)⁻¹ :=
    le_mul_of_one_le_left (inv_nonneg.2 hn.le) hL
  refine le_min ?_ ?_
  · nlinarith
  · have : D.scale 0 * ((D.scale n)⁻¹ + (D.scale n')⁻¹) ≤
        D.scale 0 * (2 * ((D.L : ℝ) * (D.scale n)⁻¹)) :=
      mul_le_mul_of_nonneg_left (by linarith) h0.le
    nlinarith
theorem blocksAndBondsShort : G.chain.BlocksAndBondsShort := by
  refine ⟨fun y hy x hx => weightedDistance_blockCenter_le G hW hS hy hx, ?_⟩
  rintro x x' hx hx' ⟨b, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · obtain ⟨μ, hμ⟩ := b.isPositive
    obtain ⟨h₁, h₂⟩ := bareLevel_bond_le G hW hS hx hx' hμ
    refine ⟨?_, weightedDistance_bond_le G hW hS hx hx' hμ, ?_⟩
    · rw [abs_le]
      constructor <;> omega
    · simp only [bareScale_eq]
      exact bond_scale_bound _ h₂
  · obtain ⟨μ, hμ⟩ := b.isPositive
    obtain ⟨h₁, h₂⟩ := bareLevel_bond_le G hW hS hx' hx hμ
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> omega
    · rw [weightedDistance_comm, add_comm]
      exact weightedDistance_bond_le G hW hS hx' hx hμ
    · simp only [bareScale_eq]
      exact bond_scale_bound _ h₁
omit hS in
theorem weightedDistLowerBoundFromSet : G.chain.WeightedDistLowerBoundFromSet := by
  intro A ρ n _ hA hρ hmiss x hx x' hx'
  have hξ := scale_pos G.data n
  obtain ⟨a, ha⟩ := hA
  have hne : ∀ z : G.data.Space, setSupDist {z} A ≠ ⊤ := fun z =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (setSupDist_le (mem_singleton z) ha)
  obtain ⟨hφL, hφ1⟩ := (hW G).2.2.1 A ⟨a, ha⟩
  set φ : G.data.Space → ℝ := fun z => (setSupDist {z} A).toReal with hφ
  let F : G.data.Space → ℝ := fun z => min (φ z) ρ
  have hFL : LipschitzL1 F := by
    obtain ⟨C, hC⟩ := hφL
    refine ⟨C, fun p q => le_trans ?_ (hC p q)⟩
    simpa using abs_min_sub_min_le_max (φ q) ρ (φ p) ρ
  have hφc := LipschitzL1.continuous hφL
  have hb : ∀ z, localLip F z ≤
      ENNReal.ofReal (G.data.scale n * G.chain.weightDensity z) := by
    intro z
    by_cases hz : setSupDist {z} A ≤ ENNReal.ofReal ρ
    · have hfl := inv_scale_le_weightDensity G.chain n z (hmiss z hz)
      have h1 : 1 ≤ G.data.scale n * G.chain.weightDensity z := by
        have := mul_le_mul_of_nonneg_left hfl hξ.le
        rwa [mul_inv_cancel₀ hξ.ne'] at this
      refine ((((hW G).2.2.2.2 φ φ hφL hφL 0 0 ρ le_rfl le_rfl hρ.le z).2.1).trans
        (hφ1 z)).trans ?_
      exact ENNReal.one_le_ofReal.2 h1
    · have hgt : ρ < φ z :=
        (ENNReal.ofReal_lt_iff_lt_toReal hρ.le (hne z)).1 (not_le.1 hz)
      have hconst : ∀ᶠ w in 𝓝 z, F w = F z := by
        filter_upwards [hφc.continuousAt.eventually (lt_mem_nhds hgt)] with w hw
        simp only [F, min_eq_right hw.le, min_eq_right hgt.le]
      rw [((hW G).2.2.2.2 F F hFL hFL 0 0 ρ le_rfl le_rfl hρ.le z).2.2.2 hconst]
      exact zero_le
  have hmain := abs_sub_le_weightedDistance hW G hFL hξ.le hb x x'
  have hFx : F x = 0 := by
    have h0 : setSupDist {x} A = 0 := by
      refine le_antisymm ?_ zero_le
      refine (setSupDist_le (mem_singleton x) hx).trans ?_
      rw [sub_self]
      exact le_of_eq (ENNReal.ofReal_eq_zero.2 (torusSupNorm_le_of_norm_le (by simp)))
    simp [F, hφ, h0, hρ.le]
  have hFx' : F x' = ρ := by
    have : ρ ≤ φ x' := (ENNReal.ofReal_le_iff_le_toReal (hne x')).1 hx'
    exact min_eq_right this
  rw [hFx, hFx', zero_sub, abs_neg, abs_of_pos hρ] at hmain
  rw [div_le_iff₀' hξ]
  exact hmain
omit hS in
theorem weightedDistGeL1 : G.chain.WeightedDistGeL1 := by
  intro x x'
  have hξ := scale_pos G.data G.data.top
  obtain ⟨hL, h1⟩ := (hW G).2.2.2.1 x
  have hb : ∀ z, localLip (fun z : G.data.Space => torusL1Norm (z - x)) z ≤
      ENNReal.ofReal (G.data.scale G.data.top * G.chain.weightDensity z) := by
    intro z
    have hz : z ∉ G.chain.stage (G.data.top + 1) := by
      rw [G.chain.empty_above _ (Nat.lt_succ_self _)]
      exact notMem_empty z
    have hfl := inv_scale_le_weightDensity G.chain _ z hz
    have h1' : 1 ≤ G.data.scale G.data.top * G.chain.weightDensity z := by
      have := mul_le_mul_of_nonneg_left hfl hξ.le
      rwa [mul_inv_cancel₀ hξ.ne'] at this
    exact (h1 z).trans (ENNReal.one_le_ofReal.2 h1')
  have hmain := abs_sub_le_weightedDistance hW G hL hξ.le hb x x'
  have hzero : torusL1Norm (x - x) = 0 := by simp [torusL1Norm_eq_sum_norm]
  have hsym : torusL1Norm (x' - x) = torusL1Norm (x - x') := by
    simp only [torusL1Norm_eq_sum_norm, Pi.sub_apply]
    exact Finset.sum_congr rfl fun μ _ => norm_sub_rev _ _
  have hnn : 0 ≤ torusL1Norm (x - x') := by
    rw [torusL1Norm_eq_sum_norm]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  simp only [hzero, zero_sub, abs_neg, hsym, abs_of_nonneg hnn] at hmain
  rw [inv_mul_le_iff₀ hξ]
  exact hmain
end ChainBounds
theorem weightedDistBounds_holds (hW : WeightedLengthAndLip)
    (hS : GivenChainGeneralFacts) : WeightedDistBounds := by
  intro G
  refine ⟨?_, ?_, weightedDistLowerBoundFromSet G hW, blocksAndBondsShort G hW hS,
    weightedDistGeL1 G hW⟩
  · intro f hf
    exact ⟨fun Γ x x' hΓ hx hx' => abs_sub_le_setLIntegral_localLip hf hΓ hx hx',
      fun τ hτ hb x x' => abs_sub_le_weightedDistance hW G hf hτ hb x x'⟩
  · exact inv_scale_le_weightDensity G.chain
end YangMills.Construction.Weighted.DistBounds
end
