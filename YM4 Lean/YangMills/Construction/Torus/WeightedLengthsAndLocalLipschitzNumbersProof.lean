import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
import YangMills.Construction.Torus.BoundsOnTheWeightedDistanceProof
import YangMills.Construction.Weighted.LocalLipCalculusProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
open Set Filter Topology MeasureTheory YangMills.Construction.TorusMetric
open scoped ENNReal NNReal
namespace WeightedLengthProof
variable {S : ℝ}
theorem l1NormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ l1NormVec v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem abs_apply_le_l1NormVec (v : Fin 4 → ℝ) (i : Fin 4) : |v i| ≤ l1NormVec v :=
  Finset.single_le_sum (f := fun i => |v i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
theorem pointAt_sub_apply (s : LiftedSegment) (u u' : ℝ) (i : Fin 4) :
    (s.pointAt S u - s.pointAt S u') i = (((u - u') * s.displacement i : ℝ) : AddCircle S) := by
  simp only [LiftedSegment.pointAt, torusProj, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [← AddCircle.coe_sub]
  congr 1
  ring
theorem continuous_pointAt (s : LiftedSegment) : Continuous (s.pointAt S) := by
  refine continuous_pi fun i => ?_
  have h : Continuous fun t : ℝ => (t : AddCircle S) := continuous_quotient_mk'
  exact h.comp (by fun_prop)
theorem torusSupNorm_le_iff (x : Torus4 S) (a : ℝ) :
    torusSupNorm x ≤ a ↔ ∀ i, ‖x i‖ ≤ a := by apply _root_.YangMills.Construction.SeparatedSequence.torusSupNorm_le_iff <;> assumption
section Segments
variable [Fact (0 < S)]
def l1Point (S : ℝ) (s : LiftedSegment) (u : ℝ) : TorusL1 S := WithLp.toLp 1 (s.pointAt S u)
omit [Fact (0 < S)] in
theorem dist_l1Point (s : LiftedSegment) (u u' : ℝ) :
    dist (l1Point S s u) (l1Point S s u') =
      ∑ i, ‖(((u - u') * s.displacement i : ℝ) : AddCircle S)‖ := by
  rw [dist_eq_norm, l1Point, l1Point, ← WithLp.toLp_sub, norm_toLp_eq_torusL1Norm,
    torusL1Norm_eq_sum_norm]
  exact Finset.sum_congr rfl fun i _ => by rw [pointAt_sub_apply]
omit [Fact (0 < S)] in
theorem dist_l1Point_le (s : LiftedSegment) (u u' : ℝ) :
    dist (l1Point S s u) (l1Point S s u') ≤ l1NormVec s.displacement * dist u u' := by
  rw [dist_l1Point, Real.dist_eq, l1NormVec, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => (addCircle_norm_coe_le_abs _).trans_eq ?_
  rw [abs_mul, mul_comm]
theorem dist_l1Point_eq (s : LiftedSegment) (hL : l1NormVec s.displacement < S) {u u' : ℝ}
    (hu : |u - u'| ≤ 1 / 2) :
    dist (l1Point S s u) (l1Point S s u') = l1NormVec s.displacement * dist u u' := by
  have hS : 0 < S := Fact.out
  rw [dist_l1Point, Real.dist_eq, l1NormVec, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hle : |(u - u') * s.displacement i| ≤ |S| / 2 := by
    rw [abs_mul, abs_of_pos hS]
    have h₁ := abs_apply_le_l1NormVec s.displacement i
    calc |u - u'| * |s.displacement i| ≤ 1 / 2 * |s.displacement i| :=
          mul_le_mul_of_nonneg_right hu (abs_nonneg _)
      _ ≤ S / 2 := by linarith
  rw [(AddCircle.norm_coe_eq_abs_iff S hS.ne').2 hle, abs_mul, mul_comm]
omit [Fact (0 < S)] in
theorem lipschitzWith_l1Point (s : LiftedSegment) :
    LipschitzWith (Real.toNNReal (l1NormVec s.displacement)) (l1Point S s) :=
  LipschitzWith.of_dist_le_mul fun u u' => by
    rw [Real.coe_toNNReal _ (l1NormVec_nonneg _)]
    exact dist_l1Point_le s u u'
omit [Fact (0 < S)] in
theorem hausdorffMeasure_image_l1Point_le (s : LiftedSegment) (B : Set ℝ) :
    μH[1] (l1Point S s '' B) ≤ ENNReal.ofReal (l1NormVec s.displacement) * volume B := by
  have h := (lipschitzWith_l1Point (S := S) s).hausdorffMeasure_image_le zero_le_one B
  simpa [hausdorffMeasure_real, ENNReal.ofReal] using h
theorem le_hausdorffMeasure_image_l1Point (s : LiftedSegment) (hL : l1NormVec s.displacement < S)
    (hpos : 0 < l1NormVec s.displacement) {I B : Set ℝ}
    (hI : ∀ u ∈ I, ∀ u' ∈ I, |u - u'| ≤ 1 / 2) (hB : B ⊆ I) :
    ENNReal.ofReal (l1NormVec s.displacement) * volume B ≤ μH[1] (l1Point S s '' B) := by
  have hinj : InjOn (l1Point S s) I := by
    intro u hu u' hu' h
    have h₀ := dist_l1Point_eq s hL (hI u hu u' hu')
    rw [h, dist_self] at h₀
    have h₁ : dist u u' = 0 := by
      rcases mul_eq_zero.1 h₀.symm with h₂ | h₂
      · exact absurd h₂ hpos.ne'
      · exact h₂
    exact dist_eq_zero.1 h₁
  have hr : ∀ u ∈ I, Function.invFunOn (l1Point S s) I (l1Point S s u) = u :=
    fun u hu => hinj.leftInvOn_invFunOn hu
  have hlip : LipschitzOnWith (Real.toNNReal (l1NormVec s.displacement)⁻¹)
      (Function.invFunOn (l1Point S s) I) (l1Point S s '' I) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    rw [hr u hu, hr u' hu', dist_l1Point_eq s hL (hI u hu u' hu'),
      Real.coe_toNNReal _ (inv_nonneg.2 hpos.le), inv_mul_cancel_left₀ hpos.ne']
  have h := (hlip.mono (image_mono hB)).hausdorffMeasure_image_le zero_le_one
  have himage : Function.invFunOn (l1Point S s) I '' (l1Point S s '' B) = B := by
    rw [image_image]
    exact (image_congr fun u hu => hr u (hB hu)).trans (image_id B)
  rw [himage, hausdorffMeasure_real] at h
  have hcancel : ENNReal.ofReal (l1NormVec s.displacement) *
      ((Real.toNNReal (l1NormVec s.displacement)⁻¹ : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne',
      ENNReal.ofReal_one]
  calc ENNReal.ofReal (l1NormVec s.displacement) * volume B
      ≤ ENNReal.ofReal (l1NormVec s.displacement) *
          (((Real.toNNReal (l1NormVec s.displacement)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ (1 : ℝ) *
            μH[1] (l1Point S s '' B)) := by gcongr
    _ = μH[1] (l1Point S s '' B) := by
        rw [ENNReal.rpow_one, ← mul_assoc, hcancel, one_mul]
theorem injOn_l1Point (s : LiftedSegment) (hL : l1NormVec s.displacement < S)
    (hpos : 0 < l1NormVec s.displacement) : InjOn (l1Point S s) (Icc 0 1) := by
  have hS : 0 < S := Fact.out
  intro u hu u' hu' h
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, s.displacement i ≠ 0 := by
    by_contra hall
    push Not at hall
    simp [l1NormVec, hall] at hpos
  have h₀ := dist_l1Point (S := S) s u u'
  rw [h, dist_self] at h₀
  have h₁ : ‖(((u - u') * s.displacement i : ℝ) : AddCircle S)‖ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => norm_nonneg _).1 h₀.symm i (Finset.mem_univ i)
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).1 (norm_eq_zero.1 h₁)
  have hdiff : |u - u'| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hu.1, hu.2, hu'.1, hu'.2]
  have hsmall : |(u - u') * s.displacement i| < S := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hdiff).trans_lt
      ((abs_apply_le_l1NormVec _ i).trans_lt hL)
  rw [← hn, zsmul_eq_mul, abs_mul, abs_of_pos hS, mul_lt_iff_lt_one_left hS] at hsmall
  have hn0 : n = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast hsmall)
  subst hn0
  rw [zero_smul] at hn
  exact mul_ne_zero (sub_ne_zero.2 hne) hi hn.symm
theorem l1LengthMeasure_apply {E : Set (Torus4 S)} (hE : MeasurableSet E) :
    l1LengthMeasure S E = μH[1] ((WithLp.ofLp : TorusL1 S → Torus4 S) ⁻¹' E) :=
  Measure.map_apply (WithLp.measurable_ofLp _ _) hE
omit [Fact (0 < S)] in
theorem ofLp_preimage_inter_image (s : LiftedSegment) (A : Set (Torus4 S)) (I : Set ℝ) :
    (WithLp.ofLp : TorusL1 S → Torus4 S) ⁻¹' (A ∩ s.pointAt S '' I) =
      l1Point S s '' (I ∩ s.pointAt S ⁻¹' A) := by
  ext x
  constructor
  · rintro ⟨hA, u, hu, hx⟩
    refine ⟨u, ⟨hu, ?_⟩, ?_⟩
    · rw [mem_preimage, hx]
      exact hA
    · rw [l1Point, hx]
  · rintro ⟨u, ⟨hu, hA⟩, rfl⟩
    exact ⟨hA, u, hu, rfl⟩
omit [Fact (0 < S)] in
theorem measurableSet_inter_image_pointAt {A : Set (Torus4 S)} (hA : MeasurableSet A)
    (s : LiftedSegment) {I : Set ℝ} (hI : IsCompact I) : MeasurableSet (A ∩ s.pointAt S '' I) :=
  hA.inter (hI.image (continuous_pointAt s)).isClosed.measurableSet
theorem l1LengthMeasure_inter_support_le {A : Set (Torus4 S)} (hA : MeasurableSet A)
    (s : LiftedSegment) :
    l1LengthMeasure S (A ∩ s.support S) ≤
      ENNReal.ofReal (l1NormVec s.displacement) *
        volume (Icc (0 : ℝ) 1 ∩ s.pointAt S ⁻¹' A) := by
  rw [LiftedSegment.support,
    l1LengthMeasure_apply (measurableSet_inter_image_pointAt hA s isCompact_Icc),
    ofLp_preimage_inter_image]
  exact hausdorffMeasure_image_l1Point_le s _
theorem le_l1LengthMeasure_inter_support {A : Set (Torus4 S)} (hA : MeasurableSet A)
    (s : LiftedSegment) (hL : l1NormVec s.displacement < S) :
    ENNReal.ofReal (l1NormVec s.displacement) * volume (Icc (0 : ℝ) 1 ∩ s.pointAt S ⁻¹' A) ≤
      l1LengthMeasure S (A ∩ s.support S) := by
  rcases (l1NormVec_nonneg s.displacement).eq_or_lt with h0 | hpos
  · simp [← h0]
  rw [LiftedSegment.support, l1LengthMeasure_apply
    (measurableSet_inter_image_pointAt hA s isCompact_Icc), ofLp_preimage_inter_image]
  set B := Icc (0 : ℝ) 1 ∩ s.pointAt S ⁻¹' A
  have hT : MeasurableSet
      ((WithLp.ofLp : TorusL1 S → Torus4 S) ⁻¹' (s.pointAt S '' Icc 0 (1 / 2))) :=
    (WithLp.measurable_ofLp _ _)
      (isCompact_Icc.image (continuous_pointAt s)).isClosed.measurableSet
  have hlow : ∀ u ∈ Icc (0 : ℝ) (1 / 2), ∀ u' ∈ Icc (0 : ℝ) (1 / 2), |u - u'| ≤ 1 / 2 :=
    fun u hu u' hu' => by
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2, hu'.1, hu'.2]
  have hhigh : ∀ u ∈ Icc (1 / 2 : ℝ) 1, ∀ u' ∈ Icc (1 / 2 : ℝ) 1, |u - u'| ≤ 1 / 2 :=
    fun u hu u' hu' => by
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2, hu'.1, hu'.2]
  have hrest : B \ Icc 0 (1 / 2) ⊆ Icc (1 / 2) 1 := fun u hu =>
    ⟨(not_le.1 fun h => hu.2 ⟨hu.1.1.1, h⟩).le, hu.1.1.2⟩
  have hinj := injOn_l1Point (S := S) s hL hpos
  have hfirst : ENNReal.ofReal (l1NormVec s.displacement) * volume (B ∩ Icc 0 (1 / 2)) ≤
      μH[1] (l1Point S s '' B ∩
        (WithLp.ofLp : TorusL1 S → Torus4 S) ⁻¹' (s.pointAt S '' Icc 0 (1 / 2))) := by
    refine (le_hausdorffMeasure_image_l1Point s hL hpos hlow
      (B := B ∩ Icc 0 (1 / 2)) inter_subset_right).trans (measure_mono ?_)
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu.1, rfl⟩, u, hu.2, rfl⟩
  have hsecond : ENNReal.ofReal (l1NormVec s.displacement) * volume (B \ Icc 0 (1 / 2)) ≤
      μH[1] (l1Point S s '' B \
        (WithLp.ofLp : TorusL1 S → Torus4 S) ⁻¹' (s.pointAt S '' Icc 0 (1 / 2))) := by
    refine (le_hausdorffMeasure_image_l1Point s hL hpos hhigh hrest).trans (measure_mono ?_)
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨⟨u, hu.1, rfl⟩, ?_⟩
    rintro ⟨v, hv, hvu⟩
    have hpt : s.pointAt S v = s.pointAt S u := hvu
    have hvI : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1, hv.2.trans (by norm_num)⟩
    have hveq : v = u := hinj hvI hu.1.1 (congrArg (WithLp.toLp 1) hpt)
    subst hveq
    exact hu.2 hv
  calc ENNReal.ofReal (l1NormVec s.displacement) * volume B
      = ENNReal.ofReal (l1NormVec s.displacement) * volume (B ∩ Icc 0 (1 / 2)) +
          ENNReal.ofReal (l1NormVec s.displacement) * volume (B \ Icc 0 (1 / 2)) := by
        rw [← mul_add, measure_inter_add_sdiff B measurableSet_Icc]
    _ ≤ _ := add_le_add hfirst hsecond
    _ = μH[1] (l1Point S s '' B) := measure_inter_add_sdiff _ hT
omit [Fact (0 < S)] in
theorem segmentsSupport_cons (s : LiftedSegment) (Γ : List LiftedSegment) :
    segmentsSupport S (s :: Γ) = s.support S ∪ segmentsSupport S Γ := by
  simp [segmentsSupport]
omit [Fact (0 < S)] in
theorem isCompact_segmentsSupport (Γ : List LiftedSegment) : IsCompact (segmentsSupport S Γ) := by
  induction Γ with
  | nil => simp [segmentsSupport]
  | cons s Γ ih =>
    rw [segmentsSupport_cons]
    exact (isCompact_Icc.image (continuous_pointAt s)).union ih
omit [Fact (0 < S)] in
theorem pathLengthIn_cons (s : LiftedSegment) (Γ : List LiftedSegment) (A : Set (Torus4 S)) :
    pathLengthIn S (s :: Γ) A =
      l1NormVec s.displacement * (volume (Icc (0 : ℝ) 1 ∩ s.pointAt S ⁻¹' A)).toReal +
        pathLengthIn S Γ A := by
  simp [pathLengthIn]
omit [Fact (0 < S)] in
theorem pathLengthIn_nonneg (Γ : List LiftedSegment) (A : Set (Torus4 S)) :
    0 ≤ pathLengthIn S Γ A := by apply _root_.YangMills.Construction.Weighted.DistBounds.pathLengthIn_nonneg <;> assumption
omit [Fact (0 < S)] in
theorem ofReal_pathLengthIn_cons (s : LiftedSegment) (Γ : List LiftedSegment)
    (A : Set (Torus4 S)) :
    ENNReal.ofReal (pathLengthIn S (s :: Γ) A) =
      ENNReal.ofReal (l1NormVec s.displacement) * volume (Icc (0 : ℝ) 1 ∩ s.pointAt S ⁻¹' A) +
        ENNReal.ofReal (pathLengthIn S Γ A) := by
  have hfin : volume (Icc (0 : ℝ) 1 ∩ s.pointAt S ⁻¹' A) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt (by simp)).ne
  rw [pathLengthIn_cons, ENNReal.ofReal_add
    (mul_nonneg (l1NormVec_nonneg _) ENNReal.toReal_nonneg) (pathLengthIn_nonneg _ _),
    ENNReal.ofReal_mul (l1NormVec_nonneg _), ENNReal.ofReal_toReal hfin]
theorem l1LengthMeasure_inter_segmentsSupport_le {A : Set (Torus4 S)} (hA : MeasurableSet A)
    (Γ : List LiftedSegment) :
    l1LengthMeasure S (A ∩ segmentsSupport S Γ) ≤ ENNReal.ofReal (pathLengthIn S Γ A) := by
  induction Γ with
  | nil => simp [segmentsSupport]
  | cons s Γ ih =>
    rw [segmentsSupport_cons, inter_union_distrib_left, ofReal_pathLengthIn_cons]
    exact (measure_union_le _ _).trans (add_le_add (l1LengthMeasure_inter_support_le hA s) ih)
theorem l1LengthMeasure_singleton_pointAt (s : LiftedSegment) (u : ℝ) :
    l1LengthMeasure S {s.pointAt S u} = 0 := by
  rw [l1LengthMeasure_apply (measurableSet_singleton _)]
  have := Measure.nullSingletonClass_hausdorff (TorusL1 S) (d := 1) zero_lt_one
  have hsub : (WithLp.ofLp : TorusL1 S → Torus4 S) ⁻¹' {s.pointAt S u} ⊆
      {l1Point S s u} := by
    intro x hx
    have hx' : WithLp.ofLp x = s.pointAt S u := hx
    rw [mem_singleton_iff, l1Point, ← hx']
  exact measure_mono_null hsub (measure_singleton _)
theorem le_l1LengthMeasure_inter_segmentsSupport {A : Set (Torus4 S)} (hA : MeasurableSet A)
    (Γ : List LiftedSegment) (hshort : ∀ s ∈ Γ, l1NormVec s.displacement < S)
    (hpair : Γ.Pairwise (MeetOnlyAtEnds S)) :
    ENNReal.ofReal (pathLengthIn S Γ A) ≤ l1LengthMeasure S (A ∩ segmentsSupport S Γ) := by
  induction Γ with
  | nil => simp [pathLengthIn]
  | cons s Γ ih =>
    obtain ⟨hs, hΓ⟩ := List.pairwise_cons.1 hpair
    have hrest := ih (fun t ht => hshort t (List.mem_cons_of_mem _ ht)) hΓ
    have hfirst := le_l1LengthMeasure_inter_support hA s (hshort s List.mem_cons_self)
    have hmeas : MeasurableSet (A ∩ segmentsSupport S Γ) :=
      hA.inter (isCompact_segmentsSupport Γ).isClosed.measurableSet
    have hnull : l1LengthMeasure S ((A ∩ s.support S) ∩ (A ∩ segmentsSupport S Γ)) = 0 := by
      have hsub : (A ∩ s.support S) ∩ (A ∩ segmentsSupport S Γ) ⊆
          {s.pointAt S 0} ∪ {s.pointAt S 1} := by
        rintro x ⟨⟨-, hx⟩, -, hx'⟩
        obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 hx'
        rcases (hs t ht ⟨hx, hxt⟩).1 with h | h
        · exact Or.inl h
        · exact Or.inr h
      exact measure_mono_null hsub (measure_union_null (l1LengthMeasure_singleton_pointAt s 0)
        (l1LengthMeasure_singleton_pointAt s 1))
    have hadd := measure_union_add_inter (μ := l1LengthMeasure S) (A ∩ s.support S) hmeas
    rw [hnull, add_zero] at hadd
    rw [segmentsSupport_cons, inter_union_distrib_left, ofReal_pathLengthIn_cons, hadd]
    exact add_le_add hfirst hrest
end Segments
section Density
variable {D : TorusData} (B : SeparatedChain D)
theorem scale_inv_nonneg (n : ℕ) : 0 ≤ (D.scale n)⁻¹ :=
  inv_nonneg.2 (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) D.bareSpacing_pos.le)
theorem measurableSet_of_isCubeUnionAt {σ : ℝ} {X : Set D.Space} (h : D.IsCubeUnionAt σ X) :
    MeasurableSet X := by
  obtain ⟨C, hC, rfl⟩ := h
  have hlat : (D.latticeAt σ).Countable := by
    refine (countable_range fun k : Fin 4 → ℤ => torusProj D.side fun i => σ * (k i : ℝ)).mono ?_
    rintro x ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  refine MeasurableSet.sUnion ((hlat.image _).mono hC) fun t ht => ?_
  obtain ⟨y, -, rfl⟩ := hC ht
  have hset : D.cubeAround σ y = ⋂ i, {x : D.Space | ‖(x - y) i‖ ≤ σ / 2} := by
    ext x
    simp only [TorusData.cubeAround, mem_ofPred_eq, mem_iInter, torusSupNorm_le_iff]
  rw [hset]
  refine MeasurableSet.iInter fun i => IsClosed.measurableSet (isClosed_le ?_ continuous_const)
  fun_prop
theorem measurableSet_stage_one : MeasurableSet (B.stage 1) := by
  by_cases h : 1 ≤ D.top
  · exact measurableSet_of_isCubeUnionAt (B.cubeUnion 1 h)
  · rw [B.empty_above 1 (not_le.1 h)]
    exact MeasurableSet.empty
theorem ofReal_indicator_one (A : Set D.Space) (x : D.Space) :
    ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) x) = A.indicator (1 : D.Space → ℝ≥0∞) x := by
  by_cases h : x ∈ A <;> simp [h]
theorem setLIntegralL1_weightDensity (hlayer : ∀ n ∈ Finset.Icc 1 D.top, MeasurableSet (B.layer n))
    (C : Set D.Space) :
    setLIntegralL1 C (fun x => ENNReal.ofReal (B.weightDensity x)) =
      ∑ n ∈ Finset.Icc 1 D.top,
        ENNReal.ofReal (D.scale n)⁻¹ * l1LengthMeasure D.side (B.layer n ∩ C) +
      ENNReal.ofReal (D.scale 0)⁻¹ * l1LengthMeasure D.side ((B.stage 1)ᶜ ∩ C) := by
  have hcompl : MeasurableSet (B.stage 1)ᶜ := (measurableSet_stage_one B).compl
  have hfun : (fun x => ENNReal.ofReal (B.weightDensity x)) = fun x =>
      (∑ n ∈ Finset.Icc 1 D.top,
        ENNReal.ofReal (D.scale n)⁻¹ * (B.layer n).indicator (1 : D.Space → ℝ≥0∞) x) +
      ENNReal.ofReal (D.scale 0)⁻¹ * (B.stage 1)ᶜ.indicator (1 : D.Space → ℝ≥0∞) x := by
    funext x
    have hind : ∀ A : Set D.Space, 0 ≤ A.indicator (fun _ => (1 : ℝ)) x :=
      fun A => indicator_nonneg (fun _ _ => zero_le_one) x
    rw [SeparatedChain.weightDensity, ENNReal.ofReal_add
      (Finset.sum_nonneg fun n _ => mul_nonneg (scale_inv_nonneg n) (hind _))
      (mul_nonneg (scale_inv_nonneg 0) (hind _)),
      ENNReal.ofReal_sum_of_nonneg fun n _ => mul_nonneg (scale_inv_nonneg n) (hind _),
      ENNReal.ofReal_mul (scale_inv_nonneg 0), ofReal_indicator_one]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ENNReal.ofReal_mul (scale_inv_nonneg n), ofReal_indicator_one]
  have hterm : ∀ (a : ℝ≥0∞) (X : Set D.Space), MeasurableSet X →
      ∫⁻ x in C, a * X.indicator (1 : D.Space → ℝ≥0∞) x ∂(l1LengthMeasure D.side) =
        a * l1LengthMeasure D.side (X ∩ C) := fun a X hX => by
    rw [lintegral_const_mul a (measurable_one.indicator hX), lintegral_indicator_one hX,
      Measure.restrict_apply hX]
  have hsum : Measurable fun x => ∑ n ∈ Finset.Icc 1 D.top,
      ENNReal.ofReal (D.scale n)⁻¹ * (B.layer n).indicator (1 : D.Space → ℝ≥0∞) x :=
    Finset.measurable_sum _ fun n hn => (measurable_one.indicator (hlayer n hn)).const_mul _
  rw [hfun, setLIntegralL1, lintegral_add_left hsum, hterm _ _ hcompl,
    lintegral_finsetSum _ fun n hn => (measurable_one.indicator (hlayer n hn)).const_mul _]
  congr 1
  exact Finset.sum_congr rfl fun n hn => hterm _ _ (hlayer n hn)
theorem ofReal_weightedLength (Γ : List LiftedSegment) :
    ENNReal.ofReal (B.weightedLength Γ) =
      ∑ n ∈ Finset.Icc 1 D.top,
        ENNReal.ofReal (D.scale n)⁻¹ * ENNReal.ofReal (pathLengthIn D.side Γ (B.layer n)) +
      ENNReal.ofReal (D.scale 0)⁻¹ *
        ENNReal.ofReal (pathLengthIn D.side Γ (B.stage 1)ᶜ) := by
  rw [SeparatedChain.weightedLength, ENNReal.ofReal_add
      (Finset.sum_nonneg fun n _ => mul_nonneg (scale_inv_nonneg n) (pathLengthIn_nonneg _ _))
      (mul_nonneg (scale_inv_nonneg 0) (pathLengthIn_nonneg _ _)),
    ENNReal.ofReal_sum_of_nonneg
      fun n _ => mul_nonneg (scale_inv_nonneg n) (pathLengthIn_nonneg _ _),
    ENNReal.ofReal_mul (scale_inv_nonneg 0)]
  congr 1
  exact Finset.sum_congr rfl fun n _ => ENNReal.ofReal_mul (scale_inv_nonneg n)
theorem stage_subset_stage_one {k : ℕ} (h₁ : 1 ≤ k) (h₂ : k ≤ D.top) :
    B.stage k ⊆ B.stage 1 := by
  induction k, h₁ using Nat.le_induction with
  | base => exact subset_rfl
  | succ k hk ih => exact (B.decreasing k h₂).trans (ih (by omega))
theorem weightDensity_eq_of_mem_interior (hLC : GivenChainGeneral.ShellsAndCubes B)
    {y : D.Space} (hy : y ∈ B.allSites) {x : D.Space} (hx : x ∈ interior (B.siteCube y)) :
    B.weightDensity x = (B.siteScale y)⁻¹ := by
  have hex : {n | y ∈ B.layerSites n}.Nonempty := by
    obtain ⟨n, -, hn⟩ := mem_iUnion₂.1 hy
    exact ⟨n, hn⟩
  have hn : y ∈ B.layerSites (sInf {n | y ∈ B.layerSites n}) := Nat.sInf_mem hex
  have hscale : B.siteScale y = D.scale (sInf {n | y ∈ B.layerSites n}) := rfl
  rw [hscale]
  generalize sInf {n | y ∈ B.layerSites n} = n at hn
  have hle : n ≤ D.top := by
    by_contra h
    have hy' : y ∈ B.layer n := hn.2
    have hnot : ¬ n < D.top := by omega
    have hne : n ≠ D.top := by omega
    simp [SeparatedChain.layer, hnot, hne] at hy'
  have hxn : x ∈ B.layer n := by
    rw [hLC.layer_eq_iUnion n hle]
    exact mem_iUnion₂.2 ⟨y, hn, interior_subset hx⟩
  have hother : ∀ m, m ≠ n → x ∉ B.layer m := fun m hm hxm =>
    Set.disjoint_left.1 (hLC.interior_disjoint_layer n y hn m hm) hx hxm
  rw [SeparatedChain.weightDensity]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hx1 : x ∉ B.stage 1 := Set.disjoint_left.1 (hLC.interior_disjoint_succ 0 y hn) hx
    rw [Finset.sum_eq_zero fun m hm => ?_]
    · simp [hx1]
    · have hm1 : m ≠ 0 := by have := (Finset.mem_Icc.1 hm).1; omega
      simp [hother m hm1]
  · have hx1 : x ∈ B.stage 1 :=
      stage_subset_stage_one B hpos hle ((hLC.layer_subset_diff n hle hxn).1)
    rw [Finset.sum_eq_single_of_mem n (Finset.mem_Icc.2 ⟨hpos, hle⟩) fun m _ hm => ?_]
    · simp [hxn, hx1]
    · simp [hother m hm]
end Density
section LocalLipschitz
variable {S : ℝ}
theorem torusL1Norm_nonneg (x : Torus4 S) : 0 ≤ torusL1Norm x := by apply _root_.YangMills.Construction.Weighted.LocalLip.torusL1Norm_nonneg <;> assumption
theorem abs_torusL1Norm_sub_sub_le (x z z' : Torus4 S) :
    |torusL1Norm (z' - x) - torusL1Norm (z - x)| ≤ torusL1Norm (z' - z) := by
  simp only [torusL1Norm_eq_sum_norm, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h := abs_norm_sub_norm_le ((z' - x) i) ((z - x) i)
  have he : (z' - x) i - (z - x) i = (z' - z) i := by simp
  rwa [he] at h
theorem localLip_le_one {f : Torus4 S → ℝ} (h : ∀ z z', |f z' - f z| ≤ torusL1Norm (z' - z))
    (z : Torus4 S) : localLip f z ≤ 1 := by
  refine limsup_le_of_le (h := ?_)
  filter_upwards with z'
  refine ENNReal.ofReal_le_one.2 ?_
  exact div_le_one_of_le₀ (h z z') (torusL1Norm_nonneg _)
theorem limsup_add_le_add {α : Type*} {F : Filter α} (u v : α → ℝ≥0∞) :
    limsup (fun a => u a + v a) F ≤ limsup u F + limsup v F := by apply _root_.YangMills.Construction.Weighted.LocalLip.ennreal_limsup_add_le <;> assumption
theorem localLip_add_le (f₁ f₂ : Torus4 S → ℝ) {s₁ s₂ : ℝ} (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂)
    (x : Torus4 S) :
    localLip (fun z => s₁ * f₁ z + s₂ * f₂ z) x ≤
      ENNReal.ofReal s₁ * localLip f₁ x + ENNReal.ofReal s₂ * localLip f₂ x := by
  unfold localLip
  rw [← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top,
    ← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  refine le_trans (limsup_le_limsup (Eventually.of_forall fun z => ?_)) (limsup_add_le_add _ _)
  beta_reduce
  have hd := torusL1Norm_nonneg (z - x)
  rw [← ENNReal.ofReal_mul h₁, ← ENNReal.ofReal_mul h₂, ← ENNReal.ofReal_add
    (mul_nonneg h₁ (div_nonneg (abs_nonneg _) hd)) (mul_nonneg h₂ (div_nonneg (abs_nonneg _) hd))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_div_assoc', mul_div_assoc', ← add_div]
  refine div_le_div_of_nonneg_right ?_ hd
  calc |s₁ * f₁ z + s₂ * f₂ z - (s₁ * f₁ x + s₂ * f₂ x)|
      = |s₁ * (f₁ z - f₁ x) + s₂ * (f₂ z - f₂ x)| := by
        congr 1
        ring
    _ ≤ |s₁ * (f₁ z - f₁ x)| + |s₂ * (f₂ z - f₂ x)| := abs_add_le _ _
    _ = s₁ * |f₁ z - f₁ x| + s₂ * |f₂ z - f₂ x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h₁, abs_of_nonneg h₂]
end LocalLipschitz
theorem weightedLengthAndLip_holds (hG : GivenChainGeneralFacts) (hR : LocalLipRules) :
    WeightedLengthAndLip := by
  intro G
  obtain ⟨-, -, hLC, -⟩ := hG G
  obtain ⟨hdist, hcomp, hprod⟩ := hR G.data
  have hlayer : ∀ n ∈ Finset.Icc 1 G.data.top, MeasurableSet (G.chain.layer n) := fun n hn =>
    measurableSet_of_isCubeUnionAt (hLC.layer_isCubeUnion n (Finset.mem_Icc.1 hn).2)
  have hcompl : MeasurableSet (G.chain.stage 1)ᶜ :=
    (measurableSet_stage_one G.chain).compl
  refine ⟨fun Γ => ⟨?_, fun hshort hpair => ?_⟩,
    fun y hy x hx => weightDensity_eq_of_mem_interior _ hLC hy hx,
    fun A hA => hdist A hA, fun x => ⟨⟨1, fun z z' => ?_⟩, localLip_le_one fun z z' => ?_⟩,
    fun f₁ f₂ h₁ h₂ s₁ s₂ ρ hs₁ hs₂ hρ x => ⟨localLip_add_le f₁ f₂ hs₁ hs₂ x, ?_, ?_, ?_⟩⟩
  · rw [setLIntegralL1_weightDensity _ hlayer, ofReal_weightedLength]
    refine add_le_add (Finset.sum_le_sum fun n hn => ?_) ?_
    · exact mul_le_mul_right (l1LengthMeasure_inter_segmentsSupport_le (hlayer n hn) Γ) _
    · exact mul_le_mul_right (l1LengthMeasure_inter_segmentsSupport_le hcompl Γ) _
  · rw [setLIntegralL1_weightDensity _ hlayer, ofReal_weightedLength]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun n hn => ?_) ?_
    · rw [le_antisymm (l1LengthMeasure_inter_segmentsSupport_le (hlayer n hn) Γ)
        (le_l1LengthMeasure_inter_segmentsSupport (hlayer n hn) Γ hshort hpair)]
    · rw [le_antisymm (l1LengthMeasure_inter_segmentsSupport_le hcompl Γ)
        (le_l1LengthMeasure_inter_segmentsSupport hcompl Γ hshort hpair)]
  · simpa using abs_torusL1Norm_sub_sub_le x z z'
  · exact abs_torusL1Norm_sub_sub_le x z z'
  · have h := ((hcomp f₁ h₁).1 (fun r => min r ρ) 1 (LipschitzWith.id.min_const ρ)).2 x
    simpa [Function.comp_def] using h
  · exact (hprod f₁ f₂ h₁ h₂).2 x
  · intro hconst
    exact (hcomp f₁ h₁).2 x ⟨_, hconst, f₁ x, fun y hy => hy⟩
end WeightedLengthProof
end YangMills.Construction.Weighted
end
