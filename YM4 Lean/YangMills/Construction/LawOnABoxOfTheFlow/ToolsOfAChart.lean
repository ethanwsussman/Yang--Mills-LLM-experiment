import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.CellOfTheFlow.ACellIsRareProof
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields RenormalizationStepParameters WeightedResponses ResponseInTheExpansion BlockAverages
variable {n : ℕ} [NeZero n]
set_option synthInstance.maxSize 1024
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
theorem continuous_unitExp : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
theorem continuous_adjointAction {α : Type*} [TopologicalSpace α] {f : α → UnitQuaternion}
    {g : α → imaginaryQuaternions} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a => ColdStepAtMirrorFrames.adjointAction (f a) (g a) := by
  refine Continuous.subtype_mk ?_ _
  exact ((continuous_subtype_val.comp hf).mul (continuous_subtype_val.comp hg)).mul
    (continuous_subtype_val.comp hf.inv)
theorem continuous_chartPoint {α : Type*} [TopologicalSpace α] {f g : α → imaginaryQuaternions}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => chartPoint (f a) (g a) := by
  unfold chartPoint
  refine Continuous.mul (Continuous.add ?_ ?_) ?_
  · have : Continuous fun a => Real.sqrt (1 - ‖g a‖ ^ 2) := by fun_prop
    exact (Quaternion.continuous_coe).comp this
  · exact continuous_subtype_val.comp hg
  · exact continuous_subtype_val.comp (continuous_unitExp.comp hf)
theorem gaugeTransform_gaugeTransform (f h : TorusSite n → UnitQuaternion) (U : TorusField n) :
    TorusFields.gaugeTransform f (TorusFields.gaugeTransform h U) =
      TorusFields.gaugeTransform (f * h) U := by
  funext x i
  simp [TorusFields.gaugeTransform, mul_assoc]
theorem continuous_glueField (o : TorusSite n) (R : ℕ) :
    Continuous fun p : OuterField o R × InnerField o R => (glueField p.1 p.2 : TorusField n) := by
  refine continuous_pi fun x => continuous_pi fun i => ?_
  by_cases h : (x, i) ∈ bondsTouching o R
  · simp only [glueField, dif_pos h]
    exact (continuous_apply _).comp continuous_snd
  · simp only [glueField, dif_neg h]
    exact (continuous_apply _).comp continuous_fst
theorem continuous_gaugeTransform_prod :
    Continuous fun p : (TorusSite n → UnitQuaternion) × TorusField n =>
      TorusFields.gaugeTransform p.1 p.2 := by
  refine continuous_pi fun x => continuous_pi fun i => ?_
  show Continuous fun p : (TorusSite n → UnitQuaternion) × TorusField n =>
    p.1 x * p.2 x i * (p.1 (x + TorusFields.unitStep n i))⁻¹
  have a1 : Continuous fun p : (TorusSite n → UnitQuaternion) × TorusField n => p.1 x :=
    (continuous_apply x).comp continuous_fst
  have a2 : Continuous fun p : (TorusSite n → UnitQuaternion) × TorusField n => p.2 x i :=
    (continuous_apply i).comp ((continuous_apply x).comp continuous_snd)
  have a3 : Continuous fun p : (TorusSite n → UnitQuaternion) × TorusField n =>
      p.1 (x + TorusFields.unitStep n i) :=
    (continuous_apply _).comp continuous_fst
  exact (a1.mul a2).mul a3.inv
theorem continuous_plaquetteCurvature (x : TorusSite n) (μ ν : Fin 4) :
    Continuous fun U : TorusField n => curvature U x μ ν := by
  unfold curvature holonomy
  have a (y : TorusSite n) (i : Fin 4) : Continuous fun U : TorusField n => U y i :=
    (continuous_apply i).comp (continuous_apply y)
  have : Continuous fun U : TorusField n =>
      U x μ * U (x + TorusFields.unitStep n μ) ν * (U (x + TorusFields.unitStep n ν) μ)⁻¹ *
        (U x ν)⁻¹ :=
    (((a _ _).mul (a _ _)).mul (a _ _).inv).mul (a _ _).inv
  exact ((continuous_subtype_val.comp this).sub continuous_const).norm
theorem continuous_exponentialField :
    Continuous fun A : TorusBond n → imaginaryQuaternions => (exponentialField A : TorusField n) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.continuous_expOfCoords <;> assumption
theorem continuous_lieFormCurl (p : TorusPlaquette n) :
    Continuous fun v : TorusBond n → imaginaryQuaternions => lieFormCurl v p := by
  unfold lieFormCurl
  fun_prop
theorem isClosed_setOf_isAxialSmall (o : TorusSite n) (R : ℕ) (δ : ℝ) :
    IsClosed {A | IsAxialSmall o R δ A} := by
  have h : {A | IsAxialSmall o R δ A} =
      (⋂ p ∈ plaquettesIn (supBall o (2 * R)), {A | curvature (exponentialField A) p.1 p.2.1 p.2.2 ≤ δ}) ∩
      (⋂ b ∈ bondsWithin (supBall o (2 * R)),
        {A : TorusBond n → imaginaryQuaternions | ‖A b‖ ≤ 7 * R * δ}) ∩
      {A | curlNormSq (supBall o (2 * R)) A ≤ 2 ^ 13 * (R : ℝ) ^ 4 * δ ^ 2} ∩
      {A | bondNormSq (supBall o (2 * R)) A ≤ 2 ^ 16 * (R : ℝ) ^ 6 * δ ^ 2} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro h
      exact ⟨⟨⟨h.curvature_le, h.norm_le⟩, h.curlNormSq_le⟩, h.bondNormSq_le⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨h1, h2, h3, h4⟩
  rw [h]
  refine ((IsClosed.inter ?_ ?_).inter ?_).inter ?_
  · exact isClosed_biInter fun p _ =>
      isClosed_le ((continuous_plaquetteCurvature _ _ _).comp continuous_exponentialField) continuous_const
  · exact isClosed_biInter fun b _ => isClosed_le (continuous_apply b).norm continuous_const
  · refine isClosed_le ?_ continuous_const
    unfold curlNormSq
    exact continuous_finset_sum _ fun p _ => ((continuous_lieFormCurl p).norm.pow 2)
  · refine isClosed_le ?_ continuous_const
    unfold bondNormSq
    exact continuous_finset_sum _ fun p _ => ((continuous_apply p).norm.pow 2)
theorem continuous_covariantGrad (χ : TorusSite n → imaginaryQuaternions) (b : TorusBond n) :
    Continuous fun A : TorusBond n → imaginaryQuaternions => covariantGrad A χ b := by
  unfold covariantGrad
  refine continuous_const.sub ?_
  exact continuous_adjointAction (continuous_unitExp.comp (continuous_apply b)) continuous_const
theorem isClosed_gaugeSlice_graph (o : TorusSite n) (R : ℕ) :
    IsClosed {p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) |
      p.2 ∈ gaugeSlice o R p.1} := by
  have h : {p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) |
      p.2 ∈ gaugeSlice o R p.1} =
      (⋂ b ∈ {b : TorusBond n | b ∉ bondsTouching o R},
        {p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) | p.2 b = 0}) ∩
      (⋂ χ ∈ {χ : TorusSite n → imaginaryQuaternions | ∀ z, z ∉ supBall o R → χ z = 0},
        {p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) |
          ∑ b : TorusBond n, inner ℝ (p.2 b) (covariantGrad p.1 χ b) = 0}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact Iff.rfl
  rw [h]
  refine IsClosed.inter (isClosed_biInter fun b _ => ?_) (isClosed_biInter fun χ _ => ?_)
  · exact isClosed_eq ((continuous_apply b).comp continuous_snd) continuous_const
  · refine isClosed_eq (continuous_finset_sum _ fun b _ => ?_) continuous_const
    exact Continuous.inner ((continuous_apply b).comp continuous_snd)
      ((continuous_covariantGrad χ b).comp continuous_fst)
theorem continuousOn_of_isClosed_graph_of_isCompact {P V : Type*} [TopologicalSpace P] [TopologicalSpace V]
    {E : Set P} {K : Set V} (hK : IsCompact K) (hE : IsClosed E) {Γ : Set (P × V)} (hΓ : IsClosed Γ)
    {φ : P → V} (hφ : ∀ p ∈ E, (p, φ p) ∈ Γ ∧ φ p ∈ K)
    (huniq : ∀ p ∈ E, ∀ v, (p, v) ∈ Γ → v ∈ K → v = φ p) :
    ContinuousOn φ E := by
  rw [continuousOn_iff_isClosed]
  intro C hC
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Z : Set (P × K) := {z | (z.1, (z.2 : V)) ∈ Γ ∧ (z.2 : V) ∈ C}
  have hZ : IsClosed Z :=
    (hΓ.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).inter
      (hC.preimage (continuous_subtype_val.comp continuous_snd))
  refine ⟨Prod.fst '' Z, isClosedMap_fst_of_compactSpace _ hZ, ?_⟩
  ext p
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨(p, ⟨φ p, (hφ p h2).2⟩), ⟨(hφ p h2).1, h1⟩, rfl⟩, h2⟩
  · rintro ⟨⟨z, ⟨hz1, hz2⟩, rfl⟩, h2⟩
    have := huniq z.1 h2 z.2 hz1 z.2.2
    exact ⟨this ▸ hz2, h2⟩
theorem le_boxRadius (κ₀ x : ℝ) (h1 : 1 / 27 ≤ κ₀) (r : ℕ) (hx : ((r : ℝ) + 1) ^ 27 ≤ x) :
    r ≤ boxRadius κ₀ x := by
  have hr : (1 : ℝ) ≤ (r : ℝ) + 1 := by
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hx1 : 1 ≤ x := le_trans (one_le_pow₀ hr) hx
  have h27 : (r : ℝ) + 1 ≤ x ^ (1 / 27 : ℝ) := by
    calc (r : ℝ) + 1 = (((r : ℝ) + 1) ^ (27 : ℕ)) ^ (1 / 27 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          norm_num
      _ ≤ x ^ (1 / 27 : ℝ) := Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have h2 : x ^ (1 / 27 : ℝ) ≤ x ^ κ₀ := Real.rpow_le_rpow_of_exponent_le hx1 h1
  have h3 : x ^ κ₀ ≤ (boxRadius κ₀ x : ℝ) := Nat.le_ceil _
  have : (r : ℝ) ≤ (boxRadius κ₀ x : ℝ) := by linarith
  exact_mod_cast this
theorem continuous_imaginaryComponent (e : Fin 3) : Continuous (imaginaryComponent e) := by
  have hv : Continuous fun w : imaginaryQuaternions => (w : ℍ[ℝ]) := continuous_subtype_val
  unfold imaginaryComponent
  fin_cases e
  · exact Quaternion.continuous_imI.comp hv
  · exact Quaternion.continuous_imJ.comp hv
  · exact Quaternion.continuous_imK.comp hv
theorem mem_bondsWithin_of_mem_bondsTouching {o : TorusSite n} {R : ℕ} (hR : 1 ≤ R) {b : TorusBond n}
    (hb : b ∈ bondsTouching o R) : b ∈ bondsWithin (supBall o (2 * R)) := by apply _root_.YangMills.SharedProofs.p15112 <;> assumption
theorem isClosed_sliceEllipsoid_graph (a : ℝ) (L k : ℕ) (o : TorusSite n) (R : ℕ) (c₀ : ℝ)
    (hq : Continuous fun v : TorusBond n → imaginaryQuaternions => hessianForm a L k (supBall o (2 * R)) v v) :
    IsClosed {p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) |
      p.2 ∈ sliceEllipsoid a L k o R p.1 c₀} :=
  (isClosed_gaugeSlice_graph o R).inter
    (isClosed_le (hq.comp (continuous_fst.add continuous_snd)) continuous_const)
theorem continuous_hessianForm_diag {a : ℝ} {L k : ℕ} {S : Finset (TorusSite n)}
    (hform : ∀ u v : TorusBond n → imaginaryQuaternions, hessianForm a L k S u v =
      ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
        mixedDeriv (actionAtLevel a L k S) (trivialField n) ![b, b'] ![imaginaryUnitI, imaginaryUnitI] *
          imaginaryComponent e (u b) * imaginaryComponent e (v b')) :
    Continuous fun v : TorusBond n → imaginaryQuaternions => hessianForm a L k S v v := by
  have : (fun v : TorusBond n → imaginaryQuaternions => hessianForm a L k S v v) = fun v =>
      ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
        mixedDeriv (actionAtLevel a L k S) (trivialField n) ![b, b'] ![imaginaryUnitI, imaginaryUnitI] *
          imaginaryComponent e (v b) * imaginaryComponent e (v b') := funext fun v => hform v v
  rw [this]
  refine continuous_finset_sum _ fun e _ => continuous_finset_sum _ fun b _ =>
    continuous_finset_sum _ fun b' _ => ?_
  exact (continuous_const.mul ((continuous_imaginaryComponent e).comp (continuous_apply b))).mul
    ((continuous_imaginaryComponent e).comp (continuous_apply b'))
theorem holdsAtAdmissibleParameters_mono {P Q : ParameterAssignment → ℝ → Prop}
    (h : ∀ T y, T.Admissible → P T y → Q T y)
    (hP : HoldsAtAdmissibleParameters P) : HoldsAtAdmissibleParameters Q := by
  intro a ha
  obtain ⟨L₀, rt₀, hrt, hp⟩ := hP a ha
  refine ⟨L₀, rt₀, hrt, fun L hL hL₀ T hTa hTL hTd hTr => ?_⟩
  obtain ⟨y₀, hy⟩ := hp L hL hL₀ T hTa hTL hTd hTr
  exact ⟨y₀, fun y hy₀ hr hw => h T y hTd (hy y hy₀ hr hw)⟩
theorem holdsAtAdmissibleParameters_and {P Q : ParameterAssignment → ℝ → Prop}
    (hP : HoldsAtAdmissibleParameters P) (hQ : HoldsAtAdmissibleParameters Q) :
    HoldsAtAdmissibleParameters fun T y => P T y ∧ Q T y := by apply _root_.YangMills.SharedProofs.p114722 <;> assumption
theorem holdsAtAdmissibleParameters_floorMin_le : HoldsAtAdmissibleParameters fun T y => T.floorMin ≤ y := by
  intro a ha
  exact ⟨0, fun _ => 1, fun _ => one_pos, fun L _ _ T _ _ hTd _ => ⟨T.floorMin, fun y hy _ _ => hy⟩⟩
theorem measurableEmbedding_sigmaMk {ι : Type*} {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)] (i : ι) :
    MeasurableEmbedding (Sigma.mk i : Z i → Sigma Z) := by
  classical
  refine ⟨sigma_mk_injective,
    Measurable.of_le_map (iInf_le (fun a => (inferInstance : MeasurableSpace (Z a)).map (Sigma.mk a)) i), ?_⟩
  intro s hs
  refine MeasurableSpace.measurableSet_iInf.2 fun a => ?_
  show MeasurableSet ((Sigma.mk a : Z a → Sigma Z) ⁻¹' (Sigma.mk i '' s))
  by_cases h : a = i
  · subst h
    rwa [sigma_mk_injective.preimage_image]
  · have : (Sigma.mk a : Z a → Sigma Z) ⁻¹' (Sigma.mk i '' s) = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
      rintro ⟨w, -, hw⟩
      exact h (congrArg Sigma.fst hw).symm
    rw [this]
    exact MeasurableSet.empty
theorem measurable_prod_sigma_of_forall {ι : Type*} [Countable ι] {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace E]
    {f : (A × Sigma Z) × B → E}
    (h : ∀ i, Measurable fun p : (A × Z i) × B => f ((p.1.1, ⟨i, p.1.2⟩), p.2)) :
    Measurable f := by
  intro s hs
  let e : ∀ i, (A × Z i) × B → (A × Sigma Z) × B := fun i p => ((p.1.1, ⟨i, p.1.2⟩), p.2)
  have he : ∀ i, MeasurableEmbedding (e i) := fun i =>
    (MeasurableEmbedding.id.prodMap (measurableEmbedding_sigmaMk i)).prodMap MeasurableEmbedding.id
  have : f ⁻¹' s = ⋃ i, e i '' ((fun p => f (e i p)) ⁻¹' s) := by
    ext ⟨⟨a, ⟨i, z⟩⟩, b⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hf
      exact ⟨i, ((a, z), b), hf, rfl⟩
    · rintro ⟨j, p, hp, hpe⟩
      rw [← hpe]
      exact hp
  rw [this]
  exact MeasurableSet.iUnion fun i => (he i).measurableSet_image.2 (h i hs)
theorem measurable_restrictOuter (o : TorusSite n) (R : ℕ) :
    Measurable (restrictOuter o R : TorusField n → OuterField o R) :=
  measurable_pi_lambda _ fun b => (measurable_pi_apply b.1.2).comp (measurable_pi_apply b.1.1)
theorem measurable_restrictInner (o : TorusSite n) (R : ℕ) :
    Measurable (restrictInner o R : TorusField n → InnerField o R) :=
  measurable_pi_lambda _ fun b => (measurable_pi_apply b.1.2).comp (measurable_pi_apply b.1.1)
theorem measurable_glueField (o : TorusSite n) (R : ℕ) :
    Measurable fun p : OuterField o R × InnerField o R => (glueField p.1 p.2 : TorusField n) := by
  refine measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun i => ?_
  by_cases h : (x, i) ∈ bondsTouching o R
  · simp only [glueField, dif_pos h]
    exact (measurable_pi_apply _).comp measurable_snd
  · simp only [glueField, dif_neg h]
    exact (measurable_pi_apply _).comp measurable_fst
theorem restrictOuter_glueField {o : TorusSite n} {R : ℕ} (u : OuterField o R) (w : InnerField o R) :
    restrictOuter o R (glueField u w) = u := by
  funext b
  simp only [restrictOuter, glueField]
  rw [dif_neg b.2]
theorem restrictInner_glueField {o : TorusSite n} {R : ℕ} (u : OuterField o R) (w : InnerField o R) :
    restrictInner o R (glueField u w) = w := by
  funext b
  simp only [restrictInner, glueField]
  rw [dif_pos b.2]
theorem glueField_restrictOuter_restrictInner {o : TorusSite n} {R : ℕ} (U : TorusField n) :
    glueField (restrictOuter o R U) (restrictInner o R U) = U := by
  funext x i
  simp only [glueField, restrictOuter, restrictInner]
  split_ifs <;> rfl
end YangMills.Construction.BoxGaussian
end
