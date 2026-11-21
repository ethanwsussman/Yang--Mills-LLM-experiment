import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.InfiniteLattice.FaceEnergyUnderProbability
import YangMills.Construction.PassageToTheLimit.EquicontinuityWithoutABound
import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBounded
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentatives
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity
namespace ApproximatingSequences
namespace BoundedOfLimits
open SeparatedTuples (IsC1c IsDisjointlySupported RealValued SepTuple)
open TestFunctions (c1NormR4 euclidDistR4 lipConstR4 partialDerivR4 sharpNormR4 uniformNorm)
open TorusMetric (euclidNormVec)
section Norms
variable {f : RealValued}
theorem partialDerivR4_eq_fderiv (hf : ContDiff ℝ 1 f) (μ : Fin 4) (x : Fin 4 → ℝ) :
    partialDerivR4 μ f x = fderiv ℝ f x (Pi.single μ 1) := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.partialDerivR4_eq_fderiv <;> assumption
theorem bddAbove_range_norm {g : RealValued} (hc : Continuous g) (hs : HasCompactSupport g) :
    BddAbove (Set.range fun x => ‖g x‖) := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
theorem uniformNorm_nonneg (g : RealValued) : 0 ≤ uniformNorm g :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem norm_le_uniformNorm {g : RealValued} (hc : Continuous g) (hs : HasCompactSupport g)
    (x : Fin 4 → ℝ) : ‖g x‖ ≤ uniformNorm g :=
  le_ciSup (bddAbove_range_norm hc hs) x
theorem uniformNorm_le_c1NormR4 (g : RealValued) : uniformNorm g ≤ c1NormR4 g :=
  le_max_left _ _
theorem c1NormR4_nonneg (g : RealValued) : 0 ≤ c1NormR4 g :=
  (uniformNorm_nonneg g).trans (uniformNorm_le_c1NormR4 g)
theorem norm_le_c1NormR4 {g : RealValued} (hc : Continuous g) (hs : HasCompactSupport g)
    (x : Fin 4 → ℝ) : ‖g x‖ ≤ c1NormR4 g :=
  (norm_le_uniformNorm hc hs x).trans (uniformNorm_le_c1NormR4 g)
theorem norm_partialDerivR4_le_c1NormR4 (hf : IsC1c f) (μ : Fin 4) (x : Fin 4 → ℝ) :
    ‖partialDerivR4 μ f x‖ ≤ c1NormR4 f := by
  have hC : ContDiff ℝ 1 f := hf.1
  have hform : partialDerivR4 μ f = fun x => fderiv ℝ f x (Pi.single μ 1) :=
    funext (partialDerivR4_eq_fderiv hC μ)
  have hcont : Continuous (partialDerivR4 μ f) := by
    rw [hform]
    exact (hC.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsupp : HasCompactSupport (partialDerivR4 μ f) := by
    rw [hform]
    exact (hf.2.fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L (Pi.single μ 1)) rfl
  refine (norm_le_uniformNorm hcont hsupp x).trans ?_
  refine le_trans ?_ (le_max_right _ _)
  exact le_ciSup (f := fun μ : Fin 4 => uniformNorm (partialDerivR4 μ f)) (Set.finite_range _).bddAbove μ
theorem sum_abs_le_two_mul_euclidNormVec (v : Fin 4 → ℝ) : ∑ μ, |v μ| ≤ 2 * euclidNormVec v := by
  have h : (∑ μ, |v μ|) / 2 ≤ euclidNormVec v := by
    refine Real.le_sqrt_of_sq_le ?_
    simp only [Fin.sum_univ_four]
    have e : ∀ μ, v μ ^ 2 = |v μ| ^ 2 := fun μ => (sq_abs _).symm
    rw [e 0, e 1, e 2, e 3]
    nlinarith [sq_nonneg (|v 0| - |v 1|), sq_nonneg (|v 0| - |v 2|), sq_nonneg (|v 0| - |v 3|),
      sq_nonneg (|v 1| - |v 2|), sq_nonneg (|v 1| - |v 3|), sq_nonneg (|v 2| - |v 3|)]
  linarith
theorem norm_sub_le_two_mul_c1NormR4 (hf : IsC1c f) (x y : Fin 4 → ℝ) :
    ‖f x - f y‖ ≤ 2 * c1NormR4 f * euclidDistR4 x y := by
  have hC : ContDiff ℝ 1 f := hf.1
  set v : Fin 4 → ℝ := x - y with hv
  set g : ℝ → ℝ := fun t => f (y + t • v) with hg
  have hder : ∀ t : ℝ, HasDerivAt g (fderiv ℝ f (y + t • v) v) t := fun t => by
    have h : HasFDerivAt f (fderiv ℝ f (y + t • v)) (y + t • v) :=
      (hC.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => y + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add y
    exact h.comp_hasDerivAt t hl
  have hsum : ∀ z : Fin 4 → ℝ, fderiv ℝ f z v = ∑ μ, v μ * partialDerivR4 μ f z := fun z => by
    have hdec : v = ∑ μ, v μ • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hdec]
    simp [map_sum, partialDerivR4_eq_fderiv hC]
  have hbound : ∀ t ∈ (Set.univ : Set ℝ), ‖deriv g t‖ ≤ 2 * c1NormR4 f * euclidNormVec v := by
    intro t _
    rw [(hder t).deriv, hsum]
    calc ‖∑ μ, v μ * partialDerivR4 μ f (y + t • v)‖
        ≤ ∑ μ, ‖v μ * partialDerivR4 μ f (y + t • v)‖ := norm_sum_le _ _
      _ ≤ ∑ μ, |v μ| * c1NormR4 f := by
          refine Finset.sum_le_sum fun μ _ => ?_
          rw [norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (norm_partialDerivR4_le_c1NormR4 hf μ _) (abs_nonneg _)
      _ = (∑ μ, |v μ|) * c1NormR4 f := (Finset.sum_mul _ _ _).symm
      _ ≤ (2 * euclidNormVec v) * c1NormR4 f :=
          mul_le_mul_of_nonneg_right (sum_abs_le_two_mul_euclidNormVec v) (c1NormR4_nonneg f)
      _ = 2 * c1NormR4 f * euclidNormVec v := by ring
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := Set.univ) (x := 0) (y := 1)
    (fun t _ => (hder t).differentiableAt) hbound convex_univ (Set.mem_univ _) (Set.mem_univ _)
  have h1 : g 1 = f x := by simp [hg, hv]
  have h0 : g 0 = f y := by simp [hg]
  rw [h1, h0] at hmv
  simpa [euclidDistR4, hv] using hmv
theorem two_mul_c1NormR4_mem_lipSet (hf : IsC1c f) :
    2 * c1NormR4 f ∈ {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y} :=
  ⟨by linarith [c1NormR4_nonneg f], norm_sub_le_two_mul_c1NormR4 hf⟩
theorem lipConstR4_le_two_mul_c1NormR4 (hf : IsC1c f) :
    lipConstR4 f ≤ 2 * c1NormR4 f :=
  csInf_le ⟨0, fun _ hC => hC.1⟩ (two_mul_c1NormR4_mem_lipSet hf)
theorem lipConstR4_nonneg (g : RealValued) : 0 ≤ lipConstR4 g :=
  Real.sInf_nonneg fun _ hC => hC.1
theorem euclidDistR4_add_smul_single (x : Fin 4 → ℝ) (μ : Fin 4) (t : ℝ) :
    euclidDistR4 (x + t • Pi.single μ (1 : ℝ)) x = ‖t‖ := by
  have h : ∑ ν, (t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) ν ^ 2 = t ^ 2 := by
    rw [Finset.sum_eq_single μ]
    · simp
    · intro ν _ hν
      simp [hν]
    · simp
  simp only [euclidDistR4, euclidNormVec, add_sub_cancel_left]
  rw [h, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
theorem norm_partialDerivR4_le_lipConstR4 (hf : IsC1c f) (μ : Fin 4) (x : Fin 4 → ℝ) :
    ‖partialDerivR4 μ f x‖ ≤ lipConstR4 f := by
  refine le_csInf ⟨_, two_mul_c1NormR4_mem_lipSet hf⟩ fun C hC => ?_
  refine norm_deriv_le_of_lip' hC.1 (Eventually.of_forall fun t => ?_)
  have h := hC.2 (x + t • Pi.single μ (1 : ℝ)) x
  rw [euclidDistR4_add_smul_single] at h
  simpa using h
theorem c1NormR4_le_sharpNormR4 {M : ℝ} (hM : 1 ≤ M) (hf : IsC1c f) :
    c1NormR4 f ≤ sharpNormR4 M f := by
  refine max_le_max le_rfl (ciSup_le fun μ => ciSup_le fun x => ?_)
  have h := norm_partialDerivR4_le_lipConstR4 hf μ x
  nlinarith [lipConstR4_nonneg f]
theorem sharpNormR4_le_c1NormR4 {M : ℝ} (hM : 1 ≤ M) (hf : IsC1c f) :
    sharpNormR4 M f ≤ 80 * M * c1NormR4 f := by
  refine max_le ?_ ?_
  · nlinarith [uniformNorm_le_c1NormR4 f, c1NormR4_nonneg f]
  · nlinarith [lipConstR4_le_two_mul_c1NormR4 hf, c1NormR4_nonneg f]
theorem le_mul_prod_of_le_of_zero {k : ℕ} {a b : Fin k → ℝ} {r C : ℝ} (hr : 0 ≤ r) (ha : ∀ l, 0 ≤ a l)
    (hab : ∀ l, a l ≤ b l) (hz : ∀ l, a l = 0 → b l = 0) (h : r ≤ C * ∏ l, a l) :
    r ≤ C * ∏ l, b l := by
  by_cases hC : 0 ≤ C
  · exact h.trans (mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun l _ => ha l) fun l _ => hab l) hC)
  · have hP : 0 ≤ ∏ l, a l := Finset.prod_nonneg fun l _ => ha l
    have hP0 : ∏ l, a l = 0 := by
      by_contra hne
      have : 0 < ∏ l, a l := lt_of_le_of_ne hP (Ne.symm hne)
      nlinarith [not_le.1 hC]
    obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.1 hP0
    rw [hP0, mul_zero] at h
    rw [Finset.prod_eq_zero (Finset.mem_univ l) (hz l hl), mul_zero]
    exact h
end Norms
section BlockEvaluations
open AxisMirror in
theorem closedSupport_euclidean (D : MirrorData) (f : RealValued) :
    Ambient.closedSupport D .euclidean f = tsupport f := by apply _root_.YangMills.Construction.R4TupleForms.closedSupport_euclidean_eq <;> assumption
open AxisMirror in
theorem isDisjointlySupported_of_mem_separatedN (D : MirrorData) {k : ℕ} {f : Fin k → RealValued}
    (h : List.ofFn f ∈ Ambient.separatedN D .euclidean k) : IsDisjointlySupported (List.ofFn f) := by
  obtain ⟨-, hC, hP⟩ := h
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨hg₁, hg₂⟩ := hC g hg
    refine ⟨hg₁, ?_⟩
    have h' := (SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) _).1 hg₂
    rw [closedSupport_euclidean] at h'
    exact h'
  · exact hP.imp fun {a b} hab =>
      hab.mono (closedSupport_euclidean D a).ge (closedSupport_euclidean D b).ge
open AxisMirror in
theorem mem_separatedN_of_isDisjointlySupported (D : MirrorData) {k : ℕ} {f : Fin k → RealValued}
    (h : IsDisjointlySupported (List.ofFn f)) : List.ofFn f ∈ Ambient.separatedN D .euclidean k := by
  refine ⟨List.length_ofFn, fun g hg => ?_, ?_⟩
  · obtain ⟨hg₁, hg₂⟩ := h.1 g hg
    refine ⟨hg₁, ?_⟩
    refine (SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) _).2 ?_
    exact (congrArg (IsCompact (X := Fin 4 → ℝ)) (closedSupport_euclidean D g)).mpr hg₂
  · exact h.2.imp fun {a b} hab =>
      hab.mono (closedSupport_euclidean D a).le (closedSupport_euclidean D b).le
theorem isC1c_of_isDisjointlySupported {k : ℕ} {f : Fin k → RealValued}
    (h : IsDisjointlySupported (List.ofFn f)) (l : Fin k) : IsC1c (f l) :=
  h.1 _ ((List.mem_ofFn' _ _).2 ⟨l, rfl⟩)
open LimitSpaces in
theorem closedSupport_limitEuclidean (s : Conventions.StandingParameters) (f : RealValued) :
    Ambient.euclidean.closedSupport s f = tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
open LimitSpaces in
theorem isCompactSubset_euclidean_iff (s : Conventions.StandingParameters) (Z : Set (Fin 4 → ℝ)) :
    Ambient.euclidean.IsCompactSubset s Z ↔ IsCompact Z :=
  SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) Z
open LimitSpaces in
theorem mem_c1Within_iff (s : Conventions.StandingParameters) (W : Set (Fin 4 → ℝ)) (f : RealValued) :
    f ∈ Ambient.euclidean.c1Within s W ↔ IsC1c f ∧ tsupport f ⊆ W := by
  have hk := isCompactSubset_euclidean_iff s (tsupport f)
  have hs := closedSupport_limitEuclidean s f
  constructor
  · rintro ⟨⟨h₁, -⟩, h₂, h₃⟩
    rw [hs] at h₂ h₃
    exact ⟨⟨h₁, hk.1 h₂⟩, h₃⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    have h₂' : Ambient.euclidean.IsCompactSubset s (Ambient.euclidean.closedSupport s f) := by
      rw [hs]
      exact hk.2 h₂
    refine ⟨⟨h₁, h₂'⟩, h₂', ?_⟩
    rw [hs]
    exact h₃
open LimitSpaces in
theorem normC1_euclidean (s : Conventions.StandingParameters) (f : RealValued) :
    Ambient.euclidean.normC1 s f = c1NormR4 f := by
  have h : ∀ μ : Fin 4, Ambient.euclidean.partialDeriv s μ f = partialDerivR4 μ f := fun μ => by
    funext x
    have hx := congrFun (Ambient.grad_comp_proj s Ambient.euclidean f) x
    exact congrFun hx μ
  simp only [Ambient.normC1, c1NormR4, h]
  rfl
end BlockEvaluations
section Field
open InfiniteLattice (faceEnergy ElementaryPlaquette refinedSpacing)
theorem exists_smearedField_bound (hP : InfiniteLattice.FaceEnergyBoundedAndFacesLocallyFinite)
    (D : AxisMirror.MirrorData) (T : LatticeApproximation D.L) (j : ℕ+) {A : Set (Fin 4 → ℝ)}
    (hA : IsCompact A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : RealValued, IsC1c f → tsupport f ⊆ A →
      ∀ U, ‖T.smearedField j f U‖ ≤ B * c1NormR4 f := by
  let s' : Conventions.StandingParameters := { D.toStandingParameters with K := T.cutoff j }
  obtain ⟨⟨-, hact⟩, hfin⟩ := hP s' (T.state j) (T.isProbabilityMeasure_state j)
  have hF := hfin A hA.isBounded
  refine ⟨(hF.toFinset.card : ℝ) * (2 + |T.offset j|), by positivity, fun f hf hsupp U => ?_⟩
  have hcont : Continuous f := hf.1.continuous
  have hsub : Function.support (fun p : ElementaryPlaquette (refinedSpacing D.L (T.cutoff j)) =>
      f p.center * ((faceEnergy U p - T.offset j : ℝ) : ℝ)) ⊆ ↑hF.toFinset := by
    intro p hp
    have hne : f p.center ≠ 0 := fun h0 => hp (by simp [h0])
    exact Finset.mem_coe.2 (hF.mem_toFinset.2 (hsupp (subset_tsupport f hne)))
  have hfield : T.smearedField j f U = ∑ p ∈ hF.toFinset,
      f p.center * ((faceEnergy U p - T.offset j : ℝ) : ℝ) := by
    simp only [LatticeApproximation.smearedField, RCLike.ofReal_real_eq_id, id]
    exact finsum_eq_sum_of_support_subset _ hsub
  rw [hfield]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ p ∈ hF.toFinset,
      ‖f p.center * ((faceEnergy U p - T.offset j : ℝ) : ℝ)‖ ≤
        c1NormR4 f * (2 + |T.offset j|) := by
    intro p _
    rw [norm_mul]
    have h₁ := norm_le_c1NormR4 hcont hf.2 p.center
    have h₂ := (hact p).2 U
    have h₃ : ‖faceEnergy U p - T.offset j‖ ≤ 2 + |T.offset j| := by
      rw [Real.norm_eq_abs]
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg h₂.1]
      linarith [h₂.2]
    exact mul_le_mul h₁ h₃ (norm_nonneg _) (c1NormR4_nonneg f)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact le_of_eq (by ring)
end Field
section Forms
open LimitSpaces (indexAtTop)
open LimitSpaces.Ambient (C1ProductSpace IsBoundedMultilinear IsMultilinearRealForm operatorBound)
theorem ofFn_eq_take_append_cons_drop_of_eq {α : Type*} {k : ℕ} (g g' : Fin k → α) (i : Fin k)
    (h : ∀ l, l ≠ i → g l = g' l) :
    List.ofFn g = (List.ofFn g').take i ++ g i :: (List.ofFn g').drop (i + 1) := by
  have ht : (List.ofFn g).take i = (List.ofFn g').take i := by
    refine List.ext_getElem (by simp) fun n h₁ h₂ => ?_
    have hn : n < i := by
      simp only [List.length_take, List.length_ofFn] at h₁
      omega
    simp only [List.getElem_take, List.getElem_ofFn]
    exact h _ fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
  have hd : (List.ofFn g).drop (i + 1) = (List.ofFn g').drop (i + 1) := by
    refine List.ext_getElem (by simp) fun n h₁ h₂ => ?_
    simp only [List.getElem_drop, List.getElem_ofFn]
    exact h _ fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
  have hi : (i : ℕ) < (List.ofFn g).length := by simp
  rw [← ht, ← hd]
  conv_lhs => rw [← List.take_append_drop (i : ℕ) (List.ofFn g), List.drop_eq_getElem_cons hi]
  simp
variable {s : Conventions.StandingParameters} {k : ℕ} {A : Fin k → Set (Fin 4 → ℝ)}
def componentFuns (h : C1ProductSpace s .euclidean A) : Fin k → RealValued := fun l => (h l).1
theorem componentFuns_spec (h : C1ProductSpace s .euclidean A) (l : Fin k) :
    IsC1c (componentFuns h l) ∧ tsupport (componentFuns h l) ⊆ A l :=
  (mem_c1Within_iff s (A l) _).1 (h l).2
theorem isDisjointlySupported_componentFuns (hd : Pairwise (Function.onFun Disjoint A))
    (h : C1ProductSpace s .euclidean A) : IsDisjointlySupported (List.ofFn (componentFuns h)) := by
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact (componentFuns_spec h l).1
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact (hd hij.ne).mono (componentFuns_spec h i).2 (componentFuns_spec h j).2
variable {D : AxisMirror.MirrorData} (T : LatticeApproximation D.L)
def productForm (s : Conventions.StandingParameters) (A : Fin k → Set (Fin 4 → ℝ)) (j : ℕ+)
    (h : C1ProductSpace s .euclidean A) : ℝ :=
  ∫ U, T.latticeProduct j (List.ofFn (componentFuns h)) U ∂T.state j
theorem productForm_isMultilinearRealForm
    (hCov : RepresentativeCovariance.RepresentativesCovariantAndLocal)
    (hd : Pairwise (Function.onFun Disjoint A)) (j : ℕ+) :
    IsMultilinearRealForm (productForm T s A j) := by
  obtain ⟨σ, hσ, -, hlin⟩ := (hCov D.L D.isAdmissible T j).2.2.2.2
  intro i a b X Y Z hY hZ hi
  have hval : ∀ h : C1ProductSpace s .euclidean A,
      σ ⟨List.ofFn (componentFuns h), isDisjointlySupported_componentFuns hd h⟩ = productForm T s A j h :=
    fun h => hσ _
  rw [← hval, ← hval, ← hval]
  refine hlin ((List.ofFn (componentFuns X)).take i)
    ((List.ofFn (componentFuns X)).drop (i + 1)) (componentFuns X i)
    (componentFuns Y i) a b _ _ _ ?_ ?_ ?_
  · exact ofFn_eq_take_append_cons_drop_of_eq _ _ i fun _ _ => rfl
  · exact ofFn_eq_take_append_cons_drop_of_eq _ _ i hY
  · have h := ofFn_eq_take_append_cons_drop_of_eq (componentFuns Z) (componentFuns X) i hZ
    have hi' : componentFuns Z i =
        a • componentFuns X i + b • componentFuns Y i := hi
    rw [hi'] at h
    exact h
theorem latticeProduct_ofFn (j : ℕ+) (f : Fin k → RealValued) (U) :
    T.latticeProduct j (List.ofFn f) U = ∏ l, T.smearedField j (f l) U := by
  simp [LatticeApproximation.latticeProduct, List.map_ofFn, List.prod_ofFn]
theorem productForm_isBoundedMultilinear (hP : InfiniteLattice.FaceEnergyBoundedAndFacesLocallyFinite)
    (hc : ∀ l, IsCompact (A l)) (j : ℕ+) : IsBoundedMultilinear (productForm T s A j) := by
  choose B hB0 hB using fun l => exists_smearedField_bound hP D T j (hc l)
  have key : ∀ h : C1ProductSpace s .euclidean A,
      (∀ l, LimitSpaces.Ambient.euclidean.normC1 s (h l).1 ≤ 1) →
        |productForm T s A j h| ≤ ∏ l, B l := by
    intro h hh
    have hU : ∀ U, ‖T.latticeProduct j (List.ofFn (componentFuns h)) U‖ ≤ ∏ l, B l := by
      intro U
      rw [latticeProduct_ofFn, norm_prod]
      refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun l _ => ?_
      have hl := hB l _ (componentFuns_spec h l).1 (componentFuns_spec h l).2 U
      have hn : c1NormR4 (componentFuns h l) ≤ 1 :=
        (normC1_euclidean s _).ge.trans (hh l)
      exact hl.trans (by nlinarith [hB0 l])
    have := T.isProbabilityMeasure_state j
    have hI := norm_integral_le_of_norm_le_const (μ := T.state j) (Eventually.of_forall hU)
    simpa [productForm] using hI
  exact lt_of_le_of_lt (iSup₂_le fun h hh => ENNReal.ofReal_le_ofReal (key h hh))
    ENNReal.ofReal_lt_top
theorem exists_uniform_bound
    (hCov : RepresentativeCovariance.RepresentativesCovariantAndLocal)
    (hF : LimitSpaces.Ambient.uniformBoundednessEquicontinuity)
    (hP : InfiniteLattice.FaceEnergyBoundedAndFacesLocallyFinite)
    (hlim : ∀ X : SepTuple, ∃ c : ℝ,
      Tendsto (fun j => ∫ U, T.latticeProduct j X.1 U ∂T.state j) atTop (𝓝 c))
    (hk : 1 ≤ k) (hc : ∀ l, IsCompact (A l)) (hd : Pairwise (Function.onFun Disjoint A)) :
    ∃ C : ℝ, ∀ (j : ℕ+) (f : Fin k → RealValued), IsDisjointlySupported (List.ofFn f) →
      (∀ l, tsupport (f l) ⊆ A l) →
      |∫ U, T.latticeProduct j (List.ofFn f) U ∂T.state j| ≤
        C * ∏ l, c1NormR4 (f l) := by
  have hAc : ∀ l, LimitSpaces.Ambient.euclidean.IsCompactSubset D.toStandingParameters (A l) :=
    fun l => (isCompactSubset_euclidean_iff _ _).2 (hc l)
  have hBF := (((hF ⟨1, le_refl (1 : ℝ)⟩ k hk).1 D.toStandingParameters
    LimitSpaces.Ambient.euclidean).2.2 A hAc hd).2.1
  let Ψ : ↥(Set.univ : Set ℕ+) → C1ProductSpace D.toStandingParameters .euclidean A → ℝ :=
    fun j => productForm T D.toStandingParameters A j.1
  have hconv : LimitSpaces.Ambient.ConvergesPointwise Ψ := by
    intro h
    obtain ⟨c, hc'⟩ := hlim ⟨List.ofFn (componentFuns h), isDisjointlySupported_componentFuns hd h⟩
    exact ⟨c, hc'.comp tendsto_comap⟩
  obtain ⟨⟨C, hC⟩, -⟩ := (hBF Set.univ Ψ Set.infinite_univ
    (fun j => productForm_isMultilinearRealForm T hCov hd j.1)
    (fun j => productForm_isBoundedMultilinear T hP hc j.1) hconv).1
  refine ⟨C, fun j f hf hs => ?_⟩
  let h : C1ProductSpace D.toStandingParameters .euclidean A := fun l =>
    ⟨f l, (mem_c1Within_iff _ _ _).2 ⟨isC1c_of_isDisjointlySupported hf l, hs l⟩⟩
  have hb := hC ⟨j, trivial⟩ h
  have hprod : ∏ l, LimitSpaces.Ambient.euclidean.normC1 D.toStandingParameters (h l).1 =
      ∏ l, c1NormR4 (f l) :=
    Finset.prod_congr rfl fun l _ => normC1_euclidean _ _
  exact hb.trans_eq (congrArg (C * ·) hprod)
end Forms
section Bounds
variable {D : AxisMirror.MirrorData} {T : LatticeApproximation D.L}
theorem isBoundedWithConstants_of_isC1ConstantFamily {M : ℝ} (hM : 1 ≤ M)
    {C : ∀ k : ℕ, (Fin k → Set (Fin 4 → ℝ)) → ℝ} (h : T.IsC1ConstantFamily C) :
    T.IsBoundedWithConstants D M C := by
  intro k hk A hc hd j f hf hs
  have hsep := isDisjointlySupported_of_mem_separatedN D hf
  have hs' : ∀ l, tsupport (f l) ⊆ A l := fun l => by
    rw [← closedSupport_euclidean D]
    exact hs l
  refine le_mul_prod_of_le_of_zero (abs_nonneg _) (fun l => c1NormR4_nonneg _)
    (fun l => c1NormR4_le_sharpNormR4 hM (isC1c_of_isDisjointlySupported hsep l)) (fun l h0 => ?_)
    (h k hk A hc hd j f hsep hs')
  have h₁ := sharpNormR4_le_c1NormR4 hM (isC1c_of_isDisjointlySupported hsep l)
  have h₂ := c1NormR4_le_sharpNormR4 hM (isC1c_of_isDisjointlySupported hsep l)
  rw [h0] at h₁ h₂
  exact le_antisymm (by simpa using h₁) h₂
theorem isC1ConstantFamily_of_isBoundedWithConstants {M : ℝ} (hM : 1 ≤ M)
    {C' : ∀ k : ℕ, (Fin k → Set (Fin 4 → ℝ)) → ℝ} (h : T.IsBoundedWithConstants D M C') :
    T.IsC1ConstantFamily fun k A => (80 * M) ^ k * C' k A := by
  intro k hk A hc hd j f hsep hs
  have hb := h k hk A hc hd j f (mem_separatedN_of_isDisjointlySupported D hsep) fun l => by
    rw [closedSupport_euclidean]
    exact hs l
  have hE := isC1c_of_isDisjointlySupported hsep
  have hm := le_mul_prod_of_le_of_zero (b := fun l => 80 * M * c1NormR4 (f l)) (abs_nonneg _)
    (fun l => (c1NormR4_nonneg _).trans (c1NormR4_le_sharpNormR4 hM (hE l)))
    (fun l => sharpNormR4_le_c1NormR4 hM (hE l))
    (fun l h0 => by
      have h₁ := c1NormR4_le_sharpNormR4 hM (hE l)
      rw [h0] at h₁
      rw [le_antisymm h₁ (c1NormR4_nonneg _), mul_zero]) hb
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hm
  calc _ ≤ _ := hm
    _ = _ := by ring
end Bounds
theorem limitsOnTuplesImplyBounded_holds
    (hCov : RepresentativeCovariance.RepresentativesCovariantAndLocal)
    (hF : LimitSpaces.Ambient.uniformBoundednessEquicontinuity)
    (hP : InfiniteLattice.FaceEnergyBoundedAndFacesLocallyFinite) : LimitsOnTuplesImplyBounded := by
  classical
  have hToC1 : ∀ (D : AxisMirror.MirrorData) (T : LatticeApproximation D.L),
      T.IsBoundedForSomeM D → T.HasC1Constants := by
    rintro D T ⟨M, hM, hB⟩
    obtain ⟨C', hC'⟩ := (LatticeApproximation.isUniformlyBounded_iff_exists_constants D T M hM).1 hB
    exact ⟨_, isC1ConstantFamily_of_isBoundedWithConstants hM hC'⟩
  have hFromC1 : ∀ (D : AxisMirror.MirrorData) (T : LatticeApproximation D.L),
      T.HasC1Constants → ∀ (M : ℝ) (hM : 1 ≤ M), T.IsUniformlyBounded D M hM := by
    rintro D T ⟨C, hC⟩ M hM
    exact (LatticeApproximation.isUniformlyBounded_iff_exists_constants D T M hM).2
      ⟨C, isBoundedWithConstants_of_isC1ConstantFamily hM hC⟩
  refine ⟨fun D T hlim => ?_, fun M hM f hf => ⟨c1NormR4_le_sharpNormR4 hM hf,
    sharpNormR4_le_c1NormR4 hM hf⟩, fun D T => ⟨fun M hM => ⟨fun C hC =>
      isBoundedWithConstants_of_isC1ConstantFamily hM hC, fun C' hC' =>
      isC1ConstantFamily_of_isBoundedWithConstants hM hC'⟩, ⟨hToC1 D T, fun h =>
      ⟨1, le_rfl, hFromC1 D T h 1 le_rfl⟩⟩, hFromC1 D T⟩⟩
  have hC1 : T.HasC1Constants := by
    have h := fun (k : ℕ) (hk : 1 ≤ k) (A : Fin k → Set (Fin 4 → ℝ)) (hc : ∀ l, IsCompact (A l))
      (hd : Pairwise (Function.onFun Disjoint A)) =>
        exists_uniform_bound T hCov hF hP hlim hk hc hd
    refine ⟨fun k A => if hA : 1 ≤ k ∧ (∀ l, IsCompact (A l)) ∧
        Pairwise (Function.onFun Disjoint A) then (h k hA.1 A hA.2.1 hA.2.2).choose else 0, ?_⟩
    intro k hk A hc hd j f hf hs
    have hA : 1 ≤ k ∧ (∀ l, IsCompact (A l)) ∧ Pairwise (Function.onFun Disjoint A) :=
      ⟨hk, hc, hd⟩
    simp only [dif_pos hA]
    exact (h k hk A hc hd).choose_spec j f hf hs
  exact ⟨hC1, 1, le_rfl, hFromC1 D T hC1 1 le_rfl⟩
end BoundedOfLimits
end ApproximatingSequences
end ReflectionPositivity
end YangMills.Construction
