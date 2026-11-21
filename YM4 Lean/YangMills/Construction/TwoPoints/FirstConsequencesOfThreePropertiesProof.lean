import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.InfiniteLattice.ExpansionsMeetTheConditionsOfTheReconstructionProof
import YangMills.Construction.InfiniteLattice.ReconstructionAtALatticeMirrorProof
import YangMills.Construction.InfiniteLattice.RulesForObservablesIsometriesAndMirrorsProof
import YangMills.Construction.InfiniteLattice.UnitLatticeIsometriesAndPlaquettesProof
import YangMills.Construction.TwoPoints.ElementaryFactsOfMirrorsAndPlates
import YangMills.Construction.TwoPoints.FirstConsequencesOfThreeProperties
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.TwoPoints.AdmissibleFormConsequences
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
theorem euclidDot_comm (x y : AmbientSpace) : euclidDot x y = euclidDot y x := by apply _root_.YangMills.Construction.LatticeConventions.ObservableRules.euclidDot_comm <;> assumption
theorem euclidDot_add_right (x y z : AmbientSpace) :
    euclidDot x (y + z) = euclidDot x y + euclidDot x z := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.euclidDot_add <;> assumption
theorem euclidDot_smul_right (c : ℝ) (x y : AmbientSpace) :
    euclidDot x (c • y) = c * euclidDot x y := by apply _root_.YangMills.Construction.LatticeConventions.MirrorExpansionsProof.euclidDot_smul_right <;> assumption
theorem euclidDot_self (x : AmbientSpace) : euclidDot x x = euclidNorm x ^ 2 := by
  rw [euclidNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [euclidDot, sq]
theorem euclidNorm_eq_of_euclidDot_self_eq {x y : AmbientSpace}
    (h : euclidDot x x = euclidDot y y) : euclidNorm x = euclidNorm y := by
  have h' : ∑ μ, x μ ^ 2 = ∑ μ, y μ ^ 2 := by simpa [euclidDot, sq] using h
  simp only [euclidNorm, h']
theorem euclidDot_coordVec (x : AmbientSpace) (μ : Fin 4) :
    euclidDot x (coordVec μ) = x μ := by
  simp [euclidDot, PeriodicLattice.coordVec, Pi.single_apply]
theorem norm_le_euclidNorm (x : AmbientSpace) : ‖x‖ ≤ euclidNorm x := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
def PreservesEuclidNorm (A : AmbientSpace →ₗ[ℝ] AmbientSpace) : Prop :=
  ∀ x, euclidNorm (A x) = euclidNorm x
theorem PreservesEuclidNorm.euclidDot {A : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hA : PreservesEuclidNorm A) (x y : AmbientSpace) :
    TwoPoints.euclidDot (A x) (A y) = TwoPoints.euclidDot x y := by
  have h1 : TwoPoints.euclidDot (A (x + y)) (A (x + y)) = TwoPoints.euclidDot (x + y) (x + y) := by
    rw [euclidDot_self, euclidDot_self, hA]
  have h2 : TwoPoints.euclidDot (A x) (A x) = TwoPoints.euclidDot x x := by
    rw [euclidDot_self, euclidDot_self, hA]
  have h3 : TwoPoints.euclidDot (A y) (A y) = TwoPoints.euclidDot y y := by
    rw [euclidDot_self, euclidDot_self, hA]
  rw [map_add] at h1
  simp only [euclidDot_add_right] at h1
  rw [euclidDot_comm (x + y), euclidDot_comm (x + y), euclidDot_comm (A x + A y),
    euclidDot_comm (A x + A y)] at h1
  simp only [euclidDot_add_right] at h1
  rw [euclidDot_comm (A y) (A x), euclidDot_comm y x] at h1
  linarith
theorem PreservesEuclidNorm.measurePreserving {A : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hA : PreservesEuclidNorm A) : MeasurePreserving A volume volume := by
  let li : EuclideanSpace ℝ (Fin 4) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
    { toLinearMap := (WithLp.linearEquiv 2 ℝ AmbientSpace).symm.toLinearMap ∘ₗ A ∘ₗ
        (WithLp.linearEquiv 2 ℝ AmbientSpace).toLinearMap
      norm_map' := by
        intro x
        have h := hA (WithLp.ofLp x)
        simp only [euclidNorm] at h
        simpa [EuclideanSpace.norm_eq, sq_abs] using h }
  have hL := (li.toLinearIsometryEquiv rfl).measurePreserving
  have hc := (PiLp.volume_preserving_ofLp (Fin 4)).comp
    (hL.comp (PiLp.volume_preserving_toLp (Fin 4)))
  exact hc
def IsAffineIsometry (ι : Equiv.Perm AmbientSpace) : Prop :=
  ∃ (A : AmbientSpace →ₗ[ℝ] AmbientSpace) (b : AmbientSpace),
    PreservesEuclidNorm A ∧ ∀ x, ι x = A x + b
namespace IsAffineIsometry
variable {ι : Equiv.Perm AmbientSpace}
theorem continuous (hι : IsAffineIsometry ι) : Continuous ι := by
  obtain ⟨A, b, -, h⟩ := hι
  have : ⇑ι = fun x => A x + b := funext h
  rw [this]
  exact (LinearMap.continuous_of_finiteDimensional A).add continuous_const
theorem contDiff (hι : IsAffineIsometry ι) : ContDiff ℝ 1 ι := by
  obtain ⟨A, b, -, h⟩ := hι
  have : ⇑ι = fun x => A x + b := funext h
  rw [this]
  exact (LinearMap.toContinuousLinearMap A).contDiff.add contDiff_const
theorem inv (hι : IsAffineIsometry ι) : IsAffineIsometry ι⁻¹ := by
  obtain ⟨A, b, hA, h⟩ := hι
  have hinj : Function.Injective A := by
    intro x y hxy
    apply ι.injective
    rw [h, h, hxy]
  let B := LinearEquiv.ofInjectiveEndo A hinj
  have hB : ∀ x, A (B.symm x) = x := fun x => B.apply_symm_apply x
  refine ⟨B.symm.toLinearMap, -(B.symm b), fun x => ?_, fun x => ?_⟩
  · change euclidNorm (B.symm x) = _
    rw [← hA, hB]
  · rw [Equiv.Perm.inv_eq_iff_eq, h]
    simp [hB]
theorem euclidNorm_sub (hι : IsAffineIsometry ι) (x y : AmbientSpace) :
    euclidNorm (ι x - ι y) = euclidNorm (x - y) := by
  obtain ⟨A, b, hA, h⟩ := hι
  rw [h, h, add_sub_add_right_eq_sub, ← map_sub, hA]
def toHomeomorph (hι : IsAffineIsometry ι) : AmbientSpace ≃ₜ AmbientSpace where
  toEquiv := ι
  continuous_toFun := hι.continuous
  continuous_invFun := hι.inv.continuous
theorem measurePreserving (hι : IsAffineIsometry ι) : MeasurePreserving ι volume volume := by
  obtain ⟨A, b, hA, h⟩ := hι
  have : ⇑ι = (fun x => x + b) ∘ A := funext h
  rw [this]
  exact (measurePreserving_add_right volume b).comp hA.measurePreserving
theorem tsupport_comp (hι : IsAffineIsometry ι) (f : AmbientSpace → ℂ) :
    tsupport (f ∘ ι) = ι ⁻¹' tsupport f :=
  tsupport_comp_eq_preimage f hι.toHomeomorph
theorem lebesgueIntegral_comp (hι : IsAffineIsometry ι) (f : AmbientSpace → ℂ) :
    lebesgueIntegral (f ∘ ι) = lebesgueIntegral f :=
  hι.measurePreserving.integral_comp hι.toHomeomorph.measurableEmbedding f
theorem comp_mem {O : Set AmbientSpace} {f : AmbientSpace → ℂ} (hι : IsAffineIsometry ι)
    (hf : f ∈ cc1In O) : f ∘ ι ∈ cc1In (ι ⁻¹' O) := by
  refine ⟨hf.1.comp hι.contDiff, ?_, ?_⟩
  · rw [hι.tsupport_comp]
    exact hι.toHomeomorph.isCompact_preimage.2 hf.2.1
  · rw [hι.tsupport_comp]
    exact preimage_mono hf.2.2
end IsAffineIsometry
theorem isBoundedFun_of_mem {f : AmbientSpace → ℂ} (hf : f ∈ compactC1Complex) :
    TestFunctions.IsBoundedFun f :=
  hf.1.continuous.bounded_above_of_compact_support hf.2.1
theorem isLipschitzFor_of_mem {f : AmbientSpace → ℂ} (hf : f ∈ compactC1Complex) :
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) hf.2.1 hf.1 one_ne_zero
  refine ⟨C, C.2, fun x y => ?_⟩
  calc ‖f x - f y‖ = dist (f x) (f y) := (dist_eq_norm _ _).symm
    _ ≤ C * dist x y := hC.dist_le_mul x y
    _ ≤ C * TestFunctions.euclidDistR4 x y := by
        refine mul_le_mul_of_nonneg_left ?_ C.2
        rw [dist_eq_norm]
        exact norm_le_euclidNorm _
theorem mem_compactC1Complex_of_mem_cc1In {O : Set AmbientSpace} {f : AmbientSpace → ℂ}
    (hf : f ∈ cc1In O) : f ∈ compactC1Complex :=
  ⟨hf.1, hf.2.1, subset_univ _⟩
theorem fixedScale_sharpNorm_nonneg (St : FixedScale) (f : AmbientSpace → ℂ) :
    0 ≤ St.sharpNorm f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem fixedScale_sharpNorm_le (St : FixedScale) {f g : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex)
    (hn : ∀ x, ‖g x‖ ≤ ‖f x‖) (hl : ∀ x y, ‖g x - g y‖ ≤ ‖f x - f y‖) :
    St.sharpNorm g ≤ St.sharpNorm f := by
  have hsup : TestFunctions.uniformNorm g ≤ TestFunctions.uniformNorm f := by
    obtain ⟨C, hC⟩ := isBoundedFun_of_mem hf
    exact ciSup_mono ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩ hn
  have hlip : TestFunctions.lipConstR4 g ≤ TestFunctions.lipConstR4 f := by
    obtain ⟨C, hC0, hC⟩ := isLipschitzFor_of_mem hf
    refine csInf_le_csInf ⟨0, fun _ h => h.1⟩ ⟨C, hC0, hC⟩ ?_
    exact fun D hD => ⟨hD.1, fun x y => (hl x y).trans (hD.2 x y)⟩
  refine max_le_max hsup (mul_le_mul_of_nonneg_left hlip ?_)
  have := St.scale_pos
  positivity
theorem uniformNorm_comp (f : AmbientSpace → ℂ) (ι : Equiv.Perm AmbientSpace) :
    TestFunctions.uniformNorm (f ∘ ι) = TestFunctions.uniformNorm f :=
  Equiv.iSup_comp (g := fun x => ‖f x‖) ι
theorem lipConstR4_comp (f : AmbientSpace → ℂ) {ι : Equiv.Perm AmbientSpace}
    (hι : IsAffineIsometry ι) :
    TestFunctions.lipConstR4 (f ∘ ι) = TestFunctions.lipConstR4 f := by
  have hd : ∀ x y, TestFunctions.euclidDistR4 (ι x) (ι y) = TestFunctions.euclidDistR4 x y :=
    hι.euclidNorm_sub
  unfold TestFunctions.lipConstR4 TestFunctions.bestLipschitzConstant
  congr 1
  ext C
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun x y => ?_⟩
    have := h (ι⁻¹ x) (ι⁻¹ y)
    rw [← hd (ι⁻¹ x) (ι⁻¹ y)] at this
    simpa using this
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun x y => ?_⟩
    rw [← hd x y]
    exact h (ι x) (ι y)
theorem preservesNormsAndBallSupport_comp (St : FixedScale) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) {ι : Equiv.Perm AmbientSpace} (hι : IsAffineIsometry ι) :
    PreservesNormsAndBallSupport St f (f ∘ ι) := by
  have hmem : f ∘ ι ∈ compactC1Complex := mem_compactC1Complex_of_mem_cc1In (hι.comp_mem hf)
  have hsup := uniformNorm_comp f ι
  have hlip := lipConstR4_comp f hι
  refine ⟨hmem, hsup, hlip, ?_, ?_⟩
  · simp only [FixedScale.sharpNorm, TestFunctions.sharpNormR4, hsup, hlip]
  · intro x R _ hs
    refine ⟨ι⁻¹ x, ?_⟩
    rw [hι.tsupport_comp]
    intro y hy
    have h1 := hs hy
    have h2 := hι.euclidNorm_sub y (ι⁻¹ x)
    simp only [euclidClosedBall, mem_ofPred_eq] at h1 ⊢
    rw [← h2]
    simpa using h1
theorem tsupport_conjFun (f : AmbientSpace → ℂ) : tsupport (conjFun f) = tsupport f := by
  have : Function.support (conjFun f) = Function.support f := by
    ext x
    simp [conjFun]
  simp only [tsupport, this]
theorem conjFun_mem {O : Set AmbientSpace} {f : AmbientSpace → ℂ} (hf : f ∈ cc1In O) :
    conjFun f ∈ cc1In O := by
  refine ⟨Complex.conjCLE.toContinuousLinearMap.contDiff.comp hf.1, ?_, ?_⟩
  · rw [tsupport_conjFun]
    exact hf.2.1
  · rw [tsupport_conjFun]
    exact hf.2.2
theorem preservesNormsAndBallSupport_conjFun (St : FixedScale) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) : PreservesNormsAndBallSupport St f (conjFun f) := by
  have hn : ∀ x, ‖conjFun f x‖ = ‖f x‖ := fun x => by simp [conjFun]
  have hd : ∀ x y, ‖conjFun f x - conjFun f y‖ = ‖f x - f y‖ := fun x y => by
    simp only [conjFun]
    rw [← map_sub, RCLike.norm_conj]
  have hsup : TestFunctions.uniformNorm (conjFun f) = TestFunctions.uniformNorm f := by
    simp only [TestFunctions.uniformNorm, hn]
  have hlip : TestFunctions.lipConstR4 (conjFun f) = TestFunctions.lipConstR4 f := by
    simp only [TestFunctions.lipConstR4, TestFunctions.bestLipschitzConstant, hd]
  refine ⟨conjFun_mem hf, hsup, hlip, ?_, ?_⟩
  · simp only [FixedScale.sharpNorm, TestFunctions.sharpNormR4, hsup, hlip]
  · intro x R _ hs
    exact ⟨x, by rwa [tsupport_conjFun]⟩
theorem lebesgueIntegral_conjFun (f : AmbientSpace → ℂ) :
    lebesgueIntegral (conjFun f) = (starRingEnd ℂ) (lebesgueIntegral f) :=
  _root_.integral_conj
theorem tsupport_realPartFun_subset (f : AmbientSpace → ℂ) :
    tsupport (realPartFun f) ⊆ tsupport f := by
  refine closure_mono fun x hx => ?_
  intro h0
  apply hx
  simp [realPartFun, h0]
theorem tsupport_imagPartFun_subset (f : AmbientSpace → ℂ) :
    tsupport (imagPartFun f) ⊆ tsupport f := by
  refine closure_mono fun x hx => ?_
  intro h0
  apply hx
  simp [imagPartFun, h0]
theorem realPartFun_mem {f : AmbientSpace → ℂ} (hf : f ∈ compactC1Complex) :
    realPartFun f ∈ compactC1Real := by
  refine ⟨⟨?_, hf.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_realPartFun_subset f),
    subset_univ _⟩, fun x => Complex.ofReal_im _⟩
  exact Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hf.1)
theorem imagPartFun_mem {f : AmbientSpace → ℂ} (hf : f ∈ compactC1Complex) :
    imagPartFun f ∈ compactC1Real := by
  refine ⟨⟨?_, hf.2.1.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_imagPartFun_subset f), subset_univ _⟩, fun x => Complex.ofReal_im _⟩
  exact Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp hf.1)
theorem sharpNorm_realPartFun_le (St : FixedScale) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) : St.sharpNorm (realPartFun f) ≤ St.sharpNorm f := by
  refine fixedScale_sharpNorm_le St hf (fun x => ?_) fun x y => ?_
  · simpa [realPartFun] using Complex.abs_re_le_norm (f x)
  · have h := Complex.abs_re_le_norm (f x - f y)
    have e : realPartFun f x - realPartFun f y = (((f x - f y).re : ℝ) : ℂ) := by
      simp [realPartFun]
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact h
theorem sharpNorm_imagPartFun_le (St : FixedScale) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) : St.sharpNorm (imagPartFun f) ≤ St.sharpNorm f := by
  refine fixedScale_sharpNorm_le St hf (fun x => ?_) fun x y => ?_
  · simpa [imagPartFun] using Complex.abs_im_le_norm (f x)
  · have h := Complex.abs_im_le_norm (f x - f y)
    have e : imagPartFun f x - imagPartFun f y = (((f x - f y).im : ℝ) : ℂ) := by
      simp [imagPartFun]
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact h
theorem reImPartsControlled_holds (St : FixedScale) : ReImPartsControlled St := by
  intro f' f'' h' h'' hf
  have e1 := realPartFun_add_I_smul h' h''
  have e2 := imagPartFun_add_I_smul h' h''
  refine ⟨e1 ▸ realPartFun_mem hf, e2 ▸ imagPartFun_mem hf, ?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [← e1]
    exact tsupport_realPartFun_subset _
  · conv_lhs => rw [← e2]
    exact tsupport_imagPartFun_subset _
  · conv_lhs => rw [← e1]
    exact sharpNorm_realPartFun_le St hf
  · conv_lhs => rw [← e2]
    exact sharpNorm_imagPartFun_le St hf
section RealForm
variable {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
theorem form_add_left (hS : IsDisjointForm S) {a b h : AmbientSpace → ℂ} (ha : a ∈ compactC1Real)
    (hb : b ∈ compactC1Real) (hh : h ∈ compactC1Real) (d₁ : DisjointSupports a h)
    (d₂ : DisjointSupports b h) : S (a + b) h = S a h + S b h := by
  simpa using hS.2 1 1 a ha b hb h hh d₁ d₂
theorem form_smul_left (hS : IsDisjointForm S) (c : ℝ) {a h : AmbientSpace → ℂ}
    (ha : a ∈ compactC1Real) (hh : h ∈ compactC1Real) (d : DisjointSupports a h) :
    S (c • a) h = c * S a h := by
  simpa using hS.2 c 0 a ha a ha h hh d d
theorem disjointSupports_symm {a b : AmbientSpace → ℂ} (d : DisjointSupports a b) :
    DisjointSupports b a :=
  Disjoint.symm d
theorem disjointSupports_smul (c : ℝ) {a h : AmbientSpace → ℂ} (d : DisjointSupports a h) :
    DisjointSupports (c • a) h :=
  Disjoint.mono_left (closure_mono (Function.support_const_smul_subset c a)) d
theorem form_smul_right (hS : IsDisjointForm S) (c : ℝ) {a h : AmbientSpace → ℂ}
    (ha : a ∈ compactC1Real) (hh : h ∈ compactC1Real) (d : DisjointSupports a h) :
    S a (c • h) = c * S a h := by
  have ds := disjointSupports_symm d
  rw [← hS.1 _ (compactC1Real.smul_mem c hh) _ ha (disjointSupports_smul c ds),
    form_smul_left hS c hh ha ds, hS.1 _ hh _ ha ds]
end RealForm
theorem complexifyDefinedAt_of_pair {f h : AmbientSpace → ℂ} (hp : IsDisjointSupportPair f h) :
    ComplexifyDefinedAt f h := by
  obtain ⟨hf, hh, d⟩ := hp
  exact ⟨realPartFun_mem hf, imagPartFun_mem hf, realPartFun_mem hh, imagPartFun_mem hh,
    Disjoint.mono (tsupport_realPartFun_subset f) (tsupport_realPartFun_subset h) d,
    Disjoint.mono (tsupport_imagPartFun_subset f) (tsupport_imagPartFun_subset h) d,
    Disjoint.mono (tsupport_realPartFun_subset f) (tsupport_imagPartFun_subset h) d,
    Disjoint.mono (tsupport_imagPartFun_subset f) (tsupport_realPartFun_subset h) d⟩
theorem tsupport_add_subset_union (f g : AmbientSpace → ℂ) :
    tsupport (f + g) ⊆ tsupport f ∪ tsupport g := by
  simp only [tsupport]
  rw [← closure_union]
  exact closure_mono (Function.support_add f g)
theorem isDisjointSupportPair_add {f₁ f₂ h : AmbientSpace → ℂ}
    (h₁ : IsDisjointSupportPair f₁ h) (h₂ : IsDisjointSupportPair f₂ h) :
    IsDisjointSupportPair (f₁ + f₂) h :=
  ⟨compactC1Complex.add_mem h₁.1 h₂.1, h₁.2.1,
    Disjoint.mono_left (tsupport_add_subset_union f₁ f₂) (disjoint_union_left.2 ⟨h₁.2.2, h₂.2.2⟩)⟩
theorem isDisjointSupportPair_smul (a : ℂ) {f h : AmbientSpace → ℂ}
    (hp : IsDisjointSupportPair f h) : IsDisjointSupportPair (a • f) h :=
  ⟨compactC1Complex.smul_mem a hp.1, hp.2.1,
    Disjoint.mono_left (closure_mono (Function.support_const_smul_subset a f)) hp.2.2⟩
theorem realPartFun_add (f g : AmbientSpace → ℂ) :
    realPartFun (f + g) = realPartFun f + realPartFun g := by
  funext x
  simp [realPartFun]
theorem imagPartFun_add (f g : AmbientSpace → ℂ) :
    imagPartFun (f + g) = imagPartFun f + imagPartFun g := by
  funext x
  simp [imagPartFun]
theorem realPartFun_smul (c : ℝ) (f : AmbientSpace → ℂ) :
    realPartFun (c • f) = c • realPartFun f := by
  funext x
  simp [realPartFun]
theorem imagPartFun_smul (c : ℝ) (f : AmbientSpace → ℂ) :
    imagPartFun (c • f) = c • imagPartFun f := by
  funext x
  simp [imagPartFun]
theorem realPartFun_I_smul (f : AmbientSpace → ℂ) :
    realPartFun (Complex.I • f) = (-1 : ℝ) • imagPartFun f := by
  funext x
  simp [realPartFun, imagPartFun]
theorem imagPartFun_I_smul (f : AmbientSpace → ℂ) :
    imagPartFun (Complex.I • f) = realPartFun f := by
  funext x
  simp [realPartFun, imagPartFun]
theorem realPartFun_conjFun (f : AmbientSpace → ℂ) : realPartFun (conjFun f) = realPartFun f := by
  funext x
  simp [realPartFun, conjFun]
theorem imagPartFun_conjFun (f : AmbientSpace → ℂ) :
    imagPartFun (conjFun f) = (-1 : ℝ) • imagPartFun f := by
  funext x
  simp [imagPartFun, conjFun]
section Complexification
variable {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
theorem complexifyForm_symm (hS : IsDisjointForm S) {f h : AmbientSpace → ℂ}
    (hp : IsDisjointSupportPair f h) : complexifyForm S f h = complexifyForm S h f := by
  obtain ⟨a, b, c, d, e₁, e₂, e₃, e₄⟩ := complexifyDefinedAt_of_pair hp
  unfold complexifyForm
  rw [hS.1 _ a _ c e₁, hS.1 _ b _ d e₂, hS.1 _ a _ d e₃, hS.1 _ b _ c e₄]
  push_cast
  ring
theorem complexifyForm_add (hS : IsDisjointForm S) {f₁ f₂ h : AmbientSpace → ℂ}
    (h₁ : IsDisjointSupportPair f₁ h) (h₂ : IsDisjointSupportPair f₂ h) :
    complexifyForm S (f₁ + f₂) h = complexifyForm S f₁ h + complexifyForm S f₂ h := by
  obtain ⟨a₁, b₁, c, d, e₁, e₂, e₃, e₄⟩ := complexifyDefinedAt_of_pair h₁
  obtain ⟨a₂, b₂, -, -, g₁, g₂, g₃, g₄⟩ := complexifyDefinedAt_of_pair h₂
  unfold complexifyForm
  rw [realPartFun_add, imagPartFun_add, form_add_left hS a₁ a₂ c e₁ g₁,
    form_add_left hS b₁ b₂ d e₂ g₂, form_add_left hS a₁ a₂ d e₃ g₃,
    form_add_left hS b₁ b₂ c e₄ g₄]
  push_cast
  ring
theorem complexifyForm_real_smul (hS : IsDisjointForm S) (r : ℝ) {f h : AmbientSpace → ℂ}
    (hp : IsDisjointSupportPair f h) :
    complexifyForm S (r • f) h = r * complexifyForm S f h := by
  obtain ⟨a, b, c, d, e₁, e₂, e₃, e₄⟩ := complexifyDefinedAt_of_pair hp
  unfold complexifyForm
  rw [realPartFun_smul, imagPartFun_smul, form_smul_left hS r a c e₁, form_smul_left hS r b d e₂,
    form_smul_left hS r a d e₃, form_smul_left hS r b c e₄]
  push_cast
  ring
theorem complexifyForm_I_smul (hS : IsDisjointForm S) {f h : AmbientSpace → ℂ}
    (hp : IsDisjointSupportPair f h) :
    complexifyForm S (Complex.I • f) h = Complex.I * complexifyForm S f h := by
  obtain ⟨a, b, c, d, e₁, e₂, e₃, e₄⟩ := complexifyDefinedAt_of_pair hp
  unfold complexifyForm
  rw [realPartFun_I_smul, imagPartFun_I_smul, form_smul_left hS (-1) b c e₄,
    form_smul_left hS (-1) b d e₂]
  apply Complex.ext <;> simp <;> ring
theorem complexifyForm_smul (hS : IsDisjointForm S) (a : ℂ) {f h : AmbientSpace → ℂ}
    (hp : IsDisjointSupportPair f h) :
    complexifyForm S (a • f) h = a * complexifyForm S f h := by
  have e : a • f = a.re • f + a.im • (Complex.I • f) := by
    funext x
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im a]
    ring
  have hre : a.re • f = ((a.re : ℂ)) • f := by
    funext x
    simp
  have him : a.im • (Complex.I • f) = ((a.im : ℂ)) • (Complex.I • f) := by
    funext x
    simp
  have hI := isDisjointSupportPair_smul Complex.I hp
  rw [e, complexifyForm_add hS (by rw [hre]; exact isDisjointSupportPair_smul _ hp)
    (by rw [him]; exact isDisjointSupportPair_smul _ hI), complexifyForm_real_smul hS _ hp,
    complexifyForm_real_smul hS _ hI, complexifyForm_I_smul hS hp]
  conv_rhs => rw [← Complex.re_add_im a]
  ring
theorem complexifyLinear_holds (hS : IsDisjointForm S) : ComplexifyLinear S := by
  intro a₁ a₂ f₁ f₂ h h₁ h₂
  have p₁ := isDisjointSupportPair_smul a₁ h₁
  have p₂ := isDisjointSupportPair_smul a₂ h₂
  have p := isDisjointSupportPair_add p₁ p₂
  have hl : complexifyForm S (a₁ • f₁ + a₂ • f₂) h =
      a₁ * complexifyForm S f₁ h + a₂ * complexifyForm S f₂ h := by
    rw [complexifyForm_add hS p₁ p₂, complexifyForm_smul hS a₁ h₁, complexifyForm_smul hS a₂ h₂]
  refine ⟨p, hl, ?_⟩
  rw [← complexifyForm_symm hS p, hl, complexifyForm_symm hS h₁, complexifyForm_symm hS h₂]
theorem complexifyConjCommute_holds (hS : IsDisjointForm S) : ComplexifyConjCommute S := by
  intro f h hp
  have hf := hp.1
  have hh := hp.2.1
  refine ⟨⟨conjFun_mem hf, conjFun_mem hh, ?_⟩, ?_⟩
  · unfold DisjointSupports
    rw [tsupport_conjFun, tsupport_conjFun]
    exact hp.2.2
  · obtain ⟨a, b, c, d, e₁, e₂, e₃, e₄⟩ := complexifyDefinedAt_of_pair hp
    unfold complexifyForm
    rw [realPartFun_conjFun, realPartFun_conjFun, imagPartFun_conjFun,
      imagPartFun_conjFun, form_smul_left hS (-1) b (compactC1Real.smul_mem (-1) d)
        (disjointSupports_symm (disjointSupports_smul (-1) (disjointSupports_symm e₂))),
      form_smul_right hS (-1) b d e₂, form_smul_right hS (-1) a d e₃,
      form_smul_left hS (-1) b c e₄]
    (apply Complex.ext <;> simp); ring
theorem complexifyBallBound_holds {St : FixedScale} {C₂ : ℝ → ℝ → ℝ}
    (hC : IsBallDecayBound St S C₂) : ComplexifyBallBound St S C₂ := by
  intro d R hd hR x x' f hf h hh hfx hhx hdist
  have key : ∀ a b : AmbientSpace → ℂ, a ∈ compactC1Real → b ∈ compactC1Real →
      tsupport a ⊆ tsupport f → tsupport b ⊆ tsupport h → St.sharpNorm a ≤ St.sharpNorm f →
      St.sharpNorm b ≤ St.sharpNorm h →
      |S a b| ≤ C₂ d R * St.sharpNorm f * St.sharpNorm h := by
    intro a b ha hb sa sb na nb
    refine (hC.2.2 d R hd hR x x' a ha b hb (sa.trans hfx) (sb.trans hhx)
      fun y hy y' hy' => hdist y (sa hy) y' (sb hy')).trans ?_
    have h0 := hC.1 d R hd hR
    exact mul_le_mul (mul_le_mul_of_nonneg_left na h0) nb (fixedScale_sharpNorm_nonneg St b)
      (mul_nonneg h0 (fixedScale_sharpNorm_nonneg St f))
  have k₁ := key _ _ (realPartFun_mem hf) (realPartFun_mem hh) (tsupport_realPartFun_subset f)
    (tsupport_realPartFun_subset h) (sharpNorm_realPartFun_le St hf)
    (sharpNorm_realPartFun_le St hh)
  have k₂ := key _ _ (imagPartFun_mem hf) (imagPartFun_mem hh)
    (tsupport_imagPartFun_subset f) (tsupport_imagPartFun_subset h)
    (sharpNorm_imagPartFun_le St hf) (sharpNorm_imagPartFun_le St hh)
  have k₃ := key _ _ (realPartFun_mem hf) (imagPartFun_mem hh) (tsupport_realPartFun_subset f)
    (tsupport_imagPartFun_subset h) (sharpNorm_realPartFun_le St hf)
    (sharpNorm_imagPartFun_le St hh)
  have k₄ := key _ _ (imagPartFun_mem hf) (realPartFun_mem hh)
    (tsupport_imagPartFun_subset f) (tsupport_realPartFun_subset h)
    (sharpNorm_imagPartFun_le St hf) (sharpNorm_realPartFun_le St hh)
  unfold complexifyForm
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have t₁ := abs_sub (S (realPartFun f) (realPartFun h)) (S (imagPartFun f) (imagPartFun h))
  have t₂ := abs_add_le (S (realPartFun f) (imagPartFun h))
    (S (imagPartFun f) (realPartFun h))
  linarith
end Complexification
theorem reflectAcross_eq (n x : AmbientSpace) :
    reflectAcross n x = x + (-(2 * euclidDot n x)) • n := by
  simp [reflectAcross, sub_eq_add_neg]
def reflectLinear (n : AmbientSpace) : AmbientSpace →ₗ[ℝ] AmbientSpace where
  toFun := reflectAcross n
  map_add' x y := by
    simp only [reflectAcross, euclidDot_add_right]
    module
  map_smul' c x := by
    simp only [reflectAcross, euclidDot_smul_right, RingHom.id_apply]
    module
theorem euclidDot_self_of_unit {n : AmbientSpace} (hn : euclidNorm n = 1) :
    euclidDot n n = 1 := by
  rw [euclidDot_self, hn]
  norm_num
theorem euclidDot_reflectAcross {n : AmbientSpace} (hn : euclidNorm n = 1) (x : AmbientSpace) :
    euclidDot n (reflectAcross n x) = -euclidDot n x := by
  rw [reflectAcross_eq, euclidDot_add_right, euclidDot_smul_right, euclidDot_self_of_unit hn]
  ring
theorem reflectAcross_reflectAcross {n : AmbientSpace} (hn : euclidNorm n = 1)
    (x : AmbientSpace) : reflectAcross n (reflectAcross n x) = x := by
  rw [reflectAcross_eq n (reflectAcross n x), euclidDot_reflectAcross hn, reflectAcross_eq n x]
  module
theorem reflectLinear_preserves {n : AmbientSpace} (hn : euclidNorm n = 1) :
    PreservesEuclidNorm (reflectLinear n) := by
  intro x
  apply euclidNorm_eq_of_euclidDot_self_eq
  change euclidDot (reflectAcross n x) (reflectAcross n x) = _
  have h1 : euclidDot (reflectAcross n x) n = -euclidDot n x := by
    rw [euclidDot_comm]
    exact euclidDot_reflectAcross hn x
  have h2 : euclidDot x (reflectAcross n x) =
      euclidDot x x + (-(2 * euclidDot n x)) * euclidDot n x := by
    rw [reflectAcross_eq, euclidDot_add_right, euclidDot_smul_right, euclidDot_comm x n]
  calc euclidDot (reflectAcross n x) (reflectAcross n x)
      = euclidDot (reflectAcross n x) (x + (-(2 * euclidDot n x)) • n) :=
        congrArg _ (reflectAcross_eq n x)
    _ = euclidDot (reflectAcross n x) x +
        (-(2 * euclidDot n x)) * euclidDot (reflectAcross n x) n := by
        rw [euclidDot_add_right, euclidDot_smul_right]
    _ = euclidDot x x := by
        rw [euclidDot_comm (reflectAcross n x) x, h2, h1]
        ring
def reflectPerm (n : AmbientSpace) (hn : euclidNorm n = 1) : Equiv.Perm AmbientSpace :=
  Function.Involutive.toPerm (reflectAcross n) (reflectAcross_reflectAcross hn)
theorem isAffineIsometry_reflectPerm (n : AmbientSpace) (hn : euclidNorm n = 1) :
    IsAffineIsometry (reflectPerm n hn) :=
  ⟨reflectLinear n, 0, reflectLinear_preserves hn, fun _ => (add_zero _).symm⟩
theorem isAffineIsometry_subRight (v : AmbientSpace) : IsAffineIsometry (Equiv.subRight v) :=
  ⟨LinearMap.id, -v, fun _ => rfl, fun x => by simp [sub_eq_add_neg]⟩
theorem exists_linear_of_mem_hyperoctahedralPerms {w : Equiv.Perm AmbientSpace}
    (hw : w ∈ hyperoctahedralPerms) :
    ∃ l : AmbientSpace →ₗ[ℝ] AmbientSpace, ⇑l = ⇑w ∧ PreservesEuclidNorm l := by
  obtain ⟨π, s, rfl⟩ := hw
  refine ⟨signedPermLinear π s, rfl, fun x => euclidNorm_eq_of_euclidDot_self_eq ?_⟩
  change ∑ μ, (((s μ : ℤˣ) : ℤ) : ℝ) * x (π μ) * ((((s μ : ℤˣ) : ℤ) : ℝ) * x (π μ)) =
    ∑ μ, x μ * x μ
  rw [← Equiv.sum_comp π (fun μ => x μ * x μ)]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h : (((s μ : ℤˣ) : ℤ) : ℝ) * (((s μ : ℤˣ) : ℤ) : ℝ) = 1 := by
    rcases Int.units_eq_one_or (s μ) with h | h <;> simp [h]
  linear_combination (x (π μ)) ^ 2 * h
theorem isAffineIsometry_of_mem_hyperoctahedralPerms {w : Equiv.Perm AmbientSpace}
    (hw : w ∈ hyperoctahedralPerms) : IsAffineIsometry w := by
  obtain ⟨l, hl, hk⟩ := exists_linear_of_mem_hyperoctahedralPerms hw
  exact ⟨l, 0, hk, fun x => by rw [add_zero, congrFun hl x]⟩
theorem isAffineIsometry_of_mem_euclideanMotions {r : Equiv.Perm AmbientSpace}
    (hr : r ∈ euclideanMotions) : IsAffineIsometry r := by
  obtain ⟨w, hw, v, h⟩ := hr
  obtain ⟨l, hl, hk⟩ := exists_linear_of_mem_hyperoctahedralPerms hw
  exact ⟨l, v, hk, fun x => by rw [h x, congrFun hl x]⟩
theorem mem_euclideanMotions_of_mem_hyperoctahedralPerms {w : Equiv.Perm AmbientSpace}
    (hw : w ∈ hyperoctahedralPerms) : w ∈ euclideanMotions :=
  ⟨w, hw, 0, fun _ => (add_zero _).symm⟩
theorem isIsometricInvolutiveReflection_holds {n : AmbientSpace} (hn : euclidNorm n = 1) :
    IsIsometricInvolutiveReflection n := by
  have hsub : ∀ x y, reflectAcross n (x - y) = reflectAcross n x - reflectAcross n y :=
    fun x y => map_sub (reflectLinear n) x y
  have comm : ∀ (E : Type) (f : AmbientSpace → E) (v : AmbientSpace),
      reflectFun n (translateFun v f) = translateFun (reflectAcross n v) (reflectFun n f) := by
    intro E f v
    funext x
    simp only [reflectFun, translateFun, Function.comp, hsub, reflectAcross_reflectAcross hn]
  refine ⟨⟨reflectLinear n, rfl, reflectLinear_preserves hn⟩,
    funext (reflectAcross_reflectAcross hn),
    euclidDot_reflectAcross hn, fun E f v s => ⟨comm E f v, ?_, fun hv => ?_⟩⟩
  · rw [comm]
    have : reflectAcross n (s • n) = (-s) • n := by
      rw [reflectAcross_eq, euclidDot_smul_right, euclidDot_self_of_unit hn]
      module
    rw [this]
  · rw [comm]
    have : reflectAcross n v = v := by
      rw [reflectAcross_eq, euclidDot_comm, hv]
      simp
    rw [this]
theorem symmetriesPreserve_holds (St : FixedScale) {f : AmbientSpace → ℂ}
    (hf : f ∈ compactC1Complex) : SymmetriesPreserve St f := by
  refine ⟨fun v => ?_, fun n hn => ?_, fun w hw => ?_, preservesNormsAndBallSupport_conjFun St hf,
    lebesgueIntegral_conjFun f, tsupport_conjFun f⟩
  · have hι := isAffineIsometry_subRight v
    have e : translateFun v f = f ∘ ⇑(Equiv.subRight v) := rfl
    rw [e]
    refine ⟨preservesNormsAndBallSupport_comp St hf hι, hι.lebesgueIntegral_comp f, ?_⟩
    rw [hι.tsupport_comp]
    ext x
    constructor
    · intro h
      exact ⟨x - v, h, v, mem_singleton v, by simp⟩
    · rintro ⟨y, hy, y', hy', rfl⟩
      rw [mem_singleton_iff] at hy'
      subst hy'
      simpa using hy
  · have hι := isAffineIsometry_reflectPerm n hn
    have e : reflectFun n f = f ∘ ⇑(reflectPerm n hn) := rfl
    rw [e]
    refine ⟨preservesNormsAndBallSupport_comp St hf hι, hι.lebesgueIntegral_comp f, ?_⟩
    rw [hι.tsupport_comp]
    ext x
    constructor
    · intro h
      exact ⟨reflectAcross n x, h, reflectAcross_reflectAcross hn x⟩
    · rintro ⟨y, hy, rfl⟩
      change reflectAcross n (reflectAcross n y) ∈ tsupport f
      rwa [reflectAcross_reflectAcross hn]
  · have hι := (isAffineIsometry_of_mem_hyperoctahedralPerms hw).inv
    have e : actOn w f = f ∘ ⇑w⁻¹ := rfl
    rw [e]
    refine ⟨preservesNormsAndBallSupport_comp St hf hι, hι.lebesgueIntegral_comp f, ?_⟩
    rw [hι.tsupport_comp]
    ext x
    constructor
    · intro h
      exact ⟨w⁻¹ x, h, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
theorem complexifyInvariant_holds {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    (hP : TimeReflectionInvariantPositive S) : ComplexifyInvariant S := by
  intro r hr f h hp
  have hι := (isAffineIsometry_of_mem_euclideanMotions hr).inv
  have pair : IsDisjointSupportPair (actOn r f) (actOn r h) := by
    refine ⟨mem_compactC1Complex_of_mem_cc1In (hι.comp_mem hp.1),
      mem_compactC1Complex_of_mem_cc1In (hι.comp_mem hp.2.1), ?_⟩
    unfold DisjointSupports actOn
    rw [hι.tsupport_comp, hι.tsupport_comp]
    exact hp.2.2.preimage _
  refine ⟨pair, ?_⟩
  obtain ⟨a, b, c, d, e₁, e₂, e₃, e₄⟩ := complexifyDefinedAt_of_pair hp
  have i := hP.1 r hr
  have er : ∀ g : AmbientSpace → ℂ, realPartFun (actOn r g) = actOn r (realPartFun g) :=
    fun _ => rfl
  have ei : ∀ g : AmbientSpace → ℂ, imagPartFun (actOn r g) = actOn r (imagPartFun g) :=
    fun _ => rfl
  unfold complexifyForm
  rw [er, er, ei, ei, i _ a _ c e₁, i _ b _ d e₂, i _ a _ d e₃, i _ b _ c e₄]
theorem reflectAcross_coordVec (n : AmbientSpace) (κ : Fin 4) :
    reflectAcross n (coordVec κ) = coordVec κ - (2 * n κ) • n := by
  rw [reflectAcross, euclidDot_coordVec]
theorem exists_intUnit_cast_eq {ε : ℝ} (h : ε = 1 ∨ ε = -1) : ∃ u : ℤˣ, ((u : ℤ) : ℝ) = ε := by
  rcases h with rfl | rfl
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp⟩
theorem sign_mul_self_eq_one {ε : ℝ} (h : ε = 1 ∨ ε = -1) : ε * ε = 1 := by
  rcases h with rfl | rfl <;> norm_num
theorem isSignedPerm_reflect_axis (μ : Fin 4) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    IsSignedPerm (reflectLinear (ε • coordVec μ)) := by
  refine ⟨1, fun κ => if κ = μ then -1 else 1, fun κ => ?_⟩
  change reflectAcross _ (coordVec κ) = _
  rw [reflectAcross_coordVec]
  by_cases h : κ = μ
  · subst h
    have e : (ε • coordVec κ) κ = ε := by
      simp [PeriodicLattice.coordVec]
    have e' : coordVec κ - (2 * ε) • ε • coordVec κ =
        (1 - 2 * (ε * ε)) • coordVec κ := by module
    rw [e, e', sign_mul_self_eq_one hε]
    norm_num
  · have e : (ε • coordVec μ) κ = 0 := by
      simp [PeriodicLattice.coordVec, h]
    rw [e]
    simp [h]
theorem reflectAcross_diagonal (v x : AmbientSpace) :
    reflectAcross ((Real.sqrt 2)⁻¹ • v) x = x - euclidDot v x • v := by
  have hs : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [reflectAcross, euclidDot_comm, euclidDot_smul_right, euclidDot_comm x v, smul_smul]
  congr 2
  linear_combination 2 * euclidDot v x * hs
theorem isSignedPerm_reflect_diagonal {μ ν : Fin 4} (hμν : μ < ν) {ε ε' : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hε' : ε' = 1 ∨ ε' = -1) :
    IsSignedPerm (reflectLinear
      ((Real.sqrt 2)⁻¹ • (ε • coordVec μ + ε' • coordVec ν))) := by
  obtain ⟨u, hu⟩ := exists_intUnit_cast_eq hε
  obtain ⟨u', hu'⟩ := exists_intUnit_cast_eq hε'
  have hne : μ ≠ ν := hμν.ne
  refine ⟨Equiv.swap μ ν, fun κ => if κ = μ ∨ κ = ν then -(u * u') else 1, fun κ => ?_⟩
  change reflectAcross _ (coordVec κ) = _
  rw [reflectAcross_diagonal, euclidDot_coordVec]
  by_cases h₁ : κ = μ
  · subst h₁
    have e : (ε • coordVec κ + ε' • coordVec ν) κ = ε := by
      simp [PeriodicLattice.coordVec, hne]
    have e' : coordVec κ - ε • (ε • coordVec κ + ε' • coordVec ν) =
        (1 - ε * ε) • coordVec κ + (-(ε * ε')) • coordVec ν := by module
    rw [e, e', sign_mul_self_eq_one hε]
    simp [hu, hu']
  · by_cases h₂ : κ = ν
    · subst h₂
      have e : (ε • coordVec μ + ε' • coordVec κ) κ = ε' := by
        simp [PeriodicLattice.coordVec, hne.symm]
      have e' : coordVec κ - ε' • (ε • coordVec μ + ε' • coordVec κ) =
          (1 - ε' * ε') • coordVec κ + (-(ε * ε')) • coordVec μ := by module
      rw [e, e', sign_mul_self_eq_one hε']
      simp [hu, hu']
    · have e : (ε • coordVec μ + ε' • coordVec ν) κ = 0 := by
        simp [PeriodicLattice.coordVec, h₁, h₂]
      rw [e]
      simp [h₁, h₂, Equiv.swap_apply_of_ne_of_ne h₁ h₂]
theorem reflectionsLieInSymmetryGroups_holds : ReflectionsLieInSymmetryGroups := by
  intro n hn
  have hs : IsSignedPerm (reflectLinear n) := by
    rcases hn with ⟨μ, ε, hε, rfl⟩ | ⟨μ, ν, ε, ε', hμν, hε, hε', rfl⟩
    · exact isSignedPerm_reflect_axis μ hε
    · exact isSignedPerm_reflect_diagonal hμν hε hε'
  obtain ⟨w, hw, he⟩ := exists_mem_hyperoctahedralPerms hs
  refine ⟨⟨w, hw, he⟩, fun hp => ⟨w, ⟨hw, ?_, ?_⟩, he⟩⟩
  · have h1 : n 1 = 0 := congrFun hp.2 0
    rw [congrFun he]
    change reflectAcross n _ = _
    rw [reflectAcross_coordVec, h1]
    simp
  · have h2 : n 2 = 0 := congrFun hp.2 1
    rw [congrFun he]
    change reflectAcross n _ = _
    rw [reflectAcross_coordVec, h2]
    simp
def IsReflectionPositiveAt (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (n : AmbientSpace) : Prop :=
  ∀ g ∈ cc1In (posHalfSpace n),
    IsRealNonneg (complexifyForm S (reflectFun n (conjFun g)) g)
theorem isDisjointSupportPair_reflectFun {n : AmbientSpace} (hn : euclidNorm n = 1)
    {f : AmbientSpace → ℂ} (hf : f ∈ cc1In (posHalfSpace n)) :
    IsDisjointSupportPair (reflectFun n (conjFun f)) f := by
  have hι := isAffineIsometry_reflectPerm n hn
  have hc := mem_compactC1Complex_of_mem_cc1In (conjFun_mem hf)
  refine ⟨mem_compactC1Complex_of_mem_cc1In (hι.comp_mem hc),
    mem_compactC1Complex_of_mem_cc1In hf, ?_⟩
  have e : reflectFun n (conjFun f) = conjFun f ∘ ⇑(reflectPerm n hn) := rfl
  unfold DisjointSupports
  rw [e, hι.tsupport_comp, tsupport_conjFun, Set.disjoint_left]
  intro x hx hx'
  have h1 : 0 < euclidDot n (reflectAcross n x) := hf.2.2 hx
  have h2 : 0 < euclidDot n x := hf.2.2 hx'
  rw [euclidDot_reflectAcross hn] at h1
  linarith
theorem reflectionPositiveAt_map {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    (hInv : ComplexifyInvariant S) {n : AmbientSpace} (hn : euclidNorm n = 1)
    {w : Equiv.Perm AmbientSpace} (hw : w ∈ hyperoctahedralPerms)
    (hpos : IsReflectionPositiveAt S n) : IsReflectionPositiveAt S (w n) := by
  obtain ⟨l, hl, hk⟩ := exists_linear_of_mem_hyperoctahedralPerms hw
  have hlx : ∀ y, w y = l y := fun y => (congrFun hl y).symm
  have hwn : euclidNorm (w n) = 1 := by rw [hlx, hk, hn]
  intro f hf
  have hp := isDisjointSupportPair_reflectFun hwn hf
  have hr : w⁻¹ ∈ euclideanMotions :=
    mem_euclideanMotions_of_mem_hyperoctahedralPerms (inv_mem hw)
  rw [← (hInv w⁻¹ hr _ _ hp).2]
  have hprod : ∀ x, euclidDot (w n) (w x) = euclidDot n x := fun x => by
    rw [hlx, hlx]
    exact hk.euclidDot n x
  have hg : actOn w⁻¹ f ∈ cc1In (posHalfSpace n) := by
    have h1 := (isAffineIsometry_of_mem_hyperoctahedralPerms hw).comp_mem hf
    have e1 : ⇑w ⁻¹' posHalfSpace (w n) = posHalfSpace n := by
      ext x
      simp only [posHalfSpace, mem_preimage, mem_ofPred_eq, hprod]
    have e2 : actOn w⁻¹ f = f ∘ ⇑w := by
      funext x
      simp [actOn]
    rw [e2, ← e1]
    exact h1
  have hc : ∀ x, reflectAcross (w n) (w x) = w (reflectAcross n x) := fun x => by
    simp only [reflectAcross, hprod]
    simp only [hlx, map_sub, map_smul]
  have hm : actOn w⁻¹ (reflectFun (w n) (conjFun f)) =
      reflectFun n (conjFun (actOn w⁻¹ f)) := by
    funext x
    simp only [actOn, reflectFun, conjFun, Function.comp, inv_inv, hc]
  rw [hm]
  exact hpos _ hg
theorem exists_signed_coordVec (σ : Equiv.Perm (Fin 4)) (t : Fin 4 → ℤˣ) :
    ∃ l : AmbientSpace →ₗ[ℝ] AmbientSpace, ∃ w ∈ hyperoctahedralPerms, ⇑w = ⇑l ∧
      ∀ μ, l (coordVec μ) = (((t μ : ℤˣ) : ℤ) : ℝ) • coordVec (σ μ) := by
  have key : ∀ μ, signedPermLinear σ⁻¹ (fun ν => t (σ.symm ν)) (coordVec μ) =
      (((t μ : ℤˣ) : ℤ) : ℝ) • coordVec (σ μ) := by
    intro μ
    rw [signedPermLinear_coordVec]
    change (((t (σ.symm (σ μ)) : ℤˣ) : ℤ) : ℝ) • coordVec (σ μ) = _
    rw [Equiv.symm_apply_apply]
  obtain ⟨w, hw, he⟩ :=
    exists_mem_hyperoctahedralPerms (l := signedPermLinear σ⁻¹ _) ⟨σ, t, key⟩
  exact ⟨_, w, hw, he, key⟩
theorem exists_perm_map_pair {μ ν μ' ν' : Fin 4} (h : μ ≠ ν) (h' : μ' ≠ ν') :
    ∃ σ : Equiv.Perm (Fin 4), σ μ = μ' ∧ σ ν = ν' := by apply _root_.YangMills.Construction.InfiniteLattice.UnitSymmetriesAndFaces.exists_perm_apply_pair <;> assumption
theorem isReflectionPositive_holds (hE : ReflectionsPlaneFacts.Statement)
    {St : FixedScale} {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ}
    (hP : IsAdmissibleForm St S) : IsReflectionPositive S := by
  have hInv := complexifyInvariant_holds hP.invariantPositive
  have hunit : ∀ n ∈ reflectionNormals, euclidNorm n = 1 := by
    rintro n (⟨μ, ε, hε, rfl⟩ | ⟨μ, ν, ε, ε', hμν, hε, hε', rfl⟩)
    · exact hE.1.1 μ ε hε
    · exact hE.1.2.1 μ ν ε ε' hμν hε hε'
  have h₃ : euclidNorm (coordVec 3) = 1 := by
    simpa [signedAxis] using hE.1.1 3 1 (Or.inl rfl)
  have hTime : IsReflectionPositiveAt S (coordVec 3) := by
    intro g hg
    rw [hE.2.2.1.2 ℂ (conjFun g)]
    have hh : posHalfSpace (coordVec 3) = TimeAxis.upperHalfSpace := by
      ext x
      have e : euclidDot (coordVec 3) x = x 3 := by
        rw [euclidDot_comm, euclidDot_coordVec]
      simp only [posHalfSpace, mem_ofPred_eq, e]
      rfl
    exact hP.invariantPositive.2 g (hh ▸ hg)
  intro n hn f hf
  refine ⟨isDisjointSupportPair_reflectFun (hunit n hn) hf, ?_⟩
  rcases hn with ⟨μ, ε, hε, rfl⟩ | ⟨μ, ν, ε, ε', hμν, hε, hε', rfl⟩
  · obtain ⟨u, hu⟩ := exists_intUnit_cast_eq hε
    obtain ⟨l, w, hw, he, hk⟩ := exists_signed_coordVec (Equiv.swap 3 μ) (fun _ => u)
    have hwe : w (coordVec 3) = ε • coordVec μ := by
      rw [congrFun he, hk, hu]
      simp
    have := reflectionPositiveAt_map hInv h₃ hw hTime
    rw [hwe] at this
    exact this f hf
  · obtain ⟨n₀, hn₀, hpos⟩ := hP.diagonalPositive
    have hd₀ : euclidNorm n₀ = 1 := hunit n₀ (Or.inr hn₀)
    obtain ⟨μ₀, ν₀, δ, δ', hμν₀, hδ, hδ', rfl⟩ := hn₀
    obtain ⟨a, ha⟩ := exists_intUnit_cast_eq hδ
    obtain ⟨a', ha'⟩ := exists_intUnit_cast_eq hδ'
    obtain ⟨b, hb⟩ := exists_intUnit_cast_eq hε
    obtain ⟨b', hb'⟩ := exists_intUnit_cast_eq hε'
    obtain ⟨σ, hσ, hσ'⟩ := exists_perm_map_pair hμν₀.ne hμν.ne
    obtain ⟨l, w, hw, he, hk⟩ := exists_signed_coordVec σ
      (fun κ => if κ = μ₀ then a * b else if κ = ν₀ then a' * b' else 1)
    have hwe : w ((Real.sqrt 2)⁻¹ • (δ • coordVec μ₀ + δ' • coordVec ν₀)) =
        (Real.sqrt 2)⁻¹ • (ε • coordVec μ + ε' • coordVec ν) := by
      have e₁ : (((if μ₀ = μ₀ then a * b else if μ₀ = ν₀ then a' * b' else 1 : ℤˣ) : ℤ) : ℝ) =
          δ * ε := by
        simp [ha, hb]
      have e₂ : (((if ν₀ = μ₀ then a * b else if ν₀ = ν₀ then a' * b' else 1 : ℤˣ) : ℤ) : ℝ) =
          δ' * ε' := by
        simp [ha', hb', hμν₀.ne.symm]
      rw [congrFun he, map_smul, map_add, map_smul, map_smul, hk, hk, e₁, e₂, hσ, hσ', smul_smul,
        smul_smul, ← mul_assoc, ← mul_assoc, sign_mul_self_eq_one hδ, sign_mul_self_eq_one hδ',
        one_mul, one_mul]
    have := reflectionPositiveAt_map hInv hd₀ hw hpos
    rw [hwe] at this
    exact this f hf
theorem statement_holds (hE : ReflectionsPlaneFacts.Statement) : Statement :=
  ⟨reflectionsLieInSymmetryGroups_holds, fun _ hn => isIsometricInvolutiveReflection_holds hn,
    fun _ hf => ⟨isBoundedFun_of_mem hf, isLipschitzFor_of_mem hf⟩,
    fun St => ⟨fun _ hf => symmetriesPreserve_holds St hf, reImPartsControlled_holds St⟩,
    fun _ _ _ hS hP hC =>
      ⟨⟨fun _ _ hp => ⟨complexifyDefinedAt_of_pair hp, complexifyForm_symm hS hp⟩,
        complexifyLinear_holds hS, complexifyInvariant_holds hP.invariantPositive,
        complexifyConjCommute_holds hS, complexifyBallBound_holds hC⟩,
        isReflectionPositive_holds hE hP⟩⟩
end YangMills.Construction.TwoPoints.AdmissibleFormConsequences
end
