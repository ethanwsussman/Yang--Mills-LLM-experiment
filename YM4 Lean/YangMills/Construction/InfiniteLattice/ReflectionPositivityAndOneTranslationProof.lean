import YangMills.Construction.InfiniteLattice.ReconstructionAtALatticeMirrorProof
import YangMills.Construction.InfiniteLattice.ReflectionPositivityDoesNotDependOnTheSide
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsOfOneLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
namespace YangMills.Construction
namespace LatticeConventions
namespace TranslationReflectionProof
open InfiniteLattice (Link GaugeField IsSymmetricUnder IsBoundedObservable LatticeSymmetry
  LatticePoint AmbientSpace localRegionObservables observableSupNorm boundedRegionObservables shift)
open NormalHyperplane
open YangMills.Construction.FormCompletion
section Forms
variable {𝒜 : Type*} [AddCommGroup 𝒜] [Module ℂ 𝒜] {q : 𝒜 → 𝒜 → ℂ}
theorem hermitian_of_im_diag_eq_zero
    (add_left : ∀ F₁ F₂ F', q (F₁ + F₂) F' = q F₁ F' + q F₂ F')
    (smul_left : ∀ (z : ℂ) F F', q (z • F) F' = conj z * q F F')
    (add_right : ∀ F F₁ F₂, q F (F₁ + F₂) = q F F₁ + q F F₂)
    (smul_right : ∀ (z : ℂ) F F', q F (z • F') = z * q F F')
    (real : ∀ F, (q F F).im = 0) (F F' : 𝒜) : q F' F = conj (q F F') := by
  have h₁ := real (F + F')
  rw [add_left, add_right, add_right] at h₁
  have h₂ := real (F + Complex.I • F')
  rw [add_left, add_right, add_right, smul_left, smul_right, smul_right, smul_left] at h₂
  have hF := real F
  have hF' := real F'
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.conj_I, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im] at h₁ h₂
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith
theorem norm_sq_le_re_mul_re (hq : IsPosSemidefHermitianForm q) (F F' : 𝒜) :
    ‖q F F'‖ ^ 2 ≤ (q F F).re * (q F' F').re := by
  let c : PreInnerProductSpace.Core ℂ 𝒜 :=
    { inner := q
      conj_inner_symm := fun x y => by
        show conj (q y x) = q x y
        rw [hq.hermitian x y, Complex.conj_conj]
      re_inner_nonneg := fun x => hq.nonneg x
      add_left := hq.add_left
      smul_left := fun x y r => hq.smul_left r x y }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ 𝒜 _ _ _ c F F'
  have h' : ‖q F F'‖ * ‖q F' F‖ ≤ RCLike.re (q F F) * RCLike.re (q F' F') := h
  rw [hq.hermitian F F', RCLike.norm_conj] at h'
  rw [pow_two]
  exact h'
end Forms
section Observables
variable {a : ℝ}
theorem isBoundedObservable_of_mem_localRegion {S : Set AmbientSpace} {F : GaugeField a → ℂ}
    (h : F ∈ localRegionObservables a S) : IsBoundedObservable F := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.isBoundedObservable_of_mem_local <;> assumption
theorem integrable_of_isBoundedObservable (ν : Measure (GaugeField a)) [IsFiniteMeasure ν]
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) : Integrable F ν := by
  obtain ⟨hm, C, hC⟩ := hF
  exact Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
theorem isBoundedObservable_mul {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) : IsBoundedObservable (fun U => F U * G U) := by
  obtain ⟨hm, C, hC⟩ := hF
  obtain ⟨hm', D, hD⟩ := hG
  refine ⟨hm.mul hm', C * D, fun U => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC U) (hD U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
theorem isBoundedObservable_conjFun {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (conjFun F) := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.isBoundedObservable_conjFun <;> assumption
theorem norm_le_supNorm {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (U : GaugeField a) : ‖F U‖ ≤ observableSupNorm F := by
  obtain ⟨_, C, hC⟩ := hF
  exact le_ciSup (f := fun U => ‖F U‖) ⟨C, by rintro _ ⟨U, rfl⟩; exact hC U⟩ U
theorem latticeSymmetry_ext {r r' : LatticeSymmetry a} (h : r.toFun = r'.toFun) : r = r' := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
end Observables
section Pairing
variable {a : ℝ} {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a)
  (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
noncomputable def conjReflectMul (F F' : GaugeField a → ℂ) : GaugeField a → ℂ :=
  fun U => conjFun ((reflectSymmetry hQ).actOn F) U * F' U
include hQ in
theorem integrable_conjReflectMul
    (hobs : ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      IsBoundedObservable ((reflectSymmetry hQ).actOn F))
    {F F' : GaugeField a → ℂ} (hF : IsBoundedObservable F) (hF' : IsBoundedObservable F') :
    Integrable (conjReflectMul hQ F F') ν :=
  integrable_of_isBoundedObservable ν
    (isBoundedObservable_mul (isBoundedObservable_conjFun (hobs F hF)) hF')
theorem upperReflectionForm_isPosSemidef
    (hobs : ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      IsBoundedObservable ((reflectSymmetry hQ).actOn F))
    (hrp : IsReflectionPositiveAcrossMirror hQ ν) :
    IsPosSemidefHermitianForm (upperReflectionForm hQ ν) := by
  have obs : ∀ F : upperObservables a Q, IsBoundedObservable F.1 :=
    fun F => isBoundedObservable_of_mem_localRegion F.2
  have hint : ∀ F F' : upperObservables a Q,
      Integrable (conjReflectMul hQ F.1 F'.1) ν :=
    fun F F' => integrable_conjReflectMul hQ ν hobs (obs F) (obs F')
  have add_left : ∀ F₁ F₂ F' : upperObservables a Q,
      upperReflectionForm hQ ν (F₁ + F₂) F' =
        upperReflectionForm hQ ν F₁ F' + upperReflectionForm hQ ν F₂ F' := by
    intro F₁ F₂ F'
    refine (integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)).trans
      (integral_add (hint F₁ F') (hint F₂ F'))
    simp [conjFun, LatticeSymmetry.actOn, add_mul]
  have smul_left : ∀ (z : ℂ) (F F' : upperObservables a Q),
      upperReflectionForm hQ ν (z • F) F' = conj z * upperReflectionForm hQ ν F F' := by
    intro z F F'
    refine (integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)).trans
      (integral_const_mul (conj z) (conjReflectMul hQ F.1 F'.1))
    simp [conjFun, LatticeSymmetry.actOn, conjReflectMul, mul_assoc]
  have add_right : ∀ F F₁ F₂ : upperObservables a Q,
      upperReflectionForm hQ ν F (F₁ + F₂) =
        upperReflectionForm hQ ν F F₁ + upperReflectionForm hQ ν F F₂ := by
    intro F F₁ F₂
    refine (integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)).trans
      (integral_add (hint F F₁) (hint F F₂))
    simp [mul_add]
  have smul_right : ∀ (z : ℂ) (F F' : upperObservables a Q),
      upperReflectionForm hQ ν F (z • F') = z * upperReflectionForm hQ ν F F' := by
    intro z F F'
    refine (integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)).trans
      (integral_const_mul z (conjReflectMul hQ F.1 F'.1))
    simp [conjReflectMul, mul_left_comm]
  have real : ∀ F : upperObservables a Q, (upperReflectionForm hQ ν F F).im = 0 :=
    fun F => (hrp ⟨F.1, F.2⟩).1
  exact
    { add_left := add_left
      smul_left := smul_left
      add_right := add_right
      smul_right := smul_right
      hermitian := hermitian_of_im_diag_eq_zero add_left smul_left add_right smul_right real
      nonneg := fun F => (hrp ⟨F.1, F.2⟩).2 }
theorem upperReflectionForm_re_le_supNorm_sq {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    {G : upperObservables a Q} (hG : G.1 = F) :
    (upperReflectionForm hQ ν G G).re ≤ observableSupNorm F ^ 2 := by
  subst hG
  have hbound : ∀ U, ‖conjReflectMul hQ G.1 G.1 U‖ ≤ observableSupNorm G.1 ^ 2 := by
    intro U
    rw [pow_two]
    simp only [conjReflectMul, norm_mul, conjFun, RCLike.norm_conj]
    exact mul_le_mul (norm_le_supNorm hF _) (norm_le_supNorm hF _) (norm_nonneg _)
      ((norm_nonneg _).trans (norm_le_supNorm hF U))
  have h := norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall hbound)
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at h
  exact (Complex.re_le_norm _).trans h
theorem integral_actOn_eq_of_upper
    (hq : IsPosSemidefHermitianForm (upperReflectionForm hQ ν))
    (hone : (fun _ => (1 : ℂ)) ∈ localRegionObservables a Q.upperHalfSpace)
    {F : GaugeField a → ℂ} (hF : F ∈ localRegionObservables a Q.upperHalfSpace) :
    ∫ U, (reflectSymmetry hQ).actOn F U ∂ν = ∫ U, F U ∂ν := by
  have h := hq.hermitian (⟨F, hF⟩ : upperObservables a Q)
    (⟨fun _ => 1, hone⟩ : upperObservables a Q)
  have h₁ : upperReflectionForm hQ ν (⟨fun _ => 1, hone⟩ : upperObservables a Q)
      ⟨F, hF⟩ = ∫ U, F U ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp [conjFun, LatticeSymmetry.actOn]
  have h₂ : upperReflectionForm hQ ν ⟨F, hF⟩
      (⟨fun _ => 1, hone⟩ : upperObservables a Q) =
        conj (∫ U, (reflectSymmetry hQ).actOn F U ∂ν) := by
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp [conjFun]
  rw [h₁, h₂, Complex.conj_conj] at h
  exact h.symm
end Pairing
theorem euclidDot_add (n x y : Point) : euclidDot n (x + y) = euclidDot n x + euclidDot n y := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.euclidDot_add <;> assumption
theorem euclidDot_smul (n x : Point) (r : ℝ) : euclidDot n (r • x) = r * euclidDot n x := by
  simp only [euclidDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun μ _ => by ring
theorem exists_abs_euclidDot_le (n : Point) {S : Set AmbientSpace} (hS : Bornology.IsBounded S) :
    ∃ B : ℝ, ∀ x ∈ S, |euclidDot n x| ≤ B := by
  obtain ⟨R, hR⟩ := hS.exists_norm_le
  refine ⟨∑ μ, |n μ| * R, fun x hx => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact (norm_le_pi_norm x μ).trans (hR x hx)
theorem isBounded_translateSet {S : Set AmbientSpace} (hS : Bornology.IsBounded S)
    (v : AmbientSpace) : Bornology.IsBounded (translateSet S v) := by
  obtain ⟨R, hR⟩ := hS.exists_norm_le
  refine isBounded_iff_forall_norm_le.2 ⟨R + ‖v‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (norm_add_le _ _).trans (by linarith [hR x hx])
section Invariance
variable (a : Spacing) {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror (a : ℝ))
  (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν]
theorem integral_actOn_eq_of_bounded
    (hA : InfiniteLattice.SymmetryActionOnObservables)
    (hM : MirrorReflections.MirrorReflectionsStatement)
    (hside : ∀ F ∈ localRegionObservables (a : ℝ) Q.upperHalfSpace,
      ∫ U, (reflectSymmetry hQ).actOn F U ∂ν = ∫ U, F U ∂ν)
    (h : LatticePoint (a : ℝ)) (h0 : h ≠ 0) (hs : Q.reflectionLinear (h : Point) = -(h : Point))
    (hinv : IsSymmetricUnder ν (shift h))
    {S : Set AmbientSpace} (hS : Bornology.IsBounded S) {F : GaugeField (a : ℝ) → ℂ}
    (hF : F ∈ boundedRegionObservables (a : ℝ) S) :
    ∫ U, (reflectSymmetry hQ).actOn F U ∂ν = ∫ U, F U ∂ν := by
  obtain ⟨-, -, hKeep, hComp, hTrans, -, hGrow, -, -, -, hMul⟩ := hA a
  obtain ⟨-, -, -, -, hLin, -⟩ := hM a
  obtain ⟨hIso, hVec⟩ := hLin Q
  have hd : euclidDot Q.normal (h : Point) ≠ 0 := by
    intro hd0
    have h1 := ((hVec (h : Point)).1).1 hs
    rw [hd0] at h1
    simp only [mul_zero, zero_smul] at h1
    exact h0 (Subtype.ext h1)
  obtain ⟨B, hB⟩ := exists_abs_euclidDot_le Q.normal hS
  obtain ⟨M, hMnat⟩ := exists_nat_ge ((Q.level + B) / |euclidDot Q.normal (h : Point)|)
  have hdpos : 0 < |euclidDot Q.normal (h : Point)| := abs_pos.2 hd
  have hMd : Q.level + B ≤ (M : ℝ) * |euclidDot Q.normal (h : Point)| :=
    (div_le_iff₀ hdpos).1 hMnat
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : ℝ) * euclidDot Q.normal (h : Point) =
      (M : ℝ) * |euclidDot Q.normal (h : Point)| := by
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · exact ⟨-(M : ℤ), by rw [abs_of_neg hneg]; push_cast; ring⟩
    · exact ⟨(M : ℤ), by rw [abs_of_pos hpos]; push_cast; ring⟩
  set v : LatticePoint (a : ℝ) := m • h with hv
  have hvpt : (v : Point) = (m : ℝ) • (h : Point) := by
    funext μ
    simp [hv]
  set w : LatticePoint (a : ℝ) := (-m) • h with hw
  have hwpt : (w : Point) = -(v : Point) := by
    rw [hvpt]
    funext μ
    simp [hw]
  have hsv : Q.reflectionLinear (v : Point) = (w : Point) := by
    rw [hwpt, hvpt, map_smul, hs, smul_neg]
  have hobsF : IsBoundedObservable F := hF.1
  have hobsθ : IsBoundedObservable ((reflectSymmetry hQ).actOn F) :=
    ((hKeep (reflectSymmetry hQ)).1 F F hobsF hobsF).1
  have hsub : translateSet S (v : AmbientSpace) ⊆ Q.upperHalfSpace := by
    rintro _ ⟨x, hx, rfl⟩
    show Q.level ≤ euclidDot Q.normal (x + (v : Point))
    rw [euclidDot_add, hvpt, euclidDot_smul, hm]
    have := (abs_le.1 (hB x hx)).1
    linarith
  have hbdd := isBounded_translateSet hS (v : AmbientSpace)
  set G : GaugeField (a : ℝ) → ℂ := (shift v).actOn F with hG
  have hGmem : G ∈ boundedRegionObservables (a : ℝ) (translateSet S (v : AmbientSpace)) := by
    rw [← ((hTrans v).1 S)]
    exact ⟨F, hF, rfl⟩
  have hGloc : G ∈ localRegionObservables (a : ℝ) Q.upperHalfSpace := by
    refine ((hGrow.2.1 _ _ hsub).2) ?_
    rw [← hGrow.2.2 _ hbdd]
    exact hGmem
  have hprob : IsProbabilityMeasure ν := inferInstance
  have hGF : ∫ U, G U ∂ν = ∫ U, F U ∂ν := ((hMul ν hprob).2 h hinv m) F hobsF
  have hmaps : (reflectSymmetry hQ).comp (shift v) =
      (shift w).comp (reflectSymmetry hQ) := by
    apply latticeSymmetry_ext
    funext x
    show Q.reflect (x + (v : Point)) = Q.reflect x + (w : Point)
    rw [hIso.2.2.1, hsv]
  have hθG : (reflectSymmetry hQ).actOn G =
      (shift w).actOn ((reflectSymmetry hQ).actOn F) := by
    rw [hG, ← (hComp _ _).2 F hobsF, hmaps, (hComp _ _).2 F hobsF]
  have hstep := hside G hGloc
  rw [hθG, ((hMul ν hprob).2 h hinv (-m)) _ hobsθ, hGF] at hstep
  exact hstep
theorem map_pullbackField_eq
    (hA : InfiniteLattice.SymmetryActionOnObservables)
    (hSp : InfiniteLattice.GaugeFieldSpace.TopologyStatement)
    (hlocal : ∀ {S : Set AmbientSpace}, Bornology.IsBounded S →
      ∀ F ∈ boundedRegionObservables (a : ℝ) S,
        ∫ U, (reflectSymmetry hQ).actOn F U ∂ν = ∫ U, F U ∂ν) :
    ν.map (reflectSymmetry hQ).pullbackField = ν := by
  obtain ⟨-, hHomeo, -⟩ := hA a
  have hcont : Continuous (reflectSymmetry hQ).pullbackField :=
    ((hHomeo (reflectSymmetry hQ)).2).continuous
  have hmeas : Measurable (reflectSymmetry hQ).pullbackField := hcont.measurable
  have hborel : borel (GaugeField (a : ℝ)) =
      ⨆ b : Link (a : ℝ), MeasurableSpace.comap (fun U : GaugeField (a : ℝ) => U b)
        (borel Matrices.ComplexMatrix2.specialUnitary) := (hSp (a : ℝ) a.2).2.2.2.2.2
  have hevals : ∀ b : Link (a : ℝ),
      MeasurableSpace.comap (fun U : GaugeField (a : ℝ) => U b)
          (borel Matrices.ComplexMatrix2.specialUnitary) ≤
        (inferInstance : MeasurableSpace (GaugeField (a : ℝ))) := fun b => by
    show _ ≤ borel (GaugeField (a : ℝ))
    rw [hborel]
    exact le_iSup (fun b : Link (a : ℝ) =>
      MeasurableSpace.comap (fun U : GaugeField (a : ℝ) => U b)
        (borel Matrices.ComplexMatrix2.specialUnitary)) b
  let m : Link (a : ℝ) → MeasurableSpace (GaugeField (a : ℝ)) := fun b =>
    MeasurableSpace.comap (fun U : GaugeField (a : ℝ) => U b)
      (borel Matrices.ComplexMatrix2.specialUnitary)
  refine ext_of_generate_finite
    (piiUnionInter (fun b => {s | MeasurableSet[m b] s}) Set.univ) ?_
    (isPiSystem_piiUnionInter _ (fun b => @MeasurableSpace.isPiSystem_measurableSet _ (m b)) _)
    ?_ ?_
  · show borel (GaugeField (a : ℝ)) = _
    rw [generateFrom_piiUnionInter_measurableSet m Set.univ]
    simpa [m] using hborel
  · rintro _ ⟨T, -, f, hf, rfl⟩
    set Y : Set (GaugeField (a : ℝ)) := ⋂ b ∈ T, f b with hY
    let S : Set AmbientSpace := ⋃ b ∈ T, {(b.initial : AmbientSpace), (b.terminal : AmbientSpace)}
    have hSfin : S.Finite :=
      Set.Finite.biUnion T.finite_toSet fun b _ => by simp
    have hSb : Bornology.IsBounded S := hSfin.isBounded
    have hYS : MeasurableSet[InfiniteLattice.regionSigma S] Y := by
      refine @Finset.measurableSet_biInter _ _ (InfiniteLattice.regionSigma S) _ T fun b hb => ?_
      have hle : m b ≤ InfiniteLattice.regionSigma S := by
        have hbS : b ∈ (InfiniteLattice.linksWithin S : Set (Link (a : ℝ))) := by
          refine ⟨Set.mem_iUnion₂.2 ⟨b, hb, by simp⟩, Set.mem_iUnion₂.2 ⟨b, hb, by simp⟩⟩
        exact le_iSup₂ (f := fun b (_ : b ∈ (InfiniteLattice.linksWithin S : Set (Link (a : ℝ)))) =>
          MeasurableSpace.comap (fun U : GaugeField (a : ℝ) => U b) inferInstance) b hbS
      exact hle _ (hf b hb)
    have hsig : InfiniteLattice.regionSigma S ≤
        (inferInstance : MeasurableSpace (GaugeField (a : ℝ))) :=
      iSup₂_le fun b _ => hevals b
    have hYm : MeasurableSet Y := hsig _ hYS
    set I : GaugeField (a : ℝ) → ℂ := Y.indicator fun _ => 1 with hI
    have hImeas : Measurable[InfiniteLattice.regionSigma S] I := by
      rw [hI]
      exact Measurable.indicator measurable_const hYS
    have hIobs : I ∈ boundedRegionObservables (a : ℝ) S := by
      refine ⟨⟨hImeas.mono hsig le_rfl, 1, fun U => ?_⟩, hImeas⟩
      by_cases hU : U ∈ Y <;> simp [hI, hU]
    have h := hlocal hSb I hIobs
    have hpre : (reflectSymmetry hQ).actOn I =
        ((reflectSymmetry hQ).pullbackField ⁻¹' Y).indicator fun _ => 1 := by
      funext U
      simp only [LatticeSymmetry.actOn, hI, Set.indicator]
      rfl
    rw [hpre, integral_indicator_const _ (hmeas hYm), hI, integral_indicator_const _ hYm] at h
    have hreal : ν.real ((reflectSymmetry hQ).pullbackField ⁻¹' Y) = ν.real Y := by
      simpa using h
    rw [Measure.map_apply hmeas hYm]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hreal
  · rw [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ]
theorem reflectedPairingBound_of_map_eq
    (hobs : ∀ F : GaugeField (a : ℝ) → ℂ, IsBoundedObservable F →
      IsBoundedObservable ((reflectSymmetry hQ).actOn F))
    (hmeas : Measurable (reflectSymmetry hQ).pullbackField)
    (hmap : ν.map (reflectSymmetry hQ).pullbackField = ν) :
    ReflectedPairingBound hQ ν := by
  intro F F' hF hF'
  have hmem : ∀ {G : GaugeField (a : ℝ) → ℂ}, IsBoundedObservable G →
      MemLp (absFun G) (ENNReal.ofReal 2) ν := by
    rintro G ⟨hm, C, hC⟩
    refine MemLp.of_bound hm.norm.aestronglyMeasurable C (Filter.Eventually.of_forall fun U => ?_)
    simpa [absFun] using hC U
  have hnonneg : ∀ G : GaugeField (a : ℝ) → ℂ, 0 ≤ᵐ[ν] absFun G :=
    fun G => Filter.Eventually.of_forall fun U => norm_nonneg (G U)
  have hsq : ∫ U, absFun ((reflectSymmetry hQ).actOn F) U ^ 2 ∂ν =
      ∫ U, absFun F U ^ 2 ∂ν := by
    have hFm : AEStronglyMeasurable (fun U => absFun F U ^ 2)
        (ν.map (reflectSymmetry hQ).pullbackField) :=
      ((hF.1.norm).pow_const 2).aestronglyMeasurable
    have := integral_map hmeas.aemeasurable hFm
    rw [hmap] at this
    exact this.symm
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ν) Real.HolderConjugate.two_two
    (hnonneg ((reflectSymmetry hQ).actOn F)) (hnonneg F')
    (hmem (hobs F hF)) (hmem hF')
  simp only [Real.rpow_two] at hcs
  rw [hsq] at hcs
  refine (norm_integral_le_integral_norm _).trans (le_trans (le_of_eq ?_) hcs)
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp [conjFun, absFun]
end Invariance
theorem reflectionPositivityWithTranslation_holds
    (h₁ : InfiniteLattice.SymmetryActionOnObservables)
    (h₂ : MirrorReflections.MirrorReflectionsStatement)
    (h₃ : InfiniteLattice.GaugeFieldSpace.TopologyStatement)
    (h₄ : MirrorSideIndependence.Statement) :
    ReflectionPositivityWithTranslation := by
  intro a Q hQ ν _ hrp
  obtain ⟨-, hHomeo, hKeep, -, -, -, -, hAlg, -⟩ := h₁ a
  have hobs : ∀ F : GaugeField (a : ℝ) → ℂ, IsBoundedObservable F →
      IsBoundedObservable ((reflectSymmetry hQ).actOn F) :=
    fun F hF => ((hKeep (reflectSymmetry hQ)).1 F F hF hF).1
  have hq := upperReflectionForm_isPosSemidef hQ ν hobs hrp
  refine ⟨⟨hq, fun F F' => ⟨norm_sq_le_re_mul_re hq F F', (hrp ⟨F.1, F.2⟩).1, hq.nonneg F,
    upperReflectionForm_re_le_supNorm_sq hQ ν (isBoundedObservable_of_mem_localRegion F.2) rfl⟩⟩, ?_⟩
  intro h h0 hs hinv
  have hone : (fun _ => (1 : ℂ)) ∈ localRegionObservables (a : ℝ) Q.upperHalfSpace :=
    (hAlg Q.upperHalfSpace).2.1 1
  have hside := fun F hF => integral_actOn_eq_of_upper hQ ν hq hone (F := F) hF
  have hlocal : ∀ {S : Set AmbientSpace}, Bornology.IsBounded S →
      ∀ F ∈ boundedRegionObservables (a : ℝ) S,
        ∫ U, (reflectSymmetry hQ).actOn F U ∂ν = ∫ U, F U ∂ν :=
    fun hS F hF => integral_actOn_eq_of_bounded a hQ ν h₁ h₂ hside h h0 hs hinv hS hF
  have hmap := map_pullbackField_eq a hQ ν h₁ h₃ hlocal
  have hmeas : Measurable (reflectSymmetry hQ).pullbackField :=
    ((hHomeo (reflectSymmetry hQ)).2).continuous.measurable
  refine ⟨fun A hA => ?_, ?_, reflectedPairingBound_of_map_eq a hQ ν hobs hmeas hmap⟩
  · have hAm : AEStronglyMeasurable A (ν.map (reflectSymmetry hQ).pullbackField) :=
      hA.1.aestronglyMeasurable
    have := integral_map hmeas.aemeasurable hAm
    rw [hmap] at this
    exact this.symm
  · exact ((h₄ a).1 Q hQ).2 ν |>.2.1 hrp
end TranslationReflectionProof
end LatticeConventions
end YangMills.Construction
