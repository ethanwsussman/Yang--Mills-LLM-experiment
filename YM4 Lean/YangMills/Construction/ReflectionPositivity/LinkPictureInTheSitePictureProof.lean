import YangMills.Construction.FormHilbert.FormCompletionAndDenseExtension
import YangMills.Construction.FormHilbert.JointSpectralCalculus
import YangMills.Construction.ReflectionPositivity.BoundedMomentumDensityWithReflectionSizesProof
import YangMills.Construction.ReflectionPositivity.LinkPictureInTheSitePicture
import Mathlib
set_option autoImplicit false
open Set
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.LinkSiteEmbedding
open InfiniteLattice (GaugeField IsBoundedObservable LatticePoint AmbientSpace UnitLatticeSymmetry
  halfSpaceLocalObservables closedHalfSpace regionSigma_mono axisStep shift unitRegionObservables)
open MirrorHyperplanes (unitPositiveClass linkReflectionForm linkReflect linkReflect_apply
  siteReflectionForm siteReflect siteReflect_apply)
theorem unitSymmetry_ext {r s : UnitLatticeSymmetry} (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound.unitLatticeSymmetry_ext <;> assumption
open FormHilbert
theorem linkReflect_eq_siteReflect_comp_shift (μ : Fin 4) :
    (linkReflect μ).toFun = (siteReflect μ).toFun ∘ (shift (axisStep 1 μ)).toFun := by
  funext x
  rw [Function.comp_apply, linkReflect_apply, siteReflect_apply]
  change _ = (x + (axisStep 1 μ : AmbientSpace)) - (2 * (x + (axisStep 1 μ : AmbientSpace)) μ) • _
  ext i
  by_cases h : i = μ
  · subst h
    simp [axisStep, MirrorHyperplanes.basisVec]
    ring
  · simp [axisStep, MirrorHyperplanes.basisVec, h]
theorem siteReflect_eq_shift_comp_linkReflect (μ : Fin 4) :
    (siteReflect μ).toFun = (shift (axisStep 1 μ)).toFun ∘ (linkReflect μ).toFun := by
  funext x
  rw [Function.comp_apply, linkReflect_apply, siteReflect_apply]
  change _ = (x - (2 * x μ + 1) • _) + (axisStep 1 μ : AmbientSpace)
  ext i
  by_cases h : i = μ
  · subst h
    simp [axisStep, MirrorHyperplanes.basisVec]
    ring
  · simp [axisStep, MirrorHyperplanes.basisVec, h]
theorem shift_actOn_mem
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (μ : Fin 4) (v : LatticePoint 1) (hv : 0 ≤ (v : AmbientSpace) μ) {F : GaugeField 1 → ℂ}
    (hF : F ∈ halfSpaceLocalObservables μ) :
    (shift v).actOn F ∈ halfSpaceLocalObservables μ := by
  obtain ⟨-, himg, -, -, hnorm, -, -, -, -, -⟩ := hAct
  obtain ⟨⟨oF, mF⟩, lF⟩ := hF
  obtain ⟨oH, -, lH⟩ := hnorm (shift v) F oF
  have hsub : (shift v).setImage (closedHalfSpace μ) ⊆ closedHalfSpace μ := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : 0 ≤ x μ := hx
    change 0 ≤ (x + (v : AmbientSpace)) μ
    rw [Pi.add_apply]
    linarith
  have hHS : (shift v).actOn F ∈
      unitRegionObservables ((shift v).setImage (closedHalfSpace μ)) := by
    rw [← himg]
    exact ⟨F, ⟨oF, mF⟩, rfl⟩
  exact ⟨⟨oH, hHS.2.mono (regionSigma_mono hsub) le_rfl⟩, lH lF⟩
theorem axisStep_actOn_mem
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (μ l : Fin 4) {F : GaugeField 1 → ℂ} (hF : F ∈ halfSpaceLocalObservables μ) :
    (shift (axisStep 1 l)).actOn F ∈ halfSpaceLocalObservables μ := by
  refine shift_actOn_mem hAct μ _ ?_ hF
  change 0 ≤ (Pi.single l (1 : ℝ) : Fin 4 → ℝ) μ
  by_cases h : μ = l
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]
variable (ν : unitPositiveClass) (μ : Fin 4)
theorem obsClass_eq_formClass (p : ReflectionPair) (F : halfSpaceLocalObservables μ) :
    p.obsClass ν μ F = formClass (p.pairForm ν μ) F :=
  dif_pos F.2
theorem reflect_actOn_relations
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (F : GaugeField 1 → ℂ) (hF : IsBoundedObservable F) :
    (linkReflect μ).actOn F =
        (siteReflect μ).actOn ((shift (axisStep 1 μ)).actOn F) ∧
      (siteReflect μ).actOn F =
        (shift (axisStep 1 μ)).actOn ((linkReflect μ).actOn F) := by
  obtain ⟨-, -, -, -, -, hrules, -, -, -, -⟩ := hAct
  have h₁ : linkReflect μ = (siteReflect μ).comp (shift (axisStep 1 μ)) :=
    unitSymmetry_ext (linkReflect_eq_siteReflect_comp_shift μ)
  have h₂ : siteReflect μ = (shift (axisStep 1 μ)).comp (linkReflect μ) :=
    unitSymmetry_ext (siteReflect_eq_shift_comp_linkReflect μ)
  constructor
  · have := (hrules (siteReflect μ) (shift (axisStep 1 μ)) F F hF hF).1
    rwa [← h₁] at this
  · have := (hrules (shift (axisStep 1 μ)) (linkReflect μ) F F hF hF).1
    rwa [← h₂] at this
theorem linkReflectionForm_eq_inner_transfer
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (hPic : ReflectionPairTheorem) (F H : halfSpaceLocalObservables μ) :
    linkReflectionForm ν μ F H =
      inner ℂ (ReflectionPair.site.obsClass ν μ F)
        (ReflectionPair.site.transferOp ν μ (ReflectionPair.site.obsClass ν μ H)) := by
  have hτ := axisStep_actOn_mem hAct μ μ F.2
  have hpos : IsPosSesqForm (ReflectionPair.site.pairForm ν μ) := (hPic ν μ ReflectionPair.site).1.1
  have hT : ReflectionPair.site.transferOp ν μ (ReflectionPair.site.obsClass ν μ F) =
      ReflectionPair.site.obsClass ν μ ((shift (axisStep 1 μ)).actOn F) :=
    (hPic ν μ ReflectionPair.site).2.1.2.2.1 F F.2
  have hsa := (isSelfAdjoint_iff_inner_eq (ReflectionPair.site.transferOp ν μ)).mp
    (ReflectionPair.site.opFamily ν μ).isSelfAdjoint_A
  have hobs : IsBoundedObservable (F : GaugeField 1 → ℂ) := F.2.1.1
  have hrefl := (reflect_actOn_relations μ hAct F hobs).1
  rw [hsa, hT, obsClass_eq_formClass ν μ ReflectionPair.site ⟨_, hτ⟩,
    obsClass_eq_formClass ν μ ReflectionPair.site H, inner_formClass hpos]
  change _ = siteReflectionForm ν μ ⟨_, hτ⟩ H
  simp only [linkReflectionForm, siteReflectionForm, hrefl]
theorem denseRange_formClass
    (hHil : DenseExtension.FormCompletionAndExtensionTheorem)
    (hPic : ReflectionPairTheorem) (p : ReflectionPair) :
    DenseRange (formClass (p.pairForm ν μ)) := by
  obtain ⟨-, ⟨-, -, -, M, hM, hd⟩, -⟩ := hHil (halfSpaceLocalObservables μ) (p.Hilb ν μ) (p.Hilb ν μ)
    (p.pairForm ν μ) (hPic ν μ p).1.1
  rw [hM] at hd
  exact hd
def sqrtClass : halfSpaceLocalObservables μ →ₗ[ℂ] ReflectionPair.site.Hilb ν μ :=
  (transferSqrt ν μ : ReflectionPair.site.Hilb ν μ →ₗ[ℂ] ReflectionPair.site.Hilb ν μ) ∘ₗ
    formClass (ReflectionPair.site.pairForm ν μ)
theorem sqrtClass_apply (F : halfSpaceLocalObservables μ) :
    sqrtClass ν μ F = transferSqrt ν μ (formClass (ReflectionPair.site.pairForm ν μ) F) := rfl
theorem transferSqrt_properties
    (hPic : ReflectionPairTheorem)
    (hSpec : JointSpectralCalculusTheorem) :
    SpectralSqrtProperties (ReflectionPair.site.opFamily ν μ) (ReflectionPair.site.jointPVM ν μ) := by
  obtain ⟨-, -, -, -, hE, -⟩ := hPic ν μ ReflectionPair.site
  exact ((hSpec (ReflectionPair.site.Hilb ν μ) (TransverseAxis μ) (ReflectionPair.site.opFamily ν μ)).2.2 _
    hE).2.2.2.2.2.1
theorem norm_sqrtClass_sq
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (hPic : ReflectionPairTheorem)
    (hSpec : JointSpectralCalculusTheorem) (F : halfSpaceLocalObservables μ) :
    ‖sqrtClass ν μ F‖ ^ 2 = (ReflectionPair.link.pairForm ν μ F F).re := by
  have hroot := transferSqrt_properties ν μ hPic hSpec
  have hsa : ∀ ψ ψ', inner ℂ ψ (transferSqrt ν μ ψ') = inner ℂ (transferSqrt ν μ ψ) ψ' :=
    (isSelfAdjoint_iff_inner_eq (transferSqrt ν μ)).mp hroot.selfAdjoint
  have hsq : ∀ ψ, transferSqrt ν μ (transferSqrt ν μ ψ) = ReflectionPair.site.transferOp ν μ ψ :=
    fun ψ => congrArg
      (fun A : ReflectionPair.site.Hilb ν μ →L[ℂ] ReflectionPair.site.Hilb ν μ => A ψ) hroot.sq_eq
  have hform : ReflectionPair.link.pairForm ν μ F F =
      inner ℂ (formClass (ReflectionPair.site.pairForm ν μ) F)
        (transferSqrt ν μ (transferSqrt ν μ (formClass (ReflectionPair.site.pairForm ν μ) F))) := by
    rw [hsq, ← obsClass_eq_formClass ν μ ReflectionPair.site F]
    exact linkReflectionForm_eq_inner_transfer ν μ hAct hPic F F
  rw [hform, hsa, sqrtClass_apply, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl
theorem closure_range_sqrtClass
    (hHil : DenseExtension.FormCompletionAndExtensionTheorem)
    (hPic : ReflectionPairTheorem)
    (hSpec : JointSpectralCalculusTheorem) :
    closure (range (sqrtClass ν μ)) =
      (transferKernelOrth ν μ : Set (ReflectionPair.site.Hilb ν μ)) := by
  have hroot := transferSqrt_properties ν μ hPic hSpec
  have hd := denseRange_formClass ν μ hHil hPic ReflectionPair.site
  have himg : range (sqrtClass ν μ) =
      transferSqrt ν μ '' range (formClass (ReflectionPair.site.pairForm ν μ)) := by
    rw [← range_comp]
    rfl
  have hcl : closure (range (sqrtClass ν μ)) = closure (range (transferSqrt ν μ)) := by
    rw [himg, ← closure_image_closure (transferSqrt ν μ).continuous, hd.closure_range, image_univ]
  rw [hcl, coe_transferKernelOrth]
  exact hroot.closure_range_eq.trans hroot.positiveLevel_range
theorem exists_isometric_extension
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (hHil : DenseExtension.FormCompletionAndExtensionTheorem)
    (hPic : ReflectionPairTheorem)
    (hSpec : JointSpectralCalculusTheorem) :
    ∃ A : ReflectionPair.link.Hilb ν μ →L[ℂ] ReflectionPair.site.Hilb ν μ,
      (∀ F, A (formClass (ReflectionPair.link.pairForm ν μ) F) = sqrtClass ν μ F) ∧
      (∀ B : ReflectionPair.link.Hilb ν μ →L[ℂ] ReflectionPair.site.Hilb ν μ,
        (∀ F, B (formClass (ReflectionPair.link.pairForm ν μ) F) = sqrtClass ν μ F) → B = A) ∧
      (∀ ψ ψ', inner ℂ (A ψ) (A ψ') = inner ℂ ψ ψ') ∧
      range A = (transferKernelOrth ν μ : Set (ReflectionPair.site.Hilb ν μ)) := by
  obtain ⟨-, -, -, hOp, -⟩ := hHil (halfSpaceLocalObservables μ) (ReflectionPair.site.Hilb ν μ)
    (ReflectionPair.site.Hilb ν μ) (ReflectionPair.link.pairForm ν μ) (hPic ν μ ReflectionPair.link).1.1
  have hn := norm_sqrtClass_sq ν μ hAct hPic hSpec
  obtain ⟨⟨A, hA, huniq⟩, hprop⟩ := hOp 1 (sqrtClass ν μ) zero_le_one
    (fun F => by rw [hn F, one_pow, one_mul])
  obtain ⟨-, hunit⟩ := hprop A hA
  obtain ⟨hinner, hrange, -⟩ := hunit hn
  exact ⟨A, hA, huniq, hinner, hrange.trans (closure_range_sqrtClass ν μ hHil hPic hSpec)⟩
theorem coe_eq_of_isLinkSiteIntertwiner
    {A : ReflectionPair.link.Hilb ν μ →L[ℂ] ReflectionPair.site.Hilb ν μ}
    (huniq : ∀ B : ReflectionPair.link.Hilb ν μ →L[ℂ] ReflectionPair.site.Hilb ν μ,
      (∀ F, B (formClass (ReflectionPair.link.pairForm ν μ) F) = sqrtClass ν μ F) → B = A)
    {W : ReflectionPair.link.Hilb ν μ →ₗ[ℂ] transferKernelOrth ν μ}
    (hW : IsLinkSiteIntertwiner ν μ W) (ψ : ReflectionPair.link.Hilb ν μ) :
    (W ψ : ReflectionPair.site.Hilb ν μ) = A ψ := by
  let L : ReflectionPair.link.Hilb ν μ →ₗᵢ[ℂ] ReflectionPair.site.Hilb ν μ :=
    LinearMap.isometryOfInner ((transferKernelOrth ν μ).subtype ∘ₗ W) hW.1.2
  have hL : L.toContinuousLinearMap = A := by
    refine huniq _ fun F => ?_
    have h := hW.2 F F.2
    rw [obsClass_eq_formClass ν μ ReflectionPair.link F,
      obsClass_eq_formClass ν μ ReflectionPair.site F] at h
    exact h
  exact congrArg (fun B : ReflectionPair.link.Hilb ν μ →L[ℂ] ReflectionPair.site.Hilb ν μ => B ψ) hL
theorem exists_isLinkSiteIntertwiner
    {A : ReflectionPair.link.Hilb ν μ →L[ℂ] ReflectionPair.site.Hilb ν μ}
    (hA : ∀ F, A (formClass (ReflectionPair.link.pairForm ν μ) F) = sqrtClass ν μ F)
    (hinner : ∀ ψ ψ', inner ℂ (A ψ) (A ψ') = inner ℂ ψ ψ')
    (hrange : range A = (transferKernelOrth ν μ : Set (ReflectionPair.site.Hilb ν μ))) :
    ∃ W, IsLinkSiteIntertwiner ν μ W := by
  have hmem : ∀ ψ, A ψ ∈ transferKernelOrth ν μ := fun ψ => by
    have : A ψ ∈ (transferKernelOrth ν μ : Set (ReflectionPair.site.Hilb ν μ)) :=
      hrange ▸ mem_range_self ψ
    exact this
  let W : ReflectionPair.link.Hilb ν μ →ₗ[ℂ] transferKernelOrth ν μ :=
    LinearMap.codRestrict _ (A : ReflectionPair.link.Hilb ν μ →ₗ[ℂ] ReflectionPair.site.Hilb ν μ) hmem
  have hcoe : ∀ ψ, (W ψ : ReflectionPair.site.Hilb ν μ) = A ψ := fun _ => rfl
  have hWinner : ∀ ψ ψ', inner ℂ (W ψ) (W ψ') = inner ℂ ψ ψ' := fun ψ ψ' => by
    rw [Submodule.coe_inner, hcoe, hcoe, hinner]
  refine ⟨W, ⟨⟨fun ψ ψ' h => ?_, fun χ => ?_⟩, hWinner⟩, fun F hF => ?_⟩
  · have hz : W (ψ - ψ') = 0 := by rw [map_sub, h, sub_self]
    have : inner ℂ (ψ - ψ') (ψ - ψ') = (0 : ℂ) := by rw [← hWinner, hz, inner_zero_left]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp this)
  · have hχ : (χ : ReflectionPair.site.Hilb ν μ) ∈ range A := by rw [hrange]; exact χ.2
    obtain ⟨ψ, hψ⟩ := hχ
    exact ⟨ψ, Subtype.ext hψ⟩
  · rw [hcoe, obsClass_eq_formClass ν μ ReflectionPair.link ⟨F, hF⟩,
      obsClass_eq_formClass ν μ ReflectionPair.site ⟨F, hF⟩]
    exact hA ⟨F, hF⟩
theorem intertwines_shift
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (hHil : DenseExtension.FormCompletionAndExtensionTheorem)
    (hPic : ReflectionPairTheorem)
    {A : ReflectionPair.link.Hilb ν μ →L[ℂ] ReflectionPair.site.Hilb ν μ}
    (hA : ∀ F, A (formClass (ReflectionPair.link.pairForm ν μ) F) = sqrtClass ν μ F) (l : Fin 4)
    {T' : ReflectionPair.link.Hilb ν μ →L[ℂ] ReflectionPair.link.Hilb ν μ}
    {T : ReflectionPair.site.Hilb ν μ →L[ℂ] ReflectionPair.site.Hilb ν μ}
    (h' : ReflectionPair.link.IsShiftOp ν μ l T') (h : ReflectionPair.site.IsShiftOp ν μ l T)
    (hc : Commute (transferSqrt ν μ) T) (ψ : ReflectionPair.link.Hilb ν μ) :
    A (T' ψ) = T (A ψ) := by
  have hd := denseRange_formClass ν μ hHil hPic ReflectionPair.link
  have hfun : (A ∘L T' : ReflectionPair.link.Hilb ν μ → ReflectionPair.site.Hilb ν μ) = (T ∘L A) := by
    refine hd.equalizer (A ∘L T').continuous (T ∘L A).continuous (funext fun F => ?_)
    have hτ := axisStep_actOn_mem hAct μ l F.2
    have e₁ := h' F F.2
    have e₂ := h F F.2
    rw [obsClass_eq_formClass ν μ ReflectionPair.link F,
      obsClass_eq_formClass ν μ ReflectionPair.link ⟨_, hτ⟩] at e₁
    rw [obsClass_eq_formClass ν μ ReflectionPair.site F,
      obsClass_eq_formClass ν μ ReflectionPair.site ⟨_, hτ⟩] at e₂
    have hcomm : transferSqrt ν μ (T (formClass (ReflectionPair.site.pairForm ν μ) F)) =
        T (transferSqrt ν μ (formClass (ReflectionPair.site.pairForm ν μ) F)) :=
      congrArg (fun B : ReflectionPair.site.Hilb ν μ →L[ℂ] ReflectionPair.site.Hilb ν μ =>
        B (formClass (ReflectionPair.site.pairForm ν μ) F)) hc.eq
    simp only [Function.comp_apply, ContinuousLinearMap.coe_comp]
    rw [e₁, hA, hA, sqrtClass_apply, sqrtClass_apply, ← e₂, hcomm]
  exact congrFun hfun ψ
theorem linkPictureEmbedsInSitePicture_holds
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (hHil : DenseExtension.FormCompletionAndExtensionTheorem)
    (hPic : ReflectionPairTheorem)
    (hSpec : JointSpectralCalculusTheorem) :
    LinkPictureEmbedsInSitePicture := by
  intro ν μ
  obtain ⟨A, hA, huniq, hinner, hrange⟩ := exists_isometric_extension ν μ hAct hHil hPic hSpec
  have hex := exists_isLinkSiteIntertwiner ν μ hA hinner hrange
  have hspec : IsLinkSiteIntertwiner ν μ (linkSiteIntertwiner ν μ) := Classical.epsilon_spec hex
  have hcoe := coe_eq_of_isLinkSiteIntertwiner ν μ huniq hspec
  have hroot := transferSqrt_properties ν μ hPic hSpec
  have hsysL := (hPic ν μ ReflectionPair.link).2.1.2.2
  have hsysS := (hPic ν μ ReflectionPair.site).2.1.2.2
  have hT : ∀ ψ, A (ReflectionPair.link.transferOp ν μ ψ) = ReflectionPair.site.transferOp ν μ (A ψ) :=
    intertwines_shift ν μ hAct hHil hPic hA μ hsysL.1 hsysS.1 hroot.commute_A
  have hU : ∀ (l : TransverseAxis μ) ψ, A (ReflectionPair.link.shiftOp ν μ l ψ) =
      ReflectionPair.site.shiftOp ν μ l (A ψ) := fun l =>
    intertwines_shift ν μ hAct hHil hPic hA l.1 (hsysL.2 l) (hsysS.2 l) (hroot.commute_B l)
  refine ⟨⟨linkReflect_eq_siteReflect_comp_shift μ, siteReflect_eq_shift_comp_linkReflect μ,
      fun F hF => reflect_actOn_relations μ hAct F hF⟩,
    linkReflectionForm_eq_inner_transfer ν μ hAct hPic, ⟨?_, hspec, ?_, ?_⟩, ?_⟩
  · obtain ⟨W, hW⟩ := hex
    refine ⟨W, hW, fun W' hW' => LinearMap.ext fun ψ => Subtype.ext ?_⟩
    rw [coe_eq_of_isLinkSiteIntertwiner ν μ huniq hW', coe_eq_of_isLinkSiteIntertwiner ν μ huniq hW]
  · intro ψ
    rw [hcoe, hcoe, hT]
  · intro l ψ
    rw [hcoe, hcoe, hU]
  · intro ψ ψ' h
    have hz : ReflectionPair.link.transferOp ν μ (ψ - ψ') = 0 := by rw [map_sub, h, sub_self]
    have hker : ReflectionPair.site.transferOp ν μ (A (ψ - ψ')) = 0 := by rw [← hT, hz, map_zero]
    have hmem : A (ψ - ψ') ∈ (transferKernelOrth ν μ : Set (ReflectionPair.site.Hilb ν μ)) :=
      hrange ▸ mem_range_self _
    rw [coe_transferKernelOrth] at hmem
    have hself : inner ℂ (A (ψ - ψ')) (A (ψ - ψ')) = (0 : ℂ) := hmem _ hker
    rw [hinner] at hself
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)
end YangMills.Construction.ReflectionPositivity.DirectionPictures.LinkSiteEmbedding
