import YangMills.Construction.HilbertSpaces.SquareRootOfAPositiveContraction
import YangMills.Construction.InfiniteLattice.ExpansionsMeetTheConditionsOfTheReconstruction
import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.LinkPictureAndSitePicture
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslation
import Mathlib
set_option autoImplicit false
open MeasureTheory
open YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert
open YangMills.Construction.ContractionUnitary
open YangMills.Construction.FormCompletion
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.LatticeConventions.LinkSiteComparison
open NormalHyperplane
open YangMills.Construction.InfiniteLattice (GaugeField IsShiftInvariant LatticePoint axisStep shift)
section Completion
variable {𝒜 : Type} [AddCommGroup 𝒜] [Module ℂ 𝒜] {q : 𝒜 → 𝒜 → ℂ}
def formClassLinearMap (hA : DualSpaceComplete q) (hB : FormCompletionHilbert q) :
    𝒜 →ₗ[ℂ] FormHilbertSpace q where
  toFun := classVec q
  map_add' x y := by
    obtain ⟨-, -, -, -, hadd, -⟩ := hA
    obtain ⟨-, -, -, -, -, hmap, -⟩ := hB
    apply asMap_injective
    rw [asMap_add, hmap, hmap, hmap, hadd]
  map_smul' c x := by
    obtain ⟨-, -, -, -, -, hsmul, -⟩ := hA
    obtain ⟨-, -, -, -, -, hmap, -⟩ := hB
    apply asMap_injective
    rw [RingHom.id_apply, asMap_smul, hmap, hmap, hsmul]
end Completion
section Operators
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
theorem eq_of_agree_on_denseRange {X : Type} {c : X → H} (hc : DenseRange c)
    {A B : BddOpBetween H H'} (h : ∀ x, A (c x) = B (c x)) : A = B :=
  DFunLike.coe_injective (hc.equalizer A.continuous B.continuous (funext h))
theorem closure_range_comp_denseRange {X : Type} {c : X → H} (hc : DenseRange c)
    (B : BddOpBetween H H') :
    closure (Set.range fun x => B (c x)) = closure (Set.range B) := by
  apply Set.Subset.antisymm
  · exact closure_mono (by rintro _ ⟨x, rfl⟩; exact ⟨c x, rfl⟩)
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨ψ, rfl⟩
    have h₁ : ψ ∈ closure (Set.range c) := hc ψ
    have h₂ := image_closure_subset_closure_image B.continuous ⟨ψ, h₁, rfl⟩
    refine closure_mono ?_ h₂
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
theorem exists_unitaryMap_of_isometry {W : BddOpBetween H H'} {M : Submodule ℂ H'}
    (hiso : ∀ ψ, ‖W ψ‖ = ‖ψ‖) (hr : Set.range W = (M : Set H')) :
    ∃ W₀ : H →ₗ[ℂ] M, (∀ ψ, (W₀ ψ : H') = W ψ) ∧ IsUnitaryMap W₀ := by
  have hmem : ∀ ψ, W ψ ∈ M := fun ψ => by
    exact show W ψ ∈ (M : Set H') from hr ▸ Set.mem_range_self ψ
  refine ⟨(W : H →ₗ[ℂ] H').codRestrict M hmem, fun _ => rfl, ⟨fun ψ => hiso ψ, ?_⟩⟩
  rintro ⟨χ, hχ⟩
  have h₁ : χ ∈ Set.range W := hr ▸ hχ
  obtain ⟨ψ, rfl⟩ := h₁
  exact ⟨ψ, rfl⟩
end Operators
theorem exists_ne_direction (μ : Direction) : ∃ l : Direction, μ ≠ l := by
  revert μ
  decide
theorem mirrorReconstruction_step_vector (hRec : MirrorReconstruction)
    (a : Spacing) {S S' : NormalHyperplane} (hS : S.IsLatticeMirror (a : ℝ))
    (hS' : S'.IsLatticeMirror (a : ℝ)) (h w : LatticePoint (a : ℝ))
    (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν]
    (hmid : S'.IsMidPlaneOf (a : ℝ) S (h : Point))
    (hdot : euclidDot S.normal (w : Point) = 0) (hinv : IsShiftInvariant ν)
    (hrp : IsReflectionPositiveAcrossMirror hS ν) (hrp' : IsReflectionPositiveAcrossMirror hS' ν) :
    StepIsPositiveContraction hS ν h ∧ VectorIsUnitary hS ν w ∧
      Commute (stepOperator hS ν h) (vectorUnitary hS ν w) := by
  have hc : MirrorReconstructionHyps (a : ℝ) S (h : Point) S'
      (fun i => (((fun _ : Fin 1 => w) i : LatticePoint (a : ℝ)) : Point)) :=
    ⟨hmid, hS', by simp, fun _ => w.2, fun _ => hdot⟩
  obtain ⟨-, hb, hc', hd⟩ :=
    hRec a S S' hS hS' h 1 (fun _ => w) ν hc (hinv h) (fun _ => hinv w) hrp hrp'
  exact ⟨hb, hc' 0, hd.1 0⟩
theorem linkFrame_reconstruction (hRec : MirrorReconstruction)
    (hRows : MirrorExpansions.Statement) (a : Spacing) (μ : Direction)
    (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν]
    (hst : LinkFrame.IsAdmissibleState a μ ν) (lam : {l : Direction // l ≠ μ}) :
    StepIsPositiveContraction (LinkFrame.linkPlane_isLatticeMirror a μ) ν (axisStep (a : ℝ) μ) ∧
      VectorIsUnitary (LinkFrame.linkPlane_isLatticeMirror a μ) ν (axisStep (a : ℝ) lam.1) ∧
      Commute (stepOperator (LinkFrame.linkPlane_isLatticeMirror a μ) ν (axisStep (a : ℝ) μ))
        (vectorUnitary (LinkFrame.linkPlane_isLatticeMirror a μ) ν (axisStep (a : ℝ) lam.1)) := by
  have row := (hRows.2.1 a μ lam.1 lam.2.symm 0 ⟨0, by simp⟩).1
  have hmid := row.midPlane_isMid
  rw [LinkFrame.linkPicture_normalStep] at hmid
  have hdot := row.euclidDot_tangentStep lam
  rw [LinkFrame.linkPicture_tangentStep] at hdot
  exact mirrorReconstruction_step_vector hRec a (LinkFrame.linkPlane_isLatticeMirror a μ)
    row.midPlane_isLatticeMirror _ _ ν hmid hdot hst.shiftInvariant
    hst.reflectionPositive_linkPlane
    (hst.reflectionPositive_sitePlane row.midPlane_isLatticeMirror)
theorem siteFrame_reconstruction (hRec : MirrorReconstruction)
    (hRows : MirrorExpansions.Statement) (a : Spacing) (μ : Direction)
    (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν]
    (hst : LinkFrame.IsAdmissibleState a μ ν) (lam : {l : Direction // l ≠ μ}) :
    StepIsPositiveContraction (SiteFrame.vertexPlane_isLatticeMirror a μ) ν (axisStep (a : ℝ) μ) ∧
      VectorIsUnitary (SiteFrame.vertexPlane_isLatticeMirror a μ) ν (axisStep (a : ℝ) lam.1) ∧
      Commute (stepOperator (SiteFrame.vertexPlane_isLatticeMirror a μ) ν (axisStep (a : ℝ) μ))
        (vectorUnitary (SiteFrame.vertexPlane_isLatticeMirror a μ) ν (axisStep (a : ℝ) lam.1)) := by
  have row := (hRows.2.1 a μ lam.1 lam.2.symm 0 ⟨0, by simp⟩).2.1
  have hmid := row.midPlane_isMid
  rw [SiteFrame.sitePicture_normalStep] at hmid
  have hdot := row.euclidDot_tangentStep lam
  rw [SiteFrame.sitePicture_tangentStep] at hdot
  exact mirrorReconstruction_step_vector hRec a (SiteFrame.vertexPlane_isLatticeMirror a μ)
    row.midPlane_isLatticeMirror _ _ ν hmid hdot hst.shiftInvariant
    (SiteFrame.reflectionPositive_vertexPlane hst)
    (SiteFrame.reflectionPositive_midPlane hst row.midPlane_isLatticeMirror)
theorem linkReflection_eq_comp_shift (a : Spacing) (μ : Direction) :
    LinkFrame.linkReflection a μ =
      (SiteFrame.siteReflection a μ).comp (shift (axisStep (a : ℝ) μ)) := by
  have h : (LinkFrame.linkReflection a μ).toFun =
      ((SiteFrame.siteReflection a μ).comp (shift (axisStep (a : ℝ) μ))).toFun := by
    rw [LinkFrame.linkReflection_toFun]
    change LinkFrame.linkReflectionMap a μ =
      fun x => (SiteFrame.siteReflection a μ).toFun (x + (axisStep (a : ℝ) μ : Point))
    rw [SiteFrame.siteReflection_toFun]
    funext x κ
    by_cases hκ : κ = μ
    · subst hκ
      simp [LinkFrame.linkReflectionMap, SiteFrame.siteReflectionMap, axisStep, basisVector]
      ring
    · simp [LinkFrame.linkReflectionMap, SiteFrame.siteReflectionMap, axisStep, basisVector,
        Pi.single_eq_of_ne hκ]
  generalize LinkFrame.linkReflection a μ = r at h
  generalize (SiteFrame.siteReflection a μ).comp (shift (axisStep (a : ℝ) μ)) = r' at h
  cases r
  cases r'
  cases h
  rfl
theorem statement_holds (hComp : FormCompletion.FormCompletionIsHilbertSpace)
    (hRP : ReflectionPositivityWithTranslation)
    (hRec : MirrorReconstruction)
    (hRows : MirrorExpansions.Statement)
    (hSides : LinkHalfSpaces.Statement)
    (hRoot : SqrtContractionProperties) :
    Statement := by
  intro a μ ν _ hst
  obtain ⟨l₀, hl₀⟩ := exists_ne_direction μ
  have hcarL := (linkFrame_reconstruction hRec hRows a μ ν hst ⟨l₀, hl₀.symm⟩).1.1
  obtain ⟨hcarS, -, saS, aboveS, belowS⟩ :=
    (siteFrame_reconstruction hRec hRows a μ ν hst ⟨l₀, hl₀.symm⟩).1
  have heq := SiteFrame.upperSpace_eq_upperAlgebra a μ ((hSides a).2.2 μ)
  have hmem : ∀ F : LinkFrame.upperAlgebra a μ, F.1 ∈ SiteFrame.upperSpace a μ :=
    fun F => heq.ge F.2
  have posL := (hRP a _ (LinkFrame.linkPlane_isLatticeMirror a μ) ν
    hst.reflectionPositive_linkPlane).1.1
  have posS := (hRP a _ (SiteFrame.vertexPlane_isLatticeMirror a μ) ν
    (SiteFrame.reflectionPositive_vertexPlane hst)).1.1
  obtain ⟨hAL, hBL, hCL⟩ := hComp _ _ posL
  obtain ⟨hAS, hBS, -⟩ := hComp _ _ posS
  have denseL : DenseRange (LinkFrame.linkClass a μ ν) := hBL.2.2.2.2.2.2.2.2
  have denseS : DenseRange (SiteFrame.siteClass a μ ν) := hBS.2.2.2.2.2.2.2.2
  have innerS : ∀ G G' : SiteFrame.upperSpace a μ,
      ⟪SiteFrame.siteClass a μ ν G, SiteFrame.siteClass a μ ν G'⟫_ℂ =
        SiteFrame.siteForm a μ ν G G' := hBS.2.2.2.2.2.2.1
  have hA : LinkFormEqSiteFormTransfer a μ ν := by
    intro F F' hF hF'
    obtain ⟨G, hG, hTG⟩ := hcarS ⟨F.1, hF⟩
    have hTG' : SiteFrame.transferOperator a μ ν (SiteFrame.siteClass a μ ν ⟨F.1, hF⟩) =
        SiteFrame.siteClass a μ ν G := hTG
    have hsa : ⟪SiteFrame.siteClass a μ ν ⟨F.1, hF⟩,
          SiteFrame.transferOperator a μ ν (SiteFrame.siteClass a μ ν ⟨F'.1, hF'⟩)⟫_ℂ =
        ⟪SiteFrame.transferOperator a μ ν (SiteFrame.siteClass a μ ν ⟨F.1, hF⟩),
          SiteFrame.siteClass a μ ν ⟨F'.1, hF'⟩⟫_ℂ := saS _ _
    rw [hsa, hTG', innerS]
    change ∫ U, conjFun ((LinkFrame.linkReflection a μ).actOn F.1) U *
        F'.1 U ∂ν =
      ∫ U, conjFun ((SiteFrame.siteReflection a μ).actOn G.1) U *
        F'.1 U ∂ν
    rw [hG, linkReflection_eq_comp_shift]
    rfl
  have saT : IsSymmetricOp (SiteFrame.transferOperator a μ ν) := saS
  obtain ⟨⟨-, -, -, hnormR, -⟩, ⟨-, hcommR⟩, -, hranR⟩ :=
    hRoot (SiteFrame.SiteHilbertSpace a μ ν) (SiteFrame.transferOperator a μ ν) saT aboveS belowS
  set T := SiteFrame.transferOperator a μ ν with hT
  set Q := contractionSqrt T with hQ
  let ι : LinkFrame.upperAlgebra a μ →ₗ[ℂ] SiteFrame.upperSpace a μ :=
    Submodule.inclusion heq.ge
  let R : LinkFrame.upperAlgebra a μ →ₗ[ℂ] SiteFrame.SiteHilbertSpace a μ ν :=
    (Q : SiteFrame.SiteHilbertSpace a μ ν →ₗ[ℂ] SiteFrame.SiteHilbertSpace a μ ν) ∘ₗ
      formClassLinearMap hAS hBS ∘ₗ ι
  have hRapply : ∀ F, R F = Q (SiteFrame.siteClass a μ ν ⟨F.1, hmem F⟩) := fun F => rfl
  have hRnorm : ∀ F, ‖R F‖ =
      seminormOfForm (upperReflectionForm (LinkFrame.linkPlane_isLatticeMirror a μ) ν) F := by
    intro F
    have h₁ := hnormR (SiteFrame.siteClass a μ ν ⟨F.1, hmem F⟩)
    have h₂ := hA F F (hmem F) (hmem F)
    have h₃ : (upperReflectionForm (LinkFrame.linkPlane_isLatticeMirror a μ) ν F F).re =
        ‖R F‖ ^ 2 := by
      have h₄ : LinkFrame.linkForm a μ ν F F =
          ((‖R F‖ ^ 2 : ℝ) : ℂ) := by rw [hRapply]; exact h₂.trans h₁.symm
      have h₅ := congrArg Complex.re h₄
      rwa [Complex.ofReal_re] at h₅
    rw [seminormOfForm, h₃, Real.sqrt_sq (norm_nonneg _)]
  obtain ⟨⟨B, hBR, hBuniq⟩, hall⟩ := hCL (SiteFrame.SiteHilbertSpace a μ ν) 1 R zero_le_one
    (fun F => by rw [one_mul, hRnorm])
  obtain ⟨hisoB, hrange⟩ := (hall B hBR).2 hRnorm
  have hcar : MapsClassToSqrtTransfer a μ ν B := fun F hF => hBR F
  have hspec : MapsClassToSqrtTransfer a μ ν (linkToSite a μ ν) :=
    Classical.epsilon_spec ⟨B, hcar⟩
  have hW : linkToSite a μ ν = B := hBuniq _ fun F => hspec F (hmem F)
  have hclass : (Set.range R) = Set.range fun G : LinkFrame.upperAlgebra a μ =>
      Q (SiteFrame.siteClass a μ ν (ι G)) := rfl
  have hsurj : Function.Surjective ι := by
    rintro ⟨G, hG⟩
    exact ⟨⟨G, heq.le hG⟩, rfl⟩
  have hrangeOrth : Set.range B = (siteKernelOrth a μ ν : Set _) := by
    rw [hrange, hclass, coe_siteKernelOrth, ← hranR, seqClosureOf_eq_closure]
    have hd : DenseRange fun G : LinkFrame.upperAlgebra a μ =>
        SiteFrame.siteClass a μ ν (ι G) := by
      change Dense (Set.range (SiteFrame.siteClass a μ ν ∘ ι))
      rw [hsurj.range_comp]
      exact denseS
    exact closure_range_comp_denseRange hd Q
  have hinter : ∀ (v : LatticePoint (a : ℝ)) (A : BddOp (LinkFrame.LinkHilbertSpace a μ ν))
      (C : BddOp (SiteFrame.SiteHilbertSpace a μ ν)),
      TransportsClassesBy (LinkFrame.linkPlane_isLatticeMirror a μ) ν v A →
      TransportsClassesBy (SiteFrame.vertexPlane_isLatticeMirror a μ) ν v C → C * T = T * C →
      B.comp A = C.comp B := by
    intro v A C hAc hCc hcomm
    refine eq_of_agree_on_denseRange denseL fun F => ?_
    obtain ⟨G, hG, hAG⟩ := hAc F
    obtain ⟨G', hG', hCG⟩ := hCc ⟨F.1, hmem F⟩
    have hGG : G' = ⟨G.1, hmem G⟩ := Subtype.ext (hG'.trans hG.symm)
    have h₁ := congrArg (fun X : BddOp (SiteFrame.SiteHilbertSpace a μ ν) =>
      X (SiteFrame.siteClass a μ ν ⟨F.1, hmem F⟩)) (hcommR C hcomm)
    have hCG' : C (SiteFrame.siteClass a μ ν ⟨F.1, hmem F⟩) =
        SiteFrame.siteClass a μ ν ⟨G.1, hmem G⟩ := by
      rw [← hGG]
      exact hCG
    have hAG' : A (LinkFrame.linkClass a μ ν F) = LinkFrame.linkClass a μ ν G := hAG
    change B (A (LinkFrame.linkClass a μ ν F)) = C (B (LinkFrame.linkClass a μ ν F))
    rw [hAG']
    have hb₁ : B (LinkFrame.linkClass a μ ν G) = R G := hBR G
    have hb₂ : B (LinkFrame.linkClass a μ ν F) = R F := hBR F
    rw [hb₁, hb₂, hRapply, hRapply, ← hCG']
    exact h₁.symm
  have hTcomm : T * T = T * T := rfl
  have hinterT : B.comp (LinkFrame.transferOperator a μ ν) = T.comp B :=
    hinter _ _ _ hcarL hcarS hTcomm
  refine ⟨hA, ?_, ?_⟩
  · rw [LinkToSiteUnitaryIntertwines, hW]
    refine ⟨hcar, ?_, ?_, ?_, hinterT, ?_⟩
    · intro W hWc
      exact hBuniq _ fun F => hWc F (hmem F)
    · exact (isClosedSet_iff _).2 (Submodule.isClosed_orthogonal _)
    · exact exists_unitaryMap_of_isometry hisoB hrangeOrth
    · intro lam
      obtain ⟨-, hVL, -⟩ := linkFrame_reconstruction hRec hRows a μ ν hst lam
      obtain ⟨-, hVS, hcomm⟩ := siteFrame_reconstruction hRec hRows a μ ν hst lam
      exact hinter _ _ _ hVL.1 hVS.1 hcomm.eq.symm
  · apply Set.eq_singleton_iff_unique_mem.2
    refine ⟨map_zero _, fun ψ hψ => ?_⟩
    have hψ' : LinkFrame.transferOperator a μ ν ψ = 0 := hψ
    have h₁ : T (B ψ) = 0 := by
      have h₂ := congrArg (fun X : BddOpBetween _ _ => X ψ) hinterT
      change B (LinkFrame.transferOperator a μ ν ψ) = T (B ψ) at h₂
      rw [hψ', map_zero] at h₂
      exact h₂.symm
    have h₃ : B ψ ∈ (siteKernelOrth a μ ν : Set _) := hrangeOrth ▸ Set.mem_range_self ψ
    have h₄ : ⟪B ψ, B ψ⟫_ℂ = 0 := by
      rw [coe_siteKernelOrth] at h₃
      exact h₃ _ h₁
    have h₅ : B ψ = 0 := inner_self_eq_zero.1 h₄
    have h₆ := hisoB ψ
    rw [h₅, norm_zero] at h₆
    exact norm_eq_zero.1 h₆.symm
end YangMills.Construction.LatticeConventions.LinkSiteComparison
end
