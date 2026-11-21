import YangMills.Construction.Torus.AveragingOnUnionsOfBlocks
import YangMills.Construction.Torus.BlockIndicatorOnAUnionOfBlocks
import YangMills.Construction.Torus.CoercivityAndWeightedBoundsOfAnAdmissiblePairProof
import YangMills.Construction.Torus.ExactlyOneOperatorOfAPairForm
import YangMills.Construction.Torus.OperatorsOfAnAdmissiblePair
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
namespace AdmissiblePairOps
variable {D : TorusData} (B : SeparatedChain D)
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem siteScale_pos (y : D.Space) : 0 < B.siteScale y := scale_pos D _
theorem bareInner_comm (f f' : D.BareSite → ℝ) : B.bareInner f f' = B.bareInner f' f := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.bareInner_comm <;> assumption
theorem bareInner_add_left (f f' g : D.BareSite → ℝ) :
    B.bareInner (f + f') g = B.bareInner f g + B.bareInner f' g := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bareInner_add_left <;> assumption
theorem bareInner_add_right (f g g' : D.BareSite → ℝ) :
    B.bareInner f (g + g') = B.bareInner f g + B.bareInner f g' := by
  rw [bareInner_comm, bareInner_add_left, bareInner_comm B g, bareInner_comm B g']
theorem bareInner_sub_left (f f' g : D.BareSite → ℝ) :
    B.bareInner (f - f') g = B.bareInner f g - B.bareInner f' g := by
  have h := bareInner_add_left B (f - f') f' g
  rw [sub_add_cancel] at h
  linarith
theorem bareInner_sub_right (f g g' : D.BareSite → ℝ) :
    B.bareInner f (g - g') = B.bareInner f g - B.bareInner f g' := by
  rw [bareInner_comm, bareInner_sub_left, bareInner_comm B g, bareInner_comm B g']
theorem bareInner_smul_left (c : ℝ) (f g : D.BareSite → ℝ) :
    B.bareInner (c • f) g = c * B.bareInner f g := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bareInner_smul_left <;> assumption
theorem bareInner_smul_right (c : ℝ) (f g : D.BareSite → ℝ) :
    B.bareInner f (c • g) = c * B.bareInner f g := by
  rw [bareInner_comm, bareInner_smul_left, bareInner_comm B g]
theorem bareInner_zero_right (f : D.BareSite → ℝ) : B.bareInner f 0 = 0 := by
  simp [SeparatedChain.bareInner]
theorem eq_zero_of_bareInner_self {f : D.BareSite → ℝ}
    (hf : ∀ x, x ∉ D.bareSites (B.stage 0) → f x = 0) (h : B.bareInner f f = 0) : f = 0 := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.eq_zero_of_bareInner_self <;> assumption
theorem layerInner_comm (w w' : B.LayerFn) : B.layerInner w w' = B.layerInner w' w := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.layerInner_comm <;> assumption
theorem admissibleOp_isUnit (W : Set D.Space) (T : Module.End ℝ ↥(B.bareSpaceOn W))
    (hpos : ∀ f : ↥(B.bareSpaceOn W), f ≠ 0 → 0 < B.bareInner f (T f)) : IsUnit T := by
  have := D.bareSite_finite
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  by_contra hne
  have h := hpos f hne
  rw [hf] at h
  have h0 : B.bareInner (f : D.BareSite → ℝ) ((0 : ↥(B.bareSpaceOn W)) : D.BareSite → ℝ) = 0 :=
    bareInner_zero_right B _
  exact absurd h (by rw [h0]; exact lt_irrefl 0)
theorem eq_of_quadForm_eq (T T' : Module.End ℝ ↥B.bareSpace)
    (hT : ∀ f g : ↥B.bareSpace, B.bareInner (T f) g = B.bareInner f (T g))
    (hT' : ∀ f g : ↥B.bareSpace, B.bareInner (T' f) g = B.bareInner f (T' g))
    (hq : ∀ f : ↥B.bareSpace, B.bareInner f (T f) = B.bareInner f (T' f)) : T = T' := by
  have hS : ∀ f g : ↥B.bareSpace,
      B.bareInner ((T - T') f) g = B.bareInner f ((T - T') g) := by
    intro f g
    simp only [LinearMap.sub_apply, Submodule.coe_sub]
    rw [bareInner_sub_left, bareInner_sub_right, hT, hT']
  have hS0 : ∀ f : ↥B.bareSpace, B.bareInner f ((T - T') f) = 0 := by
    intro f
    simp only [LinearMap.sub_apply, Submodule.coe_sub]
    rw [bareInner_sub_right, hq, sub_self]
  have hzero : ∀ g : ↥B.bareSpace, (T - T') g = 0 := by
    intro g
    set u : ↥B.bareSpace := (T - T') g with hu
    have h1 := hS0 (u + g)
    rw [map_add] at h1
    simp only [Submodule.coe_add] at h1
    rw [bareInner_add_left, bareInner_add_right, bareInner_add_right] at h1
    have h2 := hS0 u
    have h3 := hS0 g
    have h4 := hS u g
    rw [← hu] at h3 h4 h1
    have h6 : B.bareInner (g : D.BareSite → ℝ) ((T - T') u) =
        B.bareInner (u : D.BareSite → ℝ) u := by
      rw [bareInner_comm]
      exact h4
    have h5 : B.bareInner (u : D.BareSite → ℝ) u = 0 := by linarith
    exact Subtype.ext (eq_zero_of_bareInner_self B u.2 h5)
  exact sub_eq_zero.1 (LinearMap.ext hzero)
def invScaleOn (W : Set D.Space) : Module.End ℝ ↥(B.layerSpaceOn W) where
  toFun w := ⟨fun y => (B.siteScale y)⁻¹ * (w : B.LayerFn) y, fun y hy => by
    have h : (w : B.LayerFn) y = 0 := w.2 y hy
    simp [h]⟩
  map_add' w w' := by
    apply Subtype.ext
    funext y
    simp [mul_add]
  map_smul' c w := by
    apply Subtype.ext
    funext y
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem inverse_scaleOnLayerOn (W : Set D.Space) :
    Ring.inverse (B.scaleOnLayerOn W) = invScaleOn B W := by
  have h1 : B.scaleOnLayerOn W * invScaleOn B W = 1 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    funext y
    change B.siteScale y * ((B.siteScale y)⁻¹ * (w : B.LayerFn) y) = _
    rw [mul_inv_cancel_left₀ (siteScale_pos B _).ne']
    rfl
  have h2 : invScaleOn B W * B.scaleOnLayerOn W = 1 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    funext y
    change (B.siteScale y)⁻¹ * (B.siteScale y * (w : B.LayerFn) y) = _
    rw [inv_mul_cancel_left₀ (siteScale_pos B _).ne']
    rfl
  exact Ring.inverse_unit (⟨_, _, h1, h2⟩ : (Module.End ℝ ↥(B.layerSpaceOn W))ˣ)
theorem basisVec_of_ne {y z : ↥B.allSites} (h : z ≠ y) : B.basisVec y z = 0 :=
  indicator_of_notMem (by simpa using h) _
theorem layerInner_basisVec (y : ↥B.allSites) (v : B.LayerFn) :
    B.layerInner (B.basisVec y) v = B.siteScale y ^ 2 * v y := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.layerInner_basisVec <;> assumption
theorem restrictToBlocks_basisVec (W : Set D.Space) (y : ↥B.allSites)
    (hy : (y : D.Space) ∈ B.sitesIn W) :
    (B.restrictToBlocks W (B.basisVec y) : B.LayerFn) = B.basisVec y := by
  funext z
  change {y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn W}.indicator (B.basisVec y) z = _
  by_cases hz : z = y
  · subst hz
    exact indicator_of_mem (s := {y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn W}) hy _
  · rw [basisVec_of_ne B hz]
    by_cases hzW : (z : D.Space) ∈ B.sitesIn W
    · rw [indicator_of_mem (s := {y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn W}) hzW,
        basisVec_of_ne B hz]
    · exact indicator_of_notMem (s := {y : ↥B.allSites | (y : D.Space) ∈ B.sitesIn W}) hzW _
theorem pairOperatorFacts (W : Set D.Space) (𝔟 : Set D.Bond)
    (hcoer : B.AdmissibleFormCoercive W 𝔟) (hkeep : B.AvgPreservesBlockUnion W)
    (hnr : B.AdmissibleAvgGreenSqUnrestricted W 𝔟)
    (hrel : B.AvgRelations) (hbasis : B.BasisRelations)
    (hblock : ∀ y ∈ B.sitesIn W, ∃ h : B.blockIndicator y ∈ B.bareSpaceOn W,
      B.blockIndicatorIn W y = ⟨B.blockIndicator y, h⟩) :
    B.PairOperatorFacts W 𝔟 := by
  obtain ⟨-, hsym, hpos⟩ := hcoer
  obtain ⟨-, -, hresBare, -⟩ := hkeep
  set A := B.admissibleOp W 𝔟 with hA
  have hunit : IsUnit A := admissibleOp_isUnit B W A hpos
  set G := B.admissibleGreen W 𝔟 with hG
  have hAG : ∀ f, A (G f) = f := fun f =>
    LinearMap.congr_fun (Ring.mul_inverse_cancel A hunit) f
  have hGA : ∀ f, G (A f) = f := fun f =>
    LinearMap.congr_fun (Ring.inverse_mul_cancel A hunit) f
  have hGsym : ∀ f g : ↥(B.bareSpaceOn W),
      B.bareInner (G f) g = B.bareInner f (G g) := by
    intro f g
    have h := hsym (G f) (G g)
    rw [hAG, hAG] at h
    exact h.symm
  have hGpos : ∀ f : ↥(B.bareSpaceOn W), f ≠ 0 → 0 < B.bareInner f (G f) := by
    intro f hf
    have hu : G f ≠ 0 := by
      intro h0
      apply hf
      rw [← hAG f, h0, map_zero]
    have h := hpos (G f) hu
    rw [hAG, bareInner_comm] at h
    exact h
  have hTform : ∀ w w' : ↥(B.layerSpaceOn W),
      B.layerInner w (B.admissibleAvgGreenSq W 𝔟 w') =
        B.bareInner (G (B.restrictBare W (B.avgOpAdjoint w)))
          (G (B.restrictBare W (B.avgOpAdjoint w'))) := by
    intro w w'
    rw [hnr w' _ (hresBare w'), layerInner_comm, hrel.1]
    have hcoe : ((B.bareSpaceOnIncl W ((G * G)
        (B.restrictBare W (B.avgOpAdjoint w'))) : ↥B.bareSpace) :
          D.BareSite → ℝ) =
        (G (G (B.restrictBare W (B.avgOpAdjoint w'))) : D.BareSite → ℝ) := rfl
    rw [hcoe, ← hresBare w, hGsym, bareInner_comm]
  have hTsym : ∀ w w' : ↥(B.layerSpaceOn W),
      B.layerInner (B.admissibleAvgGreenSq W 𝔟 w) w' =
        B.layerInner w (B.admissibleAvgGreenSq W 𝔟 w') := by
    intro w w'
    rw [layerInner_comm, hTform, hTform, bareInner_comm]
  refine ⟨hunit, hGsym, hGpos, hTform, hTsym, ?_⟩
  intro y y' hy hy'
  have hrestrict : ∀ z : ↥B.allSites, (z : D.Space) ∈ B.sitesIn W →
      B.restrictBare W (B.avgOpAdjoint (B.restrictToBlocks W (B.basisVec z))) =
        B.siteScale z ^ (-2 : ℤ) • B.blockIndicatorIn W z := by
    intro z hz
    obtain ⟨h, hχ⟩ := hblock z hz
    rw [hχ]
    apply Subtype.ext
    rw [hresBare, restrictToBlocks_basisVec B W z hz, hbasis.2.2.2.2 z]
    rfl
  have hinv2 : ∀ z : ↥B.allSites, (z : D.Space) ∈ B.sitesIn W →
      invScaleOn B W (invScaleOn B W (B.restrictToBlocks W (B.basisVec z))) =
        (B.siteScale z ^ 2)⁻¹ • B.restrictToBlocks W (B.basisVec z) := by
    intro z hz
    apply Subtype.ext
    funext v
    change (B.siteScale v)⁻¹ * ((B.siteScale v)⁻¹ *
        (B.restrictToBlocks W (B.basisVec z) : B.LayerFn) v) =
      (B.siteScale z ^ 2)⁻¹ * (B.restrictToBlocks W (B.basisVec z) : B.LayerFn) v
    rw [restrictToBlocks_basisVec B W z hz]
    by_cases hv : v = z
    · subst hv
      rw [← mul_assoc, ← mul_inv, pow_two]
    · simp [basisVec_of_ne B hv]
  have hlp := hTform (B.restrictToBlocks W (B.basisVec y))
    (B.restrictToBlocks W (B.basisVec y'))
  rw [hrestrict y hy, hrestrict y' hy', restrictToBlocks_basisVec B W y hy, layerInner_basisVec,
    map_smul, map_smul] at hlp
  simp only [Submodule.coe_smul] at hlp
  rw [bareInner_smul_left, bareInner_smul_right] at hlp
  have hmat : B.admissibleScaledMatrix W 𝔟 y y' =
      B.siteScale y ^ 2 * (B.admissibleScaledGreenSq W 𝔟
        (B.restrictToBlocks W (B.basisVec y')) : B.LayerFn) y :=
    layerInner_basisVec B y _
  have hS : (B.admissibleScaledGreenSq W 𝔟 (B.restrictToBlocks W (B.basisVec y')) :
        B.LayerFn) y =
      (B.siteScale y)⁻¹ * ((B.siteScale y)⁻¹ * ((B.siteScale y' ^ 2)⁻¹ *
        (B.admissibleAvgGreenSq W 𝔟 (B.restrictToBlocks W (B.basisVec y')) :
          B.LayerFn) y)) := by
    unfold SeparatedChain.admissibleScaledGreenSq
    rw [inverse_scaleOnLayerOn]
    simp only [pow_two, Module.End.mul_apply]
    rw [← pow_two, hinv2 y' hy', map_smul]
    rfl
  have hξ := (siteScale_pos B (y : D.Space)).ne'
  have hξ' := (siteScale_pos B (y' : D.Space)).ne'
  rw [hmat, hS]
  simp only [zpow_neg, zpow_ofNat] at hlp ⊢
  set P := B.bareInner (G (B.blockIndicatorIn W y)) (G (B.blockIndicatorIn W y'))
  set t := (B.admissibleAvgGreenSq W 𝔟 (B.restrictToBlocks W (B.basisVec y')) :
    B.LayerFn) y
  have ht : t = (B.siteScale y ^ 2)⁻¹ * ((B.siteScale y ^ 2)⁻¹ *
      ((B.siteScale y' ^ 2)⁻¹ * P)) := by
    field_simp
    field_simp at hlp
    linarith
  rw [ht]
  field_simp
theorem initialPairFacts (hsites : B.sitesIn (B.stage 0) = B.allSites)
    (hU : B.IsBlockUnion (B.stage 0))
    (hpair : B.IsAdmissibleFormOp (B.stage 0) B.initialBonds
      (B.admissibleOp (B.stage 0) B.initialBonds))
    (hcoer : B.AdmissibleFormCoercive (B.stage 0) B.initialBonds)
    (hnr : B.AdmissibleAvgGreenSqUnrestricted (B.stage 0) B.initialBonds)
    (hwa : B.WeightedAvgForm) :
    B.InitialPairFacts := by
  have hH : B.bareSpaceOn (B.stage 0) = B.bareSpace := inf_idem _
  obtain ⟨-, hsym, hpos⟩ := hcoer
  set A := B.admissibleOp (B.stage 0) B.initialBonds with hA
  have hunit : IsUnit A := admissibleOp_isUnit B _ A hpos
  set G := B.admissibleGreen (B.stage 0) B.initialBonds with hG
  have hAG : ∀ f, A (G f) = f := fun f =>
    LinearMap.congr_fun (Ring.mul_inverse_cancel A hunit) f
  have hGA : ∀ f, G (A f) = f := fun f =>
    LinearMap.congr_fun (Ring.inverse_mul_cancel A hunit) f
  let e : ↥(B.bareSpaceOn (B.stage 0)) ≃ₗ[ℝ] ↥B.bareSpace := LinearEquiv.ofEq _ _ hH
  have hecoe : ∀ f, ((e f : ↥B.bareSpace) : D.BareSite → ℝ) = f := fun _ => rfl
  have hescoe : ∀ f : ↥B.bareSpace,
      ((e.symm f : ↥(B.bareSpaceOn (B.stage 0))) : D.BareSite → ℝ) = f := fun f => by
    have h := hecoe (e.symm f)
    rw [e.apply_symm_apply] at h
    exact h.symm
  have hincl : ∀ f, B.bareSpaceOnIncl (B.stage 0) f = e f := fun _ => rfl
  let A' : Module.End ℝ ↥B.bareSpace := e.toLinearMap ∘ₗ A ∘ₗ e.symm.toLinearMap
  let G' : Module.End ℝ ↥B.bareSpace := e.toLinearMap ∘ₗ G ∘ₗ e.symm.toLinearMap
  have hA' : ∀ f, A' f = e (A (e.symm f)) := fun _ => rfl
  have hG' : ∀ f, G' f = e (G (e.symm f)) := fun _ => rfl
  have hA'sym : ∀ f g : ↥B.bareSpace, B.bareInner (A' f) g = B.bareInner f (A' g) := by
    intro f g
    have h := hsym (e.symm f) (e.symm g)
    rw [hescoe, hescoe] at h
    rw [hA', hA', hecoe, hecoe]
    exact h
  have hform : ∀ f : ↥B.bareSpace, B.bareInner f (A' f) =
      TorusData.bondNorm (TorusData.bondsMeeting (D.bareSites (B.stage 0)))
        (TorusData.bondGrad (f : D.BareSite → ℝ)) ^ 2 +
      B.bareInner f (B.weightedAvg f) := by
    intro f
    have h := hpair.2 (e.symm f) (e.symm f)
    rw [hescoe] at h
    rw [hA', hecoe, h, hwa.1 f f]
    unfold SeparatedChain.admissibleForm TorusData.bondNorm
    rw [Real.sq_sqrt (mul_nonneg (pow_pos (scale_pos D 0) 4).le
      (finsum_nonneg fun b => finsum_nonneg fun _ => sq_nonneg _))]
    have hincl' : B.bareSpaceOnIncl (B.stage 0) (e.symm f) = f := by
      rw [hincl, e.apply_symm_apply]
    rw [hincl', hescoe, hsites]
    congr 1
    · congr 1
      exact finsum_mem_congr rfl fun b _ => (pow_two _).symm
    · rw [← finsum_set_coe_eq_finsum_mem]
      refine finsum_congr fun y => ?_
      have hv : ∀ w : B.LayerFn, B.layerEval w y = w y := fun w => by
        simp [SeparatedChain.layerEval]
      rw [hv]
  let D0 : Module.End ℝ ↥B.bareSpace := A' - B.weightedAvg
  have hD0 : B.IsDirichletLap D0 := by
    refine ⟨fun f g => ?_, fun f => ?_⟩
    · change B.bareInner ((A' f - B.weightedAvg f : ↥B.bareSpace) : D.BareSite → ℝ) g =
        B.bareInner f ((A' g - B.weightedAvg g : ↥B.bareSpace) : D.BareSite → ℝ)
      simp only [Submodule.coe_sub]
      rw [bareInner_sub_left, bareInner_sub_right, hA'sym, hwa.2]
    · change B.bareInner f ((A' f - B.weightedAvg f : ↥B.bareSpace) :
        D.BareSite → ℝ) = _
      simp only [Submodule.coe_sub]
      rw [bareInner_sub_right, hform]
      ring
  have hspec : B.IsDirichletLap B.dirichletLap := Classical.epsilon_spec ⟨D0, hD0⟩
  have hΔ : B.dirichletLap = D0 :=
    eq_of_quadForm_eq B _ _ hspec.1 hD0.1 fun f => by rw [hspec.2, hD0.2]
  have hLap : B.weightedLap = A' := by
    unfold SeparatedChain.weightedLap
    rw [hΔ]
    change A' - B.weightedAvg + B.weightedAvg = A'
    exact sub_add_cancel A' B.weightedAvg
  have h1 : A' * G' = 1 := by
    apply LinearMap.ext
    intro f
    rw [Module.End.mul_apply, hA', hG', e.symm_apply_apply, hAG, e.apply_symm_apply]
    rfl
  have h2 : G' * A' = 1 := by
    apply LinearMap.ext
    intro f
    rw [Module.End.mul_apply, hA', hG', e.symm_apply_apply, hGA, e.apply_symm_apply]
    rfl
  let u : (Module.End ℝ ↥B.bareSpace)ˣ := ⟨A', G', h1, h2⟩
  have hGreen : B.greenOp = G' := by
    unfold SeparatedChain.greenOp
    rw [hLap]
    exact Ring.inverse_unit u
  refine ⟨⟨hU, fun b hb => Or.inl hb.1, Subset.rfl⟩, hH, fun f => ?_, fun f g => ?_, fun f hf => ?_,
    ?_, fun f => ?_, ?_, fun w => ?_⟩
  · rw [hLap, hincl, hincl, hA', e.symm_apply_apply]
  · rw [hLap]
    exact hA'sym f g
  · rw [hLap, hA', hecoe]
    have hne : e.symm f ≠ 0 := fun h => hf (by simpa using h)
    have h := hpos (e.symm f) hne
    rw [hescoe] at h
    exact h
  · rw [hLap]
    exact ⟨u, rfl⟩
  · rw [hGreen, hincl, hincl, hG', e.symm_apply_apply]
  · rw [eq_top_iff]
    intro w _ y hy
    exact absurd (by rw [hsites]; exact y.2) hy
  · rw [hnr w (e.symm (B.avgOpAdjoint w)) (hescoe _)]
    unfold SeparatedChain.avgGreenSq
    rw [hGreen]
    change B.avgOp _ = B.avgOp ((G' * G') (B.avgOpAdjoint w))
    congr 1
end AdmissiblePairOps
open GivenChainGeneral in
theorem admissiblePairOperators_of
    (hGiven : GivenChainGeneralFacts)
    (hOps : AvgAndMatrixFacts)
    (hOne : UniqueAdmissibleFormOpStatement)
    (hCoer : CoercivityWeightedBounds)
    (hAvg : BlockUnionAveragingStatement)
    (hBlock : BlockIndicatorOnBlockUnionStatement) :
    AdmissiblePairOperators := by
  intro C
  obtain ⟨hrel, hwa, hbasis, -⟩ := hOps C
  have hcubes : ShellsAndCubes C.chain := (hGiven C).2.2.1
  have hb : BlockPartition C.chain := (hGiven C).2.2.2.2.1
  constructor
  · intro W 𝔟 hpair
    have hW := hpair.1
    obtain ⟨hkeep, hnr⟩ := hAvg C.data C.chain W hW
    exact AdmissiblePairOps.pairOperatorFacts C.chain W 𝔟
      (hCoer C.data C.chain W 𝔟 hpair).1 hkeep (hnr 𝔟 hpair) hrel hbasis
      (fun y hy => (hBlock C.data C.chain W hW y hy).2.2)
  · have hsites : C.chain.sitesIn (C.chain.stage 0) = C.chain.allSites := by
      have h := hb.sitesIn_iUnion C.chain.allSites Subset.rfl
      rw [hcubes.iUnion_siteCube_eq] at h
      exact h.symm
    have hU : C.chain.IsBlockUnion (C.chain.stage 0) := by
      obtain ⟨x, hx⟩ := C.stage_zero_nonempty
      rw [← hcubes.iUnion_siteCube_eq] at hx
      simp only [mem_iUnion] at hx
      obtain ⟨y, hy, -⟩ := hx
      exact ⟨C.chain.allSites, ⟨y, hy⟩, Subset.rfl, hcubes.iUnion_siteCube_eq.symm⟩
    have hadm : C.chain.IsAdmissiblePair (C.chain.stage 0) C.chain.initialBonds :=
      ⟨hU, fun b hb => Or.inl hb.1, Subset.rfl⟩
    obtain ⟨-, hnr⟩ := hAvg C.data C.chain _ hU
    exact AdmissiblePairOps.initialPairFacts C.chain hsites hU
      (Classical.epsilon_spec (hOne C.data C.chain _ _ hU).exists)
      (hCoer C.data C.chain _ _ hadm).1 (hnr _ hadm) hwa
end YangMills.Construction.Weighted
end
