import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsFollowsABijection
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.TransferOperators.SandwichConditions
noncomputable section
namespace YangMills.Construction.TransferOperators.SandwichRelabel
variable {B B' : Type} [Finite B] [Finite B']
def relabelEquiv (e : B ≃ B') : (B → specialUnitary) ≃ᵐ (B' → specialUnitary) :=
  MeasurableEquiv.piCongrLeft (fun _ => specialUnitary) e
omit [Finite B] [Finite B'] in
theorem relabelEquiv_apply_apply (e : B ≃ B') (x : B → specialUnitary) (a : B) :
    relabelEquiv e x (e a) = x a :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => specialUnitary) e x a
omit [Finite B] [Finite B'] in
theorem relabelEquiv_comp (e : B ≃ B') (w : B' → specialUnitary) : relabelEquiv e (w ∘ e) = w := by
  funext b
  obtain ⟨a, rfl⟩ := e.surjective b
  rw [relabelEquiv_apply_apply]
  rfl
omit [Finite B] [Finite B'] in
theorem comp_relabelEquiv (e : B ≃ B') (x : B → specialUnitary) : relabelEquiv e x ∘ e = x := by
  funext a
  exact relabelEquiv_apply_apply e x a
theorem measurePreserving_relabelEquiv (e : B ≃ B') :
    MeasurePreserving (relabelEquiv e) (haarPi B) (haarPi B') := by
  refine ⟨(relabelEquiv e).measurable, ?_⟩
  unfold haarPi
  exact Measure.infinitePi_map_piCongrLeft (μ := fun _ => haarProb) e
theorem measurePreserving_precomp (e : B ≃ B') :
    MeasurePreserving (fun w : B' → specialUnitary => w ∘ e) (haarPi B') (haarPi B) := by
  have h := (measurePreserving_relabelEquiv e).symm (relabelEquiv e)
  have hfun : ((relabelEquiv e).symm : (B' → specialUnitary) → (B → specialUnitary)) =
      fun w => w ∘ e := by
    funext w
    rw [MeasurableEquiv.symm_apply_eq, relabelEquiv_comp]
  rwa [hfun] at h
def relabelIsometry (e : B ≃ B') : HaarL2 B →ₗᵢ[ℂ] HaarL2 B' :=
  Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_precomp e)
def relabelIsometryInv (e : B ≃ B') : HaarL2 B' →ₗᵢ[ℂ] HaarL2 B :=
  Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_relabelEquiv e)
theorem coeFn_relabelIsometry (e : B ≃ B') (f : HaarL2 B) :
    (relabelIsometry e f : (B' → specialUnitary) → ℂ) =ᵐ[haarPi B']
      fun w => (f : (B → specialUnitary) → ℂ) (w ∘ e) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_precomp e)
theorem coeFn_relabelIsometryInv (e : B ≃ B') (g : HaarL2 B') :
    (relabelIsometryInv e g : (B → specialUnitary) → ℂ) =ᵐ[haarPi B]
      fun x => (g : (B' → specialUnitary) → ℂ) (relabelEquiv e x) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_relabelEquiv e)
theorem relabelIsometry_relabelIsometryInv (e : B ≃ B') (g : HaarL2 B') :
    relabelIsometry e (relabelIsometryInv e g) = g := by
  apply Lp.ext
  have h := (measurePreserving_precomp e).quasiMeasurePreserving.ae_eq_comp
    (coeFn_relabelIsometryInv e g)
  refine (coeFn_relabelIsometry e _).trans (h.trans (Filter.Eventually.of_forall fun w => ?_))
  simp only [Function.comp_apply, relabelEquiv_comp]
theorem relabelIsometryInv_relabelIsometry (e : B ≃ B') (f : HaarL2 B) :
    relabelIsometryInv e (relabelIsometry e f) = f := by
  apply Lp.ext
  have h := (measurePreserving_relabelEquiv e).quasiMeasurePreserving.ae_eq_comp
    (coeFn_relabelIsometry e f)
  refine (coeFn_relabelIsometryInv e _).trans (h.trans (Filter.Eventually.of_forall fun x => ?_))
  simp only [Function.comp_apply, comp_relabelEquiv]
theorem linkRelabel_eq_relabelIsometry (e : B ≃ B') (f : HaarL2 B) :
    linkRelabel e f = relabelIsometry e f := by
  have hm : MemLp (fun w : B' → specialUnitary => (f : (B → specialUnitary) → ℂ) (w ∘ e)) 2
      (haarPi B') := (Lp.memLp f).comp_measurePreserving (measurePreserving_precomp e)
  have hs : linkRelabel e f = hm.toLp _ := dif_pos hm
  rw [hs]
  apply Lp.ext
  exact hm.coeFn_toLp.trans (coeFn_relabelIsometry e f).symm
theorem relabelIsometry_toHaarL2 (e : B ≃ B') (F : (B → specialUnitary) → ℂ) :
    relabelIsometry e (toHaarL2 F) = toHaarL2 fun w => F (w ∘ e) := by
  by_cases hF : MemLp F 2 (haarPi B)
  · have hm : MemLp (fun w : B' → specialUnitary => F (w ∘ e)) 2 (haarPi B') :=
      hF.comp_measurePreserving (measurePreserving_precomp e)
    have h1 : toHaarL2 F = hF.toLp F := dif_pos hF
    have h2 : toHaarL2 (fun w : B' → specialUnitary => F (w ∘ e)) = hm.toLp _ := dif_pos hm
    rw [h1, h2]
    apply Lp.ext
    have h := (measurePreserving_precomp e).quasiMeasurePreserving.ae_eq_comp hF.coeFn_toLp
    exact (coeFn_relabelIsometry e _).trans (h.trans hm.coeFn_toLp.symm)
  · have hn : ¬MemLp (fun w : B' → specialUnitary => F (w ∘ e)) 2 (haarPi B') := by
      intro hm
      apply hF
      have h := hm.comp_measurePreserving (measurePreserving_relabelEquiv e)
      have hfun : (fun w : B' → specialUnitary => F (w ∘ e)) ∘ relabelEquiv e = F := by
        funext x
        simp only [Function.comp_apply, comp_relabelEquiv]
      rwa [hfun] at h
    have h1 : toHaarL2 F = 0 := dif_neg hF
    have h2 : toHaarL2 (fun w : B' → specialUnitary => F (w ∘ e)) = 0 := dif_neg hn
    rw [h1, h2, map_zero]
omit [Finite B] [Finite B'] in
theorem sqrtLinkKernel_comp (β : ℝ) (e : B ≃ B') (w u : B' → specialUnitary) :
    sqrtLinkKernel β (w ∘ e) (u ∘ e) = sqrtLinkKernel β w u :=
  finprod_comp_equiv e (f := fun b => sqrtKernel β (w b) (u b))
theorem relabelIsometry_sqrtLinkKernelSlice (β : ℝ) (e : B ≃ B') (u : B' → specialUnitary) :
    relabelIsometry e (sqrtLinkKernelSlice β (u ∘ e)) = sqrtLinkKernelSlice β u := by
  unfold sqrtLinkKernelSlice
  rw [relabelIsometry_toHaarL2]
  simp only [sqrtLinkKernel_comp]
theorem invFun_linkRelabel (e : B ≃ B') (g : HaarL2 B') :
    Function.invFun (linkRelabel e) g = relabelIsometryInv e g := by
  have hinj : Function.Injective (linkRelabel (e : B → B')) := by
    intro f f' h
    rw [linkRelabel_eq_relabelIsometry, linkRelabel_eq_relabelIsometry] at h
    exact (relabelIsometry e).injective h
  have hl := Function.leftInverse_invFun hinj (relabelIsometryInv e g)
  rwa [linkRelabel_eq_relabelIsometry, relabelIsometry_relabelIsometryInv] at hl
theorem linkRelabelOp_apply (e : B ≃ B') (X : HaarL2 B →L[ℂ] HaarL2 B) (g : HaarL2 B') :
    linkRelabelOp e X g = relabelIsometry e (X (relabelIsometryInv e g)) := by
  have hex : ∃ A : HaarL2 B' →L[ℂ] HaarL2 B',
      ∀ g, A g = linkRelabel e (X (Function.invFun (linkRelabel e) g)) := by
    refine ⟨(relabelIsometry e).toContinuousLinearMap ∘L X ∘L
      (relabelIsometryInv e).toContinuousLinearMap, fun g => ?_⟩
    rw [invFun_linkRelabel, linkRelabel_eq_relabelIsometry]
    rfl
  have hspec := Classical.epsilon_spec hex g
  have hdef : linkRelabelOp e X = Classical.epsilon fun A : HaarL2 B' →L[ℂ] HaarL2 B' =>
      ∀ g, A g = linkRelabel e (X (Function.invFun (linkRelabel e) g)) := rfl
  rw [hdef, hspec, invFun_linkRelabel, linkRelabel_eq_relabelIsometry]
theorem norm_linkRelabelOp (e : B ≃ B') (X : HaarL2 B →L[ℂ] HaarL2 B) :
    ‖linkRelabelOp e X‖ = ‖X‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun g => ?_
    rw [linkRelabelOp_apply, LinearIsometry.norm_map]
    simpa only [LinearIsometry.norm_map] using X.le_opNorm (relabelIsometryInv e g)
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
    have h := (linkRelabelOp e X).le_opNorm (relabelIsometry e f)
    rw [linkRelabelOp_apply, relabelIsometryInv_relabelIsometry, LinearIsometry.norm_map,
      LinearIsometry.norm_map] at h
    exact h
theorem kernelRelabelEquivariant_of_bijective (β : ℝ) (σ : B → B') (X : HaarL2 B →L[ℂ] HaarL2 B)
    (hσ : Function.Bijective σ) : KernelRelabelEquivariant β σ X := by
  obtain ⟨e, rfl⟩ : ∃ e : B ≃ B', (e : B → B') = σ := ⟨Equiv.ofBijective σ hσ, rfl⟩
  refine ⟨fun g => ⟨relabelIsometryInv e g, ?_⟩, fun f g => ?_, fun g => ?_,
    norm_linkRelabelOp e X, fun u u' => ?_⟩
  · rw [linkRelabel_eq_relabelIsometry, relabelIsometry_relabelIsometryInv]
  · rw [linkRelabel_eq_relabelIsometry, linkRelabel_eq_relabelIsometry, LinearIsometry.inner_map_map]
  · rw [linkRelabelOp_apply, invFun_linkRelabel, linkRelabel_eq_relabelIsometry]
  · unfold sqrtKernelSandwich
    rw [← relabelIsometry_sqrtLinkKernelSlice β e u, ← relabelIsometry_sqrtLinkKernelSlice β e u',
      linkRelabelOp_apply, relabelIsometryInv_relabelIsometry, LinearIsometry.inner_map_map]
theorem sandwichKernelRelabelStatement_holds : SandwichKernelRelabelStatement := by
  intro β _ B B' _ _ _ σ X hσ
  exact kernelRelabelEquivariant_of_bijective β σ X hσ
end YangMills.Construction.TransferOperators.SandwichRelabel
end
