import YangMills.Construction.ColdStepAtMirrorFrames.LimitFormOfAColdExpansionProof
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeThroughAFieldMapProof
import YangMills.Construction.ColdStepAtMirrorFrames.SmallUnitsAndTheirLogarithms
import YangMills.Construction.LawByMomentsOfTheFlow.FormOfAnInvariantFunction
import YangMills.Construction.ResponseInTheExpansion.ColdFunctionsOnAMirror
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.MomentLaw.InvariantFunctionForm
open BlockAverages hiding adjointAction unitStep
open TorusFields ColdStepAtMirrorFrames
section Calculus
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
private theorem fderiv_comp_clm_zero {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (T : E' →L[ℝ] E) :
    fderiv ℝ (f ∘ T) 0 = (fderiv ℝ f 0).comp T := by
  have hd : HasFDerivAt f (fderiv ℝ f 0) (T 0) := by
    rw [map_zero]
    exact (hf.differentiableAt (by norm_num)).hasFDerivAt
  exact (hd.comp 0 T.hasFDerivAt).fderiv
private theorem fderiv_fderiv_comp_clm_zero {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (T : E' →L[ℝ] E) (v w : E') :
    fderiv ℝ (fderiv ℝ (f ∘ T)) 0 v w = fderiv ℝ (fderiv ℝ f) 0 (T v) (T w) := by
  have hev : ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hT : Filter.Tendsto T (𝓝 0) (𝓝 0) := by
    simpa using T.continuous.tendsto 0
  have heq : fderiv ℝ (f ∘ T) =ᶠ[𝓝 0] fun σ => (fderiv ℝ f (T σ)).comp T := by
    filter_upwards [hT.eventually hev] with σ hσ
    exact (hσ.hasFDerivAt.comp σ T.hasFDerivAt).fderiv
  have hG : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) (T 0) := by
    rw [map_zero]
    exact hG.hasFDerivAt
  have hcomp : HasFDerivAt (fun σ => fderiv ℝ f (T σ)) ((fderiv ℝ (fderiv ℝ f) 0).comp T) 0 :=
    hG'.comp 0 T.hasFDerivAt
  have hpost := ((ContinuousLinearMap.compL ℝ E' E ℝ).flip T).hasFDerivAt.comp 0 hcomp
  rw [heq.fderiv_eq]
  have hfd : fderiv ℝ (fun σ => (fderiv ℝ f (T σ)).comp T) 0 = _ := hpost.fderiv
  rw [hfd]
  rfl
private theorem hasDerivAt_fderiv_along_line {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (δ v : E) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (s • δ) v) (fderiv ℝ (fderiv ℝ f) 0 δ v) 0 := by
  have hG : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) (0 : E) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hap : HasFDerivAt (fun L : E →L[ℝ] ℝ => L v) (ContinuousLinearMap.apply ℝ ℝ v)
      (fderiv ℝ f 0) := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt
  have hev : HasFDerivAt (fun y => fderiv ℝ f y v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ f) 0)) ((0 : ℝ) • δ) := by
    rw [zero_smul]
    exact hap.comp (0 : E) hG
  have hs : HasDerivAt (fun s : ℝ => s • δ) δ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const δ
  exact hev.comp_hasDerivAt (0 : ℝ) hs
end Calculus
section Basis
private def mkQuat (a b c d : ℝ) : ℍ[ℝ] := ⟨a, b, c, d⟩
@[simp] private theorem mkQuat_re (a b c d : ℝ) : (mkQuat a b c d).re = a := rfl
@[simp] private theorem mkQuat_imI (a b c d : ℝ) : (mkQuat a b c d).imI = b := rfl
@[simp] private theorem mkQuat_imJ (a b c d : ℝ) : (mkQuat a b c d).imJ = c := rfl
@[simp] private theorem mkQuat_imK (a b c d : ℝ) : (mkQuat a b c d).imK = d := rfl
private def basisVec (e : Fin 3) : imaginaryQuaternions :=
  ⟨mkQuat 0 (if e = 0 then 1 else 0) (if e = 1 then 1 else 0) (if e = 2 then 1 else 0), rfl⟩
@[simp] private theorem basisVec_coe (e : Fin 3) : (basisVec e : ℍ[ℝ]) =
    mkQuat 0 (if e = 0 then 1 else 0) (if e = 1 then 1 else 0) (if e = 2 then 1 else 0) := rfl
private theorem sum_imaginaryComponent_smul (w : imaginaryQuaternions) :
    ∑ e, imaginaryComponent e w • basisVec e = w := by
  apply Subtype.ext
  have hre : (w : ℍ[ℝ]).re = 0 := w.2
  ext <;> simp [Fin.sum_univ_three, imaginaryComponent, hre]
private theorem unitGenerator_eq_basisVec : WeightedResponses.unitGenerator = basisVec 0 := by
  apply Subtype.ext
  show (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) = _
  ext <;> simp
private def coordCLM (e : Fin 3) : imaginaryQuaternions →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := imaginaryComponent e
      map_add' := by
        intro a b
        fin_cases e <;> simp [imaginaryComponent]
      map_smul' := by
        intro r a
        fin_cases e <;> simp [imaginaryComponent] }
end Basis
section Fields
variable {n : ℕ} [NeZero n]
private def expOfForm (A : TorusBond n → imaginaryQuaternions) : TorusField n :=
  fun x i => expUnit (A (x, i))
private def pullback (ψ : TorusField n → ℝ) : (TorusBond n → imaginaryQuaternions) → ℝ :=
  fun A => ψ (expOfForm A)
private def placeCLM {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    (Fin k → ℝ) →L[ℝ] (TorusBond n → imaginaryQuaternions) :=
  ContinuousLinearMap.pi fun b =>
    ∑ l, if c l = b then (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (X l) else 0
private theorem placeCLM_apply {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (b : TorusBond n) :
    placeCLM c X σ b = ∑ l, if c l = b then σ l • X l else 0 := by
  simp only [placeCLM, ContinuousLinearMap.coe_pi', _root_.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
private theorem perturb_trivialField {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) :
    perturb c X σ (trivialField n) = expOfForm (placeCLM c X σ) := by
  funext x i
  show expUnit (∑ l, if c l = (x, i) then σ l • X l else 0) * 1 = expUnit (placeCLM c X σ (x, i))
  rw [mul_one, placeCLM_apply]
private theorem placeCLM_single {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (l : Fin k) :
    placeCLM c X (Pi.single l 1) = Pi.single (c l) (X l) := by
  funext b
  rw [placeCLM_apply, Finset.sum_eq_single l]
  · by_cases h : c l = b
    · subst h
      simp
    · have h' : b ≠ c l := fun e => h e.symm
      simp [h, h']
  · intro l' _ hne
    simp [hne]
  · simp
private theorem pullback_contDiffAt (ψ : TorusField n → ℝ)
    (hC : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => ψ (perturb c X σ (trivialField n))) 0) :
    ContDiffAt ℝ 2 (pullback ψ) 0 := by apply _root_.YangMills.DeltaSharedProofs.p502251 <;> assumption
private theorem mixedDeriv_one_eq (ψ : TorusField n → ℝ) (hf : ContDiffAt ℝ 2 (pullback ψ) 0)
    (b : TorusBond n) (X : imaginaryQuaternions) :
    mixedDeriv ψ (trivialField n) ![b] ![X] = fderiv ℝ (pullback ψ) 0 (Pi.single b X) := by
  unfold mixedDeriv
  have he : (fun σ : Fin 1 → ℝ => ψ (perturb ![b] ![X] σ (trivialField n))) =
      pullback ψ ∘ placeCLM ![b] ![X] := by
    funext σ
    simp only [pullback, Function.comp, perturb_trivialField]
  rw [iteratedFDeriv_one_apply, he, fderiv_comp_clm_zero hf]
  simp [placeCLM_single]
private theorem mixedDeriv_two_eq (ψ : TorusField n → ℝ) (hf : ContDiffAt ℝ 2 (pullback ψ) 0)
    (b b' : TorusBond n) (X X' : imaginaryQuaternions) :
    mixedDeriv ψ (trivialField n) ![b, b'] ![X, X'] =
      fderiv ℝ (fderiv ℝ (pullback ψ)) 0 (Pi.single b X) (Pi.single b' X') := by
  unfold mixedDeriv
  have he : (fun σ : Fin 2 → ℝ => ψ (perturb ![b, b'] ![X, X'] σ (trivialField n))) =
      pullback ψ ∘ placeCLM ![b, b'] ![X, X'] := by
    funext σ
    simp only [pullback, Function.comp, perturb_trivialField]
  rw [iteratedFDeriv_two_apply, he, fderiv_fderiv_comp_clm_zero hf]
  simp [placeCLM_single]
private def adjointCLM (u : UnitQuaternion) : imaginaryQuaternions →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u
      map_add' := Adjoint.adjointAction_add u
      map_smul' := fun r X => Adjoint.adjointAction_smul u r X }
private def rotateCLM (u : UnitQuaternion) :
    (TorusBond n → imaginaryQuaternions) →L[ℝ] (TorusBond n → imaginaryQuaternions) :=
  ContinuousLinearMap.pi fun b => (adjointCLM u).comp (ContinuousLinearMap.proj b)
private theorem rotateCLM_apply (u : UnitQuaternion) (A : TorusBond n → imaginaryQuaternions) (b : TorusBond n) :
    rotateCLM u A b = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u (A b) := rfl
private theorem rotateCLM_single (u : UnitQuaternion) (b : TorusBond n) (X : imaginaryQuaternions) :
    rotateCLM u (Pi.single b X) = Pi.single b (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u X) := by
  funext c
  rw [rotateCLM_apply]
  by_cases h : c = b
  · subst h
    simp
  · simp [h, Adjoint.adjointAction_zero]
private theorem gaugeTransform_const (u : UnitQuaternion) (A : TorusBond n → imaginaryQuaternions) :
    gaugeTransform (fun _ => u) (expOfForm A) = expOfForm (rotateCLM u A) := by
  funext x i
  show u * expUnit (A (x, i)) * u⁻¹ = expUnit (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u (A (x, i)))
  rw [Adjoint.expUnit_adjointAction]
private theorem eventually_isCold {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ A in 𝓝 (0 : TorusBond n → imaginaryQuaternions), IsCold ε (expOfForm A) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondVariation.eventually_isCold_fieldOfLogs <;> assumption
private theorem pullback_rotate_eventuallyEq {ψ : TorusField n → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ W : TorusField n, IsCold ε W → ∀ g : TorusSite n → UnitQuaternion, ψ (gaugeTransform g W) = ψ W)
    (u : UnitQuaternion) :
    pullback ψ ∘ rotateCLM u =ᶠ[𝓝 0] pullback ψ := by
  filter_upwards [eventually_isCold hε] with A hA
  show ψ (expOfForm (rotateCLM u A)) = ψ (expOfForm A)
  rw [← gaugeTransform_const]
  exact hg _ hA _
private theorem fderiv_pullback_rotate {ψ : TorusField n → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ W : TorusField n, IsCold ε W → ∀ g : TorusSite n → UnitQuaternion, ψ (gaugeTransform g W) = ψ W)
    (hf : ContDiffAt ℝ 2 (pullback ψ) 0) (u : UnitQuaternion) (A : TorusBond n → imaginaryQuaternions) :
    fderiv ℝ (pullback ψ) 0 (rotateCLM u A) = fderiv ℝ (pullback ψ) 0 A := by
  have h := fderiv_comp_clm_zero hf (rotateCLM u)
  rw [(pullback_rotate_eventuallyEq hε hg u).fderiv_eq] at h
  exact (DFunLike.congr_fun h A).symm
private theorem fderiv_fderiv_pullback_rotate {ψ : TorusField n → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ W : TorusField n, IsCold ε W → ∀ g : TorusSite n → UnitQuaternion, ψ (gaugeTransform g W) = ψ W)
    (hf : ContDiffAt ℝ 2 (pullback ψ) 0) (u : UnitQuaternion) (A A' : TorusBond n → imaginaryQuaternions) :
    fderiv ℝ (fderiv ℝ (pullback ψ)) 0 (rotateCLM u A) (rotateCLM u A') =
      fderiv ℝ (fderiv ℝ (pullback ψ)) 0 A A' := by
  rw [← fderiv_fderiv_comp_clm_zero hf (rotateCLM u),
    (pullback_rotate_eventuallyEq hε hg u).fderiv.fderiv_eq]
end Fields
section Invariance
private def unitI : UnitQuaternion := ⟨mkQuat 0 1 0 0, by
  rw [Unitary.mem_iff]
  constructor <;> ext <;> simp⟩
private def unitJ : UnitQuaternion := ⟨mkQuat 0 0 1 0, by
  rw [Unitary.mem_iff]
  constructor <;> ext <;> simp⟩
private def unitW : UnitQuaternion := ⟨mkQuat (1 / 2) (1 / 2) (1 / 2) (1 / 2), by
  rw [Unitary.mem_iff]
  constructor <;> ext <;> simp <;> norm_num⟩
@[simp] private theorem unitI_coe : (unitI : ℍ[ℝ]) = mkQuat 0 1 0 0 := rfl
@[simp] private theorem unitJ_coe : (unitJ : ℍ[ℝ]) = mkQuat 0 0 1 0 := rfl
@[simp] private theorem unitW_coe : (unitW : ℍ[ℝ]) = mkQuat (1 / 2) (1 / 2) (1 / 2) (1 / 2) := rfl
private theorem adjointAction_coe (u : UnitQuaternion) (X : imaginaryQuaternions) :
    (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u X : ℍ[ℝ]) = (u : ℍ[ℝ]) * (X : ℍ[ℝ]) * star (u : ℍ[ℝ]) := rfl
private theorem adjointAction_unitI_zero : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitI (basisVec 0) = basisVec 0 := by
  apply Subtype.ext
  rw [adjointAction_coe]
  ext <;> simp
private theorem adjointAction_unitI_one : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitI (basisVec 1) = -basisVec 1 := by
  apply Subtype.ext
  rw [adjointAction_coe]
  ext <;> simp
private theorem adjointAction_unitI_two : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitI (basisVec 2) = -basisVec 2 := by
  apply Subtype.ext
  rw [adjointAction_coe]
  ext <;> simp
private theorem adjointAction_unitJ_one : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitJ (basisVec 1) = basisVec 1 := by
  apply Subtype.ext
  rw [adjointAction_coe]
  ext <;> simp
private theorem adjointAction_unitJ_two : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitJ (basisVec 2) = -basisVec 2 := by
  apply Subtype.ext
  rw [adjointAction_coe]
  ext <;> simp
private theorem adjointAction_unitW_zero : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitW (basisVec 0) = basisVec 1 := by
  apply Subtype.ext
  rw [adjointAction_coe]
  ext <;> simp <;> norm_num
private theorem adjointAction_unitW_one : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitW (basisVec 1) = basisVec 2 := by
  apply Subtype.ext
  rw [adjointAction_coe]
  ext <;> simp <;> norm_num
private theorem invariant_bilinear_eq (B : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions →ₗ[ℝ] ℝ)
    (hB : ∀ (u : UnitQuaternion) (X X' : imaginaryQuaternions),
      B (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u X) (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u X') = B X X')
    (X X' : imaginaryQuaternions) :
    B X X' = (∑ e : Fin 3, imaginaryComponent e X * imaginaryComponent e X') *
      B WeightedResponses.unitGenerator WeightedResponses.unitGenerator := by
  have h01 : B (basisVec 0) (basisVec 1) = 0 := by
    have h := hB unitI (basisVec 0) (basisVec 1)
    rw [adjointAction_unitI_zero, adjointAction_unitI_one, map_neg] at h
    linarith
  have h02 : B (basisVec 0) (basisVec 2) = 0 := by
    have h := hB unitI (basisVec 0) (basisVec 2)
    rw [adjointAction_unitI_zero, adjointAction_unitI_two, map_neg] at h
    linarith
  have h10 : B (basisVec 1) (basisVec 0) = 0 := by
    have h := hB unitI (basisVec 1) (basisVec 0)
    rw [adjointAction_unitI_zero, adjointAction_unitI_one, map_neg, LinearMap.neg_apply] at h
    linarith
  have h20 : B (basisVec 2) (basisVec 0) = 0 := by
    have h := hB unitI (basisVec 2) (basisVec 0)
    rw [adjointAction_unitI_zero, adjointAction_unitI_two, map_neg, LinearMap.neg_apply] at h
    linarith
  have h12 : B (basisVec 1) (basisVec 2) = 0 := by
    have h := hB unitJ (basisVec 1) (basisVec 2)
    rw [adjointAction_unitJ_one, adjointAction_unitJ_two, map_neg] at h
    linarith
  have h21 : B (basisVec 2) (basisVec 1) = 0 := by
    have h := hB unitJ (basisVec 2) (basisVec 1)
    rw [adjointAction_unitJ_one, adjointAction_unitJ_two, map_neg, LinearMap.neg_apply] at h
    linarith
  have hd1 : B (basisVec 1) (basisVec 1) = B (basisVec 0) (basisVec 0) := by
    have h := hB unitW (basisVec 0) (basisVec 0)
    rwa [adjointAction_unitW_zero] at h
  have hd2 : B (basisVec 2) (basisVec 2) = B (basisVec 1) (basisVec 1) := by
    have h := hB unitW (basisVec 1) (basisVec 1)
    rwa [adjointAction_unitW_one] at h
  conv_lhs => rw [← sum_imaginaryComponent_smul X, ← sum_imaginaryComponent_smul X']
  rw [unitGenerator_eq_basisVec]
  simp only [Fin.sum_univ_three, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    h01, h02, h10, h20, h12, h21, hd2, hd1]
  ring
end Invariance
section Gradients
variable {n : ℕ} [NeZero n]
private def abelianForm (a : TorusBond n → ℝ) : TorusBond n → imaginaryQuaternions :=
  fun b => a b • WeightedResponses.unitGenerator
private theorem inv_expUnit_smul (r : ℝ) (D : imaginaryQuaternions) :
    (expUnit (r • D))⁻¹ = expUnit ((-r) • D) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← SmallUnits.expUnit_add_smul, add_neg_cancel, zero_smul]
  exact SmallUnits.expUnit_zero
private theorem gaugeTransform_abelianForm (t : ℝ) (φ : TorusSite n → ℝ) (a : TorusBond n → ℝ) :
    gaugeTransform (fun x => expUnit ((t * φ x) • WeightedResponses.unitGenerator)) (expOfForm (abelianForm a)) =
      expOfForm (abelianForm fun b => a b - t * latticeGradient φ b) := by
  funext x i
  show expUnit ((t * φ x) • WeightedResponses.unitGenerator) *
      expUnit (a (x, i) • WeightedResponses.unitGenerator) *
      (expUnit ((t * φ (x + unitStep n i)) • WeightedResponses.unitGenerator))⁻¹ =
    expUnit ((a (x, i) - t * (φ (x + unitStep n i) - φ x)) • WeightedResponses.unitGenerator)
  rw [inv_expUnit_smul, ← SmallUnits.expUnit_add_smul, ← SmallUnits.expUnit_add_smul]
  congr 2
  ring
private theorem fderiv_fderiv_single_gradient_eq_zero {ψ : TorusField n → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ W : TorusField n, IsCold ε W → ∀ g : TorusSite n → UnitQuaternion, ψ (gaugeTransform g W) = ψ W)
    (hf : ContDiffAt ℝ 2 (pullback ψ) 0) (φ : TorusSite n → ℝ) (b' : TorusBond n) :
    fderiv ℝ (fderiv ℝ (pullback ψ)) 0 (Pi.single b' WeightedResponses.unitGenerator)
      (abelianForm (latticeGradient φ)) = 0 := by
  set δ : TorusBond n → imaginaryQuaternions := Pi.single b' WeightedResponses.unitGenerator with hδ
  set v : TorusBond n → imaginaryQuaternions := abelianForm (latticeGradient φ) with hv
  have hline : ∀ s : ℝ, s • δ = abelianForm fun b => s * (Pi.single b' (1 : ℝ) : TorusBond n → ℝ) b := by
    intro s
    funext b
    by_cases h : b = b'
    · subst h
      simp [hδ, abelianForm]
    · simp [hδ, abelianForm, h]
  have hconst : ∀ s : ℝ, IsCold ε (expOfForm (s • δ)) → ∀ t : ℝ,
      pullback ψ (s • δ + t • v) = pullback ψ (s • δ) := by
    intro s hs t
    have hsum : s • δ + t • v =
        abelianForm fun b => s * (Pi.single b' (1 : ℝ) : TorusBond n → ℝ) b - (-t) * latticeGradient φ b := by
      rw [hline s]
      funext b
      simp only [hv, abelianForm, Pi.add_apply, Pi.smul_apply, smul_smul, ← add_smul]
      congr 1
      ring
    show ψ (expOfForm (s • δ + t • v)) = ψ (expOfForm (s • δ))
    rw [hsum, ← gaugeTransform_abelianForm, ← hline s]
    exact hg _ hs _
  have hT : Filter.Tendsto (fun s : ℝ => s • δ) (𝓝 0) (𝓝 0) := by
    have h : Continuous fun s : ℝ => s • δ := by fun_prop
    simpa using h.tendsto 0
  have hdiff : ∀ᶠ y in 𝓝 (0 : TorusBond n → imaginaryQuaternions), DifferentiableAt ℝ (pullback ψ) y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hzero : (fun s : ℝ => fderiv ℝ (pullback ψ) (s • δ) v) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    filter_upwards [hT.eventually (eventually_isCold hε), hT.eventually hdiff] with s h1 h2
    have hl : HasDerivAt (fun t : ℝ => pullback ψ (s • δ + t • v)) (fderiv ℝ (pullback ψ) (s • δ) v) 0 :=
      h2.hasFDerivAt.hasLineDerivAt v
    have he : (fun t : ℝ => pullback ψ (s • δ + t • v)) = fun _ => pullback ψ (s • δ) :=
      funext (hconst s h1)
    rw [he] at hl
    exact hl.unique (hasDerivAt_const _ _)
  have h2 := hasDerivAt_fderiv_along_line hf δ v
  have h3 : HasDerivAt (fun s : ℝ => fderiv ℝ (pullback ψ) (s • δ) v) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero
  exact h2.unique h3
private theorem abelianForm_eq_sum (a : TorusBond n → ℝ) :
    abelianForm a = ∑ b, a b • (Pi.single b WeightedResponses.unitGenerator : TorusBond n → imaginaryQuaternions) := by
  funext c
  simp [abelianForm, Finset.sum_apply, Pi.single_apply]
end Gradients
theorem invariantFunctionFormStatement_holds : invariantFunctionFormStatement := by
  intro n _ ψ ε hε hg hC
  have hf := pullback_contDiffAt ψ hC
  have hsym : ∀ A A' : TorusBond n → imaginaryQuaternions,
      fderiv ℝ (fderiv ℝ (pullback ψ)) 0 A A' = fderiv ℝ (fderiv ℝ (pullback ψ)) 0 A' A := by
    intro A A'
    exact (hf.isSymmSndFDerivAt (by simp)).eq A A'
  set D := fderiv ℝ (fderiv ℝ (pullback ψ)) 0 with hD
  let q : BondBilinear n := fun b b' =>
    D (Pi.single b WeightedResponses.unitGenerator) (Pi.single b' WeightedResponses.unitGenerator)
  have hq : ∀ b b', q b b' = q b' b := fun b b' => hsym _ _
  have hk : ∀ (φ : TorusSite n → ℝ) (b : TorusBond n), ∑ b', q b b' * latticeGradient φ b' = 0 := by
    intro φ b
    have h := fderiv_fderiv_single_gradient_eq_zero hε hg hf φ b
    rw [abelianForm_eq_sum, map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    rw [← h]
    exact Finset.sum_congr rfl fun b' _ => mul_comm _ _
  refine ⟨?_, q, hq, ?_, ?_⟩
  · intro b X
    rw [mixedDeriv_one_eq ψ hf]
    obtain ⟨u, hu⟩ := ResponseInTheExpansion.ColdMirrorFunctionals.exists_adjointAction_eq_neg X
    have h := fderiv_pullback_rotate hε hg hf u (Pi.single b X)
    rw [rotateCLM_single, hu, Pi.single_neg, map_neg] at h
    linarith
  · intro φ A
    have h2 : bilinearEval q A (latticeGradient φ) = 0 := by
      unfold bilinearEval
      refine Finset.sum_eq_zero fun b _ => ?_
      have : ∑ b', A b * q b b' * latticeGradient φ b' = A b * ∑ b', q b b' * latticeGradient φ b' := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b' _ => mul_assoc _ _ _
      rw [this, hk, mul_zero]
    refine ⟨?_, h2⟩
    have hswap : bilinearEval q (latticeGradient φ) A = bilinearEval q A (latticeGradient φ) := by
      unfold bilinearEval
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      rw [hq b' b]
      ring
    rw [hswap, h2]
  · intro b b' X X'
    rw [mixedDeriv_two_eq ψ hf]
    let B : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions →ₗ[ℝ] ℝ :=
      LinearMap.mk₂ ℝ (fun Y Y' => D (Pi.single b Y) (Pi.single b' Y'))
        (fun Y Z Y' => by simp [Pi.single_add, map_add])
        (fun r Y Y' => by simp [Pi.single_smul, map_smul])
        (fun Y Y' Z' => by simp [Pi.single_add, map_add])
        (fun r Y Y' => by simp [Pi.single_smul, map_smul])
    have hB : ∀ (u : UnitQuaternion) (Y Y' : imaginaryQuaternions),
        B (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u Y) (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u Y') = B Y Y' := by
      intro u Y Y'
      show D (Pi.single b (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u Y)) (Pi.single b' (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u Y')) =
        D (Pi.single b Y) (Pi.single b' Y')
      rw [← rotateCLM_single, ← rotateCLM_single]
      exact fderiv_fderiv_pullback_rotate hε hg hf u _ _
    exact invariant_bilinear_eq B hB X X'
end YangMills.Construction.MomentLaw.InvariantFunctionForm
end
