import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.CalculusOfLocalTerms
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinatesProof
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrder
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionIsAdmittedProof
import YangMills.Construction.SummableBoundsOfTheFlow.FieldsOfTheTopBetween
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftIsSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftIsUnique
import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import YangMills.Construction.SummableBoundsOfTheFlow.TheHigherDerivativesOfTheDensityOfTheStepProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation Estimates CellCounting SmoothSlices SummableBounds
  TorusComparison FamilyNorms BondCoordinates Topology
namespace Interpolation
namespace BlockExpansionThirdOrder
section Calculus
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem isOpen_setOf_norm_lt (ρ : ℝ) : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.isOpen_ballProduct <;> assumption
abbrev _root_.YangMills.SharedProofs.p5886 := @isOpen_setOf_norm_lt
private theorem abs_apply_le_bondGradNorm (H : BondField ι → ℝ) (b : ι) (η : BondField ι) (e : BondVector) :
    |fderiv ℝ H η (bondVariation b e)| ≤ bondGradNorm H b η * ‖e‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.abs_fderiv_bondVariation_le <;> assumption
private theorem bondGradNorm_le {H : BondField ι → ℝ} {b : ι} {η : BondField ι} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ e, |fderiv ℝ H η (bondVariation b e)| ≤ M * ‖e‖) : bondGradNorm H b η ≤ M := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus.bondGradNorm_le_of_forall <;> assumption
private theorem abs_sub_le_sum_of_bondGradNorm {ρ : ℝ} {H : BondField ι → ℝ} {D : ι → ℝ}
    (hd : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → DifferentiableAt ℝ H η)
    (hg : ∀ (η : BondField ι) (b : ι), (∀ b, ‖η b‖ < ρ) → bondGradNorm H b η ≤ D b)
    {η : BondField ι} (hη : ∀ b, ‖η b‖ < ρ) : |H η - H 0| ≤ ∑ b, D b * ‖η b‖ := by
  have hseg : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ b, ‖(v • η) b‖ < ρ := fun v hv b => by
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hv.1]
    calc v * ‖η b‖ ≤ 1 * ‖η b‖ := mul_le_mul_of_nonneg_right hv.2 (norm_nonneg _)
      _ = ‖η b‖ := one_mul _
      _ < ρ := hη b
  have hsplit : ∀ L : BondField ι →L[ℝ] ℝ, L η = ∑ b, L (bondVariation b (η b)) := fun L => by
    rw [← map_sum]
    congr 1
    exact (Finset.univ_sum_single η).symm
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun v : ℝ => H (v • η))
    (f' := fun v => fderiv ℝ H (v • η) η) (C := ∑ b, D b * ‖η b‖) ?_ ?_
  · simpa [Real.norm_eq_abs] using key
  · intro v hv
    have h1 : HasFDerivAt H (fderiv ℝ H (v • η)) (v • η) := (hd _ (hseg v hv)).hasFDerivAt
    have h2 : HasDerivAt (fun v : ℝ => v • η) η v := by
      simpa using (hasDerivAt_id v).smul_const η
    exact (h1.comp_hasDerivAt v h2).hasDerivWithinAt
  · intro v hv
    have hv' : v ∈ Set.Icc (0 : ℝ) 1 := ⟨hv.1, hv.2.le⟩
    rw [hsplit, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    exact (abs_apply_le_bondGradNorm H b _ _).trans
      (mul_le_mul_of_nonneg_right (hg _ b (hseg v hv')) (norm_nonneg _))
private theorem hasLocalSize_of_bondGradNorm (hSz : localSizeOfQuadraticBoundsStatement) {ρ x lam κ W C h h₁ : ℝ}
    {d : ι → ι → ℝ} {Φ : BondField ι → ℝ} {p : ℝ → ℝ} {dZ : ι → ℝ} {H : BondField ι → ℝ}
    (hρ : 0 < ρ) (hx : 1 ≤ x) (hlam : 0 < lam) (hκ : 0 ≤ κ) (hW : 0 ≤ W) (hp : IsCutoff ρ p)
    (hd : IsPseudoMetricOnBonds d) (hL : HasUniformlyConvexLaw ρ lam x κ C d Φ)
    (hd₂ : ∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W)
    (hsum : ∑ b, Real.exp (-(2 * κ * dZ b)) ≤ W)
    (hC : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) H η)
    (hg : ∀ (η : BondField ι) (b : ι), (∀ b, ‖η b‖ < ρ) →
      bondGradNorm H b η ≤ Real.sqrt x * h₁ * Real.exp (-(2 * κ * dZ b)))
    (hh₁ : 0 ≤ h₁) (hh : (1 + W) * h₁ ≤ h) :
    HasLocalSize ρ (cutoffFactor ρ p) Φ (lpMomentConstant lam W W) x κ h dZ H := by
  have hh₁' : h₁ ≤ h := by nlinarith
  have h0 : 0 ≤ h := hh₁.trans hh₁'
  have hx0 : 0 < x := by linarith
  have hw : ∀ b, 0 ≤ Real.exp (-(2 * κ * dZ b)) := fun b => (Real.exp_pos _).le
  refine hSz ι ρ x lam κ W W C h (H 0) d Φ p dZ (fun b => Real.exp (-(2 * κ * dZ b))) H hρ hx hlam hκ hW hW h0 hp hd hL
    hd₂ hw hsum hC ?_ ?_
  · intro η hη
    have hv := abs_sub_le_sum_of_bondGradNorm (H := H) (fun η hη => (hC η hη).differentiableAt (by simp)) hg hη
    refine hv.trans ?_
    obtain ⟨S, hS⟩ : ∃ S, S = x * ∑ b, Real.exp (-(2 * κ * dZ b)) * ‖η b‖ ^ 2 := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := by
      rw [hS]
      exact mul_nonneg hx0.le (Finset.sum_nonneg fun b _ => mul_nonneg (hw b) (by positivity))
    have hterm : ∀ b, Real.sqrt x * h₁ * Real.exp (-(2 * κ * dZ b)) * ‖η b‖ ≤
        h₁ * (x * (Real.exp (-(2 * κ * dZ b)) * ‖η b‖ ^ 2) + Real.exp (-(2 * κ * dZ b))) := by
      intro b
      have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
      have h1 : Real.sqrt x * ‖η b‖ ≤ x * ‖η b‖ ^ 2 + 1 := by
        nlinarith [sq_nonneg (Real.sqrt x * ‖η b‖ - 1), mul_nonneg (Real.sqrt_nonneg x) (norm_nonneg (η b))]
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hh₁ (hw b))
      nlinarith [h2]
    refine (Finset.sum_le_sum fun b _ => hterm b).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← hS]
    have h1 : h₁ * (S + ∑ b, Real.exp (-(2 * κ * dZ b))) ≤ h₁ * (S + W) :=
      mul_le_mul_of_nonneg_left (by linarith) hh₁
    have h2 : h₁ * (S + W) ≤ (1 + W) * h₁ * (S + 1) := by nlinarith [mul_nonneg hh₁ (mul_nonneg hW hS0), mul_nonneg hh₁ hS0]
    have h3 : (1 + W) * h₁ * (S + 1) ≤ h * (S + 1) := mul_le_mul_of_nonneg_right hh (by linarith)
    linarith
  · intro η b hη
    refine (hg η b hη).trans ?_
    have hS0 : 0 ≤ x * ∑ b, Real.exp (-(2 * κ * dZ b)) * ‖η b‖ ^ 2 :=
      mul_nonneg hx0.le (Finset.sum_nonneg fun b _ => mul_nonneg (hw b) (by positivity))
    have h1 : Real.sqrt x * h₁ * Real.exp (-(2 * κ * dZ b)) ≤ Real.sqrt x * h * Real.exp (-(2 * κ * dZ b)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh₁' (Real.sqrt_nonneg x)) (hw b)
    have h2 : 0 ≤ Real.sqrt x * h * Real.exp (-(2 * κ * dZ b)) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg x) h0) (hw b)
    nlinarith [mul_nonneg h2 hS0]
private theorem bondGradNorm_sum_le {K : Type} {s : Finset K} {Hf : K → BondField ι → ℝ}
    {H : BondField ι → ℝ} {η : BondField ι} (hH : H =ᶠ[𝓝 η] fun ζ => ∑ y ∈ s, Hf y ζ)
    (hd : ∀ y ∈ s, DifferentiableAt ℝ (Hf y) η) (b : ι) :
    bondGradNorm H b η ≤ ∑ y ∈ s, bondGradNorm (Hf y) b η := by
  refine bondGradNorm_le (Finset.sum_nonneg fun y _ => norm_nonneg _) fun e => ?_
  rw [hH.fderiv_eq, fderiv_fun_sum hd, ContinuousLinearMap.sum_apply, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  exact abs_apply_le_bondGradNorm _ b _ e
private theorem partialDeriv_along_field {f : BondField ι → ℝ} {z : BondVector → BondVector} {b : ι} {η : BondField ι}
    (hf : ContDiffAt ℝ 2 f η) (hz : ContDiffAt ℝ 1 z (η b)) :
    ContDiffAt ℝ 1 (fun ζ => bondPartialDeriv f b ζ (z (ζ b))) η ∧
      ∀ v : BondField ι, fderiv ℝ (fun ζ => bondPartialDeriv f b ζ (z (ζ b))) η v =
        fderiv ℝ (fderiv ℝ f) η v (bondVariation b (z (η b))) +
          fderiv ℝ f η (bondVariation b (fderiv ℝ z (η b) (v b))) := by
  set S := ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b with hSdef
  set P := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b with hPdef
  have hf1 : ContDiffAt ℝ 1 (fderiv ℝ f) η := hf.fderiv_right (by norm_num)
  have hP : ContDiffAt ℝ 1 (fun ζ : BondField ι => ζ b) η := P.contDiff.contDiffAt
  have hzP : ContDiffAt ℝ 1 (fun ζ : BondField ι => z (ζ b)) η := ContDiffAt.comp η hz hP
  have hu : ContDiffAt ℝ 1 (fun ζ : BondField ι => S (z (ζ b))) η := S.contDiff.contDiffAt.comp η hzP
  refine ⟨hf1.clm_apply hu, fun v => ?_⟩
  have d1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) η) η := (hf1.differentiableAt (by simp)).hasFDerivAt
  have dz : HasFDerivAt z (fderiv ℝ z (η b)) (P η) := (hz.differentiableAt (by simp)).hasFDerivAt
  have d2 : HasFDerivAt (fun ζ : BondField ι => S (z (ζ b))) (S.comp ((fderiv ℝ z (η b)).comp P)) η :=
    S.hasFDerivAt.comp η (dz.comp η P.hasFDerivAt)
  have d3 := d1.clm_apply d2
  have e : (fun ζ => bondPartialDeriv f b ζ (z (ζ b))) = fun ζ => (fderiv ℝ f ζ) (S (z (ζ b))) := rfl
  rw [e, d3.fderiv]
  simp [bondVariation, hSdef, hPdef, add_comm]
private theorem abs_le_of_homogeneous {f : BondVector → ℝ} (hl : ∀ (r : ℝ) (e : BondVector), f (r • e) = r * f e) {M : ℝ}
    (h : ∀ e, ‖e‖ = 1 → |f e| ≤ M) (e : BondVector) : |f e| ≤ M * ‖e‖ := by
  by_cases he : e = 0
  · have := hl 0 0
    simp [he] at this ⊢
    simp [this]
  · have hr : 0 < ‖e‖ := norm_pos_iff.mpr he
    have hu : ‖‖e‖⁻¹ • e‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
    have e1 : e = ‖e‖ • (‖e‖⁻¹ • e) := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [e1, hl, abs_mul, abs_of_pos hr, ← e1, mul_comm]
    have := h _ hu
    exact mul_le_mul_of_nonneg_right this hr.le
private theorem bondGradNorm_partialDeriv_along_le {f : BondField ι → ℝ} {z : BondVector → BondVector} {b b' : ι}
    {η : BondField ι} {E₁ E₂ Z₀ Dz : ℝ} (hf : ContDiffAt ℝ 2 f η) (hz : ContDiffAt ℝ 1 z (η b))
    (h1 : ∀ e, |fderiv ℝ f η (bondVariation b e)| ≤ E₁ * ‖e‖)
    (h2 : ∀ e e', |fderiv ℝ (fderiv ℝ f) η (bondVariation b' e) (bondVariation b e')| ≤ E₂ * ‖e‖ * ‖e'‖)
    (hZ : ‖z (η b)‖ ≤ Z₀) (hD : ∀ e, ‖fderiv ℝ z (η b) e‖ ≤ Dz * ‖e‖)
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) (hZ₀ : 0 ≤ Z₀) (hDz : 0 ≤ Dz) :
    bondGradNorm (fun ζ => bondPartialDeriv f b ζ (z (ζ b))) b' η ≤ E₂ * Z₀ + (if b' = b then E₁ * Dz else 0) := by
  have hnn : 0 ≤ E₂ * Z₀ + (if b' = b then E₁ * Dz else 0) := by
    split_ifs <;> positivity
  refine bondGradNorm_le hnn fun e => ?_
  rw [(partialDeriv_along_field hf hz).2]
  have t1 : |fderiv ℝ (fderiv ℝ f) η (bondVariation b' e) (bondVariation b (z (η b)))| ≤ E₂ * Z₀ * ‖e‖ := by
    refine (h2 e _).trans ?_
    have := mul_le_mul_of_nonneg_left hZ (mul_nonneg hE₂ (norm_nonneg e))
    nlinarith [this]
  have t2 : |fderiv ℝ f η (bondVariation b (fderiv ℝ z (η b) (bondVariation b' e b)))| ≤
      (if b' = b then E₁ * Dz else 0) * ‖e‖ := by
    by_cases hb : b' = b
    · subst hb
      have e1 : bondVariation b' e b' = e := by simp [bondVariation]
      rw [e1, if_pos rfl]
      refine (h1 _).trans ?_
      have := mul_le_mul_of_nonneg_left (hD e) hE₁
      nlinarith [this]
    · have e1 : bondVariation b' e b = 0 := by simp [bondVariation, Ne.symm hb]
      have e2 : bondVariation b (0 : BondVector) = (0 : BondField ι) := by simp [bondVariation]
      rw [e1, map_zero, e2, map_zero, if_neg hb]
      simp
  refine (abs_add_le _ _).trans ?_
  rw [add_mul]
  exact add_le_add t1 t2
end Calculus
section Frames
variable {F : BlockFrame}
private theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem leftTranslate_bondSpread_empty {j : ℕ} (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions)
    (τ : Fin 0 → ℝ) (V : F.GaugeField j) : leftTranslate (bondSpread c X τ) V = V := by
  funext y i
  simp [leftTranslate, ColdStepAtMirrorFrames.bondSpread, expUnit_zero]
private theorem bondDeriv_empty {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ} (G : F.GaugeField j → E)
    (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p3568 <;> assumption
private def bondMoveCLM {l : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (e : Fin l → BondVector) :
    (Fin l → ℝ) →L[ℝ] StepVariable (finiteCells F) :=
  ∑ i, (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) (b i)).comp
    ((ContinuousLinearMap.toSpanSingleton ℝ (e i)).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin l => ℝ) i))
private theorem bondMoveCLM_apply {l : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (e : Fin l → BondVector)
    (τ : Fin l → ℝ) : bondMoveCLM b e τ = ∑ i, Pi.single (b i) (τ i • e i) := by
  simp only [bondMoveCLM, sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.single_smul]
private theorem bondMoveCLM_single {l : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (e : Fin l → BondVector)
    (i : Fin l) : bondMoveCLM b e (Pi.single i 1) = Pi.single (b i) (e i) := by
  rw [bondMoveCLM_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp
private theorem jointMixedDeriv_eq_iteratedFDeriv (hS : IteratedFDerivSlices)
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top)
    {l : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (e : Fin l → BondVector)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) (hf : ContDiffAt ℝ l (fun ζ => G ζ V) η) :
    jointMixedDeriv G η V b e c X =
      iteratedFDeriv ℝ l (fun ζ => G ζ V) η fun i => Pi.single (b i) (e i) := by
  have h1 : jointDisplacement G η V b e c X = fun τ => (fun ζ => G ζ V) (η + bondMoveCLM b e τ) := by
    funext τ
    simp only [jointDisplacement, displacedPoint, leftTranslate_bondSpread_empty, bondMoveCLM_apply]
    rfl
  have h2 := hS.1 (StepVariable (finiteCells F)) (Fin l → ℝ) (fun ζ => G ζ V) (bondMoveCLM b e) η 0 l
    (fun i => Pi.single i 1) (by simpa using hf)
  unfold jointMixedDeriv
  rw [h1]
  refine h2.trans ?_
  simp only [map_zero, add_zero, bondMoveCLM_single]
abbrev _root_.YangMills.DeltaSharedProofs.p502184 := @jointMixedDeriv_eq_iteratedFDeriv
private theorem fderiv_eq_jointMixedDeriv_one (hS : IteratedFDerivSlices)
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top)
    (b : ↥(chordBonds (finiteCells F))) (e : BondVector) (c : Fin 0 → F.Site F.top × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) (hf : ContDiffAt ℝ 1 (fun ζ => G ζ V) η) :
    fderiv ℝ (fun ζ => G ζ V) η (bondVariation b e) = jointMixedDeriv G η V ![b] ![e] c X := by
  rw [jointMixedDeriv_eq_iteratedFDeriv hS G η V ![b] ![e] c X (by exact_mod_cast hf), iteratedFDeriv_one_apply]
  simp [bondVariation]
private theorem fderiv_fderiv_eq_jointMixedDeriv_two (hS : IteratedFDerivSlices)
    (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top)
    (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector) (c : Fin 0 → F.Site F.top × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) (hf : ContDiffAt ℝ 2 (fun ζ => G ζ V) η) :
    fderiv ℝ (fderiv ℝ fun ζ => G ζ V) η (bondVariation b e) (bondVariation b' e') =
      jointMixedDeriv G η V ![b, b'] ![e, e'] c X := by
  rw [jointMixedDeriv_eq_iteratedFDeriv hS G η V ![b, b'] ![e, e'] c X (by exact_mod_cast hf), iteratedFDeriv_two_apply]
  simp [bondVariation]
private theorem cellSupDist_le_diameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
private theorem cellSupDist_self (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
private theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
private theorem cellSupDist_triangle (x y z : F.Cell) : cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
private theorem isPseudoMetric_cellSupDist :
    IsPseudoMetricOnBonds (fun b b' : ↥(chordBonds (finiteCells F)) =>
      (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ)) :=
  ⟨fun b => by simp [cellSupDist_self], fun b b' => by simp [cellSupDist_comm (enclosingCell b.1.1)],
    fun b b' b'' => by exact_mod_cast cellSupDist_triangle _ _ _⟩
private theorem toImaginary_imaginaryCoords (w : imaginaryQuaternions) : toImaginary (imaginaryCoords w) = w := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_imaginaryCoords <;> assumption
private theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
private theorem norm_imaginaryCoords (w : imaginaryQuaternions) : ‖imaginaryCoords w‖ = ‖w‖ := by
  rw [← norm_toImaginary, toImaginary_imaginaryCoords]
abbrev _root_.YangMills.SharedProofs.p6124 := @norm_imaginaryCoords
private theorem toImaginary_injective {v v' : BondVector} (h : toImaginary v = toImaginary v') : v = v' := by apply _root_.YangMills.Construction.BlockTrees.toImaginary_injective <;> assumption
private def imaginaryCoordsCLM : imaginaryQuaternions →L[ℝ] BondVector :=
  LinearMap.mkContinuous
    { toFun := imaginaryCoords
      map_add' := fun a b => toImaginary_injective (by
        have := toImaginaryCLM.map_add (imaginaryCoords a) (imaginaryCoords b)
        rw [toImaginaryCLM_apply, toImaginaryCLM_apply, toImaginaryCLM_apply, toImaginary_imaginaryCoords,
          toImaginary_imaginaryCoords] at this
        rw [toImaginary_imaginaryCoords, this])
      map_smul' := fun r a => toImaginary_injective (by
        have := toImaginaryCLM.map_smul r (imaginaryCoords a)
        rw [toImaginaryCLM_apply, toImaginaryCLM_apply, toImaginary_imaginaryCoords] at this
        rw [toImaginary_imaginaryCoords, RingHom.id_apply, this]) } 1
    (fun w => by
      show ‖imaginaryCoords w‖ ≤ 1 * ‖w‖
      rw [norm_imaginaryCoords, one_mul])
private theorem imaginaryCoordsCLM_apply (w : imaginaryQuaternions) : imaginaryCoordsCLM w = imaginaryCoords w := rfl
private theorem norm_fderiv_rightTranslation_le {Th' : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions}
    {w₀ X : imaginaryQuaternions} {CT : ℝ}
    (hC : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Th' w₀) (hb : ‖iteratedFDeriv ℝ 1 Th' w₀‖ ≤ CT) (hCT : 0 ≤ CT)
    (hX : ‖X‖ = 1) (v : imaginaryQuaternions) : ‖fderiv ℝ (fun w' => Th' w' X) w₀ v‖ ≤ CT * ‖v‖ := by
  have hd : DifferentiableAt ℝ Th' w₀ := hC.differentiableAt (by simp)
  have e := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const X w₀)).fderiv
  rw [e]
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  have h1 := (fderiv ℝ Th' w₀ v).le_opNorm X
  have h2 : fderiv ℝ Th' w₀ v = iteratedFDeriv ℝ 1 Th' w₀ ![v] := by
    rw [iteratedFDeriv_one_apply]
    simp
  have h3 := (iteratedFDeriv ℝ 1 Th' w₀).le_opNorm ![v]
  have hp : ∏ i : Fin 1, ‖(![v] : Fin 1 → imaginaryQuaternions) i‖ = ‖v‖ := by simp
  rw [hX, mul_one] at h1
  rw [← h2, hp] at h3
  exact h1.trans (h3.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _)))
private theorem topVariationField_congr (hUq : RightTranslationDerivUnique)
    {Th Th₂ : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions}
    (h₁ : ∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (Th w X))
    (h₂ : ∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (Th₂ w X)) {s a ρA : ℝ} {m : ℕ}
    {c : F.Site F.top × Fin 4} {X : imaginaryQuaternions} {b : F.Site F.depth × Fin 4} {u : imaginaryQuaternions}
    {V : F.GaugeField F.top} (hu : ‖interpolatedFrame s a ρA m b V + u‖ < Real.pi) :
    topVariationField Th s a ρA m c X b u V = topVariationField Th₂ s a ρA m c X b u V := by
  unfold topVariationField
  congr 1
  split_ifs
  · exact hUq _ _ _ _ hu (h₁ _ _ hu) (h₂ _ _ hu)
  · rfl
private theorem topVariationField_coords_smooth
    {Th' : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions} {s a ρA κ CT : ℝ} {m : ℕ}
    {V : F.GaugeField F.top} {c : F.Site F.top × Fin 4} {X : imaginaryQuaternions} {b : ↥(chordBonds (finiteCells F))}
    {u₀ : BondVector} (hX : ‖X‖ = 1)
    (hC : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Th' (interpolatedFrame s a ρA m b.1 V + toImaginary u₀))
    (hD : ‖iteratedFDeriv ℝ 1 Th' (interpolatedFrame s a ρA m b.1 V + toImaginary u₀)‖ ≤ CT) (hCT : 0 ≤ CT) :
    ContDiffAt ℝ 1 (fun u => imaginaryCoords (topVariationField (fun w X => Th' w X) s a ρA m c X b.1 (toImaginary u) V)) u₀ ∧
      ∀ e, ‖fderiv ℝ (fun u => imaginaryCoords (topVariationField (fun w X => Th' w X) s a ρA m c X b.1 (toImaginary u) V))
        u₀ e‖ ≤ CT * Real.exp (-(2 ^ 6 * κ * bondDistToTopBond b c)) * ‖e‖ := by
  by_cases hP : IsCrossingBond b.1 ∧ (enclosingCell b.1.1, b.1.2) = c
  · have hd0 : bondDistToTopBond b c = 0 := by
      unfold bondDistToTopBond
      rw [← hP.2]
      simp [cellSupDist_self]
    obtain ⟨D₀, hD₀⟩ : ∃ D₀, D₀ = bondDeriv (interpolatedFrame s a ρA m b.1) V (fun _ : Fin 1 => c) (fun _ => X) :=
      ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w, w = interpolatedFrame s a ρA m b.1 V := ⟨_, rfl⟩
    rw [← hw] at hC hD
    have hQ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun w' => Th' w' X) (w + toImaginaryCLM u₀) :=
      hC.clm_apply contDiffAt_const
    have hz : (fun u => imaginaryCoords (topVariationField (fun w X => Th' w X) s a ρA m c X b.1 (toImaginary u) V)) =
        fun u => imaginaryCoordsCLM D₀ + imaginaryCoordsCLM ((fun w' => Th' w' X) (w + toImaginaryCLM u)) := by
      funext u
      simp only [topVariationField, if_pos hP, ← hD₀, ← hw, ← imaginaryCoordsCLM_apply, map_add]
      rfl
    have hg : HasFDerivAt (fun u => w + toImaginaryCLM u) toImaginaryCLM u₀ :=
      toImaginaryCLM.hasFDerivAt.const_add w
    have hTh : HasFDerivAt (fun w' => Th' w' X) (fderiv ℝ (fun w' => Th' w' X) (w + toImaginaryCLM u₀))
        (w + toImaginaryCLM u₀) := (hQ.differentiableAt (by simp)).hasFDerivAt
    have hcomp := (imaginaryCoordsCLM.hasFDerivAt.comp u₀ (hTh.comp u₀ hg)).const_add (imaginaryCoordsCLM D₀)
    rw [hz]
    constructor
    · have hin : ContDiffAt ℝ 1 (fun u => w + toImaginaryCLM u) u₀ :=
        contDiffAt_const.add toImaginaryCLM.contDiff.contDiffAt
      have hT1 : ContDiffAt ℝ 1 (fun w' => Th' w' X) (w + toImaginaryCLM u₀) := hQ.of_le (by norm_num)
      have hT2 : ContDiffAt ℝ 1 (fun u => (fun w' => Th' w' X) (w + toImaginaryCLM u)) u₀ :=
        ContDiffAt.comp (g := fun w' => Th' w' X) (f := fun u => w + toImaginaryCLM u) u₀ hT1 hin
      have hT3 : ContDiffAt ℝ 1 (fun u => imaginaryCoordsCLM ((fun w' => Th' w' X) (w + toImaginaryCLM u))) u₀ :=
        imaginaryCoordsCLM.contDiff.contDiffAt.comp u₀ hT2
      exact contDiffAt_const.add hT3
    · intro e
      have e1 : fderiv ℝ (fun u => imaginaryCoordsCLM D₀ +
          imaginaryCoordsCLM ((fun w' => Th' w' X) (w + toImaginaryCLM u))) u₀ e =
          imaginaryCoords (fderiv ℝ (fun w' => Th' w' X) (w + toImaginaryCLM u₀) (toImaginary e)) := by
        have := hcomp.fderiv
        simp only [Function.comp_def] at this
        rw [this]
        simp [imaginaryCoordsCLM_apply, toImaginaryCLM_apply]
      rw [e1, norm_imaginaryCoords, hd0]
      simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
      have h2 := norm_fderiv_rightTranslation_le hC hD hCT hX (toImaginary e)
      rwa [norm_toImaginary] at h2
  · have hz : (fun u => imaginaryCoords (topVariationField (fun w X => Th' w X) s a ρA m c X b.1 (toImaginary u) V)) =
        fun _ => imaginaryCoords (bondDeriv (interpolatedFrame s a ρA m b.1) V (fun _ : Fin 1 => c) (fun _ => X) + 0) := by
      funext u
      simp only [topVariationField, if_neg hP]
    rw [hz]
    refine ⟨contDiffAt_const, fun e => ?_⟩
    simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, norm_zero]
    positivity
open Classical in
private theorem exists_block_sites (F : BlockFrame) (Y : F.Cell) (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (hSi : SitesPerCellLePow) :
    ∃ B : Finset (F.Site F.depth), (∀ y ∈ B, enclosingCell y = Y) ∧ B.card ≤ F.blockSide ^ 4 ∧
      ∀ (s a ρA : ℝ) (m : ℕ) (f : LocalFamily) (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top),
        interpolatedBlockExpansion s a ρA m f Y η V = ∑ y ∈ B, interpolatedExpansion s a ρA m f y η V := by
  refine ⟨(sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
    fun y hy => (Finset.mem_filter.1 hy).2, ?_, fun _ _ _ _ _ _ _ => rfl⟩
  have h0 := hSi F (finiteCells F) hodd hs Y
  refine le_trans ?_ h0
  calc _ ≤ ((Finset.univ.filter fun y : ↥(sitesOfCells (finiteCells F) F.depth) =>
        enclosingCell y.1 = Y).image Subtype.val).card :=
        Finset.card_le_card fun y hy => Finset.mem_image.2
          ⟨⟨y, (Finset.mem_filter.1 hy).1⟩, by simp [(Finset.mem_filter.1 hy).2], rfl⟩
    _ ≤ _ := Finset.card_image_le
private theorem hasBoundedDerivatives_of_family {L t n₀ : ℕ} {σ δ ε ε₃ : ℝ} {f : LocalFamily}
    (hf : IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ f) :
    HasBoundedDerivatives L t n₀ σ δ 3 (fun j => if j = 3 then ε₃ else ε) f := by apply _root_.YangMills.SharedProofs.p1 <;> assumption
private theorem extendByZero_id (ζ : StepVariable (finiteCells F)) :
    extendByZero (F := F) (id : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F))) Finset.univ ζ = ζ := by apply _root_.YangMills.Construction.InterpolatedBirths.extendByZero_id <;> assumption
end Frames
section Numbers
private theorem bondVariation_smul {ι : Type} [DecidableEq ι] (b : ι) (r : ℝ) (e : BondVector) :
    bondVariation b (r • e) = r • bondVariation b e := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LocalMeans.bondVariation_smul <;> assumption
private theorem sum_le_card_mul {K : Type} {s : Finset K} {g : K → ℝ} {c N : ℝ} (hN : (s.card : ℝ) ≤ N) (hc : 0 ≤ c)
    (h : ∀ y ∈ s, g y ≤ c) : ∑ y ∈ s, g y ≤ N * c := by
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hN hc
private theorem runningMax_one {ε ε₃ : ℝ} (h : 0 ≤ ε) :
    runningMax (fun j => if j = 3 then ε₃ else ε) 1 = ε := by
  simp [runningMax, h]
private theorem runningMax_two {ε ε₃ : ℝ} (h : 0 ≤ ε) :
    runningMax (fun j => if j = 3 then ε₃ else ε) 2 = ε := by
  simp [runningMax, h]
private theorem exp_decay_antitone {κ d S r : ℝ} (hκ : 0 ≤ κ) (hr : 0 ≤ r) (h : d ≤ S) :
    Real.exp (-(r * κ * S)) ≤ Real.exp (-(r * κ * d)) :=
  Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left h (mul_nonneg hr hκ)))
private theorem exp_weights_pair_le {κ d d' dc : ℝ} (hκ : 0 ≤ κ) (hd : 0 ≤ d) (hdc : 0 ≤ dc) :
    Real.exp (-(2 ^ 7 * κ * max d' d)) * Real.exp (-(2 ^ 8 * κ * dc)) ≤
      Real.exp (-(2 ^ 4 * κ * d) - 2 ^ 6 * κ * dc) * Real.exp (-(2 * κ * d')) := by
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 := mul_le_mul_of_nonneg_left (le_max_left d' d) hκ
  have h2 := mul_le_mul_of_nonneg_left (le_max_right d' d) hκ
  have h3 := mul_nonneg hκ hd
  have h4 := mul_nonneg hκ hdc
  nlinarith [h1, h2, h3, h4]
private theorem exp_weights_single_le {κ d dc : ℝ} (hκ : 0 ≤ κ) (hd : 0 ≤ d) (hdc : 0 ≤ dc) :
    Real.exp (-(2 ^ 7 * κ * d)) * Real.exp (-(2 ^ 6 * κ * dc)) ≤
      Real.exp (-(2 ^ 4 * κ * d) - 2 ^ 6 * κ * dc) * Real.exp (-(2 * κ * d)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h3 := mul_nonneg hκ hd
  nlinarith [h3]
end Numbers
section Parameters
private theorem eventually_two_le_n₀ : EventuallyInParameters fun T => 2 ≤ T.n₀ := by apply _root_.YangMills.SharedProofs.p10519 <;> assumption
private theorem eventually_frame_room : EventuallyInParameters fun T => T.Ct * T.σ + T.σ / 64 ≤ 1 := by
  intro a _
  refine ⟨0, fun L _ _ c _ => ⟨0, fun Ct hCt => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun nss _ =>
    ⟨1 / (Ct + 1), one_div_pos.2 (by linarith), fun σ h0 h1 p _ => ⟨0, fun Cs _ E _ => ⟨0, fun n₀ _ => ⟨0, fun CE _ =>
      ⟨0, fun y _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  show Ct * σ + σ / 64 ≤ 1
  have hc : 0 < Ct + 1 := by linarith
  have h2 : σ * (Ct + 1) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h1 hc.le
    rwa [one_div, inv_mul_cancel₀ hc.ne'] at this
  nlinarith [h2, h0]
end Parameters
section Bounds
variable {F : BlockFrame}
private theorem expansion_deriv_bounds (hS : IteratedFDerivSlices) {κ C₁ ε : ℝ}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    {V : F.GaugeField F.top} {Y z : F.Cell} {η : StepVariable (finiteCells F)} (hzY : z = Y) (hκ : 0 ≤ κ) (hC₁ : 0 ≤ C₁)
    (hε : 0 ≤ ε) (hG : ContDiffAt ℝ 2 (fun ζ => G ζ V) η)
    (hg : ∀ (l : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
      (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions), 1 ≤ l → l ≤ 2 → (∀ i, ‖u i‖ = 1) →
      |jointMixedDeriv G η V b u c X| ≤ C₁ * ε *
        Real.exp (-(2 ^ 7 * κ * cellSetDiameter (insert z (chordBondCells b ∪ topBondCells c))))) :
    (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector), |fderiv ℝ (fun ζ => G ζ V) η (bondVariation b e)| ≤
      C₁ * ε * Real.exp (-(2 ^ 7 * κ * bondDistToCell Y b)) * ‖e‖) ∧
    ∀ (b' b : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
      |fderiv ℝ (fderiv ℝ fun ζ => G ζ V) η (bondVariation b' e) (bondVariation b e')| ≤
        C₁ * ε * Real.exp (-(2 ^ 7 * κ * max (bondDistToCell Y b') (bondDistToCell Y b))) * ‖e‖ * ‖e'‖ := by
  subst hzY
  have hM : 0 ≤ C₁ * ε := mul_nonneg hC₁ hε
  have h2 : (0 : ℝ) ≤ 2 ^ 7 := by norm_num
  have c0 : Fin 0 → F.Site F.top × Fin 4 := Fin.elim0
  have X0 : Fin 0 → imaginaryQuaternions := Fin.elim0
  have hG1 : ContDiffAt ℝ 1 (fun ζ => G ζ V) η := hG.of_le (by norm_num)
  constructor
  · intro b
    refine abs_le_of_homogeneous (f := fun e => fderiv ℝ (fun ζ => G ζ V) η (bondVariation b e)) (fun r e => ?_)
      (fun e he => ?_)
    · simp only [bondVariation_smul, map_smul, smul_eq_mul]
    · show |fderiv ℝ (fun ζ => G ζ V) η (bondVariation b e)| ≤ _
      rw [fderiv_eq_jointMixedDeriv_one hS G η V b e c0 X0 hG1]
      refine (hg 1 ![b] ![e] c0 X0 le_rfl (by norm_num) (fun i => by simpa using he)).trans ?_
      refine mul_le_mul_of_nonneg_left (exp_decay_antitone hκ h2 ?_) hM
      unfold bondDistToCell
      exact_mod_cast cellSupDist_le_diameter
        (Finset.mem_insert_of_mem (Finset.mem_union_left _ (by simp [chordBondCells])))
        (Finset.mem_insert_self _ _)
  · intro b' b
    have unit : ∀ e e' : BondVector, ‖e‖ = 1 → ‖e'‖ = 1 →
        |fderiv ℝ (fderiv ℝ fun ζ => G ζ V) η (bondVariation b' e) (bondVariation b e')| ≤
          C₁ * ε * Real.exp (-(2 ^ 7 * κ * max (bondDistToCell z b') (bondDistToCell z b))) := by
      intro e e' he he'
      rw [fderiv_fderiv_eq_jointMixedDeriv_two hS G η V b' b e e' c0 X0 hG]
      refine (hg 2 ![b', b] ![e, e'] c0 X0 (by norm_num) le_rfl (fun i => ?_)).trans ?_
      · fin_cases i
        · simpa using he
        · simpa using he'
      refine mul_le_mul_of_nonneg_left (exp_decay_antitone hκ h2 ?_) hM
      refine max_le ?_ ?_
      · unfold bondDistToCell
        exact_mod_cast cellSupDist_le_diameter
          (Finset.mem_insert_of_mem (Finset.mem_union_left _ (by simp [chordBondCells])))
          (Finset.mem_insert_self _ _)
      · unfold bondDistToCell
        exact_mod_cast cellSupDist_le_diameter
          (Finset.mem_insert_of_mem (Finset.mem_union_left _ (by simp [chordBondCells])))
          (Finset.mem_insert_self _ _)
    intro e e'
    have s1 : ∀ e' : BondVector, ‖e'‖ = 1 → ∀ e : BondVector,
        |fderiv ℝ (fderiv ℝ fun ζ => G ζ V) η (bondVariation b' e) (bondVariation b e')| ≤
          C₁ * ε * Real.exp (-(2 ^ 7 * κ * max (bondDistToCell z b') (bondDistToCell z b))) * ‖e‖ :=
      fun e' he' e =>
      abs_le_of_homogeneous
        (f := fun e => fderiv ℝ (fderiv ℝ fun ζ => G ζ V) η (bondVariation b' e) (bondVariation b e'))
        (fun r e => by simp only [bondVariation_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul])
        (fun e he => unit e e' he he') e
    exact abs_le_of_homogeneous
      (f := fun e' => fderiv ℝ (fderiv ℝ fun ζ => G ζ V) η (bondVariation b' e) (bondVariation b e'))
      (fun r e' => by simp only [bondVariation_smul, map_smul, smul_eq_mul]) (fun e' he' => s1 e' he' e) e'
end Bounds
section Bounds
variable {F : BlockFrame}
private theorem interpolatedExpansion_bounds_on_balls (hS : IteratedFDerivSlices)
    (hJs : JointlyContDiffOnBallsOfDisplacements)
    {T : StepParameters} {C₁ : ℝ} {Ck : ℕ → ℝ} (hTr : TransportBoundsAt T C₁ Ck) (hκ : 0 ≤ T.κ) (hC₁ : 0 ≤ C₁)
    {t : ℕ} {x s ε : ℝ} {h : LocalFamily} {V : F.GaugeField F.top} {Y : F.Cell} (hx : T.coupling ≤ x) (hs : 0 ≤ s)
    (hs1 : s ≤ 1) (hε : 0 ≤ ε) (hε₃ : 0 ≤ ε / T.η₃)
    (hh : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h)
    (hTF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V) (y : F.Site F.depth)
    (hy : enclosingCell y = Y) (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < T.ballRadius) :
    ContDiffAt ℝ 2 (fun ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V) η ∧
    (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
      |fderiv ℝ (fun ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V) η (bondVariation b e)| ≤
        C₁ * ε * Real.exp (-(2 ^ 7 * T.κ * bondDistToCell Y b)) * ‖e‖) ∧
    ∀ (b' b : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
      |fderiv ℝ (fderiv ℝ fun ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V) η
        (bondVariation b' e) (bondVariation b e')| ≤
        C₁ * ε * Real.exp (-(2 ^ 7 * T.κ * max (bondDistToCell Y b') (bondDistToCell Y b))) * ‖e‖ * ‖e'‖ := by
  have he0 : ∀ j : ℕ, 0 ≤ (fun j : ℕ => if j = 3 then ε / T.η₃ else ε) j := fun j => by
    show 0 ≤ if j = 3 then ε / T.η₃ else ε
    split_ifs
    · exact hε₃
    · exact hε
  have tr : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ T.ballRadius) →
      IsTransportBounded s T.a T.chainParams.ρA T.κ T.decayRate C₁ Ck T.L (frameRadius x) 3
        (fun j => if j = 3 then ε / T.η₃ else ε) h V ζ :=
    fun ζ hζ => hTr x t 3 _ h F V s ζ hx le_rfl (by norm_num) he0 (hasBoundedDerivatives_of_family hh) hTF hV hs hs1 hζ
  have joint : JointlyContDiffOnBalls T.ballRadius V (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y) :=
    hJs F T.ballRadius V _ fun ζ hζ l j b u c X hu hX => by exact_mod_cast (tr ζ hζ).smooth y l j b u c X hu hX
  have hcl : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
  have hC2 : ContDiffAt ℝ 2 (fun ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V) η := by
    have h3 := joint 0 Fin.elim0 Fin.elim0 η hcl
    have hin : ContDiffAt ℝ 3 (fun ζ : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), ζ)) η :=
      contDiffAt_const.prodMk contDiffAt_id
    have h4 := ContDiffAt.comp (f := fun ζ : StepVariable (finiteCells F) => ((0 : Fin 0 → ℝ), ζ)) η h3 hin
    have h5 : ContDiffAt ℝ 3 (fun ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V) η :=
      h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ζ => by
        simp only [Function.comp, leftTranslate_bondSpread_empty])
    exact h5.of_le (by norm_num)
  refine ⟨hC2, expansion_deriv_bounds hS (G := interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y) hy hκ hC₁ hε hC2 ?_⟩
  intro l b u c X h1 h2 hu
  have g := (tr η hcl).jointDeriv_le y l 0 b u c X (by omega) (by omega) hu (fun i => i.elim0)
  have hl : runningMax (fun j => if j = 3 then ε / T.η₃ else ε) (l + 0) = ε := by
    rw [Nat.add_zero]
    interval_cases l
    · exact runningMax_one hε
    · exact runningMax_two hε
  rwa [hl] at g
private theorem cellSupDist_le_bondSpan_cons {k : ℕ} (y : F.Cell) (c : F.Site F.top × Fin 4)
    (c' : Fin k → F.Site F.top × Fin 4) :
    cellSupDist y c.1 ≤ bondSpan y (Fin.cons c c' : Fin (k + 1) → F.Site F.top × Fin 4) := by
  have := Finset.le_sup (f := fun l : Fin (k + 1) =>
    siteSupDist y ((Fin.cons c c' : Fin (k + 1) → F.Site F.top × Fin 4) l).1) (Finset.mem_univ 0)
  simp only [Fin.cons_zero] at this
  exact le_max_of_le_left this
abbrev _root_.YangMills.SharedProofs.p4114 := @cellSupDist_le_bondSpan_cons
private theorem hasLocalSize_blockSum {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    (hSz : localSizeOfQuadraticBoundsStatement)
    {ρ x lam κ W C h N M : ℝ} {d : ι → ι → ℝ} {Φ : BondField ι → ℝ} {p : ℝ → ℝ} {dZ : ι → ℝ}
    {B : Finset K} {H : BondField ι → ℝ} (Hy : K → BondField ι → ℝ)
    (hρ : 0 < ρ) (hx : 1 ≤ x) (hlam : 0 < lam) (hκ : 0 ≤ κ) (hW : 0 ≤ W) (hp : IsCutoff ρ p)
    (hd : IsPseudoMetricOnBonds d) (hL : HasUniformlyConvexLaw ρ lam x κ C d Φ)
    (hd₂ : ∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W)
    (hsum : ∑ b, Real.exp (-(2 * κ * dZ b)) ≤ W) (hN : (B.card : ℝ) ≤ N) (hN0 : 0 ≤ N) (hM : 0 ≤ M)
    (hH : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → H =ᶠ[𝓝 η] fun ζ => ∑ y ∈ B, Hy y ζ)
    (hC : ∀ y ∈ B, ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ContDiffAt ℝ 1 (Hy y) η)
    (hg : ∀ y ∈ B, ∀ (η : BondField ι) (b : ι), (∀ b, ‖η b‖ < ρ) →
      bondGradNorm (Hy y) b η ≤ M * Real.exp (-(2 * κ * dZ b)))
    (hxi : Real.sqrt x * x ^ (-(1 / 2 : ℝ)) = 1) (hxi0 : 0 < x ^ (-(1 / 2 : ℝ)))
    (hh : (1 + W) * (N * M * x ^ (-(1 / 2 : ℝ))) ≤ h) :
    HasLocalSize ρ (cutoffFactor ρ p) Φ (lpMomentConstant lam W W) x κ h dZ H := by
  refine hasLocalSize_of_bondGradNorm hSz (h₁ := N * M * x ^ (-(1 / 2 : ℝ))) hρ hx hlam hκ hW hp hd hL hd₂ hsum ?_ ?_
    (by positivity) hh
  · intro η hη
    have h1 : ContDiffAt ℝ 1 (fun ζ => ∑ y ∈ B, Hy y ζ) η := ContDiffAt.sum fun y hy => hC y hy η hη
    exact_mod_cast h1.congr_of_eventuallyEq (hH η hη)
  · intro η b hη
    have h1 := bondGradNorm_sum_le (hH η hη) (fun y hy => (hC y hy η hη).differentiableAt (by simp)) b
    have h2 := sum_le_card_mul hN (mul_nonneg hM (Real.exp_pos (-(2 * κ * dZ b))).le) fun y hy => hg y hy η b hη
    refine h1.trans (h2.trans (le_of_eq ?_))
    have e : Real.sqrt x * (N * M * x ^ (-(1 / 2 : ℝ))) = N * M := by
      calc _ = (Real.sqrt x * x ^ (-(1 / 2 : ℝ))) * (N * M) := by ring
        _ = _ := by rw [hxi, one_mul]
    rw [e]
    ring
end Bounds
section Bounds
variable {F : BlockFrame}
set_option maxHeartbeats 1600000 in
private theorem blockExpansionThirdOrderAt_of_bounds (hSz : localSizeOfQuadraticBoundsStatement) (hS : IteratedFDerivSlices)
    (hJs : JointlyContDiffOnBallsOfDisplacements) (hUq : RightTranslationDerivUnique) (hSi : SitesPerCellLePow)
    {T : StepParameters} {C₁ c CT W : ℝ} {Ck : ℕ → ℝ}
    {Th' : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions}
    (hTr : TransportBoundsAt T C₁ Ck)
    (hCv : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
      (n : ℕ) (w : Fin n → ℝ) (M : Fin n → LawOnBondVariables ι), IsConvexWeights w →
      (∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
        (frameRadius x) d) →
      HasUniformlyConvexLaw T.ballRadius T.chainParams.lam x T.κ T.Ct d
        (convexCombinationExponent T.chainParams.lam x w M))
    (hNr : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ),
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
      ∀ b ∈ chordBonds (finiteCells F), ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b V‖ ≤ T.Ct * T.σ)
    (hFd : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ),
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
      TopVariationRepresentation s T.a T.chainParams.ρA T.ballRadius T.κ c (frameRadius x) V)
    (hShift : ∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (Th' w X))
    (hC2 : ∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Th' w)
    (hCT : ∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 2 → ‖iteratedFDeriv ℝ j Th' w‖ ≤ CT)
    (hCT0 : 0 ≤ CT) (hc : 1 ≤ c) (hC₁ : 0 < C₁) (hW0 : 0 ≤ W)
    (hWb : ∀ F : BlockFrame, F.blockSide = T.L → Odd F.blockSide → (∀ i, 2 ≤ F.extent i) → ∀ z : F.Cell,
      ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ W)
    (hodd : Odd T.L) (hn2 : 2 ≤ T.n₀) (hy : 1 ≤ T.coupling) (hκ : 0 < T.κ) (hσ : 0 < T.σ) (hη₃ : 0 < T.η₃)
    (hlam : 0 < T.chainParams.lam) (hcut : IsCutoff (T.σ / 64) T.p) (hroom : T.Ct * T.σ + T.σ / 64 ≤ 1)
    (hG : (1 + W) * ((T.L : ℝ) ^ 4 * C₁ * (c + CT)) ≤ T.Cs) :
    blockExpansionThirdOrderAt T (lpMomentConstant T.chainParams.lam W W) := by
  intro t x s ε φ h F V Y c₃ X Th hx hs hs1 hε hφ hh hTF hV hX hTh
  obtain ⟨hFL, -, n, hside, hn⟩ := id hTF
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    omega
  have hoddF : Odd F.blockSide := by
    rw [hFL]
    exact hodd
  have hx1 : 1 ≤ x := hy.trans hx
  have hx0 : 0 < x := by linarith
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hxi : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hxis : Real.sqrt x * x ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    norm_num
  have hκ0 : 0 ≤ T.κ := hκ.le
  have hε₃ : 0 ≤ ε / T.η₃ := by positivity
  obtain ⟨B, hBY, hBc, hBs⟩ := exists_block_sites F Y hoddF hs2 hSi
  have hBc' : (B.card : ℝ) ≤ (T.L : ℝ) ^ 4 := by
    rw [← hFL]
    exact_mod_cast hBc
  have hL0 : (0 : ℝ) ≤ (T.L : ℝ) ^ 4 := by positivity
  obtain ⟨f, hf⟩ : ∃ f : F.Site F.depth → StepVariable (finiteCells F) → ℝ,
      f = fun y ζ => interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y ζ V := ⟨_, rfl⟩
  have standingConstraints : ∀ y ∈ B, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
      ContDiffAt ℝ 2 (f y) η ∧
      (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector), |fderiv ℝ (f y) η (bondVariation b e)| ≤
        C₁ * ε * Real.exp (-(2 ^ 7 * T.κ * bondDistToCell Y b)) * ‖e‖) ∧
      ∀ (b' b : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
        |fderiv ℝ (fderiv ℝ (f y)) η (bondVariation b' e) (bondVariation b e')| ≤
          C₁ * ε * Real.exp (-(2 ^ 7 * T.κ * max (bondDistToCell Y b') (bondDistToCell Y b))) * ‖e‖ * ‖e'‖ := by
    intro y hy η hη
    rw [hf]
    exact interpolatedExpansion_bounds_on_balls hS hJs hTr hκ0 hC₁.le hx hs hs1 hε.le hε₃ hh hTF hV y (hBY y hy) η hη
  have hA : (fun η => interpolatedBlockExpansion s T.a T.chainParams.ρA (frameRadius x) h Y η V) =
      fun ζ => ∑ y ∈ B, f y ζ := by
    funext ζ
    rw [hBs, hf]
  have hAdm : (⟨F, V, id, Finset.univ, familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V⟩ :
      LawOnBondVariables ↥(chordBonds (finiteCells F))).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ
        T.decayRate T.E T.energyRatio T.L t T.n₀ (frameRadius x)
        (fun i i' => (cellSupDist (enclosingCell i.1.1) (enclosingCell i'.1.1) : ℝ)) :=
    ⟨hTF, hV, IsIntermediateLaw.ofFamily s φ hs hs1 hφ, Function.injective_id, fun _ _ => rfl⟩
  have hwt : IsConvexWeights (fun _ : Fin 1 => (1 : ℝ)) := ⟨fun _ => zero_le_one, by simp⟩
  have hcv := hCv t x hx ↥(chordBonds (finiteCells F)) _ 1 (fun _ => 1) (fun _ => _) hwt (fun _ => hAdm)
  have hΦ : convexCombinationExponent T.chainParams.lam x (fun _ : Fin 1 => (1 : ℝ))
      (fun _ => (⟨F, V, id, Finset.univ, familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V⟩ :
        LawOnBondVariables ↥(chordBonds (finiteCells F)))) =
      familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V := by
    funext ζ
    simp only [convexCombinationExponent, LawOnBondVariables.exponent, frozenExponent, extendByZero_id]
    simp
  rw [hΦ] at hcv
  have hd₂ : ∀ b₀ : ↥(chordBonds (finiteCells F)), ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) (enclosingCell b₀.1.1) : ℝ))) ≤ W :=
    fun b₀ => hWb F hFL hoddF hs2 _
  have hsumY : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 * T.κ * bondDistToCell Y b)) ≤ W :=
    hWb F hFL hoddF hs2 Y
  have hdn : ∀ b : ↥(chordBonds (finiteCells F)), 0 ≤ bondDistToCell Y b := fun b => Nat.cast_nonneg _
  have hM0 : 0 ≤ C₁ * ε := mul_nonneg hC₁.le hε.le
  have hcCT : 1 ≤ c + CT := by linarith
  refine ⟨fun η hη => ?_, ?_, fun b l => ?_⟩
  · rw [hA]
    exact ContDiffAt.sum fun y hy => (standingConstraints y hy η hη).1
  · rw [hA]
    refine hasLocalSize_blockSum hSz (N := (T.L : ℝ) ^ 4) (M := C₁ * ε) f hρ hx1 hlam hκ0 hW0 hcut
      isPseudoMetric_cellSupDist hcv hd₂ hsumY hBc' hL0 hM0
      (fun η _ => Filter.EventuallyEq.rfl) (fun y hy η hη => (standingConstraints y hy η hη).1.of_le (by norm_num)) ?_ hxis hxi ?_
    · intro y hy η b hη
      refine bondGradNorm_le (by positivity) fun e => ?_
      refine ((standingConstraints y hy η hη).2.1 b e).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg e))
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM0
      have := mul_nonneg hκ0 (hdn b)
      nlinarith [this]
    · have h1 : (1 + W) * ((T.L : ℝ) ^ 4 * C₁) ≤ T.Cs := by
        refine le_trans ?_ hG
        have h0 : 0 ≤ (1 + W) * ((T.L : ℝ) ^ 4 * C₁) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hcCT h0]
      have h2 : 0 ≤ ε * x ^ (-(1 / 2 : ℝ)) := by positivity
      calc (1 + W) * ((T.L : ℝ) ^ 4 * (C₁ * ε) * x ^ (-(1 / 2 : ℝ))) =
            ((1 + W) * ((T.L : ℝ) ^ 4 * C₁)) * (ε * x ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ T.Cs * (ε * x ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_right h1 h2
        _ = _ := by ring
  · obtain ⟨Th₂, hTh₂, -, hdec⟩ := (hFd t x hx F V s hTF hV hs hs1).exists_representation
    have hw : ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b.1 V‖ + T.ballRadius ≤ 1 := by
      have := hNr t x hx F V s hTF hV hs hs1 b.1 b.2
      show _ + T.σ / 64 ≤ 1
      linarith
    have hu : ∀ u : BondVector, ‖u‖ < T.ballRadius →
        ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b.1 V + toImaginary u‖ < 1 := fun u hu => by
      have h1 := norm_add_le (interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b.1 V) (toImaginary u)
      rw [norm_toImaginary] at h1
      linarith
    have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
    obtain ⟨z, hz⟩ : ∃ z : BondVector → BondVector, z = fun u => imaginaryCoords (topVariationField
        (fun w X => Th' w X) s T.a T.chainParams.ρA (frameRadius x) (c₃ l) (X l) b.1 (toImaginary u) V) := ⟨_, rfl⟩
    have zeq : ∀ u : BondVector, ‖u‖ < T.ballRadius → imaginaryCoords (topVariationField Th s T.a T.chainParams.ρA
        (frameRadius x) (c₃ l) (X l) b.1 (toImaginary u) V) = z u := fun u hu' => by
      rw [hz]
      show imaginaryCoords _ = imaginaryCoords _
      rw [topVariationField_congr hUq hTh (fun w X h => hShift w X h) ((hu u hu').trans hpi)]
    have zsm : ∀ u : BondVector, ‖u‖ < T.ballRadius → ContDiffAt ℝ 1 z u ∧ ∀ e, ‖fderiv ℝ z u e‖ ≤
        CT * Real.exp (-(2 ^ 6 * T.κ * bondDistToTopBond b (c₃ l))) * ‖e‖ := fun u hu' => by
      rw [hz]
      exact topVariationField_coords_smooth (hX l) (hC2 _ (hu u hu').le) (hCT _ 1 (hu u hu').le (by norm_num)) hCT0
    have zval : ∀ u : BondVector, ‖u‖ < T.ballRadius → ‖z u‖ ≤
        c * Real.exp (-(2 ^ 8 * T.κ * bondDistToTopBond b (c₃ l))) := fun u hu' => by
      rw [hz]
      show ‖imaginaryCoords _‖ ≤ _
      rw [norm_imaginaryCoords, topVariationField_congr hUq (fun w X h => hShift w X h) hTh₂ ((hu u hu').trans hpi)]
      have d := hdec (c₃ l) (X l) b (toImaginary u) 0 Fin.elim0 Fin.elim0 (hX l)
        (by rw [norm_toImaginary]; exact hu') (Nat.zero_le _) (fun i => i.elim0)
      rw [bondDeriv_empty] at d
      refine d.trans (mul_le_mul_of_nonneg_left (exp_decay_antitone hκ0 (by norm_num) ?_) (by linarith))
      unfold bondDistToTopBond
      exact_mod_cast cellSupDist_le_bondSpan_cons _ _ _
    have hdc : 0 ≤ bondDistToTopBond b (c₃ l) := Nat.cast_nonneg _
    obtain ⟨E₀, hE₀⟩ : ∃ E₀, E₀ = Real.exp (-(2 ^ 4 * T.κ * bondDistToCell Y b) -
        2 ^ 6 * T.κ * bondDistToTopBond b (c₃ l)) := ⟨_, rfl⟩
    have hE₀p : 0 < E₀ := by
      rw [hE₀]
      exact Real.exp_pos _
    rw [← hE₀, hA]
    refine hasLocalSize_blockSum hSz (N := (T.L : ℝ) ^ 4) (M := C₁ * ε * (c + CT) * E₀)
      (fun y ζ => bondPartialDeriv (f y) b ζ (z (ζ b))) hρ hx1 hlam hκ0 hW0 hcut isPseudoMetric_cellSupDist hcv hd₂
      hsumY hBc' hL0 (by positivity) ?_ ?_ ?_ hxis hxi ?_
    · intro η hη
      filter_upwards [(isOpen_setOf_norm_lt T.ballRadius).mem_nhds hη] with ζ hζ
      have hb : ‖ζ b‖ < T.ballRadius := hζ b
      show bondPartialDeriv (fun ζ => ∑ y ∈ B, f y ζ) b ζ (imaginaryCoords (topVariationField Th s T.a
        T.chainParams.ρA (frameRadius x) (c₃ l) (X l) b.1 (toImaginary (ζ b)) V)) =
        ∑ y ∈ B, bondPartialDeriv (f y) b ζ (z (ζ b))
      rw [zeq _ hb]
      unfold bondPartialDeriv
      rw [fderiv_fun_sum fun y hy => ((standingConstraints y hy ζ hζ).1.differentiableAt (by simp)), sum_apply]
    · intro y hy η hη
      exact (partialDeriv_along_field (standingConstraints y hy η hη).1 (zsm _ (hη b)).1).1
    · intro y hy η b' hη
      have hr := standingConstraints y hy η hη
      obtain ⟨hzc, hzd⟩ := zsm _ (hη b)
      have hc0 : 0 ≤ c := by linarith
      have hsite := bondGradNorm_partialDeriv_along_le (b' := b') hr.1 hzc (hr.2.1 b) (hr.2.2 b' b) (zval _ (hη b)) hzd
        (by positivity) (by positivity) (by positivity) (by positivity)
      refine hsite.trans ?_
      have w1 := exp_weights_pair_le (d := bondDistToCell Y b) (d' := bondDistToCell Y b') hκ0 (hdn b) hdc
      rw [← hE₀] at w1
      have t1 := mul_le_mul_of_nonneg_left w1 (mul_nonneg hM0 hc0)
      have t2 : (if b' = b then C₁ * ε * Real.exp (-(2 ^ 7 * T.κ * bondDistToCell Y b)) *
          (CT * Real.exp (-(2 ^ 6 * T.κ * bondDistToTopBond b (c₃ l)))) else 0) ≤
          C₁ * ε * CT * (E₀ * Real.exp (-(2 * T.κ * bondDistToCell Y b'))) := by
        split_ifs with hbb
        · subst hbb
          have w2 := exp_weights_single_le hκ0 (hdn b') hdc
          rw [← hE₀] at w2
          have := mul_le_mul_of_nonneg_left w2 (mul_nonneg hM0 hCT0)
          nlinarith [this]
        · positivity
      nlinarith [t1, t2]
    · have h2 : 0 ≤ ε * x ^ (-(1 / 2 : ℝ)) * E₀ := by positivity
      calc (1 + W) * ((T.L : ℝ) ^ 4 * (C₁ * ε * (c + CT) * E₀) * x ^ (-(1 / 2 : ℝ))) =
            ((1 + W) * ((T.L : ℝ) ^ 4 * C₁ * (c + CT))) * (ε * x ^ (-(1 / 2 : ℝ)) * E₀) := by ring
        _ ≤ T.Cs * (ε * x ^ (-(1 / 2 : ℝ)) * E₀) := mul_le_mul_of_nonneg_right hG h2
        _ = _ := by ring
end Bounds
end BlockExpansionThirdOrder
set_option maxHeartbeats 800000 in
open BlockExpansionThirdOrder in
theorem blockExpansionThirdOrder_holds (hJ : joinAtLoweredSmallnessConstantStatement)
    (hJ2 : EventuallyInParametersCombines) (hTr : transportBoundsStatement) (hFd : topVariationAlongFields)
    (hNr : interpolatedFramesControlled) (hCv : mixturesOfIntermediateLawsConvex)
    (hSz : localSizeOfQuadraticBoundsStatement) (hRS : rightTranslationSmooth) (hUq : RightTranslationDerivUnique)
    (hJs : JointlyContDiffOnBallsOfDisplacements) (hS : IteratedFDerivSlices)
    (hW : _root_.YangMills.Construction.CellCounting.ExpDecaySumBounded) (hCnt : cellBondsCardStatement)
    (hSi : SitesPerCellLePow) : blockExpansionThirdOrderStatement := by
  obtain ⟨both, -⟩ := hJ2
  obtain ⟨C, Ck, hCp, -, hTrT⟩ := hTr
  obtain ⟨Th', CT, hCT0, -, hShift, hC3, hCTb⟩ := hRS
  have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hC2 : ∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) Th' w := fun w hw =>
    (hC3 w (hw.trans_lt hpi)).of_le (by norm_num)
  have hCT2 : ∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 2 → ‖iteratedFDeriv ℝ j Th' w‖ ≤ CT :=
    fun w j h1 h2 => hCTb w j h1 (by omega)
  have hW' : ∀ (N : ℕ) (κ : ℝ), ∃ W : ℝ, 0 < κ → 0 ≤ W ∧
      ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
        (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ N) →
        ∀ z : F.Cell, ∑ b, Real.exp (-(κ * (cellSupDist (y b) z : ℝ))) ≤ W := by
    intro N κ
    by_cases h : 0 < κ
    · obtain ⟨W, h1, h2⟩ := hW N κ h
      exact ⟨W, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Wf hWf using hW'
  refine ⟨fun U q => |lpMomentConstant U.chainParams.lam (Wf (4 * U.L ^ 4) (2 * U.κ)) (Wf (4 * U.L ^ 4) (2 * U.κ)) q|,
    fun _ _ => abs_nonneg _, ?_⟩
  refine hJ _ _ _ (fun U c => (1 + Wf (4 * U.L ^ 4) (2 * U.κ)) * ((U.L : ℝ) ^ 4 * C (rateParameters U) * (c + CT)))
    (both _ _ (both _ _ hTrT (both _ _ hCv hNr)) (both _ _ eventually_two_le_n₀ eventually_frame_room)) hFd ?_
  intro T c hc hodd hn hy hE hη hη1 hκ hσ hch hcut hGle hP hR
  obtain ⟨⟨hTr1, hCv1, hNr1⟩, hn2, hroom⟩ := hP
  have hlam : 0 < T.chainParams.lam := hch.positivity.2.2.1
  have h2κ : 0 < 2 * T.κ := by positivity
  obtain ⟨hW0, hWs⟩ := hWf (4 * T.L ^ 4) (2 * T.κ) h2κ
  have hnn : ∀ q, 0 ≤ lpMomentConstant T.chainParams.lam (Wf (4 * T.L ^ 4) (2 * T.κ)) (Wf (4 * T.L ^ 4) (2 * T.κ)) q := by
    intro q
    unfold lpMomentConstant
    have hp : 0 ≤ ∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * Wf (4 * T.L ^ 4) (2 * T.κ)) :=
      Finset.prod_nonneg fun k _ => by positivity
    positivity
  have a1 : TransportBoundsAt T (C (rateParameters T)) (Ck (rateParameters T)) := hTr1
  have a3 : (1 + Wf (4 * T.L ^ 4) (2 * T.κ)) * ((T.L : ℝ) ^ 4 * C (rateParameters T) * (c + CT)) ≤ T.Cs := hGle
  have a4 : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ),
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
      TopVariationRepresentation s T.a T.chainParams.ρA T.ballRadius T.κ c (frameRadius x) V := hR
  have a5 : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ),
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
      ∀ b ∈ chordBonds (finiteCells F), ‖interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b V‖ ≤ T.Ct * T.σ :=
    fun t x hx F V s h1 h2 h3 h4 b hb => ((hNr1 t x hx).single F V s h1 h2 h3 h4).2.norm_le b hb
  have a2 : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
      (n : ℕ) (w : Fin n → ℝ) (M : Fin n → LawOnBondVariables ι), IsConvexWeights w →
      (∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
        (frameRadius x) d) →
      HasUniformlyConvexLaw T.ballRadius T.chainParams.lam x T.κ T.Ct d
        (convexCombinationExponent T.chainParams.lam x w M) := hCv1
  have a6 : ∀ F : BlockFrame, F.blockSide = T.L → Odd F.blockSide → (∀ i, 2 ≤ F.extent i) → ∀ z : F.Cell,
      ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤
        Wf (4 * T.L ^ 4) (2 * T.κ) :=
    fun F hFL hoddF hs2 z => by
      have hcount : ∀ z₀ : F.Cell,
          (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z₀).card ≤
            4 * T.L ^ 4 := by
        intro z₀
        have h0 := hCnt F hoddF hs2 z₀
        calc _ ≤ 4 * F.blockSide ^ 4 := h0
          _ = 4 * T.L ^ 4 := by rw [hFL]
      exact hWs F (↥(chordBonds (finiteCells F))) (fun b => enclosingCell b.1.1) hcount z
  have hcl := blockExpansionThirdOrderAt_of_bounds hSz hS hJs hUq hSi a1 a2 a5 a4 hShift hC2 hCT2 hCT0 hc (hCp _) hW0 a6
    hodd hn2 hy hκ hσ hη hlam hcut hroom a3
  have e : (fun q => |lpMomentConstant T.chainParams.lam (Wf (4 * T.L ^ 4) (2 * T.κ)) (Wf (4 * T.L ^ 4) (2 * T.κ)) q|) =
      lpMomentConstant T.chainParams.lam (Wf (4 * T.L ^ 4) (2 * T.κ)) (Wf (4 * T.L ^ 4) (2 * T.κ)) :=
    funext fun q => abs_of_nonneg (hnn q)
  show blockExpansionThirdOrderAt T (fun q =>
    |lpMomentConstant T.chainParams.lam (Wf (4 * T.L ^ 4) (2 * T.κ)) (Wf (4 * T.L ^ 4) (2 * T.κ)) q|)
  rw [e]
  exact hcl
end Interpolation
end YangMills.Construction
end
