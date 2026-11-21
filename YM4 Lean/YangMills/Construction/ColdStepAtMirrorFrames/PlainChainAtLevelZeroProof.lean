import YangMills.Construction.ColdStepAtMirrorFrames.BareActionIsCriticalAtAnAbelianFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.ColdChainAboveLevelZeroProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.deprecated false
noncomputable section
open scoped Quaternion ContDiff
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
private def AnalyticBound {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (Fin n → ℝ) → E)
    (u : ℕ → ℝ) : Prop :=
  ContDiff ℝ ω f ∧ ∀ m, ‖iteratedFDeriv ℝ m f 0‖ ≤ u m
private def binomialConv (u v : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * u i * v (m - i)
private theorem AnalyticBound.mul {n : ℕ} {f g : (Fin n → ℝ) → ℍ[ℝ]} {u v : ℕ → ℝ} (hf : AnalyticBound f u)
    (hg : AnalyticBound g v) : AnalyticBound (fun τ => f τ * g τ) (binomialConv u v) := by
  refine ⟨hf.1.mul hg.1, fun m => ?_⟩
  refine (norm_iteratedFDeriv_mul_le hf.1 hg.1 0 le_top).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have hfi := hf.2 i
  have hgi := hg.2 (m - i)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hfi (Nat.cast_nonneg _)) hgi (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans hfi))
private theorem AnalyticBound.comp_clm {n : ℕ} {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] {f : (Fin n → ℝ) → E} {u : ℕ → ℝ} (hf : AnalyticBound f u)
    (g : E →L[ℝ] E') (hg : ‖g‖ ≤ 1) : AnalyticBound (fun τ => g (f τ)) u := by
  refine ⟨g.contDiff.comp hf.1, fun m => ?_⟩
  have hcomp : (fun τ => g (f τ)) = g ∘ f := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left g hf.1.contDiffAt le_top]
  refine (g.norm_compContinuousMultilinearMap_le _).trans ?_
  calc ‖g‖ * ‖iteratedFDeriv ℝ m f 0‖ ≤ 1 * ‖iteratedFDeriv ℝ m f 0‖ :=
        mul_le_mul_of_nonneg_right hg (norm_nonneg _)
    _ ≤ u m := by rw [one_mul]; exact hf.2 m
private theorem AnalyticBound.const {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E)
    (hc : ‖c‖ ≤ 1) : AnalyticBound (fun _ : Fin n → ℝ => c) (fun _ => 1) := by
  refine ⟨contDiff_const, fun m => ?_⟩
  by_cases hm : m = 0
  · subst hm
    rw [norm_iteratedFDeriv_zero]
    exact hc
  · rw [iteratedFDeriv_const_of_ne hm]
    simp
private theorem AnalyticBound.add {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {u v : ℕ → ℝ} (hf : AnalyticBound f u)
    (hg : AnalyticBound g v) : AnalyticBound (fun τ => f τ + g τ) (fun m => u m + v m) := by
  refine ⟨hf.1.add hg.1, fun m => ?_⟩
  have hsum : iteratedFDeriv ℝ m (fun τ => f τ + g τ) 0 = iteratedFDeriv ℝ m f 0 + iteratedFDeriv ℝ m g 0 := by
    have := iteratedFDeriv_add_apply (i := m) (x := (0 : Fin n → ℝ)) (hf.1.contDiffAt.of_le le_top)
      (hg.1.contDiffAt.of_le le_top)
    exact this
  rw [hsum]
  exact (norm_add_le _ _).trans (add_le_add (hf.2 m) (hg.2 m))
private theorem analytic_contDiff_quaternion_exp : ContDiff ℝ ω (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) := by apply _root_.YangMills.SharedProofs.p23558 <;> assumption
private def expDerivBound (R : ℝ) (m : ℕ) : ℝ :=
  ‖iteratedFDeriv ℝ m (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) 0‖ * R ^ m
private theorem AnalyticBound.exp {n : ℕ} (T : (Fin n → ℝ) →L[ℝ] ℍ[ℝ]) {R : ℝ} (hT : ‖T‖ ≤ R) :
    AnalyticBound (fun τ => NormedSpace.exp (T τ)) (expDerivBound R) := by
  refine ⟨analytic_contDiff_quaternion_exp.comp T.contDiff, fun m => ?_⟩
  have hcomp : (fun τ => NormedSpace.exp (T τ)) = NormedSpace.exp ∘ T := rfl
  rw [hcomp, T.iteratedFDeriv_comp_right analytic_contDiff_quaternion_exp 0 le_top]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [map_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hT m) (norm_nonneg _)
private theorem abs_iteratedFDeriv_single_le {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    |iteratedFDeriv ℝ n f 0 (fun l => Pi.single l 1)| ≤ ‖iteratedFDeriv ℝ n f 0‖ := by
  have h := (iteratedFDeriv ℝ n f 0).le_opNorm (fun l => (Pi.single l 1 : Fin n → ℝ))
  have hprod : ∏ l : Fin n, ‖(Pi.single l 1 : Fin n → ℝ)‖ = 1 := by
    refine Finset.prod_eq_one fun l _ => ?_
    simp [Pi.norm_single]
  rw [hprod, mul_one] at h
  exact h
private theorem iteratedFDeriv_single_eq_zero_of_indep {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ω f)
    (l : Fin n) (h : ∀ τ, f τ = f (Function.update τ l 0)) :
    iteratedFDeriv ℝ n f 0 (fun l => Pi.single l 1) = 0 := by
  let π : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi fun i => if i = l then 0 else ContinuousLinearMap.proj i
  have hπ : ∀ τ, π τ = Function.update τ l 0 := by
    intro τ
    funext i
    by_cases hi : i = l
    · subst hi
      simp [π]
    · simp [π, hi]
  have hfπ : f = f ∘ π := by
    funext τ
    simp only [Function.comp, hπ]
    exact h τ
  rw [hfπ, π.iteratedFDeriv_comp_right hf 0 le_top]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine ContinuousMultilinearMap.map_coord_zero _ l ?_
  show π (Pi.single l 1) = 0
  rw [hπ]
  funext i
  by_cases hi : i = l
  · subst hi
    simp
  · simp [hi]
variable {F : BlockFrame}
private def reCLM : ℍ[ℝ] →L[ℝ] ℝ := innerSL ℝ (1 : ℍ[ℝ])
private theorem reCLM_apply (q : ℍ[ℝ]) : reCLM q = q.re := by
  simp [reCLM, innerSL_apply_apply, Quaternion.inner_def]
private theorem norm_reCLM_le : ‖reCLM‖ ≤ 1 := by
  unfold reCLM
  rw [innerSL_apply_norm]
  simp
private def starCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.mkContinuous ⟨⟨star, star_add⟩, fun r q => quaternion_star_real_smul r q⟩ 1 fun q => by simp [norm_star]
private theorem starCLM_apply (q : ℍ[ℝ]) : starCLM q = star q := rfl
private theorem norm_starCLM_le : ‖starCLM‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by
    rw [starCLM_apply, norm_star, one_mul]
private def bondLinear {j n : ℕ} (c : Fin n → F.Site j × Fin 4) (X : Fin n → imaginaryQuaternions)
    (b : F.Site j × Fin 4) : (Fin n → ℝ) →L[ℝ] ℍ[ℝ] :=
  ∑ l, if c l = b then (ContinuousLinearMap.proj l : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (X l : ℍ[ℝ]) else 0
private theorem bondLinear_apply {j n : ℕ} (c : Fin n → F.Site j × Fin 4) (X : Fin n → imaginaryQuaternions)
    (x : F.Site j) (i : Fin 4) (τ : Fin n → ℝ) :
    bondLinear c X (x, i) τ = ((bondSpread c X τ x i : imaginaryQuaternions) : ℍ[ℝ]) := by
  unfold bondLinear bondSpread
  rw [_root_.sum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : c l = (x, i)
  · simp [h]
  · simp [h]
private def totalNorm {n : ℕ} (X : Fin n → imaginaryQuaternions) : ℝ := ∑ l, ‖X l‖
private theorem totalNorm_of_units {n : ℕ} {X : Fin n → imaginaryQuaternions} (hX : AreUnitVectors X) :
    totalNorm X = n := by
  unfold totalNorm
  simp [hX _]
private theorem norm_bondLinear_le {j n : ℕ} (c : Fin n → F.Site j × Fin 4) (X : Fin n → imaginaryQuaternions)
    (b : F.Site j × Fin 4) : ‖bondLinear c X b‖ ≤ totalNorm X := by
  have hR : 0 ≤ totalNorm X := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hR fun τ => ?_
  unfold bondLinear
  rw [_root_.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  unfold totalNorm
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases h : c l = b
  · simp only [h, if_true, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, norm_smul]
    have hnorm : ‖(X l : ℍ[ℝ])‖ = ‖X l‖ := rfl
    rw [hnorm, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm τ l) (norm_nonneg _)
  · simp only [h, if_false, _root_.zero_apply, norm_zero]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
private theorem coe_leftTranslate {j n : ℕ} (c : Fin n → F.Site j × Fin 4) (X : Fin n → imaginaryQuaternions)
    (W : F.GaugeField j) (x : F.Site j) (i : Fin 4) (τ : Fin n → ℝ) :
    ((leftTranslate (bondSpread c X τ) W x i : UnitQuaternion) : ℍ[ℝ]) =
      NormedSpace.exp (bondLinear c X (x, i) τ) * (W x i : ℍ[ℝ]) := by
  rw [bondLinear_apply]
  rfl
private def linkDerivBound (R : ℝ) : ℕ → ℝ := binomialConv (expDerivBound R) fun _ => 1
private theorem AnalyticBound.leftTranslate {j n : ℕ} (c : Fin n → F.Site j × Fin 4)
    (X : Fin n → imaginaryQuaternions) (W : F.GaugeField j) (x : F.Site j) (i : Fin 4) :
    AnalyticBound (fun τ => ((leftTranslate (bondSpread c X τ) W x i : UnitQuaternion) : ℍ[ℝ]))
      (linkDerivBound (totalNorm X)) := by
  have hfun : (fun τ => ((ColdStepAtMirrorFrames.leftTranslate (bondSpread c X τ) W x i : UnitQuaternion) : ℍ[ℝ])) =
      fun τ => NormedSpace.exp (bondLinear c X (x, i) τ) * (W x i : ℍ[ℝ]) := funext (coe_leftTranslate c X W x i)
  rw [hfun]
  exact (AnalyticBound.exp _ (norm_bondLinear_le c X _)).mul (AnalyticBound.const _ (norm_coe_unitQuaternion _).le)
private def holonomyDerivBound (R : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 1
  | ℓ + 1 => binomialConv (linkDerivBound R) (holonomyDerivBound R ℓ)
private theorem AnalyticBound.holonomy {j n : ℕ} (c : Fin n → F.Site j × Fin 4) (X : Fin n → imaginaryQuaternions)
    (W : F.GaugeField j) :
    ∀ (p : List PathStep) (x : F.Site j),
      AnalyticBound (fun τ => ((pathHolonomy (ColdStepAtMirrorFrames.leftTranslate (bondSpread c X τ) W) x p : UnitQuaternion) : ℍ[ℝ]))
        (holonomyDerivBound (totalNorm X) p.length)
  | [], x => by
    simp only [pathHolonomy, OneMemClass.coe_one]
    exact AnalyticBound.const _ (by simp)
  | st :: r, x => by
    simp only [pathHolonomy, Submonoid.coe_mul]
    refine AnalyticBound.mul ?_ (AnalyticBound.holonomy c X W r _)
    unfold linkValue
    by_cases h : st.2 = true
    · simp only [h, if_true]
      exact AnalyticBound.leftTranslate c X W x st.1
    · simp only [h, Bool.false_eq_true, if_false]
      exact (AnalyticBound.leftTranslate c X W (x - unitStep j st.1) st.1).comp_clm starCLM norm_starCLM_le
private def plaquetteCost {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) (V : F.GaugeField j) : ℝ :=
  1 - ((plaquetteHolonomy V p : UnitQuaternion) : ℍ[ℝ]).re
private def plaquetteDerivBound (R : ℝ) (m : ℕ) : ℝ := 1 + holonomyDerivBound R 4 m
private theorem AnalyticBound.plaquetteCost {j n : ℕ} (c : Fin n → F.Site j × Fin 4)
    (X : Fin n → imaginaryQuaternions) (W : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4) :
    AnalyticBound (fun τ => plaquetteCost p (ColdStepAtMirrorFrames.leftTranslate (bondSpread c X τ) W))
      (plaquetteDerivBound (totalNorm X)) := by
  have h := (AnalyticBound.holonomy c X W [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] p.1).comp_clm
    (-reCLM) (by rw [norm_neg]; exact norm_reCLM_le)
  have h2 := (AnalyticBound.const (n := n) (1 : ℝ) (by simp)).add h
  have hfun : (fun τ => ColdStepAtMirrorFrames.plaquetteCost p (ColdStepAtMirrorFrames.leftTranslate (bondSpread c X τ) W)) = fun τ => (1 : ℝ) +
      (-reCLM) ((pathHolonomy (ColdStepAtMirrorFrames.leftTranslate (bondSpread c X τ) W) p.1
        [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ]) := by
    funext τ
    simp only [ColdStepAtMirrorFrames.plaquetteCost, plaquetteHolonomy, _root_.neg_apply, reCLM_apply]
    ring
  rw [hfun]
  exact h2
private theorem plaquetteHolonomy_eq {j : ℕ} (U : F.GaugeField j) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteHolonomy U (x, μ, ν) =
      U x μ * (U (x + unitStep j μ) ν * ((U (x + unitStep j ν) μ)⁻¹ * ((U x ν)⁻¹ * 1))) := by apply _root_.YangMills.SharedProofs.p41793 <;> assumption
private def plaquetteEdges {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) : Finset (F.Site j × Fin 4) :=
  {(p.1, p.2.1), (p.1 + unitStep j p.2.1, p.2.2), (p.1 + unitStep j p.2.2, p.2.1), (p.1, p.2.2)}
private theorem plaquetteCost_congr {j : ℕ} {p : F.Site j × Fin 4 × Fin 4} {U U' : F.GaugeField j}
    (h : ∀ b ∈ plaquetteEdges p, U b.1 b.2 = U' b.1 b.2) : plaquetteCost p U = plaquetteCost p U' := by
  obtain ⟨x, μ, ν⟩ := p
  unfold plaquetteCost
  rw [plaquetteHolonomy_eq, plaquetteHolonomy_eq]
  rw [h (x, μ) (by simp [plaquetteEdges]), h (x + unitStep j μ, ν) (by simp [plaquetteEdges]),
    h (x + unitStep j ν, μ) (by simp [plaquetteEdges]), h (x, ν) (by simp [plaquetteEdges])]
private theorem iteratedFDeriv_plaquetteCost_eq_zero {j n : ℕ} (c : Fin n → F.Site j × Fin 4)
    (X : Fin n → imaginaryQuaternions) (W : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4) (l : Fin n)
    (hl : c l ∉ plaquetteEdges p) :
    iteratedFDeriv ℝ n (fun τ => plaquetteCost p (leftTranslate (bondSpread c X τ) W)) 0
      (fun l => Pi.single l 1) = 0 := by
  refine iteratedFDeriv_single_eq_zero_of_indep (AnalyticBound.plaquetteCost c X W p).1 l fun τ => ?_
  refine plaquetteCost_congr fun b hb => ?_
  have hspread : bondSpread c X τ b.1 b.2 = bondSpread c X (Function.update τ l 0) b.1 b.2 := by
    unfold bondSpread
    refine Finset.sum_congr rfl fun l' _ => ?_
    by_cases hl' : l' = l
    · subst hl'
      have hne : c l' ≠ (b.1, b.2) := fun e => hl (by rw [e]; exact hb)
      rw [if_neg hne, if_neg hne]
    · rw [Function.update_of_ne hl']
  simp only [leftTranslate, hspread]
private theorem leftTranslate_bondSpread_zero {j n : ℕ} (c : Fin n → F.Site j × Fin 4)
    (X : Fin n → imaginaryQuaternions) (W : F.GaugeField j) : leftTranslate (bondSpread c X 0) W = W := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
private def bondDirection {j : ℕ} (c : Fin 1 → F.Site j × Fin 4) (X : Fin 1 → imaginaryQuaternions)
    (b : F.Site j × Fin 4) : ℍ[ℝ] :=
  if c 0 = b then (X 0 : ℍ[ℝ]) else 0
private theorem bondDirection_re {j : ℕ} (c : Fin 1 → F.Site j × Fin 4) (X : Fin 1 → imaginaryQuaternions)
    (b : F.Site j × Fin 4) : (bondDirection c X b).re = 0 := by
  unfold bondDirection
  split_ifs
  · exact (X 0).2
  · rfl
private theorem bondDirection_norm_le {j : ℕ} (c : Fin 1 → F.Site j × Fin 4) (X : Fin 1 → imaginaryQuaternions)
    (hX : ‖X 0‖ ≤ 1) (b : F.Site j × Fin 4) : ‖bondDirection c X b‖ ≤ 1 := by
  unfold bondDirection
  split_ifs
  · exact hX
  · simp
private theorem bondLinear_line {j : ℕ} (c : Fin 1 → F.Site j × Fin 4) (X : Fin 1 → imaginaryQuaternions)
    (b : F.Site j × Fin 4) (t : ℝ) : bondLinear c X b (fun _ => t) = t • bondDirection c X b := by
  unfold bondLinear bondDirection
  rw [_root_.sum_apply, Fin.sum_univ_one]
  by_cases h : c 0 = b
  · simp [h]
  · simp [h]
private theorem star_eq_neg_of_re_eq_zero {q : ℍ[ℝ]} (h : q.re = 0) : star q = -q := by apply _root_.YangMills.Construction.BlockAverages.star_eq_neg_of_re_eq_zero <;> assumption
private theorem hasDerivAt_leftTranslate_line {j : ℕ} (c : Fin 1 → F.Site j × Fin 4)
    (X : Fin 1 → imaginaryQuaternions) (W : F.GaugeField j) (x : F.Site j) (i : Fin 4) :
    HasDerivAt (fun t : ℝ => ((leftTranslate (bondSpread c X fun _ => t) W x i : UnitQuaternion) : ℍ[ℝ]))
      (bondDirection c X (x, i) * (W x i : ℍ[ℝ])) 0 := by
  have hfun : (fun t : ℝ => ((leftTranslate (bondSpread c X fun _ => t) W x i : UnitQuaternion) : ℍ[ℝ])) =
      fun t => NormedSpace.exp (t • bondDirection c X (x, i)) * (W x i : ℍ[ℝ]) := by
    funext t
    rw [coe_leftTranslate, bondLinear_line]
  rw [hfun]
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (bondDirection c X (x, i)) (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h.mul_const _
private theorem exists_hasDerivAt_linkValue {j : ℕ} (c : Fin 1 → F.Site j × Fin 4) (X : Fin 1 → imaginaryQuaternions)
    (hX : ‖X 0‖ ≤ 1) (W : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    ∃ Z : ℍ[ℝ], Z.re = 0 ∧ ‖Z‖ ≤ 1 ∧
      HasDerivAt (fun t : ℝ => ((linkValue (leftTranslate (bondSpread c X fun _ => t) W) x st : UnitQuaternion) : ℍ[ℝ]))
        (Z * ((linkValue W x st : UnitQuaternion) : ℍ[ℝ])) 0 := by
  unfold linkValue
  by_cases h : st.2 = true
  · simp only [h, if_true]
    exact ⟨_, bondDirection_re c X _, bondDirection_norm_le c X hX _, hasDerivAt_leftTranslate_line c X W x st.1⟩
  · simp only [h, Bool.false_eq_true, if_false]
    set x' := x - unitStep j st.1
    set ξ := bondDirection c X (x', st.1)
    set g : UnitQuaternion := (W x' st.1)⁻¹ with hg
    refine ⟨(g : ℍ[ℝ]) * (-ξ) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]), ?_, ?_, ?_⟩
    · rw [PlaquetteLinearization.re_coe_mul_mul_coe_inv]
      have := bondDirection_re c X (x', st.1)
      simp [ξ, this]
    · rw [PlaquetteLinearization.norm_coe_mul_mul_coe_inv, norm_neg]
      exact bondDirection_norm_le c X hX _
    · have h1 := starCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_leftTranslate_line c X W x' st.1)
      have e2 : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by
        rw [← Submonoid.coe_mul, inv_mul_cancel]
        rfl
      have e3 : starCLM (ξ * (W x' st.1 : ℍ[ℝ])) =
          (g : ℍ[ℝ]) * (-ξ) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) := by
        rw [mul_assoc _ _ (g : ℍ[ℝ]), e2, mul_one, starCLM_apply, star_mul,
          star_eq_neg_of_re_eq_zero (bondDirection_re c X (x', st.1))]
        rfl
      rw [← e3]
      exact h1
private theorem exists_hasDerivAt_holonomy {j : ℕ} (c : Fin 1 → F.Site j × Fin 4) (X : Fin 1 → imaginaryQuaternions)
    (hX : ‖X 0‖ ≤ 1) (W : F.GaugeField j) :
    ∀ (p : List PathStep) (x : F.Site j), ∃ Y : ℍ[ℝ], Y.re = 0 ∧ ‖Y‖ ≤ p.length ∧
      HasDerivAt (fun t : ℝ => ((pathHolonomy (leftTranslate (bondSpread c X fun _ => t) W) x p : UnitQuaternion) : ℍ[ℝ]))
        (Y * ((pathHolonomy W x p : UnitQuaternion) : ℍ[ℝ])) 0
  | [], x => ⟨0, rfl, by simp, by
      simp only [pathHolonomy, OneMemClass.coe_one, zero_mul]
      exact hasDerivAt_const _ _⟩
  | st :: r, x => by
    obtain ⟨Y', hYr, hYn, hB⟩ := exists_hasDerivAt_holonomy c X hX W r (x + stepDisplacement j st)
    obtain ⟨Z, hZr, hZn, hA⟩ := exists_hasDerivAt_linkValue c X hX W x st
    set g : UnitQuaternion := linkValue W x st with hg
    set B : ℍ[ℝ] := ((pathHolonomy W (x + stepDisplacement j st) r : UnitQuaternion) : ℍ[ℝ]) with hBdef
    refine ⟨Z + (g : ℍ[ℝ]) * Y' * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]), ?_, ?_, ?_⟩
    · show Z.re + ((g : ℍ[ℝ]) * Y' * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = 0
      rw [PlaquetteLinearization.re_coe_mul_mul_coe_inv, hZr, hYr, add_zero]
    · refine (norm_add_le _ _).trans ?_
      rw [PlaquetteLinearization.norm_coe_mul_mul_coe_inv]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith
    · have h := hA.mul hB
      have z0 : (fun _ : Fin 1 => (0 : ℝ)) = 0 := rfl
      simp only [pathHolonomy, Submonoid.coe_mul]
      have e0 : ((linkValue (leftTranslate (bondSpread c X fun _ => (0 : ℝ)) W) x st : UnitQuaternion) : ℍ[ℝ]) =
          (g : ℍ[ℝ]) := by
        rw [z0, leftTranslate_bondSpread_zero]
      rw [e0] at h
      have e1 : (Z + (g : ℍ[ℝ]) * Y' * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) * ((g : ℍ[ℝ]) * B) =
          Z * (g : ℍ[ℝ]) *
              ((pathHolonomy (leftTranslate (bondSpread c X fun _ => (0 : ℝ)) W) (x + stepDisplacement j st) r :
                UnitQuaternion) : ℍ[ℝ]) +
            (g : ℍ[ℝ]) * (Y' * B) := by
        rw [z0, leftTranslate_bondSpread_zero, add_mul, mul_assoc ((g : ℍ[ℝ]) * Y'),
          PlaquetteLinearization.inv_coe_mul_coe_mul, mul_assoc Z, mul_assoc (g : ℍ[ℝ])]
      rw [e1]
      exact h
private theorem abs_first_deriv_plaquetteCost_le {j : ℕ} (c : Fin 1 → F.Site j × Fin 4)
    (X : Fin 1 → imaginaryQuaternions) (hX : ‖X 0‖ ≤ 1) (W : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4) :
    |iteratedFDeriv ℝ 1 (fun τ => plaquetteCost p (leftTranslate (bondSpread c X τ) W)) 0
        (fun l => Pi.single l 1)| ≤
      4 * plaquetteDefect W p := by
  obtain ⟨Y, hYr, hYn, hY⟩ :=
    exists_hasDerivAt_holonomy c X hX W [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] p.1
  set f : (Fin 1 → ℝ) → ℝ := fun τ => plaquetteCost p (leftTranslate (bondSpread c X τ) W) with hf
  have hd : DifferentiableAt ℝ f 0 := ((AnalyticBound.plaquetteCost c X W p).1.differentiable (by simp)) 0
  have hline : HasDerivAt (fun t : ℝ => (fun _ : Fin 1 => t)) (fun _ => (1 : ℝ)) 0 :=
    hasDerivAt_pi.2 fun _ => hasDerivAt_id 0
  have h1 : HasDerivAt (fun t : ℝ => f fun _ => t) (fderiv ℝ f 0 fun _ => 1) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) (f := fun t : ℝ => (fun _ : Fin 1 => t)) hd.hasFDerivAt hline
  have h2 : HasDerivAt (fun t : ℝ => f fun _ => t)
      (-(Y * ((plaquetteHolonomy W p : UnitQuaternion) : ℍ[ℝ])).re) 0 := by
    have h3 := reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hY
    have h4 := h3.const_sub (1 : ℝ)
    have hfun : (fun t : ℝ => f fun _ => t) = fun t => 1 - (reCLM ∘ fun t : ℝ =>
        ((pathHolonomy (leftTranslate (bondSpread c X fun _ => t) W) p.1
          [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ])) t := by
      funext t
      simp only [hf, plaquetteCost, plaquetteHolonomy, Function.comp, reCLM_apply]
    rw [hfun]
    have hre : reCLM (Y * ((pathHolonomy W p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] :
        UnitQuaternion) : ℍ[ℝ])) = (Y * ((plaquetteHolonomy W p : UnitQuaternion) : ℍ[ℝ])).re := reCLM_apply _
    rw [← hre]
    exact h4
  have e0 : iteratedFDeriv ℝ 1 f 0 (fun l => Pi.single l 1) =
      -(Y * ((plaquetteHolonomy W p : UnitQuaternion) : ℍ[ℝ])).re := by
    rw [iteratedFDeriv_one_apply]
    have e1 : (Pi.single 0 1 : Fin 1 → ℝ) = fun _ => 1 := by
      funext l
      rw [Subsingleton.elim l 0]
      simp
    rw [e1]
    exact h1.unique h2
  rw [e0, abs_neg]
  have e2 : (Y * ((plaquetteHolonomy W p : UnitQuaternion) : ℍ[ℝ])).re =
      (Y * (((plaquetteHolonomy W p : UnitQuaternion) : ℍ[ℝ]) - 1)).re := by
    rw [mul_sub, mul_one]
    show _ = (Y * ((plaquetteHolonomy W p : UnitQuaternion) : ℍ[ℝ])).re - Y.re
    rw [hYr, sub_zero]
  rw [e2]
  have e3 : |(Y * (((plaquetteHolonomy W p : UnitQuaternion) : ℍ[ℝ]) - 1)).re| ≤
      ‖Y * (((plaquetteHolonomy W p : UnitQuaternion) : ℍ[ℝ]) - 1)‖ := by
    rw [← reCLM_apply, ← Real.norm_eq_abs]
    exact (reCLM.le_opNorm _).trans (by
      have := norm_reCLM_le
      exact (mul_le_of_le_one_left (norm_nonneg _) this))
  refine e3.trans ?_
  rw [norm_mul]
  unfold plaquetteDefect
  have hY4 : ‖Y‖ ≤ 4 := by simpa using hYn
  exact mul_le_mul_of_nonneg_right hY4 (norm_nonneg _)
private def planePairs : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun P => P.1 < P.2
private def cornerOffset (P : Fin 4 × Fin 4) (e : Bool × Bool) : Fin 4 → ℤ :=
  (if e.1 then Pi.single P.1 1 else 0) + (if e.2 then Pi.single P.2 1 else 0)
private def plaquetteAtCorner {j : ℕ} (y : F.Site j) (q : (Fin 4 × Fin 4) × (Bool × Bool)) :
    F.Site j × Fin 4 × Fin 4 :=
  (y + siteOfCoords j (-(cornerOffset q.1 q.2)), q.1.1, q.1.2)
private def cornerPlaquetteIndex : Finset ((Fin 4 × Fin 4) × (Bool × Bool)) := planePairs ×ˢ Finset.univ
private theorem sum_plaquetteCorners {j : ℕ} (hper : ∀ i, 2 ≤ F.period j i) (x : F.Site j) {μ ν : Fin 4}
    (hμν : μ ≠ ν) (f : F.Site j → ℝ) :
    ∑ z ∈ plaquetteCorners (x, μ, ν), f z = ∑ e : Bool × Bool, f (x + siteOfCoords j (cornerOffset (μ, ν) e)) := by
  have hne : ∀ i, (1 : ZMod (F.period j i)) ≠ 0 := fun i => by
    haveI : Fact (1 < F.period j i) := ⟨by have := hper i; omega⟩
    exact one_ne_zero
  set u : F.Site j := unitStep j μ with hu
  set v : F.Site j := unitStep j ν with hv
  have huμ : u μ = 1 := by simp [hu, unitStep, siteOfCoords]
  have huν : u ν = 0 := by simp [hu, unitStep, siteOfCoords, Pi.single_apply, hμν.symm]
  have hvμ : v μ = 0 := by simp [hv, unitStep, siteOfCoords, Pi.single_apply, hμν]
  have hvν : v ν = 1 := by simp [hv, unitStep, siteOfCoords]
  have sep : ∀ A B : F.Site j, (A μ ≠ B μ ∨ A ν ≠ B ν) → x + A ≠ x + B := by
    intro A B h e
    have e' := add_left_cancel e
    rcases h with h | h
    · exact h (congrFun e' μ)
    · exact h (congrFun e' ν)
  have n1 : (1 : ZMod (F.period j μ)) ≠ 0 := hne μ
  have n2 : (1 : ZMod (F.period j ν)) ≠ 0 := hne ν
  have a1 : x ≠ x + u := fun h => sep 0 u (Or.inl (by simp [huμ, n1.symm])) (by rw [add_zero]; exact h)
  have a2 : x ≠ x + v := fun h => sep 0 v (Or.inr (by simp [hvν, n2.symm])) (by rw [add_zero]; exact h)
  have a3 : x ≠ x + u + v := fun h => sep 0 (u + v) (Or.inl (by simp [huμ, hvμ, n1.symm]))
    (by rw [add_zero, ← add_assoc]; exact h)
  have a4 : x + u ≠ x + v := sep u v (Or.inl (by simp [huμ, hvμ, n1]))
  have a5 : x + u ≠ x + u + v := fun h => sep u (u + v) (Or.inr (by simp [huν, hvν, n2.symm]))
    (by rw [← add_assoc]; exact h)
  have a6 : x + v ≠ x + u + v := fun h => sep v (u + v) (Or.inl (by simp [huμ, hvμ, n1.symm]))
    (by rw [← add_assoc]; exact h)
  have e00 : siteOfCoords j (cornerOffset (μ, ν) (false, false)) = (0 : F.Site j) := by
    simp [cornerOffset, siteOfCoords_zero]
  have e10 : siteOfCoords j (cornerOffset (μ, ν) (true, false)) = u := by
    simp [cornerOffset, hu, unitStep]
  have e01 : siteOfCoords j (cornerOffset (μ, ν) (false, true)) = v := by
    simp [cornerOffset, hv, unitStep]
  have e11 : siteOfCoords j (cornerOffset (μ, ν) (true, true)) = u + v := by
    simp only [cornerOffset, if_true, siteOfCoords_add]
    rfl
  show ∑ z ∈ ({x, x + u, x + v, x + u + v} : Finset (F.Site j)), f z = _
  rw [Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨a1, a2, a3⟩), Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨a4, a5⟩), Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact a6), Finset.sum_singleton, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool,
    Fintype.sum_bool, e00, e10, e01, e11, add_zero, ← add_assoc x u v]
  ring
private theorem mem_innerPlaquettes_finiteCells {H : BlockFrame} (hodd : Odd H.blockSide) (hs : ∀ i, 0 < H.extent i)
    {k : ℕ} (hk : k ≤ H.top) (p : H.Site k × Fin 4 × Fin 4) :
    p ∈ innerPlaquettes (finiteCells H) k ↔ p.2.1 < p.2.2 := by
  unfold innerPlaquettes
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
  constructor
  · exact fun h => h.2.1
  · intro h
    exact ⟨⟨mem_allSites hodd hs hk _, Finset.mem_univ _, Finset.mem_univ _⟩, h,
      fun x _ => mem_allSites hodd hs hk x⟩
private theorem sum_innerPlaquettes {k : ℕ} (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (hk : k ≤ F.top)
    (g : F.Site k × Fin 4 × Fin 4 → ℝ) :
    ∑ p ∈ innerPlaquettes (finiteCells F) k, g p = ∑ P ∈ planePairs, ∑ x ∈ allSites F k, g (x, P.1, P.2) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => ((p.2.1, p.2.2), p.1)) (fun q => (q.2, q.1.1, q.1.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have := (mem_innerPlaquettes_finiteCells hL hs hk p).1 hp
    exact Finset.mem_product.2 ⟨by simp [planePairs, this], mem_allSites hL hs hk _⟩
  · intro q hq
    have := (Finset.mem_filter.1 (Finset.mem_product.1 hq).1).2
    exact (mem_innerPlaquettes_finiteCells hL hs hk _).2 this
  · intro p _
    rfl
  · intro q _
    rfl
  · intro p _
    rfl
private abbrev levelZeroFrame (L : ℕ) (side : Fin 4 → ℕ) : BlockFrame := ⟨L, 0, side⟩
variable {L : ℕ} {side : Fin 4 → ℕ}
private theorem ancestorSite_levelZero (x : (levelZeroFrame L side).Site 0) :
    ancestorSite (F := levelZeroFrame L side) 0 x = x := by
  unfold ancestorSite
  have hfun : (fun i => (siteCoords x i + (((levelZeroFrame L side).blockSide : ℤ) ^ (0 - 0) - 1) / 2) /
      ((levelZeroFrame L side).blockSide : ℤ) ^ (0 - 0)) = siteCoords x := by
    funext i
    simp
  rw [hfun, siteOfCoords_siteCoords]
private theorem two_le_period_levelZero {L : ℕ} {side : Fin 4 → ℕ} (hL : Odd L) (hs : ∀ i, 2 ≤ side i) (i : Fin 4) :
    2 ≤ (levelZeroFrame L side).period 0 i := by
  show 2 ≤ side i * L ^ (0 + 1 - 0)
  have := Nat.le_mul_of_pos_right (side i) (pow_pos hL.pos (0 + 1 - 0))
  exact (hs i).trans this
private theorem chainSiteShare_eq (hL : Odd L) (hs : ∀ i, 2 ≤ side i) (a : ℝ) (y : (levelZeroFrame L side).Site 0)
    (X : (levelZeroFrame L side).FieldChain) :
    chainSiteShare a (finiteCells (levelZeroFrame L side)) y X =
      (1 / 4) * ∑ q ∈ cornerPlaquetteIndex, plaquetteCost (plaquetteAtCorner y q) (X 0) := by
  have hs0 : ∀ i, 0 < (levelZeroFrame L side).extent i := fun i => by
    have := hs i
    show 0 < side i
    omega
  have e0 : ∀ g : ℕ → ℝ, ∑ j ∈ Finset.range (levelZeroFrame L side).depth, g j = 0 :=
    fun g => Finset.sum_range_zero g
  unfold chainSiteShare
  rw [e0, mul_zero, add_zero, sum_innerPlaquettes hL hs0 (Nat.zero_le _)]
  unfold cornerPlaquetteIndex
  rw [Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hlt : P.1 < P.2 := (Finset.mem_filter.1 hP).2
  have step : ∀ x : (levelZeroFrame L side).Site 0, (∑ z ∈ plaquetteCorners (x, P.1, P.2),
      if ancestorSite (F := levelZeroFrame L side) (levelZeroFrame L side).depth z = y then (1 / 4 : ℝ) else 0) =
      ∑ e : Bool × Bool, if x + siteOfCoords 0 (cornerOffset P e) = y then (1 / 4 : ℝ) else 0 := by
    intro x
    rw [sum_plaquetteCorners (two_le_period_levelZero hL hs) x hlt.ne]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : x + siteOfCoords 0 (cornerOffset P e) = y
    · rw [if_pos h, if_pos]
      exact (ancestorSite_levelZero _).trans h
    · rw [if_neg h, if_neg]
      exact fun e' => h ((ancestorSite_levelZero _).symm.trans e')
  dsimp only
  simp only [step, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_eq_single (y + siteOfCoords 0 (-(cornerOffset P e)))]
  · have : y + siteOfCoords 0 (-(cornerOffset P e)) + siteOfCoords 0 (cornerOffset P e) = y := by
      rw [siteOfCoords_neg, neg_add_cancel_right]
    rw [if_pos this]
    rfl
  · intro x _ hx
    rw [if_neg, zero_mul]
    intro h
    apply hx
    rw [← h, siteOfCoords_neg, add_neg_cancel_right]
  · intro h
    exact absurd (mem_allSites hL hs0 (Nat.zero_le _) _) h
private theorem minimalSiteShare_eq (hL : Odd L) (hs : ∀ i, 2 ≤ side i) (a : ℝ) (y : (levelZeroFrame L side).Site 0)
    (V : (levelZeroFrame L side).GaugeField 0) :
    minimalSiteShare a y V = (1 / 4) * ∑ q ∈ cornerPlaquetteIndex, plaquetteCost (plaquetteAtCorner y q) V := by
  have e0 : ∀ g : ℕ → ℝ, ∑ j ∈ Finset.range (levelZeroFrame L side).depth, g j = 0 :=
    fun g => Finset.sum_range_zero g
  have hex : ∃ X, IsMinimizingChainBelow a (finiteCells (levelZeroFrame L side)) V X := by
    refine ⟨Function.update (fun k => (fun _ _ => 1 : (levelZeroFrame L side).GaugeField k)) 0 V,
      Function.update_self _ _ _, ?_⟩
    intro X' hX'
    have e : X' 0 = V := hX'
    apply le_of_eq
    unfold chainActionBelow
    rw [e0, e0, e, Function.update_self]
  unfold minimalSiteShare
  rw [dif_pos hex, chainSiteShare_eq hL hs]
  have e : hex.choose 0 = V := hex.choose_spec.1
  rw [e]
private theorem minimalAction_eq (hL : Odd L) (hs : ∀ i, 2 ≤ side i) (a : ℝ) (V : (levelZeroFrame L side).GaugeField 0) :
    minimalAction a (finiteCells (levelZeroFrame L side)) 0 V =
      ∑ P ∈ planePairs, ∑ x ∈ allSites (levelZeroFrame L side) 0, plaquetteCost (x, P.1, P.2) V := by
  have hs0 : ∀ i, 0 < (levelZeroFrame L side).extent i := fun i => by
    have := hs i
    show 0 < side i
    omega
  show wilsonAction (finiteCells (levelZeroFrame L side)) V = _
  unfold wilsonAction
  rw [sum_innerPlaquettes hL hs0 (Nat.zero_le _)]
  rfl
private theorem bondDeriv_sum {j n : ℕ} {ι : Type} (S : Finset ι) (ps : ι → F.Site j × Fin 4 × Fin 4)
    (W : F.GaugeField j) (c : Fin n → F.Site j × Fin 4) (X : Fin n → imaginaryQuaternions) :
    bondDeriv (fun V => ∑ i ∈ S, plaquetteCost (ps i) V) W c X = ∑ i ∈ S, bondDeriv (plaquetteCost (ps i)) W c X := by
  unfold bondDeriv
  have e := iteratedFDeriv_sum (𝕜 := ℝ) (i := n) (u := S)
    (f := fun i τ => plaquetteCost (ps i) (leftTranslate (bondSpread c X τ) W))
    (fun i _ => (AnalyticBound.plaquetteCost c X W (ps i)).1.of_le le_top)
  rw [e, Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
private theorem contDiff_sum_plaquetteCost {j n : ℕ} {ι : Type} (S : Finset ι) (ps : ι → F.Site j × Fin 4 × Fin 4)
    (W : F.GaugeField j) (c : Fin n → F.Site j × Fin 4) (X : Fin n → imaginaryQuaternions) :
    ContDiff ℝ ω (fun τ => ∑ i ∈ S, plaquetteCost (ps i) (leftTranslate (bondSpread c X τ) W)) :=
  ContDiff.sum fun i _ => (AnalyticBound.plaquetteCost c X W (ps i)).1
private theorem bondDeriv_quarter_sum {j n : ℕ} {ι : Type} (S : Finset ι) (ps : ι → F.Site j × Fin 4 × Fin 4)
    (W : F.GaugeField j) (c : Fin n → F.Site j × Fin 4) (X : Fin n → imaginaryQuaternions) :
    bondDeriv (fun V => (1 / 4 : ℝ) * ∑ i ∈ S, plaquetteCost (ps i) V) W c X =
      (1 / 4) * ∑ i ∈ S, bondDeriv (plaquetteCost (ps i)) W c X := by
  rw [← bondDeriv_sum]
  unfold bondDeriv
  have e1 : (fun τ => (1 / 4 : ℝ) * ∑ i ∈ S, plaquetteCost (ps i) (leftTranslate (bondSpread c X τ) W)) =
      (1 / 4 : ℝ) • fun τ => ∑ i ∈ S, plaquetteCost (ps i) (leftTranslate (bondSpread c X τ) W) := by
    funext τ
    simp
  rw [e1, iteratedFDeriv_const_smul_apply ((contDiff_sum_plaquetteCost S ps W c X).contDiffAt.of_le le_top)]
  simp
private theorem abs_bondDeriv_plaquetteCost_le {j n : ℕ} (c : Fin n → F.Site j × Fin 4)
    {X : Fin n → imaginaryQuaternions} (hX : AreUnitVectors X) (W : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4) :
    |bondDeriv (plaquetteCost p) W c X| ≤ plaquetteDerivBound n n := by
  have h := (AnalyticBound.plaquetteCost c X W p).2 n
  rw [totalNorm_of_units hX] at h
  exact (abs_iteratedFDeriv_single_le _).trans h
private theorem valMinAbs_intCast_of_small {n : ℕ} (hn : 0 < n) (m : ℤ) (h : 2 * |m| < n) :
    ((m : ZMod n)).valMinAbs = m := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩ <;> cases abs_cases m <;> omega
private theorem siteSupDist_add_siteOfCoords {j : ℕ} (hp : ∀ i, 0 < F.period j i) (y : F.Site j) (u : Fin 4 → ℤ)
    (h : ∀ i, 2 * |u i| < F.period j i) :
    siteSupDist y (y + siteOfCoords j u) = Finset.univ.sup fun i => (u i).natAbs := by
  unfold siteSupDist
  refine Finset.sup_congr rfl fun i _ => ?_
  have e : y i - (y + siteOfCoords j u : F.Site j) i = ((-(u i) : ℤ) : ZMod (F.period j i)) := by
    simp [siteOfCoords]
  rw [e, valMinAbs_intCast_of_small (hp i) _ (by rw [abs_neg]; exact h i), Int.natAbs_neg]
private theorem siteSupDist_add_le_one {j : ℕ} (hp : ∀ i, 3 ≤ F.period j i) (y : F.Site j) (u : Fin 4 → ℤ)
    (h : ∀ i, |u i| ≤ 1) : siteSupDist y (y + siteOfCoords j u) ≤ 1 := by
  rw [siteSupDist_add_siteOfCoords (fun i => by have := hp i; omega) y u fun i => by
    have h1 := h i
    have h2 := hp i
    omega]
  refine Finset.sup_le fun i _ => ?_
  have h1 := abs_le.1 (h i)
  omega
private theorem exists_offset_of_mem_plaquetteEdges {j : ℕ} {p : F.Site j × Fin 4 × Fin 4} {b : F.Site j × Fin 4}
    (hb : b ∈ plaquetteEdges p) :
    ∃ o : Fin 4 → ℤ, (o = 0 ∨ o = Pi.single p.2.1 1 ∨ o = Pi.single p.2.2 1) ∧ b.1 = p.1 + siteOfCoords j o := by
  obtain ⟨x, μ, ν⟩ := p
  simp only [plaquetteEdges, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨0, Or.inl rfl, by simp [siteOfCoords_zero]⟩
  · exact ⟨Pi.single μ 1, Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨Pi.single ν 1, Or.inr (Or.inr rfl), rfl⟩
  · exact ⟨0, Or.inl rfl, by simp [siteOfCoords_zero]⟩
private theorem single_one_bounds (μ i : Fin 4) :
    0 ≤ (Pi.single μ 1 : Fin 4 → ℤ) i ∧ (Pi.single μ 1 : Fin 4 → ℤ) i ≤ 1 := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.single_one_bounds <;> assumption
private theorem single_add_single_le_one {μ ν : Fin 4} (h : μ ≠ ν) (i : Fin 4) :
    (Pi.single μ 1 : Fin 4 → ℤ) i + (Pi.single ν 1 : Fin 4 → ℤ) i ≤ 1 := by
  by_cases a : i = μ
  · have b : i ≠ ν := fun e => h (a.symm.trans e)
    subst a
    simp [b]
  · by_cases b : i = ν
    · subst b
      simp [a]
    · simp [a, b]
private theorem cornerOffset_bounds {P : Fin 4 × Fin 4} (hP : P.1 ≠ P.2) (e : Bool × Bool) (i : Fin 4) :
    0 ≤ cornerOffset P e i ∧ cornerOffset P e i ≤ 1 := by
  obtain ⟨e1, e2⟩ := e
  have a := single_one_bounds P.1 i
  have b := single_one_bounds P.2 i
  have c := single_add_single_le_one hP i
  have e : cornerOffset P (e1, e2) i = (if e1 then (Pi.single P.1 1 : Fin 4 → ℤ) i else 0) +
      (if e2 then (Pi.single P.2 1 : Fin 4 → ℤ) i else 0) := by
    cases e1 <;> cases e2 <;> rfl
  rw [e]
  cases e1 <;> cases e2 <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero, zero_add] <;> omega
private theorem offset_bounds {μ ν : Fin 4} {o : Fin 4 → ℤ}
    (h : o = 0 ∨ o = Pi.single μ 1 ∨ o = Pi.single ν 1) (i : Fin 4) : 0 ≤ o i ∧ o i ≤ 1 := by
  rcases h with rfl | rfl | rfl
  · simp
  · exact single_one_bounds μ i
  · exact single_one_bounds ν i
private theorem siteSupDist_le_one_of_mem_plaquetteEdges {j : ℕ} (hp : ∀ i, 3 ≤ F.period j i)
    {p : F.Site j × Fin 4 × Fin 4} {b b' : F.Site j × Fin 4} (hb : b ∈ plaquetteEdges p)
    (hb' : b' ∈ plaquetteEdges p) : siteSupDist b.1 b'.1 ≤ 1 := by
  obtain ⟨o, ho, e⟩ := exists_offset_of_mem_plaquetteEdges hb
  obtain ⟨o', ho', e'⟩ := exists_offset_of_mem_plaquetteEdges hb'
  have h : b'.1 = b.1 + siteOfCoords j (o' - o) := by
    rw [e, e', sub_eq_add_neg, siteOfCoords_add, siteOfCoords_neg]
    abel
  rw [h]
  refine siteSupDist_add_le_one hp _ _ fun i => ?_
  have h1 := offset_bounds ho i
  have h2 := offset_bounds ho' i
  rw [Pi.sub_apply, abs_le]
  omega
private theorem siteSupDist_corner_le_one {j : ℕ} (hp : ∀ i, 3 ≤ F.period j i) (y : F.Site j)
    {q : (Fin 4 × Fin 4) × (Bool × Bool)} (hq : q ∈ cornerPlaquetteIndex) {b : F.Site j × Fin 4}
    (hb : b ∈ plaquetteEdges (plaquetteAtCorner y q)) : siteSupDist y b.1 ≤ 1 := by
  obtain ⟨o, ho, e⟩ := exists_offset_of_mem_plaquetteEdges hb
  have hP : q.1.1 ≠ q.1.2 := ((Finset.mem_filter.1 (Finset.mem_product.1 hq).1).2).ne
  have h : b.1 = y + siteOfCoords j (o - cornerOffset q.1 q.2) := by
    rw [e]
    simp only [plaquetteAtCorner]
    rw [sub_eq_add_neg, siteOfCoords_add]
    abel
  rw [h]
  refine siteSupDist_add_le_one hp _ _ fun i => ?_
  have h1 := offset_bounds ho i
  have h2 := cornerOffset_bounds hP q.2 i
  rw [Pi.sub_apply, abs_le]
  omega
private theorem half_le_exp_neg_mul {δ d : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 8) (hd0 : 0 ≤ d) (hd : d ≤ 1) :
    1 / 2 ≤ Real.exp (-δ * d) := by
  have := Real.add_one_le_exp (-δ * d)
  nlinarith
private theorem card_cornerPlaquetteIndex : cornerPlaquetteIndex.card = 24 := by decide
private theorem abs_quarter_sum_le {ι : Type} (S : Finset ι) (hS : S.card = 24) (D : ι → ℝ) {B : ℝ}
    (hD : ∀ i ∈ S, |D i| ≤ B) : |(1 / 4 : ℝ) * ∑ i ∈ S, D i| ≤ 6 * B := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  have h : |∑ i ∈ S, D i| ≤ 24 * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul S _ B hD
    rw [hS] at this
    simpa using this
  linarith
private theorem abs_bondDeriv_minimalSiteShare_le (hL : Odd L) (hs : ∀ i, 64 ≤ side i) {a δ B : ℝ} (h0 : 0 ≤ δ)
    (h1 : δ ≤ 1 / 8) {n : ℕ} (W : (levelZeroFrame L side).GaugeField 0) (y : (levelZeroFrame L side).Site 0)
    (c : Fin n → (levelZeroFrame L side).Site 0 × Fin 4) (X : Fin n → imaginaryQuaternions) (hn : 1 ≤ n)
    (hB0 : 0 ≤ B) (hB : ∀ q ∈ cornerPlaquetteIndex, |bondDeriv (plaquetteCost (plaquetteAtCorner y q)) W c X| ≤ B) :
    |bondDeriv (minimalSiteShare a y) W c X| ≤ 12 * B * Real.exp (-δ * bondListDist y c) := by
  have hs2 : ∀ i, 2 ≤ side i := fun i => by have := hs i; omega
  have hp3 : ∀ i, 3 ≤ (levelZeroFrame L side).period 0 i := fun i => by
    show 3 ≤ side i * L ^ (0 + 1 - 0)
    have h := Nat.le_mul_of_pos_right (side i) (pow_pos hL.pos (0 + 1 - 0))
    have := hs i
    omega
  have hfun : minimalSiteShare a y =
      fun V => (1 / 4 : ℝ) * ∑ q ∈ cornerPlaquetteIndex, plaquetteCost (plaquetteAtCorner y q) V :=
    funext (minimalSiteShare_eq hL hs2 a y)
  rw [hfun, bondDeriv_quarter_sum]
  by_cases hall : ∀ l, siteSupDist y (c l).1 ≤ 1
  · have hd : bondListDist y c ≤ 1 := Finset.sup_le fun l _ => hall l
    have hq := abs_quarter_sum_le cornerPlaquetteIndex card_cornerPlaquetteIndex _ hB
    have he := half_le_exp_neg_mul (d := (bondListDist y c : ℝ)) h0 h1 (Nat.cast_nonneg _) (by exact_mod_cast hd)
    calc _ ≤ 6 * B := hq
      _ = 12 * B * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
  · push Not at hall
    obtain ⟨l, hl⟩ := hall
    have hz : ∀ q ∈ cornerPlaquetteIndex, bondDeriv (plaquetteCost (plaquetteAtCorner y q)) W c X = 0 := by
      intro q hq
      refine iteratedFDeriv_plaquetteCost_eq_zero c X W _ l fun hm => ?_
      exact absurd (siteSupDist_corner_le_one hp3 y hq hm) (by omega)
    rw [Finset.sum_eq_zero hz, mul_zero, abs_zero]
    positivity
private def edgePlaquetteOffsets (P : Fin 4 × Fin 4) : Finset (Fin 4 → ℤ) := {0, -Pi.single P.1 1, -Pi.single P.2 1}
private theorem edgePlaquetteOffsets_bounds {P : Fin 4 × Fin 4} {o : Fin 4 → ℤ} (ho : o ∈ edgePlaquetteOffsets P)
    (i : Fin 4) : -1 ≤ o i ∧ o i ≤ 0 := by
  simp only [edgePlaquetteOffsets, Finset.mem_insert, Finset.mem_singleton] at ho
  rcases ho with rfl | rfl | rfl
  · simp
  · have := single_one_bounds P.1 i
    rw [Pi.neg_apply]
    omega
  · have := single_one_bounds P.2 i
    rw [Pi.neg_apply]
    omega
private theorem card_edgePlaquetteOffsets_le (P : Fin 4 × Fin 4) : (edgePlaquetteOffsets P).card ≤ 3 :=
  Finset.card_le_three
private theorem card_planePairs : planePairs.card = 6 := by decide
private theorem siteOfCoords_inj_of_small {j : ℕ} (hp : ∀ i, 3 ≤ F.period j i) {u v : Fin 4 → ℤ}
    (hu : ∀ i, -1 ≤ u i ∧ u i ≤ 0) (hv : ∀ i, -1 ≤ v i ∧ v i ≤ 0)
    (e : (siteOfCoords j u : F.Site j) = siteOfCoords j v) : u = v := by
  funext i
  have d := siteOfCoords_eq_iff.1 e i
  have h1 := hu i
  have h2 := hv i
  have h3 : ((F.period j i : ℕ) : ℤ) ≥ 3 := by exact_mod_cast hp i
  have h4 : v i - u i = 0 := Int.eq_zero_of_abs_lt_dvd d (by
    rw [abs_lt]
    omega)
  omega
private theorem three_le_period_levelZero {L : ℕ} {side : Fin 4 → ℕ} (hL : Odd L) (hs : ∀ i, 64 ≤ side i)
    (i : Fin 4) : 3 ≤ (levelZeroFrame L side).period 0 i := by
  show 3 ≤ side i * L ^ (0 + 1 - 0)
  have h := Nat.le_mul_of_pos_right (side i) (pow_pos hL.pos (0 + 1 - 0))
  have := hs i
  omega
private theorem bondDeriv_minimalAction_eq_local (hL : Odd L) (hs : ∀ i, 64 ≤ side i) (a : ℝ) {n : ℕ}
    (W : (levelZeroFrame L side).GaugeField 0) (c : Fin n → (levelZeroFrame L side).Site 0 × Fin 4)
    (X : Fin n → imaginaryQuaternions) (l0 : Fin n) :
    bondDeriv (minimalAction a (finiteCells (levelZeroFrame L side)) 0) W c X =
      ∑ P ∈ planePairs, ∑ o ∈ edgePlaquetteOffsets P,
        bondDeriv (plaquetteCost ((c l0).1 + siteOfCoords 0 o, P.1, P.2)) W c X := by
  have hs2 : ∀ i, 2 ≤ side i := fun i => by have := hs i; omega
  have hs0 : ∀ i, 0 < (levelZeroFrame L side).extent i := fun i => by
    have := hs i
    show 0 < side i
    omega
  have hp3 := three_le_period_levelZero hL hs
  have hfun : minimalAction a (finiteCells (levelZeroFrame L side)) 0 = fun V =>
      ∑ r ∈ planePairs ×ˢ allSites (levelZeroFrame L side) 0, plaquetteCost (r.2, r.1.1, r.1.2) V := by
    funext V
    rw [minimalAction_eq hL hs2, Finset.sum_product]
  rw [hfun, bondDeriv_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun P _ => ?_
  have hinj : Set.InjOn (fun o => (c l0).1 + (siteOfCoords 0 o : (levelZeroFrame L side).Site 0))
      (edgePlaquetteOffsets P : Set (Fin 4 → ℤ)) := by
    intro u hu v hv e
    exact siteOfCoords_inj_of_small hp3 (edgePlaquetteOffsets_bounds hu) (edgePlaquetteOffsets_bounds hv)
      (add_left_cancel e)
  rw [← Finset.sum_image (f := fun x => bondDeriv (plaquetteCost (x, P.1, P.2)) W c X) hinj]
  symm
  refine Finset.sum_subset (fun x _ => mem_allSites hL hs0 (Nat.zero_le _) x) fun x _ hx => ?_
  refine iteratedFDeriv_plaquetteCost_eq_zero c X W _ l0 fun hm => hx ?_
  simp only [plaquetteEdges, Finset.mem_insert, Finset.mem_singleton] at hm
  rw [Finset.mem_image]
  have hz : siteOfCoords 0 (0 : Fin 4 → ℤ) = (0 : (levelZeroFrame L side).Site 0) := siteOfCoords_zero 0
  rcases hm with h | h | h | h
  · exact ⟨0, by simp [edgePlaquetteOffsets], by rw [h]; simp [hz]⟩
  · exact ⟨-Pi.single P.1 1, by simp [edgePlaquetteOffsets], by
      rw [h, siteOfCoords_neg]; exact add_neg_cancel_right _ _⟩
  · exact ⟨-Pi.single P.2 1, by simp [edgePlaquetteOffsets], by
      rw [h, siteOfCoords_neg]; exact add_neg_cancel_right _ _⟩
  · exact ⟨0, by simp [edgePlaquetteOffsets], by rw [h]; simp [hz]⟩
private theorem abs_bondDeriv_minimalAction_le (hL : Odd L) (hs : ∀ i, 64 ≤ side i) (a : ℝ) {B : ℝ} {n : ℕ}
    (W : (levelZeroFrame L side).GaugeField 0) (c : Fin n → (levelZeroFrame L side).Site 0 × Fin 4)
    (X : Fin n → imaginaryQuaternions) (l0 : Fin n) (hB0 : 0 ≤ B)
    (hB : ∀ p : (levelZeroFrame L side).Site 0 × Fin 4 × Fin 4, p.2.1 < p.2.2 →
      |bondDeriv (plaquetteCost p) W c X| ≤ B) :
    |bondDeriv (minimalAction a (finiteCells (levelZeroFrame L side)) 0) W c X| ≤ 18 * B := by
  rw [bondDeriv_minimalAction_eq_local hL hs a W c X l0]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ P ∈ planePairs, |∑ o ∈ edgePlaquetteOffsets P,
      bondDeriv (plaquetteCost ((c l0).1 + siteOfCoords 0 o, P.1, P.2)) W c X| ≤ 3 * B := by
    intro P hP
    have hlt : P.1 < P.2 := (Finset.mem_filter.1 hP).2
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h2 := Finset.sum_le_card_nsmul (edgePlaquetteOffsets P)
      (fun o => |bondDeriv (plaquetteCost ((c l0).1 + siteOfCoords 0 o, P.1, P.2)) W c X|) B
      fun o _ => hB _ hlt
    refine h2.trans ?_
    rw [nsmul_eq_mul]
    have h3 : ((edgePlaquetteOffsets P).card : ℝ) ≤ 3 := by exact_mod_cast card_edgePlaquetteOffsets_le P
    exact mul_le_mul_of_nonneg_right h3 hB0
  have h4 := Finset.sum_le_card_nsmul planePairs _ (3 * B) h1
  rw [card_planePairs] at h4
  refine h4.trans (le_of_eq ?_)
  simp only [nsmul_eq_mul]
  push_cast
  ring
private theorem abs_bondDeriv_minimalAction_le_exp (hL : Odd L) (hs : ∀ i, 64 ≤ side i) (a : ℝ) {δ B : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 8) {n : ℕ} (W : (levelZeroFrame L side).GaugeField 0)
    (c : Fin n → (levelZeroFrame L side).Site 0 × Fin 4) (X : Fin n → imaginaryQuaternions) (hn : 1 ≤ n)
    (hB0 : 0 ≤ B) (hB : ∀ p : (levelZeroFrame L side).Site 0 × Fin 4 × Fin 4, p.2.1 < p.2.2 →
      |bondDeriv (plaquetteCost p) W c X| ≤ B) :
    |bondDeriv (minimalAction a (finiteCells (levelZeroFrame L side)) 0) W c X| ≤
      36 * B * Real.exp (-δ * bondListDiameter c) := by
  have hp3 := three_le_period_levelZero hL hs
  by_cases hall : ∀ l l', siteSupDist (c l).1 (c l').1 ≤ 1
  · have hd : bondListDiameter c ≤ 1 := Finset.sup_le fun l _ => Finset.sup_le fun l' _ => hall l l'
    have he := half_le_exp_neg_mul (d := (bondListDiameter c : ℝ)) h0 h1 (Nat.cast_nonneg _) (by exact_mod_cast hd)
    calc _ ≤ 18 * B := abs_bondDeriv_minimalAction_le hL hs a W c X ⟨0, hn⟩ hB0 hB
      _ = 36 * B * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
  · push Not at hall
    obtain ⟨l, l', hl⟩ := hall
    rw [bondDeriv_minimalAction_eq_local hL hs a W c X l]
    have hz : ∀ p : (levelZeroFrame L side).Site 0 × Fin 4 × Fin 4, bondDeriv (plaquetteCost p) W c X = 0 := by
      intro p
      by_cases hm : c l ∈ plaquetteEdges p
      · refine iteratedFDeriv_plaquetteCost_eq_zero c X W p l' fun hm' => ?_
        exact absurd (siteSupDist_le_one_of_mem_plaquetteEdges hp3 hm hm') (by omega)
      · exact iteratedFDeriv_plaquetteCost_eq_zero c X W p l hm
    simp only [hz, Finset.sum_const_zero, abs_zero]
    positivity
private theorem plaquetteCost_eq {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) (V : F.GaugeField j) :
    plaquetteCost p V = plaquetteDefect V p ^ 2 / 2 := by
  unfold plaquetteCost plaquetteDefect
  set g : UnitQuaternion := plaquetteHolonomy V p
  have h1 : Quaternion.normSq (g : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, norm_coe_unitQuaternion]
    norm_num
  have h2 : ‖(g : ℍ[ℝ]) - 1‖ ^ 2 = Quaternion.normSq ((g : ℍ[ℝ]) - 1) := by
    rw [Quaternion.normSq_eq_norm_mul_self]
    ring
  rw [h2]
  rw [Quaternion.normSq_def'] at h1 ⊢
  have r0 : ((g : ℍ[ℝ]) - 1).re = (g : ℍ[ℝ]).re - 1 := rfl
  have r1 : ((g : ℍ[ℝ]) - 1).imI = (g : ℍ[ℝ]).imI - 0 := rfl
  have r2 : ((g : ℍ[ℝ]) - 1).imJ = (g : ℍ[ℝ]).imJ - 0 := rfl
  have r3 : ((g : ℍ[ℝ]) - 1).imK = (g : ℍ[ℝ]).imK - 0 := rfl
  rw [r0, r1, r2, r3]
  nlinarith
private theorem plaquetteHolonomy_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (U : F.GaugeField j)
    (x : F.Site j) (μ ν : Fin 4) :
    plaquetteHolonomy (gaugeTransform γ U) (x, μ, ν) = γ x * plaquetteHolonomy U (x, μ, ν) * (γ x)⁻¹ := by
  rw [plaquetteHolonomy_eq, plaquetteHolonomy_eq]
  have e1 : x + unitStep j ν + unitStep j μ = x + unitStep j μ + unitStep j ν := by abel
  simp only [gaugeTransform, e1, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, mul_one, inv_mul_cancel,
    mul_inv_cancel_left]
abbrev _root_.YangMills.SharedProofs.p16452 := @plaquetteHolonomy_gaugeTransform
private theorem plaquetteCost_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (U : F.GaugeField j)
    (p : F.Site j × Fin 4 × Fin 4) : plaquetteCost p (gaugeTransform γ U) = plaquetteCost p U := by
  obtain ⟨x, μ, ν⟩ := p
  unfold plaquetteCost
  rw [plaquetteHolonomy_gaugeTransform, Submonoid.coe_mul, Submonoid.coe_mul,
    PlaquetteLinearization.re_coe_mul_mul_coe_inv]
private theorem plaquetteCost_translateField {j : ℕ} (h : F.Site j) (U : F.GaugeField j) (x : F.Site j)
    (μ ν : Fin 4) : plaquetteCost (x + h, μ, ν) (translateField h U) = plaquetteCost (x, μ, ν) U := by
  unfold plaquetteCost
  rw [plaquetteHolonomy_eq, plaquetteHolonomy_eq]
  have e1 : ∀ v : F.Site j, x + h + v - h = x + v := fun v => by abel
  simp only [translateField, e1, add_sub_cancel_right]
private theorem plaquetteAtCorner_add {j : ℕ} (y h : F.Site j) (q : (Fin 4 × Fin 4) × (Bool × Bool)) :
    plaquetteAtCorner (y + h) q = ((plaquetteAtCorner y q).1 + h, (plaquetteAtCorner y q).2) := by
  simp only [plaquetteAtCorner]
  rw [add_right_comm]
private theorem coldEstimatesBelow_levelZero (hL : Odd L) (hs : ∀ i, 64 ≤ side i) {a δ : ℝ} (h0 : 0 ≤ δ)
    (h1 : δ ≤ 1 / 8) {N : ℕ → ℝ} (hN : ∀ k : ℕ, 1000 + 36 * |plaquetteDerivBound (k : ℝ) k| ≤ N k) {s : ℝ}
    {W : (levelZeroFrame L side).GaugeField 0} (hsp : 0 < s) (hW : IsSmallCurvature s W) :
    ColdEstimatesBelow a δ s N W := by
  have hs2 : ∀ i, 2 ≤ side i := fun i => by have := hs i; omega
  have hexp : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos x).le
  have hidx : ∀ q ∈ cornerPlaquetteIndex, q.1.1 < q.1.2 :=
    fun q hq => (Finset.mem_filter.1 (Finset.mem_product.1 hq).1).2
  have hfunA : (minimalAction a (finiteCells (levelZeroFrame L side)) 0) = fun V =>
      ∑ r ∈ planePairs ×ˢ allSites (levelZeroFrame L side) 0, plaquetteCost (r.2, r.1.1, r.1.2) V := by
    funext V
    rw [minimalAction_eq hL hs2, Finset.sum_product]
  have hslope : ∀ (c : Fin 1 → (levelZeroFrame L side).Site 0 × Fin 4) (X : Fin 1 → imaginaryQuaternions),
      AreUnitVectors X → ∀ p : (levelZeroFrame L side).Site 0 × Fin 4 × Fin 4, p.2.1 < p.2.2 →
        |bondDeriv (plaquetteCost p) W c X| ≤ 4 * s := by
    intro c X hX p hp
    have e := abs_first_deriv_plaquetteCost_le c X (hX 0).le W p
    have e2 := (hW p hp).le
    exact e.trans (by linarith)
  have hterm : ∀ (k : ℕ) (c : Fin k → (levelZeroFrame L side).Site 0 × Fin 4) (X : Fin k → imaginaryQuaternions),
      AreUnitVectors X → ∀ p : (levelZeroFrame L side).Site 0 × Fin 4 × Fin 4,
        |bondDeriv (plaquetteCost p) W c X| ≤ |plaquetteDerivBound (k : ℝ) k| :=
    fun k c X hX p => (abs_bondDeriv_plaquetteCost_le c hX W p).trans (le_abs_self _)
  have hNk : ∀ k : ℕ, 36 * |plaquetteDerivBound (k : ℝ) k| ≤ N k := fun k => by have := hN k; linarith
  have hN1000 : ∀ k : ℕ, 1000 ≤ N k := fun k => by
    have := hN k
    have h2 := abs_nonneg (plaquetteDerivBound (k : ℝ) k)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k c X
    show AnalyticAt ℝ (fun τ => minimalAction a (finiteCells (levelZeroFrame L side)) 0
      (leftTranslate (bondSpread c X τ) W)) 0
    rw [hfunA]
    exact (contDiff_sum_plaquetteCost _ _ W c X).contDiffAt.analyticAt
  · intro y k c X
    have e : (fun τ => minimalSiteShare a y (leftTranslate (bondSpread c X τ) W)) =
        fun τ => (1 / 4 : ℝ) * ∑ q ∈ cornerPlaquetteIndex,
          plaquetteCost (plaquetteAtCorner y q) (leftTranslate (bondSpread c X τ) W) :=
      funext fun τ => minimalSiteShare_eq hL hs2 a y _
    rw [e]
    exact (contDiff_const.mul (contDiff_sum_plaquetteCost _ _ W c X)).contDiffAt.analyticAt
  · intro X hX y
    rw [chainSiteShare_eq hL hs2, minimalSiteShare_eq hL hs2]
    have e : X 0 = W := hX.1
    rw [e]
  · intro k c X hk hX
    have e := abs_bondDeriv_minimalAction_le_exp hL hs a h0 h1 W c X hk (abs_nonneg (plaquetteDerivBound (k : ℝ) k))
      fun p _ => hterm k c X hX p
    refine e.trans (mul_le_mul_of_nonneg_right (hNk k) (hexp _))
  · intro c X hX
    have e := abs_bondDeriv_minimalAction_le hL hs a W c X 0 (by positivity : 0 ≤ 4 * s) (hslope c X hX)
    refine e.trans ?_
    have := hN1000 1
    nlinarith
  · intro y k c X hk hX
    have e := abs_bondDeriv_minimalSiteShare_le (a := a) hL hs h0 h1 W y c X hk
      (abs_nonneg (plaquetteDerivBound (k : ℝ) k)) fun q _ => hterm k c X hX _
    refine e.trans (mul_le_mul_of_nonneg_right ?_ (hexp _))
    have := hNk k
    have h2 := abs_nonneg (plaquetteDerivBound (k : ℝ) k)
    linarith
  · intro y
    rw [minimalSiteShare_eq hL hs2]
    have hnn : ∀ q ∈ cornerPlaquetteIndex, 0 ≤ plaquetteCost (plaquetteAtCorner y q) W := fun q _ => by
      rw [plaquetteCost_eq]
      positivity
    have hle : ∀ q ∈ cornerPlaquetteIndex, plaquetteCost (plaquetteAtCorner y q) W ≤ s ^ 2 / 2 := fun q hq => by
      rw [plaquetteCost_eq]
      have e1 := hW (plaquetteAtCorner y q) (hidx q hq)
      have e2 : 0 ≤ plaquetteDefect W (plaquetteAtCorner y q) := norm_nonneg _
      have e3 : plaquetteDefect W (plaquetteAtCorner y q) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ e2 e1.le 2
      linarith
    have hsum := Finset.sum_le_card_nsmul cornerPlaquetteIndex _ (s ^ 2 / 2) hle
    rw [card_cornerPlaquetteIndex] at hsum
    refine ⟨by have := Finset.sum_nonneg hnn; positivity, ?_⟩
    have h3 : (1 / 4 : ℝ) * ∑ q ∈ cornerPlaquetteIndex, plaquetteCost (plaquetteAtCorner y q) W ≤ 3 * s ^ 2 := by
      simp only [nsmul_eq_mul] at hsum
      push_cast at hsum
      linarith
    refine h3.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg s))
    have := hN1000 0
    linarith
  · intro y c X hX
    have e := abs_bondDeriv_minimalSiteShare_le (a := a) hL hs h0 h1 W y c X le_rfl (by positivity : 0 ≤ 4 * s)
      fun q hq => hslope c X hX _ (hidx q hq)
    refine e.trans (mul_le_mul_of_nonneg_right ?_ (hexp _))
    have := hN1000 1
    nlinarith
  · intro y γ
    rw [minimalSiteShare_eq hL hs2, minimalSiteShare_eq hL hs2]
    simp only [plaquetteCost_gaugeTransform]
  · intro y u
    rw [minimalSiteShare_eq hL hs2, minimalSiteShare_eq hL hs2]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [plaquetteAtCorner_add]
    exact plaquetteCost_translateField u W _ _ _
private theorem siteOfCoords_inj_withinRadius {H : BlockFrame} {j r : ℕ} (hper : ∀ i, 2 * r + 2 < H.period j i)
    {u v : Fin 4 → ℤ} (hu : WithinRadius r u) (hv : WithinRadius r v) (y : H.Site j)
    (e : y + siteOfCoords j u = y + siteOfCoords j v) : u = v := by
  funext i
  have d := siteOfCoords_eq_iff.1 (add_left_cancel e) i
  have h1 := abs_le.1 (hu i)
  have h2 := abs_le.1 (hv i)
  have h3 : (2 * (r : ℤ) + 2) < (H.period j i : ℤ) := by exact_mod_cast hper i
  have h4 : v i - u i = 0 := Int.eq_zero_of_abs_lt_dvd d (by
    rw [abs_lt]
    omega)
  omega
private theorem bondSpread_agree {F' : BlockFrame} {j r n : ℕ} (hp : ∀ i, 2 * r + 2 < F.period j i)
    (hp' : ∀ i, 2 * r + 2 < F'.period j i) (y : F.Site j) (y' : F'.Site j) (h : Fin n → (Fin 4 → ℤ) × Fin 4)
    (hh : ∀ l, BondWithinRadius r (h l)) (X : Fin n → imaginaryQuaternions) (τ : Fin n → ℝ) (z : Fin 4 → ℤ)
    (i : Fin 4) (hz : WithinRadius r z) :
    bondSpread (bondsAt y h) X τ (y + siteOfCoords j z) i = bondSpread (bondsAt y' h) X τ (y' + siteOfCoords j z) i := by
  unfold bondSpread bondsAt
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases e : (h l).1 = z ∧ (h l).2 = i
  · obtain ⟨e1, e2⟩ := e
    rw [if_pos (by rw [e1, e2]), if_pos (by rw [e1, e2])]
  · rw [if_neg, if_neg]
    · intro hq
      exact e ⟨siteOfCoords_inj_withinRadius hp' (hh l).1 hz y' (congrArg Prod.fst hq), congrArg Prod.snd hq⟩
    · intro hq
      exact e ⟨siteOfCoords_inj_withinRadius hp (hh l).1 hz y (congrArg Prod.fst hq), congrArg Prod.snd hq⟩
private theorem leftTranslate_agree {F' : BlockFrame} {j r n : ℕ} (hp : ∀ i, 2 * r + 2 < F.period j i)
    (hp' : ∀ i, 2 * r + 2 < F'.period j i) {W : F.GaugeField j} {W' : F'.GaugeField j} {y : F.Site j}
    {y' : F'.Site j}
    (hW : ∀ b, BondWithinRadius r b → W (y + siteOfCoords j b.1) b.2 = W' (y' + siteOfCoords j b.1) b.2)
    (h : Fin n → (Fin 4 → ℤ) × Fin 4) (hh : ∀ l, BondWithinRadius r (h l)) (X : Fin n → imaginaryQuaternions)
    (τ : Fin n → ℝ) (b : (Fin 4 → ℤ) × Fin 4) (hb : BondWithinRadius r b) :
    leftTranslate (bondSpread (bondsAt y h) X τ) W (y + siteOfCoords j b.1) b.2 =
      leftTranslate (bondSpread (bondsAt y' h) X τ) W' (y' + siteOfCoords j b.1) b.2 := by
  simp only [leftTranslate]
  rw [bondSpread_agree hp hp' y y' h hh X τ b.1 b.2 hb.1, hW b hb]
private theorem add_siteOfCoords_add_unitStep {H : BlockFrame} {j : ℕ} (x : H.Site j) (z : Fin 4 → ℤ) (u : Fin 4) :
    x + siteOfCoords j z + unitStep j u = x + siteOfCoords j (z + Pi.single u 1) := by
  rw [siteOfCoords_add, add_assoc]
  rfl
private theorem plaquetteCost_agree {F' : BlockFrame} {j r : ℕ} {U : F.GaugeField j} {U' : F'.GaugeField j}
    {y : F.Site j} {y' : F'.Site j}
    (hU : ∀ b, BondWithinRadius r b → U (y + siteOfCoords j b.1) b.2 = U' (y' + siteOfCoords j b.1) b.2)
    (z : Fin 4 → ℤ) (μ ν : Fin 4) (h0 : WithinRadius r z) (h1 : WithinRadius r (z + Pi.single μ 1))
    (h2 : WithinRadius r (z + Pi.single ν 1)) (h3 : WithinRadius r (z + Pi.single μ 1 + Pi.single ν 1)) :
    plaquetteCost (y + siteOfCoords j z, μ, ν) U = plaquetteCost (y' + siteOfCoords j z, μ, ν) U' := by
  unfold plaquetteCost
  rw [plaquetteHolonomy_eq, plaquetteHolonomy_eq, add_siteOfCoords_add_unitStep, add_siteOfCoords_add_unitStep,
    add_siteOfCoords_add_unitStep, add_siteOfCoords_add_unitStep]
  have e1 := hU (z, μ) ⟨h0, h1⟩
  have e2 := hU (z + Pi.single μ 1, ν) ⟨h1, h3⟩
  have e3 := hU (z + Pi.single ν 1, μ) ⟨h2, by
    show WithinRadius r (z + Pi.single ν 1 + Pi.single μ 1)
    rw [add_right_comm]
    exact h3⟩
  have e4 := hU (z, ν) ⟨h0, h2⟩
  dsimp only at e1 e2 e3 e4
  rw [e1, e2, e3, e4]
private theorem withinRadius_plaquette {r : ℕ} {z : Fin 4 → ℤ} {μ ν : Fin 4} (hμν : μ ≠ ν)
    (hz : ∀ i, -(r : ℤ) ≤ z i ∧ z i + 1 ≤ r) :
    WithinRadius r z ∧ WithinRadius r (z + Pi.single μ 1) ∧ WithinRadius r (z + Pi.single ν 1) ∧
      WithinRadius r (z + Pi.single μ 1 + Pi.single ν 1) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · have := hz i
    rw [abs_le]
    omega
  · have := hz i
    have h1 := single_one_bounds μ i
    rw [Pi.add_apply, abs_le]
    omega
  · have := hz i
    have h1 := single_one_bounds ν i
    rw [Pi.add_apply, abs_le]
    omega
  · have := hz i
    have h1 := single_one_bounds μ i
    have h2 := single_one_bounds ν i
    have h3 := single_add_single_le_one hμν i
    rw [Pi.add_apply, Pi.add_apply, abs_le]
    omega
private theorem bondDeriv_fin_zero {j : ℕ} (Φ : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv Φ W c X = Φ W := by
  unfold bondDeriv
  rw [iteratedFDeriv_zero_apply, leftTranslate_bondSpread_zero]
abbrev _root_.YangMills.SharedProofs.p8307 := @bondDeriv_fin_zero
private theorem abs_bondDeriv_plaquetteCost_le_of_small {j : ℕ} {s : ℝ} {W : F.GaugeField j}
    (hW : IsSmallCurvature s W) (c : Fin 1 → F.Site j × Fin 4) {X : Fin 1 → imaginaryQuaternions}
    (hX : AreUnitVectors X) (p : F.Site j × Fin 4 × Fin 4) (hp : p.2.1 < p.2.2) :
    |bondDeriv (plaquetteCost p) W c X| ≤ 4 * s := by
  have e := abs_first_deriv_plaquetteCost_le c X (hX 0).le W p
  have e2 := (hW p hp).le
  exact e.trans (by linarith)
private theorem coldComparisonBelow_levelZero {L' : ℕ} {side' : Fin 4 → ℕ} (hL : Odd L) (hL' : Odd L')
    (hs : ∀ i, 64 ≤ side i) (hs' : ∀ i, 64 ≤ side' i) {a δ δ₂ s₀ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 8) (h2 : 0 ≤ δ₂)
    {N : ℕ → ℝ} (hN : ∀ k : ℕ, 1000 + 36 * |plaquetteDerivBound (k : ℝ) k| ≤ N k) {s : ℝ}
    {W : (levelZeroFrame L side).GaugeField 0} {W' : (levelZeroFrame L' side').GaugeField 0}
    {y : (levelZeroFrame L side).Site 0} {y' : (levelZeroFrame L' side').Site 0} {r : ℕ} (hsp : 0 < s)
    (hW : IsSmallCurvature s W) (hW' : IsSmallCurvature s W')
    (hag : AgreeOnBox (F := levelZeroFrame L side) (F' := levelZeroFrame L' side') W W' y y' r) :
    ColdComparisonBelow (F := levelZeroFrame L side) (F' := levelZeroFrame L' side') a δ δ₂ s s₀ N W W' y y' r := by
  have hs2 : ∀ i, 2 ≤ side i := fun i => by have := hs i; omega
  have hs2' : ∀ i, 2 ≤ side' i := fun i => by have := hs' i; omega
  have hp : ∀ i, 2 * r + 2 < (levelZeroFrame L side).period 0 i := hag.1
  have hp' : ∀ i, 2 * r + 2 < (levelZeroFrame L' side').period 0 i := hag.2.1
  have hU : ∀ b, BondWithinRadius r b → W (y + siteOfCoords 0 b.1) b.2 = W' (y' + siteOfCoords 0 b.1) b.2 := hag.2.2
  have hN1000 : ∀ k : ℕ, 1000 ≤ N k := fun k => by
    have := hN k
    have h2 := abs_nonneg (plaquetteDerivBound (k : ℝ) k)
    linarith
  have hexp : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos x).le
  refine ⟨fun k h X hh hX => ?_, fun _ b X hb hX => ?_⟩
  · have hf0 : 0 ≤ derivativeScale s k := by
      unfold derivativeScale
      split_ifs <;> positivity
    rcases Nat.eq_zero_or_pos r with hr | hr
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        subst hr
        rw [bondDeriv_fin_zero, bondDeriv_fin_zero]
        have e1 := (coldEstimatesBelow_levelZero (a := a) hL hs h0 h1 hN hsp hW).siteShare_bounds y
        have e2 := (coldEstimatesBelow_levelZero (a := a) hL' hs' h0 h1 hN hsp hW').siteShare_bounds y'
        have e3 : derivativeScale s 0 = s ^ 2 := by simp [derivativeScale]
        rw [e3]
        simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
        rw [abs_le]
        constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2]
      · exfalso
        subst hr
        have hb := hh ⟨0, hk⟩
        have e1 := abs_le.1 (hb.1 (h ⟨0, hk⟩).2)
        have e2 := abs_le.1 (hb.2 (h ⟨0, hk⟩).2)
        simp only [Pi.add_apply, Pi.single_eq_same] at e2
        push_cast at e1 e2
        omega
    · have hf : (fun τ => minimalSiteShare a y (leftTranslate (bondSpread (bondsAt y h) X τ) W)) =
          fun τ => minimalSiteShare a y' (leftTranslate (bondSpread (bondsAt y' h) X τ) W') := by
        funext τ
        rw [minimalSiteShare_eq hL hs2, minimalSiteShare_eq hL' hs2']
        congr 1
        refine Finset.sum_congr rfl fun q hq => ?_
        have hP : q.1.1 ≠ q.1.2 := ((Finset.mem_filter.1 (Finset.mem_product.1 hq).1).2).ne
        obtain ⟨b0, b1, b2, b3⟩ := withinRadius_plaquette (r := r) (z := -(cornerOffset q.1 q.2)) hP fun i => by
          have := cornerOffset_bounds hP q.2 i
          rw [Pi.neg_apply]
          omega
        exact plaquetteCost_agree (leftTranslate_agree hp hp' hU h hh X τ) _ _ _ b0 b1 b2 b3
      have e : bondDeriv (minimalSiteShare a y) W (bondsAt y h) X =
          bondDeriv (minimalSiteShare a y') W' (bondsAt y' h) X := by
        unfold bondDeriv
        rw [hf]
      rw [e, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hf0 (by have := hN1000 k; linarith)) (hexp _)
  · by_cases hd : (r : ℝ) - siteSupDist y (y + siteOfCoords 0 b.1) ≤ 0
    · have e1 := abs_bondDeriv_minimalAction_le (a := a) hL hs W (bondsAt y fun _ => b) X 0
        (by positivity : 0 ≤ 4 * s) (abs_bondDeriv_plaquetteCost_le_of_small hW _ hX)
      have e2 := abs_bondDeriv_minimalAction_le (a := a) hL' hs' W' (bondsAt y' fun _ => b) X 0
        (by positivity : 0 ≤ 4 * s) (abs_bondDeriv_plaquetteCost_le_of_small hW' _ hX)
      have e3 : (1 : ℝ) ≤ Real.exp (-(δ₂ * ((r : ℝ) - siteSupDist y (y + siteOfCoords 0 b.1)))) := by
        apply Real.one_le_exp
        nlinarith
      have e4 := hN1000 0
      have e5 : 1000 * s ≤ N 0 * s := mul_le_mul_of_nonneg_right e4 hsp.le
      have e6 : N 0 * s ≤ N 0 * s * Real.exp (-(δ₂ * ((r : ℝ) - siteSupDist y (y + siteOfCoords 0 b.1)))) :=
        le_mul_of_one_le_right (by positivity) e3
      have e7 := abs_sub (bondDeriv (minimalAction a (finiteCells (levelZeroFrame L side)) 0) W (bondsAt y fun _ => b) X)
        (bondDeriv (minimalAction a (finiteCells (levelZeroFrame L' side')) 0) W' (bondsAt y' fun _ => b) X)
      have e8 : 18 * (4 * s) + 18 * (4 * s) ≤ 1000 * s := by nlinarith
      exact e7.trans ((add_le_add e1 e2).trans (e8.trans (e5.trans e6)))
    · have hd' : siteSupDist y (y + siteOfCoords 0 b.1) + 1 ≤ r := by
        have : (siteSupDist y (y + siteOfCoords 0 b.1) : ℝ) < r := by linarith [not_le.1 hd]
        exact_mod_cast this
      have hbox : ∀ i, |b.1 i| + 1 ≤ r := by
        intro i
        have e0 : siteSupDist y (y + siteOfCoords 0 b.1) = Finset.univ.sup fun i => (b.1 i).natAbs :=
          siteSupDist_add_siteOfCoords (fun i => by have := hp i; omega) y b.1 fun i => by
            have e1 := abs_le.1 (hb.1 i)
            have e2 := hp i
            have e3 : 2 * (r : ℤ) + 2 < ((levelZeroFrame L side).period 0 i : ℤ) := by exact_mod_cast e2
            cases abs_cases (b.1 i) <;> omega
        have e1 : (b.1 i).natAbs ≤ siteSupDist y (y + siteOfCoords 0 b.1) := by
          rw [e0]
          exact Finset.le_sup (f := fun i => (b.1 i).natAbs) (Finset.mem_univ i)
        rw [Int.abs_eq_natAbs]
        omega
      have hh : ∀ l : Fin 1, BondWithinRadius r ((fun _ => b : Fin 1 → (Fin 4 → ℤ) × Fin 4) l) := fun _ => hb
      rw [bondDeriv_minimalAction_eq_local hL hs a W _ X 0, bondDeriv_minimalAction_eq_local hL' hs' a W' _ X 0]
      have e : (∑ P ∈ planePairs, ∑ o ∈ edgePlaquetteOffsets P,
            bondDeriv (plaquetteCost (((bondsAt y fun _ => b) (0 : Fin 1)).1 + siteOfCoords 0 o, P.1, P.2)) W
              (bondsAt y fun _ => b) X) =
          ∑ P ∈ planePairs, ∑ o ∈ edgePlaquetteOffsets P,
            bondDeriv (plaquetteCost (((bondsAt y' fun _ => b) (0 : Fin 1)).1 + siteOfCoords 0 o, P.1, P.2)) W'
              (bondsAt y' fun _ => b) X := by
        refine Finset.sum_congr rfl fun P hP => Finset.sum_congr rfl fun o ho => ?_
        have hlt : P.1 ≠ P.2 := ((Finset.mem_filter.1 hP).2).ne
        obtain ⟨b0, b1, b2, b3⟩ := withinRadius_plaquette (r := r) (z := b.1 + o) hlt fun i => by
          have e1 := edgePlaquetteOffsets_bounds ho i
          have e2 := hbox i
          rw [Pi.add_apply]
          cases abs_cases (b.1 i) <;> omega
        have ea : (((bondsAt y fun _ => b) (0 : Fin 1)).1 + siteOfCoords 0 o : (levelZeroFrame L side).Site 0) =
            y + siteOfCoords 0 (b.1 + o) := by
          simp only [bondsAt]
          rw [siteOfCoords_add, add_assoc]
        have eb : (((bondsAt y' fun _ => b) (0 : Fin 1)).1 + siteOfCoords 0 o : (levelZeroFrame L' side').Site 0) =
            y' + siteOfCoords 0 (b.1 + o) := by
          simp only [bondsAt]
          rw [siteOfCoords_add, add_assoc]
        rw [ea, eb]
        unfold bondDeriv
        have hf : (fun τ => plaquetteCost (y + siteOfCoords 0 (b.1 + o), P.1, P.2)
              (leftTranslate (bondSpread (bondsAt y fun _ => b) X τ) W)) =
            fun τ => plaquetteCost (y' + siteOfCoords 0 (b.1 + o), P.1, P.2)
              (leftTranslate (bondSpread (bondsAt y' fun _ => b) X τ) W') := by
          funext τ
          exact plaquetteCost_agree (leftTranslate_agree hp hp' hU _ hh X τ) _ _ _ b0 b1 b2 b3
        rw [hf]
      rw [e, sub_self, abs_zero]
      have := hN1000 0
      exact mul_nonneg (mul_nonneg (by linarith) hsp.le) (hexp _)
theorem wilsonActionColdEstimates_holds : WilsonActionColdEstimates := by
  refine ⟨fun k => 1000 + 36 * |plaquetteDerivBound (k : ℝ) k|, fun k => by positivity, ?_⟩
  intro a δ δ₂ s₀ h0 h1 h2
  refine ⟨?_, ?_⟩
  · intro F s W ht hL hC hsp hW
    obtain ⟨L, t, side⟩ := F
    obtain rfl : t = 0 := ht
    obtain ⟨n, hn, hsd⟩ := hC
    have hs : ∀ i, 64 ≤ side i := fun i => by
      rw [show side i = n from hsd i]
      exact hn
    exact coldEstimatesBelow_levelZero hL hs h0 h1 (fun k => le_rfl) hsp hW
  · intro F F' s W W' y y' r ht ht' hL hL' hC hC' hsp hW hW' hag
    obtain ⟨L, t, side⟩ := F
    obtain ⟨L', t', side'⟩ := F'
    obtain rfl : t = 0 := ht
    obtain rfl : t' = 0 := ht'
    obtain ⟨n, hn, hsd⟩ := hC
    obtain ⟨n', hn', hsd'⟩ := hC'
    have hs : ∀ i, 64 ≤ side i := fun i => by
      rw [show side i = n from hsd i]
      exact hn
    have hs' : ∀ i, 64 ≤ side' i := fun i => by
      rw [show side' i = n' from hsd' i]
      exact hn'
    exact coldComparisonBelow_levelZero hL hL' hs hs' h0 h1 h2 (fun k => le_rfl) hsp hW hW' hag
end YangMills.Construction.ColdStepAtMirrorFrames
end
