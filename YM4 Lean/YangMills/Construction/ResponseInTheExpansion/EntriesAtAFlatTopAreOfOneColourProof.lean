import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyUnderGaugesAndShifts
import YangMills.Construction.ColdStepAtMirrorFrames.BlocksCoverTheLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfTheShares
import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import Mathlib
import YangMills.Construction.ResponseInTheExpansion.MixedDerivativesAlongSlotsProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeMovesByItsKernelsProof
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace FlatHessian
def colourUnit (e : Fin 3) : imaginaryQuaternions := toImaginary (EuclideanSpace.single e 1)
def HessianAtFlatIsColourDiagonal : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∀ (F : BlockFrame) (b b' : F.Site F.depth × Fin 4) (e e' : Fin 3), IsBlockTorus L F →
      b ∈ chordBonds (finiteCells F) → b' ∈ chordBonds (finiteCells F) →
      chartMixedDeriv a (fun _ _ => 0) (flatTopField (F := F))
          ![Sum.inl (b.1, b.2, colourUnit e), Sum.inl (b'.1, b'.2, colourUnit e')] =
        if e = e' then
          chartMixedDeriv a (fun _ _ => 0) (flatTopField (F := F))
            ![Sum.inl (b.1, b.2, colourUnit 0), Sum.inl (b'.1, b'.2, colourUnit 0)]
        else 0
end FlatHessian
end YangMills.Construction
end

noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.FlatHessian
variable {F : BlockFrame}
private theorem leftTranslate_zero (V : F.GaugeField F.top) :
    leftTranslate (fun _ _ => (0 : imaginaryQuaternions)) V = V := by apply _root_.YangMills.SharedProofs.p46723 <;> assumption
private theorem fderiv_fderiv_comp_clm {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [CompleteSpace E] (f : E → ℝ) (J : E' →L[ℝ] E) (x : E') (hf : AnalyticAt ℝ f (J x)) (u v : E') :
    fderiv ℝ (fderiv ℝ (fun y => f (J y))) x u v = fderiv ℝ (fderiv ℝ f) (J x) (J u) (J v) := by apply _root_.YangMills.SharedProofs.p70139 <;> assumption
private def twoDirectionCoords (b b' : F.Site F.depth × Fin 4) (X X' : imaginaryQuaternions) (σ : Fin 2 → ℝ) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions := fun x i =>
  0 + ∑ l, σ l • directionCoordinate
    ((![Sum.inl (b.1, b.2, X), Sum.inl (b'.1, b'.2, X')] : Fin 2 → ChartDirection F) l) x i
private theorem chartRestriction_eq_chartedEnergy (a : ℝ) (b b' : F.Site F.depth × Fin 4) (X X' : imaginaryQuaternions)
    (σ : Fin 2 → ℝ) :
    chartRestriction a (fun _ _ => 0) (uniformField F F.top) ![Sum.inl (b.1, b.2, X), Sum.inl (b'.1, b'.2, X')] σ =
      chartedEnergy a (twoDirectionCoords b b' X X' σ) (uniformField F F.top) := by
  unfold chartRestriction twoDirectionCoords
  have e : (fun y i => ∑ l, σ l • directionMove
      ((![Sum.inl (b.1, b.2, X), Sum.inl (b'.1, b'.2, X')] : Fin 2 → ChartDirection F) l) y i) =
      fun _ _ => (0 : imaginaryQuaternions) := by
    funext y i
    simp [Fin.sum_univ_two, directionMove]
  rw [e, leftTranslate_zero]
private theorem norm_directionCoordinate_le (b : F.Site F.depth × Fin 4) (X : imaginaryQuaternions) (hX : ‖X‖ = 1)
    (x : F.Site F.depth) (i : Fin 4) :
    ‖directionCoordinate (Sum.inl (b.1, b.2, X) : ChartDirection F) x i‖ ≤ 1 := by
  simp only [directionCoordinate]
  split_ifs
  · exact hX.le
  · simp
private theorem norm_twoDirectionCoords_le (b b' : F.Site F.depth × Fin 4) (X X' : imaginaryQuaternions)
    (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) (σ : Fin 2 → ℝ) (x : F.Site F.depth) (i : Fin 4) :
    ‖twoDirectionCoords b b' X X' σ x i‖ ≤ |σ 0| + |σ 1| := by
  unfold twoDirectionCoords
  simp only [zero_add, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    have := norm_directionCoordinate_le b X hX x i
    nlinarith [abs_nonneg (σ 0)]
  · rw [norm_smul, Real.norm_eq_abs]
    have := norm_directionCoordinate_le b' X' hX' x i
    nlinarith [abs_nonneg (σ 1)]
private theorem isAdmissibleChartPoint_uniform (hc : BlocksCoverLowerLevel) {L : ℕ} {σA ε : ℝ} (hσ : 0 < σA)
    (hF : IsBlockTorus L F) (hL : Odd L) (hε1 : ε ≤ 1 / (64 * (L : ℝ))) (hε2 : 16 * ε ≤ σA)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (hw : ∀ x i, ‖w x i‖ ≤ ε) :
    IsAdmissibleChartPoint L σA w (uniformField F F.top) := by
  obtain ⟨hFL, n, hn, hside⟩ := hF
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hall := hc F hodd fun i => by have := hs i; omega
  have hLp : (1 : ℝ) ≤ L := by exact_mod_cast hL.pos
  have hε4 : ε ≤ 1 / 4 := by
    refine hε1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ⟨fun b _ => (hw _ _).trans hε1, fun p hp => ?_⟩
  have hcold : IsCold (finiteCells F) F.top (σA / 4) (uniformField F F.top) := by
    intro p _
    have : plaquetteDefect (uniformField F F.top) p = 0 := by
      simp [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue, uniformField]
    rw [this]
    positivity
  have hmem : p ∈ innerPlaquettes (finiteCells F) F.depth := by
    simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hall _, hp, fun y _ => hall y⟩
  have hcur := GaugeFixing.plaquetteDefect_chartedField_le hs hodd (finiteCells F) (uniformField F F.top) (σA / 4) ε
    (by positivity) hcold w hε4 (fun d _ => hw _ _) p hmem
  linarith
private theorem chartMixedDeriv_conj_eq (hG : CellEnergyShareInvariant) (hS : sumCellSharesEqAction)
    (hc : BlocksCoverLowerLevel) {a : ℝ} {L : ℕ} {c : ColdChainParameters} (ha : 1 ≤ a) (hL : Odd L)
    (hL0 : 2 ^ 40 ≤ L) (hcc : c.Admissible a L) (hF : IsBlockTorus L F) (b b' : F.Site F.depth × Fin 4)
    (X X' Z Z' : imaginaryQuaternions) (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1) (γ : UnitQuaternion)
    (hZ : (Z : ℍ[ℝ]) = (γ : ℍ[ℝ]) * (X : ℍ[ℝ]) * ((γ⁻¹ : UnitQuaternion) : ℍ[ℝ]))
    (hZ' : (Z' : ℍ[ℝ]) = (γ : ℍ[ℝ]) * (X' : ℍ[ℝ]) * ((γ⁻¹ : UnitQuaternion) : ℍ[ℝ])) :
    chartMixedDeriv a (fun _ _ => 0) (uniformField F F.top) ![Sum.inl (b.1, b.2, X), Sum.inl (b'.1, b'.2, X')] =
      chartMixedDeriv a (fun _ _ => 0) (uniformField F F.top) ![Sum.inl (b.1, b.2, Z), Sum.inl (b'.1, b'.2, Z')] := by
  have hσ : 0 < c.σA := hcc.positivity.2.2.2.1
  obtain ⟨-, n, hn, hside⟩ := id hF
  have hodd : Odd F.blockSide := hF.1 ▸ hL
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  set ε : ℝ := min (1 / (64 * (L : ℝ))) (c.σA / 16) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hnear : ∀ᶠ σ : Fin 2 → ℝ in nhds 0, |σ 0| + |σ 1| < ε := by
    have hcont : Continuous fun σ : Fin 2 → ℝ => |σ 0| + |σ 1| := by fun_prop
    have := hcont.continuousAt (x := (0 : Fin 2 → ℝ))
    have h2 := this.eventually
      (gt_mem_nhds (show |(0 : Fin 2 → ℝ) 0| + |(0 : Fin 2 → ℝ) 1| < ε by simpa using hε0))
    exact h2
  have hev : chartRestriction a (fun _ _ => 0) (uniformField F F.top)
      ![Sum.inl (b.1, b.2, X), Sum.inl (b'.1, b'.2, X')] =ᶠ[nhds 0]
      chartRestriction a (fun _ _ => 0) (uniformField F F.top)
      ![Sum.inl (b.1, b.2, Z), Sum.inl (b'.1, b'.2, Z')] := by
    filter_upwards [hnear] with σ hσ'
    rw [chartRestriction_eq_chartedEnergy, chartRestriction_eq_chartedEnergy]
    have hsm : IsAdmissibleChartPoint L c.σA (twoDirectionCoords b b' X X' σ) (uniformField F F.top) :=
      isAdmissibleChartPoint_uniform hc hσ hF hL (min_le_left _ _) (by
        have := min_le_right (1 / (64 * (L : ℝ))) (c.σA / 16)
        linarith) _ (fun x i => (norm_twoDirectionCoords_le b b' X X' hX hX' σ x i).trans hσ'.le)
    have hflat : gaugeTransform (fun _ => γ) (uniformField F F.top) = uniformField F F.top := by
      funext x i
      simp [gaugeTransform, uniformField]
    have hblock : ∀ Y : F.Cell, cellEnergyShare a Y (twoDirectionCoords b b' Z Z' σ) (uniformField F F.top) =
        cellEnergyShare a Y (twoDirectionCoords b b' X X' σ) (uniformField F F.top) := by
      intro Y
      have := (hG a L c ha hL hL0 hcc F (twoDirectionCoords b b' X X' σ) (twoDirectionCoords b b' Z Z' σ)
        (uniformField F F.top) hF hsm Y).1 (fun _ => γ) (fun d _ => by
        simp only [twoDirectionCoords, zero_add, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          directionCoordinate]
        by_cases h1 : b.1 = d.1 ∧ b.2 = d.2 <;> by_cases h2 : b'.1 = d.1 ∧ b'.2 = d.2 <;>
          simp [h1, h2, hZ, hZ', mul_add, add_mul, mul_assoc])
      rwa [hflat] at this
    have h1 := (hS F a (twoDirectionCoords b b' X X' σ) (uniformField F F.top) (by linarith) hodd hs).2
    have h2 := (hS F a (twoDirectionCoords b b' Z Z' σ) (uniformField F F.top) (by linarith) hodd hs).2
    rw [← h1, ← h2]
    exact Finset.sum_congr rfl fun Y _ => (hblock Y).symm
  show iteratedFDeriv ℝ 2 _ 0 _ = iteratedFDeriv ℝ 2 _ 0 _
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, (Filter.EventuallyEq.fderiv (𝕜 := ℝ) hev).fderiv_eq]
private def negSecond : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun l : Fin 2 =>
    (![ContinuousLinearMap.proj 0, -ContinuousLinearMap.proj 1] : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ)) l
private theorem negSecond_apply (σ : Fin 2 → ℝ) : negSecond σ = ![σ 0, -σ 1] := by
  ext l
  fin_cases l <;> simp [negSecond]
private theorem chartMixedDeriv_neg_second {a : ℝ} (b b' : F.Site F.depth × Fin 4) (X X' : imaginaryQuaternions)
    (han : AnalyticAt ℝ (chartRestriction a (fun _ _ => 0) (uniformField F F.top)
      ![Sum.inl (b.1, b.2, X), Sum.inl (b'.1, b'.2, X')]) 0) :
    chartMixedDeriv a (fun _ _ => 0) (uniformField F F.top) ![Sum.inl (b.1, b.2, X), Sum.inl (b'.1, b'.2, -X')] =
      -chartMixedDeriv a (fun _ _ => 0) (uniformField F F.top) ![Sum.inl (b.1, b.2, X), Sum.inl (b'.1, b'.2, X')] := by
  set f := chartRestriction a (fun _ _ => 0) (uniformField F F.top)
    ![Sum.inl (b.1, b.2, X), Sum.inl (b'.1, b'.2, X')] with hf
  have e : chartRestriction a (fun _ _ => 0) (uniformField F F.top)
      ![Sum.inl (b.1, b.2, X), Sum.inl (b'.1, b'.2, -X')] = fun σ => f (negSecond σ) := by
    funext σ
    rw [hf, chartRestriction_eq_chartedEnergy, chartRestriction_eq_chartedEnergy]
    congr 1
    funext x i
    simp only [twoDirectionCoords, zero_add, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      directionCoordinate, negSecond_apply]
    by_cases h2 : b'.1 = x ∧ b'.2 = i
    · simp only [h2, and_self, if_true, smul_neg]
      exact congrArg _ (neg_smul _ _).symm
    · simp [h2]
  show iteratedFDeriv ℝ 2 _ 0 _ = -(iteratedFDeriv ℝ 2 _ 0 _)
  have ha' : AnalyticAt ℝ f (negSecond 0) := by simpa using han
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, e, fderiv_fderiv_comp_clm f negSecond 0 ha', ← hf]
  have e0 : negSecond (Pi.single 0 1 : Fin 2 → ℝ) = Pi.single 0 1 := by
    rw [negSecond_apply]
    ext l
    fin_cases l <;> simp
  have e1 : negSecond (Pi.single 1 1 : Fin 2 → ℝ) = -Pi.single 1 1 := by
    rw [negSecond_apply]
    ext l
    fin_cases l <;> simp
  simp [e0, e1]
private def basisQuat (e : Fin 3) : ℍ[ℝ] :=
  ⟨0, if e = 0 then 1 else 0, if e = 1 then 1 else 0, if e = 2 then 1 else 0⟩
private theorem basisQuat_re (e : Fin 3) : (basisQuat e).re = 0 := rfl
private theorem basisQuat_imI (e : Fin 3) : (basisQuat e).imI = if e = 0 then 1 else 0 := rfl
private theorem basisQuat_imJ (e : Fin 3) : (basisQuat e).imJ = if e = 1 then 1 else 0 := rfl
private theorem basisQuat_imK (e : Fin 3) : (basisQuat e).imK = if e = 2 then 1 else 0 := rfl
private def diagQuaternion : ℍ[ℝ] := ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩
private theorem diagQuaternion_re : diagQuaternion.re = 1 / 2 := rfl
private theorem diagQuaternion_imI : diagQuaternion.imI = 1 / 2 := rfl
private theorem diagQuaternion_imJ : diagQuaternion.imJ = 1 / 2 := rfl
private theorem diagQuaternion_imK : diagQuaternion.imK = 1 / 2 := rfl
private theorem coe_colourUnit (e : Fin 3) : (colourUnit e : ℍ[ℝ]) = basisQuat e := by
  fin_cases e <;> ext <;> simp [colourUnit, toImaginary, basisQuat_re, basisQuat_imI, basisQuat_imJ, basisQuat_imK]
private theorem norm_colourUnit (e : Fin 3) : ‖colourUnit e‖ = 1 := by
  have h : ‖(colourUnit e : ℍ[ℝ])‖ * ‖(colourUnit e : ℍ[ℝ])‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, coe_colourUnit, Quaternion.normSq_def']
    show (basisQuat e).re ^ 2 + (basisQuat e).imI ^ 2 + (basisQuat e).imJ ^ 2 + (basisQuat e).imK ^ 2 = 1
    fin_cases e <;> simp [basisQuat_re, basisQuat_imI, basisQuat_imJ, basisQuat_imK]
  have h0 : 0 ≤ ‖(colourUnit e : ℍ[ℝ])‖ := norm_nonneg _
  exact show ‖(colourUnit e : ℍ[ℝ])‖ = 1 from by nlinarith
abbrev _root_.YangMills.SharedProofs.p39739 := @norm_colourUnit
private def basisUnit (e : Fin 3) : UnitQuaternion :=
  ⟨basisQuat e, Unitary.mem_iff.2 ⟨by fin_cases e <;> ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star, basisQuat_re, basisQuat_imI, basisQuat_imJ, basisQuat_imK],
    by fin_cases e <;> ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, basisQuat_re, basisQuat_imI,
    basisQuat_imJ, basisQuat_imK]⟩⟩
private def diagQuaternionUnit : UnitQuaternion :=
  ⟨diagQuaternion, Unitary.mem_iff.2 ⟨by ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
    basisQuat_re, basisQuat_imI, basisQuat_imJ, basisQuat_imK, diagQuaternion_re, diagQuaternion_imI, diagQuaternion_imJ,
    diagQuaternion_imK] <;> norm_num,
    by ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, basisQuat_re, basisQuat_imI,
    basisQuat_imJ, basisQuat_imK, diagQuaternion_re, diagQuaternion_imI, diagQuaternion_imJ, diagQuaternion_imK] <;> norm_num⟩⟩
theorem hessianAtFlatIsColourDiagonal (hK : ChartEnergyKernelBound)
    (hG : CellEnergyShareInvariant) (hS : sumCellSharesEqAction)
    (hc : BlocksCoverLowerLevel) : HessianAtFlatIsColourDiagonal := by
  intro a L c ha hL hL0 hcc F b b' e e' hF hb hb'
  rw [show (flatTopField (F := F)) = uniformField F F.top from rfl]
  have hσ : 0 < c.σA := hcc.positivity.2.2.2.1
  obtain ⟨Ck, -, hker⟩ := hK a L c ha hL hL0 hcc
  have hzero : IsAdmissibleChartPoint L c.σA (fun _ _ => (0 : imaginaryQuaternions)) (uniformField F F.top) :=
    isAdmissibleChartPoint_uniform hc hσ hF hL (by positivity) (by simpa using hσ.le) _ (fun _ _ => by simp)
  by_cases hee : e = e'
  · subst hee
    rw [if_pos rfl]
    have r01 := chartMixedDeriv_conj_eq hG hS hc ha hL hL0 hcc hF b b' (colourUnit 0) (colourUnit 0) (colourUnit 1)
      (colourUnit 1) (norm_colourUnit 0) (norm_colourUnit 0) diagQuaternionUnit
      (by
        show (colourUnit 1 : ℍ[ℝ]) = _ * (colourUnit 0 : ℍ[ℝ]) * star _
        rw [coe_colourUnit, coe_colourUnit]
        show basisQuat _ = diagQuaternion * basisQuat _ * star diagQuaternion
        ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
          Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, basisQuat_re,
          basisQuat_imI, basisQuat_imJ, basisQuat_imK, diagQuaternion_re, diagQuaternion_imI, diagQuaternion_imJ, diagQuaternion_imK] <;> norm_num)
      (by
        show (colourUnit 1 : ℍ[ℝ]) = _ * (colourUnit 0 : ℍ[ℝ]) * star _
        rw [coe_colourUnit, coe_colourUnit]
        show basisQuat _ = diagQuaternion * basisQuat _ * star diagQuaternion
        ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
          Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, basisQuat_re,
          basisQuat_imI, basisQuat_imJ, basisQuat_imK, diagQuaternion_re, diagQuaternion_imI, diagQuaternion_imJ, diagQuaternion_imK] <;> norm_num)
    have r12 := chartMixedDeriv_conj_eq hG hS hc ha hL hL0 hcc hF b b' (colourUnit 1) (colourUnit 1) (colourUnit 2)
      (colourUnit 2) (norm_colourUnit 1) (norm_colourUnit 1) diagQuaternionUnit
      (by
        show (colourUnit 2 : ℍ[ℝ]) = _ * (colourUnit 1 : ℍ[ℝ]) * star _
        rw [coe_colourUnit, coe_colourUnit]
        show basisQuat _ = diagQuaternion * basisQuat _ * star diagQuaternion
        ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
          Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, basisQuat_re,
          basisQuat_imI, basisQuat_imJ, basisQuat_imK, diagQuaternion_re, diagQuaternion_imI, diagQuaternion_imJ, diagQuaternion_imK] <;> norm_num)
      (by
        show (colourUnit 2 : ℍ[ℝ]) = _ * (colourUnit 1 : ℍ[ℝ]) * star _
        rw [coe_colourUnit, coe_colourUnit]
        show basisQuat _ = diagQuaternion * basisQuat _ * star diagQuaternion
        ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
          Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, basisQuat_re,
          basisQuat_imI, basisQuat_imJ, basisQuat_imK, diagQuaternion_re, diagQuaternion_imI, diagQuaternion_imJ, diagQuaternion_imK] <;> norm_num)
    fin_cases e
    · rfl
    · exact r01.symm
    · exact r12.symm.trans r01.symm
  · rw [if_neg hee]
    have hrot := chartMixedDeriv_conj_eq hG hS hc ha hL hL0 hcc hF b b' (colourUnit e) (colourUnit e')
      (colourUnit e) (-colourUnit e') (norm_colourUnit e) (norm_colourUnit e') (basisUnit e)
      (by
        show (colourUnit e : ℍ[ℝ]) = _ * (colourUnit e : ℍ[ℝ]) * star _
        rw [coe_colourUnit]
        show basisQuat e = basisQuat e * basisQuat e * star (basisQuat e)
        fin_cases e <;> ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
          Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, basisQuat_re,
          basisQuat_imI, basisQuat_imJ, basisQuat_imK])
      (by
        show ((-colourUnit e' : imaginaryQuaternions) : ℍ[ℝ]) = _ * (colourUnit e' : ℍ[ℝ]) * star _
        have : ((-colourUnit e' : imaginaryQuaternions) : ℍ[ℝ]) = -(colourUnit e' : ℍ[ℝ]) := rfl
        rw [this, coe_colourUnit]
        show -basisQuat e' = basisQuat e * basisQuat e' * star (basisQuat e)
        fin_cases e <;> fin_cases e' <;> first | exact absurd rfl hee | (ext <;> simp [Quaternion.re_mul,
          Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
          Quaternion.imJ_star, Quaternion.imK_star, basisQuat_re, basisQuat_imI, basisQuat_imJ, basisQuat_imK]))
    have hneg := chartMixedDeriv_neg_second (a := a) b b' (colourUnit e) (colourUnit e') (hker F _ _ hF hzero 2 _).1
    linarith
end YangMills.Construction.FlatHessian
end
