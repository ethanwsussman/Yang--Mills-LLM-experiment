import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.HolomorphicOnMatrixFamilies
import YangMills.Construction.Matrices.ProductAnalyticInMatrices
import YangMills.Construction.Matrices.TracelessHolomorphyDifferentiableHolds
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
open YangMills.Construction.Coordinates
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct.MatrixAnalyticity
open ExpChartHolomorphy (logChart)
variable {σ ι κ : Type}
private def matrixCoordsCLE : ComplexMatrix2 ≃L[ℂ] ComplexCoordinates 4 :=
  LinearEquiv.toContinuousLinearEquiv
    { ComplexCoordinates.matrixEquiv with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
private theorem matrixCoordsCLE_apply (X : ComplexMatrix2) :
    matrixCoordsCLE X = ComplexCoordinates.matrixEquiv X :=
  rfl

private theorem matrixCoordsCLE_symm_apply (z : ComplexCoordinates 4) :
    matrixCoordsCLE.symm z = ComplexCoordinates.matrixEquiv.symm z := rfl

private theorem logSeries_differentiableOn
    (hD : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    DifferentiableOn ℂ ComplexMatrix2.logSeries ComplexMatrix2.logBall := by
  have hl := hH.2.2.2.2.2
  have hd := (hD _ _ _ _ hl.1).1 hl
  have h1 := hd.comp matrixCoordsCLE.differentiable.differentiableOn
    (s := ComplexMatrix2.logBall) fun X hX => ⟨X, hX, rfl⟩
  have h2 := matrixCoordsCLE.symm.differentiable.comp_differentiableOn h1
  refine h2.congr fun X _ => ?_
  simp [matrixCoordsCLE_apply, matrixCoordsCLE_symm_apply]
private theorem logSeries_one (hL : ComplexMatrix2.ExpLogEstimates) :
    ComplexMatrix2.logSeries 1 = 0 := by
  have h := (hL.2.2.2.2.1 0 (by simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  simpa [ComplexMatrix2.matExp, NormedSpace.exp_zero] using h
private theorem matExp_logSeries_of_mem (hL : ComplexMatrix2.ExpLogEstimates) {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.logBall) : ComplexMatrix2.matExp (ComplexMatrix2.logSeries Y) = Y := by
  have h := (hL.2.2.2.1 (Y - 1) hY).2.2.2.2
  simpa using h
private def tracelessProj : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun X := X - ComplexMatrix2.halfTrace X • (1 : ComplexMatrix2)
  map_add' X Y := by
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_add, mul_add,
      add_smul]
    abel
  map_smul' c X := by
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul, smul_eq_mul,
      RingHom.id_apply, smul_sub, smul_smul]
    congr 2
    ring
private theorem tracelessProj_apply (X : ComplexMatrix2) :
    tracelessProj X = X - ComplexMatrix2.halfTrace X • (1 : ComplexMatrix2) := rfl

private theorem tracelessProj_mem (X : ComplexMatrix2) :
    tracelessProj X ∈ ComplexMatrix2.traceless := by
  change ComplexMatrix2.fullTrace (tracelessProj X) = 0
  simp only [tracelessProj_apply, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring
private theorem tracelessProj_of_trace_zero {X : ComplexMatrix2}
    (hX : ComplexMatrix2.fullTrace X = 0) : tracelessProj X = X := by
  simp [tracelessProj_apply, ComplexMatrix2.halfTrace, hX]
private def piTracelessProj (σ : Type) :
    (σ → ComplexMatrix2) →ₗ[ℂ] ↥(tracelessPiSubmodule σ) :=
  LinearMap.codRestrict _ (LinearMap.pi fun i => tracelessProj ∘ₗ LinearMap.proj i)
    fun x i _ => tracelessProj_mem (x i)
private def piTracelessProjL (σ : Type) [Fintype σ] :
    (σ → ComplexMatrix2) →L[ℂ] ↥(tracelessPiSubmodule σ) :=
  LinearMap.toContinuousLinearMap (piTracelessProj σ)
private theorem isOpen_preimage_val [Fintype σ] {O : Set (σ → ComplexMatrix2)} (hO : IsSupOpen O) :
    IsOpen (Subtype.val ⁻¹' O : Set ↥(tracelessPiSubmodule σ)) := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.TracelessDifferentiable.isOpen_subtype_of_isSupOpen <;> assumption
private def groupNear (p : ι ⊕ κ → ComplexMatrix2) : Set (ι ⊕ κ → ComplexMatrix2) :=
  {q | ∀ i, ComplexMatrix2.operatorNorm (q (.inl i) * (p (.inl i))⁻¹ - 1) < 9 / 10}
private theorem isOpen_groupNear [Fintype ι] (p : ι ⊕ κ → ComplexMatrix2) :
    IsOpen (groupNear p) := by
  have : groupNear p =
      ⋂ i, {q | ComplexMatrix2.operatorNorm (q (.inl i) * (p (.inl i))⁻¹ - 1) < 9 / 10} := by
    ext q
    simp [groupNear]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  refine isOpen_lt ?_ continuous_const
  have h : Continuous fun q : ι ⊕ κ → ComplexMatrix2 => q (.inl i) * (p (.inl i))⁻¹ - 1 :=
    ((continuous_apply _).mul continuous_const).sub continuous_const
  exact continuous_norm.comp h
private theorem mem_logBall_of_near {p q : ι ⊕ κ → ComplexMatrix2} (hq : q ∈ groupNear p) (i : ι) :
    q (.inl i) * (p (.inl i))⁻¹ ∈ ComplexMatrix2.logBall :=
  lt_trans (hq i) (by norm_num)
private theorem logChart_differentiableAt [Fintype ι] [Fintype κ]
    (hlog : DifferentiableOn ℂ ComplexMatrix2.logSeries ComplexMatrix2.logBall)
    {p q : ι ⊕ κ → ComplexMatrix2} (hq : q ∈ groupNear p) :
    DifferentiableAt ℂ (logChart p) q := by
  have hopen : IsOpen ComplexMatrix2.logBall :=
    isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
  refine differentiableAt_pi.2 fun t => ?_
  rcases t with i | k
  · change DifferentiableAt ℂ
      (fun r : ι ⊕ κ → ComplexMatrix2 => ComplexMatrix2.logSeries (r (.inl i) * (p (.inl i))⁻¹)) q
    have h₁ : DifferentiableAt ℂ
        (fun r : ι ⊕ κ → ComplexMatrix2 => r (.inl i) * (p (.inl i))⁻¹) q :=
      (differentiableAt_apply _ _).mul_const _
    exact DifferentiableAt.comp (g := ComplexMatrix2.logSeries) q
      (hlog.differentiableAt (hopen.mem_nhds (mem_logBall_of_near hq i))) h₁
  · change DifferentiableAt ℂ (fun r : ι ⊕ κ → ComplexMatrix2 => r (.inr k) - p (.inr k)) q
    exact (differentiableAt_apply _ _).sub_const _
private def tracelessLogChart [Fintype ι] [Fintype κ] (p q : ι ⊕ κ → ComplexMatrix2) :
    ↥(tracelessPiSubmodule (ι ⊕ κ)) :=
  piTracelessProjL (ι ⊕ κ) (logChart p q)
private theorem det_eq_one_of_mem {x : ι ⊕ κ → ComplexMatrix2} (hx : x ∈ GroupLieProduct ι κ)
    (i : ι) : (x (.inl i)).det = 1 := hx (.inl i)
private theorem trace_eq_zero_of_mem {x : ι ⊕ κ → ComplexMatrix2} (hx : x ∈ GroupLieProduct ι κ)
    (k : κ) : ComplexMatrix2.fullTrace (x (.inr k)) = 0 := hx (.inr k)
private theorem mul_inv_of_det {X : ComplexMatrix2} (hX : X.det = 1) : X * X⁻¹ = 1 :=
  Matrix.mul_nonsing_inv X (by rw [hX]; exact isUnit_one)
private theorem inv_mul_of_det {X : ComplexMatrix2} (hX : X.det = 1) : X⁻¹ * X = 1 :=
  Matrix.nonsing_inv_mul X (by rw [hX]; exact isUnit_one)
private theorem tracelessLogChart_self [Fintype ι] [Fintype κ] (hL : ComplexMatrix2.ExpLogEstimates)
    {p : ι ⊕ κ → ComplexMatrix2} (hp : p ∈ GroupLieProduct ι κ) :
    ((tracelessLogChart p p : ↥(tracelessPiSubmodule (ι ⊕ κ))) : ι ⊕ κ → ComplexMatrix2) = 0 := by
  have h0 : logChart p p = 0 := by
    funext t
    rcases t with i | k
    · change ComplexMatrix2.logSeries (p (.inl i) * (p (.inl i))⁻¹) = 0
      rw [mul_inv_of_det (det_eq_one_of_mem hp i), logSeries_one hL]
    · change p (.inr k) - p (.inr k) = 0
      exact sub_self _
  simp [tracelessLogChart, h0]
private theorem self_mem_groupNear {p : ι ⊕ κ → ComplexMatrix2} (hp : p ∈ GroupLieProduct ι κ) :
    p ∈ groupNear p := by
  intro i
  rw [mul_inv_of_det (det_eq_one_of_mem hp i), sub_self]
  simp only [ComplexMatrix2.operatorNorm, norm_zero]
  norm_num
private theorem expChartAt_tracelessLogChart [Fintype ι] [Fintype κ]
    (hL : ComplexMatrix2.ExpLogEstimates) {p q : ι ⊕ κ → ComplexMatrix2}
    (hp : p ∈ GroupLieProduct ι κ) (hq : q ∈ GroupLieProduct ι κ) (hn : q ∈ groupNear p) :
    expChartAt p (tracelessLogChart p q : ↥(tracelessPiSubmodule (ι ⊕ κ))) = q := by
  funext t
  rcases t with i | k
  · change ComplexMatrix2.matExp
      (((tracelessLogChart p q : ↥(tracelessPiSubmodule (ι ⊕ κ))) : ι ⊕ κ → ComplexMatrix2)
        (.inl i)) * p (.inl i) = q (.inl i)
    have hdet : (q (.inl i) * (p (.inl i))⁻¹).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_nonsing_inv, det_eq_one_of_mem hq i,
        det_eq_one_of_mem hp i, Ring.inverse_one, one_mul]
    have htr := (hL.2.2.2.2.2.2.1 _ hdet (hn i).le).1
    have hv : ((tracelessLogChart p q : ↥(tracelessPiSubmodule (ι ⊕ κ))) : ι ⊕ κ → ComplexMatrix2)
        (.inl i) = ComplexMatrix2.logSeries (q (.inl i) * (p (.inl i))⁻¹) :=
      tracelessProj_of_trace_zero htr
    rw [hv, matExp_logSeries_of_mem hL (mem_logBall_of_near hn i), mul_assoc,
      inv_mul_of_det (det_eq_one_of_mem hp i), mul_one]
  · change p (.inr k) +
      ((tracelessLogChart p q : ↥(tracelessPiSubmodule (ι ⊕ κ))) : ι ⊕ κ → ComplexMatrix2) (.inr k) =
      q (.inr k)
    have htr : ComplexMatrix2.fullTrace (q (.inr k) - p (.inr k)) = 0 := by
      simp only [ComplexMatrix2.fullTrace, Matrix.trace_sub]
      rw [show Matrix.trace (q (.inr k)) = 0 from trace_eq_zero_of_mem hq k,
        show Matrix.trace (p (.inr k)) = 0 from trace_eq_zero_of_mem hp k, sub_zero]
    have hv : ((tracelessLogChart p q : ↥(tracelessPiSubmodule (ι ⊕ κ))) : ι ⊕ κ → ComplexMatrix2)
        (.inr k) = q (.inr k) - p (.inr k) :=
      tracelessProj_of_trace_zero htr
    rw [hv, add_sub_cancel]
private theorem isMatrixAnalyticAt_of_coords
    (hT : HolomorphicOnTracelessIffDifferentiable)
    (hA : ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    (hL : ComplexMatrix2.ExpLogEstimates)
    (hlog : DifferentiableOn ℂ ComplexMatrix2.logSeries ComplexMatrix2.logBall)
    [Fintype ι] [Fintype κ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (h : IsHolomorphicToCoords b ComplexCoordinates.matrixEquiv W Φ) {p : ι ⊕ κ → ComplexMatrix2}
    (hpW : p ∈ W) : IsMatrixAnalyticAt W Φ p := by
  obtain ⟨⟨O', -, hW⟩, -, hloc⟩ := h
  have hWP : ∀ {x}, x ∈ W → x ∈ GroupLieProduct ι κ := fun hx => by
    rw [hW] at hx
    exact hx.2
  have hp := hWP hpW
  obtain ⟨O, h0, -, hf⟩ := hloc p hpW
  have hlin : IsLinearMap ℂ ComplexCoordinates.matrixEquiv :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨hO, hdiff⟩ :=
    (hT (ι ⊕ κ) ComplexMatrix2 4 b ComplexCoordinates.matrixEquiv hlin O
      (Φ ∘ expChartAt p)).1 hf
  have hU := isOpen_preimage_val hO
  have ha : ∀ q ∈ groupNear p, DifferentiableAt ℂ (tracelessLogChart p) q := fun q hq =>
    (piTracelessProjL (ι ⊕ κ)).differentiableAt.comp q
      (logChart_differentiableAt hlog hq)
  have hac : ContinuousOn (tracelessLogChart p) (groupNear p) := fun q hq =>
    (ha q hq).continuousAt.continuousWithinAt
  have hN : IsOpen (groupNear p ∩ tracelessLogChart p ⁻¹' (Subtype.val ⁻¹' O)) :=
    hac.isOpen_inter_preimage (isOpen_groupNear p) hU
  have hpN : p ∈ groupNear p ∩ tracelessLogChart p ⁻¹' (Subtype.val ⁻¹' O) := by
    refine ⟨self_mem_groupNear hp, ?_⟩
    change ((tracelessLogChart p p : ↥(tracelessPiSubmodule (ι ⊕ κ))) : ι ⊕ κ → ComplexMatrix2) ∈ O
    rw [tracelessLogChart_self hL hp]
    exact h0
  have hFd : DifferentiableOn ℂ
      (fun q => (fun A : ↥(tracelessPiSubmodule (ι ⊕ κ)) =>
        (Φ ∘ expChartAt p) (A : ι ⊕ κ → ComplexMatrix2)) (tracelessLogChart p q))
      (groupNear p ∩ tracelessLogChart p ⁻¹' (Subtype.val ⁻¹' O)) := fun q hq =>
    ((hdiff.differentiableAt (hU.mem_nhds hq.2)).comp q (ha q hq.1)).differentiableWithinAt
  refine ⟨_, hA (ι ⊕ κ) _ _ hN hFd p hpN, ?_⟩
  filter_upwards [hN.mem_nhds hpN] with q hq hqW
  change Φ q = Φ (expChartAt p (tracelessLogChart p q : ↥(tracelessPiSubmodule (ι ⊕ κ))))
  rw [expChartAt_tracelessLogChart hL hp (hWP hqW) hq.1]
theorem holomorphicMatrixAnalyticity_holds (hE : ExpChartHolomorphy.ExpChartTheory)
    (hT : HolomorphicOnTracelessIffDifferentiable)
    (hA : ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    (hL : ComplexMatrix2.ExpLogEstimates)
    (hD : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    HolomorphicMatrixAnalyticity := by
  intro ι κ _ _ b W Φ h p hp
  have hc : IsHolomorphicToCoords b ComplexCoordinates.matrixEquiv W Φ := by
    rcases h with h | h
    · exact h
    · exact ((hE.2.2.2.1 ι κ).2.1 b W Φ h.1 h.2.1).1 h
  exact isMatrixAnalyticAt_of_coords hT hA hL (logSeries_differentiableOn hD hH) b hc hp
end YangMills.Construction.Matrices.GroupLieProduct.MatrixAnalyticity
