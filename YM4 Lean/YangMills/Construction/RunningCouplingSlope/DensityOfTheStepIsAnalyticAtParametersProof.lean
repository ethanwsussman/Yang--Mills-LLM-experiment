import YangMills.Construction.Matrices.HaarExpChartDensityProof
import YangMills.Construction.RunningCouplingSlope.HaarDensityAtTheLeastFieldHasKernelsProof
import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.TotalUnderATurnedTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.CurvesOfTheFrames
import YangMills.Construction.Matrices.UnitaryLogarithmClosedFormProof
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsAnalyticAtParameters
import YangMills.Construction.RunningCouplingSlope.ValueOfTheDensityOfTheStepOnTwoToriAtParametersProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ReferenceDensity YangMills.Construction.TorusFields YangMills.Construction.StepCosts
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames.StepDensityAnalytic
section Paths
variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]
private def rampCLM : A →L[ℝ] C(unitInterval, A) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun s => (s : ℝ) • x, by fun_prop⟩
      map_add' := fun x y => by
        ext s
        simp [smul_add]
      map_smul' := fun c x => ContinuousMap.ext fun s => smul_comm (s : ℝ) c x } 1
    (fun x => by
      rw [one_mul]
      refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun s => ?_
      show ‖(s : ℝ) • x‖ ≤ ‖x‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg s.2.1]
      exact mul_le_of_le_one_left (norm_nonneg _) s.2.2)
private def constPathCLM : A →L[ℝ] C(unitInterval, A) :=
  LinearMap.mkContinuous
    { toFun := fun x => ContinuousMap.const _ x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun x => by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun _ => le_rfl)
private def extendToReal (g : C(unitInterval, A)) (s : ℝ) : A := g (Set.projIcc 0 1 zero_le_one s)
omit [NormedAlgebra ℝ A] in
private theorem continuous_extendToReal (g : C(unitInterval, A)) : Continuous (extendToReal g) :=
  g.continuous.comp continuous_projIcc
private def pathIntegralCLM (Λ : A →L[ℝ] ℝ) : C(unitInterval, A) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ s in (0 : ℝ)..1, Λ (extendToReal g s)
      map_add' := fun g h => by
        have hg : IntervalIntegrable (fun s => Λ (extendToReal g s)) MeasureTheory.volume 0 1 :=
          (Λ.continuous.comp (continuous_extendToReal g)).intervalIntegrable _ _
        have hh : IntervalIntegrable (fun s => Λ (extendToReal h s)) MeasureTheory.volume 0 1 :=
          (Λ.continuous.comp (continuous_extendToReal h)).intervalIntegrable _ _
        rw [← intervalIntegral.integral_add hg hh]
        refine intervalIntegral.integral_congr fun s _ => ?_
        show Λ (g _ + h _) = _
        rw [map_add]
        rfl
      map_smul' := fun c g => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun s _ => ?_
        show Λ (c • g _) = _
        rw [map_smul]
        rfl } ‖Λ‖
    (fun g => by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (f := fun s => Λ (extendToReal g s)) (C := ‖Λ‖ * ‖g‖) fun s _ =>
          (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (norm_nonneg _))
      simpa using h)
omit [NormedAlgebra ℝ A] in
private theorem ringInverse_apply {g : C(unitInterval, A)} (hg : IsUnit g) (s : unitInterval) :
    (Ring.inverse g) s = Ring.inverse (g s) := by
  obtain ⟨u, rfl⟩ := hg
  rw [Ring.inverse_unit]
  have h1 : (u : C(unitInterval, A)) s * ((u⁻¹ : (C(unitInterval, A))ˣ) : C(unitInterval, A)) s = 1 :=
    DFunLike.congr_fun u.mul_inv s
  have h2 : ((u⁻¹ : (C(unitInterval, A))ˣ) : C(unitInterval, A)) s * (u : C(unitInterval, A)) s = 1 :=
    DFunLike.congr_fun u.inv_mul s
  exact (Ring.inverse_unit (⟨_, _, h1, h2⟩ : Aˣ)).symm
private theorem analyticAt_integral_resolvent [CompleteSpace A] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : A →L[ℝ] ℝ) (l : ℝ) (M : E → A) (z : E) (hM : AnalyticAt ℝ M z)
    (hU : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsUnit (s • M z + (1 - s) • l • (1 : A))) :
    AnalyticAt ℝ (fun τ => ∫ s in (0 : ℝ)..1,
      Λ ((M τ - l • (1 : A)) * Ring.inverse (s • M τ + (1 - s) • l • (1 : A)))) z := by
  obtain ⟨c0, hc0⟩ : ∃ c0 : C(unitInterval, A), ∀ s : unitInterval, c0 s = (1 - (s : ℝ)) • l • (1 : A) :=
    ⟨⟨fun s => (1 - (s : ℝ)) • l • (1 : A), by fun_prop⟩, fun _ => rfl⟩
  obtain ⟨U, hUd⟩ : ∃ U : E → C(unitInterval, A), U = fun τ => rampCLM (M τ) + c0 := ⟨_, rfl⟩
  have hUa : AnalyticAt ℝ U z := by
    rw [hUd]
    exact ((rampCLM.analyticAt _).comp hM).add analyticAt_const
  have hUs : ∀ τ (s : unitInterval), U τ s = (s : ℝ) • M τ + (1 - (s : ℝ)) • l • (1 : A) := fun τ s => by
    rw [hUd]
    show (s : ℝ) • M τ + c0 s = _
    rw [hc0]
  have hs : ∀ s : unitInterval, IsUnit (U z s) := fun s => by
    rw [hUs]
    exact hU s s.2
  have hcont : Continuous fun s : unitInterval => Ring.inverse (U z s) := by
    refine continuous_iff_continuousAt.2 fun s => ?_
    have h1 : ContinuousAt Ring.inverse (U z s) := by
      have := NormedRing.inverse_continuousAt (hs s).unit
      rwa [IsUnit.unit_spec] at this
    exact ContinuousAt.comp (f := fun s => U z s) h1 (U z).continuous.continuousAt
  obtain ⟨v, hv⟩ : ∃ v : C(unitInterval, A), ∀ s, v s = Ring.inverse (U z s) := ⟨⟨_, hcont⟩, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : (C(unitInterval, A))ˣ, (u : C(unitInterval, A)) = U z :=
    ⟨⟨U z, v, by
      ext1 s
      show U z s * v s = 1
      rw [hv, Ring.mul_inverse_cancel _ (hs s)], by
      ext1 s
      show v s * U z s = 1
      rw [hv, Ring.inverse_mul_cancel _ (hs s)]⟩, rfl⟩
  have hunit : IsUnit (U z) := ⟨u, hu⟩
  have hinv : AnalyticAt ℝ (fun τ => Ring.inverse (U τ)) z :=
    AnalyticAt.comp_of_eq (analyticAt_inverse (𝕜 := ℝ) u) hUa hu.symm
  have hS : AnalyticAt ℝ (fun τ => M τ - l • (1 : A)) z := hM.sub analyticAt_const
  have hA : AnalyticAt ℝ (fun τ => constPathCLM (M τ - l • (1 : A))) z :=
    ((constPathCLM (A := A)).analyticAt _).comp hS
  have hW : AnalyticAt ℝ (fun τ => constPathCLM (M τ - l • (1 : A)) * Ring.inverse (U τ)) z := hA.mul hinv
  refine (((pathIntegralCLM Λ).analyticAt _).comp hW).congr ?_
  filter_upwards [hUa.continuousAt.eventually (Units.isOpen.mem_nhds hunit)] with τ hτ
  show ∫ s in (0 : ℝ)..1, Λ (extendToReal (constPathCLM (M τ - l • (1 : A)) * Ring.inverse (U τ)) s) = _
  refine intervalIntegral.integral_congr fun s hs' => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs'
  show Λ ((constPathCLM (M τ - l • (1 : A)) * Ring.inverse (U τ)) (Set.projIcc 0 1 zero_le_one s)) = _
  rw [Set.projIcc_of_mem _ hs', ContinuousMap.mul_apply, ringInverse_apply hτ, hUs]
  rfl
end Paths
private theorem analyticAt_integral_matrix_resolvent {ι E : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (M : E → Matrix ι ι ℝ) (z : E) (l : ℝ) (P : ι → Prop) [DecidablePred P]
    (hM : ∀ i j, AnalyticAt ℝ (fun τ => M τ i j) z)
    (hU : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsUnit (s • M z + (1 - s) • l • (1 : Matrix ι ι ℝ))) :
    AnalyticAt ℝ (fun τ => ∫ s in (0 : ℝ)..1, ∑ i, if P i then
      ((M τ - l • (1 : Matrix ι ι ℝ)) * (s • M τ + (1 - s) • l • (1 : Matrix ι ι ℝ))⁻¹) i i else 0) z := by
  simp only [Matrix.nonsing_inv_eq_ringInverse]
  let _ : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix ι ι ℝ) := FiniteDimensional.complete ℝ _
  let Λ : Matrix ι ι ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun B => ∑ i, if P i then B i i else 0
      map_add' := fun B C => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : P i <;> simp [h]
      map_smul' := fun c B => by
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : P i <;> simp [h] }
  have hMa : AnalyticAt ℝ M z := by
    have e : M = fun τ => ∑ i, ∑ j, M τ i j • Matrix.single i j (1 : ℝ) := by
      funext τ
      conv_lhs => rw [Matrix.matrix_eq_sum_single (M τ)]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Matrix.smul_single]
    rw [e]
    exact Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ =>
      AnalyticAt.fun_smul (A := ℝ) (hM i j) analyticAt_const
  exact analyticAt_integral_resolvent Λ l M z hMa hU
abbrev _root_.YangMills.SharedProofs.p91236 := @analyticAt_integral_matrix_resolvent
section Quaternions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {z : E}
private def quatStarCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := star, map_add' := star_add, map_smul' := fun r q => by ext <;> simp }
private def quatReCLM : ℍ[ℝ] →L[ℝ] ℝ := innerSL ℝ (1 : ℍ[ℝ])
private theorem quatReCLM_apply (q : ℍ[ℝ]) : quatReCLM q = q.re := by
  show inner ℝ (1 : ℍ[ℝ]) q = q.re
  rw [Quaternion.inner_def]
  simp
private theorem analyticAt_log_of_pos {N : E → ℝ} (hN : AnalyticAt ℝ N z) (hp : 0 < N z) :
    AnalyticAt ℝ (fun σ => Real.log (N σ)) z :=
  (analyticAt_log hp).comp hN
private theorem analyticAt_norm_sq {G : E → ℍ[ℝ]} (hG : AnalyticAt ℝ G z) :
    AnalyticAt ℝ (fun σ => ‖G σ‖ ^ 2) z := by
  have hNeq : ∀ σ, quatReCLM (G σ * star (G σ)) = ‖G σ‖ ^ 2 := by
    intro σ
    rw [quatReCLM_apply, Quaternion.self_mul_star, Quaternion.re_coe, Quaternion.normSq_eq_norm_mul_self]
    ring
  have h2 : AnalyticAt ℝ (fun σ => star (G σ)) z := (quatStarCLM.analyticAt _).comp hG
  have h3 : AnalyticAt ℝ (fun σ => quatReCLM (G σ * star (G σ))) z := (quatReCLM.analyticAt _).comp (hG.mul h2)
  exact h3.congr (Filter.Eventually.of_forall hNeq)
private theorem analyticAt_log_norm {G : E → ℍ[ℝ]} (hG : AnalyticAt ℝ G z) (h0 : G z ≠ 0) :
    AnalyticAt ℝ (fun σ => Real.log ‖G σ‖) z := by
  have hp : 0 < ‖G z‖ ^ 2 := by
    have := norm_pos_iff.2 h0
    positivity
  have h1 : AnalyticAt ℝ (fun σ => Real.log (‖G σ‖ ^ 2)) z := analyticAt_log_of_pos (analyticAt_norm_sq hG) hp
  have h2 : AnalyticAt ℝ (fun σ => (1 / 2 : ℝ) * Real.log (‖G σ‖ ^ 2)) z := analyticAt_const.mul h1
  refine h2.congr (Filter.Eventually.of_forall fun σ => ?_)
  show (1 / 2 : ℝ) * Real.log (‖G σ‖ ^ 2) = Real.log ‖G σ‖
  rw [Real.log_pow]
  push_cast
  ring
abbrev _root_.YangMills.SharedProofs.p33293 := @analyticAt_log_norm
private theorem analyticAt_expUnit {w : E → imaginaryQuaternions} (hw : AnalyticAt ℝ w z) :
    AnalyticAt ℝ (fun p => ((expUnit (w p) : UnitQuaternion) : ℍ[ℝ])) z := by apply _root_.YangMills.SharedProofs.p29648 <;> assumption
variable {F : BlockFrame} {j : ℕ}
private theorem analyticAt_pathHolonomy {X : E → F.GaugeField j}
    (hX : ∀ x i, AnalyticAt ℝ (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ])) z)
    (l : List PathStep) : ∀ x, AnalyticAt ℝ (fun σ => ((pathHolonomy (X σ) x l : UnitQuaternion) : ℍ[ℝ])) z := by
  induction l with
  | nil =>
    intro x
    simp only [pathHolonomy]
    exact analyticAt_const
  | cons st r ih =>
    intro x
    simp only [pathHolonomy, Submonoid.coe_mul]
    refine AnalyticAt.mul ?_ (ih _)
    rcases st with ⟨k, b⟩
    cases b with
    | true =>
      simpa [linkValue] using hX x k
    | false =>
      have h := hX (x - BlockAverages.unitStep j k) k
      have h2 : AnalyticAt ℝ (fun σ => star ((X σ (x - BlockAverages.unitStep j k) k : UnitQuaternion) : ℍ[ℝ])) z :=
        (quatStarCLM.analyticAt _).comp h
      simpa [linkValue, coe_unitQuaternion_inv] using h2
private theorem analyticAt_contourAverage {X : E → F.GaugeField j}
    (hX : ∀ x i, AnalyticAt ℝ (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ])) z)
    (c : F.Site (j + 1) × Fin 4) : AnalyticAt ℝ (fun σ => BlockAverages.contourAverage (X σ) c) z := by
  have hs : AnalyticAt ℝ (fun σ => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy (X σ) (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])) z :=
    Finset.analyticAt_fun_sum _ fun h _ => Finset.analyticAt_fun_sum _ fun π _ => analyticAt_pathHolonomy hX _ _
  unfold BlockAverages.contourAverage
  exact AnalyticAt.fun_smul (A := ℝ) analyticAt_const hs
abbrev _root_.YangMills.SharedProofs.p5864 := @analyticAt_contourAverage
end Quaternions
section Haar
private def sincCoeff (n : ℕ) : ℝ := (-1) ^ n / ((2 * n + 1).factorial : ℝ)
private def sincSq (s : ℝ) : ℝ := FormalMultilinearSeries.ofScalarsSum (E := ℝ) sincCoeff s
private theorem radius_sincCoeff : (FormalMultilinearSeries.ofScalars ℝ sincCoeff).radius = ⊤ := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.HaarExpChart.sincSeries_radius <;> assumption
private theorem analyticAt_sincSq (s : ℝ) : AnalyticAt ℝ sincSq s := by
  have hpos : 0 < (FormalMultilinearSeries.ofScalars ℝ sincCoeff).radius := by
    rw [radius_sincCoeff]
    simp
  have h := (FormalMultilinearSeries.ofScalars ℝ sincCoeff).hasFPowerSeriesOnBall hpos
  have hs : s ∈ Metric.eball (0 : ℝ) (FormalMultilinearSeries.ofScalars ℝ sincCoeff).radius := by
    rw [radius_sincCoeff]
    exact edist_lt_top _ _
  exact h.analyticOnNhd s hs
private theorem sincSq_sq (u : ℝ) : sincSq (u ^ 2) = Real.sinc u := by apply _root_.YangMills.DeltaSharedProofs.p500885 <;> assumption
private theorem sinc_pos_of_lt_pi {u : ℝ} (h0 : 0 ≤ u) (hu : u < Real.pi) : 0 < Real.sinc u := by apply _root_.YangMills.SharedProofs.p1819 <;> assumption
private theorem analyticAt_haarLogRatio {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {z : E}
    {w : E → imaginaryQuaternions} (hw : AnalyticAt ℝ w z) (h : ‖w z‖ < Real.pi) :
    AnalyticAt ℝ (fun σ => haarLogRatio (w σ)) z := by
  have h1 : AnalyticAt ℝ (fun p => ((w p : imaginaryQuaternions) : ℍ[ℝ])) z :=
    (imaginaryQuaternions.subtypeL.analyticAt _).comp hw
  have h2 : AnalyticAt ℝ (fun p => sincSq (‖w p‖ ^ 2)) z :=
    AnalyticAt.comp (g := sincSq) (f := fun p => ‖w p‖ ^ 2) (analyticAt_sincSq _) (analyticAt_norm_sq h1)
  have h3 : AnalyticAt ℝ (fun p => sincSq (‖w p‖ ^ 2) ^ 2) z := h2.pow 2
  have hp : 0 < sincSq (‖w z‖ ^ 2) ^ 2 := by
    rw [sincSq_sq]
    have := sinc_pos_of_lt_pi (norm_nonneg _) h
    positivity
  have h4 : AnalyticAt ℝ (fun p => Real.log (sincSq (‖w p‖ ^ 2) ^ 2)) z := analyticAt_log_of_pos h3 hp
  refine h4.congr ?_
  have hc : ContinuousAt (fun p => ‖w p‖) z := hw.continuousAt.norm
  filter_upwards [hc.eventually (gt_mem_nhds h)] with p hp'
  show Real.log (sincSq (‖w p‖ ^ 2) ^ 2) = haarLogRatio (w p)
  unfold haarLogRatio
  congr 1
  have e0 : haarRadialDensity 0 = (2 * Real.pi ^ 2)⁻¹ := by
    simp [haarRadialDensity, Real.pi_pos]
  have e1 : haarRadialDensity ‖w p‖ = (Real.sinc ‖w p‖) ^ 2 / (2 * Real.pi ^ 2) := by
    unfold haarRadialDensity
    rw [if_pos hp']
  rw [e0, e1, sincSq_sq]
  have := Real.pi_pos.ne'
  field_simp
abbrev _root_.YangMills.SharedProofs.p101296 := @analyticAt_haarLogRatio
end Haar
section Calculus
variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
private def secondDerivAlong (f : H → ℝ) (P : G →L[ℝ] H) (u v : G) (p : H) : ℝ :=
  fderiv ℝ (fun q => fderiv ℝ f q (P u)) p (P v)
private theorem analyticAt_fderiv_apply {f : H → ℝ} {p : H} (hf : AnalyticAt ℝ f p) (e : H) :
    AnalyticAt ℝ (fun q => fderiv ℝ f q e) p :=
  ((ContinuousLinearMap.apply ℝ ℝ e).analyticAt _).comp hf.fderiv
private theorem analyticAt_secondDerivAlong {f : H → ℝ} {p : H} (P : G →L[ℝ] H) (hf : AnalyticAt ℝ f p)
    (u v : G) : AnalyticAt ℝ (secondDerivAlong f P u v) p :=
  analyticAt_fderiv_apply (analyticAt_fderiv_apply hf (P u)) (P v)
private theorem fderiv_comp_add_clm (g : H → ℝ) (P : G →L[ℝ] H) (p : H) (ζ : G)
    (hd : DifferentiableAt ℝ g (p + P ζ)) :
    fderiv ℝ (fun η => g (p + P η)) ζ = (fderiv ℝ g (p + P ζ)).comp P := by
  have h1 : HasFDerivAt (fun η => p + P η) P ζ := P.hasFDerivAt.const_add p
  exact (hd.hasFDerivAt.comp ζ h1).fderiv
private theorem fderiv_fderiv_comp_add_clm {f : H → ℝ} {p : H} (P : G →L[ℝ] H) (hf : AnalyticAt ℝ f p)
    (u v : G) : fderiv ℝ (fun ζ => fderiv ℝ (fun η => f (p + P η)) ζ u) 0 v = secondDerivAlong f P u v p := by
  have hcont : Filter.Tendsto (fun ζ : G => p + P ζ) (𝓝 0) (𝓝 p) := by
    have h : Continuous (fun ζ : G => p + P ζ) := by fun_prop
    simpa using h.tendsto 0
  have hev : ∀ᶠ ζ in 𝓝 (0 : G), AnalyticAt ℝ f (p + P ζ) := hcont.eventually hf.eventually_analyticAt
  have heq : (fun ζ => fderiv ℝ (fun η => f (p + P η)) ζ u) =ᶠ[𝓝 0]
      fun ζ => (fun q => fderiv ℝ f q (P u)) (p + P ζ) := by
    filter_upwards [hev] with ζ hζ
    rw [fderiv_comp_add_clm f P p ζ hζ.differentiableAt]
    rfl
  rw [heq.fderiv_eq]
  have hg : DifferentiableAt ℝ (fun q => fderiv ℝ f q (P u)) (p + P 0) := by
    rw [map_zero, add_zero]
    exact (analyticAt_fderiv_apply hf (P u)).differentiableAt
  rw [fderiv_comp_add_clm (fun q => fderiv ℝ f q (P u)) P p 0 hg, map_zero, add_zero]
  rfl
private theorem hasFDerivAt_fderiv_apply {Ψ : G → ℝ} (hΨ : AnalyticAt ℝ Ψ 0) (u : G) :
    HasFDerivAt (fun ζ => fderiv ℝ Ψ ζ u)
      ((ContinuousLinearMap.apply ℝ ℝ u).comp (fderiv ℝ (fderiv ℝ Ψ) 0)) 0 :=
  (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp 0 hΨ.fderiv.differentiableAt.hasFDerivAt
private theorem deriv_deriv_line {Ψ : G → ℝ} (hΨ : AnalyticAt ℝ Ψ 0) (u : G) :
    deriv (deriv fun r : ℝ => Ψ (r • u)) 0 = fderiv ℝ (fderiv ℝ Ψ) 0 u u := by
  have hline : ∀ r : ℝ, HasDerivAt (fun r : ℝ => r • u) u r := fun r => by
    simpa using (hasDerivAt_id r).smul_const u
  have hcont : Filter.Tendsto (fun r : ℝ => r • u) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun r : ℝ => r • u) := by fun_prop
    simpa using h.tendsto 0
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), AnalyticAt ℝ Ψ (r • u) := hcont.eventually hΨ.eventually_analyticAt
  have heq : (deriv fun r : ℝ => Ψ (r • u)) =ᶠ[𝓝 0] fun r => fderiv ℝ Ψ (r • u) u := by
    filter_upwards [hev] with r hr
    exact (hr.differentiableAt.hasFDerivAt.comp_hasDerivAt r (hline r)).deriv
  rw [heq.deriv_eq]
  have h1 : HasFDerivAt (fun ζ => fderiv ℝ Ψ ζ u)
      ((ContinuousLinearMap.apply ℝ ℝ u).comp (fderiv ℝ (fderiv ℝ Ψ) 0)) ((0 : ℝ) • u) := by
    rw [zero_smul]
    exact hasFDerivAt_fderiv_apply hΨ u
  exact (h1.comp_hasDerivAt 0 (hline 0)).deriv
abbrev _root_.YangMills.SharedProofs.p66357 := @deriv_deriv_line
end Calculus
section Floor
variable {B : Type} [Fintype B] [DecidableEq B]
private def basisVariation (i : B × Fin 3) : BondField B :=
  ColdStepAtMirrorFrames.bondVariation i.1 (EuclideanSpace.single i.2 1)
private theorem sum_basisVariation_apply (x : B × Fin 3 → ℝ) (b : B) (α : Fin 3) :
    (∑ i, x i • basisVariation i : BondField B) b α = x (b, α) := by
  have hc : ∀ C : BondField B, C b α =
      ((EuclideanSpace.proj α : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj b : BondField B →L[ℝ] BondVector)) C := fun _ => rfl
  rw [hc, map_sum, Finset.sum_eq_single (b, α)]
  · rw [map_smul, ← hc]
    simp [basisVariation, ColdStepAtMirrorFrames.bondVariation]
  · rintro ⟨b', α'⟩ - hne
    rw [map_smul, ← hc, smul_eq_mul]
    by_cases hb : b' = b
    · subst hb
      have hα : α' ≠ α := fun h => hne (by rw [h])
      simp [basisVariation, ColdStepAtMirrorFrames.bondVariation, hα]
    · simp [basisVariation, ColdStepAtMirrorFrames.bondVariation, Pi.single_eq_of_ne (Ne.symm hb)]
  · intro h
    exact absurd (Finset.mem_univ _) h
abbrev _root_.YangMills.DeltaSharedProofs.p501131 := @sum_basisVariation_apply
private theorem sum_norm_sq_sum_basisVariation (x : B × Fin 3 → ℝ) :
    ∑ b, ‖(∑ i, x i • basisVariation i : BondField B) b‖ ^ 2 = x ⬝ᵥ x := by
  have h : ∀ b, ‖(∑ i, x i • basisVariation i : BondField B) b‖ ^ 2 = ∑ α, x (b, α) * x (b, α) := by
    intro b
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [sum_basisVariation_apply, Real.norm_eq_abs, sq_abs, sq]
  simp only [h, dotProduct]
  rw [Fintype.sum_prod_type]
abbrev _root_.YangMills.DeltaSharedProofs.p502176 := @sum_norm_sq_sum_basisVariation
private theorem isUnit_interpolate_of_hessian_floor {Ψ : BondField B → ℝ} (hΨ : AnalyticAt ℝ Ψ 0) {lam : ℝ}
    (hlam : 0 < lam)
    (hfl : ∀ u : BondField B, lam * ∑ b, ‖u b‖ ^ 2 ≤ deriv (deriv fun r : ℝ => Ψ (r • u)) 0)
    (S : Matrix (B × Fin 3) (B × Fin 3) ℝ)
    (hS : ∀ i j, S i j = fderiv ℝ (fun ζ => fderiv ℝ Ψ ζ (basisVariation i)) 0 (basisVariation j)) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    IsUnit (s • S + (1 - s) • lam • (1 : Matrix (B × Fin 3) (B × Fin 3) ℝ)) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have hS' : ∀ i j, S i j = fderiv ℝ (fderiv ℝ Ψ) 0 (basisVariation j) (basisVariation i) := fun i j => by
    rw [hS, (hasFDerivAt_fderiv_apply hΨ (basisVariation i)).fderiv]
    rfl
  have hquad : ∀ x : B × Fin 3 → ℝ, lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ S.mulVec x := by
    intro x
    have h1 := hfl (∑ i, x i • basisVariation i)
    rw [sum_norm_sq_sum_basisVariation, deriv_deriv_line hΨ] at h1
    refine h1.trans_eq ?_
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
      dotProduct, Matrix.mulVec, hS', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hker : ∀ x : B × Fin 3 → ℝ,
      (s • S + (1 - s) • lam • (1 : Matrix (B × Fin 3) (B × Fin 3) ℝ)).mulVec x = 0 → x = 0 := by
    intro x hx
    have h2 : x ⬝ᵥ (s • S + (1 - s) • lam • (1 : Matrix (B × Fin 3) (B × Fin 3) ℝ)).mulVec x = 0 := by
      rw [hx, dotProduct_zero]
    have h3 : x ⬝ᵥ (s • S + (1 - s) • lam • (1 : Matrix (B × Fin 3) (B × Fin 3) ℝ)).mulVec x =
        s * (x ⬝ᵥ S.mulVec x) + (1 - s) * (lam * (x ⬝ᵥ x)) := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_smul]
      simp only [smul_eq_mul]
    have h4 := hquad x
    have h5 : 0 ≤ x ⬝ᵥ x := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h6 : lam * (x ⬝ᵥ x) ≤ 0 := by
      have := mul_le_mul_of_nonneg_left h4 hs.1
      have e : lam * (x ⬝ᵥ x) = s * (lam * (x ⬝ᵥ x)) + (1 - s) * (lam * (x ⬝ᵥ x)) := by ring
      rw [h3] at h2
      linarith
    have h7 : x ⬝ᵥ x = 0 := le_antisymm (by nlinarith) h5
    exact dotProduct_self_eq_zero.1 h7
  intro x y h
  have h8 : (s • S + (1 - s) • lam • (1 : Matrix (B × Fin 3) (B × Fin 3) ℝ)).mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  exact sub_eq_zero.1 (hker _ h8)
abbrev _root_.YangMills.DeltaSharedProofs.p1583 := @isUnit_interpolate_of_hessian_floor
end Floor
section Chart
variable {F : BlockFrame}
private theorem toImaginary_add_smul (u e : EuclideanSpace ℝ (Fin 3)) (τ : ℝ) :
    toImaginary (u + τ • e) = toImaginary u + τ • toImaginary e := by
  apply Subtype.ext
  ext <;> simp only [toImaginary] <;> first | rfl | (show (0 : ℝ) = 0 + τ * 0; ring)
abbrev _root_.YangMills.DeltaSharedProofs.p501185 := @toImaginary_add_smul
abbrev _root_.YangMills.SharedProofs.p23127 := @toImaginary_add_smul
private theorem toImaginary_zero : toImaginary (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
private theorem stepCoordinates_add_smul (u v : StepVariable (finiteCells F)) (θ : ℝ) (x : F.Site F.depth)
    (i : Fin 4) : stepCoordinates (u + θ • v) x i = stepCoordinates u x i + θ • stepCoordinates v x i := by
  unfold stepCoordinates
  split_ifs with h
  · exact toImaginary_add_smul _ _ _
  · simp
abbrev _root_.YangMills.SharedProofs.p44921 := @stepCoordinates_add_smul
private theorem stepCoordinates_zero (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
  unfold stepCoordinates
  split_ifs with h
  · exact toImaginary_zero
  · rfl
private theorem coordsAboveFrame_zero (flag : Bool) (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (x : F.Site F.depth) (i : Fin 4) :
    coordsAboveFrame flag a ρ m V 0 x i = stepFrame flag a ρ m (x, i) V := by
  unfold coordsAboveFrame
  rw [stepCoordinates_zero, add_zero]
private theorem chartCoordinates_add_smul_step (u v : StepVariable (finiteCells F)) (θ : ℝ) :
    chartCoordinates (stepCoordinates (u + θ • v)) (fun _ _ => 0) =
      chartCoordinates (stepCoordinates u) (fun _ _ => 0) + θ • chartCoordinates (stepCoordinates v) (fun _ _ => 0) := by
  rw [← FrameCurves.chartCoordinates_add_smul]
  congr 1
  · funext x i
    exact stepCoordinates_add_smul u v θ x i
  · funext y i
    simp
abbrev _root_.YangMills.SharedProofs.p68589 := @chartCoordinates_add_smul_step
private theorem chartCoordinates_step_zero :
    chartCoordinates (stepCoordinates (0 : StepVariable (finiteCells F)))
      (fun _ _ => (0 : imaginaryQuaternions)) = 0 := by
  have e : stepCoordinates (0 : StepVariable (finiteCells F)) = fun _ _ => 0 :=
    funext fun x => funext fun i => stepCoordinates_zero x i
  rw [e]
  exact FrameCurves.chartCoordinates_zero
abbrev _root_.YangMills.SharedProofs.p69363 := @chartCoordinates_step_zero
private def stepChartCLM (F : BlockFrame) : StepVariable (finiteCells F) →L[ℝ] (Fin (chartDimension F) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun η => chartCoordinates (stepCoordinates η) (fun _ _ => 0)
      map_add' := fun u v => by simpa using chartCoordinates_add_smul_step u v 1
      map_smul' := fun r v => by
        have h := chartCoordinates_add_smul_step 0 v r
        rw [chartCoordinates_step_zero, zero_add, zero_add] at h
        exact h }
private theorem stepChartCLM_apply (η : StepVariable (finiteCells F)) :
    stepChartCLM F η = chartCoordinates (stepCoordinates η) (fun _ _ => 0) := rfl
private theorem chartedEnergyAtMinimizer_leftTranslate (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (a ρ : ℝ) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) (η : StepVariable (finiteCells F)) :
    chartedEnergyAtMinimizer a ρ (leftTranslate (bondSpread c X τ) V) η =
      chartRestriction a (fun x i => stepFrame true a ρ 0 (x, i) V) V (chartDirections F)
        (FrameCurves.frameCurve true a ρ 0 V c X τ + stepChartCLM F η) := by
  have h := (hCE F a (fun x i => stepFrame true a ρ 0 (x, i) V)
    (fun x i => (stepFrame true a ρ 0 (x, i) (leftTranslate (bondSpread c X τ) V) - stepFrame true a ρ 0 (x, i) V) +
      (1 : ℝ) • stepCoordinates η x i) V (fun y i => bondSpread c X τ y i + (1 : ℝ) • (0 : imaginaryQuaternions))
      hL hs).1
  rw [FrameCurves.chartCoordinates_add_smul, one_smul] at h
  have e1 : (fun y i => bondSpread c X τ y i + (1 : ℝ) • (0 : imaginaryQuaternions)) = bondSpread c X τ := by
    funext y i
    simp
  rw [e1] at h
  have e2 : chartCoordinates
      (fun x i => stepFrame true a ρ 0 (x, i) (leftTranslate (bondSpread c X τ) V) - stepFrame true a ρ 0 (x, i) V)
      (bondSpread c X τ) = FrameCurves.frameCurve true a ρ 0 V c X τ := rfl
  rw [stepChartCLM_apply, ← e2]
  refine Eq.trans ?_ h.symm
  show chartedEnergy a (coordsAboveFrame true a ρ 0 (leftTranslate (bondSpread c X τ) V) η)
    (leftTranslate (bondSpread c X τ) V) = _
  congr 1
  funext x i
  simp only [coordsAboveFrame, one_smul, stepFrame]
  abel
end Chart
section Step
variable {F : BlockFrame}
private theorem mem_chordBonds_of_not_axial (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {x : F.Site F.depth} {i : Fin 4} (h : ¬ IsAxialTreeBond (x, i)) : (x, i) ∈ chordBonds (finiteCells F) := by
  have hk : F.depth ≤ F.top := Nat.le_succ _
  unfold chordBonds innerBonds
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨⟨mem_sitesOfCells_finiteCells hodd hs hk x, mem_sitesOfCells_finiteCells hodd hs hk _⟩, h⟩
abbrev _root_.YangMills.SharedProofs.p125121 := @mem_chordBonds_of_not_axial
private theorem isSmallCurvature_of_isCold (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j ≤ F.top) {s : ℝ} {X : F.GaugeField j} (h : IsCold (finiteCells F) j s X) : IsSmallCurvature s X := by apply _root_.YangMills.SharedProofs.p16091 <;> assumption
private theorem minimizingChart_spec (hOL : MinimizingChartUnique) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    {a ρ N0 s : ℝ} {V : F.GaugeField F.top} (hρ : ρ ≤ 1) (h : HasColdMinimizer a ρ N0 s (finiteCells F) V) :
    IsMinimizingChart a (finiteCells F) V ρ (minimizingCoordinates a (finiteCells F) V ρ) ∧
      ∀ b ∈ chordBonds (finiteCells F), ‖minimizingCoordinates a (finiteCells F) V ρ b.1 b.2‖ ≤ N0 * s := by
  obtain ⟨w, ⟨w0, w1, w2⟩, -, -⟩ := id h
  have hw : IsMinimizingChart a (finiteCells F) V ρ w :=
    ⟨w0, fun b hb => (w1 b hb).trans (min_le_left _ _), w2⟩
  have hw' : IsMinimizingChart a (finiteCells F) V ρ (minimizingCoordinates a (finiteCells F) V ρ) := by
    have hex : ∃ w, IsMinimizingChart a (finiteCells F) V ρ w := ⟨w, hw⟩
    unfold minimizingCoordinates
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hw', ?_⟩
  have e := (hOL F a ρ N0 s V _ hL hs hρ h hw').1 w hw
  intro b hb
  rw [← e]
  exact (w1 b hb).trans (min_le_right _ _)
abbrev _root_.YangMills.SharedProofs.p45920 := @minimizingChart_spec
private theorem norm_contourAverage_ge (hL : Odd F.blockSide) (W : F.GaugeField F.depth) (V : F.GaugeField F.top)
    (c : F.Site F.top × Fin 4) {ε : ℝ}
    (h : ∀ (u : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), u ∈ centredCube F.blockSide →
      ‖contourHolonomyDefect W V c u π - 1‖ ≤ ε) :
    1 - ε ≤ ‖BlockAverages.contourAverage W c‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.one_sub_le_norm_contourAverage <;> assumption
private theorem isBondAnalyticAt_stepDensity (hK : ChartEnergyKernelBound) (hCE : ChartedEnergyInCoordinates)
    (hOL : MinimizingChartUnique) (hCh : ChartedFieldContourBound) {a : ℝ} {L : ℕ} {c : ColdChainParameters}
    (ha : 1 ≤ a) (hL : Odd L) (hL40 : 2 ^ 40 ≤ L) (hc : c.Admissible a L) (hF : IsBlockTorus L F) {s : ℝ}
    (hs : 0 < s) (hsσ : s ≤ c.σA) (hsL : 2 ^ 10 * (L : ℝ) * (c.N 0 + 1) * s ≤ 9 / 8) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) (Y : F.Cell) : IsBondAnalyticAt (stepDensity a c.ρA c.lam Y) V := by
  obtain ⟨⟨-, hρ1, -⟩, -⟩ := hc.classical
  obtain ⟨-, -, hlam, -, -, hNpos, -⟩ := hc.positivity
  have hodd : Odd F.blockSide := by
    rw [hF.1]
    exact hL
  obtain ⟨n, hn, hside⟩ := hF.2
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    omega
  have hs1 : ∀ i, 0 < F.extent i := fun i => by
    rw [hside]
    omega
  have hcla := hc.estimates F s V hF hs hsσ hV
  obtain ⟨hleast, hsmall0⟩ := minimizingChart_spec hOL hodd hs2 hρ1 hcla.minimizer
  have hsmall : ∀ b ∈ chordBonds (finiteCells F), ‖torusCoordinate a c.ρA b V‖ ≤ c.N 0 * s := hsmall0
  have hone := (hOL F a c.ρA (c.N 0) s V _ hodd hs2 hρ1 hcla.minimizer hleast).2
  have hLone : (1 : ℝ) ≤ L := by exact_mod_cast hL.pos
  have hNs : 0 ≤ c.N 0 * s := (mul_pos (hNpos 0) hs).le
  have hε : 2 ^ 10 * ((L : ℝ) * (c.N 0 * s)) ≤ 9 / 8 := by
    have : 0 ≤ (L : ℝ) * s := by positivity
    nlinarith
  have hCs : c.N 0 * s ≤ 1 := by nlinarith
  have hframe : ∀ b : F.Site F.depth × Fin 4, stepFrame true a c.ρA 0 b V = torusCoordinate a c.ρA b V :=
    fun b => by simp [stepFrame, torusCoordinate]
  have hfun : (fun x i => stepFrame true a c.ρA 0 (x, i) V) = minimizingCoordinates a (finiteCells F) V c.ρA := by
    funext x i
    simp [stepFrame, minimizingBondCoordinate]
  have hfa : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame true a c.ρA 0 b) V := fun b hb => by
    have e : stepFrame true a c.ρA 0 b = minimizingBondCoordinate a c.ρA (finiteCells F) b := by
      funext V'
      simp [stepFrame]
    rw [e]
    exact (hcla.coordinates b hb).1
  have hpt : IsAdmissibleChartPoint L c.σA (fun x i => stepFrame true a c.ρA 0 (x, i) V) V := by
    refine ⟨fun b hb => ?_, fun p hp => ?_⟩
    · have h1 := hsmall b hb
      rw [← hframe] at h1
      refine h1.trans ?_
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · rw [hfun]
      have h1 : IsSmallCurvature (s / 8) (chartedField (minimizingCoordinates a (finiteCells F) V c.ρA) V) :=
        isSmallCurvature_of_isCold hodd hs1 (Nat.le_succ _) hone
      exact (h1 p hp).trans_le (by linarith)
  obtain ⟨Ck, -, hker⟩ := hK a L c ha hL hL40 hc
  have hf : AnalyticAt ℝ (chartRestriction a (fun x i => stepFrame true a c.ρA 0 (x, i) V) V (chartDirections F)) 0 :=
    (hker F _ V hF hpt _ (chartDirections F)).1
  intro k e X
  change AnalyticAt ℝ (fun τ : Fin k → ℝ => stepDensity a c.ρA c.lam Y (leftTranslate (bondSpread e X τ) V)) 0
  have hQa := FrameCurves.analyticAt_frameCurve hfa e X
  have hQ0 := FrameCurves.frameCurve_zero true a c.ρA 0 V e X
  have hV0 : leftTranslate (bondSpread e X 0) V = V := FrameCurves.leftTranslate_bondSpread_zero e X V
  have hen : ∀ τ, chartedEnergyAtMinimizer a c.ρA (leftTranslate (bondSpread e X τ) V) = fun η =>
      chartRestriction a (fun x i => stepFrame true a c.ρA 0 (x, i) V) V (chartDirections F)
        (FrameCurves.frameCurve true a c.ρA 0 V e X τ + stepChartCLM F η) := fun τ =>
    funext (chartedEnergyAtMinimizer_leftTranslate hCE hodd hs2 a c.ρA V e X τ)
  have hE : AnalyticAt ℝ (chartedEnergyAtMinimizer a c.ρA V) 0 := by
    have h0 := hen 0
    rw [hV0, hQ0] at h0
    rw [h0]
    have h1 : AnalyticAt ℝ (fun η : StepVariable (finiteCells F) =>
        (0 : Fin (chartDimension F) → ℝ) + stepChartCLM F η) 0 :=
      analyticAt_const.add ((stepChartCLM F).analyticAt 0)
    exact AnalyticAt.comp_of_eq hf h1 (by simp)
  have hfl : ∀ u : StepVariable (finiteCells F), c.lam * ∑ b, ‖u b‖ ^ 2 ≤
      deriv (deriv fun r : ℝ => chartedEnergyAtMinimizer a c.ρA V (r • u)) 0 := by
    intro u
    have h := hcla.hessian (minimizingCoordinates a (finiteCells F) V c.ρA) (stepCoordinates u) hleast.1
      (fun b hb => dif_neg hb) hleast.2.1 (fun p hp => (hone p hp).trans_le (by linarith))
    have e1 : ∑ b, ‖u b‖ ^ 2 = ∑ b ∈ chordBonds (finiteCells F), ‖stepCoordinates u b.1 b.2‖ ^ 2 := by
      rw [← Finset.sum_coe_sort (chordBonds (finiteCells F))]
      refine Finset.sum_congr rfl fun b _ => ?_
      have e2 : stepCoordinates u b.1.1 b.1.2 = toImaginary (u b) := dif_pos b.2
      rw [e2, norm_toImaginary]
    have e3 : (fun r : ℝ => chartedEnergyAtMinimizer a c.ρA V (r • u)) = fun τ : ℝ =>
        blockEnergy a (finiteCells F) F.depth
          (chartedField (fun x i => minimizingCoordinates a (finiteCells F) V c.ρA x i + τ • stepCoordinates u x i) V)
          V := by
      funext r
      show chartedEnergy a (coordsAboveFrame true a c.ρA 0 V (r • u)) V = _
      unfold chartedEnergy
      congr 2
      funext x i
      have h2 := stepCoordinates_add_smul 0 u r x i
      rw [stepCoordinates_zero, zero_add, zero_add] at h2
      simp only [coordsAboveFrame, h2]
      rw [← congrFun (congrFun hfun x) i]
    rw [e1, e3]
    exact h
  have hU : ∀ s' ∈ Set.Icc (0 : ℝ) 1, IsUnit (s' • chartedHessian a c.ρA V 0 +
      (1 - s') • c.lam • (1 : Matrix (ChartCoord F) (ChartCoord F) ℝ)) := fun s' h' =>
    isUnit_interpolate_of_hessian_floor hE hlam hfl _ (fun i j => rfl) s' h'
  have hQt : Filter.Tendsto (FrameCurves.frameCurve true a c.ρA 0 V e X) (𝓝 0) (𝓝 0) := by
    have h := hQa.continuousAt.tendsto
    rwa [hQ0] at h
  have hfev := hQt.eventually hf.eventually_analyticAt
  obtain ⟨M, hMd⟩ : ∃ M : (Fin k → ℝ) → Matrix (ChartCoord F) (ChartCoord F) ℝ, M = fun τ i j =>
      secondDerivAlong (chartRestriction a (fun x i => stepFrame true a c.ρA 0 (x, i) V) V (chartDirections F))
        (stepChartCLM F) (basisVariation i) (basisVariation j) (FrameCurves.frameCurve true a c.ρA 0 V e X τ) :=
    ⟨_, rfl⟩
  have hent : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), chartedHessian a c.ρA (leftTranslate (bondSpread e X τ) V) 0 = M τ := by
    filter_upwards [hfev] with τ hτ
    refine Matrix.ext fun i j => ?_
    rw [hMd]
    show fderiv ℝ (fun ζ => fderiv ℝ (chartedEnergyAtMinimizer a c.ρA (leftTranslate (bondSpread e X τ) V)) ζ
      (basisVariation i)) 0 (basisVariation j) = _
    rw [hen τ]
    exact fderiv_fderiv_comp_add_clm (stepChartCLM F) hτ _ _
  have hM0 : M 0 = chartedHessian a c.ρA V 0 := by
    have h := hent.self_of_nhds
    rw [hV0] at h
    exact h.symm
  have hMe : ∀ i j, AnalyticAt ℝ (fun τ => M τ i j) 0 := fun i j => by
    rw [hMd]
    exact AnalyticAt.comp_of_eq (analyticAt_secondDerivAlong (stepChartCLM F) hf _ _) hQa hQ0
  have hA := analyticAt_integral_matrix_resolvent M 0 c.lam (fun i : ChartCoord F => enclosingCell i.1.1.1 = Y)
    hMe (by
      rw [hM0]
      exact hU)
  have hA' : AnalyticAt ℝ (fun τ : Fin k → ℝ => ∫ s' in (0 : ℝ)..1,
      hessianCellShare a c.ρA c.lam Y (leftTranslate (bondSpread e X τ) V) s') 0 := by
    refine hA.congr ?_
    filter_upwards [hent] with τ hτ
    unfold hessianCellShare
    rw [hτ]
  have hfr : ∀ b ∈ chordBonds (finiteCells F),
      AnalyticAt ℝ (fun τ : Fin k → ℝ => stepFrame true a c.ρA 0 b (leftTranslate (bondSpread e X τ) V)) 0 :=
    fun b hb => hfa b hb k e X
  have hX : ∀ x i, AnalyticAt ℝ (fun τ : Fin k → ℝ =>
      ((fieldAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0 x i : UnitQuaternion) : ℍ[ℝ])) 0 := by
    intro x i
    by_cases hcr : IsCrossingBond (x, i)
    · have ht : ¬ IsAxialTreeBond (x, i) := fun h => h.1 hcr
      have e1 : (fun τ : Fin k → ℝ =>
          ((fieldAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0 x i : UnitQuaternion) : ℍ[ℝ])) =
          fun τ => ((expUnit (stepFrame true a c.ρA 0 (x, i) (leftTranslate (bondSpread e X τ) V)) : UnitQuaternion)
            : ℍ[ℝ]) * (((expUnit (bondSpread e X τ (enclosingCell x) i) : UnitQuaternion) : ℍ[ℝ]) *
              ((V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ])) := by
        funext τ
        simp only [fieldAboveFrame, chartedField, if_pos hcr, coordsAboveFrame_zero]
        rfl
      rw [e1]
      exact (analyticAt_expUnit (hfr _ (mem_chordBonds_of_not_axial hodd hs1 ht))).mul
        ((analyticAt_expUnit (FrameCurves.analyticAt_bondSpread e X _ _)).mul analyticAt_const)
    · by_cases ht : IsAxialTreeBond (x, i)
      · have e1 : (fun τ : Fin k → ℝ =>
            ((fieldAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0 x i : UnitQuaternion) : ℍ[ℝ])) =
            fun _ => ((1 : UnitQuaternion) : ℍ[ℝ]) := by
          funext τ
          simp only [fieldAboveFrame, chartedField, if_neg hcr, if_pos ht]
        rw [e1]
        exact analyticAt_const
      · have e1 : (fun τ : Fin k → ℝ =>
            ((fieldAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0 x i : UnitQuaternion) : ℍ[ℝ])) =
            fun τ => ((expUnit (stepFrame true a c.ρA 0 (x, i) (leftTranslate (bondSpread e X τ) V)) :
              UnitQuaternion) : ℍ[ℝ]) := by
          funext τ
          simp only [fieldAboveFrame, chartedField, if_neg hcr, if_neg ht, coordsAboveFrame_zero]
        rw [e1]
        exact analyticAt_expUnit (hfr _ (mem_chordBonds_of_not_axial hodd hs1 ht))
  have hB : AnalyticAt ℝ (fun τ : Fin k → ℝ =>
      ∑ c' ∈ (innerBonds (finiteCells F) F.top).filter (fun c' => c'.1 = Y),
        Real.log ‖BlockAverages.contourAverage (fieldAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0) c'‖) 0 := by
    refine Finset.analyticAt_fun_sum _ fun c' _ => analyticAt_log_norm (analyticAt_contourAverage hX c') ?_
    rw [hV0]
    have e3 : fieldAboveFrame true a c.ρA 0 V 0 = torusMinimizingField a c.ρA V := by
      show chartedField (coordsAboveFrame true a c.ρA 0 V 0) V =
        chartedField (minimizingCoordinates a (finiteCells F) V c.ρA) V
      congr 1
      funext x i
      rw [coordsAboveFrame_zero]
      exact congrFun (congrFun hfun x) i
    rw [e3]
    have h1 : 1 - 5 * (L : ℝ) * (c.N 0 * s) ≤ ‖BlockAverages.contourAverage (torusMinimizingField a c.ρA V) c'‖ :=
      norm_contourAverage_ge hodd _ V c' fun u π hu => by
        have h2 := hCh F (minimizingCoordinates a (finiteCells F) V c.ρA) V (c.N 0 * s) hodd hs2 hNs hsmall0 c' u π hu
        refine h2.trans_eq ?_
        rw [hF.1]
    intro h0
    rw [h0, norm_zero] at h1
    linarith
  have hH : AnalyticAt ℝ (fun τ : Fin k → ℝ => ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      haarLogRatio (coordsAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0 b.1.1 b.1.2) else 0) 0 := by
    refine Finset.analyticAt_fun_sum _ fun b _ => ?_
    by_cases hY : enclosingCell b.1.1 = Y
    · simp only [if_pos hY]
      have hw : AnalyticAt ℝ (fun τ : Fin k → ℝ =>
          coordsAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0 b.1.1 b.1.2) 0 :=
        (hfr b.1 b.2).congr (Filter.Eventually.of_forall fun τ => (coordsAboveFrame_zero _ _ _ _ _ _ _).symm)
      refine analyticAt_haarLogRatio hw ?_
      show ‖coordsAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X 0) V) 0 b.1.1 b.1.2‖ < Real.pi
      rw [hV0, coordsAboveFrame_zero]
      have h1 := hsmall b.1 b.2
      rw [← hframe] at h1
      have := Real.pi_gt_three
      exact lt_of_le_of_lt (h1.trans hCs) (by linarith)
    · simp only [if_neg hY]
      exact analyticAt_const
  unfold stepDensity
  exact ((analyticAt_const.mul hA').add (analyticAt_const.mul hB)).add hH
end Step
end ColdStepAtMirrorFrames.StepDensityAnalytic
namespace StepDensity
open ColdStepAtMirrorFrames ColdStepAtMirrorFrames.StepDensityAnalytic
theorem analyticAtAdmissibleConstants_of_estimates (hK : ChartEnergyKernelBound)
    (hCE : ChartedEnergyInCoordinates) (hOL : MinimizingChartUnique)
    (hG : AdmissibleParametersExist) (hCh : ChartedFieldContourBound) :
    AnalyticAtAdmissibleParameters := by
  intro T hT t n _ hn y W hW k b X
  obtain ⟨c, -, -, hlam, hρ, hσ, -, hN, hc⟩ :=
    hG T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N hT.a_ge hT.L_odd hT.chain
  have hp : ∀ i, (torusFrame T.side t n).period (torusFrame T.side t n).top i = n :=
    fun i => TopLevelSites.period_top i
  have : ∀ i, NeZero ((torusFrame T.side t n).period (torusFrame T.side t n).top i) := fun i => ⟨by
    rw [hp i]
    exact NeZero.ne n⟩
  have hF : IsBlockTorus T.side (torusFrame T.side t n) := ⟨rfl, n, hn, fun _ => rfl⟩
  have hcold : IsSmallCurvature (F := torusFrame T.side t n) (9 / 8 * T.threshold)
      (readAtLevel (torusFrame T.side t n) (torusFrame T.side t n).top W) := by
    rintro ⟨x, μ, ν⟩ hlt
    rw [TopLevelSites.plaquetteDefect_readAtLevel_eq hp]
    exact hW _ μ ν hlt
  have hsσ : 9 / 8 * T.threshold ≤ c.σA := by
    rw [hσ]
    linarith [hT.σ_le, hT.σ_pos]
  have hsL : 2 ^ 10 * (T.side : ℝ) * (c.N 0 + 1) * (9 / 8 * T.threshold) ≤ 9 / 8 := by
    rw [hN]
    linarith [hT.σ_L]
  have h := isBondAnalyticAt_stepDensity hK hCE hOL hCh hT.a_ge hT.L_odd hT.L_ge hc hF
    (by linarith [hT.σ_pos]) hsσ hsL hcold
    (siteOfCoords (torusFrame T.side t n).top fun k => ((y k).cast : ℤ)) k
    (fun l => (torusSiteInFrame (torusFrame T.side t n) (torusFrame T.side t n).top (b l).1, (b l).2)) X
  rw [hlam, hρ] at h
  refine h.congr (Filter.Eventually.of_forall fun τ => ?_)
  show _ = stepDensity T.coupling T.ρA T.lam _
    (readAtLevel (torusFrame T.side t n) (torusFrame T.side t n).top (perturb b X τ W))
  rw [TorusChain.readAtLevel_perturb hp]
end StepDensity
end YangMills.Construction
end
