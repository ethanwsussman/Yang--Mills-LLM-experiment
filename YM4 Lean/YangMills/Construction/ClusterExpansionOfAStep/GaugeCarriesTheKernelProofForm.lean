import YangMills.Construction.ClusterExpansionOfAStep.ContoursFromBases
import YangMills.Construction.ClusterExpansionOfAStep.GaugeCarriesTheKernel
import YangMills.Construction.ColdChainAtEveryLevel.CriticalForAllVariationsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusLumps
open BlockAverages LumpContours TorusContours TorusFields
namespace KernelGauge
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {n : ℕ} [NeZero n]
theorem fineLevelField_gaugeTransform (G : TorusSite (n * ℓ.side) → UnitQuaternion)
    (W : TorusField (n * ℓ.side)) :
    fineLevelField ℓ n (TorusFields.gaugeTransform G W) =
      BlockAverages.gaugeTransform (fun x => G (toTorusSite (n * ℓ.side) x)) (fineLevelField ℓ n W) := by
  funext x i
  have h := _root_.YangMills.Construction.TorusContours.toTorusSite_add (F := stepBlockFrame ℓ.side n) (j := 0) (m := n * ℓ.side)
    (fun i => stepBlockFrame_period_zero i) x (BlockAverages.unitStep 0 i)
  rw [_root_.YangMills.Construction.TorusContours.toTorusSite_unitStep (F := stepBlockFrame ℓ.side n) (j := 0) (m := n * ℓ.side)
    (fun i => stepBlockFrame_period_zero i)] at h
  show G (toTorusSite _ x) * W (toTorusSite _ x) i * (G (toTorusSite _ x + TorusFields.unitStep _ i))⁻¹ =
    G (toTorusSite _ x) * W (toTorusSite _ x) i * (G (toTorusSite _ (x + BlockAverages.unitStep 0 i)))⁻¹
  rw [h]
theorem fineHotLumps_gaugeTransform (γ : (stepBlockFrame ℓ.side n).Site 0 → UnitQuaternion)
    (W : (stepBlockFrame ℓ.side n).GaugeField 0) :
    fineHotLumps ℓ (BlockAverages.gaugeTransform γ W) = fineHotLumps ℓ W := by
  simp only [fineHotLumps, LumpContours.hotLumps, _root_.YangMills.Construction.TorusContours.plaquetteDefect_gaugeTransform]
theorem re_conj_unitQuaternion (u : UnitQuaternion) (q : ℍ[ℝ]) :
    ((u : ℍ[ℝ]) * q * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = q.re := by apply _root_.YangMills.Construction.GaugedCriticality.re_conj_unit <;> assumption
theorem meanKernel_mul_mul_inv (s : ℝ) (m : ℍ[ℝ]) (u v V : UnitQuaternion) :
    TorusContours.meanKernel s ((u : ℍ[ℝ]) * m * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])) (u * V * v⁻¹) =
      TorusContours.meanKernel s m V := by
  have h1 : ((u : ℍ[ℝ]) * m * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])) *
        (((u * V * v⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (u : ℍ[ℝ]) * (m * ((V⁻¹ : UnitQuaternion) : ℍ[ℝ])) * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    have h2 : ((u * V * v⁻¹)⁻¹ : UnitQuaternion) = v * V⁻¹ * u⁻¹ := by group
    have h3 : ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v : ℍ[ℝ]) = 1 := by
      rw [← Submonoid.coe_mul]
      simp
    rw [h2]
    simp only [Submonoid.coe_mul]
    calc (u : ℍ[ℝ]) * m * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          ((v : ℍ[ℝ]) * ((V⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]))
        = (u : ℍ[ℝ]) * m * (((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v : ℍ[ℝ])) *
            ((V⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
          simp only [mul_assoc]
      _ = _ := by
          rw [h3]
          simp only [mul_one, mul_assoc]
  unfold TorusContours.meanKernel
  rw [h1, re_conj_unitQuaternion, norm_mul, norm_mul, _root_.YangMills.Construction.TorusContours.norm_coe_unitQuaternion, _root_.YangMills.Construction.TorusContours.norm_coe_unitQuaternion]
  simp
theorem bondKernel_blockGauge (hL : 1 ≤ ℓ.side) (x : ℝ) (Wf : (stepBlockFrame ℓ.side n).GaugeField 0)
    (γ : (stepBlockFrame ℓ.side n).Site 0 → UnitQuaternion)
    (gy : (stepBlockFrame ℓ.side n).Cell → UnitQuaternion) (Vf Vg : (stepBlockFrame ℓ.side n).GaugeField 1)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (hb : IsBaseChoice ℓ.baseDepth (fineHotLumps ℓ Wf) b)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4)
    (hγ : ∀ y, ∀ z ∈ centredCube ℓ.side, γ (siteAtOffset y z) = gy y)
    (hV : Vg c.1 c.2 = gy c.1 * Vf c.1 c.2 *
      (gy (c.1 + BlockAverages.unitStep (stepBlockFrame ℓ.side n).top c.2))⁻¹) :
    bondKernel ℓ x (BlockAverages.gaugeTransform γ Wf) Vg b c = bondKernel ℓ x Wf Vf b c := by
  have hl := _root_.YangMills.Construction.TorusLumps.KernelGauge.fineHotLumps_gaugeTransform (ℓ := ℓ) γ Wf
  obtain ⟨z₀, hz₀, hb₀⟩ := exists_centredCube_of_isBaseChoice (F := stepBlockFrame ℓ.side n) hL hb c.1
  obtain ⟨z₁, hz₁, hb₁⟩ := exists_centredCube_of_isBaseChoice (F := stepBlockFrame ℓ.side n) hL hb
    (c.1 + BlockAverages.unitStep (stepBlockFrame ℓ.side n).top c.2)
  have h2 : γ (b c.1) = gy c.1 := by
    rw [hb₀]
    exact hγ _ _ hz₀
  have h3 : γ (b (c.1 + BlockAverages.unitStep (stepBlockFrame ℓ.side n).top c.2)) =
      gy (c.1 + BlockAverages.unitStep (stepBlockFrame ℓ.side n).top c.2) := by
    rw [hb₁]
    exact hγ _ _ hz₁
  have h1 := _root_.YangMills.Construction.TorusContours.contourMean_gaugeTransform (F := stepBlockFrame ℓ.side n) ℓ.baseDepth (fineHotLumps ℓ Wf) γ b Wf c
  rw [h2, h3] at h1
  have hm : contourMean ℓ.baseDepth (fineHotLumps ℓ (BlockAverages.gaugeTransform γ Wf)) b
        (BlockAverages.gaugeTransform γ Wf) c =
      ((gy c.1 : UnitQuaternion) : ℍ[ℝ]) * contourMean ℓ.baseDepth (fineHotLumps ℓ Wf) b Wf c *
        (((gy (c.1 + BlockAverages.unitStep (stepBlockFrame ℓ.side n).top c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) :=
    (congrArg (fun H => contourMean ℓ.baseDepth H b (BlockAverages.gaugeTransform γ Wf) c) hl).trans h1
  rw [bondKernel_eq_meanKernel, bondKernel_eq_meanKernel]
  exact (congrArg₂ (TorusContours.meanKernel (ℓ.coupling * x)) hm hV).trans (meanKernel_mul_mul_inv _ _ _ _ _)
end KernelGauge
open KernelGauge in
set_option maxHeartbeats 1000000 in
theorem KernelGaugeInvariance.holds : KernelGaugeInvariance := by
  intro ℓ hfit n _ g W V
  have hL : 1 ≤ ℓ.side := by have := hfit.L_ge; omega
  have hfine := _root_.YangMills.Construction.TorusLumps.KernelGauge.fineLevelField_gaugeTransform (ℓ := ℓ) (blockConstantGauge ℓ.side g) W
  have hlumps : fineHotLumps ℓ (fineLevelField ℓ n (TorusFields.gaugeTransform (blockConstantGauge ℓ.side g) W)) =
      fineHotLumps ℓ (fineLevelField ℓ n W) := by
    rw [hfine]
    exact _root_.YangMills.Construction.TorusLumps.KernelGauge.fineHotLumps_gaugeTransform _ _
  have hbases : baseChoices ℓ (fineLevelField ℓ n (TorusFields.gaugeTransform (blockConstantGauge ℓ.side g) W)) =
      baseChoices ℓ (fineLevelField ℓ n W) := by
    rw [baseChoices_eq, baseChoices_eq, hlumps]
  refine ⟨hlumps, hbases, fun x => ?_⟩
  have hk : ∀ b ∈ baseChoices ℓ (fineLevelField ℓ n W), ∀ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
      bondKernel ℓ x (fineLevelField ℓ n (TorusFields.gaugeTransform (blockConstantGauge ℓ.side g) W))
          (coarseLevelField ℓ n (TorusFields.gaugeTransform g V)) b c =
        bondKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V) b c := by
    intro b hb c
    have hisb : IsBaseChoice ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n W)) b := by
      classical
      exact (Finset.mem_filter.mp hb).2
    rw [hfine]
    refine bondKernel_blockGauge hL x _ _ (fun y => g (toTorusSite n y)) _ _ b hisb c ?_ ?_
    · intro y z hz
      exact congrArg g (parentBlock_siteAtOffset y hz)
    · have h2 := _root_.YangMills.Construction.TorusContours.toTorusSite_add (F := stepBlockFrame ℓ.side n) (j := 1) (m := n)
        (fun i => stepBlockFrame_period_one i) c.1 (BlockAverages.unitStep 1 c.2)
      rw [_root_.YangMills.Construction.TorusContours.toTorusSite_unitStep (F := stepBlockFrame ℓ.side n) (j := 1) (m := n)
        (fun i => stepBlockFrame_period_one i)] at h2
      exact congrArg (fun t => g (toTorusSite n c.1) * V (toTorusSite n c.1) c.2 * (g t)⁻¹) h2.symm
  refine ⟨hk, ?_⟩
  unfold averagedKernel
  rw [hbases]
  exact congrArg (fun t => (1 / ((baseChoices ℓ (fineLevelField ℓ n W)).card : ℝ)) * t)
    (Finset.sum_congr rfl fun b hb => Finset.prod_congr rfl fun c _ => hk b hb c)
end YangMills.Construction.TorusLumps
end
