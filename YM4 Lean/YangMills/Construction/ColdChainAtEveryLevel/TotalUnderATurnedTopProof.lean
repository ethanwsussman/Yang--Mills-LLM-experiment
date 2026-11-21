import YangMills.Construction.ColdChainAtEveryLevel.SmallCoordinatesAreRegular
import YangMills.Construction.ColdChainAtEveryLevel.TaylorBoundsOfTheTotal
import YangMills.Construction.ColdChainAtEveryLevel.TotalUnderATurnedTop
import YangMills.Construction.ColdChainAtEveryLevel.VariationsAlongAMisfit
import YangMills.Construction.ColdChainAtEveryLevel.VelocityOfTheTopMean
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.BlockAverages.RotatedTopAction
open ChartCoordinates LatticePaths
variable {F : BlockFrame}
section Analytic
variable {S : Finset F.Cell} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P}
private theorem analyticAt_expUnit {w : P → imaginaryQuaternions} (hw : AnalyticAt ℝ w p₀) :
    AnalyticAt ℝ (fun p => ((expUnit (w p) : UnitQuaternion) : ℍ[ℝ])) p₀ := by
  have h1 : AnalyticAt ℝ (fun p => ((w p : imaginaryQuaternions) : ℍ[ℝ])) p₀ :=
    ((Submodule.subtypeL imaginaryQuaternions).analyticAt _).comp hw
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) _).comp h1
abbrev _root_.YangMills.SharedProofs.p29648 := @analyticAt_expUnit
private theorem abs_re_le_norm (x : ℍ[ℝ]) : |x.re| ≤ ‖x‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
private def starCL : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.mkContinuous ⟨⟨star, star_add⟩, fun r q => Quaternion.star_smul r q⟩ 1 fun q => by
    rw [one_mul]
    exact (Quaternion.norm_star q).le
private theorem starCL_apply (q : ℍ[ℝ]) : starCL q = star q := rfl
private def reCL : ℍ[ℝ] →L[ℝ] ℝ :=
  LinearMap.mkContinuous (show ℍ[ℝ] →ₗ[ℝ] ℝ from QuaternionAlgebra.reₗ _ _ _) 1 fun q => by
    rw [one_mul, Real.norm_eq_abs]
    exact abs_re_le_norm q
private theorem reCL_apply (q : ℍ[ℝ]) : reCL q = q.re := rfl
private theorem analyticAt_star {q : P → ℍ[ℝ]} (hq : AnalyticAt ℝ q p₀) :
    AnalyticAt ℝ (fun p => star (q p)) p₀ := by
  simpa only [Function.comp_def, starCL_apply] using (starCL.analyticAt _).comp hq
private theorem analyticAt_re {q : P → ℍ[ℝ]} (hq : AnalyticAt ℝ q p₀) :
    AnalyticAt ℝ (fun p => (q p).re) p₀ := by
  simpa only [Function.comp_def, reCL_apply] using (reCL.analyticAt _).comp hq
private theorem analyticAt_norm {q : P → ℍ[ℝ]} (hq : AnalyticAt ℝ q p₀) (hq0 : q p₀ ≠ 0) :
    AnalyticAt ℝ (fun p => ‖q p‖) p₀ := by
  have hn : AnalyticAt ℝ (fun p => (q p * star (q p)).re) p₀ := analyticAt_re (hq.mul (analyticAt_star hq))
  have hsq : ∀ x : ℍ[ℝ], (x * star x).re = ‖x‖ ^ 2 := by
    intro x
    rw [← Quaternion.normSq_def, Quaternion.normSq_eq_norm_mul_self, sq]
  have hpos : 0 < (q p₀ * star (q p₀)).re := by
    rw [hsq]
    have := norm_pos_iff.2 hq0
    positivity
  have hl : AnalyticAt ℝ (fun p => Real.exp ((1 / 2) * Real.log ((q p * star (q p)).re))) p₀ :=
    (analyticAt_const.mul (AnalyticAt.comp (g := Real.log) (f := fun p => (q p * star (q p)).re)
      (analyticAt_log hpos) hn)).rexp'
  refine hl.congr ?_
  have hne : ∀ᶠ p in 𝓝 p₀, q p ≠ 0 := hq.continuousAt.eventually_ne hq0
  filter_upwards [hne] with p hp
  have hp' := norm_pos_iff.2 hp
  rw [hsq, Real.log_pow]
  have : (1 / 2 : ℝ) * (((2 : ℕ) : ℝ) * Real.log ‖q p‖) = Real.log ‖q p‖ := by
    push_cast
    ring
  rw [this, Real.exp_log hp']
abbrev _root_.YangMills.SharedProofs.p78004 := @analyticAt_norm
private theorem analyticAt_polarUnit {q : P → ℍ[ℝ]} (hq : AnalyticAt ℝ q p₀) (hq0 : q p₀ ≠ 0) :
    AnalyticAt ℝ (fun p => ((polarUnit (q p) : UnitQuaternion) : ℍ[ℝ])) p₀ := by
  have hne : ∀ᶠ p in 𝓝 p₀, q p ≠ 0 := hq.continuousAt.eventually_ne hq0
  have heq : (fun p => ‖q p‖⁻¹ • q p) =ᶠ[𝓝 p₀] fun p => ((polarUnit (q p) : UnitQuaternion) : ℍ[ℝ]) := by
    filter_upwards [hne] with p hp
    exact (coe_polarUnit hp).symm
  refine AnalyticAt.congr ?_ heq
  exact ((analyticAt_norm hq hq0).inv (norm_ne_zero_iff.2 hq0)).smul hq
private theorem analyticAt_inv_unit {g : P → UnitQuaternion}
    (hg : AnalyticAt ℝ (fun p => ((g p : UnitQuaternion) : ℍ[ℝ])) p₀) :
    AnalyticAt ℝ (fun p => (((g p)⁻¹ : UnitQuaternion) : ℍ[ℝ])) p₀ := by
  simp only [coe_unitQuaternion_inv]
  exact analyticAt_star hg
private theorem analyticAt_mul_unit {g g' : P → UnitQuaternion}
    (hg : AnalyticAt ℝ (fun p => ((g p : UnitQuaternion) : ℍ[ℝ])) p₀)
    (hg' : AnalyticAt ℝ (fun p => ((g' p : UnitQuaternion) : ℍ[ℝ])) p₀) :
    AnalyticAt ℝ (fun p => ((g p * g' p : UnitQuaternion) : ℍ[ℝ])) p₀ := by
  simp only [Submonoid.coe_mul]
  exact hg.mul hg'
variable {j : ℕ}
private def AnalyticOnBonds (X : P → F.GaugeField j) (p₀ : P) (D : Set (F.Site j)) : Prop :=
  ∀ x i, x ∈ D → x + unitStep j i ∈ D → AnalyticAt ℝ (fun p => ((X p x i : UnitQuaternion) : ℍ[ℝ])) p₀
private theorem analyticAt_pathHolonomy {D : Set (F.Site j)} {X : P → F.GaugeField j}
    (h : AnalyticOnBonds X p₀ D) (x0 : F.Site j) :
    ∀ (l : List PathStep) (v : LatticeFractionalIntegration.Lattice4),
      AllAlong (fun v => x0 + siteOfCoords j v ∈ D) v l →
      AnalyticAt ℝ (fun p => ((pathHolonomy (X p) (x0 + siteOfCoords j v) l : UnitQuaternion) : ℍ[ℝ])) p₀ := by
  intro l
  induction l with
  | nil =>
    intro v _
    simp only [pathHolonomy]
    exact analyticAt_const
  | cons st r ih =>
    intro v hp
    have hnext : x0 + siteOfCoords j v + stepDisplacement j st =
        x0 + siteOfCoords j (v + FlatPairing.stepDisplacement st) := by
      rw [stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_add]
    have hv : x0 + siteOfCoords j v ∈ D := hp.1
    have hw : x0 + siteOfCoords j v + stepDisplacement j st ∈ D := by
      rw [hnext]; exact allAlong_head hp.2
    simp only [pathHolonomy]
    rw [hnext]
    refine analyticAt_mul_unit ?_ (ih _ hp.2)
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      have e : x0 + siteOfCoords j v + stepDisplacement j (i, false) = x0 + siteOfCoords j v - unitStep j i := by
        simp [stepDisplacement, sub_eq_add_neg]
      rw [e] at hw
      exact analyticAt_inv_unit (h _ i hw (by rw [sub_add_cancel]; exact hv))
    · simp only [linkValue, if_true]
      have e : x0 + siteOfCoords j v + stepDisplacement j (i, true) = x0 + siteOfCoords j v + unitStep j i := by
        simp [stepDisplacement]
      rw [e] at hw
      exact h _ i hv hw
private theorem analyticAt_relativePathAverage (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X : P → F.GaugeField j} (R : F.GaugeField j)
    (h : AnalyticOnBonds X p₀ (sitesOfCells S j : Set (F.Site j))) {y : F.Site (j + 1)}
    (hy : y ∈ sitesOfCells S (j + 1)) :
    AnalyticAt ℝ (fun p => relativePathAverage (X p) R y) p₀ := by
  unfold relativePathAverage
  refine (analyticAt_const (v := (1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ))).smul ?_
  refine Finset.analyticAt_fun_sum _ fun a ha => Finset.analyticAt_fun_sum _ fun π _ => ?_
  have := analyticAt_pathHolonomy h (refineSite y) _ 0 (allAlong_axisPath hodd hj hy ha π)
  rw [add_siteOfCoords_zero] at this
  exact analyticAt_mul_unit this analyticAt_const
private theorem analyticAt_balancingGauge (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X : P → F.GaugeField j} (R : F.GaugeField j)
    (h : AnalyticOnBonds X p₀ (sitesOfCells S j : Set (F.Site j))) {y : F.Site (j + 1)}
    (hy : y ∈ sitesOfCells S (j + 1)) (hne : relativePathAverage (X p₀) R y ≠ 0) :
    AnalyticAt ℝ (fun p => ((balancingGauge (X p) R y : UnitQuaternion) : ℍ[ℝ])) p₀ :=
  analyticAt_inv_unit (analyticAt_polarUnit (analyticAt_relativePathAverage hodd hj R h hy) hne)
private theorem analyticAt_contourAverage (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X : P → F.GaugeField j} (h : AnalyticOnBonds X p₀ (sitesOfCells S j : Set (F.Site j)))
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1)) :
    AnalyticAt ℝ (fun p => contourAverage (X p) c) p₀ := by
  unfold contourAverage
  refine (analyticAt_const (v := (1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ))).smul ?_
  refine Finset.analyticAt_fun_sum _ fun a ha => Finset.analyticAt_fun_sum _ fun π _ => ?_
  have := analyticAt_pathHolonomy h (refineSite c.1) _ 0 (allAlong_bondContour hodd hj hc ha π)
  rw [add_siteOfCoords_zero] at this
  exact this
private theorem analyticAt_gaugedContourAverage (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {X : P → F.GaugeField j} (R : F.GaugeField j)
    (h : AnalyticOnBonds X p₀ (sitesOfCells S j : Set (F.Site j))) {c : F.Site (j + 1) × Fin 4}
    (hc : c ∈ innerBonds S (j + 1)) (h1 : relativePathAverage (X p₀) R c.1 ≠ 0)
    (h2 : relativePathAverage (X p₀) R (c.1 + unitStep (j + 1) c.2) ≠ 0) :
    AnalyticAt ℝ (fun p => gaugedContourAverage (X p) (balancingGauge (X p) R) c) p₀ := by
  unfold gaugedContourAverage
  exact ((analyticAt_balancingGauge hodd hj R h (innerBonds_ends hc).1 h1).mul
    (analyticAt_contourAverage hodd hj h hc)).mul
    (analyticAt_inv_unit (analyticAt_balancingGauge hodd hj R h (innerBonds_ends hc).2 h2))
private theorem analyticOnBonds_chartField (hodd : Odd F.blockSide) (R : F.FieldChain) {C : P → ChainChart F}
    (hu : ∀ b ∈ innerBonds S 0, AnalyticAt ℝ (fun p => (C p).fine b.1 b.2) p₀)
    (hmu : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
      AnalyticAt ℝ (fun p => (C p).coarse j b.1 b.2) p₀)
    (hreg : ChartIsRegular S R (C p₀)) : ∀ j, j < F.top →
    AnalyticOnBonds (fun p => chartField R (C p) j) p₀ (sitesOfCells S j : Set (F.Site j)) := by
  intro j
  induction j with
  | zero =>
    intro _ x i hx hx'
    have hb := mem_innerBonds hx hx'
    simp only [chartField]
    exact analyticAt_mul_unit (analyticAt_expUnit (hu _ hb)) analyticAt_const
  | succ j ih =>
    intro hj x i hx hx'
    have hb := mem_innerBonds hx hx'
    have hj' : j < F.top := by omega
    have hfr := analyticAt_gaugedContourAverage hodd hj' (R j) (ih hj') hb ((hreg j hj').1 _ hx)
      ((hreg j hj').1 _ hx')
    simp only [chartField]
    exact analyticAt_mul_unit (analyticAt_mul_unit (analyticAt_expUnit (hmu j hj _ hb)) analyticAt_const)
      (analyticAt_polarUnit hfr ((hreg j hj').2 _ hb))
private theorem analyticAt_wilsonAction {X : P → F.GaugeField 0}
    (h : AnalyticOnBonds X p₀ (sitesOfCells S 0 : Set (F.Site 0))) :
    AnalyticAt ℝ (fun p => wilsonAction S (X p)) p₀ := by
  unfold wilsonAction
  refine Finset.analyticAt_fun_sum _ fun q hq => ?_
  refine analyticAt_const.sub (analyticAt_re ?_)
  have := analyticAt_pathHolonomy h q.1 _ 0 (allAlong_plaquette hq)
  rw [add_siteOfCoords_zero] at this
  exact this
private theorem analyticAt_gaugedBondAverage (hodd : Odd F.blockSide) (R : F.FieldChain) {C : P → ChainChart F}
    (hu : ∀ b ∈ innerBonds S 0, AnalyticAt ℝ (fun p => (C p).fine b.1 b.2) p₀)
    (hmu : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
      AnalyticAt ℝ (fun p => (C p).coarse j b.1 b.2) p₀)
    (hreg : ChartIsRegular S R (C p₀)) {k : ℕ} (hk : k < F.top) {c : F.Site (k + 1) × Fin 4}
    (hc : c ∈ innerBonds S (k + 1)) :
    AnalyticAt ℝ (fun p => gaugedBondAverage R (C p) k c) p₀ := by
  have hf := analyticOnBonds_chartField hodd R hu hmu hreg
  exact analyticAt_gaugedContourAverage hodd hk (R k) (hf k hk) hc ((hreg k hk).1 _ (innerBonds_ends hc).1)
    ((hreg k hk).1 _ (innerBonds_ends hc).2)
private theorem analyticAt_chartAction (hodd : Odd F.blockSide) (a : ℝ) (R : F.FieldChain)
    (W : F.GaugeField F.top) {C : P → ChainChart F}
    (hu : ∀ b ∈ innerBonds S 0, AnalyticAt ℝ (fun p => (C p).fine b.1 b.2) p₀)
    (hmu : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
      AnalyticAt ℝ (fun p => (C p).coarse j b.1 b.2) p₀)
    (hreg : ChartIsRegular S R (C p₀)) :
    AnalyticAt ℝ (fun p => chartAction a S R (C p) W) p₀ := by
  have hf := analyticOnBonds_chartField hodd R hu hmu hreg
  unfold chartAction gaugedChainAction
  have h0 : 0 < F.top := Nat.succ_pos _
  simp only [chartChain_of_lt R _ W h0]
  refine (analyticAt_wilsonAction (hf 0 h0)).add (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun k hk =>
    Finset.analyticAt_fun_sum _ fun c hc => ?_))
  have hjn : k < F.top := Finset.mem_range.1 hk
  simp only [chartChain_of_lt R _ W hjn]
  unfold gaugedBlockFit chartGauge
  have hfr := analyticAt_gaugedContourAverage hodd hjn (R k) (hf k hjn) hc
    ((hreg k hjn).1 _ (innerBonds_ends hc).1) ((hreg k hjn).1 _ (innerBonds_ends hc).2)
  refine (analyticAt_norm hfr ((hreg k hjn).2 _ hc)).sub (analyticAt_re (hfr.mul ?_))
  by_cases htop : k + 1 < F.top
  · simp only [chartChain_of_lt R _ W htop]
    exact analyticAt_inv_unit (hf (k + 1) htop _ _ (innerBonds_ends hc).1 (innerBonds_ends hc).2)
  · obtain rfl : k = F.depth := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    simp only [chartChain_top R _ W]
    exact analyticAt_const
end Analytic
section Split
private theorem gaugedBlockFit_top (R : F.FieldChain) (U : ChainChart F) (W : F.GaugeField F.top)
    (c : F.Site F.top × Fin 4) :
    gaugedBlockFit (chartChain R U W F.depth) (chartGauge R U (F.depth + 1)) (chartChain R U W (F.depth + 1)) c =
      ‖gaugedBondAverage R U F.depth c‖ -
        (gaugedBondAverage R U F.depth c * (((W c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by
  have h1 : chartChain R U W F.depth = chartField R U F.depth := chartChain_of_lt R U W (Nat.lt_succ_self _)
  have h2 : chartChain R U W (F.depth + 1) = W := chartChain_top R U W
  rw [h1, h2]
  rfl
private theorem chartAction_top_change (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (V V' : F.GaugeField F.top) :
    chartAction a S R U V' = chartAction a S R U V +
      a * ∑ c ∈ innerBonds S F.top,
        ((gaugedBondAverage R U F.depth c * (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re -
        (gaugedBondAverage R U F.depth c * (((V' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) := by
  have hn : F.top = F.depth + 1 := rfl
  have hlow : ∀ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
      gaugedBlockFit (chartChain R U V' j) (chartGauge R U (j + 1)) (chartChain R U V' (j + 1)) c =
      ∑ c ∈ innerBonds S (j + 1),
        gaugedBlockFit (chartChain R U V j) (chartGauge R U (j + 1)) (chartChain R U V (j + 1)) c := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [chartChain_of_lt R U V' (show j < F.top by omega), chartChain_of_lt R U V' (show j + 1 < F.top by omega),
      chartChain_of_lt R U V (show j < F.top by omega), chartChain_of_lt R U V (show j + 1 < F.top by omega)]
  have h0 : chartChain R U V' 0 = chartChain R U V 0 := by
    rw [chartChain_of_lt R U V' (Nat.succ_pos _), chartChain_of_lt R U V (Nat.succ_pos _)]
  have key : ∀ f : ℕ → ℝ, ∑ j ∈ Finset.range F.top, f j = ∑ j ∈ Finset.range F.depth, f j + f F.depth :=
    fun f => Finset.sum_range_succ f F.depth
  unfold chartAction gaugedChainAction
  rw [key, key, h0, Finset.sum_congr rfl hlow]
  simp only [gaugedBlockFit_top]
  have e : ∑ c ∈ innerBonds S (F.depth + 1), (‖gaugedBondAverage R U F.depth c‖ -
        (gaugedBondAverage R U F.depth c * (((V' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) =
      ∑ c ∈ innerBonds S (F.depth + 1), (‖gaugedBondAverage R U F.depth c‖ -
        (gaugedBondAverage R U F.depth c * (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) +
      ∑ c ∈ innerBonds S F.top,
        ((gaugedBondAverage R U F.depth c * (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re -
        (gaugedBondAverage R U F.depth c * (((V' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [e]
  ring
private def rotationIncrement (g : UnitQuaternion) (v : imaginaryQuaternions) (τ : ℝ) : ℍ[ℝ] :=
  ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (1 - NormedSpace.exp (τ • (-(v : ℍ[ℝ]))))
private theorem star_imaginary (v : imaginaryQuaternions) : star (v : ℍ[ℝ]) = -(v : ℍ[ℝ]) := by apply _root_.YangMills.Construction.GaugeMotions.star_coe_imaginary <;> assumption
private theorem coe_inv_expUnit_mul (τ : ℝ) (v : imaginaryQuaternions) (g : UnitQuaternion) :
    (((expUnit (τ • v) * g)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * NormedSpace.exp (τ • (-(v : ℍ[ℝ]))) := by
  rw [mul_inv_rev, Submonoid.coe_mul, coe_unitQuaternion_inv (expUnit (τ • v))]
  congr 1
  have e : ((expUnit (τ • v) : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (τ • (v : ℍ[ℝ])) := rfl
  rw [e, NormedSpace.star_exp, quaternion_star_real_smul, star_imaginary]
private theorem re_mul_inv_sub_rotated (q : ℍ[ℝ]) (g : UnitQuaternion) (v : imaginaryQuaternions) (τ : ℝ) :
    (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re - (q * (((expUnit (τ • v) * g)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
      (q * rotationIncrement g v τ).re := by
  have hs : ∀ x y : ℍ[ℝ], (x - y).re = x.re - y.re := fun _ _ => rfl
  rw [coe_inv_expUnit_mul, rotationIncrement, mul_sub, mul_sub, mul_one, hs]
private theorem chartAction_rotatedField (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (V : F.GaugeField F.top) (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (τ : ℝ) :
    chartAction a S R U (rotatedField (fun y i => τ • v y i) V) = chartAction a S R U V +
      a * ∑ c ∈ innerBonds S F.top,
        (gaugedBondAverage R U F.depth c * rotationIncrement (V c.1 c.2) (v c.1 c.2) τ).re := by
  rw [chartAction_top_change a S R U V]
  congr 2
  exact Finset.sum_congr rfl fun c _ => re_mul_inv_sub_rotated _ _ _ _
private theorem analyticAt_rotationIncrement (g : UnitQuaternion) (v : imaginaryQuaternions) (τ : ℝ) :
    AnalyticAt ℝ (rotationIncrement g v) τ := by
  unfold rotationIncrement
  refine analyticAt_const.mul (analyticAt_const.sub ?_)
  have h : AnalyticAt ℝ (fun τ : ℝ => τ • (-(v : ℍ[ℝ]))) τ := analyticAt_id.smul analyticAt_const
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) _).comp h
private theorem rotationIncrement_zero (g : UnitQuaternion) (v : imaginaryQuaternions) :
    rotationIncrement g v 0 = 0 := by
  simp [rotationIncrement]
private theorem hasDerivAt_rotationIncrement (g : UnitQuaternion) (v : imaginaryQuaternions) (τ : ℝ) :
    HasDerivAt (rotationIncrement g v)
      (((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * -(NormedSpace.exp (τ • (-(v : ℍ[ℝ]))) * (-(v : ℍ[ℝ])))) τ := by
  unfold rotationIncrement
  exact ((hasDerivAt_exp_smul_const (𝕂 := ℝ) (-(v : ℍ[ℝ])) τ).const_sub 1).const_mul _
private theorem deriv_rotationIncrement_zero (g : UnitQuaternion) (v : imaginaryQuaternions) :
    deriv (rotationIncrement g v) 0 = ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v : ℍ[ℝ]) := by
  rw [(hasDerivAt_rotationIncrement g v 0).deriv]
  simp
private theorem imaginary_mul_self (v : imaginaryQuaternions) :
    (v : ℍ[ℝ]) * (v : ℍ[ℝ]) = -((‖v‖ ^ 2 : ℝ) : ℍ[ℝ]) := by
  have h : star (v : ℍ[ℝ]) * (v : ℍ[ℝ]) = ((‖(v : ℍ[ℝ])‖ ^ 2 : ℝ) : ℍ[ℝ]) := by
    rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, sq]
  rw [star_imaginary, neg_mul] at h
  have e : ‖v‖ = ‖(v : ℍ[ℝ])‖ := rfl
  rw [e, ← h, neg_neg]
private theorem deriv_deriv_rotationIncrement_zero (g : UnitQuaternion) (v : imaginaryQuaternions) :
    deriv (deriv (rotationIncrement g v)) 0 = (‖v‖ ^ 2) • ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  have e : deriv (rotationIncrement g v) = fun τ : ℝ => ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
      -(NormedSpace.exp (τ • (-(v : ℍ[ℝ]))) * (-(v : ℍ[ℝ]))) := by
    funext τ
    exact (hasDerivAt_rotationIncrement g v τ).deriv
  rw [e]
  have h := ((((hasDerivAt_exp_smul_const (𝕂 := ℝ) (-(v : ℍ[ℝ])) (0 : ℝ)).mul_const (-(v : ℍ[ℝ]))).neg).const_mul
    ((((g⁻¹ : UnitQuaternion) : ℍ[ℝ]))))
  have h2 := h.deriv
  refine h2.trans ?_
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_neg]
  rw [neg_neg, neg_mul, imaginary_mul_self, neg_neg, Quaternion.mul_coe_eq_smul]
end Split
section Calculus
private theorem hasDerivAt_re {q : ℝ → ℍ[ℝ]} {q' : ℍ[ℝ]} {τ : ℝ} (h : HasDerivAt q q' τ) :
    HasDerivAt (fun x => (q x).re) q'.re τ := by
  simpa only [Function.comp_def, reCL_apply] using reCL.hasFDerivAt.comp_hasDerivAt τ h
private theorem secondDeriv_add {f g : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) :
    deriv (deriv fun τ => f τ + g τ) 0 = deriv (deriv f) 0 + deriv (deriv g) 0 := by
  have e : deriv (fun τ => f τ + g τ) =ᶠ[𝓝 0] fun τ => deriv f τ + deriv g τ := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with τ h1 h2
    exact (h1.differentiableAt.hasDerivAt.add h2.differentiableAt.hasDerivAt).deriv
  rw [e.deriv_eq]
  exact (hf.deriv.differentiableAt.hasDerivAt.add hg.deriv.differentiableAt.hasDerivAt).deriv
abbrev _root_.YangMills.DeltaSharedProofs.p500418 := @secondDeriv_add
abbrev _root_.YangMills.SharedProofs.p79864 := @secondDeriv_add
private theorem secondDeriv_const_mul {f : ℝ → ℝ} (a : ℝ) (hf : AnalyticAt ℝ f 0) :
    deriv (deriv fun τ => a * f τ) 0 = a * deriv (deriv f) 0 := by
  have e : deriv (fun τ => a * f τ) =ᶠ[𝓝 0] fun τ => a * deriv f τ := by
    filter_upwards [hf.eventually_analyticAt] with τ h1
    exact (h1.differentiableAt.hasDerivAt.const_mul a).deriv
  rw [e.deriv_eq]
  exact (hf.deriv.differentiableAt.hasDerivAt.const_mul a).deriv
abbrev _root_.YangMills.DeltaSharedProofs.p501758 := @secondDeriv_const_mul
private theorem secondDeriv_sum {ι : Type} (B : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ c ∈ B, AnalyticAt ℝ (f c) 0) :
    deriv (deriv fun τ => ∑ c ∈ B, f c τ) 0 = ∑ c ∈ B, deriv (deriv (f c)) 0 := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert c B hc ih =>
    simp only [Finset.sum_insert hc]
    rw [secondDeriv_add (hf c (Finset.mem_insert_self _ _))
      (Finset.analyticAt_fun_sum _ fun x hx => hf x (Finset.mem_insert_of_mem hx)),
      ih fun x hx => hf x (Finset.mem_insert_of_mem hx)]
abbrev _root_.YangMills.DeltaSharedProofs.p500899 := @secondDeriv_sum
private theorem secondDeriv_re_mul {p h : ℝ → ℍ[ℝ]} (hp : AnalyticAt ℝ p 0) (hh : AnalyticAt ℝ h 0)
    (h0 : h 0 = 0) :
    deriv (deriv fun τ => (p τ * h τ).re) 0 =
      2 * (deriv p 0 * deriv h 0).re + (p 0 * deriv (deriv h) 0).re := by
  have e : deriv (fun τ => (p τ * h τ).re) =ᶠ[𝓝 0] fun τ => (deriv p τ * h τ + p τ * deriv h τ).re := by
    filter_upwards [hp.eventually_analyticAt, hh.eventually_analyticAt] with τ h1 h2
    exact (hasDerivAt_re (h1.differentiableAt.hasDerivAt.mul h2.differentiableAt.hasDerivAt)).deriv
  rw [e.deriv_eq]
  have hA := hp.deriv.differentiableAt.hasDerivAt.mul hh.differentiableAt.hasDerivAt
  have hB := hp.differentiableAt.hasDerivAt.mul hh.deriv.differentiableAt.hasDerivAt
  have hC := (hasDerivAt_re (hA.add hB)).deriv
  refine hC.trans ?_
  have hs : ∀ x y : ℍ[ℝ], (x + y).re = x.re + y.re := fun _ _ => rfl
  rw [h0, mul_zero, zero_add, hs, hs]
  ring
private theorem norm_contourAverage_le_one {j : ℕ} (hodd : Odd F.blockSide) (X : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) :
    ‖contourAverage X c‖ ≤ 1 := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.norm_contourAverage_le_one <;> assumption
private theorem norm_gaugedBondAverage_le_one (hodd : Odd F.blockSide) (R : F.FieldChain) (U : ChainChart F)
    (c : F.Site F.top × Fin 4) :
    ‖gaugedBondAverage R U F.depth c‖ ≤ 1 := by
  unfold gaugedBondAverage gaugedContourAverage
  rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
  exact norm_contourAverage_le_one hodd _ c
private theorem abs_re_mul_imaginary_le {q : ℍ[ℝ]} (hq : ‖q‖ ≤ 1) (g : UnitQuaternion)
    (v : imaginaryQuaternions) :
    |(q * (((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v : ℍ[ℝ]))).re| ≤ normSubOne (g * (polarUnit q)⁻¹) * ‖v‖ := by
  by_cases h0 : q = 0
  · subst h0
    simp only [zero_mul]
    have : 0 ≤ normSubOne (g * (polarUnit 0)⁻¹) * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    simpa using this
  set u := polarUnit q with hu
  set d : UnitQuaternion := g * u⁻¹ with hd
  have hqe : q = ‖q‖ • (u : ℍ[ℝ]) := by
    rw [hu, coe_polarUnit h0, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]
  have hdinv : (u : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = ((d⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    rw [hd, mul_inv_rev, inv_inv, Submonoid.coe_mul]
  have e1 : q * (((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v : ℍ[ℝ])) =
      ‖q‖ • (((d⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v : ℍ[ℝ])) := by
    conv_lhs => rw [hqe]
    rw [smul_mul_assoc, ← mul_assoc, hdinv]
  have hv : (v : ℍ[ℝ]).re = 0 := v.2
  have e2 : (((d⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v : ℍ[ℝ])).re =
      ((((d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) * (v : ℍ[ℝ])).re := by
    have hs : ∀ x y : ℍ[ℝ], (x - y).re = x.re - y.re := fun _ _ => rfl
    rw [sub_mul, one_mul, hs, hv, sub_zero]
  have e3 : ‖((d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = normSubOne d := by
    have : ((d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 = ((d⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (1 - (d : ℍ[ℝ])) := by
      rw [mul_sub, mul_one, ← Submonoid.coe_mul, inv_mul_cancel]
      simp
    rw [this, norm_mul, norm_coe_unitQuaternion, one_mul, norm_sub_rev]
    rfl
  have hsmul : ∀ (r : ℝ) (x : ℍ[ℝ]), (r • x).re = r * x.re := fun _ _ => rfl
  rw [e1, hsmul, abs_mul, abs_of_nonneg (norm_nonneg q), e2]
  have h4 := abs_re_le_norm ((((d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) * (v : ℍ[ℝ]))
  rw [norm_mul, e3] at h4
  have hv' : ‖(v : ℍ[ℝ])‖ = ‖v‖ := rfl
  rw [hv'] at h4
  calc _ ≤ 1 * |((((d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) * (v : ℍ[ℝ])).re| :=
        mul_le_mul_of_nonneg_right hq (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h4
private theorem chartBondMisfit_top (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top)
    (c : F.Site F.top × Fin 4) :
    chartBondMisfit R U V F.depth c = V c.1 c.2 * (polarUnit (gaugedBondAverage R U F.depth c))⁻¹ := by
  have h1 : chartChain R U V F.depth = chartField R U F.depth := chartChain_of_lt R U V (Nat.lt_succ_self _)
  have h2 : chartChain R U V (F.depth + 1) = V := chartChain_top R U V
  unfold chartBondMisfit
  rw [h1, h2]
  rfl
private theorem chartShift_zero (U A : ChainChart F) : chartMove U A 0 = U := by apply _root_.YangMills.Construction.MisfitVariation.chartMove_zero <;> assumption
private theorem bondsOver_self (hodd : Odd F.blockSide) (S : Finset F.Cell) (j : ℕ) :
    bondsOver S S j = innerBonds S j := by
  unfold bondsOver
  exact Finset.filter_true_of_mem fun b hb => BlockLines.enclosingCell_mem hodd (innerBonds_ends hb).1
abbrev _root_.YangMills.SharedProofs.p14425 := @bondsOver_self
private theorem second_variation_bond_identity (d l p : ℍ[ℝ]) (v : imaginaryQuaternions) (g : ℍ[ℝ])
    (hd : d = p * g - l) (q : ℍ[ℝ]) :
    2 * (p * (g * (v : ℍ[ℝ]))).re + (q * ((‖v‖ ^ 2) • g)).re - (‖l - (v : ℍ[ℝ])‖ ^ 2 - ‖l‖ ^ 2) =
      2 * (d * (v : ℍ[ℝ])).re + ‖v‖ ^ 2 * ((q * g - 1).re) := by
  subst hd
  have hre : (v : ℍ[ℝ]).re = 0 := v.2
  have hl : ∀ x : ℍ[ℝ], ‖x‖ ^ 2 = x.re ^ 2 + x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 := by
    intro x
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  have hn : ‖v‖ ^ 2 = ‖(v : ℍ[ℝ])‖ ^ 2 := rfl
  have hlv : ‖l - (v : ℍ[ℝ])‖ ^ 2 - ‖l‖ ^ 2 = ‖v‖ ^ 2 + 2 * (l * (v : ℍ[ℝ])).re := by
    rw [hn, hl, hl, hl]
    simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.re_mul, hre]
    ring
  have e1 : p * (g * (v : ℍ[ℝ])) = (p * g - l) * (v : ℍ[ℝ]) + l * (v : ℍ[ℝ]) := by
    rw [sub_mul, mul_assoc]
    abel
  have e2 : (q * ((‖v‖ ^ 2) • g)).re = ‖v‖ ^ 2 * (q * g).re := by
    rw [mul_smul_comm]
    rfl
  rw [hlv, e1, e2, Quaternion.re_add, Quaternion.re_sub, Quaternion.re_one]
  ring
end Calculus
theorem rotatedTopActionStatement_holds (hT : actionTaylorBoundStatement) (hV : topMeanVelocityStatement)
    (hR : smallChartIsRegularStatement) : rotatedTopActionStatement := by
  intro a del ha hdel hdel8
  obtain ⟨Ca, L₁, hCa, hT'⟩ := hT a 0 del ha le_rfl (by norm_num) hdel hdel8
  obtain ⟨L₂, hV'⟩ := hV del hdel hdel8
  obtain ⟨L₃, hR'⟩ := hR
  refine ⟨max L₁ (max L₂ L₃), fun L hodd hL => ?_⟩
  have l1 : L₁ ≤ L := (le_max_left _ _).trans hL
  have l2 : L₂ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have l3 : L₃ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  obtain ⟨c₁, C₁, hc₁, hC₁, h1⟩ := hT' L hodd l1
  obtain ⟨c₂, C₂, hc₂, hC₂, h2⟩ := hV' L hodd l2
  obtain ⟨c₃, hc₃, h3⟩ := hR' L hodd l3 del hdel hdel8
  refine ⟨min c₁ (min c₂ c₃), C₁ + 2 * a * C₂, lt_min hc₁ (lt_min hc₂ hc₃), by positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold v _
  have sc₁ : ∀ x, x ≤ min c₁ (min c₂ c₃) → x ≤ c₁ := fun x h => h.trans (min_le_left _ _)
  have sc₂ : ∀ x, x ≤ min c₁ (min c₂ c₃) → x ≤ c₂ := fun x h =>
    h.trans ((min_le_right _ _).trans (min_le_left _ _))
  have sc₃ : ∀ x, x ≤ min c₁ (min c₂ c₃) → x ≤ c₃ := fun x h =>
    h.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have hTB := h1 F m S hFL hamb hm hreg s V hs (sc₁ _ hsc) hcold
  have hVB := h2 F m S hFL hamb hm hreg s V hs (sc₂ _ hsc) hcold
  have hRB := h3 F m S hFL hamb hm hreg s V hs (sc₃ _ hsc) hcold
  set R := referenceFieldChain S V with hRd
  refine ⟨?_, ?_⟩
  · intro E _ _ e₀ Q hQ hu hmu
    have hr := (hRB (Q e₀) (sc₃ _ hQ)).1
    have hu' : ∀ b ∈ innerBonds S 0, AnalyticAt ℝ (fun p : E × ℝ => (Q p.1).fine b.1 b.2) (e₀, 0) :=
      fun b hb => AnalyticAt.comp (g := fun e => (Q e).fine b.1 b.2) (f := Prod.fst) (hu b hb) analyticAt_fst
    have hmu' : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
        AnalyticAt ℝ (fun p : E × ℝ => (Q p.1).coarse j b.1 b.2) (e₀, 0) := fun j hj b hb =>
      AnalyticAt.comp (g := fun e => (Q e).coarse j b.1 b.2) (f := Prod.fst) (hmu j hj b hb) analyticAt_fst
    have e : (fun x : E × ℝ => chartAction a S R (Q x.1) (rotatedField (fun y i => x.2 • v y i) V)) =
        fun x => chartAction a S R (Q x.1) V + a * ∑ c ∈ innerBonds S F.top,
          (gaugedBondAverage R (Q x.1) F.depth c * rotationIncrement (V c.1 c.2) (v c.1 c.2) x.2).re := by
      funext x
      exact chartAction_rotatedField a S R _ V v x.2
    rw [e]
    refine (analyticAt_chartAction hoddF a R V hu' hmu' hr).add (analyticAt_const.mul
      (Finset.analyticAt_fun_sum _ fun c hc =>
        analyticAt_re ((analyticAt_gaugedBondAverage hoddF R hu' hmu' hr (Nat.lt_succ_self _) hc).mul ?_)))
    exact AnalyticAt.comp (g := rotationIncrement (V c.1 c.2) (v c.1 c.2)) (f := Prod.snd)
      (analyticAt_rotationIncrement _ _ _) analyticAt_snd
  · intro U hU
    have hr := (hRB U (sc₃ _ hU)).1
    obtain ⟨hnear, hvel⟩ := hVB U (sc₂ _ hU)
    refine ⟨fun A => ?_, ?_⟩
    · have hu0 : 0 ≤ supWeightedNorm S del R U := Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
      set u := supWeightedNorm S del R U with hud
      set N := weightedNorm S R A (oneSiteWeights F) with hN
      set T := C₂ * (s + u) with hTd
      have hTpos : 0 < T := by positivity
      have hu' : ∀ b ∈ innerBonds S 0, AnalyticAt ℝ (fun τ : ℝ => (chartMove U A τ).fine b.1 b.2) 0 :=
        fun b _ => analyticAt_const.add (analyticAt_id.smul analyticAt_const)
      have hmu' : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1),
          AnalyticAt ℝ (fun τ : ℝ => (chartMove U A τ).coarse j b.1 b.2) 0 := fun j _ b _ =>
        analyticAt_const.add (analyticAt_id.smul analyticAt_const)
      have hr0 : ChartIsRegular S R (chartMove U A 0) := by
        rw [chartShift_zero]
        exact hr
      have hG := analyticAt_chartAction hoddF a R V hu' hmu' hr0
      have hp : ∀ c ∈ innerBonds S F.top,
          AnalyticAt ℝ (fun τ : ℝ => gaugedBondAverage R (chartMove U A τ) F.depth c) 0 := fun c hc =>
        analyticAt_gaugedBondAverage hoddF R hu' hmu' hr0 (Nat.lt_succ_self _) hc
      have hga : ∀ c ∈ innerBonds S F.top, AnalyticAt ℝ
          (fun τ : ℝ => (gaugedBondAverage R (chartMove U A τ) F.depth c *
            rotationIncrement (V c.1 c.2) (v c.1 c.2) τ).re) 0 := fun c hc =>
        analyticAt_re ((hp c hc).mul (analyticAt_rotationIncrement _ _ _))
      have hsum := Finset.analyticAt_fun_sum (innerBonds S F.top) hga
      have e : (fun τ : ℝ => chartAction a S R (chartMove U A τ) (rotatedField (fun y i => τ • v y i) V)) =
          fun τ => chartAction a S R (chartMove U A τ) V + a * ∑ c ∈ innerBonds S F.top,
            (gaugedBondAverage R (chartMove U A τ) F.depth c * rotationIncrement (V c.1 c.2) (v c.1 c.2) τ).re := by
        funext τ
        exact chartAction_rotatedField a S R _ V v τ
      have hterm : ∀ c ∈ innerBonds S F.top, deriv (deriv fun τ : ℝ =>
          (gaugedBondAverage R (chartMove U A τ) F.depth c * rotationIncrement (V c.1 c.2) (v c.1 c.2) τ).re) 0 =
          2 * (deriv (fun τ : ℝ => gaugedBondAverage R (chartMove U A τ) F.depth c) 0 *
            ((((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v c.1 c.2 : ℍ[ℝ]))).re +
          (gaugedBondAverage R U F.depth c *
            ((‖v c.1 c.2‖ ^ 2) • (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))).re := by
        intro c hc
        rw [secondDeriv_re_mul (hp c hc) (analyticAt_rotationIncrement _ _ 0) (rotationIncrement_zero _ _),
          deriv_rotationIncrement_zero, deriv_deriv_rotationIncrement_zero, chartShift_zero]
      have hD : deriv (deriv fun τ : ℝ =>
            chartAction a S R (chartMove U A τ) (rotatedField (fun y i => τ • v y i) V)) 0 =
          deriv (deriv fun τ : ℝ => chartAction a S R (chartMove U A τ) V) 0 + a * ∑ c ∈ innerBonds S F.top,
            (2 * (deriv (fun τ : ℝ => gaugedBondAverage R (chartMove U A τ) F.depth c) 0 *
              ((((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v c.1 c.2 : ℍ[ℝ]))).re +
            (gaugedBondAverage R U F.depth c *
              ((‖v c.1 c.2‖ ^ 2) • (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))).re) := by
        have hcs : AnalyticAt ℝ (fun τ : ℝ => a * ∑ c ∈ innerBonds S F.top,
            (gaugedBondAverage R (chartMove U A τ) F.depth c *
              rotationIncrement (V c.1 c.2) (v c.1 c.2) τ).re) 0 :=
          analyticAt_const.mul hsum
        rw [e, secondDeriv_add hG hcs, secondDeriv_const_mul a hsum, secondDeriv_sum _ _ hga,
          Finset.sum_congr rfl hterm]
      have hsec := hTB.second_deriv_le U A (sc₁ _ hU)
      have hform : rotatedTopQuadraticForm a S R A v =
          quadraticFormNormSq a S R A (oneSiteWeights F) + a * ∑ c ∈ innerBonds S F.top,
          (‖linearPart R A F.top c.1 c.2 - (v c.1 c.2 : ℍ[ℝ])‖ ^ 2 - ‖linearPart R A F.top c.1 c.2‖ ^ 2) := by
        unfold rotatedTopQuadraticForm quadraticFormNormSq
        simp only [oneSiteWeights, one_mul]
        rw [bondsOver_self hoddF S F.top, Finset.sum_sub_distrib]
        ring
      set dd : F.Site F.top × Fin 4 → ℍ[ℝ] := fun c =>
        deriv (fun τ : ℝ => gaugedBondAverage R (chartMove U A τ) F.depth c) 0 *
          (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - linearPart R A F.top c.1 c.2 with hdd
      have hE : ∀ c ∈ innerBonds S F.top,
          |2 * (deriv (fun τ : ℝ => gaugedBondAverage R (chartMove U A τ) F.depth c) 0 *
              ((((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v c.1 c.2 : ℍ[ℝ]))).re +
            (gaugedBondAverage R U F.depth c *
              ((‖v c.1 c.2‖ ^ 2) • (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))).re -
            (‖linearPart R A F.top c.1 c.2 - (v c.1 c.2 : ℍ[ℝ])‖ ^ 2 - ‖linearPart R A F.top c.1 c.2‖ ^ 2)| ≤
          ‖dd c‖ ^ 2 / T + 2 * T * ‖v c.1 c.2‖ ^ 2 := by
        intro c hc
        rw [second_variation_bond_identity (dd c) _ _ (v c.1 c.2) _ rfl]
        have h₁ := abs_re_le_norm (dd c * (v c.1 c.2 : ℍ[ℝ]))
        rw [norm_mul] at h₁
        have hvn : ‖(v c.1 c.2 : ℍ[ℝ])‖ = ‖v c.1 c.2‖ := rfl
        rw [hvn] at h₁
        have h₂ := (abs_re_le_norm (gaugedBondAverage R U F.depth c *
          (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1)).trans (hnear c hc)
        have h₃ : 2 * (‖dd c‖ * ‖v c.1 c.2‖) ≤ ‖dd c‖ ^ 2 / T + T * ‖v c.1 c.2‖ ^ 2 := by
          have : 0 ≤ (‖dd c‖ / T - ‖v c.1 c.2‖) ^ 2 * T := by positivity
          have e' : (‖dd c‖ / T - ‖v c.1 c.2‖) ^ 2 * T =
              ‖dd c‖ ^ 2 / T + T * ‖v c.1 c.2‖ ^ 2 - 2 * (‖dd c‖ * ‖v c.1 c.2‖) := by
            field_simp
            ring
          linarith
        have h₄ : |‖v c.1 c.2‖ ^ 2 * (gaugedBondAverage R U F.depth c *
              (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1).re| ≤ ‖v c.1 c.2‖ ^ 2 * T := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left h₂ (by positivity)
        have h₅ : |2 * (dd c * (v c.1 c.2 : ℍ[ℝ])).re| ≤ 2 * (‖dd c‖ * ‖v c.1 c.2‖) := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          linarith
        refine (abs_add_le _ _).trans ?_
        nlinarith
      have hsumE := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hE)
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum] at hsumE
      have hdsq : (∑ c ∈ innerBonds S F.top, ‖dd c‖ ^ 2) / T ≤ T * N ^ 2 := by
        rw [div_le_iff₀ hTpos]
        have := hvel A
        calc _ ≤ T ^ 2 * N ^ 2 := this
          _ = _ := by ring
      set Sv := ∑ c ∈ innerBonds S F.top, ‖v c.1 c.2‖ ^ 2 with hSv
      have hSv0 : 0 ≤ Sv := Finset.sum_nonneg fun _ _ => by positivity
      rw [hD, hform]
      set G2 := deriv (deriv fun τ : ℝ => chartAction a S R (chartMove U A τ) V) 0 with hG2
      set Fm := quadraticFormNormSq a S R A (oneSiteWeights F) with hFm
      have hsec' : |G2 - Fm| ≤ C₁ * (s + u) * N ^ 2 := hsec
      have hgen : ∀ x y : F.Site F.top × Fin 4 → ℝ,
          G2 + a * ∑ c ∈ innerBonds S F.top, x c - (Fm + a * ∑ c ∈ innerBonds S F.top, y c) =
          (G2 - Fm) + a * ∑ c ∈ innerBonds S F.top, (x c - y c) := by
        intro x y
        rw [Finset.sum_sub_distrib]
        ring
      rw [hgen]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos ha]
      have hN0 : 0 ≤ N ^ 2 := by positivity
      have hb1 : a * |∑ c ∈ innerBonds S F.top,
            (2 * (deriv (fun τ : ℝ => gaugedBondAverage R (chartMove U A τ) F.depth c) 0 *
              ((((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v c.1 c.2 : ℍ[ℝ]))).re +
            (gaugedBondAverage R U F.depth c *
              ((‖v c.1 c.2‖ ^ 2) • (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))).re -
            (‖linearPart R A F.top c.1 c.2 - (v c.1 c.2 : ℍ[ℝ])‖ ^ 2 -
              ‖linearPart R A F.top c.1 c.2‖ ^ 2))| ≤
          a * (T * N ^ 2 + 2 * T * Sv) :=
        mul_le_mul_of_nonneg_left (hsumE.trans (by linarith)) ha.le
      have hst : 0 ≤ s + u := by positivity
      have hc1 : C₁ * (s + u) * N ^ 2 ≤ C₁ * (s + u) * (N ^ 2 + Sv) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hc2 : a * (T * N ^ 2 + 2 * T * Sv) ≤ 2 * a * C₂ * (s + u) * (N ^ 2 + Sv) := by
        have hT0 : 0 ≤ a * T * N ^ 2 := by positivity
        have e3 : 2 * a * C₂ * (s + u) * (N ^ 2 + Sv) = 2 * (a * T) * N ^ 2 + 2 * (a * T) * Sv := by
          rw [hTd]
          ring
        rw [e3]
        nlinarith
      have e4 : (C₁ + 2 * a * C₂) * (s + u) * (N ^ 2 + Sv) =
          C₁ * (s + u) * (N ^ 2 + Sv) + 2 * a * C₂ * (s + u) * (N ^ 2 + Sv) := by ring
      rw [e4]
      linarith
    · have e : (fun τ : ℝ => chartAction a S R U (rotatedField (fun y i => τ • v y i) V)) =
          fun τ => chartAction a S R U V + a * ∑ c ∈ innerBonds S F.top,
            (gaugedBondAverage R U F.depth c * rotationIncrement (V c.1 c.2) (v c.1 c.2) τ).re := by
        funext τ
        exact chartAction_rotatedField a S R _ V v τ
      have hd : HasDerivAt (fun τ : ℝ => chartAction a S R U V + a * ∑ c ∈ innerBonds S F.top,
            (gaugedBondAverage R U F.depth c * rotationIncrement (V c.1 c.2) (v c.1 c.2) τ).re)
          (a * ∑ c ∈ innerBonds S F.top, (gaugedBondAverage R U F.depth c *
            ((((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v c.1 c.2 : ℍ[ℝ]))).re) 0 := by
        refine HasDerivAt.const_add _ (HasDerivAt.const_mul a (HasDerivAt.fun_sum fun c _ => hasDerivAt_re ?_))
        have h := (analyticAt_rotationIncrement (V c.1 c.2) (v c.1 c.2) 0).differentiableAt.hasDerivAt
        rw [deriv_rotationIncrement_zero] at h
        exact h.const_mul _
      rw [e, hd.deriv, abs_mul, abs_of_pos ha]
      refine mul_le_mul_of_nonneg_left ?_ ha.le
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
      rw [chartBondMisfit_top]
      exact abs_re_mul_imaginary_le (norm_gaugedBondAverage_le_one hoddF R U c) _ _
end YangMills.Construction.BlockAverages.RotatedTopAction
end
