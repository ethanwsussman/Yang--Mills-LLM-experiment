import YangMills.ContinuumLimit.PlaquetteTailOnTori
import YangMills.ContinuumLimit.ColdTailAsymptotic
import YangMills.Construction.TheStatementsProvedTogether.FromTheFourPointLawOnTheWindowProof
import YangMills.Construction.LawOnABoxOfTheFlow.ToolsOfAChart
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParametersProof
noncomputable section
open MeasureTheory Filter
open YangMills.Construction
open WeightedResponses TorusLumps TorusFields ResponseInTheExpansion RenormalizationStepParameters

namespace YangMills.ReferenceCalibration

theorem eventually_range_fits_reference_torus (A D : ℝ) (hA : 1 ≤ A) (hD : 0 ≤ D) :
    ∀ᶠ q : ℝ in atTop, ∀ x : ℝ, q^92 ≤ x → x ≤ A*q^92 →
      D * (clusterRange x : ℝ) ≤ q := by
  have H := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/25)).eventually_ge_atTop
    (D * (A ^ (1/100:ℝ) + 1))
  filter_upwards [H,eventually_ge_atTop (1:ℝ)] with q hq hq1
  intro x hlo hhi
  have hx0 := (pow_nonneg (zero_le_one.trans hq1) 92).trans hlo
  have hq0 : 0 ≤ q := zero_le_one.trans hq1
  have hpow : (q ^ 92 : ℝ) ^ (1/100:ℝ) = q ^ (23/25:ℝ) := by
    rw [←Real.rpow_natCast_mul hq0]
    norm_num
  have hprod : q ^ (2/25:ℝ) * q ^ (23/25:ℝ) = q := by
    rw [← Real.rpow_add (zero_lt_one.trans_le hq1)]
    norm_num
  have hb := Real.rpow_le_rpow hx0 hhi (by norm_num : (0:ℝ)≤1/100)
  rw [Real.mul_rpow (zero_le_one.trans hA) (pow_nonneg hq0 92),hpow] at hb
  have ht := Real.one_le_rpow hq1 (show (0:ℝ)≤23/25 by norm_num)
  calc D * (clusterRange x : ℝ) ≤ D * (x^(1/100:ℝ)+1) :=
        mul_le_mul_of_nonneg_left (StepFloors.clusterRange_le_rpow_add_one hx0) hD
    _ ≤ D*(A^(1/100:ℝ)+1)*q^(23/25:ℝ) := by
        rw [mul_assoc,add_mul,one_mul]; gcongr
    _ ≤ q^(2/25:ℝ)*q^(23/25:ℝ) := mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hq0 _)
    _ = q := hprod

/-- On fixed-aspect stopping tori the marked Wilson law is cold on every
plaquette and hull-free outside a set of exponentially small probability. -/
theorem stopped_reference_torus_tail :
    WeightedResponses.HoldsAtAdmissibleParameters fun Tb y =>
      let p := Tb.stepParameters y
      ∀ (ell A : ℝ), 1 ≤ ell → 1 ≤ A →
      ∀ᶠ q : ℝ in atTop, ∀ (T : StageTower p) (β : ℝ) (k n : ℕ) [NeZero n],
        (n:ℝ) = ell*q → (∃ e : ℕ, n = 2*p.side^e) → 2*p.side ∣ n →
        IsTowerAtParameters Tb y T β k → T.MarksMeasurable →
        IsFiniteMeasure (markedSampleLaw T β k n) →
        q^92 ≤ BoxEvents.flowCoupling p β k → BoxEvents.flowCoupling p β k ≤ A*q^92 →
        (markedSampleLaw T β k n) {u | (stageState T k n u).2.1 ≠ ∅ ∨
          ∃ z i j, (q^16)⁻¹ < curvature (stageState T k n u).1 z i j}
            ≤ ENNReal.ofReal (Real.exp (-q)) := by
  apply BoxGaussian.holdsAtAdmissibleParameters_mono _ (BoxGaussian.holdsAtAdmissibleParameters_and
    FourPointWindowLaw.hull_sites_rare FourPointWindowLaw.plaquette_energy_small_tail)
  intro Tb y had data p ell A hell hA
  obtain ⟨⟨xH, hh⟩, C, t₀, xP, ht₀, hp⟩ := data
  let a := Tb.κ₁ * Tb.threshold^2 / 2^5
  have ha : 0 < a := by dsimp [a]; have := StepFloors.κ₁_pos had; have := had.σ_pos; positivity
  have htend : Tendsto (fun q : ℝ => ((q^16)⁻¹)^2/2) atTop (nhds 0) := by
    have h : Tendsto (fun q : ℝ => (q^16)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (n:=16) (by decide))
    simpa using (h.pow 2).div_const 2
  have hL : 2 ≤ p.side := by have := had.L_ge; change 2 ≤ Tb.side; omega
  filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (max xH xP),
    eventually_ge_atTop ((p.side*p.n₀:ℕ):ℝ),
    htend.eventually (gt_mem_nhds ht₀),
    eventually_range_fits_reference_torus A (2 * (p.side:ℝ) * 2^7) hA (by positivity),
    eventually_small_reference_torus_tail ha had.cK_pos ell C A hA] with q hq hx0 hn₀ htq hr ht
  intro T β k n _ hn he hd hT hm hfinite hlo hhi
  let _ := hfinite
  let x := BoxEvents.flowCoupling p β k
  let t := (q^16)⁻¹
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hx : q ≤ x := (le_self_pow₀ hq (by decide : 92 ≠ 0)).trans hlo
  have hqn : q ≤ (n:ℝ) := by rw [hn]; exact le_mul_of_one_le_left hqpos.le hell
  have hpos : 0 < x := hqpos.trans_le hx
  have hrpos : 1 ≤ clusterRange x := by
    unfold clusterRange; apply Nat.ceil_pos.mpr; exact Real.rpow_pos_of_pos hpos _
  have hc := YangMills.SharedProofs.p1293 hL hrpos
  have hcell : 2*CellWindows.baseCellSide p.side (clusterRange x) ≤ n := by
    have h := (hr x hlo hhi).trans hqn
    have hc' : (CellWindows.baseCellSide p.side (clusterRange x):ℝ) ≤ (p.side:ℝ)*(2^7*(clusterRange x:ℝ)) := by exact_mod_cast hc
    exact_mod_cast (show 2*(CellWindows.baseCellSide p.side (clusterRange x):ℝ) ≤ (n:ℝ) by linarith)
  have hbase : p.side * p.n₀ ≤ n := by exact_mod_cast hn₀.trans hqn
  have htpos : 0 < t := by dsimp [t]; positivity
  let μ := markedSampleLaw T β k n
  have hfield (u : MarkedSample p k n) : (stageState T k n u).1 = topField p k n u := by cases k <;> rfl
  have htail := bad_reference_torus_measure μ (fun u => (stageState T k n u).1)
    (fun u => (stageState T k n u).2.1) t (Real.exp (-(a*x)))
    (Real.exp (C*Real.log x-Tb.coercivity*(x/q^32))) htpos.le (Real.exp_pos _).le
  have h₁ z := hh T β k n hT hm (((le_max_left xH xP).trans hx0).trans hx) he hcell z
  have h₂ := hp T β k n hT hm (((le_max_right xH xP).trans hx0).trans hx) hd hbase
  have hres := htail (fun z => by convert h₁ z using 2 <;> dsimp [a,x] <;> ring) (by
    intro v hv
    simp only [hfield]
    have h := h₂ v hv (t^2/2) (by positivity) htq.le
    convert h using 2
    dsimp [t,x]
    field_simp
    <;> ring)
  have hreal := hres.trans (hn ▸ ht x hlo hhi)
  simpa [μ, measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using ENNReal.ofReal_le_ofReal hreal
end YangMills.ReferenceCalibration
