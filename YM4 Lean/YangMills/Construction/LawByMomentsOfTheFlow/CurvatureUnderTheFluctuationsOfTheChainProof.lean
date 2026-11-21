import YangMills.Construction.ColdStepAtMirrorFrames.AdjointOfTheGroup
import YangMills.Construction.ColdStepAtMirrorFrames.SmallUnitsAndTheirLogarithms
import YangMills.Construction.LawByMomentsOfTheFlow.CurvatureUnderTheFluctuationsOfTheChain
import YangMills.Construction.ResponseInTheExpansion.FloorsOfTheLocalChain
import YangMills.Construction.ResponseInTheExpansion.RowSumsOfTheFunctionals
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsASumOverTheLevels
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsTheDescendedForm
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.GaugeFixing YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepCosts
open Quaternion
namespace BelowFluctuationMass
private theorem expUnit_near_one (w : imaginaryQuaternions) (s : ℝ) (hs : s ≤ 1) (hw : ‖(w : ℍ[ℝ])‖ ≤ s) :
    ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * s ∧ ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1 - (w : ℍ[ℝ])‖ ≤ s ^ 2 ∧
      ‖(((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * s ∧
      ‖(((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 - -(w : ℍ[ℝ])‖ ≤ s ^ 2 := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hw
  have hsecond : ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1 - (w : ℍ[ℝ])‖ ≤ s ^ 2 :=
    (YangMills.Construction.ColdStepAtMirrorFrames.SmallUnits.norm_expUnit_sub_one_sub_le w (hw.trans hs)).trans
      (pow_le_pow_left₀ (norm_nonneg _) hw 2)
  have hfirst : ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * s := by
    have : ((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1 =
        (((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1 - (w : ℍ[ℝ])) + (w : ℍ[ℝ]) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  have hstar : star (w : ℍ[ℝ]) = -(w : ℍ[ℝ]) := by
    have hre : (w : ℍ[ℝ]).re = 0 := w.2
    ext <;> simp [hre]
  have hinv : (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star ((expUnit w : UnitQuaternion) : ℍ[ℝ]) :=
    coe_inv_unitQuaternion _
  have hinvSub : (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 = star (((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1) := by
    rw [hinv, star_sub, star_one]
  have hinvSecond : (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 - -(w : ℍ[ℝ]) =
      star (((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1 - (w : ℍ[ℝ])) := by
    rw [hinvSub]; simp only [star_sub, star_one, hstar]
  refine ⟨hfirst, hsecond, ?_, ?_⟩
  · rw [hinvSub, norm_star]; exact hfirst
  · rw [hinvSecond, norm_star]; exact hsecond
private theorem holonomy_near_one (a b c d : imaginaryQuaternions) (s : ℝ) (hs : s ≤ 1)
    (ha : ‖(a : ℍ[ℝ])‖ ≤ s) (hb : ‖(b : ℍ[ℝ])‖ ≤ s) (hc : ‖(c : ℍ[ℝ])‖ ≤ s) (hd : ‖(d : ℍ[ℝ])‖ ≤ s) :
    ‖(((expUnit a * expUnit b * (expUnit c)⁻¹ * (expUnit d)⁻¹ : UnitQuaternion)) : ℍ[ℝ]) - 1‖ ≤
      ‖(a : ℍ[ℝ]) + (b : ℍ[ℝ]) - (c : ℍ[ℝ]) - (d : ℍ[ℝ])‖ + 28 * s ^ 2 := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans ha
  obtain ⟨a1, a2, -, -⟩ := expUnit_near_one a s hs ha
  obtain ⟨b1, b2, -, -⟩ := expUnit_near_one b s hs hb
  obtain ⟨-, -, c1, c2⟩ := expUnit_near_one c s hs hc
  obtain ⟨-, -, d1, d2⟩ := expUnit_near_one d s hs hd
  have b3 : ‖((expUnit b : UnitQuaternion) : ℍ[ℝ])‖ = 1 := norm_unitQuaternion _
  have c3 : ‖(((expUnit c)⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = 1 := norm_unitQuaternion _
  simp only [Submonoid.coe_mul]
  generalize ((expUnit a : UnitQuaternion) : ℍ[ℝ]) = A at *
  generalize ((expUnit b : UnitQuaternion) : ℍ[ℝ]) = B at *
  generalize (((expUnit c)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = C at *
  generalize (((expUnit d)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = D at *
  have e : A * B * C * D - 1 = ((a : ℍ[ℝ]) + b - c - d) + ((A - 1 - a) + (B - 1 - b) + (C - 1 - -(c : ℍ[ℝ])) +
      (D - 1 - -(d : ℍ[ℝ])) + (A - 1) * (B - 1) + (A * B - 1) * (C - 1) + (A * B * C - 1) * (D - 1)) := by
    noncomm_ring
  have hAB : ‖A * B - 1‖ ≤ 4 * s := by
    have : A * B - 1 = (A - 1) * B + (B - 1) := by noncomm_ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, b3]
    linarith
  have hABC : ‖A * B * C - 1‖ ≤ 6 * s := by
    have : A * B * C - 1 = (A * B - 1) * C + (C - 1) := by noncomm_ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, c3]
    linarith
  have m1 : ‖(A - 1) * (B - 1)‖ ≤ 4 * s ^ 2 := by
    rw [norm_mul]; nlinarith [norm_nonneg (A - 1), norm_nonneg (B - 1)]
  have m2 : ‖(A * B - 1) * (C - 1)‖ ≤ 8 * s ^ 2 := by
    rw [norm_mul]; nlinarith [norm_nonneg (A * B - 1), norm_nonneg (C - 1)]
  have m3 : ‖(A * B * C - 1) * (D - 1)‖ ≤ 12 * s ^ 2 := by
    rw [norm_mul]; nlinarith [norm_nonneg (A * B * C - 1), norm_nonneg (D - 1)]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have t2 := norm_add_le ((A - 1 - a) + (B - 1 - b) + (C - 1 - -(c : ℍ[ℝ])) + (D - 1 - -(d : ℍ[ℝ])) + (A - 1) * (B - 1) +
    (A * B - 1) * (C - 1)) ((A * B * C - 1) * (D - 1))
  have t1 := norm_add_le ((A - 1 - a) + (B - 1 - b) + (C - 1 - -(c : ℍ[ℝ])) + (D - 1 - -(d : ℍ[ℝ])) + (A - 1) * (B - 1))
    ((A * B - 1) * (C - 1))
  have t0 := norm_add_le ((A - 1 - a) + (B - 1 - b) + (C - 1 - -(c : ℍ[ℝ])) + (D - 1 - -(d : ℍ[ℝ]))) ((A - 1) * (B - 1))
  have u1 := norm_add_le ((A - 1 - a) + (B - 1 - b) + (C - 1 - -(c : ℍ[ℝ]))) (D - 1 - -(d : ℍ[ℝ]))
  have u2 := norm_add_le ((A - 1 - a) + (B - 1 - b)) (C - 1 - -(c : ℍ[ℝ]))
  have u3 := norm_add_le (A - 1 - a) (B - 1 - b)
  linarith
private theorem curvature_le_lieFormCurl {m : ℕ} [NeZero m] (g : TorusSite m → UnitQuaternion) (W : TorusField m)
    (o : TorusSite m) (r s : ℝ) (hr : 1 ≤ r) (hs : s ≤ 1) (μ ν : Fin 4)
    (h : ∀ b : TorusBond m, b.1 ∈ supBall o r →
      ‖(minimalLog (ResponseInTheExpansion.gaugeTransform g W b) : Quaternion ℝ)‖ ≤ s) :
    TorusFields.curvature W o μ ν ≤ ‖((lieFormCurl (ballLog g W o r) (o, μ, ν) : imaginaryQuaternions) : ℍ[ℝ])‖ + 28 * s ^ 2 := by
  have inBall : ∀ i : Fin 4, o + TorusFields.unitStep m i ∈ supBall o r := by
    intro i
    simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
    have := supDist_add_unitStep_le o i
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at this
    exact le_trans (by exact_mod_cast this) hr
  have centreIn : o ∈ supBall o r := by
    simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and, supDist_self]
    simpa using le_trans zero_le_one hr
  have hg : ∀ b : TorusBond m, TorusFields.gaugeTransform g W b.1 b.2 =
      expUnit (minimalLog (ResponseInTheExpansion.gaugeTransform g W b)) := fun b =>
    (expUnit_minimalLog _).symm
  rw [← curvature_gaugeTransform g W o μ ν]
  have hp := holonomy_near_one (minimalLog (ResponseInTheExpansion.gaugeTransform g W (o, μ)))
    (minimalLog (ResponseInTheExpansion.gaugeTransform g W (o + TorusFields.unitStep m μ, ν)))
    (minimalLog (ResponseInTheExpansion.gaugeTransform g W (o + TorusFields.unitStep m ν, μ)))
    (minimalLog (ResponseInTheExpansion.gaugeTransform g W (o, ν))) s hs (h _ centreIn) (h _ (inBall μ)) (h _ (inBall ν))
    (h _ centreIn)
  have e1 : TorusFields.curvature (TorusFields.gaugeTransform g W) o μ ν =
      ‖(((expUnit (minimalLog (ResponseInTheExpansion.gaugeTransform g W (o, μ))) *
        expUnit (minimalLog (ResponseInTheExpansion.gaugeTransform g W (o + TorusFields.unitStep m μ, ν))) *
        (expUnit (minimalLog (ResponseInTheExpansion.gaugeTransform g W (o + TorusFields.unitStep m ν, μ))))⁻¹ *
        (expUnit (minimalLog (ResponseInTheExpansion.gaugeTransform g W (o, ν))))⁻¹ : UnitQuaternion)) : ℍ[ℝ]) - 1‖ := by
    unfold TorusFields.curvature holonomy
    rw [hg (o, μ), hg (o + TorusFields.unitStep m μ, ν), hg (o + TorusFields.unitStep m ν, μ), hg (o, ν)]
  rw [e1]
  refine hp.trans (le_of_eq ?_)
  congr 2
  simp only [lieFormCurl, ballLog, if_pos centreIn, if_pos (inBall μ), if_pos (inBall ν)]
  rfl
abbrev _root_.YangMills.SharedProofs.p99149 := @curvature_le_lieFormCurl
private theorem minimalLog_small_of_gaugeSmall {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) (k : ℕ) (nn ρ₀ s : ℝ) :
    ∀ (d n : ℕ) [NeZero n] (u : MarkedSample ℓ (k + d) n) (o : TorusSite (fineSide ℓ.side d n)) (g : TorusSite n → UnitQuaternion),
      IsGaugeSmallAlong T k nn ρ₀ s d n u o g →
      ∀ b : TorusBond (fineSide ℓ.side d n), b.1 ∈ supBall o (ballRadius ℓ.side nn ρ₀ 0) →
        ‖(minimalLog (ResponseInTheExpansion.gaugeTransform (gaugeDescent k d n u g)
          (topField ℓ k _ (sampleBelow ℓ k d n u)) b) : Quaternion ℝ)‖ ≤ s
  | 0, n, _, u, o, g, h, b, hb => h b hb
  | d + 1, n, _, u, o, g, h, b, hb => minimalLog_small_of_gaugeSmall T k nn ρ₀ s d (n * ℓ.side) u.1 o _ h.2.2 b hb
private theorem plaquette_mem_plaquettesIn {m : ℕ} [NeZero m] (o : TorusSite m) (μ ν : Fin 4) (hμν : μ < ν) (r : ℝ)
    (hr : 2 ≤ r) : (o, μ, ν) ∈ plaquettesIn (supBall o r) := by
  simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hμν, ?_⟩
  have hb : ∀ z : TorusSite m, supDist z o ≤ 2 → z ∈ supBall o r := by
    intro z hz
    simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
    exact le_trans (by exact_mod_cast hz) hr
  intro z hz
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  have e1 : ∀ i, supDist (o + TorusFields.unitStep m i) o ≤ 1 := fun i => by
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; exact supDist_add_unitStep_le o i
  rcases hz with rfl | rfl | rfl | rfl
  · apply hb; rw [supDist_self]; omega
  · exact hb _ ((e1 μ).trans (by omega))
  · exact hb _ ((e1 ν).trans (by omega))
  · apply hb
    have h1 := supDist_triangle (o + TorusFields.unitStep m μ + TorusFields.unitStep m ν) (o + TorusFields.unitStep m μ) o
    have h2 : supDist (o + TorusFields.unitStep m μ + TorusFields.unitStep m ν) (o + TorusFields.unitStep m μ) ≤ 1 := by
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; exact supDist_add_unitStep_le _ ν
    have h3 := e1 μ
    omega
section LevelSums
variable {ℓ : TorusLumps.StepParameters}
private theorem norm_levelFluctuationSum_le (T : StageTower ℓ) (k : ℕ) (nn ρ₀ ρA : ℝ) :
    ∀ (d n : ℕ) [NeZero n] (u : MarkedSample ℓ (k + d) n) (o : TorusSite (fineSide ℓ.side d n)) (g : TorusSite n → UnitQuaternion)
      (p : TorusPlaquette (fineSide ℓ.side d n)),
      ‖levelFluctuationSum T k nn ρ₀ ρA d n u o g p‖ ≤ deviationMass T k nn ρ₀ ρA d n u o p := by
  intro d
  induction d with
  | zero =>
    intro n _ u o g p
    simp [levelFluctuationSum, deviationMass]
  | succ d ih =>
    intro n _ u o g p
    classical
    show ‖levelFluctuationSum T k nn ρ₀ ρA d (n * ℓ.side) u.1 o
        (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ (topField ℓ (k + d) (n * ℓ.side) u.1) x) p +
      ∑ b : TorusBond (n * ℓ.side), adjointTransport ℓ.coupling ρA ℓ.side k d (n * ℓ.side) (curlFunctional p) b •
        deviationInGauge T (k + d) g
          (supBall (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀)) u.2.2.1
          (topField ℓ (k + d) (n * ℓ.side) u.1) b‖ ≤ deviationMass T k nn ρ₀ ρA d (n * ℓ.side) u.1 o p +
      ∑ b ∈ readBondsAtLevel ℓ nn ρ₀ d n o, |adjointTransport ℓ.coupling ρA ℓ.side k d (n * ℓ.side) (curlFunctional p) b| *
        ‖(stepDeviation T (k + d) u.2.2.1 (topField ℓ (k + d) (n * ℓ.side) u.1) b : ℍ[ℝ])‖
    refine (norm_add_le _ _).trans (add_le_add (ih _ _ _ _ _) ?_)
    refine (norm_sum_le _ _).trans ?_
    have e : ∀ b : TorusBond (n * ℓ.side), ‖adjointTransport ℓ.coupling ρA ℓ.side k d (n * ℓ.side) (curlFunctional p) b •
        deviationInGauge T (k + d) g
          (supBall (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀)) u.2.2.1
          (topField ℓ (k + d) (n * ℓ.side) u.1) b‖ =
        if b ∈ readBondsAtLevel ℓ nn ρ₀ d n o then
          |adjointTransport ℓ.coupling ρA ℓ.side k d (n * ℓ.side) (curlFunctional p) b| *
          ‖(stepDeviation T (k + d) u.2.2.1 (topField ℓ (k + d) (n * ℓ.side) u.1) b : ℍ[ℝ])‖ else 0 := by
      intro b
      by_cases hb : b ∈ readBondsAtLevel ℓ nn ρ₀ d n o
      · rw [if_pos hb, norm_smul, Real.norm_eq_abs]
        congr 1
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hb
        unfold deviationInGauge
        rw [if_pos ⟨h2, h1⟩, YangMills.Construction.ColdStepAtMirrorFrames.Adjoint.norm_adjointAction]
        rfl
      · rw [if_neg hb]
        have : ¬ (parentBlock ℓ.side b.1 ∈ supBall (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀) ∧
            b ∈ chartBonds ℓ.side n) := fun h => hb (Finset.mem_filter.mpr ⟨h.2, h.1⟩)
        unfold deviationInGauge
        rw [if_neg this, smul_zero, norm_zero]
    rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_ite_mem, Finset.univ_inter]
private theorem norm_sum_smul_le_pi {n : ℕ} [NeZero n] (a : TorusBond n → ℝ) (B : TorusBond n → imaginaryQuaternions)
    (hB : ∀ c, ‖(B c : ℍ[ℝ])‖ ≤ Real.pi) :
    ‖∑ c : TorusBond n, a c • B c‖ ≤ (∑ c, |a c|) * Real.pi := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB c) (abs_nonneg _)
private theorem norm_topLogForm_le_pi (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n] (V : TorusField n) (o : TorusSite n)
    (r s : ℝ) (b : TorusBond n) : ‖(topLogForm ℓ V o r s b : ℍ[ℝ])‖ ≤ Real.pi := by
  classical
  unfold topLogForm
  split_ifs
  · exact norm_minimalLog_le_pi _
  · simpa using Real.pi_pos.le
end LevelSums
section AtGivenParameters
variable {Tb : ParameterAssignment} {y : ℝ}
private theorem stage_anchorRadius (T : StageTower (Tb.stepParameters y)) :
    ∀ j, (T.stage j).anchorRadius = T.base.anchorRadius
  | 0 => rfl
  | j + 1 => by
    show ((T.stage j).next _ _ _ _).anchorRadius = _
    exact stage_anchorRadius T j
private theorem holds_at (hFl : localChainFloorsStatement) (hSum : curvatureLevelSumStatement)
    (hd : curvatureNearDescendedFormAt Tb y) (hr : transportedCurlFunctionalBoundsAt Tb y) :
    curvatureBelowFluctuationMassAt Tb y := by
  obtain ⟨Cd, cd, xd, hcd, hd'⟩ := hd
  obtain ⟨X₀, hX⟩ := Filter.eventually_atTop.1 (hFl 0 cd le_rfl hcd)
  have hn₀ : ∀ᶠ x : ℝ in atTop, (Tb.n₀ : ℝ) + 1 ≤ x ^ ((1 : ℝ) / 20) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).eventually_ge_atTop _
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1 hn₀
  refine ⟨2 * |Cd| + 44, max (max X₀ X₁) xd, fun T β k N _ o hloc hLN => ?_⟩
  have hfl := hloc.floor_le
  have hX₀x : X₀ ≤ flowCouplings (Tb.stepParameters y) β k := ((le_max_left _ _).trans (le_max_left _ _)).trans hfl
  have hX₁x : X₁ ≤ flowCouplings (Tb.stepParameters y) β k := ((le_max_right _ _).trans (le_max_left _ _)).trans hfl
  have F := hX _ hX₀x
  have F₁ := hX₁ _ hX₁x
  have hOn : IsLocalChainAbove Tb y T β k N 1 xd := { hloc with floor_le := (le_max_right _ _).trans hloc.floor_le }
  set x := flowCouplings (Tb.stepParameters y) β k with hxdef
  set ρ₀ := localLogScale (Tb.stepParameters y) β k with hρdef
  have hx1 : 1 ≤ x := F.one_le
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hs0 : 0 ≤ x ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hx0 _
  have hae := hd' T β k N 1 (x ^ (-(1 / 4 : ℝ))) o hOn hLN hs0 le_rfl
  filter_upwards [hae] with u hu hl hs μ ν hμν
  have hρ : (0 : ℝ) ≤ ρ₀ := by simp only [hρdef, localLogScale, logCubeScale]; positivity
  have hrad : (2 : ℝ) ≤ ballRadius (Tb.stepParameters y).side 1 ρ₀ 0 := by
    simp only [ballRadius, pow_zero, div_one]
    linarith
  have hc := hu hl hs (o, μ, ν) (plaquette_mem_plaquettesIn o μ ν hμν _ hrad)
  have hs1 : x ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hs2 : (x ^ (-(1 / 4 : ℝ))) ^ 2 = x ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have hlogs := minimalLog_small_of_gaugeSmall T k 1 ρ₀ (x ^ (-(1 / 4 : ℝ))) (localChainDepth (Tb.stepParameters y) β k)
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)
    (sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k)) (localChainDepth (Tb.stepParameters y) β k) N u)
    o _ hs
  have h1 := curvature_le_lieFormCurl _ (topField (Tb.stepParameters y) k _ (sampleBelow (Tb.stepParameters y) k
    (localChainDepth (Tb.stepParameters y) β k) _ (sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k))
    (localChainDepth (Tb.stepParameters y) β k) N u)))
    o _ _ (by linarith) hs1 μ ν hlogs
  rw [hs2] at h1 hc
  have hρAll : ∀ j, (T.stage j).anchorRadius = Tb.ρA := by
    intro j
    rw [stage_anchorRadius T j]
    have h1 := (hloc.onFamily.onFamily 0 (Nat.zero_le _)).anchorRadius_eq
    rw [← h1]
    exact (stage_anchorRadius T 0).symm
  set db := sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k)) (localChainDepth (Tb.stepParameters y) β k) N u
    with hdb
  set V := topField (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k))
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db with hV
  set o₁ := siteAbove (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k)
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) o with ho₁
  have hG := hSum (Tb.stepParameters y) T Tb.ρA hρAll k 1 (logCubeScale x) (localChainDepth (Tb.stepParameters y) β k)
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o
    (topLogForm (Tb.stepParameters y) V o₁ (ballRadius (Tb.stepParameters y).side 1 (logCubeScale x) (localChainDepth (Tb.stepParameters y) β k))
      (x ^ (-(1 / 4 : ℝ)))) (axialGaugeAt (Tb.stepParameters y) V o₁) (o, μ, ν)
  have hGe : sampledCurvature T k (localChainDepth (Tb.stepParameters y) β k) 1 x N u o (o, μ, ν) =
      levelFluctuationSum T k 1 (logCubeScale x) Tb.ρA (localChainDepth (Tb.stepParameters y) β k)
        (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o
        (axialGaugeAt (Tb.stepParameters y) V o₁) (o, μ, ν) +
      ∑ c : TorusBond (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N),
        adjointTransport (Tb.stepParameters y).coupling Tb.ρA (Tb.stepParameters y).side k (localChainDepth (Tb.stepParameters y) β k)
          (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) (curlFunctional (o, μ, ν)) c •
          topLogForm (Tb.stepParameters y) V o₁
            (ballRadius (Tb.stepParameters y).side 1 (logCubeScale x) (localChainDepth (Tb.stepParameters y) β k)) (x ^ (-(1 / 4 : ℝ))) c := hG
  have hN₀ : Tb.n₀ ≤ fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N := by
    have h2 : (2 : ℝ) ^ 10 * localBoxRadius x ≤ (N : ℝ) := hloc.side_ge
    have h3 : (Tb.n₀ : ℝ) ≤ localBoxRadius x := by
      have h4 : ((Tb.n₀ + 1 : ℕ) : ℝ) ≤ x ^ ((1 : ℝ) / 20) := by push_cast; exact F₁
      have h5 : Tb.n₀ + 1 ≤ ⌊x ^ ((1 : ℝ) / 20)⌋₊ := Nat.le_floor h4
      have h6 : ((Tb.n₀ + 1 : ℕ) : ℝ) ≤ (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) := by exact_mod_cast h5
      have h7 : localBoxRadius x = (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) := rfl
      rw [h7]
      push_cast at h6
      linarith
    have h8 : (0 : ℝ) ≤ localBoxRadius x := Nat.cast_nonneg _
    have h9 : (Tb.n₀ : ℝ) ≤ N := by nlinarith
    have h10 : Tb.n₀ ≤ N := by exact_mod_cast h9
    rw [fineSide_eq]
    exact h10.trans (Nat.le_mul_of_pos_right _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _))
  have hrow := (hr.1 k (localChainDepth (Tb.stepParameters y) β k)
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) hN₀ (o, μ, ν) (by
    simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hμν, fun _ _ => trivial⟩)).2
  have hfl' := norm_levelFluctuationSum_le T k 1 ρ₀ Tb.ρA (localChainDepth (Tb.stepParameters y) β k)
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o
    (axialGaugeAt (Tb.stepParameters y) V o₁) (o, μ, ν)
  have htop := norm_sum_smul_le_pi (adjointTransport (Tb.stepParameters y).coupling Tb.ρA (Tb.stepParameters y).side k
      (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)
      (curlFunctional (o, μ, ν)))
    (topLogForm (Tb.stepParameters y) V o₁ (ballRadius (Tb.stepParameters y).side 1 (logCubeScale x) (localChainDepth (Tb.stepParameters y) β k))
      (x ^ (-(1 / 4 : ℝ)))) (fun c => norm_topLogForm_le_pi _ _ _ _ _ _)
  have hhalf : ((1 : ℝ) / 2) ^ (localChainDepth (Tb.stepParameters y) β k) ≤ x ^ (-(1 / 2 : ℝ)) := by
    have h2 : ((1 : ℝ) / 2) ^ (localChainDepth (Tb.stepParameters y) β k) ≤ x ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, one_div, inv_pow]
      exact inv_anti₀ hxpos F.le_two_pow_depth
    exact h2.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hEx : Real.exp (-(cd * ρ₀)) ≤ x ^ (-(1 / 2 : ℝ)) :=
    F.exp_le.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hX0 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0 _
  set Xh := x ^ (-(1 / 2 : ℝ)) with hXh
  set A := lieFormCurl (ballLog (gaugeDescent k (localChainDepth (Tb.stepParameters y) β k)
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db (axialGaugeAt (Tb.stepParameters y) V o₁))
    (topField (Tb.stepParameters y) k _ (sampleBelow (Tb.stepParameters y) k (localChainDepth (Tb.stepParameters y) β k) _ db)) o
    (ballRadius (Tb.stepParameters y).side 1 ρ₀ 0)) (o, μ, ν) with hA
  set G := sampledCurvature T k (localChainDepth (Tb.stepParameters y) β k) 1 x N u o (o, μ, ν) with hGd
  have e1 : ‖(A : ℍ[ℝ])‖ ≤ ‖((A - G : imaginaryQuaternions) : ℍ[ℝ])‖ + ‖(G : ℍ[ℝ])‖ := by
    have := norm_add_le (((A - G : imaginaryQuaternions)) : ℍ[ℝ]) (G : ℍ[ℝ])
    rwa [← Submodule.coe_add, sub_add_cancel] at this
  have e2 : ‖(G : ℍ[ℝ])‖ ≤ deviationMass T k 1 ρ₀ Tb.ρA (localChainDepth (Tb.stepParameters y) β k)
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o (o, μ, ν) + 4 * Xh * Real.pi := by
    rw [hGe]
    have h3 := norm_add_le (levelFluctuationSum T k 1 (logCubeScale x) Tb.ρA (localChainDepth (Tb.stepParameters y) β k)
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o
      (axialGaugeAt (Tb.stepParameters y) V o₁) (o, μ, ν))
      (∑ c : TorusBond (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N),
        adjointTransport (Tb.stepParameters y).coupling Tb.ρA (Tb.stepParameters y).side k (localChainDepth (Tb.stepParameters y) β k)
          (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) (curlFunctional (o, μ, ν)) c •
          topLogForm (Tb.stepParameters y) V o₁
            (ballRadius (Tb.stepParameters y).side 1 (logCubeScale x) (localChainDepth (Tb.stepParameters y) β k)) (x ^ (-(1 / 4 : ℝ))) c)
    have h4 : (∑ c, |adjointTransport (Tb.stepParameters y).coupling Tb.ρA (Tb.stepParameters y).side k
        (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)
        (curlFunctional (o, μ, ν)) c|) * Real.pi ≤ 4 * Xh * Real.pi := by
      refine mul_le_mul_of_nonneg_right ?_ Real.pi_pos.le
      refine le_trans hrow ?_
      linarith
    exact h3.trans (add_le_add hfl' (htop.trans h4))
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have e3 : Cd * (Xh + Real.exp (-(cd * ρ₀))) ≤ 2 * |Cd| * Xh := by
    have h5 : Cd * (Xh + Real.exp (-(cd * ρ₀))) ≤ |Cd| * (Xh + Real.exp (-(cd * ρ₀))) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (add_nonneg hX0 (Real.exp_pos _).le)
    have h6 : |Cd| * (Xh + Real.exp (-(cd * ρ₀))) ≤ |Cd| * (2 * Xh) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    linarith
  have e4 : 4 * Xh * Real.pi ≤ 16 * Xh := by nlinarith
  exact show TorusFields.curvature (topField (Tb.stepParameters y) k _
      (sampleBelow (Tb.stepParameters y) k (localChainDepth (Tb.stepParameters y) β k) _ db)) o μ ν ≤
      deviationMass T k 1 ρ₀ Tb.ρA (localChainDepth (Tb.stepParameters y) β k)
        (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) db o (o, μ, ν) + (2 * |Cd| + 44) * Xh from by
    have h7 : TorusFields.curvature (topField (Tb.stepParameters y) k _
        (sampleBelow (Tb.stepParameters y) k (localChainDepth (Tb.stepParameters y) β k) _ db)) o μ ν ≤
        ‖(A : ℍ[ℝ])‖ + 28 * Xh := h1
    have h8 : ‖((A - G : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ Cd * (Xh + Real.exp (-(cd * ρ₀))) := hc
    linarith
end AtGivenParameters
end BelowFluctuationMass
open BelowFluctuationMass
private theorem holdsOnParameters_and {P₁ P₂ Q : ParameterAssignment → ℝ → Prop} (h₁ : HoldsOnParameterFamilies P₁)
    (h₂ : HoldsOnParameterFamilies P₂) (hQ : ∀ Tb y, P₁ Tb y → P₂ Tb y → Q Tb y) : HoldsOnParameterFamilies Q := by
  intro a ha
  obtain ⟨L₁, r₁, c₁, hr₁, h₁⟩ := h₁ a ha
  obtain ⟨L₂, r₂, c₂, hr₂, h₂⟩ := h₂ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max c₁ c₂,
    fun c => lt_min (hr₁ c) (hr₂ c), fun L hodd hL T hTa hTL hD hS hH hrt hC => ?_⟩
  obtain ⟨y₁, p₁⟩ := h₁ L hodd ((le_max_left _ _).trans hL) T hTa hTL hD hS hH (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hC)
  obtain ⟨y₂, p₂⟩ := h₂ L hodd ((le_max_right _ _).trans hL) T hTa hTL hD hS hH (hrt.trans (min_le_right _ _))
    ((le_max_right _ _).trans hC)
  refine ⟨max y₁ y₂, fun y hy hRow hW => ?_⟩
  exact hQ T y (p₁ y ((le_max_left _ _).trans hy) hRow fun β hβ => hW β hβ)
    (p₂ y ((le_max_right _ _).trans hy) hRow fun β hβ => hW β hβ)
theorem curvatureBelowFluctuationMass_holds (hDesc : curvatureNearDescendedFormStatement)
    (hRow : transportedCurlFunctionalBoundsStatement) (hSum : curvatureLevelSumStatement)
    (hFl : localChainFloorsStatement) :
    curvatureBelowFluctuationMassStatement :=
  holdsOnParameters_and hDesc hRow fun _ _ h₁ h₂ => holds_at hFl hSum h₁ h₂
end YangMills.Construction.MomentLaw
end
