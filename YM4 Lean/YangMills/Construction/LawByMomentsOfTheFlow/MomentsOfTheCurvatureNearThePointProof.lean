import YangMills.Construction.LawByMomentsOfTheFlow.CurvatureUnderTheFluctuationsOfTheChainProof
import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheCurvatureInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheCurvatureNearThePoint
import YangMills.Construction.LawInAState.CovarianceBelowTheAveragesProof
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheCurvatureOfALevel
import YangMills.Construction.ResponseInTheExpansion.PairingsOfASum
import YangMills.Construction.ResponseInTheExpansion.TheFieldIsNearOneAlongTheChain
import YangMills.Construction.SummableBoundsOfTheFlow.SizesOfTheDerivativesOfTheCutProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace YangMills.Construction
open Quaternion ColdStepAtMirrorFrames.SmallUnits
open TorusFields TorusLumps RenormalizationStepParameters StepSettings WeightedResponses ResponseInTheExpansion BlockAverages LumpContours GaugeFixing
  ColdStepAtMirrorFrames LevelTestFunctions
namespace MomentLaw
private theorem norm_le_sum_abs_imaginaryComponent (w : imaginaryQuaternions) :
    ‖(w : ℍ[ℝ])‖ ≤ ∑ e : Fin 3, |imaginaryComponent e w| := by
  have hre : (w : ℍ[ℝ]).re = 0 := w.2
  have hw : ‖(w : ℍ[ℝ])‖ * ‖(w : ℍ[ℝ])‖ = (w : ℍ[ℝ]).imI ^ 2 + (w : ℍ[ℝ]).imJ ^ 2 + (w : ℍ[ℝ]).imK ^ 2 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def', hre]
    ring
  have hs : ∑ e : Fin 3, |imaginaryComponent e w| = |(w : ℍ[ℝ]).imI| + |(w : ℍ[ℝ]).imJ| + |(w : ℍ[ℝ]).imK| := by
    simp [Fin.sum_univ_three, imaginaryComponent]
  rw [hs]
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  have h1 := sq_abs (w : ℍ[ℝ]).imI
  have h2 := sq_abs (w : ℍ[ℝ]).imJ
  have h3 := sq_abs (w : ℍ[ℝ]).imK
  nlinarith [abs_nonneg (w : ℍ[ℝ]).imI, abs_nonneg (w : ℍ[ℝ]).imJ, abs_nonneg (w : ℍ[ℝ]).imK,
    mul_nonneg (abs_nonneg (w : ℍ[ℝ]).imI) (abs_nonneg (w : ℍ[ℝ]).imJ),
    mul_nonneg (abs_nonneg (w : ℍ[ℝ]).imI) (abs_nonneg (w : ℍ[ℝ]).imK),
    mul_nonneg (abs_nonneg (w : ℍ[ℝ]).imJ) (abs_nonneg (w : ℍ[ℝ]).imK)]
private theorem curvature_le_norm_lieFormCurl {m : ℕ} [NeZero m] (g : TorusSite m → UnitQuaternion) (W : TorusField m) (o : TorusSite m) (r s : ℝ) (hr : 1 ≤ r) (hs : s ≤ 1)
    (μ ν : Fin 4)
    (h : ∀ b : TorusBond m, b.1 ∈ supBall o r → ‖(minimalLog (ResponseInTheExpansion.gaugeTransform g W b) : Quaternion ℝ)‖ ≤ s) :
    curvature W o μ ν ≤ ‖((lieFormCurl (ballLog g W o r) (o, μ, ν) : imaginaryQuaternions) : ℍ[ℝ])‖ + 28 * s ^ 2 := by apply _root_.YangMills.SharedProofs.p99149 <;> assumption
private theorem norm_minimalLog_le_of_smallAlong {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) (k : ℕ) (nn ρ₀ s : ℝ) :
    ∀ (d n : ℕ) [NeZero n] (u : MarkedSample ℓ (k + d) n) (o : TorusSite (fineSide ℓ.side d n)) (g : TorusSite n → UnitQuaternion),
      IsGaugeSmallAlong T k nn ρ₀ s d n u o g →
      ∀ b : TorusBond (fineSide ℓ.side d n), b.1 ∈ supBall o (ballRadius ℓ.side nn ρ₀ 0) →
        ‖(minimalLog (ResponseInTheExpansion.gaugeTransform (gaugeDescent k d n u g) (topField ℓ k _ (sampleBelow ℓ k d n u)) b) : Quaternion ℝ)‖ ≤ s
  | 0, _, _, _, _, _, h, b, hb => h b hb
  | d + 1, n, _, u, o, _, h, b, hb => norm_minimalLog_le_of_smallAlong T k nn ρ₀ s d (n * ℓ.side) u.1 o _ h.2.2 b hb
private theorem measurable_topField (ℓ : TorusLumps.StepParameters) : ∀ (s n : ℕ), Measurable (topField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => by
    let := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
    exact measurable_fst.comp (measurable_snd.comp measurable_snd)
private theorem add_pow_le_two_pow_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by apply _root_.YangMills.Construction.Interpolation.CutoffDerivatives.add_pow_le_two_pow_mul <;> assumption
private theorem add_four_pow_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (n : ℕ) :
    (a + b + c + d) ^ n ≤ 4 ^ n * (a ^ n + b ^ n + c ^ n + d ^ n) := by
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  have e : a + b + c + d = (a + b) + (c + d) := by ring
  have e4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  rw [e]
  refine (add_pow_le_two_pow_mul (by positivity) (by positivity) n).trans ?_
  have h1 := add_pow_le_two_pow_mul ha hb n
  have h3 := add_pow_le_two_pow_mul hc hd n
  calc 2 ^ n * ((a + b) ^ n + (c + d) ^ n) ≤ 2 ^ n * (2 ^ n * (a ^ n + b ^ n) + 2 ^ n * (c ^ n + d ^ n)) :=
        mul_le_mul_of_nonneg_left (by linarith) h2
    _ = _ := by rw [e4]; ring
private theorem eventually_exp_bounds (cd cl : ℝ) (q : ℕ) (hcd : 0 < cd) (hcl : 0 < cl) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → 1 ≤ x ∧ Real.exp (-(cd * logCubeScale x)) ≤ x ^ (-(1 / 2 : ℝ)) ∧
      Real.exp (-(cl * x)) ≤ x ^ (-(q : ℝ)) := by
  have e1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have e2 : ∀ᶠ x : ℝ in atTop, 2 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 2
  have e3 : ∀ᶠ x : ℝ in atTop, 1 / cd ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop _
  have e4 := (isLittleO_exp_neg_mul_rpow_atTop hcl (-(q : ℝ))).bound (c := 1) one_pos
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp (e1.and (e2.and (e3.and e4)))
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hX x hx
  have hx0 : 0 < x := by linarith
  refine ⟨h1, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    set l := Real.log x with hl
    have hfl : l ^ 3 - 1 ≤ logCubeScale x := by
      have := Nat.lt_floor_add_one (l ^ 3)
      simp only [logCubeScale]
      linarith
    have hcl' : 1 ≤ cd * l := by
      rw [div_le_iff₀ hcd] at h3
      linarith
    have hl3 : l ^ 3 / 2 ≤ l ^ 3 - 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h2), sq_nonneg l]
    have hs : cd * (l ^ 3 / 2) ≤ cd * logCubeScale x := mul_le_mul_of_nonneg_left (hl3.trans hfl) hcd.le
    have hll : l / 2 ≤ cd * (l ^ 3 / 2) := by
      have : cd * (l ^ 3 / 2) = (cd * l) * (l ^ 2 / 2) := by ring
      rw [this]
      nlinarith [sq_nonneg l]
    linarith
  · have h5 : ‖Real.exp (-cl * x)‖ ≤ 1 * ‖x ^ (-(q : ℝ))‖ := h4
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at h5
    simpa [neg_mul] using h5
private theorem eventually_room (D Ξ Cw : ℝ) (hD : 0 < D) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → 2 ≤ x ∧ Cw * Real.log x ≤ x / 2 ∧
      (4 * Real.log x + 1) + 2 * Real.log (2 * x) ^ 2 + 2 ^ 10 * (2 * x) ^ ((1 : ℝ) / 20) + 8 ≤ (x - Ξ) / D := by apply _root_.YangMills.SharedProofs.p10067 <;> assumption
open Classical in
private def LevelMomentsAt (Tb : ParameterAssignment) (y : ℝ) : Prop :=
  ∀ q : ℕ, ∃ C x₀ : ℝ, ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ)
    (o : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
      (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)))
    (p : Fin q → TorusPlaquette (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
      (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))) (e : Fin q → Fin 3) (w : ℕ),
    N = 2 * (Tb.stepParameters y).side ^ (w + 1) → IsLocalChainAbove Tb y T β k N nn x₀ →
    (∀ j, p j ∈ plaquettesIn Finset.univ ∧ (p j).1 ∈ supBall o (19 * nn)) →
    MeasurableSet {u | IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o} ∧
    (∀ i, AEStronglyMeasurable (Set.indicator {u | IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
          (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o}
        (fun u => imaginaryComponent (e i) (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) nn
          (couplingFlow (Tb.stepParameters y) β k).1 N u o (p i))))
      (markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 + chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)) ∧
    (∀ᵐ u ∂(markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 + chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N),
      IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o →
      ∀ i, |imaginaryComponent (e i) (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) nn
        (couplingFlow (Tb.stepParameters y) β k).1 N u o (p i))| ≤ C) ∧
    (∀ i i', e i = e i' → |accumulatedCovariance Tb.coupling Tb.ρA (Tb.stepParameters y).side k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
      (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
      (curlFunctional (p i)) (curlFunctional (p i'))| ≤ C) ∧
    Integrable (Set.indicator {u | IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
          (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o}
        (fun u => ∏ j, imaginaryComponent (e j) (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) nn
          (couplingFlow (Tb.stepParameters y) β k).1 N u o (p j))))
      (markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 + chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) ∧
    |∫ u, Set.indicator {u | IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
          (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o}
        (fun u => ∏ j, imaginaryComponent (e j) (sampledCurvature T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) nn
          (couplingFlow (Tb.stepParameters y) β k).1 N u o (p j))) u
        ∂(markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 + chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N) -
      (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(q : ℝ) / 2) * wickPairingSum fun i j =>
        if e i = e j then accumulatedCovariance Tb.coupling Tb.ρA (Tb.stepParameters y).side k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
          (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
          (curlFunctional (p i)) (curlFunctional (p j)) else 0| ≤
      C * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-((q : ℝ) + 1) / 2 + 2 / 1000)
open Classical in
private def LocalEventLikelyAt (Tb : ParameterAssignment) (y : ℝ) : Prop :=
  ∃ c x₀ : ℝ, 0 < c ∧ ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k e N : ℕ) [NeZero N] (nn : ℝ)
    (o : TorusSite (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
      (fineSide (Tb.stepParameters y).side (chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N))),
    N = 2 * (Tb.stepParameters y).side ^ e → IsLocalChainAbove Tb y T β k N nn x₀ →
    MeasureTheory.Measure.real (markedSampleLaw T β (k + chainDepth (couplingFlow (Tb.stepParameters y) β k).1 +
        chainDepth (couplingFlow (Tb.stepParameters y) β k).1) N)
      {u | ¬ IsLocalEvent T k (chainDepth (couplingFlow (Tb.stepParameters y) β k).1)
        (localBoxRadius (couplingFlow (Tb.stepParameters y) β k).1) N u o} ≤
      Real.exp (-(c * (couplingFlow (Tb.stepParameters y) β k).1))
section LocalBounds
variable (Tb : ParameterAssignment) (y : ℝ)
variable (T : StageTower (ParameterAssignment.stepParameters Tb y)) (β : ℝ) (k N : ℕ) [NeZero N]
private def lowerField (u : MarkedSample (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) : TorusField (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)) :=
  topField (Tb.stepParameters y) k _ (sampleBelow (Tb.stepParameters y) k (localChainDepth (Tb.stepParameters y) β k) _ (sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k)) (localChainDepth (Tb.stepParameters y) β k) N u))
private def middleGauge (u : MarkedSample (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) (o : TorusSite (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))) : TorusSite (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) → UnitQuaternion :=
  axialGaugeAt (Tb.stepParameters y) (topField (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k)) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) (sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k)) (localChainDepth (Tb.stepParameters y) β k) N u))
    (siteAbove (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) o)
private def SmallAlongAt (s : ℝ) (u : MarkedSample (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) (o : TorusSite (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))) : Prop :=
  IsGaugeSmallAlong T k 1 (localLogScale (Tb.stepParameters y) β k) s (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) (sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k)) (localChainDepth (Tb.stepParameters y) β k) N u) o (middleGauge Tb y β k N u o)
private theorem mem_plaquettesIn_ball (o : TorusSite (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))) (μ ν : Fin 4) (hμν : μ < ν) (r : ℝ) (hr : 2 ≤ r) :
    (o, μ, ν) ∈ plaquettesIn (supBall o r) := by
  simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hμν, ?_⟩
  have hb : ∀ z : TorusSite (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)), TorusFields.supDist z o ≤ 2 → z ∈ supBall o r := by
    intro z hz
    simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
    exact le_trans (by exact_mod_cast hz) hr
  intro z hz
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  have e1 : ∀ i, TorusFields.supDist (o + TorusFields.unitStep _ i) o ≤ 1 := fun i => by rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; exact supDist_add_unitStep_le o i
  rcases hz with rfl | rfl | rfl | rfl
  · apply hb; rw [supDist_self]; omega
  · exact hb _ ((e1 μ).trans (by omega))
  · exact hb _ ((e1 ν).trans (by omega))
  · apply hb
    have h1 := supDist_triangle (o + TorusFields.unitStep _ μ + TorusFields.unitStep _ ν) (o + TorusFields.unitStep _ μ) o
    have h2 : TorusFields.supDist (o + TorusFields.unitStep _ μ + TorusFields.unitStep _ ν) (o + TorusFields.unitStep _ μ) ≤ 1 := by rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; exact supDist_add_unitStep_le _ ν
    have h3 := e1 μ
    omega
private theorem curvature_le_on_good_event (Cd cd : ℝ) (hx : 1 ≤ (flowCouplings (Tb.stepParameters y) β k))
    (hexp : Real.exp (-(cd * localLogScale (Tb.stepParameters y) β k)) ≤ (flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 2 : ℝ)))
    (o : TorusSite (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))) (μ ν : Fin 4) (hμν : μ < ν) (u : MarkedSample (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N)
    (hs : SmallAlongAt Tb y T β k N ((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 4 : ℝ))) u o)
    (hc : ∀ p ∈ plaquettesIn (supBall o (ballRadius (Tb.stepParameters y).side 1 (localLogScale (Tb.stepParameters y) β k) 0)),
        ‖((lieFormCurl (ballLog (gaugeDescent k (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) (sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k)) (localChainDepth (Tb.stepParameters y) β k) N u) (middleGauge Tb y β k N u o))
            (lowerField Tb y β k N u) o (ballRadius (Tb.stepParameters y).side 1 (localLogScale (Tb.stepParameters y) β k) 0)) p -
          sampledCurvature T k (localChainDepth (Tb.stepParameters y) β k) 1 (flowCouplings (Tb.stepParameters y) β k) N u o p : imaginaryQuaternions) : Quaternion ℝ)‖ ≤
        Cd * (((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 4 : ℝ))) ^ 2 + Real.exp (-(cd * localLogScale (Tb.stepParameters y) β k)))) :
    curvature (lowerField Tb y β k N u) o μ ν ≤
      (∑ e : Fin 3, |imaginaryComponent e (sampledCurvature T k (localChainDepth (Tb.stepParameters y) β k) 1 (flowCouplings (Tb.stepParameters y) β k) N u o (o, μ, ν))|) + (2 * |Cd| + 28) * (flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 2 : ℝ)) := by
  have hx0 : 0 < (flowCouplings (Tb.stepParameters y) β k) := by linarith
  have hs2 : ((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 4 : ℝ))) ^ 2 = (flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hs1 : (flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hρ : (0 : ℝ) ≤ localLogScale (Tb.stepParameters y) β k := by simp only [localLogScale, logCubeScale]; positivity
  have hr : (2 : ℝ) ≤ ballRadius (Tb.stepParameters y).side 1 (localLogScale (Tb.stepParameters y) β k) 0 := by
    simp only [ballRadius, pow_zero, div_one]
    linarith
  have hlogs := norm_minimalLog_le_of_smallAlong T k 1 (localLogScale (Tb.stepParameters y) β k) ((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 4 : ℝ))) (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)
    (sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k)) (localChainDepth (Tb.stepParameters y) β k) N u) o (middleGauge Tb y β k N u o) hs
  have h1 := curvature_le_norm_lieFormCurl _ (lowerField Tb y β k N u) o _ _ (by linarith) hs1 μ ν hlogs
  have h2 := hc (o, μ, ν) (mem_plaquettesIn_ball Tb y β k N o μ ν hμν _ hr)
  rw [hs2] at h1 h2
  have h3 := norm_le_sum_abs_imaginaryComponent (sampledCurvature T k (localChainDepth (Tb.stepParameters y) β k) 1 (flowCouplings (Tb.stepParameters y) β k) N u o (o, μ, ν))
  refine h1.trans ?_
  have h4 := norm_add_le (((lieFormCurl (ballLog (gaugeDescent k (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) (sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k)) (localChainDepth (Tb.stepParameters y) β k) N u)
      (middleGauge Tb y β k N u o)) (lowerField Tb y β k N u) o (ballRadius (Tb.stepParameters y).side 1 (localLogScale (Tb.stepParameters y) β k) 0)) (o, μ, ν) -
    sampledCurvature T k (localChainDepth (Tb.stepParameters y) β k) 1 (flowCouplings (Tb.stepParameters y) β k) N u o (o, μ, ν) : imaginaryQuaternions) : Quaternion ℝ))
    ((sampledCurvature T k (localChainDepth (Tb.stepParameters y) β k) 1 (flowCouplings (Tb.stepParameters y) β k) N u o (o, μ, ν) : imaginaryQuaternions) : Quaternion ℝ)
  rw [← Submodule.coe_add, sub_add_cancel] at h4
  have hp : 0 ≤ (flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
  have h5 : Cd * ((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 2 : ℝ)) + Real.exp (-(cd * localLogScale (Tb.stepParameters y) β k))) ≤ 2 * |Cd| * (flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 2 : ℝ)) := by
    have : Cd * ((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 2 : ℝ)) + Real.exp (-(cd * localLogScale (Tb.stepParameters y) β k))) ≤
        |Cd| * ((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 2 : ℝ)) + Real.exp (-(cd * localLogScale (Tb.stepParameters y) β k))) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (add_nonneg hp (Real.exp_pos _).le)
    have h6 : |Cd| * ((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 2 : ℝ)) + Real.exp (-(cd * localLogScale (Tb.stepParameters y) β k))) ≤ |Cd| * (2 * (flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    linarith
  nlinarith
end LocalBounds
private theorem curvature_le_two {m : ℕ} (W : TorusField m) (z : TorusSite m) (μ ν : Fin 4) : curvature W z μ ν ≤ 2 := by apply _root_.YangMills.SharedProofs.p28884 <;> assumption
private theorem curvature_pow_le {m : ℕ} (W : TorusField m) (z : TorusSite m) (μ ν : Fin 4) (q : ℕ) : curvature W z μ ν ^ (2 * q) ≤ 4 ^ q := by
  have h : (0 : ℝ) ≤ curvature W z μ ν := norm_nonneg _
  calc curvature W z μ ν ^ (2 * q) ≤ 2 ^ (2 * q) := pow_le_pow_left₀ h (curvature_le_two W z μ ν) _
    _ = 4 ^ q := by rw [pow_mul]; norm_num
section MomentBounds
variable (Tb : ParameterAssignment) (y : ℝ)
variable (T : StageTower (ParameterAssignment.stepParameters Tb y)) (β : ℝ) (k N : ℕ) [NeZero N]
private def localEvent (o : TorusSite (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))) : Set (MarkedSample (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) :=
  {u | IsLocalEvent T k (localChainDepth (Tb.stepParameters y) β k) (localBoxRadius (flowCouplings (Tb.stepParameters y) β k)) N u o}
private def componentPower (q : ℕ) (o : TorusSite (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))) (p : TorusPlaquette (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))) (e : Fin 3) : MarkedSample (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N → ℝ :=
  Set.indicator (localEvent Tb y T β k N o) fun u => imaginaryComponent e (sampledCurvature T k (localChainDepth (Tb.stepParameters y) β k) 1 (flowCouplings (Tb.stepParameters y) β k) N u o p) ^ (2 * q)
private theorem moment_bound_fixed (q : ℕ) (o : TorusSite (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))) (μ ν : Fin 4) (hμν : μ < ν)
    (hF : (Tb.stepParameters y).Admissible) (hJ : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side) (hcut : IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn) (hco : T.MarksMeasurable)
    (hlaw : sampleBelowLawStatement) (hprob : forgetLastStepStatement)
    (hx : 1 ≤ (flowCouplings (Tb.stepParameters y) β k)) (Cd cd : ℝ) (hexp : Real.exp (-(cd * localLogScale (Tb.stepParameters y) β k)) ≤ (flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 2 : ℝ)))
    (Pq Cb : ℝ) (hPq : 0 ≤ Pq) (hCb : 0 ≤ Cb)
    (hint : ∀ e, Integrable (componentPower Tb y T β k N q o (o, μ, ν) e) (markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N))
    (hI : ∀ e, ∫ u, componentPower Tb y T β k N q o (o, μ, ν) e u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) ≤ Pq * (flowCouplings (Tb.stepParameters y) β k) ^ (-(q : ℝ)))
    (hbad : (markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) ((localEvent Tb y T β k N o)ᶜ ∪
        {u | u ∈ localEvent Tb y T β k N o ∧ ¬ SmallAlongAt Tb y T β k N ((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 4 : ℝ))) u o}) ≤
      ENNReal.ofReal (Cb * (flowCouplings (Tb.stepParameters y) β k) ^ (-(q : ℝ))))
    (hclose : ∀ᵐ u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N), u ∈ localEvent Tb y T β k N o → SmallAlongAt Tb y T β k N ((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 4 : ℝ))) u o →
      ∀ p ∈ plaquettesIn (supBall o (ballRadius (Tb.stepParameters y).side 1 (localLogScale (Tb.stepParameters y) β k) 0)),
        ‖((lieFormCurl (ballLog (gaugeDescent k (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) (sampleBelow (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k)) (localChainDepth (Tb.stepParameters y) β k) N u) (middleGauge Tb y β k N u o))
            (lowerField Tb y β k N u) o (ballRadius (Tb.stepParameters y).side 1 (localLogScale (Tb.stepParameters y) β k) 0)) p -
          sampledCurvature T k (localChainDepth (Tb.stepParameters y) β k) 1 (flowCouplings (Tb.stepParameters y) β k) N u o p : imaginaryQuaternions) : Quaternion ℝ)‖ ≤
        Cd * (((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 4 : ℝ))) ^ 2 + Real.exp (-(cd * localLogScale (Tb.stepParameters y) β k)))) :
    ∫⁻ v, ENNReal.ofReal (curvature (topField (Tb.stepParameters y) k (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)) v) o μ ν ^ (2 * q)) ∂(markedSampleLaw T β k (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))) ≤
      ENNReal.ofReal ((4 ^ (2 * q) * (3 * Pq + (2 * |Cd| + 28) ^ (2 * q)) + 4 ^ q * Cb) * (flowCouplings (Tb.stepParameters y) β k) ^ (-(q : ℝ))) := by
  have hP : IsProbabilityMeasure (markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) := (hprob (Tb.stepParameters y) hF hJ T hcut hco β _ N).1
  have hx0 : 0 < (flowCouplings (Tb.stepParameters y) β k) := by linarith
  have hX0 : 0 ≤ (flowCouplings (Tb.stepParameters y) β k) ^ (-(q : ℝ)) := Real.rpow_nonneg hx0.le _
  have hFm : Measurable fun v : MarkedSample (Tb.stepParameters y) k (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)) => ENNReal.ofReal (curvature (topField (Tb.stepParameters y) k (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)) v) o μ ν ^ (2 * q)) :=
    ENNReal.measurable_ofReal.comp
      (((continuous_curvature o μ ν).measurable.comp (measurable_topField (Tb.stepParameters y) k (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)))).pow_const _)
  have law := (hlaw (Tb.stepParameters y) hF hJ T hcut hco β (fun _ => 0)).1
  have l1 := law k (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)
  have l2 := law (k + (localChainDepth (Tb.stepParameters y) β k)) (localChainDepth (Tb.stepParameters y) β k) N
  have step : ∫⁻ v, ENNReal.ofReal (curvature (topField (Tb.stepParameters y) k (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)) v) o μ ν ^ (2 * q)) ∂(markedSampleLaw T β k (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))) =
      ∫⁻ u, ENNReal.ofReal (curvature (lowerField Tb y β k N u) o μ ν ^ (2 * q)) ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) := by
    rw [← l1.2, lintegral_map hFm l1.1, ← l2.2]
    exact lintegral_map (hFm.comp l1.1) l2.1
  rw [step]
  set Ev := localEvent Tb y T β k N o with hEv
  set Bad : Set (MarkedSample (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) :=
    Evᶜ ∪ {u | u ∈ Ev ∧ ¬ SmallAlongAt Tb y T β k N ((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 4 : ℝ))) u o} with hBad
  set Tm := toMeasurable (markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) Bad with hTmdef
  have hTm : MeasurableSet Tm := measurableSet_toMeasurable _ _
  have hμT : (markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) Tm = (markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) Bad := measure_toMeasurable _
  set h := componentPower Tb y T β k N q o (o, μ, ν) with hh
  set A₁ : ℝ := 2 * |Cd| + 28 with hA₁
  have hA₁0 : 0 ≤ A₁ := by positivity
  set Dc : ℝ := 4 ^ (2 * q) * (A₁ ^ (2 * q) * (flowCouplings (Tb.stepParameters y) β k) ^ (-(q : ℝ))) with hDc
  have hh0 : ∀ e u, 0 ≤ h e u := by
    intro e u
    simp only [hh, componentPower]
    exact Set.indicator_nonneg (fun _ _ => (even_two_mul q).pow_nonneg _) u
  set H : MarkedSample (Tb.stepParameters y) (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N → ℝ := fun u => 4 ^ (2 * q) * (h 0 u + h 1 u + h 2 u) + Dc with hH
  have hle : ∀ᵐ u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N), ENNReal.ofReal (curvature (lowerField Tb y β k N u) o μ ν ^ (2 * q)) ≤
      ENNReal.ofReal (H u) + Tm.indicator (fun _ => ENNReal.ofReal (4 ^ q)) u := by
    filter_upwards [hclose] with u hu
    by_cases hb : u ∈ Bad
    · have hu' : u ∈ Tm := subset_toMeasurable _ _ hb
      rw [Set.indicator_of_mem hu']
      exact le_trans (ENNReal.ofReal_le_ofReal (curvature_pow_le _ _ _ _ _)) le_add_self
    · have hE : u ∈ Ev := by
        by_contra hc
        exact hb (Or.inl hc)
      have hS : SmallAlongAt Tb y T β k N ((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 4 : ℝ))) u o := by
        by_contra hc
        exact hb (Or.inr ⟨hE, hc⟩)
      have hg := curvature_le_on_good_event Tb y T β k N Cd cd hx hexp o μ ν hμν u hS (hu hE hS)
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) le_self_add
      rw [Fin.sum_univ_three] at hg
      have h4 := add_four_pow_le (abs_nonneg (imaginaryComponent 0 (sampledCurvature T k (localChainDepth (Tb.stepParameters y) β k) 1 (flowCouplings (Tb.stepParameters y) β k) N u o (o, μ, ν))))
        (abs_nonneg (imaginaryComponent 1 (sampledCurvature T k (localChainDepth (Tb.stepParameters y) β k) 1 (flowCouplings (Tb.stepParameters y) β k) N u o (o, μ, ν))))
        (abs_nonneg (imaginaryComponent 2 (sampledCurvature T k (localChainDepth (Tb.stepParameters y) β k) 1 (flowCouplings (Tb.stepParameters y) β k) N u o (o, μ, ν))))
        (mul_nonneg hA₁0 (Real.rpow_nonneg hx0.le (-(1 / 2 : ℝ)))) (2 * q)
      have hcurv : (0 : ℝ) ≤ curvature (lowerField Tb y β k N u) o μ ν := norm_nonneg _
      have h5 := pow_le_pow_left₀ hcurv hg (2 * q)
      have hpart : ∀ e, |imaginaryComponent e (sampledCurvature T k (localChainDepth (Tb.stepParameters y) β k) 1 (flowCouplings (Tb.stepParameters y) β k) N u o (o, μ, ν))| ^ (2 * q) = h e u := by
        intro e
        simp only [hh, componentPower]
        rw [Set.indicator_of_mem hE, (even_two_mul q).pow_abs]
      have hlast : (A₁ * (flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 2 : ℝ))) ^ (2 * q) = A₁ ^ (2 * q) * (flowCouplings (Tb.stepParameters y) β k) ^ (-(q : ℝ)) := by
        rw [mul_pow, ← Real.rpow_natCast ((flowCouplings (Tb.stepParameters y) β k) ^ (-(1 / 2 : ℝ))), ← Real.rpow_mul hx0.le]
        congr 2
        push_cast
        ring
      rw [hpart 0, hpart 1, hpart 2, hlast] at h4
      refine h5.trans (h4.trans (le_of_eq ?_))
      simp only [hH, hDc]
      ring
  have hHint : Integrable H (markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) := by
    have h0 := hint 0
    have h1 := hint 1
    have h2 := hint 2
    exact (((h0.add h1).add h2).const_mul _).add (integrable_const _)
  have hH0 : 0 ≤ᵐ[(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N)] H := by
    refine Filter.Eventually.of_forall fun u => ?_
    have a0 := hh0 0 u
    have a1 := hh0 1 u
    have a2 := hh0 2 u
    have : 0 ≤ Dc := by positivity
    simp only [hH, Pi.zero_apply]
    positivity
  have hIH : ∫ u, H u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) = 4 ^ (2 * q) * (∫ u, h 0 u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) + ∫ u, h 1 u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) + ∫ u, h 2 u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N)) + Dc := by
    have hi : Integrable (fun u => (4 : ℝ) ^ (2 * q) * (h 0 u + h 1 u + h 2 u)) (markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) :=
      (((hint 0).add (hint 1)).add (hint 2)).const_mul _
    have a1 : ∫ u, H u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) = ∫ u, (4 : ℝ) ^ (2 * q) * (h 0 u + h 1 u + h 2 u) ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) + ∫ _, Dc ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) :=
      integral_add hi (integrable_const _)
    have a2 : ∫ u, (4 : ℝ) ^ (2 * q) * (h 0 u + h 1 u + h 2 u) ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) = 4 ^ (2 * q) * ∫ u, (h 0 u + h 1 u + h 2 u) ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) :=
      integral_const_mul _ _
    have a3 : ∫ u, (h 0 u + h 1 u + h 2 u) ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) = ∫ u, (h 0 u + h 1 u) ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) + ∫ u, h 2 u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) :=
      integral_add ((hint 0).add (hint 1)) (hint 2)
    have a4 : ∫ u, (h 0 u + h 1 u) ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) = ∫ u, h 0 u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) + ∫ u, h 1 u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) := integral_add (hint 0) (hint 1)
    have a5 : ∫ _, Dc ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) = Dc := by simp
    rw [a1, a2, a3, a4, a5]
  have hHle : ∫ u, H u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) ≤ 4 ^ (2 * q) * (3 * Pq + A₁ ^ (2 * q)) * (flowCouplings (Tb.stepParameters y) β k) ^ (-(q : ℝ)) := by
    rw [hIH]
    have i0 := hI 0
    have i1 := hI 1
    have i2 := hI 2
    have h4 : (0 : ℝ) ≤ 4 ^ (2 * q) := by positivity
    have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add i0 i1) i2) h4
    simp only [hDc]
    nlinarith
  calc ∫⁻ u, ENNReal.ofReal (curvature (lowerField Tb y β k N u) o μ ν ^ (2 * q)) ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N)
      ≤ ∫⁻ u, ENNReal.ofReal (H u) + Tm.indicator (fun _ => ENNReal.ofReal (4 ^ q)) u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) := lintegral_mono_ae hle
    _ = ∫⁻ u, ENNReal.ofReal (H u) ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) + ∫⁻ u, Tm.indicator (fun _ => ENNReal.ofReal (4 ^ q)) u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) :=
        lintegral_add_right _ (measurable_const.indicator hTm)
    _ = ENNReal.ofReal (∫ u, H u ∂(markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N)) + ENNReal.ofReal (4 ^ q) * (markedSampleLaw T β (k + (localChainDepth (Tb.stepParameters y) β k) + (localChainDepth (Tb.stepParameters y) β k)) N) Tm := by
        rw [← ofReal_integral_eq_lintegral_ofReal hHint hH0, lintegral_indicator_const hTm]
    _ ≤ ENNReal.ofReal (4 ^ (2 * q) * (3 * Pq + A₁ ^ (2 * q)) * (flowCouplings (Tb.stepParameters y) β k) ^ (-(q : ℝ))) +
          ENNReal.ofReal (4 ^ q) * ENNReal.ofReal (Cb * (flowCouplings (Tb.stepParameters y) β k) ^ (-(q : ℝ))) := by
        rw [hμT]
        gcongr
    _ = ENNReal.ofReal (4 ^ (2 * q) * (3 * Pq + A₁ ^ (2 * q)) * (flowCouplings (Tb.stepParameters y) β k) ^ (-(q : ℝ)) + 4 ^ q * (Cb * (flowCouplings (Tb.stepParameters y) β k) ^ (-(q : ℝ)))) := by
        have n1 : 0 ≤ (4 : ℝ) ^ (2 * q) * (3 * Pq + A₁ ^ (2 * q)) * (flowCouplings (Tb.stepParameters y) β k) ^ (-(q : ℝ)) :=
          mul_nonneg (mul_nonneg (by positivity) (add_nonneg (by positivity) (pow_nonneg hA₁0 _))) hX0
        have n2 : (0 : ℝ) ≤ 4 ^ q := by positivity
        rw [← ENNReal.ofReal_mul n2, ← ENNReal.ofReal_add n1 (mul_nonneg n2 (mul_nonneg hCb hX0))]
    _ = _ := by
        congr 1
        ring
omit [NeZero N] in
private theorem le_of_abs_sub_pairing_le {q' : ℕ} {I X Y : ℝ} {G : Fin q' → Fin q' → ℝ} (B : ℝ) (h : |I - X * wickPairingSum G| ≤ Y)
    (hG : |wickPairingSum G| ≤ B) (hX : 0 ≤ X) : I ≤ X * B + Y := by
  have h1 := (le_abs_self _).trans h
  have h2 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hG) hX
  linarith
private theorem moment_bound_at_level (hm : LevelMomentsAt Tb y) (hn : nearIdentityAlongChainAt Tb y)
    (hd : curvatureNearDescendedFormAt Tb y) (hl : LocalEventLikelyAt Tb y)
    (hF : (Tb.stepParameters y).Admissible) (hJ : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side)
    (hlaw : sampleBelowLawStatement) (hprob : forgetLastStepStatement)
    (hpair : matchingSumPropertiesStatement) (q : ℕ) :
    ∃ A x₀ : ℝ, 0 ≤ A ∧ ∀ (T : StageTower (ParameterAssignment.stepParameters Tb y)) (β : ℝ) (k N w : ℕ) [NeZero N] (m : ℕ) [NeZero m],
      N = 2 * (Tb.stepParameters y).side ^ (w + 1) → IsLocalChainAbove Tb y T β k N 1 x₀ →
      m = fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) →
      ∀ (z : TorusSite m) (μ ν : Fin 4), μ < ν →
      ∫⁻ v, ENNReal.ofReal (curvature (topField (Tb.stepParameters y) k m v) z μ ν ^ (2 * q)) ∂(markedSampleLaw T β k m) ≤
        ENNReal.ofReal (A * flowCouplings (Tb.stepParameters y) β k ^ (-(q : ℝ))) := by
  obtain ⟨Cm, xm, hm'⟩ := hm (2 * q)
  obtain ⟨Cn, xn, hn'⟩ := hn q
  obtain ⟨Cd, cd, xd, hcd, hd'⟩ := hd
  obtain ⟨cl, xl, hcl, hl'⟩ := hl
  obtain ⟨X1, hX1⟩ := eventually_exp_bounds cd cl q hcd hcl
  set b := Real.sqrt |Cm| with hb
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = |Cm| := Real.sq_sqrt (abs_nonneg _)
  set Pq : ℝ := ((2 * q).factorial : ℝ) * b ^ (2 * q) + |Cm| with hPq
  have hPq0 : 0 ≤ Pq := by positivity
  set Cb : ℝ := 1 + |Cn| with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨4 ^ (2 * q) * (3 * Pq + (2 * |Cd| + 28) ^ (2 * q)) + 4 ^ q * Cb, max (max xm xn) (max (max xd xl) X1),
    by positivity, ?_⟩
  intro T β k N w _ m _ hN hloc hmN z μ ν hμν
  subst hmN
  have hfl := hloc.floor_le
  have mono : ∀ x', x' ≤ max (max xm xn) (max (max xd xl) X1) → IsLocalChainAbove Tb y T β k N 1 x' :=
    fun x' h => { hloc with floor_le := h.trans hfl }
  have lm := mono xm ((le_max_left _ _).trans (le_max_left _ _))
  have ln := mono xn ((le_max_right _ _).trans (le_max_left _ _))
  have ld := mono xd ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _)))
  have ll := mono xl ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _)))
  obtain ⟨hx1, hexp, hexp2⟩ := hX1 (flowCouplings (Tb.stepParameters y) β k) (((le_max_right _ _).trans (le_max_right _ _)).trans hfl)
  have hx0 : 0 < flowCouplings (Tb.stepParameters y) β k := by linarith
  have hX0 : 0 ≤ flowCouplings (Tb.stepParameters y) β k ^ (-(q : ℝ)) := Real.rpow_nonneg hx0.le _
  have hLN : (Tb.stepParameters y).side ∣ N := by
    rw [hN]
    exact ⟨2 * (Tb.stepParameters y).side ^ w, by ring⟩
  have hP : IsProbabilityMeasure (markedSampleLaw T β (k + localChainDepth (Tb.stepParameters y) β k + localChainDepth (Tb.stepParameters y) β k) N) :=
    (hprob (Tb.stepParameters y) hF hJ T hloc.cutoff hloc.measurable β _ N).1
  have hmem : ∀ _ : Fin (2 * q), ((z, μ, ν) : TorusPlaquette (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))) ∈
      plaquettesIn Finset.univ ∧ z ∈ supBall z (19 * 1) := by
    intro _
    refine ⟨?_, ?_⟩
    · simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hμν, fun _ _ => trivial⟩
    · simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and, supDist_self]
      norm_num
  have hmom := fun e : Fin 3 => hm' T β k N 1 z (fun _ => (z, μ, ν)) (fun _ => e) w hN lm hmem
  have hint : ∀ e, Integrable (componentPower Tb y T β k N q z (z, μ, ν) e)
      (markedSampleLaw T β (k + localChainDepth (Tb.stepParameters y) β k + localChainDepth (Tb.stepParameters y) β k) N) := by
    intro e
    have h5 := (hmom e).2.2.2.2.1
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h5
    exact h5
  have hI : ∀ e, ∫ u, componentPower Tb y T β k N q z (z, μ, ν) e u ∂(markedSampleLaw T β (k + localChainDepth (Tb.stepParameters y) β k + localChainDepth (Tb.stepParameters y) β k) N) ≤
      Pq * flowCouplings (Tb.stepParameters y) β k ^ (-(q : ℝ)) := by
    intro e
    have h6 := (hmom e).2.2.2.2.2
    have hcov := (hmom e).2.2.2.1
    have key : ∀ G : Fin (2 * q) → Fin (2 * q) → ℝ, (∀ i j, |G i j| ≤ b ^ 2) →
        |wickPairingSum G| ≤ ((2 * q).factorial : ℝ) * b ^ (2 * q) := by
      intro G hG
      rw [hpair.1 (2 * q) G]
      have := (hpair.2.2 (Fin (2 * q))).2.2.1 Finset.univ G b hb0 hG
      rwa [Finset.card_univ, Fintype.card_fin] at this
    have e1 : flowCouplings (Tb.stepParameters y) β k ^ (-((2 * q : ℕ) : ℝ) / 2) = flowCouplings (Tb.stepParameters y) β k ^ (-(q : ℝ)) := by
      congr 1
      push_cast
      ring
    have e2 : flowCouplings (Tb.stepParameters y) β k ^ (-(((2 * q : ℕ) : ℝ) + 1) / 2 + 2 / 1000) ≤ flowCouplings (Tb.stepParameters y) β k ^ (-(q : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hx1
      push_cast
      linarith
    have e6 : Cm * flowCouplings (Tb.stepParameters y) β k ^ (-(((2 * q : ℕ) : ℝ) + 1) / 2 + 2 / 1000) ≤ |Cm| * flowCouplings (Tb.stepParameters y) β k ^ (-(q : ℝ)) := by
      refine (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hx0.le _)).trans ?_
      exact mul_le_mul_of_nonneg_left e2 (abs_nonneg _)
    have h8 := le_of_abs_sub_pairing_le (((2 * q).factorial : ℝ) * b ^ (2 * q)) h6
      (key _ (fun i j => by
        rw [if_pos rfl, hb2]
        exact (hcov i j rfl).trans (le_abs_self _)))
      (Real.rpow_nonneg hx0.le _)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h8
    have h9 : ∫ u, componentPower Tb y T β k N q z (z, μ, ν) e u ∂(markedSampleLaw T β (k + localChainDepth (Tb.stepParameters y) β k + localChainDepth (Tb.stepParameters y) β k) N) ≤
        flowCouplings (Tb.stepParameters y) β k ^ (-((2 * q : ℕ) : ℝ) / 2) * (((2 * q).factorial : ℝ) * b ^ (2 * q)) +
          Cm * flowCouplings (Tb.stepParameters y) β k ^ (-(((2 * q : ℕ) : ℝ) + 1) / 2 + 2 / 1000) := h8
    rw [e1] at h9
    refine h9.trans ?_
    simp only [hPq]
    nlinarith
  have hbad : markedSampleLaw T β (k + localChainDepth (Tb.stepParameters y) β k + localChainDepth (Tb.stepParameters y) β k) N ((localEvent Tb y T β k N z)ᶜ ∪
        {u | u ∈ localEvent Tb y T β k N z ∧ ¬ SmallAlongAt Tb y T β k N (flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 4 : ℝ))) u z}) ≤
      ENNReal.ofReal (Cb * flowCouplings (Tb.stepParameters y) β k ^ (-(q : ℝ))) := by
    have b1 := hl' T β k (w + 1) N 1 z hN ll
    have b2 := hn' T β k N 1 z ln hLN
    have c1 : markedSampleLaw T β (k + localChainDepth (Tb.stepParameters y) β k + localChainDepth (Tb.stepParameters y) β k) N (localEvent Tb y T β k N z)ᶜ ≤
        ENNReal.ofReal (Real.exp (-(cl * flowCouplings (Tb.stepParameters y) β k))) := by
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal b1
    have c2 : markedSampleLaw T β (k + localChainDepth (Tb.stepParameters y) β k + localChainDepth (Tb.stepParameters y) β k) N
        {u | u ∈ localEvent Tb y T β k N z ∧ ¬ SmallAlongAt Tb y T β k N (flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 4 : ℝ))) u z} ≤
        ENNReal.ofReal (Cn * flowCouplings (Tb.stepParameters y) β k ^ (-(q : ℝ))) := by
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal b2
    refine (measure_union_le _ _).trans ((add_le_add c1 c2).trans ?_)
    have d1 : ENNReal.ofReal (Real.exp (-(cl * flowCouplings (Tb.stepParameters y) β k))) ≤ ENNReal.ofReal (flowCouplings (Tb.stepParameters y) β k ^ (-(q : ℝ))) :=
      ENNReal.ofReal_le_ofReal hexp2
    have d2 : ENNReal.ofReal (Cn * flowCouplings (Tb.stepParameters y) β k ^ (-(q : ℝ))) ≤
        ENNReal.ofReal (|Cn| * flowCouplings (Tb.stepParameters y) β k ^ (-(q : ℝ))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)
    refine (add_le_add d1 d2).trans ?_
    rw [← ENNReal.ofReal_add hX0 (mul_nonneg (abs_nonneg _) hX0)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    simp only [hCb]
    ring
  have hclose := hd' T β k N 1 (flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 4 : ℝ))) z ld hLN (Real.rpow_nonneg hx0.le _) le_rfl
  exact moment_bound_fixed Tb y T β k N q z μ ν hμν hF hJ hloc.cutoff hloc.measurable hlaw hprob hx1 Cd cd hexp Pq Cb hPq0 hCb0
    hint hI hbad hclose
end MomentBounds
private theorem holdsOnParameters_and {P Q : ParameterAssignment → ℝ → Prop} (hP : HoldsOnParameterFamilies P) (hQ : HoldsOnParameterFamilies Q) :
    HoldsOnParameterFamilies fun T y => P T y ∧ Q T y := by apply _root_.YangMills.SharedProofs.p24215 <;> assumption
private theorem holdsOnParameters_admissible : HoldsOnParameterFamilies fun T _ => T.Admissible := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ T _ _ hD _ _ _ _
  exact ⟨0, fun _ _ _ _ => hD⟩
private theorem holdsOnParameters_mono {P Q : ParameterAssignment → ℝ → Prop} (hP : HoldsOnParameterFamilies P) (h : ∀ T y, P T y → Q T y) : HoldsOnParameterFamilies Q := by apply _root_.YangMills.SharedProofs.p25084 <;> assumption
private theorem forAllParameters_of {P : ParameterAssignment → ℝ → Prop} {Q R : MomentParameters → Prop} (hP : HoldsOnParameterFamilies P) (hQ : ForAllParameters Q)
    (hR : ∀ Λ : MomentParameters, Λ.floor ≤ (Λ.g ^ 2)⁻¹ → P Λ.table Λ.floor → Q Λ → R Λ) : ForAllParameters R := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, h₁, k₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂, h₂, k₂⟩ := hQ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (h₁ c) (h₂ c), ?_⟩
  intro L hodd hL Tb hTa hTL hD hC hH hrt hCd Kr hKr
  obtain ⟨y₁, m₁⟩ := k₁ L hodd (le_trans (le_max_left _ _) hL) Tb hTa hTL hD hC hH (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hCd)
  obtain ⟨y₂, m₂⟩ := k₂ L hodd (le_trans (le_max_right _ _) hL) Tb hTa hTL hD hC hH (hrt.trans (min_le_right _ _))
    ((le_max_right _ _).trans hCd) Kr hKr
  refine ⟨max y₁ y₂, fun y hy hRr hW g hg hyg k _ hk2 hk8 R d hd => ?_⟩
  exact hR ⟨Tb, Kr, y, g, k, R, d⟩ hyg (m₁ y ((le_max_left _ _).trans hy) hRr hW)
    (m₂ y ((le_max_right _ _).trans hy) hRr hW g hg hyg k hk2 hk8 R d hd)
private def WindowHoldsAt (Λ : MomentParameters) (C : ℕ → ℝ) (_c X₀ : ℝ) (S : MomentPoint Λ) : Prop :=
  X₀ ≤ S.scaleCoupling →
    (Λ.stepParams.side : ℝ) ^ (-(S.logIndex : ℝ) / 4) ≤ S.scaleCoupling⁻¹ ∧ (2 : ℝ) ^ (-(S.logIndex : ℝ)) ≤ S.scaleCoupling ^ (-(1 / 2) : ℝ) ∧ 3 ≤ S.logIndex ∧
    (S.scaleCoupling - couplingWindowTop Λ.stepParams Λ.g) / (2 * Λ.stepParams.B) ≤ (S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ) ∧
    4 * (S.logIndex : ℝ) ≤ (S.scaleCoupling - couplingWindowTop Λ.stepParams Λ.g) / (2 * Λ.stepParams.B) ∧ S.lastSeparated + 2 * S.logIndex + 3 ≤ S.data.windowLevel ∧
    ∀ u, S.lastSeparated ≤ u → u ≤ S.lastSeparated + 2 * S.logIndex + 3 → |S.coupling u - S.scaleCoupling| ≤ C 0 * Real.log S.scaleCoupling ∧ Λ.stepParams.side ^ S.logIndex ≤ S.levelSide u
private def MomentBoundAt (Λ : MomentParameters) (C : ℕ → ℝ) (_c X₀ : ℝ) (S : MomentPoint Λ) : Prop :=
  X₀ ≤ S.scaleCoupling →
    ∀ (u d n : ℕ) [NeZero n], S.lastSeparated ≤ u → u ≤ S.lastSeparated + S.logIndex + 2 → u + d = S.lastSeparated + 2 * S.logIndex + 3 → n = S.levelSide (u + d) →
      ∀ p : OrientedPlaquette (fineSide Λ.stepParams.side d n), (TorusFields.supDist p.1.1 (S.originSite u (fineSide Λ.stepParams.side d n)) : ℝ) ≤ 4 * (S.range : ℝ) ^ 2 →
      ∀ q : ℕ, 1 ≤ q →
        ∫⁻ w, Set.indicator {w | S.NoLumpNear u ((S.range : ℝ) ^ 3) d n w}
            (fun w => ENNReal.ofReal (curvature (topField Λ.stepParams u (fineSide Λ.stepParams.side d n) (sampleBelow Λ.stepParams u d n w))
              p.1.1 p.1.2.1 p.1.2.2 ^ (2 * q))) w ∂(S.law (u + d) n) ≤
          ENNReal.ofReal (C q * S.scaleCoupling ^ (-(q : ℝ)))
private theorem stageOnFlow_of {Λ : MomentParameters} (S : MomentPoint Λ) (j : ℕ) (hj : j ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β j ⟨S.tower.stage j, S.resp j⟩ := by apply _root_.YangMills.SharedProofs.p6811 <;> assumption
private theorem moment_bound_at_parameters (Λ : MomentParameters) (hy : Λ.floor ≤ (Λ.g ^ 2)⁻¹) (hB : 1 ≤ Λ.table.B) (hm : LevelMomentsAt Λ.table Λ.floor)
    (hn : nearIdentityAlongChainAt Λ.table Λ.floor) (hd : curvatureNearDescendedFormAt Λ.table Λ.floor) (hl : LocalEventLikelyAt Λ.table Λ.floor)
    (hF : Λ.stepParams.Admissible) (hJ : 11 * 2 ^ 12 * Λ.stepParams.baseDepth < Λ.stepParams.side) (hlaw : sampleBelowLawStatement)
    (hprob : forgetLastStepStatement) (hpair : matchingSumPropertiesStatement)
    (hw : ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, WindowHoldsAt Λ C c X₀ S) :
    ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, MomentBoundAt Λ C c X₀ S := by
  obtain ⟨Cw, cw, Xw, hcw, hyXw, hW⟩ := hw
  have hBl : Λ.stepParams.B = Λ.table.B := rfl
  have hBp : 0 < 2 * Λ.stepParams.B := by rw [hBl]; linarith
  obtain ⟨Xr, hXr⟩ := eventually_room (2 * Λ.stepParams.B) (couplingWindowTop Λ.stepParams Λ.g) (Cw 0) hBp
  choose A xq hA hcore using fun q => moment_bound_at_level Λ.table Λ.floor hm hn hd hl hF hJ hlaw hprob hpair q
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, X₀ = max (max Xw Xr) Λ.floor := ⟨_, rfl⟩
  obtain ⟨Xq, hXq⟩ : ∃ Xq : ℕ → ℝ, Xq = fun q => max X₀ (max 1 (2 * xq q)) := ⟨_, rfl⟩
  refine ⟨fun q => max (A q * 2 ^ q) (4 ^ q * Xq q ^ q), 1, X₀, one_pos, ?_, ?_⟩
  · rw [hX₀]; exact le_max_right _ _
  intro S hS u d n _ hu1 hu2 hud hn' p _ q _
  have hXw : Xw ≤ S.scaleCoupling := by
    have : Xw ≤ X₀ := by rw [hX₀]; exact (le_max_left _ _).trans (le_max_left _ _)
    exact this.trans hS
  have hXrx : Xr ≤ S.scaleCoupling := by
    have : Xr ≤ X₀ := by rw [hX₀]; exact (le_max_right _ _).trans (le_max_left _ _)
    exact this.trans hS
  obtain ⟨hx2, hlogb, hroomx⟩ := hXr S.scaleCoupling hXrx
  have hx0 : 0 < S.scaleCoupling := by linarith
  have hu' := (hlaw Λ.stepParams hF hJ S.tower S.isCutoff S.marksMeasurable S.β (fun _ => 0)).1 u d n
  have hPu : IsProbabilityMeasure (markedSampleLaw S.tower S.β u (fineSide Λ.stepParams.side d n)) :=
    (hprob Λ.stepParams hF hJ S.tower S.isCutoff S.marksMeasurable S.β u (fineSide Λ.stepParams.side d n)).1
  have hfm : Measurable fun v : MarkedSample Λ.stepParams u (fineSide Λ.stepParams.side d n) =>
      ENNReal.ofReal (curvature (topField Λ.stepParams u (fineSide Λ.stepParams.side d n) v) p.1.1 p.1.2.1 p.1.2.2 ^ (2 * q)) :=
    ENNReal.measurable_ofReal.comp
      (((continuous_curvature p.1.1 p.1.2.1 p.1.2.2).measurable.comp (measurable_topField Λ.stepParams u _)).pow_const _)
  have hq0 : ∀ z : ℝ, 0 < z → z ^ (-(q : ℝ)) = (z ^ q)⁻¹ := fun z hz => by
    rw [Real.rpow_neg hz.le, Real.rpow_natCast]
  refine le_trans (b := ∫⁻ v, ENNReal.ofReal (curvature (topField Λ.stepParams u (fineSide Λ.stepParams.side d n) v) p.1.1 p.1.2.1 p.1.2.2 ^ (2 * q))
    ∂(markedSampleLaw S.tower S.β u (fineSide Λ.stepParams.side d n))) ?_ ?_
  · rw [← hu'.2, lintegral_map hfm hu'.1]
    exact lintegral_mono fun w => Set.indicator_le_self _ _ w
  by_cases hbig : Xq q ≤ S.scaleCoupling
  · have hxq : 2 * xq q ≤ S.scaleCoupling := by
      have : 2 * xq q ≤ Xq q := by
        rw [hXq]
        exact (le_max_right _ _).trans (le_max_right _ _)
      exact this.trans hbig
    obtain ⟨-, -, -, hKs, -, htK, hcl⟩ := hW S hXw
    have ht : S.lastSeparated ≤ S.data.scaleLevel := by
      classical
      unfold MomentPoint.lastSeparated
      exact Nat.findGreatest_le _
    have hu3 : u ≤ S.lastSeparated + 2 * S.logIndex + 3 := by omega
    obtain ⟨habs, -⟩ := hcl u hu1 hu3
    have hxu := abs_le.mp habs
    have hxu1 : S.scaleCoupling / 2 ≤ S.coupling u := by linarith [hxu.1]
    have hxu2 : S.coupling u ≤ 2 * S.scaleCoupling := by linarith [hxu.2]
    have hxu0 : 1 ≤ S.coupling u := by linarith
    obtain ⟨M, hMdef⟩ : ∃ M, M = localChainDepth Λ.stepParams S.β u := ⟨_, rfl⟩
    have hMr : (M : ℝ) ≤ Real.log (2 * S.scaleCoupling) ^ 2 := by
      rw [hMdef]
      exact (Nat.floor_le (sq_nonneg _)).trans
        (pow_le_pow_left₀ (Real.log_nonneg hxu0) (Real.log_le_log (by linarith) hxu2) 2)
    have hlog0 : 0 ≤ Real.log S.scaleCoupling := Real.log_nonneg (by linarith)
    have hN₀ : (S.logIndex : ℝ) ≤ 4 * Real.log S.scaleCoupling + 1 :=
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * Real.log S.scaleCoupling)).le
    obtain ⟨Wd, hWd⟩ : ∃ Wd : ℝ, Wd = 2 ^ 10 * (2 * S.scaleCoupling) ^ ((1 : ℝ) / 20) := ⟨_, rfl⟩
    rw [← hWd] at hroomx
    have hreal : (u : ℝ) + 2 * M + Wd + 1 ≤ S.data.windowLevel := by
      have a1 : (u : ℝ) ≤ S.data.scaleLevel + S.logIndex + 2 := by exact_mod_cast (by omega : u ≤ S.data.scaleLevel + S.logIndex + 2)
      linarith
    have hWd0 : 0 ≤ Wd := by
      rw [hWd]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _)
    have hK : u + 2 * M + 1 ≤ S.data.windowLevel := by
      have : ((u + 2 * M + 1 : ℕ) : ℝ) ≤ S.data.windowLevel := by
        push_cast
        linarith
      exact_mod_cast this
    obtain ⟨E, hE⟩ : ∃ E, S.data.windowLevel = u + 2 * M + (E + 1) := ⟨S.data.windowLevel - (u + 2 * M) - 1, by omega⟩
    have hEr : Wd ≤ (E : ℝ) + 1 := by
      have : (S.data.windowLevel : ℝ) = u + 2 * M + (E + 1) := by exact_mod_cast hE
      linarith
    have hNv : S.levelSide (u + 2 * M) = 2 * Λ.stepParams.side ^ (S.data.sideExponent + E + 1) := by
      show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (u + 2 * M)) = _
      have : S.data.windowLevel - (u + 2 * M) = E + 1 := by omega
      rw [this]
      simp only [LevelData.period]
      ring
    have hmside : fineSide Λ.stepParams.side d n = fineSide Λ.stepParams.side M (fineSide Λ.stepParams.side M (S.levelSide (u + 2 * M))) := by
      rw [fineSide_eq, fineSide_eq, fineSide_eq, hn']
      show (S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (u + d))) * Λ.stepParams.side ^ d =
        (S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - (u + 2 * M))) * Λ.stepParams.side ^ M * Λ.stepParams.side ^ M
      have a1 : S.data.windowLevel - (u + 2 * M) = E + 1 := by omega
      have a2 : (S.data.windowLevel - (u + d)) + d = (E + 1) + M + M := by omega
      have a3 : Λ.stepParams.side ^ (S.data.windowLevel - (u + d)) * Λ.stepParams.side ^ d = Λ.stepParams.side ^ (E + 1) * Λ.stepParams.side ^ M * Λ.stepParams.side ^ M := by
        rw [← pow_add, a2, pow_add, pow_add]
      rw [a1, mul_assoc, a3]
      ring
    have hL2 : 2 ≤ Λ.stepParams.side := S.tower.two_le_side
    have hNbig : (E : ℝ) + 1 ≤ (S.levelSide (u + 2 * M) : ℝ) := by
      have n1 : E + 1 < 2 ^ (E + 1) := Nat.lt_two_pow_self
      have n2 : 2 ^ (E + 1) ≤ Λ.stepParams.side ^ (E + 1) := Nat.pow_le_pow_left hL2 _
      have n3 : Λ.stepParams.side ^ (E + 1) ≤ Λ.stepParams.side ^ (S.data.sideExponent + E + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have n4 : E + 1 ≤ S.levelSide (u + 2 * M) := by
        rw [hNv]
        omega
      exact_mod_cast n4
    subst hMdef
    have hstand : IsTowerAtParameters Λ.table Λ.floor S.tower S.β (u + 2 * localChainDepth Λ.stepParams S.β u) :=
      ⟨S.startsAtWilson, fun j hj => (stageOnFlow_of S j (by omega)).coupling_eq, fun j hj => (stageOnFlow_of S j (by omega)).onFamily.onFamily⟩
    have hloc : IsLocalChainAbove Λ.table Λ.floor S.tower S.β u (S.levelSide (u + 2 * localChainDepth Λ.stepParams S.β u)) 1 (xq q) := by
      refine ⟨?_, ?_, hstand, S.isCutoff, S.marksMeasurable, ?_, le_rfl, ?_⟩
      · show xq q ≤ S.coupling u
        linarith
      · intro j hj
        have hjK : j < S.data.windowLevel := by
          have : j ≤ u + 2 * localChainDepth Λ.stepParams S.β u := hj
          omega
        have h1 := S.passage.2 j hjK
        have h2 : Λ.stepParams.y₁ = Λ.floor := rfl
        have h3 : couplingWindowTop Λ.stepParams Λ.g = (Λ.g ^ 2)⁻¹ + 2 * Λ.stepParams.B := rfl
        rw [h2]
        linarith
      · have r1 : localBoxRadius (S.coupling u) ≤ (2 * S.scaleCoupling) ^ ((1 : ℝ) / 20) := by
          have : localBoxRadius (S.coupling u) ≤ S.coupling u ^ ((1 : ℝ) / 20) := Nat.floor_le (Real.rpow_nonneg (by linarith) _)
          exact this.trans (Real.rpow_le_rpow (by linarith) hxu2 (by norm_num))
        have r2 : (2 : ℝ) ^ 10 * localBoxRadius (S.coupling u) ≤ Wd := by
          rw [hWd]
          exact mul_le_mul_of_nonneg_left r1 (by positivity)
        exact r2.trans (hEr.trans hNbig)
      · exact Real.one_le_rpow hxu0 (by norm_num)
    have hcl2 := hcore q S.tower S.β u (S.levelSide (u + 2 * localChainDepth Λ.stepParams S.β u)) (S.data.sideExponent + E) (fineSide Λ.stepParams.side d n) hNv hloc hmside
      p.1.1 p.1.2.1 p.1.2.2 p.2
    refine hcl2.trans (ENNReal.ofReal_le_ofReal ?_)
    show A q * S.coupling u ^ (-(q : ℝ)) ≤ max (A q * 2 ^ q) (4 ^ q * Xq q ^ q) * S.scaleCoupling ^ (-(q : ℝ))
    have hxu00 : 0 < S.coupling u := by linarith
    rw [hq0 _ hxu00, hq0 _ hx0]
    have c1 : (S.coupling u ^ q)⁻¹ ≤ 2 ^ q * (S.scaleCoupling ^ q)⁻¹ := by
      have h1 : (S.scaleCoupling / 2) ^ q ≤ S.coupling u ^ q := pow_le_pow_left₀ (by positivity) hxu1 q
      have h2 := inv_anti₀ (by positivity) h1
      refine h2.trans (le_of_eq ?_)
      rw [div_pow, inv_div, div_eq_mul_inv]
    have c2 : A q * 2 ^ q ≤ max (A q * 2 ^ q) (4 ^ q * Xq q ^ q) := le_max_left _ _
    have c3 : 0 ≤ (S.scaleCoupling ^ q)⁻¹ := by positivity
    calc A q * (S.coupling u ^ q)⁻¹ ≤ A q * (2 ^ q * (S.scaleCoupling ^ q)⁻¹) := mul_le_mul_of_nonneg_left c1 (hA q)
      _ = (A q * 2 ^ q) * (S.scaleCoupling ^ q)⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right c2 c3
  · have hlt : S.scaleCoupling < Xq q := not_le.mp hbig
    calc ∫⁻ v, ENNReal.ofReal (curvature (topField Λ.stepParams u (fineSide Λ.stepParams.side d n) v) p.1.1 p.1.2.1 p.1.2.2 ^ (2 * q))
          ∂(markedSampleLaw S.tower S.β u (fineSide Λ.stepParams.side d n))
        ≤ ∫⁻ _, ENNReal.ofReal (4 ^ q) ∂(markedSampleLaw S.tower S.β u (fineSide Λ.stepParams.side d n)) :=
          lintegral_mono fun v => ENNReal.ofReal_le_ofReal (curvature_pow_le _ _ _ _ _)
      _ = ENNReal.ofReal (4 ^ q) := by simp
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        show (4 : ℝ) ^ q ≤ max (A q * 2 ^ q) (4 ^ q * Xq q ^ q) * S.scaleCoupling ^ (-(q : ℝ))
        rw [hq0 _ hx0]
        have c1 : (4 : ℝ) ^ q * Xq q ^ q ≤ max (A q * 2 ^ q) (4 ^ q * Xq q ^ q) := le_max_right _ _
        have c2 : S.scaleCoupling ^ q ≤ Xq q ^ q := pow_le_pow_left₀ hx0.le hlt.le q
        have c3 : 0 < S.scaleCoupling ^ q := by positivity
        have c4 : 1 ≤ Xq q ^ q * (S.scaleCoupling ^ q)⁻¹ := by
          rw [← div_eq_mul_inv, one_le_div c3]
          exact c2
        have c5 : (0 : ℝ) ≤ 4 ^ q := by positivity
        calc (4 : ℝ) ^ q = 4 ^ q * 1 := (mul_one _).symm
          _ ≤ 4 ^ q * (Xq q ^ q * (S.scaleCoupling ^ q)⁻¹) := mul_le_mul_of_nonneg_left c4 c5
          _ = (4 ^ q * Xq q ^ q) * (S.scaleCoupling ^ q)⁻¹ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right c1 (by positivity)
theorem curvatureMomentsNearPoint_proof (h₁ : levelCurvatureMomentsStatement) (h₂ : nearIdentityAlongChainStatement)
    (h₃ : curvatureNearDescendedFormStatement) (h₄ : localEventLikelyStatement)
    (h₅ : scaleWindowStatement) (h₆ : sampleBelowLawStatement) (h₇ : forgetLastStepStatement)
    (h₈ : TowerAlongFlowStatement) (h₉ : matchingSumPropertiesStatement) :
    curvatureMomentsNearPointStatement := by
  have t₁ : HoldsOnParameterFamilies LevelMomentsAt := h₁
  have t₂ : HoldsOnParameterFamilies nearIdentityAlongChainAt := h₂
  have t₃ : HoldsOnParameterFamilies curvatureNearDescendedFormAt := h₃
  have t₄ : HoldsOnParameterFamilies LocalEventLikelyAt := h₄
  have t₈ : HoldsOnParameterFamilies fun T y => (T.stepParameters y).Admissible ∧ 11 * 2 ^ 12 * (T.stepParameters y).baseDepth < (T.stepParameters y).side :=
    holdsOnParameters_mono h₈ fun _ _ h => ⟨h.1, h.2.1⟩
  have hT := holdsOnParameters_and (holdsOnParameters_and (holdsOnParameters_and t₁ t₂) (holdsOnParameters_and t₃ t₄)) (holdsOnParameters_and t₈ holdsOnParameters_admissible)
  exact forAllParameters_of (Q := fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, WindowHoldsAt Λ C c X₀ S)
    (R := fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, MomentBoundAt Λ C c X₀ S) hT h₅
    (fun Λ hy hP hQ => moment_bound_at_parameters Λ hy hP.2.2.B_ge hP.1.1.1 hP.1.1.2 hP.1.2.1 hP.1.2.2 hP.2.1.1 hP.2.1.2 h₆ h₇ h₉ hQ)
end MomentLaw
end YangMills.Construction
end
