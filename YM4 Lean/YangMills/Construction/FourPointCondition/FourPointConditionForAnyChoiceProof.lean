import YangMills.Construction.FourPointCondition.ConditionsOfTheRatioAtAnObservable
import YangMills.Construction.FourPointCondition.ConnectedLawOfACollinearQuadruple
import YangMills.Construction.FourPointCondition.FourPointConditionForAnyChoice
import YangMills.Construction.FourPointCondition.PairAtScaleOneOfAQuadruple
import YangMills.Construction.FourPointCondition.RatioOfTheLaws
import YangMills.Construction.Torus.RescalingLiftsAndFunctionNorms
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
private theorem amplitudeConstant_eq :
    TwoPointFunction.amplitudeConstant = 9 / Real.pi ^ 4 := by
  unfold TwoPointFunction.amplitudeConstant
  norm_num [ParameterChoice.colorNumber]
private theorem gaugeGroupDim_eq : gaugeGroupDim = 3 := by
  unfold gaugeGroupDim
  norm_num [ParameterChoice.colorNumber]
private theorem uniformNorm_pos_of_lipschitz {S : ℝ} (hS : 0 < S) {f : TorusMetric.Torus4 S → ℝ}
    (hf : TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus f) (hne : ∃ y, f y ≠ 0) :
    0 < TestFunctions.uniformNorm f := by
  have : Fact (0 < S) := ⟨hS⟩
  obtain ⟨C, hC0, hC⟩ := hf
  obtain ⟨y, hy⟩ := hne
  have hcoord : ∀ z : TorusMetric.Torus4 S, ‖z‖ ≤ S / 2 := by
    intro z
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => ?_
    have := AddCircle.norm_le_half_period S (x := z μ) hS.ne'
    rwa [abs_of_pos hS] at this
  have hbdd : BddAbove (range fun x => ‖f x‖) := by
    refine ⟨‖f y‖ + C * S, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h1 : TestFunctions.euclidDistTorus x y ≤ S := by
      have h2 := TorusAnalysis.torusEuclidNorm_le_two_mul_pi_norm (x - y)
      have h3 := hcoord (x - y)
      exact h2.trans (by linarith)
    have h4 := hC x y
    have h5 : ‖f x‖ ≤ ‖f y‖ + ‖f x - f y‖ := norm_le_insert' _ _
    have h6 : C * TestFunctions.euclidDistTorus x y ≤ C * S := mul_le_mul_of_nonneg_left h1 hC0
    show ‖f x‖ ≤ _
    linarith
  exact lt_of_lt_of_le (norm_pos_iff.2 hy) (le_ciSup hbdd y)
private theorem cumulant_bounds_arith {Λ P σ r X g vt : ℝ} (hX : 0 < X) (hg : 0 < g) (hP : 0 < P)
    (hvt : 0 < vt)
    (h1 : 2 / 9 * X * g ^ 4 ≤ σ) (h2 : σ ≤ 8 / 3 * X * g ^ 4)
    (hlo : 8 / 25 * Λ ≤ r * X ^ 2 / σ ^ 2) (hhi : r * X ^ 2 / σ ^ 2 ≤ 8 / 3 * Λ)
    (hΛ1 : 27 * Real.pi ^ (-8 : ℤ) * (25 / 4 : ℝ) ^ (-16 : ℤ) * vt ^ 4 * P ≤ Λ)
    (hΛ2 : Λ ≤ 54 * Real.pi ^ (-8 : ℤ) * TorusMeasure.omega4 ^ 4 * (16 : ℝ) ^ (-16 : ℤ) * P) :
    0 < r ∧ fourPointLowerConst vt * gaugeGroupDim * g ^ 8 * P ≤ r ∧
      r ≤ fourPointUpperConst * gaugeGroupDim * g ^ 8 * P := by
  have hσ : 0 < σ := lt_of_lt_of_le (by positivity) h1
  set Q : ℝ := Real.pi ^ (-8 : ℤ) * (25 / 4 : ℝ) ^ (-16 : ℤ) with hQ
  have hQ0 : 0 < Q := by positivity
  set W : ℝ := (16 : ℝ) ^ (-16 : ℤ) with hW
  have hΛ0 : 0 < Λ := by
    have : 0 < 27 * Real.pi ^ (-8 : ℤ) * (25 / 4 : ℝ) ^ (-16 : ℤ) * vt ^ 4 * P := by positivity
    linarith
  have hΛ1' : 27 * Q * vt ^ 4 * P ≤ Λ := by
    calc 27 * Q * vt ^ 4 * P = 27 * Real.pi ^ (-8 : ℤ) * (25 / 4 : ℝ) ^ (-16 : ℤ) * vt ^ 4 * P := by
          rw [hQ]; ring
      _ ≤ Λ := hΛ1
  have hΛ2' : Λ ≤ 54 / 16 * W * P := by
    have e : Real.pi ^ (-8 : ℤ) * TorusMeasure.omega4 ^ 4 = 1 / 16 := by
      unfold TorusMeasure.omega4
      rw [zpow_neg]
      have : Real.pi ^ (8 : ℤ) = Real.pi ^ (8 : ℕ) := by norm_cast
      rw [this]
      field_simp
      norm_num
    calc Λ ≤ 54 * Real.pi ^ (-8 : ℤ) * TorusMeasure.omega4 ^ 4 * W * P := hΛ2
      _ = 54 * (Real.pi ^ (-8 : ℤ) * TorusMeasure.omega4 ^ 4) * W * P := by ring
      _ = 54 / 16 * W * P := by rw [e]; ring
  set G := g ^ 4 with hG
  have hg8 : g ^ 8 = G ^ 2 := by rw [hG]; ring
  set e := σ / X with he
  have he0 : 0 < e := by positivity
  have he1 : 2 / 9 * G ≤ e := by
    rw [he, le_div_iff₀ hX]
    linarith
  have he2 : e ≤ 8 / 3 * G := by
    rw [he, div_le_iff₀ hX]
    linarith
  set t := r * X ^ 2 / σ ^ 2 with ht
  have hr : r = t * e ^ 2 := by
    rw [ht, he]
    field_simp
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) hlo
  have hsq1 : (2 / 9 * G) ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ (by positivity) he1 2
  have hsq2 : e ^ 2 ≤ (8 / 3 * G) ^ 2 := pow_le_pow_left₀ he0.le he2 2
  have hlow : 8 / 25 * Λ * (2 / 9 * G) ^ 2 ≤ r := by
    rw [hr]
    exact mul_le_mul hlo hsq1 (by positivity) ht0.le
  have hup : r ≤ 8 / 3 * Λ * (8 / 3 * G) ^ 2 := by
    rw [hr]
    exact mul_le_mul hhi hsq2 (by positivity) (by positivity)
  have hmin0 : 0 < min vt (TorusMeasure.omega4 * (16 : ℝ) ^ (-4 : ℤ)) := by
    refine lt_min hvt ?_
    unfold TorusMeasure.omega4
    positivity
  have hmin4 : min vt (TorusMeasure.omega4 * (16 : ℝ) ^ (-4 : ℤ)) ^ 4 ≤ vt ^ 4 :=
    pow_le_pow_left₀ hmin0.le (min_le_left _ _) 4
  set μ := min vt (TorusMeasure.omega4 * (16 : ℝ) ^ (-4 : ℤ)) ^ 4 with hμ
  have hfl : fourPointLowerConst vt = 32 / 225 * Q * μ := by
    unfold fourPointLowerConst
    rw [hμ, hQ]
    ring
  have hce : fourPointUpperConst = 64 / 3 * W := rfl
  have hfl3 : 32 / 225 * Q * μ * 3 * P ≤ 32 / 2025 * Λ := by
    have h3 : Q * μ * P ≤ Q * vt ^ 4 * P :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin4 hQ0.le) hP.le
    nlinarith
  have hlowD : fourPointLowerConst vt * gaugeGroupDim * g ^ 8 * P ≤ r := by
    rw [hfl, gaugeGroupDim_eq, hg8]
    calc 32 / 225 * Q * μ * 3 * G ^ 2 * P = (32 / 225 * Q * μ * 3 * P) * G ^ 2 := by ring
      _ ≤ (32 / 2025 * Λ) * G ^ 2 := mul_le_mul_of_nonneg_right hfl3 (by positivity)
      _ = 8 / 25 * Λ * (2 / 9 * G) ^ 2 := by ring
      _ ≤ r := hlow
  refine ⟨?_, hlowD, ?_⟩
  · have hpos : 0 < fourPointLowerConst vt * gaugeGroupDim * g ^ 8 * P := by
      rw [hfl, gaugeGroupDim_eq]
      have : 0 < μ := by rw [hμ]; positivity
      positivity
    linarith
  · rw [hce, gaugeGroupDim_eq, hg8]
    calc r ≤ 8 / 3 * Λ * (8 / 3 * G) ^ 2 := hup
      _ = (512 / 27 * Λ) * G ^ 2 := by ring
      _ ≤ (512 / 27 * (54 / 16 * W * P)) * G ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith
      _ = 64 / 3 * W * 3 * G ^ 2 * P := by ring
private theorem fourPointBound_of_ratio (hQ : gaussianFourPointCollinear)
    (hC : ratioConditionsEventually) (hP : FourPointBounds.UnitScalePairOfQuadruple)
    (ℓ : TorusLumps.StepParameters) (hadm : ℓ.Admissible) (hratio : cumulantRatioAt ℓ) {vt : ℝ}
    (hvt0 : 0 < vt) (hvt1 : vt ≤ 1)
    (R : CouplingEvaluation) {lam Ca d₀ : ℝ} {n₀ : ℕ} (hl : EvaluationLaws R ℓ.side vt lam Ca d₀ n₀) :
    ∃ d₄ ∈ Ioc (0 : ℝ) d₀, FourPointConditionHolds R ℓ.side vt d₄ n₀ := by
  have hd₀ := hl.d₀_mem
  by_cases hex : ∃ φ ψ : (Fin 4 → ℝ) → ℝ, (φ, ψ) ∈ TestFunctions.separatedPairsR4 1 vt ∧
      TestFunctions.uniformNorm φ = 1 ∧ TestFunctions.uniformNorm ψ = 1
  swap
  · exact ⟨d₀, ⟨hd₀.1, le_rfl⟩, fun s β _ _ d _ _ f hf => (hex (hP s d vt f hf)).elim⟩
  obtain ⟨φ, ψ, hpair, hφ, hψ⟩ := hex
  obtain ⟨βv, nv, δv, -, hδ, hrat⟩ := hratio vt hvt0 hvt1
  obtain ⟨hK, d₄, hd₄, hcond⟩ := hC ℓ vt lam Ca d₀ n₀ R φ ψ βv nv δv hadm hvt0 hvt1 hl hpair hφ hψ hδ
  refine ⟨d₄, hd₄, ?_⟩
  intro s β hsL hdat d hd hdeep f hf
  have c := hcond s.K β hdat d hd hdeep
  obtain ⟨σ, -, hσeq, hall⟩ := hrat s.K β d R.sides φ ψ hl.sides_unbounded hpair hφ hψ
    c.coupling_ge c.sites_ge c.twoPoint_small
  have hvol : Real.exp (Real.log (1 / σ) ^ 3) ≤ PeriodicLattice.torusSide s.L s.m / d := by
    rw [hsL]
    exact c.torus_large σ hσeq s.m
  obtain ⟨r, hr, hlo, hhi⟩ := hall s hsL rfl hvol f hf
  refine ⟨r, hr, ?_⟩
  have hd₀' : d ∈ Ioc (0 : ℝ) d₀ := ⟨hd.1, hd.2.trans hd₄.2⟩
  have hg := hl.coupling_pos s.K β hdat d hd₀' hdeep
  have hσ1 := c.le_twoPoint
  have hσ2 := c.twoPoint_le
  rw [hσeq] at hσ1 hσ2
  have hσ1' := EReal.coe_le_coe_iff.1 hσ1
  have hσ2' := EReal.coe_le_coe_iff.1 hσ2
  rw [amplitudeConstant_eq] at hσ1' hσ2'
  obtain ⟨hq, hL1, hL2⟩ := hQ s d vt f hf
  have hfq := hf.1
  have hside : 0 < PeriodicLattice.torusSide s.L s.m := by
    have := hfq.2.1
    linarith [hfq.1.1]
  have hsup : ∀ i, 0 < TestFunctions.uniformNorm (f i) := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j : Fin 4, i ≠ j := exists_ne i |>.imp fun _ h => h.symm
    obtain ⟨x₁, x₂, hb, -⟩ := hfq.2.2.2 i j hj
    exact uniformNorm_pos_of_lipschitz hside (hfq.2.2.1 i).1 hb.2.2.1
  have hPpos : 0 < ∏ i, TestFunctions.uniformNorm (f i) := Finset.prod_pos fun i _ => hsup i
  have hpi := Real.pi_pos
  have hX : 0 < 9 / Real.pi ^ 4 * TestFunctions.inverseEighthKernel φ ψ := by positivity
  have e1 : 2 / 9 * (9 / Real.pi ^ 4 * TestFunctions.inverseEighthKernel φ ψ) *
      R.coupling s.K β d ^ 4 ≤ σ := by
    calc _ = 2 / 9 * (9 / Real.pi ^ 4) * TestFunctions.inverseEighthKernel φ ψ *
          R.coupling s.K β d ^ 4 := by ring
      _ ≤ σ := hσ1'
  have e2 : σ ≤ 8 / 3 * (9 / Real.pi ^ 4 * TestFunctions.inverseEighthKernel φ ψ) *
      R.coupling s.K β d ^ 4 := by
    calc σ ≤ 8 / 3 * (9 / Real.pi ^ 4) * TestFunctions.inverseEighthKernel φ ψ *
          R.coupling s.K β d ^ 4 := hσ2'
      _ = _ := by ring
  obtain ⟨h0, h1, h2⟩ := cumulant_bounds_arith hX hg hPpos hvt0 e1 e2 hlo hhi hL1 hL2
  exact ⟨h0, h1, h2⟩
theorem fourPointBoundAtEveryProfile_of_cumulantRatio (hR : cumulantRatioStatement)
    (hQ : gaussianFourPointCollinear) (hC : ratioConditionsEventually)
    (hP : FourPointBounds.UnitScalePairOfQuadruple) :
    fourPointBoundAtEveryProfile := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := hR a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hL hL₀ T hTa hTL hD hCS hCH hTr hCd => ?_⟩
  obtain ⟨y₀, Hy⟩ := H L hL hL₀ T hTa hTL hD hCS hCH hTr hCd
  refine ⟨max y₀ T.floorMin, fun y hy hrow hw => ?_⟩
  have hratio := Hy y (le_trans (le_max_left _ _) hy) hrow hw
  have hadm := hD.fits y (le_trans (le_max_right _ _) hy)
  intro vt hvt0 hvt1 R lam Ca d₀ n₀ hlaws
  exact fourPointBound_of_ratio hQ hC hP _ hadm hratio hvt0 hvt1 R hlaws
end YangMills.Construction.FourPointCondition
end
