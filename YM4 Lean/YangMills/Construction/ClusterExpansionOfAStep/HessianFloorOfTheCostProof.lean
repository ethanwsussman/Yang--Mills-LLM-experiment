import YangMills.Construction.ClusterExpansionOfAStep.ExpansionsOfCutsAndMixes
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ClusterExpansionOfAStep
theorem exp_sub_one_le_mul_exp {u : ℝ} : Real.exp u - 1 ≤ u * Real.exp u := by
  have h1 := Real.add_one_le_exp (-u)
  have h2 := Real.exp_pos u
  have h3 : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith
def costRowBound (a δ CA Cm Kf : ℝ) (L : ℕ) : ℝ :=
  Cm ^ 2 * (CA * (8 / δ) * Real.exp 1 * (4 * (2 / (1 - Real.exp (-(δ / 4) / 4))) ^ 4) +
    a * (4 * 13 ^ 4 * Kf) * Real.exp (10 * L) * (2 * (10 * L + 2)) * Real.exp 1 *
      (4 * (2 / (1 - Real.exp (-1 / 4))) ^ 4))
theorem exp_neg_mul_exp_sub_one_le {δ rt : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) (hrt0 : 0 ≤ rt) (hrt : 2 * rt ≤ δ / 2) {D : ℝ} (hD : 0 ≤ D) :
    Real.exp (-δ * D) * (Real.exp (2 * rt * (D + 1)) - 1) ≤ rt * ((8 / δ) * Real.exp 1) * Real.exp (-(δ / 4) * D) := by
  set u := 2 * rt * (D + 1) with hu
  have hu0 : 0 ≤ u := by positivity
  have hE : Real.exp u ≤ Real.exp (δ / 2 * (D + 1)) := by
    apply Real.exp_le_exp.mpr
    rw [hu]
    nlinarith
  have h1 : Real.exp u - 1 ≤ u * Real.exp (δ / 2 * (D + 1)) :=
    exp_sub_one_le_mul_exp.trans (mul_le_mul_of_nonneg_left hE hu0)
  have h2 : D + 1 ≤ (4 / δ) * Real.exp (δ / 4 * (D + 1)) := by
    have h3 := Real.add_one_le_exp (δ / 4 * (D + 1))
    have h4 : δ / 4 * (D + 1) ≤ Real.exp (δ / 4 * (D + 1)) := by linarith
    have h5 : (4 / δ) * (δ / 4 * (D + 1)) = D + 1 := by
      field_simp
    calc D + 1 = (4 / δ) * (δ / 4 * (D + 1)) := h5.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : u ≤ 2 * rt * ((4 / δ) * Real.exp (δ / 4 * (D + 1))) := by
    rw [hu]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hx := Real.exp_pos (-δ * D)
  have hy := Real.exp_pos (δ / 2 * (D + 1))
  have h7 : Real.exp (-δ * D) * (Real.exp u - 1) ≤
      Real.exp (-δ * D) * (2 * rt * ((4 / δ) * Real.exp (δ / 4 * (D + 1))) * Real.exp (δ / 2 * (D + 1))) :=
    mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h6 hy.le)) hx.le
  refine h7.trans ?_
  have h8 : Real.exp (-δ * D) * (2 * rt * ((4 / δ) * Real.exp (δ / 4 * (D + 1))) * Real.exp (δ / 2 * (D + 1))) =
      rt * (8 / δ) * (Real.exp (-δ * D) * Real.exp (δ / 4 * (D + 1)) * Real.exp (δ / 2 * (D + 1))) := by ring
  rw [h8, ← Real.exp_add, ← Real.exp_add]
  have h9 : Real.exp (-δ * D + δ / 4 * (D + 1) + δ / 2 * (D + 1)) ≤ Real.exp 1 * Real.exp (-(δ / 4) * D) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc _ ≤ rt * (8 / δ) * (Real.exp 1 * Real.exp (-(δ / 4) * D)) :=
        mul_le_mul_of_nonneg_left h9 (by positivity)
    _ = _ := by ring
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n] {s : StepSettings.ChartSetting R n} {δ lam σA cg : ℝ} {N : ℕ → ℝ}
variable {CA Cm Kf : ℝ}
theorem sum_costEntryBound_mul_exp_sub_one_le (c : s.ChainContext δ lam σA cg N) (hCA : 0 ≤ CA) (hKf : 0 ≤ Kf) (hCm : 0 ≤ Cm)
    (hrt1 : 2 * R.params.rt ≤ δ / 2) (hrt2 : 2 * R.params.rt * (10 * R.params.side + 2) ≤ 1) (b : s.free) :
    ∑ b' : s.free, costEntryBound s δ CA Cm Kf b b' *
      (Real.exp (2 * R.params.rt * StepSettings.bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) ≤
      R.params.rt * costRowBound R.params.coupling δ CA Cm Kf R.params.side := by
  classical
  have hδ : 0 < δ := c.chain.1
  have hδ8 : δ ≤ 1 / 8 := c.chain.2.1
  have hL := c.params_admissible.L_odd
  have hrt0 : 0 < R.params.rt := c.params_admissible.rt_pos
  have ha : 0 ≤ R.params.coupling := by linarith [c.params_admissible.a_ge]
  set rt := R.params.rt with hrt
  set A := R.params.coupling * (4 * 13 ^ 4 * Kf) with hA
  have hA0 : 0 ≤ A := by positivity
  have hterm : ∀ b' : s.free, costEntryBound s δ CA Cm Kf b b' *
      (Real.exp (2 * rt * StepSettings.bondBlockDist (R := R) (n := n) b.1 b'.1) - 1) ≤
      Cm ^ 2 * (CA * (rt * ((8 / δ) * Real.exp 1) * Real.exp (-(δ / 4) * TorusFields.supDist b.1.1 b'.1.1)) +
        A * Real.exp (10 * R.params.side) * (rt * (2 * (10 * R.params.side + 2))) * Real.exp 1 *
          Real.exp (-1 * TorusFields.supDist b.1.1 b'.1.1)) := by
    intro b'
    set d := TorusFields.supDist b.1.1 b'.1.1 with hd
    set dc := StepSettings.bondBlockDist (R := R) (n := n) b.1 b'.1 with hdc
    have hdcd : dc ≤ d + 1 := TorusBlocks.supDist_parentBlock_le hL b.1.1 b'.1.1
    have hdcR : (dc : ℝ) ≤ (d : ℝ) + 1 := by exact_mod_cast hdcd
    have hg0 : 0 ≤ Real.exp (2 * rt * dc) - 1 := by
      have : (1 : ℝ) ≤ Real.exp (2 * rt * dc) := Real.one_le_exp (by positivity)
      linarith
    have hgD : Real.exp (2 * rt * dc) - 1 ≤ Real.exp (2 * rt * ((d : ℝ) + 1)) - 1 := by
      have : Real.exp (2 * rt * dc) ≤ Real.exp (2 * rt * ((d : ℝ) + 1)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      linarith
    have hp1 : CA * Real.exp (-δ * d) * (Real.exp (2 * rt * dc) - 1) ≤
        CA * (rt * ((8 / δ) * Real.exp 1) * Real.exp (-(δ / 4) * d)) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hCA
      refine le_trans (mul_le_mul_of_nonneg_left hgD (Real.exp_pos _).le) ?_
      exact exp_neg_mul_exp_sub_one_le hδ hδ8 hrt0.le hrt1 (by positivity)
    have hp2 : CostDerivatives.alignmentExpansionBound R.params.side R.params.coupling Kf
          (b : TorusFields.TorusBond (n * R.params.side)) b' * (Real.exp (2 * rt * dc) - 1) ≤
        A * Real.exp (10 * R.params.side) * (rt * (2 * (10 * R.params.side + 2))) * Real.exp 1 * Real.exp (-1 * d) := by
      unfold CostDerivatives.alignmentExpansionBound
      split_ifs with hdl
      · have hdlR : (d : ℝ) ≤ 10 * R.params.side := by exact_mod_cast hdl
        set u := 2 * rt * (10 * (R.params.side : ℝ) + 2) with hu
        have hu1 : u ≤ 1 := hrt2
        have hu0 : 0 ≤ u := by positivity
        have hv : Real.exp (2 * rt * dc) - 1 ≤ u * Real.exp 1 := by
          have h3 : Real.exp (2 * rt * dc) ≤ Real.exp u := by
            apply Real.exp_le_exp.mpr
            rw [hu]
            nlinarith
          have h4 : Real.exp u - 1 ≤ u * Real.exp u := exp_sub_one_le_mul_exp
          have h5 : u * Real.exp u ≤ u * Real.exp 1 :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu1) hu0
          linarith
        have h6 : (1 : ℝ) ≤ Real.exp (10 * R.params.side) * Real.exp (-1 * d) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith)
        have h7 : 0 ≤ A * (u * Real.exp 1) := by positivity
        calc A * (Real.exp (2 * rt * dc) - 1) ≤ A * (u * Real.exp 1) := mul_le_mul_of_nonneg_left hv hA0
          _ ≤ A * (u * Real.exp 1) * (Real.exp (10 * R.params.side) * Real.exp (-1 * d)) := le_mul_of_one_le_right h7 h6
          _ = _ := by
            rw [hu]
            ring
      · rw [zero_mul]
        positivity
    unfold costEntryBound
    by_cases hbb : b = b'
    · subst hbb
      have hz : dc = 0 := by
        rw [hdc]
        unfold StepSettings.bondBlockDist
        exact TorusFields.supDist_self _
      have : Real.exp (2 * rt * dc) - 1 = 0 := by
        rw [hz]
        simp
      rw [this, mul_zero]
      positivity
    · rw [if_neg hbb, add_zero]
      have hC2 : 0 ≤ Cm ^ 2 := by positivity
      calc _ = Cm ^ 2 * (CA * Real.exp (-δ * d) * (Real.exp (2 * rt * dc) - 1) +
            CostDerivatives.alignmentExpansionBound R.params.side R.params.coupling Kf
              (b : TorusFields.TorusBond (n * R.params.side)) b' * (Real.exp (2 * rt * dc) - 1)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hp1 hp2) hC2
  refine (Finset.sum_le_sum fun b' _ => hterm b').trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hK4 := sum_exp_neg_mul_supDist_subtype_le (β := δ / 4) (by positivity) b.1.1 s.free
  have hK1 := sum_exp_neg_mul_supDist_subtype_le (β := 1) one_pos b.1.1 s.free
  have s1 : ∑ b' : s.free, CA * (rt * ((8 / δ) * Real.exp 1) * Real.exp (-(δ / 4) * TorusFields.supDist b.1.1 b'.1.1)) ≤
      CA * (rt * ((8 / δ) * Real.exp 1)) * (4 * (2 / (1 - Real.exp (-(δ / 4) / 4))) ^ 4) := by
    simp only [← Finset.mul_sum]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hK4 (by positivity)
  have s2 : ∑ b' : s.free, A * Real.exp (10 * R.params.side) * (rt * (2 * (10 * R.params.side + 2))) * Real.exp 1 *
      Real.exp (-1 * TorusFields.supDist b.1.1 b'.1.1) ≤
        A * Real.exp (10 * R.params.side) * (rt * (2 * (10 * R.params.side + 2))) * Real.exp 1 *
          (4 * (2 / (1 - Real.exp (-1 / 4))) ^ 4) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hK1 (by positivity)
  have hC2 : 0 ≤ Cm ^ 2 := by positivity
  refine (mul_le_mul_of_nonneg_left (add_le_add s1 s2) hC2).trans (le_of_eq ?_)
  unfold costRowBound
  ring
theorem update_add_smul_eq_add_smul_single (η : StepSettings.FreeCoords s.free) (b : s.free)
    (X : QuaternionLogarithm.ImaginaryCoord) (τ : ℝ) :
    Function.update η b (η b + τ • X) = η + τ • (Pi.single b X : StepSettings.FreeCoords s.free) := by apply _root_.YangMills.Construction.StepSettings.update_add_smul_eq_add_single <;> assumption
theorem mixedSecondDeriv_eq_fderiv_fderiv {u : StepSettings.FreeCoords s.free → ℝ} {η : StepSettings.FreeCoords s.free}
    (hu : ContDiffAt ℝ 2 u η) (b b' : s.free) (X X' : QuaternionLogarithm.ImaginaryCoord) :
    StepSettings.mixedSecondDeriv u η b b' X X' = fderiv ℝ (fderiv ℝ u) η (Pi.single b X) (Pi.single b' X') := by apply _root_.YangMills.Construction.StepSettings.mixedSecondDeriv_eq_fderiv_fderiv <;> assumption
theorem hasCostDecay_of_bounds (hS : StepCosts.SharesSumToAction) (hC : LumpContours.WholeCellCostEqualsMinimalAction)
    (hA : LumpContours.ActionAtLevelIsCutAction) (c : s.ChainContext δ lam σA cg N)
    (hF : CostDerivatives.ActionDerivativeBounds R.params.coupling δ σA CA R.params.side) (hCA : 0 ≤ CA)
    (hK : CostDerivatives.AlignmentDerivativeBounds R.params.side Kf) (hKf : 0 ≤ Kf) (hM : ChartTranslateBounds Cm)
    (hCm : 0 ≤ Cm) {ε : ℝ}
    (hε : 3 * CA * Real.exp 1 * ((R.range : ℝ) + 1) ^ 4 * Real.exp (-δ * R.range / 16) ≤ ε)
    (hfl : ε * (4 * (2 / (1 - Real.exp (-(δ / 4) / 4))) ^ 4 * Cm ^ 2 + Cm) ≤ lam / 2)
    (hrt1 : 2 * R.params.rt ≤ δ / 2) (hrt2 : 2 * R.params.rt * (10 * R.params.side + 2) ≤ 1)
    (hrow : R.params.rt * costRowBound R.params.coupling δ CA Cm Kf R.params.side ≤ lam / 16) :
    s.HasCostDecay lam (Cm ^ 2 * (CA + R.params.coupling * (4 * 13 ^ 4 * Kf)) +
      Cm * (CA + R.params.coupling * (4 * 13 ^ 4 * Kf)) + 1) := by
  classical
  obtain ⟨σ', w, hmin⟩ := c.exists_minimizerData
  have ha : 0 ≤ R.params.coupling := by linarith [c.params_admissible.a_ge]
  have hδ : 0 < δ := c.chain.1
  set A := R.params.coupling * (4 * 13 ^ 4 * Kf) with hAdef
  have hA0 : 0 ≤ A := by positivity
  refine ⟨⟨{η | ContDiffAt ℝ 3 s.costSum η}, ?_, fun η hη => contDiffAt_costSum hS c hF hη,
      fun η hη => ContDiffAt.contDiffWithinAt hη⟩,
    fun η hη v => hessian_costSum_ge hS hC hA c hF hCA hmin hM hη hε hfl v,
    ⟨costEntryBound s δ CA Cm Kf, fun η hη b b' X X' hX hX' => ?_, fun b b' => ?_, fun b => ?_⟩,
    fun η hη b X hX => ?_⟩
  · refine isOpen_iff_mem_nhds.mpr fun η hη => ?_
    exact ContDiffAt.eventually hη (by simp)
  · have h2 : ContDiffAt ℝ 2 s.costSum η := (contDiffAt_costSum hS c hF hη).of_le (by norm_num)
    rw [mixedSecondDeriv_eq_fderiv_fderiv h2]
    exact abs_second_fderiv_costSum_single_le hS c hF hCA hK hKf hmin hM hCm hη b b' X X' hX hX'
  · unfold costEntryBound
    have h1 : Real.exp (-δ * TorusFields.supDist b.1.1 b'.1.1) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ TorusFields.supDist b.1.1 b'.1.1 := by positivity
      nlinarith
    have h2 : CostDerivatives.alignmentExpansionBound R.params.side R.params.coupling Kf
        (b : TorusFields.TorusBond (n * R.params.side)) b' ≤ A := by
      unfold CostDerivatives.alignmentExpansionBound
      split_ifs
      · exact le_rfl
      · exact hA0
    have h3 : (if b = b' then Cm * (CA + A) else 0) ≤ Cm * (CA + A) := by
      split_ifs
      · exact le_rfl
      · positivity
    have h4 : CA * Real.exp (-δ * TorusFields.supDist b.1.1 b'.1.1) + CostDerivatives.alignmentExpansionBound R.params.side
        R.params.coupling Kf (b : TorusFields.TorusBond (n * R.params.side)) b' ≤ CA + A := by
      have := mul_le_mul_of_nonneg_left h1 hCA
      linarith
    have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ Cm ^ 2)
    linarith
  · exact (sum_costEntryBound_mul_exp_sub_one_le c hCA hKf hCm hrt1 hrt2 b).trans hrow
  · have h2 : DifferentiableAt ℝ s.costSum η := (contDiffAt_costSum hS c hF hη).differentiableAt (by norm_num)
    have e : (fun τ : ℝ => s.costSum (Function.update η b (η b + τ • X))) =
        fun τ : ℝ => s.costSum (η + τ • (Pi.single b X : StepSettings.FreeCoords s.free)) := by
      funext τ
      rw [update_add_smul_eq_add_smul_single]
    rw [e, LineCalculus.deriv_along_line h2]
    have h3 := abs_fderiv_costSum_single_le hS c hF hCA hK hKf hmin hM hCm hη b X hX
    have h4 : 0 ≤ Cm ^ 2 * (CA + A) := by positivity
    linarith
theorem le_clusterRange_of_pow_le {q : ℕ} {x : ℝ} (hx : (q : ℝ) ^ 100 ≤ x) : q ≤ TorusLumps.clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
theorem exists_pow_mul_exp_neg_le {δ τ : ℝ} (hδ : 0 < δ) (hτ : 0 < τ) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → ((r : ℝ) + 1) ^ 4 * Real.exp (-δ * r / 16) ≤ τ := by
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4
  have hx : Filter.Tendsto (fun r : ℕ => δ * ((r : ℝ) + 1) / 16) Filter.atTop Filter.atTop := by
    have h2 : Filter.Tendsto (fun r : ℕ => (r : ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h3 := h2.const_mul_atTop (r := δ / 16) (by positivity)
    refine h3.congr fun r => ?_
    ring
  have h4 := h1.comp hx
  have h5 := h4.const_mul ((16 / δ) ^ 4 * Real.exp (δ / 16))
  rw [mul_zero] at h5
  have h6 : ∀ᶠ r : ℕ in Filter.atTop, ((16 / δ) ^ 4 * Real.exp (δ / 16)) *
      (((fun x : ℝ => x ^ 4 * Real.exp (-x)) ∘ fun r : ℕ => δ * ((r : ℝ) + 1) / 16) r) < τ :=
    (tendsto_order.1 h5).2 τ hτ
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp h6
  refine ⟨r₀, fun r hr => ?_⟩
  have h7 := hr₀ r hr
  simp only [Function.comp] at h7
  have e : ((16 / δ) ^ 4 * Real.exp (δ / 16)) * ((δ * ((r : ℝ) + 1) / 16) ^ 4 * Real.exp (-(δ * ((r : ℝ) + 1) / 16))) =
      ((r : ℝ) + 1) ^ 4 * Real.exp (-δ * r / 16) := by
    have h8 : Real.exp (δ / 16) * Real.exp (-(δ * ((r : ℝ) + 1) / 16)) = Real.exp (-δ * r / 16) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h9 : (16 / δ) ^ 4 * (δ * ((r : ℝ) + 1) / 16) ^ 4 = ((r : ℝ) + 1) ^ 4 := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc _ = ((16 / δ) ^ 4 * (δ * ((r : ℝ) + 1) / 16) ^ 4) *
          (Real.exp (δ / 16) * Real.exp (-(δ * ((r : ℝ) + 1) / 16))) := by ring
      _ = _ := by rw [h8, h9]
  rw [e] at h7
  exact h7.le
theorem exists_mul_exp_neg_le {δ A τ : ℝ} (hδ : 0 < δ) (hτ : 0 < τ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → A * Real.exp (-(δ * (q : ℝ))) ≤ τ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.exists_exp_tail_le <;> assumption
theorem costHessianFloor_of_parts (hS : StepCosts.SharesSumToAction) (hC : LumpContours.WholeCellCostEqualsMinimalAction)
    (hA : LumpContours.ActionAtLevelIsCutAction) (hAct : LevelAction.ActionSmoothAlongMoves)
    (hReg : LumpContours.ComplementOfThickenedLumpsRegular) (hFr : StepFrames.FrameNearMinimizer) :
    CostHessianFloor := by
  classical
  obtain ⟨Cm₀, hCm₀, hM₀⟩ := QuaternionLogarithm.exists_chartTranslate_deriv_bounds
  have key : ∀ c : RenormalizationStepParameters.ChainParameters, ∃ r : ℝ, 0 < r ∧ ((1 ≤ c.coupling ∧ Odd c.side ∧
      ColdChain.ColdChainConstants c.coupling c.δ₁ c.side c.lam c.ρA c.σA c.cg c.N) →
      ∃ CA Kf : ℝ, 0 < CA ∧ 0 ≤ Kf ∧ CostDerivatives.ActionDerivativeBounds c.coupling c.δ₁ c.σA CA c.side ∧
        CostDerivatives.AlignmentDerivativeBounds c.side Kf ∧ 2 * r ≤ c.δ₁ / 2 ∧
        2 * r * (10 * c.side + 2) ≤ 1 ∧ r * costRowBound c.coupling c.δ₁ CA Cm₀ Kf c.side ≤ c.lam / 16) := by
    intro c
    by_cases h : 1 ≤ c.coupling ∧ Odd c.side ∧
        ColdChain.ColdChainConstants c.coupling c.δ₁ c.side c.lam c.ρA c.σA c.cg c.N
    · obtain ⟨h1, h2, h3⟩ := h
      have hδ : 0 < c.δ₁ := h3.1
      have hlam : 0 < c.lam := h3.2.2.1
      obtain ⟨CA, hCA, hF⟩ := hAct c.coupling c.δ₁ c.side c.lam c.ρA c.σA c.cg c.N (by linarith) h2 h3
      obtain ⟨Kf, hKf, hK⟩ := PlainAlignment.exists_mixedDeriv_plainAlignmentDefect_bound h2
      have hR0 : 0 ≤ costRowBound c.coupling c.δ₁ CA Cm₀ Kf c.side := by
        have hx : Real.exp (-(c.δ₁ / 4) / 4) < 1 := by
          rw [Real.exp_lt_one_iff]
          linarith
        have hx' : 0 < 1 - Real.exp (-(c.δ₁ / 4) / 4) := by linarith
        have hy : Real.exp (-1 / 4) < 1 := by
          rw [Real.exp_lt_one_iff]
          norm_num
        have hy' : 0 < 1 - Real.exp (-1 / 4) := by linarith
        have ha0 : 0 ≤ c.coupling := by linarith
        unfold costRowBound
        positivity
      set B := costRowBound c.coupling c.δ₁ CA Cm₀ Kf c.side with hB
      have hLp : (0 : ℝ) ≤ (c.side : ℝ) := by positivity
      set r := min (c.δ₁ / 4) (min (1 / (2 * (10 * (c.side : ℝ) + 2))) (c.lam / (16 * (B + 1)))) with hr
      have hr0 : 0 < r := by
        refine lt_min (by positivity) (lt_min (by positivity) (by positivity))
      refine ⟨r, hr0, fun _ => ⟨CA, Kf, hCA, hKf, hF, hK, ?_, ?_, ?_⟩⟩
      · have := min_le_left (c.δ₁ / 4) (min (1 / (2 * (10 * (c.side : ℝ) + 2))) (c.lam / (16 * (B + 1))))
        linarith
      · have h4 : r ≤ 1 / (2 * (10 * (c.side : ℝ) + 2)) :=
          (min_le_right _ _).trans (min_le_left _ _)
        have h5 : (0 : ℝ) < 2 * (10 * (c.side : ℝ) + 2) := by positivity
        rw [le_div_iff₀ h5] at h4
        linarith
      · have h4 : r ≤ c.lam / (16 * (B + 1)) := (min_le_right _ _).trans (min_le_right _ _)
        have h5 : (0 : ℝ) < 16 * (B + 1) := by positivity
        rw [le_div_iff₀ h5] at h4
        nlinarith
    · exact ⟨1, one_pos, fun h' => absurd h' h⟩
  choose rt₀ hpos hgood using key
  refine ⟨rt₀, hpos, fun T hT hrt => ?_⟩
  obtain ⟨CA, Kf, hCA, hKf, hF, hK, hr1, hr2, hr3⟩ := hgood T.toChainParameters ⟨hT.a_ge, hT.L_odd, hT.chain⟩
  have hchain := hT.chain
  have hδ : 0 < T.δ₁ := hchain.1
  have hlam : 0 < T.lam := hchain.2.2.1
  have hN0 := hchain.2.2.2.2.2.2.2.1 0
  have hσ := hT.σ_pos
  set Z := 4 * (2 / (1 - Real.exp (-(T.δ₁ / 4) / 4)) : ℝ) ^ 4 * Cm₀ ^ 2 + Cm₀ with hZ
  have hZ0 : 0 < Z := by
    have hx : Real.exp (-(T.δ₁ / 4) / 4) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have hx' : 0 < 1 - Real.exp (-(T.δ₁ / 4) / 4) := by linarith
    rw [hZ]
    positivity
  set τ₁ := T.lam / 2 / (Z * (3 * CA * Real.exp 1)) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  obtain ⟨r₁, hr₁⟩ := exists_pow_mul_exp_neg_le hδ hτ₁0
  obtain ⟨q₀, hq₀⟩ := exists_mul_exp_neg_le (δ := T.δ₁) (A := T.N 0 * (2 * T.threshold)) (τ := T.threshold / 64) hδ
    (by positivity)
  set r₀ : ℕ := r₁ + 2 ^ 11 * q₀ + 64 * T.side + 2 ^ 16 with hr₀
  refine ⟨Cm₀ ^ 2 * (CA + T.coupling * (4 * 13 ^ 4 * Kf)) + Cm₀ * (CA + T.coupling * (4 * 13 ^ 4 * Kf)) + 1,
    max T.floorMin ((r₀ : ℝ) ^ 100), ?_, fun y hy R hR n _ hn s hs => ?_⟩
  · have ha0 : 0 ≤ T.coupling := by linarith [hT.a_ge]
    positivity
  · have hyT : T.floorMin ≤ y := (le_max_left _ _).trans hy
    have hyr : (r₀ : ℝ) ^ 100 ≤ R.coupling := ((le_max_right _ _).trans hy).trans hR.le_coupling
    have hrr : r₀ ≤ R.range := le_clusterRange_of_pow_le hyr
    have hfit : R.params.Admissible := by
      rw [hR.params_eq]
      exact hT.fits y hyT
    have hσR : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
    have hLR : R.params.side = T.side := by rw [hR.params_eq]; rfl
    have hrtR : R.params.rt = T.rt := by rw [hR.params_eq]; rfl
    have haR : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
    have hnR : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
    have hJR : R.params.baseDepth = T.baseDepth := by rw [hR.params_eq]; rfl
    have hρR : R.ballRadius = T.threshold / 64 := by
      unfold StepSettings.StepSetup.ballRadius
      rw [hσR]
    have hgap : T.N 0 * (2 * T.threshold) * Real.exp (-(T.δ₁ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤ T.threshold / 64 :=
      hq₀ _ ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega))
    have hctx : s.ChainContext T.δ₁ T.lam T.σA T.cg T.N :=
      { admissible := hs
        params_admissible := hfit
        large_range := ⟨by rw [hLR]; omega, hR.isStep.2.2⟩
        n₀_le := by rw [hnR]; exact hn
        chain := by
          rw [hR.params_eq, hR.anchorRadius_eq]
          exact hchain
        baseDepth_pos := by
          have := hT.J₀_ge
          omega
        threshold_le := by
          rw [hσR]
          exact hT.σ_le
        anchor_ge := by
          have h1 := hT.ρ_le
          rw [hR.anchorRadius_eq, hρR, hσR]
          have h2 : T.ballRadius = T.threshold / 64 := rfl
          rw [h2] at h1
          linarith
        ballRadius_ge := by
          rw [hρR, hσR]
          exact hgap
        complement_regular := hReg
        frame_near := hFr }
    have hF' : CostDerivatives.ActionDerivativeBounds R.params.coupling T.δ₁ T.σA CA R.params.side := by
      rw [hR.params_eq]
      exact hF
    have hK' : CostDerivatives.AlignmentDerivativeBounds R.params.side Kf := by
      rw [hLR]
      exact hK
    have hM' : ChartTranslateBounds Cm₀ := hM₀
    have hrange := hr₁ R.range (by omega)
    set ε := 3 * CA * Real.exp 1 * ((R.range : ℝ) + 1) ^ 4 * Real.exp (-T.δ₁ * R.range / 16) with hε
    have hfl : ε * Z ≤ T.lam / 2 := by
      have h1 : ε = (3 * CA * Real.exp 1) * (((R.range : ℝ) + 1) ^ 4 * Real.exp (-T.δ₁ * R.range / 16)) := by
        rw [hε]
        ring
      have h2 : (Z * (3 * CA * Real.exp 1)) * τ₁ = T.lam / 2 := by
        rw [hτ₁]
        field_simp
      have h3 : 0 ≤ Z * (3 * CA * Real.exp 1) := by positivity
      have h4 := mul_le_mul_of_nonneg_left hrange h3
      rw [h1]
      calc (3 * CA * Real.exp 1) * (((R.range : ℝ) + 1) ^ 4 * Real.exp (-T.δ₁ * R.range / 16)) * Z =
          (Z * (3 * CA * Real.exp 1)) * (((R.range : ℝ) + 1) ^ 4 * Real.exp (-T.δ₁ * R.range / 16)) := by ring
        _ ≤ (Z * (3 * CA * Real.exp 1)) * τ₁ := h4
        _ = T.lam / 2 := h2
    have hres := hasCostDecay_of_bounds hS hC hA hctx hF' hCA.le hK' hKf hM' hCm₀.le le_rfl hfl
      (by rw [hrtR]; exact (mul_le_mul_of_nonneg_left hrt (by norm_num)).trans hr1)
      (by
        rw [hrtR, hLR]
        have h1 : 2 * T.rt ≤ 2 * rt₀ T.toChainParameters := mul_le_mul_of_nonneg_left hrt (by norm_num)
        have h2 : (0 : ℝ) ≤ 10 * (T.side : ℝ) + 2 := by positivity
        exact (mul_le_mul_of_nonneg_right h1 h2).trans hr2)
      (by
        rw [hrtR, haR, hLR]
        have hR0 : 0 ≤ costRowBound T.coupling T.δ₁ CA Cm₀ Kf T.side := by
          have hx : Real.exp (-(T.δ₁ / 4) / 4) < 1 := by
            rw [Real.exp_lt_one_iff]
            linarith
          have hx' : 0 < 1 - Real.exp (-(T.δ₁ / 4) / 4) := by linarith
          have hy' : Real.exp (-1 / 4) < 1 := by
            rw [Real.exp_lt_one_iff]
            norm_num
          have hy'' : 0 < 1 - Real.exp (-1 / 4) := by linarith
          have ha0 : 0 ≤ T.coupling := by linarith [hT.a_ge]
          unfold costRowBound
          positivity
        exact (mul_le_mul_of_nonneg_right hrt hR0).trans hr3)
    rw [haR] at hres
    exact hres
end YangMills.Construction.ClusterExpansionOfAStep
end
