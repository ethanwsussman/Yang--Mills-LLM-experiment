import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfTheImage
import YangMills.Construction.FreeEnergiesOfTheFlow.ExpansionAlongTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.ScoredTowerOfTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.TheFlowLiesInATowerOfImages
import YangMills.Construction.FreeEnergiesOfTheFlow.WilsonResponseOnEverySplitting
import YangMills.Construction.ResponseInTheExpansion.LevelsOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.RunningCouplingSlope
import YangMills.Construction.ResponseInTheExpansion.TheResponseReturns
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
section InverseSquareRootSums
private theorem rpow_neg_three_halves_le_sub {a lam : ℝ} (ha : 0 < a) (hl : 0 < lam) :
    (a + lam) ^ (-(3 / 2) : ℝ) ≤ 2 / lam * (a ^ (-(1 / 2) : ℝ) - (a + lam) ^ (-(1 / 2) : ℝ)) := by
  have hal : 0 < a + lam := by linarith
  set p := Real.sqrt a with hp
  set q := Real.sqrt (a + lam) with hq
  have hp0 : 0 < p := Real.sqrt_pos.mpr ha
  have hq0 : 0 < q := Real.sqrt_pos.mpr hal
  have hp2 : p ^ 2 = a := Real.sq_sqrt ha.le
  have hq2 : q ^ 2 = a + lam := Real.sq_sqrt hal.le
  have hpq : p < q := Real.sqrt_lt_sqrt ha.le (by linarith)
  have e1 : a ^ (-(1 / 2) : ℝ) = p⁻¹ := by
    rw [Real.rpow_neg ha.le, hp, Real.sqrt_eq_rpow]
  have e2 : (a + lam) ^ (-(1 / 2) : ℝ) = q⁻¹ := by
    rw [Real.rpow_neg hal.le, hq, Real.sqrt_eq_rpow]
  have e3 : (a + lam) ^ (-(3 / 2) : ℝ) = (q ^ 3)⁻¹ := by
    rw [Real.rpow_neg hal.le, hq, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hal.le]
    norm_num
  rw [e1, e2, e3]
  have hlam : lam = (q - p) * (q + p) := by nlinarith
  have hqp : 0 < q - p := by linarith
  have e4 : 2 / lam * (p⁻¹ - q⁻¹) = 2 / ((q + p) * p * q) := by
    rw [hlam]
    field_simp
  rw [e4, ← one_div]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hp0 hq0, mul_pos hq0 hq0, mul_pos (mul_pos hq0 hq0) hqp]
private theorem sum_rpow_neg_three_halves_le {y lam : ℝ} (hy : 0 < y) (hl : 0 < lam) (n : ℕ) :
    ∑ i ∈ Finset.range n, (y + lam * ((i : ℝ) + 1)) ^ (-(3 / 2) : ℝ) ≤
      2 / lam * (y ^ (-(1 / 2) : ℝ) - (y + lam * n) ^ (-(1 / 2) : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : 0 < y + lam * n := by positivity
    have h := rpow_neg_three_halves_le_sub hn hl
    have e : y + lam * (n : ℝ) + lam = y + lam * ((n : ℝ) + 1) := by ring
    rw [e] at h
    push_cast
    have : 2 / lam * (y ^ (-(1 / 2) : ℝ) - (y + lam * ((n : ℝ) + 1)) ^ (-(1 / 2) : ℝ)) =
        2 / lam * (y ^ (-(1 / 2) : ℝ) - (y + lam * n) ^ (-(1 / 2) : ℝ)) +
          2 / lam * ((y + lam * n) ^ (-(1 / 2) : ℝ) - (y + lam * ((n : ℝ) + 1)) ^ (-(1 / 2) : ℝ)) := by
      ring
    rw [this]
    exact add_le_add ih h
private theorem sum_rpow_neg_three_halves_of_linear_descent {x : ℕ → ℝ} {y lam c₅ Cs : ℝ} {u : ℕ}
    (hy : 0 < y) (hl : 0 < lam)
    (hCs : 0 ≤ Cs) (hc : 2 * c₅ ≤ y) (hbig : (24 * Cs / lam) ^ 2 ≤ y) (hx : y ≤ x u)
    (hs : ∀ i ≤ u, lam * ((u : ℝ) - i) - c₅ ≤ x i - x u) :
    Cs * ∑ j ∈ Finset.range u, x j ^ (-(3 / 2) : ℝ) ≤ 1 / 4 := by
  have h23 : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
    have h8 : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h0 : 0 ≤ (2 : ℝ) ^ (3 / 2 : ℝ) := by positivity
    nlinarith
  have hterm : ∀ j ∈ Finset.range u, x j ^ (-(3 / 2) : ℝ) ≤
      3 * (y + lam * (((u - 1 - j : ℕ) : ℝ) + 1)) ^ (-(3 / 2) : ℝ) := by
    intro j hj
    have hj' : j < u := Finset.mem_range.mp hj
    have hcast : (((u - 1 - j : ℕ) : ℝ) + 1) = (u : ℝ) - j := by
      have : u - 1 - j + 1 + j = u := by omega
      have h2 : (((u - 1 - j + 1 + j : ℕ)) : ℝ) = (u : ℝ) := by rw [this]
      push_cast at h2
      linarith
    rw [hcast]
    have hsj := hs j hj'.le
    have hd : 0 < (u : ℝ) - j := by
      have : (j : ℝ) < u := by exact_mod_cast hj'
      linarith
    set v := y + lam * ((u : ℝ) - j) with hv
    have hv0 : 0 < v := by positivity
    have hxj : v / 2 ≤ x j := by
      have : 0 < lam * ((u : ℝ) - j) := by positivity
      rw [hv]
      linarith
    have hv2 : 0 < v / 2 := by positivity
    have h1 : x j ^ (-(3 / 2) : ℝ) ≤ (v / 2) ^ (-(3 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hv2 hxj (by norm_num)
    have h2 : (v / 2) ^ (-(3 / 2) : ℝ) = (2 : ℝ) ^ (3 / 2 : ℝ) * v ^ (-(3 / 2) : ℝ) := by
      rw [div_eq_mul_inv, Real.mul_rpow hv0.le (by positivity), Real.inv_rpow (by norm_num),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, mul_comm]
    have hvp : 0 ≤ v ^ (-(3 / 2) : ℝ) := by positivity
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h23 hvp)
  have hsum : ∑ j ∈ Finset.range u, x j ^ (-(3 / 2) : ℝ) ≤ 6 / lam * y ^ (-(1 / 2) : ℝ) := by
    have h1 := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum,
      Finset.sum_range_reflect (fun i => (y + lam * ((i : ℝ) + 1)) ^ (-(3 / 2) : ℝ)) u] at h1
    have h2 := sum_rpow_neg_three_halves_le hy hl u
    have h3 : 0 ≤ (y + lam * u) ^ (-(1 / 2) : ℝ) := by positivity
    have h4 : 2 / lam * (y ^ (-(1 / 2) : ℝ) - (y + lam * u) ^ (-(1 / 2) : ℝ)) ≤
        2 / lam * y ^ (-(1 / 2) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h5 := h2.trans h4
    calc _ ≤ _ := h1
      _ ≤ 3 * (2 / lam * y ^ (-(1 / 2) : ℝ)) := by linarith
      _ = _ := by ring
  have hroot : 24 * Cs / lam ≤ Real.sqrt y := by
    apply Real.le_sqrt_of_sq_le hbig
  have hyh : y ^ (-(1 / 2) : ℝ) = (Real.sqrt y)⁻¹ := by
    rw [Real.rpow_neg hy.le, Real.sqrt_eq_rpow]
  have hsq : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hfin : Cs * (6 / lam * y ^ (-(1 / 2) : ℝ)) ≤ 1 / 4 := by
    rw [hyh]
    have e : Cs * (6 / lam * (Real.sqrt y)⁻¹) = (24 * Cs / lam) / Real.sqrt y / 4 := by
      field_simp
      ring
    rw [e]
    have : (24 * Cs / lam) / Real.sqrt y ≤ 1 := (div_le_one hsq).mpr hroot
    linarith
  exact (mul_le_mul_of_nonneg_left hsum hCs).trans hfin
end InverseSquareRootSums
section StageResponses
variable {ℓ : TorusLumps.StepParameters}
private def initialSetup (c : WeightedResponses.ChainStage ℓ) (ht : c.depth = 0)
    (K : WeightedResponses.ResponseParameters) : WeightedResponses.ResponseSetup c.toStepSetup := by
  obtain ⟨t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := c
  obtain rfl : t = 0 := ht
  exact ⟨K, 1, fun _ => 0, ResponseInTheExpansion.wilsonColdResponse ℓ.side,
    ResponseInTheExpansion.wilsonHullResponse ℓ.side Λ.Ω, fun _ _ _ => 0, fun _ _ _ => 0⟩
private theorem initialSetup_responseParams (c : WeightedResponses.ChainStage ℓ) (ht : c.depth = 0)
    (K : WeightedResponses.ResponseParameters) : (initialSetup c ht K).responseParams = K := by
  obtain ⟨t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := c
  obtain rfl : t = 0 := ht
  rfl
private theorem initialSetup_coeff (c : WeightedResponses.ChainStage ℓ) (ht : c.depth = 0)
    (K : WeightedResponses.ResponseParameters) : (initialSetup c ht K).coeff = 1 := by
  obtain ⟨t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := c
  obtain rfl : t = 0 := ht
  rfl
private theorem initialSetup_score (c : WeightedResponses.ChainStage ℓ) (ht : c.depth = 0)
    (K : WeightedResponses.ResponseParameters) (w : c.toStepSetup.labels.Ω) :
    (initialSetup c ht K).score w = 0 := by
  obtain ⟨t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := c
  obtain rfl : t = 0 := ht
  rfl
private theorem initialSetup_cold (c : WeightedResponses.ChainStage ℓ) (ht : c.depth = 0)
    (K : WeightedResponses.ResponseParameters) (n : ℕ) [NeZero n] (z : TorusFields.TorusSite n)
    (W : TorusFields.TorusField n) (f : FinePlaquetteFunction) :
    (initialSetup c ht K).cold n z W (fineWeight f _) = WeightedResponses.siteResponse z W (fineWeight f n) := by
  obtain ⟨t, x, x', D, f', Λ, Dq, Φ, φ, ρA, p⟩ := c
  obtain rfl : t = 0 := ht
  rfl
private theorem initialSetup_hull (c : WeightedResponses.ChainStage ℓ) (ht : c.depth = 0)
    (K : WeightedResponses.ResponseParameters) (n : ℕ) [NeZero n] (z : TorusFields.TorusSite n)
    (W : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n)) (ω : Y → c.toStepSetup.labels.Ω)
    (f : FinePlaquetteFunction) :
    (initialSetup c ht K).hull n z W Y ω (fineWeight f _) = WeightedResponses.siteResponse z W (fineWeight f n) := by
  obtain ⟨t, x, x', D, f', Λ, Dq, Φ, φ, ρA, p⟩ := c
  obtain rfl : t = 0 := ht
  rfl
private theorem initialSetup_isAdmissible (c : WeightedResponses.ChainStage ℓ) (ht : c.depth = 0)
    {K : WeightedResponses.ResponseParameters} {β : ℝ} (hx : c.coupling = β)
    (hD : c.functional = TorusLumps.wilsonWeight β) (hrow : c.toStepSetup.HasExpansions) (hK : K.Admissible ℓ)
    (hW : ∀ (f : TorusLumps.LocalDensity) (Λ : TorusLumps.LabelSpace)
      (Dq : (n : ℕ) → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) → (Y → Λ.Ω) → ℝ)
      (Φ : (n : ℕ) → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) → (Y → Λ.Ω) →
        Finset (TorusFields.TorusSite n) → ℝ)
      (φ : (n : ℕ) → TorusFields.TorusSite n → TorusFields.TorusField n → (Y : Finset (TorusFields.TorusSite n)) →
        (Y → Λ.Ω) → ℝ),
      TorusLumps.HullExpansion ℓ 0 β (TorusLumps.wilsonWeight β) f Λ Dq Φ φ →
        WeightedResponses.PriceBoundsScore ℓ β Λ Φ φ (fun _ => 0) ∧
          WeightedResponses.ResponseBounds ℓ K 0 β 1 Λ Dq (fun _ => 0)
            (ResponseInTheExpansion.wilsonColdResponse ℓ.side) (ResponseInTheExpansion.wilsonHullResponse ℓ.side Λ.Ω)
            (fun _ _ _ => 0) (fun _ _ _ => 0)) :
    (initialSetup c ht K).IsAdmissible := by
  obtain ⟨t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := c
  obtain rfl : t = 0 := ht
  obtain rfl : x = β := hx
  obtain rfl : D = TorusLumps.wilsonWeight x := hD
  obtain ⟨h1, h2⟩ := hW f Λ Dq Φ φ hrow.2
  exact ⟨hK, h1, h2, by show |(1 : ℝ)| ≤ 2; norm_num⟩
private def stageSetup (T : WeightedResponses.StageTower ℓ) (ht : T.base.depth = 0)
    (K : WeightedResponses.ResponseParameters) :
    (u : ℕ) → WeightedResponses.ResponseSetup (T.stage u).toStepSetup
  | 0 => initialSetup T.base ht K
  | u + 1 =>
    { responseParams := (stageSetup T ht K u).responseParams
      coeff := ResponseInTheExpansion.nextCoeff _ (stageSetup T ht K u) (T.labelFacts _ T.two_le_side)
      score := WeightedResponses.coarseLabelScore (stageSetup T ht K u).responseParams.s₁ (stageSetup T ht K u).score
      cold := (stageSetup T ht K u).coldStep
      hull := (stageSetup T ht K u).hullStep
      siteRemainder := ResponseInTheExpansion.nextSiteRemainder _ (stageSetup T ht K u) (T.labelFacts _ T.two_le_side)
      totalRemainder := ResponseInTheExpansion.nextTotalRemainder _ (stageSetup T ht K u) (T.labelFacts _ T.two_le_side) }
private theorem stageSetup_responseParams (T : WeightedResponses.StageTower ℓ) (ht : T.base.depth = 0)
    (K : WeightedResponses.ResponseParameters) :
    ∀ u, (stageSetup T ht K u).responseParams = K
  | 0 => initialSetup_responseParams _ _ _
  | u + 1 => stageSetup_responseParams T ht K u
private theorem stage_depth (T : WeightedResponses.StageTower ℓ) (ht : T.base.depth = 0) :
    ∀ u, (T.stage u).depth = u
  | 0 => ht
  | u + 1 => by
    show (T.stage u).depth + 1 = u + 1
    rw [stage_depth T ht u]
private theorem stage_functional {Tb : RenormalizationStepParameters.ParameterAssignment} {y β : ℝ}
    {T : WeightedResponses.StageTower (Tb.stepParameters y)} {k : ℕ}
    (hT : IsImageTower Tb y T β k) :
    ∀ u ≤ k, (T.stage u).functional = ClusterExpansionOfAStep.flowFunctional (Tb.stepParameters y) β u
  | 0, _ => hT.startsAtWilson.functional_eq
  | u + 1, h => by
    show TorusLumps.kernelImage _ (T.stage u).coupling (T.stage u).functional =
      TorusLumps.kernelImage _ (TorusLumps.couplingFlow (Tb.stepParameters y) β u).1
        (TorusLumps.couplingFlow (Tb.stepParameters y) β u).2
    rw [hT.coupling_eq u (by omega), stage_functional hT u (by omega)]
    rfl
private theorem nextCoeff_and_bounds {R : StepSettings.StepSetup} {A : WeightedResponses.ResponseSetup R}
    {h : ClusterExpansionOfAStep.CoarseLabelFacts R} {al' : ℝ}
    (hr : WeightedResponses.StepHasResponseBounds R A h al')
    (hu : ∀ al'' : ℝ, WeightedResponses.StepHasResponseBounds R A h al'' → al'' = al') :
    ResponseInTheExpansion.nextCoeff R A h = al' ∧
      WeightedResponses.ResponseBounds R.params A.responseParams (R.depth + 1) R.nextCoupling
        (ResponseInTheExpansion.nextCoeff R A h) (ClusterExpansionOfAStep.coarseLabelSpace R h) (StepSettings.coarseWeightExpansion R)
        (WeightedResponses.coarseLabelScore A.responseParams.s₁ A.score) A.coldStep A.hullStep
        (ResponseInTheExpansion.nextSiteRemainder R A h) (ResponseInTheExpansion.nextTotalRemainder R A h) := by
  have hn : ∃ al, WeightedResponses.StepHasResponseBounds R A h al := ⟨al', hr⟩
  have e : ResponseInTheExpansion.nextCoeff R A h = hn.choose := by
    unfold ResponseInTheExpansion.nextCoeff
    rw [dif_pos hn]
  have hs : WeightedResponses.StepHasResponseBounds R A h (ResponseInTheExpansion.nextCoeff R A h) := e ▸ hn.choose_spec
  refine ⟨hu _ hs, ?_⟩
  have e1 : ResponseInTheExpansion.nextSiteRemainder R A h = hs.choose := by
    unfold ResponseInTheExpansion.nextSiteRemainder
    rw [dif_pos hs]
  have e2 : ResponseInTheExpansion.nextTotalRemainder R A h = hs.choose_spec.choose := by
    unfold ResponseInTheExpansion.nextTotalRemainder
    rw [dif_pos hs]
  rw [e1, e2]
  exact hs.choose_spec.choose_spec
private theorem stageSetup_step {Tb : RenormalizationStepParameters.ParameterAssignment} {y β Cs : ℝ}
    {T : WeightedResponses.StageTower (Tb.stepParameters y)} {K : WeightedResponses.ResponseParameters}
    {tp u : ℕ} (ht : T.base.depth = 0) (hK : K.Admissible (Tb.stepParameters y)) (hN : K.N₀ = Tb.N 0)
    (hRet : WeightedResponses.ReturnsAtParameters Tb K Cs y)
    (hCold : ∀ R : StepSettings.StepSetup, R.OnParameters Tb y → R.IsSymmetricWeight →
      TorusLumps.ColdExpansion R.params (R.depth + 1) (R.shiftedCoupling Tb.lam)
        (TorusLumps.kernelImage R.params R.coupling R.functional) (R.renormalizedDensity Tb.lam))
    (hA : expansionAlongFlow) (hS : ExpansionHolds (Tb.stepParameters y))
    (hr : CouplingsAboveFloor (Tb.stepParameters y) β tp)
    (hT : IsImageTower Tb y T β tp) (hu : u < tp) (hresp : (stageSetup T ht K u).IsAdmissible) :
    |(stageSetup T ht K (u + 1)).coeff - (stageSetup T ht K u).coeff| ≤
        Cs * ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β u ^ (-(3 / 2) : ℝ) ∧
      (|(stageSetup T ht K (u + 1)).coeff| ≤ 2 → (stageSetup T ht K (u + 1)).IsAdmissible) := by
  have hD : (T.stage u).functional = ClusterExpansionOfAStep.flowFunctional (Tb.stepParameters y) β u :=
    stage_functional hT u hu.le
  have hx : (T.stage u).coupling = ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β u := hT.coupling_eq u (by omega)
  have hx' : (T.stage u).nextCoupling = ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β (u + 1) :=
    hT.coupling_eq (u + 1) (by omega)
  have htu : (T.stage u).depth = u := stage_depth T ht u
  have hrows := hA _ hS β tp hr
  have hrow := (hA _ hS β u fun j hj => hr j (by omega)).1
  have hrow₁ := (hA _ hS β (u + 1) fun j hj => hr j (by omega)).1
  have hArr : (T.stage u).toStepSetup.IsSymmetricWeight := by
    intro n _ hn
    show Measurable ((T.stage u).functional n) ∧ (∀ W, 0 ≤ (T.stage u).functional n W) ∧
      (∀ (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (W : TorusFields.TorusField n),
        (T.stage u).functional n (TorusFields.gaugeTransform g W) = (T.stage u).functional n W) ∧
      ∀ (g : TorusFields.TorusIsometry) (W W' : TorusFields.TorusField n), g.Transports W W' →
        (T.stage u).functional n W' = (T.stage u).functional n W
    rw [hD]
    exact hrow.1 n hn
  have hon := hT.onFamily u hu.le
  have hc := hCold _ hon hArr
  obtain ⟨x', -, huniq⟩ := hS.returns_at u _ _ (hr u hu.le) hrow
  have e1 : (T.stage u).toStepSetup.shiftedCoupling Tb.lam = x' := by
    have e3 : ∀ (t₁ : ℕ) (x₁ : ℝ) (D₁ : TorusLumps.TorusFunctional), t₁ = (T.stage u).depth →
        x₁ = (T.stage u).coupling → D₁ = (T.stage u).functional →
        TorusLumps.ColdExpansion (Tb.stepParameters y) (t₁ + 1) ((T.stage u).toStepSetup.shiftedCoupling Tb.lam)
          (TorusLumps.kernelImage (Tb.stepParameters y) x₁ D₁)
          ((T.stage u).toStepSetup.renormalizedDensity Tb.lam) := by
      rintro _ _ _ rfl rfl rfl
      exact hc
    exact huniq _ _ (e3 _ _ _ htu.symm hx.symm hD.symm)
  obtain ⟨-, f₁, hf₁, -⟩ := hrow₁
  have e2 : ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β (u + 1) = x' := huniq _ f₁ hf₁
  have hmove : (T.stage u).toStepSetup.nextCoupling = (T.stage u).toStepSetup.shiftedCoupling Tb.lam := by
    show (T.stage u).nextCoupling = _
    rw [hx', e2, e1]
  have hAT : WeightedResponses.OnStepParameters Tb y (stageSetup T ht K u) := by
    refine ⟨hon, ?_, hresp, ?_⟩
    · show |(T.stage u).nextCoupling - (T.stage u).coupling| ≤ 2 * Tb.B
      rw [hx, hx']
      exact hrows.2 u hu
    · rw [stageSetup_responseParams]
      exact hN
  obtain ⟨hsc, al', hb, hr', hq⟩ :=
    hRet _ (stageSetup T ht K u) (T.labelFacts _ T.two_le_side) (stageSetup_responseParams T ht K u) hAT hArr hmove
  obtain ⟨hnum, hrw⟩ := nextCoeff_and_bounds hr' hq
  refine ⟨?_, fun h2 => ⟨?_, ?_, hrw, h2⟩⟩
  · show |ResponseInTheExpansion.nextCoeff _ (stageSetup T ht K u) (T.labelFacts _ T.two_le_side) - _| ≤ _
    rw [hnum, ← hx]
    exact hb
  · show (stageSetup T ht K u).responseParams.Admissible _
    rw [stageSetup_responseParams]
    exact hK
  · show WeightedResponses.PriceBoundsScore (Tb.stepParameters y) (T.stage u).nextCoupling
      (ClusterExpansionOfAStep.coarseLabelSpace (T.stage u).toStepSetup (T.labelFacts _ T.two_le_side))
      (StepSettings.coarseFactorExpansion (T.stage u).toStepSetup) (T.siteDensities (T.stage u).toStepSetup) _
    rw [hT.siteDensities_eq u hu]
    exact hsc.2.2
private theorem stageSetup_admissible_and_coeff_near_one {Tb : RenormalizationStepParameters.ParameterAssignment} {y β Cs : ℝ}
    {T : WeightedResponses.StageTower (Tb.stepParameters y)} {K : WeightedResponses.ResponseParameters}
    {tp : ℕ} (ht : T.base.depth = 0) (hK : K.Admissible (Tb.stepParameters y)) (hN : K.N₀ = Tb.N 0)
    (hRet : WeightedResponses.ReturnsAtParameters Tb K Cs y)
    (hCold : ∀ R : StepSettings.StepSetup, R.OnParameters Tb y → R.IsSymmetricWeight →
      TorusLumps.ColdExpansion R.params (R.depth + 1) (R.shiftedCoupling Tb.lam)
        (TorusLumps.kernelImage R.params R.coupling R.functional) (R.renormalizedDensity Tb.lam))
    (hA : expansionAlongFlow) (hS : ExpansionHolds (Tb.stepParameters y))
    (hr : CouplingsAboveFloor (Tb.stepParameters y) β tp)
    (hT : IsImageTower Tb y T β tp)
    (hsum : ∀ u ≤ tp, Cs * ∑ j ∈ Finset.range u,
      ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β j ^ (-(3 / 2) : ℝ) ≤ 1 / 4)
    (h0 : (stageSetup T ht K 0).IsAdmissible) (u : ℕ) :
    u ≤ tp → (stageSetup T ht K u).IsAdmissible ∧
      |(stageSetup T ht K u).coeff - 1| ≤
        Cs * ∑ j ∈ Finset.range u, ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β j ^ (-(3 / 2) : ℝ) := by
  induction u with
  | zero =>
    intro _
    refine ⟨h0, ?_⟩
    rw [show (stageSetup T ht K 0).coeff = 1 from initialSetup_coeff _ _ _]
    simp
  | succ u ih =>
    intro hu
    obtain ⟨hR, hb⟩ := ih (by omega)
    obtain ⟨h1, h2⟩ := stageSetup_step ht hK hN hRet hCold hA hS hr hT hu hR
    have hb' : |(stageSetup T ht K (u + 1)).coeff - 1| ≤
        Cs * ∑ j ∈ Finset.range (u + 1), ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β j ^ (-(3 / 2) : ℝ) := by
      rw [Finset.sum_range_succ, mul_add]
      have e : (stageSetup T ht K (u + 1)).coeff - 1 =
          ((stageSetup T ht K (u + 1)).coeff - (stageSetup T ht K u).coeff) +
            ((stageSetup T ht K u).coeff - 1) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      linarith
    have h4 := abs_le.mp (hb'.trans (hsum _ hu))
    refine ⟨h2 ?_, hb'⟩
    rw [abs_le]
    constructor <;> linarith [h4.1, h4.2]
end StageResponses
theorem scoredTowerExists (hRet : WeightedResponses.responseReturnsStatement)
    (hWil : YangMills.Construction.FreeEnergiesOfTheFlow.WilsonResponseEverySplitting)
    (hTow : flowInImageTowerStatement) (hSl : WeightedResponses.FlowDescendsLinearly)
    (hCR : ImageColdExpansion.ImageHasColdExpansion)
    (hA : expansionAlongFlow) : scoredTowerExistsStatement := by
  intro a ha
  obtain ⟨L₁, rt₁, hrt₁, hR⟩ := hRet a ha
  obtain ⟨L₂, rt₂, C₂, hrt₂, hTw⟩ := hTow a ha
  obtain ⟨L₃, rt₃, hrt₃, hSs⟩ := hSl a ha
  obtain ⟨rt₄, hrt₄, hC⟩ := hCR
  obtain ⟨M, hM⟩ := hWil
  refine ⟨max L₁ (max L₂ L₃), fun c => min (min (rt₁ c) (rt₂ c)) (min (rt₃ c) (rt₄ c)), C₂,
    fun c => lt_min (lt_min (hrt₁ c) (hrt₂ c)) (lt_min (hrt₃ c) (hrt₄ c)),
    fun L hodd hL Tb haT hLT hD hCS hCH hrt hCd => ?_⟩
  have hL₁ : L₁ ≤ Tb.side := by
    rw [hLT]
    exact (le_max_left _ _).trans hL
  have hL₂ : L₂ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hL₃ : L₃ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have r₁ : Tb.rt ≤ rt₁ Tb.toChainParameters := hrt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have r₂ : Tb.rt ≤ rt₂ Tb.toChainParameters := hrt.trans ((min_le_left _ _).trans (min_le_right _ _))
  have r₃ : Tb.rt ≤ rt₃ Tb.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have r₄ : Tb.rt ≤ rt₄ Tb.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨lam, c₅, hlam, hSt⟩ := hSs L hodd hL₃
  obtain ⟨K, hKc, -, hN, hKf, Cs, y₁, hCs, hret⟩ := hR Tb haT hL₁ hD hCS hCH r₁ (M * Tb.weight 2)
  obtain ⟨y₂, hy₂⟩ := hTw L hodd hL₂ Tb haT hLT hD hCS hCH r₂ hCd
  obtain ⟨y₃, hy₃⟩ := hSt Tb haT hLT hD r₃
  obtain ⟨y₄, hy₄⟩ := hC Tb hD hCS r₄
  refine ⟨K, max (max (max y₁ y₂) (max y₃ y₄)) (max Tb.floorMin (max (2 * c₅) ((24 * Cs / lam) ^ 2))),
    fun y hy hS β tp hr => ?_⟩
  have hlow := (le_max_left _ _).trans hy
  have hhigh := (le_max_right _ _).trans hy
  have h₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hlow
  have h₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hlow
  have h₃ : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hlow
  have h₄ : y₄ ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hlow
  have h₀ : Tb.floorMin ≤ y := (le_max_left _ _).trans hhigh
  have hc₅ : 2 * c₅ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hhigh
  have hbig : (24 * Cs / lam) ^ 2 ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hhigh
  have hfit := hD.fits y h₀
  have hy1 : (1 : ℝ) ≤ y := hfit.y₁_ge
  have hy0 : (0 : ℝ) < y := by linarith
  have hwil : ∀ β : ℝ, y ≤ β → TorusLumps.HasExpansion (Tb.stepParameters y) 0 β (TorusLumps.wilsonWeight β) :=
    hS.wilson_expansion
  obtain ⟨T, hT, hcoin⟩ := hy₂ y h₂ hS.returns_at hwil β tp hr
  have hslope : WeightedResponses.HasLinearDescent (Tb.stepParameters y) lam c₅ := hy₃ y h₃ hS.returns_at hwil
  have hcold : ∀ R : StepSettings.StepSetup, R.OnParameters Tb y → R.IsSymmetricWeight →
      TorusLumps.ColdExpansion R.params (R.depth + 1) (R.shiftedCoupling Tb.lam)
        (TorusLumps.kernelImage R.params R.coupling R.functional) (R.renormalizedDensity Tb.lam) :=
    fun R a b => (hy₄ y h₄ R a b).1
  have ht : T.base.depth = 0 := hT.startsAtWilson.depth_eq
  have hβ : (Tb.stepParameters y).y₁ ≤ β := hr 0 (Nat.zero_le _)
  have hsum : ∀ u ≤ tp, Cs * ∑ j ∈ Finset.range u,
      ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β j ^ (-(3 / 2) : ℝ) ≤ 1 / 4 :=
    fun u hu => sum_rpow_neg_three_halves_of_linear_descent hy0 hlam hCs hc₅ hbig (hr u hu)
      fun i hi => hslope β hβ u (fun k hk => hr k (by omega)) i hi
  have hKc' : M * (Tb.stepParameters y).weight 2 ≤ K.Kc := hKc
  have hfirst : (stageSetup T ht K 0).IsAdmissible :=
    initialSetup_isAdmissible T.base ht (hT.coupling_eq 0 (Nat.zero_le _)) hT.startsAtWilson.functional_eq
      (hT.onFamily 0 (Nat.zero_le _)).isStep.1 (hKf y) (hM _ K hfit (hKf y) hKc' β hβ)
  have hresp := fun u =>
    stageSetup_admissible_and_coeff_near_one ht (hKf y) hN (hret y h₁) hcold hA hS hr hT hsum hfirst u
  have hcut : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := by
    have h := hD.cut
    rw [← (hT.onFamily 0 (Nat.zero_le _)).barrierFn_eq] at h
    exact h
  refine ⟨T, ⟨K, stageSetup T ht K⟩, rfl, ?_⟩
  exact
    { isFlowStep := fun u hu => ⟨hT.onFamily u hu, stage_depth T ht u, hT.coupling_eq u (by omega),
        hT.coupling_eq (u + 1) (by omega), stage_functional hT u hu⟩
      startsAtWilson := hT.startsAtWilson
      bottom_coupling := hT.coupling_eq 0 (Nat.zero_le _)
      isCutoff_bottom := hcut
      marksMeasurable := hcoin
      params_eq := stageSetup_responseParams T ht K
      N₀_eq := hN
      coeff_zero := initialSetup_coeff T.base ht K
      score_zero := initialSetup_score T.base ht K
      cold_zero := fun n _ z W f => initialSetup_cold T.base ht K n z W f
      hull_zero := fun n _ z W Y ω f => initialSetup_hull T.base ht K n z W Y ω f
      score_succ := fun u _ => by
        show WeightedResponses.coarseLabelScore (stageSetup T ht K u).responseParams.s₁ _ =
          WeightedResponses.coarseLabelScore K.s₁ _
        rw [stageSetup_responseParams]
      cold_succ := fun _ _ => rfl
      hull_succ := fun _ _ => rfl
      isAdmissible := fun u hu => (hresp u hu).1
      coeff_near_one := fun u hu => (hresp u hu).2.trans (hsum u hu) }
end YangMills.Construction.FreeEnergies
end
