import YangMills.Construction.FreeEnergiesOfTheFlow.ActionOfAColdField
import YangMills.Construction.ResponseInTheExpansion.MassOfALevelProof
import YangMills.Construction.ResponseInTheExpansion.ScoredMassOfAField
import YangMills.Construction.SixteenPointsOnASmallTorus.ScoreAtAnyCoupling
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
open TorusFields TorusLumps TorusFrame RenormalizationStepParameters StepSettings WeightedResponses ResponseInTheExpansion BlockAverages HaarBalls
  ColdFieldAction
private theorem norm_word_sub_one_le {e : ℝ} (a b c d : UnitQuaternion) (ha : a ∈ closedBallAtOne e)
    (hb : b ∈ closedBallAtOne e) (hc : c ∈ closedBallAtOne e) (hd : d ∈ closedBallAtOne e) :
    ‖((a * b * c⁻¹ * d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * e := by apply _root_.YangMills.SharedProofs.p54318 <;> assumption
private theorem curvature_le_of_near {n : ℕ} {e : ℝ} (W : TorusField n)
    (hW : ∀ x i, W x i ∈ closedBallAtOne e) (x : TorusSite n) (μ ν : Fin 4) :
    curvature W x μ ν ≤ 4 * e :=
  norm_word_sub_one_le _ _ _ _ (hW _ _) (hW _ _) (hW _ _) (hW _ _)
private theorem exp_bound_of_log_le {V E X b c m : ℝ} {M : ℕ} (hV : 0 < V) (hb : 0 < b) (hm : (M : ℝ) = m)
    (hm0 : 0 ≤ m) (hc : Real.log 2 + 3 * E + X - 4 * Real.log b ≤ c) :
    V * 2 ^ M * Real.exp (2 * E * M) ≤
      Real.exp (c * m) * (V * Real.exp (-((X + E) * m)) * b ^ (4 * M)) := by
  have hpow : ∀ (a : ℝ) (k : ℕ), 0 < a → a ^ k = Real.exp (k * Real.log a) := fun a k ha => by
    rw [mul_comm, Real.exp_mul, Real.exp_log ha, Real.rpow_natCast]
  have hleft : V * 2 ^ M * Real.exp (2 * E * M) = V * Real.exp (M * Real.log 2 + 2 * E * M) := by
    rw [hpow 2 M two_pos, Real.exp_add]
    ring
  have hright : Real.exp (c * m) * (V * Real.exp (-((X + E) * m)) * b ^ (4 * M)) =
      V * Real.exp (c * m + (-((X + E) * m) + ((4 * M : ℕ) : ℝ) * Real.log b)) := by
    rw [hpow b (4 * M) hb, Real.exp_add, Real.exp_add]
    ring
  rw [hleft, hright]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hV.le
  push_cast
  rw [hm]
  nlinarith [mul_le_mul_of_nonneg_right hc hm0]
private theorem le_clusterRange_of_pow_le {m : ℕ} {x : ℝ} (h : (m : ℝ) ^ 100 ≤ x) : m ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
theorem scoreExpMeanBound_holds (hS : ResponseInTheExpansion.ScoredMassStatement) (h3 : TorusLumps.ExpansionBasicBounds)
    (hH : HaarBalls.HaarMassCubicLowerBound) (hC : ColdFieldAction.ColdActionBound) :
    SmallTorusCopies.scoreExpMeanBoundStatement := by
  intro T hT
  obtain ⟨c', hc', hball⟩ := hH
  obtain ⟨N, hN0, hact⟩ := hC T hT
  have hσ := hT.σ_pos
  set e₀ : ℝ := min (T.threshold / 5) 1 with he₀
  have he₀0 : 0 < e₀ := lt_min (by positivity) one_pos
  have he₀1 : e₀ ≤ 1 := min_le_right _ _
  have h5e₀ : 5 * e₀ ≤ T.threshold := by
    have : e₀ ≤ T.threshold / 5 := min_le_left _ _
    linarith
  set X : ℝ := N * (5 * e₀) ^ 2 with hX
  set A : ℝ := Real.log 2 + 3 * T.E + X - 4 * Real.log c' - 12 * Real.log e₀ with hA
  refine ⟨max A 6, le_trans (by norm_num) (le_max_right _ _),
    max T.floorMin (((4 * T.n₀ + 2 ^ 16 : ℕ) : ℝ) ^ 100), ?_⟩
  intro y R s n _ hy hparams hyx hexp hprice hn
  obtain ⟨hc, hh⟩ := hexp
  have hyT : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hadm : R.params.Admissible := by rw [hparams]; exact hT.fits y hyT
  have hy1 : (1 : ℝ) ≤ y := by
    have := (hT.fits y hyT).y₁_ge
    exact this
  have hx1 : 1 ≤ R.coupling := hy1.trans hyx
  have hx0 : 0 < R.coupling := by linarith
  have hcoup : R.params.coupling = T.coupling := by rw [hparams]; rfl
  have hside : R.params.side = T.side := by rw [hparams]; rfl
  have hthr : R.params.threshold = T.threshold := by rw [hparams]; rfl
  have hE : R.params.E = T.E := by rw [hparams]; rfl
  have hn₀' : R.params.n₀ = T.n₀ := by rw [hparams]; rfl
  have hrange : 4 * R.params.n₀ + 2 ^ 16 ≤ clusterRange R.coupling := by
    rw [hn₀']
    exact le_clusterRange_of_pow_le (((le_max_right _ _).trans hy).trans hyx)
  have hn₀ : R.params.n₀ ≤ n := by
    have hmul : R.params.side * R.params.n₀ ≤ n := hn.2
    have hside1 : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
    nlinarith
  have hsq0 : 0 < Real.sqrt R.coupling := Real.sqrt_pos.mpr hx0
  have hsq1 : 1 ≤ Real.sqrt R.coupling := Real.one_le_sqrt.mpr hx1
  set e : ℝ := e₀ / Real.sqrt R.coupling with he
  have he0 : 0 < e := div_pos he₀0 hsq0
  have hee₀ : e ≤ e₀ := div_le_self he₀0.le hsq1
  have he1 : e ≤ 1 := hee₀.trans he₀1
  have h5e : 5 * e ≤ T.threshold := by linarith
  have hxe : R.coupling * e ^ 2 = e₀ ^ 2 := by
    rw [he, div_pow, Real.sq_sqrt hx0.le]
    field_simp
  have hloge : Real.log e = Real.log e₀ - Real.log R.coupling / 2 := by
    rw [he, Real.log_div he₀0.ne' hsq0.ne', Real.log_sqrt hx0.le]
  set b : ℝ := c' * e ^ 3 with hbdef
  have hb0 : 0 < b := by positivity
  have hlogb : Real.log b = Real.log c' + 3 * Real.log e := by
    rw [hbdef, Real.log_mul hc'.ne' (by positivity), Real.log_pow]
    norm_num
  have hcond : Real.log 2 + 3 * T.E + X - 4 * Real.log b ≤ max A 6 * (1 + Real.log R.coupling) := by
    have hl0 : 0 ≤ Real.log R.coupling := Real.log_nonneg hx1
    have hAle : A ≤ max A 6 := le_max_left _ _
    have h6le : (6 : ℝ) ≤ max A 6 := le_max_right _ _
    rw [hlogb, hloge]
    have hprod := mul_le_mul_of_nonneg_right h6le hl0
    rw [hA] at hAle
    nlinarith
  have hcent := (h3 R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
    R.siteDensity hadm hadm.E_ge hx0 hrange hc hh).1
  have hup := hS R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
    R.siteDensity s hadm hadm.E_ge hx0 hrange hc hh hprice n hn
  have htriv : IsCold R.params.threshold (trivialField n) := by
    intro z μ ν _
    have hz : curvature (trivialField n) z μ ν = 0 := by simp [curvature, holonomy, trivialField]
    rw [hz, hthr]
    exact hσ
  have hV : 0 < R.functional n (trivialField n) := hc.positive n hn₀ _ htriv
  set M : ℕ := Fintype.card (TorusSite n) with hM
  have hcard : (M : ℝ) = (n : ℝ) ^ 4 := by
    simp [hM, TorusSite, ZMod.card]
  set S : Set (TorusField n) :=
    Set.univ.pi fun _ : TorusSite n => Set.univ.pi fun _ : Fin 4 => closedBallAtOne e with hSdef
  have hmemS : ∀ W ∈ S, ∀ x i, W x i ∈ closedBallAtOne e := fun W hW x i =>
    (Set.mem_univ_pi.mp ((Set.mem_univ_pi.mp hW) x)) i
  have hclosed : MeasurableSet (closedBallAtOne e) := by
    have : Continuous fun g : UnitQuaternion => ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1‖ :=
      (continuous_subtype_val.sub continuous_const).norm
    exact (isClosed_le this continuous_const).measurableSet
  have hSm : MeasurableSet S :=
    MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => hclosed
  have hmeasure : (fieldHaar n S).toReal = (haarUnit (closedBallAtOne e)).toReal ^ (4 * M) := by
    unfold fieldHaar
    rw [hSdef, Measure.pi_pi]
    simp only [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
    rw [pow_mul]
  set K : ℝ := R.functional n (trivialField n) * Real.exp (-((X + T.E) * (n : ℝ) ^ 4)) with hK
  have hK0 : 0 < K := by positivity
  have hpoint : ∀ W ∈ S, K ≤ R.functional n W := by
    intro W hW
    have hcW : IsCold (5 * e) W := by
      intro z μ ν _
      have := curvature_le_of_near W (hmemS W hW) z μ ν
      linarith
    have hcσ : IsCold R.params.threshold W := fun z μ ν h => (hcW z μ ν h).trans_le (hthr ▸ h5e)
    have hform := hc.form n hn₀ W hcσ
    have hDW : 0 < R.functional n W := hc.positive n hn₀ W hcσ
    have hA' := hact R.depth n (hn₀' ▸ hn₀) (5 * e) W (by positivity) h5e hcW
    rw [hcoup, hside] at hform
    have hsum : -(T.E * (n : ℝ) ^ 4) ≤ ∑ z, centered R.density n z W := by
      have : ∀ z ∈ (Finset.univ : Finset (TorusSite n)), -T.E ≤ centered R.density n z W := fun z _ =>
        (abs_le.mp (hE ▸ hcent n hn₀ z W hcσ)).1
      calc -(T.E * (n : ℝ) ^ 4) = ∑ _z : TorusSite n, -T.E := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rw [show ((Fintype.card (TorusSite n) : ℕ) : ℝ) = (n : ℝ) ^ 4 from hcard]
            ring
        _ ≤ _ := Finset.sum_le_sum this
    have hxA : R.coupling * actionAtLevel T.coupling T.side R.depth Finset.univ W ≤ X * (n : ℝ) ^ 4 := by
      calc R.coupling * actionAtLevel T.coupling T.side R.depth Finset.univ W ≤
            R.coupling * (N * (5 * e) ^ 2 * (n : ℝ) ^ 4) :=
            mul_le_mul_of_nonneg_left hA' hx0.le
        _ = X * (n : ℝ) ^ 4 := by
            rw [hX]
            linear_combination (25 * N * (n : ℝ) ^ 4) * hxe
    have hlog : Real.log (R.functional n (trivialField n)) - (X + T.E) * (n : ℝ) ^ 4 ≤
        Real.log (R.functional n W) := by
      nlinarith
    have := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hDW, Real.exp_sub, Real.exp_log hV, div_eq_mul_inv, ← Real.exp_neg] at this
    exact this
  have hmass : stateLIntegral R n (fun _ _ _ => 1) =
      ∫⁻ W, ENNReal.ofReal (R.functional n W) ∂(fieldHaar n) := by
    unfold stateLIntegral
    refine lintegral_congr fun W => ?_
    simp only [mul_one]
    exact hh.sum n hn W
  have hlow : ENNReal.ofReal K * fieldHaar n S ≤ stateLIntegral R n fun _ _ _ => 1 := by
    rw [hmass, ← setLIntegral_const]
    exact (setLIntegral_mono' hSm fun W hW => ENNReal.ofReal_le_ofReal (hpoint W hW)).trans
      (setLIntegral_le_lintegral _ _)
  have hupper : stateLIntegral R n (fun _ Y ω => Real.exp (∑ z : Y, s (ω z))) ≤
      ENNReal.ofReal (R.functional n (trivialField n) * 2 ^ M * Real.exp (2 * R.params.E * M)) := by
    unfold stateLIntegral
    refine (lintegral_mono fun W => hup W).trans ?_
    simp
  have hmeas2 : ENNReal.ofReal (b ^ (4 * M)) ≤ fieldHaar n S := by
    have hreal : b ^ (4 * M) ≤ (fieldHaar n S).toReal := by
      rw [hmeasure]
      exact pow_le_pow_left₀ hb0.le (hball e he0 he1) _
    calc ENNReal.ofReal (b ^ (4 * M)) ≤ ENNReal.ofReal (fieldHaar n S).toReal :=
          ENNReal.ofReal_le_ofReal hreal
      _ = fieldHaar n S := ENNReal.ofReal_toReal (measure_ne_top _ _)
  refine hupper.trans ?_
  refine le_trans ?_ (mul_le_mul_right (hlow) _)
  refine le_trans ?_ (mul_le_mul_right (mul_le_mul_right hmeas2 _) _)
  rw [← ENNReal.ofReal_mul hK0.le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [hE]
  exact exp_bound_of_log_le hV hb0 hcard (by positivity) hcond
end YangMills.Construction.SmallTorusCopies
end
