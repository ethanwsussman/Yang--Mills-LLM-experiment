import YangMills.Construction.FreeEnergiesOfTheFlow.ActionOfAColdField
import YangMills.Construction.FreeEnergiesOfTheFlow.ExpansionAlongTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.MassOfTheFlow
import YangMills.Construction.HullsInEveryVolume.FreeEnergyBeforeTheFloor
import YangMills.Construction.ResponseInTheExpansion.MassOfALevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.HullTrees
open ClusterExpansionOfAStep WeightedResponses BlockAverages FreeEnergies HaarBalls TorusFields TorusLumps TorusFrame RenormalizationStepParameters
private theorem clusterRange_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : clusterRange x ≤ clusterRange y := by apply _root_.YangMills.Construction.WilsonExpansion.clusterRange_mono <;> assumption
private theorem le_clusterRange {k : ℕ} {y : ℝ} (hy : (k : ℝ) ^ 100 ≤ y) : k ≤ clusterRange y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
private theorem plaquette_word_near_one {e : ℝ} (a b c d : UnitQuaternion) (ha : a ∈ closedBallAtOne e)
    (hb : b ∈ closedBallAtOne e) (hc : c ∈ closedBallAtOne e)
    (hd : d ∈ closedBallAtOne e) : ‖((a * b * c⁻¹ * d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * e := by apply _root_.YangMills.SharedProofs.p54318 <;> assumption
private theorem curvature_le_of_near {n : ℕ} {e : ℝ} (W : TorusField n) (hW : ∀ x i, W x i ∈ closedBallAtOne e)
    (x : TorusSite n) (μ ν : Fin 4) :
    curvature W x μ ν ≤ 4 * e :=
  plaquette_word_near_one _ _ _ _ (hW _ _) (hW _ _) (hW _ _) (hW _ _)
theorem freeEnergyLowerBound_of (hM : flowFunctionalIntegral) (hA : expansionAlongFlow)
    (h3 : ExpansionBasicBounds) (hH : HaarMassCubicLowerBound) (hC : ColdFieldAction.ColdActionBound) :
    freeEnergyLowerBoundStatement := by
  obtain ⟨c', hc', hball⟩ := hH
  intro T hT
  obtain ⟨N, hN0, hact⟩ := hC T hT
  have hσ := hT.σ_pos
  set c : ℝ := min (T.threshold / 5) 1 with hc
  have hc0 : 0 < c := lt_min (by positivity) one_pos
  refine ⟨25 * N * c ^ 2 + T.E - 4 * Real.log c' - 12 * Real.log c,
    max T.floorMin (((4 * T.n₀ + 2 ^ 16 : ℕ) : ℝ) ^ 100), fun y hy hS β t hr n _ hn => ?_⟩
  have hy₀ : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hfit := hT.fits y hy₀
  have hfl : 4 * T.n₀ + 2 ^ 16 ≤ clusterRange y := le_clusterRange ((le_max_right _ _).trans hy)
  obtain ⟨hmeas, hpos, ⟨Cb, hCb⟩, hmass, hZ⟩ := hM _ hfit β t n
  obtain ⟨-, f, hf, Λ, Dq, Φ, φ, hHr⟩ := (hA _ hS β t hr).1
  have hx : y ≤ flowCoupling (T.stepParameters y) β t := hr t le_rfl
  have hy1 : 1 ≤ y := hfit.y₁_ge
  set x : ℝ := flowCoupling (T.stepParameters y) β t with hxdef
  have hx1 : 1 ≤ x := hy1.trans hx
  have hrange : 4 * (T.stepParameters y).n₀ + 2 ^ 16 ≤ clusterRange x :=
    hfl.trans (clusterRange_mono (by linarith) hx)
  obtain ⟨h21, -, -⟩ := h3 (T.stepParameters y) t x _ f Λ Dq Φ φ hfit hfit.E_ge (by linarith) hrange hf hHr
  have hn₀ : T.n₀ ≤ n := by
    have h1 : T.side * T.n₀ ≤ n := hn.2
    have h2 : 1 ≤ T.side := Nat.pos_of_ne_zero (NeZero.ne _)
    nlinarith
  have hsx : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1
  have hsx0 : 0 < Real.sqrt x := by linarith
  set e : ℝ := c / Real.sqrt x with he
  have he0 : 0 < e := by positivity
  have hec : e ≤ c := div_le_self hc0.le hsx
  have he1 : e ≤ 1 := hec.trans (min_le_right _ _)
  have h5e : 5 * e ≤ T.threshold := by
    have : c ≤ T.threshold / 5 := min_le_left _ _
    linarith
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
  set M : ℕ := Fintype.card (TorusSite n) with hM'
  have hcard : (M : ℝ) = (n : ℝ) ^ 4 := by
    simp [hM', TorusSite, ZMod.card]
  have hmeasure : (fieldHaar n S).toReal = (haarUnit (closedBallAtOne e)).toReal ^ (4 * M) := by
    unfold fieldHaar
    rw [hSdef, Measure.pi_pi]
    simp only [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
    rw [pow_mul]
  have hpoint : ∀ W ∈ S, flowFunctionalAtTrivial (T.stepParameters y) β t n *
      Real.exp (-((25 * N * c ^ 2 + T.E) * (n : ℝ) ^ 4)) ≤
      flowFunctional (T.stepParameters y) β t n W := by
    intro W hW
    have hcW : IsCold (5 * e) W := by
      intro z μ ν _
      have := curvature_le_of_near W (hmemS W hW) z μ ν
      linarith
    have hcσ : IsCold (T.stepParameters y).threshold W := fun z μ ν h => (hcW z μ ν h).trans_le h5e
    have hform := hf.form n hn₀ W hcσ
    have hA' := hact t n hn₀ (5 * e) W (by positivity) h5e hcW
    have hsum : -(T.E * (n : ℝ) ^ 4) ≤ ∑ z, centered f n z W := by
      have : ∀ z ∈ (Finset.univ : Finset (TorusSite n)), -T.E ≤ centered f n z W := fun z _ =>
        (abs_le.mp (h21 n hn₀ z W hcσ)).1
      calc -(T.E * (n : ℝ) ^ 4) = ∑ _z : TorusSite n, -T.E := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rw [show ((Fintype.card (TorusSite n) : ℕ) : ℝ) = (n : ℝ) ^ 4 from hcard]
            ring
        _ ≤ _ := Finset.sum_le_sum this
    have hxs : x * (N * (5 * e) ^ 2 * (n : ℝ) ^ 4) = 25 * N * c ^ 2 * (n : ℝ) ^ 4 := by
      have : x * e ^ 2 = c ^ 2 := by
        rw [he, div_pow, Real.sq_sqrt (by linarith)]
        field_simp
      calc x * (N * (5 * e) ^ 2 * (n : ℝ) ^ 4) = 25 * N * (x * e ^ 2) * (n : ℝ) ^ 4 := by ring
        _ = _ := by rw [this]
    have hlog : Real.log (flowFunctionalAtTrivial (T.stepParameters y) β t n) -
        (25 * N * c ^ 2 + T.E) * (n : ℝ) ^ 4 ≤
        Real.log (flowFunctional (T.stepParameters y) β t n W) := by
      have hxA : x * actionAtLevel T.coupling T.side t Finset.univ W ≤ 25 * N * c ^ 2 * (n : ℝ) ^ 4 := by
        rw [← hxs]
        exact mul_le_mul_of_nonneg_left hA' (by linarith)
      have hform' : Real.log (flowFunctional (T.stepParameters y) β t n W) -
          Real.log (flowFunctionalAtTrivial (T.stepParameters y) β t n) =
          -x * actionAtLevel T.coupling T.side t Finset.univ W + ∑ z, centered f n z W := hform
      nlinarith
    have hv : 0 < flowFunctionalAtTrivial (T.stepParameters y) β t n := hpos (trivialField n)
    have := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (hpos W), Real.exp_sub, Real.exp_log hv, div_eq_mul_inv, ← Real.exp_neg] at this
    exact this
  set K : ℝ := flowFunctionalAtTrivial (T.stepParameters y) β t n *
    Real.exp (-((25 * N * c ^ 2 + T.E) * (n : ℝ) ^ 4)) with hK
  have hv : 0 < flowFunctionalAtTrivial (T.stepParameters y) β t n := hpos (trivialField n)
  have hK0 : 0 < K := by positivity
  have hI : Integrable (flowFunctional (T.stepParameters y) β t n) (fieldHaar n) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable Cb (Filter.Eventually.of_forall fun V => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (hpos V)]
    exact hCb V
  have hZlow : K * (fieldHaar n S).toReal ≤ torusPartition (T.stepParameters y) β t n := by
    rw [← hmass]
    have hind : Integrable (S.indicator fun _ : TorusField n => K) (fieldHaar n) :=
      (integrable_const K).indicator hSm
    have h1 : ∫ W, S.indicator (fun _ : TorusField n => K) W ∂(fieldHaar n) = K * (fieldHaar n S).toReal := by
      rw [integral_indicator_const _ hSm]
      simp [Measure.real, mul_comm]
    rw [← h1]
    refine integral_mono hind hI fun W => ?_
    by_cases hW : W ∈ S
    · simp only [Set.indicator_of_mem hW]
      exact hpoint W hW
    · simp only [Set.indicator_of_notMem hW]
      exact (hpos W).le
  have hb := hball e he0 he1
  have hbpos : 0 < c' * e ^ 3 := by positivity
  have hmeas2 : (c' * e ^ 3) ^ (4 * M) ≤ (fieldHaar n S).toReal := by
    rw [hmeasure]
    exact pow_le_pow_left₀ hbpos.le hb _
  have hfin : K * (c' * e ^ 3) ^ (4 * M) ≤ torusPartition (T.stepParameters y) β t n :=
    (mul_le_mul_of_nonneg_left hmeas2 hK0.le).trans hZlow
  have hlogfin := Real.log_le_log (by positivity) hfin
  rw [Real.log_mul hK0.ne' (by positivity), Real.log_pow, Real.log_mul hv.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul hc'.ne' (by positivity), Real.log_pow] at hlogfin
  have hle : Real.log e = Real.log c - Real.log x / 2 := by
    rw [he, Real.log_div hc0.ne' hsx0.ne', Real.log_sqrt (by linarith)]
  rw [hle] at hlogfin
  push_cast at hlogfin
  rw [hcard] at hlogfin
  have hfinal : Real.log (flowFunctionalAtTrivial (T.stepParameters y) β t n) -
      (25 * N * c ^ 2 + T.E - 4 * Real.log c' - 12 * Real.log c + 6 * Real.log x) * (n : ℝ) ^ 4 =
      Real.log (flowFunctionalAtTrivial (T.stepParameters y) β t n) + -((25 * N * c ^ 2 + T.E) * (n : ℝ) ^ 4) +
        4 * (n : ℝ) ^ 4 * (Real.log c' + 3 * (Real.log c - Real.log x / 2)) := by
    ring
  rw [hfinal]
  exact hlogfin
end YangMills.Construction.HullTrees
end
