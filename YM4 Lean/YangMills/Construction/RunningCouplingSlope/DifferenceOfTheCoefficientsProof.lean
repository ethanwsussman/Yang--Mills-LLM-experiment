import YangMills.Construction.QuaternionicWilsonModel.TheFlowRepresentsTheMixedMomentProof
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.LawInAState.DecayOverATorusProof
import YangMills.Construction.OneLoopLaw.CoefficientOfATemperedFunctional
import YangMills.Construction.OneLoopLaw.TheSumOfTheOneLoopIncrements
import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheCoefficients
import YangMills.Construction.RunningCouplingSlope.TheDifferenceKernelDecaysOnTheSides
import YangMills.Construction.RunningCouplingSlope.TheKernelsOfTheTwoChainsAgreeOnLongWaves
import YangMills.Construction.Towers.FamilyOfTheTotalNormaliserIsTempered
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open TorusFields TorusLumps BlockAverages SlopeCoefficient
namespace CoefficientDifference
private def expWeight (θ : ℝ) (w : Fin 4 → ℤ) : ℝ := Real.exp (-(θ * ∑ μ, |(w μ : ℝ)|))
private theorem expWeight_nonneg (θ : ℝ) (w : Fin 4 → ℤ) : 0 ≤ expWeight θ w := (Real.exp_pos _).le
private theorem summable_exp_neg_mul_abs {θ : ℝ} (hθ : 0 < θ) :
    Summable fun t : ℤ => Real.exp (-(θ * |(t : ℝ)|)) := by apply _root_.YangMills.SharedProofs.p3695 <;> assumption
private theorem summable_expWeight {θ : ℝ} (hθ : 0 < θ) : Summable (expWeight θ) := by
  let e : (Fin 4 → ℤ) ≃ ℤ × ℤ × ℤ × ℤ :=
    { toFun := fun w => (w 0, w 1, w 2, w 3)
      invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      left_inv := by
        intro w
        funext i
        fin_cases i <;> rfl
      right_inv := fun p => rfl }
  have g0 : ∀ t : ℤ, 0 ≤ Real.exp (-(θ * |(t : ℝ)|)) := fun t => (Real.exp_pos _).le
  have s0 := summable_exp_neg_mul_abs hθ
  have s00 := Summable.mul_of_nonneg s0 s0 g0 g0
  have s000 := Summable.mul_of_nonneg s0 s00 g0 (fun p => mul_nonneg (g0 _) (g0 _))
  have s := Summable.mul_of_nonneg s0 s000 g0
    (fun p => mul_nonneg (g0 _) (mul_nonneg (g0 _) (g0 _)))
  rw [← e.symm.summable_iff]
  refine s.congr fun p => ?_
  have h1 : Real.exp (-(θ * (|(p.1 : ℝ)| + |(p.2.1 : ℝ)| + |(p.2.2.1 : ℝ)| + |(p.2.2.2 : ℝ)|))) =
      Real.exp (-(θ * |(p.1 : ℝ)|)) * Real.exp (-(θ * |(p.2.1 : ℝ)|)) *
        Real.exp (-(θ * |(p.2.2.1 : ℝ)|)) * Real.exp (-(θ * |(p.2.2.2 : ℝ)|)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h2 : (expWeight θ ∘ e.symm) p =
      Real.exp (-(θ * (|(p.1 : ℝ)| + |(p.2.1 : ℝ)| + |(p.2.2.1 : ℝ)| + |(p.2.2.2 : ℝ)|))) := by
    change Real.exp (-(θ * ∑ μ, |((![p.1, p.2.1, p.2.2.1, p.2.2.2] μ : ℤ) : ℝ)|)) = _
    rw [Fin.sum_univ_four]
    rfl
  rw [h2, h1]
  ring
private theorem expWeight_mul_sq_le {θ : ℝ} (hθ : 0 < θ) (w : Fin 4 → ℤ) :
    expWeight θ w * ((w 0 : ℤ) : ℝ) ^ 2 ≤ 8 / θ ^ 2 * expWeight (θ / 2) w := by
  set S : ℝ := ∑ μ, |(w μ : ℝ)| with hS
  have hw : |((w 0 : ℤ) : ℝ)| ≤ S :=
    Finset.single_le_sum (f := fun μ => |(w μ : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ 0)
  set y : ℝ := θ * |((w 0 : ℤ) : ℝ)| / 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 := Real.quadratic_le_exp_of_nonneg hy0
  have h2 : ((w 0 : ℤ) : ℝ) ^ 2 ≤ 8 / θ ^ 2 * Real.exp y := by
    have h3 : y ^ 2 / 2 ≤ Real.exp y := by nlinarith
    have h4 : y ^ 2 / 2 = θ ^ 2 / 8 * ((w 0 : ℤ) : ℝ) ^ 2 := by
      rw [hy, div_pow, mul_pow, sq_abs]; ring
    rw [h4] at h3
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have h5 : Real.exp (-(θ * S)) * Real.exp y ≤ Real.exp (-(θ / 2 * S)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hy]
    nlinarith
  calc expWeight θ w * ((w 0 : ℤ) : ℝ) ^ 2 ≤ expWeight θ w * (8 / θ ^ 2 * Real.exp y) :=
        mul_le_mul_of_nonneg_left h2 (expWeight_nonneg _ _)
    _ = 8 / θ ^ 2 * (Real.exp (-(θ * S)) * Real.exp y) := by
        simp only [expWeight, ← hS]; ring
    _ ≤ 8 / θ ^ 2 * expWeight (θ / 2) w := mul_le_mul_of_nonneg_left h5 (by positivity)
private theorem centredCoords_injective {s : ℕ} [NeZero s] :
    Function.Injective (centredCoords : TorusSite s → Fin 4 → ℤ) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.siteCoords_injective <;> assumption
private theorem centredCoords_siteOfInt {s : ℕ} [NeZero s] {w : Fin 4 → ℤ}
    (h : ∀ μ, 2 * |w μ| < (s : ℤ)) : centredCoords (siteOfInt w : TorusSite s) = w := by
  funext μ
  have hμ := h μ
  refine (ZMod.valMinAbs_spec _ _).2 ⟨rfl, ?_, ?_⟩
  · have := neg_abs_le (w μ)
    linarith
  · have := le_abs_self (w μ)
    linarith
private theorem eventually_two_mul_abs_lt {s : ℕ → ℕ} (hs : Tendsto s atTop atTop) (w : Fin 4 → ℤ) :
    ∀ᶠ n in atTop, ∀ μ, 2 * |w μ| < (s n : ℤ) := by
  rw [eventually_all]
  intro μ
  filter_upwards [hs.eventually_gt_atTop (2 * |w μ|).toNat] with n hn
  have := Int.self_le_toNat (2 * |w μ|)
  omega
private theorem tendsto_sum_torusSite {s : ℕ → ℕ} [∀ n, NeZero (s n)] (hs : Tendsto s atTop atTop)
    (G : ∀ n, TorusSite (s n) → ℝ) (g bd : (Fin 4 → ℤ) → ℝ) (hb : Summable bd) (hb0 : ∀ w, 0 ≤ bd w)
    (hbound : ∀ᶠ n in atTop, ∀ x, |G n x| ≤ bd (centredCoords x))
    (hlim : ∀ w, Tendsto (fun n => G n (siteOfInt w)) atTop (𝓝 (g w))) :
    Tendsto (fun n => ∑ x, G n x) atTop (𝓝 (∑' w, g w)) := by
  classical
  let F : ℕ → (Fin 4 → ℤ) → ℝ := fun n => Function.extend centredCoords (G n) 0
  have hsum : ∀ n, ∑ x, G n x = ∑' w, F n w := fun n =>
    ((hasSum_extend_zero centredCoords_injective).2 (hasSum_fintype _)).tsum_eq.symm
  simp_rw [hsum]
  refine tendsto_tsum_of_dominated_convergence hb ?_ ?_
  · intro w
    refine (hlim w).congr' ?_
    filter_upwards [eventually_two_mul_abs_lt hs w] with n hn
    have h1 := centredCoords_siteOfInt (s := s n) hn
    change G n (siteOfInt w) = Function.extend centredCoords (G n) 0 w
    conv_rhs => rw [← h1]
    exact (centredCoords_injective.extend_apply _ _ _).symm
  · filter_upwards [hbound] with n hn w
    by_cases hw : ∃ x : TorusSite (s n), centredCoords x = w
    · obtain ⟨x, rfl⟩ := hw
      change ‖Function.extend centredCoords (G n) 0 (centredCoords x)‖ ≤ _
      rw [centredCoords_injective.extend_apply, Real.norm_eq_abs]
      exact hn x
    · change ‖Function.extend centredCoords (G n) 0 w‖ ≤ _
      rw [Function.extend_apply' _ _ _ hw]
      simpa using hb0 w
private theorem tendsto_cosinePhase_sum {s : ℕ → ℕ} [∀ n, NeZero (s n)] (hs : Tendsto s atTop atTop)
    (G : ∀ n, TorusSite (s n) → ℝ) (g bd : (Fin 4 → ℤ) → ℝ) (hb : Summable bd) (hb0 : ∀ w, 0 ≤ bd w)
    (hbound : ∀ᶠ n in atTop, ∀ x, |G n x| ≤ bd (centredCoords x))
    (hlim : ∀ w, Tendsto (fun n => G n (siteOfInt w)) atTop (𝓝 (g w))) (t : ℝ) :
    Tendsto (fun n => ∑ x, G n x * cosinePhase t x) atTop
      (𝓝 (∑' w, g w * Real.cos (t * ((w 0 : ℤ) : ℝ)))) := by
  refine tendsto_sum_torusSite hs (fun n x => G n x * cosinePhase t x) _ bd hb hb0 ?_ ?_
  · filter_upwards [hbound] with n hn x
    rw [abs_mul]
    calc |G n x| * |cosinePhase t x| ≤ |G n x| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hn x
  · intro w
    refine ((hlim w).mul_const (Real.cos (t * ((w 0 : ℤ) : ℝ)))).congr' ?_
    filter_upwards [eventually_two_mul_abs_lt hs w] with n hn
    have h1 := centredCoords_siteOfInt (s := s n) hn
    simp only [cosinePhase, h1]
private theorem tendsto_cos_sub_one_div_sq (w : ℝ) :
    Tendsto (fun t : ℝ => (Real.cos (t * w) - 1) / t ^ 2) (𝓝[≠] 0) (𝓝 (-(1 / 2) * w ^ 2)) := by
  have hc : Continuous fun t : ℝ => |t * w| := by fun_prop
  have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), |t * w| < 1 :=
    hc.continuousAt.eventually_lt continuousAt_const (by simp)
  have hb : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖(Real.cos (t * w) - 1) / t ^ 2 - -(1 / 2) * w ^ 2‖ ≤
      t ^ 2 * (w ^ 4 * (5 / 96)) := by
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with t ht ht0
    have ht0' : t ≠ 0 := ht0
    have hcb := Real.cos_bound ht.le
    have ht2 : 0 < t ^ 2 := by positivity
    have e : (Real.cos (t * w) - 1) / t ^ 2 - -(1 / 2) * w ^ 2 =
        (Real.cos (t * w) - (1 - (t * w) ^ 2 / 2)) / t ^ 2 := by
      field_simp
      ring
    have h4 : |t * w| ^ 4 = (t * w) ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    rw [e, Real.norm_eq_abs, abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
    calc _ ≤ |t * w| ^ 4 * (5 / 96) := hcb
      _ = _ := by rw [h4]; ring
  have hz : Tendsto (fun t : ℝ => t ^ 2 * (w ^ 4 * (5 / 96))) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t ^ 2 * (w ^ 4 * (5 / 96))) (𝓝 0) (𝓝 (0 ^ 2 * (w ^ 4 * (5 / 96)))) :=
      (Continuous.tendsto (by fun_prop) 0)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero_norm' (by simpa using hb) hz)
private theorem tendsto_cosineSeries_sub_div_sq (c : (Fin 4 → ℤ) → ℝ) (hc : Summable c)
    (hc2 : Summable fun w => |c w| * ((w 0 : ℤ) : ℝ) ^ 2) :
    Tendsto (fun t : ℝ => (∑' w, c w * Real.cos (t * ((w 0 : ℤ) : ℝ)) - ∑' w, c w) / t ^ 2) (𝓝[≠] 0)
      (𝓝 (∑' w, -(1 / 2) * c w * ((w 0 : ℤ) : ℝ) ^ 2)) := by
  have hcc : ∀ t : ℝ, Summable fun w => c w * Real.cos (t * ((w 0 : ℤ) : ℝ)) := fun t =>
    Summable.of_norm_bounded hc.abs fun w => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |c w| * |Real.cos _| ≤ |c w| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = |c w| := mul_one _
  have heq : ∀ t : ℝ, (∑' w, c w * Real.cos (t * ((w 0 : ℤ) : ℝ)) - ∑' w, c w) / t ^ 2 =
      ∑' w, c w * ((Real.cos (t * ((w 0 : ℤ) : ℝ)) - 1) / t ^ 2) := by
    intro t
    rw [← (hcc t).tsum_sub hc, ← tsum_div_const]
    refine tsum_congr fun w => ?_
    ring
  simp_rw [heq]
  refine tendsto_tsum_of_dominated_convergence (bound := fun w => |c w| * ((w 0 : ℤ) : ℝ) ^ 2)
    hc2 ?_ ?_
  · intro w
    have h := (tendsto_cos_sub_one_div_sq ((w 0 : ℤ) : ℝ)).const_mul (c w)
    have e : c w * (-(1 / 2) * ((w 0 : ℤ) : ℝ) ^ 2) = -(1 / 2) * c w * ((w 0 : ℤ) : ℝ) ^ 2 := by ring
    rwa [e] at h
  · filter_upwards [self_mem_nhdsWithin] with t ht0 w
    have ht0' : t ≠ 0 := ht0
    have ht2 : 0 < t ^ 2 := by positivity
    have h1 := Real.one_sub_sq_div_two_le_cos (x := t * ((w 0 : ℤ) : ℝ))
    have h2 := Real.cos_le_one (t * ((w 0 : ℤ) : ℝ))
    have h3 : |(Real.cos (t * ((w 0 : ℤ) : ℝ)) - 1) / t ^ 2| ≤ ((w 0 : ℤ) : ℝ) ^ 2 := by
      rw [abs_div, abs_of_pos ht2, div_le_iff₀ ht2, abs_of_nonpos (by linarith)]
      nlinarith [sq_nonneg (t * ((w 0 : ℤ) : ℝ)), mul_pow t ((w 0 : ℤ) : ℝ) 2,
        mul_nonneg ht2.le (sq_nonneg ((w 0 : ℤ) : ℝ))]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
private theorem abs_le_of_tendsto_torus {s : ℕ → ℕ} [∀ n, NeZero (s n)] (hs : Tendsto s atTop atTop)
    (G : ∀ n, TorusSite (s n) → ℝ) (g : (Fin 4 → ℤ) → ℝ) (C θ : ℝ)
    (hbound : ∀ᶠ n in atTop, ∀ x, |G n x| ≤ C * expWeight θ (centredCoords x))
    (hlim : ∀ w, Tendsto (fun n => G n (siteOfInt w)) atTop (𝓝 (g w))) (w : Fin 4 → ℤ) :
    |g w| ≤ C * expWeight θ w := by
  refine le_of_tendsto (hlim w).abs ?_
  filter_upwards [hbound, eventually_two_mul_abs_lt hs w] with n hn h1
  have h2 := hn (siteOfInt w)
  rwa [centredCoords_siteOfInt h1] at h2
private theorem summable_and_secondMoment_of_le {c : (Fin 4 → ℤ) → ℝ} {C θ : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C)
    (hc : ∀ w, |c w| ≤ C * expWeight θ w) :
    Summable c ∧ Summable fun w => |c w| * ((w 0 : ℤ) : ℝ) ^ 2 := by
  refine ⟨Summable.of_norm_bounded ((summable_expWeight hθ).mul_left C) fun w => hc w, ?_⟩
  have hs := ((summable_expWeight (half_pos hθ)).mul_left (8 / θ ^ 2)).mul_left C
  refine Summable.of_nonneg_of_le (fun w => by positivity) (fun w => ?_) hs
  calc |c w| * ((w 0 : ℤ) : ℝ) ^ 2 ≤ C * expWeight θ w * ((w 0 : ℤ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (hc w) (by positivity)
    _ = C * (expWeight θ w * ((w 0 : ℤ) : ℝ) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (expWeight_mul_sq_le hθ w) hC
private theorem inner_thirdGenerator_self :
    inner ℝ ((thirdGenerator : imaginaryQuaternions) : ℍ[ℝ]) ((thirdGenerator : imaginaryQuaternions) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.DeltaSharedProofs.p500886 <;> assumption
private theorem norm_thirdGenerator : ‖thirdGenerator‖ = 1 := by
  have h := inner_thirdGenerator_self
  rw [real_inner_self_eq_norm_sq] at h
  have h1 : ‖((thirdGenerator : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by
    nlinarith [norm_nonneg ((thirdGenerator : imaginaryQuaternions) : ℍ[ℝ]),
      sq_nonneg (‖((thirdGenerator : imaginaryQuaternions) : ℍ[ℝ])‖ - 1)]
  simpa using h1
private theorem abs_centredCoords_le_supDist {s : ℕ} [NeZero s] (x : TorusSite s) (μ : Fin 4) :
    |(centredCoords x μ : ℝ)| ≤ supDist 0 x := by
  have h := Finset.le_sup (f := fun i => ((((0 : TorusSite s) i) - x i).valMinAbs).natAbs)
    (Finset.mem_univ μ)
  have h1 : ((x μ).valMinAbs).natAbs ≤ supDist 0 x := by
    simpa [supDist, ZMod.natAbs_valMinAbs_neg] using h
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  exact_mod_cast h1
private theorem sum_abs_centredCoords_le {s : ℕ} [NeZero s] (x : TorusSite s) :
    ∑ μ, |(centredCoords x μ : ℝ)| ≤ 4 * (supDist 0 x : ℝ) := by
  calc _ ≤ ∑ _μ : Fin 4, (supDist 0 x : ℝ) :=
        Finset.sum_le_sum fun μ _ => abs_centredCoords_le_supDist x μ
    _ = _ := by simp
theorem coefficientDifference_isSecondMoment (hw : ChainKernelsAgreeOnLongWaves)
    (hd : DifferenceKernelDecaysUniformly)
    (ht : Tower.NormaliserTempered.TemperedAndStiffness)
    (hc : OneLoopLaw.TemperedStiffness.TemperedStiffnessClaim)
    (hs : OneLoopLaw.IncrementSum.IncrementsSumToTotal) : CoefficientDifferenceIsSecondMoment := by
  intro a ha L hL hLs k hk κ hκ ρ v hρ hρ1 hv
  have hne : ∀ n : ℕ, NeZero (2 * L ^ n) := fun n => ⟨by positivity⟩
  have hL1 : 1 < L := by have := hLs.2; omega
  have hLr : (1 : ℝ) < L := by exact_mod_cast hL1
  have hsT : Tendsto (fun n : ℕ => 2 * L ^ n) atTop atTop :=
    tendsto_atTop_mono (fun n => by
      have := Nat.lt_pow_self (n := n) hL1
      change n ≤ 2 * L ^ n
      omega) tendsto_id
  obtain ⟨δ₀, -, hT⟩ := ht
  obtain ⟨⟨hF, δ, π, e, hch⟩, -, -, -⟩ := hT L hL hLs k hk
  obtain ⟨-, -, -, b, htensor, -, hform⟩ := hc L hL hLs _ δ π e hF hch
  have hb : OneLoopLaw.FunctionalStiffness.stiffnessConstant hL (Tower.logNormaliserFamily L k) = b :=
    (hform 0 1 (by decide)).eq_coeff
  have hsum := hs.2.2 L hL hLs k
  let P : ℝ → ℝ := fun t => (π secondAxis secondAxis
    (PeriodicOperators.toComplexVec (Pi.single 0 t))).re
  obtain ⟨K, hK, hKs⟩ := hv
  obtain ⟨M, θ, hθ, hM⟩ := hK.exp_decay
  let G₁ : ∀ n : ℕ, TorusSite (2 * L ^ n) → ℝ := fun n x =>
    hessianAtTrivial (chainLogarithm a ρ L k) (2 * L ^ n) (0, secondAxis) (x, secondAxis)
      thirdGenerator thirdGenerator
  let g₁ : (Fin 4 → ℤ) → ℝ := fun w => K (0, secondAxis) (w, secondAxis)
  have hlim₁ : ∀ w, Tendsto (fun n => G₁ n (siteOfInt w)) atTop (𝓝 (g₁ w)) := by
    intro w
    have h := (hK.tendsto_kernel (0, secondAxis) (w, secondAxis) thirdGenerator thirdGenerator).comp hsT
    rw [inner_thirdGenerator_self, one_mul] at h
    refine h.congr fun n => ?_
    have e1 : bondFrom (0 : TorusSite (2 * L ^ n)) ((0 : Fin 4 → ℤ), secondAxis) =
        (0, secondAxis) := by
      simp only [bondFrom, zero_add]
      congr 1
      funext i
      simp [siteOfInt]
    have e2 : bondFrom (0 : TorusSite (2 * L ^ n)) (w, secondAxis) = (siteOfInt w, secondAxis) := by
      simp [bondFrom]
    simp only [Function.comp, e1, e2, G₁]
  have hb₁ : ∀ᶠ n in atTop, ∀ x, |G₁ n x| ≤ |M| * expWeight (θ / 4) (centredCoords x) := by
    filter_upwards [hsT.eventually hM] with n hn x
    have h := hn (0, secondAxis) (x, secondAxis) thirdGenerator thirdGenerator
      norm_thirdGenerator norm_thirdGenerator
    refine h.trans ?_
    have h1 : Real.exp (-(θ * (supDist (0 : TorusSite (2 * L ^ n)) x : ℝ))) ≤
        expWeight (θ / 4) (centredCoords x) := by
      apply Real.exp_le_exp.mpr
      have := sum_abs_centredCoords_le x
      nlinarith
    calc M * _ ≤ |M| * Real.exp (-(θ * (supDist (0 : TorusSite (2 * L ^ n)) x : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hg₁ := abs_le_of_tendsto_torus hsT G₁ g₁ _ _ hb₁ hlim₁
  have hθ4 : 0 < θ / 4 := by positivity
  obtain ⟨hs₁, hs₁'⟩ := summable_and_secondMoment_of_le hθ4 (abs_nonneg M) hg₁
  obtain ⟨θ₂, C₂, hθ₂, hC₂, hκd⟩ := hd a ha L hLs k hk
  let G₂ : ∀ n : ℕ, TorusSite (2 * L ^ n) → ℝ := fun n x =>
    differenceKernelFinite a L n k (centredCoords x)
  have hlim₂ : ∀ w, Tendsto (fun n => G₂ n (siteOfInt w)) atTop (𝓝 (κ w)) := by
    intro w
    refine (hκ w).congr' ?_
    filter_upwards [eventually_two_mul_abs_lt hsT w] with n hn
    simp only [G₂, centredCoords_siteOfInt hn]
  have hb₂ : ∀ᶠ n in atTop, ∀ x, |G₂ n x| ≤ C₂ * expWeight θ₂ (centredCoords x) := hκd
  have hg₂ := abs_le_of_tendsto_torus hsT G₂ κ _ _ hb₂ hlim₂
  obtain ⟨hs₂, hs₂'⟩ := summable_and_secondMoment_of_le hθ₂ hC₂ hg₂
  let S₁ : ℝ → ℝ := fun t => ∑' w, g₁ w * Real.cos (t * ((w 0 : ℤ) : ℝ))
  let S₂ : ℝ → ℝ := fun t => ∑' w, κ w * Real.cos (t * ((w 0 : ℤ) : ℝ))
  have hW₁ : ∀ t, Tendsto (fun n => chainCosineSum a ρ L n k t) atTop (𝓝 (S₁ t)) := fun t =>
    tendsto_cosinePhase_sum hsT G₁ g₁ (fun w => |M| * expWeight (θ / 4) w) ((summable_expWeight hθ4).mul_left _)
      (fun w => mul_nonneg (abs_nonneg _) (expWeight_nonneg _ _)) hb₁ hlim₁ t
  have hW₂ : ∀ t, Tendsto (fun n => differenceCosineSum a L n k t) atTop (𝓝 (S₂ t)) := fun t =>
    tendsto_cosinePhase_sum hsT G₂ κ (fun w => C₂ * expWeight θ₂ w) ((summable_expWeight hθ₂).mul_left _)
      (fun w => mul_nonneg hC₂ (expWeight_nonneg _ _)) hb₂ hlim₂ t
  have hN : ∀ (n₀ : ℕ) (m : ℤ) (t : ℝ), t = 2 * Real.pi * m / (2 * (L : ℝ) ^ n₀) →
      Tendsto (fun n => normaliserCosineSum L n k t) atTop (𝓝 (P t)) := by
    intro n₀ m t htm
    obtain ⟨s₀, ⟨m₀, hm₀, rfl⟩, hlarge⟩ := hch.approx
    have hev : ∀ᶠ n in atTop, ‖normaliserCosineSum L n k t - P t‖ ≤ e n := by
      filter_upwards [eventually_ge_atTop (max (max m₀ 1) n₀)] with n hn
      have hn1 : m₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
      have hn2 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
      have hn3 : n₀ ≤ n := le_trans (le_max_right _ _) hn
      have hpos : 0 < n := hn2
      have hle : PeriodicLattice.torusSide L m₀ ≤ PeriodicLattice.torusSide L n := by
        simp only [PeriodicLattice.torusSide]
        have := pow_le_pow_right₀ hLr.le hn1
        linarith
      have hmem : (Pi.single 0 t : Fin 4 → ℝ) ∈ PeriodicOperators.dualLattice (2 * L ^ n) := by
        refine ⟨Pi.single 0 (m * (L : ℤ) ^ (n - n₀)), fun μ => ?_⟩
        by_cases hμ : μ = 0
        · subst hμ
          have hp : (L : ℝ) ^ n = (L : ℝ) ^ n₀ * (L : ℝ) ^ (n - n₀) := by
            rw [← pow_add, Nat.add_sub_cancel' hn3]
          have hL0 : (L : ℝ) ≠ 0 := by positivity
          simp only [Pi.single_eq_same]
          push_cast
          rw [htm, hp]
          field_simp
        · simp [Pi.single_eq_of_ne hμ]
      have h := hlarge (PeriodicLattice.torusSide L n) ⟨n, hpos, rfl⟩ hle n hpos rfl _ hmem 2 2
        secondAxis secondAxis
      rw [if_pos rfl] at h
      rw [Real.norm_eq_abs]
      refine le_trans ?_ h
      have hre : normaliserCosineSum L n k t - P t =
          (((((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) *
            PeriodicOperators.Tempered.complexHessian (Tower.logNormaliserFamily L k) n
              (PeriodicOperators.Tempered.fourierModeForm L n 2 (Pi.single 0 t) secondAxis)
              (PeriodicOperators.Tempered.fourierModeForm L n 2 (-Pi.single 0 t) secondAxis)) -
            π secondAxis secondAxis (PeriodicOperators.toComplexVec (Pi.single 0 t))).re := by
        simp only [normaliserCosineSum, P, Complex.sub_re]
      rw [hre]
      exact Complex.abs_re_le_norm _
    exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero_norm' (by simpa using hev) hch.err_tendsto)
  have hcont : Tendsto (fun t : ℝ => (Pi.single 0 t : Fin 4 → ℝ)) (𝓝 0) (𝓝 0) := by
    have h : Continuous fun t : ℝ => (Pi.single 0 t : Fin 4 → ℝ) := continuous_pi fun μ => by
      by_cases hμ : μ = 0
      · subst hμ
        simp only [Pi.single_eq_same]
        exact continuous_id
      · simpa [Pi.single_eq_of_ne hμ] using continuous_const
    simpa using h.tendsto 0
  obtain ⟨c₀, hc₀⟩ := ((htensor secondAxis secondAxis).comp_tendsto hcont).bound
  have hkey : ∀ᶠ t in 𝓝 (0 : ℝ), |P t - b * t ^ 2| ≤ c₀ * t ^ 4 := by
    filter_upwards [hc₀] with t ht
    have hE : TorusMetric.euclidNormVec (Pi.single 0 t) = |t| := by
      simp [TorusMetric.euclidNormVec, Real.sqrt_sq_eq_abs, Pi.single_apply]
    have hsd : (Pi.single 0 t : Fin 4 → ℝ) secondAxis = 0 := by
      simp [secondAxis]
    simp only [Function.comp, OneLoopLaw.TemperedStiffness.transverseTensor, hE, hsd, sub_self,
      zero_div, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, if_true, mul_one, sq_abs,
      sub_zero, Real.norm_eq_abs, abs_pow, abs_abs] at ht
    have h1 : |P t - b * t ^ 2| ≤ ‖π secondAxis secondAxis
        (PeriodicOperators.toComplexVec (Pi.single 0 t)) - ((b * t ^ 2 : ℝ) : ℂ)‖ := by
      have := Complex.abs_re_le_norm (π secondAxis secondAxis
        (PeriodicOperators.toComplexVec (Pi.single 0 t)) - ((b * t ^ 2 : ℝ) : ℂ))
      rwa [Complex.sub_re, Complex.ofReal_re] at this
    have h4 : |t| ^ 4 = t ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    rw [h4] at ht
    refine h1.trans (le_trans (le_of_eq ?_) ht)
    push_cast
    rfl
  have hP0 : P 0 = 0 := by
    have h := hkey.self_of_nhds
    simpa using h
  have hPq : Tendsto (fun t : ℝ => P t / t ^ 2) (𝓝[≠] 0) (𝓝 b) := by
    have hz : Tendsto (fun t : ℝ => c₀ * t ^ 2) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => c₀ * t ^ 2) (𝓝 0) (𝓝 (c₀ * 0 ^ 2)) :=
        Continuous.tendsto (by fun_prop) 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖P t / t ^ 2 - b‖ ≤ c₀ * t ^ 2 := by
      filter_upwards [nhdsWithin_le_nhds hkey, self_mem_nhdsWithin] with t ht ht0
      have ht0' : t ≠ 0 := ht0
      have ht2 : 0 < t ^ 2 := by positivity
      have e1 : P t / t ^ 2 - b = (P t - b * t ^ 2) / t ^ 2 := by
        field_simp
      rw [e1, Real.norm_eq_abs, abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
      calc _ ≤ c₀ * t ^ 4 := ht
        _ = _ := by ring
    exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero_norm' (by simpa using hev) hz)
  obtain ⟨C, r, hr, hwave⟩ := hw a ha L hLs k hk ρ hρ hρ1
  have hineq : ∀ (n₀ : ℕ) (m : ℤ) (t : ℝ), t = 2 * Real.pi * m / (2 * (L : ℝ) ^ n₀) → |t| < r →
      |S₁ t - P t - S₂ t| ≤ C * |t| ^ 3 := by
    intro n₀ m t htm htr
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hl := (((hW₁ t).sub (hN n₀ m t htm)).sub (hW₂ t)).abs
    exact le_of_tendsto hl (hwave n₀ m t htm htr ε hε)
  have hzero : S₁ 0 = S₂ 0 := by
    have h := hineq 0 0 0 (by simp) (by simpa using hr)
    simp only [abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, hP0,
      sub_zero] at h
    linarith [abs_nonpos_iff.mp h]
  have hS₁0 : S₁ 0 = ∑' w, g₁ w := by simp [S₁]
  have hS₂0 : S₂ 0 = ∑' w, κ w := by simp [S₂]
  let u : ℕ → ℝ := fun j => 2 * Real.pi * ((1 : ℤ) : ℝ) / (2 * (L : ℝ) ^ j)
  have hu0 : ∀ j, u j ≠ 0 := fun j => by
    have : (L : ℝ) ≠ 0 := by positivity
    simp only [u]
    positivity
  have hut : Tendsto u atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop_atTop_of_one_lt hLr).const_mul_atTop (by norm_num))
  have hu : Tendsto u atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hut, Eventually.of_forall hu0⟩
  have T₁ := (tendsto_cosineSeries_sub_div_sq g₁ hs₁ hs₁').comp hu
  have T₂ := (tendsto_cosineSeries_sub_div_sq κ hs₂ hs₂').comp hu
  have T₃ := hPq.comp hu
  have hE := (T₁.sub T₃).sub T₂
  have hE0 : Tendsto (fun j => C * |u j|) atTop (𝓝 0) := by
    simpa using (hut.abs).const_mul C
  have hEb : ∀ᶠ j in atTop, ‖((fun t : ℝ => (∑' w, g₁ w * Real.cos (t * ((w 0 : ℤ) : ℝ)) - ∑' w, g₁ w) / t ^ 2) ∘ u) j -
      ((fun t : ℝ => P t / t ^ 2) ∘ u) j -
      ((fun t : ℝ => (∑' w, κ w * Real.cos (t * ((w 0 : ℤ) : ℝ)) - ∑' w, κ w) / t ^ 2) ∘ u) j‖ ≤
      C * |u j| := by
    have hsmall : ∀ᶠ j in atTop, |u j| < r := by
      have := hut.abs
      simp only [abs_zero] at this
      exact this.eventually_lt_const hr
    filter_upwards [hsmall] with j hj
    have h := hineq j 1 (u j) rfl hj
    have hu2 : 0 < u j ^ 2 := by have := hu0 j; positivity
    have e1 : ((fun t : ℝ => (∑' w, g₁ w * Real.cos (t * ((w 0 : ℤ) : ℝ)) - ∑' w, g₁ w) / t ^ 2) ∘ u) j -
        ((fun t : ℝ => P t / t ^ 2) ∘ u) j -
        ((fun t : ℝ => (∑' w, κ w * Real.cos (t * ((w 0 : ℤ) : ℝ)) - ∑' w, κ w) / t ^ 2) ∘ u) j =
        (S₁ (u j) - P (u j) - S₂ (u j)) / u j ^ 2 := by
      simp only [Function.comp]
      rw [← hS₁0, ← hS₂0, hzero]
      simp only [S₁, S₂]
      ring
    rw [e1, Real.norm_eq_abs, abs_div, abs_of_pos hu2, div_le_iff₀ hu2]
    calc _ ≤ C * |u j| ^ 3 := h
      _ = C * |u j| * u j ^ 2 := by rw [← sq_abs (u j)]; ring
  have hlimE := tendsto_nhds_unique hE (squeeze_zero_norm' hEb hE0)
  have hv' : ∑' w, -(1 / 2) * g₁ w * ((w 0 : ℤ) : ℝ) ^ 2 = v := hKs.tsum_eq
  have hS : Summable fun w : Fin 4 → ℤ => -(1 / 2) * κ w * ((w 0 : ℤ) : ℝ) ^ 2 := by
    refine Summable.of_norm_bounded (hs₂'.mul_left (1 / 2)) fun w => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      abs_of_nonneg (sq_nonneg ((w 0 : ℤ) : ℝ))]
    exact (mul_assoc _ _ _).le
  have hsumb : ∑ j ∈ Finset.range k, OneLoopLaw.NormaliserLaw.normaliserStiffness hL j = b := by
    rw [← hb, ← hsum]
    rfl
  have hres : v - ∑ j ∈ Finset.range k, OneLoopLaw.NormaliserLaw.normaliserStiffness hL j =
      ∑' w, -(1 / 2) * κ w * ((w 0 : ℤ) : ℝ) ^ 2 := by
    rw [hsumb]
    linarith
  rw [hres]
  exact hS.hasSum
end CoefficientDifference
end YangMills.Construction.RunningCouplingSlope
end
