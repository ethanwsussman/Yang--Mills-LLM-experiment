import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Cumulants.MomentGeneratingFunctionStatement
import YangMills.Construction.InfiniteLattice.PeriodisationAndThreeIdentitiesOfTheCovering
import YangMills.Construction.LawInAState.TheLawInAState
import YangMills.Construction.LawInAState.TheNumberOfTheLawForm
import YangMills.Construction.LawInAState.WilsonsLawIsAProbability
import YangMills.Construction.ParameterData.FirstPassagesAreData
import YangMills.Construction.ParameterData.TheNumberOfTheFlowIsNearOne
import YangMills.Construction.SystemOfAdmissibleConstants.CovarianceOnTheTorusOfSideTwo
import YangMills.Construction.SystemOfAdmissibleConstants.EnvelopesOfTheLevel
import YangMills.Construction.SystemOfAdmissibleConstants.LevelOfADistance
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevel
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPair
import YangMills.Construction.Torus.RescalingLiftsAndFunctionNorms
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
open TrajectoryData StateLaws TestFunctions TorusMetric TorusLumps RenormalizationStepParameters
namespace LevelLaw
private def covar {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  (∫ ω, X ω * Y ω ∂μ) - (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ
private theorem rpow_neg_two_add_split {x : ℝ} (hx : 1 ≤ x) :
    x ^ (-(2 + 1 / 130) : ℝ) = (x ^ 2)⁻¹ * x ^ (-(1 / 130) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have e : (-(2 + 1 / 130) : ℝ) = -2 + -(1 / 130) := by ring
  rw [e, Real.rpow_add hx0, Real.rpow_neg hx0.le]
  norm_num
private theorem cov_factor_of_two_expansions {x al al₀ Kf κ kap cv e₂ e₃ C₁ : ℝ} (hx : 1 ≤ x)
    (hκ : 0 < κ) (hK : κ ≤ Kf) (he₂ : |e₂| ≤ 1 / 2) (he₃ : |e₃| ≤ 1 / 2) (hal₀ : 9 / 16 ≤ al₀ ^ 2)
    (h₂ : kap = al ^ 2 * (9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * Kf * (1 + e₂))
    (h₃ : kap = al₀ ^ 2 * (9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * Kf * (1 + e₃))
    (hδ : |cv - kap| ≤ C₁ * x ^ (-(2 + 1 / 130) : ℝ)) :
    ∃ ε : ℝ, |ε| ≤ |e₂| + C₁ * (16 * Real.pi ^ 4 / (27 * κ)) * x ^ (-(1 / 130) : ℝ) ∧
      cv = al ^ 2 * (9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * Kf * (1 + ε) := by
  have hKf : 0 < Kf := hκ.trans_le hK
  set W : ℝ := (9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * Kf with hW
  have hWpos : 0 < W := by positivity
  have h₂' : kap = al ^ 2 * W * (1 + e₂) := by rw [h₂, hW]; ring
  have h₃' : kap = al₀ ^ 2 * W * (1 + e₃) := by rw [h₃, hW]; ring
  have hcancel : al ^ 2 * (1 + e₂) = al₀ ^ 2 * (1 + e₃) := by
    have : W * (al ^ 2 * (1 + e₂)) = W * (al₀ ^ 2 * (1 + e₃)) := by
      calc W * (al ^ 2 * (1 + e₂)) = kap := by rw [h₂']; ring
        _ = W * (al₀ ^ 2 * (1 + e₃)) := by rw [h₃']; ring
    exact mul_left_cancel₀ hWpos.ne' this
  obtain ⟨a1, a2⟩ := abs_le.mp he₂
  obtain ⟨b1, b2⟩ := abs_le.mp he₃
  have hal : 3 / 16 ≤ al ^ 2 := by
    have hsq : 0 ≤ al ^ 2 := sq_nonneg al
    have l1 : al ^ 2 * (1 + e₂) ≤ al ^ 2 * (3 / 2) := mul_le_mul_of_nonneg_left (by linarith) hsq
    have l2 : al₀ ^ 2 * (1 / 2) ≤ al₀ ^ 2 * (1 + e₃) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg al₀)
    nlinarith
  have hD : 0 < al ^ 2 * W := by positivity
  refine ⟨e₂ + (cv - kap) / (al ^ 2 * W), ?_, ?_⟩
  · refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_div, abs_of_pos hD]
    have hlow : (27 * κ / (16 * Real.pi ^ 4)) * (x ^ 2)⁻¹ ≤ al ^ 2 * W := by
      have h1 : (3 / 16 : ℝ) * ((9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * κ) ≤
          al ^ 2 * ((9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * Kf) :=
        mul_le_mul hal (mul_le_mul_of_nonneg_left hK (by positivity)) (by positivity) (sq_nonneg al)
      calc (27 * κ / (16 * Real.pi ^ 4)) * (x ^ 2)⁻¹
          = (3 / 16 : ℝ) * ((9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * κ) := by field_simp; ring
        _ ≤ al ^ 2 * W := h1
    have hnum : 0 ≤ C₁ * x ^ (-(2 + 1 / 130) : ℝ) := (abs_nonneg _).trans hδ
    calc |cv - kap| / (al ^ 2 * W)
        ≤ C₁ * x ^ (-(2 + 1 / 130) : ℝ) / ((27 * κ / (16 * Real.pi ^ 4)) * (x ^ 2)⁻¹) :=
          div_le_div₀ hnum hδ (by positivity) hlow
      _ = C₁ * (16 * Real.pi ^ 4 / (27 * κ)) * x ^ (-(1 / 130) : ℝ) := by
          rw [rpow_neg_two_add_split hx]
          field_simp
  · have e : al ^ 2 * (9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * Kf = al ^ 2 * W := by rw [hW]; ring
    rw [e, mul_add, mul_one, mul_add, ← add_assoc, mul_div_cancel₀ _ hD.ne']
    have : al ^ 2 * W + al ^ 2 * W * e₂ = kap := by rw [h₂']; ring
    rw [this]; ring
private theorem two_mul_rpow_le_half {x c : ℝ} (hc : 0 ≤ c) (hx : (4 * c + 1) ^ 200 ≤ x) :
    2 * c * x ^ (-(1 / 200) : ℝ) ≤ 1 / 2 := by
  have h1 : (0 : ℝ) < 4 * c + 1 := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h2 : 4 * c + 1 ≤ x ^ ((1 : ℝ) / 200) := by
    have := Real.rpow_le_rpow (by positivity) hx (show (0 : ℝ) ≤ 1 / 200 by norm_num)
    have e : ((4 * c + 1) ^ 200 : ℝ) ^ ((1 : ℝ) / 200) = 4 * c + 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h1.le]
      norm_num
    rwa [e] at this
  have h3 : x ^ (-(1 / 200) : ℝ) ≤ (4 * c + 1)⁻¹ := by
    rw [Real.rpow_neg hx0.le]
    exact inv_anti₀ h1 h2
  calc 2 * c * x ^ (-(1 / 200) : ℝ) ≤ 2 * c * (4 * c + 1)⁻¹ :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ 1 / 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ h1]
        linarith
private theorem error_sum_le {x n C : ℝ} (hx : 1 ≤ x) (hn : x ^ ((1 : ℝ) / 100) ≤ n) :
    C * n ^ (-(1 / 2) : ℝ) + C * x ^ (-(1 / 130) : ℝ) ≤ 2 * |C| * x ^ (-(1 / 200) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hp : 0 < x ^ ((1 : ℝ) / 100) := by positivity
  have hn0 : 0 < n := hp.trans_le hn
  have h1 : n ^ (-(1 / 2) : ℝ) ≤ x ^ (-(1 / 200) : ℝ) := by
    have := Real.rpow_le_rpow_of_nonpos hp hn (show (-(1 / 2) : ℝ) ≤ 0 by norm_num)
    have e : (x ^ ((1 : ℝ) / 100)) ^ (-(1 / 2) : ℝ) = x ^ (-(1 / 200) : ℝ) := by
      rw [← Real.rpow_mul hx0.le]
      norm_num
    rwa [e] at this
  have h2 : x ^ (-(1 / 130) : ℝ) ≤ x ^ (-(1 / 200) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have p1 : 0 ≤ n ^ (-(1 / 2) : ℝ) := by positivity
  have p2 : 0 ≤ x ^ (-(1 / 130) : ℝ) := by positivity
  have a1 : C * n ^ (-(1 / 2) : ℝ) ≤ |C| * x ^ (-(1 / 200) : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) p1).trans
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg C))
  have a2 : C * x ^ (-(1 / 130) : ℝ) ≤ |C| * x ^ (-(1 / 200) : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) p2).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg C))
  linarith
private theorem euclidNormVec_le_two_mul_norm (v : Fin 4 → ℝ) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
private theorem continuous_of_isLipschitzFor {f : InfiniteLattice.AmbientSpace → ℝ}
    (hf : IsLipschitzFor euclidDistR4 f) : Continuous f := by apply _root_.YangMills.Construction.TestPairs.continuous_of_isLipschitzFor_r4 <;> assumption
abbrev _root_.YangMills.SharedProofs.p29528 := @continuous_of_isLipschitzFor
private theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
private theorem isCompact_closedBallR4 (c : Fin 4 → ℝ) (r : ℝ) : IsCompact (closedBallR4 c r) := by
  have hcl : IsClosed (closedBallR4 c r) :=
    isClosed_le (continuous_euclidNormVec.comp (continuous_id.sub continuous_const)) continuous_const
  refine (isCompact_closedBall c r).of_isClosed_subset hcl fun y hy => ?_
  have hy' : euclidNormVec (y - c) ≤ r := hy
  have hr : 0 ≤ r := (Real.sqrt_nonneg _).trans hy'
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg hr).2 fun μ => ?_
  refine le_trans ?_ hy'
  refine Real.le_sqrt_of_sq_le ?_
  rw [Real.norm_eq_abs, sq_abs]
  exact Finset.single_le_sum (f := fun ν => (y - c) ν ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ μ)
abbrev _root_.YangMills.DeltaSharedProofs.p501115 := @isCompact_closedBallR4
abbrev _root_.YangMills.SharedProofs.p20989 := @isCompact_closedBallR4
private theorem boundedBorel_of_bump {f : InfiniteLattice.AmbientSpace → ℝ} {x : InfiniteLattice.AmbientSpace}
    {d : ℝ} (hl : IsLipschitzFor euclidDistR4 f) (hs : tsupport f ⊆ closedBallR4 x d) :
    InfiniteLattice.IsBoundedBorelCompactlySupported f := by
  have hc := continuous_of_isLipschitzFor hl
  have hcs : HasCompactSupport f :=
    (isCompact_closedBallR4 x d).of_isClosed_subset (isClosed_tsupport f) hs
  exact ⟨hc.measurable, hcs.exists_bound_of_continuous hc, hcs⟩
private theorem boundedBorel_of_mem {d vt : ℝ} {f h : InfiniteLattice.AmbientSpace → ℝ}
    (hp : (f, h) ∈ separatedPairsR4 d vt) :
    InfiniteLattice.IsBoundedBorelCompactlySupported f ∧ InfiniteLattice.IsBoundedBorelCompactlySupported h := by
  obtain ⟨x₁, x₂, h₁, h₂, -, -⟩ := hp
  exact ⟨boundedBorel_of_bump h₁.1 h₁.2.2.2.1, boundedBorel_of_bump h₂.1 h₂.2.2.2.1⟩
private theorem boundedBorel_fin_two {d vt : ℝ} {f h : InfiniteLattice.AmbientSpace → ℝ}
    (hp : (f, h) ∈ separatedPairsR4 d vt) :
    ∀ i, InfiniteLattice.IsBoundedBorelCompactlySupported (![f, h] i) := by
  intro i
  fin_cases i
  · exact (boundedBorel_of_mem hp).1
  · exact (boundedBorel_of_mem hp).2
private theorem uniformNorm_const_mul {f : InfiniteLattice.AmbientSpace → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    uniformNorm (fun x => c * f x) = c * uniformNorm f := by
  unfold uniformNorm
  rw [Real.mul_iSup_of_nonneg hc]
  congr 1
  funext x
  rw [norm_mul, Real.norm_of_nonneg hc]
private theorem isLipschitzFor_const_mul {dist : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace → ℝ}
    {f : InfiniteLattice.AmbientSpace → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : IsLipschitzFor dist f) : IsLipschitzFor dist (fun x => c * f x) := by
  obtain ⟨C, hC0, hC⟩ := hf
  refine ⟨c * C, by positivity, fun x y => ?_⟩
  rw [← mul_sub, norm_mul, Real.norm_of_nonneg hc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC x y) hc
private theorem bestLipschitzConstant_const_mul
    {dist : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace → ℝ}
    {f : InfiniteLattice.AmbientSpace → ℝ} {c : ℝ} (hc : 0 < c) (hf : IsLipschitzFor dist f) :
    bestLipschitzConstant dist (fun x => c * f x) ≤ c * bestLipschitzConstant dist f := by
  have hmem : ({C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * dist x y}).Nonempty := by
    obtain ⟨C, hC0, hC⟩ := hf
    exact ⟨C, hC0, hC⟩
  have h1 : c⁻¹ * bestLipschitzConstant dist (fun x => c * f x) ≤ bestLipschitzConstant dist f := by
    refine le_csInf hmem fun C hC => ?_
    have h2 : bestLipschitzConstant dist (fun x => c * f x) ≤ c * C := by
      refine csInf_le ⟨0, fun _ h => h.1⟩ ⟨by have := hC.1; positivity, fun x y => ?_⟩
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg hc.le, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC.2 x y) hc.le
    rw [inv_mul_le_iff₀ hc]
    exact h2
  rwa [inv_mul_le_iff₀ hc] at h1
private theorem tsupport_const_mul {f : InfiniteLattice.AmbientSpace → ℝ} {c : ℝ} (hc : c ≠ 0) :
    tsupport (fun x => c * f x) = tsupport f := by
  unfold tsupport
  congr 1
  ext x
  simp [Function.mem_support, hc]
private theorem isShapedBump_const_mul {d vt c : ℝ} {x : InfiniteLattice.AmbientSpace}
    {f : InfiniteLattice.AmbientSpace → ℝ} (hd : 0 < d) (hvt : 0 < vt) (hc : 0 < c)
    (hb : IsShapedBump euclidDistR4 closedBallR4 (fun f => ∫ x, f x) d vt x f) :
    IsShapedBump euclidDistR4 closedBallR4 (fun f => ∫ x, f x) d vt x (fun x => c * f x) := by
  obtain ⟨b₁, b₂, ⟨y, hy⟩, b₄, b₅, b₆⟩ := hb
  refine ⟨isLipschitzFor_const_mul hc.le b₁, fun y => mul_nonneg hc.le (b₂ y),
    ⟨y, mul_ne_zero hc.ne' hy⟩, ?_, ?_, ?_⟩
  · rw [tsupport_const_mul hc.ne']
    exact b₄
  · have b₅' : vt * uniformNorm f * d ^ 4 ≤ ∫ x, f x := b₅
    show vt * uniformNorm (fun x => c * f x) * d ^ 4 ≤ ∫ x, c * f x
    rw [uniformNorm_const_mul hc.le, integral_const_mul]
    have := mul_le_mul_of_nonneg_left b₅' hc.le
    calc vt * (c * uniformNorm f) * d ^ 4 = c * (vt * uniformNorm f * d ^ 4) := by ring
      _ ≤ _ := this
  · rw [uniformNorm_const_mul hc.le]
    refine (bestLipschitzConstant_const_mul hc b₁).trans ?_
    have := mul_le_mul_of_nonneg_left b₆ hc.le
    calc _ ≤ c * (uniformNorm f / (vt * d)) := this
      _ = c * uniformNorm f / (vt * d) := by ring
private theorem const_mul_mem_separatedPairs {d vt a b : ℝ} {f h : InfiniteLattice.AmbientSpace → ℝ}
    (hd : 0 < d) (hvt : 0 < vt) (ha : 0 < a) (hb : 0 < b) (hp : (f, h) ∈ separatedPairsR4 d vt) :
    ((fun x => a * f x), (fun x => b * h x)) ∈ separatedPairsR4 d vt := by
  obtain ⟨x₁, x₂, h₁, h₂, h₃, h₄⟩ := hp
  refine ⟨x₁, x₂, isShapedBump_const_mul hd hvt ha h₁, isShapedBump_const_mul hd hvt hb h₂, ?_, ?_⟩
  · simp only [tsupport_const_mul ha.ne', tsupport_const_mul hb.ne']
    exact h₃
  · simp only [tsupport_const_mul ha.ne', tsupport_const_mul hb.ne']
    exact h₄
private theorem uniformNorm_pos {f : InfiniteLattice.AmbientSpace → ℝ} {x : InfiniteLattice.AmbientSpace}
    {d vt : ℝ} (hb : IsShapedBump euclidDistR4 closedBallR4 (fun f => ∫ x, f x) d vt x f) :
    0 < uniformNorm f := by
  obtain ⟨b₁, -, ⟨y, hy⟩, b₄, -, -⟩ := hb
  obtain ⟨-, ⟨C, hC⟩, -⟩ := boundedBorel_of_bump b₁ b₄
  have hbdd : BddAbove (range fun x => ‖f x‖) := ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  exact (norm_pos_iff.mpr hy).trans_le (le_ciSup hbdd y)
private theorem exists_normalized_pair {d vt : ℝ} {f h : InfiniteLattice.AmbientSpace → ℝ} (hd : 0 < d)
    (hvt : 0 < vt) (hp : (f, h) ∈ separatedPairsR4 d vt) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      IsNormalizedTestPair d vt (fun x => a⁻¹ * f x) (fun x => b⁻¹ * h x) := by
  obtain ⟨x₁, x₂, h₁, h₂, -, -⟩ := id hp
  have ha := uniformNorm_pos h₁
  have hb := uniformNorm_pos h₂
  refine ⟨uniformNorm f, uniformNorm h, ha, hb,
    const_mul_mem_separatedPairs hd hvt (inv_pos.mpr ha) (inv_pos.mpr hb) hp, ?_, ?_⟩
  · rw [uniformNorm_const_mul (inv_pos.mpr ha).le, inv_mul_cancel₀ ha.ne']
  · rw [uniformNorm_const_mul (inv_pos.mpr hb).le, inv_mul_cancel₀ hb.ne']
private theorem inverseEighthKernel_const_mul (f h : InfiniteLattice.AmbientSpace → ℝ) (a b : ℝ) :
    inverseEighthKernel (fun x => a * f x) (fun x => b * h x) = a * b * inverseEighthKernel f h := by
  unfold inverseEighthKernel
  rw [← integral_const_mul]
  congr 1
  funext z
  ring
private theorem smearedEnergy_const_mul {s : ℝ} (f : InfiniteLattice.AmbientSpace → ℝ) (c : ℝ)
    (U : InfiniteLattice.GaugeField s) :
    InfiniteLattice.smearedEnergy (fun x => c * f x) U = c * InfiniteLattice.smearedEnergy f U := by
  unfold InfiniteLattice.smearedEnergy
  rw [← smul_eq_mul, smul_finsum]
  congr 1
  funext p
  simp only [smul_eq_mul]
  ring
private theorem covar_const_mul {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) (a b : ℝ) :
    covar μ (fun ω => a * X ω) (fun ω => b * Y ω) = a * b * covar μ X Y := by
  unfold covar
  have e : (fun ω => a * X ω * (b * Y ω)) = fun ω => a * b * (X ω * Y ω) := by
    funext ω
    ring
  rw [e, integral_const_mul, integral_const_mul, integral_const_mul]
  ring
private theorem expansion_const_mul {s : ℝ} {μ : Measure (InfiniteLattice.GaugeField s)}
    {F H : InfiniteLattice.AmbientSpace → ℝ} {A B : ℝ}
    (hlaw : ∃ ε : ℝ, |ε| ≤ B ∧ covar μ (fun U => InfiniteLattice.smearedEnergy F U)
      (fun U => InfiniteLattice.smearedEnergy H U) = A * inverseEighthKernel F H * (1 + ε)) (a b : ℝ) :
    ∃ ε : ℝ, |ε| ≤ B ∧
      covar μ (fun U => InfiniteLattice.smearedEnergy (fun x => a * F x) U)
          (fun U => InfiniteLattice.smearedEnergy (fun x => b * H x) U) =
        A * inverseEighthKernel (fun x => a * F x) (fun x => b * H x) * (1 + ε) := by
  obtain ⟨ε, hε, h⟩ := hlaw
  refine ⟨ε, hε, ?_⟩
  simp only [smearedEnergy_const_mul]
  rw [covar_const_mul, h, inverseEighthKernel_const_mul]
  ring
private theorem cumulant_eq_covar (hGen : Cumulants.MomentGeneratingFunctionRegularity) {s : ℝ}
    (ν : Measure (InfiniteLattice.GaugeField s)) [IsProbabilityMeasure ν] {f h : InfiniteLattice.AmbientSpace → ℝ}
    (hf : Measurable (InfiniteLattice.smearedEnergy (a := s) f))
    (hh : Measurable (InfiniteLattice.smearedEnergy (a := s) h))
    (bf : ∃ C : ℝ, ∀ U, |InfiniteLattice.smearedEnergy (a := s) f U| ≤ C)
    (bh : ∃ C : ℝ, ∀ U, |InfiniteLattice.smearedEnergy (a := s) h U| ≤ C) :
    InfiniteLattice.smearedEnergyCumulant ν ![f, h] =
      ((covar ν (fun U => InfiniteLattice.smearedEnergy f U)
        (fun U => InfiniteLattice.smearedEnergy h U) : ℝ) : ℂ) := by
  have e : (fun (i : Fin 2) (U : InfiniteLattice.GaugeField s) => InfiniteLattice.smearedEnergy (![f, h] i) U) =
      ![fun U => InfiniteLattice.smearedEnergy f U, fun U => InfiniteLattice.smearedEnergy h U] := by
    funext i
    fin_cases i <;> rfl
  unfold InfiniteLattice.smearedEnergyCumulant
  rw [e]
  exact (hGen _ ν).2 _ _ hf hh bf bh
private theorem covariance_eq_covar {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (bX : ∃ C : ℝ, ∀ ω, |X ω| ≤ C)
    (bY : ∃ C : ℝ, ∀ ω, |Y ω| ≤ C) : cov[X, Y; μ] = covar μ X Y := by
  obtain ⟨C, hC⟩ := bX
  obtain ⟨C', hC'⟩ := bY
  have m1 : MemLp X 2 μ := MemLp.of_bound hX.aestronglyMeasurable C (ae_of_all _ hC)
  have m2 : MemLp Y 2 μ := MemLp.of_bound hY.aestronglyMeasurable C' (ae_of_all _ hC')
  rw [covariance_eq_sub m1 m2]
  rfl
private theorem exists_close_lifts {S : ℝ} (x₁ x₂ : Torus4 S) :
    ∃ X₁ X₂ : Fin 4 → ℝ, torusProj S X₁ = x₁ ∧ torusProj S X₂ = x₂ ∧
      euclidDistR4 X₁ X₂ = euclidDistTorus x₁ x₂ := by
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm ((x₁ - x₂) μ)
  have hX := torusProj_liftPoint x₂
  refine ⟨liftPoint x₂ + b, liftPoint x₂, ?_, hX, ?_⟩
  · funext μ
    have h1 : (liftPoint x₂ μ : AddCircle S) = x₂ μ := congrFun hX μ
    have h2 : (b μ : AddCircle S) = x₁ μ - x₂ μ := hb μ
    simp [torusProj, h1, h2]
  · unfold euclidDistR4 euclidDistTorus
    rw [TorusAnalysis.torusEuclidNorm_eq_sqrt_sum_norm_sq, add_sub_cancel_left]
    simp only [euclidNormVec, ← hb', sq_abs]
private theorem eq_of_liftToBall_eq {S r : ℝ} {c : Fin 4 → ℝ} {g f : Torus4 S → ℝ}
    (hg : LiftsToBall S c r g) (hf : LiftsToBall S c r f) (h : liftToBall S c r g = liftToBall S c r f) :
    g = f := by
  funext u
  by_cases hu : u ∈ torusProj S '' closedBallR4 c r
  · obtain ⟨v, hv, rfl⟩ := hu
    have := congrFun h v
    simpa [liftToBall, indicator_of_mem hv] using this
  · rw [hg.2.2 u hu, hf.2.2 u hu]
private theorem exists_lift_pair (hGeo : TestPairs.GeometryAndKernelBounds) {L' : ℕ} {ℓ d vt : ℝ}
    (hd : 0 < d) (hvt : 0 < vt) (hvt1 : vt ≤ 1) (hs : IsAdmissibleSide L' ℓ d) {f h : Torus4 ℓ → ℝ}
    (hp : (f, h) ∈ separatedPairsTorus ℓ d vt) :
    ∃ ψ₁ ψ₂ : InfiniteLattice.AmbientSpace → ℝ, (ψ₁, ψ₂) ∈ separatedPairsR4 d vt ∧ periodize ℓ ψ₁ = f ∧
      periodize ℓ ψ₂ = h ∧ inverseEighthKernel ψ₁ ψ₂ = inverseEighthKernelTorus f h := by
  obtain ⟨-, -, x₁, x₂, hc⟩ := (mem_separatedPairs_iff _ _ _ _ _ _ _).1 hp
  have hss : IsSepShapePair d vt := ⟨hd, hvt, hvt1⟩
  obtain ⟨X₁, X₂, e₁, e₂, e₃⟩ := exists_close_lifts x₁ x₂
  obtain ⟨-, -, hB₁, hB₂, hmem, hcen, hkeep⟩ := (hGeo.2 L' ℓ d vt hss hs x₁ x₂ f h hp hc).2 X₁ X₂ e₁ e₂ e₃
  obtain ⟨-, -, -, -, hT₁, hT₂, hl₁, hl₂, -⟩ := (hGeo.1 d vt hss X₁ X₂ _ _ hmem hcen).2 L' ℓ hs
  refine ⟨_, _, hmem, ?_, ?_, hkeep.2.2.2.2.2.2.2⟩
  · exact eq_of_liftToBall_eq hT₁ hB₁ hl₁
  · exact eq_of_liftToBall_eq hT₂ hB₂ hl₂
private theorem torus_covariance (hGen : Cumulants.MomentGeneratingFunctionRegularity)
    (hCov : PeriodizationIdentities.Statement)
    (hTwo : AdmissibleConstants.SideTwoTorusCovariance) (hProb : WilsonLaw.LiftedWilsonMeasureIsProbability)
    {L m K : ℕ} {β : ℝ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (hβ : 0 < β)
    {ψ₁ ψ₂ : InfiniteLattice.AmbientSpace → ℝ}
    (b₁ : InfiniteLattice.IsBoundedBorelCompactlySupported ψ₁)
    (b₂ : InfiniteLattice.IsBoundedBorelCompactlySupported ψ₂) :
    PeriodicLattice.torusUrsellFunction L m K β
        ![periodize (PeriodicLattice.torusSide L m) ψ₁, periodize (PeriodicLattice.torusSide L m) ψ₂] =
      ((covar (InfiniteLattice.liftedWilsonMeasure L m K β) (fun U => InfiniteLattice.smearedEnergy ψ₁ U)
        (fun U => InfiniteLattice.smearedEnergy ψ₂ U) : ℝ) : ℂ) := by
  have hL1 : 1 < L := by have := hL.2; omega
  have hb : ∀ i, InfiniteLattice.IsBoundedBorelCompactlySupported (![ψ₁, ψ₂] i) := by
    intro i
    fin_cases i
    · exact b₁
    · exact b₂
  have hmb := ((hCov L 1 K hL one_pos hK β hβ).2.2.2.1 2 ![ψ₁, ψ₂] (by norm_num) hb).2.1
  have hP := hProb L m K β hL1
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [hTwo L K hL hK β hβ ψ₁ ψ₂ b₁ b₂]
    have hP' : IsProbabilityMeasure (unitTorusMeasure L K β) := hP
    exact congrArg _ (covariance_eq_covar _ (hmb 0).1 (hmb 1).1 (hmb 0).2 (hmb 1).2)
  · obtain ⟨-, -, hc, -, -⟩ := (hCov L m K hL hm hK β hβ).2.2.2.1 2 ![ψ₁, ψ₂] (by norm_num) hb
    have e : InfiniteLattice.PeriodicLiftAtCutoff.periodizeTuple L m ![ψ₁, ψ₂] =
        ![periodize (PeriodicLattice.torusSide L m) ψ₁, periodize (PeriodicLattice.torusSide L m) ψ₂] := by
      funext i
      fin_cases i <;> rfl
    rw [e] at hc
    refine hc.symm.trans ?_
    exact cumulant_eq_covar hGen _ (hmb 0).1 (hmb 1).1 (hmb 0).2 (hmb 1).2
private theorem two_le_torusSide {L m : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) :
    (2 : ℝ) ≤ PeriodicLattice.torusSide L m := by
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := hL.2; omega : 1 ≤ L)
  have h2 : (1 : ℝ) ≤ (L : ℝ) ^ m := one_le_pow₀ h1
  unfold PeriodicLattice.torusSide
  linarith
private theorem exists_admissibleSide {L m : ℕ} {d : ℝ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (h40 : 40 * d ≤ PeriodicLattice.torusSide L m) :
    ∃ L' : ℕ, IsAdmissibleSide L' (PeriodicLattice.torusSide L m) d := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨1, ⟨1, one_pos, by simp [PeriodicLattice.torusSide]⟩, h40⟩
  · exact ⟨L, ⟨m, hm, rfl⟩, h40⟩
private theorem holdsOnAssignments_and {P Q : ParameterAssignment → ℝ → Prop} (hP : ResponseInTheExpansion.HoldsOnParameterFamilies P)
    (hQ : ResponseInTheExpansion.HoldsOnParameterFamilies Q) :
    ResponseInTheExpansion.HoldsOnParameterFamilies fun T y => P T y ∧ Q T y := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, h₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂, hr₂, h₂⟩ := hQ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hLL T e1 e2 d1 d2 d3 d4 d5
  obtain ⟨y₁, hy₁⟩ := h₁ L hL ((le_max_left _ _).trans hLL) T e1 e2 d1 d2 d3 (d4.trans (min_le_left _ _))
    ((le_max_left _ _).trans d5)
  obtain ⟨y₂, hy₂⟩ := h₂ L hL ((le_max_right _ _).trans hLL) T e1 e2 d1 d2 d3 (d4.trans (min_le_right _ _))
    ((le_max_right _ _).trans d5)
  exact ⟨max y₁ y₂, fun y hy hR hW =>
    ⟨hy₁ y ((le_max_left _ _).trans hy) hR hW, hy₂ y ((le_max_right _ _).trans hy) hR hW⟩⟩
abbrev _root_.YangMills.SharedProofs.p24215 := @holdsOnAssignments_and
end LevelLaw
set_option maxHeartbeats 1000000 in
open LevelLaw in
theorem levelLawStatement_holds (hState : covarianceApproxStatement)
    (hNum : covarianceAtSeparationStatement)
    (hOne : responseCoeffNearOneStatement)
    (hEnv : levelEnvelopesStatement)
    (hLev : separationLevelStatement)
    (hData : windowMembersAreDataStatement)
    (hGen : Cumulants.MomentGeneratingFunctionRegularity)
    (hGeo : TestPairs.GeometryAndKernelBounds)
    (hCov : PeriodizationIdentities.Statement)
    (hTwo : AdmissibleConstants.SideTwoTorusCovariance)
    (hProb : WilsonLaw.LiftedWilsonMeasureIsProbability) : levelLawStatement := by
  have hTab := holdsOnAssignments_and hState (holdsOnAssignments_and (show ResponseInTheExpansion.HoldsOnParameterFamilies _ from hEnv)
    (show ResponseInTheExpansion.HoldsOnParameterFamilies _ from hLev))
  intro a ha
  obtain ⟨L₁, r₁, B₁, hr₁, H₁⟩ := hTab a ha
  obtain ⟨L₂, r₂, B₂, hr₂, H₂⟩ := hNum a ha
  obtain ⟨L₃, r₃, B₃, hr₃, H₃⟩ := hOne a ha
  refine ⟨max L₁ (max L₂ L₃), fun c => min (r₁ c) (min (r₂ c) (r₃ c)), max B₁ (max B₂ B₃),
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)), ?_⟩
  intro L hL hLL T e1 e2 hDr d2 d3 d4 d5 Kr
  have l1 : L₁ ≤ L := (le_max_left _ _).trans hLL
  have l2 : L₂ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLL)
  have l3 : L₃ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLL)
  have t1 : T.rt ≤ r₁ T.toChainParameters := d4.trans (min_le_left _ _)
  have t2 : T.rt ≤ r₂ T.toChainParameters := d4.trans ((min_le_right _ _).trans (min_le_left _ _))
  have t3 : T.rt ≤ r₃ T.toChainParameters := d4.trans ((min_le_right _ _).trans (min_le_right _ _))
  have c1 : B₁ ≤ T.derivBound := (le_max_left _ _).trans d5
  have c2 : B₂ ≤ T.derivBound := (le_max_left _ _).trans ((le_max_right _ _).trans d5)
  have c3 : B₃ ≤ T.derivBound := (le_max_right _ _).trans ((le_max_right _ _).trans d5)
  obtain ⟨z₁, G₁⟩ := H₁ L hL l1 T e1 e2 hDr d2 d3 t1 c1
  obtain ⟨z₂, G₂⟩ := H₂ L hL l2 T e1 e2 hDr d2 d3 t2 c2 Kr
  obtain ⟨Kr₀, hF₀, z₃, G₃⟩ := H₃ L hL l3 T e1 e2 hDr d2 d3 t3 c3
  obtain ⟨z₄, G₄⟩ := H₂ L hL l2 T e1 e2 hDr d2 d3 t2 c2 Kr₀
  refine ⟨max (max z₁ z₂) (max z₃ z₄), fun y hy hRow hKr D hD g hg hfl vt hvt hvt1 => ?_⟩
  have f1 : z₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have f2 : z₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have f3 : z₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have f4 : z₄ ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  obtain ⟨hS, hE, hV⟩ := G₁ y f1 hRow.returns_at hRow.wilson_expansion
  have hN := G₂ y f2 hRow hKr
  have hN₀ := G₄ y f4 hRow (hF₀ y)
  have hO : ∀ (β : ℝ) (k : ℕ), (∀ j ≤ k, y ≤ ResponseInTheExpansion.flowCouplings (T.stepParameters y) β j) →
      ∃ al : ℕ → ℝ, ResponseInTheExpansion.IsChainResponseCoeff (T.stepParameters y) Kr₀ β k al ∧
        |al k - 1| ≤ 1 / 4 := by
    intro β k hj
    obtain ⟨al, hal, h1, h2⟩ := G₃ y f3 hRow.returns_at hRow.wilson_expansion β k hj
    exact ⟨al, hal, h1.trans h2⟩
  have hstar : D.floorStar ≤ g ^ (-2 : ℤ) := (le_max_left _ _).trans hfl
  have hoff : 0 ≤ oneLoopDeviation T := Real.iSup_nonneg fun _ => abs_nonneg _
  have hyg : y ≤ g ^ (-2 : ℤ) := by
    have h1 : y + 2 * oneLoopDeviation T + 1 ≤ inverseCouplingFloor D :=
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_of_eq rfl)))
    linarith
  have hXi : (T.stepParameters y).y₁ + 2 * (T.stepParameters y).B ≤ D.threshold g := by
    have h2 : 2 * T.B ≤ D.shift := hD.shift_ge
    show y + 2 * T.B ≤ g ^ (-2 : ℤ) + D.shift
    linarith
  obtain ⟨C₁, d₁, hd₁, h₁⟩ := hS (D.threshold g) hXi vt hvt hvt1
  obtain ⟨C₂, d₂, hd₂, h₂⟩ := hN (D.threshold g) hXi vt hvt hvt1
  obtain ⟨C₃, d₃, hd₃, h₃⟩ := hN₀ (D.threshold g) hXi vt hvt hvt1
  obtain ⟨henv, -, hanti, -, -, -⟩ := hE D hD g hg hfl
  set dm : ℝ := min (min d₁ d₂) (min d₃ (1 / 2)) with hdm
  have hdm0 : 0 < dm := lt_min (lt_min hd₁ hd₂) (lt_min hd₃ (by norm_num))
  have hdm1 : dm < 1 := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  set κ : ℝ := TestPairs.kernelLowerConst * vt ^ 2 with hκdef
  have hκ0 : 0 < κ := by
    have : (0 : ℝ) < TestPairs.kernelLowerConst := by unfold TestPairs.kernelLowerConst; positivity
    positivity
  set Q : ℝ := 16 * Real.pi ^ 4 / (27 * κ) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨max 1 (max (AdmissibleConstants.upperCouplingEnvelope D g dm + 1)
      (max ((4 * |C₂| + 1) ^ 200) ((4 * |C₃| + 1) ^ 200))),
    2 * |C₂| + |C₁| * Q, le_max_left _ _, by positivity, ?_⟩
  intro d hd hd1 K β hdat hXL hsmall al hal
  set k : ℕ := separationLevel (T.stepParameters y) β K d with hk
  set x : ℝ := D.coupling β k with hx
  have hK2 : 2 ≤ (K : ℕ) := (le_max_left _ _).trans hdat.2
  have hTD := hData T y D hD g hg hstar K β hK2 hdat.1
  have hdatum : IsFlowDatum (T.stepParameters y) (D.threshold g) K β := ⟨hK2, hTD.floor, hTD.le_threshold⟩
  obtain ⟨hfar, hlt, -⟩ := hV D hD g hg hfl d hd hd1 K β hdat
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hXL
  have hx0 : 0 < x := by linarith
  have hdle : d ≤ dm := by
    by_contra hcon
    have hup : AdmissibleConstants.upperCouplingEnvelope D g d ≤
        AdmissibleConstants.upperCouplingEnvelope D g dm :=
      hanti ⟨hdm0, hdm1⟩ ⟨hd, hd1⟩ (not_le.mp hcon).le
    have h3 : x ≤ AdmissibleConstants.upperCouplingEnvelope D g d := (henv d hd hd1 K β hdat).2.1
    have h4 : AdmissibleConstants.upperCouplingEnvelope D g dm + 1 ≤ x :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hXL)
    linarith
  have hdd₁ : d ≤ d₁ := hdle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hdd₂ : d ≤ d₂ := hdle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hdd₃ : d ≤ d₃ := hdle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hn : x ^ ((1 : ℝ) / 100) ≤ lengthInSites (T.stepParameters y).side K k d := by
    have h1 : x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) := Nat.le_ceil _
    have h2 : (2 : ℝ) ^ 12 * (clusterRange x : ℝ) ≤ lengthInSites (T.stepParameters y).side K k d := hfar.1.2
    have h3 : (0 : ℝ) ≤ (clusterRange x : ℝ) := Nat.cast_nonneg _
    nlinarith
  obtain ⟨al₀, hal₀, hnear⟩ := hO β k fun j hj => hTD.floor j (hj.trans hlt.le)
  have hsq : 9 / 16 ≤ al₀ k ^ 2 := by
    obtain ⟨n1, -⟩ := abs_le.mp hnear
    have h34 : (3 / 4 : ℝ) ≤ al₀ k := by linarith
    have := pow_le_pow_left₀ (by norm_num) h34 2
    norm_num at this ⊢
    linarith
  have hsm₂ : 2 * |C₂| * x ^ (-(1 / 200) : ℝ) ≤ 1 / 2 :=
    two_mul_rpow_le_half (abs_nonneg _) ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hXL)))
  have hsm₃ : 2 * |C₃| * x ^ (-(1 / 200) : ℝ) ≤ 1 / 2 :=
    two_mul_rpow_le_half (abs_nonneg _) ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hXL)))
  have hrate := Real.rpow_le_rpow_of_exponent_le hx1 (show (-(1 / 130) : ℝ) ≤ -(1 / 200) by norm_num)
  have hpos200 : 0 ≤ x ^ (-(1 / 200) : ℝ) := by positivity
  have hnormal : ∀ f h : InfiniteLattice.AmbientSpace → ℝ, IsNormalizedTestPair d vt f h →
      ∀ μ : Measure (LatticeConfig (T.stepParameters y).side K),
        IsAdmissibleState (T.stepParameters y).side K β μ →
      ∃ ε : ℝ, |ε| ≤ (2 * |C₂| + |C₁| * Q) * x ^ (-(1 / 200) : ℝ) ∧
        cov[smearedObservable (T.stepParameters y).side K f, smearedObservable (T.stepParameters y).side K h; μ] =
          al k ^ 2 * (9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * inverseEighthKernel f h * (1 + ε) := by
    intro f h hpair μ hμ
    obtain ⟨e₂, he₂, hk₂⟩ := h₂ d hd hdd₂ K β hdatum hdat.2 al hal f h hpair
    obtain ⟨e₃, he₃, hk₃⟩ := h₃ d hd hdd₃ K β hdatum hdat.2 al₀ hal₀ f h hpair
    have hδ := h₁ d hd hdd₁ K β hdatum hdat.2 f h hpair μ hμ
    have hb₂ : |e₂| ≤ 2 * |C₂| * x ^ (-(1 / 200) : ℝ) := he₂.trans (error_sum_le hx1 hn)
    have hb₃ : |e₃| ≤ 2 * |C₃| * x ^ (-(1 / 200) : ℝ) := he₃.trans (error_sum_le hx1 hn)
    have hkf : κ ≤ inverseEighthKernel f h := by
      obtain ⟨-, -, x₁, x₂, hc⟩ := (mem_separatedPairs_iff _ _ _ _ _ _ _).1 hpair.mem_class
      have hch := ((hGeo.1 d vt ⟨hd, hvt, hvt1⟩ x₁ x₂ f h hpair.mem_class hc).1).2.2.2.2
      have c1 := hch.1
      have c2 := hch.2.1
      rw [hpair.norm_left, hpair.norm_right, mul_one, mul_one] at c1
      exact c1.trans c2
    obtain ⟨ε, hε, hcv⟩ := cov_factor_of_two_expansions hx1 hκ0 hkf (hb₂.trans hsm₂) (hb₃.trans hsm₃)
      hsq hk₂ hk₃ (hδ.trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) (by positivity)))
    refine ⟨ε, hε.trans ?_, hcv⟩
    have h5 : |C₁| * Q * x ^ (-(1 / 130) : ℝ) ≤ |C₁| * Q * x ^ (-(1 / 200) : ℝ) :=
      mul_le_mul_of_nonneg_left hrate (by positivity)
    calc |e₂| + |C₁| * Q * x ^ (-(1 / 130) : ℝ)
        ≤ 2 * |C₂| * x ^ (-(1 / 200) : ℝ) + |C₁| * Q * x ^ (-(1 / 200) : ℝ) := add_le_add hb₂ h5
      _ = (2 * |C₂| + |C₁| * Q) * x ^ (-(1 / 200) : ℝ) := by ring
  have hL : Conventions.IsAdmissibleBlockingFactor T.side := by
    refine ⟨hDr.L_odd, ?_⟩
    have := hDr.L_ge
    norm_num at this
    omega
  have hβ : 0 < β := by
    have h1 : g ^ (-2 : ℤ) + D.shift ≤ β := hTD.threshold_le
    have h2 : 2 * T.B ≤ D.shift := hD.shift_ge
    have h3 : 1 ≤ T.B := hDr.B_ge
    have h4 : 0 < g ^ (-2 : ℤ) := by positivity
    linarith
  have hclass : ∀ p ∈ separatedPairsR4 d vt,
      ∀ μ : Measure (LatticeConfig (T.stepParameters y).side K), IsProbabilityMeasure μ →
        IsAdmissibleState (T.stepParameters y).side K β μ →
      ∃ ε : ℝ, |ε| ≤ (2 * |C₂| + |C₁| * Q) * x ^ (-(1 / 200) : ℝ) ∧
        covar μ (fun U => InfiniteLattice.smearedEnergy p.1 U) (fun U => InfiniteLattice.smearedEnergy p.2 U) =
          al k ^ 2 * (9 / Real.pi ^ 4) * (x ^ 2)⁻¹ * inverseEighthKernel p.1 p.2 * (1 + ε) := by
    rintro ⟨f, h⟩ hp μ hμ₁ hμ
    obtain ⟨a, b, ha, hb, hpair⟩ := exists_normalized_pair hd hvt hp
    obtain ⟨ε, hε, hcv⟩ := hnormal _ _ hpair μ hμ
    have hmb := ((hCov T.side 1 K hL one_pos (by omega) β hβ).2.2.2.1 2
      ![fun x => a⁻¹ * f x, fun x => b⁻¹ * h x] (by norm_num) (boundedBorel_fin_two hpair.mem_class)).2.1
    have hcv' := (covariance_eq_covar μ (hmb 0).1 (hmb 1).1 (hmb 0).2 (hmb 1).2).symm.trans hcv
    have := expansion_const_mul (F := fun x => a⁻¹ * f x) (H := fun x => b⁻¹ * h x)
      (A := al k ^ 2 * (9 / Real.pi ^ 4) * (x ^ 2)⁻¹) ⟨ε, hε, hcv'⟩ a b
    have ef : (fun x => a * (a⁻¹ * f x)) = f := by
      funext z
      field_simp
    have eh : (fun x => b * (b⁻¹ * h x)) = h := by
      funext z
      field_simp
    simpa only [ef, eh] using this
  have hK0 : 0 < (K : ℕ) := by omega
  refine ⟨?_, ?_⟩
  · intro ν hν p hp
    have hν1 : IsProbabilityMeasure ν := hν.1.1
    obtain ⟨ε, hε, hcv⟩ := hclass p hp ν hν1 (Or.inl hν)
    have hmb := ((hCov T.side 1 K hL one_pos hK0 β hβ).2.2.2.1 2 ![p.1, p.2] (by norm_num)
      (boundedBorel_fin_two hp)).2.1
    exact ⟨ε, hε, (cumulant_eq_covar hGen ν (hmb 0).1 (hmb 1).1 (hmb 0).2 (hmb 1).2).trans
      (congrArg (fun r : ℝ => (r : ℂ)) hcv)⟩
  · intro m p hp
    have h40 : 40 * d ≤ PeriodicLattice.torusSide T.side m := by
      have hp27 : 0 ≤ x ^ ((1 : ℝ) / 27) := by positivity
      have h1 : 10 * d ≤ (x ^ ((1 : ℝ) / 27) + 10) * d :=
          mul_le_mul_of_nonneg_right (by linarith) hd.le
      have h2 : (2 : ℝ) ≤ PeriodicLattice.torusSide T.side m := two_le_torusSide hL
      linarith
    obtain ⟨L', hs⟩ := exists_admissibleSide (m := m) hL h40
    obtain ⟨ψ₁, ψ₂, hψ, e₁, e₂, ek⟩ := exists_lift_pair (f := p.1) (h := p.2) hGeo hd hvt hvt1 hs hp
    have hP := hProb T.side m K β (by have := hL.2; omega)
    obtain ⟨ε, hε, hcv⟩ := hclass (ψ₁, ψ₂) hψ (InfiniteLattice.liftedWilsonMeasure T.side m K β) hP
      (Or.inr ⟨m, rfl⟩)
    obtain ⟨b₁, b₂⟩ := boundedBorel_of_mem hψ
    have ht := torus_covariance hGen hCov hTwo hProb (m := m) hL hK0 hβ b₁ b₂
    rw [e₁, e₂] at ht
    rw [ek] at hcv
    exact ⟨ε, hε, ht.trans (congrArg (fun r : ℝ => (r : ℂ)) hcv)⟩
end YangMills.Construction.SystemOfAdmissibleConstants
end
