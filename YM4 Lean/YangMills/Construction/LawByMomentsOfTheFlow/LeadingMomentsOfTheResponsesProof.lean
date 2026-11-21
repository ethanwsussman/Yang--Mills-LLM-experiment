import YangMills.Construction.LawByMomentsOfTheFlow.CumulantNearTheResponsesProof
import YangMills.Construction.LawByMomentsOfTheFlow.GoodStatesAreLikely
import YangMills.Construction.LawByMomentsOfTheFlow.GradientsOfAStepAreFarApartProof
import YangMills.Construction.LawByMomentsOfTheFlow.LeadingMomentsOfTheResponses
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheResponsesInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusLumps TorusFields WeightedResponses ResponseInTheExpansion RenormalizationStepParameters LevelTestFunctions
section ScalarEstimates
private theorem factor_near_half_form {x s r v N f Q C E : ℝ} (hs : 1 ≤ s) (hx : x = s ^ 2) (hr : 1 ≤ r) (hv : 0 ≤ v)
    (hN : 1 ≤ N) (hC : 0 ≤ C) (hE0 : 0 ≤ E) (hE : s ^ 3 * E ≤ 1)
    (h1 : |f - 1 / 2 * Q| ≤ C * (r ^ 7 * v ^ 3 + r ^ 4 * s⁻¹ * v ^ 2 + r ^ 4 * E * N))
    (h2 : |Q| ≤ C * r ^ 4 * v ^ 2) :
    |x * f - x / 2 * Q| ≤ r ^ 3 * s⁻¹ * ((3 * C + 1) * r ^ 4 * (1 + s * v) ^ 3 * N) ∧
      |x / 2 * Q| ≤ (3 * C + 1) * r ^ 4 * (1 + s * v) ^ 3 * N := by apply _root_.YangMills.SharedProofs.p27143 <;> assumption
private theorem abs_prod_sub_prod_le {ι : Type} [DecidableEq ι] (B : Finset ι) (A Z T : ι → ℝ) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hT : ∀ i ∈ B, 0 ≤ T i) (hA : ∀ i ∈ B, |A i - Z i| ≤ ε * T i) (hZ : ∀ i ∈ B, |Z i| ≤ T i) :
    |∏ i ∈ B, A i - ∏ i ∈ B, Z i| ≤ ε * (2 ^ B.card * ∏ i ∈ B, T i) ∧ ∏ i ∈ B, |A i| ≤ 2 ^ B.card * ∏ i ∈ B, T i := by apply _root_.YangMills.SharedProofs.p833 <;> assumption
private theorem closing_scalar_bound {x s Yv rr K A₂ c₁ c₂ Cf z p : ℝ} {b : ℕ} (hs : 1 ≤ s) (hxs : x = s ^ 2) (hY1 : 1 ≤ Yv)
    (hr : 1 ≤ rr) (hA₂ : 0 ≤ A₂) (hK : 0 ≤ K) (hz : z ≤ Yv) (hz0 : 0 ≤ z)
    (hterm : (2 * K) ^ b * (|c₁| + A₂) + |c₂| ≤ Cf) (hp : p = (x ^ (b + 1))⁻¹) :
    rr ^ 3 * s⁻¹ * (2 * K * rr ^ 4) ^ b * (|c₁| * z + A₂) + x ^ b * (|c₂| * p) ≤ Cf * rr ^ (4 * b + 3) * (s⁻¹ * Yv) := by apply _root_.YangMills.SharedProofs.p55882 <;> assumption
end ScalarEstimates
section Expectation
private theorem product_moments_near_form {Ω ι : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] [DecidableEq ι]
    (B : Finset ι) {G : Set Ω} (hG : MeasurableSet G) {Fi Ni Qi : ι → Ω → ℝ} {v : Ω → ℝ}
    {x s r C E vm A₁ A₂ A₃ : ℝ} (hs : 1 ≤ s) (hx : x = s ^ 2) (hr : 1 ≤ r) (hε : r ^ 3 * s⁻¹ ≤ 1) (hC : 0 ≤ C)
    (hE0 : 0 ≤ E) (hE : s ^ 3 * E ≤ 1) (hFm : ∀ i, AEStronglyMeasurable (Fi i) μ) (hNm : ∀ i, Measurable (Ni i))
    (hN1 : ∀ i w, 1 ≤ Ni i w) (hQm : ∀ i, Measurable (Qi i)) (hvm : Measurable v) (hv0 : ∀ w, 0 ≤ v w)
    (hvx : ∀ w ∈ G, v w ≤ vm)
    (hpt : ∀ᵐ w ∂μ, w ∈ G → ∀ i, |Fi i w - 1 / 2 * Qi i w| ≤
        C * (r ^ 7 * v w ^ 3 + r ^ 4 * s⁻¹ * v w ^ 2 + r ^ 4 * E * Ni i w) ∧ |Qi i w| ≤ C * r ^ 4 * v w ^ 2)
    (h₁ : ∫⁻ w, G.indicator (fun w => ENNReal.ofReal ((1 + s * v w) ^ (6 * B.card))) w ∂μ ≤ ENNReal.ofReal A₁)
    (h₂ : ∫⁻ w, ENNReal.ofReal ((∏ i ∈ B, Ni i w) ^ 2) ∂μ ≤ ENNReal.ofReal A₂)
    (h₃ : ∫⁻ w, Gᶜ.indicator (fun w => ENNReal.ofReal (∏ i ∈ B, |Fi i w|)) w ∂μ ≤ ENNReal.ofReal A₃)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hA₃ : 0 ≤ A₃) :
    Integrable (fun w => ∏ i ∈ B, Fi i w) μ ∧
      |x ^ B.card * ∫ w, ∏ i ∈ B, Fi i w ∂μ - ∫ w, G.indicator (fun w => ∏ i ∈ B, x / 2 * Qi i w) w ∂μ| ≤
        r ^ 3 * s⁻¹ * (2 * (3 * C + 1) * r ^ 4) ^ B.card * (A₁ + A₂) + x ^ B.card * A₃ := by
  have hx1 : 1 ≤ x := by rw [hx]; exact one_le_pow₀ hs
  have hx0 : 0 ≤ x := by linarith
  set b := B.card with hb
  set K := 3 * C + 1 with hK
  have hK0 : 0 < K := by rw [hK]; linarith
  set κ := (2 * K * r ^ 4) ^ b with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set ε := r ^ 3 * s⁻¹ with hεd
  have hε0 : 0 ≤ ε := by positivity
  have hP : ∀ᵐ w ∂μ, w ∈ G →
      |x ^ b * ∏ i ∈ B, Fi i w - ∏ i ∈ B, x / 2 * Qi i w| ≤ ε * κ * ((1 + s * v w) ^ (6 * b) + (∏ i ∈ B, Ni i w) ^ 2) ∧
      x ^ b * ∏ i ∈ B, |Fi i w| ≤ κ * ((1 + s * v w) ^ (6 * b) + (∏ i ∈ B, Ni i w) ^ 2) := by
    filter_upwards [hpt] with w hw hwG
    have hone := fun i => factor_near_half_form hs hx hr (hv0 w) (hN1 i w) hC hE0 hE (hw hwG i).1 (hw hwG i).2
    have hTn : ∀ i ∈ B, 0 ≤ K * r ^ 4 * (1 + s * v w) ^ 3 * Ni i w := fun i _ => by
      have : 0 ≤ v w := hv0 w
      have : 0 ≤ Ni i w := by linarith [hN1 i w]
      positivity
    have hpn := abs_prod_sub_prod_le B (fun i => x * Fi i w) (fun i => x / 2 * Qi i w)
      (fun i => K * r ^ 4 * (1 + s * v w) ^ 3 * Ni i w) hε0 hε hTn (fun i _ => (hone i).1) (fun i _ => (hone i).2)
    have hw0 : 0 ≤ 1 + s * v w := by have := hv0 w; positivity
    have hNp : 0 ≤ ∏ i ∈ B, Ni i w := Finset.prod_nonneg fun i _ => by linarith [hN1 i w]
    have eT : 2 ^ b * ∏ i ∈ B, K * r ^ 4 * (1 + s * v w) ^ 3 * Ni i w =
        κ * ((1 + s * v w) ^ (3 * b) * ∏ i ∈ B, Ni i w) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, hκ, ← hb]
      generalize (1 + s * v w) = u
      ring
    have eA : ∏ i ∈ B, x * Fi i w = x ^ b * ∏ i ∈ B, Fi i w := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← hb]
    have eB : ∏ i ∈ B, |x * Fi i w| = x ^ b * ∏ i ∈ B, |Fi i w| := by
      simp only [abs_mul, abs_of_nonneg hx0]
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← hb]
    set a := (1 + s * v w) ^ (3 * b) with ha
    have ea : (1 + s * v w) ^ (6 * b) = a ^ 2 := by rw [ha]; ring
    have ha0 : 0 ≤ a := by positivity
    set P := ∏ i ∈ B, Ni i w with hPd
    have hab : a * P ≤ a ^ 2 + P ^ 2 := by nlinarith [sq_nonneg (a - P), mul_nonneg ha0 hNp]
    rw [ea]
    obtain ⟨p1, p2⟩ := hpn
    rw [eT, eA] at p1
    rw [eT, eB] at p2
    constructor
    · refine p1.trans ?_
      rw [mul_assoc ε κ]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hab hκ0) hε0
    · exact p2.trans (mul_le_mul_of_nonneg_left hab hκ0)
  let f₁ : Ω → ENNReal := G.indicator fun w => ENNReal.ofReal ((1 + s * v w) ^ (6 * b))
  let f₂ : Ω → ENNReal := fun w => ENNReal.ofReal ((∏ i ∈ B, Ni i w) ^ 2)
  let f₃ : Ω → ENNReal := Gᶜ.indicator fun w => ENNReal.ofReal (∏ i ∈ B, |Fi i w|)
  have hf₁ : Measurable f₁ := (((measurable_const.add (hvm.const_mul s)).pow_const _).ennreal_ofReal).indicator hG
  have hf₂ : Measurable f₂ := ((Finset.measurable_prod _ fun i _ => hNm i).pow_const 2).ennreal_ofReal
  have hsum : ∀ c₁ c₂ : ENNReal, c₁ ≠ ⊤ → c₂ ≠ ⊤ → ∫⁻ w, c₁ * (f₁ w + f₂ w) + c₂ * f₃ w ∂μ ≤
      c₁ * (ENNReal.ofReal A₁ + ENNReal.ofReal A₂) + c₂ * ENNReal.ofReal A₃ := by
    intro c₁ c₂ t1 t2
    have e1 : ∫⁻ w, c₁ * (f₁ w + f₂ w) + c₂ * f₃ w ∂μ = ∫⁻ w, c₁ * (f₁ w + f₂ w) ∂μ + ∫⁻ w, c₂ * f₃ w ∂μ :=
      lintegral_add_left ((hf₁.add hf₂).const_mul c₁) _
    have e2 : ∫⁻ w, f₁ w + f₂ w ∂μ = ∫⁻ w, f₁ w ∂μ + ∫⁻ w, f₂ w ∂μ := lintegral_add_left hf₁ _
    rw [e1, lintegral_const_mul' _ _ t1, lintegral_const_mul' _ _ t2, e2]
    exact add_le_add (mul_le_mul_right (add_le_add h₁ h₂) _) (mul_le_mul_right h₃ _)
  have hFp : AEStronglyMeasurable (fun w => ∏ i ∈ B, Fi i w) μ := Finset.aestronglyMeasurable_fun_prod _ fun i _ => hFm i
  have hnonneg : ∀ w, 0 ≤ (1 + s * v w) ^ (6 * b) ∧ 0 ≤ (∏ i ∈ B, Ni i w) ^ 2 := fun w => by
    have := hv0 w
    constructor <;> positivity
  have hout : ∀ w, w ∉ G → f₁ w = 0 ∧ f₃ w = ENNReal.ofReal (∏ i ∈ B, |Fi i w|) := fun w hw =>
    ⟨Set.indicator_of_notMem hw _, Set.indicator_of_mem (Set.mem_compl hw) _⟩
  have hin : ∀ w, w ∈ G → f₁ w = ENNReal.ofReal ((1 + s * v w) ^ (6 * b)) ∧ f₃ w = 0 := fun w hw =>
    ⟨Set.indicator_of_mem hw _, Set.indicator_of_notMem (by simpa using hw) _⟩
  have hI1 : ∀ᵐ w ∂μ, ENNReal.ofReal |∏ i ∈ B, Fi i w| ≤ ENNReal.ofReal κ * (f₁ w + f₂ w) + 1 * f₃ w := by
    filter_upwards [hP] with w hw
    by_cases hwG : w ∈ G
    · rw [(hin w hwG).1, (hin w hwG).2, mul_zero, add_zero, ← ENNReal.ofReal_add (hnonneg w).1 (hnonneg w).2,
        ← ENNReal.ofReal_mul hκ0]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (hw hwG).2)
      rw [Finset.abs_prod]
      exact le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => abs_nonneg _) (one_le_pow₀ hx1)
    · rw [(hout w hwG).1, (hout w hwG).2, one_mul, Finset.abs_prod]
      exact le_add_self
  have hfin : HasFiniteIntegral (fun w => ∏ i ∈ B, Fi i w) μ := by
    show ∫⁻ w, ‖∏ i ∈ B, Fi i w‖ₑ ∂μ < ⊤
    simp only [Real.enorm_eq_ofReal_abs]
    refine lt_of_le_of_lt ((lintegral_mono_ae hI1).trans (hsum _ _ ENNReal.ofReal_ne_top ENNReal.one_ne_top)) ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩),
      ENNReal.mul_lt_top ENNReal.one_lt_top ENNReal.ofReal_lt_top⟩
  have hFI : Integrable (fun w => ∏ i ∈ B, Fi i w) μ := ⟨hFp, hfin⟩
  refine ⟨hFI, ?_⟩
  set H : Ω → ℝ := G.indicator (fun w => ∏ i ∈ B, x / 2 * Qi i w) with hH
  have hHm : Measurable H := (Finset.measurable_prod _ fun i _ => (hQm i).const_mul _).indicator hG
  have hHI : Integrable H μ := by
    refine Integrable.of_bound hHm.aestronglyMeasurable ((x / 2 * (C * r ^ 4 * vm ^ 2)) ^ b) ?_
    filter_upwards [hpt] with w hw
    by_cases hwG : w ∈ G
    · rw [hH, Set.indicator_of_mem hwG, Real.norm_eq_abs, Finset.abs_prod]
      have := Finset.prod_le_prod (s := B) (f := fun i => |x / 2 * Qi i w|) (g := fun _ => x / 2 * (C * r ^ 4 * vm ^ 2))
        (fun _ _ => abs_nonneg _) (fun i _ => by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ x / 2)]
          refine mul_le_mul_of_nonneg_left ((hw hwG i).2.trans ?_) (by positivity)
          have := hvx w hwG
          have := hv0 w
          gcongr)
      rwa [Finset.prod_const] at this
    · rw [hH, Set.indicator_of_notMem hwG, norm_zero]
      positivity
  have hI2 : ∀ᵐ w ∂μ, ENNReal.ofReal ‖x ^ b * ∏ i ∈ B, Fi i w - H w‖ ≤
      ENNReal.ofReal (ε * κ) * (f₁ w + f₂ w) + ENNReal.ofReal (x ^ b) * f₃ w := by
    filter_upwards [hP] with w hw
    by_cases hwG : w ∈ G
    · rw [(hin w hwG).1, (hin w hwG).2, mul_zero, add_zero, ← ENNReal.ofReal_add (hnonneg w).1 (hnonneg w).2,
        ← ENNReal.ofReal_mul (mul_nonneg hε0 hκ0), hH, Set.indicator_of_mem hwG]
      exact ENNReal.ofReal_le_ofReal (hw hwG).1
    · rw [(hout w hwG).1, (hout w hwG).2, hH, Set.indicator_of_notMem hwG, sub_zero, ← ENNReal.ofReal_mul (by positivity),
        Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), Finset.abs_prod]
      exact le_add_self
  have e : x ^ b * ∫ w, ∏ i ∈ B, Fi i w ∂μ - ∫ w, H w ∂μ = ∫ w, (x ^ b * ∏ i ∈ B, Fi i w - H w) ∂μ := by
    rw [integral_sub (hFI.const_mul _) hHI, integral_const_mul]
  rw [e, ← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (lintegral_mono_ae hI2).trans ((hsum _ _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).trans ?_)
  rw [← ENNReal.ofReal_add hA₁ hA₂, ← ENNReal.ofReal_mul (mul_nonneg hε0 hκ0), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
end Expectation
section LargeCoupling
private theorem eventual_range_bounds {c : ℝ} (hc : 0 < c) : ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x →
    (clusterRange x : ℝ) ^ 3 * (x ^ ((1 : ℝ) / 2))⁻¹ ≤ 1 ∧
      (x ^ ((1 : ℝ) / 2)) ^ 3 * Real.exp (-(c * (clusterRange x : ℝ) ^ 2)) ≤ 1 := by apply _root_.YangMills.SharedProofs.p37192 <;> assumption
end LargeCoupling
section Parameters
private theorem forAllParameters_and {P Q : MomentParameters → Prop} (hP : ForAllParameters P) (hQ : ForAllParameters Q) :
    ForAllParameters fun Λ => P Λ ∧ Q Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllHullParameters_of_forAllParameters {P : MomentParameters → Prop} (h : ForAllParameters P) :
    ForAllHullParameters P := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllHullParameters_and {P Q : MomentParameters → Prop} (hP : ForAllHullParameters P)
    (hQ : ForAllHullParameters Q) : ForAllHullParameters fun Λ => P Λ ∧ Q Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHullParameters_mono {P Q : MomentParameters → Prop} (hP : ForAllHullParameters P)
    (h : ∀ Λ, P Λ → Q Λ) : ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p38382 <;> assumption
private theorem forAllParameters_stepParams_admissible : ForAllParameters fun Λ => Λ.stepParams.Admissible := by apply _root_.YangMills.SharedProofs.p7443 <;> assumption
end Parameters
section AtAPoint
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem measurable_prod_sigma_of_forall {X A : Type} [MeasurableSpace X] [Countable A] {B : A → Type}
    [∀ a, MeasurableSpace (B a)] {Z : Type} [MeasurableSpace Z] {f : X × Sigma B → Z}
    (h : ∀ a, Measurable fun p : X × B a => f (p.1, ⟨a, p.2⟩)) : Measurable f := by apply _root_.YangMills.SharedProofs.p5842 <;> assumption
private theorem resp_isAdmissible {u : ℕ} (hu : u ≤ S.data.windowLevel) : (S.resp u).IsAdmissible := by apply _root_.YangMills.SharedProofs.p17647 <;> assumption
variable (u n : ℕ) [NeZero n]
private theorem measurable_meanScore (hs : Measurable (S.resp u).score) (i : Fin Λ.k) :
    Measurable fun q : StageState S.tower u n => S.meanScore u n i q := by apply _root_.YangMills.SharedProofs.p9251 <;> assumption
private theorem one_le_meanScore (hs : ∀ w, 0 ≤ (S.resp u).score w) (i : Fin Λ.k) (q : StageState S.tower u n) :
    1 ≤ S.meanScore u n i q := by apply _root_.YangMills.SharedProofs.p166 <;> assumption
private theorem measurableSet_isGoodConfig (hv : Measurable (S.localCurvature u n)) :
    MeasurableSet {q : StageState S.tower u n | S.IsGoodConfig u n q.1 q.2.1} := by
  have h1 : MeasurableSet {q : StageState S.tower u n | Disjoint q.2.1 (supBall (S.originSite u n) (8 * S.rangeSq))} := by
    have : Measurable fun q : StageState S.tower u n => Disjoint q.2.1 (supBall (S.originSite u n) (8 * S.rangeSq)) :=
      measurable_prod_sigma_of_forall fun Y =>
        (measurable_const : Measurable fun _ => Disjoint Y (supBall (S.originSite u n) (8 * S.rangeSq)))
    exact measurableSet_setOfPred.2 this
  have h2 : MeasurableSet {q : StageState S.tower u n | S.localCurvature u n q.1 ≤ S.scaleCoupling ^ (-(1 / 4) : ℝ)} :=
    measurableSet_le (hv.comp measurable_fst) measurable_const
  have e : {q : StageState S.tower u n | S.IsGoodConfig u n q.1 q.2.1} =
      {q | Disjoint q.2.1 (supBall (S.originSite u n) (8 * S.rangeSq))} ∩
        {q | S.localCurvature u n q.1 ≤ S.scaleCoupling ^ (-(1 / 4) : ℝ)} := by
    ext q
    exact ⟨fun h => ⟨h.disjoint_lumps, h.curvature_le⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [e]
  exact h1.inter h2
private theorem aestronglyMeasurable_supportTotal (hrow : (S.resp u).IsAdmissible) (hb : IsBlockTorusSide Λ.stepParams n)
    (hm : Measurable (S.state u n))
    (hl : ∀ᵐ w ∂(S.law u n), IsLiveState Λ.stepParams (S.tower.stage u).coupling (S.tower.stage u).labelWeight
      (S.state u n w).1 (S.state u n w).2.1 (S.state u n w).2.2)
    (i : Fin Λ.k) : AEStronglyMeasurable (fun w => S.supportTotal u n i (S.state u n w)) (S.law u n) := by
  classical
  let h := S.weight i (fineSide Λ.stepParams.side (S.tower.stage u).depth n)
  let f : StageState S.tower u n → ℝ := fun q =>
    ∑ y ∈ weightSupportSites Λ.stepParams.side (S.tower.stage u).depth n h,
      ((if IsLiveState Λ.stepParams (S.tower.stage u).coupling (S.tower.stage u).labelWeight q.1 q.2.1 q.2.2 then
          (S.resp u).hull n y q.1 q.2.1 q.2.2 h else 0) -
        (S.resp u).cold n y (trivialField n) h)
  have hf : Measurable f := by
    refine measurable_prod_sigma_of_forall fun Y => Finset.measurable_sum _ fun y _ => ?_
    exact (hrow.bounds.hull_borel n hb y Y h).sub measurable_const
  refine (hf.comp hm).aestronglyMeasurable.congr ?_
  filter_upwards [hl] with w hw
  simp only [Function.comp, f, if_pos hw]
  rfl
private theorem measurable_colourEval (hc : cutoffMeasurableStatement) (q : BondBilinear n) :
    Measurable fun W : TorusField n => colourEval q (S.cutoffColourForm u n W) (S.cutoffColourForm u n W) := by
  unfold colourEval bilinearEval
  refine Finset.measurable_sum _ fun e _ => Finset.measurable_sum _ fun b _ => Finset.measurable_sum _ fun b' _ => ?_
  exact (((hc Λ.stepParams n (S.originSite u n)).1 S.rangeSq b e).mul_const _).mul
    ((hc Λ.stepParams n (S.originSite u n)).1 S.rangeSq b' e)
theorem leadingResponseMoments_holds (hNear : supportTotalNearQuadraticStatement)
    (hGood : goodConfigsLikelyStatement) (hMean : meanScoreMomentBoundStatement)
    (hLive : liveStatesStatement) (hCut : cutoffMeasurableStatement)
    (hWin : scaleWindowStatement) (hSt : ResponseInTheExpansion.StageStatesMeasurableStatement) :
    leadingResponseMomentsStatement := by
  unfold supportTotalNearQuadraticStatement ForAllPoints at hNear
  unfold goodConfigsLikelyStatement ForAllHullPoints at hGood
  unfold meanScoreMomentBoundStatement ForAllHullPoints at hMean
  unfold liveStatesStatement ForAllPoints at hLive
  unfold scaleWindowStatement ForAllPoints at hWin
  unfold leadingResponseMomentsStatement ForAllHullPoints
  refine forAllHullParameters_mono (forAllHullParameters_and hMean (forAllHullParameters_and hGood
    (forAllHullParameters_of_forAllParameters (forAllParameters_and hNear (forAllParameters_and hLive
    (forAllParameters_and hWin forAllParameters_stepParams_admissible)))))) ?_
  rintro Λ ⟨⟨C₃, _, _, _, _, h₃⟩, ⟨C₂, _, X₂, _, _, h₂⟩, ⟨C₁, c₁, X₁, hc₁, _, h₁⟩, ⟨_, _, _, _, _, h₄⟩,
    ⟨_, _, X₅, _, _, h₅⟩, hfit⟩
  obtain ⟨X₆, hX₆1, hX₆⟩ := eventual_range_bounds hc₁
  set C₀ := max (C₁ 0) 0 with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  set K := 3 * C₀ + 1 with hK
  have hK0 : 0 < K := by rw [hK]; linarith
  let A₂ : ℕ → ℝ := fun b => |C₃ 0| ^ (2 * b + 1) * ((2 * b + 1).factorial : ℝ) ^ 6
  have hA₂ : ∀ b, 0 ≤ A₂ b := fun b => by positivity
  let Cf : ℝ := ∑ b ∈ Finset.range (Λ.k + 1), ((2 * K) ^ b * (|C₂ (6 * b)| + A₂ b) + |C₂ (b + 1)|)
  refine ⟨fun _ => Cf, 1, max (max X₁ X₂) (max X₅ (max X₆ Λ.floor)), one_pos,
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)), fun S hx B => ?_⟩
  have hx1 : X₁ ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx2 : X₂ ≤ S.scaleCoupling := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx5 : X₅ ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx6 : X₆ ≤ S.scaleCoupling := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hx
  have hxone : 1 ≤ S.scaleCoupling := hX₆1.trans hx6
  have hxpos : 0 < S.scaleCoupling := by linarith
  obtain ⟨-, -, -, -, -, hwin, -⟩ := h₅ S hx5
  have htK : S.lastSeparated ≤ S.data.windowLevel := by omega
  have hrow := resp_isAdmissible S htK
  have hsm : Measurable (S.resp S.lastSeparated).score := hrow.price.borel
  have hs0 : ∀ w, 0 ≤ (S.resp S.lastSeparated).score w := hrow.price.nonneg
  have hb : IsBlockTorusSide Λ.stepParams (S.levelSide S.lastSeparated) := by
    refine ⟨Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _, S.side_le.trans ?_⟩
    exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)))
  have hq : Measurable (S.state S.lastSeparated (S.levelSide S.lastSeparated)) := hSt Λ.stepParams hfit S.tower S.lastSeparated _
  have hl := h₄ S S.lastSeparated htK (S.levelSide S.lastSeparated) hb
  have hv : Measurable (S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated)) := (hCut Λ.stepParams _ _).2 _
  have hv0 : ∀ W : TorusField (S.levelSide S.lastSeparated), 0 ≤ S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated) W :=
    fun W => Real.iSup_nonneg fun _ => norm_nonneg _
  have hN1 := one_le_meanScore S S.lastSeparated (S.levelSide S.lastSeparated) hs0
  have hfin : IsFiniteMeasure (S.law S.lastSeparated (S.levelSide S.lastSeparated)) := by
    refine ⟨lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := C₃ 0 ^ 1 * ((1 : ℕ).factorial : ℝ) ^ 6))⟩
    refine le_trans ?_ (h₃ S 1 le_rfl [0] rfl).2
    rw [← lintegral_one]
    refine lintegral_mono fun w => ?_
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact ENNReal.one_le_ofReal.2 (hN1 0 _)
  set b := B.card with hbd
  set s := S.scaleCoupling ^ ((1 : ℝ) / 2) with hsd
  have hs : 1 ≤ s := Real.one_le_rpow hxone (by norm_num)
  have hxs : S.scaleCoupling = s ^ 2 := by
    rw [hsd, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    norm_num
  have hsinv : S.scaleCoupling ^ (-(1 / 2) : ℝ) = s⁻¹ := by
    rw [hsd, ← Real.rpow_neg hxpos.le]
  have hr : (1 : ℝ) ≤ S.range := by
    have h1 : (1 : ℝ) ≤ S.scaleCoupling ^ ((1 : ℝ) / 100) := Real.one_le_rpow hxone (by norm_num)
    have h2 : S.scaleCoupling ^ ((1 : ℝ) / 100) ≤ (S.range : ℝ) := Nat.le_ceil _
    linarith
  obtain ⟨hε, hE⟩ := hX₆ S.scaleCoupling hx6
  let G : Set (MarkedSample Λ.stepParams S.lastSeparated (S.levelSide S.lastSeparated)) :=
    {w | S.IsGoodConfig S.lastSeparated (S.levelSide S.lastSeparated)
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1 (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).2.1}
  have hG : MeasurableSet G := hq (measurableSet_isGoodConfig S S.lastSeparated (S.levelSide S.lastSeparated) hv)
  let A₁ : ℝ := |C₂ (6 * b)| * S.scaleCoupling ^ ((1 : ℝ) / 4000)
  let A₃ : ℝ := |C₂ (b + 1)| * S.scaleCoupling ^ (-((b + 1 : ℕ) : ℝ))
  have hA₁ : 0 ≤ A₁ := by positivity
  have hA₃ : 0 ≤ A₃ := by positivity
  have hpt : ∀ᵐ w ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)), w ∈ G → ∀ i,
      |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) -
          1 / 2 * colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i)
          (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1)
          (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1)| ≤
        C₀ * ((S.range : ℝ) ^ 7 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated)
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1 ^ 3 +
          (S.range : ℝ) ^ 4 * s⁻¹ * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated)
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1 ^ 2 +
          (S.range : ℝ) ^ 4 * Real.exp (-(c₁ * (S.range : ℝ) ^ 2)) *
            S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)) ∧
      |colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i)
          (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1)
          (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1)| ≤
        C₀ * (S.range : ℝ) ^ 4 * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated)
          (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1 ^ 2 := by
    filter_upwards [hl] with w hw hwG i
    obtain ⟨p1, p2⟩ := h₁ S hx1 i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) hw hwG
    rw [hsinv] at p1
    have hvw := hv0 (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1
    have hNw : 0 ≤ S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) := by
      linarith [hN1 i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)]
    constructor
    · refine p1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
      positivity
    · refine p2.trans ?_
      have : C₁ 0 ≤ C₀ := le_max_left _ _
      gcongr
  have i₁ : ∫⁻ w, G.indicator (fun w => ENNReal.ofReal ((1 + s * S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated)
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1) ^ (6 * b))) w
      ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤ ENNReal.ofReal A₁ := by
    refine (((h₂ S hx2).1 S.lastSeparated le_rfl (by omega)).2 (6 * b)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have i₃ : ∫⁻ w, Gᶜ.indicator (fun w => ENNReal.ofReal (∏ i ∈ B,
      |S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)|)) w
      ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤ ENNReal.ofReal A₃ := by
    refine ((h₂ S hx2).2 B (b + 1)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have i₂ : ∫⁻ w, ENNReal.ofReal ((∏ i ∈ B, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)) ^ 2)
      ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤ ENNReal.ofReal (A₂ b) := by
    have hlen : ((0 : Fin Λ.k) :: (B.toList ++ B.toList)).length = 2 * b + 1 := by
      simp [hbd]
      omega
    refine le_trans (lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_)
      (((h₃ S (2 * b + 1) (by omega) _ hlen).2).trans (ENNReal.ofReal_le_ofReal ?_))
    · simp only [List.map_cons, List.prod_cons, List.map_append, List.prod_append, Finset.prod_map_toList]
      have h1 := hN1 0 (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)
      have h2 : 0 ≤ (∏ i ∈ B, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)) *
          ∏ i ∈ B, S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
            (S.state S.lastSeparated (S.levelSide S.lastSeparated) w) := mul_self_nonneg _
      rw [sq]
      exact le_mul_of_one_le_left h2 h1
    · show C₃ 0 ^ (2 * b + 1) * _ ≤ |C₃ 0| ^ (2 * b + 1) * _
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact (le_abs_self _).trans (abs_pow (C₃ 0) _).le
  have core := product_moments_near_form (μ := S.law S.lastSeparated (S.levelSide S.lastSeparated)) B hG
    (Fi := fun i w => S.supportTotal S.lastSeparated (S.levelSide S.lastSeparated) i
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
    (Ni := fun i w => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) w))
    (Qi := fun i w => colourEval (S.supportForm S.lastSeparated (S.levelSide S.lastSeparated) i)
      (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1)
      (S.cutoffColourForm S.lastSeparated (S.levelSide S.lastSeparated) (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1))
    (v := fun w => S.localCurvature S.lastSeparated (S.levelSide S.lastSeparated)
      (S.state S.lastSeparated (S.levelSide S.lastSeparated) w).1)
    (x := S.scaleCoupling) (s := s) (r := S.range) (C := C₀) (E := Real.exp (-(c₁ * (S.range : ℝ) ^ 2)))
    (vm := S.scaleCoupling ^ (-(1 / 4) : ℝ))
    (A₁ := A₁) (A₂ := A₂ b) (A₃ := A₃) hs hxs hr hε hC₀0 (Real.exp_pos _).le hE
    (fun i => aestronglyMeasurable_supportTotal S _ _ hrow hb hq hl i)
    (fun i => (measurable_meanScore S _ _ hsm i).comp hq) (fun i w => hN1 i _)
    (fun i => (measurable_colourEval S _ _ hCut _).comp (measurable_fst.comp hq))
    (hv.comp (measurable_fst.comp hq)) (fun w => hv0 _) (fun w hw => hw.curvature_le) hpt i₁ i₂ i₃ hA₁ (hA₂ b) hA₃
  refine ⟨core.1, core.2.trans ?_⟩
  have hb_le : b ≤ Λ.k := by
    have := Finset.card_le_univ B
    simpa using this
  have hterm : (2 * K) ^ b * (|C₂ (6 * b)| + A₂ b) + |C₂ (b + 1)| ≤ Cf := by
    refine Finset.single_le_sum (f := fun b => (2 * K) ^ b * (|C₂ (6 * b)| + A₂ b) + |C₂ (b + 1)|) (fun j _ => ?_)
      (Finset.mem_range.2 (by omega))
    have := hA₂ j
    positivity
  have e₁ : S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ) = s⁻¹ * S.scaleCoupling ^ ((1 : ℝ) / 1000) := by
    rw [Real.rpow_add hxpos, hsinv]
  rw [e₁]
  have hp : S.scaleCoupling ^ (-((b + 1 : ℕ) : ℝ)) = (S.scaleCoupling ^ (b + 1))⁻¹ := by
    rw [Real.rpow_neg hxpos.le, Real.rpow_natCast]
  exact closing_scalar_bound hs hxs (Real.one_le_rpow hxone (by norm_num)) hr (hA₂ b) hK0.le
    (Real.rpow_le_rpow_of_exponent_le hxone (by norm_num)) (by positivity) hterm hp
end AtAPoint
end YangMills.Construction.MomentLaw
end
