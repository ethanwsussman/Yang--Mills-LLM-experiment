import YangMills.Construction.LawByMomentsOfTheFlow.ABoundAtClearStatesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.ChainCumulantIsTheFreeOne
import YangMills.Construction.LawByMomentsOfTheFlow.ChainHasACanonicalGaussian
import YangMills.Construction.LawByMomentsOfTheFlow.CumulantByTheGaussianChain
import YangMills.Construction.LawByMomentsOfTheFlow.CumulantNearTheResponses
import YangMills.Construction.LawByMomentsOfTheFlow.LawAtLargeCouplings
import YangMills.Construction.LawByMomentsOfTheFlow.ValueOfTheFreeCumulant
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
private theorem forAllHullParameters_of_forAllParameters {Q : MomentParameters → Prop}
    (h : ForAllParameters Q) : ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllHullParameters_and {Q Q' : MomentParameters → Prop} (h : ForAllHullParameters Q)
    (h' : ForAllHullParameters Q') : ForAllHullParameters fun P => Q P ∧ Q' P := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHullParameters_mono {Q Q' : MomentParameters → Prop} (h : ForAllHullParameters Q)
    (H : ∀ P : MomentParameters, 0 ≤ P.stepParams.coupling → Q P → Q' P) : ForAllHullParameters Q' := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := h a ha
  refine ⟨L₁, r₁, C₁, hr₁, ?_⟩
  intro L hodd hL Tb hTa hTL hD hC hO hrt hCd
  obtain ⟨M₁, G₁⟩ := H₁ L hodd hL Tb hTa hTL hD hC hO hrt hCd
  refine ⟨M₁, fun Kr hM hη hN hKr hRet => ?_⟩
  obtain ⟨y₁, F₁⟩ := G₁ Kr hM hη hN hKr hRet
  refine ⟨y₁, ?_⟩
  intro y hy hret hbot g hg hgy k _ hk2 hk8 R d hd
  refine H _ ?_ (F₁ y hy hret hbot g hg hgy k hk2 hk8 R d hd)
  change 0 ≤ Tb.coupling
  rw [hTa]
  linarith
private theorem pow_mul_exp_neg_rpow_le (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    x ^ k * Real.exp (-(x ^ ((1 : ℝ) / 300))) ≤ ((300 * (k + 1)).factorial : ℝ) * x⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 ≤ x ^ ((1 : ℝ) / 300) := by positivity
  have h1 := Real.pow_div_factorial_le_exp _ hy0 (300 * (k + 1))
  have hyp : (x ^ ((1 : ℝ) / 300)) ^ (300 * (k + 1)) = x ^ (k + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
      show ((1 : ℝ) / 300) * ((300 * (k + 1) : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hyp] at h1
  have hN : (0 : ℝ) < ((300 * (k + 1)).factorial : ℝ) := by positivity
  have h2 : x ^ (k + 1) ≤ ((300 * (k + 1)).factorial : ℝ) * Real.exp (x ^ ((1 : ℝ) / 300)) :=
    (div_le_iff₀' hN).1 h1
  rw [Real.exp_neg, ← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hx0]
  calc x ^ k * x = x ^ (k + 1) := by ring
    _ ≤ _ := h2
private theorem exp_neg_mul_clusterRange_le {c x : ℝ} (hc : 0 < c) (hx : 1 ≤ x) :
    Real.exp (-(c * (TorusLumps.clusterRange x : ℝ))) ≤ ((100).factorial / c ^ 100) * x⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hz0 : 0 ≤ c * x ^ ((1 : ℝ) / 100) := by positivity
  have h1 := Real.pow_div_factorial_le_exp _ hz0 100
  have hzp : (c * x ^ ((1 : ℝ) / 100)) ^ 100 = c ^ 100 * x := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 100)), ← Real.rpow_mul hx0.le]
    norm_num
  rw [hzp] at h1
  have hr : x ^ ((1 : ℝ) / 100) ≤ (TorusLumps.clusterRange x : ℝ) := Nat.le_ceil _
  have h2 : Real.exp (-(c * (TorusLumps.clusterRange x : ℝ))) ≤ Real.exp (-(c * x ^ ((1 : ℝ) / 100))) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hr hc.le))
  refine h2.trans ?_
  have hpos : 0 < c ^ 100 * x / ((100).factorial : ℝ) := by positivity
  rw [Real.exp_neg]
  refine (inv_anti₀ hpos h1).trans (le_of_eq ?_)
  field_simp
private theorem exists_isCanonicalGaussian_of_eq {P : MomentParameters} (S : MomentPoint P) {u v : ℕ} (h : u = v)
    (μ : Measure (LevelChain P.stepParams.side u (S.data.period P.stepParams.side)))
    (hμ : IsCanonicalGaussian (levelEnergy P.stepParams.coupling u (S.data.period P.stepParams.side)) μ) :
    ∃ μ' : Measure (LevelChain P.stepParams.side v (S.data.period P.stepParams.side)),
      IsCanonicalGaussian (levelEnergy P.stepParams.coupling v (S.data.period P.stepParams.side)) μ' ∧
      jointCumulant μ' (fun i => S.observableAt v (S.data.period P.stepParams.side) i) =
        jointCumulant μ (fun i => S.observableAt u (S.data.period P.stepParams.side) i) := by
  subst h
  exact ⟨μ, hμ, rfl⟩
theorem largeCouplingCumulant (h₁ : cumulantNearResponsesStatement)
    (h₂ : cumulantByGaussianChainStatement) (h₃ : levelCumulantApproxStatement)
    (h₄ : freeCumulantValueStatement) (h₅ : canonicalGaussianExistsStatement) :
    largeCouplingCumulantStatement := by
  unfold largeCouplingCumulantStatement ForAllHullPoints
  unfold cumulantNearResponsesStatement ForAllHullPoints at h₁
  unfold cumulantByGaussianChainStatement ForAllHullPoints at h₂
  unfold levelCumulantApproxStatement ForAllPoints at h₃
  unfold freeCumulantValueStatement ForAllPoints at h₄
  refine forAllHullParameters_mono (forAllHullParameters_and h₁ (forAllHullParameters_and h₂
    (forAllHullParameters_and (forAllHullParameters_of_forAllParameters h₃)
      (forAllHullParameters_of_forAllParameters h₄)))) ?_
  rintro P ha ⟨⟨C₁, c₁, X₁, -, hy₁, H₁⟩, ⟨C₂, c₂, X₂, -, -, H₂⟩, ⟨C₃, c₃, X₃, hc₃, -, H₃⟩, ⟨C₄, c₄, X₄, -, -, H₄⟩⟩
  refine ⟨fun _ => ((300 * (P.k + 1)).factorial : ℝ) + |C₂ 1| + |C₃ 0| * ((100).factorial / c₃ ^ 100) + |C₄ 0|,
    1, max (max X₁ X₂) (max X₄ 1), one_pos, hy₁.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro S hX
  beta_reduce
  have hx1 : 1 ≤ S.scaleCoupling := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hxX₁ : X₁ ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_left _ _)).trans hX
  have hxX₂ : X₂ ≤ S.scaleCoupling := ((le_max_right _ _).trans (le_max_left _ _)).trans hX
  have hxX₄ : X₄ ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hx0 : 0 < S.scaleCoupling := by linarith
  have ht0 : S.lastSeparated ≤ S.data.scaleLevel := by
    classical
    unfold MomentPoint.lastSeparated
    exact Nat.findGreatest_le _
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (ht0.trans S.supAdmissible.scaleLevel_le)
  obtain ⟨μ, hμ⟩ := h₅ P.stepParams.side P.stepParams.coupling ha (S.lastSeparated + d)
    (S.data.period P.stepParams.side)
  obtain ⟨μ', hμ', hval⟩ := exists_isCanonicalGaussian_of_eq S hd.symm μ hμ
  have e₁ := H₁ S hxX₁
  have e₂ := (H₂ S hxX₂ d hd.symm μ hμ).2
  have e₃ := (H₃ S d hd.symm μ hμ).1
  have e₄ := (H₄ S μ' hμ').2.2.2.1 hxX₄
  rw [hval] at e₄
  have hinv : S.scaleCoupling⁻¹ ≤ S.scaleCoupling ^ (-(1 / 10) : ℝ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hy : 0 ≤ S.scaleCoupling ^ (-(1 / 10) : ℝ) := by positivity
  have b₁ : S.scaleCoupling ^ P.k * ‖S.torusCumulant - (S.responseCumulant : ℂ)‖ ≤
      ((300 * (P.k + 1)).factorial : ℝ) * S.scaleCoupling ^ (-(1 / 10) : ℝ) :=
    calc S.scaleCoupling ^ P.k * ‖S.torusCumulant - (S.responseCumulant : ℂ)‖
        ≤ S.scaleCoupling ^ P.k * Real.exp (-(S.scaleCoupling ^ ((1 : ℝ) / 300))) :=
          mul_le_mul_of_nonneg_left e₁ (by positivity)
      _ ≤ ((300 * (P.k + 1)).factorial : ℝ) * S.scaleCoupling⁻¹ := pow_mul_exp_neg_rpow_le _ hx1
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
  have b₂ := e₂.trans (mul_le_mul_of_nonneg_right (le_abs_self (C₂ 1)) hy)
  have hr : Real.exp (-(c₃ * (S.range : ℝ))) ≤ ((100).factorial / c₃ ^ 100) * S.scaleCoupling⁻¹ :=
    exp_neg_mul_clusterRange_le hc₃ hx1
  have hM : (0 : ℝ) ≤ (100).factorial / c₃ ^ 100 := by positivity
  have b₃ := e₃.trans ((mul_le_mul_of_nonneg_right (le_abs_self (C₃ 0)) (Real.exp_pos _).le).trans
    ((mul_le_mul_of_nonneg_left hr (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv hM) (abs_nonneg _))))
  have b₄ := e₄.trans ((mul_le_mul_of_nonneg_right (le_abs_self (C₄ 0)) (inv_nonneg.2 hx0.le)).trans
    (mul_le_mul_of_nonneg_left hinv (abs_nonneg _)))
  generalize jointCumulant μ (fun i => S.halfForm d (S.data.period P.stepParams.side) i) = κ₁ at b₂ b₃
  generalize jointCumulant μ (fun i => S.observableAt (S.lastSeparated + d) (S.data.period P.stepParams.side) i)
    = κ₂ at b₃ b₄
  have hsplit : (S.scaleCoupling : ℂ) ^ P.k * S.torusCumulant - (S.latticeCycleSumAt S.data.scaleLevel : ℂ) =
      (S.scaleCoupling : ℂ) ^ P.k * (S.torusCumulant - (S.responseCumulant : ℂ)) +
        (((S.scaleCoupling ^ P.k * S.responseCumulant - κ₁) + (κ₁ - κ₂) +
          (κ₂ - S.latticeCycleSumAt S.data.scaleLevel) : ℝ) : ℂ) := by
    push_cast
    ring
  have key : ‖(S.scaleCoupling : ℂ) ^ P.k * S.torusCumulant - (S.latticeCycleSumAt S.data.scaleLevel : ℂ)‖ ≤
      S.scaleCoupling ^ P.k * ‖S.torusCumulant - (S.responseCumulant : ℂ)‖ +
        (|S.scaleCoupling ^ P.k * S.responseCumulant - κ₁| + |κ₁ - κ₂| +
          |κ₂ - S.latticeCycleSumAt S.data.scaleLevel|) := by
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_add_three _ _ _
  refine key.trans ?_
  have hsum : (((300 * (P.k + 1)).factorial : ℝ) + |C₂ 1| + |C₃ 0| * ((100).factorial / c₃ ^ 100) + |C₄ 0|) *
      S.scaleCoupling ^ (-(1 / 10) : ℝ) = ((300 * (P.k + 1)).factorial : ℝ) * S.scaleCoupling ^ (-(1 / 10) : ℝ) +
        (|C₂ 1| * S.scaleCoupling ^ (-(1 / 10) : ℝ) +
          |C₃ 0| * (((100).factorial / c₃ ^ 100) * S.scaleCoupling ^ (-(1 / 10) : ℝ)) +
          |C₄ 0| * S.scaleCoupling ^ (-(1 / 10) : ℝ)) := by ring
  rw [hsum]
  exact add_le_add b₁ (add_le_add (add_le_add b₂ b₃) b₄)
end YangMills.Construction.MomentLaw
end
