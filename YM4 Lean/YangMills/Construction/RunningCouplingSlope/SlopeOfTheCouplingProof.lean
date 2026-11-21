import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import YangMills.Construction.RunningCouplingSlope.OneStepOfTheCoupling
import YangMills.Construction.RunningCouplingSlope.SlopeOfTheCoupling
import YangMills.Construction.RunningCouplingSlope.TheStepsHaveTheSlope
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.CouplingFlow YangMills.Construction.StepReturn YangMills.Construction.BlockAverages
namespace RunningCouplingSlope.CouplingHasSlope
private def unitImaginary : imaginaryQuaternions := ⟨(⟨0, 1, 0, 0⟩ : Quaternion ℝ), rfl⟩
private theorem norm_unitImaginary : ‖unitImaginary‖ = 1 := by
  have h : Quaternion.normSq ((unitImaginary : imaginaryQuaternions) : Quaternion ℝ) = 1 := by
    rw [Quaternion.normSq_def']
    simp [unitImaginary]
  have h2 := Quaternion.normSq_eq_norm_mul_self ((unitImaginary : imaginaryQuaternions) : Quaternion ℝ)
  have h3 : 0 ≤ ‖((unitImaginary : imaginaryQuaternions) : Quaternion ℝ)‖ := norm_nonneg _
  change ‖((unitImaginary : imaginaryQuaternions) : Quaternion ℝ)‖ = 1
  nlinarith
private theorem stepCoefficients_unique {a : ℝ} {L : ℕ} {b b' : ℕ → ℝ}
    (h : AreStepCoefficients a L b) (h' : AreStepCoefficients a L b') : b = b' :=
  funext fun t => tendsto_nhds_unique
    (h t 1 1 unitImaginary one_pos le_rfl le_rfl norm_unitImaginary)
    (h' t 1 1 unitImaginary one_pos le_rfl le_rfl norm_unitImaginary)
theorem hasExpansion_expansionCoupling {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {t : ℕ}
    {x : ℝ} {D : TorusFunctional} (hx : ℓ.y₁ ≤ x) (hD : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) := by
  obtain ⟨x', ⟨h1, _⟩, h3⟩ := hR t x D hx hD
  have hex : ∃ x' : ℝ, HasExpansion ℓ (t + 1) x' (kernelImage ℓ x D) := ⟨x', h1⟩
  have hn : expansionCoupling ℓ t x D = x' := by
    unfold expansionCoupling
    rw [dif_pos hex]
    obtain ⟨_, f, hf, _⟩ := hex.choose_spec
    exact h3 _ f hf
  rw [hn]
  exact h1
theorem hasExpansion_couplingFlow {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {β : ℝ}
    (hW : HasExpansion ℓ 0 β (wilsonWeight β)) (t : ℕ) (hs : FlowStaysAboveFloor ℓ β t) :
    HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2 := by apply _root_.YangMills.DeltaSharedProofs.p3925 <;> assumption
theorem sub_eq_sum_Ico_sub (x : ℕ → ℝ) (i j : ℕ) (hij : i ≤ j) :
    x i - x j = ∑ l ∈ Finset.Ico i j, (x l - x (l + 1)) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [Finset.sum_Ico_succ_top hj, ← ih]
    ring
theorem drop_bounds_of_step_bounds (b x : ℕ → ℝ) (c₀ cH Ce : ℝ) (i j : ℕ) (hij : i ≤ j)
    (hs : HasAverageSlope b c₀ cH)
    (hstep : ∀ l, i ≤ l → l < j → |x l - x (l + 1) - b l| ≤ Ce * x l ^ (-(1 / 4) : ℝ))
    (hsmall : ∀ l, i ≤ l → l < j → Ce * x l ^ (-(1 / 4) : ℝ) ≤ c₀ / 4) :
    3 / 4 * c₀ * ((j : ℝ) - i) - 2 * cH ≤ x i - x j ∧
      x i - x j ≤ 5 / 4 * c₀ * ((j : ℝ) - i) + 2 * cH ∧
      |x i - x j - ((j : ℝ) - i) * c₀| ≤ 2 * cH + Ce * ∑ l ∈ Finset.Ico i j, x l ^ (-(1 / 4) : ℝ) := by
  have htel := sub_eq_sum_Ico_sub x i j hij
  have hS := abs_le.mp (hs i j hij)
  set S := ∑ l ∈ Finset.Ico i j, b l with hSdef
  set E := Ce * ∑ l ∈ Finset.Ico i j, x l ^ (-(1 / 4) : ℝ) with hEdef
  have hdiff : |x i - x j - S| ≤ E := by
    have h1 : x i - x j - S = ∑ l ∈ Finset.Ico i j, (x l - x (l + 1) - b l) := by
      rw [htel, hSdef, ← Finset.sum_sub_distrib]
    rw [h1, hEdef, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
    obtain ⟨hl1, hl2⟩ := Finset.mem_Ico.mp hl
    exact hstep l hl1 hl2
  have hEle : E ≤ c₀ / 4 * ((j : ℝ) - i) := by
    have h2 : E ≤ ∑ _l ∈ Finset.Ico i j, c₀ / 4 := by
      rw [hEdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun l hl => ?_
      obtain ⟨hl1, hl2⟩ := Finset.mem_Ico.mp hl
      exact hsmall l hl1 hl2
    refine h2.trans (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hij]
    ring
  have hd := abs_le.mp hdiff
  refine ⟨by nlinarith [hd.1, hS.1, hEle], by nlinarith [hd.2, hS.2, hEle], ?_⟩
  rw [abs_le]
  constructor <;> linarith [hd.1, hd.2, hS.1, hS.2]
theorem slopeConst_pos {L : ℕ} (hL : 2 ≤ L) : 0 < slopeConst L := by
  unfold slopeConst
  have h1 : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  positivity
theorem mul_rpow_neg_half_le {C c₀ x : ℝ} (hC : 0 < C) (hc : 0 < c₀)
    (hx : (4 * C / c₀) ^ 4 ≤ x) : C * x ^ (-(1 / 4) : ℝ) ≤ c₀ / 4 := by
  have hq : 0 < 4 * C / c₀ := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hs : 4 * C / c₀ ≤ x ^ (1 / 4 : ℝ) := by
    have h1 : ((4 * C / c₀) ^ 4) ^ (1 / 4 : ℝ) ≤ x ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hx (by norm_num)
    have h2 : ((4 * C / c₀) ^ 4) ^ (1 / 4 : ℝ) = 4 * C / c₀ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
      norm_num
    rwa [h2] at h1
  have hp : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hneg : x ^ (-(1 / 4) : ℝ) = (x ^ (1 / 4 : ℝ))⁻¹ := by
    rw [Real.rpow_neg hx0.le]
  rw [hneg, ← div_eq_mul_inv, div_le_iff₀ hp]
  have : 4 * C ≤ c₀ * x ^ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ hc] at hs
    linarith
  linarith
theorem holds (h1 : StepCoefficientsHaveSlope)
    (h2 : SlopeCoefficient.CouplingStepBound) : CouplingHasSlope := by
  have hc : ∀ p : ℝ × ℕ, ∃ c : ℝ, 0 ≤ c ∧ (IsAdmissibleParametersAt p.1 p.2 →
      ∃ b : ℕ → ℝ, AreStepCoefficients p.1 p.2 b ∧ HasAverageSlope b (slopeConst p.2) c) := by
    intro p
    by_cases hp : IsAdmissibleParametersAt p.1 p.2
    · obtain ⟨b, cH, h0, hb, _, hsl⟩ := h1 p.1 p.2 hp
      exact ⟨cH, h0, fun _ => ⟨b, hb, hsl⟩⟩
    · exact ⟨0, le_rfl, fun h => absurd h hp⟩
  choose cH hcH0 hcH using hc
  obtain ⟨rt₀, hrt₀, h2⟩ := h2
  refine ⟨fun a L => cH (a, L), fun a L => hcH0 (a, L), rt₀, hrt₀, fun T hT hrt => ?_⟩
  obtain ⟨b', Ce, ys, hb', hCe, hstep⟩ := h2 T hT hrt
  refine ⟨Ce, ys, hCe, ?_⟩
  intro y hy hret hW β i j hβ hij hi hwin
  obtain ⟨b, hb, hsl⟩ := hcH (T.coupling, T.side) ⟨T, hT, rfl, rfl⟩
  have hbb : b' = b := stepCoefficients_unique hb' hb
  subst hbb
  have hL2 : (2 : ℕ) ^ 40 ≤ T.side := hT.L_ge
  have hc₀ : 0 < slopeConst T.side := slopeConst_pos (by
    omega)
  set ℓ := T.stepParameters y with hℓ
  have hX1 : max y ys ≤ slopeThreshold (max y ys) Ce (slopeConst T.side) := le_max_left _ _
  have hX2 : (4 * Ce / slopeConst T.side) ^ 4 ≤ slopeThreshold (max y ys) Ce (slopeConst T.side) :=
    le_max_right _ _
  have hstay : FlowStaysAboveFloor ℓ β j := by
    intro k hk
    rcases lt_or_ge k i with h | h
    · exact hi k h
    · exact (le_max_left y ys).trans (hX1.trans (hwin k h hk))
  have hrows : ∀ l, l ≤ j → HasExpansion ℓ l (couplingFlow ℓ β l).1 (couplingFlow ℓ β l).2 :=
    fun l hl => hasExpansion_couplingFlow hret (hW β hβ) l fun k hk => hstay k (lt_of_lt_of_le hk hl)
  have hsteps : ∀ l, i ≤ l → l < j →
      |(couplingFlow ℓ β l).1 - (couplingFlow ℓ β (l + 1)).1 - b' l| ≤
        Ce * (couplingFlow ℓ β l).1 ^ (-(1 / 4) : ℝ) := fun l h₁ h₂ =>
    hstep y hy hret l (couplingFlow ℓ β l).1 (couplingFlow ℓ β l).2 (hX1.trans (hwin l h₁ h₂))
      (hrows l h₂.le) (couplingFlow ℓ β (l + 1)).1 (hrows (l + 1) h₂)
  have hsmall : ∀ l, i ≤ l → l < j →
      Ce * (couplingFlow ℓ β l).1 ^ (-(1 / 4) : ℝ) ≤ slopeConst T.side / 4 :=
    fun l h₁ h₂ => mul_rpow_neg_half_le hCe hc₀ (hX2.trans (hwin l h₁ h₂))
  obtain ⟨f1, f2, f3⟩ := drop_bounds_of_step_bounds b' (fun l => (couplingFlow ℓ β l).1)
    (slopeConst T.side) (cH (T.coupling, T.side)) Ce i j hij hsl hsteps hsmall
  exact ⟨f1, f2, f3⟩
end RunningCouplingSlope.CouplingHasSlope
end YangMills.Construction
end
