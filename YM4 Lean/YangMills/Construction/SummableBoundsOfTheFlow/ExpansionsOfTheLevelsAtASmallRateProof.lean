import YangMills.Construction.QuaternionicWilsonModel.TheFlowRepresentsTheMixedMomentProof
import YangMills.Construction.ClusterExpansionOfAStep.BondsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.ExponentialSumsOnATorus
import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorusProof
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionsOfTheLevelsAtASmallRate
import YangMills.Construction.SummableBoundsOfTheFlow.MixtureAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoLevelMixtures
open TorusFields MixtureJets ExponentialSums WeightedResponses BlockAverages
private theorem exp_sub_one_le_mul_exp_three {κ r d : ℝ} (hκ : 0 < κ) (hr0 : 0 ≤ r) (hr : r ≤ κ) (hd : 0 ≤ d) :
    Real.exp (2 * r * d) - 1 ≤ 2 * r / κ * Real.exp (3 * κ * d) := by
  set x := 2 * r * d with hxdef
  have h1 : Real.exp x - 1 ≤ x * Real.exp x := by
    have h0 := Real.add_one_le_exp (-x)
    have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have h5 : (-x + 1) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
      mul_le_mul_of_nonneg_right h0 (Real.exp_pos x).le
    rw [h2] at h5
    linarith
  have h3 : κ * d ≤ Real.exp (κ * d) := by
    have := Real.add_one_le_exp (κ * d)
    linarith
  have h4 : Real.exp x ≤ Real.exp (2 * κ * d) := by
    apply Real.exp_le_exp.mpr
    rw [hxdef]
    nlinarith
  have e : Real.exp (3 * κ * d) = Real.exp (κ * d) * Real.exp (2 * κ * d) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hq : 0 ≤ 2 * r / κ := by positivity
  calc Real.exp x - 1 ≤ x * Real.exp x := h1
    _ = 2 * r / κ * (κ * d) * Real.exp x := by
        rw [hxdef]
        field_simp
    _ ≤ 2 * r / κ * Real.exp (κ * d) * Real.exp (2 * κ * d) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h3 hq) h4 (Real.exp_pos _).le (by positivity)
    _ = 2 * r / κ * Real.exp (3 * κ * d) := by rw [e]; ring
private theorem inner_unitGenerator_self :
    inner ℝ (unitGenerator : Quaternion ℝ) (unitGenerator : Quaternion ℝ) = 1 := by apply _root_.YangMills.DeltaSharedProofs.p500886 <;> assumption
private theorem norm_unitGenerator : ‖unitGenerator‖ = 1 := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.norm_unitGenerator <;> assumption
variable {n : ℕ}
open Classical in
private theorem bondIndicator_eq_single {m : ℕ} (b : TorusBond m) :
    bondIndicator b = Pi.single b (1 : ℝ) := by
  funext x
  simp [bondIndicator, Pi.single_apply]
private theorem abs_levelHessianEntry_le (T : ColdStepAtMirrorFrames.StepParameters) [NeZero T.L] [NeZero n]
    (Cm : ℕ → ℝ) (u : ℕ) (hκ : 0 ≤ T.chainParams.δ₁)
    (hM : FlatFieldJetBounds T Cm u n 0) (b b' : TorusBond (n * T.L))
    (hb : b ∈ StepCosts.chartBonds T.L n) (hb' : b' ∈ StepCosts.chartBonds T.L n) :
    |levelHessianEntry T.a T.L u b b'| ≤
      |Cm 2| * Real.exp (-(8 * T.chainParams.δ₁ *
        supDist (TorusLumps.parentBlock T.L b.1) (TorusLumps.parentBlock T.L b'.1))) := by
  classical
  have e := hM.second_deriv_eq b hb b' hb' unitGenerator unitGenerator
  have hunits : AreUnitVectors ![unitGenerator, unitGenerator] := by
    intro l
    fin_cases l <;> simpa using norm_unitGenerator
  have k := hM.kernel_decay 2 ![Sum.inl b, Sum.inl b'] ![unitGenerator, unitGenerator] le_rfl hunits
  rw [e, inner_unitGenerator_self, one_mul, bondIndicator_eq_single, bondIndicator_eq_single] at k
  have hdiam : supDist (TorusLumps.parentBlock T.L b.1) (TorusLumps.parentBlock T.L b'.1) ≤
      mixedBondDiam T.L ![Sum.inl b, Sum.inl b'] := by
    have h1 : supDist (mixedBondSite T.L (![Sum.inl b, Sum.inl b'] (0 : Fin 2)))
        (mixedBondSite T.L (![Sum.inl b, Sum.inl b'] (1 : Fin 2))) ≤
        Finset.univ.sup fun l' : Fin 2 => supDist (mixedBondSite T.L (![Sum.inl b, Sum.inl b'] (0 : Fin 2)))
          (mixedBondSite T.L (![Sum.inl b, Sum.inl b'] l')) :=
      Finset.le_sup (f := fun l' : Fin 2 => supDist (mixedBondSite T.L (![Sum.inl b, Sum.inl b'] (0 : Fin 2)))
        (mixedBondSite T.L (![Sum.inl b, Sum.inl b'] l'))) (Finset.mem_univ 1)
    have h2 := Finset.le_sup (f := fun l : Fin 2 => Finset.univ.sup fun l' : Fin 2 =>
      supDist (mixedBondSite T.L (![Sum.inl b, Sum.inl b'] l)) (mixedBondSite T.L (![Sum.inl b, Sum.inl b'] l')))
      (Finset.mem_univ (0 : Fin 2))
    exact h1.trans h2
  have hdiam' : (supDist (TorusLumps.parentBlock T.L b.1) (TorusLumps.parentBlock T.L b'.1) : ℝ) ≤
      mixedBondDiam T.L ![Sum.inl b, Sum.inl b'] := by
    exact_mod_cast hdiam
  have hexp : Real.exp (-(8 * T.chainParams.δ₁ * mixedBondDiam T.L ![Sum.inl b, Sum.inl b'])) ≤
      Real.exp (-(8 * T.chainParams.δ₁ *
        supDist (TorusLumps.parentBlock T.L b.1) (TorusLumps.parentBlock T.L b'.1))) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hdiam' (by linarith : 0 ≤ 8 * T.chainParams.δ₁)
    linarith
  calc |levelHessianEntry T.a T.L u b b'|
      ≤ Cm 2 * Real.exp (-(8 * T.chainParams.δ₁ * mixedBondDiam T.L ![Sum.inl b, Sum.inl b'])) := k
    _ ≤ |Cm 2| * Real.exp (-(8 * T.chainParams.δ₁ * mixedBondDiam T.L ![Sum.inl b, Sum.inl b'])) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
private theorem sum_exp_supDist_parentBlock_le (hbonds : TorusLumps.BondsPerBlockBound) (L : ℕ) [NeZero L]
    [NeZero n] {c : ℝ} (hc : 0 < c) (S : Finset (TorusBond (n * L))) (Y₀ : TorusSite n) :
    ∑ b ∈ S, Real.exp (-c * supDist (TorusLumps.parentBlock L b.1) Y₀) ≤
      4 * (2 * (L : ℝ)) ^ 4 * expLatticeSum c := by
  set f : TorusSite n → ℝ := fun Y => Real.exp (-c * supDist Y Y₀) with hf
  have hf0 : ∀ Y, 0 ≤ f Y := fun _ => (Real.exp_pos _).le
  calc ∑ b ∈ S, Real.exp (-c * supDist (TorusLumps.parentBlock L b.1) Y₀)
      ≤ ∑ b : TorusBond (n * L), f (TorusLumps.parentBlock L b.1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => hf0 _
    _ = ∑ Y : TorusSite n, ∑ b ∈ Finset.univ.filter
          (fun b : TorusBond (n * L) => TorusLumps.parentBlock L b.1 = Y),
          f (TorusLumps.parentBlock L b.1) :=
        (Finset.sum_fiberwise _ _ _).symm
    _ ≤ ∑ Y : TorusSite n, 4 * (2 * (L : ℝ)) ^ 4 * f Y := by
        refine Finset.sum_le_sum fun Y _ => ?_
        have e : ∑ b ∈ Finset.univ.filter
            (fun b : TorusBond (n * L) => TorusLumps.parentBlock L b.1 = Y),
            f (TorusLumps.parentBlock L b.1) =
            ((Finset.univ.filter fun b : TorusBond (n * L) =>
              TorusLumps.parentBlock L b.1 = Y).card : ℝ) * f Y := by
          rw [Finset.sum_congr rfl fun b hb => by rw [(Finset.mem_filter.mp hb).2]]
          simp
        rw [e]
        exact mul_le_mul_of_nonneg_right (hbonds L n Y) (hf0 Y)
    _ = 4 * (2 * (L : ℝ)) ^ 4 * ∑ Y : TorusSite n, f Y := by rw [Finset.mul_sum]
    _ ≤ 4 * (2 * (L : ℝ)) ^ 4 * expLatticeSum c :=
        mul_le_mul_of_nonneg_left (sum_torus_exp_le hc Y₀) (by positivity)
private theorem row_sum_decayWeightExcess_le (hbonds : TorusLumps.BondsPerBlockBound) (L : ℕ) [NeZero L] [NeZero n]
    {κ r C : ℝ} (hκ : 0 < κ) (hr0 : 0 ≤ r) (hr : r ≤ κ) (hC : 0 ≤ C) (S : Finset (TorusBond (n * L)))
    (b : TorusBond (n * L)) (e : TorusBond (n * L) → ℝ)
    (he : ∀ b' ∈ S, |e b'| ≤
      C * Real.exp (-(8 * κ * supDist (TorusLumps.parentBlock L b.1) (TorusLumps.parentBlock L b'.1)))) :
    ∑ b' ∈ S, |e b'| * decayWeightExcess L r b b' ≤
      C * (2 * r / κ) * (4 * (2 * (L : ℝ)) ^ 4 * expLatticeSum (5 * κ)) := by
  have hq : 0 ≤ C * (2 * r / κ) := by positivity
  calc ∑ b' ∈ S, |e b'| * decayWeightExcess L r b b'
      ≤ ∑ b' ∈ S, C * (2 * r / κ) *
          Real.exp (-(5 * κ) * supDist (TorusLumps.parentBlock L b'.1) (TorusLumps.parentBlock L b.1)) := by
        refine Finset.sum_le_sum fun b' hb' => ?_
        have hd : (0 : ℝ) ≤ supDist (TorusLumps.parentBlock L b.1) (TorusLumps.parentBlock L b'.1) :=
          Nat.cast_nonneg _
        have h1 := exp_sub_one_le_mul_exp_three hκ hr0 hr hd
        have h0 : 0 ≤ decayWeightExcess L r b b' := by
          have : 1 ≤ Real.exp (2 * r * supDist (TorusLumps.parentBlock L b.1) (TorusLumps.parentBlock L b'.1)) :=
            Real.one_le_exp (by positivity)
          simp only [decayWeightExcess]
          linarith
        have e5 : Real.exp (-(8 * κ * supDist (TorusLumps.parentBlock L b.1) (TorusLumps.parentBlock L b'.1))) *
            Real.exp (3 * κ * supDist (TorusLumps.parentBlock L b.1) (TorusLumps.parentBlock L b'.1)) =
            Real.exp (-(5 * κ) * supDist (TorusLumps.parentBlock L b'.1) (TorusLumps.parentBlock L b.1)) := by
          rw [← Real.exp_add, supDist_comm (TorusLumps.parentBlock L b'.1)]
          congr 1
          ring
        calc |e b'| * decayWeightExcess L r b b'
            ≤ (C * Real.exp (-(8 * κ * supDist (TorusLumps.parentBlock L b.1) (TorusLumps.parentBlock L b'.1)))) *
                (2 * r / κ * Real.exp (3 * κ *
                  supDist (TorusLumps.parentBlock L b.1) (TorusLumps.parentBlock L b'.1))) :=
              mul_le_mul (he b' hb') h1 h0 (by positivity)
          _ = C * (2 * r / κ) *
                Real.exp (-(5 * κ) * supDist (TorusLumps.parentBlock L b'.1) (TorusLumps.parentBlock L b.1)) := by
              rw [← e5]
              ring
    _ = C * (2 * r / κ) * ∑ b' ∈ S,
          Real.exp (-(5 * κ) * supDist (TorusLumps.parentBlock L b'.1) (TorusLumps.parentBlock L b.1)) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_exp_supDist_parentBlock_le hbonds L (by positivity) S _) hq
theorem levelExpansionsAtSmallRate (h : flatFieldJetBoundsStatement) (hbonds : TorusLumps.BondsPerBlockBound) :
    levelExpansionsAtSmallRateStatement := by
  unfold flatFieldJetBoundsStatement ColdStepAtMirrorFrames.EventuallyOrdered at h
  unfold levelExpansionsAtSmallRateStatement ColdStepAtMirrorFrames.EventuallyOrdered
  refine ColdStepAtMirrorFrames.EventuallyInParameters.mono h fun T hT hd h1 => ?_
  intro _
  obtain ⟨Cm, hCm⟩ := hT hd h1
  have hlam : 0 < T.lam := hd.chain_admissible.positivity.2.2.1
  have hcl := hd.chain_admissible.classical.1
  have hκ₂ : 0 < T.chainParams.κ₂ := by
    have := hcl.2.2.2.2.1
    linarith
  have hκ : 0 < T.chainParams.δ₁ := hd.chain_admissible.positivity.1
  set C : ℝ := |Cm 2| with hC
  have hC0 : 0 ≤ C := abs_nonneg _
  set A : ℝ := 4 * (2 * (T.L : ℝ)) ^ 4 * expLatticeSum (5 * T.chainParams.δ₁) with hA
  have hA0 : 0 ≤ A := by
    have := expLatticeSum_pos (by positivity : 0 < 5 * T.chainParams.δ₁)
    positivity
  set r : ℝ := min (min T.chainParams.κ₂ T.chainParams.δ₁)
    (T.lam * T.chainParams.δ₁ / (4 * (C + 1) * (A + 1))) with hr
  have hr0 : 0 < r := lt_min (lt_min hκ₂ hκ) (by positivity)
  have hrκ₂ : r ≤ T.chainParams.κ₂ := (min_le_left _ _).trans (min_le_left _ _)
  have hrκ : r ≤ T.chainParams.δ₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hsmall : C * (2 * r / T.chainParams.δ₁) * A ≤ T.lam / 2 := by
    have h2 : r * (4 * (C + 1) * (A + 1)) ≤ T.lam * T.chainParams.δ₁ := by
      have := min_le_right (min T.chainParams.κ₂ T.chainParams.δ₁)
        (T.lam * T.chainParams.δ₁ / (4 * (C + 1) * (A + 1)))
      rwa [← hr, le_div_iff₀ (by positivity)] at this
    have h3 : 2 * r / T.chainParams.δ₁ * (2 * ((C + 1) * (A + 1))) ≤ T.lam := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hκ]
      nlinarith
    have hq : 0 ≤ 2 * r / T.chainParams.δ₁ := by positivity
    have h4 : C * A ≤ (C + 1) * (A + 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hq]
  refine ⟨r, hr0, hrκ₂, fun u n _ hn b hb => ?_⟩
  have hM := hCm u n 0 hn le_rfl zero_le_one
  constructor
  · refine (row_sum_decayWeightExcess_le hbonds T.L hκ hr0.le hrκ hC0 _ b _ fun b' hb' => ?_).trans hsmall
    exact abs_levelHessianEntry_le T Cm u hκ.le hM b b' hb hb'
  · refine (row_sum_decayWeightExcess_le hbonds T.L hκ hr0.le hrκ hC0 _ b _ fun b' hb' => ?_).trans hsmall
    rw [supDist_comm]
    exact abs_levelHessianEntry_le T Cm u hκ.le hM b' b hb' hb
end YangMills.Construction.TwoLevelMixtures
end
