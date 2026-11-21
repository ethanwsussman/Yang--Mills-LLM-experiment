import Mathlib
import YangMills.Construction.ResponseInTheExpansion.DerivativeOfAKernel
import YangMills.Construction.ResponseInTheExpansion.DerivativeOfAKernelProof
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import YangMills.Construction.ResponseInTheExpansion.ResponsesOfTheExpansion
import YangMills.Construction.ResponseInTheExpansion.WilsonWeightHasTheExpansionOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.WilsonWeightHasTheExpansionOfTheResponseProof
import YangMills.Construction.ResponseInTheExpansion.MeansOfAWeightProof
import YangMills.Construction.ClusterExpansionOfAStep.TheMeanKernelHasMassOneProofForm
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABondProof
set_option autoImplicit false

noncomputable section

open scoped Quaternion
open MeasureTheory

namespace YangMills.ContinuumLimit

open YangMills.Construction
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields
open YangMills.Construction.StepCosts YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.ResponseInTheExpansion

theorem prod_bondKernel_eq_bonds (ℓ : StepParameters) (X : ℝ) {n : ℕ} [NeZero n]
    (W : TorusField (n * ℓ.side)) (V : TorusField n) (b : BaseChoice ℓ.side n) :
    ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
      bondKernel ℓ X (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
        (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c =
    ∏ c : TorusBond n, bondKernelAt ℓ X W V b c := by
  refine Fintype.prod_equiv
    ((cellEquivTorusSite (L := ℓ.side) (n := n)).prodCongr (Equiv.refl _)) _ _ fun c => ?_
  have hy : torusSiteInFrame (stepBlockFrame ℓ.side n) 1
      (cellEquivTorusSite (L := ℓ.side) (n := n) c.1) = c.1 :=
    (cellEquivTorusSite (L := ℓ.side) (n := n)).symm_apply_apply c.1
  show _ = bondKernel ℓ X (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
    (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b
    (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (cellEquivTorusSite (L := ℓ.side) (n := n) c.1), c.2)
  rw [hy]

theorem hasDerivAt_stepTransitionDensity (hK : KernelHasCouplingDerivative) {ℓ : StepParameters}
    (hℓ : ℓ.Admissible) (x : ℝ) {n : ℕ} [NeZero n] (W : TorusField (n * ℓ.side))
    (b : BaseChoice ℓ.side n) (V : TorusField n) :
    HasDerivAt (fun X => stepTransitionDensity ℓ X W b V)
      (-ℓ.coupling * (∑ c : TorusBond n, bondScore ℓ x W V b c) * stepTransitionDensity ℓ x W b V) x := by
  classical
  by_cases hb : b ∈ baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
  · have he : ∀ X, stepTransitionDensity ℓ X W b V =
        (1 / ((baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W)).card : ℝ)) *
          ∏ c : TorusBond n, bondKernelAt ℓ X W V b c := by
      intro X
      unfold stepTransitionDensity
      rw [if_pos hb, prod_bondKernel_eq_bonds]
    have hp : HasDerivAt (fun X => ∏ c : TorusBond n, bondKernelAt ℓ X W V b c)
        (∑ c : TorusBond n, (∏ c' ∈ Finset.univ.erase c, bondKernelAt ℓ x W V b c') •
          (-ℓ.coupling * bondScore ℓ x W V b c * bondKernelAt ℓ x W V b c)) x :=
      HasDerivAt.fun_finsetProd fun c _ => hK ℓ hℓ x n b c W V
    have hs : (∑ c : TorusBond n, (∏ c' ∈ Finset.univ.erase c, bondKernelAt ℓ x W V b c') •
          (-ℓ.coupling * bondScore ℓ x W V b c * bondKernelAt ℓ x W V b c)) =
        -ℓ.coupling * (∑ c : TorusBond n, bondScore ℓ x W V b c) *
          ∏ c : TorusBond n, bondKernelAt ℓ x W V b c := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [smul_eq_mul, ← Finset.prod_erase_mul Finset.univ (fun c' => bondKernelAt ℓ x W V b c')
        (Finset.mem_univ c)]
      ring
    have h2 := hp.const_mul (1 / ((baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W)).card : ℝ))
    rw [hs] at h2
    rw [show (fun X => stepTransitionDensity ℓ X W b V) = fun X =>
        (1 / ((baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W)).card : ℝ)) *
          ∏ c : TorusBond n, bondKernelAt ℓ X W V b c from funext he, he x]
    exact h2.congr_deriv (by ring)
  · have hz : ∀ X, stepTransitionDensity ℓ X W b V = 0 := by
      intro X
      unfold stepTransitionDensity
      rw [if_neg hb]
    rw [show (fun X => stepTransitionDensity ℓ X W b V) = fun _ => (0 : ℝ) from funext hz, hz x, mul_zero]
    exact hasDerivAt_const x 0

private theorem deriv_partitionFn_eq (s : ℝ) :
    deriv partitionFn s = ∫ g : UnitQuaternion, ((g : UnitQuaternion) : ℍ[ℝ]).re *
      Real.exp (s * ((g : UnitQuaternion) : ℍ[ℝ]).re) ∂haarUnit :=
  (WeightedResponses.BondScore.hasDerivAt_integral_exp_mul
    (fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).re)
    WeightedResponses.BondScore.continuous_re_unitQuaternion s).deriv

private theorem continuous_deriv_partitionFn : Continuous (deriv partitionFn) := by
  have h := continuous_parametric_integral_of_continuous (μ := haarUnit)
    (f := fun (s : ℝ) (g : UnitQuaternion) => ((g : UnitQuaternion) : ℍ[ℝ]).re *
      Real.exp (s * ((g : UnitQuaternion) : ℍ[ℝ]).re))
    (s := Set.univ)
    ((Quaternion.continuous_re.comp (continuous_subtype_val.comp continuous_snd)).mul
      (Real.continuous_exp.comp (continuous_fst.mul
        (Quaternion.continuous_re.comp (continuous_subtype_val.comp continuous_snd))))) isCompact_univ
  have h2 : Continuous fun s : ℝ => ∫ g : UnitQuaternion, ((g : UnitQuaternion) : ℍ[ℝ]).re *
      Real.exp (s * ((g : UnitQuaternion) : ℍ[ℝ]).re) ∂haarUnit := by
    simpa [Measure.restrict_univ] using h
  rw [show deriv partitionFn = fun s : ℝ => ∫ g : UnitQuaternion, ((g : UnitQuaternion) : ℍ[ℝ]).re *
      Real.exp (s * ((g : UnitQuaternion) : ℍ[ℝ]).re) ∂haarUnit from funext deriv_partitionFn_eq]
  exact h2

theorem continuous_bondScore_coupling (hT : BondScoreProperties) {ℓ : StepParameters}
    (hℓ : ℓ.Admissible) {n : ℕ} [NeZero n] (W : TorusField (n * ℓ.side)) (V : TorusField n)
    (b : BaseChoice ℓ.side n) (c : TorusBond n) :
    Continuous fun x => bondScore ℓ x W V b c := by
  have he : ∀ x, bondScore ℓ x W V b c =
      meanNorm ℓ W b c * (deriv partitionFn (ℓ.coupling * x * meanNorm ℓ W b c) /
        partitionFn (ℓ.coupling * x * meanNorm ℓ W b c)) +
      (bondScore ℓ 0 W V b c - meanNorm ℓ W b c * (deriv partitionFn (ℓ.coupling * 0 * meanNorm ℓ W b c) /
        partitionFn (ℓ.coupling * 0 * meanNorm ℓ W b c))) := by
    intro x
    rw [(hT ℓ hℓ x n b c).2.1 W V, (hT ℓ hℓ 0 n b c).2.1 W V]
    ring
  have hlin : Continuous fun x : ℝ => ℓ.coupling * x * meanNorm ℓ W b c :=
    (continuous_const.mul continuous_id).mul continuous_const
  refine Continuous.congr ?_ fun x => (he x).symm
  exact (continuous_const.mul ((continuous_deriv_partitionFn.comp hlin).div
    (KernelMeasurability.continuous_partitionFn.comp hlin)
    fun x => (TorusLumps.partitionFn_pos _).ne')).add continuous_const

theorem le_exp_mul_of_abs_deriv_le {f f' : ℝ → ℝ} {u v B : ℝ}
    (hf : ∀ s ∈ Set.Icc u v, HasDerivAt f (f' s) s) (hB : ∀ s ∈ Set.Icc u v, |f' s| ≤ B * f s)
    {s s' : ℝ} (hs : s ∈ Set.Icc u v) (hs' : s' ∈ Set.Icc u v) :
    f s ≤ Real.exp (B * |s - s'|) * f s' := by
  have hcont : ∀ g g' : ℝ → ℝ, (∀ r ∈ Set.Icc u v, HasDerivAt g (g' r) r) →
      ContinuousOn g (Set.Icc u v) :=
    fun g g' h r hr => (h r hr).continuousAt.continuousWithinAt
  have hwithin : ∀ g g' : ℝ → ℝ, (∀ r ∈ Set.Icc u v, HasDerivAt g (g' r) r) →
      ∀ r ∈ interior (Set.Icc u v), HasDerivWithinAt g (g' r) (interior (Set.Icc u v)) r :=
    fun g g' h r hr => (h r (interior_subset hr)).hasDerivWithinAt
  rcases le_total s' s with h | h
  · have hd : ∀ r ∈ Set.Icc u v, HasDerivAt (fun r => f r * Real.exp (-B * r))
        ((f' r - B * f r) * Real.exp (-B * r)) r := by
      intro r hr
      have h1 : HasDerivAt (fun r : ℝ => -B * r) (-B) r := by
        simpa using (hasDerivAt_id r).const_mul (-B)
      exact ((hf r hr).mul h1.exp).congr_deriv (by ring)
    have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc u v) (hcont _ _ hd)
      (hwithin _ _ hd) fun r hr => by
        have h3 := hB r (interior_subset hr)
        have h4 : f' r - B * f r ≤ 0 := by linarith [le_abs_self (f' r)]
        nlinarith [Real.exp_pos (-B * r)]
    have key : f s * Real.exp (-B * s) ≤ f s' * Real.exp (-B * s') := hanti hs' hs h
    have e1 : Real.exp (-B * s) * Real.exp (B * s) = 1 := by
      rw [← Real.exp_add]
      simp
    have e2 : Real.exp (-B * s') * Real.exp (B * s) = Real.exp (B * |s - s'|) := by
      rw [← Real.exp_add, abs_of_nonneg (sub_nonneg.mpr h)]
      congr 1
      ring
    calc f s = f s * Real.exp (-B * s) * Real.exp (B * s) := by rw [mul_assoc, e1, mul_one]
      _ ≤ f s' * Real.exp (-B * s') * Real.exp (B * s) :=
        mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
      _ = Real.exp (B * |s - s'|) * f s' := by rw [mul_assoc, e2, mul_comm]
  · have hd : ∀ r ∈ Set.Icc u v, HasDerivAt (fun r => f r * Real.exp (B * r))
        ((f' r + B * f r) * Real.exp (B * r)) r := by
      intro r hr
      have h1 : HasDerivAt (fun r : ℝ => B * r) B r := by
        simpa using (hasDerivAt_id r).const_mul B
      exact ((hf r hr).mul h1.exp).congr_deriv (by ring)
    have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc u v) (hcont _ _ hd)
      (hwithin _ _ hd) fun r hr => by
        have h3 := hB r (interior_subset hr)
        have h4 : 0 ≤ f' r + B * f r := by linarith [neg_abs_le (f' r)]
        exact mul_nonneg h4 (Real.exp_pos _).le
    have key : f s * Real.exp (B * s) ≤ f s' * Real.exp (B * s') := hmono hs hs' h
    have e1 : Real.exp (B * s) * Real.exp (-B * s) = 1 := by
      rw [← Real.exp_add]
      simp
    have e2 : Real.exp (B * s') * Real.exp (-B * s) = Real.exp (B * |s - s'|) := by
      rw [← Real.exp_add, abs_of_nonpos (sub_nonpos.mpr h)]
      congr 1
      ring
    calc f s = f s * Real.exp (B * s) * Real.exp (-B * s) := by rw [mul_assoc, e1, mul_one]
      _ ≤ f s' * Real.exp (B * s') * Real.exp (-B * s) :=
        mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
      _ = Real.exp (B * |s - s'|) * f s' := by rw [mul_assoc, e2, mul_comm]

theorem hasDerivAt_wilsonWeight (L : ℕ) {n : ℕ} [NeZero n] (W : TorusField n) (γ : ℝ) :
    HasDerivAt (fun γ' => wilsonWeight γ' n W)
      (-wilsonWeight γ n W * ∑ y : TorusSite n, wilsonColdResponse L n y W (constOneWeight _)) γ := by
  have hS : ∑ y : TorusSite n, wilsonColdResponse L n y W (constOneWeight _) =
      wilsonAction Finset.univ W :=
    sum_siteResponse_constOne W
  have hw : (fun γ' => wilsonWeight γ' n W) = fun γ' => Real.exp (-γ' * wilsonAction Finset.univ W) :=
    funext fun γ' => ResponseInTheExpansion.wilsonWeight_eq W
  rw [hw, ResponseInTheExpansion.wilsonWeight_eq W, hS]
  have h1 : HasDerivAt (fun γ' : ℝ => -γ' * wilsonAction Finset.univ W) (-wilsonAction Finset.univ W) γ := by
    simpa using (hasDerivAt_id γ).neg.mul_const (wilsonAction Finset.univ W)
  convert h1.exp using 1
  ring

theorem bondBlockMean_constOne (L : ℕ) [NeZero L] (hodd : Odd L) (t n : ℕ) [NeZero n]
    (c : TorusBond n) : bondBlockMean L t n (constOneWeight _) c = 1 := by
  unfold bondBlockMean
  rw [(blockMean_one_and_linear_and_local L hodd t n c.1).1,
    (blockMean_one_and_linear_and_local L hodd t n (c.1 + TorusFields.unitStep n c.2)).1]
  norm_num

end YangMills.ContinuumLimit

end
