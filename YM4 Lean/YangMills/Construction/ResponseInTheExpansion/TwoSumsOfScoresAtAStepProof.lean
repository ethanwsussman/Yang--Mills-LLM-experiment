import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import YangMills.Construction.ResponseInTheExpansion.TwoSumsOfScoresAtAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepCosts BlockAverages
namespace ScoreSums
variable {n : ℕ} [NeZero n]
theorem integral_prod_over_bonds (f : TorusBond n → UnitQuaternion → ℝ) :
    ∫ U : TorusField n, ∏ c : TorusBond n, f c (U c.1 c.2) ∂(fieldHaar n) =
      ∏ c : TorusBond n, ∫ g, f c g ∂haarUnit := by
  have hsplit : ∀ U : TorusField n, ∏ c : TorusBond n, f c (U c.1 c.2) =
      ∏ z : TorusSite n, ∏ i : Fin 4, f (z, i) (U z i) :=
    fun U => Fintype.prod_prod_type _
  simp only [hsplit]
  unfold fieldHaar
  rw [integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun _ : TorusSite n => Measure.pi fun _ : Fin 4 => haarUnit)
    (f := fun z u => ∏ i : Fin 4, f (z, i) (u i)), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun z _ => ?_
  exact integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun _ : Fin 4 => haarUnit) (f := fun i g => f (z, i) g)
variable (k s : TorusBond n → UnitQuaternion → ℝ)
theorem integral_score_pair (hk : ∀ c, ∫ g, k c g ∂haarUnit = 1)
    (hs : ∀ c, ∫ g, s c g * k c g ∂haarUnit = 0) (c c' : TorusBond n) :
    ∫ U : TorusField n, s c (U c.1 c.2) * s c' (U c'.1 c'.2) * ∏ e : TorusBond n, k e (U e.1 e.2) ∂(fieldHaar n) =
      if c = c' then ∫ g, s c g ^ 2 * k c g ∂haarUnit else 0 := by
  classical
  set f : TorusBond n → UnitQuaternion → ℝ := fun e g =>
    (if e = c then s c g else 1) * (if e = c' then s c' g else 1) * k e g with hf
  have hU : ∀ U : TorusField n, s c (U c.1 c.2) * s c' (U c'.1 c'.2) * ∏ e : TorusBond n, k e (U e.1 e.2) =
      ∏ e : TorusBond n, f e (U e.1 e.2) := by
    intro U
    simp only [hf, Finset.prod_mul_distrib]
    congr 2
    · rw [Finset.prod_ite_eq' Finset.univ c]
      simp
    · rw [Finset.prod_ite_eq' Finset.univ c']
      simp
  simp only [hU]
  rw [integral_prod_over_bonds]
  by_cases hcc : c = c'
  · subst hcc
    rw [if_pos rfl, Finset.prod_eq_single c]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only [hf, if_true]
      ring
    · intro e _ he
      simp only [hf, if_neg he, one_mul]
      exact hk e
    · intro h
      exact absurd (Finset.mem_univ c) h
  · rw [if_neg hcc]
    refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
    have e : ∀ g, f c g = s c g * k c g := fun g => by
      simp only [hf, if_true, if_neg hcc, mul_one]
    simp only [e]
    exact hs c
theorem integral_weighted_score_sums (hkc : ∀ c, Continuous (k c)) (hsc : ∀ c, Continuous (s c))
    (hk : ∀ c, ∫ g, k c g ∂haarUnit = 1) (hs : ∀ c, ∫ g, s c g * k c g ∂haarUnit = 0)
    (v v' : TorusBond n → ℝ) :
    ∫ U : TorusField n, (∑ c : TorusBond n, v c * s c (U c.1 c.2)) * (∑ c : TorusBond n, v' c * s c (U c.1 c.2)) *
        ∏ e : TorusBond n, k e (U e.1 e.2) ∂(fieldHaar n) =
      ∑ c : TorusBond n, v c * v' c * ∫ g, s c g ^ 2 * k c g ∂haarUnit := by
  classical
  have hread : ∀ c : TorusBond n, Continuous fun U : TorusField n => U c.1 c.2 := fun c =>
    (continuous_apply c.2).comp (continuous_apply c.1)
  have hK : Continuous fun U : TorusField n => ∏ e : TorusBond n, k e (U e.1 e.2) :=
    continuous_finsetProd _ fun e _ => (hkc e).comp (hread e)
  have hcont : ∀ c c' : TorusBond n, Continuous fun U : TorusField n =>
      s c (U c.1 c.2) * s c' (U c'.1 c'.2) * ∏ e : TorusBond n, k e (U e.1 e.2) := fun c c' =>
    (((hsc c).comp (hread c)).mul ((hsc c').comp (hread c'))).mul hK
  have hint : ∀ c c' : TorusBond n, Integrable (fun U : TorusField n =>
      s c (U c.1 c.2) * s c' (U c'.1 c'.2) * ∏ e : TorusBond n, k e (U e.1 e.2)) (fieldHaar n) := fun c c' =>
    (hcont c c').integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hexp : ∀ U : TorusField n, (∑ c : TorusBond n, v c * s c (U c.1 c.2)) *
      (∑ c : TorusBond n, v' c * s c (U c.1 c.2)) * ∏ e : TorusBond n, k e (U e.1 e.2) =
      ∑ c : TorusBond n, ∑ c' : TorusBond n, v c * v' c' *
        (s c (U c.1 c.2) * s c' (U c'.1 c'.2) * ∏ e : TorusBond n, k e (U e.1 e.2)) := by
    intro U
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c' _ => ?_
    ring
  simp only [hexp]
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ => (hint c c').const_mul _]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun c' _ => (hint c c').const_mul _]
  simp only [integral_const_mul, integral_score_pair k s hk hs]
  simp
end ScoreSums
theorem scoreSumCovariance_holds (hK : BondKernelProperties) (hSc : BondScoreProperties) :
    ScoreSumCovariance := by
  classical
  intro ℓ hf x n _ W v v'
  set w := readAtLevel (stepBlockFrame ℓ.side n) 0 W with hw
  have main : ∀ b : BaseChoice ℓ.side n,
      ∫ U : TorusField n, (∑ c : TorusBond n, v c * bondScore ℓ x W U b c) *
        (∑ c : TorusBond n, v' c * bondScore ℓ x W U b c) * stepTransitionDensity ℓ x W b U ∂(fieldHaar n) =
      ∑ c : TorusBond n, v c * v' c *
        ∫ U : TorusField n, bondScoreVariance ℓ x W b c * stepTransitionDensity ℓ x W b U ∂(fieldHaar n) := by
    intro b
    set k : TorusBond n → UnitQuaternion → ℝ := fun c => kernelOfElement ℓ x w b c with hk
    set s : TorusBond n → UnitQuaternion → ℝ := fun c g => fitOfElement ℓ w b c g - fitConditionalMean ℓ x W b c with hs
    have hk1 : ∀ c, ∫ g, k c g ∂haarUnit = 1 := by
      intro c
      have h := (hK.2 ℓ x n w (fun _ _ => 1) b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)).2.2
      have hw' : ∀ g : UnitQuaternion, bondKernel ℓ x w
          (updateBond (fun _ _ => 1) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) g) b
          (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) = kernelOfElement ℓ x w b c g := by
        intro g
        simp [bondKernel, kernelOfElement, bondMean, updateBond]
      have he : (fun g : UnitQuaternion => kernelOfElement ℓ x w b c g) = fun g : UnitQuaternion =>
          bondKernel ℓ x w (updateBond (fun _ _ => 1) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) g) b
            (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) := funext fun g => (hw' g).symm
      show ∫ g, kernelOfElement ℓ x w b c g ∂haarUnit = 1
      rw [he]
      exact h
    have hkc : ∀ c, Continuous (k c) := fun c => continuous_kernelOfElement ℓ x w b c
    have hsc : ∀ c, Continuous (s c) := fun c => (continuous_fitOfElement ℓ w b c).sub continuous_const
    have hscore : ∀ (U : TorusField n) (c : TorusBond n), bondScore ℓ x W U b c = s c (U c.1 c.2) := by
      intro U c
      simp only [bondScore, hs, bondFit_eq_fitOfElement, hw]
    have hkern : ∀ (U : TorusField n) (c : TorusBond n), bondKernelAt ℓ x W U b c = k c (U c.1 c.2) := fun U c =>
      bondKernelAt_eq_kernelOfElement ℓ x W U b c
    have hs0 : ∀ c, ∫ g, s c g * k c g ∂haarUnit = 0 := by
      intro c
      have h := (hSc ℓ hf x n b c).2.2.2.1 W (trivialField n)
      have e : ∀ g : UnitQuaternion, bondScore ℓ x W (fieldAtBond (trivialField n) c g) b c *
          bondKernelAt ℓ x W (fieldAtBond (trivialField n) c g) b c = s c g * k c g := by
        intro g
        rw [hscore, hkern, fieldAtBond_apply_self]
      simp only [e] at h
      exact h
    have hvar : ∀ c, bondScoreVariance ℓ x W b c = ∫ g, s c g ^ 2 * k c g ∂haarUnit := by
      intro c
      have e1 : ∀ g : UnitQuaternion, bondScore ℓ x W (fieldAtBond (trivialField n) c g) b c ^ 2 *
          bondKernelAt ℓ x W (fieldAtBond (trivialField n) c g) b c = s c g ^ 2 * k c g := by
        intro g
        rw [hscore, hkern, fieldAtBond_apply_self]
      have e2 : ∀ g : UnitQuaternion, bondScore ℓ x W (fieldAtBond (trivialField n) c g) b c *
          bondKernelAt ℓ x W (fieldAtBond (trivialField n) c g) b c = s c g * k c g := by
        intro g
        rw [hscore, hkern, fieldAtBond_apply_self]
      unfold bondScoreVariance
      simp only [e1, e2, hs0]
      ring
    have hprod : ∀ U : TorusField n, ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
        bondKernel ℓ x w (readAtLevel (stepBlockFrame ℓ.side n) 1 U) b c = ∏ c : TorusBond n, k c (U c.1 c.2) := by
      intro U
      rw [← (Equiv.prodCongr (torusSiteEquivCell (L := ℓ.side) (n := n)) (Equiv.refl (Fin 4))).prod_comp]
      refine Finset.prod_congr rfl fun c _ => ?_
      exact bondKernelAt_eq_kernelOfElement ℓ x W U b c
    have hmass : ∫ U : TorusField n, ∏ c : TorusBond n, k c (U c.1 c.2) ∂(fieldHaar n) = 1 := by
      rw [ScoreSums.integral_prod_over_bonds]
      exact Finset.prod_eq_one fun c _ => hk1 c
    by_cases hb : b ∈ baseChoices ℓ w
    · have hden : ∀ U : TorusField n, stepTransitionDensity ℓ x W b U =
          (1 / ((baseChoices ℓ w).card : ℝ)) * ∏ c : TorusBond n, k c (U c.1 c.2) := by
        intro U
        unfold stepTransitionDensity
        rw [if_pos hb, hprod]
      have h1 := ScoreSums.integral_weighted_score_sums k s hkc hsc hk1 hs0 v v'
      have e1 : ∀ U : TorusField n, (∑ c : TorusBond n, v c * bondScore ℓ x W U b c) *
          (∑ c : TorusBond n, v' c * bondScore ℓ x W U b c) * stepTransitionDensity ℓ x W b U =
          (1 / ((baseChoices ℓ w).card : ℝ)) * ((∑ c : TorusBond n, v c * s c (U c.1 c.2)) *
            (∑ c : TorusBond n, v' c * s c (U c.1 c.2)) * ∏ e : TorusBond n, k e (U e.1 e.2)) := by
        intro U
        rw [hden]
        simp only [hscore]
        ring
      simp only [e1]
      rw [integral_const_mul, h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      have e2 : ∀ U : TorusField n, bondScoreVariance ℓ x W b c * stepTransitionDensity ℓ x W b U =
          bondScoreVariance ℓ x W b c * (1 / ((baseChoices ℓ w).card : ℝ)) * ∏ e : TorusBond n, k e (U e.1 e.2) := by
        intro U
        rw [hden]
        ring
      simp only [e2]
      rw [integral_const_mul, hmass, hvar]
      ring
    · have hden : ∀ U : TorusField n, stepTransitionDensity ℓ x W b U = 0 := by
        intro U
        unfold stepTransitionDensity
        rw [if_neg hb]
      simp [hden]
  simp only [main]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
end YangMills.Construction.WeightedResponses
end
