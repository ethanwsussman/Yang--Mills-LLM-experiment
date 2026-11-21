import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import YangMills.Construction.ResponseInTheExpansion.ElementsOfABond
import YangMills.Construction.ResponseInTheExpansion.ProductsOfScoresAtAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps StepCosts BlockAverages WeightedResponses
namespace ScoreProducts
variable {n : ℕ}
section Core
variable [NeZero n] {m : ℕ} (k s : TorusBond n → UnitQuaternion → ℝ)
theorem integral_prod_kernels_eq_one (hkc : ∀ c, Continuous (k c)) (hk : ∀ c, ∫ g, k c g ∂haarUnit = 1) :
    ∫ V : TorusField n, ∏ c : TorusBond n, k c (V c.1 c.2) ∂(fieldHaar n) = 1 := by
  have hprod : ∀ V : TorusField n, ∏ c : TorusBond n, k c (V c.1 c.2) =
      ∏ z : TorusSite n, ∏ i : Fin 4, k (z, i) (V z i) :=
    fun V => Fintype.prod_prod_type _
  simp only [hprod]
  unfold fieldHaar
  rw [integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun _ : TorusSite n => Measure.pi fun _ : Fin 4 => haarUnit)
    (f := fun z v => ∏ i : Fin 4, k (z, i) (v i))]
  refine Finset.prod_eq_one fun z _ => ?_
  rw [integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun _ : Fin 4 => haarUnit)
    (f := fun i g => k (z, i) g)]
  exact Finset.prod_eq_one fun i _ => hk _
theorem continuous_eval_bond (c : TorusBond n) : Continuous fun V : TorusField n => V c.1 c.2 :=
  (continuous_apply c.2).comp (continuous_apply c.1)
theorem integral_prod_affine_mul_kernels (hkc : ∀ c, Continuous (k c)) (hsc : ∀ c, Continuous (s c))
    (hk : ∀ c, ∫ g, k c g ∂haarUnit = 1) (hs : ∀ c, ∫ g, s c g * k c g ∂haarUnit = 0)
    (a : Fin m → ℝ) (v : Fin m → TorusBond n → ℝ)
    (hv : ∀ (c : TorusBond n) (i i' : Fin m), i ≠ i' → v i c = 0 ∨ v i' c = 0) (J : Finset (Fin m)) :
    ∫ V : TorusField n, (∏ i ∈ J, (a i + ∑ c : TorusBond n, v i c * s c (V c.1 c.2))) *
        ∏ c : TorusBond n, k c (V c.1 c.2) ∂(fieldHaar n) = ∏ i ∈ J, a i := by
  classical
  set K : TorusField n → ℝ := fun V => ∏ c : TorusBond n, k c (V c.1 c.2) with hKdef
  set f : Fin m → TorusField n → ℝ := fun i V => a i + ∑ c : TorusBond n, v i c * s c (V c.1 c.2) with hf
  have hKc : Continuous K := continuous_finsetProd _ fun c _ => (hkc c).comp (continuous_eval_bond c)
  have hfc : ∀ i, Continuous (f i) := fun i =>
    continuous_const.add (continuous_finsetSum _ fun c _ =>
      continuous_const.mul ((hsc c).comp (continuous_eval_bond c)))
  induction J using Finset.induction_on with
  | empty =>
    simpa using integral_prod_kernels_eq_one k hkc hk
  | insert j J hj ih =>
    set H : TorusField n → ℝ := fun V => ∏ i ∈ J, f i V with hH
    have hHc : Continuous H := continuous_finsetProd _ fun i _ => hfc i
    have hsplit : ∀ V : TorusField n, (∏ i ∈ insert j J, f i V) * K V =
        a j * (H V * K V) + ∑ c : TorusBond n, v j c * (s c (V c.1 c.2) * H V * K V) := by
      intro V
      rw [Finset.prod_insert hj]
      simp only [hf, hH, add_mul, Finset.sum_mul, Finset.mul_sum]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun c _ => ?_
        ring
    have hzero : ∀ c : TorusBond n, v j c * ∫ V, s c (V c.1 c.2) * H V * K V ∂(fieldHaar n) = 0 := by
      intro c
      by_cases hc : v j c = 0
      · simp [hc]
      have hT : Continuous fun V : TorusField n => s c (V c.1 c.2) * H V * K V :=
        (((hsc c).comp (continuous_eval_bond c)).mul hHc).mul hKc
      have hread : ∀ (V : TorusField n) (g : UnitQuaternion), H (fieldAtBond V c g) = H V := by
        intro V g
        refine Finset.prod_congr rfl fun i hi => ?_
        have hij : j ≠ i := fun h => hj (h ▸ hi)
        have hvi : v i c = 0 := (hv c j i hij).resolve_left hc
        simp only [hf]
        congr 1
        refine Finset.sum_congr rfl fun c' _ => ?_
        by_cases hcc : c' = c
        · subst hcc
          simp [hvi]
        · rw [fieldAtBond_apply_of_ne V c c' g hcc]
      have hKsplit : ∀ (V : TorusField n) (g : UnitQuaternion), K (fieldAtBond V c g) =
          k c g * ∏ c' ∈ Finset.univ.erase c, k c' (V c'.1 c'.2) := by
        intro V g
        simp only [hKdef]
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c), fieldAtBond_apply_self]
        congr 1
        refine Finset.prod_congr rfl fun c' hc' => ?_
        rw [fieldAtBond_apply_of_ne V c c' g (Finset.ne_of_mem_erase hc')]
      rw [integral_eq_integral_resampleBond c _ hT]
      have hinner : ∀ V : TorusField n, ∫ g, s c (fieldAtBond V c g c.1 c.2) * H (fieldAtBond V c g) *
          K (fieldAtBond V c g) ∂haarUnit = 0 := by
        intro V
        have he : ∀ g : UnitQuaternion, s c (fieldAtBond V c g c.1 c.2) * H (fieldAtBond V c g) *
            K (fieldAtBond V c g) =
            (H V * ∏ c' ∈ Finset.univ.erase c, k c' (V c'.1 c'.2)) * (s c g * k c g) := by
          intro g
          rw [hread, hKsplit, fieldAtBond_apply_self]
          ring
        simp only [he]
        rw [integral_const_mul, hs, mul_zero]
      simp [hinner]
    have hIntHK : Integrable (fun V : TorusField n => H V * K V) (fieldHaar n) :=
      Continuous.integrable_of_hasCompactSupport (hHc.mul hKc) (HasCompactSupport.of_compactSpace _)
    have hIntT : ∀ c : TorusBond n,
        Integrable (fun V : TorusField n => v j c * (s c (V c.1 c.2) * H V * K V)) (fieldHaar n) :=
      fun c => Continuous.integrable_of_hasCompactSupport
        (continuous_const.mul ((((hsc c).comp (continuous_eval_bond c)).mul hHc).mul hKc))
        (HasCompactSupport.of_compactSpace _)
    have ih' : ∫ V, H V * K V ∂(fieldHaar n) = ∏ i ∈ J, a i := ih
    show ∫ V, (∏ i ∈ insert j J, f i V) * K V ∂(fieldHaar n) = _
    simp only [hsplit]
    rw [integral_add (hIntHK.const_mul _) (integrable_finset_sum _ fun c _ => hIntT c),
      integral_const_mul, integral_finset_sum _ fun c _ => hIntT c]
    simp only [integral_const_mul, hzero, Finset.sum_const_zero, add_zero]
    rw [Finset.prod_insert hj, ih']
end Core
section Mass
variable [NeZero n]
theorem integral_kernelOfElement_eq_one (hK : BondKernelProperties) (ℓ : StepParameters) (x : ℝ)
    (w : (stepBlockFrame ℓ.side n).GaugeField 0) (b : BaseChoice ℓ.side n) (c : TorusBond n) :
    ∫ g, kernelOfElement ℓ x w b c g ∂haarUnit = 1 := by
  have h := (hK.2 ℓ x n w (fun _ _ => 1) b (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)).2.2
  have hw : ∀ g : UnitQuaternion, bondKernel ℓ x w
      (updateBond (fun _ _ => 1) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) g) b
      (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) = kernelOfElement ℓ x w b c g := by
    intro g
    simp [bondKernel, kernelOfElement, bondMean, updateBond]
  have he : (fun g : UnitQuaternion => kernelOfElement ℓ x w b c g) = fun g : UnitQuaternion =>
      bondKernel ℓ x w (updateBond (fun _ _ => 1) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) g) b
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) := funext fun g => (hw g).symm
  rw [he]
  exact h
end Mass
theorem meanOfScoreProducts (hK : BondKernelProperties) : MeanOfScoreProductsStatement := by
  intro ℓ x n _ W b m a v hv
  set w := readAtLevel (stepBlockFrame ℓ.side n) 0 W with hw
  set k : TorusBond n → UnitQuaternion → ℝ := fun c => kernelOfElement ℓ x w b c with hk
  set s : TorusBond n → UnitQuaternion → ℝ := fun c g => fitOfElement ℓ w b c g - fitConditionalMean ℓ x W b c with hs
  have hk1 : ∀ c, ∫ g, k c g ∂haarUnit = 1 := fun c => integral_kernelOfElement_eq_one hK ℓ x w b c
  have hkc : ∀ c, Continuous (k c) := fun c => continuous_kernelOfElement ℓ x w b c
  have hsc : ∀ c, Continuous (s c) := fun c => (continuous_fitOfElement ℓ w b c).sub continuous_const
  have hmean : ∀ c, fitConditionalMean ℓ x W b c = ∫ g, fitOfElement ℓ w b c g * k c g ∂haarUnit := by
    intro c
    unfold fitConditionalMean
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show bondFit ℓ W _ b c * bondKernelAt ℓ x W _ b c = _
    rw [bondFit_eq_fitOfElement, bondKernelAt_eq_kernelOfElement, fieldAtBond_apply_self]
  have hs0 : ∀ c, ∫ g, s c g * k c g ∂haarUnit = 0 := by
    intro c
    have hi1 : Integrable (fun g => fitOfElement ℓ w b c g * k c g) haarUnit :=
      Continuous.integrable_of_hasCompactSupport ((continuous_fitOfElement ℓ w b c).mul (hkc c))
        (HasCompactSupport.of_compactSpace _)
    have hi2 : Integrable (k c) haarUnit :=
      Continuous.integrable_of_hasCompactSupport (hkc c) (HasCompactSupport.of_compactSpace _)
    have he : ∀ g, s c g * k c g = fitOfElement ℓ w b c g * k c g - fitConditionalMean ℓ x W b c * k c g :=
      fun g => by
        simp only [hs]
        ring
    simp only [he]
    rw [integral_sub hi1 (hi2.const_mul _), integral_const_mul, hk1, ← hmean]
    ring
  have hscore : ∀ (V : TorusField n) (c : TorusBond n), bondScore ℓ x W V b c = s c (V c.1 c.2) := by
    intro V c
    simp only [bondScore, hs, bondFit_eq_fitOfElement, hw]
  have hprod : ∀ V : TorusField n, ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
      bondKernel ℓ x w (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c = ∏ c : TorusBond n, k c (V c.1 c.2) := by
    intro V
    rw [← (Equiv.prodCongr (torusSiteEquivCell (L := ℓ.side) (n := n)) (Equiv.refl (Fin 4))).prod_comp]
    refine Finset.prod_congr rfl fun c _ => ?_
    exact bondKernelAt_eq_kernelOfElement ℓ x W V b c
  simp only [hscore, hprod]
  simpa using integral_prod_affine_mul_kernels k s hkc hsc hk1 hs0 a v hv Finset.univ
end ScoreProducts
end YangMills.Construction.ResponseInTheExpansion
end
