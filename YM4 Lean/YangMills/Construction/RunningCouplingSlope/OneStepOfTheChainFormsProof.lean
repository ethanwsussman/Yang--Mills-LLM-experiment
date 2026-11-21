import YangMills.Construction.RunningCouplingSlope.GreenKernelsOfAChainForm
import YangMills.Construction.RunningCouplingSlope.LatticeFormsHaveATreeGauge
import YangMills.Construction.RunningCouplingSlope.LatticeResponseOfAKilledForm
import YangMills.Construction.RunningCouplingSlope.LimitOfAChainFormKillsClosedForms
import YangMills.Construction.RunningCouplingSlope.MeansOfTheConstantAndLinearForms
import YangMills.Construction.RunningCouplingSlope.NextFormOfResponsesIsAChainForm
import YangMills.Construction.RunningCouplingSlope.OneStepOfTheChainForms
import YangMills.Construction.RunningCouplingSlope.ResponsesOfGreenKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open FlatLinearization SlopeCoefficient BlockAverages TorusLumps
namespace RunningCouplingSlope
private theorem latticeLineSum_add (ξ η : LatticeOneForm) (z : Fin 4 → ℤ) (l : List PathStep) :
    latticeLineSum (fun e => ξ e + η e) z l = latticeLineSum ξ z l + latticeLineSum η z l := by
  induction l generalizing z with
  | nil => simp [latticeLineSum]
  | cons s r ih =>
    simp only [latticeLineSum, ih]
    split_ifs <;> ring
private theorem latticeContourAverage_add (L : ℕ) (ξ η : LatticeOneForm) (c : LatticeBond) :
    latticeContourAverage L (fun e => ξ e + η e) c =
      latticeContourAverage L ξ c + latticeContourAverage L η c := by
  simp only [latticeContourAverage, latticeLineSum_add, Finset.sum_add_distrib]
  ring
private theorem hasPolynomialGrowth_add {v w : LatticeOneForm} (hv : HasPolynomialGrowth v)
    (hw : HasPolynomialGrowth w) : HasPolynomialGrowth fun e => v e + w e := by
  obtain ⟨C, m, h⟩ := hv
  obtain ⟨D, k, g⟩ := hw
  refine ⟨|C| + |D|, max m k, fun e => ?_⟩
  have h1 : (1 : ℝ) ≤ 1 + offsetNormReal e.1 := by
    have : (0 : ℝ) ≤ offsetNormReal e.1 := Nat.cast_nonneg _
    linarith
  have p1 : (1 + offsetNormReal e.1) ^ m ≤ (1 + offsetNormReal e.1) ^ max m k :=
    Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _)
  have p2 : (1 + offsetNormReal e.1) ^ k ≤ (1 + offsetNormReal e.1) ^ max m k :=
    Real.rpow_le_rpow_of_exponent_le h1 (le_max_right _ _)
  have q0 : 0 ≤ (1 + offsetNormReal e.1) ^ m := Real.rpow_nonneg (by linarith) _
  have q1 : 0 ≤ (1 + offsetNormReal e.1) ^ k := Real.rpow_nonneg (by linarith) _
  have a1 : C * (1 + offsetNormReal e.1) ^ m ≤ |C| * (1 + offsetNormReal e.1) ^ max m k :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) q0).trans
      (mul_le_mul_of_nonneg_left p1 (abs_nonneg C))
  have a2 : D * (1 + offsetNormReal e.1) ^ k ≤ |D| * (1 + offsetNormReal e.1) ^ max m k :=
    (mul_le_mul_of_nonneg_right (le_abs_self D) q1).trans
      (mul_le_mul_of_nonneg_left p2 (abs_nonneg D))
  calc |v e + w e| ≤ |v e| + |w e| := abs_add_le _ _
    _ ≤ C * (1 + offsetNormReal e.1) ^ m + D * (1 + offsetNormReal e.1) ^ k :=
        add_le_add (h e) (g e)
    _ ≤ (|C| + |D|) * (1 + offsetNormReal e.1) ^ max m k := by
        rw [add_mul]; exact add_le_add a1 a2
private theorem hasPolynomialGrowth_of_bounded {w : LatticeOneForm} {C : ℝ} (h : ∀ e, |w e| ≤ C) :
    HasPolynomialGrowth w :=
  ⟨C, 0, fun e => by simpa using h e⟩
private theorem abs_constantOneForm_le (ν : Fin 4) (c : LatticeBond) : |constantOneForm ν c| ≤ 1 := by
  unfold constantOneForm
  split_ifs <;> simp
theorem flatLinearizationStep_of_parts (hG : greenKernelsExistStatement)
    (hR : GreenFamilyResponses) (hK : latticeResponseOfAnnihilatedStatement)
    (hC : flowKernelLimitAnnihilatesClosedStatement) (hM : ContourAveragesOfConstantAndLinear)
    (hT : latticeTreeGaugeStatement) (hN : RenormalizedKernelIsFlowKernel) :
    FlatLinearizationStep := by
  intro a ha L hL h hc
  obtain ⟨hl, hlim⟩ := hc.tendsto
  obtain ⟨G, Gl, hgreen⟩ := hG a ha L hL h hl hc hlim
  have hfam := hR a ha L hL h hl G Gl hc hlim hgreen
  obtain ⟨-, hconst, hgrad, hlin⟩ := hC h hl hc hlim
  obtain ⟨hmc, hml⟩ := hM L hL
  have hkill := hK a ha L hL h hl G Gl hc hlim hgreen
  have hL0 : (1 : ℝ) ≤ L := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  have hinv : (L : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL0
  have hinv0 : 0 ≤ (L : ℝ)⁻¹ := by positivity
  refine ⟨responseOfInverse a L G, latticeResponseOfInverse a L Gl, ?_, hfam.minimizer_and_pos,
    hN a ha L hL h _ _ hc hfam⟩
  refine ⟨hfam.exp_decay, hfam.translation_invariant, hfam.tendsto, fun ν => ?_, ?_⟩
  · obtain ⟨φ, hoff, hbd, -, hm0⟩ := hT L hL fun e => (L : ℝ)⁻¹ * constantOneForm ν e
    obtain ⟨C, hφ⟩ := hbd ⟨1, fun e => by
      rw [abs_mul, abs_of_nonneg hinv0]
      calc (L : ℝ)⁻¹ * |constantOneForm ν e| ≤ 1 * 1 :=
            mul_le_mul hinv (abs_constantOneForm_le ν e) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1⟩
    refine ⟨φ, ⟨C, hφ⟩, fun e => ?_⟩
    have hpoly : HasPolynomialGrowth fun e =>
        (L : ℝ)⁻¹ * constantOneForm ν e + latticeGradient φ e := by
      refine hasPolynomialGrowth_of_bounded (C := 1 + (C + C)) fun e => ?_
      have e1 : |(L : ℝ)⁻¹ * constantOneForm ν e| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hinv0]
        calc (L : ℝ)⁻¹ * |constantOneForm ν e| ≤ 1 * 1 :=
              mul_le_mul hinv (abs_constantOneForm_le ν e) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have e2 : |latticeGradient φ e| ≤ C + C := by
        unfold latticeGradient
        exact (abs_sub _ _).trans (add_le_add (hφ _) (hφ _))
      exact (abs_add_le _ _).trans (add_le_add e1 e2)
    have hkilled : ∀ e, HasSum (fun c => hl e c *
        ((L : ℝ)⁻¹ * constantOneForm ν c + latticeGradient φ c)) 0 := by
      intro e
      have s := ((hconst ν e).mul_left (L : ℝ)⁻¹).add (hgrad φ ⟨C, 0, fun z => by simpa using hφ z⟩ e)
      simp only [mul_zero, add_zero] at s
      have heq : (fun c => hl e c * ((L : ℝ)⁻¹ * constantOneForm ν c + latticeGradient φ c)) =
          fun c => (L : ℝ)⁻¹ * (hl e c * constantOneForm ν c) + hl e c * latticeGradient φ c := by
        funext c
        ring
      rw [heq]
      exact s
    have key := hkill _ hpoly hoff hkilled e
    have hmean : ∀ c, latticeContourAverage L
        (fun e => (L : ℝ)⁻¹ * constantOneForm ν e + latticeGradient φ e) c =
        constantOneForm ν c := fun c => by
      rw [latticeContourAverage_add, hmc, hm0, add_zero]
    simpa only [hmean] using key
  · obtain ⟨φ, hoff, -, hpol, hm0⟩ := hT L hL (fineLinearPotential L)
    have hw0 : HasPolynomialGrowth (fineLinearPotential L) := by
      refine ⟨1, 1, fun e => ?_⟩
      have hb0 : |((e.1 0 : ℤ) : ℝ)| ≤ offsetNormReal e.1 := by
        have : (e.1 0).natAbs ≤ TorusLumps.offsetNorm e.1 :=
          Finset.le_sup (f := fun i => (e.1 i).natAbs) (Finset.mem_univ (0 : Fin 4))
        have h2 : ((((e.1 0).natAbs : ℕ) : ℝ)) ≤ (TorusLumps.offsetNorm e.1 : ℝ) := by
          exact_mod_cast this
        have h3 : |((e.1 0 : ℤ) : ℝ)| = (((e.1 0).natAbs : ℕ) : ℝ) := by
          rw [Nat.cast_natAbs]
          push_cast
          rfl
        rw [h3]
        exact h2
      have hn : (0 : ℝ) ≤ offsetNormReal e.1 := Nat.cast_nonneg _
      unfold fineLinearPotential
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (L : ℝ)⁻¹ ^ 2), Real.rpow_one, one_mul]
      have i2 : (L : ℝ)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ hinv0 hinv
      calc (L : ℝ)⁻¹ ^ 2 * |((e.1 0 : ℤ) : ℝ)| * |constantOneForm secondAxis e|
          ≤ 1 * offsetNormReal e.1 * 1 :=
            mul_le_mul (mul_le_mul i2 hb0 (abs_nonneg _) zero_le_one)
              (abs_constantOneForm_le _ e) (abs_nonneg _) (by simpa using hn)
        _ ≤ 1 + offsetNormReal e.1 := by linarith
    obtain ⟨hφ, hdφ⟩ := hpol hw0
    refine ⟨φ, fun _ => 0, hφ, fun e => ?_⟩
    have hkilled : ∀ e, HasSum (fun c => hl e c * (fineLinearPotential L c + latticeGradient φ c)) 0 := by
      intro e
      have s := ((hlin e).mul_left ((L : ℝ)⁻¹ ^ 2)).add (hgrad φ hφ e)
      simp only [mul_zero, add_zero] at s
      have heq : (fun c => hl e c * (fineLinearPotential L c + latticeGradient φ c)) =
          fun c => (L : ℝ)⁻¹ ^ 2 * (hl e c * (((c.1 0 : ℤ) : ℝ) * constantOneForm secondAxis c)) +
            hl e c * latticeGradient φ c := by
        funext c
        unfold fineLinearPotential
        ring
      rw [heq]
      exact s
    have key := hkill _ (hasPolynomialGrowth_add hw0 hdφ) hoff hkilled e
    have hmean : ∀ c, latticeContourAverage L (fun e => fineLinearPotential L e + latticeGradient φ e) c =
        ((c.1 0 : ℤ) : ℝ) * constantOneForm secondAxis c := fun c => by
      rw [latticeContourAverage_add, hml, hm0, add_zero]
    have main2 : HasSum (fun c : LatticeBond => latticeResponseOfInverse a L Gl e c * ((c.1 0 : ℤ) : ℝ) *
        constantOneForm secondAxis c) (fineLinearPotential L e + latticeGradient φ e) := by
      simpa only [hmean, mul_assoc] using key
    simpa [fineLinearPotential] using main2
end RunningCouplingSlope
end YangMills.Construction
end
