import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormAtTheLeastFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.TorusLumps YangMills.Construction.TorusFields Filter Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
private theorem eventually_large_index (γ₀ : ℝ) (hγ₀ : 0 < γ₀) (n₁ : ℕ) :
    ∀ᶠ n : ℕ in atTop, n₁ ≤ n ∧ 2 ≤ n ∧ 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 < γ₀ ∧
      2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 ≤ 1 ∧
      4 * Real.log (1 / (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2)) ^ 2 + 4 < (n : ℝ) := by apply _root_.YangMills.SharedProofs.p36503 <;> assumption
private theorem constantPlaneCurvature_eq_curvatureAlong (X : imaginaryQuaternions) (μ ν : Fin 4) :
    constantPlaneCurvature X μ ν = curvatureAlong X (planeUnitForm μ ν) := by apply _root_.YangMills.SharedProofs.p53264 <;> assumption
private theorem planeUnitForm_antisymm (μ ν : Fin 4) (hμν : μ < ν) (i j : Fin 4) :
    planeUnitForm μ ν i j = - planeUnitForm μ ν j i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.planeUnitForm_antisymm <;> assumption
private theorem hasPolynomialGrowth_of_isLinearPotential {Fm : Fin 4 → Fin 4 → imaginaryQuaternions}
    {B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions}
    (hB : IsLinearPotential Fm B) : HasPolynomialGrowth B := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.hasPolynomialGrowth_of_linearPotential <;> assumption
theorem flatLimit_of_expansion (hsec : SecondOrderOnMultiplesOfSide)
    (htop : ConstantCurvatureTopOnTorus) (hread : TopFamilyOnTori) :
    FlatLimitFromExpansion := by
  intro ℓ t C e g hfits he hcf hexp
  set h := densityOfTopFamily ℓ.side t g with hh
  obtain ⟨hlim, _, _, hsum, _, _, hwide, _⟩ := hsec ℓ hfits 1 one_pos C h hcf
  have hflat := (hread ℓ.side t 1 0 g one_pos).2.2.2.2
  refine ⟨secondDerivLimitOnMultiples 1 h, ?_, ?_⟩
  · intro b b' X X'
    have h1 := hlim b b' X X'
    simp only [one_mul] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : NeZero n := ⟨hn.ne'⟩
    show flatSecondDeriv h n b b' X X' = secondDerivAtUniform g ℓ.side t n b b' X X'
    exact (hflat n b b' X X').symm
  · intro X μ ν B hX hμν hB
    have hB' : IsLinearPotential (curvatureAlong X (planeUnitForm μ ν)) B := by
      rw [← constantPlaneCurvature_eq_curvatureAlong]; exact hB
    have hg := hasPolynomialGrowth_of_isLinearPotential hB
    have hS := hsum B B hg hg
    refine ⟨_, hS.hasSum, ?_⟩
    set v := ∑' cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4),
      secondDerivLimitOnMultiples 1 h cc.1 cc.2 (B cc.1) (B cc.2) with hv
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨γ₀, hγ₀, hw⟩ := hwide (planeUnitForm μ ν) (planeUnitForm_antisymm μ ν hμν) (ε / 8) (by positivity)
    obtain ⟨n₁, hn₁⟩ := hexp X μ ν hX hμν (ε / 8) (by positivity)
    obtain ⟨n, hn1, hn2, hγ1, hγ2, hroom⟩ := (eventually_large_index γ₀ hγ₀ n₁).exists
    have : NeZero n := ⟨by omega⟩
    set γ : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 with hγ
    have hγpos : 0 < γ := by
      rw [hγ]
      have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      simp only [Nat.cast_one, mul_one]
      positivity
    have hodd : Odd (torusFrame ℓ.side t n).blockSide := hfits.L_odd
    have hab := htop (torusFrame ℓ.side t n) X μ ν n 1 hodd (fun _ => rfl) (by omega) hX hμν hγ2
    have h1 := hw γ hγpos hγ1 n (one_dvd n) hroom X (constantCurvatureTop ℓ.side t n X μ ν) B hX hab hB' 0
    have h2 := hn₁ n hn1
    have hγ2pos : 0 < γ ^ 2 := by positivity
    have h3 : γ ^ 2 / 2 * |v| ≤ (e / 2 + ε / 8) * γ ^ 2 + ε / 8 * γ ^ 2 := by
      generalize centered h n 0 (constantCurvatureTop ℓ.side t n X μ ν) = H at h1 h2
      have h2' : |H| ≤ (e / 2 + ε / 8) * γ ^ 2 := h2
      have h4 : |γ ^ 2 / 2 * v| ≤ |H - γ ^ 2 / 2 * v| + |H| := by
        have := abs_sub_abs_le_abs_sub (γ ^ 2 / 2 * v) H
        rw [abs_sub_comm (γ ^ 2 / 2 * v) H] at this
        linarith
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ γ ^ 2 / 2)] at h4
      linarith
    have h5 : |v| ≤ e + ε / 2 := by
      have : γ ^ 2 * |v| ≤ γ ^ 2 * (e + ε / 2) := by nlinarith
      exact le_of_mul_le_mul_left this hγ2pos
    linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
