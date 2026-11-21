import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages TorusFields
namespace BondMoves
def imaginaryBasis : Fin 3 → imaginaryQuaternions :=
  ![⟨⟨0, 1, 0, 0⟩, rfl⟩, ⟨⟨0, 0, 1, 0⟩, rfl⟩, ⟨⟨0, 0, 0, 1⟩, rfl⟩]
variable {n : ℕ}
def repeatBondsThrice {k : ℕ} (c : Fin k → TorusBond n) : Fin (k * 3) → TorusBond n :=
  fun p => c (finProdFinEquiv.symm p).1
def basisAtEachBond (k : ℕ) : Fin (k * 3) → imaginaryQuaternions :=
  fun p => imaginaryBasis (finProdFinEquiv.symm p).2
def bondMoveLinear {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (β : TorusBond n) :
    (Fin k → ℝ) →L[ℝ] imaginaryQuaternions :=
  ∑ l, if c l = β then (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).smulRight (X l) else 0
theorem bondMoveLinear_apply {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (β : TorusBond n)
    (τ : Fin k → ℝ) :
    bondMoveLinear c X β τ = ∑ l, if c l = β then τ l • X l else 0 := by
  simp only [bondMoveLinear, ContinuousLinearMap.coe_sum', Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem norm_bondMoveLinear_le {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (β : TorusBond n) :
    ‖bondMoveLinear c X β‖ ≤ ∑ l, ‖X l‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun τ => ?_
  rw [bondMoveLinear_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  split_ifs
  · rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm τ l) (norm_nonneg _)
  · rw [norm_zero]
    positivity
theorem contDiff_exp_imaginary : ContDiff ℝ ⊤ fun w : imaginaryQuaternions => NormedSpace.exp (w : ℍ[ℝ]) := by
  have h : AnalyticOnNhd ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) Set.univ := fun x _ => NormedSpace.exp_analytic x
  exact h.contDiff.comp imaginaryQuaternions.subtypeL.contDiff
theorem norm_iteratedFDeriv_exp_comp_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ξ : E →L[ℝ] imaginaryQuaternions) {j : ℕ} {C : ℝ}
    (hC : ∀ v : imaginaryQuaternions,
      ‖iteratedFDeriv ℝ j (fun w : imaginaryQuaternions => NormedSpace.exp (w : ℍ[ℝ])) v‖ ≤ C) (τ : E) :
    ‖iteratedFDeriv ℝ j (fun σ => NormedSpace.exp ((Ξ σ : imaginaryQuaternions) : ℍ[ℝ])) τ‖ ≤ C * ‖Ξ‖ ^ j := by
  have h := Ξ.iteratedFDeriv_comp_right contDiff_exp_imaginary τ (i := j) (by exact_mod_cast le_top)
  have e : (fun σ => NormedSpace.exp ((Ξ σ : imaginaryQuaternions) : ℍ[ℝ])) =
      (fun w : imaginaryQuaternions => NormedSpace.exp (w : ℍ[ℝ])) ∘ Ξ := rfl
  rw [e, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (hC _) (by positivity)
theorem perturb_eq_expUnit_mul {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (W : TorusField n) (x : TorusSite n) (i : Fin 4) :
    perturb c X σ W x i = expUnit (bondMoveLinear c X (x, i) σ) * W x i := by
  rw [bondMoveLinear_apply]
  rfl
def PerturbLocallyReparametrized : Prop :=
  ∃ a : ℕ → ℝ, ∀ (n : ℕ) (V : TorusField n) (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (τ₀ : Fin k → ℝ),
    ∃ A : (Fin k → ℝ) → (Fin (k * 3) → ℝ), ContDiffAt ℝ 40 A τ₀ ∧ A τ₀ = 0 ∧
      (∀ᶠ τ in 𝓝 τ₀, perturb c X τ V =
        perturb (repeatBondsThrice c) (basisAtEachBond k) (A τ) (perturb c X τ₀ V)) ∧
      (k ≤ 3 → AreUnitVectors X → ∀ j, 1 ≤ j → j ≤ 40 → ‖iteratedFDeriv ℝ j A τ₀‖ ≤ a j)
end BondMoves
end YangMills.Construction
end
