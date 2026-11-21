import YangMills.Construction.LawByMomentsOfTheFlow.FormAgainstTwoDecayingForms
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheParts
import YangMills.Construction.SummableBoundsOfTheFlow.BondsBelowATorus
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps TwoLevelMixtures BondSums
namespace TwoDecayingFormsBound
private theorem supDist_le_supportDiam {n : ℕ} {k : ℕ} (y : TorusSite n) (b : Fin k → TorusBond n) (l : Fin k) :
    TorusFields.supDist y (b l).1 ≤ supportDiam y b :=
  (Finset.le_sup (f := fun l : Fin k => TorusFields.supDist y (b l).1) (Finset.mem_univ l)).trans (le_max_left _ _)
private theorem inv_weight_le_exp (ℓ : StepParameters) (_hr : 0 < ℓ.rt) (D : ℕ) :
    (ℓ.weight D)⁻¹ ≤ Real.exp (-(ℓ.weightRate * D)) := by
  rw [Real.exp_neg]
  refine inv_anti₀ (Real.exp_pos _) ?_
  unfold StepParameters.weight
  exact le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _)
variable {n : ℕ} [NeZero n]
private theorem six_mul_bondSiteDist_le (ℓ : StepParameters) (hL : 6 ≤ ℓ.side) {Y : TorusSite n}
    {y : TorusSite (n * ℓ.side)} (hy : parentBlock ℓ.side y = Y)
    (b : TorusBond (n * ℓ.side)) {D : ℕ} (hD : TorusFields.supDist y b.1 ≤ D) : 6 * (bondSiteDist ℓ.side b Y : ℝ) ≤ D + 6 := by
  have h₁ : bondSiteDist ℓ.side b Y ≤ TorusFields.supDist b.1 y / ℓ.side + 1 := by
    unfold bondSiteDist
    rw [← hy]
    exact TorusBalls.supDist_parentBlock_le_div_add_one ℓ.side b.1 y
  rw [supDist_comm] at h₁
  have h₂ : TorusFields.supDist y b.1 / ℓ.side ≤ D / 6 :=
    (Nat.div_le_div_right hD).trans (Nat.div_le_div_left hL (by norm_num))
  have h₄ : 6 * bondSiteDist ℓ.side b Y ≤ D + 6 := by omega
  exact_mod_cast h₄
private theorem tripleDiam_le_sum_bondSiteDist (L : ℕ) [NeZero L] (Y : TorusSite n) (c c' : TorusBond n)
    (b b' : TorusBond (n * L)) :
    tripleDiam Y c c' ≤ bondSiteDist L b Y + bondSiteDist L b' Y + bondSiteDist L b c.1 + bondSiteDist L b' c'.1 := by
  have t₁ : TorusFields.supDist Y c.1 ≤ bondSiteDist L b Y + bondSiteDist L b c.1 := by
    unfold bondSiteDist
    rw [supDist_comm (parentBlock L b.1) Y]
    exact supDist_triangle _ _ _
  have t₂ : TorusFields.supDist Y c'.1 ≤ bondSiteDist L b' Y + bondSiteDist L b' c'.1 := by
    unfold bondSiteDist
    rw [supDist_comm (parentBlock L b'.1) Y]
    exact supDist_triangle _ _ _
  have t₃ : TorusFields.supDist c.1 c'.1 ≤
      bondSiteDist L b Y + bondSiteDist L b' Y + bondSiteDist L b c.1 + bondSiteDist L b' c'.1 := by
    have h₁ : TorusFields.supDist c.1 c'.1 ≤ TorusFields.supDist c.1 Y + TorusFields.supDist Y c'.1 := supDist_triangle _ _ _
    rw [supDist_comm c.1 Y] at h₁
    omega
  unfold tripleDiam supportDiam
  refine max_le (Finset.sup_le fun l _ => ?_) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  · fin_cases l
    · show TorusFields.supDist Y c.1 ≤ _
      omega
    · show TorusFields.supDist Y c'.1 ≤ _
      omega
  · fin_cases l <;> fin_cases l'
    · show TorusFields.supDist c.1 c.1 ≤ _
      rw [supDist_self]
      omega
    · exact t₃
    · show TorusFields.supDist c'.1 c.1 ≤ _
      rw [supDist_comm]
      exact t₃
    · show TorusFields.supDist c'.1 c'.1 ≤ _
      rw [supDist_self]
      omega
private theorem card_sitesInBlocks_le (L : ℕ) [NeZero L] (Y : TorusSite n) :
    ((sitesInBlocks L {Y}).card : ℝ) ≤ bondDecaySum L 1 := by
  classical
  have h₁ : ∀ y ∈ sitesInBlocks L {Y},
      Real.exp (-(1 * (bondSiteDist L ((y, 0) : TorusBond (n * L)) Y : ℝ))) = 1 := by
    intro y hy
    have h₂ : parentBlock L y = Y := by simpa [sitesInBlocks] using hy
    have h₃ : bondSiteDist L ((y, 0) : TorusBond (n * L)) Y = 0 := by
      unfold bondSiteDist
      rw [h₂, supDist_self]
    rw [h₃]
    simp
  have e : ((sitesInBlocks L {Y}).card : ℝ) =
      ∑ y ∈ sitesInBlocks L {Y}, Real.exp (-(1 * (bondSiteDist L ((y, 0) : TorusBond (n * L)) Y : ℝ))) := by
    rw [Finset.sum_congr rfl h₁]
    simp
  rw [e]
  have e₂ : ∑ y ∈ sitesInBlocks L {Y}, Real.exp (-(1 * (bondSiteDist L ((y, 0) : TorusBond (n * L)) Y : ℝ))) =
      ∑ b ∈ (sitesInBlocks L {Y}).image (fun y => ((y, 0) : TorusBond (n * L))),
        Real.exp (-(1 * (bondSiteDist L b Y : ℝ))) := by
    rw [Finset.sum_image]
    intro x _ x' _ h
    exact congrArg Prod.fst h
  rw [e₂]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le) ?_
  exact sum_exp_neg_bondSiteDist_le L one_pos n Y
end TwoDecayingFormsBound
open TwoDecayingFormsBound in
theorem twoDecayingFormsSumStatement_holds : twoDecayingFormsSumStatement := by
  intro ℓ hrt hn₁ hodd hL
  have hδ : 0 < ℓ.weightRate := by
    unfold StepParameters.weightRate
    positivity
  have hL6 : 6 ≤ ℓ.side := by omega
  set δ := ℓ.weightRate with hδd
  set Bs := bondDecaySum ℓ.side δ with hBs
  have hBs0 : 0 ≤ Bs := bondDecaySum_nonneg _ _
  have hK0 : 0 ≤ bondDecaySum ℓ.side 1 := bondDecaySum_nonneg _ _
  have hG0 := ResponseInTheExpansion.TermCalculus.weightGrowthSup_nonneg ℓ.rt ℓ.n₁
  refine ⟨bondDecaySum ℓ.side 1 * (Real.exp (6 * δ) * Bs ^ 2) * weightGrowthSup ℓ.rt ℓ.n₁,
    mul_nonneg (mul_nonneg hK0 (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))) hG0, ?_⟩
  intro n _ Y c c' e a a' q R R' he ha ha' hq hR hR'
  set G := ℓ.weight (tripleDiam Y c c') with hG
  set E₀ : ℝ := Real.exp (-(2 * δ * (tripleDiam Y c c' : ℝ))) with hE₀
  have hterm : ∀ y ∈ sitesInBlocks ℓ.side {Y}, ∀ b b' : TorusBond (n * ℓ.side), |R b * q y b b' * R' b'| ≤
      (e * a * a' * Real.exp (6 * δ) * E₀) *
        (Real.exp (-(δ * (bondSiteDist ℓ.side b Y : ℝ))) * Real.exp (-(δ * (bondSiteDist ℓ.side b' Y : ℝ)))) := by
    intro y hy b b'
    have hyb : parentBlock ℓ.side y = Y := by simpa [sitesInBlocks] using hy
    have hq₁ := hq y hy b b'
    set D := tripleDiam y b b' with hD
    have hq₂ : |q y b b'| ≤ e * Real.exp (-(δ * (D : ℝ))) := by
      refine hq₁.trans ?_
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_weight_le_exp ℓ hrt D) he
    have d₁ := six_mul_bondSiteDist_le ℓ hL6 hyb b (D := D) (supDist_le_supportDiam y ![b, b'] 0)
    have d₂ := six_mul_bondSiteDist_le ℓ hL6 hyb b' (D := D) (supDist_le_supportDiam y ![b, b'] 1)
    have hn : (tripleDiam Y c c' : ℝ) ≤ bondSiteDist ℓ.side b Y + bondSiteDist ℓ.side b' Y +
        bondSiteDist ℓ.side b c.1 + bondSiteDist ℓ.side b' c'.1 := by
      exact_mod_cast tripleDiam_le_sum_bondSiteDist ℓ.side Y c c' b b'
    have h₁ := hR b
    have h₂ := hR' b'
    rw [abs_mul, abs_mul]
    have h₃ : |R b| * |q y b b'| * |R' b'| ≤
        (a * Real.exp (-(2 * δ * (bondSiteDist ℓ.side b c.1 : ℝ)))) * (e * Real.exp (-(δ * (D : ℝ)))) *
        (a' * Real.exp (-(2 * δ * (bondSiteDist ℓ.side b' c'.1 : ℝ)))) :=
      mul_le_mul (mul_le_mul h₁ hq₂ (abs_nonneg _) (by positivity)) h₂ (abs_nonneg _) (by positivity)
    have hk : Real.exp (-(2 * δ * (bondSiteDist ℓ.side b c.1 : ℝ))) * Real.exp (-(δ * (D : ℝ))) *
          Real.exp (-(2 * δ * (bondSiteDist ℓ.side b' c'.1 : ℝ))) ≤
        Real.exp (6 * δ) * E₀ *
          (Real.exp (-(δ * (bondSiteDist ℓ.side b Y : ℝ))) * Real.exp (-(δ * (bondSiteDist ℓ.side b' Y : ℝ)))) := by
      rw [hE₀, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have m₁ := mul_le_mul_of_nonneg_left d₁ hδ.le
      have m₂ := mul_le_mul_of_nonneg_left d₂ hδ.le
      have m₃ := mul_le_mul_of_nonneg_left hn hδ.le
      nlinarith
    have hnn : 0 ≤ e * a * a' := by positivity
    calc _ ≤ _ := h₃
      _ = (e * a * a') * (Real.exp (-(2 * δ * (bondSiteDist ℓ.side b c.1 : ℝ))) * Real.exp (-(δ * (D : ℝ))) *
            Real.exp (-(2 * δ * (bondSiteDist ℓ.side b' c'.1 : ℝ)))) := by ring
      _ ≤ (e * a * a') * (Real.exp (6 * δ) * E₀ *
            (Real.exp (-(δ * (bondSiteDist ℓ.side b Y : ℝ))) * Real.exp (-(δ * (bondSiteDist ℓ.side b' Y : ℝ))))) :=
          mul_le_mul_of_nonneg_left hk hnn
      _ = _ := by ring
  set K₀ := e * a * a' * Real.exp (6 * δ) * E₀ with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hsum : ∑ b : TorusBond (n * ℓ.side), Real.exp (-(δ * (bondSiteDist ℓ.side b Y : ℝ))) ≤ Bs :=
    sum_exp_neg_bondSiteDist_le ℓ.side hδ n Y
  have hsum0 : 0 ≤ ∑ b : TorusBond (n * ℓ.side), Real.exp (-(δ * (bondSiteDist ℓ.side b Y : ℝ))) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hform : ∀ y ∈ sitesInBlocks ℓ.side {Y}, |bilinearEval (q y) R R'| ≤ K₀ * Bs ^ 2 := by
    intro y hy
    unfold bilinearEval
    calc _ ≤ ∑ b : TorusBond (n * ℓ.side), |∑ b' : TorusBond (n * ℓ.side), R b * q y b b' * R' b'| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b : TorusBond (n * ℓ.side), ∑ b' : TorusBond (n * ℓ.side), |R b * q y b b' * R' b'| :=
          Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b : TorusBond (n * ℓ.side), ∑ b' : TorusBond (n * ℓ.side),
            K₀ * (Real.exp (-(δ * (bondSiteDist ℓ.side b Y : ℝ))) * Real.exp (-(δ * (bondSiteDist ℓ.side b' Y : ℝ)))) :=
          Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => hterm y hy b b'
      _ = K₀ * ((∑ b : TorusBond (n * ℓ.side), Real.exp (-(δ * (bondSiteDist ℓ.side b Y : ℝ)))) *
            ∑ b : TorusBond (n * ℓ.side), Real.exp (-(δ * (bondSiteDist ℓ.side b Y : ℝ)))) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
      _ ≤ K₀ * Bs ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hK₀0
          rw [sq]
          exact mul_le_mul hsum hsum hsum0 hBs0
  have hE : E₀ ≤ weightGrowthSup ℓ.rt ℓ.n₁ / G := by
    have h₁ := ResponseInTheExpansion.TermCalculus.exp_le_weightGrowthSup_div ℓ hrt hn₁ (tripleDiam Y c c')
      (2 * (ℓ.rt / 2 ^ 10)) le_rfl
    exact h₁
  calc _ ≤ ∑ _y ∈ sitesInBlocks ℓ.side {Y}, K₀ * Bs ^ 2 := Finset.sum_le_sum hform
    _ = ((sitesInBlocks ℓ.side {Y}).card : ℝ) * (K₀ * Bs ^ 2) := by simp
    _ ≤ bondDecaySum ℓ.side 1 * (K₀ * Bs ^ 2) :=
        mul_le_mul_of_nonneg_right (card_sitesInBlocks_le ℓ.side Y) (by positivity)
    _ = bondDecaySum ℓ.side 1 * (Real.exp (6 * δ) * Bs ^ 2) * (e * a * a') * E₀ := by
        rw [hK₀]
        ring
    _ ≤ bondDecaySum ℓ.side 1 * (Real.exp (6 * δ) * Bs ^ 2) * (e * a * a') * (weightGrowthSup ℓ.rt ℓ.n₁ / G) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = _ := by ring
end YangMills.Construction.MomentLaw
end
