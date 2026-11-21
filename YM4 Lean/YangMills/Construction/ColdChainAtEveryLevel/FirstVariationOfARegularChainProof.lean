import YangMills.Construction.ColdChainAtEveryLevel.FirstVariationOfARegularChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
theorem regularChainFirstVariation : regularChainFirstVariationStatement := by
  intro F a S R U W hodd hreg
  open ChartCoordinates in
  have hreg' : ChartIsRegular S R (chartOfValues S U (chartValues S U)) := by rwa [chartOfValues_chartValues]
  open ChartCoordinates in
  have hd : DifferentiableAt ℝ (fun e : ChartValues S => chartAction a S R (chartOfValues S U e) W)
      (chartValues S U) :=
    differentiableAt_chartAction hodd a R W (fun b hb => differentiableAt_chartOfValues_fine U _ hb)
      (fun j hj b hb => differentiableAt_chartOfValues_coarse U _ hj hb) hreg'
  open ChartCoordinates in
  refine ⟨fun A => fderiv ℝ (fun e : ChartValues S => chartAction a S R (chartOfValues S U e) W)
    (chartValues S U) (chartValues S A), ?_, ?_, ?_⟩
  · intro A A'
    open ChartCoordinates in
    have : chartValues S (chartSum A A') = chartValues S A + chartValues S A' := by
      refine Prod.ext ?_ ?_
      · funext b
        simp [chartValues, chartSum, chartMove]
      · funext j b
        simp [chartValues, chartSum, chartMove]
    show fderiv ℝ _ _ _ = _
    rw [this, map_add]
  · intro t A
    open ChartCoordinates in
    have : chartValues S (chartMove ⟨fun _ _ => 0, fun _ _ _ => 0⟩ A t) = t • chartValues S A := by
      refine Prod.ext ?_ ?_
      · funext b
        simp [chartValues, chartMove]
      · funext j b
        simp [chartValues, chartMove]
    show fderiv ℝ _ _ _ = _
    rw [this, map_smul, smul_eq_mul]
  · intro C A ⟨h0, hu, hmu⟩
    open ChartCoordinates in
    have hcurve : HasDerivAt (fun τ => chartValues S (C τ)) (chartValues S A) 0 := by
      refine HasDerivAt.prodMk ?_ ?_
      · exact hasDerivAt_pi.2 fun b => hu b.1 b.2
      · refine hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun b => ?_
        have hj : j.val + 1 < F.top := by
          have hn : F.top = F.depth + 1 := rfl
          have := j.2
          omega
        exact hmu j.val hj b.1 b.2
    open ChartCoordinates in
    have e0 : chartValues S (C 0) = chartValues S U := chartValues_congr h0
    open ChartCoordinates in
    have hcomp := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (f := fun τ => chartValues S (C τ))
      (l := fun e : ChartValues S => chartAction a S R (chartOfValues S U e) W) (by
        rw [e0]; exact hd.hasFDerivAt) hcurve
    open ChartCoordinates in
    have e1 : (fun τ => chartAction a S R (C τ) W) =
        (fun e : ChartValues S => chartAction a S R (chartOfValues S U e) W) ∘ fun τ => chartValues S (C τ) := by
      funext τ
      exact (chartAction_congr hodd a R W (chartOfValues_agreeOn U (C τ))).symm
    rw [e1]
    exact hcomp
end YangMills.Construction.BlockAverages
end
