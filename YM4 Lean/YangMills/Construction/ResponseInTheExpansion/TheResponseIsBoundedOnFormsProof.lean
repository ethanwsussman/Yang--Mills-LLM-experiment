import YangMills.Construction.ResponseInTheExpansion.ALocalFunctionIsQuadraticInTheCurvatureProof
import YangMills.Construction.ResponseInTheExpansion.TheResponseContractsCurvatureLocallyProof
import YangMills.Construction.ResponseInTheExpansion.TheResponseIsBoundedOnForms
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusFrame StepCosts TopLevelSites TorusChain TorusLumps
namespace ResponseExpansionBounds
private def expLineSum (κ : ℝ) : ℝ := ∑' k : ℤ, Real.exp (-(κ * |(k : ℝ)|))
private theorem sum_zmod_le_expLineSum (m : ℕ) [NeZero m] {κ : ℝ} (hκ : 0 < κ) :
    ∑ x : ZMod m, Real.exp (-(κ * |((x.valMinAbs : ℤ) : ℝ)|)) ≤ expLineSum κ := by apply _root_.YangMills.DeltaSharedProofs.p502213 <;> assumption
private theorem exp_supDist_le_prod {m : ℕ} {κ : ℝ} (hκ : 0 < κ) (x y : TorusSite m) :
    Real.exp (-(κ * (supDist x y : ℝ))) ≤
      ∏ i, Real.exp (-(κ / 4 * |(((x i - y i).valMinAbs : ℤ) : ℝ)|)) := by apply _root_.YangMills.SharedProofs.p58634 <;> assumption
private theorem sum_sites_exp_le {m : ℕ} [NeZero m] {κ : ℝ} (hκ : 0 < κ) (x : TorusSite m) :
    ∑ y : TorusSite m, Real.exp (-(κ * (supDist x y : ℝ))) ≤ expLineSum (κ / 4) ^ 4 := by apply _root_.YangMills.DeltaSharedProofs.p501803 <;> assumption
private theorem sum_bonds_exp_le {m : ℕ} [NeZero m] {κ : ℝ} (hκ : 0 < κ) (x : TorusSite m) :
    ∑ c : TorusBond m, Real.exp (-(κ * (supDist x c.1 : ℝ))) ≤ 4 * expLineSum (κ / 4) ^ 4 := by apply _root_.YangMills.DeltaSharedProofs.p3109 <;> assumption
open ColdChain ColdStepAtMirrorFrames BlockAverages WeightedResponses
section Chain
variable {L u m : ℕ} [NeZero L] [NeZero m]
variable {a ρ δ lam σA cg : ℝ} {N : ℕ → ℝ} {L : ℕ}
private theorem abs_responseKernel_le [NeZero L] (hc : ColdChainConstants a δ L lam ρ σA cg N) {u m : ℕ}
    [NeZero m] (hm : 64 ≤ m) (b : TorusBond (m * L)) (c : TorusBond m) :
    |responseKernel a ρ L u b c| ≤ (N 1 + 1) * Real.exp (-δ * (supDist (parentBlock L b.1) c.1 : ℝ)) := by apply _root_.YangMills.SharedProofs.p72842 <;> assumption
private theorem responseKernel_rowSum_bounded [NeZero L] (hc : ColdChainConstants a δ L lam ρ σA cg N) :
    ∃ C : ℝ, ∀ (u m : ℕ) [NeZero m], 64 ≤ m → ∀ b : TorusBond (m * L),
      ∑ c : TorusBond m, |responseKernel a ρ L u b c| ≤ C := by
  have hδ : 0 < δ := hc.1
  have hN : 0 < N 1 := hc.2.2.2.2.2.2.2.1 1
  refine ⟨(N 1 + 1) * (4 * expLineSum (δ / 4) ^ 4), fun u m _ hm b => ?_⟩
  calc ∑ c : TorusBond m, |responseKernel a ρ L u b c|
      ≤ ∑ c : TorusBond m, (N 1 + 1) * Real.exp (-(δ * (supDist (parentBlock L b.1) c.1 : ℝ))) :=
        Finset.sum_le_sum fun c _ => by
          have h := abs_responseKernel_le (a := a) (ρ := ρ) hc (u := u) hm b c
          rwa [neg_mul] at h
    _ = (N 1 + 1) * ∑ c : TorusBond m, Real.exp (-(δ * (supDist (parentBlock L b.1) c.1 : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ (N 1 + 1) * (4 * expLineSum (δ / 4) ^ 4) :=
        mul_le_mul_of_nonneg_left (sum_bonds_exp_le hδ _) (by positivity)
end Chain
end ResponseExpansionBounds
theorem responseKernelRowSumBounded : responseKernelRowSumBoundedStatement := by
  intro a ha
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L _ _ T _ _ hD _ _ _ _ => ⟨0, fun y _ _ _ => ?_⟩⟩
  exact ResponseExpansionBounds.responseKernel_rowSum_bounded (L := (T.stepParameters y).side) hD.chain
end YangMills.Construction.ResponseInTheExpansion
end
