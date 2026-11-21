import YangMills.Construction.RunningCouplingSlope.LeastFieldIsABlockMap
import YangMills.Construction.RunningCouplingSlope.LeastFieldOverAFlatForm
import YangMills.Construction.RunningCouplingSlope.OneStepOfTheChainForms
import YangMills.Construction.RunningCouplingSlope.WilsonActionHasAChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.FlatLinearization
theorem minimizerIsBlockMap_of_flowKernel (hW : WilsonActionHasFlowKernel)
    (hS : FlatLinearizationStep) (hN : MinimizerOverFlatKernel) :
    MinimizerIsBlockMap := by
  intro a ha L hL t ρ h0 h1
  have tower : ∀ t : ℕ, ∃ h : BondKernel, IsFlowKernel h ∧
      ∀ᶠ m in Filter.atTop, HasHessianAtTrivial (minimalActionTotal a L t) (h m) := by
    intro t
    induction t with
    | zero => exact hW a ha L hL
    | succ t ih =>
      obtain ⟨h, hc, hf⟩ := ih
      obtain ⟨P, -, -, hr, hc'⟩ := hS a ha L hL h hc
      exact ⟨_, hc', (hN a ha L hL t h P hf hr).2⟩
  obtain ⟨h, hc, hf⟩ := tower t
  obtain ⟨P, Pl, hk, hr, -⟩ := hS a ha L hL h hc
  have hm := (hN a ha L hL t h P hf hr).1 ρ h0 h1
  refine ⟨P, Pl, ?_⟩
  exact
    { map_trivial := hm.mono fun n h => h.1
      contDiffAt_perturb := hm.mono fun n h => h.2.1
      hasDerivAt_perturb := hm.mono fun n h => h.2.2
      exp_decay := hk.decay
      translation_invariant := hk.translation_invariant
      tendsto_kernel := hk.tendsto
      constant_form := hk.constant_form
      linear_potential := hk.linear_potential }
end YangMills.Construction.RunningCouplingSlope
end
