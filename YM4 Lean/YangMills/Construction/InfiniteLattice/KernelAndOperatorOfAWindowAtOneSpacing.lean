import YangMills.Construction.InfiniteLattice.LatticeOfACutoffAndTheVariablesOfASetOfBonds
import YangMills.Construction.InfiniteLattice.WindowsKernelOperatorAndDensitiesAtOneSpacing
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicExtensions
def WindowKernelOperatorProperties : Prop :=
  ∀ (c : CutoffLinks.CutoffData) (W : LinkWindow c.spacing),
    ((∀ ξ : LinkVariables W.rim,
        ∫ V, W.rimKernel c.spacing_pos c.coupling V ξ ∂W.haarProd = 1) ∧
      (W.links = ∅ →
        W.faceCount = 0 ∧ W.rim = ∅ ∧
          (∀ (V : W.Assignments) (ξ : LinkVariables W.rim),
            W.rimKernel c.spacing_pos c.coupling V ξ = 1) ∧
          ∀ G : GaugeField c.spacing → ℝ, Measurable G → TestFunctions.IsBoundedFun G →
            W.realOperator c.spacing_pos c.coupling G = G)) ∧
    (∀ G : GaugeField c.spacing → ℝ, Measurable G → TestFunctions.IsBoundedFun G →
      Measurable (W.realOperator c.spacing_pos c.coupling G) ∧
        TestFunctions.IsBoundedFun (W.realOperator c.spacing_pos c.coupling G) ∧
        TestFunctions.uniformNorm (W.realOperator c.spacing_pos c.coupling G) ≤
          TestFunctions.uniformNorm G ∧
        (Continuous G → Continuous (W.realOperator c.spacing_pos c.coupling G)) ∧
        ∀ S : Set (Link c.spacing), CutoffLattice.DependsOnlyOn G S →
          CutoffLattice.DependsOnlyOn (W.realOperator c.spacing_pos c.coupling G)
            ((S \ (W.links : Set (Link c.spacing))) ∪ W.rim)) ∧
    (∀ ρ : RealWeakState c.spacing,
      Measurable (W.stateDensity c.spacing_pos c.coupling ρ) ∧
        TestFunctions.IsBoundedFun (W.stateDensity c.spacing_pos c.coupling ρ) ∧
        ∀ G : W.Assignments → ℝ, Measurable G → TestFunctions.IsBoundedFun G →
          ρ.value (W.realOperator c.spacing_pos c.coupling fun U => G (W.restrictInside U)) =
            ∫ V, G V * W.stateDensity c.spacing_pos c.coupling ρ V ∂W.haarProd)
end YangMills.Construction.InfiniteLattice.PeriodicExtensions
