import YangMills.Construction.Analysis.EuclideanNormsConesAndSummableFamilies
import YangMills.Construction.EuclideanFunctionals.CombinationsOfTuplesComplexComponentsAndConvergenceInC1
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open Filter Topology
namespace SharpNormC1
def gradSup (f : R4 → ℂ) : ℝ :=
  ⨆ x, Real.sqrt (∑ μ, ‖YangMills.Construction.TestFunctions.partialDerivR4 μ f x‖ ^ 2)
def BoundedAndLipschitz : Prop :=
  ∀ f ∈ C1c ℂ,
    YangMills.Construction.TestFunctions.IsBoundedFun f ∧
    (∀ μ : Fin 4, YangMills.Construction.TestFunctions.IsBoundedFun
      (YangMills.Construction.TestFunctions.partialDerivR4 μ f)) ∧
    ∀ x y : R4, ‖f x - f y‖ ≤ gradSup f * YangMills.Construction.Euclidean.euclidNorm (x - y)
def SharpLeGrad (c : SharpScale) : Prop :=
  ∀ f ∈ C1c ℂ,
    YangMills.Construction.TestFunctions.lipConstR4 f ≤ gradSup f ∧
    c.sharpNorm f ≤ max (YangMills.Construction.TestFunctions.uniformNorm f) (40 * c.M * gradSup f)
def ReImParts (c : SharpScale) : Prop :=
  ∀ f ∈ C1c ℂ,
    (fun x => (f x).re) ∈ C1c ℝ ∧
    (fun x => (f x).im) ∈ C1c ℝ ∧
    supp (fun x => (f x).re) ∪ supp (fun x => (f x).im) ⊆ supp f ∧
    c.sharpNorm (fun x => (f x).re) ≤ c.sharpNorm f ∧
    c.sharpNorm (fun x => (f x).im) ≤ c.sharpNorm f
def SharpTendstoOfC1 (c : SharpScale) : Prop :=
  ∀ (fs : ℕ → R4 → ℂ) (f : R4 → ℂ), (∀ j, 1 ≤ j → fs j ∈ C1c ℂ) →
    f ∈ C1c ℂ → TendstoC1 fs f →
    Tendsto (fun j => c.sharpNorm (fs j - f)) atTop (𝓝 0)
def TranslContinuous (c : SharpScale) : Prop :=
  ∀ f ∈ C1c ℂ, ∀ z₀ : R4,
    Tendsto
      (fun z : R4 =>
        c.sharpNorm ((EuclidMotion.transl z).actFn f -
          (EuclidMotion.transl z₀).actFn f))
      (𝓝 z₀) (𝓝 0)
def Main : Prop :=
  BoundedAndLipschitz ∧
    ∀ c : SharpScale, SharpLeGrad c ∧ ReImParts c ∧
      SharpTendstoOfC1 c ∧ TranslContinuous c
end SharpNormC1
end YangMills.Construction.EuclideanFunctionals
