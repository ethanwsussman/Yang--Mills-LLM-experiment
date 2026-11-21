import YangMills.Construction.Lattice.InfiniteLatticeCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open InfiniteLattice
variable {d : ℕ} {ξ : ℝ}
def gridLength (x : GridSite d ξ) : ℝ := l1Length (x : Fin d → ℝ)
def iteratedDiff (β : List (Fin d ⊕ Fin d)) (f : GridSite d ξ → ℝ) : GridSite d ξ → ℝ :=
  β.foldr (fun o g => Sum.elim (fun μ => forwardDiff μ g) (fun μ => backwardDiff μ g) o) f
def IsLaplacianInverse (C : GridSite d ξ → ℝ) : Prop :=
  ∀ v : GridSite d ξ → ℝ, (Function.support v).Finite →
    latticeConv C (InfiniteLattice.laplacian v) = v
def HasDiffDecay (c : ℝ) (C : GridSite d ξ → ℝ) : Prop :=
  ∀ β : List (Fin d ⊕ Fin d), β.length ≤ 3 → ∀ x : GridSite d ξ,
    |iteratedDiff β C x| ≤ c * (gridLength x + ξ) ^ (-((d : ℝ) - 2 + (β.length : ℝ)))
def BallSumBounds (d : ℕ) (ξ c : ℝ) : Prop :=
  ∀ s s' : ℝ, ξ ≤ s → s ≤ s' →
    (∀ p : ℕ, p = d - 2 ∨ p = d - 1 →
      ∑' z : GridSite d ξ, Set.indicator {z : GridSite d ξ | gridLength z ≤ s}
          (fun z => ξ ^ d * ((gridLength z + ξ) ^ p)⁻¹) z ≤ c * s ^ (d - p)) ∧
    ∑' z : GridSite d ξ, Set.indicator {z : GridSite d ξ | s < gridLength z ∧ gridLength z ≤ s'}
        (fun z => ξ ^ d * (gridLength z ^ d)⁻¹) z ≤ c * (1 + Real.log (s' / s))
def ConvBounds (d : ℕ) (ξ c : ℝ) (cHolder : ℝ → ℝ) : Prop :=
  ∀ k : GridSite d ξ → ℝ,
    (∀ z, |k z| ≤ (gridLength z + ξ) ^ (-((d : ℝ) - 1))) →
    (∀ z ν, |forwardDiff ν k z| ≤ (gridLength z + ξ) ^ (-(d : ℝ))) →
    ∀ r : ℝ, ξ ≤ r → ∀ x x' : GridSite d ξ, gridLength (x - x') ≤ d * r →
    ∀ G : GridSite d ξ → ℝ, (∀ z, 2 * d * r < gridLength (z - x) → G z = 0) →
      |latticeConv k G x| ≤ c * r * (supNorm G).toReal ∧
      ∀ α : ℝ, 0 < α → α < 1 →
        |latticeConv k G x - latticeConv k G x'| ≤
          cHolder α * r * (gridLength (x - x') / r) ^ α * (supNorm G).toReal
structure KernelData (d : ℕ) where
  const : ℝ
  holderConst : ℝ → ℝ
  kernel : ∀ ξ : ℝ, GridSite d ξ → ℝ
def KernelData.Satisfies (D : KernelData d) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    IsLaplacianInverse (D.kernel ξ) ∧
    HasDiffDecay D.const (D.kernel ξ) ∧
    BallSumBounds d ξ D.const ∧
    ConvBounds d ξ D.const D.holderConst
instance instNonemptyKernelData : Nonempty (KernelData d) := ⟨⟨0, fun _ => 0, fun _ _ => 0⟩⟩
def chosenKernelData (d : ℕ) : KernelData d := Classical.epsilon KernelData.Satisfies
def kernelConst (d : ℕ) : ℝ := (chosenKernelData d).const
def kernelHolderConst (d : ℕ) (α : ℝ) : ℝ := (chosenKernelData d).holderConst α
def greenKernel (d : ℕ) (ξ : ℝ) : GridSite d ξ → ℝ := (chosenKernelData d).kernel ξ
def GreenKernelBounds : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ ξ : ℝ, 0 < ξ →
    IsLaplacianInverse (greenKernel d ξ) ∧
    HasDiffDecay (kernelConst d) (greenKernel d ξ) ∧
    BallSumBounds d ξ (kernelConst d) ∧
    ConvBounds d ξ (kernelConst d) (kernelHolderConst d)
end YangMills.Construction.FreeKernel
