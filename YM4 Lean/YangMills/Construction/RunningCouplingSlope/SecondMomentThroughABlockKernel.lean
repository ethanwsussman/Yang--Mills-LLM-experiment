import YangMills.Construction.RunningCouplingSlope.BlockMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps
namespace SlopeCoefficient
def latticeUnitVector (ν : Fin 4) : Fin 4 → ℤ := Pi.single ν 1
def latticeBondSum (g : LatticeBond → ℝ) : ℝ := ∑ ν, ∑' z, g (z, ν)
def reflectBond (c : LatticeBond) : LatticeBond := (-c.1 - latticeUnitVector c.2, c.2)
structure IsLatticeHessianKernel (K : LatticeBond → LatticeBond → ℝ) : Prop where
  exp_decay : ∃ M θ : ℝ, 0 < θ ∧ ∀ c c', |K c c'| ≤ M * Real.exp (-(θ * offsetNormReal (c'.1 - c.1)))
  symm : ∀ c c', K c c' = K c' c
  translation_invariant : ∀ (u : Fin 4 → ℤ) (c c' : LatticeBond),
    K (c.1 + u, c.2) (c'.1 + u, c'.2) = K c c'
  divergence_zero : ∀ (c : LatticeBond) (x : Fin 4 → ℤ),
    ∑ ν, (K c (x - latticeUnitVector ν, ν) - K c (x, ν)) = 0
  reflect_invariant : ∀ c c', K (reflectBond c) (reflectBond c') = K c c'
structure IsLatticeBlockKernel (L : ℕ) (Pl : LatticeBond → LatticeBond → ℝ) : Prop where
  exp_decay : ∃ M θ : ℝ, 0 < θ ∧ ∀ b c,
    |Pl b c| ≤ M * Real.exp (-(θ * offsetNormReal (b.1 - (L : ℤ) • c.1)))
  translation_invariant : ∀ (u : Fin 4 → ℤ) (b c : LatticeBond),
    Pl (b.1 + (L : ℤ) • u, b.2) (c.1 + u, c.2) = Pl b c
  constant_form : ∃ f : (Fin 4 → ℤ) → ℝ, (∃ C, ∀ z, |f z| ≤ C) ∧ ∀ b : LatticeBond,
    HasSum (fun c => Pl b c * constantOneForm secondAxis c)
      ((L : ℝ)⁻¹ * constantOneForm secondAxis b + latticeGradient f b)
  linear_potential : ∃ (f : (Fin 4 → ℤ) → ℝ) (κ : Fin 4 → ℝ), HasPolynomialGrowth f ∧ ∀ b : LatticeBond,
    HasSum (fun c : LatticeBond => Pl b c * ((c.1 0 : ℤ) : ℝ) * constantOneForm secondAxis c)
      ((L : ℝ)⁻¹ ^ 2 * ((b.1 0 : ℤ) : ℝ) * constantOneForm secondAxis b + κ b.2 + latticeGradient f b)
def kernelPullback (Pl K : LatticeBond → LatticeBond → ℝ) (c c' : LatticeBond) : ℝ :=
  latticeBondSum fun b => Pl b c * latticeBondSum fun b' => K b b' * Pl b' c'
def latticeSecondMoment (K : LatticeBond → LatticeBond → ℝ) : ℝ :=
  ∑' z : Fin 4 → ℤ, K (0, secondAxis) (z, secondAxis) * ((z 0 : ℤ) : ℝ) ^ 2
def SecondMomentPullbackInvariant : Prop :=
  ∀ (L : ℕ) (K Pl : LatticeBond → LatticeBond → ℝ), 0 < L → IsLatticeHessianKernel K →
    IsLatticeBlockKernel L Pl → latticeSecondMoment (kernelPullback Pl K) = latticeSecondMoment K
end SlopeCoefficient
end YangMills.Construction
end
