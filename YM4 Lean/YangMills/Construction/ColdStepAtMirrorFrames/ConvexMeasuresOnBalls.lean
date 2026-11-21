import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
abbrev BondVector : Type := EuclideanSpace ℝ (Fin 3)
abbrev BondField (ι : Type) : Type := ι → BondVector
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def bondVariation (b : ι) (e : BondVector) : BondField ι := Pi.single b e
def bondPartialDeriv (f : BondField ι → ℝ) (b : ι) (η : BondField ι) (e : BondVector) : ℝ :=
  fderiv ℝ f η (bondVariation b e)
def bondGradNorm (f : BondField ι → ℝ) (b : ι) (η : BondField ι) : ℝ :=
  ‖(fderiv ℝ f η).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)‖
def secondDerivAlong (Ψ : BondField ι → ℝ) (η u v : BondField ι) : ℝ :=
  fderiv ℝ (fun ζ => fderiv ℝ Ψ ζ u) η v
def radialWeightProd (r : ℝ → ℝ) (η : BondField ι) : ℝ := ∏ b, r ‖η b‖
def ballDensity (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) (η : BondField ι) : ℝ :=
  radialWeightProd r η * Real.exp (- Ψ η)
def ballExpectation (r : ℝ → ℝ) (Ψ f : BondField ι → ℝ) : ℝ :=
  (∫ η, f η * ballDensity r Ψ η) / ∫ η, ballDensity r Ψ η
def ballCovariance (r : ℝ → ℝ) (Ψ f g : BondField ι → ℝ) : ℝ :=
  ballExpectation r Ψ (fun η => f η * g η) - ballExpectation r Ψ f * ballExpectation r Ψ g
def ballL2Norm (r : ℝ → ℝ) (Ψ h : BondField ι → ℝ) : ℝ :=
  Real.sqrt (ballExpectation r Ψ fun η => h η ^ 2)
structure IsRadialCutoff (ρ : ℝ) (r : ℝ → ℝ) : Prop where
  pos : ∀ u, 0 ≤ u → u < ρ → 0 < r u
  zero : ∀ u, ρ ≤ u → r u = 0
  one : ∀ u, 0 ≤ u → u ≤ 5 * ρ / 8 → r u = 1
  smooth : ContDiff ℝ 1 r
  anti : ∀ u, 0 ≤ u → deriv r u ≤ 0
structure IsUniformlyConvexDecaying (ρ m κ : ℝ) (d : ι → ι → ℝ) (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) :
    Prop where
  smooth : ContDiff ℝ 3 Ψ
  floor : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ u : BondField ι,
    2 * m * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong Ψ η u u
  kernel : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ (b b' : ι) (e e' : BondVector),
    |secondDerivAlong Ψ η (bondVariation b e) (bondVariation b' e')| ≤ K b b' * ‖e‖ * ‖e'‖
  symm : ∀ b b', K b b' = K b' b
  standingConstraints : ∀ b, ∑ b', K b b' * (Real.exp (2 * κ * d b b') - 1) ≤ m
structure IsPseudoMetricOnBonds (d : ι → ι → ℝ) : Prop where
  self : ∀ b, d b b = 0
  symm : ∀ b b', d b b' = d b' b
  triangle : ∀ b b' b'', d b b'' ≤ d b b' + d b' b''
end ColdStepAtMirrorFrames
end YangMills.Construction
end
