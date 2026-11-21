import YangMills.Construction.TwoPoints.TransformsOnTheLineAndTheirAlgebra
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints.LineTransforms
def convPowConst (g : ℝ → ℂ) : ℝ :=
  Real.sqrt Real.pi * Real.sqrt (∫ s : ℝ, (1 + s ^ 2) * ‖g s‖ ^ 2)
def ConvTransformRules : Prop :=
  ∀ u ∈ c1Functions, ∀ w ∈ c1Functions,
    convolve u w ∈ c1Functions ∧
    reflectConj u ∈ c1Functions ∧
    l1Norm (convolve u w) ≤ l1Norm u * l1Norm w ∧
    lineTransform (convolve u w) = lineTransform u * lineTransform w ∧
    lineTransform (reflectConj u) = conjFun (lineTransform u)
def TransformDerivBound : Prop :=
  ∀ u ∈ ccIn (Set.univ : Set ℝ),
    ContDiff ℝ 1 (lineTransform u) ∧
    (∀ q : ℝ, deriv (lineTransform u) q =
      lebesgueIntegral fun s : ℝ =>
        Complex.I * (s : ℂ) * u s * Complex.exp (Complex.I * (s : ℂ) * (q : ℂ))) ∧
    deriv (lineTransform u) = lineTransform (fun s : ℝ => Complex.I * (s : ℂ) * u s) ∧
    ∀ q : ℝ, ‖lineTransform u q‖ ≤ l1Norm u
def TransformDecay : Prop :=
  ∀ u ∈ c1Functions, ∀ q : ℝ, q ≠ 0 →
    ‖lineTransform u q‖ ≤ l1Norm (deriv u) / |q|
def ConvPowBound : Prop :=
  ∀ g ∈ c1Functions, ∀ k : ℕ, 1 ≤ k →
    l1Norm (convPow g k) ≤
      convPowConst g * (k : ℝ) * TestFunctions.uniformNorm (lineTransform g) ^ (k - 1)
def BumpProperties : Prop :=
  bumpFn ∈ realValuedPart c1Functions ∧
  (∀ s : ℝ, IsRealNonneg (bumpFn s)) ∧
  lebesgueIntegral bumpFn = 1 ∧
  (∀ k : ℕ, 1 ≤ k → ∀ a : ℝ,
    scaledBump k a ∈ c1Functions ∧
    (∀ s : ℝ, IsRealNonneg (scaledBump k a s)) ∧
    lebesgueIntegral (scaledBump k a) = 1 ∧
    (∀ s : ℝ, s ∉ Set.Icc (a - 1 / (k : ℝ)) (a + 1 / (k : ℝ)) → scaledBump k a s = 0) ∧
    ∀ q : ℝ, ‖lineTransform (scaledBump k a) q‖ ≤ 1) ∧
  ∀ a q : ℝ, Tendsto (fun k : ℕ => lineTransform (scaledBump k a) q) atTop
    (𝓝 (Complex.exp (Complex.I * (a : ℂ) * (q : ℂ))))
def StripAlgebraClosed : Prop :=
  stripAlgebra ≤ stripC0 ∧
  ∀ F ∈ stripAlgebra, ∀ G ∈ stripAlgebra,
    F * G ∈ stripAlgebra ∧ conjFun F ∈ stripAlgebra
def StripAlgebraDense : Prop :=
  ∀ F ∈ stripC0, ∃ Fs : ℕ → UnitStrip → ℂ,
    (∀ k, Fs k ∈ stripAlgebra) ∧
    Tendsto (fun k => TestFunctions.uniformNorm (F - Fs k)) atTop (𝓝 0)
def ConvPowDensity.Statement : Prop :=
  ConvTransformRules ∧
  TransformDerivBound ∧
  TransformDecay ∧
  ConvPowBound ∧
  BumpProperties ∧
  StripAlgebraClosed ∧
  StripAlgebraDense
end YangMills.Construction.TwoPoints.LineTransforms
end
