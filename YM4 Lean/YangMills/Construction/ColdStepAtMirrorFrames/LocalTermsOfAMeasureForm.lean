import YangMills.Construction.ColdStepAtMirrorFrames.MeanAlongASegmentForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {ι κ P : Type} [Fintype ι] [DecidableEq ι]
def IsAdmissiblePotential (ρ m r : ℝ) (d : ι → ι → ℝ) (Ψ : BondField ι → ℝ) : Prop :=
  ∃ K, IsUniformlyConvexDecaying ρ m r d Ψ K ∧
    ∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt m * ‖e‖
def halfSqNormOn (μ : ℝ) (Λ : Finset ι) (η : BondField ι) : ℝ := ∑ b ∈ Λ, μ / 2 * ‖η b‖ ^ 2
def restrictToBonds (Λ : Finset ι) (η : BondField ι) : BondField ι := fun b => if b ∈ Λ then η b else 0
def frozenPotential (Λ : Finset ι) (μ : ℝ) (Ψ : BondField ι → ℝ) (η : BondField ι) : ℝ :=
  Ψ (restrictToBonds Λ η) + halfSqNormOn μ Λᶜ η
def pushforwardField [Fintype κ] (j : κ → ι) (ξ : BondField κ) : BondField ι :=
  fun b => ∑ k, if j k = b then ξ k else 0
def weightedSqNormNear (r : ℝ) (pos : ι → P) (D : P → P → ℝ) (z : P) (η : BondField ι) : ℝ :=
  ∑ b, Real.exp (-(2 ^ 5 * r * D (pos b) z)) * ‖η b‖ ^ 2
structure IsLocalTermAt (ρ r c x : ℝ) (pos : ι → P) (D : P → P → ℝ) (z : P)
    (θ : BondField ι → ℝ) : Prop where
  smooth : ContDiffOn ℝ 2 θ (openPolyball ι ρ)
  slope : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm θ b η ≤
    c * (x * Real.sqrt (weightedSqNormNear r pos D z η) + 1) * Real.exp (-(2 ^ 5 * r * D (pos b) z))
  second : ∀ η ∈ openPolyball ι ρ, ∀ (b b' : ι) (e e' : BondVector),
    |secondDerivAlong θ η (bondVariation b e) (bondVariation b' e')| ≤
      c * x * Real.exp (-(2 ^ 5 * r * max (D (pos b) z) (D (pos b') z))) * ‖e‖ * ‖e'‖
end ColdStepAtMirrorFrames
end YangMills.Construction
end
