import YangMills.Construction.Lattice.LocalizedDecayBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace Mesh
variable (s : Mesh N)
def oneFormDeriv : OneForm d s →ₗ[ℝ] MultiField d s (Fin d × Fin d) :=
  fieldGrad s (Fin d)
def oneFormDerivDeriv : OneForm d s →ₗ[ℝ] MultiField d s (Fin d × Fin d × Fin d) :=
  fieldGrad s (Fin d × Fin d) ∘ₗ s.oneFormDeriv
def oneFormDerivAdj : MultiField d s (Fin d × Fin d) →ₗ[ℝ] OneForm d s :=
  LinearMap.adjoint s.oneFormDeriv
def oneFormDerivDerivAdj : MultiField d s (Fin d × Fin d × Fin d) →ₗ[ℝ] OneForm d s :=
  LinearMap.adjoint s.oneFormDerivDeriv
structure PointwiseDecayBounds (c : DecayConstants) (O : OneForm d s →ₗ[ℝ] OneForm d s)
    (E : ℝ) (x : GridPoint d s) (ζ : SiteFun d s) (J : OneForm d s)
    (J' : MultiField d s (Fin d × Fin d)) (J'' : MultiField d s (Fin d × Fin d × Fin d)) :
    Prop where
  normAt_le : MultiField.normAt (O J) x ≤ c.base * E * MultiField.maxNorm J
  gradNormAt_le : MultiField.normAt (s.oneFormDeriv (O J)) x ≤ c.base * E * MultiField.maxNorm J
  laplacianNormAt_le :
    MultiField.normAt (fieldLaplacian s (Fin d) (O J)) x ≤ c.base * E * MultiField.maxNorm J
  adjNormAt_le :
    MultiField.normAt (O (s.oneFormDerivAdj J')) x ≤ c.base * E * MultiField.maxNorm J'
  holder_grad : ∀ α : ℝ, 0 ≤ α → α < 1 →
    MultiField.holderSemi α (MultiField.mulLeft ζ (s.oneFormDeriv (O J))) ≤
      c.holder α * E * (SiteFun.holderSemi α ζ + SiteFun.maxNorm ζ) * MultiField.maxNorm J
  holder_adj : ∀ α : ℝ, 0 ≤ α → α < 1 →
    MultiField.holderSemi α (MultiField.mulLeft ζ (O (s.oneFormDerivAdj J'))) ≤
      c.holder α * E * (SiteFun.holderSemi α ζ + SiteFun.maxNorm ζ) * MultiField.maxNorm J'
  gradAdjNormAt_le : ∀ ε : ℝ, 0 < ε → ε < 1 →
    MultiField.normAt (s.oneFormDeriv (O (s.oneFormDerivAdj J'))) x ≤
      c.grad ε * E * (MultiField.holderSemi ε J' + MultiField.maxNorm J')
  holder_gradAdj : ∀ α ε : ℝ, 0 ≤ α → 0 < ε → α + ε < 1 →
    MultiField.holderSemi α
        (MultiField.mulLeft ζ (s.oneFormDeriv (O (s.oneFormDerivAdj J')))) ≤
      c.gradHolder α ε * E * (SiteFun.holderSemi α ζ + SiteFun.maxNorm ζ) *
        (MultiField.holderSemi (α + ε) J' + MultiField.maxNorm J')
  norm_mul_le : ‖MultiField.mulLeft ζ (O J)‖ ≤ c.base * E * SiteFun.maxNorm ζ * ‖J‖
  norm_mul_grad_le :
    ‖MultiField.mulLeft ζ (s.oneFormDeriv (O J))‖ ≤ c.base * E * SiteFun.maxNorm ζ * ‖J‖
  norm_mul_gradGrad_le :
    ‖MultiField.mulLeft ζ (s.oneFormDerivDeriv (O J))‖ ≤ c.base * E * SiteFun.maxNorm ζ * ‖J‖
  norm_mul_adj_le :
    ‖MultiField.mulLeft ζ (O (s.oneFormDerivAdj J'))‖ ≤ c.base * E * SiteFun.maxNorm ζ * ‖J'‖
  norm_mul_gradAdj_le :
    ‖MultiField.mulLeft ζ (s.oneFormDeriv (O (s.oneFormDerivAdj J')))‖ ≤
      c.base * E * SiteFun.maxNorm ζ * ‖J'‖
  norm_mul_gradGradAdj_le :
    ‖MultiField.mulLeft ζ (O (s.oneFormDerivDerivAdj J''))‖ ≤
      c.base * E * SiteFun.maxNorm ζ * ‖J''‖
def HasLocalizedDecay (δ : ℝ) (c : DecayConstants)
    (O : OneForm d s →ₗ[ℝ] OneForm d s) : Prop :=
  0 < δ ∧ ∀ u u' : Torus d N, ∀ x ∈ closedMaxBall s u, ∀ ζ : SiteFun d s,
    SiteFun.SupportedIn ζ (closedMaxBall s u) →
    ∀ (J : OneForm d s) (J' : MultiField d s (Fin d × Fin d))
      (J'' : MultiField d s (Fin d × Fin d × Fin d)),
      MultiField.SupportedIn J (closedMaxBall s u') →
      MultiField.SupportedIn J' (closedMaxBall s u') →
      MultiField.SupportedIn J'' (closedMaxBall s u') →
      s.PointwiseDecayBounds c O (Real.exp (-δ * taxicabDist u u')) x ζ J J' J''
end Mesh
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
end Scales
end PeriodicLattice
namespace DirichletLaplacian
open PeriodicLattice
variable {d N : ℕ} {hN : 0 < N}
def HasLocalizedDecayUnit (δ : ℝ) (c : DecayConstants)
    (O : OneForm d (Mesh.one hN) →ₗ[ℝ] OneForm d (Mesh.one hN)) : Prop :=
  (Mesh.one hN).HasLocalizedDecay δ c O
def linkKernel (O : OneForm d (Mesh.one hN) →ₗ[ℝ] OneForm d (Mesh.one hN))
    (b b' : Link d (Mesh.one hN)) : ℝ :=
  inner ℝ (deltaLink b) (O (deltaLink b'))
end DirichletLaplacian
end YangMills.Construction
