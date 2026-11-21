import YangMills.Construction.Lattice.LocalizedDecayBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
structure FineOneFormBounds (k : ℝ) (kα : ℝ → ℝ) (E : ℝ) (x : GridPoint d S.fineMesh)
    (ζ : SiteFun d S.fineMesh) (g : OneForm d S.fineMesh) : Prop where
  norm_at_le : MultiField.normAt g x ≤ k * E
  grad_norm_at_le : MultiField.normAt (S.oneFormGrad g) x ≤ k * E
  laplacian_norm_at_le : MultiField.normAt (fieldLaplacian S.fineMesh (Fin d) g) x ≤ k * E
  holder_grad_le : ∀ α : ℝ, 0 ≤ α → α < 1 →
    MultiField.holderSemi α (MultiField.mulLeft ζ (S.oneFormGrad g)) ≤
      kα α * E * (SiteFun.holderSemi α ζ + SiteFun.maxNorm ζ)
  norm_mulLeft_gradGrad_le :
    ‖MultiField.mulLeft ζ (S.oneFormGradGrad g)‖ ≤ k * E * SiteFun.maxNorm ζ
def DecaysFromPoint (δ k : ℝ) (kα : ℝ → ℝ) (p : Torus d N) (g : OneForm d S.fineMesh) : Prop :=
  ∀ u : Torus d N, ∀ x ∈ closedMaxBall S.fineMesh u, ∀ ζ : SiteFun d S.fineMesh,
    SiteFun.SupportedIn ζ (closedMaxBall S.fineMesh u) →
      S.FineOneFormBounds k kα (Real.exp (-δ * taxicabDist u p)) x ζ g
end Scales
end YangMills.Construction.PeriodicLattice
