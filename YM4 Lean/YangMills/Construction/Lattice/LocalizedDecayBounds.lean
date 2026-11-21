import YangMills.Construction.Lattice.PeriodicTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
def closedMaxBall (s : Mesh N) (u : Torus d N) : Set (GridPoint d s) :=
  {x | maxDist (x : Torus d N) u ≤ 1}
def holderQuotientSup (s : Mesh N) (α : ℝ) (v : GridPoint d s → GridPoint d s → ℝ) : ℝ :=
  sSup {t | ∃ x y : GridPoint d s,
    0 < taxicabDist (x : Torus d N) y ∧ taxicabDist (x : Torus d N) y ≤ 1 ∧
      t = taxicabDist (x : Torus d N) y ^ (-α) * v x y}
section MultiFields
variable {s : Mesh N} {ι : Type}
def SiteFun.holderSemi (α : ℝ) (f : SiteFun d s) : ℝ :=
  holderQuotientSup s α fun x y => |f x - f y|
def MultiField.holderSemi [Fintype ι] (α : ℝ) (f : MultiField d s ι) : ℝ :=
  holderQuotientSup s α fun x y => ⨆ i, |f (i, x) - f (i, y)|
def MultiField.mulLeft (φ : SiteFun d s) (f : MultiField d s ι) : MultiField d s ι :=
  ofMap fun q => φ q.2 * f q
def SiteFun.SupportedIn (φ : SiteFun d s) (X : Set (GridPoint d s)) : Prop :=
  ∀ x, x ∉ X → φ x = 0
def MultiField.SupportedIn (f : MultiField d s ι) (X : Set (GridPoint d s)) : Prop :=
  ∀ x, x ∉ X → ∀ i, f (i, x) = 0
end MultiFields
structure DecayConstants where
  base : ℝ
  holder : ℝ → ℝ
  grad : ℝ → ℝ
  gradHolder : ℝ → ℝ → ℝ
  base_pos : 0 < base
  holder_pos : ∀ α, 0 ≤ α → α < 1 → 0 < holder α
  grad_pos : ∀ ε, 0 < ε → ε < 1 → 0 < grad ε
  gradHolder_pos : ∀ α ε, 0 ≤ α → 0 < ε → α + ε < 1 → 0 < gradHolder α ε
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
def oneFormGrad : OneForm d S.fineMesh →ₗ[ℝ] MultiField d S.fineMesh (Fin d × Fin d) :=
  fieldGrad S.fineMesh (Fin d)
def oneFormGradGrad :
    OneForm d S.fineMesh →ₗ[ℝ] MultiField d S.fineMesh (Fin d × Fin d × Fin d) :=
  fieldGrad S.fineMesh (Fin d × Fin d) ∘ₗ S.oneFormGrad
def oneFormGradAdj : MultiField d S.fineMesh (Fin d × Fin d) →ₗ[ℝ] OneForm d S.fineMesh :=
  LinearMap.adjoint S.oneFormGrad
def oneFormGradGradAdj :
    MultiField d S.fineMesh (Fin d × Fin d × Fin d) →ₗ[ℝ] OneForm d S.fineMesh :=
  LinearMap.adjoint S.oneFormGradGrad
structure PointwiseDecayBounds (c : DecayConstants)
    (O : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh)
    (E : ℝ) (x : GridPoint d S.fineMesh) (φ : SiteFun d S.fineMesh) (J : OneForm d S.fineMesh)
    (K : MultiField d S.fineMesh (Fin d × Fin d))
    (M : MultiField d S.fineMesh (Fin d × Fin d × Fin d)) : Prop where
  norm_at_le : MultiField.normAt (O J) x ≤ c.base * E * MultiField.maxNorm J
  grad_norm_at_le :
    MultiField.normAt (S.oneFormGrad (O J)) x ≤ c.base * E * MultiField.maxNorm J
  laplacian_norm_at_le :
    MultiField.normAt (fieldLaplacian S.fineMesh (Fin d) (O J)) x ≤
      c.base * E * MultiField.maxNorm J
  adj_norm_at_le :
    MultiField.normAt (O (S.oneFormGradAdj K)) x ≤ c.base * E * MultiField.maxNorm K
  holder_grad_le : ∀ α : ℝ, 0 ≤ α → α < 1 →
    MultiField.holderSemi α (MultiField.mulLeft φ (S.oneFormGrad (O J))) ≤
      c.holder α * E * (SiteFun.holderSemi α φ + SiteFun.maxNorm φ) * MultiField.maxNorm J
  holder_adj_le : ∀ α : ℝ, 0 ≤ α → α < 1 →
    MultiField.holderSemi α (MultiField.mulLeft φ (O (S.oneFormGradAdj K))) ≤
      c.holder α * E * (SiteFun.holderSemi α φ + SiteFun.maxNorm φ) * MultiField.maxNorm K
  grad_adj_norm_at_le : ∀ ε : ℝ, 0 < ε → ε < 1 →
    MultiField.normAt (S.oneFormGrad (O (S.oneFormGradAdj K))) x ≤
      c.grad ε * E * (MultiField.holderSemi ε K + MultiField.maxNorm K)
  holder_grad_adj_le : ∀ α ε : ℝ, 0 ≤ α → 0 < ε → α + ε < 1 →
    MultiField.holderSemi α
        (MultiField.mulLeft φ (S.oneFormGrad (O (S.oneFormGradAdj K)))) ≤
      c.gradHolder α ε * E * (SiteFun.holderSemi α φ + SiteFun.maxNorm φ) *
        (MultiField.holderSemi (α + ε) K + MultiField.maxNorm K)
  norm_mulLeft_le : ‖MultiField.mulLeft φ (O J)‖ ≤ c.base * E * SiteFun.maxNorm φ * ‖J‖
  norm_mulLeft_grad_le :
    ‖MultiField.mulLeft φ (S.oneFormGrad (O J))‖ ≤ c.base * E * SiteFun.maxNorm φ * ‖J‖
  norm_mulLeft_gradGrad_le :
    ‖MultiField.mulLeft φ (S.oneFormGradGrad (O J))‖ ≤ c.base * E * SiteFun.maxNorm φ * ‖J‖
  norm_mulLeft_adj_le :
    ‖MultiField.mulLeft φ (O (S.oneFormGradAdj K))‖ ≤ c.base * E * SiteFun.maxNorm φ * ‖K‖
  norm_mulLeft_grad_adj_le :
    ‖MultiField.mulLeft φ (S.oneFormGrad (O (S.oneFormGradAdj K)))‖ ≤
      c.base * E * SiteFun.maxNorm φ * ‖K‖
  norm_mulLeft_gradGrad_adj_le :
    ‖MultiField.mulLeft φ (O (S.oneFormGradGradAdj M))‖ ≤
      c.base * E * SiteFun.maxNorm φ * ‖M‖
def HasLocalizedDecay (δ : ℝ) (c : DecayConstants)
    (O : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh) : Prop :=
  0 < δ ∧ ∀ u v : Torus d N, ∀ x ∈ closedMaxBall S.fineMesh u, ∀ φ : SiteFun d S.fineMesh,
    SiteFun.SupportedIn φ (closedMaxBall S.fineMesh u) →
    ∀ (J : OneForm d S.fineMesh) (K : MultiField d S.fineMesh (Fin d × Fin d))
      (M : MultiField d S.fineMesh (Fin d × Fin d × Fin d)),
      MultiField.SupportedIn J (closedMaxBall S.fineMesh v) →
      MultiField.SupportedIn K (closedMaxBall S.fineMesh v) →
      MultiField.SupportedIn M (closedMaxBall S.fineMesh v) →
      S.PointwiseDecayBounds c O (Real.exp (-δ * taxicabDist u v)) x φ J K M
end Scales
end YangMills.Construction.PeriodicLattice
