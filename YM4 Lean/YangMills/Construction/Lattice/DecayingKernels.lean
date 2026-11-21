import YangMills.Construction.Lattice.PeriodicTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
def subspaceInverse {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (H : Submodule ℝ V) (T : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  H.subtype ∘ₗ
    (Ring.inverse (LinearMap.adjoint H.subtype ∘ₗ T ∘ₗ H.subtype : Module.End ℝ H) :
      Module.End ℝ H) ∘ₗ
    LinearMap.adjoint H.subtype
variable {d N : ℕ}
class HasSitePosition (d : ℕ) {N : ℕ} (s : Mesh N) (Y : Type) where
  position : Y → GridPoint d s
instance (s : Mesh N) : HasSitePosition d s (GridPoint d s) := ⟨id⟩
instance (s : Mesh N) : HasSitePosition d s (Link d s) := ⟨Link.source⟩
section Kernels
variable {s : Mesh N} {Y Y' : Type}
def posDist [HasSitePosition d s Y] [HasSitePosition d s Y'] (p : Y) (q : Y') : ℝ :=
  taxicabDist (HasSitePosition.position (d := d) (s := s) p : Torus d N)
    (HasSitePosition.position (d := d) (s := s) q)
open Classical in
def basisVec (p : Y) : ScaledFun d s Y := ofMap fun q => if q = p then 1 else 0
def matrixEntry [Fintype Y] (U : ScaledFun d s Y' →ₗ[ℝ] ScaledFun d s Y) (p : Y) (q : Y') : ℝ :=
  inner ℝ (basisVec p : ScaledFun d s Y) (U (basisVec q))
def expDecayClass [Fintype Y] [HasSitePosition d s Y] [HasSitePosition d s Y'] (δ c : ℝ) :
    Set (ScaledFun d s Y' →ₗ[ℝ] ScaledFun d s Y) :=
  {U | ∀ (p : Y) (q : Y'), |matrixEntry U p q| ≤ c * Real.exp (-δ * posDist (d := d) (s := s) p q)}
end Kernels
variable (d) in
def latticeExpSum (δ : ℝ) : ℝ :=
  d * ∑' z : Fin d → ℤ, Real.exp (-δ * ∑ μ, |(z μ : ℝ)|)
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
def OnSitesAndLinks (P : (Y : Type) → [Fintype Y] → [HasSitePosition d S.unitMesh Y] → Prop) : Prop :=
  P (GridPoint d S.unitMesh) ∧ P (Link d S.unitMesh)
def ExpSumBound (δ : ℝ) : Prop :=
  S.OnSitesAndLinks fun Y _ _ => ∀ u u' : Torus d N,
    ∑ p : Y, Real.exp (-δ * taxicabDist u (HasSitePosition.position (d := d) (s := S.unitMesh) p : Torus d N) -
      δ * taxicabDist (HasSitePosition.position (d := d) (s := S.unitMesh) p : Torus d N) u') ≤
      latticeExpSum d (δ / 2) * Real.exp (-(δ / 2) * taxicabDist u u')
def ExpDecayCompBound (δ c₁ c₂ : ℝ) : Prop :=
  S.OnSitesAndLinks fun Y _ _ => S.OnSitesAndLinks fun Y' _ _ => S.OnSitesAndLinks fun Y'' _ _ =>
    ∀ (U₁ : ScaledFun d S.unitMesh Y' →ₗ[ℝ] ScaledFun d S.unitMesh Y)
      (U₂ : ScaledFun d S.unitMesh Y'' →ₗ[ℝ] ScaledFun d S.unitMesh Y'),
      U₁ ∈ expDecayClass δ c₁ → U₂ ∈ expDecayClass δ c₂ →
      U₁ ∘ₗ U₂ ∈ expDecayClass (δ / 2) (latticeExpSum d (δ / 2) * c₁ * c₂)
def CombesThomasBoundAt (c₁ δ₁ γ D θ : ℝ) : Prop :=
  S.OnSitesAndLinks fun Y _ _ =>
    ∀ T : ScaledFun d S.unitMesh Y →ₗ[ℝ] ScaledFun d S.unitMesh Y,
      T ∈ expDecayClass δ₁ c₁ → T.IsSymmetric →
    ∀ cells : Setoid Y, (∀ p q, cells.r p q → posDist (d := d) (s := S.unitMesh) p q ≤ D) →
    ∀ H : Submodule ℝ (ScaledFun d S.unitMesh Y),
      (∀ ζ : Y → ℝ, (∀ p q, cells.r p q → ζ p = ζ q) →
        ∀ v ∈ H, (ofMap fun p => ζ p * v p : ScaledFun d S.unitMesh Y) ∈ H) →
      (∀ v ∈ H, γ * ‖v‖ ^ 2 ≤ inner ℝ v (T v)) →
      subspaceInverse H T ∈ expDecayClass θ (2 / γ * Real.exp (θ * D)) ∧
        ∀ v, ‖subspaceInverse H T v‖ ≤ γ⁻¹ * ‖v‖
end Scales
def CombesThomasEstimateHolds : Prop :=
  (∀ (d L j N : ℕ) (S : Scales d L j N) (δ c₁ c₂ : ℝ), 0 < δ → 0 < c₁ → 0 < c₂ →
    S.ExpSumBound δ ∧ S.ExpDecayCompBound δ c₁ c₂) ∧
  ∀ (d : ℕ) (c₁ δ₁ γ D : ℝ), 0 < c₁ → 0 < δ₁ → 0 < γ →
    ∃ θ : ℝ, 0 < θ ∧ ∀ (L j N : ℕ) (S : Scales d L j N), S.CombesThomasBoundAt c₁ δ₁ γ D θ
end YangMills.Construction.PeriodicLattice
