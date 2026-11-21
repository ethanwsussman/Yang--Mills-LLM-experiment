import YangMills.Construction.Lattice.DecayingKernels
import YangMills.Construction.Lattice.LocalizedDecayBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
structure BoundFamily where
  main : ℝ
  holder : ℝ → ℝ
def BoundFamily.smul (t : ℝ) (κ : BoundFamily) : BoundFamily :=
  ⟨t * κ.main, fun α => t * κ.holder α⟩
def DecayConstants.toBoundFamily (c : DecayConstants) : BoundFamily :=
  ⟨c.base, c.holder⟩
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
def linkWeight (δ : ℝ) (b : Link d S.unitMesh) (u : Torus d N) : ℝ :=
  Real.exp (-δ * taxicabDist u (Link.source b : Torus d N))
structure LiftedFormBounds (κ : BoundFamily) (E : ℝ) (x : GridPoint d S.fineMesh)
    (ζ : SiteFun d S.fineMesh) (g : OneForm d S.fineMesh) : Prop where
  norm_at_le : MultiField.normAt g x ≤ κ.main * E
  grad_norm_at_le : MultiField.normAt (S.oneFormGrad g) x ≤ κ.main * E
  laplacian_norm_at_le : MultiField.normAt (fieldLaplacian S.fineMesh (Fin d) g) x ≤ κ.main * E
  holder_grad_le : ∀ α : ℝ, 0 ≤ α → α < 1 →
    MultiField.holderSemi α (MultiField.mulLeft ζ (S.oneFormGrad g)) ≤
      κ.holder α * E * (SiteFun.holderSemi α ζ + SiteFun.maxNorm ζ)
  norm_mulLeft_gradGrad_le :
    ‖MultiField.mulLeft ζ (S.oneFormGradGrad g)‖ ≤ κ.main * E * SiteFun.maxNorm ζ
def liftClass (δ : ℝ) (κ : BoundFamily) :
    Set (OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.fineMesh) :=
  {Y | ∀ (b : Link d S.unitMesh) (u : Torus d N), ∀ x ∈ closedMaxBall S.fineMesh u,
    ∀ ζ : SiteFun d S.fineMesh, SiteFun.SupportedIn ζ (closedMaxBall S.fineMesh u) →
      S.LiftedFormBounds κ (S.linkWeight δ b u) x ζ (Y (deltaLink b))}
def LiftClassCompKernel (δ : ℝ) : Prop :=
  ∀ (κ : BoundFamily) (c : ℝ) (Y : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.fineMesh)
    (U : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh),
    0 < c → Y ∈ S.liftClass δ κ →
    U ∈ (expDecayClass δ c : Set (OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh)) →
    Y ∘ₗ U ∈ S.liftClass (δ / 2) (κ.smul (latticeExpSum d (δ / 2) * c))
def LiftClassProducts (δ C : ℝ) : Prop :=
  ∀ (κ : BoundFamily) (Y Z : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.fineMesh),
    Y ∈ S.liftClass δ κ → Z ∈ S.liftClass δ κ →
    LinearMap.adjoint Z ∘ₗ Y ∈
        (expDecayClass (δ / 2) (C * κ.main ^ 2) : Set (OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh)) ∧
      LinearMap.adjoint Z ∘ₗ fieldLaplacian S.fineMesh (Fin d) ∘ₗ Y ∈
        (expDecayClass (δ / 2) (C * κ.main ^ 2) : Set (OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh)) ∧
      LinearMap.adjoint (LinearMap.adjoint (discreteGrad S.fineMesh) ∘ₗ Z) ∘ₗ
          (LinearMap.adjoint (discreteGrad S.fineMesh) ∘ₗ Y) ∈
        (expDecayClass (δ / 2) (C * κ.main ^ 2) : Set (OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh)) ∧
      S.fineFormAverage ∘ₗ Y ∈
        (expDecayClass δ (C * κ.main) : Set (OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh))
def LiftClassOperators (δ C : ℝ) : Prop :=
  ∀ (c : DecayConstants) (O : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh),
    S.HasLocalizedDecay δ c O →
    (∀ (k : ℝ) (f : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.fineMesh),
      (∀ (b : Link d S.unitMesh) (u : Torus d N), ∀ x ∈ closedMaxBall S.fineMesh u,
        MultiField.normAt (f (deltaLink b)) x ≤ k * S.linkWeight δ b u) →
      O ∘ₗ f ∈ S.liftClass (δ / 2) (c.toBoundFamily.smul (C * k))) ∧
    O ∘ₗ LinearMap.adjoint S.fineFormAverage ∈
      S.liftClass (δ / 2) (c.toBoundFamily.smul (C * Real.exp (3 * d * δ)))
def LiftClassLocalizedDecay (δ C : ℝ) : Prop :=
  ∀ (κ : BoundFamily) (Y Z : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.fineMesh),
    Y ∈ S.liftClass δ κ → Z ∈ S.liftClass δ κ →
    ∀ c : DecayConstants, c.base = C * κ.main ^ 2 →
      (∀ ε : ℝ, 0 < ε → ε < 1 → c.grad ε = C * κ.main ^ 2) →
      (∀ α : ℝ, 0 ≤ α → α < 1 → c.holder α = C * κ.main * (κ.main + κ.holder α)) →
      (∀ α ε : ℝ, 0 ≤ α → 0 < ε → α + ε < 1 →
        c.gradHolder α ε = C * κ.main * (κ.main + κ.holder α)) →
      S.HasLocalizedDecay (δ / 2) c (Y ∘ₗ LinearMap.adjoint Z)
end Scales
def IsLiftProductsConstant (d : ℕ) (δ C : ℝ) : Prop :=
  0 < C ∧ ∀ (L j N : ℕ) (S : Scales d L j N), S.LiftClassProducts δ C
def IsLiftOperatorsConstant (d : ℕ) (δ C : ℝ) : Prop :=
  0 < C ∧ ∀ (L j N : ℕ) (S : Scales d L j N), S.LiftClassOperators δ C
def IsLiftLocalizedDecayConstant (d : ℕ) (δ C : ℝ) : Prop :=
  0 < C ∧ ∀ (L j N : ℕ) (S : Scales d L j N), S.LiftClassLocalizedDecay δ C
def liftProductsConstant (d : ℕ) (δ : ℝ) : ℝ :=
  Classical.epsilon (IsLiftProductsConstant d δ)
def liftOperatorsConstant (d : ℕ) (δ : ℝ) : ℝ :=
  Classical.epsilon (IsLiftOperatorsConstant d δ)
def liftLocalizedDecayConstant (d : ℕ) (δ : ℝ) : ℝ :=
  Classical.epsilon (IsLiftLocalizedDecayConstant d δ)
def LiftClassPropertiesHold : Prop :=
  ∀ (d : ℕ) (δ : ℝ), 0 < δ →
    (∀ (L j N : ℕ) (S : Scales d L j N), S.LiftClassCompKernel δ) ∧
    IsLiftProductsConstant d δ (liftProductsConstant d δ) ∧
    IsLiftOperatorsConstant d δ (liftOperatorsConstant d δ) ∧
    IsLiftLocalizedDecayConstant d δ (liftLocalizedDecayConstant d δ)
end YangMills.Construction.PeriodicLattice
