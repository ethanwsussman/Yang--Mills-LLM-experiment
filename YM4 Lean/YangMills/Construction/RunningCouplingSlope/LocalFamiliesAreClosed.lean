import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
structure LocalFamilyClosure (θ S : ℝ) (L n k : ℕ) : Prop where
  ofConstant : ∀ {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] (c : ι → Tower.Vertex L n k k)
    (c' : ι' → Tower.Vertex L n k k) (A : Matrix ι' ι ℂ) (v : Fin 4 → ℤ) (M : ℝ), 0 ≤ M →
    IsLocalOnCells c c' A M θ (fun _ => 1) → IsLocalAlongBackground c c' (fun _ _ => A) v M θ
  mono : ∀ {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] (c : ι → Tower.Vertex L n k k)
    (c' : ι' → Tower.Vertex L n k k) (T : ℝ → ℝ → Matrix ι' ι ℂ) (v : Fin 4 → ℤ) (M M' θ' : ℝ),
    0 ≤ M → M ≤ M' → 0 < θ' → θ' ≤ θ → IsLocalAlongBackground c c' T v M θ →
    IsLocalAlongBackground c c' T v M' θ'
  add : ∀ {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] (c : ι → Tower.Vertex L n k k)
    (c' : ι' → Tower.Vertex L n k k) (T T' : ℝ → ℝ → Matrix ι' ι ℂ) (v : Fin 4 → ℤ) (M M' : ℝ),
    IsLocalAlongBackground c c' T v M θ → IsLocalAlongBackground c c' T' v M' θ →
    IsLocalAlongBackground c c' (fun s t => T s t + T' s t) v (M + M') θ
  smul : ∀ {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] (c : ι → Tower.Vertex L n k k)
    (c' : ι' → Tower.Vertex L n k k) (T : ℝ → ℝ → Matrix ι' ι ℂ) (v : Fin 4 → ℤ) (M : ℝ) (x : ℂ),
    IsLocalAlongBackground c c' T v M θ →
    IsLocalAlongBackground c c' (fun s t => x • T s t) v (‖x‖ * M) θ
  transpose : ∀ {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (c : ι → Tower.Vertex L n k k) (c' : ι' → Tower.Vertex L n k k) (T : ℝ → ℝ → Matrix ι' ι ℂ)
    (v : Fin 4 → ℤ) (M : ℝ), 0 ≤ M → IsLocalAlongBackground c c' T v M θ →
    IsLocalAlongBackground c' c (fun s t => (T s t).transpose) v M (θ / 4)
  fromBlocks : ∀ {ι₁ ι₂ ι₁' ι₂' : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₁'] [Fintype ι₂']
    [DecidableEq ι₁] [DecidableEq ι₂] (c₁ : ι₁ → Tower.Vertex L n k k) (c₂ : ι₂ → Tower.Vertex L n k k)
    (c₁' : ι₁' → Tower.Vertex L n k k) (c₂' : ι₂' → Tower.Vertex L n k k)
    (A : ℝ → ℝ → Matrix ι₁' ι₁ ℂ) (B : ℝ → ℝ → Matrix ι₁' ι₂ ℂ)
    (C : ℝ → ℝ → Matrix ι₂' ι₁ ℂ) (D : ℝ → ℝ → Matrix ι₂' ι₂ ℂ) (v : Fin 4 → ℤ) (M : ℝ),
    IsLocalAlongBackground c₁ c₁' A v M θ → IsLocalAlongBackground c₂ c₁' B v M θ →
    IsLocalAlongBackground c₁ c₂' C v M θ → IsLocalAlongBackground c₂ c₂' D v M θ →
    IsLocalAlongBackground (Sum.elim c₁ c₂) (Sum.elim c₁' c₂')
      (fun s t => Matrix.fromBlocks (A s t) (B s t) (C s t) (D s t)) v (4 * M) θ
  mul : ∀ {ι ι' ι'' : Type} [Fintype ι] [Fintype ι'] [Fintype ι''] [DecidableEq ι]
    [DecidableEq ι'] (c : ι → Tower.Vertex L n k k) (c' : ι' → Tower.Vertex L n k k)
    (c'' : ι'' → Tower.Vertex L n k k)
    (A : ℝ → ℝ → Matrix ι'' ι' ℂ) (B : ℝ → ℝ → Matrix ι' ι ℂ) (v : Fin 4 → ℤ) (M M' : ℝ),
    0 ≤ M → 0 ≤ M' → IsLocalAlongBackground c' c'' A v M θ → IsLocalAlongBackground c c' B v M' θ →
    IsLocalAlongBackground c c'' (fun s t => A s t * B s t) v (S * M * M') (θ / 4)
  inv : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → Tower.Vertex L n k k)
    (T : ℝ → ℝ → Matrix ι ι ℂ) (v : Fin 4 → ℤ) (M : ℝ), 0 ≤ M →
    IsLocalAlongBackground c c T v M θ →
    IsUnit (Matrix.det (T 0 0)) → IsLocalOnCells c c (T 0 0)⁻¹ M θ (fun _ => 1) →
    IsLocalAlongBackground c c (fun s t => (T s t)⁻¹) v (S ^ 4 * (M + 1) ^ 5) (θ / 256)
def LocalFamiliesClosed : Prop :=
  ∀ θ : ℝ, 0 < θ → ∃ S : ℝ, 1 ≤ S ∧ ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    LocalFamilyClosure θ S L n k
end YangMills.Construction.RunningCouplingSlope
end
