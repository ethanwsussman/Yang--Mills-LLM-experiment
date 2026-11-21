import YangMills.Construction.RunningCouplingSlope.CoordinatesOfATriple
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
structure LocallyHolomorphicFamiliesClosedOn (L n k : ℕ) : Prop where
  mono : ∀ {I ι ι' : Type} [Fintype I] [Fintype ι] [Fintype ι'] [DecidableEq ι]
    {e : I → Tower.Vertex L n k k} {c : ι → Tower.Vertex L n k k} {c' : ι' → Tower.Vertex L n k k}
    {F : (I → ℂ) → Matrix ι' ι ℂ} {ρ C r ρ' C' r' : ℝ}, ρ' ≤ ρ → C ≤ C' → r ≤ r' →
    IsLocallyHolomorphicFamily e c c' F ρ C r → IsLocallyHolomorphicFamily e c c' F ρ' C' r'
  one : ∀ {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq ι] (e : I → Tower.Vertex L n k k)
    (c : ι → Tower.Vertex L n k k) (ρ r : ℝ), 0 ≤ r →
    IsLocallyHolomorphicFamily e c c (fun _ => (1 : Matrix ι ι ℂ)) ρ 1 r
  add : ∀ {I ι ι' : Type} [Fintype I] [Fintype ι] [Fintype ι'] [DecidableEq ι]
    {e : I → Tower.Vertex L n k k} {c : ι → Tower.Vertex L n k k} {c' : ι' → Tower.Vertex L n k k}
    {F G : (I → ℂ) → Matrix ι' ι ℂ} {ρ C C' r : ℝ},
    IsLocallyHolomorphicFamily e c c' F ρ C r → IsLocallyHolomorphicFamily e c c' G ρ C' r →
    IsLocallyHolomorphicFamily e c c' (fun w => F w + G w) ρ (C + C') r
  smul : ∀ {I ι ι' : Type} [Fintype I] [Fintype ι] [Fintype ι'] [DecidableEq ι]
    {e : I → Tower.Vertex L n k k} {c : ι → Tower.Vertex L n k k} {c' : ι' → Tower.Vertex L n k k}
    {F : (I → ℂ) → Matrix ι' ι ℂ} {ρ C r : ℝ} (x : ℂ),
    IsLocallyHolomorphicFamily e c c' F ρ C r →
    IsLocallyHolomorphicFamily e c c' (fun w => x • F w) ρ (‖x‖ * C) r
  mul : ∀ {I ι ι' κ : Type} [Fintype I] [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] {e : I → Tower.Vertex L n k k} {c : ι → Tower.Vertex L n k k}
    {c' : ι' → Tower.Vertex L n k k} {d : κ → Tower.Vertex L n k k} {F : (I → ℂ) → Matrix ι' ι ℂ}
    {G : (I → ℂ) → Matrix ι κ ℂ} {ρ C C' r r' : ℝ}, 0 ≤ r → 0 ≤ r' →
    IsLocallyHolomorphicFamily e c c' F ρ C r → IsLocallyHolomorphicFamily e d c G ρ C' r' →
    IsLocallyHolomorphicFamily e d c' (fun w => F w * G w) ρ (C * C') (r + r')
  transpose : ∀ {I ι ι' : Type} [Fintype I] [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] {e : I → Tower.Vertex L n k k} {c : ι → Tower.Vertex L n k k}
    {c' : ι' → Tower.Vertex L n k k} {F : (I → ℂ) → Matrix ι' ι ℂ} {ρ C r : ℝ}, 0 ≤ r →
    IsLocallyHolomorphicFamily e c c' F ρ C r →
    IsLocallyHolomorphicFamily e c' c (fun w => (F w).transpose) ρ C (2 * r)
  fromBlocks : ∀ {I ι κ ι' κ' : Type} [Fintype I] [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    [DecidableEq ι] [DecidableEq κ] {e : I → Tower.Vertex L n k k} {c : ι → Tower.Vertex L n k k}
    {d : κ → Tower.Vertex L n k k} {c' : ι' → Tower.Vertex L n k k} {d' : κ' → Tower.Vertex L n k k}
    {A : (I → ℂ) → Matrix ι' ι ℂ} {B : (I → ℂ) → Matrix ι' κ ℂ}
    {C : (I → ℂ) → Matrix κ' ι ℂ} {D : (I → ℂ) → Matrix κ' κ ℂ} {ρ K₁ K₂ K₃ K₄ r : ℝ},
    IsLocallyHolomorphicFamily e c c' A ρ K₁ r → IsLocallyHolomorphicFamily e d c' B ρ K₂ r →
    IsLocallyHolomorphicFamily e c d' C ρ K₃ r → IsLocallyHolomorphicFamily e d d' D ρ K₄ r →
    IsLocallyHolomorphicFamily e (Sum.elim c d) (Sum.elim c' d')
      (fun w => Matrix.fromBlocks (A w) (B w) (C w) (D w)) ρ (K₁ + K₂ + K₃ + K₄) r
def LocallyHolomorphicFamiliesClosed : Prop :=
  ∀ L n k : ℕ, LocallyHolomorphicFamiliesClosedOn L n k
end YangMills.Construction.RunningCouplingSlope
end
