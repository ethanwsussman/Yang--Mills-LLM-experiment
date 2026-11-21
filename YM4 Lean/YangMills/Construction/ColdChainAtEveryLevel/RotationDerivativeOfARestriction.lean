import YangMills.Construction.ColdChainAtEveryLevel.LocalRestrictionsOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def derivAlongRotation {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → E)
    (e : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → E :=
  fun U v => deriv (fun τ : ℝ => Φ U (fun y i => v y i + τ • e y i)) 0
def localEvaluation_derivAlongRotationStatement : Prop :=
  ∀ (F : BlockFrame) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (S : Finset F.Cell)
    (R : F.FieldChain) (z : F.Cell) (B : Finset (F.Site F.top × Fin 4)) (C : ℕ → ℝ) (U : ChainChart F)
    (Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → E)
    (e : F.Site F.top → Fin 4 → imaginaryQuaternions),
    IsLocalRepresentation S R z B C U Φ →
    IsLocalRepresentation S R z B (fun k => C (k + 1) * topVariationNorm B e) U (derivAlongRotation Φ e)
end YangMills.Construction.BlockAverages
end
