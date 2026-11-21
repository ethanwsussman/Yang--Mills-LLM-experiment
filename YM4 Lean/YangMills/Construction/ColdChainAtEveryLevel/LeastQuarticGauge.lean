import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormula
import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace LatticeFractionalIntegration
def latticePlaquette (A : Lattice4 → Fin 4 → BlockAverages.UnitQuaternion) (y : Lattice4) (μ ν : Fin 4) :
    BlockAverages.UnitQuaternion :=
  A y μ * A (y + basisVector μ) ν * (A (y + basisVector ν) μ)⁻¹ * (A y ν)⁻¹
def latticeGaugeTransform (g : Lattice4 → BlockAverages.UnitQuaternion)
    (A : Lattice4 → Fin 4 → BlockAverages.UnitQuaternion) : Lattice4 → Fin 4 → BlockAverages.UnitQuaternion :=
  fun y i => g y * A y i * (g (y + basisVector i))⁻¹
def quarticGaugeStatement : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (N : ℕ) (S P : Finset Lattice4)
    (A : Lattice4 → Fin 4 → BlockAverages.UnitQuaternion) (ε : ℝ), 1 ≤ N →
    S.Nonempty → (∀ a ∈ S, ∀ i, -(10 * (N : ℤ)) ≤ a i ∧ a i ≤ 12 * (N : ℤ)) →
    (∀ x, x ∈ P ↔ (∀ i, x i ≤ 21 * (N : ℤ) - 1) ∧ ∃ a ∈ S, ∀ i, a i ≤ x i) →
    0 ≤ ε → ε ≤ c →
    ∑ p ∈ orientedPlaquettesOf P,
      ‖((latticePlaquette A p.1 p.2.1 p.2.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 ≤ ε ^ 2 →
    ∃ g : Lattice4 → BlockAverages.UnitQuaternion, ∑ b ∈ bondsOf P,
      ‖((latticeGaugeTransform g A b.1 b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 ≤ (C * ε) ^ 4
end LatticeFractionalIntegration
end YangMills.Construction
end
