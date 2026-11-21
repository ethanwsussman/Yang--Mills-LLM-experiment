import YangMills.Construction.PeriodicOperators.ExpansionsOfTheComponentsOfAJet
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
def WithinBox (r : ℝ) (x y : InfiniteLattice.AmbientSpace) : Prop := ∀ μ, |x μ - y μ| ≤ r
namespace JetComponentBound
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' T →
    ∀ w : ℝ, (∀ ι, I.weightOf ι = w) → (∀ ι', I'.weightOf ι' = w) →
    ∀ (r β : ℝ) (N : ℕ), 0 ≤ β →
      (∀ ι', {ι | WithinBox r (I.pos ι) (I'.pos ι')}.encard ≤ N) →
      (∀ ι, {ι' | WithinBox r (I.pos ι) (I'.pos ι')}.encard ≤ N) →
    ∀ (p : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ),
      (∀ ι' ι, ¬ WithinBox r (I.pos ι) (I'.pos ι') →
        coeffOne F I I' T (phaseField F p εPlus (I'.pos ι')) ι' ι = 0 ∧
        coeffOne F I I' T (phaseField F (-p) εMinus (I'.pos ι')) ι' ι = 0 ∧
        coeffTwo F I I' T (phaseField F p εPlus (I'.pos ι'))
          (phaseField F (-p) εMinus (I'.pos ι')) ι' ι = 0) →
      (∀ ι' ι, WithinBox r (I.pos ι) (I'.pos ι') →
        ‖coeffOne F I I' T (phaseField F p εPlus (I'.pos ι')) ι' ι‖ ≤ β ∧
        ‖coeffOne F I I' T (phaseField F (-p) εMinus (I'.pos ι')) ι' ι‖ ≤ β ∧
        ‖coeffTwo F I I' T (phaseField F p εPlus (I'.pos ι'))
          (phaseField F (-p) εMinus (I'.pos ι')) ι' ι‖ ≤ β) →
      ∀ κ : Fin 4 → ℂ,
        quotHomNorm ((jetAlong F I I' T p εPlus εMinus).f10 κ) ≤
            ENNReal.ofReal (N * (Real.exp (∑ μ, |(κ μ).im| * r) * β)) ∧
          quotHomNorm ((jetAlong F I I' T p εPlus εMinus).f01 κ) ≤
            ENNReal.ofReal (N * (Real.exp (∑ μ, |(κ μ).im| * r) * β)) ∧
          quotHomNorm ((jetAlong F I I' T p εPlus εMinus).f11 κ) ≤
            ENNReal.ofReal (N * (Real.exp (∑ μ, |(κ μ).im| * r) * β))
end JetComponentBound
end YangMills.Construction.PeriodicOperators
end
