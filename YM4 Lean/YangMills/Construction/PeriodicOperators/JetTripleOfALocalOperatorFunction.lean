import YangMills.Construction.PeriodicOperators.ExponentialSumsTorusWavesAndComponentSets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LocalOpFunTriple
open JetDomains
open JetQuad (IsJet EqAsJet)
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ A : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' A →
      (∀ (p : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ), ActionTripleUnique F I I' A p εp εm) ∧
      (∀ (c' : I'.UnitQuot) (c : I.UnitQuot), ∃ (n : ℕ) (f : Fin n → MomentumLinearForm)
        (w : Fin n → (F.UnitQuot → ℂ) →ₗ[ℂ] ℂ), ∀ (p k : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ),
          linearMapEntry ((jetAlong F I I' A p εp εm).f10 k) c' c =
            expSum (fun j => w j εp) f k p) ∧
      (∀ (c' : I'.UnitQuot) (c : I.UnitQuot), ∃ (n : ℕ) (f : Fin n → MomentumLinearForm)
        (w : Fin n → (F.UnitQuot → ℂ) →ₗ[ℂ] ℂ), ∀ (p k : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ),
          linearMapEntry ((jetAlong F I I' A p εp εm).f01 k) c' c =
            expSum (fun j => w j εm) f k p) ∧
      ∀ (c' : I'.UnitQuot) (c : I.UnitQuot), ∃ (n : ℕ) (f : Fin n → MomentumLinearForm)
        (w : Fin n → (F.UnitQuot → ℂ) →ₗ[ℂ] (F.UnitQuot → ℂ) →ₗ[ℂ] ℂ),
        ∀ (p k : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ),
          linearMapEntry ((jetAlong F I I' A p εp εm).f11 k) c' c =
            expSum (fun j => w j εp εm) f k p
end YangMills.Construction.PeriodicOperators.LocalOpFunTriple
end
