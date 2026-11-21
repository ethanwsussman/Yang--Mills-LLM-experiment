import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
def phaseField (F : PeriodicData) (q : Fin 4 → ℂ) (ε : F.UnitQuot → ℂ)
    (y : InfiniteLattice.AmbientSpace) : F.Carrier → ℂ :=
  fun k => Complex.exp (Complex.I * bilinDot q (toComplexVec (F.pos k - y))) * ε (F.mkQuot 1 k)
def relPhase (I I' : PeriodicData) (κ : Fin 4 → ℂ) (i' : I'.Carrier) (i : I.Carrier) : ℂ :=
  Complex.exp (Complex.I * bilinDot κ (toComplexVec (I.pos i - I'.pos i')))
namespace JetExpansions
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' T →
    ∀ (p κ : Fin 4 → ℂ) (εp εm : F.UnitQuot → ℂ) (φ : I.UnitQuot → ℂ) (i' : I'.Carrier),
      (jetAlong F I I' T p εp εm).f10 κ φ (I'.mkQuot 1 i') =
          ∑' i, relPhase I I' κ i' i *
            coeffOne F I I' T (phaseField F p εp (I'.pos i')) i' i *
            φ (I.mkQuot 1 i) ∧
        (jetAlong F I I' T p εp εm).f01 κ φ (I'.mkQuot 1 i') =
          ∑' i, relPhase I I' κ i' i *
            coeffOne F I I' T (phaseField F (-p) εm (I'.pos i')) i' i *
            φ (I.mkQuot 1 i) ∧
        (jetAlong F I I' T p εp εm).f11 κ φ (I'.mkQuot 1 i') =
          ∑' i, relPhase I I' κ i' i *
            coeffTwo F I I' T (phaseField F p εp (I'.pos i'))
              (phaseField F (-p) εm (I'.pos i')) i' i *
            φ (I.mkQuot 1 i)
end JetExpansions
end YangMills.Construction.PeriodicOperators
end
