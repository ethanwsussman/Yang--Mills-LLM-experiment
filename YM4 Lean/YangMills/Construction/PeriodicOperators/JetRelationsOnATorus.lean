import YangMills.Construction.PeriodicOperators.ExponentialSumsTorusWavesAndComponentSets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TorusJetRelations
open JetDomains
open JetQuad (IsJet EqAsJet)
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ, IsLocalOpFun F I I' T →
      ∀ ρ R : ℝ, IsLocalWith F I I' T ρ R → ∀ s : ℕ, 0 < s → 4 * R < s →
        ∀ κ ∈ dualLattice s, ∀ p ∈ dualLattice s, ∀ (εPlus εMinus : F.UnitQuot → ℂ) (φ : I.UnitQuot → ℂ),
          WavesDescend F I s κ p εPlus εMinus φ ∧
            JetRelationsDescend F I I' T s κ p εPlus εMinus φ
end YangMills.Construction.PeriodicOperators.TorusJetRelations
end
