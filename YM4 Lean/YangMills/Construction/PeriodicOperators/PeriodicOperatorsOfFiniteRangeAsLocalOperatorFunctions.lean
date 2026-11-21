import YangMills.Construction.PeriodicOperators.ExponentialSumsTorusWavesAndComponentSets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.ConstantOpFun
open JetDomains
open JetQuad (EqAsJet)
def constAssign (F : PeriodicData) {I I' : PeriodicData} (T : I'.Carrier → I.Carrier → ℂ) :
    (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ :=
  fun _ => T
def addSmulKernel {F I I' : PeriodicData} (S : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ)
    (c : ℂ) (T : I'.Carrier → I.Carrier → ℂ) : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ :=
  fun z => S z + c • T
def Claim : Prop :=
  ∀ F I I' : PeriodicData, IsPeriodic F → IsPeriodic I → IsPeriodic I' →
    ∀ T : I'.Carrier → I.Carrier → ℂ, IsPeriodicKernel I I' T → IsFiniteRange I I' T →
      ∀ (d : ℝ) (p : Fin 4 → ℂ), 0 < d → p ∈ imStrip d → ∀ sPlus sMinus : F.UnitQuot → ℂ,
        (IsLocalOpFun F I I' (constAssign F T) ∧
          coeffZero F I I' (constAssign F T) = T ∧
          (∀ z, coeffOne F I I' (constAssign F T) z = 0) ∧
          (∀ z z', coeffTwo F I I' (constAssign F T) z z' = 0) ∧
          SymbolHolomorphicNear I I' (imStrip (2 * d)) T ∧
          EqAsJet d p (jetAlong F I I' (constAssign F T) p sPlus sMinus)
            (JetQuad.ofKernel I I' T)) ∧
        ∀ (S : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (c : ℂ),
          IsLocalOpFun F I I' S →
            IsLocalOpFun F I I' (addSmulKernel S c T) ∧
              EqAsJet d p (jetAlong F I I' (addSmulKernel S c T) p sPlus sMinus)
                (JetQuad.add (jetAlong F I I' S p sPlus sMinus)
                  (JetQuad.smul c (JetQuad.ofKernel I I' T)))
end YangMills.Construction.PeriodicOperators.ConstantOpFun
end
