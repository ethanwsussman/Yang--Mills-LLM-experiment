import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace UniformDecay
def Weaken : Prop :=
  ∀ A B : PeriodicData, IsPeriodic A → IsPeriodic B →
    ∀ (T : B.Carrier → A.Carrier → ℂ) (c r c' r' : ℝ),
      IsPeriodicKernel A B T → 0 < c → 0 < r → ExpDecay A B T c r →
        c ≤ c' → 0 < r' → r' ≤ r → ExpDecay A B T c' r'
def FiniteFamily : Prop :=
  ∀ (ι : Type) [Finite ι] [Nonempty ι] (A B : ι → PeriodicData),
    (∀ i, IsPeriodic (A i)) → (∀ i, IsPeriodic (B i)) →
    ∀ (T : ∀ i, (B i).Carrier → (A i).Carrier → ℂ) (c r : ι → ℝ),
      (∀ i, IsPeriodicKernel (A i) (B i) (T i)) → (∀ i, 0 < c i) → (∀ i, 0 < r i) →
      (∀ i, ExpDecay (A i) (B i) (T i) (c i) (r i)) →
      ∃ cSup rInf : ℝ, IsGreatest (range c) cSup ∧ IsLeast (range r) rInf ∧
        (∀ i, ExpDecay (A i) (B i) (T i) cSup rInf) ∧ ∀ i, IsDecayRate (A i) (B i) (T i) rInf
def Claim : Prop := Weaken ∧ FiniteFamily
end UniformDecay
end YangMills.Construction.PeriodicOperators
end
