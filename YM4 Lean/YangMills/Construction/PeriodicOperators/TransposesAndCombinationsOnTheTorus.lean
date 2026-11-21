import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace TorusPeriodization
open Classical in
def Claim : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' → ∀ s : ℕ, 1 ≤ s →
    (∀ T : I'.Carrier → I.Carrier → ℂ, IsPeriodicKernel I I' T →
      periodicMatrix I' I (kernelTranspose I I' T) s =
        wTranspose (I.quotWeight s) (I'.quotWeight s) (periodicMatrix I I' T s) ∧
      ((∀ x' x, (T x' x).im = 0) → ∀ c' c, (periodicMatrix I I' T s c' c).im = 0) ∧
      ∀ T' : I'.Carrier → I.Carrier → ℂ, IsPeriodicKernel I I' T' → ∀ c c' : ℂ,
        IsPeriodicKernel I I' (kernelLinComb c c' T T') ∧
          ∀ x' x, periodization I I' (kernelLinComb c c' T T') s x' x =
            c * periodization I I' T s x' x + c' * periodization I I' T' s x' x) ∧
    ∀ x' x : I.Carrier, periodization I I (idKernel I) s x' x =
      if I.mkQuot s x' = I.mkQuot s x then 1 else 0
end TorusPeriodization
end YangMills.Construction.PeriodicOperators
end
