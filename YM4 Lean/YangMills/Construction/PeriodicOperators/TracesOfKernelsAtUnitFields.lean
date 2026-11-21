import YangMills.Construction.PeriodicOperators.MatricesOfTheCoefficientsOnATorus
import YangMills.Construction.PeriodicOperators.SecondDifferentialsOfLogarithmsOfDeterminants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.UnitFieldTraces
variable (F I : PeriodicData)
open Classical in
def siteIndicator (x : F.Carrier) : F.Carrier → ℂ := fun y => if y = x then 1 else 0
open Classical in
def quotIndicator (n : ℕ) (x : F.Carrier) : F.QuotMod n → ℂ :=
  fun q => if q = F.mkQuot n x then 1 else 0
variable {F I} in
def diagSum {J : Type} (A : J → J → ℂ) : ℂ := ∑' j, A j j
def quotTraceDefect (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (n : ℕ)
    (u v : F.QuotMod n → ℂ) : ℂ :=
  LinearMap.trace ℂ (I.QuotMod n → ℂ)
      (Ring.inverse (LogDetSecondDerivs.quotOperator F I T n 0) * periodicCoeffTwoMatrix F I T n u v) -
    LinearMap.trace ℂ (I.QuotMod n → ℂ)
      (Ring.inverse (LogDetSecondDerivs.quotOperator F I T n 0) * periodicCoeffOneMatrix F I T n u *
        Ring.inverse (LogDetSecondDerivs.quotOperator F I T n 0) * periodicCoeffOneMatrix F I T n v)
def kernelTraceDefect (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) (R : I.Carrier → I.Carrier → ℂ)
    (u v : F.Carrier → ℂ) : ℂ :=
  diagSum (compKernel R (coeffTwo F I I T u v)) -
    diagSum (compKernel (compKernel R (coeffOne F I I T u))
      (compKernel R (coeffOne F I I T v)))
end YangMills.Construction.PeriodicOperators.UnitFieldTraces
end
