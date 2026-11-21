import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
def expHalfTerm (c : ℝ) (m : ℤ) : ℝ := Real.exp (-c * |(m : ℝ)| / 2)
def expHalfSum (c : ℝ) : ℝ := ∑' m : ℤ, expHalfTerm c m
def ExponentialSums.Bounds : Prop :=
  ∀ c : ℝ, 0 < c →
    Summable (expHalfTerm c) ∧
    (∀ y : AmbientSpace,
      Summable (fun n : Fin 4 → ℤ => Real.exp (-c * euclidNormVec (y + castVec n))) ∧
      ∑' n : Fin 4 → ℤ, Real.exp (-c * euclidNormVec (y + castVec n)) ≤
        Real.exp (2 * c) * expHalfSum c ^ 4) ∧
    (∀ I : PeriodicData, IsPeriodic I → ∀ y : AmbientSpace,
      Summable (fun ι : I.Carrier => Real.exp (-c * euclidNormVec (I.pos ι - y))) ∧
      ∑' ι : I.Carrier, Real.exp (-c * euclidNormVec (I.pos ι - y)) ≤
        (Nat.card I.UnitQuot : ℝ) * (Real.exp (2 * c) * expHalfSum c ^ 4))
end PeriodicOperators
end YangMills.Construction
end
