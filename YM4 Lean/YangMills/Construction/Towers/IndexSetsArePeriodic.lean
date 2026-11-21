import YangMills.Construction.Towers.PeriodicExtensionsLocalKernelsAndKernelsThatDescend
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels
open YangMills.Construction.PeriodicOperators (IsPeriodic)
namespace IndexSetPeriodicity
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    (∀ P : Component k, IsPeriodic (P.toPeriodicData L)) ∧
    ∀ I : WeightedIndexSet k, IsPeriodic (I.toPeriodicData L) ∧
      ∃ e : I.Slot ≃ (I.toPeriodicData L).Component,
        (∀ a : (I.toPeriodicData L).Carrier, (I.toPeriodicData L).componentOf a = e a.1) ∧
        ∀ p : I.Slot, (I.toPeriodicData L).weight (e p) = (I.comp p).weight
end IndexSetPeriodicity
end YangMills.Construction.LocalKernels
end
