import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.TransferOperatorWithAnInsertion
import YangMills.Construction.ReflectionPositivity.AxisMirrorData
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def IsConjClosedSubalgebra (t : halfSpacingTimes a) : Prop :=
  (∀ c : ℂ, (fun _ => c : GaugeField a → ℂ) ∈ upperAlgebra t) ∧
  (∀ A ∈ upperAlgebra t, ∀ A' ∈ upperAlgebra t, A + A' ∈ upperAlgebra t) ∧
  (∀ c : ℂ, ∀ A ∈ upperAlgebra t, c • A ∈ upperAlgebra t) ∧
  (∀ A ∈ upperAlgebra t, ∀ A' ∈ upperAlgebra t, A * A' ∈ upperAlgebra t) ∧
  ∀ A ∈ upperAlgebra t, (fun U => conj (A U)) ∈ upperAlgebra t
def ReflectionPairingIsPosHermitian (μ : Measure (GaugeField a)) (t : halfSpacingTimes a) :
    Prop :=
  (∀ B ∈ upperAlgebra t, ∀ A ∈ upperAlgebra t, ∀ A' ∈ upperAlgebra t, ∀ c c' : ℂ,
    reflectionPairing μ t B (c • A + c' • A') =
      c * reflectionPairing μ t B A + c' * reflectionPairing μ t B A') ∧
  (∀ B ∈ upperAlgebra t, ∀ B' ∈ upperAlgebra t, ∀ A ∈ upperAlgebra t, ∀ c c' : ℂ,
    reflectionPairing μ t (c • B + c' • B') A =
      conj c * reflectionPairing μ t B A + conj c' * reflectionPairing μ t B' A) ∧
  (∀ B ∈ upperAlgebra t, ∀ A ∈ upperAlgebra t,
    conj (reflectionPairing μ t B A) = reflectionPairing μ t A B) ∧
  ∀ A ∈ upperAlgebra t,
    (reflectionPairing μ t A A).im = 0 ∧ 0 ≤ (reflectionPairing μ t A A).re
def ReflectionSeminormEstimates (μ : Measure (GaugeField a)) (t : halfSpacingTimes a) : Prop :=
  (∀ B ∈ upperAlgebra t, ∀ A ∈ upperAlgebra t,
    ‖reflectionPairing μ t B A‖ ≤ reflectionPairingRoot μ t B * reflectionPairingRoot μ t A) ∧
  (∀ A ∈ upperAlgebra t, reflectionPairingRoot μ t A ≤ ⨆ U, ‖A U‖) ∧
  reflectionPairingRoot μ t (fun _ => 1) = 1
def InsertMulIsLinearEndo (t : halfSpacingTimes a)
    (u : positiveMultiples a) (E : GaugeField a → ℂ) : Prop :=
  (∀ A ∈ upperAlgebra t, insertMul u E A ∈ upperAlgebra t) ∧
  ∀ A ∈ upperAlgebra t, ∀ A' ∈ upperAlgebra t, ∀ c c' : ℂ,
    insertMul u E (c • A + c' • A') = c • insertMul u E A + c' • insertMul u E A'
def InsertMulAdjoint (μ : Measure (GaugeField a)) (t : halfSpacingTimes a)
    (u : positiveMultiples a) (D : GaugeField a → ℂ) : Prop :=
  IsSlabLocalized t u (reflectedInsert t u D) ∧
  reflectedInsert t u (reflectedInsert t u D) = D ∧
  InsertMulIsLinearEndo t u D ∧
  InsertMulIsLinearEndo t u (reflectedInsert t u D) ∧
  ∀ A ∈ upperAlgebra t, ∀ B ∈ upperAlgebra t,
    reflectionPairing μ t B (insertMul u D A) =
      reflectionPairing μ t (insertMul u (reflectedInsert t u D) B) A
def ReflectionMomentsLogConvex (μ : Measure (GaugeField a))
    (t : halfSpacingTimes a) (u : positiveMultiples a) (D A : GaugeField a → ℂ) : Prop :=
  (∀ n : ℕ, (reflectionMoment μ t u D A n).im = 0 ∧ 0 ≤ (reflectionMoment μ t u D A n).re) ∧
  reflectionMoment μ t u D A 0 = ((reflectionPairingRoot μ t A ^ 2 : ℝ) : ℂ) ∧
  reflectionMoment μ t u D A 1 = ((reflectionPairingRoot μ t (insertMul u D A) ^ 2 : ℝ) : ℂ) ∧
  ∀ n : ℕ, 1 ≤ n →
    (reflectionMoment μ t u D A n).re ^ 2 ≤
      (reflectionMoment μ t u D A (n - 1)).re * (reflectionMoment μ t u D A (n + 1)).re ∧
    (reflectionMoment μ t u D A 1).re ^ n ≤
      (reflectionMoment μ t u D A 0).re ^ (n - 1) * (reflectionMoment μ t u D A n).re ∧
    (insertedTransfer t u D)^[n] A =
      (∏ i ∈ Finset.Icc 1 (2 * n), insertSeq t u D i) *
        (shift ((2 * (n : ℤ)) • timeStep u)).actOn A
def PeriodicGibbsReflectionTransfer : Prop :=
  ∀ d : ReflectionPositivity.AxisMirror.MirrorData, ∀ μ : Measure (GaugeField d.mesh),
    μ ∈ periodicGibbsSet d.L d.K d.β → ∀ t : halfSpacingTimes d.mesh,
      IsConjClosedSubalgebra t ∧
      ReflectionPairingIsPosHermitian μ t ∧
      ReflectionSeminormEstimates μ t ∧
      ∀ u : positiveMultiples d.mesh, ∀ D : GaugeField d.mesh → ℂ, IsSlabLocalized t u D →
        InsertMulAdjoint μ t u D ∧
        ∀ A ∈ upperAlgebra t, ReflectionMomentsLogConvex μ t u D A
end YangMills.Construction.InfiniteLattice
