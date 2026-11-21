import YangMills.Construction.InfiniteLattice.HalfSpaceAlgebraAndReflectionForm
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def positiveMultiples (a : ℝ) : Set ℝ := {u | ∃ n : ℕ, 0 < n ∧ u = (n : ℝ) * a}
def timeStep (u : positiveMultiples a) : LatticePoint a :=
  ⟨Pi.single timeAxis (u : ℝ), by
    obtain ⟨n, -, hn⟩ := u.2
    refine ⟨Pi.single timeAxis (n : ℤ), fun k => ?_⟩
    by_cases h : k = timeAxis
    · subst h
      simp [hn]
    · simp [Pi.single_eq_of_ne h]⟩
def midpointTime (t : halfSpacingTimes a) (u : positiveMultiples a) : halfSpacingTimes a :=
  ⟨(t : ℝ) + (u : ℝ) / 2, by
    obtain ⟨q, hq⟩ := t.2
    obtain ⟨n, -, hn⟩ := u.2
    refine ⟨q + n, ?_⟩
    rw [hq, hn]
    push_cast
    ring⟩
def openSlab (t u : ℝ) : Set AmbientSpace := {x | t < x timeAxis ∧ x timeAxis < t + u}
def IsSlabLocalized (t : halfSpacingTimes a) (u : positiveMultiples a)
    (D : GaugeField a → ℂ) : Prop :=
  IsBoundedlyLocalizedIn (openSlab t u) D
def insertMul (u : positiveMultiples a) (D A : GaugeField a → ℂ) :
    GaugeField a → ℂ :=
  fun U => D U * (shift (timeStep u)).actOn A U
def reflectedInsert (t : halfSpacingTimes a) (u : positiveMultiples a)
    (D : GaugeField a → ℂ) : GaugeField a → ℂ :=
  fun U => conj ((timeReflect (midpointTime t u)).actOn D U)
def insertSeq (t : halfSpacingTimes a) (u : positiveMultiples a)
    (D : GaugeField a → ℂ) (i : ℕ) : GaugeField a → ℂ :=
  (shift (((i : ℤ) - 1) • timeStep u)).actOn
    (if Odd i then reflectedInsert t u D else D)
def insertedTransfer (t : halfSpacingTimes a) (u : positiveMultiples a)
    (D A : GaugeField a → ℂ) : GaugeField a → ℂ :=
  insertMul u (reflectedInsert t u D) (insertMul u D A)
def reflectionMoment (μ : MeasureTheory.Measure (GaugeField a)) (t : halfSpacingTimes a)
    (u : positiveMultiples a) (D A : GaugeField a → ℂ) (n : ℕ) : ℂ :=
  reflectionPairing μ t A ((insertedTransfer t u D)^[n] A)
end InfiniteLattice
end YangMills.Construction
