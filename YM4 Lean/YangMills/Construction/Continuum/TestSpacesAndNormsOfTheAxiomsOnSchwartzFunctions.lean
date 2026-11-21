import YangMills.Construction.Continuum.ArgumentsOfTheConditionsLieInTheirDomainsAndTheirSumsAreFiniteProof
import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.Continuum.TimeAxisAndTheReflectionOfTime
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.SchwartzAxioms
def timeUnitVector : Fin 4 → ℝ := Pi.single TimeAxis.timeIdx 1
section Spaces
variable {n : ℕ}
def positiveTimeSchwartz (n : ℕ) : Set (TestSpaces.PointTuple n → ℂ) :=
  {φ | φ ∈ TestSpaces.schwartzSet n ∧
    TestSpaces.VanishesToInfiniteOrderOff φ (TestSpaces.positiveTimeLocus n)}
def negativeTimeSchwartz (n : ℕ) : Set (TestSpaces.PointTuple n → ℂ) :=
  {φ | φ ∈ TestSpaces.schwartzSet n ∧
    TestSpaces.VanishesToInfiniteOrderOff φ (TestSpaces.negativeTimeLocus n)}
theorem vanishesToInfiniteOrderOff_iff_flatOff {φ : TestSpaces.PointTuple n → ℂ}
    {U : Set (TestSpaces.PointTuple n)} :
    TestSpaces.VanishesToInfiniteOrderOff φ U ↔ ConfigSpace.FlatOff φ U :=
  ⟨fun ⟨hs, hU, h⟩ => ⟨hs, hU, fun x hx => ⟨hs, (h x hx).2.2⟩⟩,
    fun ⟨hs, hU, h⟩ => ⟨hs, hU, fun x hx => ⟨hs, (h x hx).eq_zero, (h x hx).2⟩⟩⟩
theorem mem_schwartzSet_iff_isSchwartz {φ : TestSpaces.PointTuple n → ℂ} :
    φ ∈ TestSpaces.schwartzSet n ↔ ConfigSpace.IsSchwartz φ :=
  Iff.rfl
theorem positiveTimeSchwartz_eq :
    positiveTimeSchwartz n = ConfigSpace.schwartzFlatOffPosTime n := by
  ext φ
  exact and_congr mem_schwartzSet_iff_isSchwartz vanishesToInfiniteOrderOff_iff_flatOff
theorem flatSchwartzSet_eq :
    TestSpaces.flatSchwartzSet n = ConfigSpace.schwartzFlatOffDiagonal n := by apply _root_.YangMills.Construction.ConfigSpace.DomainsAndFiniteSums.flatSchwartzSet_eq_schwartzFlatOffDiagonal <;> assumption
def seminormAt (k : ℕ) : {n : ℕ} → ConfigSpace.FnOrScalar n → ℝ≥0∞
  | 0, c => ENNReal.ofReal ‖(show ℂ from c)‖
  | _ + 1, φ => TestSpaces.weightedSeminorm k φ
def IsContinuousOnFlat (T : TestSpaces.flatSchwartzSet n → ℂ) : Prop :=
  TestSpaces.IsCLinearOnFlat T ∧ TestSpaces.IsWeightedBounded T
theorem isContinuousOnFlat_iff (T : TestSpaces.flatSchwartzSet n → ℂ) :
    IsContinuousOnFlat T ↔ ConfigSpace.IsContLinearOnFlat
      fun φ => T ⟨φ.1, flatSchwartzSet_eq.symm ▸ φ.2⟩ := by
  have key : ∀ (k : ℕ) (c : ℝ), 0 < k → 0 ≤ c → ∀ (φ : TestSpaces.flatSchwartzSet n),
      (ENNReal.ofReal ‖T φ‖ ≤ ENNReal.ofReal c * TestSpaces.weightedSeminorm k φ.1 ↔
        ‖T φ‖ ≤ c * (TestSpaces.weightedSeminorm k φ.1).toReal) := by
    intro k c hk hc φ
    have hfin : TestSpaces.weightedSeminorm k φ.1 ≠ ⊤ := (φ.2.1.2 k hk).ne
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hc, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc ENNReal.toReal_nonneg)
  constructor
  · rintro ⟨hl, k, c, hk, hc, hb⟩
    exact ⟨fun a b φ ψ χ h => hl a b _ _ _ h, k, c, hk, hc,
      fun φ => (key k c hk hc ⟨φ.1, flatSchwartzSet_eq.symm ▸ φ.2⟩).1 (hb _)⟩
  · rintro ⟨hl, k, c, hk, hc, hb⟩
    refine ⟨fun a b φ ψ χ h => ?_, k, c, hk, hc, fun φ => (key k c hk hc φ).2 ?_⟩
    · exact hl a b ⟨φ.1, flatSchwartzSet_eq ▸ φ.2⟩ ⟨ψ.1, flatSchwartzSet_eq ▸ ψ.2⟩
        ⟨χ.1, flatSchwartzSet_eq ▸ χ.2⟩ h
    · exact hb ⟨φ.1, flatSchwartzSet_eq ▸ φ.2⟩
end Spaces
end YangMills.Construction.SchwartzAxioms
end
