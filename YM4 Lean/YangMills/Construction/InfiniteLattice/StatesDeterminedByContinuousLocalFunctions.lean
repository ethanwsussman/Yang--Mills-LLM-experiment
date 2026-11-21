import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
theorem mem_continuousCylinderFunctions_iff {F : GaugeField a → ℂ} :
    F ∈ continuousCylinderFunctions a ↔
      Continuous F ∧ ∃ S : Set (Link a), S.Finite ∧ DependsOnlyOnLinks S F := by
  classical
  constructor
  · rintro ⟨hc, W, hW, -, hF⟩
    exact ⟨hc, W, hW, hF⟩
  · rintro ⟨hc, S, hS, hF⟩
    let p : Link a → Link a := fun b =>
      if b ∈ positiveLinkSet a then b else b.opposite
    refine ⟨hc, p '' S, hS.image p, ?_, fun U U' hUU => hF U U' ?_⟩
    · rintro _ ⟨b, -, rfl⟩
      by_cases hb : b ∈ positiveLinkSet a
      · simp [p, hb]
      · have hr := (mem_positiveLinks_or_opposite_mem b).resolve_left hb
        simpa [p, hb] using hr
    · funext b
      have hbp := congrFun hUU ⟨p b, mem_image_of_mem p b.2⟩
      change U (p b) = U' (p b) at hbp
      change U b = U' b
      by_cases hb : (b : Link a) ∈ positiveLinkSet a
      · simpa [p, hb] using hbp
      · have hr : U (b : Link a).opposite = U' (b : Link a).opposite := by
          simpa [p, hb] using hbp
        rw [U.2 b, U'.2 b] at hr
        exact inv_injective hr
def StatesDeterminedOnCylinderFunctions (a : ℝ) : Prop :=
  ∀ ν ν' : GaugeFieldProbability a,
    (∀ F ∈ continuousCylinderFunctions a, ν.expect F = ν'.expect F) → ν = ν'
def SymmetriesActOnCylinderFunctions (a : ℝ) : Prop :=
  ∀ s : LatticeSymmetry a,
    (∀ F : GaugeField a → ℂ, Continuous F → Continuous (s.actOn F)) ∧
    (∀ F ∈ continuousCylinderFunctions a, s.actOn F ∈ continuousCylinderFunctions a) ∧
    ∀ ν : GaugeFieldProbability a,
      (∀ F ∈ continuousCylinderFunctions a, ν.expect (s.actOn F) = ν.expect F) →
        IsSymmetricUnder ν.1 s
def CylinderFunctionsDetermineStates.Statement : Prop :=
  ∀ L K : ℕ, Odd L → 13 ≤ L → 0 < K →
    StatesDeterminedOnCylinderFunctions (PeriodicLattice.meshSize L (K : ℤ)) ∧
    SymmetriesActOnCylinderFunctions (PeriodicLattice.meshSize L (K : ℤ)) ∧
    CompactSpace (GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)))
end YangMills.Construction.InfiniteLattice
