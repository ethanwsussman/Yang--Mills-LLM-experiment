import YangMills.Construction.ForwardTube.LightConeCoordinates
import Mathlib
set_option autoImplicit false
open ComplexConjugate
noncomputable section
namespace YangMills.Construction.ForwardTube
def closedForwardTube : Set (ℂ × ℂ) := {v | (lightConePlus v).re ≥ 0 ∧ (lightConeMinus v).re ≥ 0}
def conjPair (v : ℂ × ℂ) : ℂ × ℂ := (conj v.1, conj v.2)
def timeTranslate (s : ℝ) : ℂ × ℂ := ((s : ℂ), 0)
def shiftedTuples (A : Set (ℂ × ℂ)) (n : ℕ) (η : ℝ) : Set (Fin n → ℂ × ℂ) :=
  {x | (∀ h : 0 < n, x ⟨0, h⟩ - timeTranslate (η / 4) ∈ A) ∧
    ∀ (i : ℕ) (h : i + 1 < n), x ⟨i + 1, h⟩ - x ⟨i, by omega⟩ - timeTranslate (η / 2) ∈ A}
def shiftedForwardTube (n : ℕ) (η : ℝ) : Set (Fin n → ℂ × ℂ) := shiftedTuples forwardTube n η
def closedShiftedForwardTube (n : ℕ) (η : ℝ) : Set (Fin n → ℂ × ℂ) :=
  shiftedTuples closedForwardTube n η
theorem shiftedTuples_zero (A : Set (ℂ × ℂ)) (η : ℝ) (x : Fin 0 → ℂ × ℂ) :
    shiftedTuples A 0 η = {x} := by
  ext y
  simp only [shiftedTuples, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun _ => Subsingleton.elim _ _, fun _ => ⟨fun h => absurd h (lt_irrefl 0),
    fun i h => absurd h (by omega)⟩⟩
end YangMills.Construction.ForwardTube
