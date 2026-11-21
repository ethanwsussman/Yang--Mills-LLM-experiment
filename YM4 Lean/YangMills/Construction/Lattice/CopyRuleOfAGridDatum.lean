import YangMills.Construction.Lattice.ChessboardCopiesOfAGridDatum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GridCopyRule
variable {L : ℕ} {κ : ℤ}
def CopyLaw (g : CellGrid L κ) (c c' : g.spaceCells) (F : g.cellObservables c)
    (h : g.Space → g.Space) : Prop :=
  ∀ c'' : g.spaceCells, c''.1 = h '' c'.1 →
    (g.inducedSign h = 1 →
      g.checkerboardCopy c c'' F =
        (g.symmetryOfMap h).actOnObservables (g.checkerboardCopy c c' F)) ∧
    (g.inducedSign h = -1 →
      g.checkerboardCopy c c'' F =
        fun U => starRingEnd ℂ
          ((g.symmetryOfMap h).actOnObservables (g.checkerboardCopy c c' F) U))
def ReflectedCopyLaw (g : CellGrid L κ) (c c' : g.spaceCells) (F : g.cellObservables c)
    (θ : g.Space → g.Space) : Prop :=
  ∀ c'' : g.spaceCells, c''.1 = θ '' c'.1 →
    (fun U => starRingEnd ℂ
        ((g.symmetryOfMap θ).actOnObservables (g.checkerboardCopy c c' F) U)) =
      g.checkerboardCopy c c'' F
def CopyRuleHolds : Prop :=
  ∀ (L : ℕ) (κ : ℤ) (g : CellGrid L κ) (c c' : g.spaceCells) (F : g.cellObservables c),
    ∃ hF : g.checkerboardCopy c c' F ∈ g.cellObservables c',
      (∀ h ∈ g.inducedGroupMaps, CopyLaw g c c' F h) ∧
      g.checkerboardCopy c c F = F.1 ∧
      (∀ c'' : g.spaceCells,
        g.checkerboardCopy c' c'' ⟨g.checkerboardCopy c c' F, hF⟩ = g.checkerboardCopy c c'' F) ∧
      ∀ θ ∈ g.inducedReflections, ReflectedCopyLaw g c c' F θ
end YangMills.Construction.GridCopyRule
end
