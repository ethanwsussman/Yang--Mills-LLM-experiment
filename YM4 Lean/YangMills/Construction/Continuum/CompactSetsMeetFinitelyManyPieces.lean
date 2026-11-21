import YangMills.Construction.Continuum.PiecesOfTheShellsTheirCubesAndNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PieceFiniteness
open ConfigSpace ShellPieces
variable {n : ℕ}
def pieceMul (p : ℕ × LatticePt n) (Ψ : Config n → ℂ) : Config n → ℂ :=
  fun x => (piece p.1 p.2 x : ℂ) * Ψ x
def meetingPieces (S : Set (Config n)) : Set (ℕ × LatticePt n) :=
  {p | p ∈ activeIndices n ∧ ∃ x ∈ S, piece p.1 p.2 x ≠ 0}
def supportPieces (Ψ : Config n → ℂ) : Set (ℕ × LatticePt n) :=
  {p | p ∈ activeIndices n ∧ pieceMul p Ψ ≠ 0}
def CompactMeetsFinitelyMany : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ S : Set (Config n), S ⊆ TestFunctions.injectiveTuples (Fin 4 → ℝ) n → IsCompact S →
      (meetingPieces S).Finite) ∧
    ∀ Ψ ∈ testFnOffDiag n,
      ∃ h : (supportPieces Ψ).Finite, Ψ = ∑ p ∈ h.toFinset, pieceMul p Ψ
end YangMills.Construction.PieceFiniteness
end
