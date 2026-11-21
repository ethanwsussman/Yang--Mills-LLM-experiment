import YangMills.Construction.ChessboardTori.TransferPicture
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
abbrev MatrixWord : Type := List (Fin 2 × Fin 2)
def wordMonomial (γ : MatrixWord) (u : Conventions.StandingParameters.gaugeGroup) : ℂ :=
  (γ.map fun p => (u : Matrices.ComplexMatrix2) p.1 p.2).prod
def poissonWeight (D : ChessboardSetup) (s : ℕ) : ℝ :=
  Real.exp (-D.β) * (D.β / 2) ^ s / (s.factorial : ℝ)
theorem poissonWeight_pos (D : ChessboardSetup) (s : ℕ) : 0 < poissonWeight D s := by
  have hβ := D.beta_pos
  unfold poissonWeight
  positivity
namespace TransferSetup
variable {D : ChessboardSetup} (T : TransferSetup D)
def transferKernel (ξ ξ' : T.EdgeField) : ℂ :=
  ∫ V, ∏ e : T.PositiveTransverseEdge, boltzmannFactor D (T.axialHolonomy ξ ξ' V e) ∂T.siteHaar
abbrev WordIndex : Type := T.PositiveTransverseEdge → MatrixWord
def indexMonomial (α : T.WordIndex) (ξ : T.EdgeField) : ℂ :=
  ∏ e : T.PositiveTransverseEdge, wordMonomial (α e) (ξ e)
def indexWeight (α : T.WordIndex) : ℝ :=
  ∏ e : T.PositiveTransverseEdge, poissonWeight D (α e).length
theorem indexWeight_pos (α : T.WordIndex) : 0 < T.indexWeight α :=
  Finset.prod_pos fun _ _ => poissonWeight_pos D _
def gaugeAct (V : T.SiteField) (ξ : T.EdgeField) : T.EdgeField :=
  fun e => V e.1.source * ξ e * (V e.1.target)⁻¹
def averagedMonomial (α : T.WordIndex) (ξ : T.EdgeField) : ℂ :=
  ∫ V, T.indexMonomial α (T.gaugeAct V ξ) ∂T.siteHaar
def normalizedMonomial (α : T.WordIndex) (ξ : T.EdgeField) : ℂ :=
  (Real.sqrt (T.indexWeight α) : ℂ) * T.averagedMonomial α ξ
def slabFirst (η : T.SlabConfig) : T.EdgeField :=
  η.1 ⟨0, by have := T.two_le_ratioNat; omega⟩
def slabLast (η : T.SlabConfig) : T.EdgeField :=
  η.1 ⟨T.ratioNat - 1, by have := T.two_le_ratioNat; omega⟩
def slabKernelMatrix (Φ : T.SlabConfig → ℂ) (α α' : T.WordIndex) : ℂ :=
  ∫ η, T.normalizedMonomial α (T.slabFirst η) * Φ η *
    starRingEnd ℂ (T.normalizedMonomial α' (T.slabLast η)) ∂T.slabHaar
end TransferSetup
end YangMills.Construction.ChessboardTori
end
