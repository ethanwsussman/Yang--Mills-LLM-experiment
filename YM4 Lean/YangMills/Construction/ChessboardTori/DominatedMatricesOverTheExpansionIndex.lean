import YangMills.Construction.ChessboardTori.CrossingKernelAndItsExpansionFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori.TransferSetup
variable {D : ChessboardSetup} (T : TransferSetup D)
abbrev WordMatrix : Type := T.WordIndex → T.WordIndex → ℂ
def weightedEntry (X : T.WordMatrix) (p : T.WordIndex × T.WordIndex) : ℝ :=
  (T.indexWeight p.1 * T.indexWeight p.2) ^ (-(1 / 2) : ℝ) * ‖X p.1 p.2‖
def IsDominated (X : T.WordMatrix) : Prop :=
  BddAbove (Set.range (T.weightedEntry X))
def dominationNorm (X : T.WordMatrix) : ℝ :=
  ⨆ p, T.weightedEntry X p
def wordMul (X Y : T.WordMatrix) : T.WordMatrix :=
  fun a c => ∑' b, X a b * Y b c
def diagonalTrace (X : T.WordMatrix) : ℂ :=
  ∑' a, X a a
def foldProduct : {n : ℕ} → (Fin (n + 1) → T.WordMatrix) → T.WordMatrix
  | 0, X => X 0
  | _ + 1, X => T.wordMul (foldProduct fun i => X i.castSucc) (X (Fin.last _))
def matrixPower (X : T.WordMatrix) (j : ℕ) : T.WordMatrix :=
  T.foldProduct (n := j - 1) fun _ => X
theorem slabKernelMatrix_eq_integral (Φ : T.SlabConfig → ℂ) (a b : T.WordIndex) :
    T.slabKernelMatrix Φ a b =
      (Real.sqrt (T.indexWeight a * T.indexWeight b) : ℂ) *
        ∫ η, T.averagedMonomial a (T.slabFirst η) * Φ η *
          starRingEnd ℂ (T.averagedMonomial b (T.slabLast η)) ∂T.slabHaar := by
  rw [Real.sqrt_mul (T.indexWeight_pos a).le, ← integral_const_mul]
  unfold slabKernelMatrix normalizedMonomial
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring
end YangMills.Construction.ChessboardTori.TransferSetup
end
