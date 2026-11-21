import YangMills.Construction.ConfigurationSpace.DiagonalCutoffs
import YangMills.Construction.Continuum.WhitneyDyadicScales
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open MeasureTheory
variable {n : ℕ}
abbrev IntPoint (n : ℕ) : Type := CoordIndex n → ℤ
def translateSet (a : Config n) (S : Set (Config n)) : Set (Config n) := {y | ∃ x ∈ S, y = a + x}
def blockProd (j : ℕ) (z : IntPoint n) (x : Config n) : ℝ :=
  ∏ ι : CoordIndex n,
    YangMills.Construction.BumpFunctions.mollifiedUnitIndicator
      (2 * coords x ι / YangMills.Construction.WhitneyScales.whitneySide j - z ι)
def whitneyPiece (j : ℕ) (z : IntPoint n) (x : Config n) : ℝ :=
  shellDiff j x * blockProd j z x
def pieceCenter (j : ℕ) (z : IntPoint n) : Config n :=
  fun i c => 1 / 2 * YangMills.Construction.WhitneyScales.whitneySide j * z (toLex (i, c))
def pieceBox (j : ℕ) (z : IntPoint n) : Set (Config n) :=
  translateSet (pieceCenter j z)
    {x | ∀ ι, coords x ι ∈ Set.Ioo (-(1 / 2 * YangMills.Construction.WhitneyScales.whitneySide j))
      (1 / 2 * YangMills.Construction.WhitneyScales.whitneySide j)}
def pieceIndexSet (n : ℕ) : Set (ℕ × IntPoint n) :=
  {p | IsNonzeroSomewhere (whitneyPiece p.1 p.2)}
def closedCubeAt (a : Fin 4 → ℝ) (s : ℝ) : Set (Fin 4 → ℝ) :=
  {y | maxNorm (y - a) ≤ s / 2}
def innerCube (j : ℕ) (z : IntPoint n) (i : Fin n) : Set (Fin 4 → ℝ) :=
  closedCubeAt (pieceCenter j z i) (YangMills.Construction.WhitneyScales.whitneySide j)
def middleCube (j : ℕ) (z : IntPoint n) (i : Fin n) : Set (Fin 4 → ℝ) :=
  closedCubeAt (pieceCenter j z i) (3 / 2 * YangMills.Construction.WhitneyScales.whitneySide j)
def outerCube (j : ℕ) (z : IntPoint n) (i : Fin n) : Set (Fin 4 → ℝ) :=
  closedCubeAt (pieceCenter j z i) (2 * YangMills.Construction.WhitneyScales.whitneySide j)
def lebesgueVol (D : ℕ) : Measure (Fin D → ℝ) := volume
def unitBallVol : ℕ → ℝ
  | 0 => 1
  | D + 1 => (lebesgueVol (D + 1) {x | l2Norm x ≤ 1}).toReal
def setCard {α : Type*} (S : Set α) : ℕ∞ := S.encard
def choose2Real (n : ℕ) : ℝ := 1 / 2 * n * (n - 1)
theorem choose2Real_eq_card (n : ℕ) : choose2Real n = ((orderedPairs n).card : ℝ) := by
  have hswap : (Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1).card
      = (orderedPairs n).card := by
    refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro p hp
      simpa [orderedPairs] using hp
    · intro p _ q _ h
      simpa using h
    · intro p hp
      exact ⟨p.swap, by simpa [orderedPairs] using hp, by simp⟩
  have hsplit : ((Finset.univ : Finset (Fin n)).offDiag).card =
      (orderedPairs n).card + (Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext p
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, orderedPairs, Finset.mem_union,
        Finset.mem_filter]
      exact ne_iff_lt_or_gt
    · rw [Finset.disjoint_left]
      intro p hp hq
      simp only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      exact lt_asymm hp hq
  have hoff : ((Finset.univ : Finset (Fin n)).offDiag).card + n = n * n := by
    have h := Finset.diag_card (Finset.univ : Finset (Fin n))
    have h2 := Finset.diag_union_offDiag (Finset.univ : Finset (Fin n))
    have h3 := Finset.card_union_of_disjoint
      (Finset.disjoint_diag_offDiag (s := (Finset.univ : Finset (Fin n))))
    rw [h2, Finset.card_product] at h3
    simp only [Finset.card_univ, Fintype.card_fin] at h h3
    omega
  have hreal : (((orderedPairs n).card : ℝ)) * 2 + n = n * n := by
    rw [hswap] at hsplit
    have : (orderedPairs n).card * 2 + n = n * n := by omega
    exact_mod_cast this
  unfold choose2Real
  linarith
def pieceDerivConst : ℝ :=
  2 * max pairCutoffConst
    (2 * YangMills.Construction.BumpFunctions.blockConst *
      YangMills.Construction.WhitneyScales.whitneyRatio⁻¹)
def pieceDerivBound (n r : ℕ) : ℝ :=
  2 * YangMills.Construction.BumpFunctions.integralConstBound ^ (4 * n) *
    (pieceDerivConst * n) ^ r * (r.factorial : ℝ) ^ 2
def separationConst : ℝ := 4 + 2 * YangMills.Construction.WhitneyScales.whitneyRatio
def diagonalDistConst : ℝ := Real.sqrt 2 * separationConst
def countingVolConst : ℝ :=
  (2 * separationConst) ^ 4 * (2 / YangMills.Construction.WhitneyScales.whitneyRatio) ^ 4
def pieceCountConst (n : ℕ) : ℝ :=
  countingVolConst ^ n * (1 + Real.sqrt n) ^ (4 * n) *
    max (choose2Real n * unitBallVol (4 * n - 4)) (unitBallVol (4 * n))
end YangMills.Construction.ConfigurationSpace
end
