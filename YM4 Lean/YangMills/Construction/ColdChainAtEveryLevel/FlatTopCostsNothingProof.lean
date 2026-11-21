import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdChainAtEveryLevel.SizesAtAGoodCellProof
import YangMills.Construction.RunningCouplingSlope.CurvesOfFieldsAtOne
import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfTheGeneratorsProof
import YangMills.Construction.ColdChainAtEveryLevel.FlatTopCostsNothing
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace FlatTop
variable {F : BlockFrame}
theorem pathHolonomy_flatField {j : ℕ} (l : List PathStep) (x : F.Site j) :
    pathHolonomy (flatField F j) x l = 1 := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.pathHolonomy_one <;> assumption
theorem card_centredCube (M : ℕ) (hM : Odd M) : ((centredCube M).card : ℝ) = (M : ℝ) ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.card_centredCube_real <;> assumption
theorem contourAverage_flatField (hL : Odd F.blockSide) {j : ℕ} (c : F.Site (j + 1) × Fin 4) :
    contourAverage (flatField F j) c = 1 := by apply _root_.YangMills.Construction.BlockAverages.LowCostPatch.contourAverage_trivialField <;> assumption
theorem blockFit_flatField (hL : Odd F.blockSide) {j : ℕ} (c : F.Site (j + 1) × Fin 4) :
    blockFit (flatField F j) (flatField F (j + 1)) c = 0 := by
  unfold blockFit
  rw [contourAverage_flatField hL]
  simp [flatField]
theorem wilsonAction_flatField (S : Finset F.Cell) : wilsonAction S (flatField F 0) = 0 := by
  unfold wilsonAction plaquetteHolonomy
  simp [pathHolonomy_flatField]
theorem minimalAction_flatField (hV : minimalChainExistenceStatement) (a : ℝ) (ha : 0 ≤ a)
    (hL : Odd F.blockSide) (S : Finset F.Cell) : ∀ j, minimalAction a S j (flatField F j) = 0 := by
  obtain ⟨-, hn, hex, -⟩ := hV F a S ha
  intro j
  induction j with
  | zero => exact wilsonAction_flatField S
  | succ j ih =>
    apply le_antisymm _ (hn _ _)
    obtain ⟨W, hW, hmin⟩ := hex j (flatField F (j + 1))
    rw [← hW]
    refine (hmin (flatField F j)).trans (le_of_eq ?_)
    simp only [blockEnergy]
    rw [ih, Finset.sum_eq_zero fun c _ => blockFit_flatField hL c]
    simp
theorem cellShare_nonneg_and_le_chainAction (hV : minimalChainExistenceStatement) (a : ℝ)
    (ha : 0 ≤ a) (S : Finset F.Cell) (Y : F.Cell) (X : F.FieldChain) :
    0 ≤ cellShare a S Y X ∧ cellShare a S Y X ≤ chainAction a S X := by
  classical
  obtain ⟨hf, -, -, -⟩ := hV F a S ha
  have hre : ∀ p, 0 ≤ 1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re := by
    intro p
    have h1 : ‖((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ])‖ = 1 := by
      have := (Unitary.mem_iff.1 (plaquetteHolonomy (X 0) p).2).2
      have h2 : ‖((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ])‖ *
          ‖star ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ])‖ = 1 := by
        rw [← norm_mul, this, norm_one]
      rw [Quaternion.norm_star] at h2
      nlinarith [norm_nonneg ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ])]
    have h3 : ‖((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ])‖ ^ 2 =
        Quaternion.normSq ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]) := by
      rw [Quaternion.normSq_eq_norm_mul_self, sq]
    rw [h1, Quaternion.normSq_def'] at h3
    have : ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re ≤ 1 := by
      nlinarith [sq_nonneg ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).imI,
        sq_nonneg ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).imJ,
        sq_nonneg ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).imK,
        sq_nonneg (((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re - 1)]
    linarith
  have hcoef : ∀ p : F.Site 0 × Fin 4 × Fin 4,
      0 ≤ (∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0) ∧
      (∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0) ≤ 1 := by
    intro p
    constructor
    · exact Finset.sum_nonneg fun x _ => by split_ifs <;> norm_num
    · have hcard : (plaquetteCorners p).card ≤ 4 := Finset.card_le_four
      calc _ ≤ ∑ _x ∈ plaquetteCorners p, (1 / 4 : ℝ) :=
            Finset.sum_le_sum fun x _ => by split_ifs <;> norm_num
        _ = ((plaquetteCorners p).card : ℝ) * (1 / 4) := by simp
        _ ≤ 4 * (1 / 4) := by
            have : ((plaquetteCorners p).card : ℝ) ≤ 4 := by exact_mod_cast hcard
            gcongr
        _ = 1 := by norm_num
  have hc2 : ∀ (A B : Prop) [Decidable A] [Decidable B],
      0 ≤ (if A then (1 / 2 : ℝ) else 0) + (if B then (1 / 2 : ℝ) else 0) ∧
      (if A then (1 / 2 : ℝ) else 0) + (if B then (1 / 2 : ℝ) else 0) ≤ 1 := by
    intro A B _ _
    split_ifs <;> norm_num
  unfold cellShare chainAction wilsonAction
  constructor
  · apply add_nonneg
    · exact Finset.sum_nonneg fun p _ => mul_nonneg (hcoef p).1 (hre p)
    · apply mul_nonneg ha
      exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ =>
        mul_nonneg (hc2 _ _).1 (hf j _ _ c)
  · apply add_le_add
    · apply Finset.sum_le_sum
      intro p _
      have := mul_le_mul_of_nonneg_right (hcoef p).2 (hre p)
      linarith
    · apply mul_le_mul_of_nonneg_left _ ha
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro c _
      have := mul_le_mul_of_nonneg_right (hc2 (enclosingCell c.1 = Y)
        (enclosingCell (c.1 + unitStep (j + 1) c.2) = Y)).2 (hf j (X j) (X (j + 1)) c)
      linarith
end FlatTop
theorem flatTopVanishing (hV : minimalChainExistenceStatement) :
    flatTopVanishingStatement := by
  intro F a S ha hL
  have hleast := FlatTop.minimalAction_flatField hV a ha hL S
  refine ⟨?_, hleast, ?_⟩
  · intro j s hs p _
    unfold plaquetteDefect plaquetteHolonomy
    simp [FlatTop.pathHolonomy_flatField, hs]
  · intro Y
    classical
    obtain ⟨-, -, -, hch⟩ := hV F a S ha
    have hex : ∃ X, IsMinimalChain a S (flatField F F.top) X := by
      obtain ⟨X, hX, -⟩ := hch (flatField F F.top)
      exact ⟨X, hX⟩
    unfold minimalCellShare
    rw [dif_pos hex]
    set X := hex.choose
    have hX : IsMinimalChain a S (flatField F F.top) X := hex.choose_spec
    obtain ⟨X0, hX0, hT0⟩ := hch (flatField F F.top)
    have htot : chainAction a S X ≤ 0 := by
      rw [← hleast F.top, ← hT0]
      exact hX.2 X0 hX0.1
    obtain ⟨h1, h2⟩ := FlatTop.cellShare_nonneg_and_le_chainAction hV a ha S Y X
    linarith
end YangMills.Construction.BlockAverages
end
