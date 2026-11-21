import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.JointSmoothnessFromMoves
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheGapAboveTheFramesProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Estimates
namespace ExpansionAboveFrame
variable {F : BlockAverages.BlockFrame} {s a ρA : ℝ} {m : ℕ} {V : F.GaugeField F.top}
def perturbationsOf {l k : ℕ}
    (b : Fin l → ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → BlockAverages.imaginaryQuaternions) :
    Fin (l + k) → Perturbation F :=
  Fin.addCases (fun i => Perturbation.bulk (b i) (u i)) (fun i => Perturbation.top (c i) (X i))
theorem perturbationsOf_isUnit {l k : ℕ}
    (b : Fin l → ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → BlockAverages.imaginaryQuaternions)
    (hu : ∀ i, ‖u i‖ = 1) (hX : BlockAverages.AreUnitVectors X) :
    ∀ i, (perturbationsOf b u c X i).IsUnit := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [perturbationsOf, Fin.addCases_left, Perturbation.IsUnit]
    exact hu i
  · simp only [perturbationsOf, Fin.addCases_right, Perturbation.IsUnit]
    exact hX i
theorem jointDisplacement_interpolatedExpansion_eq {l k : ℕ} (h : ColdStepAtMirrorFrames.LocalFamily)
    (y : F.Site F.depth) (η : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells F))
    (b : Fin l → ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → BlockAverages.imaginaryQuaternions) :
    Interpolation.jointDisplacement (fun ζ W => Interpolation.interpolatedExpansion s a ρA m h y ζ W) η V b u c X =
      fun τ => ColdStepAtMirrorFrames.subtractTrivial h F y
        (perturbedField s a ρA m V η (perturbationsOf b u c X) τ) := by
  classical
  funext τ
  have hVar : perturbedVariable η (perturbationsOf b u c X) τ =
      Interpolation.displacedPoint η b u fun i => τ (Fin.castAdd k i) := by
    unfold perturbedVariable Interpolation.displacedPoint
    congr 1
    rw [Fin.sum_univ_add]
    simp only [perturbationsOf, Fin.addCases_left, Fin.addCases_right, Perturbation.variableDirection,
      smul_zero, Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ => (Pi.single_smul _ _ _).symm
  have hTop : perturbedTop V (perturbationsOf b u c X) τ =
      ColdStepAtMirrorFrames.leftTranslate
        (ColdStepAtMirrorFrames.bondSpread c X fun i => τ (Fin.natAdd l i)) V := by
    unfold perturbedTop
    congr 1
    funext z i
    simp only [ColdStepAtMirrorFrames.bondSpread]
    rw [Fin.sum_univ_add]
    simp only [perturbationsOf, Fin.addCases_left, Fin.addCases_right, Perturbation.topBond,
      Perturbation.topDirection, smul_zero, ite_self, Finset.sum_const_zero, zero_add]
  simp only [Interpolation.jointDisplacement, Interpolation.interpolatedExpansion, perturbedField, hVar, hTop]
theorem cellSetDiameter_mono {P Q : Finset F.Cell} (h : P ⊆ Q) :
    Interpolation.cellSetDiameter P ≤ Interpolation.cellSetDiameter Q := by apply _root_.YangMills.SharedProofs.p30422 <;> assumption
theorem insert_cells_subset {l k : ℕ} (y : F.Cell)
    (b : Fin l → ↥(BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → BlockAverages.imaginaryQuaternions) :
    insert y (Interpolation.chordBondCells b ∪ Interpolation.topBondCells c) ⊆
      insert y (perturbationCells (perturbationsOf b u c X)) := by
  classical
  refine Finset.insert_subset_insert _ fun v hv => ?_
  rcases Finset.mem_union.1 hv with h | h
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
    exact Finset.mem_image.2 ⟨Fin.castAdd k i, Finset.mem_univ _, by simp [perturbationsOf, Perturbation.cell]⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
    exact Finset.mem_image.2 ⟨Fin.natAdd l i, Finset.mem_univ _, by simp [perturbationsOf, Perturbation.cell]⟩
end ExpansionAboveFrame
open ExpansionAboveFrame in
theorem expansionAboveFrame (hBound : boundAlongPerturbationsStatement)
    (hSmooth : JointlyContDiffOnBallsOfDisplacements) : expansionAboveFrameStatement := by
  intro K r κ L hK hκ hr hL hL40
  obtain ⟨C, hC, hB⟩ := hBound K r κ L hK hκ hr hL hL40
  refine ⟨C, hC, ?_⟩
  intro F n₀ m σ s a ρA ρ e f V y hFL hcub hlow he hHas hcold habove han hdec
  refine ⟨hSmooth F ρ V _ fun η hη l j b u c X hu hX => ?_, fun η l k b u c X hη hu hX h1 h3 => ?_⟩
  · rw [jointDisplacement_interpolatedExpansion_eq f y η b u c X]
    exact (hB F n₀ 3 (l + j) m σ s a ρA e f V η (perturbationsOf b u c X) y hFL hcub hlow (by norm_num) he hHas
      (hcold η hη) (habove η hη) han hdec (perturbationsOf_isUnit b u c X hu hX)).1
  · have hb := (hB F n₀ 3 (l + k) m σ s a ρA e f V η (perturbationsOf b u c X) y hFL hcub hlow (by norm_num) he
      hHas (hcold η hη) (habove η hη) han hdec (perturbationsOf_isUnit b u c X hu hX)).2 h1 h3
    have hDeriv : Interpolation.jointMixedDeriv
        (fun ζ W => Interpolation.interpolatedExpansion s a ρA m f y ζ W) η V b u c X =
        iteratedFDeriv ℝ (l + k) (fun τ => ColdStepAtMirrorFrames.subtractTrivial f F y
          (perturbedField s a ρA m V η (perturbationsOf b u c X) τ)) 0
          fun l => Pi.single l 1 := by
      unfold Interpolation.jointMixedDeriv
      rw [jointDisplacement_interpolatedExpansion_eq f y η b u c X]
    rw [hDeriv]
    refine hb.trans ?_
    have hs : (Interpolation.cellSetDiameter (insert (BlockAverages.enclosingCell y)
        (Interpolation.chordBondCells b ∪ Interpolation.topBondCells c)) : ℝ) ≤
        Interpolation.cellSetDiameter (insert (BlockAverages.enclosingCell y)
          (perturbationCells (perturbationsOf b u c X))) := by
      exact_mod_cast cellSetDiameter_mono (insert_cells_subset (BlockAverages.enclosingCell y) b u c X)
    have hle : 0 ≤ C * Interpolation.runningMax e (l + k) := by
      have h0 : ∀ n, 0 ≤ Interpolation.runningMax e n := by
        intro n
        cases n with
        | zero => exact le_rfl
        | succ n => exact le_max_of_le_right (he _)
      exact mul_nonneg hC.le (h0 _)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hle
    have : 0 ≤ 2 ^ 7 * κ := by positivity
    nlinarith
end YangMills.Construction.Estimates
end
