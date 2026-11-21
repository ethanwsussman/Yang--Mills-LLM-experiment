import YangMills.Construction.SummableBoundsOfTheFlow.ByPartsAtABondProof
import YangMills.Construction.SummableBoundsOfTheFlow.ReadAboveFromMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
set_option linter.unusedSectionVars false
namespace YangMills.Construction.IteratedDerivative
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace RotatedEvalAux
variable {F : BlockFrame}
open Classical in
def displacementMap {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (v : Fin l → EuclideanSpace ℝ (Fin 3)) :
    (Fin (l + k) → ℝ) →L[ℝ] StepVariable (finiteCells F) × (Fin k → ℝ) :=
  ContinuousLinearMap.prod
    (∑ i, (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => EuclideanSpace ℝ (Fin 3)) (b i)).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (l + k) => ℝ) (Fin.castAdd k i)).smulRight (v i)))
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (l + k) => ℝ) (Fin.natAdd l i))
theorem displacementMap_fst {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (v : Fin l → EuclideanSpace ℝ (Fin 3))
    (τ : Fin (l + k) → ℝ) : open Classical in
    (displacementMap b v τ).1 = ∑ i, τ (Fin.castAdd k i) • Pi.single (b i) (v i) := by
  simp [displacementMap]
theorem jointDisplacement_eq {l k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (η : StepVariable (finiteCells F))
    (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F))) (v : Fin l → EuclideanSpace ℝ (Fin 3))
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    jointDisplacement G η V b v c X = fun τ => rotatedEval G V c X ((η, 0) + displacementMap b v τ) := by
  funext τ
  simp only [jointDisplacement, rotatedEval, displacedPoint, Prod.fst_add, Prod.snd_add, zero_add, displacementMap_fst]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun i _ => Pi.single_smul _ _ _
abbrev BondCoord (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F)) × Fin 3
def coordinateMap (k : ℕ) (e : BondCoord F ≃ Fin (Fintype.card (BondCoord F))) :
    StepVariable (finiteCells F) × (Fin k → ℝ) →L[ℝ] (Fin (Fintype.card (BondCoord F) + k) → ℝ) :=
  ContinuousLinearMap.pi fun j => Fin.addCases (motive := fun _ =>
      StepVariable (finiteCells F) × (Fin k → ℝ) →L[ℝ] ℝ)
    (fun i => (((EuclideanSpace.proj (e.symm i).2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(chordBonds (finiteCells F)) =>
            EuclideanSpace ℝ (Fin 3)) (e.symm i).1)).comp
          (ContinuousLinearMap.fst ℝ _ _))
    (fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).comp
      (ContinuousLinearMap.snd ℝ _ _)) j
theorem coordinateMap_castAdd (k : ℕ) (e : BondCoord F ≃ Fin (Fintype.card (BondCoord F)))
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (i : Fin (Fintype.card (BondCoord F))) :
    coordinateMap k e p (Fin.castAdd k i) = p.1 (e.symm i).1 (e.symm i).2 := by
  unfold coordinateMap
  simp only [ContinuousLinearMap.coe_pi', Fin.addCases_left]
  simp
theorem coordinateMap_natAdd (k : ℕ) (e : BondCoord F ≃ Fin (Fintype.card (BondCoord F)))
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (i : Fin k) :
    coordinateMap k e p (Fin.natAdd _ i) = p.2 i := by
  unfold coordinateMap
  simp only [ContinuousLinearMap.coe_pi', Fin.addCases_right]
  simp
theorem sum_smul_single_eq (x : EuclideanSpace ℝ (Fin 3)) : ∑ q, x q • EuclideanSpace.single q (1 : ℝ) = x := by apply _root_.YangMills.Construction.BondIntegration.sum_smul_bondBasis <;> assumption
open Classical in
theorem displacementMap_coordinateRepr (k : ℕ) (e : BondCoord F ≃ Fin (Fintype.card (BondCoord F)))
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) :
    displacementMap (fun i => (e.symm i).1) (fun i => EuclideanSpace.single (e.symm i).2 (1 : ℝ))
      (coordinateMap k e p) = p := by
  refine Prod.ext ?_ ?_
  · rw [displacementMap_fst]
    simp only [coordinateMap_castAdd]
    rw [Equiv.sum_comp e.symm (fun s : BondCoord F => p.1 s.1 s.2 •
      (Pi.single s.1 (EuclideanSpace.single s.2 (1 : ℝ)) : StepVariable (finiteCells F)))]
    rw [Fintype.sum_prod_type]
    have hb : ∀ β : ↥(chordBonds (finiteCells F)), ∑ q : Fin 3, p.1 β q •
        (Pi.single β (EuclideanSpace.single q (1 : ℝ)) : StepVariable (finiteCells F)) = Pi.single β (p.1 β) := by
      intro β
      conv_rhs => rw [← sum_smul_single_eq (p.1 β)]
      rw [show (Pi.single β (∑ q : Fin 3, p.1 β q • EuclideanSpace.single q (1 : ℝ)) : StepVariable (finiteCells F)) =
        ∑ q : Fin 3, Pi.single β (p.1 β q • EuclideanSpace.single q (1 : ℝ)) from
        map_sum (AddMonoidHom.single (fun _ : ↥(chordBonds (finiteCells F)) => EuclideanSpace ℝ (Fin 3)) β) _ _]
      exact Finset.sum_congr rfl fun q _ => (Pi.single_smul _ _ _).symm
    simp only [hb]
    exact Finset.univ_sum_single p.1
  · funext j
    have := coordinateMap_natAdd k e p j
    simpa [displacementMap] using this
end RotatedEvalAux
open RotatedEvalAux in
theorem rotatedEvalContDiffOfDisplacements_holds : rotatedEvalContDiffOfDisplacements := by
  classical
  intro F V G η k c X n hk
  let e := Fintype.equivFin (BondCoord F)
  have h1 := hk _ (fun i => (e.symm i).1) (fun i => EuclideanSpace.single (e.symm i).2 (1 : ℝ)) (fun i => by simp)
  have hrot : rotatedEval G V c X = fun q => jointDisplacement G η V (fun i => (e.symm i).1)
      (fun i => EuclideanSpace.single (e.symm i).2 (1 : ℝ)) c X (coordinateMap k e (q - (η, 0))) := by
    funext q
    rw [jointDisplacement_eq]
    beta_reduce
    rw [displacementMap_coordinateRepr]
    simp
  rw [hrot]
  have h0 : coordinateMap k e (((η, 0) : StepVariable (finiteCells F) × (Fin k → ℝ)) - (η, 0)) = 0 := by simp
  have h2 : ContDiffAt ℝ (n : WithTop ℕ∞)
      (jointDisplacement G η V (fun i => (e.symm i).1) (fun i => EuclideanSpace.single (e.symm i).2 (1 : ℝ)) c X)
      (coordinateMap k e (((η, 0) : StepVariable (finiteCells F) × (Fin k → ℝ)) - (η, 0))) := by
    rw [h0]; exact h1
  exact ContDiffAt.comp (η, 0) h2
    (((coordinateMap k e).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt)
end YangMills.Construction.IteratedDerivative
end
