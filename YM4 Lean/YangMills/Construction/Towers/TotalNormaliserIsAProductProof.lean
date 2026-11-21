import YangMills.Construction.Towers.LinearMapsOnTheRealSpacesProof
import YangMills.Construction.Towers.HessianOfTheLastPartialSumProof
import YangMills.Construction.Towers.TotalNormaliserIsAProduct
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
private theorem prolongIter_eq_prolong {L n k : ℕ} (b : CriticalBranchData L n k) {j t : ℕ}
    (h : j + 1 ≤ t) (W : Edge L n k t → Matrices.ComplexMatrix2) :
    b.prolongIter (Nat.le_of_succ_le h) W = b.prolong j (b.prolongIter h W) := by apply _root_.YangMills.Construction.Tower.LastPartialHessian.prolongIter_eq_prolong <;> assumption
private theorem descendingChain_eq_prolongIter {L n k : ℕ}
    (W : Edge L n k k → Matrices.ComplexMatrix2) {j : ℕ}
    (hj : j ≤ k) : descendingChain W hj = (chosenCriticalBranch L n k).prolongIter hj W := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.descendingChain_eq_chosenProlongIter <;> assumption
theorem totalNormaliserFactorises_holds (hSums : PartialGaugedActionsHold)
    (hLast : LastPartialHessianFormula) : TotalNormaliserFactorises := by
  intro L n k h hn hk
  obtain ⟨hN, hValues⟩ := hLast L n k h hn hk
  have hPartial := hSums L n k k h hn hk le_rfl _ hN.isOpenNhd
  refine (hPartial.and hValues).mono ?_
  rintro W ⟨hW, hv⟩
  have hU := chainBottom_eq W
  have hPos : (partialFibreHessian L n k k (smoothingFibreNhd L n k) W (chainBottom W)).PosDef := by
    rw [hU]
    exact hW.hessian_posDef
  have hNum : constrainedGaussianOnEdgeForms (smoothingIterDifferential L n k k (chainBottom W))
      (partialFibreHessian L n k k (smoothingFibreNhd L n k) W (chainBottom W)) =
      ∏ j : Fin k, gaussianNormaliser L n k j
        ((chosenCriticalBranch L n k).prolongIter (Nat.succ_le_of_lt j.is_lt) W) := by
    rw [hU]
    exact hW.gaussian_eq
  have hSpec : ∀ B, augmentedHessian L n k W B = augmentedHessianValue W B :=
    Classical.epsilon_spec
      (p := fun T : QuadraticForm ℝ (LinearMap.ker (topConstraintMap L n k W)) =>
        ∀ B, T B = augmentedHessianValue W B)
      ⟨partialFibreHessian L n k k (smoothingFibreNhd L n k) W (chainBottom W), hv⟩
  have hForm : augmentedHessian L n k W =
      partialFibreHessian L n k k (smoothingFibreNhd L n k) W (chainBottom W) :=
    QuadraticMap.ext fun B => (hSpec B).trans (hv B).symm
  refine ⟨⟨hSpec, hForm ▸ hPos⟩, ?_⟩
  change constrainedGaussianOnEdgeForms (smoothingIterDifferential L n k k (chainBottom W))
    (augmentedHessian L n k W) = _
  rw [show constrainedGaussianOnEdgeForms (smoothingIterDifferential L n k k (chainBottom W))
      (augmentedHessian L n k W) =
      constrainedGaussianOnEdgeForms (smoothingIterDifferential L n k k (chainBottom W))
        (partialFibreHessian L n k k (smoothingFibreNhd L n k) W (chainBottom W)) from
      congrArg _ hForm, hNum]
  exact Finset.prod_congr rfl fun i _ => by rw [descendingChain_eq_prolongIter]
end YangMills.Construction.Tower
end
