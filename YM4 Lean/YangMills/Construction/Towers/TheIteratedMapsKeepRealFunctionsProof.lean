import YangMills.Construction.Matrices.SpecialUnitaryExpSurjective
import YangMills.Construction.Towers.ChainOfTheComplexIteratesAtTheSideInfinity
import YangMills.Construction.Towers.TheEntriesOfTheBackgroundKernelAreRealAtRealDataProof
import YangMills.Construction.Towers.TheMapsOfOneStepKeepRealFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IteratesPreserveRealFields
open YangMills.Construction.Matrices
theorem meshAt_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem opposite_isPositivelyOriented_of_not {s : ℝ} {e : InfiniteLattice.Link s}
    (he : ¬ e.IsPositivelyOriented) : e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem link_opposite_opposite {s : ℝ} (e : InfiniteLattice.Link s) : e.opposite.opposite = e := rfl
theorem covDiff_mem {s : ℝ} (hs : 0 < s) {V : InfiniteLattice.Link s → ComplexMatrix2}
    (hV : IsFieldIn PeriodicLattice.compactGaugeGroup V) {φ : InfiniteLattice.LatticePoint s → ComplexMatrix2}
    (hφ : φ ∈ vertexFunctionSpace s) : covDiff V φ ∈ edgeFormSpace s := by apply _root_.YangMills.Construction.Tower.FullSpace.RealBackgroundKernel.covDiff_mem <;> assumption
theorem edgeFormSpace_le_complexEdgeForms {s : ℝ} {B : InfiniteLattice.Link s → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace s) : B ∈ complexEdgeForms s :=
  ⟨fun e he => (hB.1 e he).2, hB.2⟩
theorem matExp_I_smul_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.ExpSurjective.matExp_I_smul_mem_specialUnitary <;> assumption
theorem inv_mem_specialUnitary {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem inv_inv_of_mem_specialUnitary {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    (g⁻¹)⁻¹ = g := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
theorem expForm_mem {L k j : ℕ} (hs : 0 < meshAt L k j)
    {A : Edge L k j → ComplexMatrix2} (hA : A ∈ edgeFormSpace (meshAt L k j)) :
    expForm A ∈ fieldSpace L k j := by
  have hpos : ∀ e : Edge L k j, e.IsPositivelyOriented →
      expForm A e = ComplexMatrix2.matExp (Complex.I • A e) := fun e he => by
    simp [expForm, expTwist, he]
  have hneg : ∀ e : Edge L k j, ¬ e.IsPositivelyOriented →
      expForm A e = (ComplexMatrix2.matExp (Complex.I • A e.opposite))⁻¹ := fun e he => by
    simp [expForm, expTwist, he]
  refine ⟨fun e => ?_, fun e => ?_⟩
  · by_cases he : e.IsPositivelyOriented
    · rw [hpos e he]
      exact matExp_I_smul_mem (hA.1 e he)
    · rw [hneg e he]
      exact inv_mem_specialUnitary (matExp_I_smul_mem (hA.1 _ (opposite_isPositivelyOriented_of_not he)))
  · by_cases he : e.IsPositivelyOriented
    · rw [hneg _ (InfiniteLattice.Link.opposite_not_isPositivelyOriented hs he),
        link_opposite_opposite, hpos e he]
    · rw [hpos _ (opposite_isPositivelyOriented_of_not he), hneg e he,
        inv_inv_of_mem_specialUnitary
          (matExp_I_smul_mem (hA.1 _ (opposite_isPositivelyOriented_of_not he)))]
theorem zeroExtend_mem {L k : ℕ} {g : Vertex L k k → ComplexMatrix2}
    (hg : g ∈ vertexFunctionSpace (meshAt L k k)) :
    zeroExtend g ∈ vertexFunctionSpace (meshAt L k 0) := by
  intro x _
  unfold zeroExtend
  split_ifs with h
  · exact hg _ (mem_univ _)
  · exact ComplexMatrix2.hermitianTraceless.zero_mem
theorem holds_of_step_and_chain (hStep : RealityOfOneStep.Statement)
    (hChain : ComplexIterChain) : Holds := by
  intro L hL k _
  refine ⟨fun A hA => expForm_mem (meshAt_pos hL k 0) hA, fun U hU hUr => ?_⟩
  have hV : ∀ j ≤ k, complexIter L k j U ∈ fieldSpace L k j := by
    intro j
    induction j with
    | zero => exact fun _ => hUr
    | succ j ih =>
      intro hj
      exact (hStep L hL k j hj _ (hU.2 j hj) (ih (Nat.le_of_succ_le hj))).1
  have hst := fun (j : ℕ) (hj : j < k) => hStep L hL k j hj _ (hU.2 j hj) (hV j hj.le)
  have hQ : ∀ B ∈ edgeFormSpace (meshAt L k 0), ∀ j ≤ k,
      complexIterDeriv L k j U B ∈ edgeFormSpace (meshAt L k j) := by
    intro B hB j
    have hc := hChain L hL k U hU B (edgeFormSpace_le_complexEdgeForms hB)
    induction j with
    | zero => exact fun _ => hc.1.symm ▸ hB
    | succ j ih =>
      intro hj
      rw [hc.2.1 j hj]
      exact (hst j hj).2.2.1 _ (ih (Nat.le_of_succ_le hj))
  have hC : ∀ B ∈ edgeFormSpace (meshAt L k 0), ∀ j ≤ k,
      iterCovariantDeriv L k U j B ∈ edgeFormSpace (meshAt L k j) := by
    intro B hB j
    induction j with
    | zero => exact fun _ => hB
    | succ j ih =>
      intro hj
      have hi := ih (Nat.le_of_succ_le hj)
      exact (edgeFormSpace _).add_mem ((hst j hj).2.2.1 _ hi)
        (covDiff_mem (meshAt_pos hL k (j + 1)) (hst j hj).1
          ((hst j hj).2.2.2.1 _ hi))
  have hA : ∀ φ ∈ vertexFunctionSpace (meshAt L k 0), ∀ j ≤ k,
      iterAdjointCubeAverage L k U j φ ∈ vertexFunctionSpace (meshAt L k j) := by
    intro φ hφ j
    induction j with
    | zero => exact fun _ => hφ
    | succ j ih =>
      intro hj
      exact (hst j hj).2.2.2.2 _ (ih (Nat.le_of_succ_le hj))
  have hN : ∀ B ∈ edgeFormSpace (meshAt L k 0), ∀ j ≤ k,
      iterContourLogDrift L k U j B ∈ vertexFunctionSpace (meshAt L k j) := by
    intro B hB j
    induction j with
    | zero => exact fun _ => (vertexFunctionSpace _).zero_mem
    | succ j ih =>
      intro hj
      have hj' := Nat.le_of_succ_le hj
      exact (vertexFunctionSpace _).add_mem ((hst j hj).2.2.2.2 _ (ih hj'))
        ((hst j hj).2.2.2.1 _ (hQ B hB j hj'))
  have hσ : ∀ B ∈ edgeFormSpace (meshAt L k 0),
      gaugeParam U B ∈ vertexFunctionSpace (meshAt L k 0) :=
    fun B hB => zeroExtend_mem (hN B hB k le_rfl)
  refine ⟨hV, fun j hj B hB => ⟨hQ B hB j hj, hC B hB j hj, hN B hB j hj⟩,
    fun j hj φ hφ => hA φ hφ j hj, fun B hB => ⟨hσ B hB, ?_⟩⟩
  exact (edgeFormSpace _).add_mem hB
    (covDiff_mem (meshAt_pos hL k 0) hUr (hσ B hB))
end YangMills.Construction.Tower.FullSpace.IteratesPreserveRealFields
end
