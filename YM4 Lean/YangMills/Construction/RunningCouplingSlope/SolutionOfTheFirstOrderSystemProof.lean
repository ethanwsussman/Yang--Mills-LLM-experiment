import YangMills.Construction.RunningCouplingSlope.BranchOfLeastPointsProof
import YangMills.Construction.RunningCouplingSlope.SolutionOfTheFirstOrderSystem
import YangMills.Construction.Towers.CrossingAndLinearAveragesUpToADifferenceProof
import YangMills.Construction.Towers.MapsOfTheResponseAndTheirTransposesProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Set
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FirstOrderSolution
open Matrices
open Tower
open Tower.CriticalBranchResponse
section TracePairing
variable {ι : Type*} [Finite ι]
private theorem tracePair_add_left (f f' g : ι → ComplexMatrix2) :
    traceFinsumPairing (f + f') g = traceFinsumPairing f g + traceFinsumPairing f' g := by apply _root_.YangMills.Construction.Tower.RealQuadraticTransposes.tracePair_add_left <;> assumption
private theorem tracePair_comm (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = traceFinsumPairing g f := by apply _root_.YangMills.Construction.Tower.RealQuadraticTransposes.tracePair_comm <;> assumption
private theorem tracePair_smul_left (r : ℝ) (f g : ι → ComplexMatrix2) :
    traceFinsumPairing (r • f) g = (r : ℂ) * traceFinsumPairing f g := by apply _root_.YangMills.SharedProofs.p655 <;> assumption
private theorem tracePair_zero_right (f : ι → ComplexMatrix2) :
    traceFinsumPairing f (0 : ι → ComplexMatrix2) = 0 := by
  simp [traceFinsumPairing, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
private theorem tracePair_neg_left (f g : ι → ComplexMatrix2) :
    traceFinsumPairing (-f) g = -traceFinsumPairing f g := by
  have h := tracePair_smul_left (-1 : ℝ) f g
  simpa using h
private theorem tracePair_sub_left (f f' g : ι → ComplexMatrix2) :
    traceFinsumPairing (f - f') g = traceFinsumPairing f g - traceFinsumPairing f' g := by
  rw [sub_eq_add_neg, tracePair_add_left, tracePair_neg_left, sub_eq_add_neg]
private theorem tracePair_add_right (f g g' : ι → ComplexMatrix2) :
    traceFinsumPairing f (g + g') = traceFinsumPairing f g + traceFinsumPairing f g' := by
  rw [tracePair_comm, tracePair_add_left, tracePair_comm g, tracePair_comm g']
private theorem tracePair_smul_right (r : ℝ) (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f (r • g) = (r : ℂ) * traceFinsumPairing f g := by
  rw [tracePair_comm, tracePair_smul_left, tracePair_comm g]
private theorem tracePair_self_re (hI : FaceSums.PairingIsInner ↥(univ : Set ι))
    (g : ι → ComplexMatrix2) (hg : ∀ i, g i ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (traceFinsumPairing g g).re ∧ ((traceFinsumPairing g g).re = 0 → g = 0) := by apply _root_.YangMills.SharedProofs.p120809 <;> assumption
end TracePairing
section EdgeForms
variable {L n k j : ℕ}
private theorem edgeForm_eq_zero_of_restrict {B : Edge L n k j → ComplexMatrix2}
    (h : B ∈ edgeFormSpace L n k j) (h0 : restrictToPositiveEdges B = 0) : B = 0 := by apply _root_.YangMills.SharedProofs.p27961 <;> assumption
private theorem vertexCoboundary_mem {l : Vertex L n k j → ComplexMatrix2}
    (h : l ∈ vertexFunctionSpace L n k j) :
    vertexCoboundary l ∈ edgeFormSpace L n k j := by apply _root_.YangMills.Construction.Tower.ClosedFormsSmoothing.vertexCoboundary_mem <;> assumption
private theorem vertexCoboundary_add (l l' : Vertex L n k j → ComplexMatrix2) :
    vertexCoboundary (l + l') = vertexCoboundary l + vertexCoboundary l' := by apply _root_.YangMills.SharedProofs.p26773 <;> assumption
private theorem vertexCoboundary_sub (l l' : Vertex L n k j → ComplexMatrix2) :
    vertexCoboundary (l - l') = vertexCoboundary l - vertexCoboundary l' := by apply _root_.YangMills.Construction.Tower.CoboundaryDifference.vertexCoboundary_sub <;> assumption
private theorem edgeCoboundary_vertexCoboundary (l : Vertex L n k j → ComplexMatrix2) :
    edgeCoboundary (vertexCoboundary l) = 0 := by
  funext p
  simp only [edgeCoboundary, vertexCoboundary, PeriodicLattice.Bond.forwardFrom, Pi.zero_apply]
  rw [add_right_comm p.origin]
  abel
private theorem edgeCoboundary_sub (X Y : Edge L n k j → ComplexMatrix2) :
    edgeCoboundary (X - Y) = edgeCoboundary X - edgeCoboundary Y := by
  funext p
  simp only [edgeCoboundary, Pi.sub_apply]
  abel
private theorem edgeCoboundary_apply_mem {B : Edge L n k j → ComplexMatrix2}
    (h : B ∈ edgeFormSpace L n k j) (p : Face L n k j) :
    edgeCoboundary B p ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p81306 <;> assumption
private theorem vertexSmoothing_mem {l : Vertex L n k j → ComplexMatrix2}
    (h : l ∈ vertexFunctionSpace L n k j) :
    vertexSmoothing L n k j l ∈ vertexFunctionSpace L n k (j + 1) := by
  intro y _
  simp only [vertexSmoothing, PeriodicLattice.inverseFourthPowerWeight]
  rw [Complex.coe_smul]
  refine ComplexMatrix2.hermitianTraceless.smul_mem _ ?_
  exact finsum_mem_induction (· ∈ ComplexMatrix2.hermitianTraceless)
    ComplexMatrix2.hermitianTraceless.zero_mem (fun _ _ => ComplexMatrix2.hermitianTraceless.add_mem)
    fun x _ => h x trivial
private theorem sumAlong_mem {B : Edge L n k j → ComplexMatrix2} (h : B ∈ edgeFormSpace L n k j)
    (Γ : List (Edge L n k j)) :
    PeriodicLattice.bondFormSumAlong B Γ ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.SmoothingIterProof.bondFormSumAlong_mem <;> assumption
private theorem cubeContourAverage_mem {B : Edge L n k j → ComplexMatrix2}
    (h : B ∈ edgeFormSpace L n k j) :
    cubeContourAverage L n k j B ∈ vertexFunctionSpace L n k (j + 1) := by
  intro y _
  simp only [cubeContourAverage, PeriodicLattice.inverseFourthPowerWeight]
  rw [Complex.coe_smul]
  refine ComplexMatrix2.hermitianTraceless.smul_mem _ ?_
  refine finsum_mem_induction (· ∈ ComplexMatrix2.hermitianTraceless)
    ComplexMatrix2.hermitianTraceless.zero_mem (fun _ _ => ComplexMatrix2.hermitianTraceless.add_mem)
    fun x _ => ?_
  simp only [PeriodicLattice.contourFormAverage]
  rw [Complex.coe_smul]
  exact ComplexMatrix2.hermitianTraceless.smul_mem _ (Submodule.sum_mem _ fun σ _ => sumAlong_mem h _)
end EdgeForms
section Additivity
variable {L n k j : ℕ}
private theorem crossingSmoothing_add (hfin : Finite (Vertex L n k j))
    (A A' : Edge L n k j → ComplexMatrix2) :
    crossingSmoothing L n k j (A + A') =
      crossingSmoothing L n k j A + crossingSmoothing L n k j A' := by apply _root_.YangMills.SharedProofs.p41844 <;> assumption
private theorem crossingSmoothing_smul (hfin : Finite (Vertex L n k j)) (r : ℝ)
    (A : Edge L n k j → ComplexMatrix2) :
    crossingSmoothing L n k j (r • A) = r • crossingSmoothing L n k j A := by apply _root_.YangMills.Construction.Tower.ResponseMaps.crossingSmoothing_smul <;> assumption
end Additivity
section Chains
variable {L n k : ℕ}
private theorem linearChain_succ (ξ : LevelForms L n k) {j : ℕ} (hj : j < k) :
    linearChain ξ (j + 1) = crossingSmoothing L n k j (linearChain ξ j) +
      (ξ.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) := by
  rw [linearChain, dif_pos hj]
private theorem linearTransport_succ (ξ : LevelForms L n k) {j : ℕ} (hj : j < k) :
    linearTransport ξ (j + 1) = linearSmoothing L n k j (linearTransport ξ j) +
      (ξ.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) := by
  rw [linearTransport, dif_pos hj]
private theorem linearChain_mem
    (hc : ∀ j, j < k → ∀ B ∈ edgeFormSpace L n k j,
      crossingSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1))
    (ξ : LevelForms L n k) : ∀ j, j ≤ k → linearChain ξ j ∈ edgeFormSpace L n k j := by
  intro j
  induction j with
  | zero => exact fun _ => ξ.1.2
  | succ j ih =>
    intro h
    have hj : j < k := h
    rw [linearChain_succ ξ hj]
    exact (edgeFormSpace L n k (j + 1)).add_mem (hc j hj _ (ih hj.le)) (ξ.2 ⟨j, hj⟩).2
private theorem linearTransport_mem
    (hc : ∀ j, j < k → ∀ B ∈ edgeFormSpace L n k j,
      linearSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1))
    (ξ : LevelForms L n k) : ∀ j, j ≤ k → linearTransport ξ j ∈ edgeFormSpace L n k j := by
  intro j
  induction j with
  | zero => exact fun _ => ξ.1.2
  | succ j ih =>
    intro h
    have hj : j < k := h
    rw [linearTransport_succ ξ hj]
    exact (edgeFormSpace L n k (j + 1)).add_mem (hc j hj _ (ih hj.le)) (ξ.2 ⟨j, hj⟩).2
private theorem linearTransport_eq_linearChain_add
    (hc : ∀ j, j < k → ∀ B ∈ edgeFormSpace L n k j,
      linearSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1))
    (hstep : ∀ j, j < k → TrivialLinearization.OneStepIdentities L n k j)
    (hfin : ∀ j, j ≤ k → Finite (Vertex L n k j)) (ξ : LevelForms L n k) :
    ∀ j, j ≤ k → ∃ g ∈ vertexFunctionSpace L n k j,
      linearTransport ξ j = linearChain ξ j + vertexCoboundary g := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨0, (vertexFunctionSpace L n k 0).zero_mem, ?_⟩
    funext b
    simp [linearTransport, linearChain, vertexCoboundary]
  | succ j ih =>
    intro h
    have hj : j < k := h
    obtain ⟨g, hg, e⟩ := ih hj.le
    have hp := linearTransport_mem hc ξ j hj.le
    obtain ⟨h1, h2⟩ := hstep j hj
    refine ⟨vertexSmoothing L n k j g - cubeContourAverage L n k j (linearTransport ξ j),
      (vertexFunctionSpace L n k (j + 1)).sub_mem (vertexSmoothing_mem hg)
        (cubeContourAverage_mem hp), ?_⟩
    rw [linearTransport_succ ξ hj, linearChain_succ ξ hj, h1 _ hp, vertexCoboundary_sub,
      ← (h2 g hg).2.1]
    have e2 : crossingSmoothing L n k j (linearTransport ξ j) =
        crossingSmoothing L n k j (linearChain ξ j) +
          crossingSmoothing L n k j (vertexCoboundary g) := by
      rw [e, crossingSmoothing_add (hfin j hj.le)]
    rw [e2]
    abel
private theorem linearTransport_of_snd_eq_zero (ξ : LevelForms L n k) (hξ : ξ.2 = 0) :
    ∀ j, j ≤ k → linearTransport ξ j = linearSmoothingIter L n k j ξ.1 := by apply _root_.YangMills.SharedProofs.p62364 <;> assumption
private theorem linearChain_of_snd_eq_zero (ξ : LevelForms L n k) (hξ : ξ.2 = 0) :
    ∀ j, j ≤ k → linearChain ξ j = crossingSmoothingIter L n k j ξ.1 := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    rw [linearChain_succ ξ hj, ih hj.le, hξ]
    simp only [Pi.zero_apply, ZeroMemClass.coe_zero, add_zero]
    rfl
private theorem linearChain_add (hfin : ∀ j, j ≤ k → Finite (Vertex L n k j))
    (ξ ξ' : LevelForms L n k) : ∀ j, j ≤ k →
      linearChain (ξ + ξ') j = linearChain ξ j + linearChain ξ' j := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    rw [linearChain_succ _ hj, linearChain_succ _ hj, linearChain_succ _ hj, ih hj.le,
      crossingSmoothing_add (hfin j hj.le)]
    simp only [Prod.snd_add, Pi.add_apply, Submodule.coe_add]
    abel
private theorem linearChain_smul (hfin : ∀ j, j ≤ k → Finite (Vertex L n k j)) (r : ℝ)
    (ξ : LevelForms L n k) : ∀ j, j ≤ k →
      linearChain (r • ξ) j = r • linearChain ξ j := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    rw [linearChain_succ _ hj, linearChain_succ _ hj, ih hj.le,
      crossingSmoothing_smul (hfin j hj.le)]
    simp only [Prod.smul_snd, Pi.smul_apply, Submodule.coe_smul, smul_add]
private theorem linearTransport_of_gauge (hL : 0 < L)
    (hstep : ∀ j, j < k → TrivialLinearization.OneStepIdentities L n k j)
    (l : vertexFunctionSpace L n k 0) (ξ : LevelForms L n k)
    (hξ1 : (ξ.1 : Edge L n k 0 → ComplexMatrix2) =
      vertexCoboundary (l : Vertex L n k 0 → ComplexMatrix2))
    (hξ : ξ.2 = 0) : ∀ j, j ≤ k →
      linearTransport ξ j =
        vertexCoboundary (restrictVertexFunction j (l : Vertex L n k 0 → ComplexMatrix2)) := by apply _root_.YangMills.SharedProofs.p55879 <;> assumption
end Chains
private theorem exists_linearMap_representing {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F] (p : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hp : ∀ x, p x x = 0 → x = 0) (φ : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    ∃ T : F →ₗ[ℝ] E, ∀ f e, p (T f) e = φ f e := by apply _root_.YangMills.SharedProofs.p13845 <;> assumption
section LevelPairing
variable {L n k : ℕ} {j : ℕ}
private theorem edgePair_add_left [Finite (PositiveEdge L n k j)]
    (X X' Y : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing (X + X') Y = edgeFormPairing X Y + edgeFormPairing X' Y :=
  tracePair_add_left _ _ _
private theorem edgePair_sub_left [Finite (PositiveEdge L n k j)]
    (X X' Y : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing (X - X') Y = edgeFormPairing X Y - edgeFormPairing X' Y :=
  tracePair_sub_left _ _ _
private theorem edgePair_add_right [Finite (PositiveEdge L n k j)]
    (X Y Y' : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing X (Y + Y') = edgeFormPairing X Y + edgeFormPairing X Y' :=
  tracePair_add_right _ _ _
private theorem edgePair_smul_left [Finite (PositiveEdge L n k j)] (r : ℝ)
    (X Y : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing (r • X) Y = (r : ℂ) * edgeFormPairing X Y :=
  tracePair_smul_left _ _ _
private theorem edgePair_smul_right [Finite (PositiveEdge L n k j)] (r : ℝ)
    (X Y : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing X (r • Y) = (r : ℂ) * edgeFormPairing X Y :=
  tracePair_smul_right _ _ _
private theorem edgePair_zero_right [Finite (PositiveEdge L n k j)]
    (X : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing X (0 : Edge L n k j → ComplexMatrix2) = 0 :=
  tracePair_zero_right _
private theorem edgePair_self_re [Finite (PositiveEdge L n k j)]
    (hI : FaceSums.PairingIsInner ↥(univ : Set (PositiveEdge L n k j)))
    (B : edgeFormSpace L n k j) :
    0 ≤ (edgeFormPairing (B : Edge L n k j → ComplexMatrix2) B).re ∧
      ((edgeFormPairing (B : Edge L n k j → ComplexMatrix2) B).re = 0 → B = 0) := by apply _root_.YangMills.SharedProofs.p90865 <;> assumption
variable [hF0 : Finite (PositiveEdge L n k 0)]
  [hF : ∀ i : Fin k, Finite (PositiveEdge L n k ((i : ℕ) + 1))]
private theorem levelPair_add_left (ξ ξ' η : LevelForms L n k) :
    levelPairing (formValues (ξ + ξ')) (formValues η) =
      levelPairing (formValues ξ) (formValues η) +
        levelPairing (formValues ξ') (formValues η) := by apply _root_.YangMills.SharedProofs.p57549 <;> assumption
private theorem levelPair_smul_left (r : ℝ) (ξ η : LevelForms L n k) :
    levelPairing (formValues (r • ξ)) (formValues η) =
      r * levelPairing (formValues ξ) (formValues η) := by apply _root_.YangMills.SharedProofs.p29192 <;> assumption
private theorem levelPair_comm (ξ η : LevelForms L n k) :
    levelPairing (formValues ξ) (formValues η) = levelPairing (formValues η) (formValues ξ) := by apply _root_.YangMills.SharedProofs.p11971 <;> assumption
private def levelForm : LevelForms L n k →ₗ[ℝ] LevelForms L n k →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun ξ η => levelPairing (formValues ξ) (formValues η)) levelPair_add_left
    (fun r ξ η => by rw [levelPair_smul_left, smul_eq_mul])
    (fun ξ η η' => by rw [levelPair_comm, levelPair_add_left, levelPair_comm η, levelPair_comm η'])
    (fun r ξ η => by rw [levelPair_comm, levelPair_smul_left, levelPair_comm η, smul_eq_mul])
private theorem levelForm_apply (ξ η : LevelForms L n k) :
    levelForm ξ η = levelPairing (formValues ξ) (formValues η) := rfl
private theorem levelForm_definite
    (hI0 : FaceSums.PairingIsInner ↥(univ : Set (PositiveEdge L n k 0)))
    (hI : ∀ i : Fin k, FaceSums.PairingIsInner
      ↥(univ : Set (PositiveEdge L n k ((i : ℕ) + 1))))
    (ξ : LevelForms L n k) (h : levelForm ξ ξ = 0) : ξ = 0 := by
  rw [levelForm_apply] at h
  simp only [levelPairing, formValues] at h
  have h0 := (edgePair_self_re hI0 ξ.1).1
  have hi := fun i => (edgePair_self_re (hI i) (ξ.2 i)).1
  have hs : 0 ≤ ∑ i : Fin k,
      (edgeFormPairing (ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) (ξ.2 i)).re :=
    Finset.sum_nonneg fun i _ => hi i
  have e0 : (edgeFormPairing (ξ.1 : Edge L n k 0 → ComplexMatrix2) ξ.1).re = 0 := by linarith
  have es : ∑ i : Fin k,
      (edgeFormPairing (ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) (ξ.2 i)).re = 0 := by
    linarith
  have ei := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hi i).mp es
  refine Prod.ext ((edgePair_self_re hI0 ξ.1).2 e0) (funext fun i => ?_)
  exact (edgePair_self_re (hI i) (ξ.2 i)).2 (ei i (Finset.mem_univ i))
end LevelPairing
theorem firstOrderSystemSolution_holds (hS : FaceSums.FacesAndPairings)
    (hR : TrivialLinearization.AllRelationsStatement) (hV : LinearMapValues.Statement)
    (hRel : TorusResponseRelations.statement) (hM : ResponseMaps.ResponseMapsHold)
    (hK : ClosedInSmoothingKernelIsExact) (hLR : RealLinearMaps.RealLinearMapsStatement) :
    FirstOrderSystemSolution := by
  intro a ha L hL k n hk hn B t ht
  have hLpos : 0 < L := by have := hL.2; omega
  have hPS := fun (j : ℕ) (hj : j ≤ k) => (hS L hL k j hj).1 n hn
  have finS : ∀ j, j ≤ k → Finite (Vertex L n k j) := fun j hj =>
    Set.finite_univ_iff.mp ((hPS j hj).2.1 univ).2.1
  have finB : ∀ j, j ≤ k → Finite (PositiveEdge L n k j) := fun j hj =>
    Set.finite_univ_iff.mp ((hPS j hj).2.2.1 univ).2.1
  have innB := fun (j : ℕ) (hj : j ≤ k) => ((hPS j hj).2.2.1 univ).1
  haveI finP : Finite (Face L n k 0) :=
    Set.finite_univ_iff.mp ((hPS 0 (Nat.zero_le _)).2.2.2 univ).2.1
  have innP := ((hPS 0 (Nat.zero_le _)).2.2.2 univ).1
  haveI hF0 : Finite (PositiveEdge L n k 0) := finB 0 (Nat.zero_le _)
  haveI hFk : Finite (PositiveEdge L n k k) := finB k le_rfl
  haveI hF : ∀ i : Fin k, Finite (PositiveEdge L n k ((i : ℕ) + 1)) := fun i => finB _ i.2
  have hvals := (hV L hL k).1 n hn
  have hcC : ∀ j, j < k → ∀ B ∈ edgeFormSpace L n k j,
      crossingSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1) :=
    fun j hj B hB => ((hvals.1 j hj).1 B hB).2.1
  have hcL : ∀ j, j < k → ∀ B ∈ edgeFormSpace L n k j,
      linearSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1) :=
    fun j hj B hB => ((hvals.1 j hj).1 B hB).2.2.1
  have hstep : ∀ j, j < k → TrivialLinearization.OneStepIdentities L n k j :=
    fun j hj => ((hR L hL).1 n k j j hn hj hj.le).1
  have honto : ∀ C ∈ edgeFormSpace L n k k, ∃ B ∈ edgeFormSpace L n k 0,
      crossingSmoothingIter L n k k B = C :=
    ((hR L hL).1 n k 0 k hn (by omega) le_rfl).2.2.2.1.2.2.2
  have tm := hM L hL k n hk hn
  obtain ⟨r, hrv, hrT⟩ := (hLR L n k hL hn hk).2.exists_restriction
  have hrest : ∀ g ∈ vertexFunctionSpace L n k k, ∃ l : vertexFunctionSpace L n k 0,
      restrictVertexFunction k (l : Vertex L n k 0 → ComplexMatrix2) = g := by
    intro g hg
    obtain ⟨l, hl⟩ := hrT.surjective ⟨g, hg⟩
    refine ⟨l, ?_⟩
    have := hrv l
    rw [hl] at this
    exact this.symm
  have fdim : ∀ j, j ≤ k → FiniteDimensional ℝ (edgeFormSpace L n k j) := by
    intro j hj
    haveI := finB j hj
    let f : edgeFormSpace L n k j →ₗ[ℝ] (PositiveEdge L n k j → ComplexMatrix2) :=
      { toFun := fun B => restrictToPositiveEdges (B : Edge L n k j → ComplexMatrix2)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine FiniteDimensional.of_injective f ?_
    rw [injective_iff_map_eq_zero]
    intro B hB
    exact Subtype.ext (edgeForm_eq_zero_of_restrict B.2 hB)
  haveI hfd0 := fdim 0 (Nat.zero_le _)
  haveI hfdi : ∀ i : Fin k, FiniteDimensional ℝ (edgeFormSpace L n k ((i : ℕ) + 1)) :=
    fun i => fdim _ i.2
  have hdef : ∀ ξ : LevelForms L n k, levelForm ξ ξ = 0 → ξ = 0 :=
    levelForm_definite (innB 0 (Nat.zero_le _)) fun i => innB _ i.2
  let φ : edgeFormSpace L n k k →ₗ[ℝ] LevelForms L n k →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun μ ξ => (edgeFormPairing (μ : Edge L n k k → ComplexMatrix2) (linearChain ξ k)).re)
      (fun μ μ' ξ => by
        simp only [Submodule.coe_add]
        rw [edgePair_add_left, Complex.add_re])
      (fun r μ ξ => by
        simp only [Submodule.coe_smul, smul_eq_mul]
        rw [edgePair_smul_left, Complex.re_ofReal_mul])
      (fun μ ξ ξ' => by
        rw [linearChain_add finS ξ ξ' k le_rfl, edgePair_add_right, Complex.add_re])
      (fun r μ ξ => by
        rw [linearChain_smul finS r ξ k le_rfl, edgePair_smul_right, Complex.re_ofReal_mul,
          smul_eq_mul])
  obtain ⟨T0, hT0⟩ := exists_linearMap_representing levelForm hdef φ
  have hT : IsLinearConstraintAdjoint (linearConstraintAdjoint L n k) :=
    Classical.epsilon_spec (p := IsLinearConstraintAdjoint) ⟨T0, fun μ ξ => hT0 μ ξ⟩
  obtain ⟨ξ, J, μ⟩ := t
  simp only at ht ⊢
  have hzs : ∀ (H : (i : Fin k) → edgeFormSpace L n k ((i : ℕ) + 1)),
      ∑ i : Fin k, (edgeFormPairing (H i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)
        (((0 : (i : Fin k) → edgeFormSpace L n k ((i : ℕ) + 1)) i :
          edgeFormSpace L n k ((i : ℕ) + 1)) :
          Edge L n k ((i : ℕ) + 1) → ComplexMatrix2)).re = 0 := by
    intro H
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [Pi.zero_apply, ZeroMemClass.coe_zero]
    rw [edgePair_zero_right]
    simp
  have hgrad0 : ∀ f : edgeFormSpace L n k 0,
      (traceFinsumPairing (edgeCoboundary (ξ.1 : Edge L n k 0 → ComplexMatrix2))
        (edgeCoboundary (f : Edge L n k 0 → ComplexMatrix2))).re =
      (edgeFormPairing (μ : Edge L n k k → ComplexMatrix2)
        (linearTransport ((f, 0) : LevelForms L n k) k)).re := by
    intro f
    have h1 := ht.pairing_eq_hessian (f, 0)
    rw [ht.pairing_eq_adjoint (f, 0)] at h1
    rw [h1]
    simp only [hessianAtIdentity]
    rw [hzs]
    simp
  have hgauge : ∀ g ∈ vertexFunctionSpace L n k k,
      (edgeFormPairing (μ : Edge L n k k → ComplexMatrix2) (vertexCoboundary g)).re = 0 := by
    intro g hg
    obtain ⟨l, hl⟩ := hrest g hg
    let f : edgeFormSpace L n k 0 :=
      ⟨vertexCoboundary (l : Vertex L n k 0 → ComplexMatrix2), vertexCoboundary_mem l.2⟩
    have e := linearTransport_of_gauge hLpos hstep l (f, 0) rfl rfl k le_rfl
    have h := hgrad0 f
    rw [e, hl] at h
    rw [← h]
    have e2 : edgeCoboundary (f : Edge L n k 0 → ComplexMatrix2) = 0 :=
      edgeCoboundary_vertexCoboundary _
    rw [e2, tracePair_zero_right]
    simp
  have hb : ∀ η : LevelForms L n k,
      (edgeFormPairing (μ : Edge L n k k → ComplexMatrix2) (linearTransport η k)).re =
        (edgeFormPairing (μ : Edge L n k k → ComplexMatrix2) (linearChain η k)).re := by
    intro η
    obtain ⟨g, hg, e⟩ := linearTransport_eq_linearChain_add hcL hstep finS η k le_rfl
    rw [e, edgePair_add_right, Complex.add_re, hgauge g hg, add_zero]
  have hJ : J = linearConstraintAdjoint L n k μ := by
    have hz : ∀ η, levelForm (J - linearConstraintAdjoint L n k μ) η = 0 := by
      intro η
      rw [map_sub, LinearMap.sub_apply, levelForm_apply, levelForm_apply, ht.pairing_eq_adjoint η,
        hb η]
      rw [hT μ η]
      simp
    exact sub_eq_zero.mp (hdef _ (hz _))
  refine ⟨hJ, ?_, ?_⟩
  · intro i
    rw [← hJ]
    have hD : ∀ D : edgeFormSpace L n k ((i : ℕ) + 1),
        (edgeFormPairing (J.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) D).re =
          a * (edgeFormPairing (ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) D).re := by
      intro D
      have hs : ∀ (H : (i : Fin k) → edgeFormSpace L n k ((i : ℕ) + 1)),
          ∑ i' : Fin k, (edgeFormPairing (H i' : Edge L n k ((i' : ℕ) + 1) → ComplexMatrix2)
            ((Pi.single i D : (i : Fin k) → edgeFormSpace L n k ((i : ℕ) + 1)) i' :
              Edge L n k ((i' : ℕ) + 1) → ComplexMatrix2)).re =
          (edgeFormPairing (H i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) D).re := by
        intro H
        rw [Finset.sum_eq_single i]
        · simp
        · intro i' _ hne
          simp only [Pi.single_eq_of_ne hne, ZeroMemClass.coe_zero]
          rw [edgePair_zero_right]
          simp
        · intro h
          exact absurd (Finset.mem_univ i) h
      have h1 := ht.pairing_eq_hessian (0, Pi.single i D)
      have z0 : ((0 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) = 0 := rfl
      have e1 : levelPairing (formValues J)
          (formValues ((0, Pi.single i D) : LevelForms L n k)) =
          (edgeFormPairing (J.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) D).re := by
        simp only [levelPairing, formValues]
        rw [hs J.2, z0, edgePair_zero_right]
        simp
      have e2 : hessianAtIdentity a ξ ((0, Pi.single i D) : LevelForms L n k) =
          a * (edgeFormPairing (ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) D).re := by
        simp only [hessianAtIdentity]
        rw [hs ξ.2, z0]
        have e3 : edgeCoboundary (0 : Edge L n k 0 → ComplexMatrix2) = 0 := by
          funext p
          simp [edgeCoboundary]
        rw [e3, tracePair_zero_right]
        simp
      rw [e1, e2] at h1
      exact h1
    have hDD := hD (J.2 i - a • ξ.2 i)
    have hz : J.2 i - a • ξ.2 i = 0 := by
      refine (edgePair_self_re (innB _ i.2) _).2 ?_
      rw [Submodule.coe_sub, Submodule.coe_smul, edgePair_sub_left, edgePair_smul_left,
        Complex.sub_re, Complex.re_ofReal_mul]
      rw [Submodule.coe_sub, Submodule.coe_smul] at hDD
      rw [hDD]
      ring
    rw [sub_eq_zero.mp hz, inv_smul_smul₀ ha.ne']
  · let G : edgeFormSpace L n k k := ⟨linearChain ((0, ξ.2) : LevelForms L n k) k,
      linearChain_mem hcC _ k le_rfl⟩
    let B2 : edgeFormSpace L n k k := B - G
    have rel := hRel L hL k hk n hn B2
    let A1 : edgeFormSpace L n k 0 :=
      meshScaledResponse L n k (B2 : Edge L n k k → ComplexMatrix2)
    let nu : edgeFormSpace L n k k := periodicDefect L n k (B2 : Edge L n k k → ComplexMatrix2)
    let A3 : edgeFormSpace L n k 0 := ξ.1 - A1
    let m : edgeFormSpace L n k k := μ - nu
    obtain ⟨g, hg, e⟩ := linearTransport_eq_linearChain_add hcL hstep finS ξ k le_rfl
    have hsplit : linearChain ξ k =
        crossingSmoothingIter L n k k ξ.1 + (G : Edge L n k k → ComplexMatrix2) := by
      have e1 : ξ = ((ξ.1, 0) : LevelForms L n k) + ((0, ξ.2) : LevelForms L n k) := by
        simp
      have e2 := linearChain_add finS ((ξ.1, 0) : LevelForms L n k)
        ((0, ξ.2) : LevelForms L n k) k le_rfl
      rw [linearChain_of_snd_eq_zero ((ξ.1, 0) : LevelForms L n k) rfl k le_rfl, ← e1] at e2
      exact e2
    have hCAξ : crossingSmoothingIter L n k k ξ.1 =
        (B2 : Edge L n k k → ComplexMatrix2) - vertexCoboundary g := by
      have h := ht.top_eq
      rw [e, hsplit] at h
      have e3 : ((B2 : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2) =
          (B : Edge L n k k → ComplexMatrix2) - (G : Edge L n k k → ComplexMatrix2) := rfl
      rw [e3, ← h]
      abel
    have hCA3 : crossingSmoothingIter L n k k (A3 : Edge L n k 0 → ComplexMatrix2) =
        -vertexCoboundary g := by
      rw [← tm.crossing_eq A3]
      have e4 : crossingSmoothingToTop L n k A3 =
          crossingSmoothingToTop L n k ξ.1 - crossingSmoothingToTop L n k A1 := map_sub _ _ _
      rw [e4, Submodule.coe_sub, tm.crossing_eq, tm.crossing_eq, hCAξ]
      have e5 := rel.smoothing_eq
      rw [show crossingSmoothingIter L n k k (A1 : Edge L n k 0 → ComplexMatrix2) =
        (B2 : Edge L n k k → ComplexMatrix2) from e5]
      abel
    have hA1 : ∀ f : edgeFormSpace L n k 0,
        traceFinsumPairing (edgeCoboundary (A1 : Edge L n k 0 → ComplexMatrix2))
          (edgeCoboundary (f : Edge L n k 0 → ComplexMatrix2)) =
        edgeFormPairing (nu : Edge L n k k → ComplexMatrix2)
          (crossingSmoothingToTop L n k f : Edge L n k k → ComplexMatrix2) := by
      intro f
      have h := congrArg (fun X : edgeFormSpace L n k 0 =>
        edgeFormPairing (X : Edge L n k 0 → ComplexMatrix2) (f : Edge L n k 0 → ComplexMatrix2))
        rel.coboundary_eq
      rw [tm.coboundary_transpose, tm.crossing_transpose, tm.coboundary_eq, tm.coboundary_eq]
        at h
      exact h
    have hξ0 : ∀ f : edgeFormSpace L n k 0,
        (traceFinsumPairing (edgeCoboundary (ξ.1 : Edge L n k 0 → ComplexMatrix2))
          (edgeCoboundary (f : Edge L n k 0 → ComplexMatrix2))).re =
        (edgeFormPairing (μ : Edge L n k k → ComplexMatrix2)
          (crossingSmoothingToTop L n k f : Edge L n k k → ComplexMatrix2)).re := by
      intro f
      rw [hgrad0 f, hb, linearChain_of_snd_eq_zero _ rfl k le_rfl, tm.crossing_eq]
    have hstar : ∀ f : edgeFormSpace L n k 0,
        (traceFinsumPairing (edgeCoboundary (A3 : Edge L n k 0 → ComplexMatrix2))
          (edgeCoboundary (f : Edge L n k 0 → ComplexMatrix2))).re =
        (edgeFormPairing (m : Edge L n k k → ComplexMatrix2)
          (crossingSmoothingToTop L n k f : Edge L n k k → ComplexMatrix2)).re := by
      intro f
      rw [show (A3 : Edge L n k 0 → ComplexMatrix2) = (ξ.1 : Edge L n k 0 → ComplexMatrix2) - A1
          from rfl, edgeCoboundary_sub, tracePair_sub_left, Complex.sub_re, hξ0 f, hA1 f,
        show (m : Edge L n k k → ComplexMatrix2) = (μ : Edge L n k k → ComplexMatrix2) - nu
          from rfl, edgePair_sub_left, Complex.sub_re]
    have hmd : ∀ g ∈ vertexFunctionSpace L n k k,
        (edgeFormPairing (m : Edge L n k k → ComplexMatrix2) (vertexCoboundary g)).re = 0 := by
      intro g hg
      rw [show (m : Edge L n k k → ComplexMatrix2) = (μ : Edge L n k k → ComplexMatrix2) - nu
          from rfl, edgePair_sub_left, Complex.sub_re, hgauge g hg,
        show (nu : Edge L n k k → ComplexMatrix2) = _ from rfl, rel.pairing_vertex_eq_zero g hg]
      simp
    have hd0 : (traceFinsumPairing (edgeCoboundary (A3 : Edge L n k 0 → ComplexMatrix2))
        (edgeCoboundary (A3 : Edge L n k 0 → ComplexMatrix2))).re = 0 := by
      rw [hstar A3, tm.crossing_eq, hCA3]
      have e6 : -vertexCoboundary g = vertexCoboundary (-g) := by
        funext b
        simp only [vertexCoboundary, Pi.neg_apply]
        abel
      rw [e6]
      exact hmd _ ((vertexFunctionSpace L n k k).neg_mem hg)
    have hclosed : edgeCoboundary (A3 : Edge L n k 0 → ComplexMatrix2) = 0 :=
      (tracePair_self_re innP _ (edgeCoboundary_apply_mem A3.2)).2 hd0
    obtain ⟨g1, hg1, e7⟩ :=
      linearTransport_eq_linearChain_add hcL hstep finS ((A3, 0) : LevelForms L n k) k le_rfl
    rw [linearTransport_of_snd_eq_zero _ rfl k le_rfl, linearChain_of_snd_eq_zero _ rfl k le_rfl]
      at e7
    simp only at e7
    rw [hCA3] at e7
    obtain ⟨l', hl'⟩ := hrest (g1 - g) ((vertexFunctionSpace L n k k).sub_mem hg1 hg)
    let fl : edgeFormSpace L n k 0 :=
      ⟨vertexCoboundary (l' : Vertex L n k 0 → ComplexMatrix2), vertexCoboundary_mem l'.2⟩
    have e8 := linearTransport_of_gauge hLpos hstep l' ((fl, 0) : LevelForms L n k) rfl rfl k le_rfl
    rw [linearTransport_of_snd_eq_zero _ rfl k le_rfl, hl', vertexCoboundary_sub] at e8
    simp only at e8
    let E : edgeFormSpace L n k 0 := A3 - fl
    have hE0 : linearSmoothingIter L n k k (E : Edge L n k 0 → ComplexMatrix2) = 0 := by
      rw [← tm.linear_eq E]
      have e9 : linearSmoothingToTop L n k E =
          linearSmoothingToTop L n k A3 - linearSmoothingToTop L n k fl := map_sub _ _ _
      rw [e9, Submodule.coe_sub, tm.linear_eq, tm.linear_eq, e7, e8]
      abel
    have hEc : IsClosedEdgeForm (E : Edge L n k 0 → ComplexMatrix2) := by
      show edgeCoboundary ((A3 : Edge L n k 0 → ComplexMatrix2) -
        (fl : Edge L n k 0 → ComplexMatrix2)) = 0
      rw [edgeCoboundary_sub, hclosed,
        show edgeCoboundary (fl : Edge L n k 0 → ComplexMatrix2) = 0 from
          edgeCoboundary_vertexCoboundary _]
      simp
    obtain ⟨l2, hl2, e10⟩ := hK L hL k n hk hn E E.2 hEc hE0
    have hm0 : m = 0 := by
      obtain ⟨f, hf, e11⟩ := honto m m.2
      have h := hstar ⟨f, hf⟩
      rw [hclosed, tm.crossing_eq] at h
      simp only at h
      rw [e11] at h
      refine (edgePair_self_re (innB k le_rfl) m).2 ?_
      rw [← h]
      have : traceFinsumPairing (0 : Face L n k 0 → ComplexMatrix2)
          (edgeCoboundary (f : Edge L n k 0 → ComplexMatrix2)) = 0 := by
        rw [tracePair_comm, tracePair_zero_right]
      rw [this]
      simp
    refine ⟨G, ⟨(l' : Vertex L n k 0 → ComplexMatrix2) + l2,
      (vertexFunctionSpace L n k 0).add_mem l'.2 hl2⟩, rfl, ?_, ?_⟩
    · have := sub_eq_zero.mp hm0
      exact congrArg Subtype.val this
    · show (ξ.1 : Edge L n k 0 → ComplexMatrix2) = (A1 : Edge L n k 0 → ComplexMatrix2) +
        vertexCoboundary ((l' : Vertex L n k 0 → ComplexMatrix2) + l2)
      rw [vertexCoboundary_add, e10]
      show (ξ.1 : Edge L n k 0 → ComplexMatrix2) = (A1 : Edge L n k 0 → ComplexMatrix2) +
        ((fl : Edge L n k 0 → ComplexMatrix2) + ((ξ.1 : Edge L n k 0 → ComplexMatrix2) -
          (A1 : Edge L n k 0 → ComplexMatrix2) - (fl : Edge L n k 0 → ComplexMatrix2)))
      abel
end YangMills.Construction.RunningCouplingSlope.FirstOrderSolution
end
