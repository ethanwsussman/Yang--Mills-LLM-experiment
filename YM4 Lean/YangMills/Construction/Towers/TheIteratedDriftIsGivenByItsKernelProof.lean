import YangMills.Construction.Towers.FactsOnThePartsOfTheHessianOfTheWilsonActionProof
import YangMills.Construction.Towers.HessianOfTheWilsonActionProof
import YangMills.Construction.Towers.IteratedMapsReadTheBlocksProof
import YangMills.Construction.Towers.TheBackgroundsAreBoundedNearAPointProof
import YangMills.Construction.Towers.ThreeOperatorsOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.EntriesOfTheIteratedMapsProof
import YangMills.Construction.Towers.KernelOfAMapWithFinitelyManyEvaluations
import YangMills.Construction.Towers.TheIteratedDriftIsGivenByItsKernel
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IteratedDriftKernel
open _root_.YangMills.Construction.Matrices
open _root_.YangMills.Construction.PeriodicOperators
open _root_.YangMills.Construction.Tower.SupportOfMeans (DefinedAlike DependsOnlyOn)
open _root_.YangMills.Construction.Tower.SupportOfMeans.Unbounded (baseFields supportEdges meanAt)
open _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials (iterRatio iterMean)
theorem pauliCoeff_add (i : Fin 3) {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff i (X + Y) = pauliCoeff i X + pauliCoeff i Y := by apply _root_.YangMills.SharedProofs.p106 <;> assumption
theorem pauliCoeff_smul (i : Fin 3) (z : ℂ) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff i (z • X) = z * pauliCoeff i X := by apply _root_.YangMills.SharedProofs.p5172 <;> assumption
theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (s : σ) :
    ofPauliCoeffs c s ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem ofPauliCoeffs_add {σ : Type} (c c' : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (c + c') = ofPauliCoeffs c + ofPauliCoeffs c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_add <;> assumption
theorem ofPauliCoeffs_smul {σ : Type} (z : ℂ) (c : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (z • c) = z • ofPauliCoeffs c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_smul <;> assumption
theorem conjugateBy_traceless (V : ComplexMatrix2) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
theorem conjugateBy_add (V X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (X + Y) =
      ComplexMatrix2.conjugateBy V X + ComplexMatrix2.conjugateBy V Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (V X : ComplexMatrix2) (z : ℂ) :
    ComplexMatrix2.conjugateBy V (z • X) = z • ComplexMatrix2.conjugateBy V X := by
  simp only [ComplexMatrix2.conjugateBy, mul_smul_comm, smul_mul_assoc]
section SingleLattice
variable {a a' : ℝ}
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (e : InfiniteLattice.Link a) : extendOddly f e.opposite = -extendOddly f e := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem finite_links_at (y : InfiniteLattice.LatticePoint a) :
    {c : InfiniteLattice.Link a | c.initial = y ∨ c.terminal = y}.Finite := by apply _root_.YangMills.Construction.Tower.MeanStableFields.Infinite.finite_links_with_endpoint <;> assumption
end SingleLattice
variable {L k : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem ofCoeffs_of_isPos (c : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ)
    (e : Edge L k 0) (h : e.IsPositivelyOriented) :
    (edgePauliCoordinates L k 0).ofCoeffs c e = ofPauliCoeffs c ⟨e, h⟩ := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureHessianAtInfinity.edgeField_apply <;> assumption
theorem ofCoeffs_mem (hL : Conventions.IsAdmissibleBlockingFactor L)
    (c : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) :
    (edgePauliCoordinates L k 0).ofCoeffs c ∈ complexEdgeForms (meshAt L k 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.ThreeLocalOperators.ofCoeffs_mem_complexEdgeForms <;> assumption
theorem ofCoeffs_add (c c' : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) :
    (edgePauliCoordinates L k 0).ofCoeffs (c + c') =
      (edgePauliCoordinates L k 0).ofCoeffs c + (edgePauliCoordinates L k 0).ofCoeffs c' := by apply _root_.YangMills.Construction.Tower.FullSpace.WilsonHessianProof.coeffForm_add <;> assumption
theorem ofCoeffs_smul (z : ℂ) (c : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) :
    (edgePauliCoordinates L k 0).ofCoeffs (z • c) = z • (edgePauliCoordinates L k 0).ofCoeffs c := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundsBoundedNearPoint.ofCoeffs_smul <;> assumption
def verticesOfOrder (j : ℕ) (y : Vertex L k j) : Set (Vertex L k 0) :=
  {x | (x : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) j y}
def edgesOfOrder (j : ℕ) (y : Vertex L k j) : Set (Edge L k 0) :=
  {e | e.IsPositivelyOriented ∧ e.initial ∈ verticesOfOrder j y ∧ e.terminal ∈ verticesOfOrder j y}
theorem verticesOfOrder_subset_succ (h₄ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    {y : Vertex L k (j + 1)} {x : Vertex L k j}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y) :
    verticesOfOrder j x ⊆ verticesOfOrder (j + 1) y := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.verticesOfOrder_subset_succ <;> assumption
theorem contourLogDrift_congr (h₄ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    (V C C' : Edge L k j → ComplexMatrix2) (y : Vertex L k (j + 1))
    (h : ∀ e : Edge L k j, e.IsPositivelyOriented →
      (e.initial : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y →
      (e.terminal : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y → C e = C' e) :
    contourLogDrift V C y = contourLogDrift V C' y := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.contourLogDrift_congr <;> assumption
section Maps
variable (h₄ : BlockPathContourPivotStatement)
  (hRel : CovariantIterRelations)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
  (hD : _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials.Requirements L k)
  (hR : _root_.YangMills.Construction.Tower.SupportOfMeans.Unbounded.SideRequirements L k)
  {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
include hRel hL hU in
theorem complexIterDeriv_zero {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) : complexIterDeriv L k 0 U B = B := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.complexIterDeriv_zero_level <;> assumption
include hRel hL hD hR hU in
theorem complexIterDeriv_congr {j : ℕ} (hj : j ≤ k) {c : Edge L k j}
    (hc : c.IsPositivelyOriented) {B B' : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) (hB' : B' ∈ complexEdgeForms (meshAt L k 0))
    (h : ∀ e ∈ supportEdges c, B e = B' e) :
    complexIterDeriv L k j U B c = complexIterDeriv L k j U B' c := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.complexIterDeriv_congr <;> assumption
include h₄ hRel hL hk hD hR hU in
theorem iterContourLogDrift_congr : ∀ j ≤ k, ∀ (y : Vertex L k j)
    (B B' : Edge L k 0 → ComplexMatrix2), B ∈ complexEdgeForms (meshAt L k 0) →
    B' ∈ complexEdgeForms (meshAt L k 0) → (∀ e ∈ edgesOfOrder j y, B e = B' e) →
      iterContourLogDrift L k U j B y = iterContourLogDrift L k U j B' y := by
  intro j
  induction j with
  | zero =>
    intro _ y B B' _ _ _
    rfl
  | succ j ih =>
    intro hj y B B' hB hB' h
    have hj' : j < k := by omega
    simp only [iterContourLogDrift, Pi.add_apply]
    refine congrArg₂ (· + ·) ?_ ?_
    · simp only [adjointCubeAverage]
      refine congrArg _ (finsum_mem_congr rfl fun x hx => ?_)
      have inc := verticesOfOrder_subset_succ h₄ hL hk hj' (y := y) (x := x) hx
      rw [ih (by omega) x B B' hB hB' fun e he => h e ⟨he.1, inc he.2.1, inc he.2.2⟩]
    · refine contourLogDrift_congr h₄ hL hk hj' _ _ _ y fun c hc ht hh => ?_
      refine complexIterDeriv_congr hRel hL hD hR hU (by omega) hc hB hB' fun e he => h e ?_
      have inc₁ := verticesOfOrder_subset_succ h₄ hL hk hj' (y := y) (x := c.initial) ht
      have inc₂ := verticesOfOrder_subset_succ h₄ hL hk hj' (y := y) (x := c.terminal) hh
      refine ⟨he.1, ?_, ?_⟩
      · rcases he.2.1 with h' | h'
        · exact inc₁ h'
        · exact inc₂ h'
      · rcases he.2.2 with h' | h'
        · exact inc₁ h'
        · exact inc₂ h'
include hRel hL hU hD in
theorem complexIterDeriv_mem {j : ℕ} (hj : j ≤ k) {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) :
    complexIterDeriv L k j U B ∈ complexEdgeForms (meshAt L k j) := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.complexIterDeriv_mem <;> assumption
include hRel hL hU hD in
theorem complexIterDeriv_linear {j : ℕ} (hj : j ≤ k) {B B' : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) (hB' : B' ∈ complexEdgeForms (meshAt L k 0))
    (z : ℂ) :
    complexIterDeriv L k j U (B + B') =
        complexIterDeriv L k j U B + complexIterDeriv L k j U B' ∧
      complexIterDeriv L k j U (z • B) = z • complexIterDeriv L k j U B := by
  cases j with
  | zero =>
    rw [complexIterDeriv_zero hRel hL hU hB, complexIterDeriv_zero hRel hL hU hB',
      complexIterDeriv_zero hRel hL hU (Submodule.add_mem _ hB hB'),
      complexIterDeriv_zero hRel hL hU (Submodule.smul_mem _ z hB)]
    exact ⟨rfl, rfl⟩
  | succ i =>
    exact (hD.1 i (by omega) _ (hU.2 i (by omega)) U hU).linear_iter B hB B' hB' z
end Maps
section Step
variable {j : ℕ}
theorem adjointCubeAverage_mem (hfin : ∀ y : Vertex L k (j + 1),
      (cubeVertices L (meshAt L k j) y).Finite)
    (V : Edge L k j → ComplexMatrix2) {l : Vertex L k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless)
    (y : Vertex L k (j + 1)) : adjointCubeAverage V l y ∈ ComplexMatrix2.traceless := by
  simp only [adjointCubeAverage]
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  exact ComplexMatrix2.traceless.smul_mem _
    (Submodule.sum_mem _ fun x _ => conjugateBy_traceless _ (hl x))
theorem adjointCubeAverage_add (hfin : ∀ y : Vertex L k (j + 1),
      (cubeVertices L (meshAt L k j) y).Finite)
    (V : Edge L k j → ComplexMatrix2) (l l' : Vertex L k j → ComplexMatrix2) :
    adjointCubeAverage V (l + l') = adjointCubeAverage V l + adjointCubeAverage V l' := by
  funext y
  simp only [adjointCubeAverage, Pi.add_apply, finsum_mem_eq_finite_toFinset_sum _ (hfin y),
    conjugateBy_add, Finset.sum_add_distrib, smul_add]
theorem adjointCubeAverage_smul (hfin : ∀ y : Vertex L k (j + 1),
      (cubeVertices L (meshAt L k j) y).Finite)
    (V : Edge L k j → ComplexMatrix2) (l : Vertex L k j → ComplexMatrix2) (z : ℂ) :
    adjointCubeAverage V (z • l) = z • adjointCubeAverage V l := by
  funext y
  simp only [adjointCubeAverage, Pi.smul_apply, finsum_mem_eq_finite_toFinset_sum _ (hfin y),
    conjugateBy_smul]
  rw [← Finset.smul_sum, smul_comm]
theorem cubeVertices_finite (h₅ : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hj : j < k) (y : Vertex L k (j + 1)) :
    (cubeVertices L (meshAt L k j) y).Finite := by
  have hcubes := h₅ L k (j + 1) hL (by omega) (by omega) (by omega)
  have hcard := (hcubes.2.1 y).2.2.1
  have hpos : 0 < L ^ 4 := by
    have := hL.2
    positivity
  have hf : (cube L (meshAt L k j) y).Finite :=
    Set.finite_of_ncard_pos (hcard.symm ▸ hpos)
  exact hf.preimage Subtype.val_injective.injOn
end Step
theorem iterContourLogDrift_linear (h₅ : BlockStructure)
    (hRel : CovariantIterRelations)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hD : _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials.Requirements L k)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k) :
    ∀ j ≤ k,
      (∀ B ∈ complexEdgeForms (meshAt L k 0), ∀ y,
        iterContourLogDrift L k U j B y ∈ ComplexMatrix2.traceless) ∧
      (∀ B ∈ complexEdgeForms (meshAt L k 0), ∀ B' ∈ complexEdgeForms (meshAt L k 0),
        iterContourLogDrift L k U j (B + B') =
          iterContourLogDrift L k U j B + iterContourLogDrift L k U j B') ∧
      (∀ B ∈ complexEdgeForms (meshAt L k 0), ∀ z : ℂ,
        iterContourLogDrift L k U j (z • B) = z • iterContourLogDrift L k U j B) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun _ _ _ => ComplexMatrix2.traceless.zero_mem, fun _ _ _ _ => ?_, fun _ _ z => ?_⟩
    · funext y
      simp [iterContourLogDrift]
    · funext y
      simp [iterContourLogDrift]
  | succ j ih =>
    intro hj
    have hj' : j < k := hj
    obtain ⟨v, a, s⟩ := ih hj'.le
    have hS := hD.1 j hj' _ (hU.2 j hj') U hU
    have hfin := cubeVertices_finite (j := j) h₅ hL hk hj'
    have Qm := fun B (hB : B ∈ complexEdgeForms (meshAt L k 0)) =>
      complexIterDeriv_mem hRel hL hD hU hj'.le hB
    refine ⟨fun B hB y => ?_, fun B hB B' hB' => ?_, fun B hB z => ?_⟩
    · exact ComplexMatrix2.traceless.add_mem (adjointCubeAverage_mem hfin _ (v B hB) y)
        (hS.mem_contour y _ (Qm B hB))
    · simp only [iterContourLogDrift]
      rw [(complexIterDeriv_linear hRel hL hD hU hj'.le hB hB' 0).1,
        (hS.linear_contour _ (Qm B hB) _ (Qm B' hB') 0).1, a B hB B' hB',
        adjointCubeAverage_add hfin]
      abel
    · simp only [iterContourLogDrift]
      rw [(complexIterDeriv_linear hRel hL hD hU hj'.le hB hB z).2,
        (hS.linear_contour _ (Qm B hB) _ (Qm B hB) z).2, s B hB z, adjointCubeAverage_smul hfin,
        smul_add]
theorem edgesOfOrder_finite (h₄ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (y : Vertex L k k) :
    (edgesOfOrder k y).Finite := by
  have H := (h₄ L hL k k k hk le_rfl le_rfl).2.1.ncard_eq
  rw [Nat.sub_self] at H
  have h0 : 0 < L := by
    have := hL.2
    omega
  have hf : (cubeOfOrder L (meshAt L k 0) k y).Finite :=
    Set.finite_of_ncard_pos (by rw [H y]; exact pow_pos h0 _)
  have hs : (verticesOfOrder k y).Finite := hf.preimage Subtype.val_injective.injOn
  exact (hs.biUnion fun x _ => finite_links_at x).subset fun e he =>
    mem_iUnion₂.2 ⟨e.initial, he.2.1, Or.inl rfl⟩
theorem driftKernelRepresents_holds
    (h₁ : _root_.YangMills.Construction.Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (h₂ : _root_.YangMills.Construction.Tower.SupportOfMeans.SupportOfMeansHolds)
    (h₃ : CovariantIterRelations)
    (h₄ : BlockPathContourPivotStatement)
    (h₅ : BlockStructure)
    (h₆ : FiniteSupportKernel.KernelOfFiniteSupportMap) : DriftKernelRepresents := by
  intro L hL k hk U hU
  have hD := (h₁ L hL k hk).2
  have hR := (h₂ L hL k hk).2
  obtain ⟨v, a, s⟩ := iterContourLogDrift_linear h₅ h₃ hL hk hD hU k le_rfl
  have hm := ofCoeffs_mem (k := k) hL
  let M := PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L k 0) (vertexCoordinate (Vertex L k k))
    (iterContourLogDrift L k U k)
  have hA : ∀ f g, M (f + g) = M f + M g := by
    intro f g
    have hv : iterContourLogDrift L k U k ((edgePauliCoordinates L k 0).ofCoeffs (f + g)) =
        iterContourLogDrift L k U k ((edgePauliCoordinates L k 0).ofCoeffs f) +
          iterContourLogDrift L k U k ((edgePauliCoordinates L k 0).ofCoeffs g) :=
      (congrArg _ (ofCoeffs_add f g)).trans (a _ (hm f) _ (hm g))
    funext ι
    change pauliCoeff ι.1 (iterContourLogDrift L k U k _ ι.2) = _
    rw [hv]
    exact pauliCoeff_add ι.1 (v _ (hm f) ι.2) (v _ (hm g) ι.2)
  have hS : ∀ (c : ℂ) f, M (c • f) = c • M f := by
    intro c f
    have hv : iterContourLogDrift L k U k ((edgePauliCoordinates L k 0).ofCoeffs (c • f)) =
        c • iterContourLogDrift L k U k ((edgePauliCoordinates L k 0).ofCoeffs f) :=
      (congrArg _ (ofCoeffs_smul c f)).trans (s _ (hm f) c)
    funext ι
    change pauliCoeff ι.1 (iterContourLogDrift L k U k _ ι.2) = _
    rw [hv]
    exact pauliCoeff_smul ι.1 c (v _ (hm f) ι.2)
  have hF : ∀ ι', ∃ A : Finset (Fin 3 × PositiveEdge (meshAt L k 0)),
      ∀ f g : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ,
        (∀ ι ∈ A, f ι = g ι) → M f ι' = M g ι' := by
    rintro ⟨i', y⟩
    have hb : {p : PositiveEdge (meshAt L k 0) | p.1 ∈ edgesOfOrder k y}.Finite :=
      (edgesOfOrder_finite h₄ hL hk y).preimage Subtype.val_injective.injOn
    have hp : ((univ : Set (Fin 3)) ×ˢ
        {p : PositiveEdge (meshAt L k 0) | p.1 ∈ edgesOfOrder k y}).Finite :=
      Set.finite_univ.prod hb
    refine ⟨hp.toFinset, fun f g h => ?_⟩
    have hv := iterContourLogDrift_congr h₄ h₃ hL hk hD hR hU k le_rfl y _ _ (hm f) (hm g)
      fun e he' => by
        rw [ofCoeffs_of_isPos f e he'.1, ofCoeffs_of_isPos g e he'.1]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h (i, ⟨e, he'.1⟩) (hp.mem_toFinset.2 ⟨mem_univ _, he'⟩)]
    change pauliCoeff i' _ = pauliCoeff i' _
    rw [hv]
  have H := h₆ _ _ M hA hS hF
  change Represents (kernelOfMap M) M
  rw [H.2]
  exact H.1
end YangMills.Construction.Tower.FullSpace.IteratedDriftKernel
end
