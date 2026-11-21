import YangMills.Construction.Towers.EntriesOfTheIteratedMapsProof
import YangMills.Construction.Towers.TheActionAndCurrentTermsOfTheKernelAreLocalProof
import YangMills.Construction.Towers.TheIteratedDriftIsGivenByItsKernel
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BasisFormLocality
open Matrices
open PeriodicOperators FieldValueFunctions IteratedKernelEntries
open UnsymmetrisedKernelTerms
open PeriodicOperators.HolomorphicCoordinateClosure
open FieldValueFunctions.LocalComponents
open ReadsCubes (IsFinitelySupportedForm LocalAt cubePositiveEdges cubeVertices)
open _root_.YangMills.Construction.Tower.AsDifferentials (IsLinearOn)
section Coefficients
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCombination_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem pauliCoeff_finset_sum_smul {α : Type} (I : Finset α) (c : α → ℂ) (X : α → ComplexMatrix2)
    (hX : ∀ i ∈ I, X i ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (∑ i ∈ I, c i • X i) = ∑ i ∈ I, c i * pauliCoeff a (X i) := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.pauliCoeff_finsetSum <;> assumption
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
end Coefficients
section Geometry
variable {a : ℝ}
theorem finite_latticePoints_near (ha : 0 < a) (x : InfiniteLattice.AmbientSpace) (r : ℝ) :
    {s : InfiniteLattice.LatticePoint a |
      ∀ i, |(s : InfiniteLattice.AmbientSpace) i - x i| < r}.Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.finite_points_near <;> assumption
theorem finite_links_near (ha : 0 < a) (x : InfiniteLattice.AmbientSpace) (r : ℝ) :
    {b : InfiniteLattice.Link a | ∀ i, |(b.initial : InfiniteLattice.AmbientSpace) i - x i| < r ∧
      |(b.terminal : InfiniteLattice.AmbientSpace) i - x i| < r}.Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.finite_links_near <;> assumption
theorem abs_sub_centre_lt_of_mem_cubeOfOrder {a' : ℝ} (ha' : 0 < a') {L n : ℕ}
    {y : InfiniteLattice.LatticePoint a} {x : InfiniteLattice.AmbientSpace}
    (hx : x ∈ cubeOfOrder L a' n y) (i : Fin 4) :
    |x i - (y : InfiniteLattice.AmbientSpace) i| < (L : ℝ) ^ n * a' / 2 := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.abs_sub_centre_lt_of_mem_cubeOfOrder <;> assumption
theorem extendOddly_of_isPositivelyOriented (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_of_pos <;> assumption
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) : extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
end Geometry
section Spacing
variable {L k j : ℕ}
theorem meshAt_pos (hL : 0 < L) : 0 < meshAt L k j :=
  zpow_pos (by exact_mod_cast hL) _
theorem meshAt_eq_pow_mul (hL : 0 < L) :
    meshAt L k j = (L : ℝ) ^ j * meshAt L k 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.meshAt_eq_pow_mul <;> assumption
theorem meshAt_self (hL : 0 < L) : meshAt L k k = 1 := by
  simp [meshAt]
theorem basisForm_of_isPositivelyOriented (a : Fin 3) (b : PositiveEdge (meshAt L k j))
    {c : Edge L k j} (hc : c.IsPositivelyOriented) :
    (basisForm a b : Edge L k j → ComplexMatrix2) c =
      open Classical in if c = b.1 then ComplexMatrix2.pauliFamily a else 0 := by
  simp [basisForm, extendOddly, hc]
theorem basisForm_mem (hL : 0 < L) (a : Fin 3) (b : PositiveEdge (meshAt L k j)) :
    (basisForm a b : Edge L k j → ComplexMatrix2) ∈ complexEdgeForms (meshAt L k j) := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.basisForm_mem <;> assumption
end Spacing
section Maps
open AsDifferentials (iterRatio iterLogRatio iterMean)
variable {L k : ℕ}
section Iterates
variable (hRel : CovariantIterRelations)
  (hLin : CovariantStepComplexLinear)
  (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hD : AsDifferentials.Requirements L k)
  {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
include hRel hLin hL hD hU in
theorem iterContourLogDrift_traceless_and_linear : ∀ j ≤ k,
    (∀ B ∈ complexEdgeForms (meshAt L k 0), ∀ y,
      iterContourLogDrift L k U j B y ∈ ComplexMatrix2.traceless) ∧
      IsLinearOn (complexEdgeForms (meshAt L k 0)) (iterContourLogDrift L k U j) := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.iterContourLogDrift_traceless_linear <;> assumption
end Iterates
end Maps
section Kernels
variable {L k : ℕ}
open Classical in
theorem edgePauliCoordinates_ofCoeffs_single {j : ℕ} (a : Fin 3) (b : PositiveEdge (meshAt L k j)) :
    (edgePauliCoordinates L k j).ofCoeffs (Pi.single (a, b) 1) = basisForm a b := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.edgePauliCoordinates_ofCoeffs_single <;> assumption
theorem kernel_entry_of_represents {r r' : PauliComponentsOfSymmetricKernel}
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    {T : KernelMatrix r.Index r'.Index} (h : Represents T (r.mapOnCoeffs r' m)) (ι' : r'.Index)
    (ι : r.Index) : open Classical in
    T ι' ι = r'.coeffs (m (r.ofCoeffs (Pi.single ι 1))) ι' := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.kernel_apply_of_represents <;> assumption
end Kernels
section Sets
variable {L k : ℕ}
theorem backgroundCoords_finite (hL : 0 < L) {S : Set (Edge L k 0)} (hS : S.Finite) :
    (backgroundCoords L k hL S).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValueFunctions.LocalComponents.backgroundCoords_finite <;> assumption
theorem backgroundCoords_mono (hL : 0 < L) {S S' : Set (Edge L k 0)} (h : S ⊆ S') :
    backgroundCoords L k hL S ⊆ backgroundCoords L k hL S' := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.backgroundCoords_mono <;> assumption
theorem edgesNear_finite (hL : 0 < L) (x : InfiniteLattice.AmbientSpace) (r : ℝ) :
    (edgesNear L k x r).Finite :=
  finite_links_near (meshAt_pos hL) x r
theorem edgesNear_mono {x x' : InfiniteLattice.AmbientSpace} {r r' : ℝ}
    (h : ∀ i, |x i - x' i| + r ≤ r') : edgesNear L k x r ⊆ edgesNear L k x' r' := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.edgesNear_mono <;> assumption
theorem basisForm_isFinitelySupported (hL : 0 < L) (a : Fin 3)
    (b : PositiveEdge (meshAt L k 0)) :
    IsFinitelySupportedForm (basisForm a b : Edge L k 0 → ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.basisForm_finitelySupported <;> assumption
theorem zero_isFinitelySupported :
    IsFinitelySupportedForm (0 : Edge L k 0 → ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.isFinitelySupportedForm_zero <;> assumption
end Sets
section Difference
variable {a : ℝ}
theorem conjugateBy_traceless_of_traceless (X : ComplexMatrix2) {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy X Y ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
theorem conjugateBy_zero_right (V : ComplexMatrix2) : ComplexMatrix2.conjugateBy V 0 = 0 := by
  simp [ComplexMatrix2.conjugateBy]
theorem conjugateBy_pauliCombination (V : ComplexMatrix2) (c : Fin 3 → ℂ) :
    ComplexMatrix2.conjugateBy V (∑ a, c a • ComplexMatrix2.pauliFamily a) =
      ∑ a, c a • ComplexMatrix2.conjugateBy V (ComplexMatrix2.pauliFamily a) := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelTermsLocality.conjugateBy_sum_smul <;> assumption
theorem covDiff_of_isPositivelyOriented (V : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2) {c : InfiniteLattice.Link a}
    (hc : c.IsPositivelyOriented) :
    covDiff V l c = ComplexMatrix2.conjugateBy (V c) (l c.terminal) - l c.initial :=
  extendOddly_of_isPositivelyOriented _ hc
theorem initial_ne_terminal (ha : 0 < a) (c : InfiniteLattice.Link a) :
    c.initial ≠ c.terminal := by
  intro h
  obtain ⟨μ, e | e⟩ := c.isAdjacent
  · rw [h, sub_self] at e
    have := congrArg (fun y : InfiniteLattice.LatticePoint _ =>
      (y : InfiniteLattice.AmbientSpace) μ) e
    simp [InfiniteLattice.axisStep] at this
    exact ha.ne this
  · rw [h, sub_self] at e
    have := congrArg (fun y : InfiniteLattice.LatticePoint _ =>
      (y : InfiniteLattice.AmbientSpace) μ) e
    simp [InfiniteLattice.axisStep] at this
    exact ha.ne' this
theorem pauliCoeff_covDiff {L k : ℕ} (hL : 0 < L) (V : Edge L k 0 → ComplexMatrix2)
    (l : Vertex L k 0 → ComplexMatrix2) (hl : ∀ x, l x ∈ ComplexMatrix2.traceless)
    {c : Edge L k 0} (hc : c.IsPositivelyOriented) (a' : Fin 3) :
    pauliCoeff a' (covDiff V l c) =
      (∑ e, pauliCoeff e (l c.terminal) * pauliCoeff a'
        (covDiff V (vertexBasisFunction e c.terminal) c)) +
      ∑ e, pauliCoeff e (l c.initial) * pauliCoeff a'
        (covDiff V (vertexBasisFunction e c.initial) c) := by
  classical
  have hne := initial_ne_terminal (meshAt_pos (k := k) (j := 0) hL) c
  have eh : ∀ e, covDiff V (vertexBasisFunction e c.terminal) c =
      ComplexMatrix2.conjugateBy (V c) (ComplexMatrix2.pauliFamily e) := fun e => by
    rw [covDiff_of_isPositivelyOriented _ _ hc]
    simp [vertexBasisFunction, hne]
  have et : ∀ e, covDiff V (vertexBasisFunction e c.initial) c =
      -ComplexMatrix2.pauliFamily e := fun e => by
    rw [covDiff_of_isPositivelyOriented _ _ hc]
    simp [vertexBasisFunction, hne.symm, conjugateBy_zero_right]
  have hP : ∀ e, ComplexMatrix2.conjugateBy (V c) (ComplexMatrix2.pauliFamily e) ∈
      ComplexMatrix2.traceless :=
    fun e => conjugateBy_traceless_of_traceless _ (pauliFamily_mem_traceless e)
  have hN : ∀ e, -ComplexMatrix2.pauliFamily e ∈ ComplexMatrix2.traceless :=
    fun e => ComplexMatrix2.traceless.neg_mem (pauliFamily_mem_traceless e)
  have E : covDiff V l c =
      (∑ e, pauliCoeff e (l c.terminal) •
        ComplexMatrix2.conjugateBy (V c) (ComplexMatrix2.pauliFamily e)) +
        ∑ e, pauliCoeff e (l c.initial) • (-ComplexMatrix2.pauliFamily e) := by
    rw [covDiff_of_isPositivelyOriented _ _ hc]
    conv_lhs =>
      rw [← pauliCombination_pauliCoeff (hl c.terminal), ← pauliCombination_pauliCoeff (hl c.initial)]
    rw [conjugateBy_pauliCombination]
    simp only [smul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]
  simp only [eh, et]
  rw [E, pauliCoeff_add
    (ComplexMatrix2.traceless.sum_mem fun e _ => ComplexMatrix2.traceless.smul_mem _ (hP e))
    (ComplexMatrix2.traceless.sum_mem fun e _ => ComplexMatrix2.traceless.smul_mem _ (hN e)),
    pauliCoeff_finset_sum_smul _ _ _ fun e _ => hP e,
    pauliCoeff_finset_sum_smul _ _ _ fun e _ => hN e]
end Difference
section Site
variable {L k : ℕ}
theorem gaugeParam_of_coarse {U B : Edge L k 0 → ComplexMatrix2} {x : Vertex L k 0}
    {y : Vertex L k k} (h : y.1 = x.1) :
    gaugeParam U B x = iterContourLogDrift L k U k B y := by
  have hex : ∃ y : Vertex L k k, y.1 = x.1 := ⟨y, h⟩
  unfold gaugeParam zeroExtend
  rw [dif_pos hex]
  congr 1
  exact Subtype.ext (hex.choose_spec.trans h.symm)
theorem gaugeParam_of_not_coarse {U B : Edge L k 0 → ComplexMatrix2} {x : Vertex L k 0}
    (h : ¬∃ y : Vertex L k k, y.1 = x.1) : gaugeParam U B x = 0 := by
  unfold gaugeParam zeroExtend
  rw [dif_neg h]
structure BelowRadiusData (hL : 0 < L) (ρ : ℝ) : Prop where
  small_of_below : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
    FieldValueFunctions.gaugeFieldOfCoeffs hL f ∈ smallIterateFields L k
  drift_traceless : ∀ U ∈ smallIterateFields L k, ∀ B ∈ complexEdgeForms (meshAt L k 0), ∀ y,
    iterContourLogDrift L k U k B y ∈ ComplexMatrix2.traceless
  drift_zero : ∀ U ∈ smallIterateFields L k, iterContourLogDrift L k U k 0 = 0
  local_cubes : ∀ U ∈ smallIterateFields L k, LocalAt U
  represents : ∀ U ∈ smallIterateFields L k, Represents
    ((edgePauliCoordinates L k 0).kernel (vertexCoordinate (Vertex L k k)) (iterContourLogDrift L k U k))
    (PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L k 0) (vertexCoordinate (Vertex L k k))
      (iterContourLogDrift L k U k))
  entry_holomorphic : ∀ (y : Vertex L k k) (a' : Fin 3) ι,
    HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
      (backgroundCoords L k hL (edgesNear L k y 2))
      fun f => driftKernelFn L k hL f (a', y) ι
  closure : ∀ T : Set (fieldPeriodicData L k hL).Carrier, T.Finite →
    ClosureProperties (fieldPeriodicData L k hL) ρ T
  covDiffEntry_holomorphic : ∀ (a' a : Fin 3) (b' : PositiveEdge (meshAt L k 0))
    (x : Vertex L k 0),
    HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ (backgroundCoords L k hL {b'.1})
      (covDiffEntry L k hL a' b' a x)
variable {hL : 0 < L} {ρ : ℝ} (S : BelowRadiusData (L := L) (k := k) hL ρ)
abbrev coordsNearTail (L k : ℕ) (hL : 0 < L) (b : PositiveEdge (meshAt L k 0)) :
    Set (fieldPeriodicData L k hL).Carrier :=
  backgroundCoords L k hL (edgesNear L k b.1.initial (7 / 2))
theorem coordsNearTail_finite (b : PositiveEdge (meshAt L k 0)) :
    (coordsNearTail L k hL b).Finite :=
  backgroundCoords_finite hL (edgesNear_finite hL _ _)
include S in
theorem iterContourLogDrift_basisForm_eq_zero {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) (a : Fin 3) (b : PositiveEdge (meshAt L k 0))
    {y : Vertex L k k} (hy : b.1 ∉ cubePositiveEdges y) :
    iterContourLogDrift L k U k (basisForm a b) y = 0 := by
  have e := (S.local_cubes U hU).contourDrift_local y (basisForm a b) 0
    (basisForm_isFinitelySupported hL a b) zero_isFinitelySupported fun c hc => by
      have hne : c ≠ b.1 := fun e => hy (e ▸ hc)
      rw [basisForm_of_isPositivelyOriented a b hc.1, if_neg hne]
      rfl
  rw [e, S.drift_zero U hU]
  rfl
theorem abs_sub_initial_lt_half (hL : 0 < L) {b : Edge L k 0} {y : Vertex L k k}
    (hy : b ∈ cubePositiveEdges y) (i : Fin 4) :
    |(y : InfiniteLattice.AmbientSpace) i - (b.initial : InfiniteLattice.AmbientSpace) i| <
      1 / 2 := by
  have h := abs_sub_centre_lt_of_mem_cubeOfOrder (meshAt_pos (k := k) (j := 0) hL) hy.2.1 i
  have e : (L : ℝ) ^ k * meshAt L k 0 = 1 := by
    rw [← meshAt_eq_pow_mul hL, meshAt_self hL]
  rw [e] at h
  rw [abs_sub_comm]
  exact h
include S in
theorem gaugeParam_basisForm_eq_zero {f : (fieldPeriodicData L k hL).Carrier → ℂ}
    (hf : IsSupBelow (fieldPeriodicData L k hL) f ρ)
    (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) {p : Vertex L k 0}
    (hp : p ∉ verticesWithin L k b.1.initial (1 / 2)) :
    gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm a b) p = 0 := by
  by_cases h : ∃ y : Vertex L k k, y.1 = p.1
  · obtain ⟨y, hy⟩ := h
    rw [gaugeParam_of_coarse hy]
    refine iterContourLogDrift_basisForm_eq_zero S (S.small_of_below f hf) a b
      fun hb => hp fun i => ?_
    have := abs_sub_initial_lt_half hL hb i
    have e : (p : InfiniteLattice.AmbientSpace) = (y : InfiniteLattice.AmbientSpace) := hy.symm
    rw [e]
    exact this
  · exact gaugeParam_of_not_coarse h
include S in
theorem gaugeParam_basisForm_mem {f : (fieldPeriodicData L k hL).Carrier → ℂ}
    (hf : IsSupBelow (fieldPeriodicData L k hL) f ρ)
    (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) (p : Vertex L k 0) :
    gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm a b) p ∈
      ComplexMatrix2.traceless := by
  by_cases h : ∃ y : Vertex L k k, y.1 = p.1
  · obtain ⟨y, hy⟩ := h
    rw [gaugeParam_of_coarse hy]
    exact S.drift_traceless _ (S.small_of_below f hf) _ (basisForm_mem hL a b) y
  · rw [gaugeParam_of_not_coarse h]
    exact ComplexMatrix2.traceless.zero_mem
include S in
theorem driftKernelFn_eq_pauliCoeff {f : (fieldPeriodicData L k hL).Carrier → ℂ}
    (hf : IsSupBelow (fieldPeriodicData L k hL) f ρ)
    (a' a : Fin 3) (y : Vertex L k k) (b : PositiveEdge (meshAt L k 0)) :
    driftKernelFn L k hL f (a', y) (a, b) =
      pauliCoeff a' (iterContourLogDrift L k (FieldValueFunctions.gaugeFieldOfCoeffs hL f) k
        (basisForm a b) y) := by
  classical
  have e := kernel_entry_of_represents (S.represents _ (S.small_of_below f hf)) (a', y) (a, b)
  rw [edgePauliCoordinates_ofCoeffs_single] at e
  exact e
include S in
theorem gaugeParam_basisForm_holomorphic (a e : Fin 3) (b : PositiveEdge (meshAt L k 0))
    (p : Vertex L k 0) :
    HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ (coordsNearTail L k hL b) fun f =>
      pauliCoeff e
        (gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm a b) p) := by
  have hC := S.closure _ (coordsNearTail_finite (hL := hL) b)
  by_cases h : ∃ y : Vertex L k k, y.1 = p.1
  · obtain ⟨y, hy⟩ := h
    by_cases hb : b.1 ∈ cubePositiveEdges y
    · have hsub : backgroundCoords L k hL (edgesNear L k y 2) ⊆ coordsNearTail L k hL b :=
        backgroundCoords_mono hL (edgesNear_mono fun i => by
          have := abs_sub_initial_lt_half hL hb i
          linarith)
      refine hC.congr_below _ _ (fun ζ hζ => ?_)
        (hC.of_subset _ _ hsub (S.entry_holomorphic y e (a, b)))
      rw [gaugeParam_of_coarse hy]
      exact driftKernelFn_eq_pauliCoeff S hζ e a y b
    · refine hC.congr_below (fun _ => 0) _ (fun ζ hζ => ?_) (hC.const 0)
      rw [gaugeParam_of_coarse hy,
        iterContourLogDrift_basisForm_eq_zero S (S.small_of_below ζ hζ) a b hb, pauliCoeff_zero]
  · refine hC.congr_below (fun _ => 0) _ (fun ζ _ => ?_) (hC.const 0)
    rw [gaugeParam_of_not_coarse h, pauliCoeff_zero]
theorem shiftedForm_of_isPositivelyOriented (U B : Edge L k 0 → ComplexMatrix2)
    {c : Edge L k 0} (hc : c.IsPositivelyOriented) :
    shiftedForm U B c =
      B c + (ComplexMatrix2.conjugateBy (U c) (gaugeParam U B c.terminal) -
        gaugeParam U B c.initial) := by
  show B c + covDiff U (gaugeParam U B) c = _
  rw [covDiff_of_isPositivelyOriented _ _ hc]
theorem abs_terminal_sub_initial_le_one (hL : 0 < L) (c : Edge L k 0) (i : Fin 4) :
    |(c.terminal : InfiniteLattice.AmbientSpace) i -
      (c.initial : InfiniteLattice.AmbientSpace) i| ≤ 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelTermsLocality.abs_terminal_sub_initial_le_one <;> assumption
include S in
theorem shiftedForm_basisForm_eq_zero {f : (fieldPeriodicData L k hL).Carrier → ℂ}
    (hf : IsSupBelow (fieldPeriodicData L k hL) f ρ)
    (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) {c : PositiveEdge (meshAt L k 0)}
    (hc : c ∉ positiveEdgesWithin L k b.1.initial (3 / 2)) :
    shiftedForm (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm a b) c.1 = 0 := by
  have near : ∀ x y : InfiniteLattice.AmbientSpace, ∀ i, |x i - y i| ≤ 1 →
      ∀ z : InfiniteLattice.AmbientSpace,
      |y i - z i| < 1 / 2 → |x i - z i| < 3 / 2 ∧ |y i - z i| < 3 / 2 :=
    fun x y i h z h' => by
      refine ⟨?_, by linarith⟩
      linarith [abs_sub_le (x i) (y i) (z i)]
  have hne : c.1 ≠ b.1 := fun e => hc fun i => by
    have h₁ := abs_terminal_sub_initial_le_one hL b.1 i
    rw [e]
    exact ⟨by rw [sub_self, abs_zero]; norm_num, by linarith⟩
  have hh : c.1.terminal ∉ verticesWithin L k b.1.initial (1 / 2) := fun h => hc fun i => by
    have h₁ := near _ _ i (by rw [abs_sub_comm]; exact abs_terminal_sub_initial_le_one hL c.1 i)
      _ (h i)
    exact ⟨h₁.1, h₁.2⟩
  have ht : c.1.initial ∉ verticesWithin L k b.1.initial (1 / 2) := fun h => hc fun i => by
    have h₁ := near _ _ i (abs_terminal_sub_initial_le_one hL c.1 i) _ (h i)
    exact ⟨h₁.2, h₁.1⟩
  rw [shiftedForm_of_isPositivelyOriented _ _ c.2, gaugeParam_basisForm_eq_zero S hf a b hh,
    gaugeParam_basisForm_eq_zero S hf a b ht, conjugateBy_zero_right,
    basisForm_of_isPositivelyOriented a b c.2, if_neg hne]
  simp
include S in
theorem shiftedForm_basisForm_mem {f : (fieldPeriodicData L k hL).Carrier → ℂ}
    (hf : IsSupBelow (fieldPeriodicData L k hL) f ρ)
    (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    shiftedForm (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm a b) ∈
      complexEdgeForms (meshAt L k 0) := by
  refine Submodule.add_mem _ (basisForm_mem hL a b) ⟨fun c hc => ?_,
    fun c => extendOddly_opposite (meshAt_pos hL) _ c⟩
  rw [covDiff_of_isPositivelyOriented _ _ hc]
  exact ComplexMatrix2.traceless.sub_mem
    (conjugateBy_traceless_of_traceless _ (gaugeParam_basisForm_mem S hf a b _))
    (gaugeParam_basisForm_mem S hf a b _)
include S in
theorem shiftedForm_basisForm_holomorphic (a a' : Fin 3) (b : PositiveEdge (meshAt L k 0))
    {c : PositiveEdge (meshAt L k 0)} (hc : c ∈ positiveEdgesWithin L k b.1.initial (3 / 2)) :
    HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ (coordsNearTail L k hL b) fun f =>
      pauliCoeff a'
        (restrictToPositiveEdges
          (shiftedForm (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm a b)) c) := by
  have hC := S.closure _ (coordsNearTail_finite (hL := hL) b)
  have hsub : backgroundCoords L k hL {c.1} ⊆ coordsNearTail L k hL b :=
    backgroundCoords_mono hL fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      intro i
      have := hc i
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hd : ∀ e x, HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ (coordsNearTail L k hL b)
      (covDiffEntry L k hL a' c e x) :=
    fun e x => hC.of_subset _ _ hsub (S.covDiffEntry_holomorphic a' e c x)
  have hsum : ∀ x : Vertex L k 0,
      HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ (coordsNearTail L k hL b)
      fun f => ∑ e ∈ (Finset.univ : Finset (Fin 3)), pauliCoeff e
        (gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL f) (basisForm a b) x) *
          covDiffEntry L k hL a' c e x f := fun x =>
    hC.sum _ _ fun e _ => hC.mul _ _ (gaugeParam_basisForm_holomorphic S a e b x) (hd e x)
  refine hC.congr_below _ _ (fun ζ hζ => ?_) (hC.add _ _ (hC.const
    (pauliCoeff a' ((basisForm a b : Edge L k 0 → ComplexMatrix2) c.1)))
    (hC.add _ _ (hsum c.1.terminal) (hsum c.1.initial)))
  have hB : (basisForm a b : Edge L k 0 → ComplexMatrix2) c.1 ∈ ComplexMatrix2.traceless :=
    (basisForm_mem hL a b).1 c.1 c.2
  have hD : covDiff (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
      (gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (basisForm a b)) c.1 ∈
        ComplexMatrix2.traceless := by
    rw [covDiff_of_isPositivelyOriented _ _ c.2]
    exact ComplexMatrix2.traceless.sub_mem
      (conjugateBy_traceless_of_traceless _ (gaugeParam_basisForm_mem S hζ a b _))
      (gaugeParam_basisForm_mem S hζ a b _)
  show _ = pauliCoeff a' ((basisForm a b : Edge L k 0 → ComplexMatrix2) c.1 +
    covDiff (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ)
      (gaugeParam (FieldValueFunctions.gaugeFieldOfCoeffs hL ζ) (basisForm a b)) c.1)
  rw [pauliCoeff_add hB hD, pauliCoeff_covDiff hL _ _
    (gaugeParam_basisForm_mem S hζ a b) c.2 a']
  rfl
end Site
theorem elementaryFormLocality_holds (h₁ : SmallIterates.SmallIteratesNearOne)
    (h₂ : IteratedKernelEntries.Claim)
    (h₃ : ReadsCubes.Statement)
    (h₄ : IteratedDriftKernel.DriftKernelRepresents)
    (h₅ : FieldValueFunctions.LocalComponents.EntriesAreLocalAndEntire)
    (h₆ : HolomorphicCoordinateClosure.ClosureHolds)
    (h₇ : _root_.YangMills.Construction.Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (h₈ : CovariantIterRelations)
    (h₉ : CovariantStepComplexLinear) : ElementaryFormLocality := by
  classical
  intro L hL0 hL k hk
  obtain ⟨ρ₁, hρ₁, hEn⟩ := h₂ L hL0 hL k hk
  obtain ⟨ρ₂, hρ₂, hSm₂⟩ := (h₁ L hL0 hL k hk).2
  have hD := (h₇ L hL k hk).2
  obtain ⟨hE₁, hE₂, -⟩ := h₅ L hL0 hL k
  have hm₁ : min ρ₁ ρ₂ ≤ ρ₁ := min_le_left _ _
  have hm₂ : min ρ₁ ρ₂ ≤ ρ₂ := min_le_right _ _
  have hρ : 0 < min ρ₁ ρ₂ := lt_min hρ₁ hρ₂
  have hfacts := fun U hU =>
    iterContourLogDrift_traceless_and_linear h₈ h₉ hL hD (U := U) hU k le_rfl
  have S : BelowRadiusData (L := L) (k := k) hL0 (min ρ₁ ρ₂) :=
    { small_of_below := fun f hf => by
        obtain ⟨r, hr, hb⟩ := hf
        exact hSm₂ f ⟨r, hr.trans_le hm₂, hb⟩
      drift_traceless := fun U hU => (hfacts U hU).1
      drift_zero := fun U hU => by
        have := ((hfacts U hU).2 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 0).2
        simpa using this
      local_cubes := fun U hU => (h₃ L hL k hk).1 U hU
      represents := fun U hU => h₄ L hL k hk U hU
      entry_holomorphic := fun y a' ι =>
        (h₆ _ ρ₁ _ hρ₁ (backgroundCoords_finite hL0 (edgesNear_finite hL0 _ _))).of_radius_le
          _ _ hρ hm₁ (((hEn.1 y a').1) ι)
      closure := fun T hT => h₆ _ _ T hρ hT
      covDiffEntry_holomorphic := fun a' a b' x => (hE₂ a' a b' x).2 _ hρ }
  refine ⟨min ρ₁ ρ₂, hρ, fun a b => ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩⟩
  · exact finite_latticePoints_near (meshAt_pos hL0) _ _
  · exact fun ζ hζ p hp => gaugeParam_basisForm_eq_zero S hζ a b hp
  · exact fun ζ hζ p => gaugeParam_basisForm_mem S hζ a b p
  · exact fun p _ e => gaugeParam_basisForm_holomorphic S a e b p
  · exact (finite_links_near (meshAt_pos hL0) _ _).preimage Subtype.val_injective.injOn
  · exact fun ζ hζ c hc => shiftedForm_basisForm_eq_zero S hζ a b hc
  · exact fun ζ hζ c => (shiftedForm_basisForm_mem S hζ a b).1 c.1 c.2
  · exact fun c hc e => shiftedForm_basisForm_holomorphic S a e b hc
  · exact fun ζ hζ => shiftedForm_basisForm_mem S hζ a b
end YangMills.Construction.Tower.FullSpace.BasisFormLocality
end
