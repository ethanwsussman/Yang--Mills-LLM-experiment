import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATowerProof
import YangMills.Construction.Towers.CriterionForLocalKernelsWithEntireEntries
import YangMills.Construction.Towers.EntireCoordinatesAreClosed
import YangMills.Construction.Towers.EntriesOfTheConfigurationOfAField
import YangMills.Construction.Towers.HalfPlaquetteTraceKernelOfAFieldIsLocal
import YangMills.Construction.Towers.KernelOfAMapWithFinitelyManyEvaluations
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.TranslatedConfigurationOfAField
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.HalfFaceTraceLocality
open PeriodicOperators
open EntireDependence
open BackgroundJets (gaugeFieldOfForm)
open TorusMetric (euclidNormVec)
section PauliCoefficients
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • Matrices.ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliCoeff_smul_sum (z : ℂ) (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (z • ∑ b, x b • Matrices.ComplexMatrix2.pauliFamily b) = z * x a := by
  have h : z • ∑ b, x b • Matrices.ComplexMatrix2.pauliFamily b =
      ∑ b, (z * x b) • Matrices.ComplexMatrix2.pauliFamily b := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => smul_smul _ _ _
  rw [h]
  exact pauliCoeff_sum_smul (fun b => z * x b) a
end PauliCoefficients
section MultiplicationKernel
variable {L k : ℕ}
abbrev traceMulMap (U : Edge L k 0 → Matrices.ComplexMatrix2) :
    (Fin 3 × Face L k 0 → ℂ) → Fin 3 × Face L k 0 → ℂ :=
  PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (Face L k 0))
    (vertexCoordinate (Face L k 0)) (halfFaceTraceMul U)
theorem traceMulMap_apply (U : Edge L k 0 → Matrices.ComplexMatrix2)
    (f : Fin 3 × Face L k 0 → ℂ) (ι : Fin 3 × Face L k 0) :
    traceMulMap U f ι = halfFaceTrace U ι.2 * f ι :=
  pauliCoeff_smul_sum _ (fun a => f (a, ι.2)) ι.1
theorem halfFaceTraceKernel_eq (hF : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (U : Edge L k 0 → Matrices.ComplexMatrix2) :
    halfFaceTraceKernel L k U =
      fun ι' ι => traceMulMap U (basisFunction ι : Fin 3 × Face L k 0 → ℂ) ι' :=
  (hF _ _ (traceMulMap U)
    (fun f g => funext fun ι => by
      simp only [traceMulMap_apply, Pi.add_apply, mul_add])
    (fun c f => funext fun ι => by
      simp only [traceMulMap_apply, Pi.smul_apply, smul_eq_mul]
      ring)
    (fun ι' => ⟨{ι'}, fun f g h => by
      rw [traceMulMap_apply, traceMulMap_apply, h ι' (Finset.mem_singleton_self _)]⟩)).2
theorem halfFaceTraceKernel_diag (hF : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (U : Edge L k 0 → Matrices.ComplexMatrix2) (ι : Fin 3 × Face L k 0) :
    halfFaceTraceKernel L k U ι ι = halfFaceTrace U ι.2 := by
  rw [halfFaceTraceKernel_eq hF]
  show traceMulMap U _ _ = _
  rw [traceMulMap_apply]
  simp [basisFunction]
theorem halfFaceTraceKernel_of_ne (hF : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (U : Edge L k 0 → Matrices.ComplexMatrix2) {ι' ι : Fin 3 × Face L k 0} (h : ι' ≠ ι) :
    halfFaceTraceKernel L k U ι' ι = 0 := by
  rw [halfFaceTraceKernel_eq hF]
  show traceMulMap U _ _ = _
  rw [traceMulMap_apply]
  simp [basisFunction, h]
end MultiplicationKernel
section LatticeNorms
variable {a : ℝ}
theorem euclidNormVec_zero : euclidNormVec 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
theorem euclidNormVec_axisStep (ha : 0 ≤ a) (μ : Fin 4) :
    euclidNormVec (InfiniteLattice.axisStep a μ : InfiniteLattice.AmbientSpace) = a := by
  have h : ∑ ν, ((InfiniteLattice.axisStep a μ : InfiniteLattice.AmbientSpace) ν) ^ 2 = a ^ 2 := by
    rw [Finset.sum_eq_single μ]
    · simp [InfiniteLattice.axisStep]
    · intro ν _ hν
      simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne hν]
    · simp
  rw [euclidNormVec, h, Real.sqrt_sq ha]
end LatticeNorms
section IntegerShifts
variable {a : ℝ} {N : ℕ}
theorem castVec_mem (h : a * N = 1) (m : Fin 4 → ℤ) :
    castVec m ∈ InfiniteLattice.latticeSubgroup a := by apply _root_.YangMills.Construction.PeriodicOperators.TowerIndexSets.castVec_mem_latticeSubgroup <;> assumption
def castVecPoint (h : a * N = 1) (m : Fin 4 → ℤ) : InfiniteLattice.LatticePoint a :=
  ⟨castVec m, castVec_mem h m⟩
theorem vertexImage_intShift (h : a * N = 1) (m : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a) :
    vertexImage (intShift m) x = x + castVecPoint h m :=
  Subtype.ext (Classical.epsilon_spec
    (p := fun x' : InfiniteLattice.LatticePoint a =>
      (x' : InfiniteLattice.AmbientSpace) = intShift m x)
    ⟨x + castVecPoint h m, rfl⟩ |>.trans rfl)
theorem edgeImage_intShift_ends (h : a * N = 1) (m : Fin 4 → ℤ) (b : InfiniteLattice.Link a) :
    (edgeImage (intShift m) b).initial = b.initial + castVecPoint h m ∧
      (edgeImage (intShift m) b).terminal = b.terminal + castVecPoint h m := by
  have spec := Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a =>
      b'.initial = vertexImage (intShift m) b.initial ∧
        b'.terminal = vertexImage (intShift m) b.terminal)
    ⟨⟨vertexImage (intShift m) b.initial, vertexImage (intShift m) b.terminal, by
      obtain ⟨μ, hμ⟩ := b.isAdjacent
      refine ⟨μ, ?_⟩
      rw [vertexImage_intShift h, vertexImage_intShift h, add_sub_add_right_eq_sub]
      exact hμ⟩, rfl, rfl⟩
  have spec' : (edgeImage (intShift m) b).initial = vertexImage (intShift m) b.initial ∧
      (edgeImage (intShift m) b).terminal = vertexImage (intShift m) b.terminal := spec
  rw [vertexImage_intShift h, vertexImage_intShift h] at spec'
  exact spec'
theorem eq_edgeImage_intShift (h : a * N = 1) (m : Fin 4 → ℤ) {b b' : InfiniteLattice.Link a}
    (ht : b'.initial = b.initial + castVecPoint h m)
    (hh : b'.terminal = b.terminal + castVecPoint h m) :
    b' = edgeImage (intShift m) b :=
  InfiniteLattice.Link.ext (ht.trans (edgeImage_intShift_ends h m b).1.symm)
    (hh.trans (edgeImage_intShift_ends h m b).2.symm)
end IntegerShifts
section FaceGeometry
variable {L k : ℕ}
theorem meshAt_mul_pow (hL : L ≠ 0) : meshAt L k 0 * ((L ^ k : ℕ) : ℝ) = 1 := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have e : ((0 : ℕ) : ℤ) - (k : ℤ) = -(k : ℤ) := by simp
  rw [meshAt, e, zpow_neg, zpow_natCast]
  push_cast
  exact inv_mul_cancel₀ (pow_ne_zero _ hL')
theorem finestMesh_pos (hL : L ≠ 0) : 0 < finestMesh L k := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  exact zpow_pos hL' _
def forwardEdge (x : Vertex L k 0) (μ : Fin 4) : PeriodicOperators.PosEdge L k 0 :=
  ⟨InfiniteLattice.Link.forwardFrom x μ, μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
def faceEdge (p : Face L k 0) : Fin 4 → PeriodicOperators.PosEdge L k 0 :=
  ![forwardEdge p.corner p.lowAxis,
    forwardEdge (p.corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis,
    forwardEdge (p.corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis,
    forwardEdge p.corner p.highAxis]
open Classical in
def faceIndices (p : Face L k 0) : Finset (remainderIndex L k).Carrier :=
  Finset.univ.biUnion fun i => edgeIndices L k (faceEdge p i)
theorem edgeIndices_subset_faceIndices (p : Face L k 0) (i : Fin 4) :
    edgeIndices L k (faceEdge p i) ⊆ faceIndices p := by
  classical
  exact Finset.subset_biUnion_of_mem (fun i => edgeIndices L k (faceEdge p i))
    (Finset.mem_univ i)
theorem faceVariable_eq (U : Edge L k 0 → Matrices.ComplexMatrix2)
    (hU : ∀ b, U b.opposite = (U b)⁻¹) (p : Face L k 0) :
    faceVariable U p = U (faceEdge p 0).1 * (U (faceEdge p 1).1 *
      ((U (faceEdge p 2).1)⁻¹ * (U (faceEdge p 3).1)⁻¹)) := by
  simp [faceVariable, linkHolonomy, faceBoundary, hU, faceEdge, forwardEdge]
theorem initial_dist_le (hL : L ≠ 0) (p : Face L k 0) (i : Fin 4) :
    euclidNormVec (((faceEdge p i).1.initial : InfiniteLattice.AmbientSpace) - p.corner) ≤
      2 * finestMesh L k := by
  have hη := finestMesh_pos (k := k) hL
  have h0 : euclidNormVec (0 : InfiniteLattice.AmbientSpace) ≤ 2 * finestMesh L k := by
    rw [euclidNormVec_zero]
    positivity
  have h1 : ∀ μ, euclidNormVec (InfiniteLattice.axisStep (meshAt L k 0) μ :
      InfiniteLattice.AmbientSpace) ≤ 2 * finestMesh L k := fun μ => by
    rw [euclidNormVec_axisStep (a := meshAt L k 0) hη.le]
    have : meshAt L k 0 = finestMesh L k := rfl
    linarith
  fin_cases i
  · show euclidNormVec ((p.corner : InfiniteLattice.AmbientSpace) - p.corner) ≤ _
    rwa [sub_self]
  · show euclidNormVec (((p.corner + InfiniteLattice.axisStep _ p.lowAxis : Vertex L k 0) :
      InfiniteLattice.AmbientSpace) - p.corner) ≤ _
    rw [AddSubgroup.coe_add, add_sub_cancel_left]
    exact h1 _
  · show euclidNormVec (((p.corner + InfiniteLattice.axisStep _ p.highAxis : Vertex L k 0) :
      InfiniteLattice.AmbientSpace) - p.corner) ≤ _
    rw [AddSubgroup.coe_add, add_sub_cancel_left]
    exact h1 _
  · show euclidNormVec ((p.corner : InfiniteLattice.AmbientSpace) - p.corner) ≤ _
    rwa [sub_self]
theorem pos_dist_le (hL : L ≠ 0) (p : Face L k 0)
    (κ : (remainderIndex L k).Carrier) (hκ : κ ∈ faceIndices p) :
    euclidNormVec ((remainderIndex L k).pos κ - (p.corner : InfiniteLattice.AmbientSpace)) ≤
      2 * finestMesh L k := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hκ
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hi
  exact initial_dist_le hL p i
theorem isEntireOn_halfFaceTrace (hE : GaugeFieldOfFormEntries)
    (hR : EntireDependenceClosed) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (p : Face L k 0) :
    IsEntireOn (remainderIndex L k) (faceIndices p)
      fun ζ => halfFaceTrace (gaugeFieldOfForm L k ζ) p := by
  have hent := hE L hL k
  obtain ⟨hc, -, hop, -⟩ := hR (remainderIndex L k) (faceIndices p)
  have hmul : ∀ A B : ((remainderIndex L k).Carrier → ℂ) → Matrices.ComplexMatrix2,
      (∀ i j, IsEntireOn (remainderIndex L k) (faceIndices p) fun ζ => A ζ i j) →
      (∀ i j, IsEntireOn (remainderIndex L k) (faceIndices p) fun ζ => B ζ i j) →
      ∀ i j, IsEntireOn (remainderIndex L k) (faceIndices p)
        fun ζ => (A ζ * B ζ) i j := by
    intro A B hA hB i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact (hop _ _ (hop _ _ (hA i 0) (hB 0 j)).2 (hop _ _ (hA i 1) (hB 1 j)).2).1
  have hU : ∀ (b : Fin 4) (i j : Fin 2), IsEntireOn (remainderIndex L k)
      (faceIndices p) fun ζ => gaugeFieldOfForm L k ζ (faceEdge p b).1 i j :=
    fun b i j => (hR _ _).2.2.2 _ _ (edgeIndices_subset_faceIndices p b) (hent.2 _ i j).1
  have hV : ∀ (b : Fin 4) (i j : Fin 2), IsEntireOn (remainderIndex L k)
      (faceIndices p) fun ζ => (gaugeFieldOfForm L k ζ (faceEdge p b).1)⁻¹ i j :=
    fun b i j => (hR _ _).2.2.2 _ _ (edgeIndices_subset_faceIndices p b) (hent.2 _ i j).2
  have hP := hmul _ _ (hU 0) (hmul _ _ (hU 1) (hmul _ _ (hV 2) (hV 3)))
  have e : (fun ζ => halfFaceTrace (gaugeFieldOfForm L k ζ) p) = fun ζ =>
      (1 / 2) * ((gaugeFieldOfForm L k ζ (faceEdge p 0).1 *
          (gaugeFieldOfForm L k ζ (faceEdge p 1).1 *
            ((gaugeFieldOfForm L k ζ (faceEdge p 2).1)⁻¹ *
              (gaugeFieldOfForm L k ζ (faceEdge p 3).1)⁻¹))) 0 0 +
        (gaugeFieldOfForm L k ζ (faceEdge p 0).1 *
          (gaugeFieldOfForm L k ζ (faceEdge p 1).1 *
            ((gaugeFieldOfForm L k ζ (faceEdge p 2).1)⁻¹ *
              (gaugeFieldOfForm L k ζ (faceEdge p 3).1)⁻¹))) 1 1) := by
    funext ζ
    have hcfg : IsFieldIn PeriodicLattice.complexGaugeGroup (gaugeFieldOfForm L k ζ) :=
      hent.1 ζ
    rw [halfFaceTrace, faceVariable_eq _ hcfg.2, Matrices.ComplexMatrix2.fullTrace,
      Matrix.trace_fin_two]
  rw [e]
  exact (hop _ _ (hc _) (hop _ _ (hP 0 0) (hP 1 1)).1).2
theorem shiftFace_injective (hL : L ≠ 0) (m : Fin 4 → ℤ) :
    Function.Injective (shiftFace m : Face L k 0 → Face L k 0) := by
  intro p q e
  have hb : vertexImage (intShift m) p.corner = vertexImage (intShift m) q.corner :=
    congrArg InfiniteLattice.ElementaryPlaquette.corner e
  rw [vertexImage_intShift (meshAt_mul_pow hL), vertexImage_intShift (meshAt_mul_pow hL)] at hb
  have h1 : (shiftFace m p).lowAxis = (shiftFace m q).lowAxis :=
    congrArg InfiniteLattice.ElementaryPlaquette.lowAxis e
  have h2 : (shiftFace m p).highAxis = (shiftFace m q).highAxis :=
    congrArg InfiniteLattice.ElementaryPlaquette.highAxis e
  exact InfiniteLattice.ElementaryPlaquette.ext (add_right_cancel hb) h1 h2
theorem halfFaceTrace_shiftFace (hL : L ≠ 0) (m : Fin 4 → ℤ)
    (U U' : Edge L k 0 → Matrices.ComplexMatrix2)
    (hT : ∀ b, U' (edgeImage (intShift m) b) = U b) (p : Face L k 0) :
    halfFaceTrace U' (shiftFace m p) = halfFaceTrace U p := by
  have h := meshAt_mul_pow (k := k) hL
  have key : ∀ {b b' : Edge L k 0}, b'.initial = b.initial + castVecPoint h m →
      b'.terminal = b.terminal + castVecPoint h m → U' b' = U b := fun ht hh => by
    rw [eq_edgeImage_intShift h m ht hh, hT]
  have hb : (shiftFace m p).corner = p.corner + castVecPoint h m :=
    vertexImage_intShift h m p.corner
  have e1 : U' (InfiniteLattice.Link.forwardFrom (shiftFace m p).corner p.lowAxis) =
      U (InfiniteLattice.Link.forwardFrom p.corner p.lowAxis) :=
    key hb (by
      show (shiftFace m p).corner + _ = p.corner + _ + _
      rw [hb]; abel)
  have e2 : U' (InfiniteLattice.Link.forwardFrom
        ((shiftFace m p).corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis) =
      U (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep _ p.lowAxis)
        p.highAxis) :=
    key (by
      show (shiftFace m p).corner + _ = p.corner + _ + _
      rw [hb]; abel) (by
      show (shiftFace m p).corner + _ + _ = p.corner + _ + _ + _
      rw [hb]; abel)
  have e3 : U' (InfiniteLattice.Link.forwardFrom
        ((shiftFace m p).corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis).opposite =
      U (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep _ p.highAxis)
        p.lowAxis).opposite :=
    key (by
      show (shiftFace m p).corner + _ + _ = p.corner + _ + _ + _
      rw [hb]; abel) (by
      show (shiftFace m p).corner + _ = p.corner + _ + _
      rw [hb]; abel)
  have e4 : U' (InfiniteLattice.Link.forwardFrom (shiftFace m p).corner p.highAxis).opposite =
      U (InfiniteLattice.Link.forwardFrom p.corner p.highAxis).opposite :=
    key (by
      show (shiftFace m p).corner + _ = p.corner + _ + _
      rw [hb]; abel) hb
  have hv : faceVariable U' (shiftFace m p) = faceVariable U p := by
    show ([_, _, _, _].map U').prod = ([_, _, _, _].map U).prod
    simp only [List.map_cons, List.map_nil]
    exact congrArg List.prod (by
      show [U' _, U' _, U' _, U' _] = [U _, U _, U _, U _]
      exact congrArg₂ List.cons e1 (congrArg₂ List.cons e2
        (congrArg₂ List.cons e3 (congrArg₂ List.cons e4 rfl))))
  rw [halfFaceTrace, halfFaceTrace, hv]
end FaceGeometry
theorem halfFaceTraceKernelIsLocal_holds (hC : EntireLocalCriterion.Criterion)
    (hE : GaugeFieldOfFormEntries)
    (hT : ShiftedFieldGauge.ShiftCommutes)
    (hF : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (hR : EntireDependenceClosed) : HalfFaceTraceKernelIsLocal := by
  intro L hL k _
  have hL0 : L ≠ 0 := by
    have := hL.2
    omega
  have hη := finestMesh_pos (k := k) hL0
  refine hC L hL k _ _ _ ?_ ?_ ?_ ?_
  · intro ι'
    exact ⟨(0, forwardEdge (InfiniteLattice.ElementaryPlaquette.corner (Prod.snd ι')) 0), rfl⟩
  · intro ζ ι' ι hd
    apply halfFaceTraceKernel_of_ne hF
    intro e
    apply hd
    rw [e, sub_self, euclidNormVec_zero]
    positivity
  · intro ι' ι
    by_cases e : ι' = ι
    · subst e
      refine ⟨faceIndices (Prod.snd ι'), fun κ hκ => pos_dist_le hL0 _ κ hκ, ?_⟩
      have h := isEntireOn_halfFaceTrace (k := k) hE hR hL (Prod.snd ι')
      have e' : (fun ζ => halfFaceTraceKernel L k (gaugeFieldOfForm L k ζ) ι' ι') =
          fun ζ => halfFaceTrace (gaugeFieldOfForm L k ζ) (Prod.snd ι') :=
        funext fun ζ => halfFaceTraceKernel_diag hF _ ι'
      rw [e']
      exact h
    · refine ⟨∅, by simp, ?_⟩
      have e' : (fun ζ => halfFaceTraceKernel L k (gaugeFieldOfForm L k ζ) ι' ι) =
          fun _ => (0 : ℂ) :=
        funext fun ζ => halfFaceTraceKernel_of_ne hF _ e
      rw [e']
      exact (hR _ ∅).1 0
  · intro ζ m ι' ι
    by_cases e : ι' = ι
    · subst e
      have h1 := halfFaceTraceKernel_diag hF
        (gaugeFieldOfForm L k (shiftField (remainderIndex L k) m ζ))
        ((colourFaces L k 0).translate m ι')
      have h2 := halfFaceTraceKernel_diag hF (gaugeFieldOfForm L k ζ) ι'
      refine h1.trans (Eq.trans ?_ h2.symm)
      exact halfFaceTrace_shiftFace hL0 m _ _ (hT L hL k m ζ) (Prod.snd ι')
    · have hne : (colourFaces L k 0).translate m ι' ≠ (colourFaces L k 0).translate m ι := by
        intro e'
        apply e
        have e1 : Prod.fst ((colourFaces L k 0).translate m ι') =
            Prod.fst ((colourFaces L k 0).translate m ι) := congrArg Prod.fst e'
        have e2 : Prod.snd ((colourFaces L k 0).translate m ι') =
            Prod.snd ((colourFaces L k 0).translate m ι) := congrArg Prod.snd e'
        exact Prod.ext e1 (shiftFace_injective hL0 m e2)
      rw [halfFaceTraceKernel_of_ne hF _ e]
      exact halfFaceTraceKernel_of_ne hF _ hne
end YangMills.Construction.Tower.FullSpace.HalfFaceTraceLocality
end
