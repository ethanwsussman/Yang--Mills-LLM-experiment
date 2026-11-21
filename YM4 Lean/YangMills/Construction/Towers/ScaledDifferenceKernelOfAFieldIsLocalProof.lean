import YangMills.Construction.Towers.GaugeConditionsOfTheAlgebraOfTheLeftChartOnASideProof
import YangMills.Construction.Towers.HessianCurvatureKernelOfAFieldIsLocalProof
import YangMills.Construction.Towers.KernelOfAMapWithFinitelyManyEvaluations
import YangMills.Construction.Towers.ScaledDifferenceKernelOfAFieldIsLocal
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RescaledDifferenceLocality
open YangMills.Construction
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.EntireDependence
open YangMills.Construction.Tower.FullSpace.BackgroundJets (gaugeFieldOfForm)
open YangMills.Construction.TorusMetric (euclidNormVec)
def coeffOfEntries (a : Fin 3) (X : ComplexMatrix2) : ℂ :=
  ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
theorem pauliCoeff_eq_coeffOfEntries (a : Fin 3) {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a X = coeffOfEntries a X := by
  classical
  simp only [pauliCoeff, dif_pos h]
  rfl
theorem coeffOfEntries_add (a : Fin 3) (X Y : ComplexMatrix2) :
    coeffOfEntries a (X + Y) = coeffOfEntries a X + coeffOfEntries a Y := by
  fin_cases a <;> simp [coeffOfEntries] <;> ring
theorem coeffOfEntries_smul (a : Fin 3) (c : ℂ) (X : ComplexMatrix2) :
    coeffOfEntries a (c • X) = c * coeffOfEntries a X := by
  fin_cases a <;> simp [coeffOfEntries] <;> ring
theorem coeffOfEntries_zero (a : Fin 3) : coeffOfEntries a 0 = 0 := by
  fin_cases a <;> simp [coeffOfEntries]
theorem coeffOfEntries_eq_linear (a : Fin 3) (X : ComplexMatrix2) :
    coeffOfEntries a X = (![1 / 2, -(1 / (2 * Complex.I)), 0] : Fin 3 → ℂ) a * X 0 1 +
      (![1 / 2, 1 / (2 * Complex.I), 0] : Fin 3 → ℂ) a * X 1 0 +
      (![0, 0, 1] : Fin 3 → ℂ) a * X 0 0 := by
  fin_cases a
  · change (X 0 1 + X 1 0) / 2 = 1 / 2 * X 0 1 + 1 / 2 * X 1 0 + 0 * X 0 0
    ring
  · change (X 1 0 - X 0 1) / (2 * Complex.I) = -(1 / (2 * Complex.I)) * X 0 1 +
      1 / (2 * Complex.I) * X 1 0 + 0 * X 0 0
    ring
  · change X 0 0 = 0 * X 0 1 + 0 * X 1 0 + 1 * X 0 0
    ring
theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
def scaledTwist (η : ℝ) (V X Y : ComplexMatrix2) : ComplexMatrix2 :=
  η⁻¹ • (ComplexMatrix2.conjugateBy V X - Y)
theorem trace_conjugateBy {V A : ComplexMatrix2} (hV : V.det = 1) :
    Matrix.trace (ComplexMatrix2.conjugateBy V A) = Matrix.trace A := by apply _root_.YangMills.Construction.Tower.LeftChartAlgebra.GaugeRequirements.trace_conj_eq <;> assumption
theorem scaledTwist_eq (η : ℝ) (V X Y : ComplexMatrix2) :
    scaledTwist η V X Y = ((η⁻¹ : ℝ) : ℂ) • (V * X * V⁻¹ + (-1 : ℂ) • Y) := by
  ext r s
  simp [scaledTwist, ComplexMatrix2.conjugateBy, sub_eq_add_neg]
  ring
theorem scaledTwist_mem_traceless (η : ℝ) {V X Y : ComplexMatrix2} (hV : V.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    scaledTwist η V X Y ∈ ComplexMatrix2.traceless := by
  have hA : ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.traceless := by
    change Matrix.trace _ = 0
    rw [trace_conjugateBy hV]
    exact hX
  rw [scaledTwist_eq]
  exact Submodule.smul_mem _ _
    (Submodule.add_mem _ hA (Submodule.smul_mem _ _ hY))
theorem scaledTwist_add (η : ℝ) (V X X' Y Y' : ComplexMatrix2) :
    scaledTwist η V (X + X') (Y + Y') = scaledTwist η V X Y + scaledTwist η V X' Y' := by
  simp only [scaledTwist_eq, mul_add, add_mul, smul_add]
  ext r s
  simp
  ring
theorem scaledTwist_smul (η : ℝ) (V X Y : ComplexMatrix2) (c : ℂ) :
    scaledTwist η V (c • X) (c • Y) = c • scaledTwist η V X Y := by
  simp only [scaledTwist_eq]
  ext r s
  simp
  ring
theorem scaledTwist_zero (η : ℝ) (V : ComplexMatrix2) : scaledTwist η V 0 0 = 0 := by
  simp [scaledTwist_eq]
variable {L k : ℕ}
theorem vertexImage_intShift_injective (hL : Conventions.IsAdmissibleBlockingFactor L)
    (n : Fin 4 → ℤ) :
    Function.Injective (vertexImage (intShift n) : Vertex L k 0 → Vertex L k 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.vertexImage_intShift_injective <;> assumption
theorem edgeImage_intShift_ends (hL : Conventions.IsAdmissibleBlockingFactor L)
    (n : Fin 4 → ℤ) (b : Edge L k 0) :
    (edgeImage (intShift n) b).initial = vertexImage (intShift n) b.initial ∧
      (edgeImage (intShift n) b).terminal = vertexImage (intShift n) b.terminal := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.edgeImage_intShift_spec <;> assumption
theorem shiftEdge_val (hL : Conventions.IsAdmissibleBlockingFactor L) (n : Fin 4 → ℤ)
    (b : PosEdge L k 0) :
    (shiftEdge n b).1 = edgeImage (intShift n) b.1 := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.shiftEdge_val <;> assumption
theorem initial_shiftEdge (hL : Conventions.IsAdmissibleBlockingFactor L) (n : Fin 4 → ℤ)
    (b : PosEdge L k 0) :
    (shiftEdge n b).1.initial = vertexImage (intShift n) b.1.initial := by
  rw [shiftEdge_val hL]
  exact (edgeImage_intShift_ends hL n b.1).1
theorem terminal_shiftEdge (hL : Conventions.IsAdmissibleBlockingFactor L) (n : Fin 4 → ℤ)
    (b : PosEdge L k 0) :
    (shiftEdge n b).1.terminal = vertexImage (intShift n) b.1.terminal := by
  rw [shiftEdge_val hL]
  exact (edgeImage_intShift_ends hL n b.1).2
theorem finestMesh_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.finestMesh_pos <;> assumption
theorem euclidNormVec_zero_le (hL : Conventions.IsAdmissibleBlockingFactor L) :
    euclidNormVec (0 : InfiniteLattice.AmbientSpace) ≤ 2 * finestMesh L k := by
  have h0 : euclidNormVec (0 : InfiniteLattice.AmbientSpace) = 0 := by simp [euclidNormVec]
  have := finestMesh_pos (k := k) hL
  rw [h0]
  linarith
theorem euclidNormVec_terminal_sub_initial_le (hL : Conventions.IsAdmissibleBlockingFactor L)
    (b : PosEdge L k 0) :
    euclidNormVec ((b.1.terminal : InfiniteLattice.AmbientSpace) -
        (b.1.initial : InfiniteLattice.AmbientSpace)) ≤ 2 * finestMesh L k := by
  have hη := finestMesh_pos (k := k) hL
  obtain ⟨μ, hμ⟩ := b.2
  have e : (b.1.terminal : InfiniteLattice.AmbientSpace) -
      (b.1.initial : InfiniteLattice.AmbientSpace) =
      ((InfiniteLattice.axisStep (meshAt L k 0) μ : Vertex L k 0) :
        InfiniteLattice.AmbientSpace) := by
    rw [← hμ]
    rfl
  have : euclidNormVec (((InfiniteLattice.axisStep (meshAt L k 0) μ : Vertex L k 0) :
      InfiniteLattice.AmbientSpace)) = finestMesh L k := by
    change euclidNormVec (Pi.single μ (finestMesh L k)) = _
    rw [InfiniteLattice.euclidNormVec_single, abs_of_pos hη]
  rw [e, this]
  linarith
def covDiffOnCoeffs (U : Edge L k 0 → ComplexMatrix2) :
    (Fin 3 × Vertex L k 0 → ℂ) → Fin 3 × PosEdge L k 0 → ℂ :=
  (vertexCoordinate (Vertex L k 0)).mapOnCoeffs (edgePauliCoordinates L k 0)
    fun l => (finestMesh L k)⁻¹ • covDiff U l
theorem covDiffOnCoeffs_eq {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (f : Fin 3 × Vertex L k 0 → ℂ) (a : Fin 3) (b : PosEdge L k 0) :
    covDiffOnCoeffs U f (a, b) =
      coeffOfEntries a (scaledTwist (finestMesh L k) (U b.1)
        (ofPauliCoeffs f b.1.terminal) (ofPauliCoeffs f b.1.initial)) := by
  classical
  have e : ((finestMesh L k)⁻¹ • covDiff U (ofPauliCoeffs f)) b.1 =
      scaledTwist (finestMesh L k) (U b.1)
        (ofPauliCoeffs f b.1.terminal) (ofPauliCoeffs f b.1.initial) := by
    simp only [Pi.smul_apply, covDiff, extendOddly, if_pos b.2, scaledTwist]
  change pauliCoeff a (((finestMesh L k)⁻¹ • covDiff U (ofPauliCoeffs f)) b.1) = _
  rw [e, pauliCoeff_eq_coeffOfEntries]
  exact scaledTwist_mem_traceless _ (hU.1 _) (ofPauliCoeffs_mem_traceless _ _)
    (ofPauliCoeffs_mem_traceless _ _)
theorem rescaledOperators_D_apply (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (a : Fin 3) (b : PosEdge L k 0) (ι : Fin 3 × Vertex L k 0) :
    (rescaledOperators L k U).D (a, b) ι =
      coeffOfEntries a (scaledTwist (finestMesh L k) (U b.1)
        (ofPauliCoeffs (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) b.1.terminal)
        (ofPauliCoeffs (basisFunction ι : Fin 3 × Vertex L k 0 → ℂ) b.1.initial)) := by
  classical
  have h := (hK (Fin 3 × Vertex L k 0) (Fin 3 × PosEdge L k 0)
    (covDiffOnCoeffs U) ?_ ?_ ?_).2
  · change kernelOfMap (covDiffOnCoeffs U) (a, b) ι = _
    rw [h]
    exact covDiffOnCoeffs_eq hU _ a b
  · intro f g
    funext ⟨a, b⟩
    have hadd : ∀ x, ofPauliCoeffs (f + g) x = ofPauliCoeffs f x + ofPauliCoeffs g x :=
      fun x => by
        simp [ofPauliCoeffs, add_smul, Finset.sum_add_distrib]
    rw [Pi.add_apply, covDiffOnCoeffs_eq hU, covDiffOnCoeffs_eq hU,
      covDiffOnCoeffs_eq hU, hadd, hadd, scaledTwist_add, coeffOfEntries_add]
  · intro c f
    funext ⟨a, b⟩
    have hsm : ∀ x, ofPauliCoeffs (c • f) x = c • ofPauliCoeffs f x := fun x => by
      simp [ofPauliCoeffs, mul_smul, Finset.smul_sum]
    rw [Pi.smul_apply, covDiffOnCoeffs_eq hU, covDiffOnCoeffs_eq hU, hsm, hsm,
      scaledTwist_smul, coeffOfEntries_smul, smul_eq_mul]
  · rintro ⟨a, b⟩
    refine ⟨Finset.univ.image (fun e : Fin 3 => (e, b.1.terminal)) ∪
      Finset.univ.image (fun e : Fin 3 => (e, b.1.initial)), fun f g h => ?_⟩
    rw [covDiffOnCoeffs_eq hU, covDiffOnCoeffs_eq hU]
    have hh : ofPauliCoeffs f b.1.terminal = ofPauliCoeffs g b.1.terminal := by
      simp only [ofPauliCoeffs]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [h (e, b.1.terminal)
        (Finset.mem_union_left _ (Finset.mem_image.2 ⟨e, Finset.mem_univ _, rfl⟩))]
    have ht : ofPauliCoeffs f b.1.initial = ofPauliCoeffs g b.1.initial := by
      simp only [ofPauliCoeffs]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [h (e, b.1.initial)
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨e, Finset.mem_univ _, rfl⟩))]
    rw [hh, ht]
theorem ofPauliCoeffs_basisFunction_of_ne {c : Fin 3} {x y : Vertex L k 0} (h : y ≠ x) :
    ofPauliCoeffs (basisFunction (c, x) : Fin 3 × Vertex L k 0 → ℂ) y = 0 := by
  classical
  change ∑ e, (basisFunction (c, x) : Fin 3 × Vertex L k 0 → ℂ) (e, y) •
    ComplexMatrix2.pauliFamily e = 0
  refine Finset.sum_eq_zero fun e _ => ?_
  have : (basisFunction (c, x) : Fin 3 × Vertex L k 0 → ℂ) (e, y) = 0 :=
    if_neg fun h' => h (congrArg Prod.snd h')
  rw [this, zero_smul]
theorem basisFunction_vertexImage (hL : Conventions.IsAdmissibleBlockingFactor L)
    (n : Fin 4 → ℤ) (c e : Fin 3) (x y : Vertex L k 0) :
    (basisFunction (c, vertexImage (intShift n) x) : Fin 3 × Vertex L k 0 → ℂ)
        (e, vertexImage (intShift n) y) =
      (basisFunction (c, x) : Fin 3 × Vertex L k 0 → ℂ) (e, y) := by
  have key : ((e, vertexImage (intShift n) y) = (c, vertexImage (intShift n) x)) ↔
      ((e, y) = (c, x)) := by
    simp only [Prod.mk.injEq, (vertexImage_intShift_injective hL n).eq_iff]
  by_cases h : (e, y) = (c, x)
  · exact (if_pos (key.2 h)).trans (if_pos h).symm
  · exact (if_neg (mt key.1 h)).trans (if_neg h).symm
theorem ofPauliCoeffs_basisFunction_vertexImage (hL : Conventions.IsAdmissibleBlockingFactor L)
    (n : Fin 4 → ℤ) (c : Fin 3) (x y : Vertex L k 0) :
    ofPauliCoeffs (basisFunction (c, vertexImage (intShift n) x) : Fin 3 × Vertex L k 0 → ℂ)
        (vertexImage (intShift n) y) =
      ofPauliCoeffs (basisFunction (c, x) : Fin 3 × Vertex L k 0 → ℂ) y := by
  simp only [ofPauliCoeffs]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [basisFunction_vertexImage hL]
section Entire
variable {F : PeriodicData} {S : Finset F.Carrier}
def EntriesEntireOn (F : PeriodicData) (S : Finset F.Carrier)
    (A : (F.Carrier → ℂ) → ComplexMatrix2) : Prop :=
  ∀ r s, IsEntireOn F S fun ζ => A ζ r s
theorem entriesEntireOn_const (hC : EntireDependenceClosed) (X : ComplexMatrix2) :
    EntriesEntireOn F S fun _ => X := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.entrywiseEntire_const <;> assumption
theorem entriesEntireOn_add (hC : EntireDependenceClosed)
    {A B : (F.Carrier → ℂ) → ComplexMatrix2}
    (hA : EntriesEntireOn F S A) (hB : EntriesEntireOn F S B) :
    EntriesEntireOn F S fun ζ => A ζ + B ζ := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.entrywiseEntire_add <;> assumption
theorem entriesEntireOn_mul (hC : EntireDependenceClosed)
    {A B : (F.Carrier → ℂ) → ComplexMatrix2}
    (hA : EntriesEntireOn F S A) (hB : EntriesEntireOn F S B) :
    EntriesEntireOn F S fun ζ => A ζ * B ζ := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.entrywiseEntire_mul <;> assumption
theorem entriesEntireOn_smul (hC : EntireDependenceClosed) (c : ℂ)
    {A : (F.Carrier → ℂ) → ComplexMatrix2}
    (hA : EntriesEntireOn F S A) : EntriesEntireOn F S fun ζ => c • A ζ := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.entrywiseEntire_smul <;> assumption
theorem isEntireOn_coeffOfEntries (hC : EntireDependenceClosed)
    {A : (F.Carrier → ℂ) → ComplexMatrix2}
    (hA : EntriesEntireOn F S A) (a : Fin 3) :
    IsEntireOn F S fun ζ => coeffOfEntries a (A ζ) := by
  have hc := (hC F S).1
  have hop := (hC F S).2.2.1
  simp only [coeffOfEntries_eq_linear a]
  exact (hop _ _ ((hop _ _ ((hop _ _ (hc _) (hA 0 1)).2) ((hop _ _ (hc _) (hA 1 0)).2)).1)
    ((hop _ _ (hc _) (hA 0 0)).2)).1
theorem isEntireOn_scaledTwist (hC : EntireDependenceClosed) (η : ℝ)
    {V : (F.Carrier → ℂ) → ComplexMatrix2} (hR : EntriesEntireOn F S V)
    (hI : EntriesEntireOn F S fun ζ => (V ζ)⁻¹) (X Y : ComplexMatrix2) (a : Fin 3) :
    IsEntireOn F S fun ζ => coeffOfEntries a (scaledTwist η (V ζ) X Y) := by
  simp only [scaledTwist_eq]
  exact isEntireOn_coeffOfEntries hC (entriesEntireOn_smul hC _ (entriesEntireOn_add hC
    (entriesEntireOn_mul hC (entriesEntireOn_mul hC hR (entriesEntireOn_const hC _)) hI)
    (entriesEntireOn_const hC _))) a
end Entire
theorem rescaledDifferenceKernelIsLocal_of (hCrit : EntireLocalCriterion.Criterion)
    (hEnt : GaugeFieldOfFormEntries)
    (hTr : ShiftedFieldGauge.ShiftCommutes)
    (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (hC : EntireDependenceClosed) : RescaledDifferenceKernelIsLocal := by
  classical
  intro L hL k _
  have hcfg := (hEnt L hL k).1
  refine hCrit L hL k (colourVertices L k 0) (colourEdges L k 0) _ ?_ ?_ ?_ ?_
  · intro ι'
    exact ⟨ι', rfl⟩
  · rintro ζ ⟨a, b⟩ ⟨c, x⟩ hfar
    change (rescaledOperators L k (gaugeFieldOfForm L k ζ)).D (a, b) (c, x) = 0
    have ht : b.1.initial ≠ x := by
      rintro rfl
      apply hfar
      change euclidNormVec (((b.1.initial : Vertex L k 0) : InfiniteLattice.AmbientSpace) -
        (b.1.initial : InfiniteLattice.AmbientSpace)) ≤ _
      rw [sub_self]
      exact euclidNormVec_zero_le hL
    have hh : b.1.terminal ≠ x := by
      rintro rfl
      exact hfar (euclidNormVec_terminal_sub_initial_le hL b)
    rw [rescaledOperators_D_apply hK (hcfg ζ), ofPauliCoeffs_basisFunction_of_ne hh,
      ofPauliCoeffs_basisFunction_of_ne ht, scaledTwist_zero, coeffOfEntries_zero]
  · rintro ⟨a, b⟩ ⟨c, x⟩
    refine ⟨edgeIndices L k b, ?_, ?_⟩
    · intro κ hκ
      obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hκ
      change euclidNormVec (((b.1.initial : Vertex L k 0) : InfiniteLattice.AmbientSpace) -
        (b.1.initial : InfiniteLattice.AmbientSpace)) ≤ _
      rw [sub_self]
      exact euclidNormVec_zero_le hL
    · have := isEntireOn_scaledTwist (F := remainderIndex L k) hC (finestMesh L k)
        (V := fun ζ => gaugeFieldOfForm L k ζ b.1)
        (fun r s => ((hEnt L hL k).2 b r s).1) (fun r s => ((hEnt L hL k).2 b r s).2)
        (ofPauliCoeffs (basisFunction (c, x) : Fin 3 × Vertex L k 0 → ℂ) b.1.terminal)
        (ofPauliCoeffs (basisFunction (c, x) : Fin 3 × Vertex L k 0 → ℂ) b.1.initial) a
      have e : (fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).D (a, b) (c, x)) =
          fun ζ => coeffOfEntries a (scaledTwist (finestMesh L k)
            (gaugeFieldOfForm L k ζ b.1)
            (ofPauliCoeffs (basisFunction (c, x) : Fin 3 × Vertex L k 0 → ℂ) b.1.terminal)
            (ofPauliCoeffs (basisFunction (c, x) : Fin 3 × Vertex L k 0 → ℂ) b.1.initial)) :=
        funext fun ζ => rescaledOperators_D_apply hK (hcfg ζ) a b (c, x)
      change IsEntireOn _ _ fun ζ =>
        (rescaledOperators L k (gaugeFieldOfForm L k ζ)).D (a, b) (c, x)
      rw [e]
      exact this
  · rintro ζ n ⟨a, b⟩ ⟨c, x⟩
    change (rescaledOperators L k (gaugeFieldOfForm L k
        (shiftField (remainderIndex L k) n ζ))).D (a, shiftEdge n b)
        (c, vertexImage (intShift n) x) =
      (rescaledOperators L k (gaugeFieldOfForm L k ζ)).D (a, b) (c, x)
    rw [rescaledOperators_D_apply hK (hcfg _), rescaledOperators_D_apply hK (hcfg _),
      initial_shiftEdge hL, terminal_shiftEdge hL, ofPauliCoeffs_basisFunction_vertexImage hL,
      ofPauliCoeffs_basisFunction_vertexImage hL, shiftEdge_val hL, hTr L hL k n ζ]
end YangMills.Construction.Tower.FullSpace.RescaledDifferenceLocality
end
