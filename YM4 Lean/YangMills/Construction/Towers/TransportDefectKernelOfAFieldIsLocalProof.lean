import YangMills.Construction.Towers.HessianCurvatureKernelOfAFieldIsLocalProof
import YangMills.Construction.Towers.SymbolsOfTheAveragesOnPlaneWavesProof
import YangMills.Construction.Towers.ScaledDifferenceKernelOfAFieldIsLocalProof
import YangMills.Construction.Towers.TransportDefectKernelOfAFieldIsLocal
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.HolonomyDefectLocality
open Matrices
open PeriodicOperators
open EntireDependence
open BackgroundJets (gaugeFieldOfForm)
open TorusMetric (euclidNormVec)
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
def chainTransports (W : Fin 4 → ComplexMatrix2) : Fin 4 → ComplexMatrix2 :=
  ![1, W 0, W 0 * W 1 * (W 2)⁻¹, W 0 * W 1 * (W 2)⁻¹ * (W 3)⁻¹]
def chainTransportsInv (W : Fin 4 → ComplexMatrix2) : Fin 4 → ComplexMatrix2 :=
  ![1, (W 0)⁻¹, W 2 * (W 1)⁻¹ * (W 0)⁻¹, W 3 * W 2 * (W 1)⁻¹ * (W 0)⁻¹]
theorem inv_chainTransports {W : Fin 4 → ComplexMatrix2} (hW : ∀ i, (W i).det = 1) (i : Fin 4) :
    (chainTransports W i)⁻¹ = chainTransportsInv W i := by
  have hu : ∀ i, (W i)⁻¹⁻¹ = W i := fun i =>
    Matrix.nonsing_inv_nonsing_inv _ (by rw [hW i]; exact isUnit_one)
  fin_cases i
  · simp [chainTransports, chainTransportsInv]
  · simp [chainTransports, chainTransportsInv]
  · simp [chainTransports, chainTransportsInv, Matrix.mul_inv_rev, hu, mul_assoc]
  · simp [chainTransports, chainTransportsInv, Matrix.mul_inv_rev, hu, mul_assoc]
theorem det_chainTransports {W : Fin 4 → ComplexMatrix2} (hW : ∀ i, (W i).det = 1) (i : Fin 4) :
    (chainTransports W i).det = 1 := by
  have hi : ∀ i, ((W i)⁻¹).det = 1 := fun i => by
    rw [Matrix.det_nonsing_inv, hW i]; simp
  fin_cases i <;> simp [chainTransports, Matrix.det_mul, hW, hi]
def defectValue (η : ℝ) (T X : Fin 4 → ComplexMatrix2) : ComplexMatrix2 :=
  η⁻¹ • ∑ i, transportSign i • (ComplexMatrix2.conjugateBy (T i) (X i) - X i)
theorem trace_conjugateBy {V A : ComplexMatrix2} (hV : V.det = 1) :
    Matrix.trace (ComplexMatrix2.conjugateBy V A) = Matrix.trace A := by apply _root_.YangMills.Construction.Tower.FullSpace.RescaledDifferenceLocality.trace_conjugateBy <;> assumption
theorem defectValue_mem_traceless (η : ℝ) {T : Fin 4 → ComplexMatrix2} (X : Fin 4 → ComplexMatrix2)
    (hT : ∀ i, (T i).det = 1) :
    defectValue η T X ∈ ComplexMatrix2.traceless := by
  have hterm : ∀ i, ComplexMatrix2.conjugateBy (T i) (X i) - X i ∈ ComplexMatrix2.traceless :=
    fun i => by
      change Matrix.trace _ = 0
      rw [Matrix.trace_sub, trace_conjugateBy (hT i), sub_self]
  have hsum : ∑ i, transportSign i • (ComplexMatrix2.conjugateBy (T i) (X i) - X i) ∈
      ComplexMatrix2.traceless :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hterm i)
  have : defectValue η T X = (((η⁻¹ : ℝ) : ℂ)) •
      ∑ i, transportSign i • (ComplexMatrix2.conjugateBy (T i) (X i) - X i) := by
    ext r s
    simp [defectValue]
  rw [this]
  exact Submodule.smul_mem _ _ hsum
theorem conjugateBy_add (V A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (A + B) =
      ComplexMatrix2.conjugateBy V A + ComplexMatrix2.conjugateBy V B := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (V A : ComplexMatrix2) (c : ℂ) :
    ComplexMatrix2.conjugateBy V (c • A) = c • ComplexMatrix2.conjugateBy V A := by
  simp [ComplexMatrix2.conjugateBy]
theorem conjugateBy_zero (V : ComplexMatrix2) : ComplexMatrix2.conjugateBy V 0 = 0 := by
  simp [ComplexMatrix2.conjugateBy]
theorem defectValue_add (η : ℝ) (T X Y : Fin 4 → ComplexMatrix2) :
    defectValue η T (X + Y) = defectValue η T X + defectValue η T Y := by
  simp only [defectValue, Pi.add_apply, conjugateBy_add, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  abel
theorem defectValue_smul (η : ℝ) (T X : Fin 4 → ComplexMatrix2) (c : ℂ) :
    defectValue η T (c • X) = c • defectValue η T X := by
  simp only [defectValue, Pi.smul_apply, conjugateBy_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_sub, smul_comm (transportSign i) c, smul_comm η⁻¹ c]
theorem defectValue_zero (η : ℝ) (T : Fin 4 → ComplexMatrix2) : defectValue η T 0 = 0 := by
  simp [defectValue, conjugateBy_zero]
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
variable {L k : ℕ}
theorem shiftEdge_val (hL : Conventions.IsAdmissibleBlockingFactor L) (m : Fin 4 → ℤ)
    (b : PosEdge L k 0) :
    (shiftEdge m b).1 = edgeImage (intShift m) b.1 := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.shiftEdge_val <;> assumption
theorem shiftEdge_injective (hL : Conventions.IsAdmissibleBlockingFactor L) (m : Fin 4 → ℤ) :
    Function.Injective (shiftEdge m : PosEdge L k 0 → PosEdge L k 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.shiftEdge_injective <;> assumption
def edgeStart (p : Face L k 0) : Fin 4 → Vertex L k 0 :=
  ![p.corner, p.corner + InfiniteLattice.axisStep _ p.lowAxis,
    p.corner + InfiniteLattice.axisStep _ p.highAxis, p.corner]
def edgeAxis (p : Face L k 0) : Fin 4 → Fin 4 :=
  ![p.lowAxis, p.highAxis, p.lowAxis, p.highAxis]
theorem faceEdge_eq_forwardFrom (p : Face L k 0) (i : Fin 4) :
    faceEdge p i = InfiniteLattice.Link.forwardFrom (edgeStart p i) (edgeAxis p i) := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.faceEdge_eq_forwardFrom <;> assumption
def facePosEdge (p : Face L k 0) (i : Fin 4) : PosEdge L k 0 :=
  ⟨faceEdge p i, edgeAxis p i, by
    rw [faceEdge_eq_forwardFrom]
    simp [InfiniteLattice.Link.forwardFrom]⟩
theorem initial_facePosEdge (p : Face L k 0) (i : Fin 4) :
    (facePosEdge p i).1.initial = edgeStart p i := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.initial_posEdgeOfFace <;> assumption
theorem faceEdge_shiftFace (hL : Conventions.IsAdmissibleBlockingFactor L) (m : Fin 4 → ℤ)
    (p : Face L k 0) (i : Fin 4) :
    faceEdge (shiftFace m p) i = edgeImage (intShift m) (faceEdge p i) := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.faceEdge_shiftFace <;> assumption
theorem facePosEdge_shiftFace (hL : Conventions.IsAdmissibleBlockingFactor L) (m : Fin 4 → ℤ)
    (p : Face L k 0) (i : Fin 4) :
    facePosEdge (shiftFace m p) i = shiftEdge m (facePosEdge p i) :=
  Subtype.ext ((faceEdge_shiftFace hL m p i).trans (shiftEdge_val hL m (facePosEdge p i)).symm)
theorem euclidNormVec_edgeStart_sub_corner_le (hL : Conventions.IsAdmissibleBlockingFactor L)
    (p : Face L k 0) (i : Fin 4) :
    euclidNormVec ((edgeStart p i : InfiniteLattice.AmbientSpace) -
      (p.corner : InfiniteLattice.AmbientSpace)) ≤ 2 * finestMesh L k := by
  have hη : 0 < finestMesh L k := by
    have hL0 : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    exact zpow_pos hL0 _
  have h0 : euclidNormVec (0 : InfiniteLattice.AmbientSpace) = 0 := by simp [euclidNormVec]
  have hs : ∀ μ, euclidNormVec (((InfiniteLattice.axisStep (meshAt L k 0) μ : Vertex L k 0) :
      InfiniteLattice.AmbientSpace)) ≤ 2 * finestMesh L k := fun μ => by
    have : euclidNormVec (((InfiniteLattice.axisStep (meshAt L k 0) μ : Vertex L k 0) :
        InfiniteLattice.AmbientSpace)) = finestMesh L k := by
      change euclidNormVec (Pi.single μ (finestMesh L k)) = _
      rw [InfiniteLattice.euclidNormVec_single, abs_of_pos hη]
    linarith
  fin_cases i
  · simpa [edgeStart, h0] using hη.le
  · simpa [edgeStart] using hs _
  · simpa [edgeStart] using hs _
  · simpa [edgeStart, h0] using hη.le
theorem ofCoeffs_posEdge (f : Fin 3 × PosEdge L k 0 → ℂ) (b : PosEdge L k 0) :
    (edgePauliCoordinates L k 0).ofCoeffs f b.1 = ofPauliCoeffs f b := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.extendOddly_ofCoeffs_pos <;> assumption
def formOnFace (f : Fin 3 × PosEdge L k 0 → ℂ) (p : Face L k 0) : Fin 4 → ComplexMatrix2 :=
  fun i => ofPauliCoeffs f (facePosEdge p i)
theorem formOnFace_add (f g : Fin 3 × PosEdge L k 0 → ℂ) (p : Face L k 0) :
    formOnFace (f + g) p = formOnFace f p + formOnFace g p := by
  funext i
  simp [formOnFace, ofPauliCoeffs, add_smul, Finset.sum_add_distrib]
theorem formOnFace_smul (c : ℂ) (f : Fin 3 × PosEdge L k 0 → ℂ) (p : Face L k 0) :
    formOnFace (c • f) p = c • formOnFace f p := by
  funext i
  simp [formOnFace, ofPauliCoeffs, mul_smul, Finset.smul_sum]
def fieldOnFace (U : Edge L k 0 → ComplexMatrix2) (p : Face L k 0) : Fin 4 → ComplexMatrix2 :=
  fun i => U (faceEdge p i)
theorem faceTransports_eq_chainTransports {U : Edge L k 0 → ComplexMatrix2}
    (hU : ∀ b : Edge L k 0, U b.opposite = (U b)⁻¹) (p : Face L k 0) :
    faceTransports U p = chainTransports (fieldOnFace U p) := by
  funext i
  fin_cases i <;>
    simp [chainTransports, fieldOnFace, faceTransports, faceVariable, linkHolonomy, faceBoundary,
      faceEdge, faceEdges, hU, mul_assoc]
theorem holonomyDefect_eq_defectValue {U : Edge L k 0 → ComplexMatrix2}
    (hU : ∀ b : Edge L k 0, U b.opposite = (U b)⁻¹)
    (f : Fin 3 × PosEdge L k 0 → ℂ) (p : Face L k 0) :
    holonomyDefect U ((edgePauliCoordinates L k 0).ofCoeffs f) p =
      defectValue (finestMesh L k) (chainTransports (fieldOnFace U p)) (formOnFace f p) := by
  have h : ∀ i, (edgePauliCoordinates L k 0).ofCoeffs f (faceEdge p i) = formOnFace f p i :=
    fun i => ofCoeffs_posEdge f (facePosEdge p i)
  simp only [holonomyDefect, defectValue, faceTransports_eq_chainTransports hU, h]
def defectOnCoeffs (U : Edge L k 0 → ComplexMatrix2) :
    (Fin 3 × PosEdge L k 0 → ℂ) → Fin 3 × Face L k 0 → ℂ :=
  (edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (Face L k 0)) (holonomyDefect U)
theorem defectOnCoeffs_apply {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (f : Fin 3 × PosEdge L k 0 → ℂ) (a : Fin 3) (p : Face L k 0) :
    defectOnCoeffs U f (a, p) =
      coeffOfEntries a
        (defectValue (finestMesh L k) (chainTransports (fieldOnFace U p)) (formOnFace f p)) := by
  change pauliCoeff a (holonomyDefect U ((edgePauliCoordinates L k 0).ofCoeffs f) p) = _
  rw [holonomyDefect_eq_defectValue hU.2, pauliCoeff_eq_coeffOfEntries]
  exact defectValue_mem_traceless _ _ (det_chainTransports fun i => hU.1 _)
theorem holonomyDefectKernel_apply (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (a : Fin 3) (p : Face L k 0) (ι : Fin 3 × PosEdge L k 0) :
    holonomyDefectKernel L k U (a, p) ι =
      coeffOfEntries a (defectValue (finestMesh L k) (chainTransports (fieldOnFace U p))
        (formOnFace (basisFunction ι : Fin 3 × PosEdge L k 0 → ℂ) p)) := by
  classical
  have h := (hK (Fin 3 × PosEdge L k 0) (Fin 3 × Face L k 0) (defectOnCoeffs U) ?_ ?_ ?_).2
  · change kernelOfMap (defectOnCoeffs U) (a, p) ι = _
    rw [h]
    exact defectOnCoeffs_apply hU _ a p
  · intro f g
    funext ⟨a, p⟩
    rw [Pi.add_apply, defectOnCoeffs_apply hU, defectOnCoeffs_apply hU, defectOnCoeffs_apply hU,
      formOnFace_add, defectValue_add, coeffOfEntries_add]
  · intro c f
    funext ⟨a, p⟩
    rw [Pi.smul_apply, defectOnCoeffs_apply hU, defectOnCoeffs_apply hU, formOnFace_smul,
      defectValue_smul, coeffOfEntries_smul, smul_eq_mul]
  · rintro ⟨a, p⟩
    refine ⟨Finset.univ.image fun q : Fin 3 × Fin 4 => (q.1, facePosEdge p q.2), fun f g h => ?_⟩
    rw [defectOnCoeffs_apply hU, defectOnCoeffs_apply hU]
    have : formOnFace f p = formOnFace g p := by
      funext i
      simp only [formOnFace, ofPauliCoeffs]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [h (e, facePosEdge p i) (Finset.mem_image.2 ⟨(e, i), Finset.mem_univ _, rfl⟩)]
    rw [this]
def EntriesEntireOn (F : PeriodicData) (S : Finset F.Carrier)
    (A : (F.Carrier → ℂ) → ComplexMatrix2) : Prop :=
  ∀ r s, IsEntireOn F S fun ζ => A ζ r s
section EntireEntries
variable {F : PeriodicData} {S : Finset F.Carrier}
theorem entriesEntireOn_const (hC : EntireDependenceClosed) (X : ComplexMatrix2) :
    EntriesEntireOn F S fun _ => X := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.entrywiseEntire_const <;> assumption
theorem entriesEntireOn_add (hC : EntireDependenceClosed) {A B : (F.Carrier → ℂ) → ComplexMatrix2}
    (hA : EntriesEntireOn F S A) (hB : EntriesEntireOn F S B) :
    EntriesEntireOn F S fun ζ => A ζ + B ζ := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.entrywiseEntire_add <;> assumption
theorem entriesEntireOn_mul (hC : EntireDependenceClosed) {A B : (F.Carrier → ℂ) → ComplexMatrix2}
    (hA : EntriesEntireOn F S A) (hB : EntriesEntireOn F S B) :
    EntriesEntireOn F S fun ζ => A ζ * B ζ := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.entrywiseEntire_mul <;> assumption
theorem entriesEntireOn_smul (hC : EntireDependenceClosed) (c : ℂ)
    {A : (F.Carrier → ℂ) → ComplexMatrix2} (hA : EntriesEntireOn F S A) :
    EntriesEntireOn F S fun ζ => c • A ζ := by apply _root_.YangMills.Construction.Tower.FullSpace.CurvatureKernelLocality.entrywiseEntire_smul <;> assumption
theorem isEntireOn_coeffOfEntries (hC : EntireDependenceClosed)
    {A : (F.Carrier → ℂ) → ComplexMatrix2} (hA : EntriesEntireOn F S A) (a : Fin 3) :
    IsEntireOn F S fun ζ => coeffOfEntries a (A ζ) := by
  have hc := (hC F S).1
  have hop := (hC F S).2.2.1
  simp only [coeffOfEntries_eq_linear a]
  exact (hop _ _ ((hop _ _ ((hop _ _ (hc _) (hA 0 1)).2) ((hop _ _ (hc _) (hA 1 0)).2)).1)
    ((hop _ _ (hc _) (hA 0 0)).2)).1
theorem isEntireOn_defectValue (hC : EntireDependenceClosed) (η : ℝ)
    {W : (F.Carrier → ℂ) → Fin 4 → ComplexMatrix2} (hdet : ∀ ζ i, (W ζ i).det = 1)
    (hR : ∀ i, EntriesEntireOn F S fun ζ => W ζ i)
    (hI : ∀ i, EntriesEntireOn F S fun ζ => (W ζ i)⁻¹)
    (X : Fin 4 → ComplexMatrix2) (a : Fin 3) :
    IsEntireOn F S fun ζ => coeffOfEntries a (defectValue η (chainTransports (W ζ)) X) := by
  have hT : ∀ i, EntriesEntireOn F S fun ζ => chainTransports (W ζ) i := by
    intro i
    fin_cases i
    · exact entriesEntireOn_const hC 1
    · exact hR 0
    · exact entriesEntireOn_mul hC (entriesEntireOn_mul hC (hR 0) (hR 1)) (hI 2)
    · exact entriesEntireOn_mul hC
        (entriesEntireOn_mul hC (entriesEntireOn_mul hC (hR 0) (hR 1)) (hI 2)) (hI 3)
  have hTi : ∀ i, EntriesEntireOn F S fun ζ => (chainTransports (W ζ) i)⁻¹ := by
    intro i
    simp only [inv_chainTransports (hdet _)]
    fin_cases i
    · exact entriesEntireOn_const hC 1
    · exact hI 0
    · exact entriesEntireOn_mul hC (entriesEntireOn_mul hC (hR 2) (hI 1)) (hI 0)
    · exact entriesEntireOn_mul hC
        (entriesEntireOn_mul hC (entriesEntireOn_mul hC (hR 3) (hR 2)) (hI 1)) (hI 0)
  have hterm : ∀ i, EntriesEntireOn F S fun ζ => transportSign i •
      (ComplexMatrix2.conjugateBy (chainTransports (W ζ) i) (X i) - X i) := fun i => by
    simp only [ComplexMatrix2.conjugateBy, sub_eq_add_neg]
    exact entriesEntireOn_smul hC _ (entriesEntireOn_add hC
      (entriesEntireOn_mul hC (entriesEntireOn_mul hC (hT i) (entriesEntireOn_const hC _)) (hTi i))
      (entriesEntireOn_const hC _))
  have hD : EntriesEntireOn F S fun ζ => defectValue η (chainTransports (W ζ)) X := by
    have e : ∀ ζ, defectValue η (chainTransports (W ζ)) X = ((η⁻¹ : ℝ) : ℂ) •
        (transportSign 0 • (ComplexMatrix2.conjugateBy (chainTransports (W ζ) 0) (X 0) - X 0) +
          transportSign 1 • (ComplexMatrix2.conjugateBy (chainTransports (W ζ) 1) (X 1) - X 1) +
          transportSign 2 • (ComplexMatrix2.conjugateBy (chainTransports (W ζ) 2) (X 2) - X 2) +
          transportSign 3 • (ComplexMatrix2.conjugateBy (chainTransports (W ζ) 3) (X 3) - X 3)) :=
      fun ζ => by
        rw [defectValue, Fin.sum_univ_four]
        ext r s
        simp
        ring
    simp only [e]
    exact entriesEntireOn_smul hC _ (entriesEntireOn_add hC (entriesEntireOn_add hC
      (entriesEntireOn_add hC (hterm 0) (hterm 1)) (hterm 2)) (hterm 3))
  exact isEntireOn_coeffOfEntries hC hD a
end EntireEntries
theorem basisFunction_shiftEdge (hL : Conventions.IsAdmissibleBlockingFactor L) (m : Fin 4 → ℤ)
    (c e : Fin 3) (b x : PosEdge L k 0) :
    (basisFunction (c, shiftEdge m b) : Fin 3 × PosEdge L k 0 → ℂ) (e, shiftEdge m x) =
      (basisFunction (c, b) : Fin 3 × PosEdge L k 0 → ℂ) (e, x) := by
  have key : ((e, shiftEdge m x) = (c, shiftEdge m b)) ↔ ((e, x) = (c, b)) := by
    simp only [Prod.mk.injEq, (shiftEdge_injective hL m).eq_iff]
  by_cases h : (e, x) = (c, b)
  · exact (if_pos (key.2 h)).trans (if_pos h).symm
  · exact (if_neg (mt key.1 h)).trans (if_neg h).symm
theorem kernelIsLocal (hCrit : EntireLocalCriterion.Criterion)
    (hEnt : GaugeFieldOfFormEntries)
    (hTr : ShiftedFieldGauge.ShiftCommutes)
    (hK : FiniteSupportKernel.KernelOfFiniteSupportMap)
    (hC : EntireDependenceClosed) : KernelIsLocal := by
  classical
  intro L hL k _
  have hcfg := (hEnt L hL k).1
  refine hCrit L hL k (colourEdges L k 0) (colourFaces L k 0) _ ?_ ?_ ?_ ?_
  · rintro ⟨a, p⟩
    exact ⟨(0, facePosEdge p 0),
      congrArg (fun x : Vertex L k 0 => (x : InfiniteLattice.AmbientSpace)) (initial_facePosEdge p 0)⟩
  · rintro ζ ⟨a, p⟩ ⟨c, b⟩ hfar
    change holonomyDefectKernel L k (gaugeFieldOfForm L k ζ) (a, p) (c, b) = 0
    have hne : ∀ i, facePosEdge p i ≠ b := by
      rintro i rfl
      apply hfar
      have := euclidNormVec_edgeStart_sub_corner_le hL p i
      rw [← initial_facePosEdge] at this
      exact this
    have hX : formOnFace (basisFunction (c, b) : Fin 3 × PosEdge L k 0 → ℂ) p = 0 := by
      funext i
      change ∑ e, (basisFunction (c, b) : Fin 3 × PosEdge L k 0 → ℂ)
        (e, facePosEdge p i) • ComplexMatrix2.pauliFamily e = 0
      refine Finset.sum_eq_zero fun e _ => ?_
      have : (basisFunction (c, b) : Fin 3 × PosEdge L k 0 → ℂ) (e, facePosEdge p i) = 0 :=
        if_neg fun h => hne i (congrArg Prod.snd h)
      rw [this, zero_smul]
    rw [holonomyDefectKernel_apply hK (hcfg ζ), hX, defectValue_zero, coeffOfEntries_zero]
  · rintro ⟨a, p⟩ ⟨c, b⟩
    refine ⟨Finset.univ.biUnion fun i => edgeIndices L k (facePosEdge p i), ?_, ?_⟩
    · intro κ hκ
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hκ
      obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hi
      have := euclidNormVec_edgeStart_sub_corner_le hL p i
      rw [← initial_facePosEdge] at this
      exact this
    · have hsub : ∀ i, edgeIndices L k (facePosEdge p i) ⊆
          Finset.univ.biUnion fun i => edgeIndices L k (facePosEdge p i) := fun i =>
        Finset.subset_biUnion_of_mem (fun i => edgeIndices L k (facePosEdge p i)) (Finset.mem_univ i)
      have hmono : ∀ i g, IsEntireOn (remainderIndex L k)
          (edgeIndices L k (facePosEdge p i)) g → IsEntireOn (remainderIndex L k)
          (Finset.univ.biUnion fun i => edgeIndices L k (facePosEdge p i)) g := fun i g =>
        (hC (remainderIndex L k) (edgeIndices L k (facePosEdge p i))).2.2.2 _ g (hsub i)
      have := isEntireOn_defectValue (F := remainderIndex L k) hC (finestMesh L k)
        (W := fun ζ => fieldOnFace (gaugeFieldOfForm L k ζ) p)
        (fun ζ i => (hcfg ζ).1 _)
        (fun i r s => hmono i _ (((hEnt L hL k).2 (facePosEdge p i) r s).1))
        (fun i r s => hmono i _ (((hEnt L hL k).2 (facePosEdge p i) r s).2))
        (formOnFace (basisFunction (c, b) : Fin 3 × PosEdge L k 0 → ℂ) p) a
      have e : (fun ζ => holonomyDefectKernel L k (gaugeFieldOfForm L k ζ) (a, p) (c, b)) =
          fun ζ => coeffOfEntries a (defectValue (finestMesh L k)
            (chainTransports (fieldOnFace (gaugeFieldOfForm L k ζ) p))
            (formOnFace (basisFunction (c, b) : Fin 3 × PosEdge L k 0 → ℂ) p)) :=
        funext fun ζ => holonomyDefectKernel_apply hK (hcfg ζ) a p (c, b)
      change IsEntireOn _ _ fun ζ =>
        holonomyDefectKernel L k (gaugeFieldOfForm L k ζ) (a, p) (c, b)
      rw [e]
      exact this
  · rintro ζ m ⟨a, p⟩ ⟨c, b⟩
    change holonomyDefectKernel L k (gaugeFieldOfForm L k
        (shiftField (remainderIndex L k) m ζ)) (a, shiftFace m p)
        (c, shiftEdge m b) = holonomyDefectKernel L k (gaugeFieldOfForm L k ζ) (a, p) (c, b)
    rw [holonomyDefectKernel_apply hK (hcfg _), holonomyDefectKernel_apply hK (hcfg _)]
    have hW : fieldOnFace (gaugeFieldOfForm L k (shiftField (remainderIndex L k) m ζ))
        (shiftFace m p) = fieldOnFace (gaugeFieldOfForm L k ζ) p := by
      funext i
      simp only [fieldOnFace]
      rw [faceEdge_shiftFace hL]
      exact hTr L hL k m ζ _
    have hX : formOnFace (basisFunction (c, shiftEdge m b) : Fin 3 × PosEdge L k 0 → ℂ)
        (shiftFace m p) =
        formOnFace (basisFunction (c, b) : Fin 3 × PosEdge L k 0 → ℂ) p := by
      funext i
      simp only [formOnFace, ofPauliCoeffs]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [facePosEdge_shiftFace hL, basisFunction_shiftEdge hL]
    rw [hW, hX]
end YangMills.Construction.Tower.FullSpace.HolonomyDefectLocality
end
