import YangMills.Construction.Towers.BoundsOfThePlaneWaveFunctionsAtTheFrequenciesProof
import YangMills.Construction.Towers.ExistenceOfTheBoundOfTheResponse
import YangMills.Construction.Towers.NormOfTheColourCoefficients
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.TheFormulaForTheCoefficientsOfTheResponse
import YangMills.Construction.Towers.TheFreePropagatorsAndTheirRootsProof
import YangMills.Construction.Towers.TheNormsOfTheResponseAtAPoint
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.ResponseBoundProof
open Matrices
open PeriodicOperators
open PeriodicOperators (colourEdges colourFaces colourVertices wNorm symbolHom)
open PlaneWaveCalculus
open PlaneWaves
open PlaneWaves.PlaneWaveBounds (complexPoint)
open ResponseProperties
open FreeStrip (halfSupRate)
theorem sum_smul_pauliFamily_mem (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
theorem pauliCoeff_smul (c : ℂ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (c • X) = c * pauliCoeff a X := by
  have hcX : c • X ∈ ComplexMatrix2.traceless := Submodule.smul_mem _ _ hX
  simp only [pauliCoeff, dif_pos hX, dif_pos hcX]
  have e : (⟨c • X, hcX⟩ : ComplexMatrix2.traceless) = c • ⟨X, hX⟩ := rfl
  rw [e, map_smul]
  rfl
def pauliVec (X : ComplexMatrix2) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 fun a => pauliCoeff a X
theorem pauliNorm_eq_norm (X : ComplexMatrix2) : pauliNorm X = ‖pauliVec X‖ := by
  rw [EuclideanSpace.norm_eq, pauliNorm]
  rfl
theorem pauliNorm_nonneg (X : ComplexMatrix2) : 0 ≤ pauliNorm X := Real.sqrt_nonneg _
theorem pauliNorm_add_le {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliNorm (X + Y) ≤ pauliNorm X + pauliNorm Y := by
  have e : pauliVec (X + Y) = pauliVec X + pauliVec Y := by
    ext a
    simpa [pauliVec] using pauliCoeff_add hX hY a
  rw [pauliNorm_eq_norm, pauliNorm_eq_norm, pauliNorm_eq_norm, e]
  exact norm_add_le _ _
theorem pauliNorm_smul (c : ℂ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    pauliNorm (c • X) = ‖c‖ * pauliNorm X := by
  have e : pauliVec (c • X) = c • pauliVec X := by
    ext a
    simpa [pauliVec] using pauliCoeff_smul c hX a
  rw [pauliNorm_eq_norm, pauliNorm_eq_norm, e, norm_smul]
theorem pauliNorm_sub_le {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliNorm (X - Y) ≤ pauliNorm X + pauliNorm Y := by
  have e : X - Y = X + (-1 : ℂ) • Y := by simp [sub_eq_add_neg]
  have h := pauliNorm_add_le hX (Submodule.smul_mem _ (-1 : ℂ) hY)
  rw [pauliNorm_smul _ hY] at h
  rw [e]
  simpa using h
theorem pauliNorm_le_familyNorm (F : Fin 4 → ComplexMatrix2) (ρ : Fin 4) :
    pauliNorm (F ρ) ≤ pauliFamilyNorm F := by
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  exact Finset.single_le_sum (f := fun i => pauliNorm (F i) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ ρ)
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem finite_vertexClass {L k : ℕ} (h : Finite (colourVertices L k 0).UnitQuot) :
    Finite (VertexClass L k) := by
  let f : (colourVertices L k 0).UnitQuot → VertexClass L k :=
    Quot.lift (fun ι => Quot.mk _ ι.2) (by
      rintro ι _ ⟨n, rfl⟩
      exact Quot.sound ⟨1 • n, rfl⟩)
  refine Finite.of_surjective f fun c => ?_
  induction c using Quot.ind with
  | mk x => exact ⟨Quot.mk _ ((0 : Fin 3), x), rfl⟩
theorem edgeFourierCoeff_mem (L k : ℕ) [Finite (VertexClass L k)]
    (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) (m : Fin 4 → ℤ) :
    edgeFourierCoeff L k b μ m ∈ ComplexMatrix2.traceless := by
  have := Fintype.ofFinite (VertexClass L k)
  simp only [edgeFourierCoeff, PlaneWaves.fourierCoeff]
  rw [finsum_eq_sum_of_fintype]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ (ofPauliCoeffs_mem _ _))
theorem pauliNorm_edgeFourierCoeff_le {L k : ℕ} (hC : EdgeCoeffFacts L k)
    (c : (colourEdges L k 0).UnitQuot → ℂ) {m : Fin 4 → ℤ} (hm : m ∈ freqBox L k) (μ : Fin 4) :
    pauliNorm (edgeFourierCoeff L k c μ m) ≤
      wNorm ((colourEdges L k 0).quotWeight 1) c := by
  refine (pauliNorm_le_familyNorm (fun μ => edgeFourierCoeff L k c μ m) μ).trans ?_
  rw [pauliFamilyNorm]
  refine Real.sqrt_le_iff.2 ⟨Real.sqrt_nonneg _, ?_⟩
  rw [hC.norm_sq c]
  exact Finset.single_le_sum
    (f := fun m => ∑ μ, pauliNorm (edgeFourierCoeff L k c μ m) ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) hm
theorem oddHarmonicWeight_nonneg (n : ℤ) : 0 ≤ oddHarmonicWeight n := by apply _root_.YangMills.Construction.Tower.FrequencyBounds.oddHarmonicWeight_nonneg <;> assumption
theorem one_le_supNormVec {m : Fin 4 → ℤ} (hm : m ≠ 0) :
    1 ≤ TorusMetric.supNormVec fun ν => (m ν : ℝ) := by apply _root_.YangMills.Construction.Tower.FrequencyBounds.one_le_supNormVec <;> assumption
theorem oddHarmonicWeightTerm_nonneg {m : Fin 4 → ℤ} (hm : m ≠ 0) : 0 ≤ oddHarmonicWeightTerm m := by
  have h := one_le_supNormVec hm
  exact mul_nonneg (inv_nonneg.2 (by linarith))
    (Finset.prod_nonneg fun ν _ => oddHarmonicWeight_nonneg (m ν))
theorem sum_weightTerm_le (h : oddHarmonicWeightSum < ∞) (F : Finset (Fin 4 → ℤ)) :
    ∑ m ∈ F.erase 0, oddHarmonicWeightTerm m ≤ oddHarmonicWeightSum.toReal := by
  have hnn : ∀ m ∈ F.erase 0, 0 ≤ oddHarmonicWeightTerm m := fun m hm =>
    oddHarmonicWeightTerm_nonneg (Finset.ne_of_mem_erase hm)
  rw [← ENNReal.ofReal_le_iff_le_toReal h.ne, ENNReal.ofReal_sum_of_nonneg hnn]
  have hs := le_iSup (fun s : Finset {m : Fin 4 → ℤ // m ≠ 0} =>
    ∑ m ∈ s, ENNReal.ofReal (oddHarmonicWeightTerm m)) ((F.erase 0).subtype (· ≠ 0))
  refine le_of_eq_of_le ?_ hs
  exact (Finset.sum_subtype_of_mem (fun m : Fin 4 → ℤ => ENNReal.ofReal (oddHarmonicWeightTerm m))
    fun m hm => Finset.ne_of_mem_erase hm).symm
theorem sum_le_of_termwise (h : oddHarmonicWeightSum < ∞) (F : Finset (Fin 4 → ℤ))
    (a : (Fin 4 → ℤ) → ℝ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h₀ : 0 ∈ F → a 0 ≤ A)
    (hm : ∀ m ∈ F, m ≠ 0 → a m ≤ B * oddHarmonicWeightTerm m) :
    ∑ m ∈ F, a m ≤ A + B * oddHarmonicWeightSum.toReal := by
  have h₁ : ∑ m ∈ F.erase 0, a m ≤ B * oddHarmonicWeightSum.toReal := by
    refine (Finset.sum_le_sum fun m hm' =>
      hm m (Finset.mem_of_mem_erase hm') (Finset.ne_of_mem_erase hm')).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_weightTerm_le h F) hB
  by_cases h0 : (0 : Fin 4 → ℤ) ∈ F
  · rw [← Finset.add_sum_erase F a h0]
    linarith [h₀ h0]
  · rw [Finset.erase_eq_of_notMem h0] at h₁
    linarith
theorem le_of_scaled_le {D x s A : ℝ} (hs : 1 ≤ s) (hD : 2 * s ^ 2 ≤ D) (hx : 0 ≤ x)
    (h : D * x ≤ s * A) : x ≤ A / 2 * s⁻¹ := by
  have h₁ : s * (2 * s * x) ≤ s * A := by nlinarith
  have h₂ : 2 * s * x ≤ A := le_of_mul_le_mul_left h₁ (by linarith)
  have hs0 : 0 < s := by linarith
  rw [← div_eq_mul_inv, le_div_iff₀ hs0]
  linarith
theorem symbolHom_eq (I I' : PeriodicData) [Finite I.UnitQuot] (T : I'.Carrier → I.Carrier → ℂ)
    (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) :
    symbolHom I I' T κ φ = applyKernel (quotSymbol I I' T κ) φ :=
  linearMapOfEntries_eq_applyKernel _ _
theorem coboundary_blochWave (hFO : FreeOperators.FreeOperatorsArePeriodic)
    (hS : SymbolCalculus.Claim) (hSym : Symbols.Claim) (hId : IdKernelFacts.Claim)
    {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hB : IsPeriodic (colourEdges L k 0))
    (hP : IsPeriodic (colourFaces L k 0))
    (q : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ) :
    (FullSpace.edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (FullSpace.Face L k 0))
        FullSpace.scaledEdgeCoboundary (blochWave (colourEdges L k 0) q b) =
      blochWave (colourFaces L k 0) q
        (symbolHom (colourEdges L k 0) (colourFaces L k 0)
          (FullSpace.scaledEdgeCoboundaryKernel L k 0) q b) := by
  have hk3 := (hFO.2 L hL k hk).1.edgeCoboundary 0 (Nat.zero_le k)
  obtain ⟨hper, hfin, hrate⟩ := hk3.finite_range
  have hent := (hS _ _ hB hP).1 _ hper hfin
  have hI := hId _ hB
  have facts := hSym.1 _ _ _ hB hP hB _ (idKernel _) 1 hper (hrate 1 one_pos) hI.1
    (hI.2.1 1 one_pos)
  have : Finite (colourEdges L k 0).UnitQuot := hB.finite_quot
  rw [← hk3.applyKernel_eq]
  funext ι'
  rw [(facts.applyKernel_blochWave q (hent.1 q (mem_univ q)) b ι').2]
  exact congrArg (fun φ => blochWave (colourFaces L k 0) q φ ι')
    (symbolHom_eq (colourEdges L k 0) (colourFaces L k 0)
      (FullSpace.scaledEdgeCoboundaryKernel L k 0) q b).symm
theorem modulatedForm_eq (L k : ℕ) (q : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ) :
    modulatedForm L k q (edgeFieldOfClasses L k b) =
      (FullSpace.edgePauliCoordinates L k 0).ofCoeffs (blochWave (colourEdges L k 0) q b) := by
  unfold modulatedForm
  simp only [FullSpace.edgePauliCoordinates]
  congr 1
  funext β
  by_cases h : β.IsPositivelyOriented
  · simp only [dif_pos h, edgeFieldOfClasses, ofPauliCoeffs, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_smul]
    rfl
  · simp only [dif_neg h]
open Classical in
theorem ofCoeffs_mem_traceless (L k : ℕ) (c : (FullSpace.edgePauliCoordinates L k 0).Index → ℂ)
    (β : FullSpace.Edge L k 0) :
    (FullSpace.edgePauliCoordinates L k 0).ofCoeffs c β ∈ ComplexMatrix2.traceless := by
  have hf : ∀ β' : FullSpace.Edge L k 0,
      (if h : β'.IsPositivelyOriented then ofPauliCoeffs c ⟨β', h⟩ else 0) ∈
        ComplexMatrix2.traceless := by
    intro β'
    split_ifs with h
    · exact sum_smul_pauliFamily_mem _
    · exact Submodule.zero_mem _
  simp only [FullSpace.edgePauliCoordinates, FullSpace.extendOddly]
  by_cases h : β.IsPositivelyOriented
  · rw [if_pos h]
    exact hf β
  · rw [if_neg h]
    exact Submodule.neg_mem _ (hf β.opposite)
theorem scaledCoboundary_eq_at_face (L k : ℕ) (q : Fin 4 → ℂ)
    (b : (colourEdges L k 0).UnitQuot → ℂ)
    (F : (colourFaces L k 0).UnitQuot → ℂ)
    (hmap : (FullSpace.edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (FullSpace.Face L k 0))
        FullSpace.scaledEdgeCoboundary (blochWave (colourEdges L k 0) q b) =
      blochWave (colourFaces L k 0) q F) (P : FullSpace.Face L k 0) :
    FullSpace.scaledEdgeCoboundary (L := L) (k := k) (j := 0)
        (modulatedForm L k q (edgeFieldOfClasses L k b)) P =
      expWave q P.corner • faceFieldOfClasses L k F P := by
  rw [modulatedForm_eq]
  have hW := ofCoeffs_mem_traceless L k (blochWave (colourEdges L k 0) q b)
  set W := (FullSpace.edgePauliCoordinates L k 0).ofCoeffs (blochWave (colourEdges L k 0) q b) with hWdef
  have hmem : FullSpace.scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P ∈
      ComplexMatrix2.traceless := by
    have h₁ : FullSpace.edgeCoboundary W P ∈ ComplexMatrix2.traceless :=
      Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ (hW _) (hW _)) (hW _)) (hW _)
    have ht : Matrix.trace (FullSpace.edgeCoboundary W P) = 0 := h₁
    show Matrix.trace ((meshAt L k 0)⁻¹ • FullSpace.edgeCoboundary W P) = 0
    rw [Matrix.trace_smul, ht, smul_zero]
  have hc : ∀ a, pauliCoeff a (FullSpace.scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P) =
      blochWave (colourFaces L k 0) q F (a, P) := fun a => congrFun hmap (a, P)
  calc FullSpace.scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P
      = ∑ a, pauliCoeff a (FullSpace.scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P) •
          ComplexMatrix2.pauliFamily a := (sum_pauliCoeff_smul hmem).symm
    _ = ∑ a, blochWave (colourFaces L k 0) q F (a, P) • ComplexMatrix2.pauliFamily a := by
      simp only [hc]
    _ = expWave q P.corner • faceFieldOfClasses L k F P := by
      simp only [faceFieldOfClasses, ofPauliCoeffs, Finset.smul_sum, smul_smul]
      rfl
theorem norm_integerWave (m : Fin 4 → ℤ) (x : InfiniteLattice.AmbientSpace) :
    ‖integerWave m x‖ = 1 := by
  have e : 2 * (Real.pi : ℂ) * Complex.I * bilinDot (toComplexVec (castVec m)) (toComplexVec x) =
      ((2 * Real.pi * ∑ ν, (m ν : ℝ) * x ν : ℝ) : ℂ) * Complex.I := by
    simp only [bilinDot, toComplexVec, castVec]
    push_cast
    ring
  rw [integerWave, e, Complex.norm_exp_ofReal_mul_I]
theorem operatorNorm_wave_sum_le (hO : PauliCoefficientNorm.OperatorNormComparison)
    (F : Finset (Fin 4 → ℤ)) (c : (Fin 4 → ℤ) → ComplexMatrix2)
    (hc : ∀ m ∈ F, c m ∈ ComplexMatrix2.traceless)
    (x : InfiniteLattice.AmbientSpace) :
    ComplexMatrix2.operatorNorm (∑ m ∈ F, integerWave m x • c m) ≤
      Real.sqrt 2 * ∑ m ∈ F, pauliNorm (c m) := by
  rw [Finset.mul_sum]
  refine (norm_sum_le F fun m => integerWave m x • c m).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [norm_smul, norm_integerWave, one_mul]
  exact (hO.1 ⟨c m, hc m hm⟩).2
theorem exists_eq_edgeAt {L k : ℕ} (β : PeriodicOperators.PosEdge L k 0) :
    ∃ x μ, β = edgeAt L k x μ := by apply _root_.YangMills.Construction.Tower.FreeResolvents.edgeCover <;> assumption
section NonzeroMode
variable {L k : ℕ} {p : Fin 4 → ℂ} {ε : (colourEdges L k k).UnitQuot → ℂ} {m : Fin 4 → ℤ}
theorem topVertexElement_mem (g : (colourVertices L k k).UnitQuot → ℂ) :
    topVertexElement L k g ∈ ComplexMatrix2.traceless :=
  ofPauliCoeffs_mem _ _
theorem topEdgeComponent_mem (z : (colourEdges L k k).UnitQuot → ℂ) (μ : Fin 4) :
    topEdgeComponent L k z μ ∈ ComplexMatrix2.traceless :=
  ofPauliCoeffs_mem _ _
theorem coeff_ineq {u n d v G s W N : ℝ} (hs : 1 ≤ s) (hW : 0 ≤ W) (hn₀ : 0 ≤ n)
    (hn : n ≤ N) (hG : 0 ≤ G) (hv₀ : 0 ≤ v) (h₁ : u ≤ 40 * W) (h₂ : d ≤ 12 * s) (h₃ : v ≤ 16 * W) :
    u * n + d * v * G ≤ s * (W * (40 * N + 192 * G)) := by
  have hN : 0 ≤ N := hn₀.trans hn
  have a₁ : u * n ≤ 40 * W * N := mul_le_mul h₁ hn hn₀ (by positivity)
  have a₂ : d * v * G ≤ 12 * s * (16 * W) * G :=
    mul_le_mul_of_nonneg_right (mul_le_mul h₂ h₃ hv₀ (by positivity)) hG
  have a₃ : 40 * W * N ≤ s * (40 * W * N) := le_mul_of_one_le_left (by positivity) hs
  nlinarith [a₁, a₂, a₃]
theorem curl_ineq {d u n d' u' n' s W N : ℝ} (hs : 1 ≤ s) (hW : 0 ≤ W) (hn₀ : 0 ≤ n)
    (hn₀' : 0 ≤ n') (hn : n ≤ N) (hn' : n' ≤ N) (hu₀ : 0 ≤ u) (hu₀' : 0 ≤ u') (h₁ : d ≤ 12 * s)
    (h₁' : d' ≤ 12 * s) (h₂ : u ≤ 40 * W) (h₂' : u' ≤ 40 * W) :
    d * u * n + d' * u' * n' ≤ s * (W * (960 * N)) := by
  have a₁ : d * u * n ≤ 12 * s * (40 * W) * N :=
    mul_le_mul (mul_le_mul h₁ h₂ hu₀ (by positivity)) hn hn₀ (by positivity)
  have a₂ : d' * u' * n' ≤ 12 * s * (40 * W) * N :=
    mul_le_mul (mul_le_mul h₁' h₂' hu₀' (by positivity)) hn' hn₀' (by positivity)
  nlinarith [a₁, a₂]
theorem pauliNorm_edgeFourierCoeff_le_term [Finite (VertexClass L k)]
    (hmod : ResponseModeEquations L k p ε)
    (hm : m ∈ freqBox L k) (hm0 : m ≠ 0)
    (hb : FrequencyBounds.BoundsAtFrequency L k p m) (μ : Fin 4) :
    pauliNorm (edgeFourierCoeff L k (responseSymbolForm L k p ε) μ m) ≤
      (20 * pauliFamilyNorm (topEdgeComponent L k (defectSymbol L k p ε)) +
        96 * pauliNorm (topVertexElement L k (smoothedDivergence L k p ε))) *
        oddHarmonicWeightTerm m := by
  have hs := one_le_supNormVec hm0
  have hW : 0 ≤ ∏ ν, oddHarmonicWeight (m ν) :=
    Finset.prod_nonneg fun ν _ => oddHarmonicWeight_nonneg (m ν)
  have hmem := edgeFourierCoeff_mem L k (responseSymbolForm L k p ε) μ m
  have key : ‖symbolSquare L k (PlaneWaves.shiftedFreq p m)‖ *
      pauliNorm (edgeFourierCoeff L k (responseSymbolForm L k p ε) μ m) ≤
      (TorusMetric.supNormVec fun ν => (m ν : ℝ)) *
        ((∏ ν, oddHarmonicWeight (m ν)) *
          (40 * pauliFamilyNorm (topEdgeComponent L k (defectSymbol L k p ε)) +
            192 * pauliNorm (topVertexElement L k (smoothedDivergence L k p ε)))) := by
    rw [← pauliNorm_smul _ hmem, hmod m hm μ]
    refine (pauliNorm_add_le (Submodule.smul_mem _ _ (topEdgeComponent_mem _ μ))
      (Submodule.smul_mem _ _ (topVertexElement_mem _))).trans ?_
    rw [pauliNorm_smul _ (topEdgeComponent_mem _ μ), pauliNorm_smul _ (topVertexElement_mem _),
      norm_mul]
    exact coeff_ineq hs hW (pauliNorm_nonneg _)
      (pauliNorm_le_familyNorm (topEdgeComponent L k (defectSymbol L k p ε)) μ) (pauliNorm_nonneg _)
      (norm_nonneg _) (hb.edgeWeight_neg_le μ) (hb.forwardSymbol_le μ) hb.vertexWeight_neg_le
  have h := le_of_scaled_le hs hb.symbolSquare_ge (pauliNorm_nonneg _) key
  refine h.trans (le_of_eq ?_)
  unfold oddHarmonicWeightTerm
  ring
theorem pauliNorm_curl_le_term [Finite (VertexClass L k)] (hmod : ResponseModeEquations L k p ε)
    (hm : m ∈ freqBox L k) (hm0 : m ≠ 0)
    (hb : FrequencyBounds.BoundsAtFrequency L k p m) (μ ν : Fin 4) :
    pauliNorm (forwardSymbol L k (PlaneWaves.shiftedFreq p m) μ •
          edgeFourierCoeff L k (responseSymbolForm L k p ε) ν m -
        forwardSymbol L k (PlaneWaves.shiftedFreq p m) ν •
          edgeFourierCoeff L k (responseSymbolForm L k p ε) μ m) ≤
      480 * pauliFamilyNorm (topEdgeComponent L k (defectSymbol L k p ε)) *
        oddHarmonicWeightTerm m := by
  have hs := one_le_supNormVec hm0
  have hW : 0 ≤ ∏ ρ, oddHarmonicWeight (m ρ) :=
    Finset.prod_nonneg fun ρ _ => oddHarmonicWeight_nonneg (m ρ)
  have hmem : forwardSymbol L k (PlaneWaves.shiftedFreq p m) μ •
        edgeFourierCoeff L k (responseSymbolForm L k p ε) ν m -
      forwardSymbol L k (PlaneWaves.shiftedFreq p m) ν •
        edgeFourierCoeff L k (responseSymbolForm L k p ε) μ m ∈
      ComplexMatrix2.traceless :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ (edgeFourierCoeff_mem L k _ ν m))
      (Submodule.smul_mem _ _ (edgeFourierCoeff_mem L k _ μ m))
  have e : symbolSquare L k (PlaneWaves.shiftedFreq p m) •
      (forwardSymbol L k (PlaneWaves.shiftedFreq p m) μ •
          edgeFourierCoeff L k (responseSymbolForm L k p ε) ν m -
        forwardSymbol L k (PlaneWaves.shiftedFreq p m) ν •
          edgeFourierCoeff L k (responseSymbolForm L k p ε) μ m) =
      (forwardSymbol L k (PlaneWaves.shiftedFreq p m) μ *
          edgeWeight L k (-PlaneWaves.shiftedFreq p m) ν) •
          topEdgeComponent L k (defectSymbol L k p ε) ν -
        (forwardSymbol L k (PlaneWaves.shiftedFreq p m) ν *
          edgeWeight L k (-PlaneWaves.shiftedFreq p m) μ) •
          topEdgeComponent L k (defectSymbol L k p ε) μ := by
    have h₁ := hmod m hm ν
    have h₂ := hmod m hm μ
    calc _ = forwardSymbol L k (PlaneWaves.shiftedFreq p m) μ •
            (symbolSquare L k (PlaneWaves.shiftedFreq p m) •
              edgeFourierCoeff L k (responseSymbolForm L k p ε) ν m) -
          forwardSymbol L k (PlaneWaves.shiftedFreq p m) ν •
            (symbolSquare L k (PlaneWaves.shiftedFreq p m) •
              edgeFourierCoeff L k (responseSymbolForm L k p ε) μ m) := by module
      _ = _ := by
        rw [h₁, h₂]
        module
  have key : ‖symbolSquare L k (PlaneWaves.shiftedFreq p m)‖ *
      pauliNorm (forwardSymbol L k (PlaneWaves.shiftedFreq p m) μ •
          edgeFourierCoeff L k (responseSymbolForm L k p ε) ν m -
        forwardSymbol L k (PlaneWaves.shiftedFreq p m) ν •
          edgeFourierCoeff L k (responseSymbolForm L k p ε) μ m) ≤
      (TorusMetric.supNormVec fun ρ => (m ρ : ℝ)) *
        ((∏ ρ, oddHarmonicWeight (m ρ)) *
          (960 * pauliFamilyNorm (topEdgeComponent L k (defectSymbol L k p ε)))) := by
    rw [← pauliNorm_smul _ hmem, e]
    refine (pauliNorm_sub_le (Submodule.smul_mem _ _ (topEdgeComponent_mem _ ν))
      (Submodule.smul_mem _ _ (topEdgeComponent_mem _ μ))).trans ?_
    rw [pauliNorm_smul _ (topEdgeComponent_mem _ ν), pauliNorm_smul _ (topEdgeComponent_mem _ μ),
      norm_mul, norm_mul]
    exact curl_ineq hs hW (pauliNorm_nonneg _) (pauliNorm_nonneg _)
      (pauliNorm_le_familyNorm (topEdgeComponent L k (defectSymbol L k p ε)) ν)
      (pauliNorm_le_familyNorm (topEdgeComponent L k (defectSymbol L k p ε)) μ)
      (norm_nonneg _) (norm_nonneg _) (hb.forwardSymbol_le μ) (hb.forwardSymbol_le ν)
      (hb.edgeWeight_neg_le ν) (hb.edgeWeight_neg_le μ)
  have h := le_of_scaled_le hs hb.symbolSquare_ge (pauliNorm_nonneg _) key
  refine h.trans (le_of_eq ?_)
  unfold oddHarmonicWeightTerm
  ring
end NonzeroMode
theorem finestMesh_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.finestMesh_pos <;> assumption
theorem finestMesh_le_one {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    finestMesh L k ≤ 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.finestMesh_le_one <;> assumption
theorem norm_forwardSymbol_zero_le (hE : PlaneWaves.PlaneWaveBounds.Claim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {p : Fin 4 → ℂ}
    (hre : ∀ ρ, |(p ρ).re| ≤ Real.pi) (him : ∀ ρ, |(p ρ).im| ≤ 1 / 8) (μ : Fin 4) :
    ‖forwardSymbol L k (PlaneWaves.shiftedFreq p 0) μ‖ ≤ 4 := by
  have e₁ : PlaneWaves.shiftedFreq p 0 = p := by
    funext ρ
    simp [PlaneWaves.shiftedFreq]
  have e₂ : complexPoint (fun ρ => (p ρ).re) (fun ρ => (p ρ).im) = p := by
    funext ρ
    simp only [complexPoint]
    rw [mul_comm]
    exact Complex.re_add_im (p ρ)
  have hη := finestMesh_pos hL k
  have hq : ∀ ρ, |(fun ρ => (p ρ).re) ρ| ≤ Real.pi / finestMesh L k := fun ρ => by
    refine (hre ρ).trans ?_
    rw [le_div_iff₀ hη]
    exact mul_le_of_le_one_right Real.pi_pos.le (finestMesh_le_one hL k)
  obtain ⟨-, hD, -⟩ := hE.1 L k hL hk _ _ hq him
  have h₁ := (hD.2.2.2.2.1 μ).1
  have h₂ := (hD.1 μ).2
  rw [e₂] at h₁
  rw [e₁]
  have h₃ := hre μ
  have h₄ := Real.pi_lt_d2
  simp only at h₂
  linarith
theorem pauliNorm_curl_zero_le {L k : ℕ} [Finite (VertexClass L k)] (hC : EdgeCoeffFacts L k)
    {p : Fin 4 → ℂ} (h0 : (0 : Fin 4 → ℤ) ∈ freqBox L k)
    (hd : ∀ μ, ‖forwardSymbol L k (PlaneWaves.shiftedFreq p 0) μ‖ ≤ 4)
    (b : (colourEdges L k 0).UnitQuot → ℂ) (μ ν : Fin 4) :
    pauliNorm (forwardSymbol L k (PlaneWaves.shiftedFreq p 0) μ • edgeFourierCoeff L k b ν 0 -
        forwardSymbol L k (PlaneWaves.shiftedFreq p 0) ν • edgeFourierCoeff L k b μ 0) ≤
      8 * wNorm ((colourEdges L k 0).quotWeight 1) b := by
  have hν := edgeFourierCoeff_mem L k b ν 0
  have hμ := edgeFourierCoeff_mem L k b μ 0
  refine (pauliNorm_sub_le (Submodule.smul_mem _ _ hν) (Submodule.smul_mem _ _ hμ)).trans ?_
  rw [pauliNorm_smul _ hν, pauliNorm_smul _ hμ]
  have a₁ := pauliNorm_edgeFourierCoeff_le hC b h0 ν
  have a₂ := pauliNorm_edgeFourierCoeff_le hC b h0 μ
  have b₁ := mul_le_mul (hd μ) a₁ (pauliNorm_nonneg _) (by norm_num)
  have b₂ := mul_le_mul (hd ν) a₂ (pauliNorm_nonneg _) (by norm_num)
  linarith
theorem edgeBound_nonneg {r B N G S : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B) (hN : 0 ≤ N) (hG : 0 ≤ G)
    (hS : 0 ≤ S) : 0 ≤ r * (B + (20 * N + 96 * G) * S) := by
  positivity
theorem faceBound_nonneg {r B N S : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B) (hN : 0 ≤ N) (hS : 0 ≤ S) :
    0 ≤ r * (8 * B + 480 * N * S) := by
  positivity
theorem total_ineq {r S B N G E c a f : ℝ} (hr : 0 ≤ r) (hS : 0 ≤ S) (hB : B ≤ c * E)
    (hN : N ≤ c * E) (hG : G ≤ c * E) (ha : a ≤ r * (B + (20 * N + 96 * G) * S))
    (hf : f ≤ r * (8 * B + 480 * N * S)) :
    B + N + G + a + f ≤
      (3 * c + r * (c + 116 * c * S) + r * (8 * c + 480 * c * S)) * E := by
  have h₁ : r * (B + (20 * N + 96 * G) * S) ≤ r * ((c + 116 * c * S) * E) := by
    refine mul_le_mul_of_nonneg_left ?_ hr
    have : (20 * N + 96 * G) * S ≤ (116 * (c * E)) * S :=
      mul_le_mul_of_nonneg_right (by linarith) hS
    linarith
  have h₂ : r * (8 * B + 480 * N * S) ≤ r * ((8 * c + 480 * c * S) * E) := by
    refine mul_le_mul_of_nonneg_left ?_ hr
    have : 480 * N * S ≤ (480 * (c * E)) * S :=
      mul_le_mul_of_nonneg_right (by linarith) hS
    linarith
  calc B + N + G + a + f
      ≤ c * E + c * E + c * E + r * ((c + 116 * c * S) * E) +
          r * ((8 * c + 480 * c * S) * E) := by linarith
    _ = _ := by ring
theorem responseBoundExists (hFormula : ResponseCoefficientFormula.Claim)
    (hNorms : ResponseNormBounds.Claim)
    (hFreq : FrequencyBounds.FrequencyBoundsHold)
    (hW : PlaneWaveCalculus.PlaneWaveCalculusHolds) (hNorm : PauliCoefficientNorm.Claim)
    (hE : PlaneWaves.PlaneWaveBounds.Claim)
    (hNum : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hI : TowerIndexSets.Claim) (hFO : FreeOperators.FreeOperatorsArePeriodic)
    (hS : SymbolCalculus.Claim) (hSym : Symbols.Claim)
    (hId : IdKernelFacts.Claim) : ResponseBoundExists := by
  obtain ⟨C, hC⟩ := hNorms
  have hfin : oddHarmonicWeightSum < ∞ := hE.2
  have hO := hNorm.2.1
  have hS₀ : 0 ≤ oddHarmonicWeightSum.toReal := ENNReal.toReal_nonneg
  have hr₂ : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  refine ⟨3 * |C| + Real.sqrt 2 * (|C| + 116 * |C| * oddHarmonicWeightSum.toReal) +
    Real.sqrt 2 * (8 * |C| + 480 * |C| * oddHarmonicWeightSum.toReal), ?_⟩
  intro δ₀ hδ L hL k hk p hp ε α f hα hf
  obtain ⟨pS, pB, pP⟩ := hI L hL k 0 (Nat.zero_le k)
  have : Finite (VertexClass L k) := finite_vertexClass pS.finite_quot
  have hcalc := hW L hL k hk
  have hedges : EdgeCoeffFacts L k := hcalc.2.2.1
  have hfaces : FaceCoeffFacts L k := hcalc.2.2.2.1
  have hact : CoboundarySymbols L k := hcalc.2.2.2.2.2.1
  have hmod := hFormula δ₀ hδ L hL k hk p hp ε
  have hfreq := hFreq δ₀ hδ L hL k hk p hp
  have him : ∀ ρ, |(p ρ).im| ≤ 1 / 8 := by
    obtain ⟨-, -, δ₁, hδ₁, C₀, -, hI', -⟩ := hNum
    have hδ' : δ₀ ≤ 1 / 64 := by
      rw [Part.mem_unique hδ hδ₁]
      exact hI'.2
    intro ρ
    have h : |(p ρ).im| ≤ 2 * δ₀ := hp.1 ρ
    linarith
  have hd0 := norm_forwardSymbol_zero_le hE hL hk hp.2 him
  obtain ⟨hB, hN, hG⟩ := hC δ₀ hδ L hL k hk p hp ε
  have hE₀ : 0 ≤ pauliFamilyNorm (topEdgeComponent L k ε) := Real.sqrt_nonneg _
  have hCE : C * pauliFamilyNorm (topEdgeComponent L k ε) ≤
      |C| * pauliFamilyNorm (topEdgeComponent L k ε) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hE₀
  set B := wNorm ((colourEdges L k 0).quotWeight 1) (responseSymbolForm L k p ε) with hBdef
  set N := pauliFamilyNorm (topEdgeComponent L k (defectSymbol L k p ε)) with hNdef
  set G := pauliNorm (topVertexElement L k (smoothedDivergence L k p ε)) with hGdef
  set E := pauliFamilyNorm (topEdgeComponent L k ε) with hEdef
  set S := oddHarmonicWeightSum.toReal with hSdef
  have hB₀ : 0 ≤ B := Real.sqrt_nonneg _
  have hN₀ : 0 ≤ N := Real.sqrt_nonneg _
  have hG₀ : 0 ≤ G := Real.sqrt_nonneg _
  have hαb : ∀ β, ComplexMatrix2.operatorNorm (α β) ≤ Real.sqrt 2 * (B + (20 * N + 96 * G) * S) := by
    intro β
    obtain ⟨x, μ, rfl⟩ := exists_eq_edgeAt β
    rw [hα x μ]
    refine (operatorNorm_wave_sum_le hO _ _ (fun m _ => edgeFourierCoeff_mem L k _ μ m) x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hr₂
    exact sum_le_of_termwise hfin _
      (fun m => pauliNorm (edgeFourierCoeff L k (responseSymbolForm L k p ε) μ m))
      hB₀ (add_nonneg (mul_nonneg (by norm_num) hN₀) (mul_nonneg (by norm_num) hG₀))
      (fun h0 => pauliNorm_edgeFourierCoeff_le hedges _ h0 μ)
      fun m hm h0 => pauliNorm_edgeFourierCoeff_le_term hmod hm h0 (hfreq m hm h0) μ
  have hαform : α = edgeFieldOfClasses L k (responseSymbolForm L k p ε) := by
    funext β
    obtain ⟨x, μ, rfl⟩ := exists_eq_edgeAt β
    rw [hα x μ, hedges.expansion _ μ x]
  have hfP : ∀ P, f P = faceFieldOfClasses L k
      (symbolHom (colourEdges L k 0) (colourFaces L k 0)
        (FullSpace.scaledEdgeCoboundaryKernel L k 0) p (responseSymbolForm L k p ε)) P := by
    intro P
    have h := hf P
    rw [hαform, scaledCoboundary_eq_at_face L k p _ _
      (coboundary_blochWave hFO hS hSym hId hL hk pB pP p _) P] at h
    exact (smul_right_injective ComplexMatrix2 (Complex.exp_ne_zero _) h).symm
  have hfb : ∀ P, ComplexMatrix2.operatorNorm (f P) ≤ Real.sqrt 2 * (8 * B + 480 * N * S) := by
    rintro ⟨x, μ, ν, h⟩
    rw [hfP, hfaces.expansion _ μ ν h x,
      Finset.sum_congr rfl fun m hm => by rw [hact.edgeCoboundary p _ μ ν h m hm]]
    refine (operatorNorm_wave_sum_le hO _ _ (fun m _ => Submodule.sub_mem _
      (Submodule.smul_mem _ _ (edgeFourierCoeff_mem L k _ ν m))
      (Submodule.smul_mem _ _ (edgeFourierCoeff_mem L k _ μ m))) x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hr₂
    exact sum_le_of_termwise hfin _ (fun m => pauliNorm
        (forwardSymbol L k (PlaneWaves.shiftedFreq p m) μ •
            edgeFourierCoeff L k (responseSymbolForm L k p ε) ν m -
          forwardSymbol L k (PlaneWaves.shiftedFreq p m) ν •
            edgeFourierCoeff L k (responseSymbolForm L k p ε) μ m))
      (mul_nonneg (by norm_num) hB₀) (mul_nonneg (by norm_num) hN₀)
      (fun h0 => pauliNorm_curl_zero_le hedges h0 hd0 _ μ ν)
      fun m hm h0 => pauliNorm_curl_le_term hmod hm h0 (hfreq m hm h0) μ ν
  have hA₀ := edgeBound_nonneg hr₂ hB₀ hN₀ hG₀ hS₀
  have hF₀ := faceBound_nonneg hr₂ hB₀ hN₀ hS₀
  refine ⟨⟨_, by rintro _ ⟨β, rfl⟩; exact hαb β⟩, ⟨_, by rintro _ ⟨P, rfl⟩; exact hfb P⟩, ?_⟩
  exact total_ineq hr₂ hS₀ (hB.trans hCE) (hN.trans hCE) (hG.trans hCE) (Real.iSup_le hαb hA₀)
    (Real.iSup_le hfb hF₀)
end YangMills.Construction.Tower.ResponseBoundProof
end
