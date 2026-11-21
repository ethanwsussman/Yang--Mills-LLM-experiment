import YangMills.Construction.Towers.ExistenceOfTheBoundOfTheResponseProof
import YangMills.Construction.PeriodicOperators.ComponentsOfAJetWithBoundedRowsProof
import YangMills.Construction.Towers.CoefficientsOfTheHalfPlaquetteTraceNearAnIndexProof
import YangMills.Construction.Towers.PropertiesOfTheBackgroundsProof
import YangMills.Construction.Towers.TheBackgroundsAreBoundedNearAPoint
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundsBoundedNearPoint
open PeriodicOperators
open Matrices
open BackgroundJets
open FinestLatticeNeighbours
open BackgroundProperties (edgeFormOf faceFunctionOf edgeCoboundarySymbol)
open PeriodicLattice (supOfOperatorNorms)
open scoped Matrix.Norms.L2Operator
theorem finestMesh_le_one {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) :
    finestMesh L k ≤ 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.HalfFaceTraceNearIndex.finestMesh_le_one <;> assumption
theorem norm_exp_phase_le {δ η : ℝ} (hη : η ≤ 1) {q : Fin 4 → ℂ} (hq : q ∈ momentumPolydisc δ)
    {x y : InfiniteLattice.AmbientSpace} (hxy : WithinBox (2 * η) x y) :
    ‖Complex.exp (Complex.I * bilinDot q (toComplexVec (x - y)))‖ ≤ Real.exp (8 * |δ|) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have hre : (Complex.I * bilinDot q (toComplexVec (x - y))).re =
      ∑ μ, -((q μ).im * (x μ - y μ)) := by
    simp [bilinDot, toComplexVec, Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum,
      Finset.sum_neg_distrib]
  have hterm : ∀ μ : Fin 4, -((q μ).im * (x μ - y μ)) ≤ 2 * |δ| := fun μ => by
    have him : |(q μ).im| ≤ |δ| :=
      ((Complex.abs_im_le_norm (q μ)).trans (hq μ)).trans (le_abs_self δ)
    have hdiff : |x μ - y μ| ≤ 2 := (hxy μ).trans (by linarith)
    calc -((q μ).im * (x μ - y μ)) ≤ |(q μ).im * (x μ - y μ)| := neg_le_abs _
      _ = |(q μ).im| * |x μ - y μ| := abs_mul _ _
      _ ≤ |δ| * 2 := mul_le_mul him hdiff (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |δ| := mul_comm _ _
  rw [hre]
  calc ∑ μ, -((q μ).im * (x μ - y μ)) ≤ ∑ _μ : Fin 4, 2 * |δ| :=
        Finset.sum_le_sum fun μ _ => hterm μ
    _ = 8 * |δ| := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
theorem exp_phase_sub (q : Fin 4 → ℂ) (x y : InfiniteLattice.AmbientSpace) :
    Complex.exp (Complex.I * bilinDot q (toComplexVec (x - y))) =
      Complex.exp (-(Complex.I * bilinDot q (toComplexVec y))) *
        Complex.exp (Complex.I * bilinDot q (toComplexVec x)) := by
  rw [← Complex.exp_add]
  congr 1
  have hsub : bilinDot q (toComplexVec (x - y)) =
      bilinDot q (toComplexVec x) - bilinDot q (toComplexVec y) := by
    simp only [bilinDot, toComplexVec, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Pi.sub_apply, Complex.ofReal_sub]
    ring
  rw [hsub]
  ring
theorem phaseField_eq_smul_blochWave (F : PeriodicData) (q : Fin 4 → ℂ) (ε : F.UnitQuot → ℂ)
    (y : InfiniteLattice.AmbientSpace) :
    phaseField F q ε y =
      Complex.exp (-(Complex.I * bilinDot q (toComplexVec y))) • blochWave F q ε := by apply _root_.YangMills.Construction.PeriodicOperators.BoundedExpansionJets.phaseField_eq_smul_blochWave <;> assumption
theorem ofPauliCoeffs_phaseField (L k : ℕ) (q : Fin 4 → ℂ)
    (a : (colourEdges L k 0).UnitQuot → ℂ) (y : InfiniteLattice.AmbientSpace)
    (b : PeriodicOperators.PosEdge L k 0) :
    ofPauliCoeffs (phaseField (remainderIndex L k) q a y) b =
      Complex.exp (Complex.I * bilinDot q (toComplexVec (b.1.initial - y))) •
        edgeFormOf L k a b := by
  simp only [edgeFormOf, ofPauliCoeffs, Finset.smul_sum, smul_smul]
  rfl
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
open Classical in
theorem ofCoeffs_mem_traceless (L k : ℕ) (c : (edgePauliCoordinates L k 0).Index → ℂ)
    (β : Edge L k 0) : (edgePauliCoordinates L k 0).ofCoeffs c β ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.ofCoeffs_mem_traceless <;> assumption
theorem scaledEdgeCoboundary_ofCoeffs_blochWave (L k : ℕ) (q : Fin 4 → ℂ)
    (b : (colourEdges L k 0).UnitQuot → ℂ)
    (F : (colourFaces L k 0).UnitQuot → ℂ)
    (hmap : (edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (Face L k 0))
        scaledEdgeCoboundary (blochWave (colourEdges L k 0) q b) =
      blochWave (colourFaces L k 0) q F) (P : Face L k 0) :
    scaledEdgeCoboundary (L := L) (k := k) (j := 0)
        ((edgePauliCoordinates L k 0).ofCoeffs (blochWave (colourEdges L k 0) q b)) P =
      Complex.exp (Complex.I * bilinDot q (toComplexVec P.corner)) • faceFunctionOf L k F P := by
  have hW := ofCoeffs_mem_traceless L k (blochWave (colourEdges L k 0) q b)
  set W := (edgePauliCoordinates L k 0).ofCoeffs (blochWave (colourEdges L k 0) q b) with hWdef
  have hmem : scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P ∈ ComplexMatrix2.traceless := by
    have hcob : edgeCoboundary W P ∈ ComplexMatrix2.traceless :=
      Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ (hW _) (hW _)) (hW _)) (hW _)
    have htr : Matrix.trace (edgeCoboundary W P) = 0 := hcob
    show Matrix.trace ((meshAt L k 0)⁻¹ • edgeCoboundary W P) = 0
    rw [Matrix.trace_smul, htr, smul_zero]
  have hcoeff : ∀ a, pauliCoeff a (scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P) =
      blochWave (colourFaces L k 0) q F (a, P) := fun a => congrFun hmap (a, P)
  calc scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P
      = ∑ a, pauliCoeff a (scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P) •
          ComplexMatrix2.pauliFamily a := (sum_pauliCoeff_smul hmem).symm
    _ = ∑ a, blochWave (colourFaces L k 0) q F (a, P) • ComplexMatrix2.pauliFamily a := by
      simp only [hcoeff]
    _ = Complex.exp (Complex.I * bilinDot q (toComplexVec P.corner)) • faceFunctionOf L k F P := by
      simp only [faceFunctionOf, ofPauliCoeffs, Finset.smul_sum, smul_smul]
      rfl
open Classical in
theorem extendOddly_smul {a : ℝ} (c : ℂ) (g : Fin 3 × PositiveEdge a → ℂ) :
    (extendOddly fun b =>
        if h : b.IsPositivelyOriented then ofPauliCoeffs (fun ι => c * g ι) ⟨b, h⟩ else 0) =
      c • extendOddly fun b =>
        if h : b.IsPositivelyOriented then ofPauliCoeffs g ⟨b, h⟩ else 0 := by
  have hcoeffs : ∀ b', ofPauliCoeffs (fun ι => c * g ι) b' = c • ofPauliCoeffs g b' := fun b' => by
    simp only [ofPauliCoeffs, Finset.smul_sum, smul_smul]
  funext β
  simp only [extendOddly, Pi.smul_apply]
  by_cases h : β.IsPositivelyOriented
  · rw [if_pos h, if_pos h, dif_pos h, dif_pos h, hcoeffs]
  · rw [if_neg h, if_neg h]
    by_cases hr : β.opposite.IsPositivelyOriented
    · rw [dif_pos hr, dif_pos hr, hcoeffs, smul_neg]
    · rw [dif_neg hr, dif_neg hr, smul_neg, smul_zero]
theorem ofCoeffs_smul (L k : ℕ) (c : ℂ) (g : (edgePauliCoordinates L k 0).Index → ℂ) :
    (edgePauliCoordinates L k 0).ofCoeffs (c • g) = c • (edgePauliCoordinates L k 0).ofCoeffs g :=
  extendOddly_smul c g
theorem scaledEdgeCoboundary_smul (L k : ℕ) (c : ℂ) (W : Edge L k 0 → ComplexMatrix2)
    (P : Face L k 0) :
    scaledEdgeCoboundary (L := L) (k := k) (j := 0) (c • W) P =
      c • scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P := by
  simp only [scaledEdgeCoboundary, edgeCoboundary, Pi.smul_apply, smul_add, smul_sub]
  simp only [smul_comm c]
theorem waveAmplitude_blochWave (I : PeriodicData) (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) :
    waveAmplitude I κ (blochWave I κ φ) = φ := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.waveAmplitude_blochWave <;> assumption
theorem symbolHom_eq_applyKernel (I I' : PeriodicData) [Finite I.UnitQuot]
    (T : I'.Carrier → I.Carrier → ℂ) (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) :
    symbolHom I I' T κ φ = applyKernel (quotSymbol I I' T κ) φ :=
  linearMapOfEntries_eq_applyKernel _ _
theorem mapOnCoeffs_blochWave (hFO : FreeOperators.FreeOperatorsArePeriodic)
    (hS : SymbolCalculus.Claim) (hSym : Symbols.Claim) (hId : IdKernelFacts.Claim)
    {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hB : IsPeriodic (colourEdges L k 0))
    (hP : IsPeriodic (colourFaces L k 0))
    (q : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ) :
    (edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (Face L k 0))
        scaledEdgeCoboundary (blochWave (colourEdges L k 0) q b) =
      blochWave (colourFaces L k 0) q (edgeCoboundarySymbol L k q b) := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.coboundary_blochWave <;> assumption
theorem claim_holds (hB : BackgroundProperties.BackgroundPropertiesHold)
    (hR : ResponseProperties.AllProperties)
    (hFO : FreeOperators.FreeOperatorsArePeriodic) (hS : SymbolCalculus.Claim)
    (hSym : Symbols.Claim) (hId : IdKernelFacts.Claim)
    (hO : ScaledOperatorFunctions.ScaledOperatorFunctionsClaim) : Claim := by
  intro L hL
  refine ⟨Real.exp (8 * |stripHalfWidth|) * |ResponseProperties.responseConstant|,
    by positivity, fun k hk q hq μ y => ?_⟩
  have hat := ((hB L hL k hk).on_polydisc q hq μ μ).1
  have hsum := hat.le_bound _ hR.2.2.1
  have hα0 : 0 ≤ supOfOperatorNorms (edgeFormOf L k (responseAmplitude L k q μ)) :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  have hf0 : 0 ≤ supOfOperatorNorms (faceFunctionOf L k (responseCurvature L k q μ)) :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  have hC := le_abs_self (ResponseProperties.responseConstant)
  have hα : ∀ b, ‖edgeFormOf L k (responseAmplitude L k q μ) b‖ ≤
      |ResponseProperties.responseConstant| := fun b =>
    (le_ciSup hat.amplitude_bddAbove b).trans (by
      show supOfOperatorNorms (edgeFormOf L k (responseAmplitude L k q μ)) ≤ _
      linarith)
  have hf : ∀ P, ‖faceFunctionOf L k (responseCurvature L k q μ) P‖ ≤
      |ResponseProperties.responseConstant| := fun P =>
    (le_ciSup hat.curvature_bddAbove P).trans (by
      show supOfOperatorNorms (faceFunctionOf L k (responseCurvature L k q μ)) ≤ _
      linarith)
  have hη := finestMesh_le_one (k := k) hL
  have hexp : (0 : ℝ) ≤ Real.exp (8 * |stripHalfWidth|) := (Real.exp_pos _).le
  refine ⟨fun b hb => ?_, fun P hP => ?_⟩
  · rw [ofPauliCoeffs_phaseField]
    show ‖_ • _‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul (norm_exp_phase_le hη hq hb) (hα b) (norm_nonneg _) hexp
  · obtain ⟨_, pB, pP, _, _⟩ := (hO.1 L hL k hk).1.periodic
    have hcurv : (edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (Face L k 0))
        scaledEdgeCoboundary
          (blochWave (colourEdges L k 0) q (responseAmplitude L k q μ)) =
        blochWave (colourFaces L k 0) q (responseCurvature L k q μ) := by
      rw [responseCurvature, mapOnCoeffs_blochWave hFO hS hSym hId hL hk pB pP,
        waveAmplitude_blochWave]
    have hface : scaledEdgeCoboundary (L := L) (k := k) (j := 0)
        ((edgePauliCoordinates L k 0).ofCoeffs
          (phaseField (remainderIndex L k) q (responseAmplitude L k q μ) y)) P =
        Complex.exp (Complex.I * bilinDot q (toComplexVec (P.corner - y))) •
          faceFunctionOf L k (responseCurvature L k q μ) P := by
      rw [phaseField_eq_smul_blochWave]
      erw [ofCoeffs_smul]
      refine (scaledEdgeCoboundary_smul L k _ _ P).trans ?_
      refine (congrArg _ (scaledEdgeCoboundary_ofCoeffs_blochWave L k q _ _ hcurv P)).trans ?_
      rw [smul_smul, exp_phase_sub]
    rw [hface]
    show ‖_ • _‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul (norm_exp_phase_le hη hq hP) (hf P) (norm_nonneg _) hexp
end YangMills.Construction.Tower.FullSpace.BackgroundsBoundedNearPoint
end
