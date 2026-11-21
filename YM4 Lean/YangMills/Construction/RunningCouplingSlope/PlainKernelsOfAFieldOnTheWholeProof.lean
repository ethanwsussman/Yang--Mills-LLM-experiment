import YangMills.Construction.RunningCouplingSlope.PlainIteratesOfAFieldOnTheWholeProof
import YangMills.Construction.PeriodicOperators.MultiplesOfLocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.ProductOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.SumOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.TransposeOfALocalOperatorFunction
import YangMills.Construction.RunningCouplingSlope.PlainKernelsOfAFieldOnTheWhole
import YangMills.Construction.RunningCouplingSlope.PlainStepKernelsOfAFieldOnTheWhole
import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.FreeOperatorsAreRealOfFiniteRangeAndTrivialOnTheColourProof
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
namespace MeanKernels
open Tower Tower.FullSpace PeriodicOperators
section KernelEntries
variable {N N' : Type}
private theorem kernelOfMap_eq {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) : kernelOfMap M = T := by apply _root_.YangMills.Construction.Tower.FullSpace.RescaledTrivialRelationsProof.kernelOfMap_eq <;> assumption
private theorem im_tsum_eq_zero {ι : Type} {g : ι → ℂ} (h : ∀ i, (g i).im = 0) :
    (∑' i, g i).im = 0 := by apply _root_.YangMills.Construction.Tower.FreeOperatorsRealLocal.im_tsum_eq_zero <;> assumption
private theorem im_compKernel_eq_zero {J J' J'' : Type} {T : J' → J → ℂ} {S : J → J'' → ℂ}
    (hT : ∀ a b, (T a b).im = 0) (hS : ∀ a b, (S a b).im = 0) (a : J') (b : J'') :
    (compKernel T S a b).im = 0 :=
  im_tsum_eq_zero fun i => by simp [Complex.mul_im, hT, hS]
end KernelEntries
section LocalFunctions
variable {F I I' : PeriodicData}
private theorem supBelow_mono {ζ : F.Carrier → ℂ} {ρ ρ' : ℝ} (h : IsSupBelow F ζ ρ')
    (hle : ρ' ≤ ρ) : IsSupBelow F ζ ρ := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.isSupBelow_mono <;> assumption
private theorem supBelow_shift {ζ : F.Carrier → ℂ} {ρ : ℝ} (h : IsSupBelow F ζ ρ)
    (n : Fin 4 → ℤ) : IsSupBelow F (shiftField F n ζ) ρ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.isSupBelow_shiftField <;> assumption
private theorem isLocalWith_congr {T T' : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    {ρ R : ℝ} (hT : IsLocalWith F I I' T ρ R) (hc : ∀ ζ, IsSupBelow F ζ ρ → T' ζ = T ζ) :
    IsLocalWith F I I' T' ρ R where
  radius_pos := hT.radius_pos
  vanish_far := fun ζ hζ ι' ι hn => by
    rw [hc ζ hζ]
    exact hT.vanish_far ζ hζ ι' ι hn
  holo_entry := fun ι' ι => by
    obtain ⟨l, e, h, hh, he⟩ := hT.holo_entry ι' ι
    exact ⟨l, e, h, hh, fun ζ hζ => by rw [hc ζ hζ]; exact he ζ hζ⟩
  shift_covariant := fun ζ hζ n ι' ι => by
    rw [hc _ (supBelow_shift hζ n), hc ζ hζ]
    exact hT.shift_covariant ζ hζ n ι' ι
private theorem isLocalOpFun_smul (hMult : PeriodicOperators.OpFunMultiples.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {S : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} (hS : IsLocalOpFun F I I' S) (c : ℂ) :
    IsLocalOpFun F I I' (fun ζ => c • S ζ) :=
  (hMult F hF 1 0 one_pos (fun μ => by simp) 0 0 I I' hI hI' S hS c).1
private theorem isLocalOpFun_congr (hNumbers : PeriodicOperators.ParameterIndependence.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T T' : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} (hT : IsLocalOpFun F I I' T)
    {ρ : ℝ} (hρ : 0 < ρ) (hc : ∀ ζ, IsSupBelow F ζ ρ → T' ζ = T ζ) :
    IsLocalOpFun F I I' T' := by
  obtain ⟨ρ₁, R, hM⟩ := hT
  refine ⟨min ρ₁ ρ, R, isLocalWith_congr
    ((hNumbers _ _ _ hF hI hI' _ _ _ _ _ hM hM).1.1 _ _ (lt_min hM.radius_pos hρ)
      (min_le_left _ _) le_rfl) fun ζ hζ => hc ζ (supBelow_mono hζ (min_le_right _ _))⟩
end LocalFunctions
section PauliCoordinates
private theorem pauliFamily_mem (a : Fin 3) :
    Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private theorem sum_pauliCoeff_smul {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • Matrices.ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem real_smul_eq_complex_smul (x : ℝ) (X : Matrices.ComplexMatrix2) :
    x • X = (x : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
private theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
private theorem ofPauliCoeffs_toPauliCoeffs {σ : Type} {l : σ → Matrices.ComplexMatrix2}
    (hl : ∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) : ofPauliCoeffs (toPauliCoeffs l) = l := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofPauliCoeffs_toPauliCoeffs <;> assumption
end PauliCoordinates
section EdgeForms
variable {L k i : ℕ}
private theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
private theorem positive_or_opposite_positive {a : ℝ} (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
private def edgeForm (ζ : (colourEdges L k i).Carrier → ℂ) :
    FullSpace.Edge L k i → Matrices.ComplexMatrix2 :=
  (FullSpace.edgePauliCoordinates L k i).ofCoeffs ζ
private theorem edgeForm_of_pos (ζ : (colourEdges L k i).Carrier → ℂ) {b : FullSpace.Edge L k i}
    (h : b.IsPositivelyOriented) :
    edgeForm ζ b = ∑ a, ζ (a, ⟨b, h⟩) • Matrices.ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.DeltaSharedProofs.p500947 <;> assumption
private theorem edgeForm_of_not_pos (ζ : (colourEdges L k i).Carrier → ℂ)
    {b : FullSpace.Edge L k i} (h : ¬ b.IsPositivelyOriented) :
    edgeForm ζ b = -edgeForm ζ b.opposite := by apply _root_.YangMills.DeltaSharedProofs.p500478 <;> assumption
private theorem not_positive_opposite {a : ℝ} (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
private theorem edgeForm_mem (hL : Conventions.IsAdmissibleBlockingFactor L)
    (ζ : (colourEdges L k i).Carrier → ℂ) :
    edgeForm ζ ∈ FullSpace.complexEdgeForms (meshAt L k i) := by apply _root_.YangMills.DeltaSharedProofs.p502175 <;> assumption
private def edgeCoeffs (B : FullSpace.Edge L k i → Matrices.ComplexMatrix2) :
    (colourEdges L k i).Carrier → ℂ :=
  fun ι => pauliCoeff ι.1 (B ι.2.1)
private theorem edgeForm_edgeCoeffs {B : FullSpace.Edge L k i → Matrices.ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k i)) : edgeForm (edgeCoeffs B) = B := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofCoeffs_coeffs <;> assumption
end EdgeForms
section Compositions
variable {L K : ℕ}
private def compQ (L K : ℕ) (U : FullSpace.Edge L K 0 → Matrices.ComplexMatrix2) : (m : ℕ) →
    KernelMatrix (Fin 3 × FullSpace.PositiveEdge (meshAt L K 0))
      (Fin 3 × FullSpace.PositiveEdge (meshAt L K (m + 1)))
  | 0 => meanStepKernel L K U 0
  | m + 1 => compKernel (meanStepKernel L K U (m + 1)) (compQ L K U m)
private def compR (L K : ℕ) (U : FullSpace.Edge L K 0 → Matrices.ComplexMatrix2) : (m : ℕ) →
    KernelMatrix (Fin 3 × FullSpace.Vertex L K 0) (Fin 3 × FullSpace.Vertex L K (m + 1))
  | 0 => meanVertexStepKernel L K U 0
  | m + 1 => compKernel (meanVertexStepKernel L K U (m + 1)) (compR L K U m)
private def qCoeffMap (U : FullSpace.Edge L K 0 → Matrices.ComplexMatrix2) (j : ℕ) :
    ((colourEdges L K 0).Carrier → ℂ) → (colourEdges L K j).Carrier → ℂ :=
  PauliComponentsOfSymmetricKernel.mapOnCoeffs (FullSpace.edgePauliCoordinates L K 0) (FullSpace.edgePauliCoordinates L K j)
    fun B => ((L : ℝ) ^ j)⁻¹ • meanCovariant U j B
private def rCoeffMap (U : FullSpace.Edge L K 0 → Matrices.ComplexMatrix2) (j : ℕ) :
    ((colourVertices L K 0).Carrier → ℂ) → (colourVertices L K j).Carrier → ℂ :=
  PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L K 0))
    (vertexCoordinate (FullSpace.Vertex L K j)) (meanCubeAverage U j)
private theorem compQ_represents (hP : PeriodicOperators.RowFiniteKernels.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {U : FullSpace.Edge L K 0 → Matrices.ComplexMatrix2}
    (H : ∀ j, j < K → StepKernelConditions L K j U) : ∀ m, m < K →
      Represents (compQ L K U m) (qCoeffMap U (m + 1)) ∧ RowFinite (compQ L K U m) ∧
      ∀ B ∈ FullSpace.complexEdgeForms (meshAt L K 0),
        meanCovariant U (m + 1) B ∈ FullSpace.complexEdgeForms (meshAt L K (m + 1)) := by
  have hLne : (L : ℝ) ≠ 0 := (Nat.cast_pos.2 (by have := hL.2; omega)).ne'
  intro m
  induction m with
  | zero =>
    intro hm
    refine ⟨?_, (H 0 hm).step_rowFinite, fun B hB => (H 0 hm).maps_complexForms B hB⟩
    have e : qCoeffMap U 1 = PauliComponentsOfSymmetricKernel.mapOnCoeffs (FullSpace.edgePauliCoordinates L K 0)
        (FullSpace.edgePauliCoordinates L K (0 + 1))
        (fun B => (L : ℝ)⁻¹ • meanCovariantStep (meanIterate U 0) B) := by
      unfold qCoeffMap
      congr 1
      funext B
      rw [pow_one]
      rfl
    rw [e]
    exact (H 0 hm).step_represents
  | succ m ih =>
    intro hm
    obtain ⟨h₁, h₂, h₃⟩ := ih (by omega)
    have S := H (m + 1) hm
    obtain ⟨-, hprod⟩ := hP.1 _ _ (compQ L K U m) h₂
    obtain ⟨-, hrows, hact⟩ := hprod _ (meanStepKernel L K U (m + 1)) S.step_rowFinite
    refine ⟨fun g => ⟨(hact g).1, ?_⟩, hrows, fun B hB => S.maps_complexForms _ (h₃ B hB)⟩
    have e1 : applyKernel (compQ L K U (m + 1)) g =
        applyKernel (meanStepKernel L K U (m + 1)) (applyKernel (compQ L K U m) g) :=
      (hact g).2.2
    rw [e1, (h₁ g).2]
    refine Eq.trans (S.step_represents (qCoeffMap U (m + 1) g)).2 ?_
    funext ι'
    set Y := meanCovariant U (m + 1) (edgeForm g) with hY
    have hYf : Y ∈ FullSpace.complexEdgeForms (meshAt L K (m + 1)) := h₃ _ (edgeForm_mem hL g)
    set r : ℝ := ((L : ℝ) ^ (m + 1))⁻¹ with hr
    have hXf : r • Y ∈ FullSpace.complexEdgeForms (meshAt L K (m + 1)) := by
      have e : r • Y = (r : ℂ) • Y := by
        funext b
        exact real_smul_eq_complex_smul r (Y b)
      rw [e]
      exact Submodule.smul_mem _ _ hYf
    have hq : edgeForm (qCoeffMap U (m + 1) g) = r • Y := edgeForm_edgeCoeffs hXf
    show pauliCoeff ι'.1 (((L : ℝ)⁻¹ • meanCovariantStep (meanIterate U (m + 1))
        (edgeForm (qCoeffMap U (m + 1) g))) ι'.2.1) =
      pauliCoeff ι'.1 ((((L : ℝ) ^ (m + 1 + 1))⁻¹ •
        meanCovariantStep (meanIterate U (m + 1)) Y) ι'.2.1)
    rw [hq]
    have e2 : r • Y = (r : ℂ) • Y := by
      funext b
      exact real_smul_eq_complex_smul r (Y b)
    simp only [Pi.smul_apply]
    rw [e2, S.map_smul _ hYf _ _ ι'.2.2, ← real_smul_eq_complex_smul, smul_smul]
    congr 2
    rw [hr, pow_succ (L : ℝ) (m + 1), mul_inv]
    ring
private theorem cubeAverage_mem {U : FullSpace.Edge L K 0 → Matrices.ComplexMatrix2}
    (H : ∀ j, j < K → StepKernelConditions L K j U)
    {l : FullSpace.Vertex L K 0 → Matrices.ComplexMatrix2}
    (hl : ∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) :
    ∀ j, j ≤ K → ∀ x, meanCubeAverage U j l x ∈ Matrices.ComplexMatrix2.traceless := by
  intro j
  induction j with
  | zero => exact fun _ => hl
  | succ j ih => exact fun hj => (H j (by omega)).maps_traceless _ (ih (by omega))
private theorem compR_represents (hP : PeriodicOperators.RowFiniteKernels.Claim)
    {U : FullSpace.Edge L K 0 → Matrices.ComplexMatrix2}
    (H : ∀ j, j < K → StepKernelConditions L K j U) : ∀ m, m < K →
      Represents (compR L K U m) (rCoeffMap U (m + 1)) ∧ RowFinite (compR L K U m) := by
  intro m
  induction m with
  | zero =>
    intro hm
    exact ⟨(H 0 hm).vertex_represents, (H 0 hm).vertex_rowFinite⟩
  | succ m ih =>
    intro hm
    obtain ⟨h₁, h₂⟩ := ih (by omega)
    have S := H (m + 1) hm
    obtain ⟨-, hprod⟩ := hP.1 _ _ (compR L K U m) h₂
    obtain ⟨-, hrows, hact⟩ := hprod _ (meanVertexStepKernel L K U (m + 1)) S.vertex_rowFinite
    refine ⟨fun g => ⟨(hact g).1, ?_⟩, hrows⟩
    have e1 : applyKernel (compR L K U (m + 1)) g =
        applyKernel (meanVertexStepKernel L K U (m + 1)) (applyKernel (compR L K U m) g) :=
      (hact g).2.2
    rw [e1, (h₁ g).2]
    refine Eq.trans (S.vertex_represents (rCoeffMap U (m + 1) g)).2 ?_
    have hl : ∀ x, meanCubeAverage U (m + 1) (ofPauliCoeffs g) x ∈
        Matrices.ComplexMatrix2.traceless :=
      cubeAverage_mem H (ofPauliCoeffs_mem g) (m + 1) (by omega)
    have e2 : ofPauliCoeffs (rCoeffMap U (m + 1) g) =
        meanCubeAverage U (m + 1) (ofPauliCoeffs g) := ofPauliCoeffs_toPauliCoeffs hl
    show toPauliCoeffs (FullSpace.adjointCubeAverage (meanIterate U (m + 1))
      (ofPauliCoeffs (rCoeffMap U (m + 1) g))) = _
    rw [e2]
    rfl
private theorem finestMesh_eq (hL : Conventions.IsAdmissibleBlockingFactor L) :
    finestMesh L K = ((L : ℝ) ^ K)⁻¹ := by
  simp [finestMesh, meshAt, zpow_neg]
end Compositions
section RealEntries
variable {L K : ℕ}
private theorem compQ_im {U : FullSpace.Edge L K 0 → Matrices.ComplexMatrix2}
    (H : ∀ j, j < K → ∀ ι' ι, (meanStepKernel L K U j ι' ι).im = 0) :
    ∀ m, m < K → ∀ ι' ι, (compQ L K U m ι' ι).im = 0 := by
  intro m
  induction m with
  | zero => exact fun hm => H 0 hm
  | succ m ih =>
    intro hm
    exact im_compKernel_eq_zero (H (m + 1) hm) (ih (by omega))
private theorem compR_im {U : FullSpace.Edge L K 0 → Matrices.ComplexMatrix2}
    (H : ∀ j, j < K → ∀ ι' ι, (meanVertexStepKernel L K U j ι' ι).im = 0) :
    ∀ m, m < K → ∀ ι' ι, (compR L K U m ι' ι).im = 0 := by
  intro m
  induction m with
  | zero => exact fun hm => H 0 hm
  | succ m ih =>
    intro hm
    exact im_compKernel_eq_zero (H (m + 1) hm) (ih (by omega))
private theorem noiseCovariance_im {U : FullSpace.Edge L K 0 → Matrices.ComplexMatrix2} (a : ℝ)
    (H : ∀ j, j < K → ∀ ι' ι, (meanStepKernel L K U j ι' ι).im = 0)
    (H₂ : ∀ j, j < K → ∀ ι' ι, (invRadiusDiag U j ι' ι).im = 0) :
    ∀ j, j ≤ K → ∀ ι' ι, (noiseCovariance a L K U j ι' ι).im = 0 := by
  intro j
  induction j with
  | zero => exact fun _ ι' ι => rfl
  | succ j ih =>
    intro hj ι' ι
    have hj' : j < K := by omega
    have ht : ∀ x y, (meshTranspose (meshAt L K j) (meshAt L K (j + 1))
        (meanStepKernel L K U j) x y).im = 0 := fun x y => by
      simp only [meshTranspose, PeriodicOperators.wTranspose, Complex.mul_im,
        Complex.ofReal_im, Complex.ofReal_re, H j hj' y x]
      simp
    have hp := im_compKernel_eq_zero (im_compKernel_eq_zero (H j hj') (ih hj'.le)) ht ι' ι
    have e : noiseCovariance a L K U (j + 1) ι' ι =
        ((a⁻¹ : ℝ) : ℂ) * invRadiusDiag U j ι' ι +
        (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ) *
          compKernel (compKernel (meanStepKernel L K U j) (noiseCovariance a L K U j))
            (meshTranspose (meshAt L K j) (meshAt L K (j + 1))
              (meanStepKernel L K U j)) ι' ι := rfl
    rw [e, Complex.add_im, Complex.mul_im, Complex.mul_im, H₂ j hj' ι' ι, hp, Complex.ofReal_im,
      Complex.ofReal_im]
    simp
end RealEntries
end MeanKernels
open MeanKernels Tower Tower.FullSpace PeriodicOperators in
theorem meanKernelsAreLocal_holds (hK : MeanStepKernelsAreLocal)
    (hP : PeriodicOperators.RowFiniteKernels.Claim)
    (hProd : PeriodicOperators.OpFunComp.LocalClosed)
    (hSum : PeriodicOperators.OpFunAdd.LocalClosed)
    (hTrn : PeriodicOperators.OpFunTransposeLocal.Claim)
    (hMult : PeriodicOperators.OpFunMultiples.Claim)
    (hNumbers : PeriodicOperators.ParameterIndependence.Claim)
    (hSets : PeriodicOperators.TowerIndexSets.Claim) : MeanKernelsAreLocal := by
  intro L hL k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hloc, ρ, hρ, H⟩ := hK L hL (m + 1) hk
  have hb : ∀ j, j ≤ m + 1 → IsPeriodic (colourEdges L (m + 1) j) := fun j hj =>
    (hSets L hL (m + 1) j hj).2.1
  have hs : ∀ j, j ≤ m + 1 → IsPeriodic (colourVertices L (m + 1) j) := fun j hj =>
    (hSets L hL (m + 1) j hj).1
  have hF := hb 0 (Nat.zero_le _)
  have hQ : ∀ i, i ≤ m → IsLocalOpFun (colourEdges L (m + 1) 0)
      (colourEdges L (m + 1) 0) (colourEdges L (m + 1) (i + 1))
      (fun f => compQ L (m + 1) (FullSpace.BackgroundJets.gaugeFieldOfForm L (m + 1) f) i) := by
    intro i
    induction i with
    | zero => exact fun _ => (hloc 0 (by omega)).1
    | succ i ih =>
      intro hi
      exact hProd _ (colourEdges L (m + 1) (i + 1)) (colourEdges L (m + 1) (i + 1 + 1))
        (colourEdges L (m + 1) 0) hF (hb _ (by omega)) (hb _ (by omega)) hF _ _
        (hloc (i + 1) (by omega)).1 (ih (by omega))
  have hR : ∀ i, i ≤ m → IsLocalOpFun (colourEdges L (m + 1) 0)
      (colourVertices L (m + 1) 0) (colourVertices L (m + 1) (i + 1))
      (fun f => compR L (m + 1) (FullSpace.BackgroundJets.gaugeFieldOfForm L (m + 1) f) i) := by
    intro i
    induction i with
    | zero => exact fun _ => (hloc 0 (by omega)).2.2
    | succ i ih =>
      intro hi
      exact hProd _ (colourVertices L (m + 1) (i + 1)) (colourVertices L (m + 1) (i + 1 + 1))
        (colourVertices L (m + 1) 0) hF (hs _ (by omega)) (hs _ (by omega))
        (hs _ (Nat.zero_le _)) _ _ (hloc (i + 1) (by omega)).2.2 (ih (by omega))
  have hN : ∀ (a : ℝ) (j : ℕ), j ≤ m + 1 → IsLocalOpFun (colourEdges L (m + 1) 0)
      (colourEdges L (m + 1) j) (colourEdges L (m + 1) j)
      (fun f => noiseCovariance a L (m + 1)
        (FullSpace.BackgroundJets.gaugeFieldOfForm L (m + 1) f) j) := by
    intro a j
    induction j with
    | zero =>
      intro _
      have h₀ := (hloc 0 (by omega)).1
      have h₁ := hTrn _ _ _ hF hF (hb 1 (by omega)) _ h₀
      have h₂ := hProd _ (colourEdges L (m + 1) (0 + 1)) (colourEdges L (m + 1) 0)
        (colourEdges L (m + 1) 0) hF (hb 1 (by omega)) hF hF _ _ h₁ h₀
      have h₃ := isLocalOpFun_smul hMult hF hF hF h₂ 0
      refine (congrArg _ (funext fun f => ?_)).mp h₃
      rw [zero_smul]
      rfl
    | succ j ih =>
      intro hj
      have hj' : j < m + 1 := by omega
      have hbj := hb j hj'.le
      have hbj' := hb (j + 1) hj
      have hS := (hloc j hj').1
      have hT2 := (hloc j hj').2.1
      have hNj := ih hj'.le
      have P₁ := hProd _ (colourEdges L (m + 1) j) (colourEdges L (m + 1) (j + 1))
        (colourEdges L (m + 1) j) hF hbj hbj' hbj _ _ hS hNj
      have Tt := hTrn _ _ _ hF hbj hbj' _ hS
      have P₂ := hProd _ (colourEdges L (m + 1) j) (colourEdges L (m + 1) (j + 1))
        (colourEdges L (m + 1) (j + 1)) hF hbj hbj' hbj' _ _ P₁ Tt
      exact hSum _ _ _ hF hbj' hbj' _ _
        (isLocalOpFun_smul hMult hF hbj' hbj' hT2 ((a⁻¹ : ℝ) : ℂ))
        (isLocalOpFun_smul hMult hF hbj' hbj' P₂ (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ))
  have hU : ∀ f : (colourEdges L (m + 1) 0).Carrier → ℂ,
      IsSupBelow (colourEdges L (m + 1) 0) f ρ → ∀ j, j < m + 1 →
        StepKernelConditions L (m + 1) j (FullSpace.BackgroundJets.gaugeFieldOfForm L (m + 1) f) :=
    fun f hf j hj => (H f hf j hj).1
  have eQ : ∀ f : (colourEdges L (m + 1) 0).Carrier → ℂ,
      IsSupBelow (colourEdges L (m + 1) 0) f ρ →
      meanKernelQ L (m + 1) (FullSpace.BackgroundJets.gaugeFieldOfForm L (m + 1) f) =
        compQ L (m + 1) (FullSpace.BackgroundJets.gaugeFieldOfForm L (m + 1) f) m := by
    intro f hf
    have h := (compQ_represents hP hL (hU f hf) m (by omega)).1
    unfold meanKernelQ PauliComponentsOfSymmetricKernel.kernel
    rw [finestMesh_eq hL]
    exact kernelOfMap_eq h
  have eR : ∀ f : (colourEdges L (m + 1) 0).Carrier → ℂ,
      IsSupBelow (colourEdges L (m + 1) 0) f ρ →
      meanKernelR L (m + 1) (FullSpace.BackgroundJets.gaugeFieldOfForm L (m + 1) f) =
        compR L (m + 1) (FullSpace.BackgroundJets.gaugeFieldOfForm L (m + 1) f) m :=
    fun f hf => kernelOfMap_eq (compR_represents hP (hU f hf) m (by omega)).1
  refine ⟨isLocalOpFun_congr hNumbers hF hF (hb _ le_rfl) (hQ m le_rfl) hρ eQ,
    isLocalOpFun_congr hNumbers hF (hs _ (Nat.zero_le _)) (hs _ le_rfl) (hR m le_rfl) hρ eR,
    fun a => hN a _ le_rfl, ρ, hρ, fun f hr hf => ?_⟩
  have H₁ := fun j hj => ((H f hf j hj).2 hr).1
  have H₂ := fun j hj => ((H f hf j hj).2 hr).2.1
  have H₃ := fun j hj => ((H f hf j hj).2 hr).2.2
  refine ⟨fun ι' ι => ?_, fun ι' ι => ?_,
    fun a ι' ι => noiseCovariance_im a H₁ H₂ _ le_rfl ι' ι⟩
  · rw [eQ f hf]
    exact compQ_im H₁ m (by omega) ι' ι
  · rw [eR f hf]
    exact compR_im H₃ m (by omega) ι' ι
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
