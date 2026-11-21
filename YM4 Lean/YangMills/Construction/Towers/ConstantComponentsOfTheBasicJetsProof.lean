import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperatorsProof
import YangMills.Construction.PeriodicOperators.TheNumberOfASaddleJetProof
import YangMills.Construction.Towers.BoundOfTheBondAverageJetProof
import YangMills.Construction.Towers.ConstantComponentsOfTheBasicJets
import YangMills.Construction.Towers.StepOfTheCovariantAveragesAtOneAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ZeroFieldJets
open PeriodicOperators
open BackgroundJets
open Matrices
section KernelMatrices
variable {N N' : Type}
open Classical in
theorem entry_of_represents {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ} (hT : Represents T M)
    (j : N') (i : N) : T j i = M (fun x => if x = i then 1 else 0) j := by apply _root_.YangMills.Construction.Tower.FreeOperators.kernel_eq_apply_indicator <;> assumption
theorem kernelOfMap_zero :
    kernelOfMap (fun _ _ => 0 : (N → ℂ) → N' → ℂ) = fun _ _ => 0 := by
  have hZero : Represents (fun _ _ => 0 : KernelMatrix N N') (fun _ _ => 0) := fun f =>
    ⟨fun j => by simpa [ApplySummableAt] using (summable_zero : Summable fun _ : N => (0 : ℝ)),
      by funext j; simp [applyKernel]⟩
  have hChosen : Represents (kernelOfMap (fun _ _ => 0 : (N → ℂ) → N' → ℂ)) (fun _ _ => 0) :=
    Classical.epsilon_spec (p := fun T => Represents T (fun _ _ => (0 : ℂ))) ⟨_, hZero⟩
  funext j i
  exact entry_of_represents hChosen j i
open Classical in
theorem kernelOfMap_id :
    kernelOfMap (fun f => f : (N → ℂ) → N → ℂ) = fun j i => if j = i then 1 else 0 := by
  have hDelta : Represents (fun j i => if j = i then 1 else 0 : KernelMatrix N N) (fun f => f) := by
    intro f
    refine ⟨fun j => ?_, ?_⟩
    · refine summable_of_ne_finset_zero (s := {j}) fun x hx => ?_
      have hne : j ≠ x := fun e => hx (by simp [e])
      simp [hne]
    · funext j
      unfold applyKernel
      rw [tsum_eq_single j]
      · simp
      · intro x hx
        simp [Ne.symm hx]
  have hChosen : Represents (kernelOfMap (fun f => f : (N → ℂ) → N → ℂ)) (fun f => f) :=
    Classical.epsilon_spec (p := fun T => Represents T (fun f => f)) ⟨_, hDelta⟩
  funext j i
  exact entry_of_represents hChosen j i
end KernelMatrices
section LinearMaps
variable {J J' : Type}
theorem linearMap_eq_of_entries [Finite J] {M M' : (J → ℂ) →ₗ[ℂ] (J' → ℂ)}
    (h : linearMapEntry M = linearMapEntry M') : M = M' := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMap_ext_of_entry <;> assumption
theorem linearMapOfEntries_linearMapEntry [Finite J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) :
    linearMapOfEntries (linearMapEntry M) = M :=
  linearMap_eq_of_entries
    (Classical.epsilon_spec (p := fun M' => linearMapEntry M' = linearMapEntry M) ⟨M, rfl⟩)
end LinearMaps
section FourierSymbols
theorem symbolHom_zero (I I' : PeriodicData) [Finite I.UnitQuot] (κ : Fin 4 → ℂ) :
    symbolHom I I' (fun _ _ => 0) κ = 0 := by
  have hSym : fourierSymbol I I' (fun _ _ => 0) κ = fun _ _ => 0 := by
    funext j i
    simp [fourierSymbol, symbolSummand]
  have hDesc : descendMatrix I I' 1 (fun _ _ => 0) = linearMapEntry (0 : QuotHom I I') := by
    funext c' c
    obtain ⟨j, hj⟩ : ∃ j, I'.mkQuot 1 j = c' := Quot.exists_rep c'
    obtain ⟨i, hi⟩ : ∃ i, I.mkQuot 1 i = c := Quot.exists_rep c
    have hSpec := Classical.epsilon_spec
      (p := fun z : ℂ => ∀ x' x, I'.mkQuot 1 x' = c' → I.mkQuot 1 x = c → (0 : ℂ) = z)
      ⟨0, fun _ _ _ _ => rfl⟩
    have hAt := hSpec j i hj hi
    simpa [descendMatrix, linearMapEntry] using hAt.symm
  unfold symbolHom
  rw [hSym, hDesc]
  exact linearMapOfEntries_linearMapEntry _
theorem symbolHom_idKernel (hId : IdKernelFacts.Claim) (I : PeriodicData)
    (hI : IsPeriodic I) (κ : Fin 4 → ℂ) :
    symbolHom I I (idKernel I) κ = LinearMap.id := by
  classical
  haveI : Finite I.UnitQuot := hI.finite_quot
  have hDesc : descendMatrix I I 1 (fourierSymbol I I (idKernel I) κ) = quotOne I :=
    (hId I hI).2.2.2.2.1 κ
  have hOne : quotOne I = linearMapEntry (LinearMap.id : QuotHom I I) := by
    funext c' c
    simp [quotOne, linearMapEntry, Pi.single_apply]
  unfold symbolHom
  rw [hDesc, hOne]
  exact linearMapOfEntries_linearMapEntry _
end FourierSymbols
section PauliCoordinates
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
end PauliCoordinates
section TrivialField
variable {L k : ℕ}
open Classical in
theorem ofCoeffs_zero : (edgePauliCoordinates L k 0).ofCoeffs 0 = (0 : Edge L k 0 → ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.FullSpace.EdgeSmoothingJetEstimate.ofCoeffs_zero <;> assumption
theorem expForm_zero : expForm (0 : Edge L k 0 → ComplexMatrix2) = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.EdgeSmoothingJetEstimate.expForm_zero <;> assumption
theorem gaugeFieldOfForm_zero : gaugeFieldOfForm L k 0 = 1 :=
  (congrArg expForm ofCoeffs_zero).trans expForm_zero
theorem faceVariable_one (p : Face L k 0) :
    faceVariable (1 : Edge L k 0 → ComplexMatrix2) p = 1 := by
  simp [faceVariable, linkHolonomy, faceBoundary]
theorem faceTransports_one (p : Face L k 0) (i : Fin 4) :
    faceTransports (1 : Edge L k 0 → ComplexMatrix2) p i = 1 := by
  fin_cases i <;> simp [faceTransports, faceVariable_one]
theorem conjugateBy_one (X : ComplexMatrix2) : ComplexMatrix2.conjugateBy 1 X = X := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.conjugateBy_one <;> assumption
end TrivialField
section KernelsAtIdentity
variable (L k : ℕ)
theorem rescaledOperators_D_one :
    (rescaledOperators L k (1 : Edge L k 0 → ComplexMatrix2)).D =
      scaledVertexCoboundaryKernel L k 0 := by
  have hMap : PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (Vertex L k 0)) (edgePauliCoordinates L k 0)
        (fun l => (finestMesh L k)⁻¹ • covDiff (1 : Edge L k 0 → ComplexMatrix2) l) =
      PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (Vertex L k 0)) (edgePauliCoordinates L k 0)
        scaledVertexCoboundary := by
    funext f
    have hPos : restrictToPositiveEdges ((finestMesh L k)⁻¹ •
          covDiff (1 : Edge L k 0 → ComplexMatrix2) (ofPauliCoeffs f)) =
        restrictToPositiveEdges (scaledVertexCoboundary (ofPauliCoeffs f)) := by
      funext b
      simp [restrictToPositiveEdges, covDiff, extendOddly, b.2, scaledVertexCoboundary,
        vertexCoboundary, conjugateBy_one, finestMesh]
    exact congrArg toPauliCoeffs hPos
  exact congrArg kernelOfMap hMap
theorem holonomyDefectKernel_one :
    holonomyDefectKernel L k (1 : Edge L k 0 → ComplexMatrix2) = fun _ _ => 0 := by
  have hMap : PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L k 0) (vertexCoordinate (Face L k 0))
      (holonomyDefect (1 : Edge L k 0 → ComplexMatrix2)) = fun _ _ => 0 := by
    have hVanish : ∀ (b : Edge L k 0 → ComplexMatrix2) (q : Face L k 0),
        holonomyDefect (1 : Edge L k 0 → ComplexMatrix2) b q = 0 := by
      intro b q
      simp [holonomyDefect, faceTransports_one, conjugateBy_one]
    funext f i
    exact (congrArg (pauliCoeff i.1) (hVanish _ i.2)).trans (pauliCoeff_zero i.1)
  unfold holonomyDefectKernel PauliComponentsOfSymmetricKernel.kernel
  rw [hMap]
  exact kernelOfMap_zero
theorem halfFaceTraceKernel_one :
    halfFaceTraceKernel L k (1 : Edge L k 0 → ComplexMatrix2) =
      idKernel (colourFaces L k 0) := by
  have hTrace : ∀ p : Face L k 0,
      halfFaceTrace (1 : Edge L k 0 → ComplexMatrix2) p = 1 := by
    intro p
    simp [halfFaceTrace, faceVariable_one, ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
  have hMap : PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (Face L k 0))
      (vertexCoordinate (Face L k 0))
      (halfFaceTraceMul (1 : Edge L k 0 → ComplexMatrix2)) = fun f => f := by
    funext f
    have hMul : halfFaceTraceMul (1 : Edge L k 0 → ComplexMatrix2) (ofPauliCoeffs f) =
        ofPauliCoeffs f := by
      funext p
      change halfFaceTrace (1 : Edge L k 0 → ComplexMatrix2) p • ofPauliCoeffs f p = _
      rw [hTrace p, one_smul]
    exact (congrArg toPauliCoeffs hMul).trans (toPauliCoeffs_ofPauliCoeffs f)
  unfold halfFaceTraceKernel PauliComponentsOfSymmetricKernel.kernel
  rw [hMap]
  exact kernelOfMap_id
variable {L k}
theorem curvatureKernel_one (hSymm : SymmetricKernels.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) :
    curvatureKernel (1 : Edge L k 0 → ComplexMatrix2) = fun _ _ => 0 := by
  have hLpos : (0 : ℝ) < L := by
    have hL2 := hL.2
    exact_mod_cast (by omega : 0 < L)
  have hMesh : 0 < finestMesh L k := zpow_pos hLpos _
  have hWeight : ∀ i : Fin 3 × PositiveEdge (meshAt L k 0),
      0 < meshWeight (finestMesh L k) i := fun _ => pow_pos hMesh 4
  have hForm : ∀ b b' : Edge L k 0 → ComplexMatrix2,
      curvatureBilinear (1 : Edge L k 0 → ComplexMatrix2) b b' = 0 := by
    intro b b'
    simp [curvatureBilinear, curvatureMatrix, faceVariable_one]
  have hZero : IsCurvatureKernel (1 : Edge L k 0 → ComplexMatrix2) (fun _ _ => 0) := by
    refine ⟨?_, fun f => ?_⟩
    · funext a b
      simp [IsSymmKernel, wTranspose]
    · have hPair : kernelPairing (meshWeight (finestMesh L k)) (fun _ _ => 0)
          (f : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) f = 0 := by
        simp [kernelPairing]
      exact hPair.trans (hForm _ _).symm
  have hChosen : IsCurvatureKernel (1 : Edge L k 0 → ComplexMatrix2)
      (curvatureKernel (1 : Edge L k 0 → ComplexMatrix2)) :=
    Classical.epsilon_spec (p := IsCurvatureKernel (1 : Edge L k 0 → ComplexMatrix2)) ⟨_, hZero⟩
  have hUniq := ((hSymm.1 _ _ hWeight 0).2).1
  exact hUniq.unique ⟨hChosen.1, fun f => (hChosen.2 f).trans (hForm _ _)⟩
    ⟨hZero.1, fun f => (hZero.2 f).trans (hForm _ _)⟩
end KernelsAtIdentity
section JetComponents
theorem add_neg_one_smul_self {I I' : PeriodicData} (M : QuotHom I I') :
    M + (-1 : ℂ) • M = 0 := by apply _root_.YangMills.SharedProofs.p42708 <;> assumption
variable (L k : ℕ) (p : Fin 4 → ℂ) (μPlus μMinus : Fin 4) (κ : Fin 4 → ℂ)
theorem covDerivDefectJet_f00 :
    (covDerivDefectJet L k p μPlus μMinus).f00 κ =
      symbolHom (colourVertices L k 0) (colourEdges L k 0)
          (rescaledOperators L k (gaugeFieldOfForm L k 0)).D κ +
        (-1 : ℂ) • symbolHom (colourVertices L k 0) (colourEdges L k 0)
          (scaledVertexCoboundaryKernel L k 0) κ :=
  rfl
theorem holonomyDefectJet_f00 :
    (holonomyDefectJet L k p μPlus μMinus).f00 κ =
      symbolHom (colourEdges L k 0) (colourFaces L k 0)
        (holonomyDefectKernel L k (gaugeFieldOfForm L k 0)) κ :=
  rfl
theorem halfFaceTraceJet_f00 :
    (halfFaceTraceJet L k p μPlus μMinus).f00 κ =
      symbolHom (colourFaces L k 0) (colourFaces L k 0)
        (halfFaceTraceKernel L k (gaugeFieldOfForm L k 0)) κ :=
  rfl
theorem curvatureJet_f00 :
    (curvatureJet L k p μPlus μMinus).f00 κ =
      symbolHom (colourEdges L k 0) (colourEdges L k 0)
        (curvatureKernel (gaugeFieldOfForm L k 0)) κ :=
  rfl
end JetComponents
theorem constantJetComponents_holds (hIdx : TowerIndexSets.Claim) (hId : IdKernelFacts.Claim)
    (hSymm : SymmetricKernels.Claim) : ConstantJetComponents := by
  intro L hL k _ μPlus μMinus p _ κ _
  obtain ⟨-, hE, hF⟩ := hIdx L hL k 0 (Nat.zero_le k)
  have : Finite (colourEdges L k 0).UnitQuot := hE.finite_quot
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [covDerivDefectJet_f00, gaugeFieldOfForm_zero, rescaledOperators_D_one]
    exact add_neg_one_smul_self _
  · rw [holonomyDefectJet_f00, gaugeFieldOfForm_zero, holonomyDefectKernel_one]
    exact symbolHom_zero _ _ κ
  · rw [halfFaceTraceJet_f00, gaugeFieldOfForm_zero, halfFaceTraceKernel_one]
    exact symbolHom_idKernel hId _ hF κ
  · rw [curvatureJet_f00, gaugeFieldOfForm_zero, curvatureKernel_one hSymm hL]
    exact symbolHom_zero _ _ κ
end YangMills.Construction.Tower.FullSpace.ZeroFieldJets
end
