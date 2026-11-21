import YangMills.Construction.Towers.TheDifferencesOfFormsReadAtTheSideInfinityProof
import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinatesProof
import YangMills.Construction.RunningCouplingSlope.FreeInversesOnASideAreLocalProof
import YangMills.Construction.Towers.DifferencesGiveTheTwoOperatorsAtOneOnTheUnitLatticeProof
import YangMills.Construction.Towers.LinearMapsOfATowerOnPeriodicFunctions
import YangMills.Construction.Towers.PeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.PolydiscServesAtTheSideInfinityProof
import YangMills.Construction.Towers.SecondDifferentialOfTheActionDescendsProof
import YangMills.Construction.Towers.SymbolsOfTheAveragesOnPlaneWavesProof
import YangMills.Construction.Towers.WeightedTransposesOfTheScaledPictureOnASideProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open PeriodicOperators
namespace TorusPeriodization
variable {I I' I'' : PeriodicData} {J J' J'' : Type}
private theorem translate_lattice_injective (hI : IsPeriodic I) {s : ℕ} (hs : 0 < s) (i : I.Carrier) :
    Function.Injective fun m : Fin 4 → ℤ => I.translate (s • m) i := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.translate_nsmul_injective <;> assumption
private theorem readsKernel_of_apply_eq (hI : IsPeriodic I) {q : I.Carrier → J} {q' : I'.Carrier → J'} {s : ℕ}
    (hs : 0 < s) (he : ∀ i i', q i = q i' ↔ ∃ m : Fin 4 → ℤ, i' = I.translate (s • m) i)
    {T : I'.Carrier → I.Carrier → ℂ} {M : J' → J → ℂ}
    (hact : ∀ (g : J → ℂ) (i' : I'.Carrier),
      applyKernel M g (q' i') = applyKernel T (fun i => g (q i)) i') :
    ReadsKernel q q' s T M := by
  classical
  intro i' i
  have h := hact (Pi.single (q i) 1) i'
  have hL : applyKernel M (Pi.single (q i) 1) (q' i') = M (q' i') (q i) := by
    unfold applyKernel
    rw [tsum_eq_single (q i)]
    · simp
    · intro j hj
      simp [hj]
  rw [hL] at h
  rw [h]
  unfold applyKernel periodization
  have hinj := translate_lattice_injective hI hs i
  have hsupp : Function.support (fun ι => T i' ι * (Pi.single (q i) (1 : ℂ) : J → ℂ) (q ι)) ⊆
      Set.range fun m : Fin 4 → ℤ => I.translate (s • m) i := by
    intro ι hι
    by_contra hn
    apply hι
    have hne : q ι ≠ q i := by
      intro hq
      obtain ⟨m, hm⟩ := (he i ι).1 hq.symm
      exact hn ⟨m, hm.symm⟩
    simp [hne]
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun m => ?_
  have hq : q (I.translate (s • m) i) = q i := ((he i _).2 ⟨m, rfl⟩).symm
  show T i' (I.translate (s • m) i) * (Pi.single (q i) (1 : ℂ) : J → ℂ) (q (I.translate (s • m) i)) = _
  rw [hq]
  simp
private theorem exists_decayRate {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) :
    ∃ δ, IsDecayRate I I' T δ := by apply _root_.YangMills.Construction.PeriodicOperators.TorusAction.exists_decayRate <;> assumption
private theorem periodized_properties (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hTK : Periodized.Claim)
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) :
    Periodized.Properties I I' T := by
  obtain ⟨δ, hδ⟩ := exists_decayRate hT
  exact hTK I I' hI hI' T δ hT hδ
private theorem summable_translates (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hTK : Periodized.Claim)
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) {s : ℕ} (hs : 0 < s)
    (i' : I'.Carrier) (i : I.Carrier) :
    Summable fun m : Fin 4 → ℤ => T i' (I.translate (s • m) i) :=
  ((periodized_properties hI hI' hTK hT).summable s hs i' i).of_norm
private theorem readsKernel_add (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hTK : Periodized.Claim) {q : I.Carrier → J} {q' : I'.Carrier → J'}
    {s : ℕ} (hs : 0 < s) {T T' : I'.Carrier → I.Carrier → ℂ} {M M' : J' → J → ℂ}
    (hT : IsPeriodicKernel I I' T) (hT' : IsPeriodicKernel I I' T')
    (h : ReadsKernel q q' s T M) (h' : ReadsKernel q q' s T' M') :
    ReadsKernel q q' s (T + T') (M + M') := by
  intro i' i
  show M (q' i') (q i) + M' (q' i') (q i) = ∑' m : Fin 4 → ℤ, (T i' _ + T' i' _)
  rw [h, h', Summable.tsum_add (summable_translates hI hI' hTK hT hs i' i)
    (summable_translates hI hI' hTK hT' hs i' i)]
  rfl
private theorem readsKernel_sub (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hTK : Periodized.Claim) {q : I.Carrier → J} {q' : I'.Carrier → J'}
    {s : ℕ} (hs : 0 < s) {T T' : I'.Carrier → I.Carrier → ℂ} {M M' : J' → J → ℂ}
    (hT : IsPeriodicKernel I I' T) (hT' : IsPeriodicKernel I I' T')
    (h : ReadsKernel q q' s T M) (h' : ReadsKernel q q' s T' M') :
    ReadsKernel q q' s (T - T') (M - M') := by
  intro i' i
  show M (q' i') (q i) - M' (q' i') (q i) = ∑' m : Fin 4 → ℤ, (T i' _ - T' i' _)
  rw [h, h', Summable.tsum_sub (summable_translates hI hI' hTK hT hs i' i)
    (summable_translates hI hI' hTK hT' hs i' i)]
  rfl
private theorem readsKernel_transpose (hI' : IsPeriodic I') {q : I.Carrier → J} {q' : I'.Carrier → J'} {s : ℕ}
    {T : I'.Carrier → I.Carrier → ℂ} {M : J' → J → ℂ} (hcov : IsShiftInvariant I I' T) (c : ℂ)
    (h : ReadsKernel q q' s T M) :
    ReadsKernel q' q s (fun ι ι' => c * T ι' ι) (fun j j' => c * M j' j) := by
  intro i i'
  show c * M (q' i') (q i) = ∑' m : Fin 4 → ℤ, c * T (I'.translate (s • m) i') i
  rw [h, tsum_mul_left]
  congr 1
  unfold periodization
  rw [← (Equiv.neg (Fin 4 → ℤ)).tsum_eq]
  refine tsum_congr fun m => ?_
  have h1 := hcov (-(s • m)) (I'.translate (s • m) i') i
  rw [← hI'.translate_add, add_neg_cancel, hI'.translate_zero] at h1
  rw [← h1]
  simp
private theorem decayRate_mono {T : I'.Carrier → I.Carrier → ℂ} {δ δ' : ℝ} (h : IsDecayRate I I' T δ)
    (h0 : 0 < δ') (hle : δ' ≤ δ) : IsDecayRate I I' T δ' := by apply _root_.YangMills.Construction.PeriodicOperators.TorusAction.decayRate_of_le <;> assumption
private theorem isPeriodicKernel_comp (hP : CompClaim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S) :
    IsPeriodicKernel I'' I' (compKernel T S) := by apply _root_.YangMills.SharedProofs.p12760 <;> assumption
private theorem isPeriodicKernel_sub {T T' : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T)
    (hT' : IsPeriodicKernel I I' T') : IsPeriodicKernel I I' (T - T') := by
  obtain ⟨δ, hδ⟩ := exists_decayRate hT
  obtain ⟨δ', hδ'⟩ := exists_decayRate hT'
  have h0 : 0 < min δ δ' := lt_min hδ.1 hδ'.1
  obtain ⟨-, C, hC, hb⟩ := decayRate_mono hδ h0 (min_le_left _ _)
  obtain ⟨-, C', hC', hb'⟩ := decayRate_mono hδ' h0 (min_le_right _ _)
  refine ⟨fun m ι' ι => ?_, C + C', min δ δ', by positivity, h0, fun ι' ι => ?_⟩
  · show T _ _ - T' _ _ = T _ _ - T' _ _
    rw [hT.1 m ι' ι, hT'.1 m ι' ι]
  · refine (norm_sub_le _ _).trans ?_
    have h1 := hb ι' ι
    have h2 := hb' ι' ι
    rw [add_mul]
    exact add_le_add h1 h2
private theorem readsKernel_of_represents (hI : IsPeriodic I) {q : I.Carrier → J} {q' : I'.Carrier → J'} {s : ℕ}
    (hs : 0 < s) (he : ∀ i i', q i = q i' ↔ ∃ m : Fin 4 → ℤ, i' = I.translate (s • m) i)
    {T : I'.Carrier → I.Carrier → ℂ} {M : J' → J → ℂ} {mW : (I.Carrier → ℂ) → I'.Carrier → ℂ}
    {mS : (J → ℂ) → J' → ℂ} (hT : ∀ f, applyKernel T f = mW f) (hM : ∀ g, applyKernel M g = mS g)
    (hm : ∀ (g : J → ℂ) (i' : I'.Carrier), mS g (q' i') = mW (fun i => g (q i)) i') :
    ReadsKernel q q' s T M :=
  readsKernel_of_apply_eq hI hs he fun g i' => by rw [hM, hT, hm]
section Quotients
open Tower LocalKernels LocalKernels.Periodisation
variable {L n k l : ℕ}
private theorem torus_ofPauliCoeffs_pos (c : Fin 3 × Tower.PositiveEdge L n k l → ℂ)
    {b : Edge L n k l} (hb : b.IsPositivelyOriented) :
    (edgePauliCoordinates L n k l).ofCoeffs c b = ofPauliCoeffs c ⟨b, hb⟩ := by apply _root_.YangMills.Construction.Tower.WeightedTransposesOnTorus.edgePauliCoordinates_ofCoeffs_apply_of_pos <;> assumption
private theorem torus_ofPauliCoeffs_opposite
    (hx : ∀ b : Edge L n k l, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (c : Fin 3 × Tower.PositiveEdge L n k l → ℂ) (b : Edge L n k l) :
    (edgePauliCoordinates L n k l).ofCoeffs c b.opposite = -(edgePauliCoordinates L n k l).ofCoeffs c b := by apply _root_.YangMills.Construction.Tower.FormCoboundariesAtInfinity.edgeFormOf_opposite <;> assumption
private theorem full_flip_isPositive {b : FullSpace.Edge L k l} (hb : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.InfiniteSideAdmissibility.fullSpace_opposite_isPositivelyOriented <;> assumption
private theorem full_ofPauliCoeffs_pos (c : (FullSpace.edgePauliCoordinates L k l).Index → ℂ)
    {b : FullSpace.Edge L k l} (hb : b.IsPositivelyOriented) :
    (FullSpace.edgePauliCoordinates L k l).ofCoeffs c b = ofPauliCoeffs c ⟨b, hb⟩ := by apply _root_.YangMills.Construction.Tower.IdentityOperators.ofCoeffs_of_positive <;> assumption
private theorem full_ofPauliCoeffs_neg (c : (FullSpace.edgePauliCoordinates L k l).Index → ℂ)
    {b : FullSpace.Edge L k l} (hb : ¬b.IsPositivelyOriented) :
    (FullSpace.edgePauliCoordinates L k l).ofCoeffs c b =
      -ofPauliCoeffs c ⟨b.opposite, full_flip_isPositive hb⟩ := by
  unfold FullSpace.edgePauliCoordinates
  dsimp only
  rw [FullSpace.extendOddly, if_neg hb]
  exact congrArg Neg.neg (dif_pos (full_flip_isPositive hb))
private theorem lift_ofPauliCoeffs_pos (hBI : ProjEdgesCompatible L n k l)
    (g : Fin 3 × Tower.PositiveEdge L n k l → ℂ) {b : FullSpace.Edge L k l}
    (hb : b.IsPositivelyOriented) :
    ofPauliCoeffs (fun ι : (FullSpace.edgePauliCoordinates L k l).Index => g (colouredEdgeProj L n k l ι)) ⟨b, hb⟩ =
      (edgePauliCoordinates L n k l).ofCoeffs g (FullSpace.projEdge L n k l b) := by
  have e := hBI.2.1 ⟨b, hb⟩
  have hp : (FullSpace.projEdge L n k l b).IsPositivelyOriented :=
    e ▸ (projPositiveEdge L n k l ⟨b, hb⟩).2
  have e' : projPositiveEdge L n k l ⟨b, hb⟩ = ⟨FullSpace.projEdge L n k l b, hp⟩ :=
    Subtype.ext e
  rw [torus_ofPauliCoeffs_pos g hp]
  unfold ofPauliCoeffs colouredEdgeProj
  simp only
  exact Finset.sum_congr rfl fun a _ => by rw [e']
private theorem projEdge_flip (hBI : ProjEdgesCompatible L n k l) (b : FullSpace.Edge L k l) :
    FullSpace.projEdge L n k l b.opposite = (FullSpace.projEdge L n k l b).opposite := by apply _root_.YangMills.Construction.LocalKernels.HessianAtLifts.projEdge_opposite <;> assumption
private theorem ofPauliCoeffs_extend
    (hx : ∀ b : Edge L n k l, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hBI : ProjEdgesCompatible L n k l)
    (g : Fin 3 × Tower.PositiveEdge L n k l → ℂ) (b : FullSpace.Edge L k l) :
    (FullSpace.edgePauliCoordinates L k l).ofCoeffs (fun ι => g (colouredEdgeProj L n k l ι)) b =
      (edgePauliCoordinates L n k l).ofCoeffs g (FullSpace.projEdge L n k l b) := by
  by_cases hb : b.IsPositivelyOriented
  · rw [full_ofPauliCoeffs_pos _ hb]
    exact lift_ofPauliCoeffs_pos hBI g hb
  · rw [full_ofPauliCoeffs_neg _ hb, lift_ofPauliCoeffs_pos hBI g (full_flip_isPositive hb),
      projEdge_flip hBI, torus_ofPauliCoeffs_opposite hx, neg_neg]
private theorem coeffs_projEdge (hBI : ProjEdgesCompatible L n k l) (F : Edge L n k l → Matrices.ComplexMatrix2)
    (i : (FullSpace.edgePauliCoordinates L k l).Index) :
    (FullSpace.edgePauliCoordinates L k l).coeffs (fun b => F (FullSpace.projEdge L n k l b)) i =
      (edgePauliCoordinates L n k l).coeffs F (colouredEdgeProj L n k l i) := by
  have e := hBI.2.1 i.2
  show pauliCoeff i.1 (F (FullSpace.projEdge L n k l i.2.1)) =
    pauliCoeff i.1 (F (projPositiveEdge L n k l i.2).1)
  rw [e]
private theorem pauli_combination_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
private theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) :
    ofPauliCoeffs c ∈ Matrices.GroupLieProduct.tracelessFunctions σ := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.ofPauliCoeffs_mem <;> assumption
private theorem torus_ofPauliCoeffs_mem
    (hx : ∀ b : Edge L n k l, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (c : Fin 3 × Tower.PositiveEdge L n k l → ℂ) :
    (edgePauliCoordinates L n k l).ofCoeffs c ∈ complexEdgeForms L n k l := by
  refine ⟨fun b hb => ?_, fun b => torus_ofPauliCoeffs_opposite hx c b⟩
  rw [torus_ofPauliCoeffs_pos c hb]
  exact pauli_combination_mem_traceless _
section Base
open Tower.UnitScale.OneStepChart
open Tower.RescaledConditions (TrivialRelations)
private theorem vertexCoboundary_reads (hs : 0 < periodSide L n)
    (hes : ∀ i i', colouredVertexProj L n k 0 i = colouredVertexProj L n k 0 i' ↔ ∃ m : Fin 4 → ℤ,
      i' = (colourVertices L k 0).translate (periodSide L n • m) i)
    (hPs : IsPeriodic (colourVertices L k 0))
    (hBI : ProjEdgesCompatible L n k 0)
    (hW : Represents ((vertexCoordinate (FullSpace.Vertex L k 0)).kernel (FullSpace.edgePauliCoordinates L k 0)
        FullSpace.scaledVertexCoboundary)
      ((vertexCoordinate (FullSpace.Vertex L k 0)).mapOnCoeffs (FullSpace.edgePauliCoordinates L k 0)
        FullSpace.scaledVertexCoboundary))
    (hS : Represents ((vertexCoordinate (Vertex L n k 0)).kernel (edgePauliCoordinates L n k 0) scaledVertexCoboundary)
      ((vertexCoordinate (Vertex L n k 0)).mapOnCoeffs (edgePauliCoordinates L n k 0) scaledVertexCoboundary))
    (hM : TwoScaleMap (vertexFunctions L n k 0) (edgeForms L n k 0) FullSpace.vertexCoboundary
      Tower.vertexCoboundary) :
    ReadsKernel (I := colourVertices L k 0) (I' := colourEdges L k 0) (colouredVertexProj L n k 0)
      (colouredEdgeProj L n k 0) (periodSide L n)
      ((vertexCoordinate (FullSpace.Vertex L k 0)).kernel (FullSpace.edgePauliCoordinates L k 0)
        FullSpace.scaledVertexCoboundary)
      ((vertexCoordinate (Vertex L n k 0)).kernel (edgePauliCoordinates L n k 0) scaledVertexCoboundary) := by
  refine readsKernel_of_represents hPs hs hes (fun f => (hW f).2) (fun g => (hS g).2) fun g i' => ?_
  have h1 := hM.map_extend (ofPauliCoeffs g) (ofPauliCoeffs_mem g)
  show (edgePauliCoordinates L n k 0).coeffs (scaledVertexCoboundary (ofPauliCoeffs g)) (colouredEdgeProj L n k 0 i') =
    (FullSpace.edgePauliCoordinates L k 0).coeffs (FullSpace.scaledVertexCoboundary
      (ofPauliCoeffs fun i => g (colouredVertexProj L n k 0 i))) i'
  have h2 : FullSpace.scaledVertexCoboundary (ofPauliCoeffs fun i => g (colouredVertexProj L n k 0 i)) =
      fun b => (scaledVertexCoboundary (ofPauliCoeffs g) : Edge L n k 0 → Matrices.ComplexMatrix2)
        (FullSpace.projEdge L n k 0 b) := by
    unfold FullSpace.scaledVertexCoboundary scaledVertexCoboundary
    have h3 : (ofPauliCoeffs fun i => g (colouredVertexProj L n k 0 i)) =
        (vertexFunctions L n k 0).extend (ofPauliCoeffs g) := rfl
    rw [h3, h1]
    rfl
  rw [h2]
  exact (coeffs_projEdge hBI _ i').symm
private theorem edgeCoboundary_reads (hs : 0 < periodSide L n)
    (heb : ∀ i i', colouredEdgeProj L n k 0 i = colouredEdgeProj L n k 0 i' ↔ ∃ m : Fin 4 → ℤ,
      i' = (colourEdges L k 0).translate (periodSide L n • m) i)
    (hPb : IsPeriodic (colourEdges L k 0))
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hBI : ProjEdgesCompatible L n k 0)
    (hW : Represents ((FullSpace.edgePauliCoordinates L k 0).kernel (vertexCoordinate (FullSpace.Face L k 0))
        FullSpace.scaledEdgeCoboundary)
      ((FullSpace.edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (FullSpace.Face L k 0))
        FullSpace.scaledEdgeCoboundary))
    (hS : Represents ((edgePauliCoordinates L n k 0).kernel (vertexCoordinate (Face L n k 0))
        scaledEdgeCoboundary)
      ((edgePauliCoordinates L n k 0).mapOnCoeffs (vertexCoordinate (Face L n k 0))
        scaledEdgeCoboundary))
    (hM : TwoScaleMap (edgeForms L n k 0) (faceFunctions L n k 0) FullSpace.edgeCoboundary
      Tower.edgeCoboundary) :
    ReadsKernel (I := colourEdges L k 0) (I' := colourFaces L k 0) (colouredEdgeProj L n k 0)
      (colouredFaceProj L n k 0) (periodSide L n)
      ((FullSpace.edgePauliCoordinates L k 0).kernel (vertexCoordinate (FullSpace.Face L k 0))
        FullSpace.scaledEdgeCoboundary)
      ((edgePauliCoordinates L n k 0).kernel (vertexCoordinate (Face L n k 0))
        scaledEdgeCoboundary) := by
  refine readsKernel_of_represents hPb hs heb (fun f => (hW f).2) (fun g => (hS g).2) fun g i' => ?_
  have h1 := hM.map_extend ((edgePauliCoordinates L n k 0).ofCoeffs g) (torus_ofPauliCoeffs_mem hx g)
  show toPauliCoeffs (scaledEdgeCoboundary ((edgePauliCoordinates L n k 0).ofCoeffs g))
      (colouredFaceProj L n k 0 i') =
    toPauliCoeffs (FullSpace.scaledEdgeCoboundary
      ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs fun i => g (colouredEdgeProj L n k 0 i))) i'
  have h3 : ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs fun i => g (colouredEdgeProj L n k 0 i)) =
      (edgeForms L n k 0).extend ((edgePauliCoordinates L n k 0).ofCoeffs g) :=
    funext fun b => ofPauliCoeffs_extend hx hBI g b
  have h2 : FullSpace.scaledEdgeCoboundary
      ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs fun i => g (colouredEdgeProj L n k 0 i)) =
      fun p => (scaledEdgeCoboundary ((edgePauliCoordinates L n k 0).ofCoeffs g) :
        Face L n k 0 → Matrices.ComplexMatrix2) (FullSpace.projFace L n k 0 p) := by
    unfold FullSpace.scaledEdgeCoboundary scaledEdgeCoboundary
    rw [h3, h1]
    rfl
  rw [h2]
  rfl
private theorem edgeMap_reads (hs : 0 < periodSide L n)
    (heb : ∀ i i', colouredEdgeProj L n k 0 i = colouredEdgeProj L n k 0 i' ↔ ∃ m : Fin 4 → ℤ,
      i' = (colourEdges L k 0).translate (periodSide L n • m) i)
    (hPb : IsPeriodic (colourEdges L k 0))
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hBI : ProjEdgesCompatible L n k 0) (hBIk : ProjEdgesCompatible L n k k)
    {O : (FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) → FullSpace.Edge L k k → Matrices.ComplexMatrix2}
    {O' : (Edge L n k 0 → Matrices.ComplexMatrix2) → Edge L n k k → Matrices.ComplexMatrix2} (c : ℝ)
    {T : (colourEdges L k k).Carrier → (colourEdges L k 0).Carrier → ℂ}
    {M : Fin 3 × Tower.PositiveEdge L n k k → Fin 3 × Tower.PositiveEdge L n k 0 → ℂ}
    (hW : Represents (I := (FullSpace.edgePauliCoordinates L k 0).Index) (J := (FullSpace.edgePauliCoordinates L k k).Index) T
      ((FullSpace.edgePauliCoordinates L k 0).mapOnCoeffs (FullSpace.edgePauliCoordinates L k k) fun B => c • O B))
    (hS : Represents (I := (edgePauliCoordinates L n k 0).Index) (J := (edgePauliCoordinates L n k k).Index) M
      ((edgePauliCoordinates L n k 0).mapOnCoeffs (edgePauliCoordinates L n k k) fun B => c • O' B))
    (hM : TwoScaleMap (edgeForms L n k 0) (edgeForms L n k k) O O') :
    ReadsKernel (I := colourEdges L k 0) (I' := colourEdges L k k) (colouredEdgeProj L n k 0)
      (colouredEdgeProj L n k k) (periodSide L n) T M := by
  refine readsKernel_of_represents hPb hs heb (fun f => (hW f).2) (fun g => (hS g).2) fun g i' => ?_
  have h1 := hM.map_extend ((edgePauliCoordinates L n k 0).ofCoeffs g) (torus_ofPauliCoeffs_mem hx g)
  have h3 : ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs fun i => g (colouredEdgeProj L n k 0 i)) =
      (edgeForms L n k 0).extend ((edgePauliCoordinates L n k 0).ofCoeffs g) :=
    funext fun b => ofPauliCoeffs_extend hx hBI g b
  show (edgePauliCoordinates L n k k).coeffs (c • O' ((edgePauliCoordinates L n k 0).ofCoeffs g))
      (colouredEdgeProj L n k k i') =
    (FullSpace.edgePauliCoordinates L k k).coeffs (c • O
      ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs fun i => g (colouredEdgeProj L n k 0 i))) i'
  rw [h3, h1]
  exact (coeffs_projEdge hBIk _ i').symm
private theorem vertexMap_reads (hs : 0 < periodSide L n)
    (hes : ∀ i i', colouredVertexProj L n k 0 i = colouredVertexProj L n k 0 i' ↔ ∃ m : Fin 4 → ℤ,
      i' = (colourVertices L k 0).translate (periodSide L n • m) i)
    (hPs : IsPeriodic (colourVertices L k 0))
    {O : (FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2) → FullSpace.Vertex L k k → Matrices.ComplexMatrix2}
    {O' : (Vertex L n k 0 → Matrices.ComplexMatrix2) → Vertex L n k k → Matrices.ComplexMatrix2}
    {T : (colourVertices L k k).Carrier → (colourVertices L k 0).Carrier → ℂ}
    {M : Fin 3 × Vertex L n k k → Fin 3 × Vertex L n k 0 → ℂ}
    (hW : Represents (I := (vertexCoordinate (FullSpace.Vertex L k 0)).Index)
      (J := (vertexCoordinate (FullSpace.Vertex L k k)).Index) T
      ((vertexCoordinate (FullSpace.Vertex L k 0)).mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L k k)) O))
    (hS : Represents (I := (vertexCoordinate (Vertex L n k 0)).Index)
      (J := (vertexCoordinate (Vertex L n k k)).Index) M
      ((vertexCoordinate (Vertex L n k 0)).mapOnCoeffs (vertexCoordinate (Vertex L n k k)) O'))
    (hM : TwoScaleMap (vertexFunctions L n k 0) (vertexFunctions L n k k) O O') :
    ReadsKernel (I := colourVertices L k 0) (I' := colourVertices L k k) (colouredVertexProj L n k 0)
      (colouredVertexProj L n k k) (periodSide L n) T M := by
  refine readsKernel_of_represents hPs hs hes (fun f => (hW f).2) (fun g => (hS g).2) fun g i' => ?_
  have h1 := hM.map_extend (ofPauliCoeffs g) (ofPauliCoeffs_mem g)
  show toPauliCoeffs (O' (ofPauliCoeffs g)) (colouredVertexProj L n k k i') =
    toPauliCoeffs (O (ofPauliCoeffs fun i => g (colouredVertexProj L n k 0 i))) i'
  have h3 : (ofPauliCoeffs fun i => g (colouredVertexProj L n k 0 i)) =
      (vertexFunctions L n k 0).extend (ofPauliCoeffs g) := rfl
  rw [h3, h1]
  rfl
end Base
end Quotients
open Tower Tower.FreeResolvents LocalKernels LocalKernels.Periodisation in
theorem freeOperatorsPeriodizeOnTorus_holds (hR : KernelMatricesOnSide) (hCR : CellQuotientsOfTower)
    (hTK : Periodized.Claim) (hP : CompClaim)
    (hFO : FreeOperators.FreeOperatorsArePeriodic) (hIS : PeriodicOperators.TowerIndexSets.Claim)
    (hPE : LocalKernels.Periodisation.PeriodisationHolds)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hRS : TrivialFieldRescaledRelations.Statement)
    (hRW : FullSpace.RescaledTrivialRelations)
    (hLM : UnitScale.PeriodicTowerMaps.AgreeWithTorusMaps) :
    FreeOperatorsPeriodizeOnTorus := by
  intro L n k hL hn hk
  have hs : 0 < periodSide L n := by
    have : 0 < L := by have := hL.2; omega
    unfold periodSide
    positivity
  obtain ⟨cS, cB, cP, cTS, cTB⟩ := hCR L n k hL hn
  have rS : IsPeriodicQuotient (colourVertices L k 0) (colouredVertexProj L n k 0) (periodSide L n) :=
    ⟨cS.surjective, cS.image_eq_iff⟩
  have rB : IsPeriodicQuotient (colourEdges L k 0) (colouredEdgeProj L n k 0) (periodSide L n) :=
    ⟨cB.surjective, cB.image_eq_iff⟩
  have rP : IsPeriodicQuotient (colourFaces L k 0) (colouredFaceProj L n k 0) (periodSide L n) :=
    ⟨cP.surjective, cP.image_eq_iff⟩
  have rTS : IsPeriodicQuotient (colourVertices L k k) (colouredVertexProj L n k k) (periodSide L n) :=
    ⟨cTS.surjective, cTS.image_eq_iff⟩
  have rTB : IsPeriodicQuotient (colourEdges L k k) (colouredEdgeProj L n k k) (periodSide L n) :=
    ⟨cTB.surjective, cTB.image_eq_iff⟩
  obtain ⟨pS, pB, pP⟩ := hIS L hL k 0 (Nat.zero_le k)
  obtain ⟨pTS, pTB, -⟩ := hIS L hL k k le_rfl
  obtain ⟨maps, ops⟩ := hFO.2 L hL k hk
  have RW := hRW L hL k hk
  have RS := hRS L hL k hk n hn
  have MP := hLM L hL n k hn
  have hx : ∀ l, l ≤ k → ∀ b : Edge L n k l, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun l hl b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ l hl).2.2.2 b).2.2.2.2.2
  have hBI0 := ((hPE L hL k n hn).1 0 (Nat.zero_le k)).2
  have hBIk := ((hPE L hL k n hn).1 k le_rfl).2
  have eDW : (trivialRescaledOperators L k).D = FullSpace.scaledVertexCoboundaryKernel L k 0 := RW.D_eq
  have eDS : (rescaledOperators L n k (trivialField L n k 0)).D =
      (vertexCoordinate (Vertex L n k 0)).kernel (edgePauliCoordinates L n k 0) scaledVertexCoboundary := RS.D_eq
  have hD : ReadsKernel (I := colourVertices L k 0) (I' := colourEdges L k 0) (colouredVertexProj L n k 0)
      (colouredEdgeProj L n k 0) (periodSide L n) (trivialRescaledOperators L k).D
      (rescaledOperators L n k (trivialField L n k 0)).D := by
    rw [eDW, eDS]
    exact vertexCoboundary_reads hs rS.eq_iff_exists_translate pS hBI0 RW.vertex_represents
      RS.vertex_represents (MP.vertexCoboundary 0 (Nat.zero_le k))
  have hC : ReadsKernel (I := colourEdges L k 0) (I' := colourFaces L k 0)
      (colouredEdgeProj L n k 0) (colouredFaceProj L n k 0) (periodSide L n)
      (FullSpace.scaledEdgeCoboundaryKernel L k 0) (scaledEdgeCoboundaryKernel L n k 0) :=
    edgeCoboundary_reads hs rB.eq_iff_exists_translate pB (hx 0 (Nat.zero_le k)) hBI0 RW.edge_represents
      RS.edge_represents (MP.edgeCoboundary 0 (Nat.zero_le k))
  have hQ : ReadsKernel (I := colourEdges L k 0) (I' := colourEdges L k k) (colouredEdgeProj L n k 0)
      (colouredEdgeProj L n k k) (periodSide L n) (trivialRescaledOperators L k).Q
      (rescaledOperators L n k (trivialField L n k 0)).Q :=
    edgeMap_reads hs rB.eq_iff_exists_translate pB (hx 0 (Nat.zero_le k)) hBI0 hBIk (finestMesh L k)
      RW.Q_represents RS.Q_represents (MP.crossingIter k le_rfl)
  have hRr : ReadsKernel (I := colourVertices L k 0) (I' := colourVertices L k k) (colouredVertexProj L n k 0)
      (colouredVertexProj L n k k) (periodSide L n) (trivialRescaledOperators L k).R
      (rescaledOperators L n k (trivialField L n k 0)).R :=
    vertexMap_reads hs rS.eq_iff_exists_translate pS RW.R_represents RS.R_represents
      (MP.vertexSmoothingIter k le_rfl)
  have perD : IsPeriodicKernel (colourVertices L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).D := by
    rw [eDW]
    exact (maps.vertexCoboundary 0 (Nat.zero_le k)).finite_range.1
  have perC : IsPeriodicKernel (colourEdges L k 0) (colourFaces L k 0)
      (FullSpace.scaledEdgeCoboundaryKernel L k 0) :=
    (maps.edgeCoboundary 0 (Nat.zero_le k)).finite_range.1
  have perQ : IsPeriodicKernel (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q :=
    maps.edgeAverage.finite_range.1
  have perR : IsPeriodicKernel (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R :=
    maps.vertexAverage.finite_range.1
  have perQt : IsPeriodicKernel (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt :=
    ops.edgeAverage_transpose.1
  have perRt : IsPeriodicKernel (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt :=
    ops.vertexAverage_transpose.1
  have perDt : IsPeriodicKernel (colourEdges L k 0) (colourVertices L k 0)
      (trivialRescaledOperators L k).Dt := by
    have h := (ops.vertexCoboundary_transpose 0 (Nat.zero_le k)).1
    have e : (trivialRescaledOperators L k).Dt = kernelTranspose (colourVertices L k 0) (colourEdges L k 0)
        (FullSpace.scaledVertexCoboundaryKernel L k 0) := by
      show meshTranspose _ _ (trivialRescaledOperators L k).D = _
      rw [eDW]
      rfl
    rw [e]
    exact h
  have perCt : IsPeriodicKernel (colourFaces L k 0) (colourEdges L k 0)
      (meshTranspose (finestMesh L k) (finestMesh L k)
        (FullSpace.scaledEdgeCoboundaryKernel L k 0)) :=
    (ops.edgeCoboundary_transpose 0 (Nat.zero_le k)).1
  have hDt : ReadsKernel (I := colourEdges L k 0) (I' := colourVertices L k 0) (colouredEdgeProj L n k 0)
      (colouredVertexProj L n k 0) (periodSide L n) (trivialRescaledOperators L k).Dt
      (rescaledOperators L n k (trivialField L n k 0)).Dt :=
    readsKernel_transpose pB perD.1 ((((finestMesh L k) ^ 4 / (finestMesh L k) ^ 4 : ℝ)) : ℂ) hD
  have hQt : ReadsKernel (I := colourEdges L k k) (I' := colourEdges L k 0) (colouredEdgeProj L n k k)
      (colouredEdgeProj L n k 0) (periodSide L n) (trivialRescaledOperators L k).Qt
      (rescaledOperators L n k (trivialField L n k 0)).Qt :=
    readsKernel_transpose pTB perQ.1 ((((meshAt L k k) ^ 4 / (finestMesh L k) ^ 4 : ℝ)) : ℂ) hQ
  have hRt : ReadsKernel (I := colourVertices L k k) (I' := colourVertices L k 0) (colouredVertexProj L n k k)
      (colouredVertexProj L n k 0) (periodSide L n) (trivialRescaledOperators L k).Rt
      (rescaledOperators L n k (trivialField L n k 0)).Rt :=
    readsKernel_transpose pTS perR.1 ((((meshAt L k k) ^ 4 / (finestMesh L k) ^ 4 : ℝ)) : ℂ) hRr
  have hCt : ReadsKernel (I := colourFaces L k 0) (I' := colourEdges L k 0)
      (colouredFaceProj L n k 0) (colouredEdgeProj L n k 0) (periodSide L n)
      (meshTranspose (finestMesh L k) (finestMesh L k)
        (FullSpace.scaledEdgeCoboundaryKernel L k 0))
      (meshTranspose (finestMesh L k) (finestMesh L k)
        (scaledEdgeCoboundaryKernel L n k 0)) :=
    readsKernel_transpose pP perC.1 ((((finestMesh L k) ^ 4 / (finestMesh L k) ^ 4 : ℝ)) : ℂ) hC
  have eHW : (trivialRescaledOperators L k).H = compKernel (meshTranspose (finestMesh L k)
      (finestMesh L k) (FullSpace.scaledEdgeCoboundaryKernel L k 0))
      (FullSpace.scaledEdgeCoboundaryKernel L k 0) := RW.H_eq
  have eHS : (rescaledOperators L n k (trivialField L n k 0)).H =
      compKernel (meshTranspose (finestMesh L k) (finestMesh L k)
        (scaledEdgeCoboundaryKernel L n k 0)) (scaledEdgeCoboundaryKernel L n k 0) :=
    RS.H_eq
  have hH : ReadsKernel (I := colourEdges L k 0) (I' := colourEdges L k 0) (colouredEdgeProj L n k 0)
      (colouredEdgeProj L n k 0) (periodSide L n) (trivialRescaledOperators L k).H
      (rescaledOperators L n k (trivialField L n k 0)).H := by
    rw [eHW, eHS]
    exact (hR _ _ _ pP pB pB (colouredFaceProj L n k 0) (colouredEdgeProj L n k 0)
      (colouredEdgeProj L n k 0) _ hs rP rB rB).1 _ _ _ _ perCt perC hCt hC
  have perH : IsPeriodicKernel (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).H := by
    rw [eHW]
    exact isPeriodicKernel_comp hP pP pB pB perCt perC
  have perDDt := isPeriodicKernel_comp hP pS pB pB perD perDt
  have hDDt := (hR _ _ _ pS pB pB (colouredVertexProj L n k 0) (colouredEdgeProj L n k 0)
    (colouredEdgeProj L n k 0) _ hs rS rB rB).1 _ _ _ _ perD perDt hD hDt
  have hK : ReadsKernel (I := colourEdges L k 0) (I' := colourEdges L k 0) (colouredEdgeProj L n k 0)
      (colouredEdgeProj L n k 0) (periodSide L n) (trivialRescaledOperators L k).K
      (rescaledOperators L n k (trivialField L n k 0)).K :=
    readsKernel_add pB pB hTK hs perH perDDt hH hDDt
  have perDelta := isPeriodicKernel_comp hP pB pS pS perDt perD
  have hDelta := (hR _ _ _ pB pS pS (colouredEdgeProj L n k 0) (colouredVertexProj L n k 0)
    (colouredVertexProj L n k 0) _ hs rB rS rS).1 _ _ _ _ perDt perD hDt hD
  have perDRt := isPeriodicKernel_comp hP pS pB pTS perD perRt
  have hDRt := (hR _ _ _ pS pB pTS (colouredVertexProj L n k 0) (colouredEdgeProj L n k 0)
    (colouredVertexProj L n k k) _ hs rS rB rTS).1 _ _ _ _ perD perRt hD hRt
  have perRDt := isPeriodicKernel_comp hP pS pTS pB perR perDt
  have hRDt := (hR _ _ _ pS pTS pB (colouredVertexProj L n k 0) (colouredVertexProj L n k k)
    (colouredEdgeProj L n k 0) _ hs rS rTS rB).1 _ _ _ _ perR perDt hRr hDt
  have perDRRD := isPeriodicKernel_comp hP pTS pB pB perDRt perRDt
  have hDRRD := (hR _ _ _ pTS pB pB (colouredVertexProj L n k k) (colouredEdgeProj L n k 0)
    (colouredEdgeProj L n k 0) _ hs rTS rB rB).1 _ _ _ _ perDRt perRDt hDRt hRDt
  have perQtQ := isPeriodicKernel_comp hP pTB pB pB perQt perQ
  have hQtQ := (hR _ _ _ pTB pB pB (colouredEdgeProj L n k k) (colouredEdgeProj L n k 0)
    (colouredEdgeProj L n k 0) _ hs rTB rB rB).1 _ _ _ _ perQt perQ hQt hQ
  have perK : IsPeriodicKernel (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).K :=
    ops.K.1
  have hKm := readsKernel_sub pB pB hTK hs perK perDRRD hK hDRRD
  have perKm := isPeriodicKernel_sub perK perDRRD
  have hXi := readsKernel_add pB pB hTK hs perKm perQtQ hKm hQtQ
  have perRtR := isPeriodicKernel_comp hP pTS pS pS perRt perR
  have hRtR := (hR _ _ _ pTS pS pS (colouredVertexProj L n k k) (colouredVertexProj L n k 0)
    (colouredVertexProj L n k 0) _ hs rTS rS rS).1 _ _ _ _ perRt perR hRt hRr
  have hY := readsKernel_add pS pS hTK hs perDelta perRtR hDelta hRtR
  exact ⟨hD, hDt, hQ, hQt, hRr, hRt, hC, hXi, hY⟩
end TorusPeriodization
end YangMills.Construction.RunningCouplingSlope
end
