import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Towers.FactsOfTheMatricesOfAPeriodicFunctionProof
import YangMills.Construction.Towers.KernelsOfTheTwoOperatorsAreProductsProof
import YangMills.Construction.Towers.AbelianOperatorsAreLocalAndSelfAdjoint
import YangMills.Construction.Towers.EntriesOfTheAbelianKernels
import YangMills.Construction.Towers.GaugeDirectionsOnTheUnitLattice
import YangMills.Construction.Towers.NormOfTheColourCoefficients
import YangMills.Construction.Towers.PlaquettesOfAnAbelianField
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.SymbolsOfTheAveragesOnPlaneWavesProof
import YangMills.Construction.Towers.SymmetriesOfTheAbelianOperators
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.AbelianOperatorsLocalSelfAdjointProof
open YangMills.Construction.Tower.AbelianFieldFacts YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.AbelianFieldDensity
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Matrices
theorem trigPoly_bounded {E : Type} {Q : (E → ℝ) → ℂ} (h : IsTrigPolynomial Q) :
    ∃ c : ℝ, ∀ φ, ‖Q φ‖ ≤ c := by
  obtain ⟨-, -, γ, hfin, hQ⟩ := h
  refine ⟨∑ n ∈ hfin.toFinset, ‖γ n‖, fun φ => ?_⟩
  have hsub : Function.support (fun n => γ n * fourierMode n φ) ⊆ (hfin.toFinset : Set (E → ℤ)) := by
    intro n hn
    simp only [Function.mem_support] at hn
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    exact fun h0 => hn (by simp [h0])
  rw [hQ, finsum_eq_sum_of_support_subset _ hsub]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul]
  have : ‖fourierMode n φ‖ = 1 := by
    unfold fourierMode
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  rw [this, mul_one]
theorem exists_translate_out {I : PeriodicData} (hI : IsPeriodic I) (ι : I.Carrier) :
    ∃ n : Fin 4 → ℤ, ι = I.translate n (Quot.out (I.mkQuot 1 ι)) := by
  have key : ∀ x y : I.Carrier, Relation.EqvGen (fun ι ι' : I.Carrier =>
      ∃ n : Fin 4 → ℤ, ι' = I.translate (1 • n) ι) x y → ∃ n : Fin 4 → ℤ, y = I.translate n x := by
    intro x y h
    induction h with
    | rel x y h =>
      obtain ⟨n, rfl⟩ := h
      exact ⟨1 • n, rfl⟩
    | refl x => exact ⟨0, (hI.translate_zero x).symm⟩
    | symm x y _ ih =>
      obtain ⟨n, rfl⟩ := ih
      refine ⟨-n, ?_⟩
      rw [← hI.translate_add, add_neg_cancel, hI.translate_zero]
    | trans x y z _ _ ih₁ ih₂ =>
      obtain ⟨n, rfl⟩ := ih₁
      obtain ⟨m, rfl⟩ := ih₂
      exact ⟨n + m, (hI.translate_add n m x).symm⟩
  exact key _ _ (Quot.eqvGen_exact (Quot.out_eq (I.mkQuot 1 ι)))
theorem euclidNormVec_neg (v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (-v) = TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem kernel_entries_bounded (L : ℕ) (I : PeriodicData) (hI : IsPeriodic I)
    (hFin : ∀ ι : I.Carrier,
      {κ : I.Carrier | TorusMetric.euclidNormVec (I.pos κ - I.pos ι) ≤ 2}.Finite)
    (T : (FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) → I.Carrier → I.Carrier → ℂ)
    (hT : KernelEntriesTrigPoly L I T)
    (hR : ∀ θ', HasRangeLeTwo I.pos (T θ'))
    (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) :
    ∃ C : ℝ, ∀ ι' ι, ‖T θ ι' ι‖ ≤ C := by
  classical
  have hbound : ∀ ι' ι : I.Carrier, ∃ c : ℝ, ∀ (θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
      (ζ : Fin 4 → ℤ), ‖T θ' (I.translate ζ ι') (I.translate ζ ι)‖ ≤ c := by
    intro ι' ι
    obtain ⟨P, hP, hval⟩ := hT ι' ι
    obtain ⟨c, hc⟩ := trigPoly_bounded hP
    exact ⟨c, fun θ' ζ => by rw [hval]; exact hc _⟩
  choose c hc using hbound
  have : Finite I.UnitQuot := hI.finite_quot
  let S : Set (I.Carrier × I.Carrier) := ⋃ q : I.UnitQuot,
    (fun κ => (Quot.out q, κ)) ''
      {κ : I.Carrier | TorusMetric.euclidNormVec (I.pos κ - I.pos (Quot.out q)) ≤ 2}
  have hS : S.Finite := Set.finite_iUnion fun q => (hFin _).image _
  obtain ⟨C, hC⟩ := (hS.image fun p => c p.1 p.2).bddAbove
  refine ⟨max C 0, fun ι' ι => ?_⟩
  by_cases hd : TorusMetric.euclidNormVec (I.pos ι' - I.pos ι) ≤ 2
  · obtain ⟨n, hn⟩ := exists_translate_out hI ι'
    set r := Quot.out (I.mkQuot 1 ι') with hr
    set κ := I.translate (-n) ι with hκ
    have hι : ι = I.translate n κ := by
      rw [hκ, ← hI.translate_add, neg_add_cancel, hI.translate_zero]
    have hmem : (r, κ) ∈ S := by
      refine Set.mem_iUnion.2 ⟨I.mkQuot 1 ι', κ, ?_, rfl⟩
      show TorusMetric.euclidNormVec (I.pos κ - I.pos r) ≤ 2
      have hk : I.pos κ = I.pos ι - castVec n := by
        rw [hκ, hI.pos_translate, sub_eq_add_neg]
        congr 1
        funext μ
        simp [castVec]
      have hp : I.pos ι' = I.pos r + castVec n := by
        conv_lhs => rw [hn]
        exact hI.pos_translate n r
      have e : I.pos κ - I.pos r = -(I.pos ι' - I.pos ι) := by
        rw [hk, hp]
        abel
      rw [e, euclidNormVec_neg]
      exact hd
    have h1 := hC ⟨(r, κ), hmem, rfl⟩
    have h2 := hc r κ θ n
    rw [← hι, ← hn] at h2
    exact (h2.trans h1).trans (le_max_left _ _)
  · rw [hR θ ι' ι hd, norm_zero]
    exact le_max_right _ _
theorem sum_smul_pauliFamily_mem (c : Fin 3 → ℂ) :
    ∑ b, c b • ComplexMatrix2.pauliFamily b ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_sum_smul (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, c b • ComplexMatrix2.pauliFamily b) = c a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
theorem adjointMatrix_pauliFamily (a : Fin 3) :
    ComplexMatrix2.adjointMatrix (ComplexMatrix2.pauliFamily a) = ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.pauliFamily_conjTranspose <;> assumption
theorem adjointMatrix_sum_smul (c : Fin 3 → ℂ) :
    ComplexMatrix2.adjointMatrix (∑ b, c b • ComplexMatrix2.pauliFamily b) =
      ∑ b, conj (c b) • ComplexMatrix2.pauliFamily b := by
  simp only [ComplexMatrix2.adjointMatrix, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
  exact Finset.sum_congr rfl fun b _ => by
    have := adjointMatrix_pauliFamily b
    simp only [ComplexMatrix2.adjointMatrix] at this
    rw [this]
    rfl
theorem pauliCoeff_im_eq_zero {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless)
    (hs : ComplexMatrix2.adjointMatrix X = X) (a : Fin 3) :
    (pauliCoeff a X).im = 0 := by
  have e := adjointMatrix_sum_smul fun b => pauliCoeff b X
  rw [sum_pauliCoeff_smul h, hs] at e
  have := congrArg (pauliCoeff a) e
  rw [pauliCoeff_sum_smul] at this
  exact Complex.conj_eq_iff_im.1 this.symm
section Operator
variable {σ : Type}
theorem ofCoords_injective {x y : L2Field σ}
    (h : ofCoords x = ofCoords y) : x = y := by
  apply lp.ext
  funext ι
  have := congrArg (pauliCoeff ι.1) (congrFun h ι.2)
  simpa [ofCoords, pauliCoeff_sum_smul] using this
theorem opOfMap_of_kernel (position : Fin 3 × σ → InfiniteLattice.AmbientSpace)
    (hOK : BoundedKernelOperator position) (K : Fin 3 × σ → Fin 3 × σ → ℂ) (C : ℝ)
    (hC : ∀ ι' ι, ‖K ι' ι‖ ≤ C)
    (hR : ∀ ι' ι, ¬ TorusMetric.euclidNormVec (position ι' - position ι) ≤ 2 → K ι' ι = 0)
    (M : (σ → ComplexMatrix2) → σ → ComplexMatrix2)
    (hgive : ∀ f : Fin 3 × σ → ℂ, applyKernel K f = toPauliCoeffs (M (ofPauliCoeffs f)))
    (hmem : ∀ (f : Fin 3 × σ → ℂ) (s : σ), M (ofPauliCoeffs f) s ∈ ComplexMatrix2.traceless) :
    (∀ v : L2Field σ, ofCoords (opOfMap M v) = M (ofCoords v)) ∧
    ((∀ ι' ι, K ι ι' = conj (K ι' ι)) → IsSelfAdjointOp (opOfMap M)) := by
  obtain ⟨T, hT, -, hsa⟩ := hOK C K hC hR
  have hval : ∀ v : L2Field σ, ofCoords (T v) = M (ofCoords v) := by
    intro v
    funext s
    have e : ∀ a, T v (a, s) = pauliCoeff a (M (ofCoords v) s) := fun a => by
      rw [(hT v (a, s)).2.2]
      exact congrFun (hgive v) (a, s)
    show ∑ a, T v (a, s) • ComplexMatrix2.pauliFamily a = _
    simp only [e]
    exact sum_pauliCoeff_smul (hmem v s)
  have hspec : ∀ v : L2Field σ, ofCoords (opOfMap M v) = M (ofCoords v) :=
    Classical.epsilon_spec (p := fun T : L2Field σ →L[ℂ] L2Field σ =>
      ∀ v : L2Field σ, ofCoords (T v) = M (ofCoords v)) ⟨T, hval⟩
  refine ⟨hspec, fun hs => ?_⟩
  have e : opOfMap M = T := by
    ext1 v
    exact ofCoords_injective ((hspec v).trans (hval v).symm)
  rw [e]
  exact hsa hs
end Operator
section Distances
open TorusMetric
theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_sub_le_two {x y z : Fin 4 → ℝ} (h₁ : euclidNormVec (x - z) ≤ 1)
    (h₂ : euclidNormVec (y - z) ≤ 1) : euclidNormVec (x - y) ≤ 2 := by
  have e : x - y = (x - z) + -(y - z) := by abel
  rw [e]
  refine (euclidNormVec_add_le _ _).trans ?_
  rw [euclidNormVec_neg]
  linarith
theorem meshAt_zero (L : ℕ) : meshAt L 0 0 = 1 := by
  simp [meshAt]
theorem euclidNormVec_zero : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
theorem euclidNormVec_axisStep (L : ℕ) (μ : Fin 4) :
    euclidNormVec ((InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) :
      InfiniteLattice.AmbientSpace) = 1 := by
  show euclidNormVec (Pi.single μ (meshAt L 0 0)) = 1
  rw [meshAt_zero]
  fin_cases μ <;> simp [euclidNormVec, Pi.single_apply]
theorem endpoint_near_initial {L : ℕ} (b : FullSpace.PositiveEdge (meshAt L 0 0))
    {c : FullSpace.Vertex L 0 0} (h : c = b.1.terminal ∨ c = b.1.initial) :
    euclidNormVec ((c : InfiniteLattice.AmbientSpace) - b.1.initial) ≤ 1 := by
  rcases h with rfl | rfl
  · obtain ⟨μ, hμ⟩ := b.2
    have e : ((b.1.terminal : InfiniteLattice.AmbientSpace) - b.1.initial) =
        ((InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) :
          InfiniteLattice.AmbientSpace) := by
      rw [← hμ]
      rfl
    rw [e, euclidNormVec_axisStep]
  · simp [euclidNormVec_zero]
theorem faceEdge_near_corner {L : ℕ} (p : FullSpace.Face L 0 0)
    {b : FullSpace.Edge L 0 0} (h : b ∈ FullSpace.faceEdges p) :
    euclidNormVec ((b.initial : InfiniteLattice.AmbientSpace) - p.corner) ≤ 1 := by
  have step_near : ∀ μ : Fin 4, euclidNormVec
      (((p.corner + InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) :
        InfiniteLattice.AmbientSpace) - p.corner) ≤ 1 := by
    intro μ
    have := euclidNormVec_axisStep L μ
    simp only [AddSubgroup.coe_add, add_sub_cancel_left]
    exact this.le
  simp only [FullSpace.faceEdges, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · simp [InfiniteLattice.Link.forwardFrom, euclidNormVec_zero]
  · exact step_near _
  · exact step_near _
  · simp [InfiniteLattice.Link.forwardFrom, euclidNormVec_zero]
end Distances
section Forms
variable {L : ℕ}
theorem not_opposite_positive (b : FullSpace.Edge L 0 0) (h : b.IsPositivelyOriented) :
    ¬ b.opposite.IsPositivelyOriented := by
  rintro ⟨ν, hν⟩
  obtain ⟨μ, hμ⟩ := h
  have e : (InfiniteLattice.axisStep (meshAt L 0 0) ν : FullSpace.Vertex L 0 0) =
      -InfiniteLattice.axisStep (meshAt L 0 0) μ := by
    rw [← hν, ← hμ]
    show b.initial - b.terminal = _
    abel
  have := congrArg (fun x : FullSpace.Vertex L 0 0 => (x : InfiniteLattice.AmbientSpace) μ) e
  have hs : ∀ κ : Fin 4, ((InfiniteLattice.axisStep (meshAt L 0 0) κ : FullSpace.Vertex L 0 0) :
      InfiniteLattice.AmbientSpace) = Pi.single κ (1 : ℝ) := fun κ => by
    show (Pi.single κ (meshAt L 0 0) : InfiniteLattice.AmbientSpace) = _
    rw [meshAt_zero]
  simp only [AddSubgroup.coe_neg, Pi.neg_apply, hs] at this
  by_cases hh : μ = ν
  · subst hh
    simp at this
    linarith
  · simp [hh] at this
theorem formOfPositiveValues_mem (g : PosEdge L 0 0 → ComplexMatrix2)
    (hg : ∀ b, g b ∈ ComplexMatrix2.traceless) :
    formOfPositiveValues g ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by
  classical
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [formOfPositiveValues, FullSpace.extendOddly, if_pos hb, dif_pos hb]
    exact hg _
  · have hrr : b.opposite.opposite = b := rfl
    have key : ∀ f : FullSpace.Edge L 0 0 → ComplexMatrix2,
        (∀ c, ¬ c.IsPositivelyOriented → f c = 0) →
        FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by
      intro f hf
      simp only [FullSpace.extendOddly]
      by_cases hb : b.IsPositivelyOriented
      · rw [if_neg (not_opposite_positive b hb), if_pos hb, hrr]
      · by_cases hr : b.opposite.IsPositivelyOriented
        · rw [if_pos hr, if_neg hb, neg_neg]
        · rw [if_neg hr, if_neg hb, hrr, hf b hb, hf _ hr]
          simp
    exact key _ fun c hc => dif_neg hc
end Forms
section Kernels
open UnitGaugeDirections (IsUniqueRowFiniteKernelAction basisFunction)
open CovDiffTransposes (matrixKernel LatticeTransposeData)
open HessianKernel (SupportedOnRelation IsSymm)
theorem applyKernel_basisFunction {N : Type} (K : N → N → ℂ) (ι' ι : N) :
    applyKernel K (basisFunction ι) ι' = K ι' ι := by
  classical
  show ∑' κ, K ι' κ * basisFunction ι κ = _
  rw [tsum_eq_single ι]
  · simp [basisFunction]
  · intro κ hκ
    simp [basisFunction, hκ]
theorem kernelOfMap_spec {N : Type} {M : (N → ℂ) → N → ℂ}
    (h : IsUniqueRowFiniteKernelAction M) :
    Represents (kernelOfMap M) M ∧ ∀ ι' ι, kernelOfMap M ι' ι = M (basisFunction ι) ι' := by
  obtain ⟨T, hg, hu, he, -⟩ := h
  have hk : Represents (kernelOfMap M) M :=
    Classical.epsilon_spec (p := fun T => Represents T M) ⟨T, hg⟩
  refine ⟨hk, fun ι' ι => ?_⟩
  rw [hu _ hk, he]
theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (f : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs f) = f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
variable {L : ℕ}
theorem toPauliCoeffs_restrict_formOfPositiveValues (f : EdgeIndex L → ℂ) :
    toPauliCoeffs (FullSpace.restrictToPositiveEdges (formOfPositiveValues (ofPauliCoeffs f))) = f := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.edge_coeffs_ofCoeffs <;> assumption
theorem ofPauliCoeffs_mem {σ : Type} (f : Fin 3 × σ → ℂ) :
    ofPauliCoeffs f ∈ Matrices.GroupLieProduct.tracelessFunctions σ := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.ofPauliCoeffs_mem <;> assumption
theorem tracelessFunctions_apply_mem {σ : Type} {f : σ → ComplexMatrix2}
    (h : f ∈ Matrices.GroupLieProduct.tracelessFunctions σ) (s : σ) :
    f s ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.PauliCoefficientNorm.apply_mem_traceless <;> assumption
theorem formOfPositiveValues_ofPauliCoeffs_mem (f : EdgeIndex L → ℂ) :
    formOfPositiveValues (ofPauliCoeffs f) ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.edge_ofCoeffs_mem <;> assumption
def covDiffEntry (U : FullSpace.Edge L 0 0 → ComplexMatrix2) (ι' : EdgeIndex L)
    (ι : VertexIndex L) : ℂ :=
  pauliCoeff ι'.1
    (FullSpace.covDiff U (ofPauliCoeffs (basisFunction ι)) ι'.2.1)
theorem covDiffEntry_eq_zero (U : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (ι' : EdgeIndex L) (ι : VertexIndex L)
    (h : ι.2 ≠ ι'.2.1.terminal) (h' : ι.2 ≠ ι'.2.1.initial) : covDiffEntry U ι' ι = 0 := by
  classical
  have hl : ∀ y : FullSpace.Vertex L 0 0, y ≠ ι.2 →
      ofPauliCoeffs (basisFunction ι) y = 0 := by
    intro y hy
    simp only [ofPauliCoeffs, basisFunction]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg (fun e => hy (congrArg Prod.snd e)), zero_smul]
  have e : FullSpace.covDiff U (ofPauliCoeffs (basisFunction ι)) ι'.2.1 = 0 := by
    simp only [FullSpace.covDiff, FullSpace.extendOddly, if_pos ι'.2.2]
    rw [hl _ h.symm, hl _ h'.symm]
    simp [ComplexMatrix2.conjugateBy]
  rw [covDiffEntry, e, pauliCoeff_zero]
abbrev TransposeData (U : FullSpace.Edge L 0 0 → ComplexMatrix2) : Prop :=
  LatticeTransposeData (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
    (vertexCoordinate (FullSpace.Face L 0 0)) (FullSpace.covDiff U)
    FullSpace.vertexCoboundary FullSpace.edgeCoboundary
    (FullSpace.complexHessianOperator U) (FullSpace.complexHessianKernel U)
theorem matrixKernel_eq (U : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    matrixKernel (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
      (FullSpace.covDiff U) = covDiffEntry U := by
  classical
  funext ι' ι
  show pauliCoeff ι'.1 (FullSpace.covDiff U (ofPauliCoeffs _) ι'.2.1) =
    pauliCoeff ι'.1
      (FullSpace.covDiff U (ofPauliCoeffs (basisFunction (N := VertexIndex L) ι)) ι'.2.1)
  refine congrArg (fun f : VertexIndex L → ℂ =>
    pauliCoeff ι'.1 (FullSpace.covDiff U (ofPauliCoeffs f) ι'.2.1)) ?_
  funext κ
  unfold basisFunction
  by_cases h : κ = ι
  · exact (if_pos h).trans (if_pos h).symm
  · exact (if_neg h).trans (if_neg h).symm
theorem gaugeLaplacian_kernel_eq {U : FullSpace.Edge L 0 0 → ComplexMatrix2} (hX : TransposeData U)
    (hK : IsUniqueRowFiniteKernelAction
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L 0 0))
        (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.gaugeLaplacian U)))
    (ι' ι : VertexIndex L) :
    PauliComponentsOfSymmetricKernel.kernel (vertexCoordinate (FullSpace.Vertex L 0 0))
        (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.gaugeLaplacian U) ι' ι =
      ∑' m : EdgeIndex L, covDiffEntry U m ι' * covDiffEntry U m ι := by
  refine ((kernelOfMap_spec hK).2 ι' ι).trans ?_
  have h := (hX.transposeComp_represents.2 (ofPauliCoeffs (basisFunction ι))
    (ofPauliCoeffs_mem (basisFunction ι)) ι').2
  rw [matrixKernel_eq] at h
  have h' : toPauliCoeffs (FullSpace.gaugeLaplacian U (ofPauliCoeffs (basisFunction ι))) ι' =
      applyKernel (fun κ' κ : VertexIndex L => ∑' m : EdgeIndex L,
        covDiffEntry U m κ' * covDiffEntry U m κ)
        (toPauliCoeffs (ofPauliCoeffs (basisFunction ι))) ι' := h
  rw [toPauliCoeffs_ofPauliCoeffs, applyKernel_basisFunction] at h'
  exact h'
theorem massiveHessian_kernel_eq {U : FullSpace.Edge L 0 0 → ComplexMatrix2} (hX : TransposeData U)
    (hK : IsUniqueRowFiniteKernelAction
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs (FullSpace.edgePauliCoordinates L 0 0) (FullSpace.edgePauliCoordinates L 0 0)
        (FullSpace.massiveHessian U)))
    (ι' ι : EdgeIndex L) :
    PauliComponentsOfSymmetricKernel.kernel (FullSpace.edgePauliCoordinates L 0 0) (FullSpace.edgePauliCoordinates L 0 0)
        (FullSpace.massiveHessian U) ι' ι =
      FullSpace.complexHessianKernel U ι' ι +
        ∑' m : VertexIndex L, covDiffEntry U ι' m * covDiffEntry U ι m := by
  classical
  refine ((kernelOfMap_spec hK).2 ι' ι).trans ?_
  have hmem := formOfPositiveValues_ofPauliCoeffs_mem (L := L) (basisFunction ι)
  set B : FullSpace.Edge L 0 0 → ComplexMatrix2 :=
    formOfPositiveValues (ofPauliCoeffs (basisFunction ι)) with hB
  have hA₂ : FullSpace.complexHessianOperator U B ∈ FullSpace.complexEdgeForms (meshAt L 0 0) :=
    (hX.operator_mem B hmem).2.1
  have hD : FullSpace.covDiff U (FullSpace.covDiffAdjoint U B) ∈
      FullSpace.complexEdgeForms (meshAt L 0 0) := (hX.compTranspose_mem B hmem).2
  have hc : toPauliCoeffs (FullSpace.restrictToPositiveEdges B) = basisFunction ι :=
    toPauliCoeffs_restrict_formOfPositiveValues _
  have h₀ := (hX.compTranspose_represents.2 B hmem ι').2
  rw [matrixKernel_eq] at h₀
  have h : toPauliCoeffs (FullSpace.restrictToPositiveEdges
      (FullSpace.covDiff U (FullSpace.covDiffAdjoint U B))) ι' =
      applyKernel (fun κ' κ : EdgeIndex L => ∑' m : VertexIndex L,
        covDiffEntry U κ' m * covDiffEntry U κ m)
        (toPauliCoeffs (FullSpace.restrictToPositiveEdges B)) ι' := h₀
  rw [hc, applyKernel_basisFunction] at h
  have hA : pauliCoeff ι'.1 (FullSpace.complexHessianOperator U B ι'.2.1) =
      FullSpace.complexHessianKernel U ι' ι := by
    simp only [FullSpace.complexHessianOperator, FullSpace.extendOddly, if_pos ι'.2.2,
      dif_pos ι'.2.2]
    refine (pauliCoeff_sum_smul (fun a => _) ι'.1).trans ?_
    rw [hc]
    exact applyKernel_basisFunction _ ι' ι
  show pauliCoeff ι'.1 (FullSpace.complexHessianOperator U B ι'.2.1 +
    FullSpace.covDiff U (FullSpace.covDiffAdjoint U B) ι'.2.1) = _
  rw [pauliCoeff_add (hA₂.1 _ ι'.2.2) (hD.1 _ ι'.2.2), hA]
  exact congrArg _ h
theorem gaugeLaplacian_range {U : FullSpace.Edge L 0 0 → ComplexMatrix2} (hX : TransposeData U)
    (hK : IsUniqueRowFiniteKernelAction
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L 0 0))
        (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.gaugeLaplacian U))) :
    HasRangeLeTwo (vertexPos L)
      (PauliComponentsOfSymmetricKernel.kernel (vertexCoordinate (FullSpace.Vertex L 0 0))
        (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.gaugeLaplacian U)) := by
  intro ι' ι hd
  change ¬ TorusMetric.euclidNormVec
    ((ι'.2 : InfiniteLattice.AmbientSpace) - (ι.2 : InfiniteLattice.AmbientSpace)) ≤ 2 at hd
  rw [gaugeLaplacian_kernel_eq hX hK ι' ι]
  refine (tsum_congr fun m : EdgeIndex L => ?_).trans tsum_zero
  by_contra hne
  have end_of : ∀ κ : VertexIndex L, covDiffEntry U m κ ≠ 0 →
      κ.2 = m.2.1.terminal ∨ κ.2 = m.2.1.initial := by
    intro κ hκ
    by_contra hh
    exact hκ (covDiffEntry_eq_zero U m κ (not_or.1 hh).1 (not_or.1 hh).2)
  exact hd (euclidNormVec_sub_le_two (endpoint_near_initial m.2 (end_of ι' (left_ne_zero_of_mul hne)))
    (endpoint_near_initial m.2 (end_of ι (right_ne_zero_of_mul hne))))
theorem massiveHessian_range {U : FullSpace.Edge L 0 0 → ComplexMatrix2} (hX : TransposeData U)
    (hK : IsUniqueRowFiniteKernelAction
      (PauliComponentsOfSymmetricKernel.mapOnCoeffs (FullSpace.edgePauliCoordinates L 0 0) (FullSpace.edgePauliCoordinates L 0 0)
        (FullSpace.massiveHessian U)))
    (hA : SupportedOnRelation (FullSpace.complexHessianKernel U)
      (fun b b' : FullSpace.PositiveEdge (meshAt L 0 0) =>
        ∃ p : FullSpace.Face L 0 0,
          b.1 ∈ FullSpace.faceEdges p ∧ b'.1 ∈ FullSpace.faceEdges p)) :
    HasRangeLeTwo (edgePos L)
      (PauliComponentsOfSymmetricKernel.kernel (FullSpace.edgePauliCoordinates L 0 0) (FullSpace.edgePauliCoordinates L 0 0)
        (FullSpace.massiveHessian U)) := by
  intro ι' ι hd
  change ¬ TorusMetric.euclidNormVec ((ι'.2.1.initial : InfiniteLattice.AmbientSpace) -
    (ι.2.1.initial : InfiniteLattice.AmbientSpace)) ≤ 2 at hd
  rw [massiveHessian_kernel_eq hX hK ι' ι]
  have h₁ : FullSpace.complexHessianKernel U ι' ι = 0 := by
    refine hA ι' ι ?_
    rintro ⟨p, hb, hb'⟩
    exact hd (euclidNormVec_sub_le_two (faceEdge_near_corner p hb) (faceEdge_near_corner p hb'))
  have h₂ : ∑' m : VertexIndex L, covDiffEntry U ι' m * covDiffEntry U ι m = 0 := by
    refine (tsum_congr fun m : VertexIndex L => ?_).trans tsum_zero
    by_contra hne
    have end_of : ∀ κ : EdgeIndex L, covDiffEntry U κ m ≠ 0 →
        TorusMetric.euclidNormVec ((κ.2.1.initial : InfiniteLattice.AmbientSpace) -
          (m.2 : InfiniteLattice.AmbientSpace)) ≤ 1 := by
      intro κ hκ
      have hend : m.2 = κ.2.1.terminal ∨ m.2 = κ.2.1.initial := by
        by_contra hh
        exact hκ (covDiffEntry_eq_zero U κ m (not_or.1 hh).1 (not_or.1 hh).2)
      have := endpoint_near_initial κ.2 hend
      rw [← euclidNormVec_neg, neg_sub]
      exact this
    exact hd (euclidNormVec_sub_le_two (end_of ι' (left_ne_zero_of_mul hne))
      (end_of ι (right_ne_zero_of_mul hne)))
  rw [h₁, h₂, add_zero]
theorem basisVec_coe {J : Type} (ι : J) :
    (⇑(basisVec ι) : J → ℂ) = basisFunction ι := by
  classical
  funext κ
  by_cases h : κ = ι
  · subst h
    simp [basisVec, basisFunction, lp.single_apply]
  · simp [basisVec, basisFunction, lp.single_apply, h]
theorem isL2Traceless_basisFunction {σ : Type} (hc : CoordsIsometry σ) (ι : Fin 3 × σ) :
    IsL2Traceless (ofPauliCoeffs (basisFunction ι)) := by
  have h := (hc.2.2.1 (basisVec ι)).1
  have e : ofCoords (basisVec ι) = ofPauliCoeffs (basisFunction ι) :=
    congrArg ofPauliCoeffs (basisVec_coe ι)
  rwa [e] at h
theorem adjointMatrix_ofPauliCoeffs_basisFunction {σ : Type} (ι : Fin 3 × σ) (s : σ) :
    ComplexMatrix2.adjointMatrix (ofPauliCoeffs (basisFunction ι) s) =
      ofPauliCoeffs (basisFunction ι) s := by
  classical
  show ComplexMatrix2.adjointMatrix (∑ b, basisFunction ι (b, s) • ComplexMatrix2.pauliFamily b) = _
  rw [adjointMatrix_sum_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : conj (basisFunction ι (b, s)) = basisFunction ι (b, s) := by
    unfold basisFunction
    split_ifs <;> simp
  rw [this]
theorem fieldStar_formOfPositiveValues (g : PosEdge L 0 0 → ComplexMatrix2)
    (hg : ∀ b, ComplexMatrix2.adjointMatrix (g b) = g b) :
    fieldStar (formOfPositiveValues g) = formOfPositiveValues g := by
  classical
  funext b
  simp only [fieldStar, formOfPositiveValues, FullSpace.extendOddly]
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb, dif_pos hb, hg]
  · rw [if_neg hb]
    by_cases hr : b.opposite.IsPositivelyOriented
    · rw [dif_pos hr, ComplexMatrix2.adjointMatrix, Matrix.conjTranspose_neg]
      exact congrArg Neg.neg (hg _)
    · rw [dif_neg hr]
      simp [ComplexMatrix2.adjointMatrix]
end Kernels
theorem abelianOperators_local_selfAdjoint
    (hEntries : AbelianKernelEntries.EntriesAreTrigPolynomials)
    (hSymmetries : AbelianOperatorSymmetries)
    (hPlaquettes : AbelianFieldPlaquettes.Claim)
    (hGauge : UnitGaugeDirections.Claim)
    (hSquare : UnitLatticeL2Statement)
    (hSecond : HessianKernel.KernelProperties)
    (hTransposes : CovDiffTransposes.Claim)
    (hIndex : TowerIndexSets.Claim) :
    AbelianOperatorsLocalSelfAdjoint := by
  intro L hL θ
  have hU : ∀ θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      FullSpace.abelianLinkField θ' ∈
        FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup := fun θ' => by
    have h := (hPlaquettes L hL θ').abelianLinkField_mem
    exact ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.1 (h.1 b)).2, h.2⟩
  have hG := hGauge L hL
  have hX : ∀ θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ,
      TransposeData (FullSpace.abelianLinkField θ') :=
    fun θ' => ((hTransposes L hL 0 0 le_rfl).2 _ (hU θ')).1
  have hA := fun θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ =>
    (hSecond L hL 0 0 le_rfl).2 _ (hU θ')
  have hF := fun θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ => (hG.2 _ (hU θ')).2.2.1
  have hKs := fun θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ => (hG.2 _ (hU θ')).2.2.2.1
  have hKb := fun θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ => (hG.2 _ (hU θ')).2.2.2.2
  obtain ⟨-, ⟨hcS, -, -, hiS, -, hoS⟩, ⟨hcB, -, -, hiB, -, hoB⟩⟩ := hSquare.2 L
  have rS : ∀ θ', HasRangeLeTwo (vertexPos L) (abelianLaplacianKernel θ') :=
    fun θ' => gaugeLaplacian_range (hX θ') (hKs θ')
  have rB : ∀ θ', HasRangeLeTwo (edgePos L) (abelianHessianKernel θ') :=
    fun θ' => massiveHessian_range (hX θ') (hKb θ') (hA θ').2.1
  obtain ⟨CS, hCS⟩ := kernel_entries_bounded L (colourVertices L 0 0) (hIndex L hL 0 0 le_rfl).1
    (fun ι => (hiS.2 ι.2).1) abelianLaplacianKernel (hEntries L hL).laplacian rS θ
  obtain ⟨CB, hCB⟩ := kernel_entries_bounded L (colourEdges L 0 0) (hIndex L hL 0 0 le_rfl).2.1
    (fun ι => (hiB.2 ι.2.1.initial).1) abelianHessianKernel (hEntries L hL).hessian rB θ
  have hSym := hSymmetries L hL θ
  have realS : ∀ ι' ι : VertexIndex L, (abelianLaplacianKernel θ ι' ι).im = 0 := by
    intro ι' ι
    have hss := isL2Traceless_basisFunction hcS ι
    have hstar := hSym.laplacian_star _ hss
    have hse : fieldStar (ofPauliCoeffs (UnitGaugeDirections.basisFunction ι)) =
        ofPauliCoeffs (UnitGaugeDirections.basisFunction ι) :=
      funext (adjointMatrix_ofPauliCoeffs_basisFunction ι)
    rw [hse] at hstar
    have hmem : FullSpace.abelianGaugeLaplacian θ
        (ofPauliCoeffs (UnitGaugeDirections.basisFunction ι)) ι'.2 ∈ ComplexMatrix2.traceless := by
      exact tracelessFunctions_apply_mem
        ((hF θ).1 _ (ofPauliCoeffs_mem (UnitGaugeDirections.basisFunction ι))).2 ι'.2
    have e : abelianLaplacianKernel θ ι' ι = pauliCoeff ι'.1 (FullSpace.abelianGaugeLaplacian θ
        (ofPauliCoeffs (UnitGaugeDirections.basisFunction ι)) ι'.2) :=
      (kernelOfMap_spec (hKs θ)).2 ι' ι
    rw [e]
    exact pauliCoeff_im_eq_zero hmem (congrFun hstar ι'.2).symm ι'.1
  have realB : ∀ ι' ι : EdgeIndex L, (abelianHessianKernel θ ι' ι).im = 0 := by
    intro ι' ι
    have hB := formOfPositiveValues_ofPauliCoeffs_mem (L := L) (UnitGaugeDirections.basisFunction ι)
    set B : FullSpace.Edge L 0 0 → ComplexMatrix2 :=
      formOfPositiveValues (ofPauliCoeffs (UnitGaugeDirections.basisFunction ι))
      with hBdef
    have hon : FullSpace.restrictToPositiveEdges B =
        ofPauliCoeffs (UnitGaugeDirections.basisFunction ι) := by
      funext b
      simp only [FullSpace.restrictToPositiveEdges, hBdef, formOfPositiveValues,
        FullSpace.extendOddly, if_pos b.2, dif_pos b.2]
    have hss : B ∈ FullSpace.l2Forms (meshAt L 0 0) :=
      ⟨hB, by rw [hon]; exact isL2Traceless_basisFunction hcB ι⟩
    have hstar := hSym.hessian_star B hss
    have hse : fieldStar B = B :=
      fieldStar_formOfPositiveValues _ (adjointMatrix_ofPauliCoeffs_basisFunction ι)
    rw [hse] at hstar
    have hmem : FullSpace.abelianMassiveHessian θ B ι'.2.1 ∈ ComplexMatrix2.traceless :=
      ((hF θ).2 B hB).2.2.2.1 _ ι'.2.2
    have e : abelianHessianKernel θ ι' ι =
        pauliCoeff ι'.1 (FullSpace.abelianMassiveHessian θ B ι'.2.1) :=
      (kernelOfMap_spec (hKb θ)).2 ι' ι
    rw [e]
    exact pauliCoeff_im_eq_zero hmem (congrFun hstar ι'.2.1).symm ι'.1
  have symS : ∀ ι' ι : VertexIndex L,
      abelianLaplacianKernel θ ι' ι = abelianLaplacianKernel θ ι ι' := by
    intro ι' ι
    have e := gaugeLaplacian_kernel_eq (hX θ) (hKs θ)
    refine (e ι' ι).trans (Eq.trans ?_ (e ι ι').symm)
    exact tsum_congr fun m => mul_comm _ _
  have symB : ∀ ι' ι : EdgeIndex L,
      abelianHessianKernel θ ι' ι = abelianHessianKernel θ ι ι' := by
    intro ι' ι
    have e := massiveHessian_kernel_eq (hX θ) (hKb θ)
    refine (e ι' ι).trans (Eq.trans ?_ (e ι ι').symm)
    rw [(hA θ).2.2.2.2.2 ι' ι]
    exact congrArg _ (tsum_congr fun m => mul_comm _ _)
  have opS := opOfMap_of_kernel (vertexPos L) hoS (abelianLaplacianKernel θ) CS hCS (rS θ)
    (FullSpace.abelianGaugeLaplacian θ) (fun f => ((kernelOfMap_spec (hKs θ)).1 f).2)
    (fun f s => tracelessFunctions_apply_mem ((hF θ).1 _ (ofPauliCoeffs_mem f)).2 s)
  have opB := opOfMap_of_kernel (edgePos L) hoB (abelianHessianKernel θ) CB hCB (rB θ)
    (fun g b => FullSpace.abelianMassiveHessian θ (formOfPositiveValues g) b.1)
    (fun f => ((kernelOfMap_spec (hKb θ)).1 f).2)
    (fun f b => ((hF θ).2 _ (formOfPositiveValues_ofPauliCoeffs_mem f)).2.2.2.1 _ b.2)
  exact
    { laplacian_range := rS θ
      hessian_range := rB θ
      laplacian_apply := opS.1
      hessian_apply := opB.1
      laplacian_isSelfAdjoint := opS.2 fun ι' ι =>
        (symS ι ι').trans (Complex.conj_eq_iff_im.2 (realS ι' ι)).symm
      hessian_isSelfAdjoint := opB.2 fun ι' ι =>
        (symB ι ι').trans (Complex.conj_eq_iff_im.2 (realB ι' ι)).symm
      laplacian_im := realS
      hessian_im := realB
      laplacian_symm := symS
      hessian_symm := symB }
end YangMills.Construction.Tower.AbelianOperatorsLocalSelfAdjointProof
end
