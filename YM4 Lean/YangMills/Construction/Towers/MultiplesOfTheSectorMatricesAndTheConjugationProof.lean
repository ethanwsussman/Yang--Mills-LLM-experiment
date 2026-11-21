import YangMills.Construction.Towers.CovariantShiftsOfAnAbelianFieldProof
import YangMills.Construction.Towers.LogarithmsOfTheAbelianOperatorsProof
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.OneLoopNotation
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Matrices
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.WeightMultiplesProof
open SectorDecomposition
section PauliMatrices
theorem raisingPauli_eq : raisingPauli = !![0, 1; 0, 0] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.raisingPauli_eq_matrix <;> assumption
theorem loweringPauli_eq : loweringPauli = !![0, 0; 1, 0] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.loweringPauli_eq_matrix <;> assumption
theorem isWeightMatrix_mem_traceless {t : ComplexMatrix2} (ht : IsWeightMatrix t) :
    t ∈ ComplexMatrix2.traceless := by
  show ComplexMatrix2.fullTrace t = 0
  rcases ht with rfl | rfl | rfl
  · rw [ComplexMatrix2.pauliFamily_apply.2.2]
    simp [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
  · rw [raisingPauli_eq]
    simp [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
  · rw [loweringPauli_eq]
    simp [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
theorem adjointMatrix_raisingPauli : ComplexMatrix2.adjointMatrix raisingPauli = loweringPauli := by
  rw [raisingPauli_eq, loweringPauli_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ComplexMatrix2.adjointMatrix, Matrix.conjTranspose_apply]
theorem adjointMatrix_loweringPauli : ComplexMatrix2.adjointMatrix loweringPauli = raisingPauli := by
  rw [raisingPauli_eq, loweringPauli_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ComplexMatrix2.adjointMatrix, Matrix.conjTranspose_apply]
theorem halfTrace_third :
    ComplexMatrix2.halfTrace
      (ComplexMatrix2.adjointMatrix (ComplexMatrix2.pauliFamily 2) * ComplexMatrix2.pauliFamily 2) = 1 := by
  rw [ComplexMatrix2.pauliFamily_apply.2.2]
  simp [ComplexMatrix2.adjointMatrix, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  norm_num
theorem halfTrace_raising :
    ComplexMatrix2.halfTrace (ComplexMatrix2.adjointMatrix raisingPauli * raisingPauli) = 1 / 2 := by
  rw [raisingPauli_eq]
  simp [ComplexMatrix2.adjointMatrix, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
theorem halfTrace_lowering :
    ComplexMatrix2.halfTrace (ComplexMatrix2.adjointMatrix loweringPauli * loweringPauli) = 1 / 2 := by
  rw [loweringPauli_eq]
  simp [ComplexMatrix2.adjointMatrix, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
theorem isWeightMatrix_halfTrace_pos {t : ComplexMatrix2} (ht : IsWeightMatrix t) :
    ∃ k : ℝ, 0 < k ∧ ComplexMatrix2.halfTrace (ComplexMatrix2.adjointMatrix t * t) = (k : ℂ) := by
  rcases ht with rfl | rfl | rfl
  · exact ⟨1, one_pos, by rw [halfTrace_third]; simp⟩
  · exact ⟨1 / 2, by norm_num, by rw [halfTrace_raising]; simp⟩
  · exact ⟨1 / 2, by norm_num, by rw [halfTrace_lowering]; simp⟩
theorem adjointMatrix_smul (c : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.adjointMatrix (c • X) = conj c • ComplexMatrix2.adjointMatrix X := by
  simp [ComplexMatrix2.adjointMatrix, Matrix.conjTranspose_smul]
theorem halfTraceProduct_smul_re (c : ℂ) (t : ComplexMatrix2) (k : ℝ)
    (hk : ComplexMatrix2.halfTrace (ComplexMatrix2.adjointMatrix t * t) = (k : ℂ)) :
    (halfTraceProduct (c • t) (c • t)).re = ‖c‖ ^ 2 * k := by
  have e : halfTraceProduct (c • t) (c • t) = ((‖c‖ ^ 2 * k : ℝ) : ℂ) := by
    have e1 : ComplexMatrix2.adjointMatrix (c • t) * (c • t) =
        (conj c * c) • (ComplexMatrix2.adjointMatrix t * t) := by
      rw [adjointMatrix_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have e2 : ComplexMatrix2.halfTrace ((conj c * c) • (ComplexMatrix2.adjointMatrix t * t)) =
        (conj c * c) * ComplexMatrix2.halfTrace (ComplexMatrix2.adjointMatrix t * t) := by
      simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul, smul_eq_mul]
      ring
    unfold halfTraceProduct
    rw [e1, e2, hk, Complex.conj_mul']
    push_cast
    ring
  rw [e, Complex.ofReal_re]
end PauliMatrices
section StarOperation
variable {σ : Type}
theorem ofCoords_injective (hC : CoordsIsometry σ) {f g : L2Field σ}
    (h : ofCoords f = ofCoords g) : f = g := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.ofCoords_injective <;> assumption
theorem ofCoords_pointwiseStar (hC : CoordsIsometry σ) (hS : StarProperties σ)
    (f : L2Field σ) :
    ofCoords (pointwiseStar f) = fieldStar (ofCoords f) :=
  Classical.epsilon_spec (hC.2.2.2.1 _ (hS _ (hC.2.2.1 f).1).2.2.1)
theorem pointwiseStar_apply (hC : CoordsIsometry σ) (hS : StarProperties σ)
    (f : L2Field σ) (ι : Fin 3 × σ) : pointwiseStar f ι = conj (f ι) := by
  have h1 := (hC.2.2.1 (pointwiseStar f)).2 ι
  rw [ofCoords_pointwiseStar hC hS] at h1
  rw [← h1, (hS _ (hC.2.2.1 f).1).2.1 ι, (hC.2.2.1 f).2 ι]
theorem starInvolutionFacts_of (hC : CoordsIsometry σ) (hS : StarProperties σ) :
    StarInvolutionFacts σ where
  ofCoords_eq_fieldStar := ofCoords_pointwiseStar hC hS
  isConjLinear := by
    refine ⟨fun f f' => lp.ext (funext fun ι => ?_), fun s f => lp.ext (funext fun ι => ?_)⟩
    · simp [pointwiseStar_apply hC hS]
    · simp [pointwiseStar_apply hC hS]
  norm_eq := by
    intro f
    have hp : 0 < (2 : ENNReal).toReal := by norm_num
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    simp [pointwiseStar_apply hC hS]
  involutive := by
    intro f
    refine lp.ext (funext fun ι => ?_)
    simp [pointwiseStar_apply hC hS]
  apply_eq_conj := pointwiseStar_apply hC hS
  basisVec_fixed := by
    intro ι
    refine lp.ext (funext fun ι' => ?_)
    rw [pointwiseStar_apply hC hS]
    unfold basisVec
    by_cases h : ι' = ι
    · subst h
      simp
    · simp [lp.single_apply, h]
end StarOperation
section WeightMultiples
variable {L N' : ℕ} {σ : Type}
def coeffAt (e : FullSpace.Vertex L 0 0 × Fin N' ≃ σ) (v : VectorL2 L N') (s : σ) : ℂ :=
  v (e.symm s).1 (e.symm s).2
theorem coeffAt_apply (e : FullSpace.Vertex L 0 0 × Fin N' ≃ σ) (v : VectorL2 L N')
    (p : FullSpace.Vertex L 0 0 × Fin N') : coeffAt e v (e p) = v p.1 p.2 := by
  simp [coeffAt]
theorem summable_sq_pairs (hV : VectorL2Description L N') (v : VectorL2 L N') :
    Summable fun p : FullSpace.Vertex L 0 0 × Fin N' => ‖v p.1 p.2‖ ^ 2 := by
  rw [summable_prod_of_nonneg (fun _ => by positivity)]
  refine ⟨fun x => (hasSum_fintype _).summable, ?_⟩
  simp only [tsum_fintype]
  exact (hV.1 v).1 (lp.memℓp v)
theorem summable_sq_coeffAt (hV : VectorL2Description L N')
    (e : FullSpace.Vertex L 0 0 × Fin N' ≃ σ) (v : VectorL2 L N') :
    Summable fun s => ‖coeffAt e v s‖ ^ 2 :=
  (e.symm.summable_iff (f := fun p : FullSpace.Vertex L 0 0 × Fin N' => ‖v p.1 p.2‖ ^ 2)).2
    (summable_sq_pairs hV v)
theorem exists_ofCoords_eq_smul (hV : VectorL2Description L N') (hC : CoordsIsometry σ)
    (hM : ScalarMultipleInner σ) (e : FullSpace.Vertex L 0 0 × Fin N' ≃ σ)
    (v : VectorL2 L N') {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∃ f : L2Field σ, ∀ p : FullSpace.Vertex L 0 0 × Fin N',
      ofCoords f (e p) = v p.1 p.2 • X := by
  have hs := summable_sq_coeffAt hV e v
  obtain ⟨f, hf⟩ := hC.2.2.2.1 _ (hM X hX _ _ hs hs).1
  refine ⟨f, fun p => ?_⟩
  rw [hf]
  exact congrArg (· • X) (coeffAt_apply e v p)
theorem conjVec_apply_eq (hV : VectorL2Description L N') (v : VectorL2 L N')
    (x : FullSpace.Vertex L 0 0) (i : Fin N') : conjVec v x i = conj (v x i) := by
  have hex : ∃ w : VectorL2 L N', ∀ x i, w x i = conj (v x i) := by
    let w : FullSpace.Vertex L 0 0 → EuclideanSpace ℂ (Fin N') :=
      fun x => WithLp.toLp 2 fun i => conj (v x i)
    have hw : Memℓp w 2 := by
      refine (hV.1 w).2 ?_
      have h := (hV.1 v).1 (lp.memℓp v)
      simpa [w] using h
    exact ⟨⟨w, hw⟩, fun x i => rfl⟩
  exact Classical.epsilon_spec hex x i
variable {multiple : VectorL2 L N' → ComplexMatrix2 → L2Field σ}
  {e : FullSpace.Vertex L 0 0 × Fin N' ≃ σ}
theorem ofCoords_multiple
    (hm : ∀ X ∈ ComplexMatrix2.traceless, ∀ (v : VectorL2 L N') (p : FullSpace.Vertex L 0 0 × Fin N'),
      ofCoords (multiple v X) (e p) = v p.1 p.2 • X)
    {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) (v : VectorL2 L N') :
    ofCoords (multiple v X) = fun s => coeffAt e v s • X := by
  funext s
  have h := hm X hX v (e.symm s)
  rwa [e.apply_symm_apply] at h
theorem inner_multiple_eq (hV : VectorL2Description L N') (hC : CoordsIsometry σ)
    (hM : ScalarMultipleInner σ)
    (hm : ∀ X ∈ ComplexMatrix2.traceless, ∀ (v : VectorL2 L N') (p : FullSpace.Vertex L 0 0 × Fin N'),
      ofCoords (multiple v X) (e p) = v p.1 p.2 • X)
    {t : ComplexMatrix2} (ht : t ∈ ComplexMatrix2.traceless) (v v' : VectorL2 L N') :
    inner ℂ (multiple v t) (multiple v' t) =
      ComplexMatrix2.halfTrace (ComplexMatrix2.adjointMatrix t * t) * inner ℂ v v' := by
  rw [← hC.2.2.2.2.2, ofCoords_multiple hm ht, ofCoords_multiple hm ht,
    (hM t ht _ _ (summable_sq_coeffAt hV e v) (summable_sq_coeffAt hV e v')).2.2]
  congr 1
  rw [(hV.2 v v').2]
  have hsum : Summable fun p : FullSpace.Vertex L 0 0 × Fin N' =>
      conj (v p.1 p.2) * v' p.1 p.2 := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      ((summable_sq_pairs hV v).add (summable_sq_pairs hV v')))
    rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖v p.1 p.2‖ - ‖v' p.1 p.2‖), sq_nonneg (‖v p.1 p.2‖ + ‖v' p.1 p.2‖)]
  have h1 := e.symm.tsum_eq fun p : FullSpace.Vertex L 0 0 × Fin N' =>
    conj (v p.1 p.2) * v' p.1 p.2
  have h2 := hsum.tsum_prod
  simp only [tsum_fintype] at h2
  exact h1.trans h2
theorem exists_smul_iff (hV : VectorL2Description L N') (hC : CoordsIsometry σ)
    (hm : ∀ X ∈ ComplexMatrix2.traceless, ∀ (v : VectorL2 L N') (p : FullSpace.Vertex L 0 0 × Fin N'),
      ofCoords (multiple v X) (e p) = v p.1 p.2 • X)
    {t : ComplexMatrix2} (ht : IsWeightMatrix t) (f : L2Field σ) :
    (∃ c : σ → ℂ, ∀ s, ofCoords f s = c s • t) ↔ ∃ v, f = multiple v t := by
  have htm := isWeightMatrix_mem_traceless ht
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨k, hk0, hk⟩ := isWeightMatrix_halfTrace_pos ht
    have hsq : Summable fun s => ‖c s‖ ^ 2 := by
      have h := (hC.2.2.1 f).1.2
      have h' : Summable fun s => ‖c s‖ ^ 2 * k := by
        refine h.congr fun s => ?_
        rw [hc s, halfTraceProduct_smul_re _ _ k hk]
      exact (summable_mul_right_iff hk0.ne').1 h'
    have hpairs : Summable fun p : FullSpace.Vertex L 0 0 × Fin N' => ‖c (e p)‖ ^ 2 :=
      (e.summable_iff (f := fun s => ‖c s‖ ^ 2)).2 hsq
    rw [summable_prod_of_nonneg (fun _ => by positivity)] at hpairs
    have hx := hpairs.2
    simp only [tsum_fintype] at hx
    let w : FullSpace.Vertex L 0 0 → EuclideanSpace ℂ (Fin N') :=
      fun x => WithLp.toLp 2 fun i => c (e (x, i))
    have hw : Memℓp w 2 := (hV.1 w).2 hx
    refine ⟨⟨w, hw⟩, ofCoords_injective hC ?_⟩
    rw [ofCoords_multiple hm htm]
    funext s
    rw [hc s]
    have : coeffAt e (⟨w, hw⟩ : VectorL2 L N') s = c s := by
      show c (e ((e.symm s).1, (e.symm s).2)) = c s
      simp
    rw [this]
  · rintro ⟨v, rfl⟩
    exact ⟨coeffAt e v, fun s => congrFun (ofCoords_multiple hm htm v) s⟩
theorem pointwiseStar_multiple (hV : VectorL2Description L N')
    (hC : CoordsIsometry σ) (hS : StarProperties σ)
    (hm : ∀ X ∈ ComplexMatrix2.traceless, ∀ (v : VectorL2 L N') (p : FullSpace.Vertex L 0 0 × Fin N'),
      ofCoords (multiple v X) (e p) = v p.1 p.2 • X)
    {t t' : ComplexMatrix2} (ht : t ∈ ComplexMatrix2.traceless) (ht' : t' ∈ ComplexMatrix2.traceless)
    (h : ComplexMatrix2.adjointMatrix t = t') (v : VectorL2 L N') :
    pointwiseStar (multiple v t) = multiple (conjVec v) t' := by
  refine ofCoords_injective hC ?_
  rw [ofCoords_pointwiseStar hC hS, ofCoords_multiple hm ht, ofCoords_multiple hm ht']
  funext s
  show ComplexMatrix2.adjointMatrix (coeffAt e v s • t) = _
  rw [adjointMatrix_smul, h]
  congr 1
  exact (conjVec_apply_eq hV v _ _).symm
theorem weightMultipleFacts_of (hV : VectorL2Description L N')
    (hC : CoordsIsometry σ) (hS : StarProperties σ) (hM : ScalarMultipleInner σ)
    (hm : ∀ X ∈ ComplexMatrix2.traceless, ∀ (v : VectorL2 L N') (p : FullSpace.Vertex L 0 0 × Fin N'),
      ofCoords (multiple v X) (e p) = v p.1 p.2 • X) :
    WeightMultipleFacts multiple where
  conjVec_apply := conjVec_apply_eq hV
  map_add := by
    intro t ht v v'
    have htm := isWeightMatrix_mem_traceless ht
    refine ofCoords_injective hC ?_
    rw [(hC.2.2.2.2.1 0 _ _).1, ofCoords_multiple hm htm, ofCoords_multiple hm htm,
      ofCoords_multiple hm htm]
    funext s
    show coeffAt e (v + v') s • t = coeffAt e v s • t + coeffAt e v' s • t
    rw [← add_smul]
    rfl
  map_smul := by
    intro t ht c v
    have htm := isWeightMatrix_mem_traceless ht
    refine ofCoords_injective hC ?_
    rw [(hC.2.2.2.2.1 c (multiple v t) 0).2, ofCoords_multiple hm htm,
      ofCoords_multiple hm htm]
    funext s
    show coeffAt e (c • v) s • t = c • coeffAt e v s • t
    rw [smul_smul]
    rfl
  inner_third := by
    intro v v'
    rw [inner_multiple_eq hV hC hM hm (isWeightMatrix_mem_traceless (Or.inl rfl)), halfTrace_third,
      one_mul]
  inner_raising := by
    intro v v'
    rw [inner_multiple_eq hV hC hM hm (isWeightMatrix_mem_traceless (Or.inr (Or.inl rfl))),
      halfTrace_raising]
  inner_lowering := by
    intro v v'
    rw [inner_multiple_eq hV hC hM hm (isWeightMatrix_mem_traceless (Or.inr (Or.inr rfl))),
      halfTrace_lowering]
  neutral_iff := exists_smul_iff hV hC hm (Or.inl rfl)
  positive_iff := exists_smul_iff hV hC hm (Or.inr (Or.inl rfl))
  negative_iff := exists_smul_iff hV hC hm (Or.inr (Or.inr rfl))
  star_raising := pointwiseStar_multiple hV hC hS hm
    (isWeightMatrix_mem_traceless (Or.inr (Or.inl rfl)))
    (isWeightMatrix_mem_traceless (Or.inr (Or.inr rfl))) adjointMatrix_raisingPauli
  star_lowering := pointwiseStar_multiple hV hC hS hm
    (isWeightMatrix_mem_traceless (Or.inr (Or.inr rfl)))
    (isWeightMatrix_mem_traceless (Or.inr (Or.inl rfl))) adjointMatrix_loweringPauli
end WeightMultiples
section PositiveEdges
variable {L : ℕ}
theorem axisStep_injective :
    Function.Injective (InfiniteLattice.axisStep (meshAt L 0 0)) := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.axisStep_injective <;> assumption
theorem forwardEdge_bijective : Function.Bijective
    (fun c : FullSpace.Vertex L 0 0 × Fin 4 =>
      (FullSpace.forwardEdge c.1 c.2 : PeriodicOperators.PosEdge L 0 0)) := by
  constructor
  · rintro ⟨x, μ⟩ ⟨y, ν⟩ h
    have h' := congrArg Subtype.val h
    have ht : x = y := congrArg InfiniteLattice.Link.initial h'
    subst ht
    have hh : x + InfiniteLattice.axisStep _ μ = x + InfiniteLattice.axisStep _ ν :=
      congrArg InfiniteLattice.Link.terminal h'
    have hμ := axisStep_injective (add_left_cancel hh)
    subst hμ
    rfl
  · rintro ⟨b, μ, hμ⟩
    refine ⟨(b.initial, μ), Subtype.ext (InfiniteLattice.Link.ext rfl ?_)⟩
    show b.initial + InfiniteLattice.axisStep _ μ = b.terminal
    rw [← hμ]
    abel
def pairEdgeEquiv (L : ℕ) :
    FullSpace.Vertex L 0 0 × Fin 4 ≃ PeriodicOperators.PosEdge L 0 0 :=
  Equiv.ofBijective _ forwardEdge_bijective
def pairVertexEquiv (L : ℕ) : FullSpace.Vertex L 0 0 × Fin 1 ≃ FullSpace.Vertex L 0 0 :=
  Equiv.prodUnique _ _
theorem existsUnique_forwardEdge (b : PeriodicOperators.PosEdge L 0 0) :
    ∃! p : FullSpace.Vertex L 0 0 × Fin 4, FullSpace.forwardEdge p.1 p.2 = b := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.existsUnique_forwardEdge_eq <;> assumption
end PositiveEdges
theorem weightMultiplesAndStar_holds (h : Tower.UnitLatticeL2Statement) :
    WeightMultiplesAndStar := by
  intro L _
  obtain ⟨hV, ⟨hCs, hSs, hMs, -⟩, hCb, hSb, hMb, -⟩ := h.2 L
  have hV1 := hV 1 le_rfl
  have hV4 := hV 4 (by norm_num)
  have vertex_spec : ∀ X ∈ ComplexMatrix2.traceless, ∀ (v : VectorL2 L 1) (x : FullSpace.Vertex L 0 0),
      ofCoords (vertexTensor v X) x = v x 0 • X := by
    intro X hX v
    obtain ⟨f, hf⟩ := exists_ofCoords_eq_smul hV1 hCs hMs (pairVertexEquiv L) v hX
    exact Classical.epsilon_spec (p := fun f : L2Field (FullSpace.Vertex L 0 0) =>
      ∀ x : FullSpace.Vertex L 0 0, ofCoords f x = v x 0 • X)
      ⟨f, fun x => hf (x, 0)⟩
  have edge_spec : ∀ X ∈ ComplexMatrix2.traceless, ∀ (v : VectorL2 L 4) (x : FullSpace.Vertex L 0 0)
      (μ : Fin 4), ofCoords (edgeTensor v X) (FullSpace.forwardEdge x μ) = v x μ • X := by
    intro X hX v
    obtain ⟨f, hf⟩ := exists_ofCoords_eq_smul hV4 hCb hMb (pairEdgeEquiv L) v hX
    exact Classical.epsilon_spec
      (p := fun f : L2Field (PeriodicOperators.PosEdge L 0 0) =>
        ∀ (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
          ofCoords f (FullSpace.forwardEdge x μ) = v x μ • X)
      ⟨f, fun x μ => hf (x, μ)⟩
  refine ⟨existsUnique_forwardEdge, fun _ ht => isWeightMatrix_mem_traceless ht, vertex_spec, edge_spec,
    starInvolutionFacts_of hCs hSs, starInvolutionFacts_of hCb hSb,
    weightMultipleFacts_of (e := pairVertexEquiv L) hV1 hCs hSs hMs ?_,
    weightMultipleFacts_of (e := pairEdgeEquiv L) hV4 hCb hSb hMb ?_⟩
  · rintro X hX v ⟨x, i⟩
    rw [Subsingleton.elim i 0]
    exact vertex_spec X hX v x
  · rintro X hX v ⟨x, μ⟩
    exact edge_spec X hX v x μ
end YangMills.Construction.Tower.AbelianFieldDensity.WeightMultiplesProof
end
