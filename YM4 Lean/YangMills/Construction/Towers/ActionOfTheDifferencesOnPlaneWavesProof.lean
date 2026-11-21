import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.SymbolOnClassesAndPlaneWaves
import YangMills.Construction.PeriodicOperators.SymbolsOnStrips
import YangMills.Construction.PeriodicOperators.TranslationsOnTheIndexSetsOfATower
import YangMills.Construction.Towers.ActionOfTheDifferencesOnPlaneWaves
import YangMills.Construction.Towers.PlaquettesOfABondProof
import YangMills.Construction.Towers.TransposesAndRelationsOfTheScaledPicture
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.PlaneWaveCoboundaries
open PeriodicOperators
open PeriodicOperators.TowerTranslations (posEdgeForward)
open InfiniteLattice (AmbientSpace)
open PlaneWaves (VertexClass fourierPhase freqBox)
section Abstract
variable {I I' : PeriodicData}
theorem symbolHom_mkQuot (hC : SymbolOnQuotients.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) {κ : Fin 4 → ℂ}
    (hF : SymbolSummableAt I I' T κ) (φ : I.UnitQuot → ℂ) (ι' : I'.Carrier) :
    symbolHom I I' T κ φ (I'.mkQuot 1 ι') =
      Complex.exp (-(Complex.I * bilinDot κ (toComplexVec (I'.pos ι')))) *
        applyKernel T (blochWave I κ φ) ι' := by
  have := hI.finite_quot
  have e := ((hC I I' hI hI' T hT).applyKernel_blochWave κ hF φ ι').2
  have e₂ : symbolHom I I' T κ φ = applyKernel (quotSymbol I I' T κ) φ :=
    linearMapOfEntries_eq_applyKernel _ φ
  rw [e, e₂, blochWave, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
theorem sum_mul_symbolHom_transpose (hS : StripSymbols.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) (hR : IsFiniteRange I I' T)
    {w : ℝ} (hw₀ : w ≠ 0) (hw : ∀ c, I.quotWeight 1 c = w) (hw' : ∀ c, I'.quotWeight 1 c = w)
    [Fintype I.UnitQuot] [Fintype I'.UnitQuot] (κ : Fin 4 → ℂ) (g : I.UnitQuot → ℂ)
    (f : I'.UnitQuot → ℂ) :
    ∑ c, g c * symbolHom I' I (kernelTranspose I I' T) κ f c =
      ∑ c', symbolHom I I' T (-κ) g c' * f c' := by
  have hs := (hS.2.1 I I' hI hI').1.finiteRange T hT hR (-κ) (mem_univ _)
  have ht := ((hS.2.1 I I' hI hI').2.1 T (-κ) hT hs).transpose.2.2
  rw [neg_neg] at ht
  have e₁ : symbolHom I' I (kernelTranspose I I' T) κ f =
      applyKernel (quotSymbol I' I (kernelTranspose I I' T) κ) f := linearMapOfEntries_eq_applyKernel _ f
  have e₂ : symbolHom I I' T (-κ) g = applyKernel (quotSymbol I I' T (-κ)) g :=
    linearMapOfEntries_eq_applyKernel _ g
  rw [e₁, e₂, ht]
  simp only [applyKernel, tsum_fintype, quotTranspose, wTranspose, hw, hw', div_self hw₀,
    Complex.ofReal_one, one_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun c _ => ?_
  ring
end Abstract
def pauliSum (z : Fin 3 → ℂ) : Matrices.ComplexMatrix2 :=
  ∑ a, z a • Matrices.ComplexMatrix2.pauliFamily a
theorem smul_pauliSum (c : ℂ) (z : Fin 3 → ℂ) :
    c • pauliSum z = pauliSum fun a => c * z a := by
  simp [pauliSum, Finset.smul_sum, mul_smul]
theorem pauliSum_sub_pauliSum (z w : Fin 3 → ℂ) :
    pauliSum z - pauliSum w = pauliSum fun a => z a - w a := by
  simp [pauliSum, sub_smul, Finset.sum_sub_distrib]
theorem sum_pauliSum {ι : Type} (s : Finset ι) (z : ι → Fin 3 → ℂ) :
    ∑ i ∈ s, pauliSum (z i) = pauliSum fun a => ∑ i ∈ s, z i a := by
  simp only [pauliSum, Finset.sum_smul]
  rw [Finset.sum_comm]
theorem pauliSum_mem_traceless (z : Fin 3 → ℂ) : pauliSum z ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.LieInnerProductProof.pauliCombination_mem_traceless <;> assumption
theorem pauliCoeff_pauliSum (z : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (pauliSum z) = z a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem real_smul_pauliSum (r : ℝ) (z : Fin 3 → ℂ) :
    r • pauliSum z = pauliSum fun a => (r : ℂ) * z a := by
  have : r • pauliSum z = (r : ℂ) • pauliSum z := by
    ext i j
    simp
  rw [this, smul_pauliSum]
theorem ofPauliCoeffs_apply {σ : Type} (f : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs f x = pauliSum fun c => f (c, x) := rfl
structure TripleCoding (L k : ℕ) (I : PeriodicData) (D : Type) where
  encode : Fin 3 → D → FullSpace.Vertex L k 0 → I.Carrier
  decode : I.Carrier → Fin 3 × D × FullSpace.Vertex L k 0
  translate_encode : ∀ a d x n, I.translate n (encode a d x) = encode a d (FullSpace.vertexImage (intShift n) x)
  decode_encode : ∀ a d x, decode (encode a d x) = (a, d, x)
  encode_decode : ∀ ι, encode (decode ι).1 (decode ι).2.1 (decode ι).2.2 = ι
namespace TripleCoding
variable {L k : ℕ} {I : PeriodicData} {D : Type} (R : TripleCoding L k I D)
def quot (a : Fin 3) (d : D) (x : FullSpace.Vertex L k 0) : I.UnitQuot := I.mkQuot 1 (R.encode a d x)
theorem quot_vertexImage (a : Fin 3) (d : D) (x : FullSpace.Vertex L k 0) (n : Fin 4 → ℤ) :
    R.quot a d (FullSpace.vertexImage (intShift n) x) = R.quot a d x := by
  refine (Quot.sound ⟨n, ?_⟩).symm
  rw [one_smul, R.translate_encode]
def descend {β : Type} (G : Fin 3 → D → FullSpace.Vertex L k 0 → β)
    (hG : ∀ a d x n, G a d (FullSpace.vertexImage (intShift n) x) = G a d x) : I.UnitQuot → β :=
  Quot.lift (fun ι => G (R.decode ι).1 (R.decode ι).2.1 (R.decode ι).2.2) (by
    rintro ι ι' ⟨n, h⟩
    have e : ι' = R.encode (R.decode ι).1 (R.decode ι).2.1
        (FullSpace.vertexImage (intShift n) (R.decode ι).2.2) := by
      rw [h, one_smul, ← R.translate_encode, R.encode_decode]
    show _ = G (R.decode ι').1 (R.decode ι').2.1 (R.decode ι').2.2
    rw [e, R.decode_encode]
    exact (hG _ _ _ _).symm)
theorem descend_quot {β : Type} (G : Fin 3 → D → FullSpace.Vertex L k 0 → β)
    (hG : ∀ a d x n, G a d (FullSpace.vertexImage (intShift n) x) = G a d x)
    (a : Fin 3) (d : D) (x : FullSpace.Vertex L k 0) :
    R.descend G hG (R.quot a d x) = G a d x := by
  show G (R.decode (R.encode a d x)).1 (R.decode (R.encode a d x)).2.1
    (R.decode (R.encode a d x)).2.2 = _
  rw [R.decode_encode]
theorem quot_out (a : Fin 3) (d : D) (x : FullSpace.Vertex L k 0) :
    R.quot a d (Quot.out (Quot.mk _ x : VertexClass L k)) = R.quot a d x := by
  let φ : VertexClass L k → I.UnitQuot := Quot.lift (R.quot a d) (by
    rintro x _ ⟨n, rfl⟩
    exact (R.quot_vertexImage a d x n).symm)
  exact congrArg φ (Quot.out_eq (Quot.mk _ x : VertexClass L k))
def equivUnitQuot : Fin 3 × D × VertexClass L k ≃ I.UnitQuot where
  toFun t := R.quot t.1 t.2.1 (Quot.out t.2.2)
  invFun := R.descend (fun a d x => (a, d, (Quot.mk _ x : VertexClass L k))) (by
    intro a d x n
    have : (Quot.mk _ (FullSpace.vertexImage (intShift n) x) : VertexClass L k) = Quot.mk _ x :=
      (Quot.sound ⟨n, rfl⟩).symm
    rw [this])
  left_inv t := by
    obtain ⟨a, d, s⟩ := t
    simp only [descend_quot, Quot.out_eq]
  right_inv c := by
    induction c using Quot.ind with
    | mk ι =>
      have e : R.quot (R.decode ι).1 (R.decode ι).2.1 (R.decode ι).2.2 = Quot.mk _ ι := by
        show I.mkQuot 1 _ = _
        rw [R.encode_decode]
        rfl
      rw [← e, descend_quot]
      exact R.quot_out _ _ _
theorem sum_unitQuot [Fintype D] [Fintype (VertexClass L k)] [Fintype I.UnitQuot]
    (F : I.UnitQuot → ℂ) :
    ∑ c, F c = ∑ a, ∑ d, ∑ s : VertexClass L k, F (R.quot a d (Quot.out s)) := by
  rw [← Equiv.sum_comp R.equivUnitQuot, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  rfl
end TripleCoding
structure Hypotheses (L k : ℕ) : Prop where
  symbolOnQuot : SymbolOnQuotients.Claim
  stripSymbols : StripSymbols.Claim
  vertices : IsPeriodic (colourVertices L k 0)
  edges : IsPeriodic (colourEdges L k 0)
  faces : IsPeriodic (colourFaces L k 0)
  kernels : FreeOperators.FreeMapsRangeThree L k
  finiteRange : FreeOperators.FreeOperatorsFiniteRange L k
  rescaled : FullSpace.RescaledConditions.OnFullSpace L k
  vertexImage_coe : ∀ (n : Fin 4 → ℤ) (x : FullSpace.Vertex L k 0),
    ((FullSpace.vertexImage (intShift n) x : FullSpace.Vertex L k 0) : AmbientSpace) =
      (x : AmbientSpace) + castVec n
  edge_translate : ∀ (n : Fin 4 → ℤ) (c : Fin 3) (b : PeriodicOperators.PosEdge L k 0) (μ : Fin 4),
    b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L k 0) μ →
    ((colourEdges L k 0).translate n (c, b) : Fin 3 × PeriodicOperators.PosEdge L k 0) =
      (c, posEdgeForward (FullSpace.vertexImage (intShift n) b.1.initial) μ)
  mesh_pos : 0 < meshAt L k 0
section Tower
variable {L k : ℕ}
def vertexCoding (L k : ℕ) : TripleCoding L k (colourVertices L k 0) Unit where
  encode a _ x := ((a, x) : Fin 3 × FullSpace.Vertex L k 0)
  decode ι := (ι.1, (), ι.2)
  translate_encode _ _ _ _ := rfl
  decode_encode _ _ _ := rfl
  encode_decode _ := rfl
def faceCoding (L k : ℕ) :
    TripleCoding L k (colourFaces L k 0) PlaneWaveCalculus.AxisPair where
  encode a p x := ((a, ⟨x, p.1.1, p.1.2, p.2⟩) : Fin 3 × FullSpace.Face L k 0)
  decode ι := (ι.1, ⟨(ι.2.lowAxis, ι.2.highAxis), ι.2.lowAxis_lt_highAxis⟩, ι.2.corner)
  translate_encode _ _ _ _ := rfl
  decode_encode _ _ _ := rfl
  encode_decode _ := rfl
theorem axisStep_injective {a : ℝ} (ha : a ≠ 0) {μ ν : Fin 4}
    (h : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ν) : μ = ν := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
def edgeCoding (h : Hypotheses L k) : TripleCoding L k (colourEdges L k 0) (Fin 4) where
  encode a μ x := ((a, posEdgeForward x μ) : Fin 3 × PeriodicOperators.PosEdge L k 0)
  decode ι := (ι.1, Classical.choose ι.2.2, ι.2.1.initial)
  translate_encode a μ x n := h.edge_translate n a (posEdgeForward x μ) μ (by
    show x + InfiniteLattice.axisStep _ μ - x = _
    abel)
  decode_encode a μ x := by
    have s := Classical.choose_spec (posEdgeForward x μ : PeriodicOperators.PosEdge L k 0).2
    have e : InfiniteLattice.axisStep (meshAt L k 0) μ =
        InfiniteLattice.axisStep (meshAt L k 0)
          (Classical.choose (posEdgeForward x μ : PeriodicOperators.PosEdge L k 0).2) := by
      rw [← s]
      show _ = x + InfiniteLattice.axisStep _ μ - x
      abel
    have := axisStep_injective h.mesh_pos.ne' e
    exact Prod.ext rfl (Prod.ext this.symm rfl)
  encode_decode ι := by
    obtain ⟨c, b⟩ := ι
    refine Prod.ext rfl (Subtype.ext (InfiniteLattice.Link.ext rfl ?_))
    have s := Classical.choose_spec b.2
    show b.1.initial + InfiniteLattice.axisStep _ (Classical.choose b.2) = b.1.terminal
    rw [← s]
    abel
theorem bilinDot_add_axisStep {a : ℝ} (q : Fin 4 → ℂ) (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    bilinDot q (toComplexVec ((x + InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a) :
        AmbientSpace)) =
      bilinDot q (toComplexVec (x : AmbientSpace)) + q μ * (a : ℂ) := by
  have e : ∀ ν, toComplexVec ((x + InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a) :
      AmbientSpace) ν =
      toComplexVec (x : AmbientSpace) ν + (Pi.single μ (a : ℂ) : Fin 4 → ℂ) ν := by
    intro ν
    by_cases hν : ν = μ
    · subst hν
      simp [toComplexVec, InfiniteLattice.axisStep]
    · simp [toComplexVec, InfiniteLattice.axisStep, Pi.single_eq_of_ne hν]
  simp only [bilinDot, e, mul_add, Finset.sum_add_distrib]
  simp [Pi.single_apply]
theorem fourierPhase_vertexImage (h : Hypotheses L k) (m n : Fin 4 → ℤ) (x : FullSpace.Vertex L k 0) :
    fourierPhase m (FullSpace.vertexImage (intShift n) x : FullSpace.Vertex L k 0) =
      fourierPhase m (x : AmbientSpace) := by
  have e : bilinDot (toComplexVec (castVec m))
      (toComplexVec ((FullSpace.vertexImage (intShift n) x : FullSpace.Vertex L k 0) : AmbientSpace)) =
      bilinDot (toComplexVec (castVec m)) (toComplexVec (x : AmbientSpace)) +
        ((∑ μ, m μ * n μ : ℤ) : ℂ) := by
    rw [h.vertexImage_coe]
    simp only [bilinDot, toComplexVec, castVec, Pi.add_apply, Complex.ofReal_add, mul_add,
      Finset.sum_add_distrib]
    push_cast
    simp
  rw [fourierPhase, fourierPhase, e, mul_add, Complex.exp_add]
  have e₂ : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ μ, m μ * n μ : ℤ) : ℂ)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (-∑ μ, m μ * n μ)
    rw [← this]
    congr 1
    push_cast
    ring
  rw [e₂, mul_one]
theorem fourierPhase_add_axisStep (m : Fin 4 → ℤ) (x : FullSpace.Vertex L k 0) (μ : Fin 4) :
    fourierPhase m ((x + InfiniteLattice.axisStep (meshAt L k 0) μ : FullSpace.Vertex L k 0) :
        AmbientSpace) =
      fourierPhase m (x : AmbientSpace) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((m μ : ℂ) * (meshAt L k 0 : ℂ))) := by
  rw [fourierPhase, fourierPhase, bilinDot_add_axisStep, mul_add, Complex.exp_add]
  simp [toComplexVec, castVec]
section Scalar
variable [Fintype (VertexClass L k)]
def scalarCoeff (L k : ℕ) [Fintype (VertexClass L k)] (m : Fin 4 → ℤ)
    (F : FullSpace.Vertex L k 0 → ℂ) : ℂ :=
  ((finestMesh L k ^ 4 : ℝ) : ℂ) *
    ∑ s : VertexClass L k, fourierPhase m (Quot.out s : FullSpace.Vertex L k 0) * F (Quot.out s)
theorem scalarCoeff_const_mul (m : Fin 4 → ℤ) (c : ℂ) (F : FullSpace.Vertex L k 0 → ℂ) :
    scalarCoeff L k m (fun x => c * F x) = c * scalarCoeff L k m F := by
  simp only [scalarCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring
theorem scalarCoeff_add (m : Fin 4 → ℤ) (F G : FullSpace.Vertex L k 0 → ℂ) :
    scalarCoeff L k m (fun x => F x + G x) = scalarCoeff L k m F + scalarCoeff L k m G := by
  simp only [scalarCoeff, mul_add, Finset.sum_add_distrib]
theorem scalarCoeff_sub (m : Fin 4 → ℤ) (F G : FullSpace.Vertex L k 0 → ℂ) :
    scalarCoeff L k m (fun x => F x - G x) = scalarCoeff L k m F - scalarCoeff L k m G := by
  simp only [scalarCoeff, mul_sub, Finset.sum_sub_distrib]
theorem fourierCoeff_ofPauliCoeffs (F : Fin 3 × FullSpace.Vertex L k 0 → ℂ) (m : Fin 4 → ℤ) :
    PlaneWaves.fourierCoeff L k (ofPauliCoeffs F) m =
      pauliSum fun a => scalarCoeff L k m fun x => F (a, x) := by
  rw [PlaneWaves.fourierCoeff, finsum_eq_sum_of_fintype]
  simp only [ofPauliCoeffs_apply, smul_pauliSum, sum_pauliSum]
  rfl
def latticePhase (L k : ℕ) (m : Fin 4 → ℤ) (μ : Fin 4) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m μ : ℂ) * (meshAt L k 0 : ℂ)))
omit [Fintype (VertexClass L k)] in
theorem vertexImage_add (h : Hypotheses L k) (n : Fin 4 → ℤ) (x y : FullSpace.Vertex L k 0) :
    (FullSpace.vertexImage (intShift n) (x + y) : FullSpace.Vertex L k 0) =
      FullSpace.vertexImage (intShift n) x + y := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, h.vertexImage_coe]
  abel
def vertexClassAdd (h : Hypotheses L k) (y : FullSpace.Vertex L k 0) :
    VertexClass L k ≃ VertexClass L k where
  toFun := Quot.map (· + y) (by
    rintro x _ ⟨n, rfl⟩
    exact ⟨n, (vertexImage_add h n x y).symm⟩)
  invFun := Quot.map (· + -y) (by
    rintro x _ ⟨n, rfl⟩
    exact ⟨n, (vertexImage_add h n x (-y)).symm⟩)
  left_inv s := by
    induction s using Quot.ind with
    | mk x =>
      show Quot.mk _ (x + y + -y) = _
      rw [add_neg_cancel_right]
  right_inv s := by
    induction s using Quot.ind with
    | mk x =>
      show Quot.mk _ (x + -y + y) = _
      rw [neg_add_cancel_right]
theorem scalarCoeff_shift (h : Hypotheses L k) {F : FullSpace.Vertex L k 0 → ℂ}
    (hF : ∀ n x, F (FullSpace.vertexImage (intShift n) x) = F x) (m : Fin 4 → ℤ) (μ : Fin 4) :
    scalarCoeff L k m (fun x => F (x + InfiniteLattice.axisStep (meshAt L k 0) μ)) =
      latticePhase L k m μ * scalarCoeff L k m F := by
  let G : FullSpace.Vertex L k 0 → ℂ := fun x => fourierPhase m (x : AmbientSpace) * F x
  have hG : ∀ n x, G (FullSpace.vertexImage (intShift n) x) = G x := fun n x => by
    show fourierPhase m _ * _ = _
    rw [fourierPhase_vertexImage h, hF]
  let Gq : VertexClass L k → ℂ := Quot.lift G (by
    rintro x _ ⟨n, rfl⟩
    exact (hG n x).symm)
  have gq : ∀ s : VertexClass L k, Gq s = G (Quot.out s) := fun s =>
    (congrArg Gq (Quot.out_eq s)).symm
  let st := InfiniteLattice.axisStep (meshAt L k 0) μ
  have gs : ∀ s : VertexClass L k, Gq (vertexClassAdd h st s) = G (Quot.out s + st) := fun s =>
    (congrArg (fun t => Gq (vertexClassAdd h st t)) (Quot.out_eq s)).symm
  have e : ∑ s : VertexClass L k, G (Quot.out s + st) = ∑ s : VertexClass L k, G (Quot.out s) :=
    (Finset.sum_congr rfl fun s _ => (gs s).symm).trans
      ((Equiv.sum_comp (vertexClassAdd h st) Gq).trans (Finset.sum_congr rfl fun s _ => gq s))
  have e₂ : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((m μ : ℂ) * (meshAt L k 0 : ℂ))) *
      latticePhase L k m μ = 1 := by
    rw [latticePhase, ← Complex.exp_add]
    simp
  have e₃ : ∀ s : VertexClass L k, fourierPhase m (Quot.out s : FullSpace.Vertex L k 0) *
      F (Quot.out s + st) = latticePhase L k m μ * G (Quot.out s + st) := fun s => by
    show _ = _ * (fourierPhase m _ * _)
    rw [fourierPhase_add_axisStep]
    linear_combination (-(fourierPhase m (Quot.out s : FullSpace.Vertex L k 0) * F (Quot.out s + st))) * e₂
  have e₄ : ∑ s : VertexClass L k, fourierPhase m (Quot.out s : FullSpace.Vertex L k 0) *
      F (Quot.out s + st) =
      latticePhase L k m μ * ∑ s : VertexClass L k, G (Quot.out s) := by
    rw [← e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => e₃ s
  show _ * ∑ s : VertexClass L k, fourierPhase m _ * F (Quot.out s + st) =
    latticePhase L k m μ * (_ * ∑ s : VertexClass L k, G (Quot.out s))
  rw [e₄]
  ring
end Scalar
theorem pauliCoeff_smul_sub {σ : Type} (f : Fin 3 × σ → ℂ) (x y : σ) (a : Fin 3) (c : ℝ) :
    pauliCoeff a (c • (ofPauliCoeffs f x - ofPauliCoeffs f y)) = (c : ℂ) * (f (a, x) - f (a, y)) := by
  rw [ofPauliCoeffs_apply, ofPauliCoeffs_apply, pauliSum_sub_pauliSum, real_smul_pauliSum,
    pauliCoeff_pauliSum]
theorem ofCoeffs_forwardFrom (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ)
    (x : FullSpace.Vertex L k 0) (μ : Fin 4) :
    (FullSpace.edgePauliCoordinates L k 0).ofCoeffs f (InfiniteLattice.Link.forwardFrom x μ) =
      pauliSum fun c => f (c, posEdgeForward x μ) := by
  have hp : (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented := ⟨μ, by
    show x + InfiniteLattice.axisStep _ μ - x = _
    abel⟩
  simp only [FullSpace.edgePauliCoordinates, FullSpace.extendOddly, if_pos hp, dif_pos hp]
  rfl
theorem mapOnCoeffs_vertex (f : Fin 3 × FullSpace.Vertex L k 0 → ℂ) (a : Fin 3)
    (x : FullSpace.Vertex L k 0) (μ : Fin 4) :
    (vertexCoordinate (FullSpace.Vertex L k 0)).mapOnCoeffs (FullSpace.edgePauliCoordinates L k 0)
        FullSpace.scaledVertexCoboundary f (a, posEdgeForward x μ) =
      (((meshAt L k 0)⁻¹ : ℝ) : ℂ) *
        (f (a, x + InfiniteLattice.axisStep _ μ) - f (a, x)) :=
  pauliCoeff_smul_sub f _ _ a _
theorem mapOnCoeffs_face (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ) (a : Fin 3)
    (x : FullSpace.Vertex L k 0) (μ ν : Fin 4) (hμν : μ < ν) :
    (FullSpace.edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (FullSpace.Face L k 0))
        FullSpace.scaledEdgeCoboundary f (a, ⟨x, μ, ν, hμν⟩) =
      (((meshAt L k 0)⁻¹ : ℝ) : ℂ) *
        (f (a, posEdgeForward x μ) +
          f (a, posEdgeForward (x + InfiniteLattice.axisStep _ μ) ν) -
          f (a, posEdgeForward (x + InfiniteLattice.axisStep _ ν) μ) -
          f (a, posEdgeForward x ν)) := by
  show pauliCoeff a ((meshAt L k 0)⁻¹ •
      ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs f (InfiniteLattice.Link.forwardFrom x μ) +
        (FullSpace.edgePauliCoordinates L k 0).ofCoeffs f (InfiniteLattice.Link.forwardFrom
          (x + InfiniteLattice.axisStep _ μ) ν) -
        (FullSpace.edgePauliCoordinates L k 0).ofCoeffs f (InfiniteLattice.Link.forwardFrom
          (x + InfiniteLattice.axisStep _ ν) μ) -
        (FullSpace.edgePauliCoordinates L k 0).ofCoeffs f (InfiniteLattice.Link.forwardFrom x ν))) = _
  have e₁ : ∀ z w : Fin 3 → ℂ, pauliSum z + pauliSum w = pauliSum fun a => z a + w a := by
    intro z w
    simp [pauliSum, add_smul, Finset.sum_add_distrib]
  rw [ofCoeffs_forwardFrom, ofCoeffs_forwardFrom, ofCoeffs_forwardFrom, ofCoeffs_forwardFrom, e₁,
    pauliSum_sub_pauliSum, pauliSum_sub_pauliSum, real_smul_pauliSum, pauliCoeff_pauliSum]
abbrev vertexKernel (L k : ℕ) := FullSpace.scaledVertexCoboundaryKernel L k 0
abbrev edgeKernel (L k : ℕ) := FullSpace.scaledEdgeCoboundaryKernel L k 0
theorem vertexKernel_summable (h : Hypotheses L k) (κ : Fin 4 → ℂ) :
    SymbolSummableAt (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k) κ :=
  (h.stripSymbols.2.1 _ _ h.vertices h.edges).1.finiteRange _
    (h.kernels.vertexCoboundary 0 (Nat.zero_le k)).finite_range.1
    (h.kernels.vertexCoboundary 0 (Nat.zero_le k)).finite_range.2.1 κ (mem_univ _)
theorem edgeKernel_summable (h : Hypotheses L k) (κ : Fin 4 → ℂ) :
    SymbolSummableAt (colourEdges L k 0) (colourFaces L k 0) (edgeKernel L k) κ :=
  (h.stripSymbols.2.1 _ _ h.edges h.faces).1.finiteRange _
    (h.kernels.edgeCoboundary 0 (Nat.zero_le k)).finite_range.1
    (h.kernels.edgeCoboundary 0 (Nat.zero_le k)).finite_range.2.1 κ (mem_univ _)
def meshPhase (L k : ℕ) (κ : Fin 4 → ℂ) (μ : Fin 4) : ℂ :=
  Complex.exp (Complex.I * (meshAt L k 0 : ℂ) * κ μ)
theorem symbolHom_vertexKernel (h : Hypotheses L k) (κ : Fin 4 → ℂ)
    (l : (colourVertices L k 0).UnitQuot → ℂ) (a : Fin 3) (x : FullSpace.Vertex L k 0) (μ : Fin 4) :
    symbolHom (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k) κ l
        ((edgeCoding h).quot a μ x) =
      (((meshAt L k 0)⁻¹ : ℝ) : ℂ) *
        (meshPhase L k κ μ * l ((vertexCoding L k).quot a ()
            (x + InfiniteLattice.axisStep _ μ)) - l ((vertexCoding L k).quot a () x)) := by
  show symbolHom _ _ _ κ l ((colourEdges L k 0).mkQuot 1 (a, posEdgeForward x μ)) = _
  refine (symbolHom_mkQuot h.symbolOnQuot h.vertices h.edges
    (h.kernels.vertexCoboundary 0 (Nat.zero_le k)).finite_range.1 (vertexKernel_summable h κ) l
    (a, posEdgeForward x μ)).trans ?_
  refine (congrArg (_ * ·)
    (congrFun ((h.kernels.vertexCoboundary 0 (Nat.zero_le k)).applyKernel_eq _) _)).trans ?_
  refine (congrArg (_ * ·) (mapOnCoeffs_vertex _ a x μ)).trans ?_
  have pos : (colourEdges L k 0).pos (a, posEdgeForward x μ) = (x : AmbientSpace) := rfl
  have pw : ∀ y : FullSpace.Vertex L k 0, blochWave (colourVertices L k 0) κ l (a, y) =
      Complex.exp (Complex.I * bilinDot κ (toComplexVec (y : AmbientSpace))) *
        l ((vertexCoding L k).quot a () y) := fun _ => rfl
  rw [pos, pw, pw, bilinDot_add_axisStep, mul_add, Complex.exp_add]
  have e : Complex.exp (-(Complex.I * bilinDot κ (toComplexVec (x : AmbientSpace)))) *
      Complex.exp (Complex.I * bilinDot κ (toComplexVec (x : AmbientSpace))) = 1 := by
    rw [← Complex.exp_add]
    simp
  have e₂ : Complex.exp (Complex.I * (κ μ * (meshAt L k 0 : ℂ))) = meshPhase L k κ μ := by
    rw [meshPhase]
    congr 1
    ring
  rw [e₂]
  linear_combination (((((meshAt L k 0)⁻¹ : ℝ) : ℂ)) *
    (meshPhase L k κ μ * l ((vertexCoding L k).quot a () (x + InfiniteLattice.axisStep _ μ)) -
      l ((vertexCoding L k).quot a () x))) * e
theorem symbolHom_edgeKernel (h : Hypotheses L k) (κ : Fin 4 → ℂ)
    (b : (colourEdges L k 0).UnitQuot → ℂ) (a : Fin 3) (x : FullSpace.Vertex L k 0)
    (p : PlaneWaveCalculus.AxisPair) :
    symbolHom (colourEdges L k 0) (colourFaces L k 0) (edgeKernel L k) κ b
        ((faceCoding L k).quot a p x) =
      (((meshAt L k 0)⁻¹ : ℝ) : ℂ) *
        (b ((edgeCoding h).quot a p.1.1 x) +
          meshPhase L k κ p.1.1 *
            b ((edgeCoding h).quot a p.1.2 (x + InfiniteLattice.axisStep _ p.1.1)) -
          meshPhase L k κ p.1.2 *
            b ((edgeCoding h).quot a p.1.1 (x + InfiniteLattice.axisStep _ p.1.2)) -
          b ((edgeCoding h).quot a p.1.2 x)) := by
  obtain ⟨⟨μ, ν⟩, hμν⟩ := p
  show symbolHom _ _ _ κ b ((colourFaces L k 0).mkQuot 1 (a, ⟨x, μ, ν, hμν⟩)) = _
  refine (symbolHom_mkQuot h.symbolOnQuot h.edges h.faces
    (h.kernels.edgeCoboundary 0 (Nat.zero_le k)).finite_range.1 (edgeKernel_summable h κ) b
    (a, ⟨x, μ, ν, hμν⟩)).trans ?_
  refine (congrArg (_ * ·)
    (congrFun ((h.kernels.edgeCoboundary 0 (Nat.zero_le k)).applyKernel_eq _) _)).trans ?_
  refine (congrArg (_ * ·) (mapOnCoeffs_face _ a x μ ν hμν)).trans ?_
  have pos : (colourFaces L k 0).pos (a, ⟨x, μ, ν, hμν⟩) = (x : AmbientSpace) := rfl
  have pw : ∀ (y : FullSpace.Vertex L k 0) (ρ : Fin 4),
      blochWave (colourEdges L k 0) κ b (a, posEdgeForward y ρ) =
        Complex.exp (Complex.I * bilinDot κ (toComplexVec (y : AmbientSpace))) *
          b ((edgeCoding h).quot a ρ y) := fun _ _ => rfl
  rw [pos, pw, pw, pw, pw, bilinDot_add_axisStep, bilinDot_add_axisStep, mul_add, mul_add,
    Complex.exp_add, Complex.exp_add]
  have e : Complex.exp (-(Complex.I * bilinDot κ (toComplexVec (x : AmbientSpace)))) *
      Complex.exp (Complex.I * bilinDot κ (toComplexVec (x : AmbientSpace))) = 1 := by
    rw [← Complex.exp_add]
    simp
  have e₂ : ∀ ρ, Complex.exp (Complex.I * (κ ρ * (meshAt L k 0 : ℂ))) =
      meshPhase L k κ ρ := fun ρ => by
    rw [meshPhase]
    congr 1
    ring
  rw [e₂, e₂]
  linear_combination (((((meshAt L k 0)⁻¹ : ℝ) : ℂ)) *
    (b ((edgeCoding h).quot a μ x) +
      meshPhase L k κ μ * b ((edgeCoding h).quot a ν (x + InfiniteLattice.axisStep _ μ)) -
      meshPhase L k κ ν * b ((edgeCoding h).quot a μ (x + InfiniteLattice.axisStep _ ν)) -
      b ((edgeCoding h).quot a ν x))) * e
section Coefficients
variable [Fintype (VertexClass L k)]
def TripleCoding.coeff {I : PeriodicData} {D : Type} (R : TripleCoding L k I D)
    (u : I.UnitQuot → ℂ) (a : Fin 3) (d : D) (m : Fin 4 → ℤ) : ℂ :=
  scalarCoeff L k m fun x => u (R.quot a d x)
theorem TripleCoding.coeff_shift (h : Hypotheses L k) {I : PeriodicData} {D : Type}
    (R : TripleCoding L k I D) (u : I.UnitQuot → ℂ) (a : Fin 3) (d : D) (m : Fin 4 → ℤ) (μ : Fin 4) :
    scalarCoeff L k m (fun x => u (R.quot a d (x + InfiniteLattice.axisStep (meshAt L k 0) μ))) =
      latticePhase L k m μ * R.coeff u a d m :=
  scalarCoeff_shift h (F := fun x => u (R.quot a d x)) (fun n x => by simp only [R.quot_vertexImage]) m μ
omit [Fintype (VertexClass L k)] in
theorem forwardSymbol_shiftedFreq (κ : Fin 4 → ℂ) (m : Fin 4 → ℤ) (μ : Fin 4) :
    PlaneWaves.forwardSymbol L k (PlaneWaves.shiftedFreq κ m) μ =
      (((meshAt L k 0)⁻¹ : ℝ) : ℂ) * (meshPhase L k κ μ * latticePhase L k m μ - 1) := by
  show ((meshAt L k 0 : ℝ) : ℂ)⁻¹ * (Complex.exp (Complex.I * ((meshAt L k 0 : ℝ) : ℂ) *
    (κ μ + 2 * (Real.pi : ℂ) * (m μ : ℂ))) - 1) = _
  rw [Complex.ofReal_inv, meshPhase, latticePhase, ← Complex.exp_add]
  have e : Complex.I * ((meshAt L k 0 : ℝ) : ℂ) * (κ μ + 2 * (Real.pi : ℂ) * (m μ : ℂ)) =
      Complex.I * ((meshAt L k 0 : ℝ) : ℂ) * κ μ +
        2 * (Real.pi : ℂ) * Complex.I * ((m μ : ℂ) * ((meshAt L k 0 : ℝ) : ℂ)) := by
    ring
  rw [e]
omit [Fintype (VertexClass L k)] in
theorem neg_shiftedFreq (κ : Fin 4 → ℂ) (m : Fin 4 → ℤ) :
    -PlaneWaves.shiftedFreq κ m = PlaneWaves.shiftedFreq (-κ) (-m) := by
  funext μ
  simp only [PlaneWaves.shiftedFreq, Pi.neg_apply, Int.cast_neg]
  ring
omit [Fintype (VertexClass L k)] in
theorem fourierPhase_add_axisStep' (m : Fin 4 → ℤ) (x : FullSpace.Vertex L k 0) (μ : Fin 4) :
    fourierPhase m ((x + InfiniteLattice.axisStep (meshAt L k 0) μ : FullSpace.Vertex L k 0) :
        AmbientSpace) =
      fourierPhase m (x : AmbientSpace) * latticePhase L k (-m) μ := by
  rw [fourierPhase_add_axisStep, latticePhase]
  congr 2
  simp only [Pi.neg_apply, Int.cast_neg]
  ring
theorem coeff_vertexSymbol (h : Hypotheses L k) (κ : Fin 4 → ℂ)
    (l : (colourVertices L k 0).UnitQuot → ℂ) (a : Fin 3) (μ : Fin 4) (m : Fin 4 → ℤ) :
    (edgeCoding h).coeff
        (symbolHom (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k) κ l) a μ m =
      PlaneWaves.forwardSymbol L k (PlaneWaves.shiftedFreq κ m) μ *
        (vertexCoding L k).coeff l a () m := by
  have e : (fun x => symbolHom (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k) κ l
      ((edgeCoding h).quot a μ x)) = fun x => (((meshAt L k 0)⁻¹ : ℝ) : ℂ) *
        (meshPhase L k κ μ * l ((vertexCoding L k).quot a ()
            (x + InfiniteLattice.axisStep _ μ)) - l ((vertexCoding L k).quot a () x)) :=
    funext fun x => symbolHom_vertexKernel h κ l a x μ
  rw [TripleCoding.coeff, e, scalarCoeff_const_mul, scalarCoeff_sub, scalarCoeff_const_mul,
    (vertexCoding L k).coeff_shift h l a () m μ, forwardSymbol_shiftedFreq, TripleCoding.coeff]
  ring
theorem coeff_edgeSymbol (h : Hypotheses L k) (κ : Fin 4 → ℂ)
    (b : (colourEdges L k 0).UnitQuot → ℂ) (a : Fin 3) (p : PlaneWaveCalculus.AxisPair)
    (m : Fin 4 → ℤ) :
    (faceCoding L k).coeff
        (symbolHom (colourEdges L k 0) (colourFaces L k 0) (edgeKernel L k) κ b) a p m =
      PlaneWaves.forwardSymbol L k (PlaneWaves.shiftedFreq κ m) p.1.1 *
          (edgeCoding h).coeff b a p.1.2 m -
        PlaneWaves.forwardSymbol L k (PlaneWaves.shiftedFreq κ m) p.1.2 *
          (edgeCoding h).coeff b a p.1.1 m := by
  have e : (fun x => symbolHom (colourEdges L k 0) (colourFaces L k 0) (edgeKernel L k) κ b
      ((faceCoding L k).quot a p x)) = fun x => (((meshAt L k 0)⁻¹ : ℝ) : ℂ) *
        (b ((edgeCoding h).quot a p.1.1 x) +
          meshPhase L k κ p.1.1 *
            b ((edgeCoding h).quot a p.1.2 (x + InfiniteLattice.axisStep _ p.1.1)) -
          meshPhase L k κ p.1.2 *
            b ((edgeCoding h).quot a p.1.1 (x + InfiniteLattice.axisStep _ p.1.2)) -
          b ((edgeCoding h).quot a p.1.2 x)) :=
    funext fun x => symbolHom_edgeKernel h κ b a x p
  rw [TripleCoding.coeff, e, scalarCoeff_const_mul, scalarCoeff_sub, scalarCoeff_sub, scalarCoeff_add,
    scalarCoeff_const_mul, scalarCoeff_const_mul,
    (edgeCoding h).coeff_shift h b a p.1.2 m p.1.1, (edgeCoding h).coeff_shift h b a p.1.1 m p.1.2,
    forwardSymbol_shiftedFreq, forwardSymbol_shiftedFreq, TripleCoding.coeff, TripleCoding.coeff]
  ring
def indicatorWave (h : Hypotheses L k) {I : PeriodicData} {D : Type} [DecidableEq D]
    (R : TripleCoding L k I D) (a : Fin 3) (d : D) (m : Fin 4 → ℤ) : I.UnitQuot → ℂ :=
  R.descend (fun a' d' x => if a' = a ∧ d' = d then fourierPhase m (x : AmbientSpace) else 0)
    (fun a' d' x n => by simp only [fourierPhase_vertexImage h])
omit [Fintype (VertexClass L k)] in
theorem indicatorWave_quot (h : Hypotheses L k) {I : PeriodicData} {D : Type} [DecidableEq D]
    (R : TripleCoding L k I D) (a : Fin 3) (d : D) (m : Fin 4 → ℤ) (a' : Fin 3) (d' : D)
    (x : FullSpace.Vertex L k 0) :
    indicatorWave h R a d m (R.quot a' d' x) =
      if a' = a ∧ d' = d then fourierPhase m (x : AmbientSpace) else 0 :=
  R.descend_quot _ _ _ _ _
theorem coeff_of_pairing (h : Hypotheses L k) {I I' : PeriodicData} {D D' : Type} [Fintype D]
    [DecidableEq D] [Fintype D'] (R : TripleCoding L k I D) (R' : TripleCoding L k I' D')
    [Fintype I.UnitQuot] [Fintype I'.UnitQuot] (a : Fin 3) (d : D) (m : Fin 4 → ℤ)
    (A : I.UnitQuot → ℂ) (f B : I'.UnitQuot → ℂ) (t : D' → ℂ)
    (hp : ∑ c, indicatorWave h R a d m c * A c = ∑ c', B c' * f c')
    (hB : ∀ a' d' x, B (R'.quot a' d' x) =
      if a' = a then t d' * fourierPhase m (x : AmbientSpace) else 0) :
    R.coeff A a d m = ∑ d', t d' * R'.coeff f a d' m := by
  have l : ∑ c, indicatorWave h R a d m c * A c =
      ∑ s : VertexClass L k, fourierPhase m (Quot.out s : FullSpace.Vertex L k 0) *
        A (R.quot a d (Quot.out s)) := by
    rw [R.sum_unitQuot]
    simp only [indicatorWave_quot]
    rw [Finset.sum_eq_single a, Finset.sum_eq_single d]
    · simp
    · intro d' _ hd
      simp [hd]
    · simp
    · intro a' _ ha
      simp [ha]
    · simp
  have r : ∑ c', B c' * f c' = ∑ d', t d' * ∑ s : VertexClass L k,
      fourierPhase m (Quot.out s : FullSpace.Vertex L k 0) * f (R'.quot a d' (Quot.out s)) := by
    rw [R'.sum_unitQuot]
    simp only [hB]
    rw [Finset.sum_eq_single a]
    · simp only [if_true, Finset.mul_sum, mul_assoc]
    · intro a' _ ha
      simp [ha]
    · simp
  simp only [TripleCoding.coeff, scalarCoeff]
  rw [← l, hp, r, Finset.mul_sum]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d' _ => Finset.sum_congr rfl fun s _ => ?_
  ring
omit [Fintype (VertexClass L k)] in
theorem quotWeight_of_const (I : PeriodicData) {w : ℝ} (hI : ∀ ι, I.weightOf ι = w)
    (c : I.UnitQuot) : I.quotWeight 1 c = w := by
  induction c using Quot.ind with
  | mk ι =>
    have hz : ∃ z, ∀ ι', I.mkQuot 1 ι' = Quot.mk _ ι → I.weightOf ι' = z :=
      ⟨w, fun ι' _ => hI ι'⟩
    exact (Classical.epsilon_spec hz ι rfl).symm.trans (hI ι)
variable [Fintype (colourVertices L k 0).UnitQuot] [Fintype (colourEdges L k 0).UnitQuot]
  [Fintype (colourFaces L k 0).UnitQuot]
omit [Fintype (colourFaces L k 0).UnitQuot] in
theorem coeff_vertexSymbol_transpose (h : Hypotheses L k) (κ : Fin 4 → ℂ)
    (b : (colourEdges L k 0).UnitQuot → ℂ) (a : Fin 3) (m : Fin 4 → ℤ) :
    (vertexCoding L k).coeff (symbolHom (colourEdges L k 0) (colourVertices L k 0)
        (kernelTranspose (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k)) κ b) a () m =
      ∑ μ, PlaneWaves.forwardSymbol L k (-PlaneWaves.shiftedFreq κ m) μ *
        (edgeCoding h).coeff b a μ m := by
  have hw₀ : meshAt L k 0 ^ 4 ≠ 0 := (pow_pos h.mesh_pos 4).ne'
  refine coeff_of_pairing h (vertexCoding L k) (edgeCoding h) a () m _ b
    (symbolHom (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k) (-κ)
      (indicatorWave h (vertexCoding L k) a () m)) _
    (sum_mul_symbolHom_transpose h.stripSymbols h.vertices h.edges
      (h.kernels.vertexCoboundary 0 (Nat.zero_le k)).finite_range.1
      (h.kernels.vertexCoboundary 0 (Nat.zero_le k)).finite_range.2.1 hw₀
      (quotWeight_of_const _ fun _ => rfl) (quotWeight_of_const _ fun _ => rfl) κ _ b) ?_
  intro a' μ x
  rw [symbolHom_vertexKernel, indicatorWave_quot, indicatorWave_quot]
  by_cases ha : a' = a
  · subst ha
    simp only [and_self, if_true, fourierPhase_add_axisStep', neg_shiftedFreq, forwardSymbol_shiftedFreq]
    ring
  · simp [ha]
omit [Fintype (colourVertices L k 0).UnitQuot] in
theorem coeff_edgeSymbol_transpose (h : Hypotheses L k) (κ : Fin 4 → ℂ)
    (f : (colourFaces L k 0).UnitQuot → ℂ) (a : Fin 3) (ν : Fin 4) (m : Fin 4 → ℤ) :
    (edgeCoding h).coeff (symbolHom (colourFaces L k 0) (colourEdges L k 0)
        (kernelTranspose (colourEdges L k 0) (colourFaces L k 0) (edgeKernel L k)) κ f)
        a ν m =
      ∑ p : PlaneWaveCalculus.AxisPair,
        ((if p.1.2 = ν then PlaneWaves.forwardSymbol L k (-PlaneWaves.shiftedFreq κ m) p.1.1 else 0) -
          (if p.1.1 = ν then PlaneWaves.forwardSymbol L k (-PlaneWaves.shiftedFreq κ m) p.1.2
            else 0)) *
        (faceCoding L k).coeff f a p m := by
  have hw₀ : meshAt L k 0 ^ 4 ≠ 0 := (pow_pos h.mesh_pos 4).ne'
  refine coeff_of_pairing h (edgeCoding h) (faceCoding L k) a ν m _ f
    (symbolHom (colourEdges L k 0) (colourFaces L k 0) (edgeKernel L k) (-κ)
      (indicatorWave h (edgeCoding h) a ν m)) _
    (sum_mul_symbolHom_transpose h.stripSymbols h.edges h.faces
      (h.kernels.edgeCoboundary 0 (Nat.zero_le k)).finite_range.1
      (h.kernels.edgeCoboundary 0 (Nat.zero_le k)).finite_range.2.1 hw₀
      (quotWeight_of_const _ fun _ => rfl) (quotWeight_of_const _ fun _ => rfl) κ _ f) ?_
  intro a' p x
  rw [symbolHom_edgeKernel h, indicatorWave_quot, indicatorWave_quot, indicatorWave_quot,
    indicatorWave_quot]
  by_cases ha : a' = a
  · subst ha
    simp only [true_and, if_true, neg_shiftedFreq, forwardSymbol_shiftedFreq]
    by_cases h₁ : p.1.1 = ν <;> by_cases h₂ : p.1.2 = ν <;>
      simp only [h₁, h₂, if_true, if_false, fourierPhase_add_axisStep'] <;> ring
  · simp [ha]
end Coefficients
section Assembly
variable [Fintype (VertexClass L k)]
theorem vertexFourierCoeff_eq (l : (colourVertices L k 0).UnitQuot → ℂ) (m : Fin 4 → ℤ) :
    PlaneWaves.vertexFourierCoeff L k l m =
      pauliSum fun a => (vertexCoding L k).coeff l a () m :=
  fourierCoeff_ofPauliCoeffs (fun ι => l ((colourVertices L k 0).mkQuot 1 ι)) m
theorem edgeFourierCoeff_eq (h : Hypotheses L k) (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4)
    (m : Fin 4 → ℤ) :
    PlaneWaves.edgeFourierCoeff L k b μ m = pauliSum fun a => (edgeCoding h).coeff b a μ m :=
  fourierCoeff_ofPauliCoeffs
    (fun ι => b ((colourEdges L k 0).mkQuot 1 (ι.1, posEdgeForward ι.2 μ))) m
theorem faceFourierCoeff_eq (f : (colourFaces L k 0).UnitQuot → ℂ) (μ ν : Fin 4)
    (hμν : μ < ν) (m : Fin 4 → ℤ) :
    PlaneWaves.faceFourierCoeff L k f μ ν hμν m =
      pauliSum fun a => (faceCoding L k).coeff f a ⟨(μ, ν), hμν⟩ m :=
  fourierCoeff_ofPauliCoeffs
    (fun ι => f ((colourFaces L k 0).mkQuot 1 (ι.1, ⟨ι.2, μ, ν, hμν⟩))) m
omit [Fintype (VertexClass L k)] in
theorem sum_axisPair (F : Fin 4 → Fin 4 → ℂ) :
    ∑ p : PlaneWaveCalculus.AxisPair, F p.1.1 p.1.2 =
      F 0 1 + F 0 2 + F 0 3 + F 1 2 + F 1 3 + F 2 3 := by
  have e : (Finset.univ.filter fun p : Fin 4 × Fin 4 => p.1 < p.2) =
      {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
  have e₂ : ∑ p ∈ Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2), F p.1 p.2 =
      ∑ p : PlaneWaveCalculus.AxisPair, F p.1.1 p.1.2 :=
    Finset.sum_subtype _ (by simp) (fun p : Fin 4 × Fin 4 => F p.1 p.2)
  refine e₂.symm.trans ?_
  rw [e, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
omit [Fintype (VertexClass L k)] in
theorem sum_axisPair_add_sum (d e c : Fin 4 → ℂ) (ν : Fin 4) :
    (∑ p : PlaneWaveCalculus.AxisPair,
        ((if p.1.2 = ν then e p.1.1 else 0) - (if p.1.1 = ν then e p.1.2 else 0)) *
          (d p.1.1 * c p.1.2 - d p.1.2 * c p.1.1)) +
      d ν * ∑ μ, e μ * c μ = (∑ μ, d μ * e μ) * c ν := by
  refine Eq.trans (congrArg (· + _) (sum_axisPair fun u v =>
    ((if v = ν then e u else 0) - (if u = ν then e v else 0)) * (d u * c v - d v * c u))) ?_
  simp only [Fin.sum_univ_four]
  fin_cases ν <;> simp <;> ring
omit [Fintype (VertexClass L k)] in
theorem edgeKernel_comp_vertexKernel (h : Hypotheses L k) :
    compKernel (edgeKernel L k) (vertexKernel L k) = 0 := by
  classical
  funext ι' ι
  show compKernel (edgeKernel L k) (vertexKernel L k) ι' ι = (0 : ℂ)
  let δ : Fin 3 × FullSpace.Vertex L k 0 → ℂ := fun y => if y = ι then 1 else 0
  have c : ∀ y, vertexKernel L k y ι =
      (vertexCoordinate (FullSpace.Vertex L k 0)).mapOnCoeffs (FullSpace.edgePauliCoordinates L k 0)
        FullSpace.scaledVertexCoboundary δ y := fun y => by
    have e := congrFun ((h.kernels.vertexCoboundary 0 (Nat.zero_le k)).applyKernel_eq δ) y
    refine Eq.trans ?_ e
    show _ = ∑' x, vertexKernel L k y x * δ x
    rw [tsum_eq_single ι]
    · simp [δ]
    · intro x hx
      simp [δ, hx]
  have e₁ : compKernel (edgeKernel L k) (vertexKernel L k) ι' ι =
      applyKernel (edgeKernel L k) ((vertexCoordinate (FullSpace.Vertex L k 0)).mapOnCoeffs
        (FullSpace.edgePauliCoordinates L k 0) FullSpace.scaledVertexCoboundary δ) ι' :=
    tsum_congr fun y => by rw [c y]
  refine e₁.trans
    ((congrFun ((h.kernels.edgeCoboundary 0 (Nat.zero_le k)).applyKernel_eq _) ι').trans ?_)
  obtain ⟨a, ⟨x, μ, ν, hμν⟩⟩ := ι'
  refine (mapOnCoeffs_face _ a x μ ν hμν).trans ?_
  have key : ∀ (c t₁ t₂ t₃ t₄ : ℂ) (u₀ u₁ u₂ u₃ : ℂ), t₁ = c * (u₁ - u₀) → t₂ = c * (u₃ - u₁) →
      t₃ = c * (u₃ - u₂) → t₄ = c * (u₂ - u₀) → c * (t₁ + t₂ - t₃ - t₄) = 0 := by
    intro c t₁ t₂ t₃ t₄ u₀ u₁ u₂ u₃ e₁ e₂ e₃ e₄
    rw [e₁, e₂, e₃, e₄]
    ring
  have e₃ := mapOnCoeffs_vertex (L := L) (k := k) δ a (x + InfiniteLattice.axisStep _ ν) μ
  rw [add_right_comm x (InfiniteLattice.axisStep _ ν)] at e₃
  exact key _ _ _ _ _ _ _ _ _ (mapOnCoeffs_vertex δ a x μ) (mapOnCoeffs_vertex δ a _ ν) e₃
    (mapOnCoeffs_vertex δ a x ν)
omit [Fintype (VertexClass L k)] in
theorem transpose_comp_transpose_eq_zero (h : Hypotheses L k) :
    compKernel
      (kernelTranspose (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k))
      (kernelTranspose (colourEdges L k 0) (colourFaces L k 0) (edgeKernel L k)) = 0 := by
  funext ι ι''
  have e := congrFun (congrFun (edgeKernel_comp_vertexKernel h) ι'') ι
  have hw : ((meshAt L k 0 ^ 4 / meshAt L k 0 ^ 4 : ℝ) : ℂ) = 1 := by
    rw [div_self (pow_pos h.mesh_pos 4).ne', Complex.ofReal_one]
  refine (tsum_congr fun y => ?_).trans e
  show ((meshAt L k 0 ^ 4 / meshAt L k 0 ^ 4 : ℝ) : ℂ) * vertexKernel L k y ι *
      (((meshAt L k 0 ^ 4 / meshAt L k 0 ^ 4 : ℝ) : ℂ) * edgeKernel L k ι'' y) =
    edgeKernel L k ι'' y * vertexKernel L k y ι
  rw [hw]
  ring
omit [Fintype (VertexClass L k)] in
theorem symbolHom_Delta (h : Hypotheses L k) (κ : Fin 4 → ℂ) :
    symbolHom (colourVertices L k 0) (colourVertices L k 0) (PlaneWaveCalculus.freeOps L k).Delta κ =
      (symbolHom (colourEdges L k 0) (colourVertices L k 0)
        (kernelTranspose (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k)) κ).comp
      (symbolHom (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k) κ) := by
  obtain ⟨-, -, -, -, -, hOne, -⟩ := h.rescaled
  have e : (PlaneWaveCalculus.freeOps L k).Delta = compKernel
      (kernelTranspose (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k))
      (vertexKernel L k) := hOne.Delta_eq
  have pt := h.finiteRange.vertexCoboundary_transpose 0 (Nat.zero_le k)
  have st := (h.stripSymbols.2.1 _ _ h.edges h.vertices)
  have ft := st.1.finiteRange _ pt.1 pt.2.1 κ (mem_univ _)
  exact (congrArg (fun T => symbolHom (colourVertices L k 0) (colourVertices L k 0) T κ) e).trans
    ((st.2.1 _ κ pt.1 ft).comp _ h.vertices _
      (h.kernels.vertexCoboundary 0 (Nat.zero_le k)).finite_range.1 (vertexKernel_summable h κ)).2.2.2
omit [Fintype (VertexClass L k)] in
theorem symbolHom_K (h : Hypotheses L k) (κ : Fin 4 → ℂ) :
    symbolHom (colourEdges L k 0) (colourEdges L k 0) (PlaneWaveCalculus.freeOps L k).K κ =
      (symbolHom (colourFaces L k 0) (colourEdges L k 0)
        (kernelTranspose (colourEdges L k 0) (colourFaces L k 0) (edgeKernel L k)) κ).comp
        (symbolHom (colourEdges L k 0) (colourFaces L k 0) (edgeKernel L k) κ) +
      (symbolHom (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k) κ).comp
        (symbolHom (colourEdges L k 0) (colourVertices L k 0)
          (kernelTranspose (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k)) κ) := by
  obtain ⟨-, -, -, -, -, hOne, -⟩ := h.rescaled
  have ps := h.finiteRange.vertexCoboundary_transpose 0 (Nat.zero_le k)
  have pp := h.finiteRange.edgeCoboundary_transpose 0 (Nat.zero_le k)
  have sE := h.stripSymbols.2.1 _ _ h.edges h.vertices
  have sF := h.stripSymbols.2.1 _ _ h.faces h.edges
  have sV := h.stripSymbols.2.1 _ _ h.vertices h.edges
  have fs := sE.1.finiteRange _ ps.1 ps.2.1 κ (mem_univ _)
  have fp := sF.1.finiteRange _ pp.1 pp.2.1 κ (mem_univ _)
  obtain ⟨-, qA, fA, eA⟩ := (sF.2.1 _ κ pp.1 fp).comp _ h.edges _
    (h.kernels.edgeCoboundary 0 (Nat.zero_le k)).finite_range.1 (edgeKernel_summable h κ)
  obtain ⟨-, qC, fC, eC⟩ := (sV.2.1 _ κ (h.kernels.vertexCoboundary 0 (Nat.zero_le k)).finite_range.1
    (vertexKernel_summable h κ)).comp _ h.edges _ ps.1 fs
  have sEE := h.stripSymbols.2.1 _ _ h.edges h.edges
  have eK := ((sEE.2.1 _ κ qA fA).linComb _ qC fC 1 1).2.2
  have e₂ : (PlaneWaveCalculus.freeOps L k).K = StripSymbols.linCombKernel 1 1
      (compKernel
        (kernelTranspose (colourEdges L k 0) (colourFaces L k 0) (edgeKernel L k))
        (edgeKernel L k))
      (compKernel (vertexKernel L k)
        (kernelTranspose (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k))) := by
    funext ι' ι
    refine (congrFun (congrFun hOne.K_eq ι') ι).trans ?_
    show (_ : ℂ) + _ = 1 * _ + 1 * _
    rw [one_mul, one_mul]
    rfl
  refine (congrArg (fun T => symbolHom (colourEdges L k 0) (colourEdges L k 0) T κ) e₂).trans
    (eK.trans ?_)
  rw [one_smul, one_smul, eA, eC]
variable [Fintype (colourVertices L k 0).UnitQuot] [Fintype (colourEdges L k 0).UnitQuot]
  [Fintype (colourFaces L k 0).UnitQuot]
theorem coboundarySymbols (h : Hypotheses L k) : PlaneWaveCalculus.CoboundarySymbols L k where
  vertexCoboundary κ l μ m _ := by
    rw [edgeFourierCoeff_eq h, vertexFourierCoeff_eq, smul_pauliSum]
    exact congrArg pauliSum (funext fun a => coeff_vertexSymbol h κ l a μ m)
  edgeCoboundary κ b μ ν hμν m _ := by
    rw [faceFourierCoeff_eq, edgeFourierCoeff_eq h, edgeFourierCoeff_eq h, smul_pauliSum,
      smul_pauliSum, pauliSum_sub_pauliSum]
    exact congrArg pauliSum (funext fun a => coeff_edgeSymbol h κ b a ⟨(μ, ν), hμν⟩ m)
  vertexCoboundary_transpose κ b m _ := by
    rw [vertexFourierCoeff_eq]
    simp only [edgeFourierCoeff_eq h, smul_pauliSum]
    rw [sum_pauliSum]
    exact congrArg pauliSum (funext fun a => coeff_vertexSymbol_transpose h κ b a m)
  K κ b μ m _ := by
    rw [symbolHom_K h, edgeFourierCoeff_eq h, edgeFourierCoeff_eq h, smul_pauliSum]
    refine congrArg pauliSum (funext fun a => ?_)
    have e : (edgeCoding h).coeff (fun c => ((symbolHom (colourFaces L k 0) (colourEdges L k 0)
          (kernelTranspose (colourEdges L k 0) (colourFaces L k 0) (edgeKernel L k)) κ).comp
          (symbolHom (colourEdges L k 0) (colourFaces L k 0) (edgeKernel L k) κ) b) c +
        ((symbolHom (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k) κ).comp
          (symbolHom (colourEdges L k 0) (colourVertices L k 0)
            (kernelTranspose (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k)) κ) b) c)
        a μ m = _ := scalarCoeff_add m _ _
    refine Eq.trans e ?_
    have e₁ := coeff_edgeSymbol_transpose h κ
      (symbolHom (colourEdges L k 0) (colourFaces L k 0) (edgeKernel L k) κ b) a μ m
    have e₂ := coeff_vertexSymbol h κ (symbolHom (colourEdges L k 0) (colourVertices L k 0)
      (kernelTranspose (colourVertices L k 0) (colourEdges L k 0) (vertexKernel L k)) κ b) a μ m
    rw [coeff_vertexSymbol_transpose h κ b a m] at e₂
    simp only [coeff_edgeSymbol h κ b a _ m] at e₁
    refine (congrArg₂ (· + ·) e₁ e₂).trans ?_
    exact sum_axisPair_add_sum
      (PlaneWaves.forwardSymbol L k (PlaneWaves.shiftedFreq κ m))
      (PlaneWaves.forwardSymbol L k (-PlaneWaves.shiftedFreq κ m))
      (fun ρ => (edgeCoding h).coeff b a ρ m) μ
  Delta κ l m _ := by
    rw [symbolHom_Delta h, vertexFourierCoeff_eq, vertexFourierCoeff_eq, smul_pauliSum]
    refine congrArg pauliSum (funext fun a => ?_)
    refine (coeff_vertexSymbol_transpose h κ _ a m).trans ?_
    simp only [coeff_vertexSymbol h κ l a _ m, PlaneWaves.symbolSquare, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    ring
  coboundary_comp_coboundary := edgeKernel_comp_vertexKernel h
  transpose_comp_transpose := transpose_comp_transpose_eq_zero h
end Assembly
end Tower
theorem coboundarySymbolsOnPlaneWaves_holds (hC : SymbolOnQuotients.Claim)
    (hS : StripSymbols.Claim) (hI : TowerIndexSets.Claim) (hG : TowerTranslations.Claim)
    (hF : FreeOperators.FreeOperatorsArePeriodic) (hR : RescaledConditions.Holds) :
    CoboundarySymbolsOnPlaneWaves := by
  intro L hL k hk
  have hz := Nat.zero_le k
  have h : Hypotheses L k :=
    { symbolOnQuot := hC
      stripSymbols := hS
      vertices := (hI L hL k 0 hz).1
      edges := (hI L hL k 0 hz).2.1
      faces := (hI L hL k 0 hz).2.2
      kernels := (hF.2 L hL k hk).1
      finiteRange := (hF.2 L hL k hk).2
      rescaled := (hR L hL k hk).2
      vertexImage_coe := fun n x => ((hG L hL k 0 hk hz n).2.1 x).1
      edge_translate := fun n c b μ e => (hG L hL k 0 hk hz n).2.2.2.1 c b μ e
      mesh_pos := zpow_pos (by have := hL.2; positivity) _ }
  have := h.vertices.finite_quot
  have := h.edges.finite_quot
  have := h.faces.finite_quot
  have : Finite (VertexClass L k) :=
    Finite.of_injective (fun s => (vertexCoding L k).equivUnitQuot (0, (), s)) fun s s' e => by
      simpa using (vertexCoding L k).equivUnitQuot.injective e
  let _ := Fintype.ofFinite (VertexClass L k)
  let _ := Fintype.ofFinite (colourVertices L k 0).UnitQuot
  let _ := Fintype.ofFinite (colourEdges L k 0).UnitQuot
  let _ := Fintype.ofFinite (colourFaces L k 0).UnitQuot
  exact coboundarySymbols h
end YangMills.Construction.Tower.PlaneWaveCoboundaries
end
