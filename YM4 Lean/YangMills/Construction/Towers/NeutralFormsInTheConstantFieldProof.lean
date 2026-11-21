import YangMills.Construction.Towers.FirstCoefficientOnTheGaugeColumnProof
import YangMills.Construction.Towers.GaugeRelationOfTheChargedSymbolProof
import YangMills.Construction.InfiniteLattice.BondsAndTheirVariablesProof
import YangMills.Construction.Towers.ChargedSymbolAtFluxZeroProof
import YangMills.Construction.Towers.CoefficientsOfASymbol
import YangMills.Construction.Towers.LowerBoundsOfTheAbelianOperatorsProof
import YangMills.Construction.Towers.NeutralFormsInTheConstantField
import YangMills.Construction.Towers.QuantizationIsTheSumOfItsSeries
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Tower.UnitLatticeL2 Tower.UnitaryCombinations
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (toComplexVec castVec bilinDot)
open Matrices (ComplexMatrix2)
open scoped ComplexConjugate
noncomputable section
namespace Tower.ConstantFieldSymbols
open MagneticWeyl AbelianFieldDensity AbelianFieldDensity.SectorDecomposition Massive
open MagneticWeyl.FluxZeroCalculus (latticePoint)
namespace NeutralSectorProof
section CharacterSums
variable {ι : Type} [Fintype ι]
def finiteCharSum (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin 4) (Fin 4) ℂ) (q : AmbientSpace) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ i, MagneticWeyl.fourierChar (n i) q • c i
def gatheredCoeff (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin 4) (Fin 4) ℂ) (m : Fin 4 → ℤ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ i, if m = n i then c i else 0
theorem hasFourierExpansion_gatheredCoeff (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin 4) (Fin 4) ℂ) :
    HasFourierExpansion (gatheredCoeff n c) (finiteCharSum n c) := by
  intro q
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      HasSum (fun m => if m = n i then MagneticWeyl.fourierChar (n i) q • c i else 0)
        (MagneticWeyl.fourierChar (n i) q • c i) := fun i _ => hasSum_ite_eq _ _
  have htot : HasSum (fun m => ∑ i, if m = n i then MagneticWeyl.fourierChar (n i) q • c i else 0)
      (finiteCharSum n c q) := hasSum_sum hterm
  convert htot using 2 with m
  rw [gatheredCoeff, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hm
  · rw [hm]
  · simp
theorem opNormValue_zero : Matrices.RectangularMatrix.opNormValue (0 : Matrix (Fin 4) (Fin 4) ℂ) = 0 := by
  simp [Matrices.RectangularMatrix.opNormValue, OneLoopNotation.opNormOf]
theorem summable_opNormValue_gatheredCoeff (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin 4) (Fin 4) ℂ) :
    Summable fun m => Matrices.RectangularMatrix.opNormValue (gatheredCoeff n c m) := by
  refine summable_of_hasFiniteSupport ((Set.finite_range n).subset fun m hm => ?_)
  by_contra hrange
  apply hm
  have : gatheredCoeff n c m = 0 := by
    refine Finset.sum_eq_zero fun i _ => if_neg fun hm' => hrange ⟨i, hm'.symm⟩
  simp [this, opNormValue_zero]
theorem hasAbsSummableFourier_finiteCharSum (n : ι → Fin 4 → ℤ)
    (c : ι → Matrix (Fin 4) (Fin 4) ℂ) : HasAbsSummableFourier (finiteCharSum n c) :=
  ⟨gatheredCoeff n c, hasFourierExpansion_gatheredCoeff n c, summable_opNormValue_gatheredCoeff n c⟩
theorem fourierCoeff_finiteCharSum (hCoeff : FourierCoeffsOfSymbol) (n : ι → Fin 4 → ℤ)
    (c : ι → Matrix (Fin 4) (Fin 4) ℂ) : fourierCoeff (finiteCharSum n c) = gatheredCoeff n c :=
  (((hCoeff 4 4 (finiteCharSum n c)).1 (hasAbsSummableFourier_finiteCharSum n c)).2.2 _
    (hasFourierExpansion_gatheredCoeff n c) (summable_opNormValue_gatheredCoeff n c)).symm
variable {L : ℕ}
theorem matMulUnitaryOp_apply (hUnit : UnitaryOperatorSeriesClaim)
    {V : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hV : IsUnitaryOp V)
    (X : Matrix (Fin 4) (Fin 4) ℂ) (w : VectorL2 L 4) (x : FullSpace.Vertex L 0 0) :
    matMulUnitaryOp X V w x = matMulUnitary X V w x :=
  ((hUnit L 4 4).1 X V hV).1 w x
theorem matMulUnitaryOp_sum (hUnit : UnitaryOperatorSeriesClaim)
    {V : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hV : IsUnitaryOp V)
    (X : ι → Matrix (Fin 4) (Fin 4) ℂ) :
    matMulUnitaryOp (∑ i, X i) V = ∑ i, matMulUnitaryOp (X i) V := by
  refine ContinuousLinearMap.ext fun w => lp.ext (funext fun x => ?_)
  rw [_root_.sum_apply, lp.coeFn_sum, Finset.sum_apply, matMulUnitaryOp_apply hUnit hV]
  simp only [matMulUnitaryOp_apply hUnit hV, matMulUnitary, map_sum, LinearMap.sum_apply]
theorem matMulUnitaryOp_zero (hUnit : UnitaryOperatorSeriesClaim)
    {V : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hV : IsUnitaryOp V) :
    matMulUnitaryOp (0 : Matrix (Fin 4) (Fin 4) ℂ) V = 0 := by
  refine ContinuousLinearMap.ext fun w => lp.ext (funext fun x => ?_)
  rw [matMulUnitaryOp_apply hUnit hV]
  simp [matMulUnitary]
theorem weylQuant_finiteCharSum (hSum : WeylQuantHasSum)
    (hCoeff : FourierCoeffsOfSymbol)
    (hUnit : UnitaryOperatorSeriesClaim)
    (φ : ℝ) (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin 4) (Fin 4) ℂ) :
    weylQuant L φ (finiteCharSum n c) =
      ∑ i, matMulUnitaryOp (c i) (magneticWeyl L φ (n i)) := by
  have hser := (hSum L φ 4 4 (finiteCharSum n c) (hasAbsSummableFourier_finiteCharSum n c)).1
  rw [fourierCoeff_finiteCharSum hCoeff] at hser
  refine hser.unique ?_
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      HasSum (fun m => if m = n i then matMulUnitaryOp (c i) (magneticWeyl L φ (n i))
          else 0)
        (matMulUnitaryOp (c i) (magneticWeyl L φ (n i))) :=
    fun i _ => hasSum_ite_eq _ _
  convert hasSum_sum hterm using 2 with m
  have hV : IsUnitaryOp (magneticWeyl L φ m) := magneticWeyl_isUnitary φ m
  rw [gatheredCoeff, matMulUnitaryOp_sum hUnit hV]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hm
  · rw [hm]
  · exact matMulUnitaryOp_zero hUnit hV
theorem weylQuant_zero_finiteCharSum_apply (hSum : WeylQuantHasSum)
    (hCoeff : FourierCoeffsOfSymbol)
    (hUnit : UnitaryOperatorSeriesClaim)
    (hTrans : MagneticWeyl.FluxZeroCalculus.MagneticWeylIsTranslation L)
    (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin 4) (Fin 4) ℂ) (v : VectorL2 L 4)
    (k : Fin 4 → ℤ) (i : Fin 4) :
    weylQuant L 0 (finiteCharSum n c) v (latticePoint L k) i =
      ∑ p, ∑ j, c p i j * v (latticePoint L (k + n p)) j := by
  rw [weylQuant_finiteCharSum hSum hCoeff hUnit, _root_.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, matMulUnitaryOp_apply hUnit (magneticWeyl_isUnitary 0 _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hshift : ∀ j, magneticWeyl L 0 (n p) (coord v j) (latticePoint L k) 0 =
      v (latticePoint L (k + n p)) j := fun j => by
    rw [hTrans]
    simp [coord]
  simp [matMulUnitary, applyCoordwise, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, hshift]
end CharacterSums
section SymbolAsSum
def basisVec (μ : Fin 4) : Fin 4 → ℤ := Pi.single μ 1
theorem intDot_eq_sum (n : Fin 4 → ℤ) (q : AmbientSpace) :
    MagneticWeyl.intDot n q = ∑ μ, (n μ : ℂ) * (q μ : ℂ) := by
  simp [MagneticWeyl.intDot, bilinDot, toComplexVec, castVec]
theorem fourierChar_add (n m : Fin 4 → ℤ) (q : AmbientSpace) :
    MagneticWeyl.fourierChar (n + m) q =
      MagneticWeyl.fourierChar n q * MagneticWeyl.fourierChar m q := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.FluxZero.fourierChar_add <;> assumption
theorem fourierChar_zero (q : AmbientSpace) : MagneticWeyl.fourierChar 0 q = 1 := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.FluxZero.fourierChar_zero <;> assumption
theorem fourierChar_basisVec (μ : Fin 4) (q : AmbientSpace) :
    MagneticWeyl.fourierChar (basisVec μ) q = Complex.exp (Complex.I * (q μ : ℂ)) := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.GaugeColumnFirstCoeff.fourierChar_basisIndex <;> assumption
theorem fourierChar_neg_basisVec (μ : Fin 4) (q : AmbientSpace) :
    MagneticWeyl.fourierChar (-basisVec μ) q = Complex.exp (-(Complex.I * (q μ : ℂ))) := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.GaugeRelation.fourierChar_neg_basisVec <;> assumption
def faceRowShift : Fin 3 → Fin 4 → ℤ := ![0, basisVec 1, basisVec 0]
def faceRowCoeff : Fin 3 → Fin 4 → ℂ := ![![1, -1, 0, 0], ![-1, 0, 0, 0], ![0, 1, 0, 0]]
theorem faceRow_eq_sum (q : AmbientSpace) (j : Fin 4) :
    faceRow q 0 j = ∑ a, MagneticWeyl.fourierChar (faceRowShift a) q * faceRowCoeff a j := by
  simp only [Fin.sum_univ_three, faceRowShift, faceRowCoeff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, fourierChar_zero, fourierChar_basisVec, faceRow, Matrix.of_apply]
  fin_cases j <;> simp <;> ring
theorem conj_faceRowCoeff (a : Fin 3) (j : Fin 4) : conj (faceRowCoeff a j) = faceRowCoeff a j := by
  fin_cases a <;> fin_cases j <;> simp [faceRowCoeff]
theorem conj_fourierChar (n : Fin 4 → ℤ) (q : AmbientSpace) :
    conj (MagneticWeyl.fourierChar n q) = MagneticWeyl.fourierChar (-n) q := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.FluxZero.conj_fourierChar <;> assumption
def neutralShifts : (Fin 4 × Fin 3) ⊕ (Fin 3 × Fin 3) → Fin 4 → ℤ
  | .inl p => ![0, basisVec p.1, -basisVec p.1] p.2
  | .inr p => -faceRowShift p.1 + faceRowShift p.2
def neutralCoeffs (κ : ℂ) : (Fin 4 × Fin 3) ⊕ (Fin 3 × Fin 3) → Matrix (Fin 4) (Fin 4) ℂ
  | .inl p => ![(2 : ℂ) • 1, -1, -1] p.2
  | .inr p => Matrix.of fun i j => (κ - 1) * (faceRowCoeff p.1 i * faceRowCoeff p.2 j)
theorem neutralSectorSymbol_eq_finiteCharSum (f : ℝ) :
    neutralSectorSymbol f = finiteCharSum neutralShifts (neutralCoeffs (Real.cos f : ℂ)) := by
  funext q
  ext i j
  have hcos : ∀ t : ℝ, 2 * Complex.cos (t : ℂ) =
      Complex.exp (Complex.I * (t : ℂ)) + Complex.exp (-(Complex.I * (t : ℂ))) := fun t => by
    rw [Complex.two_cos]
    ring_nf
  have hsym : Massive.latticeSymbol (toComplexVec q) = ∑ μ, (2 - (Complex.exp (Complex.I * (q μ : ℂ)) +
      Complex.exp (-(Complex.I * (q μ : ℂ))))) :=
    Finset.sum_congr rfl fun μ _ => by rw [axisSymbol, ← hcos]; rfl
  have hgram : faceGram q i j = ∑ a, ∑ b, MagneticWeyl.fourierChar (-faceRowShift a + faceRowShift b) q *
      (faceRowCoeff a i * faceRowCoeff b j) := by
    simp only [faceGram, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_one,
      RCLike.star_def, faceRow_eq_sum, map_sum, map_mul, conj_faceRowCoeff, conj_fourierChar,
      fourierChar_add, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hlap : ∀ μ : Fin 4, ∑ k : Fin 3,
      MagneticWeyl.fourierChar (neutralShifts (.inl (μ, k))) q *
        neutralCoeffs (Real.cos f : ℂ) (.inl (μ, k)) i j =
      (2 - (Complex.exp (Complex.I * (q μ : ℂ)) + Complex.exp (-(Complex.I * (q μ : ℂ))))) *
        (1 : Matrix (Fin 4) (Fin 4) ℂ) i j := fun μ => by
    rw [Fin.sum_univ_three]
    change MagneticWeyl.fourierChar 0 q * ((2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) i j +
      MagneticWeyl.fourierChar (basisVec μ) q * (-1 : Matrix (Fin 4) (Fin 4) ℂ) i j +
      MagneticWeyl.fourierChar (-basisVec μ) q * (-1 : Matrix (Fin 4) (Fin 4) ℂ) i j = _
    rw [fourierChar_zero, fourierChar_basisVec, fourierChar_neg_basisVec]
    simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
    ring
  simp only [finiteCharSum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Fintype.sum_sum_type,
    Fintype.sum_prod_type, hlap]
  simp only [neutralSectorSymbol, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hsym, hgram,
    ← Finset.sum_mul]
  congr 1
  simp only [neutralShifts, neutralCoeffs, Matrix.of_apply, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
def neutralStencil (κ : ℂ) (V : (Fin 4 → ℤ) → Fin 4 → ℂ) (k : Fin 4 → ℤ) (i : Fin 4) : ℂ :=
  (∑ μ, (2 * V k i - V (k + basisVec μ) i - V (k + -basisVec μ) i)) +
    (κ - 1) * ∑ a, ∑ b, ∑ j, faceRowCoeff a i * faceRowCoeff b j * V (k + (-faceRowShift a + faceRowShift b)) j
theorem weylQuant_neutralSectorSymbol_apply {L : ℕ} (hSum : WeylQuantHasSum)
    (hCoeff : FourierCoeffsOfSymbol)
    (hUnit : UnitaryOperatorSeriesClaim)
    (hTrans : MagneticWeyl.FluxZeroCalculus.MagneticWeylIsTranslation L)
    (f : ℝ) (v : VectorL2 L 4) (k : Fin 4 → ℤ) (i : Fin 4) :
    weylQuant L 0 (neutralSectorSymbol f) v (latticePoint L k) i =
      neutralStencil (Real.cos f : ℂ) (fun m j => v (latticePoint L m) j) k i := by
  rw [neutralSectorSymbol_eq_finiteCharSum, weylQuant_zero_finiteCharSum_apply hSum hCoeff hUnit hTrans]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, neutralStencil]
  congr 1
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Fin.sum_univ_three]
    change (∑ j, ((2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) i j * v (latticePoint L (k + 0)) j) +
      (∑ j, (-1 : Matrix (Fin 4) (Fin 4) ℂ) i j * v (latticePoint L (k + basisVec μ)) j) +
      (∑ j, (-1 : Matrix (Fin 4) (Fin 4) ℂ) i j * v (latticePoint L (k + -basisVec μ)) j) = _
    simp [Matrix.one_apply]
    ring
  · simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun j _ => ?_
    simp only [neutralShifts, neutralCoeffs, Matrix.of_apply]
    ring
end SymbolAsSum
section EdgeOperator
variable {a : ℝ}
def edgeOperator (θ c : FullSpace.PositiveEdge a → ℝ) : FullSpace.PositiveEdge a → ℝ := fun b =>
  FullSpace.faceAdjoint (fun p => Real.cos (FullSpace.faceAngle θ p) *
      FullSpace.edgeDifference c p) b +
    FullSpace.vertexDifference (FullSpace.vertexAdjoint c) b
def edgeQuadForm (θ c c' : FullSpace.PositiveEdge a → ℝ) : ℝ :=
  (∑ᶠ p, Real.cos (FullSpace.faceAngle θ p) * FullSpace.edgeDifference c p *
      FullSpace.edgeDifference c' p) +
    ∑ᶠ x, FullSpace.vertexAdjoint c x * FullSpace.vertexAdjoint c' x
theorem edgeQuadForm_comm (θ c c' : FullSpace.PositiveEdge a → ℝ) :
    edgeQuadForm θ c c' = edgeQuadForm θ c' c := by
  unfold edgeQuadForm
  congr 1
  · exact finsum_congr fun p => by ring
  · exact finsum_congr fun x => by ring
theorem forwardEdge_initial_injective (μ : Fin 4) :
    Function.Injective fun x : InfiniteLattice.LatticePoint a => FullSpace.forwardEdge x μ := fun _ _ h =>
  congrArg InfiniteLattice.Link.initial (congrArg Subtype.val h)
theorem vertexAdjoint_support_finite (hV : FullSpace.VertexAdjointProperties ℝ a)
    (c : FullSpace.PositiveEdge a → ℝ)
    (hc : (Function.support c).Finite) : (Function.support (FullSpace.vertexAdjoint c)).Finite := by
  have hfwd : ∀ μ : Fin 4,
      ({x : InfiniteLattice.LatticePoint a | c (FullSpace.forwardEdge x μ) ≠ 0}).Finite := fun μ =>
    hc.preimage (f := fun x : InfiniteLattice.LatticePoint a => FullSpace.forwardEdge x μ)
      ((forwardEdge_initial_injective μ).injOn)
  have hbwd : ∀ μ : Fin 4, ({x : InfiniteLattice.LatticePoint a |
      c (FullSpace.forwardEdge (x - InfiniteLattice.axisStep a μ) μ) ≠ 0}).Finite := fun μ =>
    hc.preimage (f := fun x : InfiniteLattice.LatticePoint a =>
      FullSpace.forwardEdge (x - InfiniteLattice.axisStep a μ) μ)
      (((forwardEdge_initial_injective μ).comp (sub_left_injective)).injOn)
  refine ((Set.finite_iUnion hfwd).union (Set.finite_iUnion hbwd)).subset fun x hx => ?_
  by_contra hout
  apply hx
  rw [hV.2.2.2.2]
  refine Finset.sum_eq_zero fun μ _ => ?_
  have h1 : c (FullSpace.forwardEdge x μ) = 0 := by
    by_contra h
    exact hout (Or.inl (Set.mem_iUnion.mpr ⟨μ, h⟩))
  have h2 : c (FullSpace.forwardEdge (x - InfiniteLattice.axisStep a μ) μ) = 0 := by
    by_contra h
    exact hout (Or.inr (Set.mem_iUnion.mpr ⟨μ, h⟩))
  rw [h1, h2, sub_zero]
theorem finsum_edgeOperator_mul (hV : FullSpace.VertexAdjointProperties ℝ a)
    (hF : FullSpace.FaceAdjointProperties ℝ a) (θ c c' : FullSpace.PositiveEdge a → ℝ)
    (hc : (Function.support c).Finite) (hc' : (Function.support c').Finite) :
    ∑ᶠ b, edgeOperator θ c b * c' b = edgeQuadForm θ c c' := by
  have h1 := hF.2.2.1 (fun p => Real.cos (FullSpace.faceAngle θ p) *
    FullSpace.edgeDifference c p) c' hc'
  have h2 := hV.2.2.1 c' (FullSpace.vertexAdjoint c) (vertexAdjoint_support_finite hV c hc)
  have hsupp : ∀ F : FullSpace.PositiveEdge a → ℝ, (Function.support fun b => F b * c' b).Finite :=
    fun F => hc'.subset fun b hb h0 => hb (by simp [show c' b = 0 from h0])
  simp only [edgeOperator, add_mul]
  rw [finsum_add_distrib (hsupp _) (hsupp _), h1]
  unfold edgeQuadForm
  congr 1
  rw [finsum_congr (fun x => mul_comm (FullSpace.vertexAdjoint c x) (FullSpace.vertexAdjoint c' x)), h2]
  exact finsum_congr fun b => mul_comm _ _
theorem edgeOperator_add (hV : FullSpace.VertexAdjointProperties ℝ a)
    (hF : FullSpace.FaceAdjointProperties ℝ a) (θ c c' : FullSpace.PositiveEdge a → ℝ) :
    edgeOperator θ (c + c') = edgeOperator θ c + edgeOperator θ c' := by
  have hdiff : FullSpace.edgeDifference (c + c') =
      FullSpace.edgeDifference c + FullSpace.edgeDifference c' := by
    funext p
    simp only [FullSpace.edgeDifference, Pi.add_apply]
    ring
  have hweighted : (fun p => Real.cos (FullSpace.faceAngle θ p) *
        FullSpace.edgeDifference (c + c') p) =
      (fun p => Real.cos (FullSpace.faceAngle θ p) * FullSpace.edgeDifference c p) +
        fun p => Real.cos (FullSpace.faceAngle θ p) * FullSpace.edgeDifference c' p := by
    funext p
    simp only [hdiff, Pi.add_apply]
    ring
  funext b
  simp only [edgeOperator, Pi.add_apply, hweighted, hF.2.2.2.1.map_add, hV.2.2.2.1.map_add,
    FullSpace.vertexDifference]
  ring
open Classical in
def edgeIndicator (b₀ : FullSpace.PositiveEdge a) : FullSpace.PositiveEdge a → ℝ :=
  fun b => if b = b₀ then 1 else 0
theorem edgeIndicator_support_finite (b₀ : FullSpace.PositiveEdge a) :
    (Function.support (edgeIndicator b₀)).Finite :=
  (Set.finite_singleton b₀).subset fun b hb => by
    by_contra hne
    exact hb (if_neg hne)
theorem finsum_mul_edgeIndicator (F : FullSpace.PositiveEdge a → ℝ) (b₀ : FullSpace.PositiveEdge a) :
    ∑ᶠ b, F b * edgeIndicator b₀ b = F b₀ := by
  rw [finsum_eq_single _ b₀ fun b hb => by simp [edgeIndicator, hb]]
  simp [edgeIndicator]
theorem edgeQuadForm_edgeIndicator (hV : FullSpace.VertexAdjointProperties ℝ a)
    (hF : FullSpace.FaceAdjointProperties ℝ a) (θ : FullSpace.PositiveEdge a → ℝ)
    (b b' : FullSpace.PositiveEdge a) :
    edgeQuadForm θ (edgeIndicator b) (edgeIndicator b') = edgeOperator θ (edgeIndicator b) b' := by
  rw [← finsum_edgeOperator_mul hV hF θ _ _ (edgeIndicator_support_finite b)
    (edgeIndicator_support_finite b'), finsum_mul_edgeIndicator]
theorem edgeQuadForm_edgeIndicator_add (hV : FullSpace.VertexAdjointProperties ℝ a)
    (hF : FullSpace.FaceAdjointProperties ℝ a) (θ : FullSpace.PositiveEdge a → ℝ)
    (b b' : FullSpace.PositiveEdge a) :
    edgeQuadForm θ (edgeIndicator b + edgeIndicator b') (edgeIndicator b + edgeIndicator b') =
      edgeOperator θ (edgeIndicator b) b + edgeOperator θ (edgeIndicator b') b +
        (edgeOperator θ (edgeIndicator b) b' + edgeOperator θ (edgeIndicator b') b') := by
  have hfin : (Function.support (edgeIndicator b + edgeIndicator b')).Finite :=
    ((edgeIndicator_support_finite b).union (edgeIndicator_support_finite b')).subset
      (Function.support_add _ _)
  have hsupp : ∀ (F : FullSpace.PositiveEdge a → ℝ) (b₀ : FullSpace.PositiveEdge a),
      (Function.support fun x => F x * edgeIndicator b₀ x).Finite := fun F b₀ =>
    (edgeIndicator_support_finite b₀).subset fun x hx h0 =>
      hx (by simp [show edgeIndicator b₀ x = 0 from h0])
  rw [← finsum_edgeOperator_mul hV hF θ _ _ hfin hfin, edgeOperator_add hV hF]
  simp only [Pi.add_apply, mul_add]
  rw [finsum_add_distrib (hsupp _ _) (hsupp _ _), finsum_mul_edgeIndicator, finsum_mul_edgeIndicator]
end EdgeOperator
section PositiveEdgeForms
variable {L : ℕ}
theorem meshAt_zero_pos (L : ℕ) : 0 < meshAt L 0 0 := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.meshAt_zero_pos <;> assumption
theorem axisStep_injective {a : ℝ} (ha : 0 < a) {μ ν : Fin 4}
    (h : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ν) : μ = ν := by apply _root_.YangMills.Construction.CutoffLinks.LinksAndTheirVariables.axisStep_injective <;> assumption
theorem formOfPositiveValues_apply_pos (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (b : PeriodicOperators.PosEdge L 0 0) : formOfPositiveValues g b.1 = g b := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.formOfPositiveValues_apply <;> assumption
theorem fieldStar_formOfPositiveValues (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (hg : ∀ b, ComplexMatrix2.adjointMatrix (g b) = g b) :
    fieldStar (formOfPositiveValues g) = formOfPositiveValues g := by apply _root_.YangMills.Construction.Tower.AbelianOperatorsLocalSelfAdjointProof.fieldStar_formOfPositiveValues <;> assumption
theorem restrict_formOfPositiveValues (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2) :
    FullSpace.restrictToPositiveEdges (formOfPositiveValues g) = g :=
  funext (formOfPositiveValues_apply_pos g)
theorem formOfPositiveValues_mem_l2Forms (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (hg : IsL2Traceless g) :
    formOfPositiveValues g ∈ FullSpace.l2Forms (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.AbelianOperatorBounds.formOfPositiveValues_mem_l2Forms <;> assumption
theorem formOfPositiveValues_mem_edgeFormSpace (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (hg : IsL2Traceless g) (hsa : ∀ b, ComplexMatrix2.adjointMatrix (g b) = g b) :
    formOfPositiveValues g ∈ FullSpace.edgeFormSpace (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.AbelianOperatorBounds.formOfPositiveValues_mem_edgeFormSpace <;> assumption
theorem formOfPositiveValues_hasFiniteEdgeSupport
    (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (hs : (Function.support g).Finite) :
    FullSpace.HasFiniteEdgeSupport (formOfPositiveValues g) := by apply _root_.YangMills.Construction.Tower.AbelianOperatorBounds.formOfPositiveValues_hasFiniteEdgeSupport <;> assumption
theorem hermitianInner_eq_traceFinsumPairing {σ : Type} (f g : σ → ComplexMatrix2)
    (hf : ∀ s, ComplexMatrix2.adjointMatrix (f s) = f s) (hs : (Function.support f).Finite) :
    hermitianInner f g = traceFinsumPairing f g := by apply _root_.YangMills.Construction.Tower.AbelianOperatorBounds.hermitianInner_eq_traceFinsumPairing <;> assumption
end PositiveEdgeForms
section NeutralQuadratic
open AbelianFieldFacts
variable {L : ℕ} {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
theorem adjointMatrix_smul_pauliZ (c : ℝ) :
    ComplexMatrix2.adjointMatrix ((c : ℂ) • ComplexMatrix2.pauliFamily 2) =
      (c : ℂ) • ComplexMatrix2.pauliFamily 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ComplexMatrix2.adjointMatrix, ComplexMatrix2.pauliFamily, OneLoop.pauliZ]
theorem halfTrace_smul_pauliZ_mul_pauliZ (c : ℝ) :
    ComplexMatrix2.halfTrace (((c : ℂ) • ComplexMatrix2.pauliFamily 2) * ComplexMatrix2.pauliFamily 2) = c := by
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, ComplexMatrix2.pauliFamily, OneLoop.pauliZ,
    Matrix.trace_fin_two]
  ring
theorem halfTrace_smul_pauliZ_mul_lowering (c : ℝ) :
    ComplexMatrix2.halfTrace (((c : ℂ) • ComplexMatrix2.pauliFamily 2) * loweringPauli) = 0 := by
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, ComplexMatrix2.pauliFamily, OneLoop.pauliX,
    OneLoop.pauliY, OneLoop.pauliZ, loweringPauli, Matrix.trace_fin_two]
theorem faceNumbers_zero {a : ℝ} (φ : FullSpace.PositiveEdge a → ℝ)
    (p : InfiniteLattice.ElementaryPlaquette a) (i : Fin 4) : FullSpace.faceNumbers φ 0 p i = 0 := by
  fin_cases i <;> simp [FullSpace.faceNumbers, FullSpace.chargedShift, FullSpace.edgeComponent]
theorem re_inner_massiveOp (hquad : HessianQuadraticForm θ)
    (hops : AbelianOperators θ)
    (hco : CoordsIsometry (PeriodicOperators.PosEdge L 0 0))
    (v : L2Field (PeriodicOperators.PosEdge L 0 0))
    (c : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (hc : (Function.support c).Finite)
    (hv : ∀ b, ofCoords v b = (c b : ℂ) • ComplexMatrix2.pauliFamily 2) :
    (inner ℂ v (AbelianFieldDensity.massiveOp θ v) : ℂ).re = edgeQuadForm θ c c := by
  classical
  have hcv := hco.2.2.1 v
  have hsa : ∀ b, ComplexMatrix2.adjointMatrix (ofCoords v b) = ofCoords v b := fun b => by
    rw [hv, adjointMatrix_smul_pauliZ]
  have hgs : (Function.support (ofCoords
      (v : Fin 3 × PeriodicOperators.PosEdge L 0 0 → ℂ))).Finite :=
    hc.subset fun b hb h0 => hb (by rw [hv, show c b = 0 from h0]; simp)
  set g := ofCoords (v : Fin 3 × PeriodicOperators.PosEdge L 0 0 → ℂ) with hgdef
  set B := formOfPositiveValues g with hBdef
  have hBf : B ∈ FullSpace.edgeFormSpace (meshAt L 0 0) :=
    formOfPositiveValues_mem_edgeFormSpace g hcv.1 hsa
  have hBs : FullSpace.HasFiniteEdgeSupport B := formOfPositiveValues_hasFiniteEdgeSupport g hgs
  obtain ⟨h0, -, -, hpair⟩ := hquad B hBf hBs
  have hinner : (inner ℂ v (AbelianFieldDensity.massiveOp θ v) : ℂ) =
      FullSpace.finiteEdgePairing B (FullSpace.abelianMassiveHessian θ B) := by
    rw [← hco.2.2.2.2.2 v (AbelianFieldDensity.massiveOp θ v), hops.hessian_apply v,
      hermitianInner_eq_traceFinsumPairing _ _ hsa hgs]
    simp only [FullSpace.finiteEdgePairing, hBdef, restrict_formOfPositiveValues]
    rfl
  have hval : ∀ b : FullSpace.PositiveEdge (meshAt L 0 0),
      B b.1 = (c b : ℂ) • ComplexMatrix2.pauliFamily 2 :=
    fun b => by rw [hBdef, formOfPositiveValues_apply_pos]; exact hv b
  have hdiag : FullSpace.diagonalComponent B = c := by
    funext b
    simp only [FullSpace.diagonalComponent, hval, halfTrace_smul_pauliZ_mul_pauliZ, Complex.ofReal_re]
  have hoff : FullSpace.offDiagonalComponent B = 0 := by
    funext b
    simp only [FullSpace.offDiagonalComponent, hval, halfTrace_smul_pauliZ_mul_lowering, mul_zero,
      Pi.zero_apply]
  have hscalar : ∀ μ : Fin 4,
      toScalarL2 (FullSpace.edgeComponent (FullSpace.offDiagonalComponent B) μ) = 0 := by
    intro μ
    refine lp.ext (funext fun x => ?_)
    ext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [h0 μ x, hoff]
    simp [FullSpace.edgeComponent]
  have hface : ∀ p, _root_.YangMills.Construction.Tower.AbelianFieldFacts.faceTerm θ B p = Real.cos (FullSpace.faceAngle θ p) *
      FullSpace.edgeDifference c p * FullSpace.edgeDifference c p := by
    intro p
    simp only [_root_.YangMills.Construction.Tower.AbelianFieldFacts.faceTerm, hdiag, hoff, faceNumbers_zero]
    simp
    ring
  have hvert : ∀ x, _root_.YangMills.Construction.Tower.AbelianFieldFacts.vertexTerm θ B x = FullSpace.vertexAdjoint c x * FullSpace.vertexAdjoint c x := by
    intro x
    simp only [_root_.YangMills.Construction.Tower.AbelianFieldFacts.vertexTerm, hdiag, hscalar, covShiftAdjSubOne]
    simp
    ring
  rw [hinner, hpair, Complex.ofReal_re, edgeQuadForm]
  simp only [hface, hvert]
end NeutralQuadratic
section IntegerPoints
variable {L : ℕ}
theorem exists_latticePoint_eq (x : FullSpace.Vertex L 0 0) : ∃ k, latticePoint L k = x := by
  obtain ⟨y, n, hn⟩ := x
  refine ⟨n, Subtype.ext (funext fun μ => ?_)⟩
  simp [latticePoint, castVec, hn, meshAt]
theorem latticePoint_add_axisStep (k : Fin 4 → ℤ) (μ : Fin 4) :
    latticePoint L k + InfiniteLattice.axisStep (meshAt L 0 0) μ =
      latticePoint L (k + basisVec μ) := by
  refine Subtype.ext (funext fun ν => ?_)
  rw [AddSubgroup.coe_add, Pi.add_apply]
  by_cases h : ν = μ
  · subst h
    simp [latticePoint, castVec, InfiniteLattice.axisStep, basisVec, meshAt]
  · simp [latticePoint, castVec, InfiniteLattice.axisStep, basisVec, meshAt,
      Pi.single_eq_of_ne h]
theorem latticePoint_sub_axisStep (k : Fin 4 → ℤ) (μ : Fin 4) :
    latticePoint L k - InfiniteLattice.axisStep (meshAt L 0 0) μ =
      latticePoint L (k + -basisVec μ) := by
  refine Subtype.ext (funext fun ν => ?_)
  rw [AddSubgroup.coe_sub, Pi.sub_apply]
  by_cases h : ν = μ
  · subst h
    simp [latticePoint, castVec, InfiniteLattice.axisStep, basisVec, meshAt, sub_eq_add_neg]
  · simp [latticePoint, castVec, InfiniteLattice.axisStep, basisVec, meshAt,
      Pi.single_eq_of_ne h]
theorem sum_subtype_gt_eq_ite (F : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ ν : {ν : Fin 4 // μ < ν}, F ν.1 = ∑ ν, if μ < ν then F ν else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) F).symm
theorem sum_subtype_lt_eq_ite (F : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ ν : {ν : Fin 4 // ν < μ}, F ν.1 = ∑ ν, if ν < μ then F ν else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) F).symm
theorem edgeOperator_forwardEdge (hV : FullSpace.VertexAdjointProperties ℝ (meshAt L 0 0))
    (hF : FullSpace.FaceAdjointProperties ℝ (meshAt L 0 0)) (f : ℝ)
    (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (hθ : ∀ p : FullSpace.Face L 0 0,
      FullSpace.faceAngle θ p = if p.lowAxis = 0 ∧ p.highAxis = 1 then f else 0)
    (c : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ) (k : Fin 4 → ℤ) (μ : Fin 4) :
    ((edgeOperator θ c (FullSpace.forwardEdge (latticePoint L k) μ) : ℝ) : ℂ) =
      neutralStencil (Real.cos f : ℂ)
        (fun m j => ((c (FullSpace.forwardEdge (latticePoint L m) j) : ℝ) : ℂ)) k μ := by
  set G : FullSpace.Vertex L 0 0 → Fin 4 → Fin 4 → ℝ := fun x ν ν' =>
    (if ν = 0 ∧ ν' = 1 then Real.cos f else 1) *
      (c (FullSpace.forwardEdge x ν) +
        c (FullSpace.forwardEdge (x + InfiniteLattice.axisStep (meshAt L 0 0) ν) ν') -
        c (FullSpace.forwardEdge (x + InfiniteLattice.axisStep (meshAt L 0 0) ν') ν) -
        c (FullSpace.forwardEdge x ν')) with hG
  have hweighted : ∀ (x : FullSpace.Vertex L 0 0) (ν ν' : Fin 4) (h : ν < ν'),
      Real.cos (FullSpace.faceAngle θ ⟨x, ν, ν', h⟩) *
        FullSpace.edgeDifference c ⟨x, ν, ν', h⟩ = G x ν ν' := by
    intro x ν ν' h
    rw [hθ]
    simp only [hG, FullSpace.edgeDifference]
    split_ifs <;> simp
  have hop : edgeOperator θ c (FullSpace.forwardEdge (latticePoint L k) μ) =
      (∑ ν, if μ < ν then G (latticePoint L k) μ ν -
          G (latticePoint L k - InfiniteLattice.axisStep (meshAt L 0 0) ν) μ ν else 0) -
      (∑ ν, if ν < μ then G (latticePoint L k) ν μ -
          G (latticePoint L k - InfiniteLattice.axisStep (meshAt L 0 0) ν) ν μ else 0) +
      (FullSpace.vertexAdjoint c (latticePoint L k + InfiniteLattice.axisStep (meshAt L 0 0) μ) -
        FullSpace.vertexAdjoint c (latticePoint L k)) := by
    rw [edgeOperator, hF.2.2.2.2]
    simp only [hweighted]
    rw [sum_subtype_gt_eq_ite (fun ν => G (latticePoint L k) μ ν -
        G (latticePoint L k - InfiniteLattice.axisStep (meshAt L 0 0) ν) μ ν) μ,
      sum_subtype_lt_eq_ite (fun ν => G (latticePoint L k) ν μ -
        G (latticePoint L k - InfiniteLattice.axisStep (meshAt L 0 0) ν) ν μ) μ]
    rfl
  rw [hop]
  simp only [hV.2.2.2.2]
  fin_cases μ <;>
  simp [hG, neutralStencil, Fin.sum_univ_four, Fin.sum_univ_three, faceRowCoeff, faceRowShift,
    latticePoint_add_axisStep, latticePoint_sub_axisStep] <;>
  abel_nf <;>
  ring_nf
end IntegerPoints
section NeutralEntries
open AbelianFieldFacts
variable {L : ℕ} {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
open Classical in
def edgeUnit (x : FullSpace.Vertex L 0 0) (μ : Fin 4) : VectorL2 L 4 :=
  lp.single 2 x (EuclideanSpace.single μ (1 : ℂ))
theorem forwardEdge_inj {x y : FullSpace.Vertex L 0 0} {μ ν : Fin 4}
    (h : FullSpace.forwardEdge x μ = FullSpace.forwardEdge y ν) : x = y ∧ μ = ν := by
  have hval := congrArg Subtype.val h
  have hxy : x = y := congrArg InfiniteLattice.Link.initial hval
  have hterm : x + InfiniteLattice.axisStep (meshAt L 0 0) μ =
      y + InfiniteLattice.axisStep (meshAt L 0 0) ν := congrArg InfiniteLattice.Link.terminal hval
  subst hxy
  exact ⟨rfl, axisStep_injective (meshAt_zero_pos L) (add_left_cancel hterm)⟩
theorem edgeUnit_apply (x y : FullSpace.Vertex L 0 0) (μ ν : Fin 4) :
    edgeUnit x μ y ν =
      ((edgeIndicator (FullSpace.forwardEdge x μ) (FullSpace.forwardEdge y ν) : ℝ) : ℂ) := by
  classical
  by_cases hy : y = x
  · subst hy
    by_cases hν : ν = μ
    · subst hν
      simp [edgeUnit, edgeIndicator, lp.single_apply]
    · have hne : FullSpace.forwardEdge y ν ≠ FullSpace.forwardEdge y μ := fun h =>
        hν (forwardEdge_inj h).2
      simp [edgeUnit, edgeIndicator, lp.single_apply, hne, hν]
  · have hne : FullSpace.forwardEdge y ν ≠ FullSpace.forwardEdge x μ := fun h =>
      hy (forwardEdge_inj h).1
    simp [edgeUnit, edgeIndicator, lp.single_apply, hne, hy]
theorem massiveOp_edgeUnit (hops : AbelianOperators θ) (hsym : ChargeSymmetries θ)
    (hquad : HessianQuadraticForm θ)
    (hco : CoordsIsometry (PeriodicOperators.PosEdge L 0 0))
    (hV : FullSpace.VertexAdjointProperties ℝ (meshAt L 0 0))
    (hF : FullSpace.FaceAdjointProperties ℝ (meshAt L 0 0))
    (hfac : WeightMultipleFacts (edgeTensor (L := L)))
    (hval : ∀ (v : VectorL2 L 4) (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
      ofCoords (edgeTensor v (ComplexMatrix2.pauliFamily 2)) (FullSpace.forwardEdge x μ) =
        v x μ • ComplexMatrix2.pauliFamily 2)
    (hedge : ∀ b : PeriodicOperators.PosEdge L 0 0,
      ∃ p : FullSpace.Vertex L 0 0 × Fin 4, FullSpace.forwardEdge p.1 p.2 = b)
    (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    ∃ w : VectorL2 L 4,
      AbelianFieldDensity.massiveOp θ (edgeTensor (edgeUnit x μ) (ComplexMatrix2.pauliFamily 2)) =
        edgeTensor w (ComplexMatrix2.pauliFamily 2) ∧
      ∀ y ν, w y ν =
        ((edgeOperator θ (edgeIndicator (FullSpace.forwardEdge x μ)) (FullSpace.forwardEdge y ν) : ℝ) : ℂ) := by
  classical
  have hunitc : ∀ (x : FullSpace.Vertex L 0 0) (μ : Fin 4) (b : PeriodicOperators.PosEdge L 0 0),
      ofCoords (edgeTensor (edgeUnit x μ) (ComplexMatrix2.pauliFamily 2)) b =
        ((edgeIndicator (FullSpace.forwardEdge x μ) b : ℝ) : ℂ) • ComplexMatrix2.pauliFamily 2 := by
    intro x μ b
    obtain ⟨⟨y, ν⟩, rfl⟩ := hedge b
    rw [hval, edgeUnit_apply]
  have hneu : ∀ (g : L2Field (PeriodicOperators.PosEdge L 0 0))
      (c : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ),
      (∀ b, ofCoords g b = (c b : ℂ) • ComplexMatrix2.pauliFamily 2) →
      ∃ w, AbelianFieldDensity.massiveOp θ g = edgeTensor w (ComplexMatrix2.pauliFamily 2) := by
    intro g c hg
    have hmem := formOfPositiveValues_mem_l2Forms _ (hco.2.2.1 g).1
    have h1 := hsym.hessian_neutral _ hmem (by
      rw [restrict_formOfPositiveValues]
      exact ⟨fun b => (c b : ℂ), hg⟩)
    have h2 : IsNeutral (ofCoords (AbelianFieldDensity.massiveOp θ g)) := by
      rw [hops.hessian_apply g]
      exact h1
    exact (hfac.neutral_iff _).1 h2
  choose w hw using fun (x : FullSpace.Vertex L 0 0) (μ : Fin 4) => hneu _ _ (hunitc x μ)
  have hentry : ∀ (x y : FullSpace.Vertex L 0 0) (μ ν : Fin 4),
      (inner ℂ (edgeTensor (edgeUnit y ν) (ComplexMatrix2.pauliFamily 2))
        (AbelianFieldDensity.massiveOp θ (edgeTensor (edgeUnit x μ) (ComplexMatrix2.pauliFamily 2))) : ℂ) =
        w x μ y ν := by
    intro x y μ ν
    rw [hw, hfac.inner_third, edgeUnit, lp.inner_single_left, EuclideanSpace.inner_single_left]
    simp
  have hreal : ∀ (x y : FullSpace.Vertex L 0 0) (μ ν : Fin 4), (w x μ y ν).im = 0 := by
    intro x y μ ν
    have hsa : ∀ b, ComplexMatrix2.adjointMatrix
        (ofCoords (edgeTensor (edgeUnit x μ) (ComplexMatrix2.pauliFamily 2)) b) =
        ofCoords (edgeTensor (edgeUnit x μ) (ComplexMatrix2.pauliFamily 2)) b := fun b => by
      rw [hunitc, adjointMatrix_smul_pauliZ]
    have hmem := formOfPositiveValues_mem_l2Forms _
      (hco.2.2.1 (edgeTensor (edgeUnit x μ) (ComplexMatrix2.pauliFamily 2))).1
    have h1 := hsym.hessian_star _ hmem
    rw [fieldStar_formOfPositiveValues _ hsa] at h1
    have h2 := congrFun h1 (FullSpace.forwardEdge y ν).1
    have h3 := congrFun (hops.hessian_apply (edgeTensor (edgeUnit x μ) (ComplexMatrix2.pauliFamily 2)))
      (FullSpace.forwardEdge y ν)
    simp only [fieldStar] at h2
    rw [← h3, hw, hval] at h2
    have h4 := congrFun (congrFun h2 0) 0
    simp [ComplexMatrix2.adjointMatrix, ComplexMatrix2.pauliFamily, OneLoop.pauliZ] at h4
    exact Complex.conj_eq_iff_im.mp h4.symm
  have hsymm : ∀ u u' : L2Field (PeriodicOperators.PosEdge L 0 0),
      (inner ℂ u (AbelianFieldDensity.massiveOp θ u') : ℂ).re =
        (inner ℂ u' (AbelianFieldDensity.massiveOp θ u) : ℂ).re := by
    intro u u'
    have h1 : (inner ℂ u (AbelianFieldDensity.massiveOp θ u') : ℂ) =
        inner ℂ (opAdjoint (AbelianFieldDensity.massiveOp θ) u) u' :=
      (ContinuousLinearMap.adjoint_inner_left (AbelianFieldDensity.massiveOp θ) u' u).symm
    rw [h1, hops.hessian_isSelfAdjoint, ← inner_conj_symm, Complex.conj_re]
  have hdiag : ∀ (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
      (inner ℂ (edgeTensor (edgeUnit x μ) (ComplexMatrix2.pauliFamily 2))
        (AbelianFieldDensity.massiveOp θ (edgeTensor (edgeUnit x μ) (ComplexMatrix2.pauliFamily 2))) : ℂ).re =
        edgeOperator θ (edgeIndicator (FullSpace.forwardEdge x μ)) (FullSpace.forwardEdge x μ) := by
    intro x μ
    rw [re_inner_massiveOp hquad hops hco _ _ (edgeIndicator_support_finite _) (hunitc x μ),
      edgeQuadForm_edgeIndicator hV hF]
  refine ⟨w x μ, hw x μ, fun y ν => ?_⟩
  have hfin : (Function.support (edgeIndicator (FullSpace.forwardEdge x μ) +
      edgeIndicator (FullSpace.forwardEdge y ν))).Finite :=
    ((edgeIndicator_support_finite _).union (edgeIndicator_support_finite _)).subset
      (Function.support_add _ _)
  have hpol := re_inner_massiveOp hquad hops hco
    (edgeTensor (edgeUnit x μ) (ComplexMatrix2.pauliFamily 2) +
      edgeTensor (edgeUnit y ν) (ComplexMatrix2.pauliFamily 2))
    (edgeIndicator (FullSpace.forwardEdge x μ) + edgeIndicator (FullSpace.forwardEdge y ν)) hfin
    (fun b => by
      rw [(hco.2.2.2.2.1 1 _ _).1, Pi.add_apply, hunitc, hunitc, Pi.add_apply, Complex.ofReal_add,
        add_smul])
  rw [edgeQuadForm_edgeIndicator_add hV hF] at hpol
  simp only [map_add, inner_add_left, inner_add_right, Complex.add_re] at hpol
  have hs := hsymm (edgeTensor (edgeUnit x μ) (ComplexMatrix2.pauliFamily 2))
    (edgeTensor (edgeUnit y ν) (ComplexMatrix2.pauliFamily 2))
  have hswap : edgeOperator θ (edgeIndicator (FullSpace.forwardEdge y ν)) (FullSpace.forwardEdge x μ) =
      edgeOperator θ (edgeIndicator (FullSpace.forwardEdge x μ)) (FullSpace.forwardEdge y ν) := by
    rw [← edgeQuadForm_edgeIndicator hV hF, ← edgeQuadForm_edgeIndicator hV hF, edgeQuadForm_comm]
  have h1 := hdiag x μ
  have h2 := hdiag y ν
  have h3 := hentry x y μ ν
  refine Complex.ext ?_ (by simpa using hreal x y μ ν)
  rw [Complex.ofReal_re, ← h3]
  linarith
end NeutralEntries
theorem neutralSectorOperator_holds (hFacts : AbelianFieldFacts.AllFacts)
    (hAdj : ScalarDifferenceAdjoints)
    (hCalc : MagneticWeyl.FluxZeroCalculus.Claim)
    (hWeights : AbelianFieldDensity.WeightMultiplesAndStar)
    (hSum : WeylQuantHasSum)
    (hCoeff : FourierCoeffsOfSymbol)
    (hUnit : UnitaryOperatorSeriesClaim)
    (hL2 : UnitLatticeL2Statement) :
    NeutralSectorOperator := by
  classical
  intro L hL f _ v
  obtain ⟨-, -, -, -, hAngles, hField⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ := by
    obtain ⟨h1, h2, h3⟩ := hFacts
    obtain ⟨h4, h5, h6, h7⟩ := h3 L hL 1 one_pos
    exact ⟨h1, h2, h4, h5, h6, h7⟩
  obtain ⟨hops, hsym, -, -, hquad, -, -⟩ := hField (scaledLinearAngle L f)
  have hco := ((hL2.2 L).2.2).1
  obtain ⟨-, -, -, -, hRealV, hRealF⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ := by
    obtain ⟨-, -, h1, h2, h3, h4, h5, h6⟩ := hAdj L hL
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨hedge, hsl, -, hval, -, -, -, hfac⟩ := hWeights L hL
  have hz : IsWeightMatrix (ComplexMatrix2.pauliFamily 2) := Or.inl rfl
  have hval' := hval (ComplexMatrix2.pauliFamily 2) (hsl _ hz)
  have hTrans := (hCalc L 4 4 4).2.1
  have hθ : ∀ p : FullSpace.Face L 0 0,
      FullSpace.faceAngle (scaledLinearAngle L f) p =
        if p.lowAxis = 0 ∧ p.highAxis = 1 then f else 0 := hAngles f
  have hedge' : ∀ b : PeriodicOperators.PosEdge L 0 0,
      ∃ p : FullSpace.Vertex L 0 0 × Fin 4, FullSpace.forwardEdge p.1 p.2 = b := fun b =>
    (hedge b).exists
  have hunit : ∀ (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
      AbelianFieldDensity.massiveOp (scaledLinearAngle L f)
          (edgeTensor (edgeUnit x μ) (ComplexMatrix2.pauliFamily 2)) =
        edgeTensor (weylQuant L 0 (neutralSectorSymbol f) (edgeUnit x μ)) (ComplexMatrix2.pauliFamily 2) := by
    intro x μ
    obtain ⟨w, hw, hwv⟩ :=
      massiveOp_edgeUnit hops hsym hquad hco hRealV hRealF hfac hval' hedge' x μ
    rw [hw]
    congr 1
    refine lp.ext (funext fun y => ?_)
    ext ν
    obtain ⟨k, rfl⟩ := exists_latticePoint_eq y
    rw [hwv, edgeOperator_forwardEdge hRealV hRealF f _ hθ,
      weylQuant_neutralSectorSymbol_apply hSum hCoeff hUnit hTrans]
    simp only [edgeUnit_apply]
  have hnorm : ∀ u : VectorL2 L 4, ‖edgeTensor u (ComplexMatrix2.pauliFamily 2)‖ = ‖u‖ := by
    intro u
    have h := hfac.inner_third u u
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖edgeTensor u (ComplexMatrix2.pauliFamily 2)‖ ^ 2 = ‖u‖ ^ 2 := by exact_mod_cast h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h'
  let Φ : VectorL2 L 4 →L[ℂ]
      L2Field (PeriodicOperators.PosEdge L 0 0) :=
    LinearMap.mkContinuous
      { toFun := fun u => edgeTensor u (ComplexMatrix2.pauliFamily 2)
        map_add' := hfac.map_add _ hz
        map_smul' := hfac.map_smul _ hz } 1 (fun u => by
          simp [hnorm])
  let D : VectorL2 L 4 →L[ℂ]
      L2Field (PeriodicOperators.PosEdge L 0 0) :=
    (AbelianFieldDensity.massiveOp (scaledLinearAngle L f)).comp Φ -
      Φ.comp (weylQuant L 0 (neutralSectorSymbol f))
  have hDunit : ∀ (x : FullSpace.Vertex L 0 0) (μ : Fin 4), D (edgeUnit x μ) = 0 := by
    intro x μ
    exact sub_eq_zero.mpr (hunit x μ)
  have hsingle : ∀ (x : FullSpace.Vertex L 0 0) (u : EuclideanSpace ℂ (Fin 4)),
      D (lp.single 2 x u) = 0 := by
    intro x u
    have hu : (lp.single 2 x u : VectorL2 L 4) = ∑ μ, u μ • edgeUnit x μ := by
      have h1 : u = ∑ μ, u μ • EuclideanSpace.single μ (1 : ℂ) := by
        ext i
        simp [Finset.sum_apply, Pi.single_apply]
      refine lp.ext (funext fun y => ?_)
      rw [lp.coeFn_sum, Finset.sum_apply]
      simp only [lp.coeFn_smul, Pi.smul_apply, edgeUnit]
      by_cases hy : y = x
      · subst hy
        simp only [lp.single_apply, Pi.single_eq_same]
        exact h1
      · simp [lp.single_apply, hy]
    rw [hu, map_sum]
    exact Finset.sum_eq_zero fun μ _ => by rw [map_smul, hDunit, smul_zero]
  have hD : D v = 0 := by
    have h := (lp.hasSum_single (p := 2) (by norm_num) v).mapL D
    simp only [hsingle] at h
    exact h.unique hasSum_zero
  exact sub_eq_zero.mp hD
end NeutralSectorProof
end Tower.ConstantFieldSymbols
end
end YangMills.Construction
