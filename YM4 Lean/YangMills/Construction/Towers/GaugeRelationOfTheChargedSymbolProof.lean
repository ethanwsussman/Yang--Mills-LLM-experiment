import YangMills.Construction.Towers.ChargedFormInComponentsProof
import YangMills.Construction.Towers.FirstCoefficientOnTheGaugeColumnProof
import YangMills.Construction.Towers.ChargedSymbolAtFluxZeroProof
import YangMills.Construction.Towers.CoefficientsOfASymbol
import YangMills.Construction.Towers.CoefficientsReadOffAQuantization
import YangMills.Construction.Towers.FactsOfAbelianFields
import YangMills.Construction.Towers.GaugeCovarianceOfTheCovariantAveragesAtTheSideInfinityProof
import YangMills.Construction.Towers.GaugeRelationOfTheChargedSymbol
import YangMills.Construction.Towers.MassiveOperatorOnGaugeDirectionsOfTheConstantField
import YangMills.Construction.Towers.MultiplesOfTheSectorMatricesAndTheConjugation
import YangMills.Construction.Towers.QuantizationIsTheSumOfItsSeries
import YangMills.Construction.Towers.QuantizationOfAStarProduct
import YangMills.Construction.Towers.RelationsOfTheWeylOperators
import YangMills.Construction.Towers.StarProductOfTwoSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (toComplexVec castVec bilinDot)
open YangMills.Construction.Tower.MagneticWeyl YangMills.Construction.Tower.AbelianFieldDensity YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition YangMills.Construction.Tower.Massive
open YangMills.Construction.Tower.AbelianFieldFacts (CovariantShifts covShift covShiftSubOne
  covShiftAdjSubOne raisingVertexFn IsRaisingFormOf)
namespace GaugeRelation
section CharacterSums
variable {N' N'' : ℕ} [NeZero N'] [NeZero N''] {ι : Type} [Fintype ι]
def charSum (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin N') (Fin N'') ℂ) (q : AmbientSpace) :
    Matrix (Fin N') (Fin N'') ℂ :=
  ∑ i, MagneticWeyl.fourierChar (n i) q • c i
def charSumCoeff (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin N') (Fin N'') ℂ) (m : Fin 4 → ℤ) :
    Matrix (Fin N') (Fin N'') ℂ :=
  ∑ i, if m = n i then c i else 0
omit [NeZero N'] [NeZero N''] in
theorem hasFourierExpansion_charSumCoeff (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin N') (Fin N'') ℂ) :
    HasFourierExpansion (charSumCoeff n c) (charSum n c) := by
  intro q
  have h : ∀ i ∈ (Finset.univ : Finset ι),
      HasSum (fun m => if m = n i then MagneticWeyl.fourierChar (n i) q • c i else 0)
        (MagneticWeyl.fourierChar (n i) q • c i) := fun i _ => hasSum_ite_eq _ _
  have h3 : HasSum (fun m => ∑ i, if m = n i then MagneticWeyl.fourierChar (n i) q • c i else 0)
      (charSum n c q) := hasSum_sum h
  convert h3 using 2 with m
  rw [charSumCoeff, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with e
  · rw [e]
  · simp
theorem opNormValue_zero : Matrices.RectangularMatrix.opNormValue (0 : Matrix (Fin N') (Fin N'') ℂ) = 0 := by
  simp [Matrices.RectangularMatrix.opNormValue, OneLoopNotation.opNormOf]
theorem summable_opNormValue_charSumCoeff_mul (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin N') (Fin N'') ℂ)
    (f : (Fin 4 → ℤ) → ℝ) :
    Summable fun m => Matrices.RectangularMatrix.opNormValue (charSumCoeff n c m) * f m := by
  refine summable_of_hasFiniteSupport ((Set.finite_range n).subset fun m hm => ?_)
  by_contra hr
  apply hm
  have : charSumCoeff n c m = 0 := by
    refine Finset.sum_eq_zero fun i _ => if_neg fun e => hr ⟨i, e.symm⟩
  simp [this, opNormValue_zero]
theorem isWeylSymbol_charSum (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin N') (Fin N'') ℂ) :
    IsWeylSymbol (charSum n c) :=
  ⟨charSumCoeff n c, hasFourierExpansion_charSumCoeff n c,
    fun _ _ => summable_opNormValue_charSumCoeff_mul n c _⟩
theorem summable_opNormValue_charSumCoeff (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin N') (Fin N'') ℂ) :
    Summable fun m => Matrices.RectangularMatrix.opNormValue (charSumCoeff n c m) := by
  simpa using summable_opNormValue_charSumCoeff_mul n c fun _ => 1
theorem hasAbsSummableFourier_charSum (n : ι → Fin 4 → ℤ)
    (c : ι → Matrix (Fin N') (Fin N'') ℂ) : HasAbsSummableFourier (charSum n c) :=
  ⟨charSumCoeff n c, hasFourierExpansion_charSumCoeff n c, summable_opNormValue_charSumCoeff n c⟩
theorem fourierCoeff_charSum (hC : FourierCoeffsOfSymbol) (n : ι → Fin 4 → ℤ)
    (c : ι → Matrix (Fin N') (Fin N'') ℂ) : MagneticWeyl.fourierCoeff (charSum n c) = charSumCoeff n c :=
  (((hC N' N'' (charSum n c)).1 (hasAbsSummableFourier_charSum n c)).2.2 _
    (hasFourierExpansion_charSumCoeff n c) (summable_opNormValue_charSumCoeff n c)).symm
variable {L : ℕ}
theorem matMulUnitaryOp_apply (hU : UnitaryOperatorSeriesClaim)
    {V : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hV : IsUnitaryOp V)
    (X : Matrix (Fin N') (Fin N'') ℂ) (w : VectorL2 L N'') (x : FullSpace.Vertex L 0 0) :
    matMulUnitaryOp X V w x = matMulUnitary X V w x :=
  ((hU L N' N'').1 X V hV).1 w x
theorem matMulUnitaryOp_sum (hU : UnitaryOperatorSeriesClaim)
    {V : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hV : IsUnitaryOp V)
    (X : ι → Matrix (Fin N') (Fin N'') ℂ) :
    matMulUnitaryOp (∑ i, X i) V = ∑ i, matMulUnitaryOp (X i) V := by
  refine ContinuousLinearMap.ext fun w => lp.ext (funext fun x => ?_)
  rw [_root_.sum_apply, lp.coeFn_sum, Finset.sum_apply, matMulUnitaryOp_apply hU hV]
  simp only [matMulUnitaryOp_apply hU hV, matMulUnitary, map_sum, LinearMap.sum_apply]
theorem matMulUnitaryOp_zero (hU : UnitaryOperatorSeriesClaim)
    {V : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hV : IsUnitaryOp V) :
    matMulUnitaryOp (0 : Matrix (Fin N') (Fin N'') ℂ) V = 0 := by
  refine ContinuousLinearMap.ext fun w => lp.ext (funext fun x => ?_)
  rw [matMulUnitaryOp_apply hU hV]
  simp [matMulUnitary]
theorem weylQuant_charSum (hS : WeylQuantHasSum)
    (hC : FourierCoeffsOfSymbol)
    (hU : UnitaryOperatorSeriesClaim)
    (φ : ℝ) (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin N') (Fin N'') ℂ) :
    weylQuant L φ (charSum n c) =
      ∑ i, matMulUnitaryOp (c i) (magneticWeyl L φ (n i)) := by
  have h := (hS L φ N' N'' (charSum n c) (hasAbsSummableFourier_charSum n c)).1
  rw [fourierCoeff_charSum hC] at h
  refine h.unique ?_
  have h2 : ∀ i ∈ (Finset.univ : Finset ι),
      HasSum (fun m => if m = n i then matMulUnitaryOp (c i) (magneticWeyl L φ (n i))
          else 0)
        (matMulUnitaryOp (c i) (magneticWeyl L φ (n i))) :=
    fun i _ => hasSum_ite_eq _ _
  convert hasSum_sum h2 using 2 with m
  have hV : IsUnitaryOp (magneticWeyl L φ m) := magneticWeyl_isUnitary φ m
  rw [charSumCoeff, matMulUnitaryOp_sum hU hV]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with e
  · rw [e]
  · exact matMulUnitaryOp_zero hU hV
end CharacterSums
section TwoSymbols
def basisVec (μ : Fin 4) : Fin 4 → ℤ := Pi.single μ 1
theorem fourierChar_basisVec (μ : Fin 4) (q : AmbientSpace) :
    MagneticWeyl.fourierChar (basisVec μ) q = Complex.exp (Complex.I * (q μ : ℂ)) := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.GaugeColumnFirstCoeff.fourierChar_basisIndex <;> assumption
theorem fourierChar_neg_basisVec (μ : Fin 4) (q : AmbientSpace) :
    MagneticWeyl.fourierChar (-basisVec μ) q = Complex.exp (-(Complex.I * (q μ : ℂ))) := by
  fin_cases μ <;> simp [MagneticWeyl.fourierChar, MagneticWeyl.intDot, bilinDot, toComplexVec, castVec,
    basisVec, Fin.sum_univ_four]
theorem fourierChar_zero (q : AmbientSpace) : MagneticWeyl.fourierChar 0 q = 1 := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.FluxZero.fourierChar_zero <;> assumption
def basisColumn (μ : Fin 4) : Matrix (Fin 4) (Fin 1) ℂ := Matrix.of fun i _ => if i = μ then 1 else 0
def gaugeFreqs (p : Fin 4 × Fin 2) : Fin 4 → ℤ := ![basisVec p.1, 0] p.2
def gaugeAmps (p : Fin 4 × Fin 2) : Matrix (Fin 4) (Fin 1) ℂ :=
  ![basisColumn p.1, -basisColumn p.1] p.2
theorem gaugeSymbolColumn_eq_charSum : gaugeSymbolColumn = charSum gaugeFreqs gaugeAmps := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.GaugeColumnFirstCoeff.gaugeSymbolColumn_eq_charSum <;> assumption
def scalarFreqs (p : Fin 4 × Fin 3) : Fin 4 → ℤ := ![0, basisVec p.1, -basisVec p.1] p.2
def scalarAmps (p : Fin 4 × Fin 3) : Matrix (Fin 1) (Fin 1) ℂ := ![(2 : ℂ) • 1, -1, -1] p.2
theorem scalarMultiplier_eq_charSum : scalarMultiplier = charSum scalarFreqs scalarAmps := by
  funext q
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have hcos : ∀ t : ℝ, 2 * Complex.cos (t : ℂ) =
      Complex.exp (Complex.I * (t : ℂ)) + Complex.exp (-(Complex.I * (t : ℂ))) := fun t => by
    rw [Complex.two_cos]
    ring_nf
  have hs : Massive.latticeSymbol (toComplexVec q) = ∑ μ, (2 - (Complex.exp (Complex.I * (q μ : ℂ)) +
      Complex.exp (-(Complex.I * (q μ : ℂ))))) :=
    Finset.sum_congr rfl fun μ _ => by rw [axisSymbol, ← hcos]; rfl
  have hf : ∀ μ : Fin 4, ∑ k : Fin 3, (MagneticWeyl.fourierChar (scalarFreqs (μ, k)) q •
      scalarAmps (μ, k)) 0 0 = 2 - (Complex.exp (Complex.I * (q μ : ℂ)) +
        Complex.exp (-(Complex.I * (q μ : ℂ)))) := fun μ => by
    rw [Fin.sum_univ_three]
    change (MagneticWeyl.fourierChar 0 q • ((2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ))) 0 0 +
      (MagneticWeyl.fourierChar (basisVec μ) q • (-1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 0 +
      (MagneticWeyl.fourierChar (-basisVec μ) q • (-1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 0 = _
    rw [fourierChar_zero, fourierChar_basisVec, fourierChar_neg_basisVec]
    simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply_eq, smul_eq_mul]
    ring
  have e₁ : scalarMultiplier q 0 0 = Massive.latticeSymbol (toComplexVec q) := by
    simp only [scalarMultiplier, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  have e₂ : charSum scalarFreqs scalarAmps q 0 0 = ∑ μ : Fin 4, ∑ k : Fin 3,
      (MagneticWeyl.fourierChar (scalarFreqs (μ, k)) q • scalarAmps (μ, k)) 0 0 := by
    simp only [charSum, Matrix.sum_apply, Fintype.sum_prod_type]
  rw [e₁, e₂, hs]
  exact Finset.sum_congr rfl fun μ _ => (hf μ).symm
end TwoSymbols
section Operators
variable {L : ℕ} {N' : ℕ} [NeZero N']
theorem coord_zero (w : ScalarL2 L) : coord w 0 = w := by
  refine lp.ext (funext fun x => ?_)
  ext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [coord]
theorem matMulUnitaryOp_column_apply (hU : UnitaryOperatorSeriesClaim)
    {V : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hV : IsUnitaryOp V)
    (X : Matrix (Fin N') (Fin 1) ℂ) (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0)
    (i : Fin N') :
    matMulUnitaryOp X V w x i = X i 0 * V w x 0 := by
  rw [matMulUnitaryOp_apply hU hV]
  simp [matMulUnitary, applyCoordwise, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    coord_zero]
theorem weylQuant_charSum_apply (hS : WeylQuantHasSum)
    (hC : FourierCoeffsOfSymbol)
    (hU : UnitaryOperatorSeriesClaim)
    {ι : Type} [Fintype ι] (φ : ℝ) (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin N') (Fin 1) ℂ)
    (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) (i : Fin N') :
    weylQuant L φ (charSum n c) w x i = ∑ p, c p i 0 * magneticWeyl L φ (n p) w x 0 := by
  rw [weylQuant_charSum hS hC hU, _root_.sum_apply, lp.coeFn_sum,
    Finset.sum_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply,
    matMulUnitaryOp_column_apply hU (magneticWeyl_isUnitary φ _)]
theorem magneticWeyl_basisVec (φ : ℝ) (μ : Fin 4) (w : ScalarL2 L) :
    magneticWeyl L φ (basisVec μ) w = magneticTranslation L φ μ w := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.ChargedPairsFormProof.magneticWeyl_basisVec <;> assumption
theorem covShift_eq_magneticWeyl {φ : ℝ} (hS : CovariantShifts (halfFluxAngle L φ)) (μ : Fin 4)
    (w : ScalarL2 L) :
    covShift (halfFluxAngle L φ) μ w = magneticWeyl L φ (basisVec μ) w := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.ChargedPairsFormProof.covShift_eq_magneticWeyl <;> assumption
theorem opAdjoint_covShift_eq (hR : MagneticWeylRelations) {φ : ℝ}
    (hS : CovariantShifts (halfFluxAngle L φ)) (μ : Fin 4) (w : ScalarL2 L) :
    opAdjoint (covShift (halfFluxAngle L φ) μ) w =
      magneticWeyl L φ (-basisVec μ) w := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.ChargedPairsFormProof.opAdjoint_covShift_eq <;> assumption
theorem magneticWeyl_neg_comp (hR : MagneticWeylRelations) (φ : ℝ) (n : Fin 4 → ℤ)
    (w : ScalarL2 L) : magneticWeyl L φ (-n) (magneticWeyl L φ n w) = w := by
  have hω : MagneticWeyl.symplecticForm (-n) n = 0 := by
    simp only [MagneticWeyl.symplecticForm, Pi.neg_apply]
    ring
  rw [(hR L φ (-n) n).1 w, hω, neg_add_cancel, (hR L φ 0 0).2.1 w]
  simp
theorem weylQuant_gaugeSymbolColumn_apply (hS : WeylQuantHasSum)
    (hC : FourierCoeffsOfSymbol)
    (hU : UnitaryOperatorSeriesClaim)
    (hR : MagneticWeylRelations) {φ : ℝ}
    (hF : CovariantShifts (halfFluxAngle L φ)) (w : ScalarL2 L)
    (x : FullSpace.Vertex L 0 0) (ν : Fin 4) :
    weylQuant L φ gaugeSymbolColumn w x ν = covShiftSubOne (halfFluxAngle L φ) ν w x 0 := by
  rw [gaugeSymbolColumn_eq_charSum, weylQuant_charSum_apply hS hC hU, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, gaugeFreqs, gaugeAmps]
  simp [basisColumn, (hR L φ 0 0).2.1 w, covShiftSubOne, covShift_eq_magneticWeyl hF,
    Finset.sum_add_distrib, sub_eq_add_neg]
theorem sum_covShiftAdj_eq_weylQuant_scalarMultiplier (hS : WeylQuantHasSum)
    (hC : FourierCoeffsOfSymbol)
    (hU : UnitaryOperatorSeriesClaim)
    (hR : MagneticWeylRelations) {φ : ℝ}
    (hF : CovariantShifts (halfFluxAngle L φ)) (w : ScalarL2 L) :
    ∑ μ, covShiftAdjSubOne (halfFluxAngle L φ) μ (covShiftSubOne (halfFluxAngle L φ) μ w) =
      weylQuant L φ scalarMultiplier w := by
  refine lp.ext (funext fun x => ?_)
  ext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rw [scalarMultiplier_eq_charSum, weylQuant_charSum_apply hS hC hU, Fintype.sum_prod_type,
    lp.coeFn_sum, Finset.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e : covShiftAdjSubOne (halfFluxAngle L φ) μ (covShiftSubOne (halfFluxAngle L φ) μ w) =
      w + w - magneticWeyl L φ (basisVec μ) w - magneticWeyl L φ (-basisVec μ) w := by
    simp only [covShiftAdjSubOne, covShiftSubOne, _root_.sub_apply,
      ContinuousLinearMap.id_apply, map_sub, opAdjoint_covShift_eq hR hF, covShift_eq_magneticWeyl hF,
      magneticWeyl_neg_comp hR]
    abel
  have e₀ : (w + w - magneticWeyl L φ (basisVec μ) w - magneticWeyl L φ (-basisVec μ) w) x 0 =
      w x 0 + w x 0 - magneticWeyl L φ (basisVec μ) w x 0 -
        magneticWeyl L φ (-basisVec μ) w x 0 := by simp
  rw [e, e₀, Fin.sum_univ_three]
  change _ = ((2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 0 0 * magneticWeyl L φ 0 w x 0 +
    (-1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 * magneticWeyl L φ (basisVec μ) w x 0 +
    (-1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 * magneticWeyl L φ (-basisVec μ) w x 0
  rw [(hR L φ 0 0).2.1 w]
  simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply_eq, smul_eq_mul]
  ring
end Operators
section Intertwining
variable {L : ℕ}
theorem opposite_isPositivelyOriented_of_not {a : ℝ} {b : InfiniteLattice.Link a}
    (hb : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem extendOddly_of_not_isPositivelyOriented {a : ℝ}
    (f : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : ¬b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = -FullSpace.extendOddly f b.opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.CovarianceProof.extendOddly_opposite <;> assumption
theorem eq_of_forwardFrom {a : ℝ} {B₁ B₂ : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (h₁ : ∀ b : InfiniteLattice.Link a, ¬b.IsPositivelyOriented → B₁ b = -B₁ b.opposite)
    (h₂ : ∀ b : InfiniteLattice.Link a, ¬b.IsPositivelyOriented → B₂ b = -B₂ b.opposite)
    (h : ∀ (x : InfiniteLattice.LatticePoint a) (μ : Fin 4),
      B₁ (InfiniteLattice.Link.forwardFrom x μ) = B₂ (InfiniteLattice.Link.forwardFrom x μ)) :
    B₁ = B₂ := by
  have hfwd : ∀ c : InfiniteLattice.Link a, c.IsPositivelyOriented → B₁ c = B₂ c := by
    rintro c ⟨μ, hμ⟩
    have e : InfiniteLattice.Link.forwardFrom c.initial μ = c := by
      refine InfiniteLattice.Link.ext rfl ?_
      change c.initial + _ = c.terminal
      rw [← hμ]
      abel
    rw [← e]
    exact h _ _
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact hfwd b hb
  · rw [h₁ b hb, h₂ b hb, hfwd _ (opposite_isPositivelyOriented_of_not hb)]
theorem massiveOp_edgeTensor_forward {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
    (hO : AbelianFieldFacts.AbelianOperators θ) (hF : CovariantShifts θ)
    (hbond : ∀ (v : VectorL2 L 4) (x : FullSpace.Vertex L 0 0) (μ : Fin 4),
      ofCoords (edgeTensor v raisingPauli) (FullSpace.forwardEdge x μ) =
        v x μ • raisingPauli)
    (w : ScalarL2 L) (v : VectorL2 L 4)
    (hv : ∀ (x : FullSpace.Vertex L 0 0) (μ : Fin 4), v x μ = covShiftSubOne θ μ w x 0)
    (hG : FullSpace.abelianMassiveHessian θ
        (FullSpace.covDiff (FullSpace.abelianLinkField θ) (raisingVertexFn w)) =
      FullSpace.covDiff (FullSpace.abelianLinkField θ)
        (FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ)
          (FullSpace.covDiff (FullSpace.abelianLinkField θ) (raisingVertexFn w))))
    (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    ofCoords (AbelianFieldDensity.massiveOp θ (edgeTensor v raisingPauli))
        (FullSpace.forwardEdge x μ) =
      covShiftSubOne θ μ
        (∑ ν, covShiftAdjSubOne θ ν (covShiftSubOne θ ν w)) x 0 • raisingPauli := by
  obtain ⟨B, hB⟩ := hF.exists_raisingForm fun ν => covShiftSubOne θ ν w
  have hanti : ∀ b : FullSpace.Edge L 0 0, ¬b.IsPositivelyOriented → B b = -B b.opposite :=
    fun b _ => by rw [hB.1.2 b, neg_neg]
  have hBB : FullSpace.covDiff (FullSpace.abelianLinkField θ) (raisingVertexFn w) = B :=
    eq_of_forwardFrom (fun b hb => extendOddly_of_not_isPositivelyOriented _ hb) hanti fun x μ => by
      rw [hF.covDiff_raising w x μ, hB.2 x μ]
  have hform : formOfPositiveValues (ofCoords (edgeTensor v raisingPauli)) = B := by
    refine eq_of_forwardFrom (fun b hb => extendOddly_of_not_isPositivelyOriented _ hb) hanti
      fun x μ => ?_
    have hp : (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented := (FullSpace.forwardEdge x μ).2
    rw [hB.2 x μ, ← hv x μ, ← hbond v x μ]
    simp only [formOfPositiveValues, FullSpace.extendOddly, if_pos hp, dif_pos hp]
    rfl
  have hT : FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B =
      raisingVertexFn (∑ ν, covShiftAdjSubOne θ ν (covShiftSubOne θ ν w)) := by
    funext y
    rw [hF.covDiffAdjoint_raising _ B hB y]
    simp only [raisingVertexFn]
    rw [lp.coeFn_sum, Finset.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  rw [congrFun (hO.hessian_apply (edgeTensor v raisingPauli)) (FullSpace.forwardEdge x μ)]
  change FullSpace.abelianMassiveHessian θ
    (formOfPositiveValues (ofCoords (edgeTensor v raisingPauli)))
    (InfiniteLattice.Link.forwardFrom x μ) = _
  rw [hform, ← hBB, hG, hBB, hT]
  exact hF.covDiff_raising _ x μ
theorem raisingPauli_ne_zero : raisingPauli ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun h 0) 1
  simp [raisingPauli, Matrices.ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY] at h1
theorem weylQuant_intertwining (hG : GaugeDirectionHessianIdentity)
    (hA : AbelianFieldFacts.AllFacts)
    (hM : AbelianFieldDensity.WeightMultiplesAndStar)
    (hS : WeylQuantHasSum) (hC : FourierCoeffsOfSymbol)
    (hU : UnitaryOperatorSeriesClaim)
    (hR : MagneticWeylRelations) (hL : Conventions.IsAdmissibleBlockingFactor L) (φ : ℝ)
    (s : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ)
    (hmass : ∀ v : VectorL2 L 4,
      AbelianFieldDensity.massiveOp (halfFluxAngle L φ) (edgeTensor v raisingPauli) =
        edgeTensor (weylQuant L φ s v) raisingPauli)
    (w : ScalarL2 L) (hw : HasFiniteSupp (raisingVertexFn w)) :
    weylQuant L φ s (weylQuant L φ gaugeSymbolColumn w) =
      weylQuant L φ gaugeSymbolColumn (weylQuant L φ scalarMultiplier w) := by
  obtain ⟨-, -, hFacts⟩ := hA
  obtain ⟨-, -, -, hθ⟩ := hFacts L hL 1 one_pos
  obtain ⟨hO, -, hF, -⟩ := hθ (halfFluxAngle L φ)
  obtain ⟨-, hsec, -, hbond, -⟩ := hM L hL
  have ht : raisingPauli ∈ Matrices.ComplexMatrix2.traceless := hsec _ (Or.inr (Or.inl rfl))
  have hfield : scaledLinearAngle L (φ / 2) = halfFluxAngle L φ := by
    funext b
    simp only [scaledLinearAngle, halfFluxAngle]
    ring
  have hGw := hG L hL (φ / 2) (raisingVertexFn w)
    (fun x => Matrices.ComplexMatrix2.traceless.smul_mem _ ht) hw
  rw [hfield] at hGw
  refine lp.ext (funext fun x => ?_)
  ext ν
  have h2 := massiveOp_edgeTensor_forward hO hF (hbond _ ht) w (weylQuant L φ gaugeSymbolColumn w)
    (weylQuant_gaugeSymbolColumn_apply hS hC hU hR hF w) hGw x ν
  rw [hmass, hbond _ ht] at h2
  have h3 := smul_left_injective ℂ raisingPauli_ne_zero h2
  rw [sum_covShiftAdj_eq_weylQuant_scalarMultiplier hS hC hU hR hF] at h3
  rw [weylQuant_gaugeSymbolColumn_apply hS hC hU hR hF]
  exact h3
end Intertwining
end GaugeRelation
open GaugeRelation in
theorem chargedSymbolGaugeRelation_holds
    (hG : GaugeDirectionHessianIdentity)
    (hA : AbelianFieldFacts.AllFacts)
    (hM : AbelianFieldDensity.WeightMultiplesAndStar)
    (hS : WeylQuantHasSum) (hC : FourierCoeffsOfSymbol)
    (hU : UnitaryOperatorSeriesClaim)
    (hR : MagneticWeylRelations)
    (hStar : MoyalProductBounds) (hProd : WeylQuantMoyalProduct)
    (hRead : FourierCoeffsFromQuantization) :
    ChargedSymbolGaugeRelation := by
  intro D C σ₁ σ₂ σ σr h φ hφ
  have hL : Conventions.IsAdmissibleBlockingFactor 13 := ⟨by decide, le_refl _⟩
  have hs : IsWeylSymbol (σ φ) := (h.isFiniteFourierSymbol φ hφ).1
  have hg : IsWeylSymbol gaugeSymbolColumn := gaugeSymbolColumn_eq_charSum ▸ isWeylSymbol_charSum _ _
  have hψ : IsWeylSymbol scalarMultiplier := scalarMultiplier_eq_charSum ▸ isWeylSymbol_charSum _ _
  have hf : |φ / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_two]
    linarith
  have hfield : scaledLinearAngle 13 (φ / 2) = halfFluxAngle 13 φ := by
    funext b
    simp only [scaledLinearAngle, halfFluxAngle]
    ring
  have hmass : ∀ v : VectorL2 13 4,
      AbelianFieldDensity.massiveOp (halfFluxAngle 13 φ) (edgeTensor v raisingPauli) =
        edgeTensor (weylQuant 13 φ (σ φ) v) raisingPauli := by
    intro v
    have e := h.massiveOp_eq 13 hL (φ / 2) hf v
    rwa [hfield, show 2 * (φ / 2) = φ by ring] at e
  have hfin : HasFiniteSupp (raisingVertexFn
      (vectorAtZero 13 (EuclideanSpace.single (0 : Fin 1) (1 : ℂ)))) := by
    refine (Set.finite_singleton (0 : FullSpace.Vertex 13 0 0)).subset fun x hx => ?_
    by_contra hne
    apply hx
    have hne' : x ≠ 0 := hne
    simp [raisingVertexFn, vectorAtZero_apply, indicatorAtZero, hne']
  have hrel := weylQuant_intertwining hG hA hM hS hC hU hR hL φ (σ φ) hmass _ hfin
  have hA' := (hStar φ 4 4 1 (σ φ) gaugeSymbolColumn hs hg).2.2.1
  have hB' := (hStar φ 4 1 1 gaugeSymbolColumn scalarMultiplier hg hψ).2.2.1
  have hread := (hRead 13 φ).1
  have hz : weylQuant 13 φ (moyalProduct φ (σ φ) gaugeSymbolColumn)
        (vectorAtZero 13 (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))) =
      weylQuant 13 φ (moyalProduct φ gaugeSymbolColumn scalarMultiplier)
        (vectorAtZero 13 (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))) := by
    rw [← hProd 13 φ 4 4 1 (σ φ) gaugeSymbolColumn hs hg,
      ← hProd 13 φ 4 1 1 gaugeSymbolColumn scalarMultiplier hg hψ]
    exact hrel
  have hcoef : MagneticWeyl.fourierCoeff (moyalProduct φ (σ φ) gaugeSymbolColumn) =
      MagneticWeyl.fourierCoeff (moyalProduct φ gaugeSymbolColumn scalarMultiplier) := by
    funext n
    rw [(hread 4 1 _ hA').1 n, (hread 4 1 _ hB').1 n]
    ext i k
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [matrixAtZero, Matrix.of_apply, ContinuousLinearMap.comp_apply]
    rw [hz]
  refine (hread 4 1 _ hA').2 _ hB' ?_
  unfold weylQuant
  rw [hcoef]
end YangMills.Construction.Tower.ConstantFieldSymbols
end
