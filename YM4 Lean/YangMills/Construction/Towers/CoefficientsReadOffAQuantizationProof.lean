import YangMills.Construction.Towers.AlgebraOfMatricesTimesUnitaryOperators
import YangMills.Construction.Towers.AsymptoticsOfTheMassiveCoefficientProof
import YangMills.Construction.Towers.CoefficientsOfASymbol
import YangMills.Construction.Towers.CoefficientsReadOffAQuantization
import YangMills.Construction.Towers.QuantizationIsTheSumOfItsSeries
import YangMills.Construction.Towers.RelationsOfTheWeylOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open UnitLatticeL2 UnitaryCombinations AbelianFieldDensity OneLoopNotation
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (torusAverage castVec)
open MagneticWeyl
section Auxiliary
variable {L P Q : ℕ}
private def entryAtZeroCLM (i : Fin P) (k : Fin Q) :
    BddOpBetween (VectorL2 L Q) (VectorL2 L P) →L[ℂ] ℂ :=
  ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin P) →L[ℂ] ℂ).comp
      (lp.evalCLM ℂ (fun _ : FullSpace.Vertex L 0 0 => EuclideanSpace ℂ (Fin P)) 2 0)).comp
    (ContinuousLinearMap.apply ℂ (VectorL2 L P)
      (vectorAtZero L (EuclideanSpace.single k (1 : ℂ))))
private theorem hasSum_matrixAtZero_entry {ι : Type}
    {S : ι → BddOpBetween (VectorL2 L Q) (VectorL2 L P)}
    {T : BddOpBetween (VectorL2 L Q) (VectorL2 L P)}
    (hST : HasSum S T) (i : Fin P) (k : Fin Q) :
    HasSum (fun j => matrixAtZero (S j) i k) (matrixAtZero T i k) :=
  (entryAtZeroCLM i k).hasSum hST
private theorem vecTraceAt_zero_eq_diagSum [NeZero P]
    (T : BddOpBetween (VectorL2 L P) (VectorL2 L P)) :
    vecTraceAt T 0 = Matrices.RectangularMatrix.diagSum (matrixAtZero T) := by
  unfold vecTraceAt
  have hset : {ι : Fin P × FullSpace.Vertex L 0 0 | ι.2 = 0} =
      (fun l : Fin P => (l, (0 : FullSpace.Vertex L 0 0))) '' Set.univ := by
    ext ⟨l, y⟩
    simp [eq_comm]
  rw [hset, finsum_mem_image (fun _ _ _ _ h => (Prod.ext_iff.1 h).1), finsum_mem_univ,
    finsum_eq_sum_of_fintype]
  rfl
private theorem magneticWeyl_comp_isUnitaryOp (φ : ℝ) (u v : Fin 4 → ℤ) :
    IsUnitaryOp (magneticWeyl L φ u ∘ₗ magneticWeyl L φ v) := by
  have hu := magneticWeyl_isUnitary (L := L) φ u
  have hv := magneticWeyl_isUnitary (L := L) φ v
  refine ⟨?_, fun w => ?_⟩
  · rw [LinearMap.coe_comp]
    exact hu.1.comp hv.1
  · rw [LinearMap.comp_apply, hu.2, hv.2]
private theorem magneticWeyl_comp_vectorAtZero (hRel : MagneticWeylRelations) (φ : ℝ)
    (u v : Fin 4 → ℤ) :
    (magneticWeyl L φ (-u) ∘ₗ magneticWeyl L φ v)
        (vectorAtZero L (EuclideanSpace.single 0 (1 : ℂ))) 0 0 = if v = u then 1 else 0 := by
  rw [LinearMap.comp_apply, (hRel L φ (-u) v).1, lp.coeFn_smul, Pi.smul_apply,
    (hRel L φ (-u + v) 0).2.2.2]
  by_cases huv : v = u
  · subst huv
    have hsym : symplecticForm (-v) v = 0 := by
      simp only [symplecticForm, Pi.neg_apply]
      ring
    simp [kronecker, hsym]
  · have hne : -u + v ≠ 0 := fun h => huv (by
      have := congrArg (fun x => u + x) h
      simpa using this)
    simp [kronecker, hne, huv]
private theorem magneticWeyl_vectorAtZero (hRel : MagneticWeylRelations) (φ : ℝ)
    (u : Fin 4 → ℤ) :
    magneticWeyl L φ u (vectorAtZero L (EuclideanSpace.single 0 (1 : ℂ))) 0 0 =
      if u = 0 then 1 else 0 := by
  rw [(hRel L φ u 0).2.2.2]
  by_cases hu : u = 0 <;> simp [kronecker, hu]
private theorem norm_apply_le_opNormValue [NeZero P] [NeZero Q] (X : Matrix (Fin P) (Fin Q) ℂ)
    (i : Fin P) (k : Fin Q) : ‖X i k‖ ≤ Matrices.RectangularMatrix.opNormValue X := by apply _root_.YangMills.Construction.Tower.Massive.CoefficientAsymptoticsProof.norm_apply_le_opNormValue <;> assumption
private theorem opNormValue_scalar_le (t : ℂ) :
    Matrices.RectangularMatrix.opNormValue (Matrix.of fun _ _ => t : Matrix (Fin 1) (Fin 1) ℂ) ≤ ‖t‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg t) fun v => ?_
  have hsc : LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin (Matrix.of fun _ _ => t : Matrix (Fin 1) (Fin 1) ℂ)) v = t • v := by
    ext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  rw [hsc, norm_smul]
end Auxiliary
private theorem fourierCoeff_eq_matrixAtZero
    (hAlg : MatMulUnitaryOpAlgebra)
    (hSum : WeylQuantHasSum)
    (hRel : MagneticWeylRelations)
    (hCoef : FourierCoeffsOfSymbol)
    (L : ℕ) (φ : ℝ) (P Q : ℕ) [NeZero P] [NeZero Q]
    (a : AmbientSpace → Matrix (Fin P) (Fin Q) ℂ) (ha : IsWeylSymbol a) (u : Fin 4 → ℤ) :
    fourierCoeff a u =
      matrixAtZero ((matMulUnitaryOp (1 : Matrix (Fin P) (Fin P) ℂ)
        (magneticWeyl L φ (-u))).comp (weylQuant L φ a)) := by
  have hser := (hSum L φ P Q a ((hCoef P Q a).2 ha).1).1
  have hser' := ((ContinuousLinearMap.compL ℂ (VectorL2 L Q) (VectorL2 L P)
    (VectorL2 L P))
      (matMulUnitaryOp (1 : Matrix (Fin P) (Fin P) ℂ)
        (magneticWeyl L φ (-u)))).hasSum hser
  ext i k
  have h := hasSum_matrixAtZero_entry hser' i k
  have terms : ∀ v : Fin 4 → ℤ,
      matrixAtZero ((ContinuousLinearMap.compL ℂ (VectorL2 L Q) (VectorL2 L P)
        (VectorL2 L P))
          (matMulUnitaryOp (1 : Matrix (Fin P) (Fin P) ℂ) (magneticWeyl L φ (-u)))
          (matMulUnitaryOp (fourierCoeff a v) (magneticWeyl L φ v))) i k =
        if v = u then fourierCoeff a u i k else 0 := by
    intro v
    rw [ContinuousLinearMap.compL_apply,
      (hAlg L P P (magneticWeyl L φ (-u)) (magneticWeyl_isUnitary φ (-u))).2.1 Q
        (magneticWeyl L φ v) (magneticWeyl_isUnitary φ v) 1 (fourierCoeff a v), Matrix.one_mul,
      (hAlg L P Q (magneticWeyl L φ (-u) ∘ₗ magneticWeyl L φ v)
        (magneticWeyl_comp_isUnitaryOp φ (-u) v)).2.2.2 (fourierCoeff a v),
      magneticWeyl_comp_vectorAtZero hRel]
    by_cases huv : v = u
    · subst huv; simp
    · simp [huv]
  simp only [terms] at h
  exact ((hasSum_ite_eq u _).unique h)
private theorem matrixAtZero_weylQuant
    (hAlg : MatMulUnitaryOpAlgebra)
    (hSum : WeylQuantHasSum)
    (hRel : MagneticWeylRelations)
    (hCoef : FourierCoeffsOfSymbol)
    (L : ℕ) (φ : ℝ) (P Q : ℕ) [NeZero P] [NeZero Q]
    (a : AmbientSpace → Matrix (Fin P) (Fin Q) ℂ) (ha : IsWeylSymbol a) :
    matrixAtZero (weylQuant L φ a) = fourierCoeff a 0 := by
  have hser := (hSum L φ P Q a ((hCoef P Q a).2 ha).1).1
  ext i k
  have h := hasSum_matrixAtZero_entry hser i k
  have terms : ∀ v : Fin 4 → ℤ,
      matrixAtZero (matMulUnitaryOp (fourierCoeff a v) (magneticWeyl L φ v)) i k =
        if v = 0 then fourierCoeff a 0 i k else 0 := by
    intro v
    rw [(hAlg L P Q (magneticWeyl L φ v) (magneticWeyl_isUnitary φ v)).2.2.2 (fourierCoeff a v),
      magneticWeyl_vectorAtZero hRel]
    by_cases hv : v = 0
    · subst hv; simp
    · simp [hv]
  simp only [terms] at h
  exact h.unique (hasSum_ite_eq 0 _)
private theorem diagSum_fourierCoeff_zero (hCoef : FourierCoeffsOfSymbol)
    (P : ℕ) [NeZero P] (a : AmbientSpace → Matrix (Fin P) (Fin P) ℂ) (ha : IsWeylSymbol a) :
    Matrices.RectangularMatrix.diagSum (fourierCoeff a 0) =
      torusAverage fun q => Matrices.RectangularMatrix.diagSum (a q) := by
  obtain ⟨hexp, hsum, -⟩ := (hCoef P P a).1 ((hCoef P P a).2 ha).1
  let c : (Fin 4 → ℤ) → Matrix (Fin 1) (Fin 1) ℂ :=
    fun u => Matrix.of fun _ _ => Matrices.RectangularMatrix.diagSum (fourierCoeff a u)
  let b : AmbientSpace → Matrix (Fin 1) (Fin 1) ℂ :=
    fun q => Matrix.of fun _ _ => Matrices.RectangularMatrix.diagSum (a q)
  have hcb : HasFourierExpansion c b := by
    intro q
    have hentry : ∀ i k, HasSum (fun u => fourierChar u q • fourierCoeff a u i k) (a q i k) := by
      intro i k
      have h1 := Pi.hasSum.1 (hexp q) i
      exact Pi.hasSum.1 h1 k
    have hdiag : HasSum (fun u => ∑ i, fourierChar u q • fourierCoeff a u i i) (∑ i, a q i i) :=
      hasSum_sum fun i _ => hentry i i
    refine Pi.hasSum.2 fun i => Pi.hasSum.2 fun k => ?_
    change HasSum (fun u => fourierChar u q • Matrices.RectangularMatrix.diagSum (fourierCoeff a u))
      (Matrices.RectangularMatrix.diagSum (a q))
    simpa only [Matrices.RectangularMatrix.diagSum, Finset.smul_sum] using hdiag
  have hcs : Summable fun u => Matrices.RectangularMatrix.opNormValue (c u) := by
    refine Summable.of_nonneg_of_le (fun u => ?_) (fun u => ?_)
      (hsum.mul_left (P : ℝ))
    · exact norm_nonneg (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (c u)))
    · refine (opNormValue_scalar_le _).trans ?_
      calc ‖Matrices.RectangularMatrix.diagSum (fourierCoeff a u)‖
          ≤ ∑ i : Fin P, ‖fourierCoeff a u i i‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin P, Matrices.RectangularMatrix.opNormValue (fourierCoeff a u) :=
            Finset.sum_le_sum fun i _ => norm_apply_le_opNormValue _ i i
        _ = (P : ℝ) * Matrices.RectangularMatrix.opNormValue (fourierCoeff a u) := by simp
  have hb : HasAbsSummableFourier b := ⟨c, hcb, hcs⟩
  have huniq := ((hCoef 1 1 b).1 hb).2.2 c hcb hcs
  have h0 : Matrices.RectangularMatrix.diagSum (fourierCoeff a 0) = fourierCoeff b 0 0 0 :=
    congrFun (congrFun (congrFun huniq 0) 0) 0
  have hdot : ∀ q : AmbientSpace, MagneticWeyl.intDot 0 q = 0 := fun q => by
    simp [MagneticWeyl.intDot, PeriodicOperators.bilinDot, castVec,
      PeriodicOperators.toComplexVec]
  rw [h0]
  show torusAverage (fun q => b q 0 0 * Complex.exp (-(Complex.I * intDot 0 q))) = _
  simp only [hdot, mul_zero, neg_zero, Complex.exp_zero, mul_one]
  rfl
theorem fourierCoeffsFromQuantization_holds
    (hAlg : MatMulUnitaryOpAlgebra)
    (hSum : WeylQuantHasSum)
    (hRel : MagneticWeylRelations)
    (hCoef : FourierCoeffsOfSymbol) :
    FourierCoeffsFromQuantization := by
  intro L φ
  refine ⟨fun P Q _ _ a ha => ⟨fourierCoeff_eq_matrixAtZero hAlg hSum hRel hCoef L φ P Q a ha,
    fun b hb heq => ?_⟩, fun P _ a ha => ⟨?_, diagSum_fourierCoeff_zero hCoef P a ha⟩⟩
  · have hcoef : fourierCoeff a = fourierCoeff b := funext fun u => by
      rw [fourierCoeff_eq_matrixAtZero hAlg hSum hRel hCoef L φ P Q a ha,
        fourierCoeff_eq_matrixAtZero hAlg hSum hRel hCoef L φ P Q b hb, heq]
    funext q
    have ha' := ((hCoef P Q a).1 ((hCoef P Q a).2 ha).1).1 q
    have hb' := ((hCoef P Q b).1 ((hCoef P Q b).2 hb).1).1 q
    rw [hcoef] at ha'
    exact ha'.unique hb'
  · rw [vecTraceAt_zero_eq_diagSum, matrixAtZero_weylQuant hAlg hSum hRel hCoef L φ P P a ha]
end YangMills.Construction.Tower
end
