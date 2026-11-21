import YangMills.Construction.Towers.AdjointOfAQuantization
import YangMills.Construction.Towers.ChargedSymbolAtFluxZeroProof
import YangMills.Construction.Towers.CoefficientsOfASymbol
import YangMills.Construction.Towers.CoefficientsReadOffAQuantization
import YangMills.Construction.Towers.DensityOfAResolventFromAParametrix
import YangMills.Construction.Towers.QuantizationIsTheSumOfItsSeries
import YangMills.Construction.Towers.QuantizationOfAStarProduct
import YangMills.Construction.Towers.RelationsOfTheWeylOperators
import YangMills.Construction.Towers.TheDensityIsABoundedLinearFunctional
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations YangMills.Construction.OneLoopNotation
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (torusAverage castVec toComplexVec bilinDot)
noncomputable section
namespace YangMills.Construction.Tower.MagneticWeyl
namespace ParametrixResolvent
variable {L N' : ℕ} [NeZero N']
theorem fourierChar_zero (q : AmbientSpace) : fourierChar 0 q = 1 := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.FluxZero.fourierChar_zero <;> assumption
theorem hasFourierExpansion_add_const (hCoeffs : FourierCoeffsOfSymbol)
    {a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ} (ha : HasAbsSummableFourier a)
    (C : Matrix (Fin N') (Fin N') ℂ) :
    HasFourierExpansion (fun n => fourierCoeff a n + if n = 0 then C else 0) (fun q => a q + C) := by
  intro q
  have h1 := ((hCoeffs N' N' a).1 ha).1 q
  have h2 : HasSum (fun n : Fin 4 → ℤ => fourierChar n q • (if n = 0 then C else 0)) C := by
    have h := hasSum_single (f := fun n : Fin 4 → ℤ => fourierChar n q • (if n = 0 then C else 0)) 0
      (fun n hn => by simp [hn])
    simpa [fourierChar_zero] using h
  simpa [smul_add] using h1.add h2
theorem isWeylSymbol_add_const (hCoeffs : FourierCoeffsOfSymbol)
    {a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ} (ha : IsWeylSymbol a) (C : Matrix (Fin N') (Fin N') ℂ) :
    IsWeylSymbol fun q => a q + C := by
  have h := (hCoeffs N' N' a).2 ha
  refine ⟨_, hasFourierExpansion_add_const hCoeffs h.1 C, fun j hj => ?_⟩
  refine (h.2 j hj).congr_cofinite ?_
  exact (Filter.eventually_cofinite_ne (0 : Fin 4 → ℤ)).mono fun n hn => by simp [hn]
theorem fourierCoeff_add_const (hCoeffs : FourierCoeffsOfSymbol)
    {a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ} (ha : IsWeylSymbol a) (C : Matrix (Fin N') (Fin N') ℂ)
    (n : Fin 4 → ℤ) :
    fourierCoeff (fun q => a q + C) n = fourierCoeff a n + if n = 0 then C else 0 := by
  have h := (hCoeffs N' N' a).2 ha
  have hs := ((hCoeffs N' N' _).2 (isWeylSymbol_add_const hCoeffs ha C)).1
  have hc : Summable fun n : Fin 4 → ℤ =>
      Matrices.RectangularMatrix.opNormValue (fourierCoeff a n + if n = 0 then C else 0) := by
    refine ((hCoeffs N' N' a).1 h.1).2.1.congr_cofinite ?_
    exact (Filter.eventually_cofinite_ne (0 : Fin 4 → ℤ)).mono fun n hn => by simp [hn]
  exact (congrFun (((hCoeffs N' N' _).1 hs).2.2 _
    (hasFourierExpansion_add_const hCoeffs h.1 C) hc) n).symm
theorem matMulUnitaryOp_add
    (hSeries : UnitaryOperatorSeriesClaim)
    (X Y : Matrix (Fin N') (Fin N') ℂ) {V : ScalarL2 L →ₗ[ℂ] ScalarL2 L}
    (hV : IsUnitaryOp V) :
    matMulUnitaryOp (X + Y) V =
      matMulUnitaryOp X V + matMulUnitaryOp Y V := by
  have hB := (hSeries L N' N').1
  refine ContinuousLinearMap.ext fun u => lp.ext (funext fun x => ?_)
  rw [add_apply, lp.coeFn_add, Pi.add_apply, (hB (X + Y) V hV).1,
    (hB X V hV).1, (hB Y V hV).1]
  simp [matMulUnitary, map_add]
theorem matMulUnitaryOp_zero
    (hSeries : UnitaryOperatorSeriesClaim)
    {V : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hV : IsUnitaryOp V) :
    matMulUnitaryOp (0 : Matrix (Fin N') (Fin N') ℂ) V = 0 := by
  have h := matMulUnitaryOp_add hSeries (0 : Matrix (Fin N') (Fin N') ℂ) 0 hV
  rw [add_zero] at h
  exact left_eq_add.mp h
theorem matMulUnitaryOp_scalar
    (hSeries : UnitaryOperatorSeriesClaim)
    (hRel : MagneticWeylRelations) (φ : ℝ) (c : ℂ) :
    matMulUnitaryOp (c • (1 : Matrix (Fin N') (Fin N') ℂ)) (magneticWeyl L φ 0) =
      (scalarOp c : BddOp (VectorL2 L N')) := by
  have hB := ((hSeries L N' N').1 (c • (1 : Matrix (Fin N') (Fin N') ℂ)) (magneticWeyl L φ 0)
    (magneticWeyl_isUnitary φ 0)).1
  have hId : ∀ u : ScalarL2 L, magneticWeyl L φ 0 u = u :=
    fun u => (hRel L φ 0 0).2.1 u
  refine ContinuousLinearMap.ext fun u => lp.ext (funext fun x => ?_)
  rw [hB]
  have hC : applyCoordwise (magneticWeyl L φ 0) u x = u x := by
    ext i
    simp [applyCoordwise, hId, coord]
  simp [matMulUnitary, hC, scalarOp]
theorem weylQuant_add_scalar (hCoeffs : FourierCoeffsOfSymbol)
    (hSum : WeylQuantHasSum)
    (hSeries : UnitaryOperatorSeriesClaim)
    (hRel : MagneticWeylRelations) (φ : ℝ)
    {a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ} (ha : IsWeylSymbol a) (c : ℂ) :
    weylQuant L φ (fun q => a q + c • (1 : Matrix (Fin N') (Fin N') ℂ)) =
      weylQuant L φ a + scalarOp c := by
  have hs := isWeylSymbol_add_const hCoeffs ha (c • (1 : Matrix (Fin N') (Fin N') ℂ))
  have h1 := (hSum L φ N' N' a ((hCoeffs N' N' a).2 ha).1).1
  have h2 := (hSum L φ N' N' _ ((hCoeffs N' N' _).2 hs).1).1
  have h3 : HasSum (fun n : Fin 4 → ℤ =>
      if n = 0 then (scalarOp c : BddOp (VectorL2 L N')) else 0)
      (scalarOp c) := hasSum_ite_eq 0 _
  have hU := fun n => magneticWeyl_isUnitary (L := L) φ n
  have hTerm : ∀ n : Fin 4 → ℤ,
      matMulUnitaryOp
          (fourierCoeff (fun q => a q + c • (1 : Matrix (Fin N') (Fin N') ℂ)) n)
          (magneticWeyl L φ n) =
        matMulUnitaryOp (fourierCoeff a n) (magneticWeyl L φ n) +
          if n = 0 then (scalarOp c : BddOp (VectorL2 L N')) else 0 := by
    intro n
    rw [fourierCoeff_add_const hCoeffs ha, matMulUnitaryOp_add hSeries _ _ (hU n)]
    by_cases hn : n = 0
    · subst hn
      simp only [if_true]
      rw [matMulUnitaryOp_scalar hSeries hRel]
    · simp only [if_neg hn]
      rw [matMulUnitaryOp_zero hSeries (hU n)]
  rw [funext hTerm] at h2
  exact h2.unique (h1.add h3)
end ParametrixResolvent
open ParametrixResolvent in
theorem resolventDensityViaParametrix_holds
    (hLog : Calculus.Statement)
    (hCoeffs : FourierCoeffsOfSymbol)
    (hSum : WeylQuantHasSum)
    (hStar : WeylQuantMoyalProduct)
    (hAdj : WeylQuantAdjoint)
    (hRead : FourierCoeffsFromQuantization)
    (hSeries : UnitaryOperatorSeriesClaim)
    (hRel : MagneticWeylRelations)
    (hDensity : AbelianFieldDensity.TraceIsBoundedLinear) :
    ResolventDensityViaParametrix := by
  intro L N' _ φ z w hz hw σ ρ e hσ hρ he hHerm hLower hParametrix
  have hN : 1 ≤ N' := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N')
  obtain ⟨hScalar, -, -, -, -, -, hLogarithm⟩ := hLog (VectorL2 L N') (VectorL2 L N')
  have hSelf : IsSelfAdjointOp (weylQuant L φ σ) := by
    have h := (hAdj L φ N' N' σ hσ).2
    rwa [show pointwiseAdjoint σ = σ from funext hHerm] at h
  have hS := (hScalar (weylQuant L φ σ) hSelf z 0).1
  obtain ⟨hInv, hNorm⟩ := (hLogarithm _ (z / 2) hS (by positivity) hLower).1 w hw
  have hE : ‖weylQuant L φ e‖ ≤ weightedCoeffNorm 0 e :=
    (hSum L φ N' N' e ((hCoeffs N' N' e).2 he).1).2
  have hShift : weylQuant L φ
      (fun q => σ q + ((z + w : ℝ) : ℂ) • (1 : Matrix (Fin N') (Fin N') ℂ)) =
      addScalar (addScalar (weylQuant L φ σ) z) w := by
    rw [weylQuant_add_scalar hCoeffs hSum hSeries hRel φ hσ]
    simp only [addScalar, scalarOp]
    push_cast
    rw [add_smul, add_assoc]
  have hOne : weylQuant L φ (fun q => 1 + e q) = 1 + weylQuant L φ e := by
    have h := weylQuant_add_scalar (L := L) hCoeffs hSum hSeries hRel φ he (1 : ℂ)
    have hf : (fun q => 1 + e q) = fun q => e q + (1 : ℂ) • (1 : Matrix (Fin N') (Fin N') ℂ) := by
      funext q
      rw [one_smul, add_comm]
    rw [hf, h, add_comm]
    congr 1
    simp [scalarOp]
    rfl
  have hProd : weylQuant L φ ρ * addScalar (addScalar (weylQuant L φ σ) z) w =
      1 + weylQuant L φ e := by
    rw [← hShift, ← hOne, ← hParametrix]
    exact hStar L φ N' N' N' ρ _ hρ (isWeylSymbol_add_const hCoeffs hσ _)
  have hRes : weylQuant L φ ρ =
      inverseOp (addScalar (addScalar (weylQuant L φ σ) z) w) +
        weylQuant L φ e *
          inverseOp (addScalar (addScalar (weylQuant L φ σ) z) w) := by
    calc weylQuant L φ ρ
        = weylQuant L φ ρ * (addScalar (addScalar (weylQuant L φ σ) z) w *
            inverseOp (addScalar (addScalar (weylQuant L φ σ) z) w)) := by
          rw [hInv.1, mul_one]
      _ = _ := by rw [← mul_assoc, hProd, add_mul, one_mul]
  obtain ⟨hLin, hBd, -⟩ := ((hDensity L 0).2.2 N' hN).1
  have hLin' : ∀ (T T' : BddOp (VectorL2 L N')) (s : ℂ),
      AbelianFieldDensity.vecTraceAt (T + s • T') 0 =
        AbelianFieldDensity.vecTraceAt T 0 + s * AbelianFieldDensity.vecTraceAt T' 0 := hLin
  have hBd' : ∀ T : BddOp (VectorL2 L N'),
      ‖AbelianFieldDensity.vecTraceAt T 0‖ ≤ (N' : ℝ) * ‖T‖ := hBd
  have hTr := (hRead L φ).2 N' ρ hρ
  have hDiff :
      AbelianFieldDensity.vecTraceAt
          (inverseOp (addScalar (addScalar (weylQuant L φ σ) z) w)) 0 -
        torusAverage (fun q => Matrices.RectangularMatrix.diagSum (ρ q)) =
      -AbelianFieldDensity.vecTraceAt
        (weylQuant L φ e *
          inverseOp (addScalar (addScalar (weylQuant L φ σ) z) w)) 0 := by
    have h := hLin' (inverseOp (addScalar (addScalar (weylQuant L φ σ) z) w))
      (weylQuant L φ e * inverseOp (addScalar (addScalar (weylQuant L φ σ) z) w)) 1
    rw [one_smul, one_mul, ← hRes, hTr.1, hTr.2] at h
    rw [h]
    ring
  have hNonneg : 0 ≤ weightedCoeffNorm 0 e := (norm_nonneg _).trans hE
  rw [hDiff, norm_neg]
  calc _ ≤ (N' : ℝ) * ‖weylQuant L φ e *
        inverseOp (addScalar (addScalar (weylQuant L φ σ) z) w)‖ := hBd' _
    _ ≤ (N' : ℝ) * (weightedCoeffNorm 0 e * (z / 2 + w)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact (norm_mul_le _ _).trans
          (mul_le_mul hE hNorm (norm_nonneg _) hNonneg)
    _ = _ := by ring
end YangMills.Construction.Tower.MagneticWeyl
end
