import YangMills.Construction.Towers.AlgebraOfMatricesTimesUnitaryOperators
import YangMills.Construction.Towers.MoyalExpansionOfAStarProductProof
import YangMills.Construction.Towers.QuantizationIsTheSumOfItsSeries
import YangMills.Construction.Towers.QuantizationOfAStarProduct
import YangMills.Construction.Towers.RelationsOfTheWeylOperators
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations YangMills.Construction.OneLoopNotation
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Matrices.RectangularMatrix (opNormValue)
noncomputable section
namespace YangMills.Construction.Tower
open MagneticWeyl
section Matrices
open scoped Matrix.Norms.L2Operator
variable {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
private theorem opNormValue_eq_norm (M : Matrix (Fin p) (Fin q) ℂ) :
    opNormValue M = ‖M‖ :=
  (Matrix.l2_opNorm_def M).symm
private theorem opNormValue_nonneg (M : Matrix (Fin p) (Fin q) ℂ) :
    0 ≤ opNormValue M := by apply _root_.YangMills.Construction.Tower.MagneticWeyl.FluxZeroCalculus.opNormValue_nonneg <;> assumption
private theorem summable_of_opNormValue_le {ι : Type}
    (F : ι → Matrix (Fin p) (Fin q) ℂ) (b : ι → ℝ) (hb : Summable b)
    (hFb : ∀ i, opNormValue (F i) ≤ b i) : Summable F := by
  have : CompleteSpace (Matrix (Fin p) (Fin q) ℂ) := FiniteDimensional.complete ℂ _
  refine Summable.of_norm_bounded hb fun i => ?_
  rw [← opNormValue_eq_norm]
  exact hFb i
private theorem opNormValue_mul_le (M : Matrix (Fin p) (Fin q) ℂ)
    (M' : Matrix (Fin q) (Fin r) ℂ) :
    opNormValue (M * M') ≤ opNormValue M * opNormValue M' := by apply _root_.YangMills.Construction.Tower.MoyalRemainderProof.opNormValue_mul_le <;> assumption
private theorem opNormValue_smul_of_norm_one (c : ℂ) (hc : ‖c‖ = 1)
    (M : Matrix (Fin p) (Fin q) ℂ) :
    opNormValue (c • M) = opNormValue M := by
  simp only [opNormValue_eq_norm]
  rw [norm_smul, hc, one_mul]
end Matrices
private theorem matMulUnitaryOp_smul_unitary
    (hSer : UnitaryOperatorSeriesClaim)
    {L p q : ℕ} [NeZero p] [NeZero q] (c : ℂ) (M : Matrix (Fin p) (Fin q) ℂ)
    (U : ScalarL2 L →ₗ[ℂ] ScalarL2 L) (hU : IsUnitaryOp U)
    (hcU : IsUnitaryOp (c • U)) :
    matMulUnitaryOp M (c • U) = matMulUnitaryOp (c • M) U := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun x => ?_)
  rw [((hSer L p q).1 M (c • U) hcU).1 v x, ((hSer L p q).1 (c • M) U hU).1 v x]
  have hcoord : applyCoordwise (c • U) v x = c • applyCoordwise U v x := by
    ext i
    simp [applyCoordwise]
  simp only [matMulUnitary, hcoord, map_smul, LinearMap.smul_apply]
private theorem IsUnitaryOp.comp' {L : ℕ}
    {U U' : ScalarL2 L →ₗ[ℂ] ScalarL2 L} (hU : IsUnitaryOp U)
    (hU' : IsUnitaryOp U') : IsUnitaryOp (U ∘ₗ U') :=
  ⟨hU.1.comp hU'.1, fun v => (hU.2 _).trans (hU'.2 v)⟩
private theorem summable_prod_mul_of_nonneg {ι : Type} (u v : ι → ℝ) (hu : Summable u)
    (hv : Summable v) (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i) :
    Summable fun k : ι × ι => u k.1 * v k.2 :=
  hu.mul_of_nonneg hv hu0 hv0
private theorem hasSum_prod_comp_of_norm_le {ι E₁ E₂ E₃ : Type} [NormedAddCommGroup E₁]
    [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [NormedAddCommGroup E₃]
    [NormedSpace ℂ E₃] [CompleteSpace E₃] {T : ι → E₂ →L[ℂ] E₃} {S : ι → E₁ →L[ℂ] E₂}
    {A : E₂ →L[ℂ] E₃} {B : E₁ →L[ℂ] E₂} (hT : HasSum T A) (hS : HasSum S B) {u v : ι → ℝ}
    (hTu : ∀ i, ‖T i‖ ≤ u i) (hSv : ∀ i, ‖S i‖ ≤ v i) (hu : Summable u) (hv : Summable v) :
    HasSum (fun k : ι × ι => (T k.1).comp (S k.2)) (A.comp B) := by
  have hu0 : ∀ i, 0 ≤ u i := fun i => (norm_nonneg _).trans (hTu i)
  have hv0 : ∀ i, 0 ≤ v i := fun i => (norm_nonneg _).trans (hSv i)
  have hnorm : Summable fun k : ι × ι => ‖(T k.1).comp (S k.2)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hTu _) (hSv _) (norm_nonneg _) (hu0 _)))
      (hu.mul_of_nonneg hv hu0 hv0)
  have hsum : Summable fun k : ι × ι => (T k.1).comp (S k.2) := hnorm.of_norm
  have hfib : HasSum (fun i => (T i).comp B) (∑' k : ι × ι, (T k.1).comp (S k.2)) :=
    hsum.hasSum.prod_fiberwise fun i => (ContinuousLinearMap.compL ℂ E₁ E₂ E₃ (T i)).hasSum hS
  have hcol : HasSum (fun i => (T i).comp B) (A.comp B) :=
    ((ContinuousLinearMap.compL ℂ E₁ E₂ E₃).flip B).hasSum hT
  rw [← hfib.unique hcol]
  exact hsum.hasSum
private theorem hasSum_of_hasSum_addFibers {ι E : Type} [AddCommMonoid ι] [NormedAddCommGroup E]
    {F : ι × ι → E} {s : E} (hF : HasSum F s) {G : ι → E}
    (hG : ∀ m, HasSum (fun k : {k : ι × ι // k.1 + k.2 = m} => F k.1) (G m)) : HasSum G s :=
  ((Equiv.sigmaFiberEquiv fun k : ι × ι => k.1 + k.2).hasSum_iff.2 hF).sigma hG
private theorem norm_exp_symplecticPhase (θ : ℝ) (m m' : Fin 4 → ℤ) :
    ‖Complex.exp (Complex.I / 2 * (θ : ℂ) * (symplecticForm m m' : ℂ))‖ = 1 := by
  have : Complex.I / 2 * (θ : ℂ) * (symplecticForm m m' : ℂ) =
      ((θ * (symplecticForm m m' : ℝ) / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]
private theorem matMulUnitaryOp_magneticWeyl_comp
    (hRel : MagneticWeylRelations)
    (hAlg : MatMulUnitaryOpAlgebra)
    (hSer : UnitaryOperatorSeriesClaim)
    (L : ℕ) (θ : ℝ) {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (M : Matrix (Fin p) (Fin q) ℂ) (M' : Matrix (Fin q) (Fin r) ℂ) (m m' : Fin 4 → ℤ) :
    (matMulUnitaryOp M (magneticWeyl L θ m)).comp
        (matMulUnitaryOp M' (magneticWeyl L θ m')) =
      matMulUnitaryOp
        (Complex.exp (Complex.I / 2 * (θ : ℂ) * (symplecticForm m m' : ℂ)) • (M * M'))
        (magneticWeyl L θ (m + m')) := by
  have hU : ∀ m, IsUnitaryOp (magneticWeyl L θ m) := magneticWeyl_isUnitary θ
  have hcomp := (hAlg L p q (magneticWeyl L θ m) (hU m)).2.1 r (magneticWeyl L θ m')
    (hU m') M M'
  have hWW : magneticWeyl L θ m ∘ₗ magneticWeyl L θ m' =
      Complex.exp (Complex.I / 2 * (θ : ℂ) * (symplecticForm m m' : ℂ)) •
        magneticWeyl L θ (m + m') :=
    LinearMap.ext fun v => (hRel L θ m m').1 v
  have hcU := IsUnitaryOp.comp' (hU m) (hU m')
  rw [hWW] at hcomp hcU
  rw [hcomp, matMulUnitaryOp_smul_unitary hSer _ _ _ (hU _) hcU]
private theorem exists_continuousLinear_matMulUnitaryOp
    (hAlg : MatMulUnitaryOpAlgebra) (L : ℕ) {p q : ℕ} [NeZero p]
    [NeZero q] (U : ScalarL2 L →ₗ[ℂ] ScalarL2 L)
    (hU : IsUnitaryOp U) :
    ∃ Ψ : Matrix (Fin p) (Fin q) ℂ →ₗ[ℂ]
      BddOpBetween (VectorL2 L q) (VectorL2 L p),
      Continuous Ψ ∧ ∀ M, Ψ M = matMulUnitaryOp M U := by
  have hlin := (hAlg L p q U hU).1
  have hzero : matMulUnitaryOp (0 : Matrix (Fin p) (Fin q) ℂ) U = 0 := by
    simpa using hlin 1 0 0
  let Ψ : Matrix (Fin p) (Fin q) ℂ →ₗ[ℂ]
      BddOpBetween (VectorL2 L q) (VectorL2 L p) :=
    { toFun := fun M => matMulUnitaryOp M U
      map_add' := fun M M' => by simpa using hlin 1 M M'
      map_smul' := fun s M => by simpa [hzero] using hlin s M 0 }
  exact ⟨Ψ, Ψ.continuous_of_finiteDimensional, fun _ => rfl⟩
private theorem hasSum_addFiber_moyalCoeff
    (hRel : MagneticWeylRelations)
    (hAlg : MatMulUnitaryOpAlgebra)
    (hSer : UnitaryOperatorSeriesClaim)
    (L : ℕ) (θ : ℝ) {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (f : AmbientSpace → Matrix (Fin p) (Fin q) ℂ) (g : AmbientSpace → Matrix (Fin q) (Fin r) ℂ)
    (hprod : Summable fun k : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
      opNormValue (fourierCoeff f k.1) * opNormValue (fourierCoeff g k.2))
    (m : Fin 4 → ℤ) :
    HasSum (fun k : {k : (Fin 4 → ℤ) × (Fin 4 → ℤ) // k.1 + k.2 = m} =>
        (matMulUnitaryOp (fourierCoeff f k.1.1) (magneticWeyl L θ k.1.1)).comp
          (matMulUnitaryOp (fourierCoeff g k.1.2) (magneticWeyl L θ k.1.2)))
      (matMulUnitaryOp (moyalCoeff θ f g m) (magneticWeyl L θ m)) := by
  obtain ⟨Ψ, hcont, hΨ⟩ := exists_continuousLinear_matMulUnitaryOp (p := p) (q := r)
    hAlg L (magneticWeyl L θ m) (magneticWeyl_isUnitary θ m)
  have hsumm : Summable fun k : {k : (Fin 4 → ℤ) × (Fin 4 → ℤ) // k.1 + k.2 = m} =>
      Complex.exp (Complex.I / 2 * (θ : ℂ) * (symplecticForm k.1.1 k.1.2 : ℂ)) •
        (fourierCoeff f k.1.1 * fourierCoeff g k.1.2) := by
    refine summable_of_opNormValue_le _ _
      (hprod.comp_injective Subtype.val_injective) fun k => ?_
    rw [opNormValue_smul_of_norm_one _ (norm_exp_symplecticPhase θ _ _)]
    exact opNormValue_mul_le _ _
  have hmap := hsumm.hasSum.map Ψ hcont
  have hval : Ψ (∑' k : {k : (Fin 4 → ℤ) × (Fin 4 → ℤ) // k.1 + k.2 = m},
      Complex.exp (Complex.I / 2 * (θ : ℂ) * (symplecticForm k.1.1 k.1.2 : ℂ)) •
        (fourierCoeff f k.1.1 * fourierCoeff g k.1.2)) =
      matMulUnitaryOp (moyalCoeff θ f g m) (magneticWeyl L θ m) := hΨ _
  rw [hval] at hmap
  have hfun : (fun k : {k : (Fin 4 → ℤ) × (Fin 4 → ℤ) // k.1 + k.2 = m} =>
      (matMulUnitaryOp (fourierCoeff f k.1.1) (magneticWeyl L θ k.1.1)).comp
        (matMulUnitaryOp (fourierCoeff g k.1.2) (magneticWeyl L θ k.1.2))) =
      Ψ ∘ fun k : {k : (Fin 4 → ℤ) × (Fin 4 → ℤ) // k.1 + k.2 = m} =>
        Complex.exp (Complex.I / 2 * (θ : ℂ) * (symplecticForm k.1.1 k.1.2 : ℂ)) •
          (fourierCoeff f k.1.1 * fourierCoeff g k.1.2) := by
    funext k
    rw [Function.comp_apply, hΨ, matMulUnitaryOp_magneticWeyl_comp hRel hAlg hSer, k.2]
  rw [hfun]
  exact hmap
theorem weylQuant_moyalProduct_holds
    (hQ : WeylQuantHasSum)
    (hMoyal : MoyalProductBounds)
    (hRel : MagneticWeylRelations)
    (hFour : FourierCoeffsOfSymbol)
    (hAlg : MatMulUnitaryOpAlgebra)
    (hSer : UnitaryOperatorSeriesClaim) :
    WeylQuantMoyalProduct := by
  intro L θ p q r _ _ _ f g hf hg
  have hsf : HasAbsSummableFourier f := ((hFour p q f).2 hf).1
  have hsg : HasAbsSummableFourier g := ((hFour q r g).2 hg).1
  have hcf := ((hFour p q f).1 hsf).2.1
  have hcg := ((hFour q r g).1 hsg).2.1
  have hU : ∀ m, IsUnitaryOp (magneticWeyl L θ m) := magneticWeyl_isUnitary θ
  have hTn : ∀ m, ‖matMulUnitaryOp (fourierCoeff f m) (magneticWeyl L θ m)‖ ≤
      opNormValue (fourierCoeff f m) := fun m => ((hSer L p q).1 _ _ (hU m)).2
  have hSn : ∀ m, ‖matMulUnitaryOp (fourierCoeff g m) (magneticWeyl L θ m)‖ ≤
      opNormValue (fourierCoeff g m) := fun m => ((hSer L q r).1 _ _ (hU m)).2
  have hf0 : ∀ m, 0 ≤ opNormValue (fourierCoeff f m) :=
    fun m => opNormValue_nonneg (fourierCoeff f m)
  have hg0 : ∀ m, 0 ≤ opNormValue (fourierCoeff g m) :=
    fun m => opNormValue_nonneg (fourierCoeff g m)
  have hprod : Summable fun k : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
      opNormValue (fourierCoeff f k.1) * opNormValue (fourierCoeff g k.2) :=
    summable_prod_mul_of_nonneg (fun m => opNormValue (fourierCoeff f m))
      (fun m => opNormValue (fourierCoeff g m)) hcf hcg hf0 hg0
  have hdouble := hasSum_prod_comp_of_norm_le (hQ L θ p q f hsf).1
    (hQ L θ q r g hsg).1 hTn hSn hcf hcg
  have hfibers := hasSum_of_hasSum_addFibers hdouble (hasSum_addFiber_moyalCoeff hRel hAlg hSer L θ f g hprod)
  obtain ⟨-, -, hsym, hcoef, -⟩ := hMoyal θ p q r f g hf hg
  have hquant := (hQ L θ p r (moyalProduct θ f g) ((hFour p r _).2 hsym).1).1
  rw [hcoef] at hquant
  exact hfibers.unique hquant
end YangMills.Construction.Tower
end
