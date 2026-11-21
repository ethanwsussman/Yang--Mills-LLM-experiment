import YangMills.Construction.Towers.AbelianFields
import YangMills.Construction.Towers.SeriesOfUnitaryOperatorsWithSummableMatrixCoefficients
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations
open YangMills.Construction.OneLoopNotation
open YangMills.Construction.PeriodicOperators (torusAverage castVec toComplexVec bilinDot)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.MagneticWeyl
section Shifts
variable {L : ℕ}
def twistedTranslateFun (τ : FullSpace.Vertex L 0 0) (p : FullSpace.Vertex L 0 0 → ℂ)
    (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) : EuclideanSpace ℂ (Fin 1) :=
  p x • w (x + τ)
theorem norm_twistedTranslateFun (τ : FullSpace.Vertex L 0 0) {p : FullSpace.Vertex L 0 0 → ℂ}
    (hp : ∀ x, ‖p x‖ = 1) (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) :
    ‖twistedTranslateFun τ p w x‖ = ‖w (x + τ)‖ := by
  simp [twistedTranslateFun, norm_smul, hp]
theorem memℓp_twistedTranslateFun (τ : FullSpace.Vertex L 0 0) {p : FullSpace.Vertex L 0 0 → ℂ}
    (hp : ∀ x, ‖p x‖ = 1) (w : ScalarL2 L) : Memℓp (twistedTranslateFun τ p w) 2 := by
  have hw := lp.memℓp w
  rw [memℓp_gen_iff (by norm_num)] at hw ⊢
  simp only [norm_twistedTranslateFun τ hp]
  exact (Equiv.addRight τ).summable_iff.mpr hw
def twistedTranslate (τ : FullSpace.Vertex L 0 0) (p : FullSpace.Vertex L 0 0 → ℂ)
    (hp : ∀ x, ‖p x‖ = 1) : ScalarL2 L →ₗᵢ[ℂ] ScalarL2 L where
  toFun w := ⟨twistedTranslateFun τ p w, memℓp_twistedTranslateFun τ hp w⟩
  map_add' w w' := lp.ext (funext fun x => by
    change p x • (w + w' : ScalarL2 L) (x + τ) = p x • w (x + τ) + p x • w' (x + τ)
    rw [lp.coeFn_add, Pi.add_apply, smul_add])
  map_smul' c w := lp.ext (funext fun x => by
    change p x • (c • w : ScalarL2 L) (x + τ) = c • (p x • w (x + τ))
    rw [lp.coeFn_smul, Pi.smul_apply, smul_comm])
  norm_map' w := by
    have h2 : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    rw [lp.norm_eq_tsum_rpow h2, lp.norm_eq_tsum_rpow h2]
    congr 1
    change ∑' x, ‖twistedTranslateFun τ p w x‖ ^ (2 : ℝ≥0∞).toReal = _
    simp only [norm_twistedTranslateFun τ hp]
    exact (Equiv.addRight τ).tsum_eq fun x => ‖w x‖ ^ (2 : ℝ≥0∞).toReal
theorem twistedTranslate_surjective (τ : FullSpace.Vertex L 0 0) (p : FullSpace.Vertex L 0 0 → ℂ)
    (hp : ∀ x, ‖p x‖ = 1) : Function.Surjective (twistedTranslate τ p hp) := by
  have hq : ∀ x, ‖(p (x - τ))⁻¹‖ = 1 := fun x => by simp [hp]
  intro w
  refine ⟨twistedTranslate (-τ) (fun x => (p (x - τ))⁻¹) hq w, ?_⟩
  refine lp.ext (funext fun x => ?_)
  have hne : p x ≠ 0 := fun h => by simpa [h] using hp x
  change p x • ((p (x + τ - τ))⁻¹ • w (x + τ + -τ)) = w x
  rw [add_sub_cancel_right, add_neg_cancel_right, smul_smul, mul_inv_cancel₀ hne, one_smul]
def twistedTranslateEquiv (τ : FullSpace.Vertex L 0 0) (p : FullSpace.Vertex L 0 0 → ℂ)
    (hp : ∀ x, ‖p x‖ = 1) : ScalarL2 L ≃ₗᵢ[ℂ] ScalarL2 L :=
  LinearIsometryEquiv.ofSurjective (twistedTranslate τ p hp) (twistedTranslate_surjective τ p hp)
def halfFluxAngle (L : ℕ) (φ : ℝ) : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ :=
  fun b => 1 / 2 * φ * FullSpace.linearAbelianAngle b
def magneticTranslation (L : ℕ) (φ : ℝ) (μ : Fin 4) : ScalarL2 L ≃ₗᵢ[ℂ] ScalarL2 L :=
  twistedTranslateEquiv (InfiniteLattice.axisStep _ μ)
    (fun x => Complex.exp (2 * Complex.I * (halfFluxAngle L φ (FullSpace.forwardEdge x μ) : ℂ)))
    (fun x => by
      have e : 2 * Complex.I * (halfFluxAngle L φ (FullSpace.forwardEdge x μ) : ℂ) =
          ((2 * halfFluxAngle L φ (FullSpace.forwardEdge x μ) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [e, Complex.norm_exp_ofReal_mul_I])
theorem magneticTranslation_apply (φ : ℝ) (μ : Fin 4) (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) :
    magneticTranslation L φ μ w x 0 =
      FullSpace.chargedShift (halfFluxAngle L φ) μ (fun y => w y 0) x := rfl
def magneticTranslationProd (L : ℕ) (φ : ℝ) (n : Fin 4 → ℤ) : ScalarL2 L ≃ₗᵢ[ℂ] ScalarL2 L :=
  magneticTranslation L φ 0 ^ n 0 * magneticTranslation L φ 1 ^ n 1 *
    magneticTranslation L φ 2 ^ n 2 * magneticTranslation L φ 3 ^ n 3
def magneticWeyl (L : ℕ) (φ : ℝ) (n : Fin 4 → ℤ) : ScalarL2 L →ₗ[ℂ] ScalarL2 L :=
  Complex.exp (-Complex.I * (φ : ℂ) * (n 0 : ℂ) * (n 1 : ℂ) / 2) •
    ((magneticTranslationProd L φ n).toLinearEquiv : ScalarL2 L →ₗ[ℂ] ScalarL2 L)
theorem magneticWeyl_isUnitary (φ : ℝ) (n : Fin 4 → ℤ) :
    IsUnitaryOp (magneticWeyl L φ n) := by
  have hc : ‖Complex.exp (-Complex.I * (φ : ℂ) * (n 0 : ℂ) * (n 1 : ℂ) / 2)‖ = 1 := by
    have e : -Complex.I * (φ : ℂ) * (n 0 : ℂ) * (n 1 : ℂ) / 2 =
        ((-(φ * n 0 * n 1 / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e, Complex.norm_exp_ofReal_mul_I]
  have hne : Complex.exp (-Complex.I * (φ : ℂ) * (n 0 : ℂ) * (n 1 : ℂ) / 2) ≠ 0 :=
    Complex.exp_ne_zero _
  refine ⟨⟨fun w w' h => ?_, fun w => ?_⟩, fun w => ?_⟩
  · simp only [magneticWeyl, LinearMap.smul_apply] at h
    exact (magneticTranslationProd L φ n).injective (smul_right_injective _ hne h)
  · obtain ⟨v, hv⟩ := (magneticTranslationProd L φ n).surjective
      ((Complex.exp (-Complex.I * (φ : ℂ) * (n 0 : ℂ) * (n 1 : ℂ) / 2))⁻¹ • w)
    refine ⟨v, ?_⟩
    simp only [magneticWeyl, LinearMap.smul_apply]
    change _ • (magneticTranslationProd L φ n) v = w
    rw [hv, smul_smul, mul_inv_cancel₀ hne, one_smul]
  · simp only [magneticWeyl, LinearMap.smul_apply]
    change ‖_ • (magneticTranslationProd L φ n) w‖ = ‖w‖
    rw [norm_smul, hc, one_mul, LinearIsometryEquiv.norm_map]
end Shifts
def symplecticForm (n n' : Fin 4 → ℤ) : ℤ := n 0 * n' 1 - n 1 * n' 0
section Symbols
open InfiniteLattice (AmbientSpace)
variable {N' N'' N''' : ℕ}
def intDot (n : Fin 4 → ℤ) (q : AmbientSpace) : ℂ := bilinDot (toComplexVec (castVec n)) (toComplexVec q)
def fourierChar (n : Fin 4 → ℤ) (q : AmbientSpace) : ℂ := Complex.exp (Complex.I * intDot n q)
def HasFourierExpansion (c : (Fin 4 → ℤ) → Matrix (Fin N') (Fin N'') ℂ)
    (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) : Prop :=
  ∀ q, HasSum (fun n => fourierChar n q • c n) (a q)
def HasAbsSummableFourier [NeZero N'] [NeZero N''] (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) :
    Prop :=
  ∃ c, HasFourierExpansion c a ∧ Summable fun n => Matrices.RectangularMatrix.opNormValue (c n)
def IsWeylSymbol [NeZero N'] [NeZero N''] (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) : Prop :=
  ∃ c, HasFourierExpansion c a ∧ ∀ j : ℕ, j ≤ 3 → Summable fun n =>
    Matrices.RectangularMatrix.opNormValue (c n) * (1 + TorusMetric.euclidNormVec (castVec n)) ^ j
def fourierCoeff (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) (n : Fin 4 → ℤ) :
    Matrix (Fin N') (Fin N'') ℂ :=
  Matrix.of fun i k => torusAverage fun q => a q i k * Complex.exp (-(Complex.I * intDot n q))
def weightedCoeffNorm [NeZero N'] [NeZero N''] (j : ℕ) (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) : ℝ :=
  ∑' n, Matrices.RectangularMatrix.opNormValue (fourierCoeff a n) *
    (1 + TorusMetric.euclidNormVec (castVec n)) ^ j
def weylQuant (L : ℕ) (φ : ℝ) (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) :
    BddOpBetween (VectorL2 L N'') (VectorL2 L N') :=
  tsumOp (fourierCoeff a) (magneticWeyl L φ)
def moyalCoeff (φ : ℝ) (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
    (a' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ) (n : Fin 4 → ℤ) :
    Matrix (Fin N') (Fin N''') ℂ :=
  ∑' p : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = n},
    Complex.exp (Complex.I / 2 * (φ : ℂ) * (symplecticForm p.1.1 p.1.2 : ℂ)) •
      (fourierCoeff a p.1.1 * fourierCoeff a' p.1.2)
def moyalProduct (φ : ℝ) (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
    (a' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ) (q : AmbientSpace) : Matrix (Fin N') (Fin N''') ℂ :=
  ∑' n, fourierChar n q • moyalCoeff φ a a' n
def coordDeriv (μ : Fin 4) (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) (q : AmbientSpace) :
    Matrix (Fin N') (Fin N'') ℂ :=
  Matrix.of fun i k => deriv (fun t : ℝ => a (Function.update q μ t) i k) (q μ)
def poissonBracket (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
    (a' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ) (q : AmbientSpace) : Matrix (Fin N') (Fin N''') ℂ :=
  coordDeriv 0 a q * coordDeriv 1 a' q -
    coordDeriv 1 a q * coordDeriv 0 a' q
def secondPoissonBracket (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
    (a' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ) (q : AmbientSpace) : Matrix (Fin N') (Fin N''') ℂ :=
  coordDeriv 0 (coordDeriv 0 a) q * coordDeriv 1 (coordDeriv 1 a') q -
    (2 : ℂ) •
      (coordDeriv 0 (coordDeriv 1 a) q *
        coordDeriv 0 (coordDeriv 1 a') q) +
    coordDeriv 1 (coordDeriv 1 a) q * coordDeriv 0 (coordDeriv 0 a') q
def pointwiseAdjoint (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) (q : AmbientSpace) :
    Matrix (Fin N'') (Fin N') ℂ :=
  (a q).conjTranspose
end Symbols
section Origin
variable {L N' N'' : ℕ}
open Classical in
def indicatorAtZero (L : ℕ) (x : FullSpace.Vertex L 0 0) : ℂ := if x = 0 then 1 else 0
open Classical in
def vectorAtZero (L : ℕ) (v : EuclideanSpace ℂ (Fin N')) : VectorL2 L N' :=
  lp.single 2 0 v
theorem vectorAtZero_apply (v : EuclideanSpace ℂ (Fin N')) (x : FullSpace.Vertex L 0 0) :
    vectorAtZero L v x = indicatorAtZero L x • v := by
  classical
  by_cases h : x = 0
  · subst h; simp [vectorAtZero, indicatorAtZero, lp.single_apply]
  · simp [vectorAtZero, indicatorAtZero, lp.single_apply, h]
def matrixAtZero (T : BddOpBetween (VectorL2 L N'') (VectorL2 L N')) :
    Matrix (Fin N') (Fin N'') ℂ :=
  Matrix.of fun i k => T (vectorAtZero L (EuclideanSpace.single k 1)) 0 i
end Origin
end YangMills.Construction.Tower.MagneticWeyl
end
