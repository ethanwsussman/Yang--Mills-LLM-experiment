import YangMills.Construction.Towers.AsymptoticsOfTheMassiveCoefficientProof
import YangMills.Construction.Towers.BracketsOfTheParametrixProof
import YangMills.Construction.Towers.ChargedSymbolAtFluxZeroProof
import YangMills.Construction.Towers.CoefficientsOfASymbol
import YangMills.Construction.Towers.FirstCoefficientOnTheGaugeColumn
import YangMills.Construction.Towers.MoyalExpansionOfAStarProduct
import YangMills.Construction.Towers.SymbolsOfTheParametrix
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (toComplexVec castVec bilinDot)
namespace Tower.ConstantFieldSymbols
open MagneticWeyl MagneticWeyl.SymbolAlgebra MagneticWeyl.FluxExpansion
namespace GaugeColumnFirstCoeff
section Values
variable {N' N'' N''' : ℕ} [NeZero N'] [NeZero N''] [NeZero N''']
theorem entry_norm_le_opNormValue (X : Matrix (Fin N') (Fin N'') ℂ) (i : Fin N') (k : Fin N'') :
    ‖X i k‖ ≤ Matrices.RectangularMatrix.opNormValue X := by apply _root_.YangMills.Construction.Tower.Massive.CoefficientAsymptoticsProof.norm_apply_le_opNormValue <;> assumption
theorem norm_fourierChar (n : Fin 4 → ℤ) (q : AmbientSpace) :
    ‖MagneticWeyl.fourierChar n q‖ = 1 := by apply _root_.YangMills.Construction.Tower.Massive.CoefficientAsymptoticsProof.norm_fourierChar <;> assumption
theorem entry_norm_le_coeffNorm (hC : FourierCoeffsOfSymbol)
    {a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ} (ha : HasAbsSummableFourier a)
    (q : AmbientSpace) (i : Fin N') (k : Fin N'') : ‖a q i k‖ ≤ weightedCoeffNorm 0 a := by
  obtain ⟨hs, hsum, -⟩ := (hC N' N'' a).1 ha
  have h1 : HasSum (fun n => (MagneticWeyl.fourierChar n q • fourierCoeff a n) i k) (a q i k) :=
    (hs q).map (Matrix.entryAddMonoidHom ℂ i k) (continuous_id.matrix_elem i k)
  have hb : ∀ n, ‖(MagneticWeyl.fourierChar n q • fourierCoeff a n) i k‖ ≤
      Matrices.RectangularMatrix.opNormValue (fourierCoeff a n) := fun n => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_fourierChar, one_mul]
    exact entry_norm_le_opNormValue _ i k
  have h2 : ‖a q i k‖ ≤ ∑' n, Matrices.RectangularMatrix.opNormValue (fourierCoeff a n) := by
    rw [← h1.tsum_eq]
    exact tsum_of_norm_bounded hsum.hasSum hb
  simpa [weightedCoeffNorm] using h2
variable (hC : FourierCoeffsOfSymbol) (hS : SymbolAlgebra.Claim)
include hC hS
theorem mul_entry_norm_le {a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    {a' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ} (ha : IsWeylSymbol a)
    (ha' : IsWeylSymbol a') (q : AmbientSpace) (i : Fin N') (k : Fin N''') :
    ‖(a q * a' q) i k‖ ≤ weightedCoeffNorm 3 a * weightedCoeffNorm 3 a' := by
  obtain ⟨hp, hpn, -⟩ := (hS N' N'' N''').2.2.1 a a' ha ha'
  have h1 := entry_norm_le_coeffNorm hC ((hC N' N''' _).2 hp).1 q i k
  have h2 := (((hS N' N''' N''').2.1.2.2.2) _ hp).2.1
  exact h1.trans (h2.trans (hpn 3 le_rfl))
theorem poissonBracket_entry_norm_le {a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    {a' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ} (ha : IsWeylSymbol a)
    (ha' : IsWeylSymbol a') (q : AmbientSpace) (i : Fin N') (k : Fin N''') :
    ‖poissonBracket a a' q i k‖ ≤ 2 * weightedCoeffNorm 3 a * weightedCoeffNorm 3 a' := by
  obtain ⟨-, -, hb, hbn, -⟩ := (hS N' N'' N''').2.2.1 a a' ha ha'
  exact (entry_norm_le_coeffNorm hC hb q i k).trans hbn
theorem moyal_firstOrder_entry_norm_le (hM : MoyalRemainderBound)
    {a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    {a' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ} (ha : IsWeylSymbol a)
    (ha' : IsWeylSymbol a') {φ : ℝ} (hφ : |φ| ≤ 1) (q : AmbientSpace) (i : Fin N') (k : Fin N''') :
    ‖(moyalProduct φ a a' q - a q * a' q + (Complex.I / 2 * (φ : ℂ)) • poissonBracket a a' q) i k‖ ≤
      φ ^ 2 * (weightedCoeffNorm 3 a * weightedCoeffNorm 3 a') := by
  obtain ⟨-, -, -, -, hs, hsn⟩ := (hS N' N'' N''').2.2.1 a a' ha ha'
  obtain ⟨r, hrq⟩ : ∃ r : AmbientSpace → Matrix (Fin N') (Fin N''') ℂ, r = fun q =>
      moyalProduct φ a a' q - a q * a' q + (Complex.I / 2 * (φ : ℂ)) • poissonBracket a a' q +
        ((1 / 8 : ℂ) * (φ : ℂ) ^ 2) • secondPoissonBracket a a' q := ⟨_, rfl⟩
  obtain ⟨hr, hrn⟩ := hM φ N' N'' N''' a a' ha ha' r fun q => by rw [hrq]
  have h0 : 0 ≤ weightedCoeffNorm 3 a * weightedCoeffNorm 3 a' :=
    mul_nonneg (((hS N' N'' N''').2.1.2.2.2 a ha).1 3 le_rfl)
      (((hS N'' N''' N').2.1.2.2.2 a' ha').1 3 le_rfl)
  have e : (moyalProduct φ a a' q - a q * a' q +
      (Complex.I / 2 * (φ : ℂ)) • poissonBracket a a' q) i k =
      r q i k - (1 / 8 * (φ : ℂ) ^ 2) * secondPoissonBracket a a' q i k := by
    rw [hrq]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have h1 := (entry_norm_le_coeffNorm hC hr q i k).trans hrn
  have h2 := (entry_norm_le_coeffNorm hC hs q i k).trans hsn
  have hc : ‖(1 / 8 * (φ : ℂ) ^ 2)‖ = 1 / 8 * φ ^ 2 := by
    simp [norm_pow, sq_abs]
  have h3 : ‖(1 / 8 * (φ : ℂ) ^ 2) * secondPoissonBracket a a' q i k‖ ≤
      1 / 8 * φ ^ 2 * (4 * (weightedCoeffNorm 3 a * weightedCoeffNorm 3 a')) := by
    rw [norm_mul, hc]
    have : ‖secondPoissonBracket a a' q i k‖ ≤
        4 * (weightedCoeffNorm 3 a * weightedCoeffNorm 3 a') := by
      linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h4 : 1 / 48 * |φ| ^ 3 * weightedCoeffNorm 3 a * weightedCoeffNorm 3 a' ≤
      1 / 48 * φ ^ 2 * (weightedCoeffNorm 3 a * weightedCoeffNorm 3 a') := by
    have : |φ| ^ 3 ≤ φ ^ 2 := by
      rw [← sq_abs φ]
      nlinarith [abs_nonneg φ, sq_nonneg |φ|]
    have h5 := mul_le_mul_of_nonneg_right this h0
    nlinarith
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h6 : 0 ≤ φ ^ 2 * (weightedCoeffNorm 3 a * weightedCoeffNorm 3 a') :=
    mul_nonneg (sq_nonneg _) h0
  nlinarith
omit hC in
theorem coordDeriv_add {a b : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ} (ha : IsWeylSymbol a)
    (hb : IsWeylSymbol b) (μ : Fin 4) (q : AmbientSpace) :
    coordDeriv μ (fun q => a q + b q) q = coordDeriv μ a q + coordDeriv μ b q := by
  ext i k
  have h1 := ((hS N' N'' N').2.1.2.2.2 a ha).2.2.2.2 μ q i k
  have h2 := ((hS N' N'' N').2.1.2.2.2 b hb).2.2.2.2 μ q i k
  exact (h1.add h2).deriv
omit hC [NeZero N'''] in
theorem poissonBracket_add {a b : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    (ha : IsWeylSymbol a) (hb : IsWeylSymbol b) (a' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ)
    (q : AmbientSpace) :
    poissonBracket (fun q => a q + b q) a' q = poissonBracket a a' q + poissonBracket b a' q := by
  simp only [poissonBracket, coordDeriv_add hS ha hb, Matrix.add_mul]
  abel
end Values
section TheColumn
theorem hasDerivAt_baseSymbol_update (μ : Fin 4) (q : AmbientSpace) :
    HasDerivAt (fun t : ℝ => baseSymbol (Function.update q μ t)) (baseSymbolDeriv μ q) (q μ) := by apply _root_.YangMills.SharedProofs.p30430 <;> assumption
theorem coordDeriv_baseSymbolMatrix (N' : ℕ) (μ : Fin 4) (q : AmbientSpace) :
    coordDeriv μ (baseSymbolMatrix N') q =
      baseSymbolDeriv μ q • (1 : Matrix (Fin N') (Fin N') ℂ) := by
  ext i k
  have h := (hasDerivAt_baseSymbol_update μ q).mul_const ((1 : Matrix (Fin N') (Fin N') ℂ) i k)
  exact h.deriv
def expDerivColumn (μ : Fin 4) (q : AmbientSpace) : Matrix (Fin 4) (Fin 1) ℂ :=
  Matrix.of fun i _ => if i = μ then Complex.I * Complex.exp (Complex.I * (q μ : ℂ)) else 0
theorem coordDeriv_gaugeSymbolColumn (μ : Fin 4) (q : AmbientSpace) :
    coordDeriv μ gaugeSymbolColumn q = expDerivColumn μ q := by
  ext i k
  by_cases hi : i = μ
  · subst hi
    have e : (fun t : ℝ => gaugeSymbolColumn (Function.update q i t) i k) =
        fun t : ℝ => Complex.exp (Complex.I * (t : ℂ)) - 1 := by
      funext t
      simp [gaugeSymbolColumn]
    have h : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ)) - 1)
        (Complex.I * Complex.exp (Complex.I * (q i : ℂ))) (q i) := by
      have h1 : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * z) - 1)
          (Complex.exp (Complex.I * (q i : ℂ)) * (Complex.I * 1)) (q i : ℂ) :=
        (((hasDerivAt_id (q i : ℂ)).const_mul Complex.I).cexp).sub_const 1
      refine h1.comp_ofReal.congr_deriv ?_
      ring
    simp only [coordDeriv, Matrix.of_apply, expDerivColumn, if_true]
    rw [e]
    exact h.deriv
  · have e : (fun t : ℝ => gaugeSymbolColumn (Function.update q μ t) i k) =
        fun _ : ℝ => gaugeSymbolColumn q i k := by
      funext t
      simp [gaugeSymbolColumn, Function.update_of_ne hi]
    simp only [coordDeriv, Matrix.of_apply, expDerivColumn, if_neg hi]
    rw [e]
    simp
def charSum {ι : Type} [Fintype ι] (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin 4) (Fin 1) ℂ)
    (q : AmbientSpace) : Matrix (Fin 4) (Fin 1) ℂ :=
  ∑ i, MagneticWeyl.fourierChar (n i) q • c i
def charSumCoeff {ι : Type} [Fintype ι] (n : ι → Fin 4 → ℤ) (c : ι → Matrix (Fin 4) (Fin 1) ℂ)
    (m : Fin 4 → ℤ) : Matrix (Fin 4) (Fin 1) ℂ :=
  ∑ i, if m = n i then c i else 0
theorem isWeylSymbol_charSum {ι : Type} [Fintype ι] (n : ι → Fin 4 → ℤ)
    (c : ι → Matrix (Fin 4) (Fin 1) ℂ) : IsWeylSymbol (charSum n c) := by
  refine ⟨charSumCoeff n c, fun q => ?_, fun j _ => ?_⟩
  · have h : ∀ i ∈ (Finset.univ : Finset ι),
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
  · refine summable_of_hasFiniteSupport ((Set.finite_range n).subset fun m hm => ?_)
    by_contra hr
    apply hm
    have : charSumCoeff n c m = 0 := by
      refine Finset.sum_eq_zero fun i _ => if_neg fun e => hr ⟨i, e.symm⟩
    simp [this, Matrices.RectangularMatrix.opNormValue, OneLoopNotation.opNormOf]
def basisIndex (μ : Fin 4) : Fin 4 → ℤ := Pi.single μ 1
theorem fourierChar_basisIndex (μ : Fin 4) (q : AmbientSpace) :
    MagneticWeyl.fourierChar (basisIndex μ) q = Complex.exp (Complex.I * (q μ : ℂ)) := by
  fin_cases μ <;> simp [MagneticWeyl.fourierChar, MagneticWeyl.intDot, bilinDot, toComplexVec,
    castVec, basisIndex, Fin.sum_univ_four]
theorem fourierChar_zero (q : AmbientSpace) : MagneticWeyl.fourierChar 0 q = 1 := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.FluxZero.fourierChar_zero <;> assumption
def stdColumn (μ : Fin 4) : Matrix (Fin 4) (Fin 1) ℂ := Matrix.of fun i _ => if i = μ then 1 else 0
def gaugeCharIndex (p : Fin 4 × Fin 2) : Fin 4 → ℤ := ![basisIndex p.1, 0] p.2
def gaugeCharCoeff (p : Fin 4 × Fin 2) : Matrix (Fin 4) (Fin 1) ℂ :=
  ![stdColumn p.1, -stdColumn p.1] p.2
theorem gaugeSymbolColumn_eq_charSum : gaugeSymbolColumn = charSum gaugeCharIndex gaugeCharCoeff := by
  funext q
  ext i j
  simp [charSum, Fintype.sum_prod_type, Fin.sum_univ_two, gaugeCharIndex, gaugeCharCoeff,
    fourierChar_basisIndex, fourierChar_zero, stdColumn, gaugeSymbolColumn, Matrix.sum_apply,
    Finset.sum_add_distrib]
  ring
theorem isWeylSymbol_gaugeSymbolColumn : IsWeylSymbol gaugeSymbolColumn := by
  rw [gaugeSymbolColumn_eq_charSum]
  exact isWeylSymbol_charSum _ _
theorem baseSymbolMatrix_mul_gaugeSymbolColumn (q : AmbientSpace) :
    baseSymbolMatrix 4 q * gaugeSymbolColumn q = gaugeSymbolColumn q * scalarMultiplier q := by
  have e : scalarMultiplier q = baseSymbol q • (1 : Matrix (Fin 1) (Fin 1) ℂ) := rfl
  rw [e, baseSymbolMatrix, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
theorem poissonBracket_gaugeSymbolColumn_scalarMultiplier (q : AmbientSpace) :
    poissonBracket gaugeSymbolColumn scalarMultiplier q =
      -poissonBracket (baseSymbolMatrix 4) gaugeSymbolColumn q := by
  have e : scalarMultiplier = baseSymbolMatrix 1 := rfl
  simp only [poissonBracket, e, coordDeriv_baseSymbolMatrix, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  abel
end TheColumn
section FirstOrder
def linearDefect (σ₁ : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ) (q : AmbientSpace) :
    Matrix (Fin 4) (Fin 1) ℂ :=
  σ₁ q * gaugeSymbolColumn q - (Complex.I / 2) • poissonBracket (baseSymbolMatrix 4) gaugeSymbolColumn q +
    (Complex.I / 2) • poissonBracket gaugeSymbolColumn scalarMultiplier q
variable {D C : ℝ} {σ₁ σ₂ : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ}
  {σ σr : ℝ → AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ}
theorem linearDefect_entry_norm_le (hC : FourierCoeffsOfSymbol) (hS : SymbolAlgebra.Claim)
    (hM : MoyalRemainderBound) (hP : ApproxInverseSymbolBounds)
    (hE : ChargedSymbolExpansion D C σ₁ σ₂ σ σr)
    (hrel : ∀ φ : ℝ, |φ| ≤ Real.pi →
      moyalProduct φ (σ φ) gaugeSymbolColumn = moyalProduct φ gaugeSymbolColumn scalarMultiplier) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ φ : ℝ, φ ≠ 0 → |φ| ≤ 1 → ∀ (q : AmbientSpace) (i : Fin 4) (k : Fin 1),
      ‖linearDefect σ₁ q i k‖ ≤ K * |φ| := by
  have hOne := (hS 4 4 1).2.1
  have hs₁ : IsWeylSymbol σ₁ := hE.linear_isFiniteFourierSymbol.1
  have hs₂ : IsWeylSymbol σ₂ := hE.quadratic_isFiniteFourierSymbol.1
  have hP4 : IsWeylSymbol (baseSymbolMatrix 4) := (hP 4).1.1
  have hP1 : IsWeylSymbol scalarMultiplier := (hP 1).1.1
  have hb := isWeylSymbol_gaugeSymbolColumn
  obtain ⟨S₁, hS₁⟩ : ∃ x, x = weightedCoeffNorm 3 σ₁ := ⟨_, rfl⟩
  obtain ⟨S₂, hS₂⟩ : ∃ x, x = weightedCoeffNorm 3 σ₂ := ⟨_, rfl⟩
  obtain ⟨P, hPn⟩ : ∃ x, x = weightedCoeffNorm 3 (baseSymbolMatrix 4) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ x, x = weightedCoeffNorm 3 gaugeSymbolColumn := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ x, x = weightedCoeffNorm 3 scalarMultiplier := ⟨_, rfl⟩
  have p₁ : 0 ≤ S₁ := hS₁ ▸ (hOne.2.2.2 σ₁ hs₁).1 3 le_rfl
  have p₂ : 0 ≤ S₂ := hS₂ ▸ (hOne.2.2.2 σ₂ hs₂).1 3 le_rfl
  have pP : 0 ≤ P := hPn ▸ (hOne.2.2.2 _ hP4).1 3 le_rfl
  have pB : 0 ≤ B := hB ▸ ((hS 4 1 1).2.1.2.2.2 _ hb).1 3 le_rfl
  have pQ : 0 ≤ Q := hQ ▸ ((hS 1 1 1).2.1.2.2.2 _ hP1).1 3 le_rfl
  have pC : 0 ≤ |C| := abs_nonneg C
  refine ⟨(P + S₁ + S₂ + |C|) * B + B * Q + (S₂ + |C|) * B + (S₁ + S₂ + |C|) * B, by positivity,
    fun φ h0 h1 q i k => ?_⟩
  have hπ : |φ| ≤ Real.pi := h1.trans (by linarith [Real.pi_gt_three])
  have pφ : 0 < |φ| := abs_pos.mpr h0
  have hr := hE.error_isWeylSymbol φ hπ
  have hrn := hE.error_norm_le φ hπ
  have hcube : |φ| ^ 3 ≤ φ ^ 2 := by
    rw [← sq_abs φ]
    nlinarith [sq_nonneg |φ|]
  obtain ⟨e, he⟩ : ∃ e : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ,
      e = fun q => (φ : ℂ) ^ 2 • σ₂ q + σr φ q := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ,
      d = fun q => (φ : ℂ) • σ₁ q + e q := ⟨_, rfl⟩
  have m₂ := hOne.2.1 ((φ : ℂ) ^ 2) σ₂ hs₂
  have m₁ := hOne.2.1 (φ : ℂ) σ₁ hs₁
  have se := hOne.1 _ _ m₂.1 hr
  rw [← he] at se
  have sd := hOne.1 _ _ m₁.1 se.1
  rw [← hd] at sd
  have sa := hOne.1 _ _ hP4 sd.1
  have hσ : σ φ = fun q => baseSymbolMatrix 4 q + d q := by
    funext q
    rw [hE.eq_add φ hπ q, hd, he]
    simp only [baseSymbolMatrix, baseSymbol, add_assoc]
  rw [← hσ] at sa
  have hen : weightedCoeffNorm 3 e ≤ φ ^ 2 * (S₂ + |C|) := by
    have h2 := m₂.2.2 3 le_rfl
    have hn : ‖(φ : ℂ) ^ 2‖ = φ ^ 2 := by simp [norm_pow, sq_abs]
    rw [hn, ← hS₂] at h2
    have h3 : C * |φ| ^ 3 ≤ |C| * φ ^ 2 :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hcube pC)
    have h4 := se.2.2 3 le_rfl
    nlinarith
  have hdn : weightedCoeffNorm 3 d ≤ |φ| * (S₁ + S₂ + |C|) := by
    have h2 := m₁.2.2 3 le_rfl
    have hn : ‖(φ : ℂ)‖ = |φ| := by simp
    rw [hn, ← hS₁] at h2
    have h4 := sd.2.2 3 le_rfl
    have h5 : φ ^ 2 ≤ |φ| := by
      rw [← sq_abs φ]
      nlinarith
    have h6 := mul_le_mul_of_nonneg_right h5 (add_nonneg p₂ pC)
    nlinarith
  have han : weightedCoeffNorm 3 (σ φ) ≤ P + S₁ + S₂ + |C| := by
    have h4 := sa.2.2 3 le_rfl
    rw [← hPn] at h4
    have h5 := mul_le_mul_of_nonneg_right h1 (add_nonneg (add_nonneg p₁ p₂) pC)
    nlinarith
  have hc₁ : poissonBracket (σ φ) gaugeSymbolColumn q =
      poissonBracket (baseSymbolMatrix 4) gaugeSymbolColumn q +
        poissonBracket d gaugeSymbolColumn q := by
    rw [hσ]
    exact poissonBracket_add hS hP4 sd.1 _ q
  have hc₂ : σ φ q * gaugeSymbolColumn q = gaugeSymbolColumn q * scalarMultiplier q +
      (φ : ℂ) • (σ₁ q * gaugeSymbolColumn q) + e q * gaugeSymbolColumn q := by
    rw [hσ, hd]
    simp only [Matrix.add_mul, Matrix.smul_mul, baseSymbolMatrix_mul_gaugeSymbolColumn, add_assoc]
  obtain ⟨R₁, hR₁⟩ : ∃ R, R = moyalProduct φ (σ φ) gaugeSymbolColumn q -
      σ φ q * gaugeSymbolColumn q +
      (Complex.I / 2 * (φ : ℂ)) • poissonBracket (σ φ) gaugeSymbolColumn q := ⟨_, rfl⟩
  obtain ⟨R₂, hR₂⟩ : ∃ R, R = moyalProduct φ gaugeSymbolColumn scalarMultiplier q -
      gaugeSymbolColumn q * scalarMultiplier q +
      (Complex.I / 2 * (φ : ℂ)) • poissonBracket gaugeSymbolColumn scalarMultiplier q := ⟨_, rfl⟩
  have hid : (φ : ℂ) • linearDefect σ₁ q =
      R₂ - R₁ - e q * gaugeSymbolColumn q +
        (Complex.I / 2 * (φ : ℂ)) • poissonBracket d gaugeSymbolColumn q := by
    rw [hR₁, hR₂, linearDefect, hrel φ hπ, hc₁, hc₂]
    module
  have b₁ : ‖R₁ i k‖ ≤ φ ^ 2 * (weightedCoeffNorm 3 (σ φ) * B) := by
    rw [hR₁, hB]
    exact moyal_firstOrder_entry_norm_le hC hS hM sa.1 hb h1 q i k
  have b₂ : ‖R₂ i k‖ ≤ φ ^ 2 * (B * Q) := by
    rw [hR₂, hB, hQ]
    exact moyal_firstOrder_entry_norm_le hC hS hM hb hP1 h1 q i k
  have b₃ : ‖(e q * gaugeSymbolColumn q) i k‖ ≤ weightedCoeffNorm 3 e * B := by
    rw [hB]
    exact mul_entry_norm_le hC hS se.1 hb q i k
  have b₄ : ‖poissonBracket d gaugeSymbolColumn q i k‖ ≤ 2 * weightedCoeffNorm 3 d * B := by
    rw [hB]
    exact poissonBracket_entry_norm_le hC hS sd.1 hb q i k
  have hent := congrFun (congrFun hid i) k
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul] at hent
  have hnorm : |φ| * ‖linearDefect σ₁ q i k‖ ≤
      ‖R₂ i k‖ + ‖R₁ i k‖ + ‖(e q * gaugeSymbolColumn q) i k‖ +
        |φ| / 2 * ‖poissonBracket d gaugeSymbolColumn q i k‖ := by
    have e₁ : ‖(φ : ℂ) * linearDefect σ₁ q i k‖ = |φ| * ‖linearDefect σ₁ q i k‖ := by simp
    have e₂ : ‖Complex.I / 2 * (φ : ℂ)‖ = |φ| / 2 := by simp; ring
    rw [← e₁, hent]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (norm_sub_le _ _) le_rfl)) ?_)
    rw [norm_mul, e₂]
  have hq : φ ^ 2 = |φ| * |φ| := by rw [abs_mul_abs_self]; ring
  have c₁ : ‖R₁ i k‖ ≤ |φ| * |φ| * ((P + S₁ + S₂ + |C|) * B) := by
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right han pB) (sq_nonneg φ)
    rw [hq] at b₁ h2
    exact b₁.trans h2
  have c₂ : ‖R₂ i k‖ ≤ |φ| * |φ| * (B * Q) := by
    rw [hq] at b₂
    exact b₂
  have c₃ : ‖(e q * gaugeSymbolColumn q) i k‖ ≤ |φ| * |φ| * ((S₂ + |C|) * B) := by
    have h2 := mul_le_mul_of_nonneg_right hen pB
    rw [hq] at h2
    calc _ ≤ _ := b₃
      _ ≤ _ := h2
      _ = _ := by ring
  have c₄ : |φ| / 2 * ‖poissonBracket d gaugeSymbolColumn q i k‖ ≤
      |φ| * |φ| * ((S₁ + S₂ + |C|) * B) := by
    have h2 : 2 * weightedCoeffNorm 3 d * B ≤ 2 * (|φ| * (S₁ + S₂ + |C|)) * B :=
      mul_le_mul_of_nonneg_right (by linarith) pB
    have h3 := mul_le_mul_of_nonneg_left (b₄.trans h2) (by positivity : 0 ≤ |φ| / 2)
    calc _ ≤ _ := h3
      _ = _ := by ring
  refine le_of_mul_le_mul_left ?_ pφ
  have e₃ : |φ| * (((P + S₁ + S₂ + |C|) * B + B * Q + (S₂ + |C|) * B + (S₁ + S₂ + |C|) * B) * |φ|) =
      |φ| * |φ| * ((P + S₁ + S₂ + |C|) * B) + |φ| * |φ| * (B * Q) +
        |φ| * |φ| * ((S₂ + |C|) * B) + |φ| * |φ| * ((S₁ + S₂ + |C|) * B) := by ring
  rw [e₃]
  linarith
theorem linearDefect_eq_zero (hC : FourierCoeffsOfSymbol)
    (hS : SymbolAlgebra.Claim) (hM : MoyalRemainderBound)
    (hP : ApproxInverseSymbolBounds) (hE : ChargedSymbolExpansion D C σ₁ σ₂ σ σr)
    (hrel : ∀ φ : ℝ, |φ| ≤ Real.pi →
      moyalProduct φ (σ φ) gaugeSymbolColumn = moyalProduct φ gaugeSymbolColumn scalarMultiplier)
    (q : AmbientSpace) :
    linearDefect σ₁ q = 0 := by
  obtain ⟨K, hK, hb⟩ := linearDefect_entry_norm_le hC hS hM hP hE hrel
  ext i k
  by_contra hne
  have hx : 0 < ‖linearDefect σ₁ q i k‖ := norm_pos_iff.mpr hne
  obtain ⟨x, hxd⟩ : ∃ x, x = ‖linearDefect σ₁ q i k‖ := ⟨_, rfl⟩
  rw [← hxd] at hx
  have hm : 0 < min 1 (x / (2 * (K + 1))) := lt_min one_pos (by positivity)
  have h2 := hb (min 1 (x / (2 * (K + 1)))) hm.ne' (by rw [abs_of_pos hm]; exact min_le_left _ _) q i k
  rw [abs_of_pos hm, ← hxd] at h2
  have h3 : K * min 1 (x / (2 * (K + 1))) ≤ K * (x / (2 * (K + 1))) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hK
  have h4 : K * (x / (2 * (K + 1))) < x := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith
end FirstOrder
theorem poissonBracket_baseSymbolMatrix_gaugeSymbolColumn (q : AmbientSpace) :
    poissonBracket (baseSymbolMatrix 4) gaugeSymbolColumn q =
      baseSymbolDeriv 0 q • expDerivColumn 1 q - baseSymbolDeriv 1 q • expDerivColumn 0 q := by
  simp only [poissonBracket, coordDeriv_baseSymbolMatrix, coordDeriv_gaugeSymbolColumn,
    Matrix.smul_mul, Matrix.one_mul]
theorem I_smul_poissonBracket_eq_rotated (q : AmbientSpace) :
    Complex.I • poissonBracket (baseSymbolMatrix 4) gaugeSymbolColumn q =
      rotatedGaugeSymbolColumn q := by
  rw [poissonBracket_baseSymbolMatrix_gaugeSymbolColumn]
  have hI := Complex.I_mul_I
  ext ν k
  fin_cases ν
  · simp [expDerivColumn, rotatedGaugeSymbolColumn, baseSymbolDeriv]
    linear_combination (-(2 * Complex.sin (q 1 : ℂ)) * Complex.exp (Complex.I * (q 0 : ℂ))) * hI
  · simp [expDerivColumn, rotatedGaugeSymbolColumn, baseSymbolDeriv]
    linear_combination (2 * Complex.sin (q 0 : ℂ) * Complex.exp (Complex.I * (q 1 : ℂ))) * hI
  · simp [expDerivColumn, rotatedGaugeSymbolColumn, baseSymbolDeriv]
  · simp [expDerivColumn, rotatedGaugeSymbolColumn, baseSymbolDeriv]
end GaugeColumnFirstCoeff
open GaugeColumnFirstCoeff in
theorem firstCoeffOnGaugeColumn_holds (hG : ChargedSymbolGaugeRelation)
    (hM : MoyalRemainderBound) (hS : SymbolAlgebra.Claim)
    (hC : FourierCoeffsOfSymbol) (hP : ApproxInverseSymbolBounds) :
    FirstCoeffOnGaugeColumn := by
  intro D C σ₁ σ₂ σ σr hE q
  have h0 := linearDefect_eq_zero hC hS hM hP hE (hG D C σ₁ σ₂ σ σr hE) q
  rw [linearDefect, poissonBracket_gaugeSymbolColumn_scalarMultiplier] at h0
  rw [← I_smul_poissonBracket_eq_rotated]
  have e : σ₁ q * gaugeSymbolColumn q = (σ₁ q * gaugeSymbolColumn q - (Complex.I / 2) •
      poissonBracket (baseSymbolMatrix 4) gaugeSymbolColumn q + (Complex.I / 2) •
        -poissonBracket (baseSymbolMatrix 4) gaugeSymbolColumn q) +
      Complex.I • poissonBracket (baseSymbolMatrix 4) gaugeSymbolColumn q := by
    module
  rw [e, h0, zero_add]
end Tower.ConstantFieldSymbols
end YangMills.Construction
end
