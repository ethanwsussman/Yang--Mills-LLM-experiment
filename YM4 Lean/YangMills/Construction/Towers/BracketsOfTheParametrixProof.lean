import YangMills.Construction.Towers.BracketsOfTheParametrix
import YangMills.Construction.Towers.SumsAndProductsOfSymbols
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (toComplexVec)
noncomputable section
namespace YangMills.Construction.Tower.MagneticWeyl
open FluxExpansion
private theorem baseSymbol_eq_ofReal (x : AmbientSpace) :
    baseSymbol x = ((∑ a, (2 - 2 * Real.cos (x a)) : ℝ) : ℂ) := by
  simp [baseSymbol, Massive.latticeSymbol, Massive.axisSymbol, toComplexVec]
private theorem baseSymbol_add_ne_zero {m : ℝ} (hm : 0 < m) (x : AmbientSpace) :
    baseSymbol x + (m : ℂ) ≠ 0 := by
  have hnn : 0 ≤ ∑ a, (2 - 2 * Real.cos (x a)) :=
    Finset.sum_nonneg fun a _ => by linarith [Real.cos_le_one (x a)]
  have hpos : (∑ a, (2 - 2 * Real.cos (x a))) + m ≠ 0 := by positivity
  rw [baseSymbol_eq_ofReal]
  exact_mod_cast hpos
private theorem hasDerivAt_baseSymbol_update (a : Fin 4) (x : AmbientSpace) :
    HasDerivAt (fun t : ℝ => baseSymbol (Function.update x a t)) (baseSymbolDeriv a x) (x a) := by
  have each : ∀ b : Fin 4, HasDerivAt
      (fun t : ℝ => Massive.axisSymbol b (toComplexVec (Function.update x a t)))
      (if b = a then baseSymbolDeriv a x else 0) (x a) := by
    intro b
    by_cases hba : b = a
    · subst hba
      have hcos : HasDerivAt (fun t : ℝ => Complex.cos (t : ℂ)) (-Complex.sin (x b : ℂ)) (x b) :=
        (Complex.hasDerivAt_cos (x b : ℂ)).comp_ofReal
      have hlin := (hcos.const_mul (2 : ℂ)).const_sub (2 : ℂ)
      have hfun : (fun t : ℝ =>
          Massive.axisSymbol b (toComplexVec (Function.update x b t))) =
          fun t : ℝ => 2 - 2 * Complex.cos (t : ℂ) := by
        funext t
        simp [Massive.axisSymbol, toComplexVec]
      rw [if_pos rfl, hfun]
      exact hlin.congr_deriv (by simp [baseSymbolDeriv])
    · have hconst : (fun t : ℝ =>
          Massive.axisSymbol b (toComplexVec (Function.update x a t))) =
          fun _ => Massive.axisSymbol b (toComplexVec x) := by
        funext t
        simp [Massive.axisSymbol, toComplexVec, Function.update_of_ne hba]
      rw [hconst, if_neg hba]
      exact hasDerivAt_const _ _
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun b _ => each b
  simpa [baseSymbol, Massive.latticeSymbol] using hsum
abbrev _root_.YangMills.SharedProofs.p30430 := @hasDerivAt_baseSymbol_update
private theorem hasDerivAt_baseSymbolDeriv_update (a : Fin 4) (x : AmbientSpace) :
    HasDerivAt (fun t : ℝ => baseSymbolDeriv a (Function.update x a t))
      (baseSymbolSecondDeriv a x) (x a) := by
  have hsin : HasDerivAt (fun t : ℝ => Complex.sin (t : ℂ)) (Complex.cos (x a : ℂ)) (x a) :=
    (Complex.hasDerivAt_sin (x a : ℂ)).comp_ofReal
  have hfun : (fun t : ℝ => baseSymbolDeriv a (Function.update x a t)) =
      fun t : ℝ => 2 * Complex.sin (t : ℂ) := by
    funext t
    simp [baseSymbolDeriv]
  rw [hfun]
  exact (hsin.const_mul (2 : ℂ)).congr_deriv (by simp [baseSymbolSecondDeriv])
private theorem hasDerivAt_baseSymbolDeriv_update_of_ne {a b : Fin 4} (hba : b ≠ a)
    (x : AmbientSpace) :
    HasDerivAt (fun t : ℝ => baseSymbolDeriv b (Function.update x a t)) 0 (x a) := by
  have hconst : (fun t : ℝ => baseSymbolDeriv b (Function.update x a t)) =
      fun _ => baseSymbolDeriv b x := by
    funext t
    simp [baseSymbolDeriv, Function.update_of_ne hba]
  rw [hconst]
  exact hasDerivAt_const _ _
private theorem hasDerivAt_shiftedInverse_update {m : ℝ} (hm : 0 < m) (a : Fin 4)
    (x : AmbientSpace) :
    HasDerivAt (fun t : ℝ => shiftedInverse m (Function.update x a t))
      (-(shiftedInverse m x ^ 2 * baseSymbolDeriv a x)) (x a) := by
  have hinv : HasDerivAt (fun t : ℝ => shiftedInverse m (Function.update x a t)) _ (x a) :=
    ((hasDerivAt_baseSymbol_update a x).add_const (m : ℂ)).fun_inv
      (by simpa using baseSymbol_add_ne_zero hm x)
  refine hinv.congr_deriv ?_
  simp only [Function.update_eq_self, shiftedInverse]
  rw [inv_pow, div_eq_mul_inv]
  ring
private theorem hasDerivAt_neg_shiftedInverse_sq_update {m : ℝ} (hm : 0 < m) (a : Fin 4)
    (x : AmbientSpace) :
    HasDerivAt (fun t : ℝ => -(shiftedInverse m (Function.update x a t) ^ 2))
      (2 * shiftedInverse m x ^ 3 * baseSymbolDeriv a x) (x a) := by
  have hv := hasDerivAt_shiftedInverse_update hm a x
  have hfun : (fun t : ℝ => -(shiftedInverse m (Function.update x a t) ^ 2)) =
      fun t : ℝ => -(shiftedInverse m (Function.update x a t) *
        shiftedInverse m (Function.update x a t)) := by
    funext t
    rw [pow_two]
  rw [hfun]
  refine (hv.fun_mul hv).fun_neg.congr_deriv ?_
  rw [Function.update_eq_self]
  ring
private theorem hasDerivAt_shiftedInverse_deriv_update {m : ℝ} (hm : 0 < m) (a : Fin 4)
    (x : AmbientSpace) :
    HasDerivAt (fun t : ℝ => -(shiftedInverse m (Function.update x a t) ^ 2 *
        baseSymbolDeriv a (Function.update x a t)))
      (shiftedInverseSecondDeriv m a x) (x a) := by
  have hfun : (fun t : ℝ => -(shiftedInverse m (Function.update x a t) ^ 2 *
      baseSymbolDeriv a (Function.update x a t))) =
      fun t : ℝ => -(shiftedInverse m (Function.update x a t) ^ 2) *
        baseSymbolDeriv a (Function.update x a t) := by
    funext t
    ring
  rw [hfun]
  refine ((hasDerivAt_neg_shiftedInverse_sq_update hm a x).fun_mul
    (hasDerivAt_baseSymbolDeriv_update a x)).congr_deriv ?_
  rw [Function.update_eq_self, shiftedInverseSecondDeriv]
  ring
variable {n : ℕ}
private theorem coordDeriv_smul_one {g : AmbientSpace → ℂ} {c : ℂ} {a : Fin 4} {x : AmbientSpace}
    (hg : HasDerivAt (fun t : ℝ => g (Function.update x a t)) c (x a)) :
    coordDeriv a (fun y => g y • (1 : Matrix (Fin n) (Fin n) ℂ)) x =
      c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simpa [coordDeriv] using hg.deriv
  · simp [coordDeriv, Matrix.one_apply, hij]
private theorem coordDeriv_smul {g : AmbientSpace → ℂ} {c : ℂ} {a : Fin 4} {x : AmbientSpace}
    {M : AmbientSpace → Matrix (Fin n) (Fin n) ℂ}
    (hg : HasDerivAt (fun t : ℝ => g (Function.update x a t)) c (x a))
    (hM : ∀ i j, HasDerivAt (fun t : ℝ => M (Function.update x a t) i j)
      (coordDeriv a M x i j) (x a)) :
    coordDeriv a (fun y => g y • M y) x = c • M x + g x • coordDeriv a M x := by
  ext i j
  have hprod := (hg.fun_mul (hM i j)).deriv
  simpa [coordDeriv] using hprod
private theorem coordDeriv_termZero {m : ℝ} (hm : 0 < m) (a : Fin 4) :
    coordDeriv a (termZero n m) =
      fun y => (-(shiftedInverse m y ^ 2 * baseSymbolDeriv a y)) •
        (1 : Matrix (Fin n) (Fin n) ℂ) :=
  funext fun y => coordDeriv_smul_one (g := shiftedInverse m)
    (hasDerivAt_shiftedInverse_update hm a y)
private theorem coordDeriv_baseSymbolMatrix (a : Fin 4) :
    coordDeriv a (baseSymbolMatrix n) =
      fun y => baseSymbolDeriv a y • (1 : Matrix (Fin n) (Fin n) ℂ) :=
  funext fun y => coordDeriv_smul_one (g := baseSymbol) (hasDerivAt_baseSymbol_update a y)
private theorem coordDeriv_coordDeriv_termZero {m : ℝ} (hm : 0 < m) (a : Fin 4)
    (x : AmbientSpace) :
    coordDeriv a (coordDeriv a (termZero n m)) x =
      shiftedInverseSecondDeriv m a x • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [coordDeriv_termZero hm]
  exact coordDeriv_smul_one (g := fun y => -(shiftedInverse m y ^ 2 * baseSymbolDeriv a y))
    (hasDerivAt_shiftedInverse_deriv_update hm a x)
private theorem coordDeriv_coordDeriv_baseSymbolMatrix (a : Fin 4) (x : AmbientSpace) :
    coordDeriv a (coordDeriv a (baseSymbolMatrix n)) x =
      baseSymbolSecondDeriv a x • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [coordDeriv_baseSymbolMatrix]
  exact coordDeriv_smul_one (g := baseSymbolDeriv a) (hasDerivAt_baseSymbolDeriv_update a x)
private theorem coordDeriv_coordDeriv_baseSymbolMatrix_mixed (x : AmbientSpace) :
    coordDeriv 0 (coordDeriv 1 (baseSymbolMatrix n)) x = 0 := by
  rw [coordDeriv_baseSymbolMatrix]
  rw [coordDeriv_smul_one (g := baseSymbolDeriv 1)
    (hasDerivAt_baseSymbolDeriv_update_of_ne (a := 0) (b := 1) (by decide) x)]
  simp
private theorem coordDeriv_termOne {m : ℝ} (hm : 0 < m) {M : AmbientSpace → Matrix (Fin n) (Fin n) ℂ}
    (a : Fin 4) (x : AmbientSpace)
    (hM : ∀ i j, HasDerivAt (fun t : ℝ => M (Function.update x a t) i j)
      (coordDeriv a M x i j) (x a)) :
    coordDeriv a (termOne m M) x =
      (2 * shiftedInverse m x ^ 3 * baseSymbolDeriv a x) • M x +
        (-(shiftedInverse m x ^ 2)) • coordDeriv a M x :=
  coordDeriv_smul (g := fun y => -(shiftedInverse m y ^ 2))
    (hasDerivAt_neg_shiftedInverse_sq_update hm a x) hM
theorem fluxExpansionBrackets_of_symbolAlgebra (hAlg : SymbolAlgebra.Claim) :
    FluxExpansionBrackets := by
  intro n _ m hm M hM x
  have hpart : ∀ (a : Fin 4) (i j : Fin n), HasDerivAt
      (fun t : ℝ => M (Function.update x a t) i j) (coordDeriv a M x i j) (x a) :=
    fun a i j => ((hAlg n n n).2.1.2.2.2 M hM).2.2.2.2 a x i j
  refine ⟨?_, ?_, ?_⟩
  · simp only [poissonBracket, coordDeriv_termZero hm, coordDeriv_baseSymbolMatrix,
      smul_mul_assoc, mul_smul_comm, one_mul, smul_smul]
    rw [← sub_smul]
    have hzero : -(shiftedInverse m x ^ 2 * baseSymbolDeriv 0 x) * baseSymbolDeriv 1 x -
        -(shiftedInverse m x ^ 2 * baseSymbolDeriv 1 x) * baseSymbolDeriv 0 x = 0 := by ring
    simp only [mul_comm (baseSymbolDeriv 1 x), mul_comm (baseSymbolDeriv 0 x)] at *
    rw [hzero, zero_smul]
  · simp only [poissonBracket, coordDeriv_termOne hm _ x (hpart _), coordDeriv_termZero hm,
      coordDeriv_baseSymbolMatrix, smul_mul_assoc, mul_smul_comm, mul_one, one_mul]
    module
  · simp only [secondPoissonBracket, coordDeriv_coordDeriv_termZero hm,
      coordDeriv_coordDeriv_baseSymbolMatrix, coordDeriv_coordDeriv_baseSymbolMatrix_mixed,
      mul_zero, smul_zero, sub_zero, mul_smul_comm, add_smul, smul_smul, mul_one]
    simp only [mul_comm (baseSymbolSecondDeriv 1 x), mul_comm (baseSymbolSecondDeriv 0 x)]
end YangMills.Construction.Tower.MagneticWeyl
end
