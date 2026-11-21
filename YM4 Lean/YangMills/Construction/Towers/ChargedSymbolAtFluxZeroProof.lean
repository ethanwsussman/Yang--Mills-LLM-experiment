import YangMills.Construction.Matrices.SeriesWithSummableMatrixCoefficientsProof
import YangMills.Construction.Towers.ChargedSymbolAtFluxZero
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (toComplexVec castVec bilinDot)
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
open Massive MagneticWeyl
namespace FluxZero
theorem intDot_eq_sum (k : Fin 4 → ℤ) (q : AmbientSpace) :
    MagneticWeyl.intDot k q = ((∑ μ, (k μ : ℝ) * q μ : ℝ) : ℂ) := by
  simp [MagneticWeyl.intDot, bilinDot, toComplexVec, castVec]
theorem fourierChar_zero (q : AmbientSpace) : fourierChar 0 q = 1 := by
  simp [fourierChar, intDot_eq_sum]
theorem fourierChar_add (k l : Fin 4 → ℤ) (q : AmbientSpace) :
    fourierChar (k + l) q = fourierChar k q * fourierChar l q := by apply _root_.YangMills.Construction.Matrices.FourierMatrixSeries.character_add <;> assumption
theorem conj_fourierChar (k : Fin 4 → ℤ) (q : AmbientSpace) :
    conj (fourierChar k q) = fourierChar (-k) q := by
  simp only [fourierChar, intDot_eq_sum, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib,
    Complex.ofReal_neg, mul_neg]
theorem fourierChar_sub (k l : Fin 4 → ℤ) (q : AmbientSpace) :
    fourierChar (k - l) q = conj (fourierChar l q) * fourierChar k q := by
  rw [sub_eq_add_neg, fourierChar_add, conj_fourierChar, mul_comm]
def termValue (t : WeylTerm) (q : AmbientSpace) : ℂ := t.coeff * fourierChar t.offset q
theorem termPair_smul (P : TermPair) (q : AmbientSpace) :
    fourierChar P.offset q • P.coeffMatrix =
      (P.coeff * (conj (termValue P.conjTerm q) * termValue P.term q)) •
        Matrix.single P.conjTerm.comp P.term.comp (1 : ℂ) := by
  simp only [TermPair.offset, TermPair.coeffMatrix, termValue, fourierChar_sub, smul_smul, map_mul]
  congr 1
  ring
theorem phaseWeight_add (i j : Fin 4) : phaseWeight i j true + phaseWeight i j false = 1 := by
  rcases lt_trichotomy i j with h | h | h
  · simp [phaseWeight, h, h.ne, h.not_gt]
  · subst h
    simp [phaseWeight]
    norm_num
  · simp [phaseWeight, h, h.ne', h.not_gt]
def faceTerms (d : {d : Fin 4 × Fin 4 // d.1 < d.2}) : Fin 4 → WeylTerm :=
  faceTerm d.1.1 d.1.2 (fluxWeight d.1.1 d.1.2)
theorem chargedSymbolExplicit_zero_eq (q : AmbientSpace) :
    chargedSymbolExplicit 0 q =
      (∑ d : {d : Fin 4 × Fin 4 // d.1 < d.2}, ∑ i, ∑ j,
        (conj (termValue (faceTerms d i) q) * termValue (faceTerms d j) q) •
          Matrix.single (faceTerms d i).comp (faceTerms d j).comp (1 : ℂ)) +
      ∑ a : Fin 4 × Bool, ∑ b : Fin 4 × Bool,
        (conj (termValue (vertexTerm a.1 a.2) q) * termValue (vertexTerm b.1 b.2) q) •
          Matrix.single (vertexTerm a.1 a.2).comp (vertexTerm b.1 b.2).comp (1 : ℂ) := by
  simp only [chargedSymbolExplicit, pairsSymbol, trigMatrixSum, mul_zero, Complex.ofReal_zero,
    Complex.exp_zero, one_mul, termPair_smul]
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_bool]
    simp only [chargedTermPair, faceTerms]
    rw [← add_smul, ← add_mul, phaseWeight_add, one_mul]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [chargedTermPair, one_mul]
theorem sum_smul_single_apply {ι : Type} [Fintype ι] (c : ι → Fin 4) (g : ι → ℂ) (x y : Fin 4) :
    (∑ i, ∑ j, (conj (g i) * g j) • Matrix.single (c i) (c j) (1 : ℂ)) x y =
      conj (∑ i, if c i = x then g i else 0) * ∑ j, if c j = y then g j else 0 := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : c i = x <;> by_cases h' : c j = y <;> simp [h, h']
def phaseDiff (q : AmbientSpace) (μ : Fin 4) : ℂ := fourierChar (basisVec μ) q - 1
def faceRow (d : Fin 4 → ℂ) (μ ν x : Fin 4) : ℂ :=
  (if μ = x then -d ν else 0) + if ν = x then d μ else 0
theorem faceTerms_row (q : AmbientSpace) (μ ν x : Fin 4) (ε : ℝ) :
    (∑ i, if (faceTerm μ ν ε i).comp = x then termValue (faceTerm μ ν ε i) q
      else 0) = faceRow (phaseDiff q) μ ν x := by
  simp only [Fin.sum_univ_four, faceTerm, termValue, faceRow, phaseDiff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, fourierChar_zero]
  by_cases h : μ = x <;> by_cases h' : ν = x <;> simp [h, h'] <;> ring
theorem vertexTerm_comp (μ : Fin 4) (s : Bool) : (vertexTerm μ s).comp = μ := by
  cases s <;> simp [vertexTerm]
theorem vertexTerms_row (q : AmbientSpace) (x : Fin 4) :
    (∑ a : Fin 4 × Bool, if (vertexTerm a.1 a.2).comp = x then termValue (vertexTerm a.1 a.2) q
      else 0) = conj (phaseDiff q x) := by
  simp only [vertexTerm_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [vertexTerm, termValue, phaseDiff, map_sub, map_one, conj_fourierChar]
  simp [fourierChar_zero, Finset.sum_ite_eq', ← ite_add_zero]
  ring
theorem sum_ordered_pairs (F : Fin 4 × Fin 4 → ℂ) :
    ∑ p : {p : Fin 4 × Fin 4 // p.1 < p.2}, F p.1 =
      F (0, 1) + F (0, 2) + F (0, 3) + F (1, 2) + F (1, 3) + F (2, 3) := by
  rw [← Finset.sum_subtype ({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} :
    Finset (Fin 4 × Fin 4)) (by decide) F]
  simp [Finset.sum_insert]
  ring
theorem faceRow_entries (d : Fin 4 → ℂ) (x y : Fin 4) :
    (∑ p : {p : Fin 4 × Fin 4 // p.1 < p.2},
        conj (faceRow d p.1.1 p.1.2 x) * faceRow d p.1.1 p.1.2 y) + conj (conj (d x)) * conj (d y) =
      (∑ ν, conj (d ν) * d ν) * (if x = y then 1 else 0) := by
  rw [sum_ordered_pairs fun p => conj (faceRow d p.1 p.2 x) * faceRow d p.1 p.2 y]
  fin_cases x <;> fin_cases y <;> simp [faceRow, Fin.sum_univ_four] <;> ring
theorem latticeSymbol_eq_sum (q : AmbientSpace) :
    latticeSymbol (toComplexVec q) = ∑ ν, conj (phaseDiff q ν) * phaseDiff q ν := by
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hc : fourierChar (basisVec ν) q = Complex.exp ((q ν : ℂ) * Complex.I) := by
    simp [fourierChar, intDot_eq_sum, basisVec, Pi.single_apply, mul_comm]
  have hb : conj (Complex.exp ((q ν : ℂ) * Complex.I)) = Complex.exp (-(q ν : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    simp
  have h1 : Complex.exp (-(q ν : ℂ) * Complex.I) * Complex.exp ((q ν : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    simp
  simp only [axisSymbol, toComplexVec, phaseDiff, hc, map_sub, map_one, hb, Complex.cos]
  linear_combination -h1
end FluxZero
open FluxZero in
theorem chargedSymbolFluxZeroClaim_holds : ChargedSymbolFluxZeroClaim := by
  intro q
  have hsum : ∀ F : {d : Fin 4 × Fin 4 // d.1 < d.2} → Matrix (Fin 4) (Fin 4) ℂ, ∀ x y,
      (∑ d, F d) x y = ∑ d, F d x y := fun F x y => Matrix.sum_apply x y _ F
  ext x y
  rw [chargedSymbolExplicit_zero_eq, Matrix.add_apply, hsum]
  simp only [sum_smul_single_apply, faceTerms, faceTerms_row, vertexTerms_row]
  rw [latticeSymbol_eq_sum, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    ← faceRow_entries (phaseDiff q) x y]
end YangMills.Construction.Tower.ConstantFieldSymbols
end
