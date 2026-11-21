import YangMills.Construction.LawByMomentsOfTheFlow.ChainObeysTheFirstLevelProof
import YangMills.Construction.LawByMomentsOfTheFlow.CompletedFormAcrossAStep
import YangMills.Construction.LawByMomentsOfTheFlow.VariablesOfAPointSplitProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.CompletedForms
open MomentLaw TorusFields TorusPaths TorusLumps WeightedResponses ResponseInTheExpansion StepCosts LevelTestFunctions
namespace AcrossStep
section Averages
variable {L : ℕ} [NeZero L]
private theorem sumAlongWord_add {m : ℕ} (A B : TorusBond m → ℝ) (w : BondWord m) :
    sumAlongWord (A + B) w = sumAlongWord A w + sumAlongWord B w := by apply _root_.YangMills.SharedProofs.p21609 <;> assumption
variable {n : ℕ} [NeZero n]
private theorem contourAverage_add (A B : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (A + B) c = _root_.YangMills.Construction.MomentLaw.contourAverage L A c + _root_.YangMills.Construction.MomentLaw.contourAverage L B c := by
  simp only [_root_.YangMills.Construction.MomentLaw.contourAverage, sumAlongWord_add, Finset.sum_add_distrib, mul_add]
private theorem contourAverage_smul (r : ℝ) (A : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    _root_.YangMills.Construction.MomentLaw.contourAverage L (r • A) c = r * _root_.YangMills.Construction.MomentLaw.contourAverage L A c := by apply _root_.YangMills.SharedProofs.p14469 <;> assumption
end Averages
section Recursion
variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]
private theorem summed_recursion (a ρ : ℝ) {s τ : ℕ} (hτ : τ = s) (Qn : TorusSite n → BondBilinear n)
    (q : TorusSite (n * L) → BondBilinear (n * L))
    (hv : TorusSite n → ℝ) (hc : TorusBond n → ℝ)
    (hmean : ∀ c : TorusBond n, (hv c.1 + hv (c.1 + unitStep n c.2)) / 2 = hc c)
    (R : ∀ (Y : TorusSite n) (c c' : TorusBond n), Qn Y c c' =
      ∑ y ∈ sitesInBlocks L {Y}, pullbackForm a ρ L τ (q y) c c' + a / 2 * hv Y * ∑ i : Fin 4,
        (fitDefect L a ρ τ (Y, i) c * fitDefect L a ρ τ (Y, i) c' +
          fitDefect L a ρ τ (Y - unitStep n i, i) c * fitDefect L a ρ τ (Y - unitStep n i, i) c'))
    (A : TorusBond n → ℝ) :
    bilinearEval (n := n) (fun b b' => ∑ Y, Qn Y b b') A A =
      bilinearEval (n := n * L) (fun b b' => ∑ y, q y b b') (responseMap a ρ L s A) (responseMap a ρ L s A) +
        a * ∑ c : TorusBond n, hc c * (_root_.YangMills.Construction.MomentLaw.contourAverage L (responseMap a ρ L s A) c - A c) ^ 2 := by apply _root_.YangMills.SharedProofs.p28188 <;> assumption
end Recursion
section Quadratic
variable {L : ℕ} [NeZero L] {m : ℕ} [NeZero m]
private theorem bilinearEval_add_left {n : ℕ} [NeZero n] (q : BondBilinear n) (A A' B : TorusBond n → ℝ) :
    bilinearEval q (A + A') B = bilinearEval q A B + bilinearEval q A' B := by
  simp only [bilinearEval, Pi.add_apply, add_mul, Finset.sum_add_distrib]
private theorem bilinearEval_add_right {n : ℕ} [NeZero n] (q : BondBilinear n) (A B B' : TorusBond n → ℝ) :
    bilinearEval q A (B + B') = bilinearEval q A B + bilinearEval q A B' := by
  simp only [bilinearEval, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem bilinearEval_smul_left {n : ℕ} [NeZero n] (q : BondBilinear n) (r : ℝ) (A B : TorusBond n → ℝ) :
    bilinearEval q (r • A) B = r * bilinearEval q A B := by
  simp only [bilinearEval, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
private theorem bilinearEval_smul_right {n : ℕ} [NeZero n] (q : BondBilinear n) (r : ℝ) (A B : TorusBond n → ℝ) :
    bilinearEval q A (r • B) = r * bilinearEval q A B := by
  simp only [bilinearEval, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
private theorem colourEval_add_left {n : ℕ} [NeZero n] (q : BondBilinear n) (X X' Y : ColourForm n) :
    colourEval q (X + X') Y = colourEval q X Y + colourEval q X' Y := by
  simp only [colourEval, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => bilinearEval_add_left q (X e) (X' e) (Y e)
private theorem colourEval_add_right {n : ℕ} [NeZero n] (q : BondBilinear n) (X Y Y' : ColourForm n) :
    colourEval q X (Y + Y') = colourEval q X Y + colourEval q X Y' := by
  simp only [colourEval, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => bilinearEval_add_right q (X e) (Y e) (Y' e)
private theorem colourEval_smul_left {n : ℕ} [NeZero n] (q : BondBilinear n) (r : ℝ) (X Y : ColourForm n) :
    colourEval q (r • X) Y = r * colourEval q X Y := by
  simp only [colourEval, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => bilinearEval_smul_left q r (X e) (Y e)
private theorem colourEval_smul_right {n : ℕ} [NeZero n] (q : BondBilinear n) (r : ℝ) (X Y : ColourForm n) :
    colourEval q X (r • Y) = r * colourEval q X Y := by
  simp only [colourEval, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => bilinearEval_smul_right q r (X e) (Y e)
private def averagePairing (hb : TorusBond m → ℝ) (A A' : ColourForm (m * L)) : ℝ :=
  ∑ c, hb c * ∑ e : Fin 3, _root_.YangMills.Construction.MomentLaw.contourAverage L (A e) c * _root_.YangMills.Construction.MomentLaw.contourAverage L (A' e) c
private theorem averagePairing_comm (hb : TorusBond m → ℝ) (A A' : ColourForm (m * L)) :
    averagePairing hb A A' = averagePairing hb A' A := by
  unfold averagePairing
  exact Finset.sum_congr rfl fun c _ => by
    congr 1
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
private theorem averagePairing_add_left (hb : TorusBond m → ℝ) (A A' B : ColourForm (m * L)) :
    averagePairing hb (A + A') B = averagePairing hb A B + averagePairing hb A' B := by
  unfold averagePairing
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← add_mul, Pi.add_apply, contourAverage_add]
private theorem averagePairing_smul_left (hb : TorusBond m → ℝ) (r : ℝ) (A B : ColourForm (m * L)) :
    averagePairing hb (r • A) B = r * averagePairing hb A B := by
  unfold averagePairing
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 : ∑ e : Fin 3, _root_.YangMills.Construction.MomentLaw.contourAverage L ((r • A) e) c * _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c =
      r * ∑ e : Fin 3, _root_.YangMills.Construction.MomentLaw.contourAverage L (A e) c * _root_.YangMills.Construction.MomentLaw.contourAverage L (B e) c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Pi.smul_apply, contourAverage_smul, mul_assoc]
  rw [e1]
  ring
private def stepBilinear (q : BondBilinear (m * L)) (hb : TorusBond m → ℝ) (a : ℝ) (A A' : ColourForm (m * L)) : ℝ :=
  (1 / 2) * (colourEval q A A' + colourEval q A' A) + a * averagePairing hb A A'
variable (q : BondBilinear (m * L)) (hb : TorusBond m → ℝ) (a : ℝ)
private theorem stepBilinear_comm (A A' : ColourForm (m * L)) : stepBilinear q hb a A A' = stepBilinear q hb a A' A := by
  unfold stepBilinear
  rw [averagePairing_comm hb A A']
  ring
private theorem stepBilinear_add_left (A A' B : ColourForm (m * L)) :
    stepBilinear q hb a (A + A') B = stepBilinear q hb a A B + stepBilinear q hb a A' B := by
  unfold stepBilinear
  rw [colourEval_add_left, colourEval_add_right, averagePairing_add_left]
  ring
private theorem stepBilinear_smul_left (r : ℝ) (A B : ColourForm (m * L)) :
    stepBilinear q hb a (r • A) B = r * stepBilinear q hb a A B := by
  unfold stepBilinear
  rw [colourEval_smul_left, colourEval_smul_right, averagePairing_smul_left]
  ring
private theorem stepBilinear_add_right (A B B' : ColourForm (m * L)) :
    stepBilinear q hb a A (B + B') = stepBilinear q hb a A B + stepBilinear q hb a A B' := by
  rw [stepBilinear_comm, stepBilinear_add_left, stepBilinear_comm q hb a B, stepBilinear_comm q hb a B']
private theorem stepBilinear_smul_right (r : ℝ) (A B : ColourForm (m * L)) :
    stepBilinear q hb a A (r • B) = r * stepBilinear q hb a A B := by
  rw [stepBilinear_comm, stepBilinear_smul_left, stepBilinear_comm q hb a B]
private def stepBilinearRight (A : ColourForm (m * L)) : ColourForm (m * L) →ₗ[ℝ] ℝ where
  toFun := stepBilinear q hb a A
  map_add' := stepBilinear_add_right q hb a A
  map_smul' r B := stepBilinear_smul_right q hb a r A B
private theorem stepBilinear_sum_right {ι : Type} [Fintype ι] (A : ColourForm (m * L)) (N : ι → ColourForm (m * L))
    (η : ι → ℝ) :
    stepBilinear q hb a A (∑ x, η x • N x) = ∑ x, η x * stepBilinear q hb a A (N x) := by
  have e := map_sum (stepBilinearRight q hb a A) (fun x => η x • N x) Finset.univ
  refine e.trans (Finset.sum_congr rfl fun x _ => ?_)
  exact stepBilinear_smul_right q hb a (η x) A (N x)
private def stepLinear (Z : ColourForm m) (A : ColourForm (m * L)) : ℝ :=
  -(a * ∑ c, hb c * ∑ e : Fin 3, Z e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (A e) c)
private theorem stepLinear_add (Z : ColourForm m) (A B : ColourForm (m * L)) :
    stepLinear hb a Z (A + B) = stepLinear hb a Z A + stepLinear hb a Z B := by
  unfold stepLinear
  rw [← neg_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← mul_add, Pi.add_apply, contourAverage_add]
private theorem stepLinear_smul (Z : ColourForm m) (r : ℝ) (A : ColourForm (m * L)) :
    stepLinear hb a Z (r • A) = r * stepLinear hb a Z A := by
  unfold stepLinear
  have e1 : ∑ c, hb c * ∑ e : Fin 3, Z e c * _root_.YangMills.Construction.MomentLaw.contourAverage L ((r • A) e) c =
      r * ∑ c, hb c * ∑ e : Fin 3, Z e c * contourAverage L (A e) c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e2 : ∑ e : Fin 3, Z e c * _root_.YangMills.Construction.MomentLaw.contourAverage L ((r • A) e) c =
        r * ∑ e : Fin 3, Z e c * contourAverage L (A e) c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Pi.smul_apply, contourAverage_smul, mul_left_comm]
    rw [e2]
    ring
  rw [e1]
  ring
private theorem stepLinear_add_coarse (Z Z' : ColourForm m) (A : ColourForm (m * L)) :
    stepLinear hb a (Z + Z') A = stepLinear hb a Z A + stepLinear hb a Z' A := by
  unfold stepLinear
  rw [← neg_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← add_mul]
  rfl
private theorem stepLinear_smul_coarse (r : ℝ) (Z : ColourForm m) (A : ColourForm (m * L)) :
    stepLinear hb a (r • Z) A = r * stepLinear hb a Z A := by
  unfold stepLinear
  have e1 : ∑ c, hb c * ∑ e : Fin 3, (r • Z) e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (A e) c =
      r * ∑ c, hb c * ∑ e : Fin 3, Z e c * contourAverage L (A e) c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e2 : ∑ e : Fin 3, (r • Z) e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (A e) c =
        r * ∑ e : Fin 3, Z e c * contourAverage L (A e) c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← mul_assoc]
      rfl
    rw [e2]
    ring
  rw [e1]
  ring
private def stepLinearMap (Z : ColourForm m) : ColourForm (m * L) →ₗ[ℝ] ℝ where
  toFun := stepLinear hb a Z
  map_add' := stepLinear_add hb a Z
  map_smul' r B := stepLinear_smul hb a Z r B
private theorem stepLinear_sum {ι : Type} [Fintype ι] (Z : ColourForm m) (N : ι → ColourForm (m * L)) (η : ι → ℝ) :
    stepLinear hb a Z (∑ x, η x • N x) = ∑ x, η x * stepLinear hb a Z (N x) := by
  have e := map_sum (stepLinearMap hb a Z) (fun x => η x • N x) Finset.univ
  refine e.trans (Finset.sum_congr rfl fun x _ => ?_)
  exact stepLinear_smul hb a Z (η x) (N x)
private def stepEnergy (Z : ColourForm m) (X : ColourForm (m * L)) : ℝ :=
  (1 / 2) * colourEval q X X + a * ∑ c : TorusBond m, hb c *
    ((1 / 2) * ∑ e : Fin 3, (Z e c - _root_.YangMills.Construction.MomentLaw.contourAverage L (X e) c) ^ 2 - 3 / (2 * a))
private def stepConstant : ℝ := a * ∑ c : TorusBond m, hb c * (-(3 / (2 * a)))
private theorem stepEnergy_eq_gap (Z : ColourForm m) (X : ColourForm (m * L)) :
    stepEnergy q hb a Z X = (1 / 2) * colourEval q X X +
      a / 2 * ∑ c : TorusBond m, hb c * ∑ e : Fin 3, (Z e c - _root_.YangMills.Construction.MomentLaw.contourAverage L (X e) c) ^ 2 + stepConstant hb a := by
  unfold stepEnergy stepConstant
  have key : ∀ c : TorusBond m,
      hb c * ((1 / 2) * ∑ e : Fin 3, (Z e c - contourAverage L (X e) c) ^ 2 - 3 / (2 * a)) =
      (1 / 2) * (hb c * ∑ e : Fin 3, (Z e c - _root_.YangMills.Construction.MomentLaw.contourAverage L (X e) c) ^ 2) + hb c * (-(3 / (2 * a))) :=
    fun c => by ring
  rw [Finset.sum_congr rfl fun c _ => key c, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
private theorem stepEnergy_eq (Z : ColourForm m) (X : ColourForm (m * L)) :
    stepEnergy q hb a Z X = (1 / 2) * stepBilinear q hb a X X + stepLinear hb a Z X +
      a / 2 * ∑ c : TorusBond m, hb c * ∑ e : Fin 3, Z e c ^ 2 + stepConstant hb a := by
  unfold stepEnergy stepConstant stepBilinear stepLinear averagePairing
  have key : ∀ c : TorusBond m,
      hb c * ((1 / 2) * ∑ e : Fin 3, (Z e c - contourAverage L (X e) c) ^ 2 - 3 / (2 * a)) =
      (1 / 2) * (hb c * ∑ e : Fin 3, _root_.YangMills.Construction.MomentLaw.contourAverage L (X e) c * _root_.YangMills.Construction.MomentLaw.contourAverage L (X e) c) -
        hb c * ∑ e : Fin 3, Z e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (X e) c + (1 / 2) * (hb c * ∑ e : Fin 3, Z e c ^ 2) +
        hb c * (-(3 / (2 * a))) := fun c => by
    simp only [Fin.sum_univ_three]
    ring
  rw [Finset.sum_congr rfl fun c _ => key c, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring
private theorem stepEnergy_add (Z : ColourForm m) (P R : ColourForm (m * L)) :
    stepEnergy q hb a Z (P + R) = stepEnergy q hb a Z P + (stepBilinear q hb a P R + stepLinear hb a Z R) +
      (1 / 2) * stepBilinear q hb a R R := by
  rw [stepEnergy_eq, stepEnergy_eq, stepBilinear_add_left, stepBilinear_add_right, stepBilinear_add_right,
    stepBilinear_comm q hb a R P, stepLinear_add]
  ring
private theorem stepEnergy_expansion {ι : Type} [Fintype ι] (N : ι → ColourForm (m * L)) (Z : ColourForm m)
    (P : ColourForm (m * L)) (η : ι → ℝ) :
    stepEnergy q hb a Z (P + ∑ x, η x • N x) =
      stepEnergy q hb a Z P + ∑ x, (stepBilinear q hb a P (N x) + stepLinear hb a Z (N x)) * η x +
      (1 / 2) * ∑ x, ∑ y, stepBilinear q hb a (N x) (N y) * η x * η y := by
  have e : stepBilinear q hb a (∑ x, η x • N x) (∑ x, η x • N x) =
      ∑ x, ∑ y, stepBilinear q hb a (N x) (N y) * η x * η y := by
    rw [stepBilinear_sum_right]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [stepBilinear_comm q hb a _ (N x), stepBilinear_sum_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have e2 : stepBilinear q hb a P (∑ x, η x • N x) + stepLinear hb a Z (∑ x, η x • N x) =
      ∑ x, (stepBilinear q hb a P (N x) + stepLinear hb a Z (N x)) * η x := by
    rw [stepBilinear_sum_right, stepLinear_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [stepEnergy_add, e, e2]
private def stepDirectional (Z : ColourForm m) (X A : ColourForm (m * L)) : ℝ :=
  (1 / 2) * (colourEval q X A + colourEval q A X) -
    a * ∑ c : TorusBond m, hb c * ∑ e : Fin 3, (Z e c - _root_.YangMills.Construction.MomentLaw.contourAverage L (X e) c) * _root_.YangMills.Construction.MomentLaw.contourAverage L (A e) c
private theorem stepDirectional_eq (Z : ColourForm m) (X A : ColourForm (m * L)) :
    stepDirectional q hb a Z X A = stepBilinear q hb a X A + stepLinear hb a Z A := by
  unfold stepDirectional stepBilinear stepLinear averagePairing
  have key : ∑ c : TorusBond m, hb c * ∑ e : Fin 3, (Z e c - _root_.YangMills.Construction.MomentLaw.contourAverage L (X e) c) * _root_.YangMills.Construction.MomentLaw.contourAverage L (A e) c =
      ∑ c : TorusBond m, hb c * ∑ e : Fin 3, Z e c * _root_.YangMills.Construction.MomentLaw.contourAverage L (A e) c -
        ∑ c : TorusBond m, hb c * ∑ e : Fin 3, _root_.YangMills.Construction.MomentLaw.contourAverage L (X e) c * _root_.YangMills.Construction.MomentLaw.contourAverage L (A e) c := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Fin.sum_univ_three]
    ring
  rw [key]
  ring
private theorem stepDirectional_across {ι : Type} [Fintype ι] (N : ι → ColourForm (m * L)) (Z : ColourForm m)
    (P : ColourForm (m * L)) (η : ι → ℝ) (x : ι) :
    stepDirectional q hb a Z (P + ∑ y, η y • N y) (N x) =
      stepBilinear q hb a P (N x) + stepLinear hb a Z (N x) + ∑ y, stepBilinear q hb a (N x) (N y) * η y := by
  have e : stepBilinear q hb a (∑ y, η y • N y) (N x) = ∑ y, stepBilinear q hb a (N x) (N y) * η y := by
    rw [stepBilinear_comm, stepBilinear_sum_right]
    exact Finset.sum_congr rfl fun y _ => mul_comm _ _
  rw [stepDirectional_eq, stepBilinear_add_left, e]
  ring
private theorem pushColours_add (ρ : ℝ) (u : ℕ) (Z Z' : ColourForm m) :
    pushColours a ρ L u (Z + Z') = pushColours a ρ L u Z + pushColours a ρ L u Z' := by
  funext e b
  simp only [pushColours, responseMap, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem pushColours_smul (ρ : ℝ) (u : ℕ) (r : ℝ) (Z : ColourForm m) :
    pushColours a ρ L u (r • Z) = r • pushColours a ρ L u Z := by
  funext e b
  simp only [pushColours, responseMap, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring
private theorem linearPart_measurable (ρ : ℝ) (u : ℕ) (A : ColourForm (m * L)) :
    Measurable fun Z : ColourForm m => stepBilinear q hb a (pushColours a ρ L u Z) A + stepLinear hb a Z A := by
  have hl : IsLinearMap ℝ fun Z : ColourForm m => stepBilinear q hb a (pushColours a ρ L u Z) A + stepLinear hb a Z A :=
    ⟨fun Z Z' => by
      simp only [pushColours_add, stepBilinear_add_left, stepLinear_add_coarse]
      ring, fun r Z => by
      simp only [pushColours_smul, stepBilinear_smul_left, stepLinear_smul_coarse, smul_eq_mul]
      ring⟩
  exact (hl.mk' _).continuous_of_finiteDimensional.measurable
end Quadratic
section Extension
variable {L : ℕ} [NeZero L]
open Classical in
private def unitExtension (u n : ℕ) [NeZero n] (x : Fin 3 × ChartBondIndex L u n) : ColourForm (n * L) :=
  extendFluctuation (EuclideanSpace.single x 1)
private theorem extendFluctuation_eq_sum {u n : ℕ} [NeZero n] (η : StepFluctuation L u n) :
    extendFluctuation η = ∑ x, η x • unitExtension u n x := by
  classical
  funext e c
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitExtension, extendFluctuation, extendChart,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth c.1, c.2) = b.1
  · simp only [if_pos h]
    rw [Finset.sum_eq_single (e, b)]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  · simp [if_neg h]
end Extension
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private def summedClassical (i : Fin Λ.k) (u n : ℕ) [NeZero n] : BondBilinear n := fun b b' =>
  ∑ y : TorusSite n, classicalQuadratic S.tower S.resp u n (S.weight i _) y b b'
private theorem stage_depth (u : ℕ) : (S.tower.stage u).depth = u := by apply _root_.YangMills.SharedProofs.p98506 <;> assumption
private theorem stage_anchorRadius (t : ℕ) : (S.tower.stage t).anchorRadius = Λ.table.ρA := by apply _root_.YangMills.SharedProofs.p56052 <;> assumption
private theorem n₀_le_levelSide (u : ℕ) : Λ.stepParams.n₀ ≤ S.levelSide u := by
  have hL : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  show Λ.stepParams.n₀ ≤ S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - u)
  calc Λ.stepParams.n₀ ≤ Λ.stepParams.side * Λ.stepParams.n₀ := Nat.le_mul_of_pos_left _ hL
    _ ≤ S.data.period Λ.stepParams.side := S.side_le
    _ ≤ _ := Nat.le_mul_of_pos_right _ (pow_pos hL _)
private theorem supportForm_eq
    (Kl : ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (y : TorusSite n)
      (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)),
      (∀ p, IsPlaquetteAt Λ.stepParams.side (S.tower.stage t).depth y p → h p = 0) →
        classicalQuadratic S.tower S.resp t n h y = 0)
    (i : Fin Λ.k) {s n : ℕ} [NeZero n] (hs : s ≤ S.data.windowLevel) (hn : Λ.stepParams.n₀ ≤ n) :
    S.supportForm s n i = summedClassical S i s n := by
  classical
  funext b b'
  show ∑ y ∈ S.supportAt s n i, _ = ∑ y : TorusSite n, _
  refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
  have hy' : ¬ ∃ p, IsPlaquetteAt Λ.stepParams.side s y p ∧
      S.weight i (fineSide Λ.stepParams.side s n) p ≠ 0 := fun h =>
    hy (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have hz : ∀ v, v = s → ∀ p : TorusPlaquette (fineSide Λ.stepParams.side v n),
      IsPlaquetteAt Λ.stepParams.side v y p → S.weight i (fineSide Λ.stepParams.side v n) p = 0 := by
    rintro v rfl p hp
    by_contra hne
    exact hy' ⟨p, hp, hne⟩
  rw [Kl s hs n hn y _ (hz _ (stage_depth S s))]
  rfl
private theorem colourEval_across
    (R : ∀ t, t < S.data.windowLevel → ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
      ∀ (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage (t + 1)).depth n))
      (Y : TorusSite n) (c c' : TorusBond n),
      classicalQuadratic S.tower S.resp (t + 1) n h Y c c' =
        ∑ y ∈ sitesInBlocks Λ.stepParams.side {Y}, pullbackForm Λ.stepParams.coupling (S.tower.stage t).anchorRadius
          Λ.stepParams.side (S.tower.stage t).depth
          (classicalQuadratic S.tower S.resp t (n * Λ.stepParams.side) h y) c c' +
        Λ.stepParams.coupling / 2 * blockMean Λ.stepParams.side ((S.tower.stage t).depth + 1) n Y h * ∑ i : Fin 4,
          (fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius (S.tower.stage t).depth
              (Y, i) c *
              fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius
                (S.tower.stage t).depth (Y, i) c' +
            fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius (S.tower.stage t).depth
              (Y - unitStep n i, i) c *
              fitDefect Λ.stepParams.side Λ.stepParams.coupling (S.tower.stage t).anchorRadius
                (S.tower.stage t).depth (Y - unitStep n i, i) c'))
    (Kl : ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (y : TorusSite n)
      (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)),
      (∀ p, IsPlaquetteAt Λ.stepParams.side (S.tower.stage t).depth y p → h p = 0) →
        classicalQuadratic S.tower S.resp t n h y = 0)
    {l : ℕ} (hl : l < S.data.windowLevel) (m : ℕ) [NeZero m] (hm : Λ.stepParams.n₀ ≤ m) (i : Fin Λ.k)
    (Z : ColourForm m) :
    (1 / 2) * colourEval (S.supportForm (l + 1) m i) Z Z =
      (1 / 2) * colourEval (S.supportForm l (m * Λ.stepParams.side) i)
        (pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l Z)
        (pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l Z) +
      Λ.stepParams.coupling / 2 * ∑ c : TorusBond m,
        bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _) c *
        ∑ e : Fin 3, (Z e c - contourAverage Λ.stepParams.side
          (pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l Z e) c) ^ 2 := by
  have hL : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hmL : Λ.stepParams.n₀ ≤ m * Λ.stepParams.side := hm.trans (Nat.le_mul_of_pos_right _ hL)
  have mean_eq : ∀ v, v = l → ∀ Y : TorusSite m,
      blockMean Λ.stepParams.side (v + 1) m Y (S.weight i (fineSide Λ.stepParams.side (v + 1) m)) =
      blockMean Λ.stepParams.side (l + 1) m Y (S.weight i (fineSide Λ.stepParams.side (l + 1) m)) := by
    rintro v rfl Y
    rfl
  have each : ∀ A : TorusBond m → ℝ, bilinearEval (summedClassical S i (l + 1) m) A A =
      bilinearEval (summedClassical S i l (m * Λ.stepParams.side))
        (responseMap Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l A)
        (responseMap Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l A) +
        Λ.stepParams.coupling * ∑ c : TorusBond m, bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _) c *
          (_root_.YangMills.Construction.MomentLaw.contourAverage Λ.stepParams.side
            (responseMap Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l A) c - A c) ^ 2 := by
    intro A
    refine summed_recursion (L := Λ.stepParams.side) Λ.stepParams.coupling Λ.table.ρA (stage_depth S l)
      (fun Y => classicalQuadratic S.tower S.resp (l + 1) m (S.weight i _) Y)
      (fun y => classicalQuadratic S.tower S.resp l (m * Λ.stepParams.side) (S.weight i _) y)
      (fun Y => blockMean Λ.stepParams.side ((S.tower.stage l).depth + 1) m Y
        (S.weight i (fineSide Λ.stepParams.side ((S.tower.stage l).depth + 1) m)))
      (bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _)) (fun c => ?_) (fun Y c c' => ?_) A
    · show (_ + _) / 2 = (_ + _) / 2
      rw [mean_eq _ (stage_depth S l), mean_eq _ (stage_depth S l)]
    · have := R l hl m hm (S.weight i _) Y c c'
      rw [stage_anchorRadius] at this
      exact this
  rw [supportForm_eq S Kl i (Nat.succ_le_of_lt hl) hm, supportForm_eq S Kl i hl.le hmL]
  have hM : ∀ e, pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l Z e =
      responseMap Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l (Z e) := fun _ => rfl
  have swap : ∑ e : Fin 3, ∑ c : TorusBond m, bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _) c *
        (_root_.YangMills.Construction.MomentLaw.contourAverage Λ.stepParams.side
          (responseMap Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l (Z e)) c - Z e c) ^ 2 =
      ∑ c : TorusBond m, bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _) c *
        ∑ e : Fin 3, (Z e c - contourAverage Λ.stepParams.side
          (responseMap Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l (Z e)) c) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  unfold colourEval
  simp only [hM]
  rw [Finset.sum_congr rfl fun e _ => each (Z e), Finset.sum_add_distrib, ← Finset.mul_sum, swap]
  ring
end Point
section Parameters
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h₂ : ForAllParameters Q₂) : ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_imp {Q Q' : MomentParameters → Prop} (h : ForAllParameters Q)
    (hq : ∀ Λ : MomentParameters, Q Λ → Q' Λ) : ForAllParameters Q' := by
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hrt₁, H₁⟩ := h a ha
  refine ⟨L₁, rt₁, C₁, hrt₁, ?_⟩
  intro L hLodd hLge Tb hTa hTL hDr hCS hOn hrt hCd Kr hKr
  obtain ⟨y₁, Y₁⟩ := H₁ L hLodd hLge Tb hTa hTL hDr hCS hOn hrt hCd Kr hKr
  refine ⟨y₁, ?_⟩
  intro y hy hRet hHas g hg hyg k _ hk2 hk8 R d hd
  exact hq ⟨Tb, Kr, y, g, k, R, d⟩ (Y₁ y hy hRet hHas g hg hyg k hk2 hk8 R d hd)
abbrev _root_.YangMills.SharedProofs.p9549 := @forAllParameters_imp
private theorem forAllParameters_of_forAllPoints
    {Q : ∀ Λ : MomentParameters, (ℕ → ℝ) → ℝ → ℝ → MomentPoint Λ → Prop} (h : ForAllPoints Q) :
    ForAllParameters fun Λ => ∃ (C : ℕ → ℝ) (c X₀ : ℝ), 0 < c ∧ Λ.floor ≤ X₀ ∧ ∀ S : MomentPoint Λ, Q Λ C c X₀ S :=
  h
end Parameters
end AcrossStep
open AcrossStep in
theorem completedFormAcrossStep_holds (h₁ : classicalQuadraticRecursionStatement)
    (h₂ : classicalFormsAnnihilateClosedStatement) : completedFormAcrossStepStatement := by
  unfold completedFormAcrossStepStatement ForAllPoints
  refine forAllParameters_imp (forAllParameters_and (forAllParameters_of_forAllPoints h₁)
    (forAllParameters_of_forAllPoints h₂)) fun Λ H => ?_
  obtain ⟨⟨_, _, _, _, _, f₁⟩, ⟨_, _, _, _, _, f₂⟩⟩ := H
  refine ⟨fun _ => 0, 1, Λ.floor, one_pos, le_rfl, fun S => ?_⟩
  intro l hl m _ hm i
  have hts : S.lastSeparated ≤ S.data.scaleLevel := by
    classical
    unfold MomentPoint.lastSeparated
    apply Nat.findGreatest_le
  have hlt : S.lastSeparated ≤ S.data.windowLevel := hts.trans S.supAdmissible.scaleLevel_le
  have hlK : l < S.data.windowLevel := lt_of_lt_of_le hl hlt
  have hn : Λ.stepParams.n₀ ≤ m := hm ▸ n₀_le_levelSide S (l + 1)
  have hform := colourEval_across S (f₁ S).1 (fun t ht n _ hn y h hh => ((f₂ S t ht n hn y h).2.2.2 hh).2) hlK m hn i
  refine ⟨fun x y => stepBilinear (S.supportForm l (m * Λ.stepParams.side) i)
      (bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _)) Λ.stepParams.coupling
      (unitExtension l m x) (unitExtension l m y),
    fun Z x => stepBilinear (S.supportForm l (m * Λ.stepParams.side) i)
        (bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _)) Λ.stepParams.coupling
        (pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l Z) (unitExtension l m x) +
      stepLinear (bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _)) Λ.stepParams.coupling Z
        (unitExtension l m x),
    stepConstant (bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _)) Λ.stepParams.coupling, ?_, ?_, ?_⟩
  · ext x y
    exact stepBilinear_comm _ _ _ _ _
  · intro x
    exact linearPart_measurable _ _ _ _ _ _
  · intro Z η
    have hX : descendForm Λ l m Z η =
        pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l Z + ∑ x, η x • unitExtension l m x := by
      rw [← extendFluctuation_eq_sum]
      rfl
    refine ⟨?_, fun x => ?_⟩
    · have e1 : S.levelStepValue l m i Z (descendForm Λ l m Z η) =
          stepEnergy (S.supportForm l (m * Λ.stepParams.side) i)
            (bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _)) Λ.stepParams.coupling Z
            (pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l Z + ∑ x, η x • unitExtension l m x) := by
        rw [hX]
        rfl
      rw [e1, stepEnergy_expansion, stepEnergy_eq_gap, hform Z]
    · have e2 : S.levelStepGradient l m i Z (descendForm Λ l m Z η) x =
          stepDirectional (S.supportForm l (m * Λ.stepParams.side) i)
            (bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _)) Λ.stepParams.coupling Z
            (pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l Z + ∑ y, η y • unitExtension l m y)
            (unitExtension l m x) := by
        rw [hX]
        rfl
      rw [e2, stepDirectional_across]
end YangMills.Construction.CompletedForms
end
