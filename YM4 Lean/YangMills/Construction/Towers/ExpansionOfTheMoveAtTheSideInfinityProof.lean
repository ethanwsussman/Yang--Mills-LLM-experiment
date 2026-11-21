import YangMills.Construction.Averaging.MeanInTheComplexGroupProof
import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroupProof
import YangMills.Construction.Towers.ExpansionOfTheMoveAtTheSideInfinity
import YangMills.Construction.Towers.ExpansionOfThreeExponentialsInTheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.TwistExpansionAtInfiniteSide
open Matrices (ComplexMatrix2)
section Links
variable {a : ℝ}
theorem opposite_pos_of_not_pos (e : InfiniteLattice.Link a) (h : ¬ e.IsPositivelyOriented) :
    e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem not_opposite_pos (ha : 0 < a) (e : InfiniteLattice.Link a) (h : e.IsPositivelyOriented) :
    ¬ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
end Links
theorem matExp_mem_complexGaugeGroup (hExp : Matrices.ComplexMatrix2.ExpLogEstimates)
    {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.matExp X ∈ PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.ComplexMeanMembership.matExp_mem <;> assumption
theorem isUnit_of_mem_complexGaugeGroup {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.complexGaugeGroup) : IsUnit g := by apply _root_.YangMills.Construction.Averaging.ComplexLogMean.isUnit_of_mem_complexGaugeGroup <;> assumption
theorem mul_mem_complexGaugeGroup {g h : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.complexGaugeGroup) (hh : h ∈ PeriodicLattice.complexGaugeGroup) :
    g * h ∈ PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.SharedProofs.p592 <;> assumption
theorem inv_mem_complexGaugeGroup {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.complexGaugeGroup) : g⁻¹ ∈ PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
theorem conj_mem_traceless {V X : ComplexMatrix2} (hV : IsUnit V)
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.traceless := by
  have htr : Matrix.trace X = 0 := hX
  have hdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV
  change Matrix.trace (V * X * V⁻¹) = 0
  rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul V hdet, one_mul, htr]
section SingleLattice
variable {a : ℝ}
theorem expTwist_isFieldIn (hExp : Matrices.ComplexMatrix2.ExpLogEstimates) (ha : 0 < a)
    {U B : InfiniteLattice.Link a → ComplexMatrix2}
    (hU : FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup U)
    (hB : B ∈ FullSpace.complexEdgeForms a) (s : ℂ) :
    FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup (FullSpace.expTwist (s • B) U) := by
  have hval : ∀ e : InfiniteLattice.Link a, e.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • (s • B) e) * U e ∈
        PeriodicLattice.complexGaugeGroup := fun e he =>
    mul_mem_complexGaugeGroup (matExp_mem_complexGaugeGroup hExp (ComplexMatrix2.traceless.smul_mem _
      (ComplexMatrix2.traceless.smul_mem _ (hB.1 e he)))) (hU.1 e)
  refine ⟨fun e => ?_, fun e => ?_⟩
  · by_cases he : e.IsPositivelyOriented
    · simpa [FullSpace.expTwist, he] using hval e he
    · simpa [FullSpace.expTwist, he] using
        inv_mem_complexGaugeGroup (hval e.opposite (opposite_pos_of_not_pos e he))
  · by_cases he : e.IsPositivelyOriented
    · have hop := not_opposite_pos ha e he
      simp only [FullSpace.expTwist, he, hop, if_true, if_false]
      rfl
    · have hop := opposite_pos_of_not_pos e he
      have hunit := isUnit_of_mem_complexGaugeGroup (hval e.opposite hop)
      have hdet : IsUnit (ComplexMatrix2.matExp (Complex.I • (s • B) e.opposite) *
          U e.opposite).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp hunit
      simp only [FullSpace.expTwist, he, hop, if_true, if_false]
      rw [Matrix.nonsing_inv_nonsing_inv _ hdet]
theorem twistedField_eq_tripleProduct {U : InfiniteLattice.Link a → ComplexMatrix2}
    {Λ : InfiniteLattice.LatticePoint a → ComplexMatrix2}
    {B : InfiniteLattice.Link a → ComplexMatrix2}
    {e : InfiniteLattice.Link a} (he : e.IsPositivelyOriented) (hV : IsUnit (U e)) (s t : ℂ) :
    FullSpace.twistedField U Λ B s t e =
      TripleExpExpansion.tripleProduct (Λ e.initial) (B e)
        (ComplexMatrix2.conjugateBy (U e) (Λ e.terminal)) (U e) s t := by
  have hconj : U e * ComplexMatrix2.matExp (-(Complex.I • t • Λ e.terminal)) =
      ComplexMatrix2.matExp (-(Complex.I • t • ComplexMatrix2.conjugateBy (U e) (Λ e.terminal))) *
        U e := by
    have hdet : IsUnit (U e).det := (Matrix.isUnit_iff_isUnit_det _).mp hV
    have hexpo : -(Complex.I • t • ComplexMatrix2.conjugateBy (U e) (Λ e.terminal)) =
        U e * (-(Complex.I • t • Λ e.terminal)) * (U e)⁻¹ := by
      simp [ComplexMatrix2.conjugateBy, mul_assoc]
    have hexp : ComplexMatrix2.matExp (U e * (-(Complex.I • t • Λ e.terminal)) * (U e)⁻¹) =
        U e * ComplexMatrix2.matExp (-(Complex.I • t • Λ e.terminal)) * (U e)⁻¹ :=
      Matrix.exp_conj _ _ hV
    rw [hexpo, hexp, mul_assoc _ (U e)⁻¹, Matrix.nonsing_inv_mul _ hdet, mul_one]
  have hinv : (ComplexMatrix2.matExp (Complex.I • t • Λ e.terminal))⁻¹ =
      ComplexMatrix2.matExp (-(Complex.I • t • Λ e.terminal)) := (Matrix.exp_neg _).symm
  simp only [FullSpace.twistedField, FullSpace.gaugeAct, FullSpace.vertexExp, FullSpace.expTwist,
    he, if_true, Pi.smul_apply, TripleExpExpansion.tripleProduct]
  rw [hinv]
  simp only [mul_assoc]
  rw [hconj]
theorem principalExponent_eq_principalPart {U : InfiniteLattice.Link a → ComplexMatrix2}
    {Λ : InfiniteLattice.LatticePoint a → ComplexMatrix2}
    {B : InfiniteLattice.Link a → ComplexMatrix2}
    {e : InfiniteLattice.Link a} (he : e.IsPositivelyOriented) (s t : ℂ) :
    FullSpace.principalExponent U Λ B s t e =
      TripleExpExpansion.principalPart (Λ e.initial) (B e)
        (ComplexMatrix2.conjugateBy (U e) (Λ e.terminal)) s t := by
  simp only [FullSpace.principalExponent, FullSpace.covDiff, FullSpace.levelBracketTerm,
    FullSpace.gaugeQuadTerm, FullSpace.extendOddly, he, if_true, TripleExpExpansion.principalPart,
    smul_neg, sub_eq_add_neg]
end SingleLattice
theorem fullSpaceTwistExpansionClaim_holds (hExp : Matrices.ComplexMatrix2.ExpLogEstimates)
    (hTriple : TripleExpExpansion.Claim) : FullSpaceTwistExpansionClaim := by
  intro L k j hL _ U Λ B hU hΛ hB
  have ha : 0 < meshAt L k j := by
    have : (0 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 0 < L)
    exact zpow_pos this _
  refine ⟨fun s => expTwist_isFieldIn hExp ha hU hB s, fun t x => ?_, fun e he => ?_⟩
  · exact matExp_mem_complexGaugeGroup hExp
      (ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.smul_mem _ (hΛ x)))
  · have hV : IsUnit (U e) := isUnit_of_mem_complexGaugeGroup (hU.1 e)
    have hfield : (fun s t => FullSpace.twistedField U Λ B s t e) =
        TripleExpExpansion.tripleProduct (Λ e.initial) (B e)
          (ComplexMatrix2.conjugateBy (U e) (Λ e.terminal)) (U e) := by
      funext s t
      exact twistedField_eq_tripleProduct he hV s t
    have hprincipal : (fun s t => FullSpace.principalExponent U Λ B s t e) =
        TripleExpExpansion.principalPart (Λ e.initial) (B e)
          (ComplexMatrix2.conjugateBy (U e) (Λ e.terminal)) := by
      funext s t
      exact principalExponent_eq_principalPart he s t
    rw [hfield, hprincipal]
    exact hTriple _ _ _ _ (hΛ _) (hB.1 e he) (conj_mem_traceless hV (hΛ _)) hV
end YangMills.Construction.Tower.TwistExpansionAtInfiniteSide
end
