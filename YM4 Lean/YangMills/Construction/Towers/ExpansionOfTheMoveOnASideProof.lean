import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Matrices.ConjugationOnTraceless
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.NormExpLogBasics
import YangMills.Construction.Towers.ExpansionOfTheMoveOnASide
import YangMills.Construction.Towers.ExpansionOfThreeExponentialsInTheLeftChart
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Matrices
namespace YangMills.Construction.Tower
namespace TwistExpansionProof
variable {L n k j : ℕ}
theorem det_matExp_I_smul (hE : ComplexMatrix2.ExpLogEstimates) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    (ComplexMatrix2.matExp (Complex.I • X)).det = 1 := by
  obtain ⟨-, -, -, -, -, hdet, -⟩ := hE
  have h : ComplexMatrix2.fullTrace (Complex.I • X) = 0 :=
    ComplexMatrix2.traceless.smul_mem Complex.I hX
  rw [hdet, h, Complex.exp_zero]
theorem det_matExp_mul (hE : ComplexMatrix2.ExpLogEstimates) {A U : Edge L n k j → ComplexMatrix2}
    (hU : ∀ b, (U b).det = 1)
    (hA : ∀ b : Edge L n k j, b.IsPositivelyOriented → A b ∈ ComplexMatrix2.traceless)
    {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    (ComplexMatrix2.matExp (Complex.I • A b) * U b).det = 1 := by
  rw [Matrix.det_mul, det_matExp_I_smul hE (hA b hb), hU b, one_mul]
theorem expTwist_mem_fieldsIn (hE : ComplexMatrix2.ExpLogEstimates) (hL : 1 < L) (hn : 0 < n)
    (hj : j ≤ k) {A U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hA : ∀ b : Edge L n k j, b.IsPositivelyOriented → A b ∈ ComplexMatrix2.traceless) :
    PeriodicLattice.expTwist A U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  have hdet : ∀ b, (U b).det = 1 := fun b => hU.1 b (mem_univ b)
  have hdepth : -(n : ℤ) < (k : ℤ) - (j : ℤ) := by omega
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · change (PeriodicLattice.expTwist A U b).det = 1
    by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb]
      exact det_matExp_mul hE hdet hA hb
    · simp only [PeriodicLattice.expTwist, if_neg hb]
      rw [Matrix.det_nonsing_inv,
        det_matExp_mul hE hdet hA (PeriodicLattice.Bond.opposite_isPositivelyOriented hb),
        Ring.inverse_one]
  · by_cases hb : b.IsPositivelyOriented
    · have hr : ¬ b.opposite.IsPositivelyOriented :=
        PeriodicLattice.Bond.opposite_not_isPositivelyOriented hL hdepth hb
      simp only [PeriodicLattice.expTwist, if_neg hr, if_pos hb]
      rfl
    · have hr : b.opposite.IsPositivelyOriented :=
        PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      simp only [PeriodicLattice.expTwist, if_neg hb, if_pos hr]
      have hd : IsUnit (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite).det := by
        rw [det_matExp_mul hE hdet hA hr]
        exact isUnit_one
      rw [Matrix.nonsing_inv_nonsing_inv _ hd]
theorem mul_inv_matExp (hF : ComplexMatrix2.NormExpLogBasics) {V : ComplexMatrix2} (hV : IsUnit V)
    (Z : ComplexMatrix2) :
    V * (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-(V * Z * V⁻¹)) * V := by
  obtain ⟨-, hExp, -⟩ := hF
  obtain ⟨-, -, -, -, hInv, -, -⟩ := hExp Z
  have hd : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).1 hV
  obtain ⟨-, -, -, -, -, -, hConj⟩ := hExp (-Z)
  have h' := hConj V hV
  rw [hInv]
  have e : V * (-Z) * V⁻¹ = -(V * Z * V⁻¹) := by noncomm_ring
  rw [e] at h'
  rw [← h', mul_assoc _ V⁻¹ V, Matrix.nonsing_inv_mul _ hd, mul_one]
end TwistExpansionProof
theorem TwistExpansionOnTorus.claim_holds
    (hThree : TripleExpExpansion.Claim)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hF : ComplexMatrix2.NormExpLogBasics)
    (hC : ComplexMatrix2.ConjugationPreservesTraceless) :
    TwistExpansionOnTorus.Claim := by
  intro L n k j hL hn hj U l B hU hl hB
  have hL' : 1 < L := lt_of_lt_of_le (by norm_num) hL.2
  refine ⟨fun s => ?_, fun t x => ?_, fun b hb => ?_⟩
  · exact TwistExpansionProof.expTwist_mem_fieldsIn hE hL' hn hj hU
      fun b hb => ComplexMatrix2.traceless.smul_mem s (hB.1 b hb)
  · exact TwistExpansionProof.det_matExp_I_smul hE (ComplexMatrix2.traceless.smul_mem t (hl x))
  · have hV : IsUnit (U b) := hC.1 (U b) (hU.1 b (mem_univ b))
    have hl' : ComplexMatrix2.conjugateBy (U b) (l b.target) ∈ ComplexMatrix2.traceless :=
      (hC.2.2 (U b) hV).2.2.2.1 (hl b.target)
    have hW : (fun s t => twistedField U l B s t b) =
        TripleExpExpansion.tripleProduct (l b.source) (B b)
          (ComplexMatrix2.conjugateBy (U b) (l b.target)) (U b) := by
      funext s t
      have hm := TwistExpansionProof.mul_inv_matExp hF hV (Complex.I • t • l b.target)
      have e : U b * (Complex.I • t • l b.target) * (U b)⁻¹ =
          Complex.I • t • ComplexMatrix2.conjugateBy (U b) (l b.target) := by
        simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
      rw [e] at hm
      simp only [twistedField, PeriodicLattice.gaugeTransform, vertexExp,
        PeriodicLattice.expTwist, if_pos hb, TripleExpExpansion.tripleProduct, Pi.smul_apply]
      rw [mul_assoc (ComplexMatrix2.matExp _) (ComplexMatrix2.matExp _ * U b),
        mul_assoc (ComplexMatrix2.matExp _) (U b), hm]
      simp only [mul_assoc]
    have hP : (fun s t => principalExponent U l B s t b) =
        TripleExpExpansion.principalPart (l b.source) (B b)
          (ComplexMatrix2.conjugateBy (U b) (l b.target)) := by
      funext s t
      simp only [principalExponent, levelBracketTerm, covDiff, gaugeQuadTerm, extendOddly,
        if_pos hb, TripleExpExpansion.principalPart, smul_neg, sub_eq_add_neg]
    rw [hW, hP]
    exact hThree _ _ _ _ (hl b.source) (hB.1 b hb) hl' hV
end YangMills.Construction.Tower
