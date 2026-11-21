import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.Lattice.SumOfARealBondFunctionRoundAPlaquette
import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
import YangMills.Construction.Matrices.RestatedElementaryInequalities
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
theorem realBondSumAroundPlaquetteBound_holds
    (hE : ComplexMatrix2.RestatedElementaryInequalitiesStatement) :
    RealBondSumAroundPlaquetteBound := by
  intro L hL m K n hm hn Z a hreal hsup q hq
  obtain ⟨ha, -, -, -, -, -, he⟩ := hE
  have hL13 : 13 ≤ L := hL.2
  have hLpos : 0 < L := by omega
  have hLtwo : 2 ≤ L := by omega
  have hj : -(m : ℤ) < levelDepth K n := by
    have hnK : (n : ℤ) ≤ K := by exact_mod_cast hn
    have hmpos : (0 : ℤ) < m := by exact_mod_cast hm
    simp only [levelDepth]
    omega
  have hsites : Finite (Site L m (levelDepth K n)) :=
    (SeparatedSequence.sublattice_finite hLpos hj.le).to_subtype
  have hbonds : Finite (BondAtLevel L m K n) :=
    Finite.of_injective (fun b : BondAtLevel L m K n => (b.source, b.target))
      (fun b b' h => Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  have hbdd : BddAbove
      (Set.range fun i : PositiveBondsOf (bondsWithin Z) =>
        ComplexMatrix2.operatorNorm (a i : ComplexMatrix2)) :=
    (Set.finite_range _).bddAbove
  set A := LieBondField.matrixValues a with hA
  set σ := supOperatorNorm a with hσ
  have key : ∀ b : BondAtLevel L m K n, b.LiesIn Z → b.IsPositivelyOriented →
      A b ∈ ComplexMatrix2.hermitianTraceless ∧ ComplexMatrix2.operatorNorm (A b) ≤ σ ∧
      A b.opposite = -A b ∧
      expTwist A trivialGaugeField b = ComplexMatrix2.matExp (Complex.I • A b) ∧
      expTwist A trivialGaugeField b.opposite =
        ComplexMatrix2.matExp (-(Complex.I • A b)) := by
    intro b hin hpos
    have hnot : ¬ b.opposite.IsPositivelyOriented := by
      rcases MatrixValued.xor_isPositivelyOriented_opposite hLtwo hj b with h | h
      · exact h.2
      · exact absurd hpos h.2
    let i : PositiveBondsOf (bondsWithin Z) := ⟨b, hin, hpos⟩
    have hv : A b = (a i : ComplexMatrix2) := by
      show ((a.eval b : ↥ComplexMatrix2.traceless) : ComplexMatrix2) = _
      rw [show a.eval b = a i from a.eval_of_positive i]
    refine ⟨hv ▸ hreal i, ?_, ?_, ?_, ?_⟩
    · rw [hv]
      exact le_ciSup hbdd i
    · show ((a.eval b.opposite : ↥ComplexMatrix2.traceless) : ComplexMatrix2) = _
      rw [show a.eval b.opposite = -a i from a.eval_opposite i hnot, hv]
      rfl
    · simp only [expTwist, if_pos hpos, trivialGaugeField, mul_one]
    · simp only [expTwist, if_neg hnot, trivialGaugeField, mul_one]
      exact (Matrix.exp_neg _).symm
  have hbd := hq.boundaryBonds_liesIn
  have h1 := hbd (Bond.forwardFrom q.origin q.firstAxis) (by simp [Plaquette.boundaryBonds])
  have h2 := hbd (Bond.forwardFrom (q.origin + unitStep L m (levelDepth K n) q.firstAxis)
    q.secondAxis) (by simp [Plaquette.boundaryBonds])
  have h3 := hbd (Bond.forwardFrom (q.origin + unitStep L m (levelDepth K n) q.secondAxis)
    q.firstAxis).opposite (by simp [Plaquette.boundaryBonds])
  have h4 := hbd (Bond.forwardFrom q.origin q.secondAxis).opposite
    (by simp [Plaquette.boundaryBonds])
  have pos : ∀ (x : SiteAtLevel L m K n) (μ : Fin 4),
      (Bond.forwardFrom x μ).IsPositivelyOriented :=
    fun x μ => ⟨μ, by simp [Bond.forwardFrom]⟩
  obtain ⟨s1, n1, -, e1, -⟩ := key _ h1 (pos _ _)
  obtain ⟨s2, n2, -, e2, -⟩ := key _ h2 (pos _ _)
  obtain ⟨s3, n3, r3, -, e3⟩ := key _ ⟨h3.2, h3.1⟩ (pos _ _)
  obtain ⟨s4, n4, r4, -, e4⟩ := key _ ⟨h4.2, h4.1⟩ (pos _ _)
  have hsumA : bondFormSumAlong A q.boundaryBonds =
      A (Bond.forwardFrom q.origin q.firstAxis) +
        A (Bond.forwardFrom (q.origin + unitStep L m (levelDepth K n) q.firstAxis) q.secondAxis) -
        A (Bond.forwardFrom (q.origin + unitStep L m (levelDepth K n) q.secondAxis) q.firstAxis) -
        A (Bond.forwardFrom q.origin q.secondAxis) := by
    simp only [bondFormSumAlong, Plaquette.boundaryBonds, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, r3, r4]
    abel
  have hprodE : plaquetteHolonomy (expTwist A trivialGaugeField) q =
      ComplexMatrix2.expListProduct ![Complex.I • A (Bond.forwardFrom q.origin q.firstAxis),
        Complex.I • A (Bond.forwardFrom (q.origin + unitStep L m (levelDepth K n) q.firstAxis)
          q.secondAxis),
        -(Complex.I • A (Bond.forwardFrom (q.origin + unitStep L m (levelDepth K n) q.secondAxis)
          q.firstAxis)),
        -(Complex.I • A (Bond.forwardFrom q.origin q.secondAxis))] := by
    simp only [plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, e1, e2, e3, e4]
    simp [ComplexMatrix2.expListProduct, List.ofFn_succ]
  rw [hprodE, hsumA]
  generalize A (Bond.forwardFrom q.origin q.firstAxis) = c₁ at *
  generalize A (Bond.forwardFrom (q.origin + unitStep L m (levelDepth K n) q.firstAxis)
    q.secondAxis) = c₂ at *
  generalize A (Bond.forwardFrom (q.origin + unitStep L m (levelDepth K n) q.secondAxis)
    q.firstAxis) = c₃ at *
  generalize A (Bond.forwardFrom q.origin q.secondAxis) = c₄ at *
  set X : Fin 4 → ComplexMatrix2 :=
    ![Complex.I • c₁, Complex.I • c₂, -(Complex.I • c₃), -(Complex.I • c₄)] with hX
  set Y : ComplexMatrix2 := c₁ + c₂ - c₃ - c₄ with hYdef
  have hnI : ∀ c : ComplexMatrix2,
      ComplexMatrix2.operatorNorm (Complex.I • c) = ComplexMatrix2.operatorNorm c := fun c => by
    simp [ComplexMatrix2.operatorNorm, norm_smul]
  have hnIneg : ∀ c : ComplexMatrix2,
      ComplexMatrix2.operatorNorm (-(Complex.I • c)) = ComplexMatrix2.operatorNorm c :=
    fun c => by
      simp [ComplexMatrix2.operatorNorm, norm_smul]
  have hsumX : ∑ j, X j = Complex.I • Y := by
    simp only [hX, hYdef, Fin.sum_univ_four]
    simp only [Matrix.cons_val]
    simp only [smul_sub, smul_add]
    abel
  have hnorms : ∑ j, ComplexMatrix2.operatorNorm (X j) =
      ComplexMatrix2.operatorNorm c₁ + ComplexMatrix2.operatorNorm c₂ +
        ComplexMatrix2.operatorNorm c₃ + ComplexMatrix2.operatorNorm c₄ := by
    simp only [hX, Fin.sum_univ_four]
    simp only [Matrix.cons_val, hnI, hnIneg]
  have hσ0 : 0 ≤ σ := le_trans (norm_nonneg _) n1
  have hn4 : ∑ j, ComplexMatrix2.operatorNorm (X j) ≤ 4 * σ := by rw [hnorms]; linarith
  have hn0 : 0 ≤ ∑ j, ComplexMatrix2.operatorNorm (X j) :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcmp := ((ha 4 le_rfl X).1 (by linarith)).2
  rw [hsumX] at hcmp
  have hYn : ComplexMatrix2.operatorNorm Y ≤ 4 * σ := by
    have : ComplexMatrix2.operatorNorm Y ≤
        ComplexMatrix2.operatorNorm c₁ + ComplexMatrix2.operatorNorm c₂ +
          ComplexMatrix2.operatorNorm c₃ + ComplexMatrix2.operatorNorm c₄ := by
      simp only [hYdef, ComplexMatrix2.operatorNorm]
      calc ‖c₁ + c₂ - c₃ - c₄‖ ≤ ‖c₁ + c₂ - c₃‖ + ‖c₄‖ := norm_sub_le _ _
        _ ≤ ‖c₁ + c₂‖ + ‖c₃‖ + ‖c₄‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ ‖c₁‖ + ‖c₂‖ + ‖c₃‖ + ‖c₄‖ := by gcongr; exact norm_add_le _ _
    linarith
  have hYmem : Y ∈ ComplexMatrix2.hermitianTraceless :=
    ComplexMatrix2.hermitianTraceless.sub_mem
      (ComplexMatrix2.hermitianTraceless.sub_mem
        (ComplexMatrix2.hermitianTraceless.add_mem s1 s2) s3) s4
  have hpi : ComplexMatrix2.operatorNorm Y ≤ Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hcube := he Y hYmem hpi
  have htri : ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp (Complex.I • Y) - 1) ≤
      ComplexMatrix2.operatorNorm (ComplexMatrix2.expListProduct X - 1) +
        ComplexMatrix2.operatorNorm
          (ComplexMatrix2.expListProduct X - ComplexMatrix2.matExp (Complex.I • Y)) := by
    have : ComplexMatrix2.matExp (Complex.I • Y) - 1 = (ComplexMatrix2.expListProduct X - 1) -
        (ComplexMatrix2.expListProduct X - ComplexMatrix2.matExp (Complex.I • Y)) := by abel
    rw [this]
    exact norm_sub_le _ _
  have hsq : (∑ j, ComplexMatrix2.operatorNorm (X j)) ^ 2 ≤ (4 * σ) ^ 2 := by gcongr
  have hYn0 : 0 ≤ ComplexMatrix2.operatorNorm Y := norm_nonneg _
  have hY3 : ComplexMatrix2.operatorNorm Y ^ 3 ≤ (4 * σ) ^ 3 := by gcongr
  have hσ3 : σ ^ 3 ≤ 1 / 4 * σ ^ 2 := by nlinarith [mul_nonneg hσ0 hσ0]
  nlinarith [mul_nonneg hσ0 hσ0]
end YangMills.Construction.PeriodicLattice
end
