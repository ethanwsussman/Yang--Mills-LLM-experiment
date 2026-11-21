import YangMills.Construction.Lattice.GaugeCovarianceOfTheIteratesOfTheSchemes
import YangMills.Construction.Lattice.GaugeCovarianceOfTheTwoSchemes
import YangMills.Construction.Lattice.LieFieldsOnBondSets
import YangMills.Construction.Lattice.SchemeAverageDependsOnTheDoubleBlockAlone
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
private theorem opposite_isPositivelyOriented_of_not {L m : ℕ} {j : ℤ} {c : Bond L m j}
    (hc : ¬c.IsPositivelyOriented) : c.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.Bond.opposite_isPositivelyOriented <;> assumption
private theorem schemeBlockAverage_of_not_isPositivelyOriented {L m : ℕ} {j j' : ℤ}
    (s : AveragingScheme) (W : Bond L m j' → Matrices.ComplexMatrix2) {c : Bond L m j}
    (hc : ¬c.IsPositivelyOriented) :
    schemeBlockAverage s W c = (schemeBlockAverage s W c.opposite)⁻¹ := by
  unfold schemeBlockAverage
  rw [if_neg hc, if_pos (opposite_isPositivelyOriented_of_not hc)]
private theorem schemeBlockAverage_of_eqOn_gaugeTransform
    (hcov : GaugeCovarianceStatement)
    (hloc : OneStepAverageIsLocal)
    {L m K n : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (s : AveragingScheme)
    {c : BondAtLevel L m K (n + 1)} (hc : c.IsPositivelyOriented)
    (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2)
    (hg : ∀ x, g x ∈ compactGaugeGroup) (W W' : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (hf : IsOneStepAverageFormed s W c)
    (heq : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
      W' b = gaugeTransform g W b) :
    IsOneStepAverageFormed s W' c ∧
      schemeBlockAverage s W' c =
        g (schemeBaseSite s (levelDepth K n) c.source) * schemeBlockAverage s W c *
          (g (schemeBaseSite s (levelDepth K n) c.target))⁻¹ := by
  have hW : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W := hf.1
  obtain ⟨hgf, hgv⟩ := (hcov L hL m K n hm hn s c hc g W (fun x _ => hg x) hW).average hf
  have hG : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) (gaugeTransform g W) := hgf.1
  have hopp : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
      b.opposite ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) :=
    fun b hb => ⟨hb.2, hb.1⟩
  have hW' : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W' := by
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · rw [heq b hb]
      exact hG.1 b hb
    · rw [heq b hb, heq _ (hopp b hb)]
      exact hG.2 b hb
  obtain ⟨hiff, hval⟩ := hloc L hL m K n hm hn s c hc (gaugeTransform g W) W' hG hW'
    (fun b hb => (heq b hb).symm)
  refine ⟨hiff.1 hgf, ?_⟩
  have e : oneStepAverage s (gaugeTransform g W) c = oneStepAverage s W' c :=
    (hval hgf).1
  exact e.symm.trans hgv
theorem iteratedAverage_gaugeCovariant
    (hcov : GaugeCovarianceStatement)
    (hloc : OneStepAverageIsLocal) :
    IteratedAverageGaugeCovariance := by
  intro L hL K m _ hm s j hj U _ u hu
  induction j with
  | zero => exact fun c _ => ⟨trivial, rfl⟩
  | succ n ih =>
    intro c hdef
    have ih' := ih (by omega)
    have hdef' : (∀ b ∈ (bondsInDoubleBlock c.positivelyOriented : Set (BondAtLevel L m K n)),
          IsBareIterateDefined s U n b) ∧
        IsOneStepAverageFormed s (iteratedAverage s n U) c.positivelyOriented := hdef
    have hpos : c.positivelyOriented.IsPositivelyOriented := by
      by_cases hc : c.IsPositivelyOriented
      · rw [Bond.positivelyOriented, if_pos hc]
        exact hc
      · rw [Bond.positivelyOriented, if_neg hc]
        exact opposite_isPositivelyOriented_of_not hc
    have key := schemeBlockAverage_of_eqOn_gaugeTransform hcov hloc hL hm (show n < K by omega)
      s hpos (fun y => u (finestBaseSite s K n y)) (fun x => hu _) (iteratedAverage s n U)
      (iteratedAverage s n (gaugeTransform u U)) hdef'.2
      (fun b hb => (ih' b (hdef'.1 b hb)).2)
    have hdefined : IsBareIterateDefined s (gaugeTransform u U) (n + 1) c :=
      ⟨fun b hb => (ih' b (hdef'.1 b hb)).1, key.1⟩
    refine ⟨hdefined, ?_⟩
    change schemeBlockAverage s (iteratedAverage s n (gaugeTransform u U)) c =
      u (finestBaseSite s K (n + 1) c.source) * schemeBlockAverage s (iteratedAverage s n U) c *
        (u (finestBaseSite s K (n + 1) c.target))⁻¹
    by_cases hc : c.IsPositivelyOriented
    · have e : c.positivelyOriented = c := if_pos hc
      rw [e] at key
      exact key.2
    · have e : c.positivelyOriented = c.opposite := if_neg hc
      rw [e] at key
      have hval : schemeBlockAverage s (iteratedAverage s n (gaugeTransform u U)) c.opposite =
          u (finestBaseSite s K (n + 1) c.target) *
            schemeBlockAverage s (iteratedAverage s n U) c.opposite *
            (u (finestBaseSite s K (n + 1) c.source))⁻¹ := key.2
      have hdet : IsUnit (u (finestBaseSite s K (n + 1) c.source)).det := by
        rw [(Matrix.mem_specialUnitaryGroup_iff.1 (hu _)).2]
        exact isUnit_one
      rw [schemeBlockAverage_of_not_isPositivelyOriented s _ hc,
        schemeBlockAverage_of_not_isPositivelyOriented s _ hc, hval,
        Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdet, mul_assoc]
end YangMills.Construction.PeriodicLattice
