import YangMills.Construction.TransferOperators.GaugeAveragesOfFunctionsOfLayersProof
import YangMills.Construction.TransferOperators.ReversalInvarianceOnTheSymmetricStackOfTwoLayers
import YangMills.Construction.TransferOperators.TwoLayerPrinciple
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics
noncomputable section
namespace YangMills.Construction.TransferOperators.ReversalInvariantTwoLevel
variable {μ : Fin 4}
def spannedBlock (v : Set (SliceSite μ)) [Finite v] (hne : (linksWithin v).Nonempty) :
    Block μ where
  links := (linksWithin_finite v).toFinset
  links_nonempty := (Set.Finite.toFinset_nonempty _).2 hne
variable (v : Set (SliceSite μ)) [Finite v] (hne : (linksWithin v).Nonempty)
theorem link_mem_spannedBlock (i : ℤ) (p : centeredLinkPairs i 1 v) :
    p.1.2 ∈ (spannedBlock v hne).links :=
  (Set.Finite.mem_toFinset _).2 p.2.2.2
def twoLevelAssignment (i : ℤ)
    (u w : (spannedBlock v hne).links → Matrices.ComplexMatrix2.specialUnitary) :
    centeredLinkPairs i 1 v → Matrices.ComplexMatrix2.specialUnitary :=
  fun p => if p.1.1 = i then u ⟨p.1.2, link_mem_spannedBlock v hne i p⟩
    else w ⟨p.1.2, link_mem_spannedBlock v hne i p⟩
theorem continuous_twoLevelAssignment (i : ℤ) :
    Continuous fun x : ((spannedBlock v hne).links → Matrices.ComplexMatrix2.specialUnitary) ×
        ((spannedBlock v hne).links → Matrices.ComplexMatrix2.specialUnitary) =>
      twoLevelAssignment v hne i x.1 x.2 := by
  refine continuous_pi fun p => ?_
  by_cases h : p.1.1 = i
  · simp only [twoLevelAssignment, if_pos h]
    exact (continuous_apply _).comp continuous_fst
  · simp only [twoLevelAssignment, if_neg h]
    exact (continuous_apply _).comp continuous_snd
variable {v hne}
open Classical in
def extendByOne (g : (spannedBlock v hne).vertices → Matrices.ComplexMatrix2.specialUnitary)
    (y : v) : Matrices.ComplexMatrix2.specialUnitary :=
  if h : (y : SliceSite μ) ∈ (spannedBlock v hne).vertices then g ⟨y, h⟩ else 1
theorem extendByOne_apply (g : (spannedBlock v hne).vertices → Matrices.ComplexMatrix2.specialUnitary)
    (y : v) (h : (y : SliceSite μ) ∈ (spannedBlock v hne).vertices) :
    extendByOne g y = g ⟨y, h⟩ :=
  dif_pos h
theorem twoLevelAssignment_gaugeAct (i : ℤ)
    (g : (spannedBlock v hne).vertices → Matrices.ComplexMatrix2.specialUnitary)
    (u w : (spannedBlock v hne).links → Matrices.ComplexMatrix2.specialUnitary) :
    twoLevelAssignment v hne i (gaugeAct (spannedBlock v hne).links_subset_linksWithin g u)
        (gaugeAct (spannedBlock v hne).links_subset_linksWithin g w) =
      diagonalGaugeAct (snd_mem_linksWithin i 1 v) (extendByOne g)
        (twoLevelAssignment v hne i u w) := by
  funext p
  have hs : p.1.2.source ∈ (spannedBlock v hne).vertices :=
    ⟨p.1.2, link_mem_spannedBlock v hne i p, Or.inl rfl⟩
  have ht : p.1.2.target ∈ (spannedBlock v hne).vertices :=
    ⟨p.1.2, link_mem_spannedBlock v hne i p, Or.inr rfl⟩
  simp only [diagonalGaugeAct]
  rw [extendByOne_apply g _ hs, extendByOne_apply g _ ht]
  by_cases h : p.1.1 = i
  · simp only [twoLevelAssignment, if_pos h, gaugeAct]
  · simp only [twoLevelAssignment, if_neg h, gaugeAct]
def antisymmetrization (i : ℤ)
    (Ψ : (centeredLinkPairs i 1 v → Matrices.ComplexMatrix2.specialUnitary) → ℂ)
    (hc : Continuous Ψ) :
    C(((spannedBlock v hne).links → Matrices.ComplexMatrix2.specialUnitary) ×
      ((spannedBlock v hne).links → Matrices.ComplexMatrix2.specialUnitary), ℝ) where
  toFun x := (Ψ (twoLevelAssignment v hne i x.1 x.2)).re -
    (Ψ (twoLevelAssignment v hne i x.2 x.1)).re
  continuous_toFun := by
    have h₁ := continuous_twoLevelAssignment v hne i
    have h₂ : Continuous fun x : ((spannedBlock v hne).links →
        Matrices.ComplexMatrix2.specialUnitary) ×
        ((spannedBlock v hne).links → Matrices.ComplexMatrix2.specialUnitary) =>
        twoLevelAssignment v hne i x.2 x.1 :=
      h₁.comp continuous_swap
    exact (Complex.continuous_re.comp (hc.comp h₁)).sub (Complex.continuous_re.comp (hc.comp h₂))
theorem ofConsecutive_eq_centeredStack (i : ℤ) :
    Stack.ofConsecutive i = centeredStack i 1 le_rfl := by
  simp [Stack.ofConsecutive, centeredStack]
theorem continuous_transportedLinkVariable (S : Stack) (j : ℤ) (b : SliceLink μ) :
    Continuous fun U : InfiniteLattice.GaugeField 1 => S.transportedLinkVariable μ U j b := by apply _root_.YangMills.Construction.TransferOperators.SliceMean.continuous_transportedLinkVariable <;> assumption
theorem reversalInvariantTwoLevelStatement_holds (hTwo : TwoLevelPrinciple.Statement) :
    ReversalInvariantTwoLevelStatement := by
  intro μ β hβ ν hν i v _ Ψ hne hΨ hinv
  have hprob : IsProbabilityMeasure ν := hν.1.1
  have hc : Continuous Ψ := hΨ.1.continuous
  let T : InfiniteLattice.GaugeField 1 → centeredLinkPairs i 1 v →
      Matrices.ComplexMatrix2.specialUnitary := fun U p =>
    (centeredStack i 1 le_rfl).transportedLinkVariable μ U p.1.1 p.1.2
  have hT : Continuous T := continuous_pi fun p => continuous_transportedLinkVariable _ _ _
  have hlevel : ∀ p : centeredLinkPairs i 1 v, p.1.1 ≠ i → p.1.1 = i + 1 := by
    intro p h
    have h₁ := p.2.1
    have h₂ := p.2.2.1
    omega
  have h₁ : ∀ U, twoLevelAssignment v hne i
      ((Stack.ofConsecutive i).blockValues (spannedBlock v hne) U i)
      ((Stack.ofConsecutive i).blockValues (spannedBlock v hne) U (i + 1)) = T U := by
    intro U
    funext p
    by_cases h : p.1.1 = i
    · simp only [twoLevelAssignment, T, h, ofConsecutive_eq_centeredStack]
      rfl
    · simp only [twoLevelAssignment, if_neg h, T, ofConsecutive_eq_centeredStack]
      rw [hlevel p h]
      rfl
  have h₂ : ∀ U, twoLevelAssignment v hne i
      ((Stack.ofConsecutive i).blockValues (spannedBlock v hne) U (i + 1))
      ((Stack.ofConsecutive i).blockValues (spannedBlock v hne) U i) =
        fun p => T U (reflectPair i 1 v p) := by
    intro U
    funext p
    by_cases h : p.1.1 = i
    · have hm : reflectedLevel i p.1.1 = i + 1 := by
        simp only [reflectedLevel]
        omega
      simp only [twoLevelAssignment, if_pos h, T, reflectPair, hm, ofConsecutive_eq_centeredStack]
      rfl
    · have hm : reflectedLevel i p.1.1 = i := by
        have := hlevel p h
        simp only [reflectedLevel]
        omega
      simp only [twoLevelAssignment, if_neg h, T, reflectPair, hm, ofConsecutive_eq_centeredStack]
      rfl
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hint₁ : Integrable (fun U => Ψ (T U)) ν :=
    Integrable.of_bound (hc.comp hT).measurable.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun U => hC _ (Set.mem_univ _))
  have hrev : Continuous fun U => levelReversal i 1 v Ψ (T U) := by
    refine hc.comp (continuous_pi fun p => ?_)
    exact (continuous_apply _).comp hT
  have hint₂ : Integrable (fun U => levelReversal i 1 v Ψ (T U)) ν :=
    Integrable.of_bound hrev.measurable.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun U => hC _ (Set.mem_univ _))
  have hreal : ∀ x, (((Ψ x).re : ℝ) : ℂ) = Ψ x := fun x =>
    Complex.ext rfl (by simp [hΨ.2 x])
  have hzero := hTwo β hβ μ ν hν (spannedBlock v hne) i (antisymmetrization i Ψ hc)
    (fun g u w => by
      change (Ψ _).re - (Ψ _).re = (Ψ _).re - (Ψ _).re
      rw [twoLevelAssignment_gaugeAct, twoLevelAssignment_gaugeAct, hinv, hinv])
    (fun u w => by
      change (Ψ _).re - (Ψ _).re = -((Ψ _).re - (Ψ _).re)
      ring)
  have hF : ∀ U, (((antisymmetrization i Ψ hc)
      ((Stack.ofConsecutive i).blockValues (spannedBlock v hne) U i,
        (Stack.ofConsecutive i).blockValues (spannedBlock v hne) U (i + 1)) : ℝ) : ℂ) =
      Ψ (T U) - levelReversal i 1 v Ψ (T U) := by
    intro U
    change (((Ψ _).re - (Ψ _).re : ℝ) : ℂ) = _
    rw [h₁, h₂, Complex.ofReal_sub, hreal, hreal]
    rfl
  simp only [stateEval] at hzero
  have hzero' : ∫ U, (((antisymmetrization i Ψ hc)
      ((Stack.ofConsecutive i).blockValues (spannedBlock v hne) U i,
        (Stack.ofConsecutive i).blockValues (spannedBlock v hne) U (i + 1)) : ℝ) : ℂ) ∂ν = 0 := by
    rw [integral_complex_ofReal, hzero, Complex.ofReal_zero]
  simp only [hF] at hzero'
  rw [integral_sub hint₁ hint₂] at hzero'
  exact sub_eq_zero.1 hzero'
end YangMills.Construction.TransferOperators.ReversalInvariantTwoLevel
end
