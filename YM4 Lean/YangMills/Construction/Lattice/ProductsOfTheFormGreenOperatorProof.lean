import YangMills.Construction.Lattice.DecompositionOfTheFormGreenOperatorProof
import YangMills.Construction.Lattice.DifferenceOperatorsOfTheBareLattice
import YangMills.Construction.Lattice.GaugeInvarianceOfTheConditionsOfASequence
import YangMills.Construction.Lattice.KernelOfTheSiteAverageOfASequence
import YangMills.Construction.Lattice.ProductsOfTheFormGreenOperator
import YangMills.Construction.Lattice.RepresentationOfTheGaugeProjections
import YangMills.Construction.Lattice.SiteOperatorsOfASeparatedSequenceArePositiveDefinite
import YangMills.Construction.Lattice.SymmetryOfTheDirichletSiteOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice PeriodicLattice.DirichletOperators FiniteDimReal SeparatedSequences.BaseParameters
namespace SeparatedSequences.GreenOperatorProducts
variable {D : SeparatedSequences.BaseParameters} {Ω : ℕ → Set D.Torus} {φ : BondFrame}
theorem latticeInner_comm {ι : Type} (L t : ℕ) (f g : ι → ℝ) :
    latticeInner L t f g = latticeInner L t g f := by apply _root_.YangMills.Construction.SeparatedSequences.GreenDecomposition.latticeInner_comm <;> assumption
theorem restrictedZeroInner_sub (g u v : ↥(zeroFormsOn D.K (Ω 0))) :
    D.restrictedZeroInner Ω g (u - v) =
      D.restrictedZeroInner Ω g u - D.restrictedZeroInner Ω g v := by
  have : Finite (BareSite D.L D.m D.K) := (inferInstance : Finite (D.LatticeSite 0))
  simp only [restrictedZeroInner, latticeInner]
  rw [← mul_sub, ← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
  congr 1
  refine finsum_congr fun x => ?_
  simp only [Submodule.coe_sub, Pi.sub_apply]
  ring
theorem eq_of_restrictedZeroInner_eq {X : Module.End ℝ ↥(zeroFormsOn D.K (Ω 0))}
    (hX : IsPosDefFor (D.restrictedZeroInner Ω) X) {u v : ↥(zeroFormsOn D.K (Ω 0))}
    (h : ∀ g, D.restrictedZeroInner Ω g u = D.restrictedZeroInner Ω g v) : u = v := by
  by_contra hne
  have hpos := hX.2 (u - v) (sub_ne_zero.2 hne)
  rw [hX.1, restrictedZeroInner_sub, h, sub_self] at hpos
  exact lt_irrefl _ hpos
theorem restrictedZeroInner_comm (u v : ↥(zeroFormsOn D.K (Ω 0))) :
    D.restrictedZeroInner Ω u v = D.restrictedZeroInner Ω v u :=
  latticeInner_comm _ _ _ _
theorem restrictedOneInner_comm (A B : ↥(oneFormsOn D.K (Ω 0) φ)) :
    D.restrictedOneInner Ω φ A B = D.restrictedOneInner Ω φ B A := by apply _root_.YangMills.Construction.SeparatedSequences.GreenDecomposition.restrictedOneInner_comm <;> assumption
theorem of_properties (hR : D.MassiveOperatorsRelation Ω φ)
    (hK : D.AverageKernelProperties Ω φ) (hG : D.GaugeFixingProperties Ω φ)
    (hP : D.GaugeProjectionFormulas Ω) (hS : D.ZeroFormSymmetries Ω)
    (hT : D.MassiveOneOperatorForms Ω φ)
    (hpos : IsPosDefFor (D.restrictedZeroInner Ω) (D.massiveZeroOperator Ω))
    (hunit : IsUnit (D.massiveZeroOperator Ω))
    (hQ : IsAdjointFor (D.restrictedOneInner Ω φ) (D.coarseOneInner Ω φ)
      (D.averageOne Ω φ) (D.averageOneAdjoint Ω φ))
    (hd : BareLatticeOperators.DirichletGradAdjointIdentity D.K D.t (Ω 0)) :
    D.OneGreenProducts Ω φ := by
  have hdadj : ∀ (A : D.RegionOneForms Ω φ) (f : D.RegionZeroForms Ω),
      D.restrictedOneInner Ω φ A (D.regionGrad Ω φ f) =
        D.restrictedZeroInner Ω (D.regionGradAdjoint Ω φ A) f := fun A f => hd φ f A
  have hGdR : ∀ f, D.oneGreen Ω φ (D.regionGrad Ω φ (D.gaugeRangeProjection Ω f)) =
      D.regionGrad Ω φ (D.zeroGreen Ω (D.gaugeRangeProjection Ω f)) :=
    fun f => LinearMap.congr_fun hR.green_grad_range f
  have hmem : ∀ f, D.zeroGreen Ω (D.gaugeRangeProjection Ω f) ∈ D.averageZeroKernel Ω := fun f => by
    rw [← hP.range_green_comp_range]
    exact ⟨f, rfl⟩
  have hinv : ∀ f, D.massiveZeroOperator Ω (D.zeroGreen Ω f) = f := fun f =>
    LinearMap.congr_fun (Ring.mul_inverse_cancel _ hunit) f
  have hright : ∀ f, D.regionGradAdjoint Ω φ (D.oneGreen Ω φ
      (D.regionGrad Ω φ (D.gaugeRangeProjection Ω f))) = D.gaugeRangeProjection Ω f := fun f => by
    rw [hGdR]
    refine Eq.trans (Subtype.ext ?_) (hinv (D.gaugeRangeProjection Ω f))
    rw [hK.gradAdjoint_grad_eq _ (hmem f), hK.massive_eq _ (hmem f)]
  have haverage : ∀ f, D.averageOne Ω φ (D.oneGreen Ω φ
      (D.regionGrad Ω φ (D.gaugeRangeProjection Ω f))) = 0 := fun f => by
    rw [hGdR]
    exact hG.average_grad _ (hmem f)
  have hmove : ∀ (g : D.RegionZeroForms Ω) (A : D.RegionOneForms Ω φ),
      D.restrictedZeroInner Ω g (D.gaugeRangeProjection Ω
        (D.regionGradAdjoint Ω φ (D.oneGreen Ω φ A))) =
      D.restrictedOneInner Ω φ
        (D.oneGreen Ω φ (D.regionGrad Ω φ (D.gaugeRangeProjection Ω g))) A := fun g A => by
    rw [hS.gaugeRange_symm g, restrictedZeroInner_comm (D.gaugeRangeProjection Ω g), ← hdadj,
      restrictedOneInner_comm (D.oneGreen Ω φ A), hT.green_symm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun f => eq_of_restrictedZeroInner_eq hpos fun g => ?_
    simp only [LinearMap.comp_apply]
    rw [hmove, hdadj, hright, restrictedZeroInner_comm (D.gaugeRangeProjection Ω g) f,
      hS.gaugeRange_symm f g]
    exact restrictedZeroInner_comm _ _
  · exact LinearMap.ext hright
  · refine LinearMap.ext fun B => eq_of_restrictedZeroInner_eq hpos fun g => ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    have hz : D.restrictedZeroInner Ω g 0 = 0 := by simp [restrictedZeroInner, latticeInner]
    have hzB : D.coarseOneInner Ω φ B 0 = 0 := by
      have h := hQ 0 B
      rw [map_zero] at h
      rw [h]
      simp [restrictedOneInner, latticeInner]
    rw [hmove, restrictedOneInner_comm, ← hQ, haverage, hz, hzB]
  · exact LinearMap.ext haverage
theorem holds (hRelation : MassiveOperatorsRelatedByDifferential)
    (hKernel : SequenceDatum.AverageKernelPropertiesHold)
    (hGauge : SequenceConditionsGaugeInvariant)
    (hRepresentation : GaugeProjections.RepresentationStatement)
    (hSymmetry : DirichletSiteOperatorsSymmetric)
    (hTwoForms : MassiveOneOperatorHasTwoForms)
    (hSite : SiteOperatorPositivity.AllSiteOperatorsPositive)
    (hAdjoints : AdjointsAndProjections.Statement)
    (hDifference : BareLatticeOperators.Statement) : Statement := by
  intro S φ
  obtain ⟨-, -, -, -, hframe⟩ := hDifference S.toBaseParameters
  obtain ⟨-, hd, -, -, -⟩ := hframe (S.region 0)
  exact of_properties (hRelation S φ) (hKernel S φ) (hGauge S φ) (hRepresentation S)
    (hSymmetry S) (hTwoForms S φ) (hSite S).massivePosDef (hSite S).massiveIsUnit
    (hAdjoints S.toBaseParameters S.region φ).one_adjoint hd
end SeparatedSequences.GreenOperatorProducts
end YangMills.Construction
end
