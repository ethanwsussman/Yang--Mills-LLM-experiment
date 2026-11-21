import YangMills.Construction.PassageToTheLimit.LatticeFunctionalsAreBoundedForms
import YangMills.Construction.PassageToTheLimit.SpacesOfTestFunctionsProductsAndSeparatedTuples
import YangMills.Construction.ReflectionPositivity.CentredMomentsAreSumsOfCumulants
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import YangMills.Construction.SystemOfAdmissibleConstants.TentsOfASmallSideProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.LimitSpaces
namespace BoundedForms
open ReflectionPositivity.CutoffMirrors
abbrev gibbs (D : MirrorData) : Measure D.BondField :=
  PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling
theorem uniformNorm_nonneg {X : Type*} (u : X → ℝ) : 0 ≤ TestFunctions.uniformNorm u :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem norm_le_uniformNorm {X : Type*} {u : X → ℝ} (hu : TestFunctions.IsBoundedFun u) (x : X) :
    ‖u x‖ ≤ TestFunctions.uniformNorm u := by apply _root_.YangMills.SharedProofs.p10108 <;> assumption
section Measure
variable {D : MirrorData} (hA : D.FieldSpaceIsProduct) (hC : D.EnergiesBoundedAndMeasureProbability)
include hA in
theorem opensMeasurableSpace_bondField : OpensMeasurableSpace D.BondField := by
  have := hA.2.1
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  infer_instance
include hA in
theorem measurableSet_compactGaugeFields :
    MeasurableSet (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) := by
  have hB := opensMeasurableSpace_bondField hA
  obtain ⟨-, -, -, hbij, hc, -, htop, -, -, -⟩ := hA
  have hind : Topology.IsInducing D.positiveEdgeValues := ⟨htop.symm⟩
  let e : D.FieldSpace ≃ₜ (D.PositiveEdge → Matrices.ComplexMatrix2.specialUnitary) :=
    (Equiv.ofBijective _ hbij).toHomeomorphOfIsInducing hind
  have hcs : CompactSpace D.FieldSpace := e.symm.compactSpace
  have hK : IsCompact (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) :=
    isCompact_iff_compactSpace.mpr hcs
  exact hK.isClosed.measurableSet
include hC in
theorem isProbabilityMeasure_gibbs : IsProbabilityMeasure (gibbs D) :=
  hC.2.2.2.2.2.2.2.2.2.2.1
include hA hC in
theorem ae_mem_compactGaugeFields :
    ∀ᵐ U ∂gibbs D, U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hp, hpc⟩ := hC
  have hS := measurableSet_compactGaugeFields hA
  have hu : D.gibbsMeasureOnFields univ = 1 := measure_univ
  rw [MirrorData.gibbsMeasureOnFields,
    (MeasurableEmbedding.subtype_coe hS).comap_apply] at hu
  have h1 : PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling
      (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) = 1 := by
    simpa using hu
  exact mem_ae_iff.mpr ((prob_compl_eq_zero_iff hS).mpr h1)
include hA hC in
theorem aestronglyMeasurable_smeared (u : D.Torus → ℝ) :
    AEStronglyMeasurable (PeriodicLattice.smearedObservable u) (gibbs D) := by
  have hS := measurableSet_compactGaugeFields hA
  have hae := ae_mem_compactGaugeFields hA hC
  obtain ⟨hcont, -⟩ := hC.2.1 u
  have htop := hA.2.2.2.2.2.2.1
  have hc : Continuous fun U : D.FieldSpace => PeriodicLattice.smearedObservable u U.1 := by
    have h := hcont
    rw [MirrorData.ContinuousForProduct, htop] at h
    exact h
  have := opensMeasurableSpace_bondField hA
  have hm : Measurable fun U : D.FieldSpace => PeriodicLattice.smearedObservable u U.1 :=
    hc.measurable
  have hX : Measurable (Function.extend (Subtype.val : D.FieldSpace → D.BondField)
      (fun U : D.FieldSpace => PeriodicLattice.smearedObservable u U.1) 0) :=
    (MeasurableEmbedding.subtype_coe hS).measurable_extend hm measurable_const
  refine hX.aestronglyMeasurable.congr ?_
  filter_upwards [hae] with U hU
  exact Subtype.val_injective.extend_apply _ _ (⟨U, hU⟩ : D.FieldSpace)
include hA hC in
theorem ae_norm_smeared_le {u : D.Torus → ℝ} (hu : TestFunctions.IsBoundedFun u) :
    ∀ᵐ U ∂gibbs D, ‖PeriodicLattice.smearedObservable u U‖ ≤
      2 * (D.faceCount : ℝ) * TestFunctions.uniformNorm u := by
  filter_upwards [ae_mem_compactGaugeFields hA hC] with U hU
  have := hA.2.2.1
  have := Fintype.ofFinite D.Face
  have e : PeriodicLattice.smearedObservable u U = ∑ p : D.Face,
      PeriodicLattice.plaquetteCost U p • u p.barycenter := finsum_eq_sum_of_fintype _
  rw [e]
  calc ‖∑ p : D.Face, PeriodicLattice.plaquetteCost U p • u p.barycenter‖
      ≤ ∑ _p : D.Face, 2 * TestFunctions.uniformNorm u := by
        refine norm_sum_le_of_le _ fun p _ => ?_
        have ha := (hC.1 p).2 ⟨U, hU⟩
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1]
        exact mul_le_mul ha.2 (norm_le_uniformNorm hu _) (norm_nonneg _) (by norm_num)
    _ = 2 * (D.faceCount : ℝ) * TestFunctions.uniformNorm u := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, MirrorData.faceCount,
          Nat.card_eq_fintype_card]
        ring
include hA hC in
theorem integrable_smeared {u : D.Torus → ℝ} (hu : TestFunctions.IsBoundedFun u) :
    Integrable (PeriodicLattice.smearedObservable u) (gibbs D) := by
  have := isProbabilityMeasure_gibbs hC
  exact Integrable.of_bound (aestronglyMeasurable_smeared hA hC u) _
    (ae_norm_smeared_le hA hC hu)
include hA hC in
theorem ae_norm_centred_le {u : D.Torus → ℝ} (hu : TestFunctions.IsBoundedFun u) :
    ∀ᵐ U ∂gibbs D, ‖D.centredObservable u U‖ ≤
      4 * (D.faceCount : ℝ) * TestFunctions.uniformNorm u := by
  have := isProbabilityMeasure_gibbs hC
  have hmean : ‖PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
      (PeriodicLattice.smearedObservable u)‖ ≤
      2 * (D.faceCount : ℝ) * TestFunctions.uniformNorm u := by
    have h := norm_integral_le_of_norm_le_const (ae_norm_smeared_le hA hC hu)
    simpa [PeriodicLattice.gibbsExpectation] using h
  filter_upwards [ae_norm_smeared_le hA hC hu] with U hU
  have h := norm_sub_le (PeriodicLattice.smearedObservable u U)
    (PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling (PeriodicLattice.smearedObservable u))
  have e : D.centredObservable u U = PeriodicLattice.smearedObservable u U -
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
        (PeriodicLattice.smearedObservable u) := rfl
  rw [e]
  linarith
include hA hC in
theorem aestronglyMeasurable_centred (u : D.Torus → ℝ) :
    AEStronglyMeasurable (D.centredObservable u) (gibbs D) :=
  (aestronglyMeasurable_smeared hA hC u).sub aestronglyMeasurable_const
include hA hC in
theorem ae_norm_prod_centred_le {q : ℕ} {g : Fin q → D.Torus → ℝ}
    (hg : ∀ l, TestFunctions.IsBoundedFun (g l)) :
    ∀ᵐ U ∂gibbs D, ‖∏ l, D.centredObservable (g l) U‖ ≤
      (4 * (D.faceCount : ℝ)) ^ q * ∏ l, TestFunctions.uniformNorm (g l) := by
  filter_upwards [ae_all_iff.mpr fun l => ae_norm_centred_le hA hC (hg l)] with U hU
  rw [norm_prod]
  calc ∏ l, ‖D.centredObservable (g l) U‖
      ≤ ∏ l, 4 * (D.faceCount : ℝ) * TestFunctions.uniformNorm (g l) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun l _ => hU l
    _ = (4 * (D.faceCount : ℝ)) ^ q * ∏ l, TestFunctions.uniformNorm (g l) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
include hA hC in
theorem integrable_prod_centred {q : ℕ} {g : Fin q → D.Torus → ℝ}
    (hg : ∀ l, TestFunctions.IsBoundedFun (g l)) :
    Integrable (fun U => ∏ l, D.centredObservable (g l) U) (gibbs D) := by
  have := isProbabilityMeasure_gibbs hC
  exact Integrable.of_bound
    (Finset.aestronglyMeasurable_fun_prod _ fun l _ => aestronglyMeasurable_centred hA hC (g l)) _
    (ae_norm_prod_centred_le hA hC hg)
include hA in
theorem smeared_linear (a b : ℝ) (u v : D.Torus → ℝ) (U : D.BondField) :
    PeriodicLattice.smearedObservable (a • u + b • v) U =
      a * PeriodicLattice.smearedObservable u U + b * PeriodicLattice.smearedObservable v U := by
  have := hA.2.2.1
  have := Fintype.ofFinite D.Face
  simp only [PeriodicLattice.smearedObservable, finsum_eq_sum_of_fintype, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
include hA hC in
theorem centred_linear (a b : ℝ) {u v : D.Torus → ℝ} (hu : TestFunctions.IsBoundedFun u)
    (hv : TestFunctions.IsBoundedFun v) (U : D.BondField) :
    D.centredObservable (a • u + b • v) U =
      a * D.centredObservable u U + b * D.centredObservable v U := by
  have e : ∀ w : D.Torus → ℝ, D.centredObservable w U = PeriodicLattice.smearedObservable w U -
      ∫ V, PeriodicLattice.smearedObservable w V ∂gibbs D := fun _ => rfl
  have hi : ∫ V, PeriodicLattice.smearedObservable (a • u + b • v) V ∂gibbs D =
      a * ∫ V, PeriodicLattice.smearedObservable u V ∂gibbs D +
        b * ∫ V, PeriodicLattice.smearedObservable v V ∂gibbs D := by
    simp only [smeared_linear hA]
    rw [integral_add ((integrable_smeared hA hC hu).const_mul a)
      ((integrable_smeared hA hC hv).const_mul b), integral_const_mul, integral_const_mul]
  rw [e, e, e, hi, smeared_linear hA]
  ring
end Measure
variable (hM : ReflectionPositivity.CutoffMirrors.CentredMomentCumulantExpansion)
  (hE : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement)
  (hT : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
include hT in
theorem isBoundedFun_of_isAdmissibleArg {D : MirrorData} {q : ℕ} {g : Fin q → D.Torus → ℝ}
    (hg : MirrorData.IsAdmissibleArg g) (l : Fin q) : TestFunctions.IsBoundedFun (g l) :=
  ((hT D).2.1 ℝ (g l) (hg.1 l)).2.1
include hM hE hT in
theorem latticeFunctionalBound_holds (D : MirrorData) (q : ℕ) : LatticeFunctionalBound D q := by
  intro g hg
  obtain ⟨hA, -, hC⟩ := hE D
  have := isProbabilityMeasure_gibbs hC
  refine ⟨?_, fun _ => D.truncatedFunctional_eq_centredSchwinger g⟩
  rw [← ((hM.2 D q g hg).2), Complex.norm_real]
  have h := norm_integral_le_of_norm_le_const
    (ae_norm_prod_centred_le hA hC (isBoundedFun_of_isAdmissibleArg hT hg))
  simpa [PeriodicLattice.gibbsExpectation] using h
theorem isAdmissibleArg_components
    (hS : Ambient.testSpacesAndSepTuples) (D : MirrorData) {q : ℕ}
    {W : Fin q → Set (Ambient.periodic.Carrier D.toStandingParameters)}
    (hW : Pairwise (Function.onFun Disjoint W))
    (h : Ambient.periodic.C1ProductSpace D.toStandingParameters W) :
    MirrorData.IsAdmissibleArg (D := D) (Ambient.components h) := by
  refine ⟨fun l => ?_, fun l l' hl => ?_⟩
  · have hsub := (hS D.toStandingParameters Ambient.periodic ⟨1, Set.mem_Ici.mpr le_rfl⟩
      (W l) univ 1 le_rfl).1.2.2.2.1
    exact (hsub (h l).2).1
  · have h₁ : D.supp (Ambient.components h l) ⊆ W l := (h l).2.2.2
    have h₂ : D.supp (Ambient.components h l') ⊆ W l' := (h l').2.2.2
    exact Set.disjoint_iff_inter_eq_empty.mp ((hW hl).mono h₁ h₂)
end BoundedForms
open BoundedForms ReflectionPositivity.CutoffMirrors
theorem torusFormsBounded_holds
    (hM : ReflectionPositivity.CutoffMirrors.CentredMomentCumulantExpansion)
    (hE : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement)
    (hT : ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts)
    (hS : Ambient.testSpacesAndSepTuples) :
    torusFormsBounded := by
  intro q _
  refine ⟨fun D => latticeFunctionalBound_holds hM hE hT D q, fun D W _ hW => ?_⟩
  obtain ⟨hA, -, hC⟩ := hE D
  have harg := fun h => isAdmissibleArg_components hS D hW h
  have hval : ∀ h : Ambient.periodic.C1ProductSpace D.toStandingParameters W,
      MirrorData.truncatedFunctional D (Ambient.components h) =
        ((∫ U, ∏ l, D.centredObservable (Ambient.components h l) U ∂gibbs D : ℝ) : ℂ) :=
    fun h => ((hM.2 D q _ (harg h)).2).symm
  have hb : ∀ (h : Ambient.periodic.C1ProductSpace D.toStandingParameters W) l,
      TestFunctions.IsBoundedFun (Ambient.components h l) :=
    fun h l => isBoundedFun_of_isAdmissibleArg hT (harg h) l
  refine ⟨fun h => ?_, fun i a b X Y Z hY hZ hi => ?_, fun h => ?_⟩
  · change (D.truncatedFunctional (Ambient.components h)).im = 0
    rw [hval h, Complex.ofReal_im]
  · change (D.truncatedFunctional (Ambient.components Z)).re =
      a * (D.truncatedFunctional (Ambient.components X)).re +
        b * (D.truncatedFunctional (Ambient.components Y)).re
    rw [hval Z, hval X, hval Y, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]
    have hpt : ∀ U, ∏ l, D.centredObservable (Ambient.components Z l) U =
        a * ∏ l, D.centredObservable (Ambient.components X l) U +
          b * ∏ l, D.centredObservable (Ambient.components Y l) U := by
      intro U
      have hrest : ∀ W' : Ambient.periodic.C1ProductSpace D.toStandingParameters W,
          (∀ l, l ≠ i → (W' l).1 = (X l).1) →
          ∏ l ∈ Finset.univ.erase i, D.centredObservable (Ambient.components W' l) U =
            ∏ l ∈ Finset.univ.erase i, D.centredObservable (Ambient.components X l) U := by
        intro W' hW'
        refine Finset.prod_congr rfl fun l hl => ?_
        have e : Ambient.components W' l = Ambient.components X l :=
          hW' l (Finset.ne_of_mem_erase hl)
        rw [e]
      have hZi : D.centredObservable (Ambient.components Z i) U =
          a * D.centredObservable (Ambient.components X i) U +
            b * D.centredObservable (Ambient.components Y i) U := by
        have e : (Ambient.components Z i : D.Torus → ℝ) =
            a • (Ambient.components X i : D.Torus → ℝ) +
              b • (Ambient.components Y i : D.Torus → ℝ) := hi
        rw [e]
        exact centred_linear hA hC a b (hb X i) (hb Y i) U
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
        ← Finset.mul_prod_erase _ (fun l => D.centredObservable (Ambient.components X l) U)
          (Finset.mem_univ i),
        ← Finset.mul_prod_erase _ (fun l => D.centredObservable (Ambient.components Y l) U)
          (Finset.mem_univ i),
        hrest Z hZ, hrest Y hY, hZi]
      ring
    simp only [hpt]
    rw [integral_add ((integrable_prod_centred hA hC (hb X)).const_mul a)
      ((integrable_prod_centred hA hC (hb Y)).const_mul b), integral_const_mul, integral_const_mul]
  · have h₁ := (latticeFunctionalBound_holds hM hE hT D q (Ambient.components h) (harg h)).1
    refine h₁.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Finset.prod_le_prod (fun _ _ => uniformNorm_nonneg _) fun l _ => le_max_left _ _
end YangMills.Construction.LimitSpaces
end
