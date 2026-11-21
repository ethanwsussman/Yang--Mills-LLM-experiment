import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.ReflectionPositivity.ActionInTheDoubledVariablesOfALinkMirror
import YangMills.Construction.ReflectionPositivity.DoublingOfTheCrossingVariables
import YangMills.Construction.ReflectionPositivity.ObservablesOfOneSideOfALinkMirror
import YangMills.Construction.ReflectionPositivity.ReflectionInALinkMirror
import YangMills.Construction.ReflectionPositivity.SpaceOfConfigurationsAndPlaquetteEnergiesAtOneCutoff
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.OneSideObservables
variable {D : MirrorData} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem mem_supp_of_ne_zero (hdist : FamilyTopology.IsMetricFunction D.torusDist)
    {f : D.Torus → E} {x : D.Torus} (hx : f x ≠ 0) : x ∈ D.supp f := by
  intro r hr
  refine ⟨x, hx, ?_⟩
  rw [(hdist.eq_zero_iff x x).2 rfl]
  exact hr
theorem facesInHalf_of_supp_subset (hGeo : HalfSpaces.HalfSpaceStructure)
    (hdist : FamilyTopology.IsMetricFunction D.torusDist) (C : LinkLevel D) {f : D.Torus → E}
    (hsupp : D.supp f ⊆ C.openSlab .pos) : FacesInHalf C f := by
  obtain ⟨-, -, -, -, hedges, -, hcenter, -⟩ := hGeo D C
  intro p hp
  have hmem : p ∈ C.halfFaces .pos := hcenter p (hsupp (mem_supp_of_ne_zero hdist hp))
  refine ⟨hmem, fun b hb => ?_⟩
  have hbE : b ∈ C.halfEdges .pos := hedges .pos p hmem hb
  exact ⟨hbE, hbE.2.1.2, hbE.2.2.2⟩
theorem observableEqHalfSum_of_facesInHalf (C : LinkLevel D) {f : D.Torus → E}
    (hfaces : FacesInHalf C f) : ObservableEqHalfSum C f := by
  classical
  intro U
  unfold PeriodicLattice.smearedObservable
  refine finsum_congr fun p => ?_
  by_cases hmem : p ∈ C.halfFaces .pos
  · simp [hmem]
  · have hzero : f p.barycenter = 0 := by
      by_contra hne
      exact hmem (hfaces p hne).1
    simp [hmem, hzero]
theorem faceEnergy_mem_halfAlgebra (hAct : DoubledAction.DoubledActionProperties) (C : LinkLevel D)
    {p : D.Face} (hp : p ∈ C.halfFaces .pos) :
    (fun U : D.FieldSpace => ((PeriodicLattice.plaquetteCost U.1 p : ℝ) : ℂ)) ∈
      C.halfAlgebra .pos := by
  obtain ⟨hcont, hval⟩ := (hAct D C).1.1 p hp
  have hc : Continuous fun u => ((C.faceEnergyOfHalf p u : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hcont
  refine ⟨fun u => ((C.faceEnergyOfHalf p u : ℝ) : ℂ), ?_, ?_, ?_⟩
  · letI : MeasurableSpace (C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary) := borel _
    have : BorelSpace (C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary) := ⟨rfl⟩
    exact hc.measurable
  · obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨B, fun v => hB v (mem_univ _)⟩
  · funext U
    rw [hval U]
    rfl
theorem finset_sum_mem_halfAlgebra {C : LinkLevel D}
    (hAlg : DoubledTransversal.HalfAlgebraClosed C .pos)
    {P : Type} (T : Finset P) (c : P → ℂ) (F : P → D.FieldSpace → ℂ)
    (hF : ∀ p ∈ T, F p ∈ C.halfAlgebra .pos) :
    (fun U => ∑ p ∈ T, c p * F p U) ∈ C.halfAlgebra .pos := by
  classical
  obtain ⟨-, hconst, hadd, hsmul, -, -⟩ := hAlg
  induction T using Finset.induction_on with
  | empty => simpa using hconst 0
  | insert a T ha ih =>
    have h₁ := hsmul (c a) (F a) (hF a (Finset.mem_insert_self a T))
    have h₂ := ih fun p hp => hF p (Finset.mem_insert_of_mem hp)
    have h₃ := hadd _ h₁ _ h₂
    have e : (fun U => ∑ p ∈ insert a T, c p * F p U) =
        c a • F a + fun U => ∑ p ∈ T, c p * F p U := by
      funext U
      rw [Finset.sum_insert ha]
      rfl
    rw [e]
    exact h₃
theorem observablesMemHalfAlgebra_of_eqHalfSum (hAct : DoubledAction.DoubledActionProperties)
    [Finite D.Face] (C : LinkLevel D)
    (hAlg : DoubledTransversal.HalfAlgebraClosed C .pos)
    (ι : E →ₗ[ℝ] ℂ) {f : D.Torus → E} (hsum : ObservableEqHalfSum C f) :
    ObservablesMemHalfAlgebra ι C f := by
  have hfin : (C.halfFaces .pos).Finite := Set.toFinite _
  have hobs : (fun U : D.FieldSpace => ι (PeriodicLattice.smearedObservable f U.1)) ∈
      C.halfAlgebra .pos := by
    have e : (fun U : D.FieldSpace => ι (PeriodicLattice.smearedObservable f U.1)) =
        fun U => ∑ p ∈ hfin.toFinset, ι (f p.barycenter) *
          ((PeriodicLattice.plaquetteCost U.1 p : ℝ) : ℂ) := by
      funext U
      rw [hsum U, finsum_mem_eq_finite_toFinset_sum _ hfin, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul, Complex.real_smul, mul_comm]
    rw [e]
    exact finset_sum_mem_halfAlgebra hAlg _ _ _ fun p hp =>
      faceEnergy_mem_halfAlgebra hAct C (hfin.mem_toFinset.mp hp)
  refine ⟨hobs, ?_⟩
  have hconst := hAlg.2.1
    (-ι (PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
      (PeriodicLattice.smearedObservable f)))
  have e : (fun U : D.FieldSpace => ι (D.centredObservable f U.1)) =
      (fun U : D.FieldSpace => ι (PeriodicLattice.smearedObservable f U.1)) +
        fun _ => -ι (PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
          (PeriodicLattice.smearedObservable f)) := by
    funext U
    simp [MirrorData.centredObservable, sub_eq_add_neg]
  rw [e]
  exact hAlg.2.2.1 _ hobs _ hconst
theorem ae_mem_compactGaugeFields (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (D : MirrorData) :
    ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling,
      U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) := by
  have hL : 1 < D.L := lt_of_lt_of_le (by norm_num) D.isAdmissible.2
  obtain ⟨-, -, -, -, -, -, -, -, hnull, -⟩ := hW D.L D.m D.K D.coupling hL D.m.pos D.K.pos
  exact mem_ae_iff.mpr hnull
theorem reflectImage_of_expectation_eq (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hIso : TorusMetricSpace.IsometryActionOnFunctions D)
    (C : LinkLevel D) (hT : LinkReflection.ActsOnTorus C)
    (s : D.Symmetry) (hs : s.toFun = C.refl) (hP : LinkReflection.ActsOnPlaquettes C s)
    {f : D.Torus → E} (hb : TestFunctions.IsBoundedFun f) (hsupp : D.supp f ⊆ C.openSlab .pos)
    (hinv : PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
        (PeriodicLattice.smearedObservable f ∘ MirrorData.Symmetry.pullback s) =
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
        (PeriodicLattice.smearedObservable f)) :
    ReflectImage C f := by
  obtain ⟨hinvol, hisom, -, -, hslab, -⟩ := hT
  have hobs : ∀ U ∈ LinkReflection.gaugeFieldSpace D,
      PeriodicLattice.smearedObservable f (MirrorData.Symmetry.pullback s U) =
        PeriodicLattice.smearedObservable (C.reflectFn f) U :=
    hP.2.2.2.2 E f hb
  have hrefl : ∀ U : D.FieldSpace, PeriodicLattice.smearedObservable f (C.reflectField U).1 =
      PeriodicLattice.smearedObservable (C.reflectFn f) U.1 := fun U => by
    rw [C.reflectField_val s hs U]
    exact hobs U.1 U.2
  have hexp : PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
      (PeriodicLattice.smearedObservable (C.reflectFn f)) =
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
        (PeriodicLattice.smearedObservable f) := by
    rw [← hinv]
    exact integral_congr_ae
      ((ae_mem_compactGaugeFields hW D).mono fun U hU => (hobs U hU).symm)
  refine ⟨hrefl, ?_, hexp, fun U => ?_⟩
  · have e : D.supp (C.reflectFn f) = C.refl ⁻¹' D.supp f :=
      ((hIso C.refl hinvol.bijective hisom).2.1 E f).1
    rw [e]
    intro y hy
    rw [← hslab]
    exact ⟨C.refl y, hsupp hy, hinvol y⟩
  · simp only [MirrorData.centredObservable]
    rw [hrefl U, hexp]
theorem boundedFunClaims_of_expectation_eq (hGeo : HalfSpaces.HalfSpaceStructure)
    (hAct : DoubledAction.DoubledActionProperties)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hdist : FamilyTopology.IsMetricFunction D.torusDist)
    (hIso : TorusMetricSpace.IsometryActionOnFunctions D)
    [Finite D.Face] (C : LinkLevel D)
    (hAlg : DoubledTransversal.HalfAlgebraClosed C .pos)
    (hT : LinkReflection.ActsOnTorus C)
    (s : D.Symmetry) (hs : s.toFun = C.refl) (hP : LinkReflection.ActsOnPlaquettes C s)
    (ι : E →ₗ[ℝ] ℂ) (f : D.Torus → E)
    (hinv : PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
        (PeriodicLattice.smearedObservable f ∘ MirrorData.Symmetry.pullback s) =
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
        (PeriodicLattice.smearedObservable f)) :
    BoundedFunClaims ι C f := by
  intro hb hsupp
  have hfaces := facesInHalf_of_supp_subset hGeo hdist C hsupp
  have hsum := observableEqHalfSum_of_facesInHalf C hfaces
  exact ⟨hfaces, hsum, observablesMemHalfAlgebra_of_eqHalfSum hAct C hAlg ι hsum,
    reflectImage_of_expectation_eq hW hIso C hT s hs hP hb hsupp hinv⟩
theorem isBoundedMeasurable_of_continuous {F : Type} [NormedAddCommGroup F] [MeasurableSpace F]
    [TopologicalSpace.PseudoMetrizableSpace F] [BorelSpace F]
    (hprod : D.productTopology = (inferInstance : TopologicalSpace D.FieldSpace))
    {Φ : D.BondField → F}
    (hc : D.ContinuousForProduct fun U : D.FieldSpace => Φ U.1)
    (hb : TestFunctions.IsBoundedFun fun U : D.FieldSpace => Φ U.1) :
    LinkReflection.IsBoundedMeasurableOnGaugeFields Φ := by
  refine ⟨hb, ?_⟩
  have hc' : Continuous fun U : D.FieldSpace => Φ U.1 := by
    unfold MirrorData.ContinuousForProduct at hc
    rw [hprod] at hc
    exact hc
  let _ : MeasurableSpace D.FieldSpace := borel _
  have : BorelSpace D.FieldSpace := ⟨rfl⟩
  exact hc'.measurable
theorem halfSpaceObservables_holds (hGeo : HalfSpaces.HalfSpaceStructure)
    (hRefl : LinkReflection.LinkReflectionProperties)
    (hAct : DoubledAction.DoubledActionProperties)
    (hDbl : DoubledTransversal.DoublingProperties)
    (hMet : TorusMetricSpace.MetricTorusFacts)
    (hSpace : FieldSpaceAndFaceEnergies.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) : HalfSpaceObservables := by
  intro D C
  obtain ⟨hT, s, hs, -, -, hP, hEr, hEc⟩ := hRefl D C
  obtain ⟨⟨-, -, hfin, -, -, -, hprod, -⟩, -, -, hR, hCx, -⟩ := hSpace D
  have : Finite D.Face := hfin
  have hdist := (hMet D).1.2.1
  have hIso := (hMet D).2.2.2
  have hAlg := ((hDbl D C).2.2.1 .pos).2.1
  refine ⟨fun f => ?_, fun f => ?_⟩
  · exact boundedFunClaims_of_expectation_eq hGeo hAct hW hdist hIso C hAlg hT s hs hP
      Complex.ofRealLI.toLinearMap f
      (hEr _ (isBoundedMeasurable_of_continuous hprod (hR f).1 (hR f).2))
  · exact boundedFunClaims_of_expectation_eq hGeo hAct hW hdist hIso C hAlg hT s hs hP
      LinearMap.id f
      (hEc _ (isBoundedMeasurable_of_continuous hprod (hCx f).1 (hCx f).2.1))
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.OneSideObservables
end
