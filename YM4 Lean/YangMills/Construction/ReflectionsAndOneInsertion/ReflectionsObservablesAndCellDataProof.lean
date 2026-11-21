import YangMills.Construction.ChessboardTori.MirrorPeriodicWeightsAsCellFunctionsProof
import YangMills.Construction.MirrorGridsOfEverySide.IsometriesThatKeepTheFacePlanesAtEveryMirrorGridProof
import YangMills.Construction.ChessboardTori.FromTheInfiniteLatticeToTheTorus
import YangMills.Construction.ChessboardTori.JensenAgainstTheChessboardProof
import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorusProof
import YangMills.Construction.Continuum.SubTuplesIsometriesAndTheConjugateOnFourSpace
import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnConfigurationsAndFunctionsProof
import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLattice
import YangMills.Construction.InfiniteLattice.FunctionsOfASetOfBonds
import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import YangMills.Construction.InfiniteLattice.SigmaAlgebrasOfSetsOfBondsAndDependenceOnVariables
import YangMills.Construction.InfiniteLattice.WindowDensitiesAndStandardWindows
import YangMills.Construction.MirrorGridsOfEverySide.ChessboardEstimateOnGridsOfEverySide
import YangMills.Construction.ReflectionPositivity.LatticeFormulaForTheScalarProductProof
import YangMills.Construction.ReflectionsAndOneInsertion.ReflectionsObservablesAndCellData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set MeasureTheory
open InfiniteLattice (AmbientSpace IsBoundedObservable IsRegionMeasurable halfSpacingTimes timeAxis
  timeReflect timeReflectAtOrigin localObsAbove)
open ChessboardTori (ReflectionGrid GridCell)
open MirrorGridsAllSides (conjFun transportFun)
namespace ReflectionsAndOneInsertion
theorem timeReflect_coord {a : ℝ} (t : halfSpacingTimes a) (x : AmbientSpace) (μ : Fin 4) :
    (timeReflect t).toFun x μ = if μ = timeAxis then 2 * (t : ℝ) - x μ else x μ := by
  rw [InfiniteLattice.timeReflect_apply]
  by_cases h : μ = timeAxis
  · subst h
    simp
    ring
  · simp [Pi.single_eq_of_ne h, h]
theorem timeUnitVec_coord (μ : Fin 4) :
    timeUnitVec μ = if μ = timeAxis then 1 else 0 := by
  by_cases h : μ = timeAxis
  · subst h
    simp [timeUnitVec, ChessboardTori.coordVec]
  · simp [timeUnitVec, ChessboardTori.coordVec, Pi.single_eq_of_ne h, h]
theorem spaceTimePoint_time (v : Fin 3 → ℝ) (t : ℝ) :
    spaceTimePoint v t timeAxis = t := by
  have h : timeAxis = Fin.last 3 := rfl
  rw [h, spaceTimePoint, Fin.snoc_last]
theorem reflectShiftRelations_holds (D : InsertionData) : ReflectShiftRelations D := by
  intro t u hu v s
  have hz : ((InfiniteLattice.originTime D.mesh : halfSpacingTimes D.mesh) : ℝ) = 0 := rfl
  have hs : ((addHalfStep t hu : halfSpacingTimes D.mesh) : ℝ) = t + u / 2 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext x μ <;> by_cases h : μ = timeAxis
  all_goals
    simp only [Function.comp, timeReflectAtOrigin, timeReflect_coord, hz, hs, h, if_true,
      if_false, SeparatedTuples.translate, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      timeUnitVec_coord, spaceTimePoint_time]
  all_goals try simp only [h, if_true, if_false, mul_one, mul_zero, add_zero]
  all_goals ring
theorem observableActionLaws_holds (hA : InfiniteLattice.SymmetryActionOnObservables)
    (D : InsertionData) : ObservableActionLaws D := by
  obtain ⟨-, -, h3, h4, -, h6, -⟩ := hA ⟨D.mesh, ChessboardTori.ChessboardSetup.mesh_pos D⟩
  intro r r' A B hA' hB
  refine ⟨(h4 r r').2 A hA', rfl, rfl, ((h6 r).2 A hA').2.2.2, fun S hS => ?_⟩
  have hmem : r.actOn A ∈ InfiniteLattice.boundedRegionObservables D.mesh (r.setImage S) := by
    rw [← (h3 r).2 S]
    exact ⟨A, ⟨hA', hS⟩, rfl⟩
  exact hmem.2
section Isometries
variable {r r' : Equiv.Perm AmbientSpace}
theorem isEuclidIsometry_symm (hr : SeparatedTuples.IsEuclidIsometry r) :
    SeparatedTuples.IsEuclidIsometry r.symm := fun x y => by
  have h := hr (r.symm x) (r.symm y)
  simpa using h.symm
theorem single_eq_smul_basisVec (X : SeparatedTuples.SepTuple) (c : ℂ) :
    (Finsupp.single X c : SeparatedTuples.FormalSpan) = c • SeparatedTuples.basisVec X := by
  simp [SeparatedTuples.basisVec]
theorem pushSpan_smul_basisVec (f : AmbientSpace → AmbientSpace) (X : SeparatedTuples.SepTuple)
    (c : ℂ) :
    SeparatedTuples.pushSpan f (c • SeparatedTuples.basisVec X) =
      c • SeparatedTuples.basisVec (SeparatedTuples.push f X) := by
  rw [map_smul, SeparatedTuples.pushSpan, SeparatedTuples.linearExtend_basisVec]
theorem pushSpan_eq_mapDomain (f : AmbientSpace → AmbientSpace) (F : SeparatedTuples.FormalSpan) :
    SeparatedTuples.pushSpan f F = Finsupp.mapDomain (SeparatedTuples.push f) F := by
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F G hF hG => rw [map_add, hF, hG, Finsupp.mapDomain_add]
  | single X c =>
    rw [Finsupp.mapDomain_single, single_eq_smul_basisVec, single_eq_smul_basisVec,
      pushSpan_smul_basisVec]
theorem exists_of_mem_support_pushSpan {f : AmbientSpace → AmbientSpace}
    {F : SeparatedTuples.FormalSpan} {X : SeparatedTuples.SepTuple}
    (hX : X ∈ (SeparatedTuples.pushSpan f F).support) :
    ∃ Y ∈ F.support, SeparatedTuples.push f Y = X := by
  classical
  rw [pushSpan_eq_mapDomain] at hX
  have := Finsupp.mapDomain_support hX
  simpa using this
theorem formalSpan_eq_sum (F : SeparatedTuples.FormalSpan) :
    F = ∑ X ∈ F.support, F X • SeparatedTuples.basisVec X := by
  conv_lhs => rw [← Finsupp.sum_single F]
  simp only [Finsupp.sum, single_eq_smul_basisVec]
theorem conjugation_pushSpan (f : AmbientSpace → AmbientSpace) (F : SeparatedTuples.FormalSpan) :
    SeparatedTuples.conjugation (SeparatedTuples.pushSpan f F) =
      SeparatedTuples.pushSpan f (SeparatedTuples.conjugation F) := by apply _root_.YangMills.Construction.ReflectionPositivity.LatticeScalarProduct.conjugation_pushSpan <;> assumption
variable (D : InsertionData)
include D
theorem contDiff_of_isEuclidIsometry (hr : SeparatedTuples.IsEuclidIsometry r) : ContDiff ℝ 1 r :=
  Continuum.SeparatedFourTuples.contDiff_of_isDistIsometry (s := D.toStandingParameters) (r := r) hr
def homeomorphOfIsEuclidIsometry (hr : SeparatedTuples.IsEuclidIsometry r) :
    AmbientSpace ≃ₜ AmbientSpace where
  toEquiv := r
  continuous_toFun := (contDiff_of_isEuclidIsometry D hr).continuous
  continuous_invFun := (contDiff_of_isEuclidIsometry D (isEuclidIsometry_symm hr)).continuous
omit D in
theorem euclidSupp_transportFun {E : Type*} [Zero E] (hr : SeparatedTuples.IsEuclidIsometry r)
    (f : AmbientSpace → E) :
    ReflectionPositivity.CutoffMirrors.euclidSupp (transportFun r f) =
      r '' ReflectionPositivity.CutoffMirrors.euclidSupp f := by
  have hset : {x | transportFun r f x ≠ 0} = r '' {x | f x ≠ 0} := by
    ext x
    constructor
    · intro hx
      exact ⟨r.symm x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [transportFun] using hy
  simp only [ReflectionPositivity.CutoffMirrors.euclidSupp]
  rw [hset]
  ext x
  constructor
  · intro h
    refine ⟨r.symm x, fun ε hε => ?_, by simp⟩
    obtain ⟨_, ⟨z, hz, rfl⟩, hd⟩ := h ε hε
    refine ⟨z, hz, ?_⟩
    have h1 := hr (r.symm x) z
    rw [Equiv.apply_symm_apply] at h1
    exact h1.symm.trans_lt hd
  · rintro ⟨y, hy, rfl⟩ ε hε
    obtain ⟨z, hz, hd⟩ := hy ε hε
    refine ⟨r z, ⟨z, hz, rfl⟩, ?_⟩
    have h1 := hr y z
    exact h1.trans_lt hd
omit D in
theorem sharpNormR4_transportFun {E : Type*} [NormedAddCommGroup E]
    (hr : SeparatedTuples.IsEuclidIsometry r) (M : ℝ) (f : AmbientSpace → E) :
    TestFunctions.sharpNormR4 M (transportFun r f) = TestFunctions.sharpNormR4 M f := by
  have hsup : TestFunctions.uniformNorm (transportFun r f) = TestFunctions.uniformNorm f :=
    Equiv.iSup_comp (g := fun x => ‖f x‖) r.symm
  have hlip : TestFunctions.lipConstR4 (transportFun r f) = TestFunctions.lipConstR4 f := by
    unfold TestFunctions.lipConstR4 TestFunctions.bestLipschitzConstant
    congr 1
    ext C
    constructor
    · rintro ⟨h0, h⟩
      refine ⟨h0, fun x y => ?_⟩
      have h1 := h (r x) (r y)
      have h2 : TestFunctions.euclidDistR4 (r x) (r y) = TestFunctions.euclidDistR4 x y := hr x y
      simpa [transportFun, h2] using h1
    · rintro ⟨h0, h⟩
      refine ⟨h0, fun x y => ?_⟩
      have h1 := h (r.symm x) (r.symm y)
      have h2 : TestFunctions.euclidDistR4 (r.symm x) (r.symm y) =
        TestFunctions.euclidDistR4 x y := isEuclidIsometry_symm hr x y
      simpa [transportFun, h2] using h1
  rw [TestFunctions.sharpNormR4, TestFunctions.sharpNormR4, hsup, hlip]
theorem invMap_perm (r : Equiv.Perm AmbientSpace) : SeparatedTuples.invMap r = r.symm :=
  R4TupleForms.invMap_eq_symm (s := D.toStandingParameters) r
theorem tsupport_comp_symm (hr : SeparatedTuples.IsEuclidIsometry r)
    (f : SeparatedTuples.RealValued) :
    tsupport (f ∘ r.symm) = r.symm ⁻¹' tsupport f :=
  Continuum.SeparatedFourTuples.tsupport_comp_homeo (homeomorphOfIsEuclidIsometry D hr).symm f
theorem isDisjointlySupported_pushList (hr : SeparatedTuples.IsEuclidIsometry r)
    {X : List SeparatedTuples.RealValued} (hX : SeparatedTuples.IsDisjointlySupported X) :
    SeparatedTuples.IsDisjointlySupported (SeparatedTuples.pushList r X) := by
  simp only [SeparatedTuples.pushList, invMap_perm D]
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    exact ⟨ContDiff.comp (hX.1 f hf).1 (contDiff_of_isEuclidIsometry D (isEuclidIsometry_symm hr)),
      (hX.1 f hf).2.comp_homeomorph (homeomorphOfIsEuclidIsometry D hr).symm⟩
  · rw [List.pairwise_map]
    refine hX.2.imp fun {f h} hd => ?_
    rw [tsupport_comp_symm D hr, tsupport_comp_symm D hr]
    exact hd.preimage _
theorem push_val (hr : SeparatedTuples.IsEuclidIsometry r) (X : SeparatedTuples.SepTuple) :
    (SeparatedTuples.push r X).1 = SeparatedTuples.pushList r X.1 := by
  unfold SeparatedTuples.push
  rw [dif_pos (isDisjointlySupported_pushList D hr X.2)]
theorem push_mul (hr : SeparatedTuples.IsEuclidIsometry r)
    (hr' : SeparatedTuples.IsEuclidIsometry r')
    (hrr : SeparatedTuples.IsEuclidIsometry (⇑(r * r'))) (X : SeparatedTuples.SepTuple) :
    SeparatedTuples.push (⇑(r * r')) X =
      SeparatedTuples.push r (SeparatedTuples.push r' X) := by
  refine Subtype.ext ?_
  rw [push_val D hrr, push_val D hr, push_val D hr']
  simp only [SeparatedTuples.pushList, invMap_perm D, List.map_map]
  refine List.map_congr_left fun f _ => ?_
  rfl
theorem composable_push (hr : SeparatedTuples.IsEuclidIsometry r)
    {X Y : SeparatedTuples.SepTuple} (h : SeparatedTuples.SepTuple.Composable X Y) :
    SeparatedTuples.SepTuple.Composable (SeparatedTuples.push r X)
      (SeparatedTuples.push r Y) := by
  intro f hf g hg
  rw [push_val D hr] at hf hg
  simp only [SeparatedTuples.pushList, invMap_perm D] at hf hg
  obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hf
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
  rw [tsupport_comp_symm D hr, tsupport_comp_symm D hr]
  exact (h f' hf' g' hg').preimage _
theorem push_juxt (hr : SeparatedTuples.IsEuclidIsometry r) {X Y : SeparatedTuples.SepTuple}
    (h : SeparatedTuples.SepTuple.Composable X Y) :
    SeparatedTuples.push r (SeparatedTuples.SepTuple.juxt X Y) =
      SeparatedTuples.SepTuple.juxt (SeparatedTuples.push r X) (SeparatedTuples.push r Y) := by
  refine Subtype.ext ?_
  rw [push_val D hr, SeparatedTuples.SepTuple.juxt_val h,
    SeparatedTuples.SepTuple.juxt_val (composable_push D hr h), push_val D hr, push_val D hr]
  simp [SeparatedTuples.pushList]
theorem pushSpan_formalMul_of_sums (hr : SeparatedTuples.IsEuclidIsometry r)
    (s t : Finset SeparatedTuples.SepTuple) (c c' : SeparatedTuples.SepTuple → ℂ)
    (h : ∀ X ∈ s, ∀ Y ∈ t, SeparatedTuples.SepTuple.Composable X Y) :
    SeparatedTuples.pushSpan r (SeparatedTuples.formalMul
        (∑ X ∈ s, c X • SeparatedTuples.basisVec X)
        (∑ Y ∈ t, c' Y • SeparatedTuples.basisVec Y)) =
      SeparatedTuples.formalMul
        (SeparatedTuples.pushSpan r (∑ X ∈ s, c X • SeparatedTuples.basisVec X))
        (SeparatedTuples.pushSpan r (∑ Y ∈ t, c' Y • SeparatedTuples.basisVec Y)) := by
  have hL : ∀ (u : Finset SeparatedTuples.SepTuple) (e : SeparatedTuples.SepTuple → ℂ),
      SeparatedTuples.pushSpan r (∑ X ∈ u, e X • SeparatedTuples.basisVec X) =
        ∑ X ∈ u, e X • SeparatedTuples.basisVec (SeparatedTuples.push r X) := fun u e => by
    simp only [map_sum, pushSpan_smul_basisVec]
  rw [hL s c, hL t c', SeparatedTuples.formalMul_sum s t c c'
    (fun X => SeparatedTuples.push r X) (fun Y => SeparatedTuples.push r Y),
    SeparatedTuples.formalMul_sum s t c c' (fun X => X) (fun Y => Y), map_sum]
  refine Finset.sum_congr rfl fun X hX => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun Y hY => ?_
  rw [pushSpan_smul_basisVec, push_juxt D hr (h X hX Y hY)]
theorem pushSpan_mul (hr : SeparatedTuples.IsEuclidIsometry r)
    (hr' : SeparatedTuples.IsEuclidIsometry r') (Ξ : SeparatedTuples.FormalSpan) :
    SeparatedTuples.pushSpan (⇑(r * r')) Ξ =
      SeparatedTuples.pushSpan r (SeparatedTuples.pushSpan r' Ξ) := by
  have hrr : SeparatedTuples.IsEuclidIsometry (⇑(r * r')) := fun x y =>
    (hr (r' x) (r' y)).trans (hr' x y)
  induction Ξ using Finsupp.induction_linear with
  | zero => simp
  | add F G hF hG => simp only [map_add, hF, hG]
  | single X c =>
    rw [single_eq_smul_basisVec, pushSpan_smul_basisVec, pushSpan_smul_basisVec,
      pushSpan_smul_basisVec, push_mul D hr hr' hrr]
theorem formalMulDefined_pushSpan (hr : SeparatedTuples.IsEuclidIsometry r)
    {Ξ Ξ' : SeparatedTuples.FormalSpan} (h : R4TupleForms.FormalMulDefined Ξ Ξ') :
    R4TupleForms.FormalMulDefined (SeparatedTuples.pushSpan r Ξ)
      (SeparatedTuples.pushSpan r Ξ') := by
  intro X hX Y hY
  obtain ⟨X', hX', rfl⟩ := exists_of_mem_support_pushSpan hX
  obtain ⟨Y', hY', rfl⟩ := exists_of_mem_support_pushSpan hY
  exact composable_push D hr (h X' hX' Y' hY')
theorem pushSpan_formalMul (hr : SeparatedTuples.IsEuclidIsometry r)
    {Ξ Ξ' : SeparatedTuples.FormalSpan} (h : R4TupleForms.FormalMulDefined Ξ Ξ') :
    SeparatedTuples.pushSpan r (SeparatedTuples.formalMul Ξ Ξ') =
      SeparatedTuples.formalMul (SeparatedTuples.pushSpan r Ξ) (SeparatedTuples.pushSpan r Ξ') := by
  have := pushSpan_formalMul_of_sums D hr Ξ.support Ξ'.support Ξ Ξ' h
  rwa [← formalSpan_eq_sum Ξ, ← formalSpan_eq_sum Ξ'] at this
end Isometries
theorem functionAndSpanActionLaws_holds (D : InsertionData) : FunctionAndSpanActionLaws :=
  fun r r' hr hr' =>
    ⟨fun _ _ f _ _ => ⟨rfl, euclidSupp_transportFun hr f, fun M _ => sharpNormR4_transportFun hr M f⟩,
      fun Ξ Ξ' h => ⟨pushSpan_mul D hr hr' Ξ, formalMulDefined_pushSpan D hr h,
        pushSpan_formalMul D hr h, conjugation_pushSpan r Ξ⟩⟩
section Reads
open InfiniteLattice (positiveLinksWithin positiveLinkSet restrictField LinkVariables
  boundedBorelSpace linkSigma regionSigma linksWithin DependsOnlyOnLinks)
abbrev fixedSpacingSetup (D : InsertionData) : FixedSpacing.Params :=
  ⟨D.toStandingParameters, D.β, D.beta_pos⟩
theorem borel_linkVariables (ι : Type) [Countable ι] :
    borel (LinkVariables ι) = (MeasurableSpace.pi : MeasurableSpace (LinkVariables ι)) := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.borel_linkVariables <;> assumption
theorem linkSigma_le_borel {a : ℝ} (ℬ : Set (InfiniteLattice.Link a)) :
    linkSigma ℬ ≤ (inferInstance : MeasurableSpace (InfiniteLattice.GaugeField a)) := by apply _root_.YangMills.Construction.GibbsAtFixedSpacing.SymmetryActionProof.linkSigma_le_borel <;> assumption
theorem isRegionMeasurable_mono {a : ℝ} {S S' : Set AmbientSpace} (h : S ⊆ S')
    {A : InfiniteLattice.GaugeField a → ℂ} (hA : IsRegionMeasurable S A) :
    IsRegionMeasurable S' A := by apply _root_.YangMills.Construction.ChessboardTori.JensenChessboardBound.isRegionMeasurable_mono <;> assumption
theorem measurable_of_coords {X ι : Type*} (m : MeasurableSpace X)
    {f : X → ι → Matrices.ComplexMatrix2.specialUnitary}
    (h : ∀ i, Measurable[m] fun x => f x i) : Measurable[m] f :=
  measurable_pi_iff.2 h
theorem linksWithin_finite_of_isBounded (a : ℝ) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) :
    (linksWithin S : Set (InfiniteLattice.Link a)).Finite := by
  obtain ⟨R, hR⟩ := hS.exists_norm_le
  refine (InfiniteLattice.linksWithin_supNormVec_le_finite a R).subset fun b hb => ?_
  have hv : ∀ x ∈ S, TorusMetric.supNormVec x ≤ R := fun x hx =>
    Finset.sup'_le _ _ fun μ _ => (norm_le_pi_norm x μ).trans (hR x hx)
  exact ⟨hv _ hb.1, hv _ hb.2⟩
variable (hF : InfiniteLattice.LinkSetFunctions.Claim)
  (hS : InfiniteLattice.LinkSigmaAndDependence) (D : InsertionData)
include hS
theorem isRegionMeasurable_iff_linkSigma (S : Set AmbientSpace) {A : D.GaugeField → ℂ}
    (hA : IsBoundedObservable A) :
    IsRegionMeasurable S A ↔ Measurable[linkSigma (positiveLinksWithin D.mesh S)] A := by
  have h := (hS D.mesh D.mesh_pos).2.1 S
  constructor
  · intro hm
    have hmem : A ∈ InfiniteLattice.regionObservables D.mesh S := ⟨hA, hm⟩
    rw [h] at hmem
    exact hmem.2
  · intro hm
    have hmem : A ∈ {F | IsBoundedObservable F ∧
        Measurable[linkSigma (positiveLinksWithin D.mesh S)] F} := ⟨hA, hm⟩
    rw [← h] at hmem
    exact hmem.2
include hF
theorem isRegionMeasurable_iff (S : Set AmbientSpace) {A : D.GaugeField → ℂ}
    (hA : IsBoundedObservable A) :
    IsRegionMeasurable S A ↔
      ∃ A' ∈ boundedBorelSpace (LinkVariables (positiveLinksWithin D.mesh S)),
        ∀ U, A U = A' (restrictField U (positiveLinksWithin D.mesh S)) := by
  have hfun := (hF (fixedSpacingSetup D)).1 (positiveLinksWithin D.mesh S) inter_subset_left A hA
  refine (isRegionMeasurable_iff_linkSigma hS D S hA).trans (hfun.1.trans ?_)
  constructor
  · intro h
    obtain ⟨e, hb, -⟩ := hfun.2 h
    exact ⟨_, ⟨hb.1, hb.2⟩, e⟩
  · rintro ⟨A', -, e⟩ U U' h
    exact (e U).trans ((congrArg A' h).trans (e U').symm)
omit hF in
theorem isRegionMeasurable_inter (S₁ S₂ : Set AmbientSpace) {A : D.GaugeField → ℂ}
    (hA : IsBoundedObservable A) (h₁ : IsRegionMeasurable S₁ A) (h₂ : IsRegionMeasurable S₂ A) :
    IsRegionMeasurable (S₁ ∩ S₂) A :=
  (hS D.mesh D.mesh_pos).2.2 S₁ S₂ A hA h₁ h₂
theorem localObsAbove_eq (t : halfSpacingTimes D.mesh) :
    localObsAbove t =
      {A | ∃ B' : Finset D.Link,
        (B' : Set D.Link) ⊆ linksWithin (InfiniteLattice.abovePlane t) ∧
        MirrorGridsAllSides.GridSetup.IsBoundedMeasurableInLinks D B' A} := by
  ext A
  constructor
  · rintro ⟨hA, S, hSa, hSb, hm⟩
    obtain ⟨A', hA', e⟩ := (isRegionMeasurable_iff hF hS D S hA).1 hm
    have hfin : (positiveLinksWithin D.mesh S).Finite :=
      (linksWithin_finite_of_isBounded D.mesh hSb).subset inter_subset_right
    refine ⟨hfin.toFinset, fun b hb => ?_, ?_⟩
    · have hb' : b ∈ positiveLinksWithin D.mesh S := by simpa using hb
      exact ⟨hSa hb'.2.1, hSa hb'.2.2⟩
    · refine ⟨fun u => A' fun b => u ⟨b.1, by simp⟩, ?_, funext fun U => e U⟩
      obtain ⟨hm', C, hC⟩ := hA'
      refine ⟨?_, C, fun u => hC _⟩
      let _ : MeasurableSpace (LinkVariables (positiveLinksWithin D.mesh S)) := borel _
      have : BorelSpace (LinkVariables (positiveLinksWithin D.mesh S)) := ⟨rfl⟩
      let _ : MeasurableSpace (LinkVariables ((hfin.toFinset : Finset D.Link) : Set D.Link)) :=
        borel _
      have : BorelSpace (LinkVariables ((hfin.toFinset : Finset D.Link) : Set D.Link)) := ⟨rfl⟩
      refine hm'.comp (Continuous.measurable ?_)
      exact continuous_pi fun b => continuous_apply _
  · rintro ⟨B', hB', Φ, hΦ, rfl⟩
    refine ⟨InfiniteLattice.isBoundedObservable_observableOfLinks B' hΦ,
      (fun b : D.Link => (b.initial : AmbientSpace)) '' B' ∪
        (fun b : D.Link => (b.terminal : AmbientSpace)) '' B',
      ?_, ?_, ?_⟩
    · rintro x (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact (hB' hb).1
      · exact (hB' hb).2
    · exact ((B'.finite_toSet.image _).union (B'.finite_toSet.image _)).isBounded
    · have hres : Measurable[regionSigma ((fun b : D.Link => (b.initial : AmbientSpace)) '' B' ∪
          (fun b : D.Link => (b.terminal : AmbientSpace)) '' B')]
          fun U : D.GaugeField => restrictField U (B' : Set D.Link) := by
        refine measurable_of_coords _ fun b => ?_
        refine Measurable.of_comap_le (le_iSup₂_of_le b.1 ?_ le_rfl)
        exact ⟨Or.inl ⟨b.1, b.2, rfl⟩, Or.inr ⟨b.1, b.2, rfl⟩⟩
      have hΦ' : Measurable Φ := by
        have h := hΦ.1
        rwa [borel_linkVariables] at h
      exact hΦ'.comp hres
theorem cellObservables_eq (S : Set AmbientSpace) :
    ReflectionGrid.cellObservables (D := D) S =
      {A | IsBoundedObservable A ∧ IsRegionMeasurable (interior S) A} := by
  ext A
  constructor
  · rintro ⟨f, hf, ⟨C, hC⟩, rfl⟩
    have hres : Measurable[regionSigma (interior S)] (ReflectionGrid.restrictField (D := D) S) := by
      refine measurable_of_coords _ fun b => ?_
      exact Measurable.of_comap_le (le_iSup₂_of_le b.1 b.2 le_rfl)
    have hm : Measurable[regionSigma (interior S)] (f ∘ ReflectionGrid.restrictField (D := D) S) :=
      hf.comp hres
    exact ⟨⟨hm.mono (linkSigma_le_borel _) le_rfl, C, fun U => hC _⟩, hm⟩
  · rintro ⟨hA, hm⟩
    obtain ⟨A', hA', e⟩ := (isRegionMeasurable_iff hF hS D (interior S) hA).1 hm
    have hA'm : Measurable A' := by
      have h := hA'.1
      rwa [borel_linkVariables] at h
    obtain ⟨C, hC⟩ := hA'.2
    refine ⟨fun u => A' fun b => u ⟨b.1, b.2.2⟩, ?_, ⟨C, fun u => hC _⟩, funext fun U => e U⟩
    refine hA'm.comp (measurable_pi_iff.2 fun b => ?_)
    exact measurable_pi_apply _
theorem observableLocality_holds : ObservableLocality D :=
  ⟨fun S _ hA => isRegionMeasurable_iff hF hS D S hA,
    fun S₁ S₂ _ hA h₁ h₂ => isRegionMeasurable_inter hS D S₁ S₂ hA h₁ h₂,
    fun t => localObsAbove_eq hF hS D t,
    fun _ _ S _ => cellObservables_eq hF hS D S⟩
end Reads
section TheTorus
open InfiniteLattice (latticeMotions hypercubicGroup)
variable (D : InsertionData)
theorem shift_mem_latticeMotions (v : InfiniteLattice.LatticePoint D.mesh) :
    (InfiniteLattice.shift v).toFun ∈ latticeMotions D.mesh :=
  ⟨LinearMap.id, ⟨1, fun κ => Or.inl rfl⟩, v, v.2, fun _ => rfl⟩
theorem timeReflect_mem_latticeMotions (s : halfSpacingTimes D.mesh) :
    (timeReflect s).toFun ∈ latticeMotions D.mesh := by
  obtain ⟨q, hq⟩ := s.2
  refine ⟨InfiniteLattice.coordinateSignFlip timeAxis,
    InfiniteLattice.coordinateSignFlip_mem_hypercubicGroup _,
    (2 * (s : ℝ)) • InfiniteLattice.basisVector timeAxis,
    ⟨Pi.single timeAxis q, fun μ => ?_⟩, fun x => ?_⟩
  · by_cases h : μ = timeAxis
    · subst h
      simp [InfiniteLattice.basisVector, hq]
      ring
    · simp [InfiniteLattice.basisVector, Pi.single_eq_of_ne h]
  · funext μ
    rw [timeReflect_coord]
    by_cases h : μ = timeAxis
    · subst h
      simp [InfiniteLattice.coordinateSignFlip, InfiniteLattice.basisVector]
      ring
    · simp [InfiniteLattice.coordinateSignFlip, InfiniteLattice.basisVector,
        Pi.single_eq_of_ne h, h]
theorem shiftsAndReflectsDescend_holds (hC : LatticeCovering.CoveringStatement) :
    ShiftsAndReflectsDescend D := by
  intro r hr
  have hmem : r.toFun ∈ latticeMotions D.mesh := by
    rcases hr with ⟨v, rfl⟩ | ⟨s, rfl⟩
    · exact shift_mem_latticeMotions D v
    · exact timeReflect_mem_latticeMotions D s
  obtain ⟨-, -, -, hmap, -⟩ := hC (fixedSpacingSetup D)
  obtain ⟨hind, huniq, hiso, honto, -, -, -, hpull⟩ := hmap ⟨r.toFun, hmem⟩
  refine ⟨⟨_, hind, fun σ h => huniq σ h⟩,
    ⟨_, hiso, honto⟩, hind, fun A _ U hU => ?_⟩
  have h := hpull ⟨_, hiso, honto⟩ rfl ⟨U, hU⟩
  exact congrArg A h
end TheTorus
section CellData
open InfiniteLattice (abovePlane)
variable {D : InsertionData}
theorem cellSide_pos (g : ReflectionGrid D) : 0 < g.cellSide :=
  zpow_pos (by linarith [D.one_lt_factor]) _
theorem cell_eq_pi (g : ReflectionGrid D) (k : Fin 4 → ℤ) :
    g.cell k = univ.pi fun μ =>
      Icc (g.origin μ + g.cellSide * k μ) (g.origin μ + g.cellSide * k μ + g.cellSide) := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionPeriodicWeightsAsCellFunctions.cell_eq_pi <;> assumption
theorem interior_cell (g : ReflectionGrid D) (k : Fin 4 → ℤ) :
    interior (g.cell k) = univ.pi fun μ =>
      Ioo (g.origin μ + g.cellSide * k μ) (g.origin μ + g.cellSide * k μ + g.cellSide) := by apply _root_.YangMills.Construction.MirrorGridsAllSides.WallPreserving.interior_cell <;> assumption
theorem isBounded_interior_cell (g : ReflectionGrid D) (k : Fin 4 → ℤ) :
    Bornology.IsBounded (interior (g.cell k)) := by
  have h : Bornology.IsBounded (g.cell k) := by
    rw [cell_eq_pi]
    exact (isCompact_univ_pi fun _ => isCompact_Icc).isBounded
  exact h.subset interior_subset
theorem cellRatio_odd (g : ReflectionGrid D) : Odd g.cellRatio := by
  have h : Odd ((D.L : ℕ) : ℤ) := by exact_mod_cast D.isAdmissible.1
  exact h.pow
namespace GridCellFacts
variable (c : GridCell D)
theorem centre_time : c.centre timeAxis =
    c.grid.origin timeAxis + c.grid.cellSide * c.index timeAxis + c.grid.cellSide / 2 := rfl
theorem bottomTime_eq : c.bottomTime =
    c.grid.origin timeAxis + c.grid.cellSide * c.index timeAxis := by
  simp only [GridCell.bottomTime, centre_time, GridCell.side]
  ring
theorem cellArithmetic_holds : CellArithmetic c := by
  obtain ⟨p, hp⟩ := cellRatio_odd c.grid
  obtain ⟨i, hi⟩ := c.grid.origin_mem timeAxis
  have hs : c.grid.cellSide = (2 * (p : ℝ) + 1) * D.mesh := by
    rw [c.grid.cellSide_eq, hp]
    push_cast
    ring
  have hρ : (c.grid.cellRatio : ℝ) = 2 * (p : ℝ) + 1 := by
    rw [hp]
    push_cast
    ring
  refine ⟨c.side_mem_zmultiples, ?_, ⟨i + c.grid.cellRatio * c.index timeAxis + p + 1, ?_⟩,
    ⟨i + c.grid.cellRatio * c.index timeAxis, ?_⟩, ⟨c.timeShift 1, ?_⟩,
    ⟨timeReflect c.baseTime, ?_⟩, ⟨timeReflect c.midTime, ?_⟩⟩
  · simp only [GridCell.bottomTime]
    ring
  · rw [centre_time, hi, hs]
    push_cast
    rw [hρ]
    ring
  · rw [bottomTime_eq, hi, hs]
    push_cast
    rw [hρ]
    ring
  · funext x
    simp [GridCell.timeShift, GridCell.timeStep, InfiniteLattice.shift,
      SeparatedTuples.translate]
  · funext x
    rw [InfiniteLattice.timeReflect_apply]
    rfl
  · funext x
    rw [InfiniteLattice.timeReflect_apply]
    rfl
theorem cellAndWalls_holds : CellAndWalls c := by
  have hcell : ∀ x μ, x ∈ c.cell → x μ - c.centre μ ∈ Icc (-(c.side / 2)) (c.side / 2) := by
    intro x μ hx
    obtain ⟨h1, h2⟩ := hx μ
    simp only [GridCell.centre, ReflectionGrid.cellCentre, GridCell.side]
    exact ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    refine ⟨fun hx μ => hcell x μ hx, fun hx μ => ?_⟩
    obtain ⟨h1, h2⟩ := hx μ
    simp only [GridCell.centre, ReflectionGrid.cellCentre, GridCell.side] at h1 h2
    exact ⟨by linarith, by linarith⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hcell x timeAxis hx
    simp only [GridCell.bottomTime]
    exact ⟨by linarith, by linarith⟩
  · ext P
    constructor
    · rintro ⟨⟨μ, k⟩, rfl⟩
      refine ⟨⟨μ, k - c.index μ - 1⟩, ?_⟩
      ext x
      simp only [ReflectionGrid.wall, mem_setOf_eq, GridCell.centre, ReflectionGrid.cellCentre,
        GridCell.side]
      push_cast
      constructor
      · intro h
        rw [h]
        ring
      · intro h
        rw [h]
        ring
    · rintro ⟨⟨μ, n⟩, rfl⟩
      refine ⟨⟨μ, n + c.index μ + 1⟩, ?_⟩
      ext x
      simp only [ReflectionGrid.wall, mem_setOf_eq, GridCell.centre, ReflectionGrid.cellCentre,
        GridCell.side]
      push_cast
      constructor
      · intro h
        rw [h]
        ring
      · intro h
        rw [h]
        ring
  · refine ⟨⟨timeAxis, c.index timeAxis⟩, ?_⟩
    ext x
    simp only [ReflectionGrid.wall, mem_setOf_eq, bottomTime_eq]
    constructor
    · intro h
      rw [h]
      ring
    · intro h
      rw [h]
      ring
theorem timeShift_coord (i : ℤ) (x : AmbientSpace) (μ : Fin 4) :
    (c.timeShift i).toFun x μ =
      x μ + if μ = timeAxis then (i : ℝ) * c.side else 0 := by
  by_cases h : μ = timeAxis
  · subst h
    simp [GridCell.timeShift, GridCell.timeStep, InfiniteLattice.shift,
      timeUnitVec, ChessboardTori.coordVec]
  · simp [GridCell.timeShift, GridCell.timeStep, InfiniteLattice.shift,
      timeUnitVec, ChessboardTori.coordVec, Pi.single_eq_of_ne h, h]
theorem shiftedCell_eq (i : ℤ) :
    c.shiftedCell i = c.grid.cell (c.index + Pi.single timeAxis i) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ μ
    obtain ⟨h1, h2⟩ := hy μ
    rw [timeShift_coord]
    by_cases h : μ = timeAxis
    · subst h
      simp only [if_true, Pi.add_apply, Pi.single_eq_same, GridCell.side, mem_Icc]
      push_cast
      exact ⟨by nlinarith, by nlinarith⟩
    · have hk : ((c.index μ + (Pi.single timeAxis i : Fin 4 → ℤ) μ : ℤ) : ℝ) = c.index μ := by
        simp [Pi.single_eq_of_ne h]
      simp only [h, if_false, Pi.add_apply, hk, add_zero]
      exact ⟨h1, h2⟩
  · intro hx
    refine ⟨fun μ => x μ - if μ = timeAxis then (i : ℝ) * c.side else 0, fun μ => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hx μ
      by_cases h : μ = timeAxis
      · subst h
        simp only [if_true, Pi.add_apply, Pi.single_eq_same, GridCell.side, mem_Icc] at h1 h2 ⊢
        push_cast at h1 h2
        exact ⟨by nlinarith, by nlinarith⟩
      · have hk : ((c.index μ + (Pi.single timeAxis i : Fin 4 → ℤ) μ : ℤ) : ℝ) = c.index μ := by
          simp [Pi.single_eq_of_ne h]
        simp only [Pi.add_apply, hk] at h1 h2
        simp only [h, if_false, sub_zero]
        exact ⟨h1, h2⟩
    · funext μ
      rw [timeShift_coord]
      ring
theorem shiftedCell_mem_cellSet (i : ℤ) : c.shiftedCell i ∈ c.grid.cellSet :=
  ⟨_, (shiftedCell_eq c i).symm⟩
theorem interior_cell_subset_abovePlane :
    interior c.cell ⊆ abovePlane (c.baseTime : ℝ) := by
  intro x hx
  have hx' : x ∈ interior (c.grid.cell c.index) := hx
  rw [interior_cell] at hx'
  have h := (hx' timeAxis (mem_univ _)).1
  change c.bottomTime < x timeAxis
  rw [bottomTime_eq]
  exact h
theorem imageSet_interior_shifted (i : ℤ) :
    (c.timeShift i).setImage (interior c.cell) ⊆ interior (c.shiftedCell i) := by
  rw [shiftedCell_eq]
  change (c.timeShift i).setImage (interior (c.grid.cell c.index)) ⊆ _
  rw [interior_cell, interior_cell]
  rintro _ ⟨y, hy, rfl⟩ μ _
  obtain ⟨h1, h2⟩ := hy μ (mem_univ _)
  rw [timeShift_coord]
  by_cases h : μ = timeAxis
  · subst h
    simp only [if_true, Pi.add_apply, Pi.single_eq_same, GridCell.side, mem_Ioo]
    push_cast
    exact ⟨by nlinarith, by nlinarith⟩
  · have hk : ((c.index μ + (Pi.single timeAxis i : Fin 4 → ℤ) μ : ℤ) : ℝ) = c.index μ := by
      simp [Pi.single_eq_of_ne h]
    simp only [h, if_false, Pi.add_apply, hk, add_zero]
    exact ⟨h1, h2⟩
theorem imageSet_interior_reflected :
    (timeReflect c.midTime).setImage (interior c.cell) ⊆ interior c.cell := by
  change (timeReflect c.midTime).setImage (interior (c.grid.cell c.index)) ⊆
    interior (c.grid.cell c.index)
  rw [interior_cell]
  rintro _ ⟨y, hy, rfl⟩ μ _
  obtain ⟨h1, h2⟩ := hy μ (mem_univ _)
  rw [timeReflect_coord]
  by_cases h : μ = timeAxis
  · subst h
    have hm : ((c.midTime : halfSpacingTimes D.mesh) : ℝ) = c.bottomTime + c.side / 2 := rfl
    simp only [if_true, hm, bottomTime_eq, GridCell.side, mem_Ioo]
    exact ⟨by linarith, by linarith⟩
  · simp only [h, if_false]
    exact ⟨h1, h2⟩
theorem isBoundedObservable_actOn (hA : InfiniteLattice.SymmetryActionOnObservables)
    (r : D.LatticeSym) {F : D.GaugeField → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (r.actOn F) :=
  (((hA ⟨D.mesh, ChessboardTori.ChessboardSetup.mesh_pos D⟩).2.2.1 r).1 F F hF hF).1
theorem chessboardNormAt_bounds (hB : ChessboardTori.TorusReduction.Statement)
    (hCh : MirrorGridsAllSides.chessboardEstimate_allSides)
    {m : ℕ+ → ℕ+} (hm : c.IsAdmissibleSideSequence m) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) c.cell) (hFo : IsBoundedObservable F)
    (r : ℕ+) :
    0 ≤ c.chessboardNormAt m F r ∧
      c.chessboardNormAt m F r ≤ InfiniteLattice.observableSupNorm F := by
  refine ⟨Real.rpow_nonneg (norm_nonneg _) _, ?_⟩
  have hside : (c.grid.withExponent (m r)).HasAdmissibleSide := c.hasAdmissibleSide
  have h2 : 2 * (c.grid.withExponent (m r)).cellSide ≤
      PeriodicLattice.torusSide (D.withExponent (m r)).L (D.withExponent (m r)).m := hm.1 r
  have hchess := hCh (D.withExponent (m r)) (c.grid.withExponent (m r)) hside h2
  have hcell : c.cell ∈ (c.grid.withExponent (m r)).cellSet := c.cell_mem_cellSet
  have hC : (D.withExponent (m r)).proj '' c.cell ∈ (c.grid.withExponent (m r)).torusCellSet :=
    ⟨c.cell, hcell, rfl⟩
  have hread := ((hB (D.withExponent (m r)) (c.grid.withExponent (m r)) h2).1 c.cell hcell).2.1 F hF
  have hle := (((hchess.2.1 _ hC).1 _ hread).2.2.1)
  refine hle.trans (Real.iSup_le (fun U => ?_) (Real.iSup_nonneg fun _ => norm_nonneg _))
  obtain ⟨C, hC'⟩ := hFo.2
  exact le_ciSup (f := fun V : D.GaugeField => ‖F V‖) ⟨C, by rintro _ ⟨V, rfl⟩; exact hC' V⟩ _
theorem cellObservableAlgebras_holds (hA : InfiniteLattice.SymmetryActionOnObservables)
    (hFn : InfiniteLattice.LinkSetFunctions.Claim)
    (hS : InfiniteLattice.LinkSigmaAndDependence)
    (hB : ChessboardTori.TorusReduction.Statement)
    (hCh : MirrorGridsAllSides.chessboardEstimate_allSides) :
    CellObservableAlgebras c := by
  have hrules := observableActionLaws_holds hA D
  refine ⟨fun i => shiftedCell_mem_cellSet c i, fun F hF => ?_⟩
  have hF' := hF
  rw [cellObservables_eq hFn hS D] at hF'
  obtain ⟨hFo, hFm⟩ := hF'
  refine ⟨⟨hFo, interior c.cell, interior_cell_subset_abovePlane c,
    isBounded_interior_cell c.grid c.index, hFm⟩, ?_, ?_, ?_, ?_⟩
  · rintro A ⟨hAo, S, hSa, hSb, hAm⟩
    have hro := isBoundedObservable_actOn hA (c.timeShift 1) hAo
    have hrm : IsRegionMeasurable ((c.timeShift 1).setImage S) ((c.timeShift 1).actOn A) :=
      (hrules _ (c.timeShift 1) A A hAo hAo).2.2.2.2 S hAm
    obtain ⟨C₁, hC₁⟩ := hFo.2
    obtain ⟨C₂, hC₂⟩ := hro.2
    refine ⟨⟨hFo.1.mul hro.1, C₁ * C₂, fun U => ?_⟩, interior c.cell ∪
      (c.timeShift 1).setImage S, ?_, ?_, ?_⟩
    · rw [Pi.mul_apply, norm_mul]
      exact mul_le_mul (hC₁ U) (hC₂ U) (norm_nonneg _) ((norm_nonneg _).trans (hC₁ U))
    · refine union_subset (interior_cell_subset_abovePlane c) ?_
      rintro _ ⟨y, hy, rfl⟩
      have h1 : (c.baseTime : ℝ) < y timeAxis := hSa hy
      have h2 : 0 < c.side := cellSide_pos c.grid
      change (c.baseTime : ℝ) < (c.timeShift 1).toFun y timeAxis
      rw [timeShift_coord]
      simp only [if_true, Int.cast_one, one_mul]
      linarith
    · refine (isBounded_interior_cell c.grid c.index).union ?_
      obtain ⟨R, hR⟩ := hSb.exists_norm_le
      refine isBounded_iff_forall_norm_le.2
        ⟨R + ‖((c.timeStep 1 : InfiniteLattice.LatticePoint D.mesh) : AmbientSpace)‖, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact (norm_add_le _ _).trans (add_le_add (hR y hy) le_rfl)
    · exact Measurable.mul (isRegionMeasurable_mono subset_union_left hFm)
        (isRegionMeasurable_mono subset_union_right hrm)
  · rw [cellObservables_eq hFn hS D]
    have ho := isBoundedObservable_actOn hA (timeReflect c.midTime) hFo
    have hm' : IsRegionMeasurable (interior c.cell) ((timeReflect c.midTime).actOn F) :=
      isRegionMeasurable_mono (imageSet_interior_reflected c)
        ((hrules _ (timeReflect c.midTime) F F hFo hFo).2.2.2.2 _ hFm)
    obtain ⟨C, hC⟩ := ho.2
    refine ⟨⟨Complex.continuous_conj.measurable.comp ho.1, C, fun U => ?_⟩,
      Complex.continuous_conj.measurable.comp hm'⟩
    simpa [conjFun] using hC U
  · intro i
    rw [cellObservables_eq hFn hS D]
    exact ⟨isBoundedObservable_actOn hA _ hFo,
      isRegionMeasurable_mono (imageSet_interior_shifted c i)
        ((hrules _ (c.timeShift i) F F hFo hFo).2.2.2.2 _ hFm)⟩
  · intro m hm
    have hb := chessboardNormAt_bounds c hB hCh hm hF hFo
    have hbd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (c.chessboardNormAt m F) :=
      Filter.isBoundedUnder_of ⟨_, fun r => (hb r).2⟩
    have hlow : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (c.chessboardNormAt m F) :=
      Filter.isBoundedUnder_of ⟨0, fun r => (hb r).1⟩
    exact ⟨Filter.le_limsup_of_frequently_le (Filter.Frequently.of_forall fun r => (hb r).1) hbd,
      Filter.limsup_le_of_le hlow.isCoboundedUnder_le (Filter.Eventually.of_forall fun r => (hb r).2)⟩
end GridCellFacts
end CellData
theorem reflectionsObservablesCells_holds (hA : InfiniteLattice.SymmetryActionOnObservables)
    (hFn : InfiniteLattice.LinkSetFunctions.Claim)
    (hS : InfiniteLattice.LinkSigmaAndDependence)
    (hC : LatticeCovering.CoveringStatement)
    (hCh : MirrorGridsAllSides.chessboardEstimate_allSides)
    (hB : ChessboardTori.TorusReduction.Statement) :
    ReflectionsObservablesCells.Statement := fun D =>
  ⟨reflectShiftRelations_holds D, observableActionLaws_holds hA D,
    functionAndSpanActionLaws_holds D, observableLocality_holds hFn hS D,
    shiftsAndReflectsDescend_holds D hC, fun c =>
      ⟨GridCellFacts.cellArithmetic_holds c,
        GridCellFacts.cellAndWalls_holds c,
        GridCellFacts.cellObservableAlgebras_holds c hA hFn hS hB hCh⟩⟩
end ReflectionsAndOneInsertion
end YangMills.Construction
end
