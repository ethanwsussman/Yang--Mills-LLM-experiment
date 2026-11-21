import YangMills.Construction.Towers.BlockGaugesUnderTheDilation
import YangMills.Construction.Towers.CarriedFamilyIsACriticalBranch
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSitesProof
import YangMills.Construction.Towers.CurvesUnderTheDilation
import YangMills.Construction.Towers.DifferentialsOfTheIteratesUnderTheDilation
import YangMills.Construction.Towers.DifferentialsUnderTheDilation
import YangMills.Construction.Towers.DilationNearTheTrivialConfiguration
import YangMills.Construction.Towers.GradientsUnderTheDilation
import YangMills.Construction.Towers.HessiansUnderTheDilation
import YangMills.Construction.Towers.IteratesOfTheAveragesUnderTheDilation
import YangMills.Construction.Towers.LinearTermsUnderTheDilation
import YangMills.Construction.Towers.RealAnalyticMapsAlongPaths
import YangMills.Construction.Towers.RealAnalyticSubmanifoldsUnderTheDilation
import YangMills.Construction.Towers.RealTransposesUnderTheDilation
import YangMills.Construction.Towers.SecondOrderOfACompositeAtOneProof
import YangMills.Construction.Towers.WhatTheDilationKeeps
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices (ComplexMatrix2)
namespace Tower
namespace PushForward
variable {L n k j : ℕ}
section Family
variable (hL : 0 < L) (hj : j ≤ k) (b : CriticalBranchData L n k)
theorem energy_pushForward (l : ℕ) (V : Edge L n k l → ComplexMatrix2) :
    (b.pushForward hL hj).energy l (transportTotal (scaleEdge hL hj l) V) =
      b.energy l V :=
  transportTotalScalar_transportTotal _ _ _
theorem prolong_pushForward (i : ℕ) (W : Edge L n k (i + 1) → ComplexMatrix2) :
    (b.pushForward hL hj).prolong i (transportTotal (scaleEdge hL hj (i + 1)) W) =
      transportTotal (scaleEdge hL hj i) (b.prolong i W) :=
  transportTotalFunValued_transportTotal _ _ _ _
theorem prolongComp_pushForward : ∀ (l : ℕ) (W : Edge L n k l → ComplexMatrix2),
    (b.pushForward hL hj).prolongComp l (transportTotal (scaleEdge hL hj l) W) =
      transportTotal (scaleEdge hL hj 0) (b.prolongComp l W)
  | 0, _ => rfl
  | i + 1, W => by
    change (b.pushForward hL hj).prolongComp i ((b.pushForward hL hj).prolong i _) =
      transportTotal (scaleEdge hL hj 0) (b.prolongComp i (b.prolong i W))
    rw [prolong_pushForward, prolongComp_pushForward i]
end Family
section Images
variable (hL : 0 < L) (hj : j ≤ k)
theorem exists_transport_eq (l : ℕ) (W' : Edge L (scaledExponent n k j) j l → ComplexMatrix2) :
    ∃ W : Edge L n k l → ComplexMatrix2, transportTotal (scaleEdge hL hj l) W = W' :=
  ⟨W' ∘ scaleEdge hL hj l, by
    funext c
    simp [transportTotal]⟩
theorem exists_vertex_transport_eq (l : ℕ)
    (v' : Vertex L (scaledExponent n k j) j l → ComplexMatrix2) :
    ∃ v : Vertex L n k l → ComplexMatrix2, transportTotal (scaleVertex hL hj l).toEquiv v = v' :=
  ⟨v' ∘ (scaleVertex hL hj l).toEquiv, by
    funext c
    simp [transportTotal]⟩
theorem transport_injective (l : ℕ) :
    Function.Injective (transportTotal (scaleEdge (n := n) hL hj l) (V := ComplexMatrix2)) := by
  intro V W h
  funext c
  have := congrFun h (scaleEdge hL hj l c)
  simpa [transportTotal] using this
variable {hL hj}
theorem eventually_transport_image {l : ℕ} (h : ScalingPreservesOpenSets (m := n) hL hj l)
    {P : (Edge L n k l → ComplexMatrix2) → Prop} (hP : EventuallyNearIdentity (fieldSpace L n k l) P) :
    EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j l) fun W' =>
      ∃ W ∈ fieldSpace L n k l, transportTotal (scaleEdge hL hj l) W = W' ∧ P W := by
  have h1 : EventuallyNearIdentity (fieldSpace L n k l)
      (· ∈ {V | V ∈ fieldSpace L n k l ∧ P V}) :=
    Filter.Eventually.and eventually_mem_nhdsWithin hP
  have h2 := ((h.1 {V | V ∈ fieldSpace L n k l ∧ P V} fun V hV => hV.1).2).1 h1
  refine Filter.Eventually.mono h2 ?_
  rintro _ ⟨W, ⟨hW, hPW⟩, rfl⟩
  exact ⟨W, hW, rfl, hPW⟩
theorem isOpenNhdOfOne_image {l : ℕ} (h : ScalingPreservesOpenSets (m := n) hL hj l)
    {U : Set (Edge L n k l → ComplexMatrix2)} (hU : IsOpenNhdOfOne U) :
    IsOpenNhdOfOne (transportTotal (scaleEdge hL hj l) '' U) :=
  ⟨(h.2.1 U hU.1.1).1 hU.1, mem_image_of_mem _ hU.2⟩
theorem transport_mem_edgeFormSpace_iff {l : ℕ}
    (h : ScalingPreservesFieldsAndForms (m := n) hL hj l) (B : Edge L n k l → ComplexMatrix2) :
    transportTotal (scaleEdge hL hj l) B ∈ edgeFormSpace L (scaledExponent n k j) j l ↔
      B ∈ edgeFormSpace L n k l := by
  obtain ⟨-, -, -, ⟨T, hT⟩, -⟩ := h
  constructor
  · intro hB
    obtain ⟨B₁, hB₁⟩ := T.surjective ⟨_, hB⟩
    have h₁ := hT B₁
    rw [hB₁] at h₁
    have := transport_injective hL hj l h₁
    rw [this]
    exact B₁.2
  · intro hB
    rw [← hT ⟨B, hB⟩]
    exact (T ⟨B, hB⟩).2
theorem exists_edgeForm_transport_eq {l : ℕ}
    (h : ScalingPreservesFieldsAndForms (m := n) hL hj l)
    {B' : Edge L (scaledExponent n k j) j l → ComplexMatrix2}
    (hB' : B' ∈ edgeFormSpace L (scaledExponent n k j) j l) :
    ∃ B ∈ edgeFormSpace L n k l, transportTotal (scaleEdge hL hj l) B = B' := by
  obtain ⟨B, rfl⟩ := exists_transport_eq hL hj l B'
  exact ⟨B, (transport_mem_edgeFormSpace_iff h B).1 hB', rfl⟩
end Images
theorem traceFinsumNorm_transport {ι ι' : Type*} (e : ι ≃ ι') (f : ι → ComplexMatrix2) :
    traceFinsumNorm (transportTotal e f) = traceFinsumNorm f := by
  unfold traceFinsumNorm traceFinsumPairing
  congr 2
  exact finsum_comp_equiv e.symm (f := fun i => ComplexMatrix2.halfTrace (f i * f i))
theorem compact_mem_complex {u : ComplexMatrix2} (hu : u ∈ PeriodicLattice.compactGaugeGroup) :
    u ∈ PeriodicLattice.complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.mp hu).2
section Near
variable {i : ℕ}
theorem eventually_mem_of_isOpenNhdOfOne {U : Set (Edge L n k i → ComplexMatrix2)}
    (h : IsOpenNhdOfOne U) :
    ∀ᶠ V in 𝓝[fieldSpace L n k i] trivialField L n k i, V ∈ U := by apply _root_.YangMills.Construction.Tower.ProlongCompositesProof.eventually_mem_of_isOpenNhdOfOne <;> assumption
end Near
structure PushForwardHypotheses (hL : 0 < L) (hj : j ≤ k) (n : ℕ) : Prop where
  hS : Conventions.IsAdmissibleBlockingFactor L
  hn : 0 < n
  hj1 : 1 ≤ j
  conf : ∀ l ≤ j, ScalingPreservesFieldsAndForms (m := n) hL hj l
  opens : ∀ l ≤ j, ScalingPreservesOpenSets (m := n) hL hj l
  analytic : ∀ a ≤ j, ∀ a' ≤ j, ScalingPreservesAnalyticity (m := n) hL hj a a'
  gauge : ∀ l ≤ j, ScalingPreservesGaugeAct hL hj n l
  isometry : ∀ l ≤ j, ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
    IsDistancePreserving f → MapsSublatticeOnto k l f → ScalingPreservesSymmetry hL hj l f
  lattices : ScalingPreservesSublattices hL hj n
  action : ScalingPreservesAction hL hj n
  step : ∀ i < j, ScalingPreservesAtStep hL hj n i
  finer : TorusSymmetries L n k
  paths : AnalyticMapsAlongCurves
  wilson : WilsonActionAnalytic
  linear : CoboundaryScaling.Statement
  block : BlockGaugeLiftCommutesWithScaling
  iterate : ScalingCommutesWithSmoothingIter
  curves : ScalingPreservesTangentsAndCriticalPoints
  hessians : HessianScaling.Statement
  submanifolds : AnalyticSubmanifoldScaling
  differentials : ScalingTransportsDerivatives
  gradients : ScaledGradients
  transposes : ScalingCommutesWithRealTranspose
  iterateDifferentials : ScaledIterateDifferentials
variable {hL : 0 < L} {hj : j ≤ k} {b : CriticalBranchData L n k} {i : ℕ}
theorem trivialField_mem_fieldSpace (l : ℕ) : trivialField L n k l ∈ fieldSpace L n k l := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.trivialField_mem <;> assumption
theorem eventually_prolong_mem (hb : b.IsCritical) (hi : i < k) :
    EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
      b.prolong i W ∈ fieldSpace L n k i := by
  obtain ⟨U, hU, hA⟩ := hb.analytic_prolong i hi
  exact Filter.Eventually.mono (eventually_mem_of_isOpenNhdOfOne hU) fun W hW => hA.2.1 hW
theorem tendsto_prolong (F : PushForwardHypotheses hL hj n) (hb : b.IsCritical) (hi : i < k) :
    Tendsto (b.prolong i) (𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1))
      (𝓝[fieldSpace L n k i] trivialField L n k i) := by
  obtain ⟨U, hU, hA⟩ := hb.analytic_prolong i hi
  have hnear := eventually_mem_of_isOpenNhdOfOne hU
  have hc := ((F.paths L n k (i + 1) i F.hS F.hn hi hi.le).1 U _ hA).1 _ hU.2
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, hnear.mono fun W hW => hA.2.1 hW⟩
  have h := hc.tendsto.mono_left (nhdsWithin_le_of_mem (Filter.mem_of_superset hnear fun _ h => h))
  rwa [hb.prolong_trivial i hi] at h
theorem tendsto_prolongComp (F : PushForwardHypotheses hL hj n) (hb : b.IsCritical) : ∀ l ≤ k,
    Tendsto (b.prolongComp l) (𝓝[fieldSpace L n k l] trivialField L n k l)
      (𝓝[fieldSpace L n k 0] trivialField L n k 0)
  | 0, _ => tendsto_id
  | i + 1, hl => (tendsto_prolongComp F hb i (by omega)).comp (tendsto_prolong F hb (by omega))
theorem gaugeFixedEnergy_pushForward (F : PushForwardHypotheses hL hj n) (hi : i < j)
    {V : Edge L n k i → ComplexMatrix2} (hV : V ∈ axialFunctionDomain L n k i) :
    (b.pushForward hL hj).gaugeFixedEnergy i (transportTotal (scaleEdge hL hj i) V) =
      b.gaugeFixedEnergy i V := by
  unfold CriticalBranchData.gaugeFixedEnergy
  rw [energy_pushForward]
  congr 1
  exact ((F.step i hi).axialFunction_eq V hV.2).symm
theorem smoothingStep_transport (F : PushForwardHypotheses hL hj n) (hi : i < j)
    {V : Edge L n k i → ComplexMatrix2} (hV : V ∈ fieldSpace L n k i) :
    smoothingStep L (scaledExponent n k j) j i (transportTotal (scaleEdge hL hj i) V) =
      transportTotal (scaleEdge hL hj (i + 1)) (smoothingStep L n k i V) :=
  ((F.step i hi).smoothingStep_eq V hV).symm
theorem linearSmoothing_transport (F : PushForwardHypotheses hL hj n) (hi : i < j)
    (B : Edge L n k i → ComplexMatrix2) :
    linearSmoothing L (scaledExponent n k j) j i (transportTotal (scaleEdge hL hj i) B) =
      transportTotal (scaleEdge hL hj (i + 1)) (linearSmoothing L n k i B) :=
  ((F.step i hi).linearSmoothing_eq B).symm
theorem smoothingIter_transport (F : PushForwardHypotheses hL hj n) {l : ℕ} (hl : l ≤ j)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0) :
    smoothingIter L (scaledExponent n k j) j l (transportTotal (scaleEdge hL hj 0) U) =
      transportTotal (scaleEdge hL hj l) (smoothingIter L n k l U) :=
  (F.iterate L n k j hL hj F.hS F.hn F.hj1 l hl U hU).symm
theorem hessianAtOne_pushForward (F : PushForwardHypotheses hL hj n) {l : ℕ} (hl : l ≤ j)
    {B B' : Edge L n k l → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k l) (hB' : B' ∈ edgeFormSpace L n k l) :
    (b.pushForward hL hj).hessianAtOne l (transportTotal (scaleEdge hL hj l) B)
        (transportTotal (scaleEdge hL hj l) B') = b.hessianAtOne l B B' :=
  (F.differentials L n k j hL hj F.hS F.hn l hl l hl).2 (b.energy l)
    ((b.pushForward hL hj).energy l) (fun V _ => energy_pushForward hL hj b l V) _
    (trivialField_mem_fieldSpace l) B hB B' hB'
theorem stepQuadratic_pushForward (F : PushForwardHypotheses hL hj n) (hi : i < j)
    {ξ : Edge L n k i → ComplexMatrix2} (hξ : ξ ∈ edgeFormSpace L n k i) :
    (b.pushForward hL hj).stepQuadratic i (transportTotal (scaleEdge hL hj i) ξ) =
      b.stepQuadratic i ξ := by
  unfold CriticalBranchData.stepQuadratic
  rw [hessianAtOne_pushForward F hi.le hξ hξ,
    (F.linear L n k j hL hj F.hS F.hn F.hj1).2 i hi ξ]
theorem transport_gaugeTransform (F : PushForwardHypotheses hL hj n) {l : ℕ} (hl : l ≤ j)
    {v : Vertex L n k l → ComplexMatrix2} {W : Edge L n k l → ComplexMatrix2}
    (hv : v ∈ gaugeGroupAt L n k l) (hW : W ∈ fieldSpace L n k l) :
    transportTotal (scaleEdge hL hj l) (PeriodicLattice.gaugeTransform v W) =
      PeriodicLattice.gaugeTransform (transportTotal (scaleVertex hL hj l).toEquiv v)
        (transportTotal (scaleEdge hL hj l) W) :=
  F.gauge l hl W v ⟨fun c _ => compact_mem_complex (hW.1 c (mem_univ _)), hW.2⟩
    fun x => compact_mem_complex (hv x)
theorem forGaugesNearOneOrConstant_transport {l : ℕ}
    (hO : ScalingPreservesOpenSets (m := n) hL hj l)
    {P : (Vertex L n k l → ComplexMatrix2) → (Edge L n k l → ComplexMatrix2) → Prop}
    {P' : (Vertex L (scaledExponent n k j) j l → ComplexMatrix2) →
      (Edge L (scaledExponent n k j) j l → ComplexMatrix2) → Prop}
    {R : (Edge L n k l → ComplexMatrix2) → Prop} (hP : ForGaugesNearOneOrConstant P)
    (hR : EventuallyNearIdentity (fieldSpace L n k l) R)
    (himg : ∀ v ∈ gaugeGroupAt L n k l, ∀ W ∈ fieldSpace L n k l, R W → P v W →
      P' (transportTotal (scaleVertex hL hj l).toEquiv v)
        (transportTotal (scaleEdge hL hj l) W)) :
    ForGaugesNearOneOrConstant P' := by
  obtain ⟨h₁, h₂⟩ := hP
  constructor
  · obtain ⟨pa, hpa, pb, hpb, hall⟩ := Filter.eventually_prod_iff.1 h₁
    have hA : EventuallyNearIdentity (gaugeGroupAt L n k l)
        (· ∈ {v | v ∈ gaugeGroupAt L n k l ∧ pa v}) :=
      Filter.Eventually.and eventually_mem_nhdsWithin hpa
    have hB : EventuallyNearIdentity (fieldSpace L n k l)
        (· ∈ {W | W ∈ fieldSpace L n k l ∧ R W ∧ pb W}) :=
      Filter.Eventually.and eventually_mem_nhdsWithin (Filter.Eventually.and hR hpb)
    have hA' := ((hO.2.2.2 _ fun v hv => hv.1).2).1 hA
    have hB' := ((hO.1 _ fun v hv => hv.1).2).1 hB
    refine Filter.eventually_prod_iff.2 ⟨_, hA', _, hB', ?_⟩
    rintro _ ⟨v, ⟨hv, hpv⟩, rfl⟩ _ ⟨W, ⟨hW, hRW, hpW⟩, rfl⟩
    exact himg v hv W hW hRW (hall hpv hpW)
  · refine Filter.Eventually.mono
      (eventually_transport_image hO (Filter.Eventually.and h₂ hR)) ?_
    rintro _ ⟨W, hW, rfl, hc, hRW⟩ v' hv' hconst
    obtain ⟨v, rfl⟩ := exists_vertex_transport_eq hL hj l v'
    have hval : ∀ x, transportTotal (scaleVertex hL hj l).toEquiv v
        (scaleVertex hL hj l x) = v x := fun x =>
      transportTotal_apply (scaleVertex hL hj l).toEquiv v x
    have hv : v ∈ gaugeGroupAt L n k l := fun x => by
      have := hv' (scaleVertex hL hj l x)
      rwa [hval] at this
    refine himg v hv W hW hRW (hc v hv fun x x' => ?_)
    have := hconst (scaleVertex hL hj l x) (scaleVertex hL hj l x')
    rwa [hval, hval] at this
theorem levelFibre_transport (F : PushForwardHypotheses hL hj n) (hi : i < j)
    {U : Set (Edge L n k i → ComplexMatrix2)}
    (hsub : U ⊆ fieldSpace L n k i) (W : Edge L n k (i + 1) → ComplexMatrix2) :
    CriticalBranchData.levelFibre (transportTotal (scaleEdge hL hj i) '' U)
        (transportTotal (scaleEdge hL hj (i + 1)) W) =
      transportTotal (scaleEdge hL hj i) '' CriticalBranchData.levelFibre U W := by
  ext V'
  constructor
  · rintro ⟨⟨V, hV, rfl⟩, he⟩
    rw [smoothingStep_transport F hi (hsub hV)] at he
    exact ⟨V, ⟨hV, transport_injective hL hj _ he⟩, rfl⟩
  · rintro ⟨V, ⟨hV, he⟩, rfl⟩
    exact ⟨mem_image_of_mem _ hV, by rw [smoothingStep_transport F hi (hsub hV), he]⟩
theorem tangentSpacesAreKernels_image (F : PushForwardHypotheses hL hj n) (hi : i < j)
    {N : Set (Edge L n k i → ComplexMatrix2)}
    (hsub : N ⊆ fieldSpace L n k i) (h : TangentSpacesAreKernels i N) :
    TangentSpacesAreKernels i (transportTotal (scaleEdge hL hj i) '' N) := by
  rintro _ ⟨V, hV, rfl⟩ B'
  obtain ⟨B, rfl⟩ := exists_transport_eq hL hj i B'
  have hD := fun hB : B ∈ edgeFormSpace L n k i =>
    (F.differentials L n k j hL hj F.hS F.hn i hi.le (i + 1) hi).1 (smoothingStep L n k i)
      (smoothingStep L (scaledExponent n k j) j i) (fun V hV => smoothingStep_transport F hi hV) V
      (hsub hV) B hB
  rw [← ((F.curves L n k j hL hj F.hS F.hn i hi.le N V).1 B), h V hV B,
    transport_mem_edgeFormSpace_iff (F.conf i hi.le)]
  constructor
  · rintro ⟨hB, h0⟩
    refine ⟨hB, ?_⟩
    rw [hD hB, h0]
    rfl
  · rintro ⟨hB, h0⟩
    refine ⟨hB, transport_injective hL hj (i + 1) ?_⟩
    rw [← hD hB, h0]
    rfl
theorem exists_fibreNhd_pushForward (F : PushForwardHypotheses hL hj n) (hi : i < j)
    {U : Set (Edge L n k i → ComplexMatrix2)} (hF : b.IsFibreNhd i U) :
    ∃ U' : Set (Edge L (scaledExponent n k j) j i → ComplexMatrix2), IsOpenNhdOfOne U' ∧
      EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j (i + 1))
        (fun W => IsAnalyticFieldSubmanifold (CriticalBranchData.levelFibre U' W) ∧
          TangentSpacesAreKernels i (CriticalBranchData.levelFibre U' W)) ∧
      ∃ O ∈ 𝓝[fieldSpace L (scaledExponent n k j) j i]
          (trivialField L (scaledExponent n k j) j i),
        EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j (i + 1)) fun W =>
          IsUniqueCriticalPointIn O (CriticalBranchData.levelFibre U' W)
              ((b.pushForward hL hj).gaugeFixedEnergy i)
              ((b.pushForward hL hj).prolong i W) ∧
            HasPosDefHessian (CriticalBranchData.levelFibre U' W)
              ((b.pushForward hL hj).gaugeFixedEnergy i)
              ((b.pushForward hL hj).prolong i W) := by
  have hU := hF.isOpenNhd
  have hsub : U ⊆ fieldSpace L n k i := hU.1.1
  have hU' := isOpenNhdOfOne_image (F.opens i hi.le) hU
  have hO := F.opens (i + 1) hi
  have hfs : ∀ W, CriticalBranchData.levelFibre U W ⊆ fieldSpace L n k i :=
    fun W V hV => hsub hV.1
  refine ⟨_, hU', ?_, _, eventually_mem_of_isOpenNhdOfOne hU', ?_⟩
  · refine Filter.Eventually.mono (eventually_transport_image hO hF.unique_critical) ?_
    rintro _ ⟨W, hW, rfl, hu, -⟩
    rw [levelFibre_transport F hi hsub]
    rcases hF.fibre_structure W hW with hE | ⟨hsm, hker⟩
    · have := hu.1
      rw [hE] at this
      exact this.elim
    · exact ⟨F.submanifolds L n k j hL hj F.hS F.hn i hi.le _ hsm,
        tangentSpacesAreKernels_image F hi (hfs W) hker⟩
  · have hsm : EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
        IsAnalyticFieldSubmanifold (CriticalBranchData.levelFibre U W) := by
      refine Filter.Eventually.mono (Filter.Eventually.and hF.unique_critical
        eventually_mem_nhdsWithin) ?_
      rintro W ⟨⟨hu, -⟩, hW⟩
      rcases hF.fibre_structure W hW with hE | ⟨hsm, -⟩
      · have := hu.1
        rw [hE] at this
        exact this.elim
      · exact hsm
    refine Filter.Eventually.mono
      (eventually_transport_image hO (Filter.Eventually.and hF.unique_critical hsm)) ?_
    rintro _ ⟨W, hW, rfl, ⟨hu, hpd⟩, hsW⟩
    rw [levelFibre_transport F hi hsub, prolong_pushForward]
    have hval : ∀ V ∈ CriticalBranchData.levelFibre U W,
        (b.pushForward hL hj).gaugeFixedEnergy i (transportTotal (scaleEdge hL hj i) V) =
          b.gaugeFixedEnergy i V := fun V hV =>
      gaugeFixedEnergy_pushForward F hi (hF.subset_domain hV.1)
    have hcrit := fun x => (F.curves L n k j hL hj F.hS F.hn i hi.le
      (CriticalBranchData.levelFibre U W) x).2 _ _ hval
    refine ⟨⟨mem_image_of_mem _ hu.1.1, (hcrit _).1 hu.2.1, ?_⟩, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩ hV'
      exact congrArg _ (hu.2.2 V ((hcrit V).2 hV').1 ((hcrit V).2 hV'))
    · exact F.hessians L n k j hL hj F.hS F.hn i hi.le U _ _ _ hF.analytic_gaugeFixedEnergy
        hsW.1 (fun V hV => hV.1) hval _ hu.2.1 hpd
theorem isCritical_pushForward (F : PushForwardHypotheses hL hj n) (hb : b.IsCritical)
    (hN : ∀ i < k, ∃ U : Set (Edge L n k i → ComplexMatrix2), b.IsFibreNhd i U) :
    (b.pushForward hL hj).IsCritical where
  analytic_energy l hl := by
    obtain ⟨U, hU, hA⟩ := hb.analytic_energy l (hl.trans hj)
    exact ⟨_, isOpenNhdOfOne_image (F.opens l hl) hU,
      (((F.analytic l hl l hl) U hU.1).1 (b.energy l)).1 hA⟩
  energy_nonneg l hl := by
    refine Filter.Eventually.mono
      (eventually_transport_image (F.opens l hl) (hb.energy_nonneg l (hl.trans hj))) ?_
    rintro _ ⟨W, -, rfl, h⟩
    rwa [energy_pushForward]
  energy_bottom := by
    refine Filter.Eventually.mono
      (eventually_transport_image (F.opens 0 (Nat.zero_le j)) hb.energy_bottom) ?_
    rintro _ ⟨W, hW, rfl, h⟩
    rw [energy_pushForward, h, F.action.action_eq W hW]
  analytic_prolong i hi := by
    obtain ⟨U, hU, hA⟩ := hb.analytic_prolong i (hi.trans_le hj)
    exact ⟨_, isOpenNhdOfOne_image (F.opens (i + 1) hi) hU,
      (((F.analytic (i + 1) hi i hi.le) U hU.1).2.2 (b.prolong i) hA.2.1).1 hA⟩
  prolong_trivial i hi := by
    have h2 := prolong_pushForward hL hj b i (trivialField L n k (i + 1))
    rw [hb.prolong_trivial i (hi.trans_le hj)] at h2
    exact h2
  prolong_section i hi := by
    have hik := hi.trans_le hj
    obtain ⟨U, hF⟩ := hN i hik
    have hdom : EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
        b.prolong i W ∈ axialFunctionDomain L n k i :=
      Filter.Eventually.mono hF.unique_critical fun W h => hF.subset_domain h.1.1.1
    refine Filter.Eventually.mono (eventually_transport_image (F.opens (i + 1) hi)
      (Filter.Eventually.and (hb.prolong_section i hik) hdom)) ?_
    rintro _ ⟨W, hW, rfl, ⟨h1, h2, h3, h4⟩, hd⟩
    rw [prolong_pushForward]
    refine ⟨?_, (((F.step i hi).isAxialGauge_iff _).1 h2), ?_, ?_⟩
    · rw [smoothingStep_transport F hi hd.1, h1]
    · rw [energy_pushForward, energy_pushForward, h3]
    · rw [energy_pushForward, gaugeFixedEnergy_pushForward F hi hd, h4]
  fibre_structure i hi := by
    obtain ⟨U, hF⟩ := hN i (hi.trans_le hj)
    exact exists_fibreNhd_pushForward F hi hF
  energy_gauge_invariant l hl := by
    refine forGaugesNearOneOrConstant_transport (R := fun _ => True) (F.opens l hl)
      (hb.energy_gauge_invariant l (hl.trans hj)) (Filter.Eventually.of_forall fun _ => trivial) ?_
    intro v hv W hW _ h
    rw [← _root_.YangMills.Construction.Tower.PushForward.transport_gaugeTransform F hl hv hW, energy_pushForward, energy_pushForward, h]
  prolong_gauge_equivariant i hi := by
    have hik := hi.trans_le hj
    refine forGaugesNearOneOrConstant_transport (F.opens (i + 1) hi)
      (hb.prolong_gauge_equivariant i hik) (eventually_prolong_mem hb hik) ?_
    intro v hv W hW hc h
    have hv' : blockGaugeLift v ∈ gaugeGroupAt L n k i := fun x => hv _
    rw [← _root_.YangMills.Construction.Tower.PushForward.transport_gaugeTransform F hi hv hW, prolong_pushForward, prolong_pushForward, h,
      _root_.YangMills.Construction.Tower.PushForward.transport_gaugeTransform F hi.le hv' hc, F.block L n k j hL hj F.hS F.hn F.hj1 i hi v]
  energy_symmetry_invariant l hl := by
    refine Filter.Eventually.mono (eventually_transport_image (F.opens l hl)
      (hb.energy_symmetry_invariant l (hl.trans hj))) ?_
    rintro _ ⟨W, hW, rfl, h⟩ f' ⟨hf1, hf2⟩
    obtain ⟨f, ⟨hI, hM⟩, rfl⟩ := (F.lattices.bijOn_symmetries l hl).surjOn ⟨hf1, hf2⟩
    rw [← (F.isometry l hl f hI hM).field_comm W (Or.inl hW), energy_pushForward,
      energy_pushForward]
    exact h f ⟨hI, hM⟩
  prolong_symmetry_equivariant i hi := by
    have hik := hi.trans_le hj
    refine Filter.Eventually.mono (eventually_transport_image (F.opens (i + 1) hi)
      (Filter.Eventually.and (hb.prolong_symmetry_equivariant i hik)
        (eventually_prolong_mem hb hik))) ?_
    rintro _ ⟨W, hW, rfl, h, hc⟩ f' ⟨hf1, hf2⟩
    obtain ⟨f, ⟨hI, hM⟩, rfl⟩ := (F.lattices.bijOn_symmetries (i + 1) hi).surjOn ⟨hf1, hf2⟩
    have hMi : MapsSublatticeOnto k i f :=
      ((F.finer (i + 1) hik f hI hM).2 i (Nat.le_succ i)).1
    rw [← (F.isometry (i + 1) hi f hI hM).field_comm W (Or.inl hW), prolong_pushForward,
      prolong_pushForward, h f ⟨hI, hM⟩,
      (F.isometry i hi.le f hI hMi).field_comm _ (Or.inl hc)]
  energy_trivial l hl :=
    (energy_pushForward hL hj b l _).trans (hb.energy_trivial l (hl.trans hj))
  gradient_trivial l hl := by
    obtain ⟨U, hU, hA⟩ := hb.analytic_energy l (hl.trans hj)
    have h := F.gradients L n k j hL hj F.hS F.hn l hl U (b.energy l)
      ((b.pushForward hL hj).energy l) hA
      (fun V _ => energy_pushForward hL hj b l V) _ hU.2
    have h0 : leftGradient (fieldSpace L n k l) (fun V => (b.energy l V : ℂ))
        (trivialField L n k l) = 0 := hb.gradient_trivial l (hl.trans hj)
    rw [h0] at h
    exact h
  hessianAtOne_nonneg l hl B' hB' := by
    obtain ⟨B, hB, rfl⟩ := exists_edgeForm_transport_eq (F.conf l hl) hB'
    rw [hessianAtOne_pushForward F hl hB hB]
    exact hb.hessianAtOne_nonneg l (hl.trans hj) B hB
  hessianAtOne_null_iff l hl B' hB' := by
    obtain ⟨B, hB, rfl⟩ := exists_edgeForm_transport_eq (F.conf l hl) hB'
    have hclosed : IsClosedEdgeForm (transportTotal (scaleEdge hL hj l) B) ↔
        IsClosedEdgeForm B := by
      unfold IsClosedEdgeForm
      rw [(F.linear L n k j hL hj F.hS F.hn F.hj1).1 l hl B]
      constructor
      · intro h
        funext p
        have := congrFun h (scaleFace hL hj l p)
        simpa [transportTotal] using this
      · intro h
        rw [h]
        rfl
    rw [hclosed, ← hb.hessianAtOne_null_iff l (hl.trans hj) B hB]
    constructor
    · intro h B₂ hB₂
      have := h _ ((transport_mem_edgeFormSpace_iff (F.conf l hl) B₂).2 hB₂)
      rwa [hessianAtOne_pushForward F hl hB hB₂] at this
    · intro h B₂' hB₂'
      obtain ⟨B₂, hB₂, rfl⟩ := exists_edgeForm_transport_eq (F.conf l hl) hB₂'
      rw [hessianAtOne_pushForward F hl hB hB₂]
      exact h B₂ hB₂
  hessianAtOne_bottom B' hB' := by
    obtain ⟨B, hB, rfl⟩ := exists_edgeForm_transport_eq (F.conf 0 (Nat.zero_le j)) hB'
    rw [hessianAtOne_pushForward F (Nat.zero_le j) hB hB, hb.hessianAtOne_bottom B hB,
      (F.linear L n k j hL hj F.hS F.hn F.hj1).1 0 (Nat.zero_le j) B, traceFinsumNorm_transport]
  hessianAtOne_isLeast i hi B' hB' := by
    obtain ⟨B, hB, rfl⟩ := exists_edgeForm_transport_eq (F.conf (i + 1) hi) hB'
    have h := hb.hessianAtOne_isLeast i (hi.trans_le hj) B hB
    rw [hessianAtOne_pushForward F hi hB hB]
    constructor
    · obtain ⟨ξ, hξ, hQ, hr⟩ := h.1
      exact ⟨_, (transport_mem_edgeFormSpace_iff (F.conf i hi.le) ξ).2 hξ,
        by rw [linearSmoothing_transport F hi, hQ], by rw [stepQuadratic_pushForward F hi hξ, hr]⟩
    · rintro r ⟨ξ', hξ', hQ', rfl⟩
      obtain ⟨ξ, hξ, rfl⟩ := exists_edgeForm_transport_eq (F.conf i hi.le) hξ'
      rw [stepQuadratic_pushForward F hi hξ]
      rw [linearSmoothing_transport F hi] at hQ'
      exact h.2 ⟨ξ, hξ, transport_injective hL hj _ hQ', rfl⟩
  hessianAtOne_minimizer_iff i hi B' hB' ξ' := by
    obtain ⟨B, hB, rfl⟩ := exists_edgeForm_transport_eq (F.conf (i + 1) hi) hB'
    obtain ⟨ξ, rfl⟩ := exists_transport_eq hL hj i ξ'
    have hiff := hb.hessianAtOne_minimizer_iff i (hi.trans_le hj) B hB ξ
    have hdiff : leftDifferential ((b.pushForward hL hj).prolong i)
        (trivialField L (scaledExponent n k j) j (i + 1))
        (transportTotal (scaleEdge hL hj (i + 1)) B) =
          transportTotal (scaleEdge hL hj i)
            (leftDifferential (b.prolong i) (trivialField L n k (i + 1)) B) :=
      (F.differentials L n k j hL hj F.hS F.hn (i + 1) hi i hi.le).1 (b.prolong i)
        ((b.pushForward hL hj).prolong i) (fun V _ => prolong_pushForward hL hj b i V) _
        (trivialField_mem_fieldSpace _) B hB
    rw [hdiff]
    constructor
    · rintro ⟨hξ', hQ', hE⟩
      have hξ := (transport_mem_edgeFormSpace_iff (F.conf i hi.le) ξ).1 hξ'
      rw [linearSmoothing_transport F hi] at hQ'
      rw [stepQuadratic_pushForward F hi hξ, hessianAtOne_pushForward F hi hB hB] at hE
      rw [hiff.1 ⟨hξ, transport_injective hL hj _ hQ', hE⟩]
    · intro h
      obtain ⟨hξ, hQ, hE⟩ := hiff.2 (transport_injective hL hj _ h)
      exact ⟨(transport_mem_edgeFormSpace_iff (F.conf i hi.le) ξ).2 hξ,
        by rw [linearSmoothing_transport F hi, hQ],
        by rw [stepQuadratic_pushForward F hi hξ, hE, hessianAtOne_pushForward F hi hB hB]⟩
  prolongComp_section l hl := by
    have hlk := hl.trans hj
    obtain ⟨U₀, hU₀, hid⟩ := F.iterateDifferentials L n k j hL hj F.hS F.hn F.hj1 l hl
    obtain ⟨U₁, hU₁, hA₁⟩ := hb.analytic_energy l hlk
    have hnear : EventuallyNearIdentity (fieldSpace L n k l) fun W => b.prolongComp l W ∈ U₀ :=
      (tendsto_prolongComp F hb l hlk).eventually (eventually_mem_of_isOpenNhdOfOne hU₀)
    refine Filter.Eventually.mono (eventually_transport_image (F.opens l hl)
      (Filter.Eventually.and (hb.prolongComp_section l hlk)
        (Filter.Eventually.and hnear (eventually_mem_of_isOpenNhdOfOne hU₁)))) ?_
    rintro _ ⟨W, hW, rfl, ⟨h1, h2, g, hg, hrel⟩, hc, hW₁⟩
    have hcfg := hU₀.1.1 hc
    refine ⟨?_, ?_, ?_⟩
    · rw [prolongComp_pushForward, smoothingIter_transport F hl hcfg, h1]
    · rw [prolongComp_pushForward, energy_pushForward, h2, F.action.action_eq _ hcfg]
    · unfold CriticalBranchData.SatisfiesMultiplierIdentity
      rw [prolongComp_pushForward]
      have hgrad := F.gradients L n k j hL hj F.hS F.hn l hl U₁ (b.energy l)
        ((b.pushForward hL hj).energy l) hA₁
        (fun V _ => energy_pushForward hL hj b l V) W hW₁
      have haction := F.gradients L n k j hL hj F.hS F.hn 0 (Nat.zero_le j)
        (fieldSpace L n k 0) (plaquetteAction L n k) (plaquetteAction L (scaledExponent n k j) j)
        (F.wilson L n k F.hS F.hn) (fun V hV => F.action.action_eq V hV) _ hcfg
      have hg' := (transport_mem_edgeFormSpace_iff (F.conf l hl)
        (g : Edge L n k l → ComplexMatrix2)).2 g.2
      refine ⟨⟨_, hg'⟩, ?_, ?_⟩
      · change transportTotal (scaleEdge hL hj l) (g : Edge L n k l → ComplexMatrix2) = _
        rw [hg]
        exact hgrad.symm
      · rw [F.transposes L n k j hL hj F.hS F.hn 0 (Nat.zero_le j) l hl
          (leftDifferentialLinear (smoothingIter L n k l) (b.prolongComp l W))
          (leftDifferentialLinear (smoothingIter L (scaledExponent n k j) j l)
            (transportTotal (scaleEdge hL hj 0) (b.prolongComp l W)))
          (fun B B' hB' => hid _ hc B B' hB') g ⟨_, hg'⟩ rfl, hrel]
        exact haction.symm
  prolongComp_lift i hi := by
    have hik := hi.trans_le hj
    have hnear : EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
        b.prolongComp (i + 1) W ∈ fieldSpace L n k 0 :=
      (tendsto_prolongComp F hb (i + 1) hik).eventually eventually_mem_nhdsWithin
    refine Filter.Eventually.mono (eventually_transport_image (F.opens (i + 1) hi)
      (Filter.Eventually.and (hb.prolongComp_lift i hik) hnear)) ?_
    rintro _ ⟨W, hW, rfl, h, hc⟩
    rw [prolongComp_pushForward, smoothingIter_transport F hi.le hc, h, prolong_pushForward]
  prolongComp_critical l hl := by
    obtain ⟨U, hU, hcr⟩ := hb.prolongComp_critical l (hl.trans hj)
    refine ⟨_, isOpenNhdOfOne_image (F.opens 0 (Nat.zero_le j)) hU, ?_⟩
    refine Filter.Eventually.mono (eventually_transport_image (F.opens l hl) hcr) ?_
    rintro _ ⟨W, hW, rfl, h⟩
    rw [prolongComp_pushForward]
    have hset : {U' | U' ∈ transportTotal (scaleEdge hL hj 0) '' U ∧
        smoothingIter L (scaledExponent n k j) j l U' =
          transportTotal (scaleEdge hL hj l) W} =
        transportTotal (scaleEdge hL hj 0) '' {X | X ∈ U ∧ smoothingIter L n k l X = W} := by
      ext U'
      constructor
      · rintro ⟨⟨X, hXm, rfl⟩, he⟩
        rw [smoothingIter_transport F hl (hU.1.1 hXm)] at he
        exact ⟨X, ⟨hXm, transport_injective hL hj _ he⟩, rfl⟩
      · rintro ⟨X, ⟨hXm, he⟩, rfl⟩
        exact ⟨mem_image_of_mem _ hXm, by rw [smoothingIter_transport F hl (hU.1.1 hXm), he]⟩
    rw [hset]
    exact ((F.curves L n k j hL hj F.hS F.hn 0 (Nat.zero_le j) _ _).2 (plaquetteAction L n k)
      (plaquetteAction L (scaledExponent n k j) j)
      (fun V hV => F.action.action_eq V (hU.1.1 hV.1))).1 h
end PushForward
open PushForward in
theorem scaledBranchIsCritical
    (hNear : ScalingNearTrivialField)
    (hKeeps : ScalingCompatibility.Statement)
    (hFacts : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hPaths : AnalyticMapsAlongCurves)
    (hFibre : FibreNeighbourhoodsOfSteps)
    (hWilson : WilsonActionAnalytic)
    (hLinear : CoboundaryScaling.Statement)
    (hBlock : BlockGaugeLiftCommutesWithScaling)
    (hIterate : ScalingCommutesWithSmoothingIter)
    (hCurves : ScalingPreservesTangentsAndCriticalPoints)
    (hHessians : HessianScaling.Statement)
    (hSub : AnalyticSubmanifoldScaling)
    (hDiff : ScalingTransportsDerivatives)
    (hGrad : ScaledGradients)
    (hTrans : ScalingCommutesWithRealTranspose)
    (hIterDiff : ScaledIterateDifferentials) :
    ScaledBranchIsCriticalStatement := by
  intro L n k j hL hj hS hn hj1 b hb
  have hnear := fun a (ha : a ≤ j) a' (ha' : a' ≤ j) => hNear L n k j a a' hL hj hS hn ha ha'
  obtain ⟨-, -, -, hIso, -, hDil, -⟩ := hFacts L hL hS k
  have hTower := (hDil j hj).1 n hn
  have hKept := fun l (hl : l ≤ j) => (hKeeps L hS hL k j l hj hl).1 n hn
  refine isCritical_pushForward
    { hS := hS, hn := hn, hj1 := hj1
      conf := fun l hl => (hnear l hl l hl).1
      opens := fun l hl => (hnear l hl l hl).2.1
      analytic := fun a ha a' ha' => (hnear a ha a' ha').2.2
      gauge := fun l hl => (hKept l hl).2.1
      isometry := fun l hl => (hKept l hl).2.2
      lattices := hTower.toScalingPreservesSublattices
      action := hTower.toScalingPreservesAction
      step := fun i hi => (hTower.preserves hj1).atStep i hi
      finer := hIso n hn
      paths := hPaths, wilson := hWilson, linear := hLinear, block := hBlock
      iterate := hIterate, curves := hCurves, hessians := hHessians, submanifolds := hSub
      differentials := hDiff, gradients := hGrad, transposes := hTrans
      iterateDifferentials := hIterDiff } hb ?_
  exact fun i hi => (hFibre.2.2.2 L n k hS hn (hj1.trans hj) b hb) i hi
end Tower
end YangMills.Construction
end
