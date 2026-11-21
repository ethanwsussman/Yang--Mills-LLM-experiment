import YangMills.Construction.Towers.AveragingCommutesWithIsometriesAtTheSideInfinityProof
import YangMills.Construction.Lattice.HolonomyUnderReorderingProof
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSitesProof
import YangMills.Construction.Towers.GaugeCovarianceOfTheLift
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Filter Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
open Matrices (ComplexMatrix2)
open scoped Topology Matrix.Norms.L2Operator
namespace Tower.LiftGaugeCovariance
variable {L n k i j : ℕ}
private theorem continuousWithinAt_of_positiveEdges {Y : Type} [TopologicalSpace Y]
    {m : Y → Edge L n k j → ComplexMatrix2} {s : Set Y} {y : Y} (hy : y ∈ s)
    (hconf : MapsTo m s (fieldSpace L n k j))
    (hpos : ∀ c : Edge L n k j, c.IsPositivelyOriented →
      ContinuousWithinAt (fun y => m y c) s y) :
    ContinuousWithinAt m s y := by apply _root_.YangMills.Construction.Tower.IdentityLieBallSmoothing.continuousWithinAt_of_positivelyOriented <;> assumption
private theorem eventually_mem_of_isOpenNhdOfOne {𝒰 : Set (Edge L n k i → ComplexMatrix2)}
    (h : IsOpenNhdOfOne 𝒰) :
    ∀ᶠ V in 𝓝[fieldSpace L n k i] trivialField L n k i, V ∈ 𝒰 := by apply _root_.YangMills.Construction.Tower.ProlongCompositesProof.eventually_mem_of_isOpenNhdOfOne <;> assumption
private theorem continuousOn_of_isAnalyticFieldMap {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k i → ComplexMatrix2}
    (h : IsAnalyticFieldMap 𝒰 m) : ContinuousOn m 𝒰 := by apply _root_.YangMills.Construction.Tower.ProlongCompositesProof.continuousOn_of_isAnalyticFieldMap <;> assumption
private theorem isUnit_det_of_mem {X : ComplexMatrix2}
    (hX : X ∈ PeriodicLattice.compactGaugeGroup) : IsUnit X.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem mul_inv_of_mem {X : ComplexMatrix2}
    (hX : X ∈ PeriodicLattice.compactGaugeGroup) : X * X⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p16098 <;> assumption
private theorem inv_mul_of_mem {X : ComplexMatrix2}
    (hX : X ∈ PeriodicLattice.compactGaugeGroup) : X⁻¹ * X = 1 := by apply _root_.YangMills.SharedProofs.p14555 <;> assumption
private theorem inv_mem_group {X : ComplexMatrix2} (hX : X ∈ PeriodicLattice.compactGaugeGroup) :
    X⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem mem_unitary_of_mem {X : ComplexMatrix2}
    (hX : X ∈ PeriodicLattice.compactGaugeGroup) : X ∈ unitary ComplexMatrix2 :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hX).1
private theorem mul_mem_group {X Y : ComplexMatrix2} (hX : X ∈ PeriodicLattice.compactGaugeGroup)
    (hY : Y ∈ PeriodicLattice.compactGaugeGroup) : X * Y ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
private theorem norm_conj_sub_one_le {a c X : ComplexMatrix2}
    (ha : a ∈ PeriodicLattice.compactGaugeGroup) (hc : c ∈ PeriodicLattice.compactGaugeGroup) :
    ‖a * X * c⁻¹ - 1‖ ≤ ‖X - 1‖ + ‖a - 1‖ + ‖c - 1‖ := by
  have e : a * X * c⁻¹ - 1 = (a * (X - 1) + (a - 1) - (c - 1)) * c⁻¹ := by
    have : (a * (X - 1) + (a - 1) - (c - 1)) * c⁻¹ = a * X * c⁻¹ - c * c⁻¹ := by noncomm_ring
    rw [this, mul_inv_of_mem hc]
  rw [e, CStarRing.norm_mul_mem_unitary _ (mem_unitary_of_mem (inv_mem_group hc))]
  calc ‖a * (X - 1) + (a - 1) - (c - 1)‖ ≤ ‖a * (X - 1) + (a - 1)‖ + ‖c - 1‖ := norm_sub_le _ _
    _ ≤ ‖a * (X - 1)‖ + ‖a - 1‖ + ‖c - 1‖ := by gcongr; exact norm_add_le _ _
    _ = ‖X - 1‖ + ‖a - 1‖ + ‖c - 1‖ := by
      rw [CStarRing.norm_mem_unitary_mul _ (mem_unitary_of_mem ha)]
abbrev _root_.YangMills.SharedProofs.p32758 := @norm_conj_sub_one_le
private theorem norm_conj_sub_one_eq {a X : ComplexMatrix2}
    (ha : a ∈ PeriodicLattice.compactGaugeGroup) : ‖a * X * a⁻¹ - 1‖ = ‖X - 1‖ := by apply _root_.YangMills.Construction.PeriodicLattice.HolonomyUnderReordering.norm_conj_sub_one_of_mem <;> assumption
private theorem gaugeTransform_mem_fieldSpace {u : Vertex L n k j → ComplexMatrix2}
    {U : Edge L n k j → ComplexMatrix2}
    (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup) (hU : U ∈ fieldSpace L n k j) :
    PeriodicLattice.gaugeTransform u U ∈ fieldSpace L n k j := by
  refine ⟨fun b _ => mul_mem_group (mul_mem_group (hu _) (hU.1 b (mem_univ _)))
    (inv_mem_group (hu _)), fun b _ => ?_⟩
  have h := hU.2 b (mem_univ _)
  change u b.target * U b.opposite * (u b.source)⁻¹ = (u b.source * U b * (u b.target)⁻¹)⁻¹
  rw [h, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hu _)), mul_assoc]
abbrev _root_.YangMills.SharedProofs.p8548 := @gaugeTransform_mem_fieldSpace
private theorem gaugeTransform_inv_gaugeTransform {u : Vertex L n k j → ComplexMatrix2}
    (U : Edge L n k j → ComplexMatrix2) (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup) :
    PeriodicLattice.gaugeTransform (fun x => (u x)⁻¹) (PeriodicLattice.gaugeTransform u U) = U := by
  funext b
  change (u b.source)⁻¹ * (u b.source * U b * (u b.target)⁻¹) * ((u b.target)⁻¹)⁻¹ = U b
  rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hu _))]
  calc (u b.source)⁻¹ * (u b.source * U b * (u b.target)⁻¹) * u b.target
      = ((u b.source)⁻¹ * u b.source) * U b * ((u b.target)⁻¹ * u b.target) := by noncomm_ring
    _ = U b := by rw [inv_mul_of_mem (hu _), inv_mul_of_mem (hu _), one_mul, mul_one]
private theorem gaugeTransform_gaugeTransform_inv {u : Vertex L n k j → ComplexMatrix2}
    (U : Edge L n k j → ComplexMatrix2) (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup) :
    PeriodicLattice.gaugeTransform u (PeriodicLattice.gaugeTransform (fun x => (u x)⁻¹) U) = U := by
  funext b
  change u b.source * ((u b.source)⁻¹ * U b * ((u b.target)⁻¹)⁻¹) * (u b.target)⁻¹ = U b
  rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hu _))]
  calc u b.source * ((u b.source)⁻¹ * U b * u b.target) * (u b.target)⁻¹
      = (u b.source * (u b.source)⁻¹) * U b * (u b.target * (u b.target)⁻¹) := by noncomm_ring
    _ = U b := by rw [mul_inv_of_mem (hu _), mul_inv_of_mem (hu _), one_mul, mul_one]
private theorem isOpen_near_one {ι : Type*} [Finite ι] (δ : ℝ) :
    IsOpen {V : ι → ComplexMatrix2 | ∀ b, ‖V b - 1‖ < δ} := by
  have e : {V : ι → ComplexMatrix2 | ∀ b, ‖V b - 1‖ < δ} =
      ⋂ b, {V : ι → ComplexMatrix2 | ‖V b - 1‖ < δ} := by
    ext V
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun b =>
    isOpen_lt (continuous_norm.comp ((continuous_apply b).sub continuous_const)) continuous_const
abbrev _root_.YangMills.SharedProofs.p24342 := @isOpen_near_one
private theorem eventually_near_one {ι : Type*} [Finite ι] {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ V in 𝓝 (fun _ : ι => (1 : ComplexMatrix2)), ∀ b, ‖V b - 1‖ < δ :=
  (isOpen_near_one δ).mem_nhds fun b => by simpa using hδ
private theorem exists_radius_of_eventually {ι : Type*} [Finite ι] {D : Set (ι → ComplexMatrix2)}
    {P : (ι → ComplexMatrix2) → Prop} (h : EventuallyNearIdentity D P) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ V ∈ D, (∀ b, ‖V b - 1‖ < δ) → P V := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.exists_ball_of_eventuallyNearIdentity <;> assumption
abbrev _root_.YangMills.SharedProofs.p388 := @exists_radius_of_eventually
private theorem tendsto_section {F : (Edge L n k i → ComplexMatrix2) → ℝ}
    {𝒰 : Set (Edge L n k i → ComplexMatrix2)} {ε : ℝ}
    {p : (Edge L n k (i + 1) → ComplexMatrix2) → Edge L n k i → ComplexMatrix2}
    (hp : IsFibreCriticalSection F 𝒰 ε p) :
    Tendsto p (𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1))
      (𝓝[fieldSpace L n k i] trivialField L n k i) := by
  obtain ⟨𝒲, hU, hA⟩ := hp.analytic_section
  have hnear := eventually_mem_of_isOpenNhdOfOne hU
  have hc := continuousOn_of_isAnalyticFieldMap hA _ hU.2
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, hnear.mono fun W hW => hA.2.1 hW⟩
  have h := hc.tendsto.mono_left (nhdsWithin_le_of_mem (Filter.mem_of_superset hnear fun _ h => h))
  rwa [hp.section_trivial] at h
private theorem continuousAt_zero_of_curve {I : Set ℝ} {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ) : ContinuousAt γ 0 := by
  have h0 : (0 : ℝ) ∈ I := hγ.1.2.2
  have hI : I ∈ 𝓝 (0 : ℝ) := hγ.1.1.mem_nhds h0
  exact (continuousWithinAt_of_positiveEdges (s := I) (y := 0) h0 hγ.2.1
    fun c hc => ((hγ.2.2 c hc) 0 h0).continuousWithinAt).continuousAt hI
private theorem mem_nearIdentityBall {ε : ℝ} {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k i) (hs : ∀ b, ‖V b - 1‖ < ε) : V ∈ nearIdentityBall L n k i ε :=
  And.intro hV hs
private theorem mem_levelFibre {𝒰 : Set (Edge L n k i → ComplexMatrix2)}
    {V : Edge L n k i → ComplexMatrix2} {W : Edge L n k (i + 1) → ComplexMatrix2} (hV : V ∈ 𝒰)
    (hW : smoothingStep L n k i V = W) : V ∈ CriticalBranchData.levelFibre 𝒰 W :=
  And.intro hV hW
private theorem section_gaugeTransform [Finite (Edge L n k i)]
    {F : (Edge L n k i → ComplexMatrix2) → ℝ} {𝒰 : Set (Edge L n k i → ComplexMatrix2)} {ε δ : ℝ}
    {p : (Edge L n k (i + 1) → ComplexMatrix2) → Edge L n k i → ComplexMatrix2}
    (hball : nearIdentityBall L n k i ε ⊆ 𝒰) (hδ : δ ≤ ε)
    {v : Vertex L n k (i + 1) → ComplexMatrix2} (hv : ∀ y, v y ∈ PeriodicLattice.compactGaugeGroup)
    {w : Vertex L n k i → ComplexMatrix2} (hw : ∀ x, w x ∈ PeriodicLattice.compactGaugeGroup)
    {W : Edge L n k (i + 1) → ComplexMatrix2}
    (hC : IsUniqueCriticalPointIn (nearIdentityBall L n k i ε)
      (CriticalBranchData.levelFibre 𝒰 W) F (p W))
    (hC' : IsUniqueCriticalPointIn (nearIdentityBall L n k i ε)
      (CriticalBranchData.levelFibre 𝒰 (PeriodicLattice.gaugeTransform v W)) F
      (p (PeriodicLattice.gaugeTransform v W)))
    (hpW : ∀ b, ‖p W b - 1‖ < δ)
    (hO : ∀ U ∈ fieldSpace L n k i, (∀ b, ‖U b - 1‖ < δ) →
      (∀ b, ‖PeriodicLattice.gaugeTransform w U b - 1‖ < ε) ∧
      smoothingStep L n k i (PeriodicLattice.gaugeTransform w U) =
        PeriodicLattice.gaugeTransform v (smoothingStep L n k i U) ∧
      F (PeriodicLattice.gaugeTransform w U) = F U) :
    p (PeriodicLattice.gaugeTransform v W) = PeriodicLattice.gaugeTransform w (p W) ∧
      F (p (PeriodicLattice.gaugeTransform v W)) = F (p W) := by
  have hVb : p W ∈ nearIdentityBall L n k i ε := hC.1
  have hVf : p W ∈ CriticalBranchData.levelFibre 𝒰 W := hC.2.1.1
  have hVc := hC.2.1.2
  have hVconf : p W ∈ fieldSpace L n k i := hVb.1
  obtain ⟨hOb, hOM, hOF⟩ := hO (p W) hVconf hpW
  have hV'conf : PeriodicLattice.gaugeTransform w (p W) ∈ fieldSpace L n k i :=
    gaugeTransform_mem_fieldSpace hw hVconf
  have hV'ball : PeriodicLattice.gaugeTransform w (p W) ∈ nearIdentityBall L n k i ε :=
    mem_nearIdentityBall hV'conf hOb
  have hV'fib : PeriodicLattice.gaugeTransform w (p W) ∈
      CriticalBranchData.levelFibre 𝒰 (PeriodicLattice.gaugeTransform v W) :=
    mem_levelFibre (hball hV'ball) (by rw [hOM, show smoothingStep L n k i (p W) = W from hVf.2])
  have hcrit : (fieldCurveData L n k i).IsCriticalOn
      (CriticalBranchData.levelFibre 𝒰 (PeriodicLattice.gaugeTransform v W)) F
      (PeriodicLattice.gaugeTransform w (p W)) := by
    refine And.intro hV'fib fun I γ hγ hγN hγ0 => ?_
    have hγd : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ := hγ
    let γ' : ℝ → Edge L n k i → ComplexMatrix2 :=
      fun t => PeriodicLattice.gaugeTransform (fun x => (w x)⁻¹) (γ t)
    have hγ' : ∀ t, PeriodicLattice.gaugeTransform w (γ' t) = γ t :=
      fun t => gaugeTransform_gaugeTransform_inv _ hw
    have hγ'0 : γ' 0 = p W := by
      change PeriodicLattice.gaugeTransform (fun x => (w x)⁻¹) (γ 0) = _
      rw [hγ0]
      exact gaugeTransform_inv_gaugeTransform _ hw
    have hcont : ContinuousAt γ' 0 := by
      refine continuousAt_pi.2 fun b => ?_
      have h1 : ContinuousAt (fun t => γ t b) 0 :=
        (continuous_apply b).continuousAt.comp (continuousAt_zero_of_curve hγd)
      change ContinuousAt (fun t => (w b.source)⁻¹ * γ t b * ((w b.target)⁻¹)⁻¹) 0
      exact (continuousAt_const.mul h1).mul continuousAt_const
    have hE : {t | ∀ b, ‖γ' t b - 1‖ < δ} ∈ 𝓝 (0 : ℝ) :=
      hcont.preimage_mem_nhds ((isOpen_near_one δ).mem_nhds (by
        rw [hγ'0]
        exact hpW))
    have hI : I ∈ 𝓝 (0 : ℝ) := hγd.1.1.mem_nhds hγd.1.2.2
    obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 (inter_mem hI hE)
    have hconf' : ∀ t ∈ I, γ' t ∈ fieldSpace L n k i :=
      fun t ht => gaugeTransform_mem_fieldSpace (fun x => inv_mem_group (hw x)) (hγd.2.1 ht)
    have hγ'curve : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup
        (Metric.ball (0 : ℝ) r) γ' := by
      unfold IsDifferentiableFieldCurve IsOpenIntervalAroundZero
      refine ⟨⟨Metric.isOpen_ball, ?_, Metric.mem_ball_self hr⟩,
        fun t ht => hconf' t (hrs ht).1, fun b hb => ?_⟩
      · rw [Real.ball_eq_Ioo]
        exact ordConnected_Ioo
      · change DifferentiableOn ℝ (fun t => (w b.source)⁻¹ * γ t b * ((w b.target)⁻¹)⁻¹) _
        exact (((hγd.2.2 b hb).mono fun t ht => (hrs ht).1).const_mul _).mul_const _
    have hmaps : MapsTo γ' (Metric.ball (0 : ℝ) r) (CriticalBranchData.levelFibre 𝒰 W) := by
      intro t ht
      have htI : t ∈ I := (hrs ht).1
      have hs : ∀ b, ‖γ' t b - 1‖ < δ := (hrs ht).2
      have hc := hconf' t htI
      refine mem_levelFibre (hball (mem_nearIdentityBall hc fun b => (hs b).trans_le hδ)) ?_
      have h2 := (hO _ hc hs).2.1
      rw [hγ', show smoothingStep L n k i (γ t) = PeriodicLattice.gaugeTransform v W
        from (hγN htI).2] at h2
      have h3 := congrArg (PeriodicLattice.gaugeTransform fun y => (v y)⁻¹) h2
      rw [gaugeTransform_inv_gaugeTransform _ hv, gaugeTransform_inv_gaugeTransform _ hv] at h3
      exact h3.symm
    have hder := hVc _ γ' hγ'curve hmaps hγ'0
    have heq : (fun t => F (γ t)) =ᶠ[𝓝 0] fun t => F (γ' t) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
      have h4 := (hO _ (hconf' t (hrs ht).1) (hrs ht).2).2.2
      rwa [hγ'] at h4
    rw [heq.deriv_eq]
    exact hder
  have e : p (PeriodicLattice.gaugeTransform v W) = PeriodicLattice.gaugeTransform w (p W) :=
    (hC'.2.2 _ hV'ball hcrit).symm
  exact ⟨e, by rw [e]; exact hOF⟩
private theorem blockGaugeLift_of_mem (hS : BlocksPartitionFiner L n k (i + 1))
    (v : Vertex L n k (i + 1) → ComplexMatrix2) {y : Vertex L n k (i + 1)} {x : Vertex L n k i}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y) :
    blockGaugeLift v x = v y := by
  have hspec : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i)
      (Classical.epsilon fun y' : Vertex L n k (i + 1) =>
        x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y') :=
    Classical.epsilon_spec (p := fun y' : Vertex L n k (i + 1) =>
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y') ⟨y, hx⟩
  have e := (hS.2.1 x).unique hspec hx
  unfold blockGaugeLift
  rw [e]
abbrev _root_.YangMills.SharedProofs.p60232 := @blockGaugeLift_of_mem
private theorem toSublattice_mem_sitesInBlock (hB : ∀ y, BlockEqOffsetImage L n k (i + 1) y)
    (hS : BlocksPartitionFiner L n k (i + 1)) (y : Vertex L n k (i + 1)) :
    (y.toSublattice (PeriodicLattice.levelDepth k i) : Vertex L n k i) ∈
      PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y := by
  have hy : (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
    have h : (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∩
        (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) :
          Set (PeriodicLattice.FourTorus L n)) := by
      rw [hS.1 y]
      exact mem_singleton _
    exact h.1
  have hlat : (y : PeriodicLattice.FourTorus L n) ∈
      (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
        Set (PeriodicLattice.FourTorus L n)) :=
    (hB y).2.2.2 hy
  have e : ((y.toSublattice (PeriodicLattice.levelDepth k i) : Vertex L n k i) :
      PeriodicLattice.FourTorus L n) = y :=
    Classical.epsilon_spec (p := fun x : Vertex L n k i => (x : PeriodicLattice.FourTorus L n) = y)
      ⟨⟨y, hlat⟩, rfl⟩
  change ((y.toSublattice (PeriodicLattice.levelDepth k i) : Vertex L n k i) :
    PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y
  rw [e]
  exact hy
abbrev _root_.YangMills.SharedProofs.p22504 := @toSublattice_mem_sitesInBlock
private theorem restrictVertexFunction_blockGaugeLift
    (hB : ∀ y, BlockEqOffsetImage L n k (i + 1) y) (hS : BlocksPartitionFiner L n k (i + 1))
    (v : Vertex L n k (i + 1) → ComplexMatrix2) :
    restrictVertexFunction (i + 1) (blockGaugeLift v) = v := by
  funext y
  exact blockGaugeLift_of_mem hS v (toSublattice_mem_sitesInBlock hB hS y)
private theorem axialFunction_blockGaugeLift (hB : ∀ y, BlockEqOffsetImage L n k (i + 1) y)
    (hS : BlocksPartitionFiner L n k (i + 1)) {v : Vertex L n k (i + 1) → ComplexMatrix2}
    (hv : ∀ y, v y ∈ PeriodicLattice.compactGaugeGroup) {U : Edge L n k i → ComplexMatrix2}
    (hc : ∀ (y : Vertex L n k (i + 1)),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
      PeriodicLattice.meanContourHolonomy (PeriodicLattice.gaugeTransform (blockGaugeLift v) U) y x =
        blockGaugeLift v (y.toSublattice (PeriodicLattice.levelDepth k i)) *
          PeriodicLattice.meanContourHolonomy U y x * (blockGaugeLift v x)⁻¹) :
    axialFunction L n k i (PeriodicLattice.gaugeTransform (blockGaugeLift v) U) =
      axialFunction L n k i U := by
  unfold axialFunction PeriodicLattice.axialGaugeFunction
  refine finsum_congr fun y => finsum_congr fun _ => finsum_congr fun z =>
    finsum_congr fun hz => ?_
  have hz' : z ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y := hz.1
  rw [hc y z hz', blockGaugeLift_of_mem hS v (toSublattice_mem_sitesInBlock hB hS y),
    blockGaugeLift_of_mem hS v hz']
  have e : Matrix.trace (v y * PeriodicLattice.meanContourHolonomy U y z * (v y)⁻¹) =
      Matrix.trace (PeriodicLattice.meanContourHolonomy U y z) := by
    rw [Matrix.trace_mul_comm, ← mul_assoc, inv_mul_of_mem (hv y), one_mul]
  unfold PeriodicLattice.traceDeficit
  rw [Matrices.ComplexMatrix2.fullTrace, Matrices.ComplexMatrix2.fullTrace, e]
abbrev _root_.YangMills.SharedProofs.p62128 := @axialFunction_blockGaugeLift
private theorem finite_edge (hL : 0 < L) : Finite (Edge L n k j) :=
  haveI := SeparatedSequences.BaseParameters.site_finite hL n (PeriodicLattice.levelDepth k j)
  Finite.of_injective (fun b : Edge L n k j => (b.source, b.target)) fun _ _ h =>
    PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
theorem statement_holds (hAvg : SmoothingAnalyticCovariantOnSides)
    (hBlocks : BlockStructure) : Statement := by
  intro L n k i hL hn hik b 𝒰 ε p hb hp
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hfs : ∀ j : ℕ, Finite (Vertex L n k j) :=
    fun j => SeparatedSequences.BaseParameters.site_finite hL0 n _
  have hfb : ∀ j : ℕ, Finite (Edge L n k j) := fun _ => finite_edge hL0
  obtain ⟨hDisp, hSort, -, -⟩ :=
    (hBlocks L k (i + 1) hL (by omega) (by omega) (by omega)).1 n hn
  obtain ⟨δ₁, hδ₁, hcov⟩ := exists_radius_of_eventually (hAvg L hL n k i hn hik).gauge_covariant
  obtain ⟨δ₃, hδ₃, hgood⟩ := exists_radius_of_eventually hp.unique_critical
  have hlift := tendsto_section hp
  have hε := hp.radius_pos
  have hwG : ∀ v : Vertex L n k (i + 1) → ComplexMatrix2,
      (∀ y, v y ∈ PeriodicLattice.compactGaugeGroup) →
      ∀ x, blockGaugeLift v x ∈ PeriodicLattice.compactGaugeGroup := fun _ h _ => h _
  have hstep : ∀ (v : Vertex L n k (i + 1) → ComplexMatrix2),
      (∀ y, v y ∈ PeriodicLattice.compactGaugeGroup) →
      ∀ U ∈ fieldSpace L n k i, (∀ c, ‖U c - 1‖ < δ₁) →
      b.energy i (PeriodicLattice.gaugeTransform (blockGaugeLift v) U) = b.energy i U →
      smoothingStep L n k i (PeriodicLattice.gaugeTransform (blockGaugeLift v) U) =
          PeriodicLattice.gaugeTransform v (smoothingStep L n k i U) ∧
        b.gaugeFixedEnergy i (PeriodicLattice.gaugeTransform (blockGaugeLift v) U) =
          b.gaugeFixedEnergy i U := by
    intro v hv U hU hs hF
    obtain ⟨h1, h2⟩ := hcov U hU hs (blockGaugeLift v) (hwG v hv)
    rw [restrictVertexFunction_blockGaugeLift hDisp hSort] at h1
    refine ⟨h1, ?_⟩
    unfold CriticalBranchData.gaugeFixedEnergy
    rw [hF, axialFunction_blockGaugeLift hDisp hSort hv h2]
  refine ⟨?_, ?_⟩
  · obtain ⟨pa, hpa, pb, hpb, hab⟩ := eventually_prod_iff.1 (hb.energy_gauge_invariant i le_rfl).1
    obtain ⟨η₁, hη₁, ha⟩ := exists_radius_of_eventually (D := gaugeGroupAt L n k i) (P := pa) hpa
    obtain ⟨δ₂, hδ₂, hb₂⟩ := exists_radius_of_eventually (D := fieldSpace L n k i) (P := pb) hpb
    obtain ⟨δ, hδ, hδa, hδb, hδc⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₁ ∧ δ ≤ δ₂ ∧ δ ≤ ε / 2 :=
      ⟨min (min δ₁ δ₂) (ε / 2), lt_min (lt_min hδ₁ hδ₂) (half_pos hε),
        (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
        min_le_right _ _⟩
    obtain ⟨η, hη, hηa, hηb, hηc⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ η₁ ∧ η ≤ ε / 8 ∧ η ≤ δ₃ / 4 :=
      ⟨min (min η₁ (ε / 8)) (δ₃ / 4), lt_min (lt_min hη₁ (by positivity)) (by positivity),
        (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
        min_le_right _ _⟩
    refine eventually_prod_iff.2 ⟨fun v => v ∈ gaugeGroupAt L n k (i + 1) ∧
      ∀ y, ‖v y - 1‖ < η, ?_, fun W => W ∈ fieldSpace L n k (i + 1) ∧
      (∀ c, ‖W c - 1‖ < δ₃ / 2) ∧ ∀ c, ‖p W c - 1‖ < δ, ?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_near_one hη)]
        with v h1 h2
      exact ⟨h1, h2⟩
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_near_one (half_pos hδ₃)),
        hlift.eventually (nhdsWithin_le_nhds (eventually_near_one hδ))] with W h1 h2 h3
      exact ⟨h1, h2, h3⟩
    · intro v hv W hW
      obtain ⟨hvG, hvs⟩ := hv
      obtain ⟨hWc, hWs, hpW⟩ := hW
      have hvg : ∀ y, v y ∈ PeriodicLattice.compactGaugeGroup := hvG
      have hws : ∀ x, ‖blockGaugeLift v x - 1‖ < η := fun x => hvs _
      have hWvs : ∀ c, ‖PeriodicLattice.gaugeTransform v W c - 1‖ < δ₃ := by
        intro c
        have h0 := norm_conj_sub_one_le (X := W c) (hvg c.source) (hvg c.target)
        have h1 := hWs c
        have h2 := hvs c.source
        have h3 := hvs c.target
        change ‖v c.source * W c * (v c.target)⁻¹ - 1‖ < δ₃
        linarith
      have hG1 := hgood W hWc fun c => (hWs c).trans (half_lt_self hδ₃)
      have hG2 := hgood _ (gaugeTransform_mem_fieldSpace hvg hWc) hWvs
      refine section_gaugeTransform hp.ball_subset (by linarith) hvg (hwG v hvg) hG1.1 hG2.1 hpW
        fun U hU hs => ?_
      have hS : b.energy i (PeriodicLattice.gaugeTransform (blockGaugeLift v) U) = b.energy i U :=
        hab (ha _ (hwG v hvg) fun x => (hws x).trans_le hηa)
          (hb₂ U hU fun c => (hs c).trans_le hδb)
      refine ⟨fun c => ?_, hstep v hvg U hU (fun c => (hs c).trans_le hδa) hS⟩
      have h0 := norm_conj_sub_one_le (X := U c) (hwG v hvg c.source) (hwG v hvg c.target)
      have h1 := hs c
      have h2 := hws c.source
      have h3 := hws c.target
      change ‖blockGaugeLift v c.source * U c * (blockGaugeLift v c.target)⁻¹ - 1‖ < ε
      linarith
  · obtain ⟨δ₂, hδ₂, hb₂⟩ := exists_radius_of_eventually (hb.energy_gauge_invariant i le_rfl).2
    obtain ⟨δ, hδ, hδa, hδb, hδc⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₁ ∧ δ ≤ δ₂ ∧ δ ≤ ε :=
      ⟨min (min δ₁ δ₂) ε, lt_min (lt_min hδ₁ hδ₂) hε,
        (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
        min_le_right _ _⟩
    change ∀ᶠ W in 𝓝[fieldSpace L n k (i + 1)] (fun _ => (1 : ComplexMatrix2)), _
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_near_one hδ₃),
      hlift.eventually (nhdsWithin_le_nhds (eventually_near_one hδ))]
      with W hWc hWs hpW v hvG hconst
    have hvg : ∀ y, v y ∈ PeriodicLattice.compactGaugeGroup := hvG
    have hWvs : ∀ c, ‖PeriodicLattice.gaugeTransform v W c - 1‖ < δ₃ := by
      intro c
      change ‖v c.source * W c * (v c.target)⁻¹ - 1‖ < δ₃
      rw [hconst c.target c.source, norm_conj_sub_one_eq (hvg _)]
      exact hWs c
    have hG1 := hgood W hWc hWs
    have hG2 := hgood _ (gaugeTransform_mem_fieldSpace hvg hWc) hWvs
    refine section_gaugeTransform hp.ball_subset hδc hvg (hwG v hvg) hG1.1 hG2.1 hpW
      fun U hU hs => ?_
    have hS : b.energy i (PeriodicLattice.gaugeTransform (blockGaugeLift v) U) = b.energy i U :=
      hb₂ U hU (fun c => (hs c).trans_le hδb) _ (hwG v hvg) fun x x' => hconst _ _
    refine ⟨fun c => ?_, hstep v hvg U hU (fun c => (hs c).trans_le hδa) hS⟩
    change ‖blockGaugeLift v c.source * U c * (blockGaugeLift v c.target)⁻¹ - 1‖ < ε
    rw [show blockGaugeLift v c.target = blockGaugeLift v c.source from hconst _ _,
      norm_conj_sub_one_eq (hwG v hvg _)]
    exact (hs c).trans_le hδc
end Tower.LiftGaugeCovariance
end YangMills.Construction
end
