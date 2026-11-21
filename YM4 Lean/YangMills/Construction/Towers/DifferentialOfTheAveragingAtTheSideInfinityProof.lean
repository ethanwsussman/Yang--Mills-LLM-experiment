import YangMills.Construction.Towers.BlocksOfATowerProof
import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Lattice.BondOrientationDichotomy
import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Towers.AverageIsDifferentiableOnThePolydisc
import YangMills.Construction.Towers.AveragesAtTheSideInfinityNearTheTrivialConfiguration
import YangMills.Construction.Towers.AveragingPolydiscRadiusExists
import YangMills.Construction.Towers.BondsOfADoubleBlockAndTheirImageInATorus
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.DifferentialOfTheAveragingAtTheSideInfinity
import YangMills.Construction.Towers.DifferentialOfTheAveragingOnTheSides
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import YangMills.Construction.Towers.OneValueForEveryWriting
import YangMills.Construction.Towers.QuotientCarriesTheLinearObjects
import YangMills.Construction.Towers.ReverseOfAStraightPathOfATower
import YangMills.Construction.Towers.ValuesOfTheAveragesNearTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.FullSpace.SmoothingDerivAllScalesLemmas
open PeriodicLattice (compactGaugeGroup complexGaugeGroup)
open InfiniteLattice (AmbientSpace)
variable {L k j : ℕ}
theorem link_opposite_isPositivelyOriented {a : ℝ} {b : InfiniteLattice.Link a}
    (h : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem meshAt_pos (hL : 0 < L) (k j : ℕ) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.meshAt_pos <;> assumption
theorem mem_complexGaugeGroup_of_mem_compact {X : ComplexMatrix2} (hX : X ∈ compactGaugeGroup) :
    X ∈ complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hX).2
theorem inv_inv_of_mem_compact {X : ComplexMatrix2} (hX : X ∈ compactGaugeGroup) :
    (X⁻¹)⁻¹ = X := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem inv_mem_compact {X : ComplexMatrix2} (hX : X ∈ compactGaugeGroup) :
    X⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
structure ProjectionData (L k j : ℕ) (c : Edge L k (j + 1)) : Prop where
  preserves : ProjPreservesStructures L 1 k j c
  injOn : InjOn (projEdge L 1 k j) (doubleCubeLinks L (meshAt L k j) c)
  closed : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
    b.opposite ∈ doubleCubeLinks L (meshAt L k j) c
  opposite_proj : ∀ b : Edge L k j,
    (projEdge L 1 k j b).opposite = projEdge L 1 k j b.opposite
  positive : ∀ b : Edge L k j, b.IsPositivelyOriented →
    (projEdge L 1 k j b).IsPositivelyOriented
  dichotomy : ∀ b : Tower.Edge L 1 k j,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
theorem projField_apply {ℬ : Set (Edge L k j)}
    (hinj : InjOn (projEdge L 1 k j) ℬ) (V : Edge L k j → ComplexMatrix2) {b : Edge L k j}
    (hb : b ∈ ℬ) : projField L 1 k j ℬ V (projEdge L 1 k j b) = V b := by
  have h : ∃ b' ∈ ℬ, projEdge L 1 k j b' = projEdge L 1 k j b := ⟨b, hb, rfl⟩
  unfold projField
  rw [dif_pos h, hinj h.choose_spec.1 hb h.choose_spec.2]
theorem pushforwardForm_apply {ℬ : Set (Edge L k j)}
    (hinj : InjOn (projEdge L 1 k j) ℬ) (B : Edge L k j → ComplexMatrix2) {b : Edge L k j}
    (hb : b ∈ ℬ) : pushforwardForm L 1 k j ℬ B (projEdge L 1 k j b) = B b := by
  have h : ∃ b' ∈ ℬ, projEdge L 1 k j b' = projEdge L 1 k j b := ⟨b, hb, rfl⟩
  unfold pushforwardForm
  rw [dif_pos h, hinj h.choose_spec.1 hb h.choose_spec.2]
theorem projField_congr {ℬ : Set (Edge L k j)} {V V' : Edge L k j → ComplexMatrix2}
    (h : ∀ b ∈ ℬ, V b = V' b) :
    projField L 1 k j ℬ V = projField L 1 k j ℬ V' := by
  funext c
  unfold projField
  split_ifs with hc
  · exact h _ hc.choose_spec.1
  · rfl
variable {c : Edge L k (j + 1)}
theorem ProjectionData.not_isPositivelyOriented (h : ProjectionData L k j c) {b : Edge L k j}
    (hb : ¬b.IsPositivelyOriented) : ¬(projEdge L 1 k j b).IsPositivelyOriented := by
  intro hp
  have hr := h.positive _ (link_opposite_isPositivelyOriented hb)
  rw [← h.opposite_proj] at hr
  rcases h.dichotomy (projEdge L 1 k j b) with h₁ | h₁
  · exact h₁.2 hr
  · exact h₁.2 hp
theorem projField_expTwist (h : ProjectionData L k j c) (B : Edge L k j → ComplexMatrix2) (s : ℂ) :
    projField L 1 k j (doubleCubeLinks L (meshAt L k j) c)
        (expTwist (s • B) fun _ => 1) =
      PeriodicLattice.expTwist
        (s • pushforwardForm L 1 k j (doubleCubeLinks L (meshAt L k j) c) B) fun _ => 1 := by
  classical
  funext b'
  by_cases hb : ∃ b ∈ doubleCubeLinks L (meshAt L k j) c, projEdge L 1 k j b = b'
  · obtain ⟨b, hbP, rfl⟩ := hb
    rw [projField_apply h.injOn _ hbP]
    by_cases hpos : b.IsPositivelyOriented
    · have hpos' := h.positive b hpos
      simp only [expTwist, PeriodicLattice.expTwist, if_pos hpos, if_pos hpos', Pi.smul_apply,
        pushforwardForm_apply h.injOn B hbP]
    · have hneg := h.not_isPositivelyOriented hpos
      simp only [expTwist, PeriodicLattice.expTwist, if_neg hpos, if_neg hneg, Pi.smul_apply,
        h.opposite_proj, pushforwardForm_apply h.injOn B (h.closed b hbP)]
  · have h₀ : projField L 1 k j (doubleCubeLinks L (meshAt L k j) c)
        (expTwist (s • B) fun _ => 1) b' = 1 := dif_neg hb
    have f₀ : pushforwardForm L 1 k j (doubleCubeLinks L (meshAt L k j) c) B b' = 0 :=
      dif_neg hb
    have f₁ : pushforwardForm L 1 k j (doubleCubeLinks L (meshAt L k j) c) B b'.opposite = 0 :=
      dif_neg fun ⟨b, hbP, e⟩ => hb ⟨b.opposite, h.closed b hbP, by rw [← h.opposite_proj, e]; rfl⟩
    rw [h₀]
    by_cases hp : b'.IsPositivelyOriented <;>
      simp [PeriodicLattice.expTwist, hp, f₀, f₁, NormedSpace.exp_zero]
theorem pushforwardForm_mem (h : ProjectionData L k j c) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace (meshAt L k j)) :
    pushforwardForm L 1 k j (doubleCubeLinks L (meshAt L k j) c) B ∈
      Tower.edgeFormSpace L 1 k j := by
  classical
  refine ⟨fun b' hb' => ?_, fun b' => ?_⟩
  · by_cases hb : ∃ b ∈ doubleCubeLinks L (meshAt L k j) c, projEdge L 1 k j b = b'
    · obtain ⟨b, hbP, rfl⟩ := hb
      rw [pushforwardForm_apply h.injOn B hbP]
      by_cases hpos : b.IsPositivelyOriented
      · exact hB.1 b hpos
      · exact absurd hb' (h.not_isPositivelyOriented hpos)
    · have f₀ : pushforwardForm L 1 k j (doubleCubeLinks L (meshAt L k j) c) B b' = 0 :=
        dif_neg hb
      rw [f₀]
      exact ComplexMatrix2.hermitianTraceless.zero_mem
  · by_cases hb : ∃ b ∈ doubleCubeLinks L (meshAt L k j) c, projEdge L 1 k j b = b'
    · obtain ⟨b, hbP, rfl⟩ := hb
      rw [h.opposite_proj, pushforwardForm_apply h.injOn B hbP,
        pushforwardForm_apply h.injOn B (h.closed b hbP)]
      exact hB.2 b
    · have f₀ : pushforwardForm L 1 k j (doubleCubeLinks L (meshAt L k j) c) B b' = 0 :=
        dif_neg hb
      have f₁ : pushforwardForm L 1 k j (doubleCubeLinks L (meshAt L k j) c) B b'.opposite = 0 :=
        dif_neg fun ⟨b, hbP, e⟩ => hb ⟨b.opposite, h.closed b hbP, by rw [← h.opposite_proj, e]; rfl⟩
      rw [f₀, f₁, neg_zero]
structure Hypotheses : Prop where
  sides : SmoothingDerivAtOneOnAllSides
  radius : AdmissiblePolydiscRadiusExists
  linear : ProjectionCommutesWithSmoothing
  differentiable : ComplexSmoothingDifferentiableOnPolydisc
  towers : SublatticesSymmetriesScalingsAndProjections.Statement
  edges : EdgeProjectionProperties
  doubleCube : DoubleCubeLinksAndTorusImage
  orientation : PeriodicLattice.BondOrientationDichotomy
  bondSets : BondSetFields.ProductStructureHolds
  periodicDoubleBlock : PeriodicLattice.DoubleBlockStructure.Statement
  near : SmoothingNearIdentity
  presentations : UniqueValue.PresentationsAgreeAndBallsOpen
  schemes : PeriodicLattice.AveragingSchemeProperties
  values : SmoothingNearTrivialField
  chart : LeftChartFields.Claim
  reversal : AxisPathReversal.MainStatement
theorem projectionData (I : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) (hc : c.IsPositivelyOriented) : ProjectionData L k j c := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hKc := I.doubleCube L k (j + 1) hL (by omega) (by omega) c hc
  have hbonds := (I.edges L 1 k j hL one_pos hj.le).1
  refine ⟨((I.towers L hL0 hL k).2.2.2.2.2.2 (by omega) 1 one_pos).2 j hj c hc,
    ((hKc.2 1 Nat.one_pos).2.2.2.2.2.2).injOn, hKc.1.2, fun b => (hbonds b).2.2.2,
    fun b => (hbonds b).2.2.1, fun b => ?_⟩
  refine I.orientation L 1 hL one_pos _ ?_ b
  show -((1 : ℕ) : ℤ) < PeriodicLattice.levelDepth k j
  unfold PeriodicLattice.levelDepth
  omega
theorem one_mem_compact : (1 : ComplexMatrix2) ∈ compactGaugeGroup := one_mem _
theorem one_mem_fieldSpace :
    (fun _ => 1 : Edge L k j → ComplexMatrix2) ∈ fieldSpace L k j :=
  ⟨fun _ => one_mem_compact, fun _ => by simp⟩
theorem expTwist_mem_fieldSpace (I : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j ≤ k) {B : Edge L k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace (meshAt L k j)) (t : ℝ) :
    expTwist ((t : ℂ) • B) (fun _ => 1) ∈ fieldSpace L k j := by
  classical
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hcl := ((I.chart.2.2 L k j hL hj).2.1).1.1
  have hE : ∀ b : Edge L k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B) b) * 1 ∈ compactGaugeGroup := fun b hb =>
    (hcl (fun _ => 1) one_mem_fieldSpace B hB ⟨b, hb⟩).1 t
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [expTwist, if_pos hb]
      exact hE b hb
    · simp only [expTwist, if_neg hb]
      exact inv_mem_compact (hE _ (link_opposite_isPositivelyOriented hb))
  · by_cases hb : b.IsPositivelyOriented
    · have hnr := InfiniteLattice.Link.opposite_not_isPositivelyOriented (meshAt_pos hL0 k j) hb
      have hrr : b.opposite.opposite = b := rfl
      simp only [expTwist, if_pos hb, if_neg hnr, hrr]
    · have hr := link_opposite_isPositivelyOriented hb
      simp only [expTwist, if_pos hr, if_neg hb]
      rw [inv_inv_of_mem_compact (hE _ hr)]
theorem eventually_mem_commonSmoothingDomain (I : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {B : Tower.Edge L 1 k j → ComplexMatrix2} (hB : B ∈ Tower.edgeFormSpace L 1 k j) :
    ∀ᶠ t : ℝ in 𝓝 0, PeriodicLattice.expTwist ((t : ℂ) • B) (fun _ => 1) ∈
      commonSmoothingDomain L 1 k j := by
  classical
  have hv := I.values L 1 k hL one_pos (by omega)
  obtain ⟨⟨hsub, O, hO, hOe⟩, h1⟩ := (hv.1 j hj).1
  have hft := (I.chart.2.2 L k j hL hj.le).1 1 one_pos
  have hbij := hft.2.1.2.1
  have hcl := hft.1.1.1
  have hone : (fun _ => 1 : Tower.Edge L 1 k j → ComplexMatrix2) ∈ Tower.fieldSpace L 1 k j :=
    hsub h1
  have hsm : ∀ t : ℝ, ((t : ℂ) • B) = t • B := fun t => by
    funext b
    exact Complex.coe_smul t (B b)
  have hconf : ∀ t : ℝ, PeriodicLattice.expTwist ((t : ℂ) • B) (fun _ => 1) ∈
      Tower.fieldSpace L 1 k j := fun t => by
    rw [hsm]
    exact hv.2 j hj.le (t • B) ((Tower.edgeFormSpace L 1 k j).smul_mem t hB) _ hone
  have h1O : Tower.restrictToPositiveEdges (fun _ => 1 : Tower.Edge L 1 k j → ComplexMatrix2) ∈ O := by
    have h := mem_image_of_mem Tower.restrictToPositiveEdges h1
    rw [hOe] at h
    exact h.1
  have h0 : PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B) (fun _ => 1) =
      (fun _ => 1 : Tower.Edge L 1 k j → ComplexMatrix2) := by
    funext b
    by_cases hb : b.IsPositivelyOriented <;>
      simp [PeriodicLattice.expTwist, hb, NormedSpace.exp_zero]
  have hcont : ContinuousAt (fun t : ℝ => Tower.restrictToPositiveEdges
      (PeriodicLattice.expTwist ((t : ℂ) • B) (fun _ => 1))) 0 := by
    refine continuousAt_pi.2 fun b => ?_
    have hd := (hcl (fun _ => 1) hone B hB b).2
    refine hd.continuousAt.congr (Eventually.of_forall fun t => ?_)
    have hb : (b : Tower.Edge L 1 k j).IsPositivelyOriented := b.2
    simp [Tower.restrictToPositiveEdges, PeriodicLattice.expTwist, hb,
      LeftChartFields.leftExpMul, LeftChartFields.LatticeData.onPositive,
      LeftChartFields.finiteData]
  have hmem : Tower.restrictToPositiveEdges
      (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B) (fun _ => 1)) ∈ O := by
    rw [h0]
    exact h1O
  filter_upwards [hcont.eventually (hO.mem_nhds hmem)] with t ht
  have hm : Tower.restrictToPositiveEdges (PeriodicLattice.expTwist ((t : ℂ) • B) (fun _ => 1)) ∈
      Tower.restrictToPositiveEdges '' commonSmoothingDomain L 1 k j := by
    rw [hOe]
    exact ⟨ht, hbij.mapsTo (hconf t)⟩
  obtain ⟨V, hV, e⟩ := hm
  rw [← hbij.injOn (hsub hV) (hconf t) e]
  exact hV
theorem projVertex_mem_block (I : Hypotheses) (h : ProjectionData L k j c)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {y : Vertex L k (j + 1)}
    (hy : y = c.initial ∨ y = c.terminal) {x : Vertex L k j}
    (hx : x ∈ cubeVertices L (meshAt L k j) y) :
    projVertex L 1 k (j + 1) y ∈
        ({(projEdge L 1 k (j + 1) c).source, (projEdge L 1 k (j + 1) c).target} :
          Set (Tower.Vertex L 1 k (j + 1))) ∧
      projVertex L 1 k j x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (projVertex L 1 k (j + 1) y) := by
  obtain ⟨hdt, hdh, -, -⟩ := (I.edges L 1 k (j + 1) hL one_pos hj).1 c
  rcases hy with rfl | rfl
  · refine ⟨Or.inl hdt.symm, ?_⟩
    have := h.preserves.cube_initial
    rw [← hdt]
    show ((projVertex L 1 k j x : Tower.Vertex L 1 k j) : PeriodicLattice.FourTorus L 1) ∈
      PeriodicLattice.unitBlock (projEdge L 1 k (j + 1) c).source
    rw [← this]
    exact ⟨_, hx, rfl⟩
  · refine ⟨Or.inr hdh.symm, ?_⟩
    have := h.preserves.cube_terminal
    rw [← hdh]
    show ((projVertex L 1 k j x : Tower.Vertex L 1 k j) : PeriodicLattice.FourTorus L 1) ∈
      PeriodicLattice.unitBlock (projEdge L 1 k (j + 1) c).target
    rw [← this]
    exact ⟨_, hx, rfl⟩
theorem complex_data_eq_proj (I : Hypotheses) (h : ProjectionData L k j c)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) (hc : c.IsPositivelyOriented) {V : Edge L k j → ComplexMatrix2}
    (hV : IsFieldOn complexGaugeGroup (doubleCubeLinks L (meshAt L k j) c) V)
    (hW : projField L 1 k j (doubleCubeLinks L (meshAt L k j) c) V ∈
      commonSmoothingDomain L 1 k j) :
    V ∈ complexDomainNearOne L c ∧
      complexSmoothing L V c = Tower.smoothingStep L 1 k j
        (projField L 1 k j (doubleCubeLinks L (meshAt L k j) c) V)
        (projEdge L 1 k (j + 1) c) ∧
      ∀ y : Vertex L k (j + 1), y = c.initial ∨ y = c.terminal →
        ∀ x ∈ cubeVertices L (meshAt L k j) y,
          complexContourMean L V y x = PeriodicLattice.meanContourHolonomy
            (projField L 1 k j (doubleCubeLinks L (meshAt L k j) c) V)
            (projVertex L 1 k (j + 1) y) (projVertex L 1 k j x) := by
  obtain ⟨-, -, hdp, -⟩ := (I.edges L 1 k (j + 1) hL one_pos hj).1 c
  have hd := hdp hc
  have hval := ((I.values L 1 k hL one_pos (by omega)).1 j hj).2 _ hW _ hd
  have hsch := (I.schemes L hL 1 k j one_pos hj .centred).2.1 _ hd
  have hmean := hsch.2.2.2.2.1 _ hval.isGaugeField hval.curvature_lt
  have hdom : projField L 1 k j (doubleCubeLinks L (meshAt L k j) c) V ∈
      (PeriodicLattice.complexAveragingDomainNearOne (projEdge L 1 k (j + 1) c) :
        Set (Tower.Edge L 1 k j → ComplexMatrix2)) := by
    rw [← hsch.2.2.1.domain_eq]
    exact hmean.mem_domain
  have hVO : V ∈ complexDomainNearOne L c := (h.preserves.mem_complexDomain_iff V hV).2 hdom
  refine ⟨hVO, ?_, fun y hy x hx => ?_⟩
  · rw [h.preserves.complexSmoothing_eq V hVO, ← hsch.2.2.1.average_eq _ hmean.mem_domain]
    exact hmean.average_eq
  · rw [h.preserves.complexContourMean_eq V hVO y hy x hx]
    obtain ⟨hyd, hxd⟩ := projVertex_mem_block I h hL hj hy hx
    exact hmean.contour_eq _ hyd _ hxd
theorem smoothing_local (h : ProjectionData L k j c) {V V' : Edge L k j → ComplexMatrix2}
    (hV : IsFieldOn complexGaugeGroup (doubleCubeLinks L (meshAt L k j) c) V)
    (hag : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V' b = V b)
    (hS : V ∈ complexDomainNearOne L c) :
    V' ∈ complexDomainNearOne L c ∧ complexSmoothing L V' c = complexSmoothing L V c := by
  have hV' : IsFieldOn complexGaugeGroup (doubleCubeLinks L (meshAt L k j) c) V' :=
    ⟨fun b hb => by rw [hag b hb]; exact hV.1 b hb,
      fun b hb => by rw [hag _ (h.closed b hb), hag b hb]; exact hV.2 b hb⟩
  have hq := projField_congr (L := L) (k := k) (j := j) hag
  have hT := (h.preserves.mem_complexDomain_iff V hV).1 hS
  have hS' : V' ∈ complexDomainNearOne L c :=
    (h.preserves.mem_complexDomain_iff V' hV').2 (by rw [hq]; exact hT)
  exact ⟨hS', by
    rw [h.preserves.complexSmoothing_eq V' hS', h.preserves.complexSmoothing_eq V hS, hq]⟩
theorem complexSmoothing_of_pos {V : Edge L k j → ComplexMatrix2} (hc : c.IsPositivelyOriented) :
    complexSmoothing L V c = complexSmoothingPositive L V c := if_pos hc
theorem complexSmoothing_of_not_pos {V : Edge L k j → ComplexMatrix2}
    (hc : ¬c.IsPositivelyOriented) :
    complexSmoothing L V c = (complexSmoothingPositive L V c.opposite)⁻¹ := if_neg hc
theorem operatorNorm_lt_of_supDistOne {V : Edge L k j → ComplexMatrix2} {ε : ℝ} (hε : 0 < ε)
    (hd : supDistOne V < ENNReal.ofReal ε) (b : Edge L k j) :
    ComplexMatrix2.operatorNorm (V b - 1) < ε := by
  have h : ENNReal.ofReal (ComplexMatrix2.operatorNorm (V b - 1)) < ENNReal.ofReal ε :=
    lt_of_le_of_lt (le_iSup (fun b => ENNReal.ofReal (ComplexMatrix2.operatorNorm (V b - 1))) b) hd
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 h
theorem smoothingBall_eq_supBall (I : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) {ε : ℝ} (hε : ε ≤ Averaging.smoothingRadius L / 4) :
    smoothingBall L k j ε = UniqueValue.supBall L k j compactGaugeGroup ε := by
  ext V
  constructor
  · rintro ⟨hD, hd⟩
    exact ⟨hD.1, hd⟩
  · rintro ⟨hV, hd⟩
    refine ⟨⟨hV, fun c hc => ?_⟩, hd⟩
    have h := I.near L k (j + 1) hL (by omega) (by omega) (by omega) V hV
      (lt_of_lt_of_le hd (ENNReal.ofReal_le_ofReal hε)) c hc
    refine ⟨h.1, ?_⟩
    rw [← complexSmoothing_of_pos hc]
    exact h.2.1
theorem one_mem_smoothingBall (I : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ Averaging.smoothingRadius L / 4) :
    (fun _ => 1 : Edge L k j → ComplexMatrix2) ∈ smoothingBall L k j ε := by
  rw [smoothingBall_eq_supBall I hL hj hε]
  refine ⟨one_mem_fieldSpace, ?_⟩
  simp [supDistOne, hε0]
theorem isFinitelyOpen_smoothingBall (I : Hypotheses)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ Averaging.smoothingRadius L / 4) :
    IsFinitelyOpen compactGaugeGroup (smoothingBall L k j ε) := by
  rw [smoothingBall_eq_supBall I hL hj hε]
  exact ((I.presentations L k j hL.1 hL.2 hj.le).2.1 ε hε0).2.1
theorem mapsTo_fieldSpace (hL : Conventions.IsAdmissibleBlockingFactor L) {ε : ℝ} :
    MapsTo (smoothingMap L k j) (smoothingBall L k j ε) (fieldSpace L k (j + 1)) := by
  intro V hV
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hG : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      complexSmoothingPositive L V c ∈ compactGaugeGroup := fun c hc => (hV.1.2 c hc).2
  refine ⟨fun c => ?_, fun c => ?_⟩
  · by_cases hc : c.IsPositivelyOriented
    · show complexSmoothing L V c ∈ compactGaugeGroup
      rw [complexSmoothing_of_pos hc]
      exact hG c hc
    · show complexSmoothing L V c ∈ compactGaugeGroup
      rw [complexSmoothing_of_not_pos hc]
      exact inv_mem_compact (hG _ (link_opposite_isPositivelyOriented hc))
  · show complexSmoothing L V c.opposite = (complexSmoothing L V c)⁻¹
    by_cases hc : c.IsPositivelyOriented
    · have hnr :=
        InfiniteLattice.Link.opposite_not_isPositivelyOriented (meshAt_pos hL0 k (j + 1)) hc
      rw [complexSmoothing_of_pos hc, complexSmoothing_of_not_pos hnr]
      rfl
    · have hr := link_opposite_isPositivelyOriented hc
      rw [complexSmoothing_of_pos hr, complexSmoothing_of_not_pos hc,
        inv_inv_of_mem_compact (hG _ hr)]
theorem exists_positive_finset (I : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) (hc : c.IsPositivelyOriented) : ∃ F : Finset (Edge L k j),
      (∀ b, b ∈ F ↔ b ∈ doubleCubeLinks L (meshAt L k j) c ∧ b.IsPositivelyOriented) ∧
      IsFinitePositiveEdgeSet F := by
  have hKc := I.doubleCube L k (j + 1) hL (by omega) (by omega) c hc
  have hbij : BijOn (projEdge L 1 k j) (doubleCubeLinks L (meshAt L k j) c)
      (PeriodicLattice.bondsInDoubleBlock (projEdge L 1 k (j + 1) c)) :=
    (hKc.2 1 Nat.one_pos).2.2.2.2.2.2
  have hE := I.bondSets L hL k j hj.le
  have hfinT : (PeriodicLattice.bondsInDoubleBlock (projEdge L 1 k (j + 1) c) :
      Set (Tower.Edge L 1 k j)).Finite := (hE.1 1 le_rfl).2.1.subset (subset_univ _)
  have hfin : (doubleCubeLinks L (meshAt L k j) c).Finite :=
    Set.Finite.of_injOn hbij.mapsTo hbij.injOn hfinT
  have hne : (doubleCubeLinks L (meshAt L k j) c).Nonempty := by
    obtain ⟨b, hb⟩ := (I.periodicDoubleBlock L 1 k j hL one_pos hj
      (projEdge L 1 k (j + 1) c)).2.2.1.2
    obtain ⟨b', hb', -⟩ := hbij.surjOn (show b ∈ _ from ⟨Or.inl hb.1, Or.inr hb.2⟩)
    exact ⟨b', hb'⟩
  obtain ⟨hpf, hpne, -⟩ := (hE.2 _ hfin hne hKc.1.2).1
  refine ⟨hpf.toFinset, fun b => ?_, ?_, fun b hb => ?_⟩
  · simp [BondSetFields.positivePart]
  · obtain ⟨b, hb⟩ := hpne
    exact ⟨b, by simpa using hb⟩
  · have : b ∈ BondSetFields.positivePart InfiniteLattice.Link.IsPositivelyOriented
        (doubleCubeLinks L (meshAt L k j) c) := by simpa using hb
    exact this.2
theorem fieldOfValuesOn_eq (h : ProjectionData L k j c) {F : Finset (Edge L k j)}
    (hF : ∀ b, b ∈ F ↔ b ∈ doubleCubeLinks L (meshAt L k j) c ∧ b.IsPositivelyOriented)
    {U : Edge L k j → ComplexMatrix2}
    (hU : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, U b.opposite = (U b)⁻¹)
    {w : F → ComplexMatrix2} (hw : ∀ b : F, w b = U b) {b : Edge L k j}
    (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) :
    fieldOfValuesOn F w b = U b := by
  classical
  by_cases hp : b.IsPositivelyOriented
  · have hbF : b ∈ F := (hF b).2 ⟨hb, hp⟩
    unfold fieldOfValuesOn
    rw [dif_pos hbF]
    exact hw ⟨b, hbF⟩
  · have hbF : b ∉ F := fun h' => hp ((hF b).1 h').2
    have hr : b.opposite ∈ F := (hF _).2 ⟨h.closed b hb, link_opposite_isPositivelyOriented hp⟩
    unfold fieldOfValuesOn
    rw [dif_neg hbF, dif_pos hr, hw ⟨b.opposite, hr⟩]
    exact (hU b.opposite (h.closed b hb)).symm
theorem isLocalPresentation (h : ProjectionData L k j c) (hc : c.IsPositivelyOriented)
    {ρ ε : ℝ} (hε0 : 0 < ε) (hερ : ε ≤ ρ) {F : Finset (Edge L k j)}
    (hF : ∀ b, b ∈ F ↔ b ∈ doubleCubeLinks L (meshAt L k j) c ∧ b.IsPositivelyOriented)
    (hFin : IsFinitePositiveEdgeSet F)
    (hO : ComplexMatrix2.IsRelativelyOpen (specialUnitaryPower F) (nearIdentityValues F ρ))
    {U : Edge L k j → ComplexMatrix2} (hU : U ∈ smoothingBall L k j ε) :
    IsLocalPresentation compactGaugeGroup (smoothingBall L k j ε) (fun V => smoothingMap L k j V c)
      U F (nearIdentityValues F ρ) fun w => complexSmoothing L (fieldOfValuesOn F w) c := by
  refine ⟨hFin, hO, ⟨fun b => hU.1.1.1 b, fun b => ?_⟩, fun U' hU' _ => ?_⟩
  · exact lt_of_lt_of_le (operatorNorm_lt_of_supDistOne hε0 hU.2 b.1) hερ
  · have hconf : IsFieldOn complexGaugeGroup (doubleCubeLinks L (meshAt L k j) c) U' :=
      ⟨fun b _ => mem_complexGaugeGroup_of_mem_compact (hU'.1.1.1 b), fun b _ => hU'.1.1.2 b⟩
    have hag : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
        fieldOfValuesOn F (restrictToEdges F U') b = U' b := fun b hb =>
      fieldOfValuesOn_eq h hF hconf.2 (fun _ => rfl) hb
    exact (smoothing_local h hconf hag (hU'.1.2 c hc).1).2.symm
theorem expTwist_zero (B : Edge L k j → ComplexMatrix2) :
    expTwist (((0 : ℝ) : ℂ) • B) (fun _ => 1) = (fun _ => 1 : Edge L k j → ComplexMatrix2) := by
  classical
  funext b
  by_cases hb : b.IsPositivelyOriented <;> simp [expTwist, hb, NormedSpace.exp_zero]
theorem expTwist_zero_periodic (B : Tower.Edge L 1 k j → ComplexMatrix2) :
    PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B) (fun _ => 1) =
      (fun _ => 1 : Tower.Edge L 1 k j → ComplexMatrix2) := by
  classical
  funext b
  by_cases hb : b.IsPositivelyOriented <;>
    simp [PeriodicLattice.expTwist, hb, NormedSpace.exp_zero]
theorem curve_eq_proj (I : Hypotheses) (h : ProjectionData L k j c)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) (hc : c.IsPositivelyOriented) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace (meshAt L k j)) :
    ∀ᶠ t : ℝ in 𝓝 0, expTwist ((t : ℂ) • B) (fun _ => 1) ∈ complexDomainNearOne L c ∧
      complexSmoothing L (expTwist ((t : ℂ) • B) (fun _ => 1)) c =
        Tower.smoothingStep L 1 k j (PeriodicLattice.expTwist
          ((t : ℂ) • pushforwardForm L 1 k j (doubleCubeLinks L (meshAt L k j) c) B)
          (fun _ => 1)) (projEdge L 1 k (j + 1) c) ∧
      ∀ y : Vertex L k (j + 1), y = c.initial ∨ y = c.terminal →
        ∀ x ∈ cubeVertices L (meshAt L k j) y,
          complexContourMean L (expTwist ((t : ℂ) • B) (fun _ => 1)) y x =
            PeriodicLattice.meanContourHolonomy (PeriodicLattice.expTwist
              ((t : ℂ) • pushforwardForm L 1 k j (doubleCubeLinks L (meshAt L k j) c) B)
              (fun _ => 1)) (projVertex L 1 k (j + 1) y) (projVertex L 1 k j x) := by
  filter_upwards [eventually_mem_commonSmoothingDomain I hL hj (pushforwardForm_mem h hB)]
    with t ht
  have hq := projField_expTwist h B (t : ℂ)
  have hconf := expTwist_mem_fieldSpace I hL hj.le hB t
  have hV : IsFieldOn complexGaugeGroup (doubleCubeLinks L (meshAt L k j) c)
      (expTwist ((t : ℂ) • B) (fun _ => 1)) :=
    ⟨fun b _ => mem_complexGaugeGroup_of_mem_compact (hconf.1 b), fun b _ => hconf.2 b⟩
  have htr := complex_data_eq_proj I h hL hj hc hV (by rw [hq]; exact ht)
  rw [hq] at htr
  exact htr
theorem deriv_at_pos (I : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) {ρ ε : ℝ} (hρ : IsAdmissiblePolydiscRadius L ρ) (hε0 : 0 < ε) (hερ : ε ≤ ρ)
    (hεω : ε ≤ Averaging.smoothingRadius L / 4) (hc : c.IsPositivelyOriented)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace (meshAt L k j)) :
    logDirectionalDeriv ℝ
        (valueViaPresentation compactGaugeGroup (smoothingBall L k j ε)
          (differentiablePresentations L k j ComplexMatrix2) (fun U' => smoothingMap L k j U' c)
          fun _ => 1)
        (smoothingMap L k j (fun _ => 1) c) B =
      linearSmoothing L B c := by
  classical
  have h := projectionData I hL hj hc
  obtain ⟨F, hF, hFin⟩ := exists_positive_finset I hL hj hc
  have hdiff := I.differentiable L hL k j hj ρ hρ c hc F hF
  have hone := one_mem_smoothingBall I hL hj hε0 hεω
  have hw₁ := isLocalPresentation h hc hε0 hερ hF hFin hdiff.1 hone
  have hspec := Classical.epsilon_spec
    (p := fun w : LocalData L k j ComplexMatrix2 =>
      IsLocalPresentation compactGaugeGroup (smoothingBall L k j ε)
        (fun V => smoothingMap L k j V c) (fun _ => 1) w.support w.region w.fn ∧
        differentiablePresentations L k j ComplexMatrix2 w.support w.region w.fn)
    ⟨⟨F, nearIdentityValues F ρ, fun w => complexSmoothing L (fieldOfValuesOn F w) c⟩,
      hw₁, hdiff⟩
  obtain ⟨ε', hε', hval⟩ := (I.presentations L k j hL.1 hL.2 hj.le).1.2.1 _
    (isFinitelyOpen_smoothingBall I hL hj hε0 hεω) (fun V => smoothingMap L k j V c)
    (fun _ => 1) hone _ _ _ _ _ _ hspec.1 hw₁ B B hB hB
  have hcurve := curve_eq_proj I h hL hj hc hB
  obtain ⟨-, hzero, -⟩ := hcurve.self_of_nhds
  rw [expTwist_zero, expTwist_zero_periodic] at hzero
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ‖t‖ < ε' := by
    have : Metric.ball (0 : ℝ) ε' ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε'
    filter_upwards [this] with t ht
    simpa using ht
  have hev : ∀ᶠ t : ℝ in 𝓝 0,
      valueViaPresentation compactGaugeGroup (smoothingBall L k j ε)
          (differentiablePresentations L k j ComplexMatrix2) (fun U' => smoothingMap L k j U' c)
          (fun _ => 1) (algebraMap ℝ ℂ t • B) =
        Tower.smoothingStep L 1 k j (PeriodicLattice.expTwist
          ((t : ℂ) • pushforwardForm L 1 k j (doubleCubeLinks L (meshAt L k j) c) B)
          (fun _ => 1)) (projEdge L 1 k (j + 1) c) := by
    filter_upwards [hsmall, hcurve] with t ht₁ ht₂
    obtain ⟨hS, hM, -⟩ := ht₂
    obtain ⟨-, -, e⟩ := hval t 0 ht₁ (by simpa using hε')
    have hconf := expTwist_mem_fieldSpace I hL hj.le hB t
    have hcV : IsFieldOn complexGaugeGroup (doubleCubeLinks L (meshAt L k j) c)
        (expTwist ((t : ℂ) • B) (fun _ => 1)) :=
      ⟨fun b _ => mem_complexGaugeGroup_of_mem_compact (hconf.1 b), fun b _ => hconf.2 b⟩
    have hag : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
        fieldOfValuesOn F (UniqueValue.perturbedTuple F B B (fun _ => 1)
          (algebraMap ℝ ℂ t) (algebraMap ℝ ℂ 0)) b = expTwist ((t : ℂ) • B) (fun _ => 1) b :=
      fun b hb => fieldOfValuesOn_eq h hF hcV.2 (fun b' => by
        have hp : (b' : Edge L k j).IsPositivelyOriented := hFin.2 _ b'.2
        simp [UniqueValue.perturbedTuple, expTwist, hp]) hb
    rw [← hM, ← (smoothing_local h hcV hag hS).2]
    refine Eq.trans ?_ e
    unfold valueViaPresentation
    congr 1
    funext b
    simp [UniqueValue.perturbedTuple]
  have hquot := pushforwardForm_mem h hB
  obtain ⟨𝒰, -, -, hQ⟩ := (I.sides L hL 1 k j one_pos hj).deriv_eq_linear
  have hq := congrFun (hQ _ hquot) (projEdge L 1 k (j + 1) c)
  have hd : (projEdge L 1 k (j + 1) c).IsPositivelyOriented :=
    ((I.edges L 1 k (j + 1) hL one_pos hj).1 c).2.2.1 hc
  rw [← (I.linear L k j 1 hL hj one_pos c hc B).2, ← hq]
  simp only [Tower.leftDifferential, Tower.extendOddly, if_pos hd, logDirectionalDeriv]
  congr 1
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [hev] with t ht
  rw [ht]
  show _ = ComplexMatrix2.logSeries (_ * (Tower.smoothingStep L 1 k j (fun _ => 1) _)⁻¹)
  rw [← hzero]
  rfl
theorem deriv_contour_eq (I : Hypotheses) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) {B : Edge L k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace (meshAt L k j))
    (y : Vertex L k (j + 1)) (x : Vertex L k j)
    (hx : x ∈ cubeVertices L (meshAt L k j) y) :
    Complex.I⁻¹ • deriv (fun t : ℝ => ComplexMatrix2.logSeries (complexContourMean L
        (expTwist ((t : ℂ) • B) (fun _ => 1)) y x)) 0 =
      contourAverage L B y x := by
  have hc : (InfiniteLattice.Link.forwardFrom y 0).IsPositivelyOriented :=
    ⟨0, by simp [InfiniteLattice.Link.forwardFrom]⟩
  have h := projectionData I hL hj hc
  have hy : y = (InfiniteLattice.Link.forwardFrom y 0).initial ∨
      y = (InfiniteLattice.Link.forwardFrom y 0).terminal := Or.inl rfl
  have hquot := pushforwardForm_mem h hB
  rw [← (I.linear L k j 1 hL hj one_pos _ hc B).1 y hy x hx,
    ← (I.sides L hL 1 k j one_pos hj).deriv_contour _ hquot _ _
      (projVertex_mem_block I h hL hj hy hx).2]
  congr 1
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [curve_eq_proj I h hL hj hc hB] with t ht
  rw [ht.2.2 y hy x hx]
end Tower.FullSpace.SmoothingDerivAllScalesLemmas
namespace Tower.FullSpace
open SmoothingDerivAllScalesLemmas in
theorem smoothingDerivAtOneAllScales_holds
    (sides : SmoothingDerivAtOneOnAllSides)
    (radius : AdmissiblePolydiscRadiusExists)
    (linear : ProjectionCommutesWithSmoothing)
    (differentiable : ComplexSmoothingDifferentiableOnPolydisc)
    (towers : SublatticesSymmetriesScalingsAndProjections.Statement)
    (edges : EdgeProjectionProperties)
    (doubleCube : DoubleCubeLinksAndTorusImage)
    (orientation : PeriodicLattice.BondOrientationDichotomy)
    (bondSets : BondSetFields.ProductStructureHolds)
    (periodicDoubleBlock : PeriodicLattice.DoubleBlockStructure.Statement)
    (near : SmoothingNearIdentity)
    (presentations : UniqueValue.PresentationsAgreeAndBallsOpen)
    (schemes : PeriodicLattice.AveragingSchemeProperties)
    (values : SmoothingNearTrivialField)
    (chart : LeftChartFields.Claim)
    (reversal : AxisPathReversal.MainStatement) :
    SmoothingDerivAtOneAllScales := by
  have I : Hypotheses := ⟨sides, radius, linear, differentiable, towers, edges, doubleCube,
    orientation, bondSets, periodicDoubleBlock, near, presentations, schemes, values, chart,
    reversal⟩
  intro L hL k j hj
  obtain ⟨ρ, hρ⟩ := radius L hL
  have hω : 0 < Averaging.smoothingRadius L :=
    (Averaging.isSmoothingRadius_smoothingRadius hL.1 hL.2).1
  refine ⟨⟨min ρ (Averaging.smoothingRadius L / 4), lt_min hρ.pos (by positivity),
    fun ε hε hle => ?_⟩, fun B hB y x hx => deriv_contour_eq I hL hj hB y x hx⟩
  have hερ : ε ≤ ρ := hle.trans (min_le_left _ _)
  have hεω : ε ≤ Averaging.smoothingRadius L / 4 := hle.trans (min_le_right _ _)
  refine ⟨⟨isFinitelyOpen_smoothingBall I hL hj hε hεω, mapsTo_fieldSpace hL, fun c hc =>
    ⟨fun U hU => hU.1.1, fun U hU => ?_⟩⟩, fun B hB => ?_⟩
  · obtain ⟨F, hF, hFin⟩ := exists_positive_finset I hL hj hc
    have hdiff := differentiable L hL k j hj ρ hρ c hc F hF
    exact ⟨F, nearIdentityValues F ρ, _,
      isLocalPresentation (projectionData I hL hj hc) hc hε hερ hF hFin hdiff.1 hU, hdiff⟩
  · funext c
    by_cases hc : c.IsPositivelyOriented
    · simp only [leftDifferential, extendOddly, if_pos hc]
      exact deriv_at_pos I hL hj hρ hε hερ hεω hc hB
    · have hr := link_opposite_isPositivelyOriented hc
      simp only [leftDifferential, extendOddly, if_neg hc]
      rw [deriv_at_pos I hL hj hρ hε hερ hεω hr hB]
      have hform := ((reversal L hL k).2.1 j hj.le).1 B hB
      have hrev := ((reversal L hL k).2.2 j (by omega) c.opposite B hform).2
      have hcc : c.opposite.opposite = c := rfl
      rw [hcc] at hrev
      rw [hrev]
end Tower.FullSpace
end YangMills.Construction
end
