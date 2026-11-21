import YangMills.Construction.Towers.ChainRuleAtAFiniteSideInTheLeftChartProof
import YangMills.Construction.Towers.SecondOrderOfACompositeAtOneProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.GroupLieProduct
namespace Tower.TrivialFieldSmoothingStep
open LeftChartFields (leftExpMul CurveLogDerivative)
open MeanStableFields (fieldsNearOne IsHolomorphicOnFields)
open LeftChartFacts (MapDerivAlongCurves)
variable {L n k j j' : ℕ}
theorem opposite_pos_of_not_pos {b : Edge L n k j} (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
theorem forwardFrom_pos (y : Vertex L n k j) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom y μ : Edge L n k j).IsPositivelyOriented :=
  ⟨μ, by show y + PeriodicLattice.unitStep L n _ μ - y = _; abel⟩
theorem extendOddly_congr {f g : Edge L n k j → ComplexMatrix2}
    (h : ∀ c : Edge L n k j, c.IsPositivelyOriented → f c = g c) : extendOddly f = extendOddly g := by apply _root_.YangMills.Construction.Tower.CovDiffStep.extendOddly_congr <;> assumption
theorem inv_eq_adjugate_of_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ = X.adjugate := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.MeanData.inv_eq_adjugate_of_mem <;> assumption
theorem isOpen_operatorNorm_sub_one_lt {r : ℝ} :
    IsOpen {X : ComplexMatrix2 | ComplexMatrix2.operatorNorm (X - 1) < r} :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
theorem mem_fieldsIn_complex {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j) :
    V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_fieldsIn_of_mem <;> assumption
theorem trivialField_mem_fieldSpace : trivialField L n k j ∈ fieldSpace L n k j := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.trivialField_mem <;> assumption
theorem fieldOfPositiveValues_mem
    (ho : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {w : PositiveEdge L n k j → ComplexMatrix2} (hw : ∀ c, w c ∈ ComplexMatrix2.unitDeterminant) :
    fieldOfPositiveValues w ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.CovDiffStep.fieldOfPositiveValues_mem <;> assumption
def expCurve (L n k j : ℕ) (B : Edge L n k j → ComplexMatrix2) (t : ℝ) :
    Edge L n k j → ComplexMatrix2 :=
  PeriodicLattice.expTwist ((t : ℂ) • B) (trivialField L n k j)
theorem leftExpMul_hasDerivAt (X V : ComplexMatrix2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => leftExpMul ((s : ℂ) • X) V)
      (ComplexMatrix2.matExp ((t : ℂ) • (Complex.I • X)) * (Complex.I • X) * V) t := by apply _root_.YangMills.Construction.Tower.FiniteLevelChainRule.hasDerivAt_leftExpMul <;> assumption
theorem expCurve_apply_pos (B : Edge L n k j → ComplexMatrix2) (t : ℝ) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : expCurve L n k j B t b = leftExpMul ((t : ℂ) • B b) 1 :=
  if_pos hb
theorem expCurve_apply_neg (B : Edge L n k j → ComplexMatrix2) (t : ℝ) {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) : expCurve L n k j B t b = (expCurve L n k j B t b.opposite)⁻¹ := by
  rw [expCurve_apply_pos B t (opposite_pos_of_not_pos hb)]
  exact if_neg hb
theorem expCurve_zero (B : Edge L n k j → ComplexMatrix2) :
    expCurve L n k j B 0 = trivialField L n k j := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [expCurve_apply_pos B 0 hb]
    simp [leftExpMul, ComplexMatrix2.matExp, NormedSpace.exp_zero]
  · rw [expCurve_apply_neg B 0 hb, expCurve_apply_pos B 0 (opposite_pos_of_not_pos hb)]
    simp [leftExpMul, ComplexMatrix2.matExp, NormedSpace.exp_zero]
theorem expCurve_differentiableAt (B : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) (t : ℝ) :
    DifferentiableAt ℝ (fun s => expCurve L n k j B s b) t := by
  have he : (fun s => expCurve L n k j B s b) = fun s : ℝ => leftExpMul ((s : ℂ) • B b) 1 :=
    funext fun s => expCurve_apply_pos B s hb
  rw [he]
  exact (leftExpMul_hasDerivAt (B b) 1 t).differentiableAt
theorem curveTangent_expCurve {B : Edge L n k j → ComplexMatrix2}
    (hrev : ∀ b : Edge L n k j, B b.opposite = -B b) :
    curveTangent (expCurve L n k j B) = B := by
  have key : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      Complex.I⁻¹ • (deriv (fun t => expCurve L n k j B t b) 0 * (expCurve L n k j B 0 b)⁻¹) =
        B b := by
    intro b hb
    have he : (fun s => expCurve L n k j B s b) = fun s : ℝ => leftExpMul ((s : ℂ) • B b) 1 :=
      funext fun s => expCurve_apply_pos B s hb
    rw [he, (leftExpMul_hasDerivAt (B b) 1 0).deriv, expCurve_zero B]
    simp only [Complex.ofReal_zero, zero_smul, ComplexMatrix2.matExp, NormedSpace.exp_zero,
      one_mul, mul_one, trivialField, inv_one]
    exact inv_smul_smul₀ Complex.I_ne_zero _
  funext b
  unfold curveTangent extendOddly
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb]
    exact key b hb
  · rw [if_neg hb]
    beta_reduce
    rw [key _ (opposite_pos_of_not_pos hb), hrev, neg_neg]
section Fields
variable (hB1 : SmoothingNearTrivialField)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) (hj : j ≤ k)
  {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j)
include hB1 hL hn hk hj hB
theorem expCurve_mem (t : ℝ) : expCurve L n k j B t ∈ fieldSpace L n k j := by
  have e : (t : ℂ) • B = t • B := by
    funext b
    ext r s
    simp
  have h : (t : ℂ) • B ∈ edgeFormSpace L n k j := by
    rw [e]
    exact (edgeFormSpace L n k j).smul_mem t hB
  exact (hB1 L n k hL hn hk).2 j hj _ h _ trivialField_mem_fieldSpace
theorem expCurve_isCurve_compact :
    IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup univ (expCurve L n k j B) :=
  ⟨⟨isOpen_univ, ordConnected_univ, mem_univ _⟩,
    fun t _ => expCurve_mem hB1 hL hn hk hj hB t,
    fun _ hb t _ => (expCurve_differentiableAt B hb t).differentiableWithinAt⟩
theorem expCurve_isCurve_complex :
    IsDifferentiableFieldCurve PeriodicLattice.complexGaugeGroup univ (expCurve L n k j B) :=
  ⟨⟨isOpen_univ, ordConnected_univ, mem_univ _⟩,
    fun t _ => mem_fieldsIn_complex (expCurve_mem hB1 hL hn hk hj hB t),
    fun _ hb t _ => (expCurve_differentiableAt B hb t).differentiableWithinAt⟩
theorem expCurve_tendsto :
    Tendsto (expCurve L n k j B) (𝓝 0) (𝓝 (trivialField L n k j)) := by
  have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      Tendsto (fun t => expCurve L n k j B t b) (𝓝 0) (𝓝 1) := by
    intro b hb
    have h := (expCurve_differentiableAt B hb 0).continuousAt.tendsto
    rwa [expCurve_zero B] at h
  refine tendsto_pi_nhds.2 fun b => ?_
  by_cases hb : b.IsPositivelyOriented
  · exact hpos b hb
  · have hr := opposite_pos_of_not_pos hb
    have h2 : Tendsto (fun t => (expCurve L n k j B t b.opposite).adjugate) (𝓝 0)
        (𝓝 (1 : ComplexMatrix2).adjugate) :=
      (Continuous.matrix_adjugate continuous_id).continuousAt.tendsto.comp (hpos _ hr)
    rw [Matrix.adjugate_one] at h2
    refine h2.congr fun t => ?_
    rw [expCurve_apply_neg B t hb]
    exact (inv_eq_adjugate_of_mem
      ((mem_fieldsIn_complex (expCurve_mem hB1 hL hn hk hj hB t)).1 _ trivial)).symm
theorem eventually_expCurve_of_near {P : (Edge L n k j → ComplexMatrix2) → Prop}
    (h : EventuallyNearIdentity (fieldSpace L n k j) P) :
    ∀ᶠ t in 𝓝 (0 : ℝ), P (expCurve L n k j B t) :=
  (tendsto_nhdsWithin_iff.2 ⟨expCurve_tendsto hB1 hL hn hk hj hB,
    Eventually.of_forall (expCurve_mem hB1 hL hn hk hj hB)⟩).eventually h
end Fields
theorem trivialField_mem_fieldsNearOne {ρ : ℝ} (hρ : ρ = polydiscRadius L) (h0 : 0 < ρ) :
    trivialField L n k j ∈ fieldsNearOne L n k j :=
  ⟨mem_fieldsIn_complex trivialField_mem_fieldSpace, fun b => by
    rw [← hρ]
    simpa using h0⟩
theorem eventually_expCurve_mem_fieldsNearOne (hB1 : SmoothingNearTrivialField)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) (hj : j ≤ k)
    [Finite (Edge L n k j)] (h0 : 0 < polydiscRadius L)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j) :
    ∀ᶠ t in 𝓝 (0 : ℝ), expCurve L n k j B t ∈ fieldsNearOne L n k j := by
  have hT := expCurve_tendsto hB1 hL hn hk hj hB
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ b,
      ComplexMatrix2.operatorNorm (expCurve L n k j B t b - 1) < polydiscRadius L := by
    refine eventually_all.2 fun b => ?_
    refine (tendsto_pi_nhds.1 hT b).eventually (isOpen_operatorNorm_sub_one_lt.mem_nhds ?_)
    simpa using h0
  filter_upwards [hall] with t ht
  exact ⟨mem_fieldsIn_complex (expCurve_mem hB1 hL hn hk hj hB t), ht⟩
theorem isHolomorphicFieldMap_of_entries {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {𝔇 : Set (Edge L n k j → ComplexMatrix2)}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (h𝔇 : IsOpenFieldSet PeriodicLattice.complexGaugeGroup 𝔇)
    (hc : MapsTo m 𝔇 (fieldsIn L n k j' PeriodicLattice.complexGaugeGroup))
    (hm : ∀ c : Edge L n k j', c.IsPositivelyOriented → IsHolomorphicOnFields β 𝔇 fun V => m V c)
    (fin : Fintype (PositiveEdge L n k j')) {c₀ : Edge L n k j'}
    (hc₀ : c₀.IsPositivelyOriented) :
    IsHolomorphicFieldMap β 𝔇 m := by apply _root_.YangMills.Construction.Tower.CovDiffStep.isHolomorphicFieldMap_of_components <;> assumption
theorem apply_mem_unitDeterminant {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {𝔇 : Set (Edge L n k j → ComplexMatrix2)}
    {h : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2} (hh : IsHolomorphicOnFields β 𝔇 h)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ 𝔇) : h V ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.Construction.Tower.CovDiffStep.apply_mem_unitDeterminant <;> assumption
theorem curveTangent_congr {m₁ m₂ : ℝ → Edge L n k j' → ComplexMatrix2}
    (h : ∀ c : Edge L n k j', c.IsPositivelyOriented →
      (fun t => m₁ t c) =ᶠ[𝓝 0] fun t => m₂ t c) :
    curveTangent m₁ = curveTangent m₂ := by apply _root_.YangMills.Construction.Tower.CovDiffStep.curveTangent_congr <;> assumption
theorem exists_mem_sitesInBlock (hBlk : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i : ℕ} (hi : i < k)
    (y : Vertex L n k (i + 1)) :
    ∃ x : Vertex L n k i, x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y := by
  have hb := (hBlk L k (i + 1) hL (by omega) (by omega) hi).1 n hn
  have hmem : (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
    have h := hb.2.1.1 y
    have h' : (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∩
        (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) :
          Set (PeriodicLattice.FourTorus L n)) := by
      rw [h]
      exact mem_singleton _
    exact h'.1
  exact ⟨⟨_, (hb.1 y).2.2.2 hmem⟩, hmem⟩
theorem xor_pos_opposite_pos (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) (hj : j ≤ k)
    (b : Edge L n k j) : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
  ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj).2.2.2 b).2.2.2.2.2
theorem finite_edge (hE6 : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Finite (Edge L n k j) :=
  Set.finite_univ_iff.1 ((hE6 L hL k j hj).1 n hn).2.1
theorem complexBlockAverageStep_eq {i : ℕ} (V : Edge L n k i → ComplexMatrix2) :
    PeriodicLattice.complexBlockAverageStep i V =
      fieldOfPositiveValues fun c : PositiveEdge L n k (i + 1) =>
        PeriodicLattice.complexBlockAverage V c.1 := by apply _root_.YangMills.Construction.Tower.CovDiffStep.complexBlockAverageStep_eq <;> assumption
section Main
variable {i : ℕ}
theorem complexBlockAverageStep_trivial (hH : LevelwiseMeans.LevelwiseMeansHold)
    (hT : TrivialFieldAtStep) (hBlk : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i < k)
    {c : Edge L n k (i + 1)} (hc : c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverageStep i (trivialField L n k i) c = 1 := by
  have hk : 1 ≤ k := by omega
  obtain ⟨x, hx⟩ := exists_mem_sitesInBlock hBlk hL hn hi c.source
  have hnear := ((hH L hL k hk).1 n hn).agree_near_identity i hi c hc c.source (Or.inl rfl) x hx
  have h1 := Filter.Eventually.self_of_nhdsWithin hnear trivialField_mem_fieldSpace
  have h3 := h1.2.1
  rw [(hT L n k i hL hn hi).2.1] at h3
  exact h3
theorem complexMeanContourHolonomy_trivial (hH : LevelwiseMeans.LevelwiseMeansHold)
    (hT : TrivialFieldAtStep)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i < k)
    (y : Vertex L n k (i + 1)) {x : Vertex L n k i}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y) :
    PeriodicLattice.complexMeanContourHolonomy (trivialField L n k i) y x = 1 := by
  have hk : 1 ≤ k := by omega
  have hc := forwardFrom_pos y 0
  have hnear := ((hH L hL k hk).1 n hn).agree_near_identity i hi _ hc y (Or.inl rfl) x hx
  have h1 := Filter.Eventually.self_of_nhdsWithin hnear trivialField_mem_fieldSpace
  rw [h1.2.2.2.1]
  exact (hT L n k i hL hn hi).1 y x hx
theorem complexSmoothingDeriv_trivial (hS : SmoothingNearIdentity)
    (hH : LevelwiseMeans.LevelwiseMeansHold)
    (hP1 : MeanStableFields.MeanStableFieldsHold)
    (hCu : FiniteLevelCurveDifferentials.Statement)
    (hB1 : SmoothingNearTrivialField)
    (hBlk : BlockStructure)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hE6 : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i < k)
    {B : Edge L n k i → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k i) :
    complexSmoothingDeriv (trivialField L n k i) B = linearSmoothing L n k i B := by
  have hk : 1 ≤ k := by omega
  have ho := xor_pos_opposite_pos (j := i + 1) hE hL hn hk hi
  have hP' := (hP1 L hL k hk).1 n hn
  have h0 : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  have := finite_edge (j := i + 1) hE6 hL hn hi
  have fin : Fintype (PositiveEdge L n k (i + 1)) := Fintype.ofFinite _
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless := OneLoop.pauliBasis
  have hmaps : MapsTo (PeriodicLattice.complexBlockAverageStep (L := L) (m := n) (K := k) i)
      (fieldsNearOne L n k i)
      (fieldsIn L n k (i + 1) PeriodicLattice.complexGaugeGroup) := by
    intro V hV
    rw [complexBlockAverageStep_eq]
    exact fieldOfPositiveValues_mem ho fun c =>
      apply_mem_unitDeterminant (hP'.holomorphic_smoothing i hi c.1 c.2 β) hV
  have hhol : IsHolomorphicFieldMap β (fieldsNearOne L n k i)
      (PeriodicLattice.complexBlockAverageStep (L := L) (m := n) (K := k) i) :=
    isHolomorphicFieldMap_of_entries (hP'.isOpen_nearOne i hi) hmaps
      (fun c hc => hP'.holomorphic_smoothing i hi c hc β) fin
      (forwardFrom_pos (0 : Vertex L n k (i + 1)) 0)
  have hcurv := hCu L k i (i + 1) hL hi.le hi n hn
  have h1 := (hcurv.2.2.1 β _ _ hhol _ (trivialField_mem_fieldsNearOne rfl h0)) univ
    (expCurve L n k i B) (expCurve_isCurve_complex hB1 hL hn hk hi.le hB) (expCurve_zero B)
  obtain ⟨𝒰, hU, hdm, hd⟩ := ((hS.1 L hL).1 n k i hn hi).2.1.deriv_eq_linear
  have h2 := (hcurv.1 𝒰 _ hdm _ hU.2) univ (expCurve L n k i B)
    (expCurve_isCurve_compact hB1 hL hn hk hi.le hB) (expCurve_zero B)
  have ht : curveTangent (expCurve L n k i B) = B := curveTangent_expCurve hB.2
  have t1 := h1.2
  have t2 := h2.2
  rw [ht] at t1 t2
  rw [← hd B hB]
  show holLeftDifferential _ _ B = _
  rw [← t1, ← t2]
  refine curveTangent_congr fun c hc => ?_
  obtain ⟨x, hx⟩ := exists_mem_sitesInBlock hBlk hL hn hi c.source
  have hnear := ((hH L hL k hk).1 n hn).agree_near_identity i hi c hc c.source (Or.inl rfl) x hx
  filter_upwards [eventually_expCurve_of_near hB1 hL hn hk hi.le hB hnear] with t ht'
  exact ht'.2.1
theorem logDirectionalDeriv_contour_trivial (hS : SmoothingNearIdentity)
    (hH : LevelwiseMeans.LevelwiseMeansHold)
    (hP1 : MeanStableFields.MeanStableFieldsHold)
    (hO2 : PolydiscContours.ContourHolomorphyHolds)
    (hA : LeftChartFields.Claim)
    (hCu : FiniteLevelCurveDifferentials.Statement)
    (hT : TrivialFieldAtStep)
    (hB1 : SmoothingNearTrivialField)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hE6 : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i < k)
    {B : Edge L n k i → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k i)
    (y : Vertex L n k (i + 1)) {x : Vertex L n k i}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y) :
    logDirectionalDeriv ℂ
      (fun X => PeriodicLattice.complexMeanContourHolonomy
        (PeriodicLattice.expTwist X (trivialField L n k i)) y x)
      (PeriodicLattice.complexMeanContourHolonomy (trivialField L n k i) y x) B =
      PeriodicLattice.contourFormAverage B y x := by
  have hk : 1 ≤ k := by omega
  have ho := xor_pos_opposite_pos (j := i + 1) hE hL hn hk hi
  have hP' := (hP1 L hL k hk).1 n hn
  have h0 : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  have := finite_edge (j := i + 1) hE6 hL hn hi
  have := finite_edge (j := i) hE6 hL hn hi.le
  have fin : Fintype (PositiveEdge L n k (i + 1)) := Fintype.ofFinite _
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless := OneLoop.pauliBasis
  have hc : (PeriodicLattice.Bond.forwardFrom y 0 : Edge L n k (i + 1)).IsPositivelyOriented :=
    forwardFrom_pos y 0
  have hy : y ∈ ({(PeriodicLattice.Bond.forwardFrom y 0 : Edge L n k (i + 1)).source,
      (PeriodicLattice.Bond.forwardFrom y 0 : Edge L n k (i + 1)).target} :
      Set (Vertex L n k (i + 1))) := Or.inl rfl
  have hg := (((hO2 L hL k i hi).1 n hn _ hc).holomorphicOn_fieldsNearOne y hy x hx).isHolomorphicOnFields β
  let h : (Edge L n k i → ComplexMatrix2) → ComplexMatrix2 :=
    fun V => PeriodicLattice.complexMeanContourHolonomy V y x
  let m : (Edge L n k i → ComplexMatrix2) → Edge L n k (i + 1) → ComplexMatrix2 :=
    fun V => fieldOfPositiveValues fun _ => h V
  have hmpos : ∀ (V : Edge L n k i → ComplexMatrix2) (c : Edge L n k (i + 1)),
      c.IsPositivelyOriented → m V c = h V :=
    fun V c hc' => dif_pos hc'
  have hmaps : MapsTo m (fieldsNearOne L n k i)
      (fieldsIn L n k (i + 1) PeriodicLattice.complexGaugeGroup) :=
    fun V hV => fieldOfPositiveValues_mem ho fun _ => apply_mem_unitDeterminant hg hV
  have hhol : IsHolomorphicFieldMap β (fieldsNearOne L n k i) m := by
    refine isHolomorphicFieldMap_of_entries (hP'.isOpen_nearOne i hi) hmaps (fun c hc' => ?_) fin hc
    have e : (fun V => m V c) = h := funext fun V => hmpos V c hc'
    rw [e]
    exact hg
  have hcurv := hCu L k i (i + 1) hL hi.le hi n hn
  have h1 := (hcurv.2.2.1 β _ _ hhol _ (trivialField_mem_fieldsNearOne rfl h0)) univ
    (expCurve L n k i B) (expCurve_isCurve_complex hB1 hL hn hk hi.le hB) (expCurve_zero B)
  have ht : curveTangent (expCurve L n k i B) = B := curveTangent_expCurve hB.2
  have t1 := h1.2
  rw [ht] at t1
  have e1 := congrFun t1 (PeriodicLattice.Bond.forwardFrom y 0)
  simp only [curveTangent, holLeftDifferential, extendOddly, if_pos hc] at e1
  have e2 : (fun t => m (expCurve L n k i B t) (PeriodicLattice.Bond.forwardFrom y 0)) =
      fun t => h (expCurve L n k i B t) := funext fun t => hmpos _ _ hc
  have e3 : (fun X => m (PeriodicLattice.expTwist X (trivialField L n k i))
      (PeriodicLattice.Bond.forwardFrom y 0)) =
      fun X => h (PeriodicLattice.expTwist X (trivialField L n k i)) :=
    funext fun X => hmpos _ _ hc
  rw [e2, e3, hmpos _ _ hc, hmpos _ _ hc, expCurve_zero B] at e1
  have hone : h (trivialField L n k i) = 1 := complexMeanContourHolonomy_trivial hH hT hL hn hi y hx
  have hd : DifferentiableAt ℝ (fun t => h (expCurve L n k i B t)) 0 := by
    have h2 := h1.1 _ hc
    rwa [e2] at h2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (eventually_expCurve_mem_fieldsNearOne hB1 hL hn hk hi.le h0 hB)
  have hI : IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) ε) :=
    ⟨Metric.isOpen_ball, by rw [Real.ball_eq_Ioo]; exact ordConnected_Ioo, Metric.mem_ball_self hε⟩
  have hlog := (hA.1 _ hI).2 (fun t => h (expCurve L n k i B t))
    (fun t ht' => apply_mem_unitDeterminant hg (hball t ht')) hd
  have hnear := ((hH L hL k hk).1 n hn).agree_near_identity i hi _ hc y (Or.inl rfl) x hx
  have hev := eventually_expCurve_of_near hB1 hL hn hk hi.le hB hnear
  have hcontour := ((hS.1 L hL).1 n k i hn hi).2.1.deriv_contour B hB y x hx
  show logDirectionalDeriv ℂ
      (fun X => h (PeriodicLattice.expTwist X (trivialField L n k i)))
      (h (trivialField L n k i)) B = _
  rw [← e1, ← hcontour]
  have e4 : Complex.I⁻¹ • (deriv (fun t => h (expCurve L n k i B t)) 0 *
      (h (trivialField L n k i))⁻¹) =
      Complex.I⁻¹ • deriv (fun t => ComplexMatrix2.logSeries (h (expCurve L n k i B t) *
        (h (expCurve L n k i B 0))⁻¹)) 0 := by
    have := hlog.2.2.1
    simp only [expCurve_zero B] at this
    rw [expCurve_zero B]
    exact this.symm
  rw [e4]
  congr 1
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [hev] with t ht'
  rw [expCurve_zero B, hone, inv_one, mul_one]
  show ComplexMatrix2.logSeries
    (PeriodicLattice.complexMeanContourHolonomy (expCurve L n k i B t) y x) = _
  rw [ht'.2.2.2.1]
  rfl
theorem covDiff_complexStep_trivial (hH : LevelwiseMeans.LevelwiseMeansHold)
    (hT : TrivialFieldAtStep) (hBlk : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i < k)
    (l : Vertex L n k (i + 1) → ComplexMatrix2) :
    covDiff (PeriodicLattice.complexBlockAverageStep i (trivialField L n k i)) l =
      vertexCoboundary l := by
  have e : covDiff (PeriodicLattice.complexBlockAverageStep i (trivialField L n k i)) l =
      extendOddly (vertexCoboundary l) := by
    refine extendOddly_congr fun c hc => ?_
    rw [complexBlockAverageStep_trivial hH hT hBlk hL hn hi hc]
    simp [ComplexMatrix2.conjugateBy, vertexCoboundary]
  rw [e]
  funext b
  unfold extendOddly
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb]
  · rw [if_neg hb]
    show -(l b.source - l b.target) = l b.target - l b.source
    rw [neg_sub]
end Main
theorem statement_holds (hS : SmoothingNearIdentity)
    (hH : LevelwiseMeans.LevelwiseMeansHold)
    (hP1 : MeanStableFields.MeanStableFieldsHold)
    (hO2 : PolydiscContours.ContourHolomorphyHolds)
    (hA : LeftChartFields.Claim)
    (hCu : FiniteLevelCurveDifferentials.Statement)
    (hT : TrivialFieldAtStep)
    (hB1 : SmoothingNearTrivialField)
    (hBlk : BlockStructure)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hE6 : BondSetFields.ProductStructureHolds)
    (hR : TrivialLinearization.AllRelationsStatement) : Statement := by
  intro L hL n k i hn hi
  have hQ : ∀ B ∈ edgeFormSpace L n k i,
      complexSmoothingDeriv (trivialField L n k i) B = linearSmoothing L n k i B :=
    fun B hB => complexSmoothingDeriv_trivial hS hH hP1 hCu hB1 hBlk hE hE6 hL hn hi hB
  have hN : ∀ B ∈ edgeFormSpace L n k i,
      contourLogDrift (trivialField L n k i) B = cubeContourAverage L n k i B := by
    intro B hB
    funext y
    unfold contourLogDrift cubeContourAverage
    congr 1
    exact finsum_mem_congr rfl fun x hx =>
      logDirectionalDeriv_contour_trivial hS hH hP1 hO2 hA hCu hT hB1 hE hE6 hL hn hi hB y hx
  have hrel := ((hR L hL).1 n k i 0 hn hi (Nat.zero_le _)).1.1
  refine ⟨fun B hB => ⟨hQ B hB, hN B hB, ?_⟩, fun l _ => ?_⟩
  · unfold covariantSmoothingDeriv
    rw [hQ B hB, hN B hB, covDiff_complexStep_trivial hH hT hBlk hL hn hi, hrel B hB,
      sub_add_cancel]
  · funext y
    unfold adjointCubeAverage vertexSmoothing
    congr 1
    refine finsum_mem_congr rfl fun x hx => ?_
    rw [complexMeanContourHolonomy_trivial hH hT hL hn hi y hx]
    simp [ComplexMatrix2.conjugateBy]
end Tower.TrivialFieldSmoothingStep
end YangMills.Construction
end
