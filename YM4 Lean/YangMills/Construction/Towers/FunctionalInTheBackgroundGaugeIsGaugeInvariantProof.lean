import YangMills.Construction.Towers.BackgroundGaugeFunctionalIsFormedAtTheTrivialPointProof
import YangMills.Construction.Towers.FunctionalInTheBackgroundGaugeIsGaugeInvariant
import YangMills.Construction.Towers.GaugeCovarianceOfTheCovariantAveragesOnTheSidesProof
import YangMills.Construction.Towers.GaugeCovarianceOfTheLiftProof
import YangMills.Construction.Towers.LinearMapsOnTheRealSpacesProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
namespace YangMills.Construction
open YangMills.Construction.Tower YangMills.Construction.Matrices
noncomputable section
namespace BackgroundGaugeInvariance
section InnerCores
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
theorem adjoint_intertwine (c : InnerProductSpace.Core ℝ V) (c' : InnerProductSpace.Core ℝ W)
    (a : V ≃ₗ[ℝ] V) (b : W ≃ₗ[ℝ] W) (hb : ∀ x y, c'.inner (b x) (b y) = c'.inner x y)
    (ha : ∀ x y, c.inner (a x) (a y) = c.inner x y)
    {T T' : V →ₗ[ℝ] W} {S S' : W →ₗ[ℝ] V} (hT : ∀ x, T' (a x) = b (T x))
    (hS : ∀ y x, c.inner (S y) x = c'.inner y (T x))
    (hS' : ∀ y x, c.inner (S' y) x = c'.inner y (T' x)) (y : W) :
    S' (b y) = a (S y) := by
  let := c.toNormedAddCommGroup
  let := InnerProductSpace.ofCore c.toCore
  refine ext_inner_right ℝ fun x => ?_
  obtain ⟨x, rfl⟩ := a.surjective x
  show c.inner _ _ = c.inner _ _
  rw [hS', hT, hb, ha, hS]
theorem saddleDetOfCores_conj_eq [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (c : InnerProductSpace.Core ℝ V) (c' : InnerProductSpace.Core ℝ W)
    (a : V ≃ₗ[ℝ] V) (b : W ≃ₗ[ℝ] W) (ha : ∀ x y, c.inner (a x) (a y) = c.inner x y)
    (hb : ∀ x y, c'.inner (b x) (b y) = c'.inner x y) {X X' : V →ₗ[ℝ] V} {M M' : V →ₗ[ℝ] W}
    (hX : ∀ x, X' (a x) = a (X x)) (hM : ∀ x, M' (a x) = b (M x)) :
    GaussianConstraint.saddleDetOfCores c c' X' M' =
      GaussianConstraint.saddleDetOfCores c c' X M := by
  let := c.toNormedAddCommGroup
  let := InnerProductSpace.ofCore c.toCore
  let := c'.toNormedAddCommGroup
  let := InnerProductSpace.ofCore c'.toCore
  unfold GaussianConstraint.saddleDetOfCores
  have hadj : ∀ y, LinearMap.adjoint M' (b y) = a (LinearMap.adjoint M y) :=
    adjoint_intertwine c c' a b hb ha hM (fun y x => LinearMap.adjoint_inner_left M x y)
      (fun y x => LinearMap.adjoint_inner_left M' x y)
  let e : (V × W) ≃ₗ[ℝ] V × W := a.prodCongr b
  have hconj : GaussianConstraint.saddlePointOperator X' M' =
      (e : (V × W) →ₗ[ℝ] V × W) ∘ₗ GaussianConstraint.saddlePointOperator X M ∘ₗ
        (e.symm : (V × W) →ₗ[ℝ] V × W) := by
    refine LinearMap.ext fun p => ?_
    obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective p
    have h₁ : e (x, y) = (a x, b y) := rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [h₁]
    refine Prod.ext ?_ ?_
    · show X' (a x) + LinearMap.adjoint M' (b y) = a (X x + LinearMap.adjoint M y)
      rw [hX, hadj, map_add]
    · show M' (a x) = b (M x)
      exact hM x
  rw [hconj, LinearMap.det_conj]
end InnerCores
section TwoByTwo
theorem inv_mul_self_of_det_one {V : ComplexMatrix2} (h : V.det = 1) : V⁻¹ * V = 1 :=
  Matrix.nonsing_inv_mul V (by rw [h]; exact isUnit_one)
theorem inv_inv_of_det_one {V : ComplexMatrix2} (h : V.det = 1) : V⁻¹⁻¹ = V :=
  Matrix.nonsing_inv_nonsing_inv V (by rw [h]; exact isUnit_one)
theorem det_eq_one_of_mem {V : ComplexMatrix2} (h : V ∈ PeriodicLattice.compactGaugeGroup) :
    V.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem conjugateBy_add (g X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (X + Y) =
      ComplexMatrix2.conjugateBy g X + ComplexMatrix2.conjugateBy g Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_sub (g X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (X - Y) =
      ComplexMatrix2.conjugateBy g X - ComplexMatrix2.conjugateBy g Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_sub, sub_mul]
theorem conjugateBy_smul (g : ComplexMatrix2) (c : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (c • X) = c • ComplexMatrix2.conjugateBy g X := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
theorem conjugateBy_real_smul (g : ComplexMatrix2) (c : ℝ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (c • X) = c • ComplexMatrix2.conjugateBy g X := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.conjugateBy_real_smul <;> assumption
theorem conjugateBy_zero (g : ComplexMatrix2) : ComplexMatrix2.conjugateBy g 0 = 0 := by
  simp only [ComplexMatrix2.conjugateBy, mul_zero, zero_mul]
theorem conjugateBy_mul {g : ComplexMatrix2} (hg : g.det = 1) (X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g X * ComplexMatrix2.conjugateBy g Y =
      ComplexMatrix2.conjugateBy g (X * Y) := by
  simp only [ComplexMatrix2.conjugateBy]
  calc g * X * g⁻¹ * (g * Y * g⁻¹) = g * X * (g⁻¹ * g) * Y * g⁻¹ := by simp only [mul_assoc]
    _ = g * (X * Y) * g⁻¹ := by
      rw [inv_mul_self_of_det_one hg, mul_one]; simp only [mul_assoc]
theorem conjugateBy_lie {g : ComplexMatrix2} (hg : g.det = 1) (X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g ⁅X, Y⁆ =
      ⁅ComplexMatrix2.conjugateBy g X, ComplexMatrix2.conjugateBy g Y⁆ := by
  simp only [Ring.lie_def, conjugateBy_mul hg, conjugateBy_sub]
theorem halfTrace_conjugateBy {g : ComplexMatrix2} (hg : g.det = 1) (X Y : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (ComplexMatrix2.conjugateBy g X * ComplexMatrix2.conjugateBy g Y) =
      ComplexMatrix2.halfTrace (X * Y) := by
  rw [conjugateBy_mul hg]
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, ComplexMatrix2.conjugateBy]
  rw [Matrix.trace_mul_comm, ← mul_assoc, inv_mul_self_of_det_one hg, one_mul]
theorem conjugateBy_twisted {g h : ComplexMatrix2} (X A : ComplexMatrix2) (hh : h.det = 1) :
    ComplexMatrix2.conjugateBy (g * X * h⁻¹) (ComplexMatrix2.conjugateBy h A) =
      ComplexMatrix2.conjugateBy g (ComplexMatrix2.conjugateBy X A) := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.conjugateBy_conjugateBy_gauge <;> assumption
theorem logSeries_conj {g : ComplexMatrix2} (hg : g.det = 1) (X : ComplexMatrix2) :
    ComplexMatrix2.logSeries (g * X * g⁻¹) =
      ComplexMatrix2.conjugateBy g (ComplexMatrix2.logSeries X) := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.logSeries_conj <;> assumption
theorem twisted_mul_inv {g h W W₀ : ComplexMatrix2} (hh : h.det = 1) :
    (g * W * h⁻¹) * (g * W₀ * h⁻¹)⁻¹ = g * (W * W₀⁻¹) * g⁻¹ := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.mul_inv_gauge_conj <;> assumption
theorem twisted_inv {g h X : ComplexMatrix2} (hh : h.det = 1) :
    (g * X * h⁻¹)⁻¹ = h * X⁻¹ * g⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_of_det_one hh, mul_assoc]
theorem isUnit_det_of_mem {X : ComplexMatrix2} (hX : X ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit X.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem inv_mem_compact {X : ComplexMatrix2} (hX : X ∈ PeriodicLattice.compactGaugeGroup) :
    X⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem mem_unitary_of_mem {X : ComplexMatrix2} (hX : X ∈ PeriodicLattice.compactGaugeGroup) :
    X ∈ unitary ComplexMatrix2 :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hX).1
theorem norm_conjugateBy {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (X : ComplexMatrix2) : ‖ComplexMatrix2.conjugateBy g X‖ = ‖X‖ := by
  unfold ComplexMatrix2.conjugateBy
  rw [CStarRing.norm_mul_mem_unitary _ (mem_unitary_of_mem (inv_mem_compact hg)),
    CStarRing.norm_mem_unitary_mul _ (mem_unitary_of_mem hg)]
theorem norm_twisted_sub_one_le {a c X : ComplexMatrix2}
    (ha : a ∈ PeriodicLattice.compactGaugeGroup) (hc : c ∈ PeriodicLattice.compactGaugeGroup) :
    ‖a * X * c⁻¹ - 1‖ ≤ ‖X - 1‖ + ‖a - 1‖ + ‖c - 1‖ := by apply _root_.YangMills.SharedProofs.p32758 <;> assumption
theorem norm_conj_sub_one_eq {a X : ComplexMatrix2} (ha : a ∈ PeriodicLattice.compactGaugeGroup) :
    ‖a * X * a⁻¹ - 1‖ = ‖X - 1‖ := by apply _root_.YangMills.Construction.PeriodicLattice.HolonomyUnderReordering.norm_conj_sub_one_of_mem <;> assumption
end TwoByTwo
section NearIdentity
theorem isOpen_nearIdentity {ι : Type*} [Finite ι] (δ : ℝ) :
    IsOpen {V : ι → ComplexMatrix2 | ∀ b, ‖V b - 1‖ < δ} := by apply _root_.YangMills.SharedProofs.p24342 <;> assumption
theorem eventually_nearIdentity {ι : Type*} [Finite ι] {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ V in 𝓝 (fun _ : ι => (1 : ComplexMatrix2)), ∀ b, ‖V b - 1‖ < δ :=
  (isOpen_nearIdentity δ).mem_nhds fun b => by simpa using hδ
theorem exists_radius_of_eventually {ι : Type*} [Finite ι] {D : Set (ι → ComplexMatrix2)}
    {P : (ι → ComplexMatrix2) → Prop} (h : EventuallyNearIdentity D P) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ V ∈ D, (∀ b, ‖V b - 1‖ < δ) → P V := by apply _root_.YangMills.SharedProofs.p388 <;> assumption
end NearIdentity
section TowerFacts
variable {L n k i : ℕ}
structure TowerData (L n k : ℕ) : Prop where
  pos : 0 < L
  xor_opposite : ∀ i ≤ k, ∀ b : Edge L n k i,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  admissible : ∀ i < k, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
    PolydiscIsAdmissible (polydiscRadius L) c
  mem_polydisc : ∀ i < k, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
    ∀ V ∈ smallComplexFields L n k i, V ∈ nearIdentityPolydisc (polydiscRadius L) c
  equivariance : ∀ i ≤ k, LeftChartFacts.GaugeEquivarianceForms L n k i
  expMul_mem : ∀ V ∈ fieldSpace L n k 0, ∀ B ∈ edgeFormSpace L n k 0, ∀ b : Edge L n k 0,
    b.IsPositivelyOriented →
    ComplexMatrix2.matExp (Complex.I • B b) * V b ∈ PeriodicLattice.compactGaugeGroup
  action_gaugeTransform : ∀ U ∈ fieldSpace L n k 0, ∀ u ∈ gaugeGroupAt L n k 0,
    plaquetteAction L n k (PeriodicLattice.gaugeTransform u U) = plaquetteAction L n k U
theorem opposite_opposite (b : Edge L n k i) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
theorem TowerData.opposite_pos (T : TowerData L n k) (hi : i ≤ k) {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases T.xor_opposite i hi b with h | h
  · exact absurd h.1 hb
  · exact h.1
theorem TowerData.not_opposite_pos (T : TowerData L n k) (hi : i ≤ k) {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by
  rcases T.xor_opposite i hi b with h | h
  · exact h.2
  · exact absurd hb h.2
theorem extendOddly_pos {g : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) : extendOddly g b = g b := if_pos hb
theorem extendOddly_neg {g : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) : extendOddly g b = -g b.opposite := if_neg hb
theorem extendOddly_congr (T : TowerData L n k) (hi : i ≤ k) {g g' : Edge L n k i → ComplexMatrix2}
    (h : ∀ b, b.IsPositivelyOriented → g b = g' b) : extendOddly g = extendOddly g' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_pos hb, extendOddly_pos hb, h b hb]
  · rw [extendOddly_neg hb, extendOddly_neg hb, h _ (T.opposite_pos hi hb)]
theorem adjointForm_pos (u : Vertex L n k i → ComplexMatrix2) (B : Edge L n k i → ComplexMatrix2)
    {b : Edge L n k i} (hb : b.IsPositivelyOriented) :
    adjointForm u B b = ComplexMatrix2.conjugateBy (u b.source) (B b) :=
  extendOddly_pos hb
theorem adjointForm_add (u : Vertex L n k i → ComplexMatrix2) (B B' : Edge L n k i → ComplexMatrix2) :
    adjointForm u (B + B') = adjointForm u B + adjointForm u B' := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.adjointForm_add <;> assumption
theorem smul_adjointForm (u : Vertex L n k i → ComplexMatrix2) (t : ℂ)
    (B : Edge L n k i → ComplexMatrix2) : t • adjointForm u B = adjointForm u (t • B) := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.smul_adjointForm <;> assumption
theorem mem_complexEdgeForms {B : Edge L n k i → ComplexMatrix2} (h : B ∈ edgeFormSpace L n k i) :
    B ∈ complexEdgeForms L n k i := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
theorem expTwist_pos {A V : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A V b = ComplexMatrix2.matExp (Complex.I • A b) * V b := if_pos hb
theorem expTwist_neg {A V : Edge L n k i → ComplexMatrix2} {b : Edge L n k i}
    (hb : ¬b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A V b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * V b.opposite)⁻¹ := if_neg hb
theorem expTwist_mem (T : TowerData L n k) {V B : Edge L n k 0 → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k 0) (hB : B ∈ edgeFormSpace L n k 0) :
    PeriodicLattice.expTwist B V ∈ fieldSpace L n k 0 := by
  have hz := Nat.zero_le k
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_pos hb]
      exact T.expMul_mem V hV B hB b hb
    · rw [expTwist_neg hb]
      exact inv_mem_compact (T.expMul_mem V hV B hB _ (T.opposite_pos hz hb))
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_neg (T.not_opposite_pos hz hb), expTwist_pos hb, opposite_opposite]
    · have hr := T.opposite_pos hz hb
      rw [expTwist_pos hr, expTwist_neg hb,
        Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (T.expMul_mem V hV B hB _ hr))]
variable {u : Vertex L n k i → ComplexMatrix2} {V : Edge L n k i → ComplexMatrix2}
theorem det_gauge (hu : u ∈ gaugeGroupAt L n k i) (x : Vertex L n k i) : (u x).det = 1 :=
  det_eq_one_of_mem (hu x)
theorem blockAverage_opposite {a : ℕ} (W : Edge L n k i → ComplexMatrix2) (T : TowerData L n k)
    (ha : a ≤ k) {c : Edge L n k a} (hc : ¬c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage W c =
      (PeriodicLattice.complexBlockAverage W c.opposite)⁻¹ := by
  have hr := T.opposite_pos ha hc
  simp only [PeriodicLattice.complexBlockAverage, if_neg hc, if_pos hr]
theorem blockAverageStep_gauge (T : TowerData L n k) (hi : i < k)
    (hV : V ∈ smallComplexFields L n k i) (hu : u ∈ gaugeGroupAt L n k i) :
    PeriodicLattice.complexBlockAverageStep i (PeriodicLattice.gaugeTransform u V) =
      PeriodicLattice.gaugeTransform (restrictVertexFunction (i + 1) u)
        (PeriodicLattice.complexBlockAverageStep i V) := by
  have hr : ∀ x, (restrictVertexFunction (i + 1) u x).det = 1 := fun x => det_eq_one_of_mem (hu _)
  have hpos : ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
      PeriodicLattice.complexBlockAverage (PeriodicLattice.gaugeTransform u V) c =
        PeriodicLattice.gaugeTransform (restrictVertexFunction (i + 1) u)
          (PeriodicLattice.complexBlockAverage V) c :=
    fun c hc => ((T.admissible i hi c hc).gauge_covariant V (T.mem_polydisc i hi c hc V hV) u hu).2.1
  funext c
  by_cases hc : c.IsPositivelyOriented
  · exact hpos c hc
  · have hp := T.opposite_pos (show i + 1 ≤ k from hi) hc
    show PeriodicLattice.complexBlockAverage (PeriodicLattice.gaugeTransform u V) c =
      restrictVertexFunction (i + 1) u c.source * PeriodicLattice.complexBlockAverage V c *
        (restrictVertexFunction (i + 1) u c.target)⁻¹
    rw [blockAverage_opposite _ T (show i + 1 ≤ k from hi) hc, hpos _ hp,
      blockAverage_opposite V T (show i + 1 ≤ k from hi) hc]
    exact twisted_inv (hr _)
end TowerFacts
section IteratedFields
variable {L n k : ℕ} {U : Edge L n k 0 → ComplexMatrix2} {u : Vertex L n k 0 → ComplexMatrix2}
theorem coe_toSublattice {a b : ℤ} (hL : 0 < L) (h : a ≤ b) (y : PeriodicLattice.Site L n a) :
    ((y.toSublattice b : PeriodicLattice.Site L n b) : PeriodicLattice.FourTorus L n) = y := by apply _root_.YangMills.Construction.SeparatedSequences.BlockAverages.coe_toSublattice <;> assumption
theorem restrictVertexFunction_zero (hL : 0 < L) (l : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction 0 l = l := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.restrictVertexFunction_zero <;> assumption
theorem restrictVertexFunction_succ (hL : 0 < L) (i : ℕ) (l : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction (i + 1) (restrictVertexFunction i l) =
      restrictVertexFunction (i + 1) l := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.restrictVertexFunction_succ <;> assumption
theorem restrictVertexFunction_mem (hu : u ∈ gaugeGroupAt L n k 0) (i : ℕ) :
    restrictVertexFunction i u ∈ gaugeGroupAt L n k i :=
  fun _ => hu _
theorem blockField_gauge (T : TowerData L n k) (hU : U ∈ smallIterateFields L n k)
    (hu : u ∈ gaugeGroupAt L n k 0) :
    ∀ i ≤ k, PeriodicLattice.complexBlockFieldAtLevel i (PeriodicLattice.gaugeTransform u U) =
      PeriodicLattice.gaugeTransform (restrictVertexFunction i u)
        (PeriodicLattice.complexBlockFieldAtLevel i U) := by
  intro i
  induction i with
  | zero =>
    intro _
    show PeriodicLattice.gaugeTransform u U =
      PeriodicLattice.gaugeTransform (restrictVertexFunction 0 u) U
    rw [restrictVertexFunction_zero T.pos]
  | succ i ih =>
    intro h
    have hi : i < k := h
    show PeriodicLattice.complexBlockAverageStep i
        (PeriodicLattice.complexBlockFieldAtLevel i (PeriodicLattice.gaugeTransform u U)) =
      PeriodicLattice.gaugeTransform (restrictVertexFunction (i + 1) u)
        (PeriodicLattice.complexBlockAverageStep i (PeriodicLattice.complexBlockFieldAtLevel i U))
    rw [ih hi.le, blockAverageStep_gauge T hi (hU.2 i hi) (restrictVertexFunction_mem hu i),
      restrictVertexFunction_succ T.pos]
theorem extendByZero_adjoint (hL : 0 < L) (g : Vertex L n k k → ComplexMatrix2) :
    _root_.YangMills.Construction.Tower.extendByZero (adjointVertexFn (restrictVertexFunction k u) g) =
      adjointVertexFn u (_root_.YangMills.Construction.Tower.extendByZero g) := by
  funext x
  unfold _root_.YangMills.Construction.Tower.extendByZero adjointVertexFn
  by_cases h : ∃ y : Vertex L n k k, (y : PeriodicLattice.FourTorus L n) = x
  · simp only [dif_pos h]
    have hle : PeriodicLattice.levelDepth k k ≤ PeriodicLattice.levelDepth k 0 := by
      simp [PeriodicLattice.levelDepth]
    have e : h.choose.toSublattice (PeriodicLattice.levelDepth k 0) = x :=
      Subtype.ext ((coe_toSublattice hL hle _).trans h.choose_spec)
    show ComplexMatrix2.conjugateBy (u (h.choose.toSublattice (PeriodicLattice.levelDepth k 0))) _ = _
    rw [e]
  · simp only [dif_neg h, conjugateBy_zero]
end IteratedFields
section TracePairings
variable {L n k i : ℕ}
theorem pairing_conjugateBy {ι : Type*} {v : ι → ComplexMatrix2} (hv : ∀ x, (v x).det = 1)
    (f g : ι → ComplexMatrix2) :
    traceFinsumPairing (fun x => ComplexMatrix2.conjugateBy (v x) (f x))
        (fun x => ComplexMatrix2.conjugateBy (v x) (g x)) = traceFinsumPairing f g :=
  finsum_congr fun x => halfTrace_conjugateBy (hv x) _ _
theorem restrictPositive_adjointForm (u : Vertex L n k i → ComplexMatrix2)
    (f : Edge L n k i → ComplexMatrix2) :
    restrictToPositiveEdges (adjointForm u f) =
      fun b : PositiveEdge L n k i =>
        ComplexMatrix2.conjugateBy (u b.1.source) (restrictToPositiveEdges f b) :=
  funext fun b => adjointForm_pos _ _ b.2
theorem edgeFormPairing_adjointForm {u : Vertex L n k i → ComplexMatrix2} (hd : ∀ x, (u x).det = 1)
    (f g : Edge L n k i → ComplexMatrix2) :
    edgeFormPairing (adjointForm u f) (adjointForm u g) = edgeFormPairing f g := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.edgeFormPairing_adjointForm <;> assumption
theorem edgeFormNorm_adjointForm {u : Vertex L n k i → ComplexMatrix2} (hd : ∀ x, (u x).det = 1)
    (f : Edge L n k i → ComplexMatrix2) : edgeFormNorm (adjointForm u f) = edgeFormNorm f := by
  show Real.sqrt (edgeFormPairing _ _).re = Real.sqrt (edgeFormPairing _ _).re
  rw [edgeFormPairing_adjointForm hd]
theorem pairing_adjointVertexFn {u : Vertex L n k i → ComplexMatrix2} (hd : ∀ x, (u x).det = 1)
    (f g : Vertex L n k i → ComplexMatrix2) :
    traceFinsumPairing (adjointVertexFn u f) (adjointVertexFn u g) = traceFinsumPairing f g :=
  pairing_conjugateBy hd f g
theorem norm_adjointVertexFn {u : Vertex L n k i → ComplexMatrix2} (hd : ∀ x, (u x).det = 1)
    (f : Vertex L n k i → ComplexMatrix2) :
    traceFinsumNorm (adjointVertexFn u f) = traceFinsumNorm f := by
  unfold traceFinsumNorm
  rw [pairing_adjointVertexFn hd]
theorem bracketTerm_gauge (T : TowerData L n k) {u : Vertex L n k 0 → ComplexMatrix2}
    (hd : ∀ x, (u x).det = 1) (U : Edge L n k 0 → ComplexMatrix2)
    (l : Vertex L n k 0 → ComplexMatrix2) (B : Edge L n k 0 → ComplexMatrix2) :
    bracketTerm (PeriodicLattice.gaugeTransform u U) (adjointVertexFn u l) (adjointForm u B) =
      adjointForm u (bracketTerm U l B) := by
  show extendOddly _ = extendOddly _
  refine extendOddly_congr T (Nat.zero_le k) fun b hb => ?_
  rw [adjointForm_pos _ _ hb]
  have e : bracketTerm U l B b =
      (Complex.I / 2) • ⁅l b.source + ComplexMatrix2.conjugateBy (U b) (l b.target), B b⁆ :=
    extendOddly_pos hb
  rw [e, conjugateBy_smul, conjugateBy_lie (hd _), conjugateBy_add]
  show (Complex.I / 2) • ⁅ComplexMatrix2.conjugateBy (u b.source) (l b.source) +
      ComplexMatrix2.conjugateBy (u b.source * U b * (u b.target)⁻¹)
        (ComplexMatrix2.conjugateBy (u b.target) (l b.target)),
      ComplexMatrix2.conjugateBy (u b.source) (B b)⁆ = _
  rw [conjugateBy_twisted _ _ (hd _)]
end TracePairings
section RegularFields
open RealQuadraticTransposes
variable {L n k : ℕ}
structure IsRegularField (U : Edge L n k 0 → ComplexMatrix2) : Prop where
  mem_fields : U ∈ fieldSpace L n k 0
  mem_small : U ∈ smallIterateFields L n k
  covDiffLinear_apply : ∀ l : vertexFunctionSpace L n k 0,
    (covDiffLinear L n k U l : Edge L n k 0 → ComplexMatrix2) =
      covDiff U (l : Vertex L n k 0 → ComplexMatrix2)
  iterAverageLinear_apply : ∀ l : vertexFunctionSpace L n k 0,
    (iterAverageLinear L n k U l : Vertex L n k k → ComplexMatrix2) =
      iterAdjointCubeAverage L n k U k (l : Vertex L n k 0 → ComplexMatrix2)
  iterCovDerivLinear_apply : ∀ B : edgeFormSpace L n k 0,
    (iterCovariantDerivLinear L n k U B : Edge L n k k → ComplexMatrix2) =
      iterCovariantDeriv L n k U k (B : Edge L n k 0 → ComplexMatrix2)
  covDiff_adjoint : ∀ (g : edgeFormSpace L n k 0) (f : vertexFunctionSpace L n k 0),
    traceFinsumPairing (covDiffRealTranspose L n k U g : Vertex L n k 0 → ComplexMatrix2)
        (f : Vertex L n k 0 → ComplexMatrix2) =
      edgeFormPairing (g : Edge L n k 0 → ComplexMatrix2)
        (covDiffLinear L n k U f : Edge L n k 0 → ComplexMatrix2)
  iterAverage_adjoint : ∀ (g : vertexFunctionSpace L n k k) (f : vertexFunctionSpace L n k 0),
    traceFinsumPairing (iterAverageRealTranspose L n k U g : Vertex L n k 0 → ComplexMatrix2)
        (f : Vertex L n k 0 → ComplexMatrix2) =
      traceFinsumPairing (g : Vertex L n k k → ComplexMatrix2)
        (iterAverageLinear L n k U f : Vertex L n k k → ComplexMatrix2)
  hessian : BackgroundOperatorProperties U
  logRatio : IterLogRatioAnalytic U
  quadratic : IterHasUniqueQuadraticExpansion U
theorem IsRegularField.gaugeParameter_mem {U : Edge L n k 0 → ComplexMatrix2}
    (hU : IsRegularField U) (B : edgeFormSpace L n k 0) :
    backgroundGaugeParameter U (B : Edge L n k 0 → ComplexMatrix2) ∈ vertexFunctionSpace L n k 0 := by
  obtain ⟨σ, hσ⟩ := hU.hessian.gaugeParameter_linear
  rw [← (hσ B).2]
  exact (σ B).2
structure GaugeConjugation (L n k : ℕ) (U : Edge L n k 0 → ComplexMatrix2)
    (u : Vertex L n k 0 → ComplexMatrix2) where
  A : edgeFormSpace L n k 0 ≃ₗ[ℝ] edgeFormSpace L n k 0
  S : vertexFunctionSpace L n k 0 ≃ₗ[ℝ] vertexFunctionSpace L n k 0
  Ak : edgeFormSpace L n k k ≃ₗ[ℝ] edgeFormSpace L n k k
  Sk : vertexFunctionSpace L n k k ≃ₗ[ℝ] vertexFunctionSpace L n k k
  A_apply : ∀ B : edgeFormSpace L n k 0, (A B : Edge L n k 0 → ComplexMatrix2) = adjointForm u B
  S_apply : ∀ l : vertexFunctionSpace L n k 0,
    (S l : Vertex L n k 0 → ComplexMatrix2) = adjointVertexFn u l
  Ak_apply : ∀ B : edgeFormSpace L n k k,
    (Ak B : Edge L n k k → ComplexMatrix2) = adjointForm (restrictVertexFunction k u) B
  Sk_apply : ∀ l : vertexFunctionSpace L n k k,
    (Sk l : Vertex L n k k → ComplexMatrix2) = adjointVertexFn (restrictVertexFunction k u) l
  mem_gauge : u ∈ gaugeGroupAt L n k 0
  towerData : TowerData L n k
  expTwist_eq : ∀ B ∈ complexEdgeForms L n k 0,
    PeriodicLattice.expTwist (adjointForm u B) (PeriodicLattice.gaugeTransform u U) =
      PeriodicLattice.gaugeTransform u (PeriodicLattice.expTwist B U)
  covDiff_eq : ∀ l ∈ vertexFunctionSpace L n k 0,
    covDiff (PeriodicLattice.gaugeTransform u U) (adjointVertexFn u l) =
      adjointForm u (covDiff U l)
  average_eq : ∀ l ∈ vertexFunctionSpace L n k 0,
    iterAdjointCubeAverage L n k (PeriodicLattice.gaugeTransform u U) k (adjointVertexFn u l) =
      adjointVertexFn (restrictVertexFunction k u) (iterAdjointCubeAverage L n k U k l)
  complexDeriv_eq : ∀ B ∈ edgeFormSpace L n k 0,
    complexIterDeriv L n k k (PeriodicLattice.gaugeTransform u U) (adjointForm u B) =
      adjointForm (restrictVertexFunction k u) (complexIterDeriv L n k k U B)
  covDeriv_eq : ∀ B ∈ edgeFormSpace L n k 0,
    iterCovariantDeriv L n k (PeriodicLattice.gaugeTransform u U) k (adjointForm u B) =
      adjointForm (restrictVertexFunction k u) (iterCovariantDeriv L n k U k B)
  drift_eq : ∀ B ∈ edgeFormSpace L n k 0,
    iterContourLogDrift L n k (PeriodicLattice.gaugeTransform u U) k (adjointForm u B) =
      adjointVertexFn (restrictVertexFunction k u) (iterContourLogDrift L n k U k B)
namespace GaugeConjugation
variable {U : Edge L n k 0 → ComplexMatrix2} {u : Vertex L n k 0 → ComplexMatrix2}
  (P : GaugeConjugation L n k U u)
include P
theorem det_one (x : Vertex L n k 0) : (u x).det = 1 := det_gauge P.mem_gauge x
theorem det_one_top (x : Vertex L n k k) : (restrictVertexFunction k u x).det = 1 :=
  det_gauge (restrictVertexFunction_mem P.mem_gauge k) x
theorem inner_A {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k 0)} (hc : IsEdgePairingCore c)
    (x y : edgeFormSpace L n k 0) : c.inner (P.A x) (P.A y) = c.inner x y := by
  rw [hc, hc, P.A_apply, P.A_apply, edgeFormPairing_adjointForm P.det_one]
theorem inner_Ak {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k k)} (hc : IsEdgePairingCore c)
    (x y : edgeFormSpace L n k k) : c.inner (P.Ak x) (P.Ak y) = c.inner x y := by
  rw [hc, hc, P.Ak_apply, P.Ak_apply, edgeFormPairing_adjointForm P.det_one_top]
theorem inner_S {c : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)}
    (hc : IsVertexPairingCore c) (x y : vertexFunctionSpace L n k 0) :
    c.inner (P.S x) (P.S y) = c.inner x y := by
  rw [hc, hc, P.S_apply, P.S_apply, pairing_adjointVertexFn P.det_one]
theorem inner_Sk {c : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k k)}
    (hc : IsVertexPairingCore c) (x y : vertexFunctionSpace L n k k) :
    c.inner (P.Sk x) (P.Sk y) = c.inner x y := by
  rw [hc, hc, P.Sk_apply, P.Sk_apply, pairing_adjointVertexFn P.det_one_top]
variable (hU : IsRegularField U) (hU' : IsRegularField (PeriodicLattice.gaugeTransform u U))
include hU hU'
theorem covDiffLinear_conj (l : vertexFunctionSpace L n k 0) :
    covDiffLinear L n k (PeriodicLattice.gaugeTransform u U) (P.S l) =
      P.A (covDiffLinear L n k U l) :=
  Subtype.ext (by
    rw [hU'.covDiffLinear_apply, P.S_apply, P.covDiff_eq _ l.2, P.A_apply,
      hU.covDiffLinear_apply])
theorem iterAverageLinear_conj (l : vertexFunctionSpace L n k 0) :
    iterAverageLinear L n k (PeriodicLattice.gaugeTransform u U) (P.S l) =
      P.Sk (iterAverageLinear L n k U l) :=
  Subtype.ext (by
    rw [hU'.iterAverageLinear_apply, P.S_apply, P.average_eq _ l.2, P.Sk_apply,
      hU.iterAverageLinear_apply])
theorem iterCovariantDerivLinear_conj (B : edgeFormSpace L n k 0) :
    iterCovariantDerivLinear L n k (PeriodicLattice.gaugeTransform u U) (P.A B) =
      P.Ak (iterCovariantDerivLinear L n k U B) :=
  Subtype.ext (by
    rw [hU'.iterCovDerivLinear_apply, P.A_apply, P.covDeriv_eq _ B.2, P.Ak_apply,
      hU.iterCovDerivLinear_apply])
theorem covDiffTranspose_conj {cF : InnerProductSpace.Core ℝ (edgeFormSpace L n k 0)}
    {cS : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)} (hF : IsEdgePairingCore cF)
    (hS : IsVertexPairingCore cS) (g : edgeFormSpace L n k 0) :
    covDiffRealTranspose L n k (PeriodicLattice.gaugeTransform u U) (P.A g) =
      P.S (covDiffRealTranspose L n k U g) :=
  adjoint_intertwine cS cF P.S P.A (P.inner_A hF) (P.inner_S hS) (P.covDiffLinear_conj hU hU')
    (fun y x => by rw [hS, hF]; exact congrArg Complex.re (hU.covDiff_adjoint y x))
    (fun y x => by rw [hS, hF]; exact congrArg Complex.re (hU'.covDiff_adjoint y x)) g
theorem iterAverageTranspose_conj {cS : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)}
    {cK : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k k)} (hS : IsVertexPairingCore cS)
    (hK : IsVertexPairingCore cK) (g : vertexFunctionSpace L n k k) :
    iterAverageRealTranspose L n k (PeriodicLattice.gaugeTransform u U) (P.Sk g) =
      P.S (iterAverageRealTranspose L n k U g) :=
  adjoint_intertwine cS cK P.S P.Sk (P.inner_Sk hK) (P.inner_S hS) (P.iterAverageLinear_conj hU hU')
    (fun y x => by rw [hS, hK]; exact congrArg Complex.re (hU.iterAverage_adjoint y x))
    (fun y x => by rw [hS, hK]; exact congrArg Complex.re (hU'.iterAverage_adjoint y x)) g
omit hU hU' in
theorem gaugeParameter_conj (B : edgeFormSpace L n k 0) :
    backgroundGaugeParameter (PeriodicLattice.gaugeTransform u U)
        (P.A B : Edge L n k 0 → ComplexMatrix2) =
      adjointVertexFn u (backgroundGaugeParameter U (B : Edge L n k 0 → ComplexMatrix2)) := by
  unfold backgroundGaugeParameter
  rw [P.A_apply, P.drift_eq _ B.2, extendByZero_adjoint P.towerData.pos]
theorem backgroundShift_conj (B : edgeFormSpace L n k 0) :
    backgroundShift L n k (PeriodicLattice.gaugeTransform u U) (P.A B) =
      P.A (backgroundShift L n k U B) :=
  Subtype.ext (by
    rw [hU'.hessian.backgroundShift_apply, P.gaugeParameter_conj,
      P.covDiff_eq _ (hU.gaugeParameter_mem B), P.A_apply, P.A_apply,
      hU.hessian.backgroundShift_apply, adjointForm_add])
theorem gaugeFixingTerm_conj {cF : InnerProductSpace.Core ℝ (edgeFormSpace L n k 0)}
    {cS : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)}
    {cK : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k k)} (hF : IsEdgePairingCore cF)
    (hS : IsVertexPairingCore cS) (hK : IsVertexPairingCore cK) (B : edgeFormSpace L n k 0) :
    gaugeSliceResidual (PeriodicLattice.gaugeTransform u U) (P.A B) =
      P.S (gaugeSliceResidual U B) := by
  unfold gaugeSliceResidual
  rw [P.covDiffTranspose_conj hU hU' hF hS, P.iterAverageLinear_conj hU hU',
    P.iterAverageTranspose_conj hU hU' hS hK, map_sub, map_smul]
omit hU hU' in
theorem iterLogRatio_conj (hUs : U ∈ smallIterateFields L n k) {B : edgeFormSpace L n k 0}
    (hB : PeriodicLattice.expTwist (B : Edge L n k 0 → ComplexMatrix2) U ∈ smallIterateFields L n k)
    (c : PositiveEdge L n k k) :
    iterLogRatio (PeriodicLattice.gaugeTransform u U) c (P.A B : Edge L n k 0 → ComplexMatrix2) =
      ComplexMatrix2.conjugateBy (restrictVertexFunction k u c.1.source)
        (iterLogRatio U c (B : Edge L n k 0 → ComplexMatrix2)) := by
  unfold iterLogRatio
  rw [P.A_apply, P.expTwist_eq _ (mem_complexEdgeForms B.2),
    blockField_gauge P.towerData hB P.mem_gauge k le_rfl,
    blockField_gauge P.towerData hUs P.mem_gauge k le_rfl]
  show Complex.I⁻¹ • ComplexMatrix2.logSeries
      ((restrictVertexFunction k u c.1.source * _ * (restrictVertexFunction k u c.1.target)⁻¹) *
        (restrictVertexFunction k u c.1.source * _ *
          (restrictVertexFunction k u c.1.target)⁻¹)⁻¹) = _
  rw [twisted_mul_inv (P.det_one_top _), logSeries_conj (P.det_one_top _), conjugateBy_smul]
omit P hU hU' in
def conjOnEdges (v : Vertex L n k k → ComplexMatrix2) :
    (PositiveEdge L n k k → ComplexMatrix2) →ₗ[ℝ] PositiveEdge L n k k → ComplexMatrix2 where
  toFun p c := ComplexMatrix2.conjugateBy (v c.1.source) (p c)
  map_add' _ _ := funext fun _ => conjugateBy_add _ _ _
  map_smul' _ _ := funext fun _ => conjugateBy_real_smul _ _ _
omit hU hU' in
def conjTerm (q : IterBilinearForm L n k) : IterBilinearForm L n k :=
  (q.compl₁₂ (P.A.symm : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0)
    (P.A.symm : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0)).compr₂
      (conjOnEdges (restrictVertexFunction k u))
omit hU hU' in
theorem conjTerm_apply (q : IterBilinearForm L n k) (B B' : edgeFormSpace L n k 0)
    (c : PositiveEdge L n k k) :
    P.conjTerm q (P.A B) (P.A B') c =
      ComplexMatrix2.conjugateBy (restrictVertexFunction k u c.1.source) (q B B' c) := by
  simp [conjTerm, conjOnEdges]
omit hU' in
theorem conjTerm_isExpansion [FiniteDimensional ℝ (edgeFormSpace L n k 0)] :
    IsIterQuadraticExpansion (PeriodicLattice.gaugeTransform u U)
      (P.conjTerm (iterQuadraticTerm U)) := by
  obtain ⟨hsym, hexp⟩ := hU.quadratic.2.1
  refine ⟨fun B B' => ?_, fun c => ?_⟩
  · obtain ⟨B, rfl⟩ := P.A.surjective B
    obtain ⟨B', rfl⟩ := P.A.surjective B'
    funext c
    rw [P.conjTerm_apply, P.conjTerm_apply, hsym]
  · obtain ⟨C, hC⟩ := hexp c
    refine ⟨C, ?_⟩
    have hcont : Continuous (P.A.symm : edgeFormSpace L n k 0 → edgeFormSpace L n k 0) :=
      LinearMap.continuous_of_finiteDimensional
        (P.A.symm : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0)
    have ht : Tendsto (P.A.symm : edgeFormSpace L n k 0 → edgeFormSpace L n k 0) (𝓝 0) (𝓝 0) := by
      have := hcont.tendsto 0
      rwa [map_zero] at this
    have hf := hU.logRatio.2.2.1
    filter_upwards [ht.eventually hC, ht.eventually hf] with B h₁ h₂
    obtain ⟨B, rfl⟩ := P.A.surjective B
    simp only [LinearEquiv.symm_apply_apply] at h₁ h₂
    have hc : (c : Edge L n k k).IsPositivelyOriented := c.2
    have e₁ := P.iterLogRatio_conj hU.mem_small h₂.1 c
    have e₂ : complexIterDeriv L n k k (PeriodicLattice.gaugeTransform u U)
        (P.A B : Edge L n k 0 → ComplexMatrix2) c =
        ComplexMatrix2.conjugateBy (restrictVertexFunction k u c.1.source)
          (complexIterDeriv L n k k U (B : Edge L n k 0 → ComplexMatrix2) c) := by
      rw [P.A_apply, P.complexDeriv_eq _ B.2, adjointForm_pos _ _ hc]
    rw [e₁, e₂, P.conjTerm_apply, ← conjugateBy_sub, ← conjugateBy_real_smul, ← conjugateBy_sub]
    show ‖ComplexMatrix2.conjugateBy _ _‖ ≤ _
    rw [norm_conjugateBy (restrictVertexFunction_mem P.mem_gauge k _), P.A_apply,
      edgeFormNorm_adjointForm P.det_one]
    exact h₁
theorem iterQuadraticTerm_conj [FiniteDimensional ℝ (edgeFormSpace L n k 0)]
    (B B' : edgeFormSpace L n k 0) (c : PositiveEdge L n k k) :
    iterQuadraticTerm (PeriodicLattice.gaugeTransform u U) (P.A B) (P.A B') c =
      ComplexMatrix2.conjugateBy (restrictVertexFunction k u c.1.source)
        (iterQuadraticTerm U B B' c) := by
  have e := hU'.quadratic.1.unique hU'.quadratic.2.1 (P.conjTerm_isExpansion hU)
  rw [e, P.conjTerm_apply]
omit hU' in
theorem leftSecondDeriv_conj (B B' : edgeFormSpace L n k 0) :
    leftSecondDeriv (plaquetteAction L n k) (PeriodicLattice.gaugeTransform u U)
        (P.A B : Edge L n k 0 → ComplexMatrix2) (P.A B' : Edge L n k 0 → ComplexMatrix2) =
      leftSecondDeriv (plaquetteAction L n k) U (B : Edge L n k 0 → ComplexMatrix2)
        (B' : Edge L n k 0 → ComplexMatrix2) := by
  have key : ∀ s t : ℝ, plaquetteAction L n k (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ s • (P.A B : Edge L n k 0 → ComplexMatrix2) +
          algebraMap ℝ ℂ t • (P.A B' : Edge L n k 0 → ComplexMatrix2))
        (PeriodicLattice.gaugeTransform u U)) =
      plaquetteAction L n k (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ s • (B : Edge L n k 0 → ComplexMatrix2) +
          algebraMap ℝ ℂ t • (B' : Edge L n k 0 → ComplexMatrix2)) U) := by
    intro s t
    have hX : algebraMap ℝ ℂ s • (B : Edge L n k 0 → ComplexMatrix2) +
        algebraMap ℝ ℂ t • (B' : Edge L n k 0 → ComplexMatrix2) ∈ edgeFormSpace L n k 0 := by
      rw [algebraMap_smul, algebraMap_smul]
      exact (edgeFormSpace L n k 0).add_mem ((edgeFormSpace L n k 0).smul_mem s B.2)
        ((edgeFormSpace L n k 0).smul_mem t B'.2)
    rw [P.A_apply, P.A_apply, smul_adjointForm, smul_adjointForm, ← adjointForm_add,
      P.expTwist_eq _ (mem_complexEdgeForms hX),
      P.towerData.action_gaugeTransform _ (expTwist_mem P.towerData hU.mem_fields hX) _
        P.mem_gauge]
  simp only [leftSecondDeriv, mixedDirectionalDeriv, key]
theorem sourceQuadraticForm_conj [FiniteDimensional ℝ (edgeFormSpace L n k 0)]
    {J J' : edgeFormSpace L n k 0} {μ μ' : edgeFormSpace L n k k}
    (hJ : (J' : Edge L n k 0 → ComplexMatrix2) = adjointForm u J)
    (hμ : (μ' : Edge L n k k → ComplexMatrix2) = adjointForm (restrictVertexFunction k u) μ)
    (B : edgeFormSpace L n k 0) :
    sourceQuadraticForm (PeriodicLattice.gaugeTransform u U) J' μ' (P.A B) =
      sourceQuadraticForm U J μ B := by
  have h₃ : traceFinsumPairing (restrictToPositiveEdges (μ' : Edge L n k k → ComplexMatrix2))
      (iterQuadraticTerm (PeriodicLattice.gaugeTransform u U)
        (backgroundShift L n k (PeriodicLattice.gaugeTransform u U) (P.A B))
        (backgroundShift L n k (PeriodicLattice.gaugeTransform u U) (P.A B))) =
      traceFinsumPairing (restrictToPositiveEdges (μ : Edge L n k k → ComplexMatrix2))
        (iterQuadraticTerm U (backgroundShift L n k U B) (backgroundShift L n k U B)) := by
    rw [P.backgroundShift_conj hU hU', hμ, restrictPositive_adjointForm]
    have e : iterQuadraticTerm (PeriodicLattice.gaugeTransform u U)
        (P.A (backgroundShift L n k U B)) (P.A (backgroundShift L n k U B)) =
        fun c : PositiveEdge L n k k =>
          ComplexMatrix2.conjugateBy (restrictVertexFunction k u c.1.source)
            (iterQuadraticTerm U (backgroundShift L n k U B) (backgroundShift L n k U B) c) :=
      funext fun c => P.iterQuadraticTerm_conj hU hU' _ _ c
    rw [e]
    exact pairing_conjugateBy (fun c => P.det_one_top _) _ _
  have hσ := P.gaugeParameter_conj B
  unfold sourceQuadraticForm
  rw [h₃, hσ, P.covDiff_eq _ (hU.gaugeParameter_mem B), P.A_apply, hJ,
    bracketTerm_gauge P.towerData P.det_one, bracketTerm_gauge P.towerData P.det_one,
    edgeFormPairing_adjointForm P.det_one, edgeFormPairing_adjointForm P.det_one]
theorem backgroundHessianForm_conj [FiniteDimensional ℝ (edgeFormSpace L n k 0)]
    {cF : InnerProductSpace.Core ℝ (edgeFormSpace L n k 0)}
    {cS : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)}
    {cK : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k k)} (hF : IsEdgePairingCore cF)
    (hS : IsVertexPairingCore cS) (hK : IsVertexPairingCore cK) {J J' : edgeFormSpace L n k 0}
    {μ μ' : edgeFormSpace L n k k} (hJ : (J' : Edge L n k 0 → ComplexMatrix2) = adjointForm u J)
    (hμ : (μ' : Edge L n k k → ComplexMatrix2) = adjointForm (restrictVertexFunction k u) μ)
    (B : edgeFormSpace L n k 0) :
    backgroundHessianForm (PeriodicLattice.gaugeTransform u U) J' μ' (P.A B) =
      backgroundHessianForm U J μ B := by
  unfold backgroundHessianForm
  rw [P.leftSecondDeriv_conj hU, P.sourceQuadraticForm_conj hU hU' hJ hμ,
    P.gaugeFixingTerm_conj hU hU' hF hS hK, P.S_apply, norm_adjointVertexFn P.det_one]
theorem backgroundHessian_conj [FiniteDimensional ℝ (edgeFormSpace L n k 0)]
    {cF : InnerProductSpace.Core ℝ (edgeFormSpace L n k 0)}
    {cS : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k 0)}
    {cK : InnerProductSpace.Core ℝ (vertexFunctionSpace L n k k)} (hF : IsEdgePairingCore cF)
    (hS : IsVertexPairingCore cS) (hK : IsVertexPairingCore cK) {J J' : edgeFormSpace L n k 0}
    {μ μ' : edgeFormSpace L n k k} (hJ : (J' : Edge L n k 0 → ComplexMatrix2) = adjointForm u J)
    (hμ : (μ' : Edge L n k k → ComplexMatrix2) = adjointForm (restrictVertexFunction k u) μ)
    (B : edgeFormSpace L n k 0) :
    backgroundHessian (PeriodicLattice.gaugeTransform u U) J' μ' (P.A B) =
      P.A (backgroundHessian U J μ B) := by
  have hX : IsBackgroundHessian U J μ (backgroundHessian U J μ) :=
    Classical.epsilon_spec (hU.hessian.existsUnique_hessian J μ).exists
  have hX' : IsBackgroundHessian (PeriodicLattice.gaugeTransform u U) J' μ'
      (backgroundHessian (PeriodicLattice.gaugeTransform u U) J' μ') :=
    Classical.epsilon_spec (hU'.hessian.existsUnique_hessian J' μ').exists
  let Y : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0 :=
    (P.A : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0) ∘ₗ backgroundHessian U J μ ∘ₗ
      (P.A.symm : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0)
  have hY : ∀ B, Y (P.A B) = P.A (backgroundHessian U J μ B) := fun B => by
    simp [Y]
  have hYop : IsBackgroundHessian (PeriodicLattice.gaugeTransform u U) J' μ' Y := by
    refine ⟨fun B B' => ?_, fun B => ?_⟩
    · obtain ⟨B, rfl⟩ := P.A.surjective B
      obtain ⟨B', rfl⟩ := P.A.surjective B'
      rw [hY, hY, P.A_apply, P.A_apply, P.A_apply, P.A_apply, edgeFormPairing_adjointForm P.det_one,
        edgeFormPairing_adjointForm P.det_one]
      exact hX.1 B B'
    · obtain ⟨B, rfl⟩ := P.A.surjective B
      rw [hY, P.A_apply, P.A_apply, edgeFormPairing_adjointForm P.det_one, hX.2 B,
        P.backgroundHessianForm_conj hU hU' hF hS hK hJ hμ]
  have e := (hU'.hessian.existsUnique_hessian J' μ').unique hX' hYop
  rw [e, hY]
theorem hessianSaddleDet_eq (hFF : EdgeFormsEuclidean L n k 0 ∧ EdgeFormsEuclidean L n k k)
    (hSS : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k)
    {J J' : edgeFormSpace L n k 0} {μ μ' : edgeFormSpace L n k k}
    (hJ : (J' : Edge L n k 0 → ComplexMatrix2) = adjointForm u J)
    (hμ : (μ' : Edge L n k k → ComplexMatrix2) = adjointForm (restrictVertexFunction k u) μ) :
    hessianSaddleDet (PeriodicLattice.gaugeTransform u U) J' μ' = hessianSaddleDet U J μ := by
  unfold hessianSaddleDet saddleDetOnEdgeForms
  rw [dif_pos hFF, dif_pos hFF]
  have := hFF.1.1
  have := hFF.2.1
  exact saddleDetOfCores_conj_eq _ _ P.A P.Ak (P.inner_A hFF.1.2.choose_spec)
    (P.inner_Ak hFF.2.2.choose_spec)
    (P.backgroundHessian_conj hU hU' hFF.1.2.choose_spec hSS.1.2.choose_spec
      hSS.2.2.choose_spec hJ hμ)
    (P.iterCovariantDerivLinear_conj hU hU')
theorem ghostSaddleDet_eq (hFF : EdgeFormsEuclidean L n k 0 ∧ EdgeFormsEuclidean L n k k)
    (hSS : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k) :
    ghostSaddleDet L n k (PeriodicLattice.gaugeTransform u U) = ghostSaddleDet L n k U := by
  unfold ghostSaddleDet saddleDetOnVertexFunctions
  rw [dif_pos hSS, dif_pos hSS]
  have := hSS.1.1
  have := hSS.2.1
  refine saddleDetOfCores_conj_eq _ _ P.S P.Sk (P.inner_S hSS.1.2.choose_spec)
    (P.inner_Sk hSS.2.2.choose_spec) (fun x => ?_) (P.iterAverageLinear_conj hU hU')
  rw [LinearMap.comp_apply, LinearMap.comp_apply, P.covDiffLinear_conj hU hU',
    P.covDiffTranspose_conj hU hU' hFF.1.2.choose_spec hSS.1.2.choose_spec]
theorem functional_invariant (hFF : EdgeFormsEuclidean L n k 0 ∧ EdgeFormsEuclidean L n k k)
    (hSS : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k) :
    BackgroundFunctionalGaugeInvariant u U := by
  intro J μ hform
  have hJ := P.A_apply J
  have hμ := P.Ak_apply μ
  have e₁ := P.hessianSaddleDet_eq hU hU' hFF hSS hJ hμ
  have e₂ := P.ghostSaddleDet_eq hU hU' hFF hSS
  refine ⟨P.A J, P.Ak μ, hJ, hμ, ?_, ?_⟩
  · unfold BackgroundFunctionalWellDefined
    rw [e₁, e₂]
    exact hform
  · unfold backgroundFunctional
    rw [e₁, e₂]
end GaugeConjugation
end RegularFields
section Assembly
open RealQuadraticTransposes
variable {L n k j : ℕ}
theorem linearMapWithValues_apply {α β : Type*} {p : Submodule ℝ (α → ComplexMatrix2)}
    {p' : Submodule ℝ (β → ComplexMatrix2)} {f : (α → ComplexMatrix2) → β → ComplexMatrix2}
    (h : ∃ T : p →ₗ[ℝ] p', ∀ x : p, (T x : β → ComplexMatrix2) = f x) (x : p) :
    (linearMapWithValues p p' f x : β → ComplexMatrix2) = f x := by apply _root_.YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide.linearMapWithValues_apply <;> assumption
theorem finite_vertex (hP : FaceSums.FacesAndPairings)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Finite (Vertex L n k j) :=
  Set.finite_univ_iff.mp (((hP L hL k j hj).1 n hn).2.1 Set.univ).2.1
theorem vertexFunctionsEuclidean_of (hP : FaceSums.FacesAndPairings)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    VertexFunctionsEuclidean L n k j := by apply _root_.YangMills.Construction.Tower.TrivialFieldGauge.vertexFunctionsEuclidean_of <;> assumption
theorem edgeFormsEuclidean_of (hS : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    EdgeFormsEuclidean L n k j := by apply _root_.YangMills.Construction.Tower.TrivialFieldGauge.edgeFormsEuclidean_of <;> assumption
theorem gaugeTransform_mem_fieldSpace {u : Vertex L n k j → ComplexMatrix2}
    {U : Edge L n k j → ComplexMatrix2} (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup)
    (hU : U ∈ fieldSpace L n k j) :
    PeriodicLattice.gaugeTransform u U ∈ fieldSpace L n k j := by apply _root_.YangMills.SharedProofs.p8548 <;> assumption
theorem eventually_isRegularField (hQ : RealQuadraticTransposes.Statement)
    (hE : IterLeftChartExpansion) (hY : RealLinearMaps.RealLinearMapsStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    EventuallyNearIdentity (fieldSpace L n k 0) (IsRegularField (L := L) (n := n) (k := k)) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hDT, hnear⟩ := hQ L n (i + 1) hL hn hk
  obtain ⟨hAt, hTower⟩ := hY L n (i + 1) hL hn hk
  have hAi := hAt i (by omega)
  show ∀ᶠ V in 𝓝[fieldSpace L n (i + 1) 0] (fun _ => (1 : ComplexMatrix2)), IsRegularField V
  filter_upwards [self_mem_nhdsWithin, hnear, hE L n (i + 1) hL hn hk,
    hAi.iterAdjointCubeAverage_isLinear, hAi.iterCovariantDeriv_isLinear]
    with U hc hR hX hav hdi
  obtain ⟨-, hTr, hOp⟩ := hR
  obtain ⟨hF, -, hS⟩ := hX
  obtain ⟨T, -, hK⟩ := hDT 0 (Nat.zero_le _) U hc
  obtain ⟨T', -, hK'⟩ := hTr.average_transpose
  exact
    { mem_fields := hc
      mem_small := hF.1
      covDiffLinear_apply := fun l =>
        linearMapWithValues_apply (hTower.covDiff_isLinear 0 (Nat.zero_le _) U hc) l
      iterAverageLinear_apply := fun l => linearMapWithValues_apply hav l
      iterCovDerivLinear_apply := fun B => linearMapWithValues_apply hdi B
      covDiff_adjoint := fun g f => hK.2.2 g f
      iterAverage_adjoint := fun g f => hK'.2.2 g f
      hessian := hOp
      logRatio := hF
      quadratic := hS }
theorem nonempty_gaugeConjugation (T : TowerData L n k) (hGC : AveragesGaugeCovariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {U : Edge L n k 0 → ComplexMatrix2}
    {u : Vertex L n k 0 → ComplexMatrix2} (hu : u ∈ gaugeGroupAt L n k 0) (hU : IsRegularField U)
    (hU' : IsRegularField (PeriodicLattice.gaugeTransform u U)) :
    Nonempty (GaugeConjugation L n k U u) := by
  have hc0 : PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup u :=
    fun x => det_gauge hu x
  have hck : PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup
      (restrictVertexFunction k u) :=
    fun x => det_gauge (restrictVertexFunction_mem hu k) x
  have h0 := T.equivariance 0 (Nat.zero_le k) u hc0
  have hkk := T.equivariance k le_rfl (restrictVertexFunction k u) hck
  obtain ⟨⟨A, hA, -⟩, ⟨S, hS, -⟩⟩ := h0.2.2.2 hu
  obtain ⟨⟨Ak, hAk, -⟩, ⟨Sk, hSk, -⟩⟩ := hkk.2.2.2 (restrictVertexFunction_mem hu k)
  have cov := hGC L hL n k k hn le_rfl U hU.mem_small u hu hU'.mem_small
  have hUc : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup :=
    ⟨fun b _ => det_eq_one_of_mem (hU.mem_fields.1 b (mem_univ _)), hU.mem_fields.2⟩
  have hsl : ∀ l ∈ vertexFunctionSpace L n k 0, ∀ x, l x ∈ ComplexMatrix2.traceless :=
    fun l hl x => (hl x (mem_univ x)).2
  exact ⟨{ A := A, S := S, Ak := Ak, Sk := Sk
           A_apply := hA, S_apply := hS, Ak_apply := hAk, Sk_apply := hSk
           mem_gauge := hu, towerData := T
           expTwist_eq := fun B hB => h0.1 U hUc B hB
           covDiff_eq := fun l hl => (cov.1 l (hsl l hl)).1
           average_eq := fun l hl => (cov.1 l (hsl l hl)).2
           complexDeriv_eq := fun B hB => (cov.2 B (mem_complexEdgeForms hB)).1
           covDeriv_eq := fun B hB => (cov.2 B (mem_complexEdgeForms hB)).2.1
           drift_eq := fun B hB => (cov.2 B (mem_complexEdgeForms hB)).2.2 }⟩
end Assembly
theorem backgroundFunctional_isGaugeInvariant
    (hQ : RealQuadraticTransposes.Statement)
    (hE : IterLeftChartExpansion)
    (hY : RealLinearMaps.RealLinearMapsStatement)
    (hGC : AveragesGaugeCovariant)
    (hA : SmoothingNearIdentity)
    (hG : GaugeEquivarianceFormsAllSides)
    (hPo : MeanStableFields.MeanStableFieldsHold)
    (hC : LeftChartFields.Claim)
    (hO : PeriodicLattice.LevelBondOrientationDichotomy)
    (hAct : ActionFacts.Statement)
    (hS : FiniteSideFormSpaces)
    (hP : FaceSums.FacesAndPairings) :
    BackgroundFunctionalIsGaugeInvariant := by
  intro L n k hL hn hk
  have T : TowerData L n k :=
    { pos := by have := hL.2; omega
      xor_opposite := fun i hi b => hO L n k hL hn hk i hi b
      admissible := fun i hi c hc => (hA.1 L hL).2.2.periodic n k i hn hi c hc
      mem_polydisc := fun i hi c hc V hV =>
        ((hPo L hL k (by omega)).1 n hn).mem_polydisc i hi c hc V hV
      equivariance := fun i hi => (hG L k i hL hi).1 n hn
      expMul_mem := fun V hV B hB b hb => by
        have h := (((hC.2.2 L k 0 hL (Nat.zero_le k)).1 n hn).1.1.1 V hV B hB ⟨b, hb⟩).1 1
        simpa [LeftChartFields.leftExpMul, LeftChartFields.LatticeData.onPositive,
          LeftChartFields.finiteData] using h
      action_gaugeTransform := (hAct L k n hL hn).2.1 }
  have hfs := finite_vertex (k := k) (j := 0) hP hL hn (Nat.zero_le k)
  have hfb : Finite (Edge L n k 0) :=
    Finite.of_injective (fun b : Edge L n k 0 => (b.source, b.target)) fun _ _ h =>
      PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hFF : EdgeFormsEuclidean L n k 0 ∧ EdgeFormsEuclidean L n k k :=
    ⟨edgeFormsEuclidean_of hS hL hn (Nat.zero_le _), edgeFormsEuclidean_of hS hL hn le_rfl⟩
  have hSS : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k :=
    ⟨vertexFunctionsEuclidean_of hP hL hn (Nat.zero_le _),
      vertexFunctionsEuclidean_of hP hL hn le_rfl⟩
  obtain ⟨δ, hδ, hgood⟩ := exists_radius_of_eventually (eventually_isRegularField hQ hE hY hL hn hk)
  have key : ∀ u ∈ gaugeGroupAt L n k 0, ∀ U : Edge L n k 0 → ComplexMatrix2, IsRegularField U →
      IsRegularField (PeriodicLattice.gaugeTransform u U) →
        BackgroundFunctionalGaugeInvariant u U := by
    intro u hu U h h'
    obtain ⟨P⟩ := nonempty_gaugeConjugation T hGC hL hn hu h h'
    exact P.functional_invariant h h' hFF hSS
  refine ⟨?_, ?_⟩
  · refine eventually_prod_iff.2 ⟨fun v => v ∈ gaugeGroupAt L n k 0 ∧
      ∀ y, ‖v y - 1‖ < δ / 4, ?_, fun W => W ∈ fieldSpace L n k 0 ∧
      ∀ c, ‖W c - 1‖ < δ / 2, ?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_nearIdentity (show 0 < δ / 4 by positivity))] with v h₁ h₂
      exact ⟨h₁, h₂⟩
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_nearIdentity (half_pos hδ))] with W h₁ h₂
      exact ⟨h₁, h₂⟩
    · rintro v ⟨hvG, hvs⟩ W ⟨hWc, hWs⟩
      have hvg : ∀ y, v y ∈ PeriodicLattice.compactGaugeGroup := hvG
      have hWvs : ∀ c, ‖PeriodicLattice.gaugeTransform v W c - 1‖ < δ := by
        intro c
        have h0 := norm_twisted_sub_one_le (X := W c) (hvg c.source) (hvg c.target)
        have h1 := hWs c
        have h2 := hvs c.source
        have h3 := hvs c.target
        change ‖v c.source * W c * (v c.target)⁻¹ - 1‖ < δ
        linarith
      exact key v hvG W (hgood W hWc fun c => (hWs c).trans (half_lt_self hδ))
        (hgood _ (_root_.YangMills.Construction.BackgroundGaugeInvariance.gaugeTransform_mem_fieldSpace hvg hWc) hWvs)
  · change ∀ᶠ W in 𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)), _
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_nearIdentity hδ)]
      with W hWc hWs v hvG hconst
    have hvg : ∀ y, v y ∈ PeriodicLattice.compactGaugeGroup := hvG
    have hWvs : ∀ c, ‖PeriodicLattice.gaugeTransform v W c - 1‖ < δ := by
      intro c
      change ‖v c.source * W c * (v c.target)⁻¹ - 1‖ < δ
      rw [hconst c.target c.source, norm_conj_sub_one_eq (hvg _)]
      exact hWs c
    exact key v hvG W (hgood W hWc hWs) (hgood _ (_root_.YangMills.Construction.BackgroundGaugeInvariance.gaugeTransform_mem_fieldSpace hvg hWc) hWvs)
end BackgroundGaugeInvariance
end
end YangMills.Construction
