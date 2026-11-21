import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Lattice.AveragesAndContourVariablesOfTheIdentityConfigurationProof
import YangMills.Construction.Towers.RelationsOfOneCovariantStepAtTheSideInfinityProof
import YangMills.Construction.Towers.RelationsOfTheLinearMapsAtTheTrivialConfiguration
import YangMills.Construction.Towers.WritingOfTheRealAveragingMap
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.StepAtTrivial
open YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct
open YangMills.Construction.Tower.LeftChartFields YangMills.Construction.Tower.DoubleBlockPolydisc
section Rules
open YangMills.Construction.Coordinates.ComplexCoordinates
variable {ι : Type} [Fintype ι]
theorem inv_mem_unitDeterminant {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹⁻¹ = X := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
variable (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
  (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
include H
theorem isHolomorphicToUnimodular_eval {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Empty) W) (i : ι) :
    IsHolomorphicToUnimodular β W fun p => p (.inl i) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isHolomorphicToUnimodular_component <;> assumption
end Rules
section Points
variable {σ : Type}
theorem asGroupFactors_image (O : Set (σ → ComplexMatrix2)) :
    asGroupFactors '' O = leftComponents ⁻¹' O := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.image_asGroupFactors <;> assumption
theorem asGroupFactors_leftComponents (p : σ ⊕ Empty → ComplexMatrix2) :
    asGroupFactors (leftComponents p) = p := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.asGroupFactors_leftComponents <;> assumption
theorem asGroupFactors_mem_iff {w : σ → ComplexMatrix2} :
    asGroupFactors w ∈ GroupLieProduct σ Empty ↔ w ∈ unimodularPi σ := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.asGroupFactors_mem_iff <;> assumption
end Points
abbrev scalarCoords : ℂ ≃ Coordinates.ComplexCoordinates 1 := (Equiv.funUnique (Fin 1) ℂ).symm
theorem differentiableAt_leftChart (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {Λ : LatticeData} (hΛ : Λ.HolomorphicGradientExists) {σ : Type} [Fintype σ] [Nonempty σ]
    (ι : σ → Λ.PosLink) {O : Set (σ → ComplexMatrix2)}
    (hO : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) O)
    {Φ : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hent : ∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (r s : Fin 2),
      IsHolomorphicToCoords β scalarCoords (leftComponents ⁻¹' O)
        fun p => Φ (leftComponents p) r s)
    {U : Λ.Link → ComplexMatrix2} (hU : U ∈ Λ.fields PeriodicLattice.complexGaugeGroup)
    (hUO : (fun s => U (Λ.incl (ι s))) ∈ O) {B : Λ.Link → ComplexMatrix2} (hB : B ∈ Λ.cforms) :
    DifferentiableAt ℂ (fun t : ℂ => Φ fun s =>
      leftExpMul (t • B (Λ.incl (ι s))) (U (Λ.incl (ι s)))) 0 := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.differentiableAt_along_leftChart <;> assumption
theorem hasDerivAt_ofReal_of_hasDerivAt {g : ℂ → ComplexMatrix2} {d : ComplexMatrix2}
    (h : HasDerivAt g d 0) : HasDerivAt (fun t : ℝ => g (t : ℂ)) d 0 := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.hasDerivAt_ofReal_of_complex <;> assumption
section Trivial
variable {L k j : ℕ} {a a' : ℝ}
theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by
  simp [ComplexMatrix2.logSeries]
theorem conjugateBy_one (X : ComplexMatrix2) : ComplexMatrix2.conjugateBy 1 X = X := by
  simp [ComplexMatrix2.conjugateBy]
theorem opposite_isPositivelyOriented_of_not (hL : Conventions.IsAdmissibleBlockingFactor L)
    {b : Edge L k j} (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.StepRelations.opposite_isPositivelyOriented_of_not <;> assumption
theorem not_opposite_isPositivelyOriented (hL : Conventions.IsAdmissibleBlockingFactor L)
    {b : Edge L k j} (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.StepRelations.not_opposite_isPositivelyOriented <;> assumption
theorem linkHolonomy_const_one (Γ : List (InfiniteLattice.Link a)) :
    linkHolonomy (fun _ : InfiniteLattice.Link a => (1 : ComplexMatrix2)) Γ = 1 := by
  simp [linkHolonomy]
theorem complexLogMean_const_one (hM : Averaging.IdentityFamilyMeanIsOne) {ι : Type*} [Fintype ι]
    [Nonempty ι] : PeriodicLattice.complexLogMean (fun _ : ι => (1 : ComplexMatrix2)) = 1 := by apply _root_.YangMills.SharedProofs.p63807 <;> assumption
theorem contourOrder_nonempty (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') : Nonempty (ContourOrder L y x) :=
  ⟨(Finset.equivFin _).symm⟩
theorem complexContourMean_one (hM : Averaging.IdentityFamilyMeanIsOne)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    complexContourMean L (fun _ : InfiniteLattice.Link a' => (1 : ComplexMatrix2)) y x = 1 := by
  have := contourOrder_nonempty (L := L) y x
  have e : contourHolonomies L (fun _ : InfiniteLattice.Link a' => (1 : ComplexMatrix2)) y x =
      fun _ => 1 :=
    funext fun _ => linkHolonomy_const_one _
  unfold complexContourMean
  rw [e]
  exact complexLogMean_const_one hM
theorem crossingDefect_one (hM : Averaging.IdentityFamilyMeanIsOne) (c : InfiniteLattice.Link a)
    (x : InfiniteLattice.LatticePoint a') :
    crossingDefect L (fun _ : InfiniteLattice.Link a' => (1 : ComplexMatrix2)) c x = 1 := by
  simp [crossingDefect, complexContourMean_one hM, transportAlong, linkHolonomy_const_one]
theorem complexSmoothingPositive_one (hM : Averaging.IdentityFamilyMeanIsOne)
    (c : InfiniteLattice.Link a) :
    complexSmoothingPositive L (fun _ : InfiniteLattice.Link a' => (1 : ComplexMatrix2)) c = 1 := by
  simp [complexSmoothingPositive, crossingDefect_one hM, logSeries_one, transportAlong,
    linkHolonomy_const_one, NormedSpace.exp_zero]
theorem complexSmoothing_one (hM : Averaging.IdentityFamilyMeanIsOne) :
    complexSmoothing L (fun _ : InfiniteLattice.Link a' => (1 : ComplexMatrix2)) =
      (fun _ : InfiniteLattice.Link a => (1 : ComplexMatrix2)) := by
  funext c
  unfold complexSmoothing
  split_ifs
  · exact complexSmoothingPositive_one hM c
  · rw [complexSmoothingPositive_one hM]
    simp
theorem covDiff_one (l : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    covDiff (fun _ : InfiniteLattice.Link a => (1 : ComplexMatrix2)) l = vertexCoboundary l := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [covDiff, extendOddly, if_pos hb, conjugateBy_one, vertexCoboundary]
  · simp only [covDiff, extendOddly, if_neg hb, conjugateBy_one, vertexCoboundary,
      InfiniteLattice.Link.opposite, neg_sub]
theorem extendOddly_of_not_positive {f : Edge L k j → ComplexMatrix2} (b : Edge L k j)
    (hb : ¬ b.IsPositivelyOriented) (hr : b.opposite.IsPositivelyOriented) :
    extendOddly f b = -extendOddly f b.opposite := by
  simp only [extendOddly, if_neg hb, if_pos hr]
theorem one_mem_fieldSpace : (fun _ : Edge L k j => (1 : ComplexMatrix2)) ∈ fieldSpace L k j :=
  ⟨fun _ => one_mem _, fun _ => by simp⟩
theorem one_mem_fieldsValuedIn : (fun _ : Edge L k j => (1 : ComplexMatrix2)) ∈
    fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
  ⟨fun _ => Matrix.det_one, fun _ => by simp⟩
theorem one_mem_nearIdentityPolydisc {ρ : ℝ} (hρ : 0 < ρ) (c : Edge L k (j + 1)) :
    (fun _ : Edge L k j => (1 : ComplexMatrix2)) ∈ nearIdentityPolydisc L k j ρ c :=
  ⟨⟨fun _ _ => Matrix.det_one, fun _ _ => by simp⟩,
    fun _ _ => by simpa [ComplexMatrix2.operatorNorm] using hρ⟩
theorem expTwist_zero_smul (B : Edge L k j → ComplexMatrix2) :
    expTwist ((0 : ℂ) • B) (fun _ : Edge L k j => (1 : ComplexMatrix2)) = fun _ => 1 := by
  funext b
  unfold expTwist
  split_ifs <;> simp [NormedSpace.exp_zero]
theorem leftExp_mem_and_continuousAt (hA : Tower.LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k j)) (b : Edge L k j) (hb : b.IsPositivelyOriented) :
    (∀ t : ℂ, ComplexMatrix2.matExp (Complex.I • (t • B) b) * 1 ∈
        PeriodicLattice.complexGaugeGroup) ∧
      ContinuousAt (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B) b) *
        (1 : ComplexMatrix2)) 0 := by
  have hl := (((hA.2.2 L k j hL hj).2.1).1).2 (fun _ => 1) one_mem_fieldsValuedIn B hB ⟨b, hb⟩
  exact ⟨hl.1, hl.2.continuousAt⟩
theorem expTwist_curve_spec (hA : Tower.LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k j)) (t : ℂ) :
    (∀ b, expTwist (t • B) (fun _ : Edge L k j => (1 : ComplexMatrix2)) b ∈
        PeriodicLattice.complexGaugeGroup) ∧
      ∀ b : Edge L k j, expTwist (t • B) (fun _ : Edge L k j => (1 : ComplexMatrix2)) b.opposite =
        (expTwist (t • B) (fun _ : Edge L k j => (1 : ComplexMatrix2)) b)⁻¹ := by
  classical
  have hmem : ∀ b, expTwist (t • B) (fun _ : Edge L k j => (1 : ComplexMatrix2)) b ∈
      PeriodicLattice.complexGaugeGroup := by
    intro b
    by_cases hb : b.IsPositivelyOriented
    · simp only [expTwist, if_pos hb]
      exact (leftExp_mem_and_continuousAt hA hL hj hB b hb).1 t
    · simp only [expTwist, if_neg hb]
      exact inv_mem_unitDeterminant ((leftExp_mem_and_continuousAt hA hL hj hB _
        (opposite_isPositivelyOriented_of_not hL hb)).1 t)
  refine ⟨hmem, fun b => ?_⟩
  by_cases hb : b.IsPositivelyOriented
  · have hn := not_opposite_isPositivelyOriented hL hb
    simp only [expTwist, if_neg hn, if_pos hb, InfiniteLattice.Link.opposite_opposite]
  · have hr := opposite_isPositivelyOriented_of_not hL hb
    simp only [expTwist, if_pos hr, if_neg hb]
    exact (inv_inv_of_mem_unitDeterminant ((leftExp_mem_and_continuousAt hA hL hj hB _ hr).1 t)).symm
theorem inv_eq_adjugate_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹ = X.adjugate := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.MeanData.inv_eq_adjugate_of_mem <;> assumption
theorem tendsto_expTwist_curve (hA : Tower.LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k j)) (b : Edge L k j) :
    Tendsto (fun t : ℂ => expTwist (t • B) (fun _ : Edge L k j => (1 : ComplexMatrix2)) b) (𝓝 0)
      (𝓝 1) := by
  classical
  have hzero : ∀ b : Edge L k j,
      ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • B) b) * (1 : ComplexMatrix2) = 1 := by
    intro b
    simp [NormedSpace.exp_zero]
  by_cases hb : b.IsPositivelyOriented
  · have h := (leftExp_mem_and_continuousAt hA hL hj hB b hb).2.tendsto
    rw [hzero] at h
    refine h.congr fun t => ?_
    simp only [expTwist, if_pos hb]
  · have hr := opposite_isPositivelyOriented_of_not hL hb
    have h := (leftExp_mem_and_continuousAt hA hL hj hB _ hr).2.tendsto
    rw [hzero] at h
    have h2 : Tendsto (fun t : ℂ =>
        (ComplexMatrix2.matExp (Complex.I • (t • B) b.opposite) * (1 : ComplexMatrix2)).adjugate)
        (𝓝 0) (𝓝 (1 : ComplexMatrix2).adjugate) :=
      (Continuous.matrix_adjugate continuous_id).continuousAt.tendsto.comp h
    rw [Matrix.adjugate_one] at h2
    refine h2.congr fun t => ?_
    simp only [expTwist, if_neg hb]
    exact (inv_eq_adjugate_of_mem_unitDeterminant
      ((leftExp_mem_and_continuousAt hA hL hj hB _ hr).1 t)).symm
theorem isOpen_operatorNorm_sub_one_lt {r : ℝ} :
    IsOpen {X : ComplexMatrix2 | ComplexMatrix2.operatorNorm (X - 1) < r} :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
theorem eventually_expTwist_mem_polydisc (hA : Tower.LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k j)) {ρ : ℝ} (hρ : 0 < ρ) {c : Edge L k (j + 1)}
    (hfin : (doubleCubeLinks L (meshAt L k j) c).Finite) :
    ∀ᶠ t : ℂ in 𝓝 0, expTwist (t • B) (fun _ : Edge L k j => (1 : ComplexMatrix2)) ∈
      nearIdentityPolydisc L k j ρ c := by
  have hn : ∀ᶠ t : ℂ in 𝓝 0, ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
      ComplexMatrix2.operatorNorm
        (expTwist (t • B) (fun _ : Edge L k j => (1 : ComplexMatrix2)) b - 1) < ρ := by
    refine (eventually_all_finite hfin).2 fun b _ => ?_
    refine (tendsto_expTwist_curve hA hL hj hB b).eventually
      (isOpen_operatorNorm_sub_one_lt.mem_nhds ?_)
    simpa [ComplexMatrix2.operatorNorm] using hρ
  filter_upwards [hn] with t ht
  have hconf := expTwist_curve_spec hA hL hj hB t
  exact ⟨⟨fun b _ => hconf.1 b, fun b _ => hconf.2 b⟩, ht⟩
theorem eq_fieldOfValues_on_doubleCubeLinks (hL : Conventions.IsAdmissibleBlockingFactor L)
    {c : Edge L k (j + 1)}
    (hrev : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
      b.opposite ∈ doubleCubeLinks L (meshAt L k j) c)
    {ρ : ℝ} {V : Edge L k j → ComplexMatrix2} (hV : V ∈ nearIdentityPolydisc L k j ρ c)
    (b : Edge L k j) (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) :
    V b = DoubleBlockPolydisc.Infinite.fieldOfValues L k j c (fun b => V b.1) b := by apply _root_.YangMills.Construction.Tower.FullSpace.StepRelations.eq_fieldOfValues_of_mem <;> assumption
theorem mem_nearIdentityPolydisc_of_eqOn {c : Edge L k (j + 1)}
    (hrev : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
      b.opposite ∈ doubleCubeLinks L (meshAt L k j) c)
    {ρ : ℝ} {V V' : Edge L k j → ComplexMatrix2} (hV : V ∈ nearIdentityPolydisc L k j ρ c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    V' ∈ nearIdentityPolydisc L k j ρ c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.mem_nearIdentityPolydisc_congr <;> assumption
theorem complexContourMean_eq_of_eqOn (hS : Tower.SmoothingNearIdentity)
    (hQ : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hj : j < k)
    {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented) {y : Vertex L k (j + 1)}
    (hy : y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))))
    {x : Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {V V' : Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (hV' : V' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    complexContourMean L V y x = complexContourMean L V' y x := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hserve := (hS.1 L hL).2.2.fullSpace k j hj c hc
  have hQ' := ((hQ L hL0 hL k).2.2.2.2.2.2 hk 1 one_pos).2 j hj c hc
  have hy' : y = c.initial ∨ y = c.terminal := by simpa using hy
  have e1 := hQ'.complexContourMean_eq V (hserve.subset_complexDomain hV) y hy' x hx
  have e2 := hQ'.complexContourMean_eq V' (hserve.subset_complexDomain hV') y hy' x hx
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 1
  funext z
  unfold projField
  split_ifs with h
  · exact he _ h.choose_spec.1
  · rfl
theorem differentiableAt_complexContourMean_curve
    (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hS : Tower.SmoothingNearIdentity) (hA : Tower.LeftChartFields.Claim)
    (hQ : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hP : Tower.DoubleBlockPolydisc.PolydiscsHold) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hj : j < k) {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    {y : Vertex L k (j + 1)} (hy : y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))))
    {x : Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    DifferentiableAt ℂ (fun t : ℂ => complexContourMean L
      (expTwist (t • B) (fun _ : Edge L k j => (1 : ComplexMatrix2))) y x) 0 := by
  classical
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  have holo := (hP L hL k j hj).2 c hc
  obtain ⟨inst, h⟩ := holo.holomorphic_contourMean y hy x hx
  have hfo := holo.finite_open
  have hne : Nonempty (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c) :=
    hfo.positive_nonempty.to_subtype
  have hd := differentiableAt_leftChart H (((hA.2.2 L k j hL hj.le).2.1).2.2.2)
    (Λ := fullData L k j) (σ := DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    (fun s => (⟨s.1, s.2.2⟩ : PositiveEdge (meshAt L k j)))
    hfo.isRelativelyOpen
    (Φ := fun v => complexContourMean L
      (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c v) y x) h.entries one_mem_fieldsValuedIn
    ⟨_, ⟨_, one_mem_nearIdentityPolydisc hρ c, rfl⟩, rfl⟩ hB
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [eventually_expTwist_mem_polydisc hA hL hj.le hB hρ (c := c) hfo.finite]
    with t ht
  have hag := eq_fieldOfValues_on_doubleCubeLinks hL hfo.opposite_mem ht
  rw [complexContourMean_eq_of_eqOn hS hQ hL hk hj hc hy hx ht
    (mem_nearIdentityPolydisc_of_eqOn hfo.opposite_mem ht hag) hag]
  congr 2
  funext s
  show expTwist (t • B) (fun _ : Edge L k j => (1 : ComplexMatrix2)) s.1 = _
  simp only [expTwist, if_pos s.2.2]
  rfl
theorem logDirectionalDeriv_complexContourMean_one (hM : Averaging.IdentityFamilyMeanIsOne)
    (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hS : Tower.SmoothingNearIdentity)
    (hV : Tower.ComplexMeanLiesInComplexGaugeGroup)
    (hA : Tower.LeftChartFields.Claim)
    (hQ : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hP : Tower.DoubleBlockPolydisc.PolydiscsHold) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) {B : Edge L k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace (meshAt L k j))
    (y : Vertex L k (j + 1)) {x : Vertex L k j}
    (hx : x ∈ cubeVertices L (meshAt L k j) y) :
    logDirectionalDeriv ℂ (fun X => complexContourMean L
        (expTwist X (fun _ : Edge L k j => (1 : ComplexMatrix2))) y x)
      (complexContourMean L (fun _ : Edge L k j => (1 : ComplexMatrix2)) y x) B =
      _root_.YangMills.Construction.Tower.FullSpace.contourAverage L B y x := by
  classical
  have hk : 1 ≤ k := by omega
  have hBC : B ∈ complexEdgeForms (meshAt L k j) := ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
  obtain ⟨c, hc, hct⟩ : ∃ c : Edge L k (j + 1), c.IsPositivelyOriented ∧ y = c.initial :=
    ⟨InfiniteLattice.Link.forwardFrom y 0,
      InfiniteLattice.mem_positiveLinks_iff.1 ⟨y, 0, rfl⟩, rfl⟩
  have hy : y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))) := Or.inl hct
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  have hfo := ((hP L hL k j hj).2 c hc).finite_open
  have hserve := (hS.1 L hL).2.2.fullSpace k j hj c hc
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (eventually_expTwist_mem_polydisc hA hL hj.le hBC hρ (c := c) hfo.finite)
  let W : ℂ → ComplexMatrix2 := fun t => complexContourMean L
    (expTwist (t • B) (fun _ : Edge L k j => (1 : ComplexMatrix2))) y x
  have hgroup : ∀ V : Edge L k j → ComplexMatrix2, V ∈ complexDomainNearOne L c →
      complexContourMean L V y x ∈ PeriodicLattice.complexGaugeGroup := fun V hV' =>
    ((hV.2 L k (j + 1) hL (Nat.succ_le_succ (Nat.zero_le j)) (Nat.succ_le_of_lt hj)).2 c V hc
      hV').1 y (Or.inl hct) x hx
  have hmaps : MapsTo W (Metric.ball 0 ρ₀) PeriodicLattice.complexGaugeGroup := fun t ht =>
    hgroup _ (hserve.subset_complexDomain (hball t ht))
  have hdW : DifferentiableAt ℂ W 0 :=
    differentiableAt_complexContourMean_curve H hS hA hQ hP hL hk hj hc hy hx hBC
  have hW0 : W 0 = 1 := by
    show complexContourMean L _ y x = 1
    rw [expTwist_zero_smul]
    exact complexContourMean_one hM y x
  have hlog := (hA.2.1 ρ₀ hρ₀ W hmaps hdW).2.1
  have hreal := hasDerivAt_ofReal_of_hasDerivAt hlog.hasDerivAt
  have hcon := ((hS.1 L hL).2.1 k j hj).2.1.deriv_contour B hB y x hx
  have e : (fun t : ℝ => ComplexMatrix2.logSeries (complexContourMean L
      (expTwist ((t : ℂ) • B) (fun _ : Edge L k j => (1 : ComplexMatrix2))) y x)) =
      fun r : ℝ => ComplexMatrix2.logSeries (W (r : ℂ) * (W 0)⁻¹) := by
    funext r
    rw [hW0]
    simp [W]
  rw [e, hreal.deriv] at hcon
  have e2 : (fun t : ℂ => ComplexMatrix2.logSeries (complexContourMean L
      (expTwist (algebraMap ℂ ℂ t • B) (fun _ : Edge L k j => (1 : ComplexMatrix2))) y x *
        (1 : ComplexMatrix2)⁻¹)) =
      fun t : ℂ => ComplexMatrix2.logSeries (W t * (W 0)⁻¹) := by
    funext t
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [hW0]
  rw [complexContourMean_one hM y x]
  unfold logDirectionalDeriv
  rw [e2]
  exact hcon
end Trivial
theorem smoothingStepAtOne_holds (hM : Averaging.IdentityFamilyMeanIsOne)
    (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hS : Tower.SmoothingNearIdentity)
    (hV : Tower.ComplexMeanLiesInComplexGaugeGroup)
    (hA : Tower.LeftChartFields.Claim)
    (hQ : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hP : Tower.DoubleBlockPolydisc.PolydiscsHold)
    (hR : Tower.TrivialLinearization.AllRelationsStatement)
    (hW : Tower.FullSpace.CompactPresentation.PresentationTheorem) :
    Tower.FullSpace.SmoothingStepAtOne := by
  intro L hL k i hi
  classical
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  have hD := ((hS.1 L hL).2.1 k i hi).2.1
  have hrel := ((hR L hL).2 k i 0 hi (Nat.zero_le k)).1
  obtain ⟨ε₀, hε₀, hdiff⟩ := hD.deriv_eq_linear
  obtain ⟨hmap, hval⟩ := hdiff ε₀ hε₀ le_rfl
  have hAv : smoothingMap L k i (fun _ => 1) = fun _ => 1 := complexSmoothing_one hM
  have hwithin : ∀ b : Edge L k i,
      ComplexMatrix2.operatorNorm ((1 : ComplexMatrix2) - 1) < polydiscRadius L :=
    fun _ => by simpa [ComplexMatrix2.operatorNorm] using hρ
  have hOne : (fun _ : Edge L k i => (1 : ComplexMatrix2)) ∈ smoothingBall L k i ε₀ := by
    refine ⟨⟨one_mem_fieldSpace, fun c hc => ⟨?_, ?_⟩⟩, ?_⟩
    · exact ((hS.1 L hL).2.2.fullSpace k i hi c hc).subset_complexDomain
        (one_mem_nearIdentityPolydisc hρ c)
    · rw [complexSmoothingPositive_one hM]
      exact one_mem _
    · simpa [supDistOne, ComplexMatrix2.operatorNorm] using hε₀
  have hQ₁ : ∀ B ∈ edgeFormSpace (meshAt L k i),
      complexSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) B =
        linearSmoothing (a := meshAt L k (i + 1)) L B := by
    intro B hB
    have hpos : ∀ c : Edge L k (i + 1), c.IsPositivelyOriented →
        leftDifferential (smoothingBall L k i ε₀) (smoothingMap L k i) (fun _ => 1) B c =
          complexSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) B c := fun c hc =>
      ((hW L hL k i hi c hc _ (fun V hV => hV.1) _ hOne hwithin).2 hmap.1 B hB).leftDifferential_eq
    rw [← hval B hB]
    funext c
    by_cases hc : c.IsPositivelyOriented
    · exact (hpos c hc).symm
    · have hr := opposite_isPositivelyOriented_of_not hL hc
      have h := hpos _ hr
      unfold leftDifferential complexSmoothingDeriv holLeftDifferential at h ⊢
      rw [extendOddly_of_not_positive c hc hr, extendOddly_of_not_positive c hc hr]
      exact congrArg Neg.neg h.symm
  refine ⟨fun B hB => ?_, fun l _ => ?_⟩
  · have hn : contourLogDrift (L := L) (k := k) (j := i) (fun _ => 1) B =
        cubeContourAverage (a := meshAt L k (i + 1)) L B := by
      funext y
      show PeriodicLattice.inverseFourthPowerWeight L • _ =
        PeriodicLattice.inverseFourthPowerWeight L • _
      congr 1
      exact finsum_mem_congr rfl fun x hx =>
        logDirectionalDeriv_complexContourMean_one hM H hS hV hA hQ hP hL hi hB y hx
    refine ⟨hQ₁ B hB, hn, ?_⟩
    show complexSmoothingDeriv (L := L) (k := k) (j := i) (fun _ => 1) B +
      covDiff (smoothingMap L k i fun _ => 1)
        (contourLogDrift (L := L) (k := k) (j := i) (fun _ => 1) B) = _
    rw [hQ₁ B hB, hn, hAv, covDiff_one, hrel.1 B hB, sub_add_cancel]
  · funext y
    show PeriodicLattice.inverseFourthPowerWeight L • _ =
      PeriodicLattice.inverseFourthPowerWeight L • _
    congr 1
    exact finsum_mem_congr rfl fun x _ => by rw [complexContourMean_one hM, conjugateBy_one]
end YangMills.Construction.Tower.FullSpace.StepAtTrivial
end
