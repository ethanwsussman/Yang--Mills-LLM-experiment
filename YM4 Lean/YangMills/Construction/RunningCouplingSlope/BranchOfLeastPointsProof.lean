import YangMills.Construction.RunningCouplingSlope.GradientAndMultiplierAtALeastPointProof
import YangMills.Construction.RunningCouplingSlope.BranchOfLeastPoints
import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOneProof
import YangMills.Construction.RunningCouplingSlope.LeastPointsInTheNearestGauge
import YangMills.Construction.RunningCouplingSlope.LeastValueAlongATopFormProof
import YangMills.Construction.RunningCouplingSlope.SystemOfTheFirstOrder
import YangMills.Construction.Towers.StepOfTheCovariantAveragesAtOneAtTheSideInfinityProof
import YangMills.Construction.Towers.TheResponseOfTheCriticalBranchProof
import YangMills.Construction.Towers.ValuesOfTheLinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FirstVariationProof
open Tower
open Tower.LeftChartFields
open Matrices
section Smooth
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P} {m : WithTop ℕ∞}
private theorem contDiffAt_inv_of_one {f : P → ComplexMatrix2} (hf : ContDiffAt ℝ m f p₀)
    (h1 : f p₀ = 1) : ContDiffAt ℝ m (fun p => (f p)⁻¹) p₀ := by
  have e : (fun p => (f p)⁻¹) = fun p => Ring.inverse (f p) := by
    funext p
    exact Matrix.nonsing_inv_eq_ringInverse _
  rw [e]
  have h : ContDiffAt ℝ m (Ring.inverse : ComplexMatrix2 → ComplexMatrix2) (f p₀) := by
    rw [h1]
    exact contDiffAt_ringInverse ℝ (1 : ComplexMatrix2ˣ)
  exact h.comp p₀ hf
abbrev _root_.YangMills.SharedProofs.p36358 := @contDiffAt_inv_of_one
private def entryL (a b : Fin 2) : ComplexMatrix2 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
private theorem contDiffAt_det {f : P → ComplexMatrix2} (hf : ContDiffAt ℝ m f p₀) :
    ContDiffAt ℝ m (fun p => Matrix.det (f p)) p₀ := by apply _root_.YangMills.SharedProofs.p54943 <;> assumption
private theorem contDiffAt_sqrt_of_one {f : P → ℂ} (hf : ContDiffAt ℝ m f p₀) (h1 : f p₀ = 1) :
    ContDiffAt ℝ m (fun p => f p ^ (1 / 2 : ℂ)) p₀ := by
  have h : ContDiffAt ℝ m (fun z : ℂ => Complex.exp (Complex.log z * (1 / 2 : ℂ))) (f p₀) := by
    rw [h1]
    have hl : ContDiffAt ℂ m Complex.log 1 :=
      Complex.contDiffAt_log (by simp)
    exact ((Complex.contDiff_exp.contDiffAt.comp (1 : ℂ)
      (hl.mul contDiffAt_const))).restrict_scalars ℝ
  have hc := h.comp p₀ hf
  refine hc.congr_of_eventuallyEq ?_
  have hne : ∀ᶠ p in 𝓝 p₀, f p ≠ 0 :=
    hf.continuousAt.eventually_ne (by rw [h1]; exact one_ne_zero)
  filter_upwards [hne] with p hp
  simp only [Function.comp]
  rw [Complex.cpow_def_of_ne_zero hp]
abbrev _root_.YangMills.SharedProofs.p99689 := @contDiffAt_sqrt_of_one
end Smooth
section Family
variable {L n k j : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P} {m : WithTop ℕ∞}
private theorem pathHolonomy_const_one (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy (fun _ : Edge L n k j => (1 : ComplexMatrix2)) Γ = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.pathHolonomy_one <;> assumption
private theorem contDiffAt_pathHolonomy {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (Γ : List (Edge L n k j)) :
    ContDiffAt ℝ m (fun p => PeriodicLattice.pathHolonomy (V p) Γ) p₀ := by apply _root_.YangMills.SharedProofs.p35651 <;> assumption
private theorem contDiffAt_contourHolonomy {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (h1 : V p₀ = fun _ => 1)
    (c : Edge L n k (j + 1)) (x : Vertex L n k j) (π : Equiv.Perm (Fin 4)) :
    ContDiffAt ℝ m (fun p => contourHolonomy (V p) c x π) p₀ := by
  simp only [contourHolonomy]
  refine ((contDiffAt_pathHolonomy hV _).mul (contDiffAt_pathHolonomy hV _)).mul
    (contDiffAt_inv_of_one (contDiffAt_pathHolonomy hV _) ?_)
  rw [h1]
  exact pathHolonomy_const_one _
private theorem contDiffAt_contourMean [Finite (Vertex L n k j)] {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (h1 : V p₀ = fun _ => 1)
    (c : Edge L n k (j + 1)) :
    ContDiffAt ℝ m (fun p => contourMean (V p) c) p₀ := by
  simp only [contourMean]
  have hs : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  simp only [finsum_mem_eq_finite_toFinset_sum _ hs]
  refine ContDiffAt.const_smul _ ?_
  exact ContDiffAt.sum fun x _ => ContDiffAt.sum fun π _ => contDiffAt_contourHolonomy hV h1 c x π
abbrev _root_.YangMills.SharedProofs.p17315 := @contDiffAt_contourMean
private theorem contDiffAt_meanRadius [Finite (Vertex L n k j)] {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (h1 : V p₀ = fun _ => 1)
    (c : Edge L n k (j + 1)) (hc : Matrix.det (contourMean (V p₀) c) = 1) :
    ContDiffAt ℝ m (fun p => meanRadius (V p) c) p₀ :=
  contDiffAt_sqrt_of_one (contDiffAt_det (contDiffAt_contourMean hV h1 c)) hc
private theorem contDiffAt_normalizedMean [Finite (Vertex L n k j)]
    {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (h1 : V p₀ = fun _ => 1)
    (c : Edge L n k (j + 1)) (hc : meanRadius (V p₀) c = 1)
    (hd : Matrix.det (contourMean (V p₀) c) = 1) :
    ContDiffAt ℝ m (fun p => normalizedMean (V p) c) p₀ := by
  simp only [normalizedMean]
  refine ContDiffAt.smul (ContDiffAt.inv (contDiffAt_meanRadius hV h1 c hd) ?_)
    (contDiffAt_contourMean hV h1 c)
  rw [hc]
  exact one_ne_zero
abbrev _root_.YangMills.SharedProofs.p35211 := @contDiffAt_normalizedMean
end Family
section Fields
variable {L n k : ℕ}
private theorem oriented_or_opposite {j : ℕ} (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem levelField_succ_pos (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    levelField X (j + 1) c = X.noise ⟨j, hj⟩ ⟨c, hc⟩ * normalizedMean (levelField X j) c := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
private theorem levelField_succ_neg (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : ¬c.IsPositivelyOriented) (hc' : c.opposite.IsPositivelyOriented) :
    levelField X (j + 1) c =
      (X.noise ⟨j, hj⟩ ⟨c.opposite, hc'⟩ * normalizedMean (levelField X j) c.opposite)⁻¹ := by apply _root_.YangMills.SharedProofs.p3610 <;> assumption
private structure TowerFacts (L n k : ℕ) : Prop where
  sites_finite : ∀ j, j ≤ k → Finite (Vertex L n k j)
  posEdges_finite : ∀ j, j ≤ k → Finite (PositiveEdge L n k j)
  edges_finite : ∀ j, j ≤ k → Finite (Edge L n k j)
  faces_finite : Finite (Face L n k 0)
  deriv_at_one : ∀ j, j < k → ∀ B ∈ edgeFormSpace L n k j, ∀ c : Edge L n k (j + 1),
    c.IsPositivelyOriented →
    leftDifferential normalizedMean (fun _ => 1) B c = linearSmoothing L n k j B c
  smoothing_mem : ∀ j, j < k → ∀ B ∈ edgeFormSpace L n k j,
    linearSmoothing L n k j B ∈ edgeFormSpace L n k (j + 1)
  not_both : ∀ j, j ≤ k → ∀ b : Edge L n k j, b.IsPositivelyOriented →
    ¬ b.opposite.IsPositivelyOriented
  at_one : ∀ j, j < k → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    contourMean (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1 ∧
      meanRadius (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1 ∧
      normalizedMean (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1
  leftExp : ∀ j, j ≤ k → (finiteData L n k j).LeftExpMulMemGroup
  curveLogs : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
    CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P} {m : WithTop ℕ∞}
private theorem contDiffAt_levelFields (hT : TowerFacts L n k) {X : P → ChainPoint L n k}
    (hb : ∀ b, ContDiffAt ℝ m (fun p => (X p).fine b) p₀)
    (hn : ∀ i c, ContDiffAt ℝ m (fun p => (X p).noise i c) p₀)
    (h0 : X p₀ = unitPoint L n k) : ∀ j, j ≤ k →
      (∀ b, ContDiffAt ℝ m (fun p => levelField (X p) j b) p₀) ∧
        levelField (X p₀) j = fun _ => 1 := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨hb, ?_⟩
    rw [h0]
    rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    obtain ⟨ih1, ih2⟩ := ih hj.le
    haveI := hT.sites_finite j hj.le
    have hpos : ∀ c : Edge L n k (j + 1), ∀ hc : c.IsPositivelyOriented,
        ContDiffAt ℝ m (fun p => (X p).noise ⟨j, hj⟩ ⟨c, hc⟩ *
          normalizedMean (levelField (X p) j) c) p₀ ∧
        (X p₀).noise ⟨j, hj⟩ ⟨c, hc⟩ * normalizedMean (levelField (X p₀) j) c = 1 := by
      intro c hc
      obtain ⟨h1, h2, h3⟩ := hT.at_one j hj c hc
      refine ⟨(hn _ _).mul (contDiffAt_normalizedMean ih1 ih2 c ?_ ?_), ?_⟩
      · rw [ih2, h2]
      · rw [ih2, h1]
        simp
      · rw [ih2, h3, h0]
        simp [unitPoint]
    have hval : levelField (X p₀) (j + 1) = fun _ => 1 := by
      funext c
      by_cases hc : c.IsPositivelyOriented
      · rw [levelField_succ_pos _ hj c hc]
        exact (hpos c hc).2
      · have hc' : c.opposite.IsPositivelyOriented := (oriented_or_opposite c).resolve_left hc
        rw [levelField_succ_neg _ hj c hc hc', (hpos c.opposite hc').2]
        simp
    refine ⟨fun c => ?_, hval⟩
    by_cases hc : c.IsPositivelyOriented
    · have e : (fun p => levelField (X p) (j + 1) c) = fun p => (X p).noise ⟨j, hj⟩ ⟨c, hc⟩ *
          normalizedMean (levelField (X p) j) c := by
        funext p
        exact levelField_succ_pos _ hj c hc
      rw [e]
      exact (hpos c hc).1
    · have hc' : c.opposite.IsPositivelyOriented := (oriented_or_opposite c).resolve_left hc
      have e : (fun p => levelField (X p) (j + 1) c) = fun p =>
          ((X p).noise ⟨j, hj⟩ ⟨c.opposite, hc'⟩ *
          normalizedMean (levelField (X p) j) c.opposite)⁻¹ := by
        funext p
        exact levelField_succ_neg _ hj c hc hc'
      rw [e]
      exact contDiffAt_inv_of_one (hpos c.opposite hc').1 (hpos c.opposite hc').2
private theorem contDiffAt_levelRadius (hT : TowerFacts L n k) {X : P → ChainPoint L n k}
    (hb : ∀ b, ContDiffAt ℝ m (fun p => (X p).fine b) p₀)
    (hn : ∀ i c, ContDiffAt ℝ m (fun p => (X p).noise i c) p₀)
    (h0 : X p₀ = unitPoint L n k) {i : ℕ} (hi : i < k) (c : Edge L n k (i + 1))
    (hc : c.IsPositivelyOriented) :
    ContDiffAt ℝ m (fun p => meanRadius (levelField (X p) i) c) p₀ := by
  obtain ⟨h1, h2⟩ := contDiffAt_levelFields hT hb hn h0 i hi.le
  haveI := hT.sites_finite i hi.le
  refine contDiffAt_meanRadius h1 h2 c ?_
  rw [h2, (hT.at_one i hi c hc).1]
  simp
private theorem contDiffAt_matExp_I {f : P → ComplexMatrix2} (hf : ContDiffAt ℝ m f p₀) :
    ContDiffAt ℝ m (fun p => ComplexMatrix2.matExp (Complex.I • f p)) p₀ := by apply _root_.YangMills.SharedProofs.p25406 <;> assumption
private theorem matExp_I_zero : ComplexMatrix2.matExp (Complex.I • (0 : ComplexMatrix2)) = 1 := by
  rw [smul_zero]
  exact NormedSpace.exp_zero
private theorem contDiffAt_expTwist {j : ℕ} {A U : P → Edge L n k j → ComplexMatrix2}
    (hA : ∀ b, ContDiffAt ℝ m (fun p => A p b) p₀) (hU : ∀ b, ContDiffAt ℝ m (fun p => U p b) p₀)
    (hA0 : A p₀ = 0) (hU0 : U p₀ = fun _ => 1) (b : Edge L n k j) :
    ContDiffAt ℝ m (fun p => PeriodicLattice.expTwist (A p) (U p) b) p₀ := by
  by_cases hb : b.IsPositivelyOriented
  · simp only [PeriodicLattice.expTwist, if_pos hb]
    exact (contDiffAt_matExp_I (hA b)).mul (hU b)
  · simp only [PeriodicLattice.expTwist, if_neg hb]
    refine contDiffAt_inv_of_one ((contDiffAt_matExp_I (hA _)).mul (hU _)) ?_
    rw [hA0, hU0]
    simp only [Pi.zero_apply, mul_one]
    exact matExp_I_zero
abbrev _root_.YangMills.SharedProofs.p28082 := @contDiffAt_expTwist
end Fields
private theorem exists_partialDeriv_snd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E × ℝ → F}
    (hf : ContDiffAt ℝ 2 f ((0 : E), (0 : ℝ))) :
    ∃ G : E → F, ContinuousAt G 0 ∧ ∀ᶠ w in 𝓝 (0 : E), HasDerivAt (fun t => f (w, t)) (G w) 0 := by
  refine ⟨fun w => fderiv ℝ f (w, 0) (0, 1), ?_, ?_⟩
  · have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) ((0 : E), (0 : ℝ)) :=
      hf.fderiv_right (m := 1) (by norm_num)
    have h2 : ContinuousAt (fun w : E => fderiv ℝ f (w, (0 : ℝ))) 0 :=
      ContinuousAt.comp (f := fun w : E => (w, (0 : ℝ))) h1.continuousAt
        (by fun_prop)
    exact h2.clm_apply continuousAt_const
  · have h3 : ∀ᶠ y in 𝓝 ((0 : E), (0 : ℝ)), ContDiffAt ℝ 2 f y := hf.eventually (by simp)
    have h4 : Tendsto (fun w : E => (w, (0 : ℝ))) (𝓝 0) (𝓝 ((0 : E), (0 : ℝ))) :=
      Continuous.tendsto (by fun_prop) _
    filter_upwards [h4.eventually h3] with w hw
    have hd : HasFDerivAt f (fderiv ℝ f (w, 0)) (w, (0 : ℝ)) :=
      (hw.differentiableAt (by norm_num)).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => (w, t)) ((0 : E), (1 : ℝ)) 0 :=
      (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
    exact hd.comp_hasDerivAt_of_eq 0 hl rfl
abbrev _root_.YangMills.SharedProofs.p85562 := @exists_partialDeriv_snd
section Curves
private theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
private theorem hasDerivAt_expLine (X : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • (t • X))) (Complex.I • X) 0 := by apply _root_.YangMills.SharedProofs.p9756 <;> assumption
private theorem expLine_zero (X : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • ((0 : ℝ) • X)) = 1 := by apply _root_.YangMills.SharedProofs.p11429 <;> assumption
variable {L n k j : ℕ}
private def velocity (V M : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) : ComplexMatrix2 :=
  open Classical in
  if b.IsPositivelyOriented then Complex.I • M b * V b else V b * (Complex.I • M b)
private theorem edge_opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
private theorem det_eq_one_of_mem {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (b : Edge L n k j) :
    Matrix.det (V b) = 1 := hV.1 b (Set.mem_univ b)
private theorem hasDerivAt_expTwist_line {V M : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hM : ∀ b, M b.opposite = -M b) (b : Edge L n k j) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.expTwist (t • M) V b) (velocity V M b) 0 := by apply _root_.YangMills.DeltaSharedProofs.p350 <;> assumption
private theorem expTwist_zero {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist (0 : Edge L n k j → ComplexMatrix2) V = V := by apply _root_.YangMills.SharedProofs.p57400 <;> assumption
private theorem hasDerivAt_inv_of_det_one
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {W : ℝ → ComplexMatrix2} {W' : ComplexMatrix2} (hW : HasDerivAt W W' 0)
    (h0 : Matrix.det (W 0) = 1) :
    HasDerivAt (fun t => (W t)⁻¹) (-((W 0)⁻¹ * W' * (W 0)⁻¹)) 0 := by apply _root_.YangMills.SharedProofs.p36414 <;> assumption
end Curves
section Movement
variable {L n k : ℕ}
private theorem extendOddly_opposite (hT : TowerFacts L n k) {j : ℕ} (hj : j ≤ k)
    (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by
  by_cases hb : b.IsPositivelyOriented
  · have hb' := hT.not_both j hj b hb
    simp only [extendOddly, if_pos hb, if_neg hb', edge_opposite_opposite]
  · have hb' : b.opposite.IsPositivelyOriented := (oriented_or_opposite b).resolve_left hb
    simp only [extendOddly, if_pos hb', if_neg hb, neg_neg]
private theorem transport_succ_pos (X : ChainPoint L n k) (ξ : LevelForms L n k) {j : ℕ}
    (hj : j < k) (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    tangentTransport X ξ (j + 1) c = ComplexMatrix2.conjugateBy (X.noise ⟨j, hj⟩ ⟨c, hc⟩)
        (leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) c) +
      (ξ.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) c := by apply _root_.YangMills.SharedProofs.p457 <;> assumption
private theorem transport_opposite (hT : TowerFacts L n k) (X : ChainPoint L n k)
    (ξ : LevelForms L n k) : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      tangentTransport X ξ j b.opposite = -tangentTransport X ξ j b := by
  intro j hj b
  cases j with
  | zero => exact ξ.1.2.2 b
  | succ j =>
    have hj' : j < k := hj
    rw [tangentTransport, dif_pos hj']
    exact extendOddly_opposite hT hj _ b
private theorem levelField_opposite (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : ¬c.IsPositivelyOriented) (hc' : c.opposite.IsPositivelyOriented) :
    levelField X (j + 1) c = (levelField X (j + 1) c.opposite)⁻¹ := by
  rw [levelField_succ_neg X hj c hc hc', levelField_succ_pos X hj c.opposite hc']
private def NearOneBounds (L n k : ℕ) (ρ : ℝ) : Prop :=
  ∀ j, j < k → ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ) → ∀ c : Edge L n k (j + 1),
      c.IsPositivelyOriented →
      meanRadius V c ≠ 0 ∧ ‖meanRadius V c - 1‖ < 1 / 2 ∧
      ComplexMatrix2.operatorNorm (normalizedMean V c - 1) < 1 / 2 ∧
      normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup ∧
      ∃ D : (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2,
        ∀ (g : Edge L n k j → ComplexMatrix2)
        (γ : ℝ → Edge L n k j → ComplexMatrix2), γ 0 = V →
        (∀ b, HasDerivAt (fun t => γ t b) (g b) 0) →
          HasDerivAt (fun t => normalizedMean (γ t) c) (D g) 0
private theorem mem_fieldsIn_of_mem {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_fieldsIn_of_mem <;> assumption
private theorem det_of_compact {g : ComplexMatrix2} (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    Matrix.det g = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
private theorem isUnit_det_of_eq_one {g : ComplexMatrix2} (h : Matrix.det g = 1) :
    IsUnit (Matrix.det g) := by apply _root_.YangMills.SharedProofs.p11557 <;> assumption
private theorem expMove_zero {X : ChainPoint L n k}
    (hX : X.fine ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup) (η : LevelForms L n k) :
    expMove ((0 : ℝ) • η) X = X := by apply _root_.YangMills.SharedProofs.p18865 <;> assumption
private theorem transport_identity (n u D ν : ComplexMatrix2) (hn : n⁻¹ * n = 1)
    (hu : u⁻¹ * u = 1) :
    Complex.I • (ComplexMatrix2.conjugateBy n (Complex.I⁻¹ • (D * u⁻¹)) + ν) * (n * u) =
      (Complex.I • ν * n) * u + n * D := by apply _root_.YangMills.SharedProofs.p26677 <;> assumption
private theorem leftDifferential_eq (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {j : ℕ} {V M : Edge L n k j → ComplexMatrix2} {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) {D : ComplexMatrix2}
    (h2 : HasDerivAt (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist (t • M) V) c) D 0)
    (h0 : normalizedMean (PeriodicLattice.expTwist ((0 : ℝ) • M) V) c = normalizedMean V c)
    (hu : Matrix.det (normalizedMean V c) = 1) :
    leftDifferential normalizedMean V M c = Complex.I⁻¹ • (D * (normalizedMean V c)⁻¹) := by apply _root_.YangMills.SharedProofs.p13783 <;> assumption
private theorem hasDerivAt_levelField_expMove
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n k) {ρ : ℝ} (hρ : NearOneBounds L n k ρ) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    (hnear : ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ)
    (η : LevelForms L n k) : ∀ j, j ≤ k → ∀ b,
      HasDerivAt (fun t : ℝ => levelField (expMove (t • η) X) j b)
        (velocity (levelField X j) (tangentTransport X η j) b) 0 := by
  have hX0 : X.fine ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup :=
    mem_fieldsIn_of_mem (hX.2 0 (Nat.zero_le _))
  have hY0 := expMove_zero hX0 η
  intro j
  induction j with
  | zero =>
    intro _ b
    exact hasDerivAt_expTwist_line hX0 η.1.2.2 b
  | succ j ih =>
    intro h
    have hj : j < k := h
    have ih' := ih hj.le
    have hWc := mem_fieldsIn_of_mem (hX.2 j hj.le)
    have hMa := transport_opposite hT X η j hj.le
    have hW1 : ∀ c : Edge L n k (j + 1), Matrix.det (levelField X (j + 1) c) = 1 :=
      det_eq_one_of_mem (mem_fieldsIn_of_mem (hX.2 (j + 1) hj))
    have pos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        HasDerivAt (fun t : ℝ => levelField (expMove (t • η) X) (j + 1) c)
          (Complex.I • tangentTransport X η (j + 1) c * levelField X (j + 1) c) 0 := by
      intro c hc
      obtain ⟨-, -, -, hu, D, hD⟩ := hρ j hj _ hWc (hnear j hj.le) c hc
      have h1 := hD _ (fun t => levelField (expMove (t • η) X) j) (by simp only [hY0]) ih'
      have h0 : PeriodicLattice.expTwist ((0 : ℝ) • tangentTransport X η j) (levelField X j) =
          levelField X j := by
        rw [zero_smul]
        exact expTwist_zero hWc
      have h2 := hD _ (fun t => PeriodicLattice.expTwist (t • tangentTransport X η j)
        (levelField X j)) h0 (fun b => hasDerivAt_expTwist_line hWc hMa b)
      have hmd := leftDifferential_eq hd hc h2 (by rw [h0]) hu
      have hn : HasDerivAt (fun t : ℝ => (expMove (t • η) X).noise ⟨j, hj⟩ ⟨c, hc⟩)
          (Complex.I • (η.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) c *
            X.noise ⟨j, hj⟩ ⟨c, hc⟩) 0 :=
        (hasDerivAt_expLine _).mul_const _
      have hp := hn.mul h1
      have e : (fun t : ℝ => levelField (expMove (t • η) X) (j + 1) c) =
          fun t : ℝ => (expMove (t • η) X).noise ⟨j, hj⟩ ⟨c, hc⟩ *
            normalizedMean (levelField (expMove (t • η) X) j) c := by
        funext t
        exact levelField_succ_pos _ hj c hc
      rw [e]
      refine hp.congr_deriv ?_
      simp only [hY0]
      rw [transport_succ_pos X η hj c hc, levelField_succ_pos X hj c hc, hmd]
      exact (transport_identity _ _ _ _
        (Matrix.nonsing_inv_mul _ (isUnit_det_of_eq_one (det_of_compact (hX.1 _ _))))
        (Matrix.nonsing_inv_mul _ (isUnit_det_of_eq_one hu))).symm
    intro b
    by_cases hb : b.IsPositivelyOriented
    · simp only [velocity, if_pos hb]
      exact pos b hb
    · have hb' : b.opposite.IsPositivelyOriented := (oriented_or_opposite b).resolve_left hb
      have e : (fun t : ℝ => levelField (expMove (t • η) X) (j + 1) b) =
          fun t : ℝ => (levelField (expMove (t • η) X) (j + 1) b.opposite)⁻¹ := by
        funext t
        exact levelField_opposite _ hj b hb hb'
      rw [e]
      have hdet : Matrix.det ((fun t : ℝ => levelField (expMove (t • η) X) (j + 1) b.opposite) 0)
          = 1 := by
        simp only [hY0]
        exact hW1 _
      refine (hasDerivAt_inv_of_det_one hd (pos b.opposite hb') hdet).congr_deriv ?_
      simp only [hY0, velocity, if_neg hb]
      rw [levelField_opposite X hj b hb hb', transport_opposite hT X η (j + 1) hj b]
      have hA : levelField X (j + 1) b.opposite * (levelField X (j + 1) b.opposite)⁻¹ = 1 :=
        Matrix.mul_nonsing_inv _ (isUnit_det_of_eq_one (hW1 _))
      simp only [smul_neg, mul_neg, neg_mul, neg_neg]
      rw [mul_assoc ((levelField X (j + 1) b.opposite)⁻¹), mul_assoc (Complex.I • _), hA, mul_one]
end Movement
section Real
private def IsQuaternionic (A : ComplexMatrix2) : Prop :=
  A 1 1 = (starRingEnd ℂ) (A 0 0) ∧ A 1 0 = -(starRingEnd ℂ) (A 0 1)
private theorem isQuaternionic_of_compact {A : ComplexMatrix2}
    (h : A ∈ PeriodicLattice.compactGaugeGroup) : IsQuaternionic A := by
  obtain ⟨h1, h2⟩ := Matrix.mem_specialUnitaryGroup_iff.mp h
  have hu : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp h1
  have e : Matrix.adjugate A = star A := by
    calc Matrix.adjugate A = Matrix.adjugate A * (A * star A) := by rw [hu, mul_one]
      _ = (Matrix.adjugate A * A) * star A := by rw [mul_assoc]
      _ = star A := by rw [Matrix.adjugate_mul, h2, one_smul, one_mul]
  rw [Matrix.adjugate_fin_two] at e
  have e00 := congrFun (congrFun e 0) 0
  have e10 := congrFun (congrFun e 0) 1
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at e00 e10
  refine ⟨e00, ?_⟩
  rw [neg_eq_iff_eq_neg] at e10
  rw [e10]
  simp
private theorem inv_mem_compact {A : ComplexMatrix2} (h : A ∈ PeriodicLattice.compactGaugeGroup) :
    A⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
variable {L n k j : ℕ}
private theorem normalizedMean_mem_compact [Finite (Vertex L n k j)]
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1))
    (hu : Matrix.det (normalizedMean V c) = 1) :
    normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p11178 <;> assumption
private theorem expTwist_mem_fieldSpace (hT : TowerFacts L n k) (hj : j ≤ k)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (M : edgeFormSpace L n k j) (t : ℝ) :
    PeriodicLattice.expTwist (t • (M : Edge L n k j → ComplexMatrix2)) V ∈ fieldSpace L n k j := by
  have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • ((t • (M : Edge L n k j → ComplexMatrix2)) b)) * V b ∈
        PeriodicLattice.compactGaugeGroup := by
    intro b hb
    have h := ((hT.leftExp j hj).1 V hV (M : Edge L n k j → ComplexMatrix2) M.2 ⟨b, hb⟩).1 t
    have e : ((t : ℂ) • (M : Edge L n k j → ComplexMatrix2) b) =
        (t • (M : Edge L n k j → ComplexMatrix2)) b :=
      Complex.coe_smul _ _
    simp only [leftExpMul, LatticeData.onPositive, finiteData] at h
    rwa [e] at h
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb]
      exact hpos b hb
    · simp only [PeriodicLattice.expTwist, if_neg hb]
      exact inv_mem_compact (hpos _ ((oriented_or_opposite b).resolve_left hb))
  · by_cases hb : b.IsPositivelyOriented
    · have hb' := hT.not_both j hj b hb
      simp only [PeriodicLattice.expTwist, if_pos hb, if_neg hb', edge_opposite_opposite]
    · have hb' : b.opposite.IsPositivelyOriented := (oriented_or_opposite b).resolve_left hb
      simp only [PeriodicLattice.expTwist, if_pos hb', if_neg hb]
      rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_eq_one (det_of_compact (hpos _ hb')))]
end Real
section Top
variable {L n k j : ℕ}
private theorem expTwist_line_near (hT : TowerFacts L n k) (hj : j ≤ k)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (M : edgeFormSpace L n k j) {ρ : ℝ}
    (hnear : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ b, ComplexMatrix2.operatorNorm
      (PeriodicLattice.expTwist (t • (M : Edge L n k j → ComplexMatrix2)) V b - 1) < ρ := by
  haveI := hT.edges_finite j hj
  have hc := mem_fieldsIn_of_mem hV
  have h : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ b, ComplexMatrix2.operatorNorm
      (PeriodicLattice.expTwist (t • (M : Edge L n k j → ComplexMatrix2)) V b - 1) < ρ := by
    refine Filter.eventually_all.mpr fun b => ?_
    have h1 := (hasDerivAt_expTwist_line hc M.2.2 b).continuousAt
    have h2 : Tendsto (fun t : ℝ =>
        ‖PeriodicLattice.expTwist (t • (M : Edge L n k j → ComplexMatrix2)) V b - 1‖)
        (𝓝 0) (𝓝 ‖V b - 1‖) := by
      have h3 := ((h1.tendsto.sub_const (1 : ComplexMatrix2)).norm)
      simpa only [zero_smul, expTwist_zero hc] using h3
    exact h2.eventually_lt_const (hnear b)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨δ, hδ, fun t ht => hh (by simpa [Real.dist_eq] using ht)⟩
private theorem leftDifferential_mem (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n k) {ρ : ℝ} (hρ : NearOneBounds L n k ρ) (hj : j < k)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j)
    (hnear : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ) (M : edgeFormSpace L n k j)
    (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    leftDifferential normalizedMean V (M : Edge L n k j → ComplexMatrix2) c ∈
      ComplexMatrix2.hermitianTraceless := by
  obtain ⟨δ, hδ, hh⟩ := expTwist_line_near hT hj.le hV M hnear
  have hWc := mem_fieldsIn_of_mem hV
  obtain ⟨-, -, -, hu, D, hD⟩ := hρ j hj _ hWc hnear c hc
  have h0 : PeriodicLattice.expTwist ((0 : ℝ) • (M : Edge L n k j → ComplexMatrix2)) V = V := by
    rw [zero_smul]
    exact expTwist_zero hWc
  have h2 := hD _ (fun t => PeriodicLattice.expTwist (t • (M : Edge L n k j → ComplexMatrix2)) V) h0
    (fun b => hasDerivAt_expTwist_line hWc M.2.2 b)
  rw [leftDifferential_eq hd hc h2 (by rw [h0]) hu]
  haveI := hT.sites_finite j hj.le
  have hI : IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) δ) := by
    refine ⟨Metric.isOpen_ball, ?_, Metric.mem_ball_self hδ⟩
    rw [Real.ball_eq_Ioo]
    exact Set.ordConnected_Ioo
  have hmaps : MapsTo (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist
      (t • (M : Edge L n k j → ComplexMatrix2)) V) c) (Metric.ball (0 : ℝ) δ)
      PeriodicLattice.compactGaugeGroup := by
    intro t ht
    have ht' : |t| < δ := by simpa [Real.dist_eq] using ht
    have hr := expTwist_mem_fieldSpace hT hj.le hV M t
    exact normalizedMean_mem_compact hr c
      (hρ j hj _ (mem_fieldsIn_of_mem hr) (hh t ht') c hc).2.2.2.1
  have hl := (hT.curveLogs _ hI _ hmaps h2.differentiableAt).2.2.2
  rw [h2.deriv] at hl
  simp only [h0] at hl
  exact hl
private theorem conjugateBy_mem {g A : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy g A ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p2904 <;> assumption
private theorem velocity_add (V M M' : Edge L n k j → ComplexMatrix2) :
    velocity V (M + M') = velocity V M + velocity V M' := by apply _root_.YangMills.DeltaSharedProofs.p501277 <;> assumption
private theorem velocity_smul (V M : Edge L n k j → ComplexMatrix2) (r : ℝ) :
    velocity V (r • M) = r • velocity V M := by apply _root_.YangMills.DeltaSharedProofs.p500676 <;> assumption
private theorem exists_transport_linearMap
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n k) {ρ : ℝ} (hρ : NearOneBounds L n k ρ) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    (hnear : ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ) :
    ∀ j, j ≤ k → ∃ T : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k j,
      ∀ ξ, (T ξ : Edge L n k j → ComplexMatrix2) = tangentTransport X ξ j := by
  intro j
  induction j with
  | zero => exact fun _ => ⟨LinearMap.fst ℝ _ _, fun _ => rfl⟩
  | succ j ih =>
    intro h
    have hj : j < k := h
    obtain ⟨T, hTv⟩ := ih hj.le
    have hWr := hX.2 j hj.le
    have hWc := mem_fieldsIn_of_mem hWr
    have hmem : ∀ ξ : LevelForms L n k,
        tangentTransport X ξ (j + 1) ∈ edgeFormSpace L n k (j + 1) := by
      intro ξ
      refine ⟨fun b hb => ?_, transport_opposite hT X ξ (j + 1) hj⟩
      rw [transport_succ_pos X ξ hj b hb, ← hTv ξ]
      exact ComplexMatrix2.hermitianTraceless.add_mem (conjugateBy_mem (hX.1 _ _)
        (leftDifferential_mem hd hT hρ hj hWr (hnear j hj.le) (T ξ) b hb))
        ((ξ.2 ⟨j, hj⟩).2.1 b hb)
    have hform : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        ∃ Λ : (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2, ∀ ξ : LevelForms L n k,
          tangentTransport X ξ (j + 1) c = Λ (velocity (levelField X j) (tangentTransport X ξ j)) +
            (ξ.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) c := by
      intro c hc
      obtain ⟨-, -, -, hu, D, hD⟩ := hρ j hj _ hWc (hnear j hj.le) c hc
      let Λ : (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2 :=
        { toFun := fun Y => ComplexMatrix2.conjugateBy (X.noise ⟨j, hj⟩ ⟨c, hc⟩)
            (Complex.I⁻¹ • (D Y * (normalizedMean (levelField X j) c)⁻¹))
          map_add' := fun Y Y' => by
            simp only [ComplexMatrix2.conjugateBy, map_add, add_mul, mul_add, smul_add]
          map_smul' := fun r Y => by
            simp only [ComplexMatrix2.conjugateBy, map_smul, smul_mul_assoc, mul_smul_comm,
              RingHom.id_apply]
            rw [smul_comm] }
      refine ⟨Λ, fun ξ => ?_⟩
      have hMa := transport_opposite hT X ξ j hj.le
      have h0 : PeriodicLattice.expTwist ((0 : ℝ) • tangentTransport X ξ j) (levelField X j) =
          levelField X j := by
        rw [zero_smul]
        exact expTwist_zero hWc
      have h2 := hD _ (fun t => PeriodicLattice.expTwist (t • tangentTransport X ξ j)
        (levelField X j)) h0 (fun b => hasDerivAt_expTwist_line hWc hMa b)
      rw [transport_succ_pos X ξ hj c hc, leftDifferential_eq hd hc h2 (by rw [h0]) hu]
      rfl
    have hadd : ∀ ξ ξ' : LevelForms L n k,
        tangentTransport X (ξ + ξ') (j + 1) =
          tangentTransport X ξ (j + 1) + tangentTransport X ξ' (j + 1) := by
      intro ξ ξ'
      have hp : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
          tangentTransport X (ξ + ξ') (j + 1) c =
          tangentTransport X ξ (j + 1) c + tangentTransport X ξ' (j + 1) c := by
        intro c hc
        obtain ⟨Λ, hΛ⟩ := hform c hc
        rw [hΛ, hΛ, hΛ, ← hTv, ← hTv, ← hTv, map_add, Submodule.coe_add, velocity_add, map_add]
        simp only [Prod.snd_add, Pi.add_apply, Submodule.coe_add]
        abel
      funext c
      by_cases hc : c.IsPositivelyOriented
      · exact hp c hc
      · have hc' := (oriented_or_opposite c).resolve_left hc
        have e := fun ξ'' : LevelForms L n k =>
          transport_opposite hT X ξ'' (j + 1) hj c.opposite
        rw [edge_opposite_opposite] at e
        rw [Pi.add_apply, e, e, e, hp _ hc']
        abel
    have hsmul : ∀ (r : ℝ) (ξ : LevelForms L n k),
        tangentTransport X (r • ξ) (j + 1) = r • tangentTransport X ξ (j + 1) := by
      intro r ξ
      have hp : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
          tangentTransport X (r • ξ) (j + 1) c = r • tangentTransport X ξ (j + 1) c := by
        intro c hc
        obtain ⟨Λ, hΛ⟩ := hform c hc
        rw [hΛ, hΛ, ← hTv, ← hTv, map_smul, Submodule.coe_smul, velocity_smul, map_smul, smul_add]
        simp only [Prod.smul_snd, Pi.smul_apply, Submodule.coe_smul]
      funext c
      by_cases hc : c.IsPositivelyOriented
      · exact hp c hc
      · have hc' := (oriented_or_opposite c).resolve_left hc
        have e := fun ξ'' : LevelForms L n k =>
          transport_opposite hT X ξ'' (j + 1) hj c.opposite
        rw [edge_opposite_opposite] at e
        rw [Pi.smul_apply, e, e, hp _ hc', smul_neg]
    exact ⟨{ toFun := fun ξ => ⟨tangentTransport X ξ (j + 1), hmem ξ⟩
             map_add' := fun ξ ξ' => Subtype.ext (hadd ξ ξ')
             map_smul' := fun r ξ => Subtype.ext (hsmul r ξ) }, fun _ => rfl⟩
private theorem topDeriv_eq (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n k) {ρ : ℝ} (hρ : NearOneBounds L n k ρ) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    (hnear : ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ)
    (ξ : LevelForms L n k) :
    (topDeriv X ξ : Edge L n k k → ComplexMatrix2) = tangentTransport X ξ k := by
  obtain ⟨T, hTv⟩ := exists_transport_linearMap hd hT hρ hX hnear k le_rfl
  exact Classical.epsilon_spec (p := IsTopDeriv X) ⟨T, hTv⟩ ξ
end Top
section Flat
variable {L n k : ℕ}
private theorem levelField_unitPoint (hT : TowerFacts L n k) : ∀ j, j ≤ k →
    levelField (unitPoint L n k) j = fun _ => 1 := fun j hj =>
  (contDiffAt_levelFields (P := ℝ) (p₀ := 0) (m := 0) hT (X := fun _ => unitPoint L n k)
    (fun _ => contDiffAt_const) (fun _ _ => contDiffAt_const) rfl j hj).2
private theorem const_one_mem {j : ℕ} :
    (fun _ : Edge L n k j => (1 : ComplexMatrix2)) ∈ fieldSpace L n k j :=
  ⟨fun _ _ => ComplexMatrix2.specialUnitary.one_mem, fun _ _ => by simp⟩
private theorem unitPoint_compact (hT : TowerFacts L n k) : IsCompactValued (unitPoint L n k) := by
  refine ⟨fun _ _ => ComplexMatrix2.specialUnitary.one_mem, fun j hj => ?_⟩
  rw [levelField_unitPoint hT j hj]
  exact const_one_mem
private theorem linearTransport_succ (ξ : LevelForms L n k) {j : ℕ} (hj : j < k) :
    linearTransport ξ (j + 1) = linearSmoothing L n k j (linearTransport ξ j) +
      (ξ.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) := by
  rw [linearTransport, dif_pos hj]
private theorem linearTransport_mem (hT : TowerFacts L n k) (ξ : LevelForms L n k) :
    ∀ j, j ≤ k → linearTransport ξ j ∈ edgeFormSpace L n k j := by
  intro j
  induction j with
  | zero => exact fun _ => ξ.1.2
  | succ j ih =>
    intro h
    have hj : j < k := h
    rw [linearTransport_succ ξ hj]
    exact (edgeFormSpace L n k (j + 1)).add_mem (hT.smoothing_mem j hj _ (ih hj.le))
      (ξ.2 ⟨j, hj⟩).2
private theorem conjugateBy_one (A : ComplexMatrix2) : ComplexMatrix2.conjugateBy 1 A = A := by apply _root_.YangMills.Construction.Tower.FullSpace.StepAtTrivial.conjugateBy_one <;> assumption
private theorem transport_unitPoint (hT : TowerFacts L n k) (ξ : LevelForms L n k) :
    ∀ j, j ≤ k → tangentTransport (unitPoint L n k) ξ j = linearTransport ξ j := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    have hp : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        tangentTransport (unitPoint L n k) ξ (j + 1) c = linearTransport ξ (j + 1) c := by
      intro c hc
      rw [transport_succ_pos _ ξ hj c hc, ih hj.le, levelField_unitPoint hT j hj.le,
        linearTransport_succ ξ hj]
      simp only [unitPoint, conjugateBy_one, Pi.add_apply]
      rw [hT.deriv_at_one j hj _ (linearTransport_mem hT ξ j hj.le) c hc]
    funext c
    by_cases hc : c.IsPositivelyOriented
    · exact hp c hc
    · have hc' := (oriented_or_opposite c).resolve_left hc
      have e := transport_opposite hT (unitPoint L n k) ξ (j + 1) hj c.opposite
      rw [edge_opposite_opposite] at e
      have e2 := (linearTransport_mem hT ξ (j + 1) hj).2 c.opposite
      rw [edge_opposite_opposite] at e2
      rw [e, e2, hp _ hc']
end Flat
section Families
variable {L n k : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {m : WithTop ℕ∞}
private theorem contDiffAt_coord {j : ℕ} {p₀ : P} (A : P →ₗ[ℝ] edgeFormSpace L n k j)
    (b : Edge L n k j) :
    ContDiffAt ℝ m (fun p => (A p : Edge L n k j → ComplexMatrix2) b) p₀ :=
  (LinearMap.toContinuousLinearMap
    ((LinearMap.proj b : (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2) ∘ₗ
      (edgeFormSpace L n k j).subtype ∘ₗ A)).contDiff.contDiffAt
private def familyPoint (A C : P →ₗ[ℝ] LevelForms L n k) (p : P) : ChainPoint L n k :=
  expMove (A p) (expMove (C p) (unitPoint L n k))
private def baseSlot : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k 0 := LinearMap.fst ℝ _ _
private def noiseSlotAt (i : Fin k) : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k ((i : ℕ) + 1) :=
  (LinearMap.proj i) ∘ₗ LinearMap.snd ℝ _ _
private theorem familyPoint_zero (hT : TowerFacts L n k) (A C : P →ₗ[ℝ] LevelForms L n k) :
    familyPoint A C 0 = unitPoint L n k := by
  have h1 := mem_fieldsIn_of_mem (const_one_mem (L := L) (n := n) (k := k) (j := 0))
  have e := expMove_zero (X := unitPoint L n k) h1 (0 : LevelForms L n k)
  simp only [smul_zero] at e
  simp only [familyPoint, map_zero]
  rw [e, e]
private theorem contDiffAt_familyPoint_fine (A C : P →ₗ[ℝ] LevelForms L n k) (b : Edge L n k 0) :
    ContDiffAt ℝ m (fun p => (familyPoint A C p).fine b) (0 : P) := by
  have hc : ∀ b', ContDiffAt ℝ m (fun p => PeriodicLattice.expTwist
      ((C p).1 : Edge L n k 0 → ComplexMatrix2) (fun _ => 1) b') (0 : P) := fun b' =>
    contDiffAt_expTwist (A := fun p => ((C p).1 : Edge L n k 0 → ComplexMatrix2))
      (U := fun _ _ => 1)
      (fun b'' => contDiffAt_coord (baseSlot ∘ₗ C) b'') (fun _ => contDiffAt_const)
      (by simp) rfl b'
  refine contDiffAt_expTwist (A := fun p => ((A p).1 : Edge L n k 0 → ComplexMatrix2))
    (U := fun p => PeriodicLattice.expTwist ((C p).1 : Edge L n k 0 → ComplexMatrix2) (fun _ => 1))
    (fun b'' => contDiffAt_coord (baseSlot ∘ₗ A) b'') hc (by simp) ?_ b
  have h1 := mem_fieldsIn_of_mem (const_one_mem (L := L) (n := n) (k := k) (j := 0))
  simp only [map_zero, Prod.fst_zero, ZeroMemClass.coe_zero]
  exact expTwist_zero h1
private theorem contDiffAt_familyPoint_noise (A C : P →ₗ[ℝ] LevelForms L n k) (i : Fin k)
    (c : PositiveEdge L n k ((i : ℕ) + 1)) :
    ContDiffAt ℝ m (fun p => (familyPoint A C p).noise i c) (0 : P) := by
  simp only [familyPoint, expMove, unitPoint]
  exact (contDiffAt_matExp_I (contDiffAt_coord (noiseSlotAt i ∘ₗ A) c.1)).mul
    ((contDiffAt_matExp_I (contDiffAt_coord (noiseSlotAt i ∘ₗ C) c.1)).mul contDiffAt_const)
end Families
section Branch
variable {L n k N : ℕ}
private def chartPoint (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) (w : Fin N → ℝ) :
    ChainPoint L n k :=
  expMove (e w).1 (unitPoint L n k)
private def chartSlot (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) :
    (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k :=
  LinearMap.fst ℝ _ _ ∘ₗ e.toLinearMap
private theorem chartPoint_fine_mem (hT : TowerFacts L n k)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) (w : Fin N → ℝ) :
    (chartPoint e w).fine ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup := by
  have h := expTwist_mem_fieldSpace hT (Nat.zero_le k)
    (const_one_mem (L := L) (n := n) (k := k) (j := 0)) (e w).1.1 1
  rw [one_smul] at h
  exact mem_fieldsIn_of_mem h
private theorem familyPoint_eq_chartPoint (hT : TowerFacts L n k)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) (w : Fin N → ℝ) :
    familyPoint (0 : (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k) (chartSlot e) w = chartPoint e w := by
  have h := expMove_zero (chartPoint_fine_mem hT e w) (0 : LevelForms L n k)
  simp only [smul_zero] at h
  simp only [familyPoint, LinearMap.zero_apply]
  exact h
private theorem chartPoint_levelFields (hT : TowerFacts L n k)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {m : WithTop ℕ∞} : ∀ j, j ≤ k →
      (∀ b, ContDiffAt ℝ m (fun w => levelField (chartPoint e w) j b) (0 : Fin N → ℝ)) ∧
        levelField (chartPoint e 0) j = fun _ => 1 := by
  intro j hj
  have h := contDiffAt_levelFields (p₀ := (0 : Fin N → ℝ)) (m := m) hT
    (X := familyPoint (0 : (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k) (chartSlot e))
    (contDiffAt_familyPoint_fine _ _) (contDiffAt_familyPoint_noise _ _)
    (familyPoint_zero hT _ _) j hj
  simpa only [familyPoint_eq_chartPoint hT e] using h
private theorem eventually_chartPoint_near (hT : TowerFacts L n k)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k)
    {ρ : ℝ} (hρ0 : 0 < ρ) : ∀ᶠ w in 𝓝 (0 : Fin N → ℝ), ∀ j, j ≤ k → ∀ b,
      ComplexMatrix2.operatorNorm (levelField (chartPoint e w) j b - 1) < ρ := by
  have h : ∀ j ∈ Finset.range (k + 1), ∀ᶠ w in 𝓝 (0 : Fin N → ℝ), ∀ b,
      ComplexMatrix2.operatorNorm (levelField (chartPoint e w) j b - 1) < ρ := by
    intro j hj
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    haveI := hT.edges_finite j hj'
    refine Filter.eventually_all.mpr fun b => ?_
    obtain ⟨h1, h2⟩ := chartPoint_levelFields (m := 0) hT e j hj'
    have h3 : Tendsto (fun w => ‖levelField (chartPoint e w) j b - 1‖)
        (𝓝 (0 : Fin N → ℝ)) (𝓝 0) := by
      have h4 := (((h1 b).continuousAt).tendsto.sub_const (1 : ComplexMatrix2)).norm
      simpa [h2] using h4
    exact h3.eventually_lt_const hρ0
  have h' := (Filter.eventually_all_finset _).mpr h
  filter_upwards [h'] with w hw j hj
  exact hw j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
private theorem velocity_one {j : ℕ} (M : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    velocity (fun _ => 1) M b = Complex.I • M b := by
  by_cases hb : b.IsPositivelyOriented <;> simp [velocity, hb]
private theorem hasDerivAt_levelField_chart
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n k) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : NearOneBounds L n k ρ)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {c : ℝ → Fin N → ℝ} (hc0 : c 0 = 0)
    {t : LevelTriple L n k} (hcd : HasDerivAt c (e.symm t) 0) (j : ℕ) (hj : j ≤ k)
    (b : Edge L n k j) :
    HasDerivAt (fun s => levelField (chartPoint e (c s)) j b)
      (Complex.I • linearTransport t.1 j b) 0 := by
  obtain ⟨h1, h2⟩ := chartPoint_levelFields (m := 2) hT e j hj
  have hdiff : HasFDerivAt (fun w => levelField (chartPoint e w) j b)
      (fderiv ℝ (fun w => levelField (chartPoint e w) j b) 0) 0 :=
    ((h1 b).differentiableAt (by norm_num)).hasFDerivAt
  have hF : HasFDerivAt (fun w => levelField (chartPoint e w) j b)
      (fderiv ℝ (fun w => levelField (chartPoint e w) j b) 0) (c 0) := by
    rw [hc0]
    exact hdiff
  have hcurve : HasDerivAt (fun s => levelField (chartPoint e (c s)) j b)
      (fderiv ℝ (fun w => levelField (chartPoint e w) j b) 0 (e.symm t)) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) hF hcd
  have hline : HasDerivAt (fun τ : ℝ => levelField (chartPoint e (τ • e.symm t)) j b)
      (fderiv ℝ (fun w => levelField (chartPoint e w) j b) 0 (e.symm t)) 0 := by
    have hl : HasDerivAt (fun τ : ℝ => τ • e.symm t) (e.symm t) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (e.symm t)
    have hF' : HasFDerivAt (fun w => levelField (chartPoint e w) j b)
        (fderiv ℝ (fun w => levelField (chartPoint e w) j b) 0) ((0 : ℝ) • e.symm t) := by
      rw [zero_smul]
      exact hdiff
    exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hF' hl
  have hflat : ∀ j, j ≤ k → ∀ b,
      ComplexMatrix2.operatorNorm (levelField (unitPoint L n k) j b - 1) < ρ := by
    intro j hj b
    rw [levelField_unitPoint hT j hj]
    simpa using hρ0
  have hmv := hasDerivAt_levelField_expMove hd hT hρ (unitPoint_compact hT) hflat t.1 j hj b
  have e1 : (fun τ : ℝ => levelField (chartPoint e (τ • e.symm t)) j b) =
      fun τ : ℝ => levelField (expMove (τ • t.1) (unitPoint L n k)) j b := by
    funext τ
    simp only [chartPoint, map_smul, LinearEquiv.apply_symm_apply, Prod.smul_fst]
  rw [e1] at hline
  have e2 := hline.unique hmv
  rw [e2, levelField_unitPoint hT j hj, transport_unitPoint hT t.1 j hj, velocity_one] at hcurve
  exact hcurve
end Branch
section Products
private theorem hasDerivAt_mul_of_left_zero {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {f g : ℝ → 𝔸} {f' g₀ : 𝔸} (hf0 : f 0 = 0) (hf : HasDerivAt f f' 0)
    (hg : Tendsto g (𝓝 0) (𝓝 g₀)) : HasDerivAt (fun s => f s * g s) (f' * g₀) 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hf ⊢
  have h := hf.mul (hg.mono_left nhdsWithin_le_nhds)
  refine h.congr' ?_
  filter_upwards with s
  simp only [slope, vsub_eq_sub, hf0, zero_mul, sub_zero, smul_mul_assoc]
abbrev _root_.YangMills.SharedProofs.p10857 := @hasDerivAt_mul_of_left_zero
private def reHalfTrace : ComplexMatrix2 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (ComplexMatrix2.halfTrace A).re
      map_add' := fun A B => by
        simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_add, mul_add]
      map_smul' := fun r A => by
        have e : r • A = (r : ℂ) • A := (Complex.coe_smul r A).symm
        simp only [RingHom.id_apply, smul_eq_mul, ComplexMatrix2.halfTrace,
          ComplexMatrix2.fullTrace]
        rw [e, Matrix.trace_smul, smul_eq_mul, mul_left_comm, Complex.re_ofReal_mul] }
private theorem reHalfTrace_apply (A : ComplexMatrix2) :
    reHalfTrace A = (ComplexMatrix2.halfTrace A).re := rfl
variable {L n k j : ℕ}
private theorem re_edgeFormPairing [Fintype (PositiveEdge L n k j)]
    (X Y : Edge L n k j → ComplexMatrix2) :
    (edgeFormPairing X Y).re = ∑ c : PositiveEdge L n k j, reHalfTrace (X c * Y c) := by
  simp only [edgeFormPairing, traceFinsumPairing, restrictToPositiveEdges]
  rw [finsum_eq_sum_of_fintype, Complex.re_sum]
  rfl
end Products
section Partials
variable {L n k N : ℕ}
private def lineMap (η : LevelForms L n k) : ((Fin N → ℝ) × ℝ) →ₗ[ℝ] LevelForms L n k :=
  (LinearMap.toSpanSingleton ℝ _ η) ∘ₗ LinearMap.snd ℝ _ _
private def chartSlotFst (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) :
    ((Fin N → ℝ) × ℝ) →ₗ[ℝ] LevelForms L n k :=
  chartSlot e ∘ₗ LinearMap.fst ℝ _ _
private theorem exists_meanRadius_partial (hT : TowerFacts L n k)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k)
    (η : LevelForms L n k) {i : ℕ} (hi : i < k) (c : Edge L n k (i + 1))
    (hc : c.IsPositivelyOriented) :
    ∃ G : (Fin N → ℝ) → ℝ, ContinuousAt G 0 ∧ ∀ᶠ w in 𝓝 (0 : Fin N → ℝ),
      HasDerivAt (fun τ : ℝ => (meanRadius (levelField (expMove (τ • η) (chartPoint e w)) i) c).re)
        (G w) 0 := by
  have h := contDiffAt_levelRadius (p₀ := (((0 : Fin N → ℝ), (0 : ℝ)) : (Fin N → ℝ) × ℝ))
    (m := 2) hT
    (X := familyPoint (lineMap η) (chartSlotFst e)) (contDiffAt_familyPoint_fine _ _)
    (contDiffAt_familyPoint_noise _ _) (familyPoint_zero hT _ _) hi c hc
  exact exists_partialDeriv_snd (Complex.reCLM.contDiff.contDiffAt.comp _ h)
private theorem hasDerivAt_coord (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {c : ℝ → Fin N → ℝ}
    {t : LevelTriple L n k} (hcd : HasDerivAt c (e.symm t) 0) {j : ℕ}
    (ℓ : LevelTriple L n k →ₗ[ℝ] edgeFormSpace L n k j) (b : Edge L n k j) :
    HasDerivAt (fun s => (ℓ (e (c s)) : Edge L n k j → ComplexMatrix2) b)
      ((ℓ t : Edge L n k j → ComplexMatrix2) b) 0 := by
  let A : (Fin N → ℝ) →L[ℝ] ComplexMatrix2 := LinearMap.toContinuousLinearMap
    ((LinearMap.proj b : (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2) ∘ₗ
      (edgeFormSpace L n k j).subtype ∘ₗ ℓ ∘ₗ e.toLinearMap)
  have h := A.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcd
  have e1 : A (e.symm t) = (ℓ t : Edge L n k j → ComplexMatrix2) b := by
    simp [A]
  rw [e1] at h
  exact h
abbrev _root_.YangMills.SharedProofs.p21944 := @hasDerivAt_coord
end Partials
section Multiplier
variable {L n k N : ℕ}
private theorem chartPoint_zero (hT : TowerFacts L n k) (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) :
    chartPoint e 0 = unitPoint L n k := by
  have h1 := mem_fieldsIn_of_mem (const_one_mem (L := L) (n := n) (k := k) (j := 0))
  have h := expMove_zero (X := unitPoint L n k) h1 (0 : LevelForms L n k)
  simp only [smul_zero] at h
  simp only [chartPoint, map_zero, Prod.fst_zero]
  exact h
private theorem unitPoint_near (hT : TowerFacts L n k) {ρ : ℝ} (hρ0 : 0 < ρ) :
    ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField (unitPoint L n k) j b - 1) < ρ := by
  intro j hj b
  rw [levelField_unitPoint hT j hj]
  simpa using hρ0
end Multiplier
section Action
variable {L n k j : ℕ}
private def holonomyDeriv (U M : Edge L n k j → ComplexMatrix2) :
    List (Edge L n k j) → ComplexMatrix2
  | [] => 0
  | b :: Γ => velocity U M b * PeriodicLattice.pathHolonomy U Γ + U b * holonomyDeriv U M Γ
private theorem pathHolonomy_cons (U : Edge L n k j → ComplexMatrix2) (b : Edge L n k j)
    (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy U (b :: Γ) = U b * PeriodicLattice.pathHolonomy U Γ := by
  simp [PeriodicLattice.pathHolonomy]
private theorem sumAlong_cons (A : Edge L n k j → ComplexMatrix2) (b : Edge L n k j)
    (Γ : List (Edge L n k j)) :
    PeriodicLattice.bondFormSumAlong A (b :: Γ) = A b + PeriodicLattice.bondFormSumAlong A Γ := by
  simp [PeriodicLattice.bondFormSumAlong]
private theorem hasDerivAt_pathHolonomy_twist {U M : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hM : ∀ b, M b.opposite = -M b) (Γ : List (Edge L n k j)) :
    HasDerivAt (fun τ : ℝ =>
      PeriodicLattice.pathHolonomy (PeriodicLattice.expTwist (τ • M) U) Γ)
      (holonomyDeriv U M Γ) 0 := by
  induction Γ with
  | nil => exact hasDerivAt_const _ _
  | cons b Γ ih =>
    simp only [pathHolonomy_cons]
    refine ((hasDerivAt_expTwist_line hU hM b).mul ih).congr_deriv ?_
    simp only [zero_smul, expTwist_zero hU, holonomyDeriv]
private theorem hasDerivAt_pathHolonomy_curve {U : ℝ → Edge L n k j → ComplexMatrix2}
    {Ξ : Edge L n k j → ComplexMatrix2}
    (h0 : U 0 = fun _ => 1) (hU : ∀ b, HasDerivAt (fun s => U s b) (Complex.I • Ξ b) 0)
    (Γ : List (Edge L n k j)) :
    HasDerivAt (fun s => PeriodicLattice.pathHolonomy (U s) Γ)
      (Complex.I • PeriodicLattice.bondFormSumAlong Ξ Γ) 0 := by
  induction Γ with
  | nil =>
    simp only [PeriodicLattice.bondFormSumAlong, List.map_nil, List.sum_nil, smul_zero]
    exact hasDerivAt_const _ _
  | cons b Γ ih =>
    simp only [pathHolonomy_cons]
    refine ((hU b).mul ih).congr_deriv ?_
    rw [h0, pathHolonomy_const_one, sumAlong_cons, smul_add]
    simp
abbrev _root_.YangMills.SharedProofs.p5333 := @hasDerivAt_pathHolonomy_curve
private theorem holonomyDeriv_one (M : Edge L n k j → ComplexMatrix2) (Γ : List (Edge L n k j)) :
    holonomyDeriv (fun _ => 1) M Γ = Complex.I • PeriodicLattice.bondFormSumAlong M Γ := by
  induction Γ with
  | nil => simp [holonomyDeriv, PeriodicLattice.bondFormSumAlong]
  | cons b Γ ih =>
    simp only [holonomyDeriv, ih, velocity_one, pathHolonomy_const_one, sumAlong_cons, smul_add]
    simp
private theorem exists_deriv_holonomyDeriv {U : ℝ → Edge L n k j → ComplexMatrix2}
    {M Ξ : Edge L n k j → ComplexMatrix2}
    (h0 : U 0 = fun _ => 1) (hU : ∀ b, HasDerivAt (fun s => U s b) (Complex.I • Ξ b) 0)
    (Γ : List (Edge L n k j)) :
    ∃ R, HasDerivAt (fun s => holonomyDeriv (U s) M Γ) R 0 ∧ ComplexMatrix2.fullTrace R =
      ComplexMatrix2.fullTrace (-(PeriodicLattice.bondFormSumAlong M Γ *
        PeriodicLattice.bondFormSumAlong Ξ Γ)) := by
  induction Γ with
  | nil =>
    refine ⟨0, hasDerivAt_const _ _, ?_⟩
    simp [PeriodicLattice.bondFormSumAlong, ComplexMatrix2.fullTrace]
  | cons b Γ ih =>
    obtain ⟨R, hR, htr⟩ := ih
    have hv : ∃ Rv, HasDerivAt (fun s => velocity (U s) M b) Rv 0 ∧
        ComplexMatrix2.fullTrace Rv = ComplexMatrix2.fullTrace (-(M b * Ξ b)) := by
      by_cases hb : b.IsPositivelyOriented
      · refine ⟨(Complex.I • M b) * (Complex.I • Ξ b), ?_, ?_⟩
        · simp only [velocity, if_pos hb]
          exact (hU b).const_mul _
        · simp only [ComplexMatrix2.fullTrace, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
            Complex.I_mul_I, neg_smul, one_smul]
      · refine ⟨(Complex.I • Ξ b) * (Complex.I • M b), ?_, ?_⟩
        · simp only [velocity, if_neg hb]
          exact (hU b).mul_const _
        · simp only [ComplexMatrix2.fullTrace, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
            Complex.I_mul_I, neg_smul, one_smul]
          rw [Matrix.trace_neg, Matrix.trace_neg, Matrix.trace_mul_comm]
    obtain ⟨Rv, hRv, hvtr⟩ := hv
    have hQ := (hRv.mul (hasDerivAt_pathHolonomy_curve h0 hU Γ)).add ((hU b).mul hR)
    refine ⟨_, hQ, ?_⟩
    simp only [h0, pathHolonomy_const_one, holonomyDeriv_one, velocity_one, mul_one, one_mul,
      sumAlong_cons]
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, smul_smul, Complex.I_mul_I, neg_smul, one_smul, add_mul, mul_add,
      Matrix.trace_neg, neg_add_rev] at hvtr htr ⊢
    rw [hvtr, htr, Matrix.trace_mul_comm (PeriodicLattice.bondFormSumAlong Ξ Γ |> fun _ => Ξ b)
      (PeriodicLattice.bondFormSumAlong M Γ)]
    ring
end Action
section Gradient
variable {L n k N : ℕ}
private theorem reHalfTrace_eq (X : ComplexMatrix2) :
    reHalfTrace X = 1 / 2 * (ComplexMatrix2.fullTrace X).re := by
  rw [reHalfTrace_apply, ComplexMatrix2.halfTrace, Complex.mul_re]
  simp
private theorem reHalfTrace_mul_comm (A B : ComplexMatrix2) :
    reHalfTrace (A * B) = reHalfTrace (B * A) := by
  rw [reHalfTrace_eq, reHalfTrace_eq, ComplexMatrix2.fullTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_mul_comm]
private theorem reHalfTrace_I_smul {Z : ComplexMatrix2} (hZ : Z ∈ ComplexMatrix2.hermitianTraceless) :
    reHalfTrace (Complex.I • Z) = 0 := by
  rw [reHalfTrace_eq]
  simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul]
  have h := hZ.2
  simp only [ComplexMatrix2.fullTrace] at h
  rw [h]
  simp
private theorem neg_reHalfTrace_I_I (A B : ComplexMatrix2) :
    -reHalfTrace (Complex.I • A * Complex.I • B) = reHalfTrace (A * B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_smul, one_smul, map_neg,
    neg_neg]
private theorem traceDefect_eq (g : ComplexMatrix2) : traceDefect g = 1 - reHalfTrace g := rfl
private theorem hasDerivAt_traceDefect_line (ν Y : ComplexMatrix2) :
    HasDerivAt (fun τ : ℝ => traceDefect (ComplexMatrix2.matExp (Complex.I • (τ • ν)) * Y))
      (-reHalfTrace (Complex.I • ν * Y)) 0 := by
  simp only [traceDefect_eq]
  have h := reHalfTrace.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_expLine ν).mul_const Y)
  exact h.const_sub 1
private theorem sumAlong_boundary {A : Edge L n k 0 → ComplexMatrix2}
    (hA : ∀ b, A b.opposite = -A b) (p : Face L n k 0) :
    PeriodicLattice.bondFormSumAlong A p.boundaryBonds = edgeCoboundary A p := by
  simp only [PeriodicLattice.bondFormSumAlong, PeriodicLattice.Plaquette.boundaryBonds,
    edgeCoboundary, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hA, add_zero]
  abel
private theorem hasDerivAt_plaquetteAction [Fintype (Face L n k 0)]
    {U M : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup)
    (hM : ∀ b, M b.opposite = -M b) :
    HasDerivAt (fun τ : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist (τ • M) U))
      (∑ p : Face L n k 0, -reHalfTrace (holonomyDeriv U M p.boundaryBonds)) 0 := by
  have e : (fun τ : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist (τ • M) U)) =
      fun τ : ℝ => ∑ p : Face L n k 0,
        (1 - reHalfTrace (PeriodicLattice.pathHolonomy (PeriodicLattice.expTwist (τ • M) U)
          p.boundaryBonds)) := by
    funext τ
    simp only [plaquetteAction, PeriodicLattice.wilsonAction, finsum_eq_sum_of_fintype,
      PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteHolonomy, reHalfTrace_eq]
  rw [e]
  refine HasDerivAt.fun_sum fun p _ => ?_
  exact (reHalfTrace.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_pathHolonomy_twist hU hM p.boundaryBonds)).const_sub 1
private theorem hasDerivAt_noise_term (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n k) (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {c : ℝ → Fin N → ℝ}
    (hc0 : c 0 = 0) (hcc : Tendsto c (𝓝 0) (𝓝 0)) {t : LevelTriple L n k}
    (hcd : HasDerivAt c (e.symm t) 0) (i : Fin k) (q : PositiveEdge L n k ((i : ℕ) + 1))
    {G : (Fin N → ℝ) → ℝ} (hG : ContinuousAt G 0) {ν : ComplexMatrix2}
    (hν : ν ∈ ComplexMatrix2.hermitianTraceless) :
    HasDerivAt (fun s => G (c s) * traceDefect ((chartPoint e (c s)).noise i q) +
        (meanRadius (levelField (chartPoint e (c s)) i) q.1).re *
          -reHalfTrace (Complex.I • ν * (chartPoint e (c s)).noise i q))
      (reHalfTrace (ν * (t.1.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) q.1)) 0 := by
  have hZ := hasDerivAt_coord e hcd (noiseSlotAt i ∘ₗ LinearMap.fst ℝ _ _) q.1
  simp only [LinearMap.comp_apply] at hZ
  set Z : ℝ → ComplexMatrix2 := fun s => (noiseSlotAt i (LinearMap.fst ℝ _ _ (e (c s))) :
    Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) q.1 with hZdef
  set Z' : ComplexMatrix2 := (noiseSlotAt i (LinearMap.fst ℝ _ _ t) :
    Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) q.1 with hZ'def
  have hZ'mem : Z' ∈ ComplexMatrix2.hermitianTraceless := (t.1.2 i).2.1 q.1 q.2
  have hZ0 : Z 0 = 0 := by
    simp [hZdef, hc0, noiseSlotAt]
  have hY : HasDerivAt (fun s => Complex.I • Z s) (Complex.I • Z') 0 := hZ.const_smul Complex.I
  have hE : HasDerivAt (fun s => ComplexMatrix2.matExp (Complex.I • Z s)) (Complex.I • Z') 0 :=
    (hd.1 univ _ _ _ _ _ _ Filter.univ_mem hY hY hY).2.2 (by simp [hZ0])
  have hN : HasDerivAt (fun s => (chartPoint e (c s)).noise i q) (Complex.I • Z') 0 := by
    have h := hE.mul_const (1 : ComplexMatrix2)
    rw [mul_one] at h
    exact h
  have hN0 : (chartPoint e (c 0)).noise i q = 1 := by
    rw [hc0, chartPoint_zero hT e]
    rfl
  have h1 : HasDerivAt (fun s => traceDefect ((chartPoint e (c s)).noise i q)) 0 0 := by
    simp only [traceDefect_eq]
    have h := (reHalfTrace.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hN).const_sub 1
    rw [reHalfTrace_I_smul hZ'mem, neg_zero] at h
    exact h
  have h10 : traceDefect ((chartPoint e (c 0)).noise i q) = 0 := by
    rw [hN0, traceDefect_eq, reHalfTrace_eq]
    simp [ComplexMatrix2.fullTrace]
  have h2 : HasDerivAt (fun s => -reHalfTrace (Complex.I • ν * (chartPoint e (c s)).noise i q))
      (reHalfTrace (ν * Z')) 0 := by
    have h := (reHalfTrace.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hN.const_mul (Complex.I • ν))).neg
    rw [← neg_reHalfTrace_I_I]
    exact h
  have h20 : -reHalfTrace (Complex.I • ν * (chartPoint e (c 0)).noise i q) = 0 := by
    rw [hN0, mul_one, reHalfTrace_I_smul hν, neg_zero]
  have hρ : Tendsto (fun s => (meanRadius (levelField (chartPoint e (c s)) i) q.1).re)
      (𝓝 0) (𝓝 1) := by
    have h := contDiffAt_levelRadius (p₀ := (0 : Fin N → ℝ)) (m := 0) hT
      (X := familyPoint (0 : (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k) (chartSlot e))
      (contDiffAt_familyPoint_fine _ _) (contDiffAt_familyPoint_noise _ _)
      (familyPoint_zero hT _ _) i.2 q.1 q.2
    simp only [familyPoint_eq_chartPoint hT e] at h
    have h3 := Complex.continuous_re.continuousAt.tendsto.comp h.continuousAt.tendsto
    have h4 : (meanRadius (levelField (chartPoint e 0) i) q.1).re = 1 := by
      rw [(chartPoint_levelFields (m := 0) hT e i i.2.le).2, (hT.at_one i i.2 q.1 q.2).2.1]
      simp
    simp only [Function.comp_def, h4] at h3
    exact h3.comp hcc
  have hg : Tendsto (fun s => G (c s)) (𝓝 0) (𝓝 (G 0)) := hG.tendsto.comp hcc
  have t1 := hasDerivAt_mul_of_left_zero h10 h1 hg
  have t2 := hasDerivAt_mul_of_left_zero h20 h2 hρ
  have t3 := t1.add t2
  have e1 : (fun s => G (c s) * traceDefect ((chartPoint e (c s)).noise i q) +
      (meanRadius (levelField (chartPoint e (c s)) i) q.1).re *
        -reHalfTrace (Complex.I • ν * (chartPoint e (c s)).noise i q)) =
      fun s => traceDefect ((chartPoint e (c s)).noise i q) * G (c s) +
        -reHalfTrace (Complex.I • ν * (chartPoint e (c s)).noise i q) *
          (meanRadius (levelField (chartPoint e (c s)) i) q.1).re := by
    funext s
    ring
  rw [e1]
  refine t3.congr_deriv ?_
  simp only [zero_mul, zero_add, mul_one]
  rfl
private theorem hasDerivAt_leftDeriv_chart
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n k) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : NearOneBounds L n k ρ)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {c : ℝ → Fin N → ℝ} (hc0 : c 0 = 0)
    {t : LevelTriple L n k} (hcd : HasDerivAt c (e.symm t) 0) (a : ℝ)
    (η : LevelForms L n k) :
    HasDerivAt (fun s => leftDeriv (chainAction a) (chartPoint e (c s)) η)
      (hessianAtIdentity a t.1 η) 0 := by
  have hcc : Tendsto c (𝓝 0) (𝓝 0) := by
    have := hcd.continuousAt.tendsto
    rwa [hc0] at this
  letI hFq : ∀ i : Fin k, Fintype (PositiveEdge L n k ((i : ℕ) + 1)) := fun i =>
    @Fintype.ofFinite _ (hT.posEdges_finite _ i.2)
  letI hFp : Fintype (Face L n k 0) := @Fintype.ofFinite _ hT.faces_finite
  choose G hGc hGe using fun (i : Fin k) (q : PositiveEdge L n k ((i : ℕ) + 1)) =>
    exists_meanRadius_partial hT e η i.2 q.1 q.2
  let U : ℝ → Edge L n k 0 → ComplexMatrix2 := fun s => (chartPoint e (c s)).fine
  let ν : (i : Fin k) → PositiveEdge L n k ((i : ℕ) + 1) → ComplexMatrix2 := fun i q =>
    (η.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) q.1
  let hf : ℝ → ℝ := fun s =>
    (∑ p : Face L n k 0, -reHalfTrace (holonomyDeriv (U s) η.1 p.boundaryBonds)) +
    a * ∑ i : Fin k, ∑ q : PositiveEdge L n k ((i : ℕ) + 1),
      (G i q (c s) * traceDefect ((chartPoint e (c s)).noise i q) +
        (meanRadius (levelField (chartPoint e (c s)) i) q.1).re *
          -reHalfTrace (Complex.I • ν i q * (chartPoint e (c s)).noise i q))
  have claim1 : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun τ : ℝ => chainAction a (expMove (τ • η) (chartPoint e (c s)))) (hf s) 0 := by
    have hall : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ (i : Fin k) (q : PositiveEdge L n k ((i : ℕ) + 1)),
        HasDerivAt (fun τ : ℝ =>
          (meanRadius (levelField (expMove (τ • η) (chartPoint e (c s))) i) q.1).re)
          (G i q (c s)) 0 :=
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun q =>
        hcc.eventually (hGe i q)
    filter_upwards [hall] with s hs
    have hb := chartPoint_fine_mem hT e (c s)
    have hzero := expMove_zero hb η
    have e1 : (fun τ : ℝ => chainAction a (expMove (τ • η) (chartPoint e (c s)))) = fun τ : ℝ =>
        plaquetteAction L n k
          (PeriodicLattice.expTwist (τ • (η.1 : Edge L n k 0 → ComplexMatrix2)) (U s)) +
          a * ∑ i : Fin k, ∑ q : PositiveEdge L n k ((i : ℕ) + 1),
            (meanRadius (levelField (expMove (τ • η) (chartPoint e (c s))) i) q.1).re *
              traceDefect (ComplexMatrix2.matExp (Complex.I • (τ • ν i q)) *
                (chartPoint e (c s)).noise i q) := by
      funext τ
      simp only [chainAction, finsum_eq_sum_of_fintype]
      rfl
    rw [e1]
    refine (hasDerivAt_plaquetteAction hb η.1.2.2).add (HasDerivAt.const_mul a
      (HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun q _ => ?_))
    refine ((hs i q).mul (hasDerivAt_traceDefect_line (ν i q)
      ((chartPoint e (c s)).noise i q))).congr_deriv ?_
    simp only [hzero, expLine_zero, one_mul]
  have claim2 : HasDerivAt hf (hessianAtIdentity a t.1 η) 0 := by
    have hU0 : U 0 = fun _ => 1 := by
      show (chartPoint e (c 0)).fine = _
      rw [hc0, chartPoint_zero hT e]
      rfl
    have hUd : ∀ b, HasDerivAt (fun s => U s b)
        (Complex.I • (t.1.1 : Edge L n k 0 → ComplexMatrix2) b) 0 :=
      fun b => hasDerivAt_levelField_chart hd hT hρ0 hρ e hc0 hcd 0 (Nat.zero_le _) b
    choose R hR htr using fun p : Face L n k 0 =>
      exists_deriv_holonomyDeriv (M := (η.1 : Edge L n k 0 → ComplexMatrix2)) hU0 hUd
        p.boundaryBonds
    have hA : HasDerivAt (fun s => ∑ p : Face L n k 0,
        -reHalfTrace (holonomyDeriv (U s) η.1 p.boundaryBonds))
        (∑ p : Face L n k 0, -reHalfTrace (R p)) 0 :=
      HasDerivAt.fun_sum fun p _ => (reHalfTrace.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hR p)).neg
    have hB : HasDerivAt (fun s => ∑ i : Fin k, ∑ q : PositiveEdge L n k ((i : ℕ) + 1),
        (G i q (c s) * traceDefect ((chartPoint e (c s)).noise i q) +
          (meanRadius (levelField (chartPoint e (c s)) i) q.1).re *
            -reHalfTrace (Complex.I • ν i q * (chartPoint e (c s)).noise i q)))
        (∑ i : Fin k, ∑ q : PositiveEdge L n k ((i : ℕ) + 1),
          reHalfTrace (ν i q * (t.1.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) q.1)) 0 :=
      HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun q _ =>
        hasDerivAt_noise_term hd hT e hc0 hcc hcd i q (hGc i q) ((η.2 i).2.1 q.1 q.2)
    refine (hA.add (hB.const_mul a)).congr_deriv ?_
    simp only [hessianAtIdentity]
    congr 1
    · have e2 : ∀ p : Face L n k 0, -reHalfTrace (R p) =
          (ComplexMatrix2.halfTrace (edgeCoboundary (t.1.1 : Edge L n k 0 → ComplexMatrix2) p *
            edgeCoboundary (η.1 : Edge L n k 0 → ComplexMatrix2) p)).re := by
        intro p
        rw [reHalfTrace_eq, htr p, sumAlong_boundary η.1.2.2, sumAlong_boundary t.1.1.2.2,
          ← reHalfTrace_apply, reHalfTrace_mul_comm, reHalfTrace_eq]
        simp only [ComplexMatrix2.fullTrace, Matrix.trace_neg, Complex.neg_re]
        ring
      simp only [e2]
      rw [traceFinsumPairing, finsum_eq_sum_of_fintype, Complex.re_sum]
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [re_edgeFormPairing]
      exact Finset.sum_congr rfl fun q _ => reHalfTrace_mul_comm _ _
  refine claim2.congr_of_eventuallyEq ?_
  filter_upwards [claim1] with s hs2
  rw [leftDeriv, hs2.deriv]
end Gradient
section Abstract
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
private theorem second_order_taylor {f : V → ℝ} (hf : ContDiffAt ℝ 2 f 0) (h0 : f 0 = 0)
    (h1 : fderiv ℝ f 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : V, ‖w‖ < δ →
      |f w - 1 / 2 * fderiv ℝ (fderiv ℝ f) 0 w w| ≤ ε * ‖w‖ ^ 2 := by
  have hΦ : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) 0 :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  set Hs := fderiv ℝ (fderiv ℝ f) 0 with hHs
  have e1 := hΦ.isLittleO.def hε
  have e2 : ∀ᶠ w in 𝓝 (0 : V), ContDiffAt ℝ 2 f w := hf.eventually (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (e1.and e2)
  refine ⟨δ, hδ, fun w hw => ?_⟩
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, dist (τ • w) 0 < δ := by
    intro τ hτ
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hτ.1]
    have : τ * ‖w‖ ≤ 1 * ‖w‖ := by gcongr; exact hτ.2
    linarith
  let g : ℝ → ℝ := fun τ => f (τ • w) - 1 / 2 * τ ^ 2 * Hs w w
  have hg : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (fderiv ℝ f (τ • w) w - τ * Hs w w)
      (Icc 0 1) τ := by
    intro τ hτ
    have hd : HasFDerivAt f (fderiv ℝ f (τ • w)) (τ • w) :=
      ((hball (hseg τ hτ)).2.differentiableAt (by norm_num)).hasFDerivAt
    have hl : HasDerivAt (fun τ : ℝ => τ • w) w τ := by
      simpa using (hasDerivAt_id τ).smul_const w
    have h2 := HasFDerivAt.comp_hasDerivAt τ hd hl
    have h3 : HasDerivAt (fun τ : ℝ => 1 / 2 * τ ^ 2 * Hs w w) (τ * Hs w w) τ := by
      have := (((hasDerivAt_id τ).pow 2).const_mul (1 / 2 : ℝ)).mul_const (Hs w w)
      refine this.congr_deriv ?_
      simp
    exact (h2.sub h3).hasDerivWithinAt
  have hb : ∀ τ ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ f (τ • w) w - τ * Hs w w‖ ≤ ε * ‖w‖ ^ 2 := by
    intro τ hτ
    have h4 := (hball (hseg τ hτ)).1
    rw [h1, sub_zero, sub_zero] at h4
    have h5 : fderiv ℝ f (τ • w) w - τ * Hs w w = (fderiv ℝ f (τ • w) - Hs (τ • w)) w := by
      simp [map_smul]
    rw [h5]
    have h6 := (fderiv ℝ f (τ • w) - Hs (τ • w)).le_opNorm w
    have h7 : ‖τ • w‖ ≤ ‖w‖ := by
      rw [norm_smul, Real.norm_of_nonneg hτ.1]
      have : τ * ‖w‖ ≤ 1 * ‖w‖ := by gcongr; exact hτ.2
      linarith
    calc _ ≤ ‖fderiv ℝ f (τ • w) - Hs (τ • w)‖ * ‖w‖ := h6
      _ ≤ (ε * ‖τ • w‖) * ‖w‖ := by gcongr
      _ ≤ (ε * ‖w‖) * ‖w‖ := by gcongr
      _ = ε * ‖w‖ ^ 2 := by ring
  have hmv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hg hb
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  simp only [g, zero_smul, one_smul, h0] at hmv
  simpa using hmv
private theorem exists_riesz {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] (p : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hp : ∀ x, p x x = 0 → x = 0)
    (φ : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) : ∃ T : F →ₗ[ℝ] E, ∀ f e, p (T f) e = φ f e := by apply _root_.YangMills.SharedProofs.p13845 <;> assumption
variable [FiniteDimensional ℝ V]
private theorem exists_coercive_bound {q : V → ℝ} (hc : Continuous q)
    (hpos : ∀ v, v ≠ 0 → 0 < q v)
    (hh : ∀ (t : ℝ) v, q (t • v) = t ^ 2 * q v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ^ 2 ≤ q v := by
  haveI : ProperSpace V := FiniteDimensional.proper ℝ V
  by_cases hne : (Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn hne hc.continuousOn
    have hu0 : u ≠ 0 := by
      intro h
      have := mem_sphere_zero_iff_norm.mp hu
      rw [h, norm_zero] at this
      exact zero_ne_one this
    refine ⟨q u, hpos u hu0, fun v => ?_⟩
    by_cases hv : v = 0
    · have h0 : q 0 = 0 := by simpa using hh 0 0
      simp [hv, h0]
    · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hs : (‖v‖⁻¹ • v) ∈ Metric.sphere (0 : V) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      have h1 := hmin hs
      simp only [Set.mem_setOf_eq] at h1
      rw [hh] at h1
      calc q u * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * q v) * ‖v‖ ^ 2 := by gcongr
        _ = q v := by field_simp
  · refine ⟨1, one_pos, fun v => ?_⟩
    have hv : v = 0 := by
      by_contra h
      apply hne
      have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr h
      exact ⟨‖v‖⁻¹ • v, by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]⟩
    have h0 : q 0 = 0 := by simpa using hh 0 0
    simp [hv, h0]
private theorem quadratic_core (h : V →L[ℝ] V →L[ℝ] ℝ) (hs : ∀ u v, h u v = h v u)
    (hp : ∀ v, 0 ≤ h v v)
    {ι : Type*} [Fintype ι] (ψ : ι → V →L[ℝ] ℝ)
    (hdef : ∀ v, h v v = 0 → (∀ i, ψ i v = 0) → v = 0) (v₀ : V) :
    ∃ vh : V, (∀ i, ψ i vh = ψ i v₀) ∧ (∀ u, (∀ i, ψ i u = 0) → h vh u = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (v : V) (s : ℝ),
        (∀ i, |ψ i (v - s • vh)| ≤ δ * (‖v‖ + |s|)) →
        h v v ≤ s ^ 2 * h vh vh + δ * (‖v‖ ^ 2 + s ^ 2) → ‖v - s • vh‖ ≤ ε * |s| := by
  classical
  let Z : Submodule ℝ V := ⨅ i, LinearMap.ker (ψ i : V →ₗ[ℝ] ℝ)
  have hZ : ∀ z : Z, ∀ i, ψ i (z : V) = 0 := by
    intro z i
    have := (Submodule.mem_iInf _).mp z.2 i
    simpa using this
  let hl : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun u v => h u v) (by simp) (by simp) (by simp)
    (by simp)
  let pZ : Z →ₗ[ℝ] Z →ₗ[ℝ] ℝ := hl.domRestrict₁₂ Z Z
  have hpZ : ∀ x : Z, pZ x x = 0 → x = 0 := by
    intro x hx
    exact Subtype.ext (hdef _ hx (hZ x))
  let φ : ℝ →ₗ[ℝ] Z →ₗ[ℝ] ℝ := LinearMap.toSpanSingleton ℝ _ ((hl v₀).domRestrict Z)
  obtain ⟨T, hT⟩ := exists_riesz pZ hpZ φ
  set z : Z := T 1 with hz
  have hzv : ∀ u : Z, h (z : V) (u : V) = h v₀ (u : V) := by
    intro u
    have h1 : pZ z u = h (z : V) (u : V) := rfl
    have h2 : φ 1 u = h v₀ (u : V) := by simp [φ, hl]
    rw [← h1, ← h2]
    exact hT 1 u
  set vh : V := v₀ - (z : V) with hvh
  have hK0 : ∀ u, (∀ i, ψ i u = 0) → h vh u = 0 := by
    intro u hu
    have hm : u ∈ Z := (Submodule.mem_iInf _).mpr fun i => by simpa using hu i
    have := hzv ⟨u, hm⟩
    simp only [hvh, map_sub, ContinuousLinearMap.sub_apply]
    simp only at this
    linarith
  refine ⟨vh, fun i => ?_, hK0, ?_⟩
  · simp only [hvh, map_sub, hZ z i, sub_zero]
  have hKmem : (h vh : V →ₗ[ℝ] ℝ) ∈ Submodule.span ℝ
      (Set.range fun i => (ψ i : V →ₗ[ℝ] ℝ)) := by
    refine mem_span_of_iInf_ker_le_ker fun u hu => ?_
    have hu' : ∀ i, ψ i u = 0 := by
      intro i
      have := (Submodule.mem_iInf _).mp hu i
      simpa using this
    simpa using hK0 u hu'
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hKmem
  have hKf : ∀ u, h vh u = ∑ i, cf i * ψ i u := by
    intro u
    have := congrArg (fun g : V →ₗ[ℝ] ℝ => g u) hcf
    simp at this
    exact this.symm
  set A : ℝ := ∑ i, |cf i| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => abs_nonneg _
  set I : ℝ := (Fintype.card ι : ℝ) with hI
  obtain ⟨c, hc0, hcq⟩ := exists_coercive_bound (q := fun v => h v v + ∑ i, (ψ i v) ^ 2)
    (by fun_prop)
    (by
      intro v hv
      have h1 := hp v
      have h2 : 0 ≤ ∑ i, (ψ i v) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      by_contra hcon
      have h3 : h v v = 0 := by linarith
      have h4 : ∑ i, (ψ i v) ^ 2 = 0 := by linarith
      have h5 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (ψ i v)).mp h4
      exact hv (hdef v h3 fun i => by simpa using h5 i (Finset.mem_univ i)))
    (by
      intro t v
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_pow, mul_add,
        Finset.mul_sum]
      ring_nf)
  set R : ℝ := ‖vh‖ + 1 with hR
  have hR1 : 1 ≤ R := by have := norm_nonneg vh; linarith
  set C : ℝ := 1 + 2 * A + I with hC
  have hC1 : 1 ≤ C := by simp only [hC]; linarith
  intro ε hε
  set δ : ℝ := min 1 (min (c / (4 * C)) (c * ε ^ 2 / (8 * C * R ^ 2))) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ * (4 * C) ≤ c := by
    have h1 : δ ≤ c / (4 * C) := (min_le_right _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ (by positivity)] at h1
  have hδ3 : δ * (8 * C * R ^ 2) ≤ c * ε ^ 2 := by
    have h1 : δ ≤ c * ε ^ 2 / (8 * C * R ^ 2) := (min_le_right _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at h1
  refine ⟨δ, hδ0, fun v s hψ hH => ?_⟩
  set d := v - s • vh with hd
  have hv : v = s • vh + d := by simp [hd]
  set S : ℝ := ‖v‖ + |s| with hS
  have hS0 : 0 ≤ S := by positivity
  have hSle : S ≤ ‖d‖ + R * |s| := by
    have h1 : ‖v‖ ≤ ‖s • vh‖ + ‖d‖ := by rw [hv]; exact norm_add_le _ _
    rw [norm_smul, Real.norm_eq_abs] at h1
    have h2 : R * |s| = ‖vh‖ * |s| + |s| := by simp only [hR]; ring
    simp only [hS]
    rw [h2]
    linarith
  have hys : |s| ≤ S := by have := norm_nonneg v; simp only [hS]; linarith
  have hvS : ‖v‖ ≤ S := by have := abs_nonneg s; simp only [hS]; linarith
  have hexp : h v v = s ^ 2 * h vh vh + 2 * s * h vh d + h d d := by
    rw [hv]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hs d vh]
    ring
  have hKd : |h vh d| ≤ A * (δ * S) := by
    rw [hKf]
    calc |∑ i, cf i * ψ i d| ≤ ∑ i, |cf i * ψ i d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |cf i| * (δ * S) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hψ i) (abs_nonneg _)
      _ = A * (δ * S) := by rw [hA, Finset.sum_mul]
  have hdd : h d d ≤ δ * S ^ 2 + 2 * A * δ * S ^ 2 := by
    have h3 : |s * h vh d| ≤ |s| * (A * (δ * S)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hKd (abs_nonneg _)
    have h2' := neg_abs_le (s * h vh d)
    have h2 : ‖v‖ ^ 2 + s ^ 2 ≤ S ^ 2 := by
      have e : S ^ 2 = ‖v‖ ^ 2 + 2 * (‖v‖ * |s|) + s ^ 2 := by
        simp only [hS]
        rw [add_sq, sq_abs]
        ring
      have : 0 ≤ ‖v‖ * |s| := by positivity
      linarith
    have h4 : |s| * (A * (δ * S)) ≤ S * (A * (δ * S)) :=
      mul_le_mul_of_nonneg_right hys (by positivity)
    have h5 : δ * (‖v‖ ^ 2 + s ^ 2) ≤ δ * S ^ 2 := by gcongr
    have e2 : S * (A * (δ * S)) = A * δ * S ^ 2 := by ring
    have e3 : 2 * s * h vh d = 2 * (s * h vh d) := by ring
    rw [e2] at h4
    rw [e3] at hexp
    linarith
  have hψ2 : ∑ i, (ψ i d) ^ 2 ≤ I * (δ * S) ^ 2 := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun i => (ψ i d) ^ 2) ((δ * S) ^ 2) (fun i _ => by
      have h1 := hψ i
      have h2 : (ψ i d) ^ 2 = |ψ i d| ^ 2 := (sq_abs _).symm
      rw [h2]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2)
    simpa [hI] using this
  have hq : c * ‖d‖ ^ 2 ≤ h d d + ∑ i, (ψ i d) ^ 2 := hcq d
  have hmain : c * ‖d‖ ^ 2 ≤ δ * C * S ^ 2 := by
    have h1 : I * (δ * S) ^ 2 ≤ I * δ * S ^ 2 := by
      have h0 : δ ^ 2 ≤ δ := by
        have : δ * δ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδ1 hδ0.le
        rw [sq]
        linarith
      have h2 : 0 ≤ S ^ 2 := by positivity
      calc I * (δ * S) ^ 2 = I * (δ ^ 2 * S ^ 2) := by ring
        _ ≤ I * (δ * S ^ 2) := by gcongr
        _ = I * δ * S ^ 2 := by ring
    have e : δ * C * S ^ 2 = δ * S ^ 2 + 2 * A * δ * S ^ 2 + I * δ * S ^ 2 := by
      simp only [hC]
      ring
    rw [e]
    linarith
  have hS2 : S ^ 2 ≤ 2 * ‖d‖ ^ 2 + 2 * R ^ 2 * s ^ 2 := by
    have h1 : S ^ 2 ≤ (‖d‖ + R * |s|) ^ 2 := pow_le_pow_left₀ hS0 hSle 2
    have h3 : (‖d‖ + R * |s|) ^ 2 ≤ 2 * ‖d‖ ^ 2 + 2 * (R * |s|) ^ 2 := by
      nlinarith [sq_nonneg (‖d‖ - R * |s|)]
    have e : (R * |s|) ^ 2 = R ^ 2 * s ^ 2 := by rw [mul_pow, sq_abs]
    rw [e] at h3
    linarith
  have hfin : ‖d‖ ^ 2 ≤ (ε * |s|) ^ 2 := by
    have hP : 0 ≤ δ * C := by positivity
    have hX : 0 ≤ ‖d‖ ^ 2 := by positivity
    have hY : 0 ≤ s ^ 2 := sq_nonneg s
    have h1 : δ * C * S ^ 2 ≤ δ * C * (2 * ‖d‖ ^ 2 + 2 * R ^ 2 * s ^ 2) :=
      mul_le_mul_of_nonneg_left hS2 hP
    have h2 : 2 * (δ * C) ≤ c / 2 := by linarith
    have h3 : 2 * (δ * C) * ‖d‖ ^ 2 ≤ c / 2 * ‖d‖ ^ 2 := mul_le_mul_of_nonneg_right h2 hX
    have h4 : 2 * (δ * C) * R ^ 2 ≤ c / 4 * ε ^ 2 := by linarith
    have h5 : 2 * (δ * C) * R ^ 2 * s ^ 2 ≤ c / 4 * ε ^ 2 * s ^ 2 :=
      mul_le_mul_of_nonneg_right h4 hY
    have h6 : 0 ≤ c * ε ^ 2 * s ^ 2 := by positivity
    have h7 : c * ‖d‖ ^ 2 ≤ c * (ε ^ 2 * s ^ 2) := by
      have e2 : c * (ε ^ 2 * s ^ 2) = c * ε ^ 2 * s ^ 2 := by ring
      rw [e2]
      linarith
    have h8 := le_of_mul_le_mul_left h7 hc0
    calc ‖d‖ ^ 2 ≤ ε ^ 2 * s ^ 2 := h8
      _ = (ε * |s|) ^ 2 := by rw [mul_pow, sq_abs]
  exact abs_le_of_sq_le_sq' hfin (by positivity) |>.2
end Abstract
section LimitTools
private theorem det_compact {g : ComplexMatrix2} (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    Matrix.det g = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
private theorem isUnit_det_compact {g : ComplexMatrix2} (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit (Matrix.det g) := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem det_isQuaternionic {A : ComplexMatrix2} (hA : IsQuaternionic A) :
    Matrix.det A = ((Complex.normSq (A 0 0) + Complex.normSq (A 0 1) : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two, hA.1, hA.2]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  ring
private theorem traceDefect_compact {g : ComplexMatrix2} (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    0 ≤ traceDefect g ∧ (traceDefect g = 0 → g = 1) := by
  have hq := isQuaternionic_of_compact h
  have hd := det_isQuaternionic hq
  rw [det_compact h] at hd
  have hd' : Complex.normSq (g 0 0) + Complex.normSq (g 0 1) = 1 := by
    have := congrArg Complex.re hd
    simpa using this.symm
  have e : traceDefect g = 1 - (g 0 0).re := by
    simp only [traceDefect, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
      Matrix.trace_fin_two, hq.1]
    simp [Complex.add_conj, Complex.mul_re]
  have hre : (g 0 0).re ^ 2 + (g 0 0).im ^ 2 + Complex.normSq (g 0 1) = 1 := by
    rw [← hd', Complex.normSq_apply (g 0 0)]
    ring
  have hb := Complex.normSq_nonneg (g 0 1)
  refine ⟨?_, fun h0 => ?_⟩
  · rw [e]
    nlinarith [sq_nonneg ((g 0 0).im), sq_nonneg ((g 0 0).re - 1)]
  · rw [e] at h0
    have h1 : (g 0 0).re = 1 := by linarith
    rw [h1] at hre
    have h2 : (g 0 0).im = 0 := by nlinarith [sq_nonneg ((g 0 0).im)]
    have h3 : Complex.normSq (g 0 1) = 0 := by nlinarith [sq_nonneg ((g 0 0).im)]
    have h4 : g 0 1 = 0 := Complex.normSq_eq_zero.mp h3
    have h5 : g 0 0 = 1 := Complex.ext h1 h2
    ext a b
    fin_cases a <;> fin_cases b
    · simpa using h5
    · simpa using h4
    · simp [hq.2, h4]
    · simp [hq.1, h5]
abbrev _root_.YangMills.SharedProofs.p27652 := @traceDefect_compact
variable {L n k j : ℕ}
private theorem meanRadius_re_nonneg [Finite (Vertex L n k j)] {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1)) :
    0 ≤ (meanRadius V c).re := by apply _root_.YangMills.SharedProofs.p43485 <;> assumption
end LimitTools
section FactsOfTheTower
private theorem towerFacts (hd : NormalizedMeanAtOne)
    (hCfg : LeftChartFields.Claim) (hS : FaceSums.FacesAndPairings)
    (hV : LinearMapValues.Statement) (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    TowerFacts L n k := by
  have hPS := fun (j : ℕ) (hj : j ≤ k) => (hS L hL k j hj).1 n hn
  have finS : ∀ j, j ≤ k → Finite (Vertex L n k j) := fun j hj =>
    Set.finite_univ_iff.mp ((hPS j hj).2.1 univ).2.1
  have hvals := (hV L hL k).1 n hn
  refine
    { sites_finite := finS
      posEdges_finite := fun j hj => Set.finite_univ_iff.mp ((hPS j hj).2.2.1 univ).2.1
      edges_finite := fun j hj => ?_
      faces_finite := Set.finite_univ_iff.mp ((hPS 0 (Nat.zero_le _)).2.2.2 univ).2.1
      deriv_at_one := fun j hj B hB c hc => (hd L hL n k j hn hj B hB c hc).2.2.2.2
      smoothing_mem := fun j hj B hB => ((hvals.1 j hj).1 B hB).2.2.1
      not_both := fun j hj b hb => ?_
      at_one := fun j hj c hc => ?_
      leftExp := fun j hj => ((hCfg.2.2 L k j hL hj).1 n hn).1.1
      curveLogs := fun I hI => (hCfg.1 I hI).1 }
  · haveI := finS j hj
    have h : Function.Injective (fun b : Edge L n k j => (b.source, b.target)) := by
      intro b b' hb
      exact PeriodicLattice.Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
    exact Finite.of_injective _ h
  · obtain ⟨μ, hμ⟩ := hb
    rintro ⟨ν, hν⟩
    have hN := (hA L hL n j k hn hj).2.2.2.2.2.1
    have hs : QuotientLattices.IsSignedAxisStep
        (QuotientLattices.torusAxisSteps L n k j)
        (b.source : PeriodicLattice.FourTorus L n) (b.target : PeriodicLattice.FourTorus L n) 1 μ := by
      have h := congrArg Subtype.val hμ
      simpa [QuotientLattices.IsSignedAxisStep,
        QuotientLattices.torusAxisSteps] using h
    have hs' : QuotientLattices.IsSignedAxisStep
        (QuotientLattices.torusAxisSteps L n k j)
        (b.target : PeriodicLattice.FourTorus L n) (b.source : PeriodicLattice.FourTorus L n) 1 ν := by
      have h := congrArg Subtype.val hν
      simpa [QuotientLattices.IsSignedAxisStep,
        QuotientLattices.torusAxisSteps, PeriodicLattice.Bond.opposite] using h
    have hX := ((hN.2.2 _ b.source.2 _ b.target.2).2 1 μ hs).2
    rcases hX with ⟨-, h⟩ | ⟨-, h⟩
    · exact h ⟨ν, hs'⟩
    · exact h ⟨μ, hs⟩
  · obtain ⟨h1, h2, h3, -, -⟩ := hd L hL n k j hn hj 0 (edgeFormSpace L n k j).zero_mem c hc
    exact ⟨h1, h2, h3⟩
end FactsOfTheTower
section Near
variable {L n k j : ℕ}
private theorem contDiffAt_chainAction (hT : TowerFacts L n k) {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P]
    {p₀ : P} {m : WithTop ℕ∞} {X : P → ChainPoint L n k}
    (hb : ∀ b, ContDiffAt ℝ m (fun p => (X p).fine b) p₀)
    (hn : ∀ i c, ContDiffAt ℝ m (fun p => (X p).noise i c) p₀)
    (h0 : X p₀ = unitPoint L n k) (a : ℝ) :
    ContDiffAt ℝ m (fun p => chainAction a (X p)) p₀ := by
  letI hFq : ∀ i : Fin k, Fintype (PositiveEdge L n k ((i : ℕ) + 1)) := fun i =>
    @Fintype.ofFinite _ (hT.posEdges_finite _ i.2)
  letI hFp : Fintype (Face L n k 0) := @Fintype.ofFinite _ hT.faces_finite
  have rtC : ∀ {f : P → ComplexMatrix2}, ContDiffAt ℝ m f p₀ →
      ContDiffAt ℝ m (fun p => (ComplexMatrix2.halfTrace (f p)).re) p₀ := by
    intro f hf
    let T : ComplexMatrix2 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      { toFun := fun A => (ComplexMatrix2.halfTrace A).re
        map_add' := fun A B => by
          simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_add, mul_add]
        map_smul' := fun r A => by
          have e : r • A = (r : ℂ) • A := (Complex.coe_smul r A).symm
          simp only [RingHom.id_apply, smul_eq_mul, ComplexMatrix2.halfTrace,
            ComplexMatrix2.fullTrace]
          rw [e, Matrix.trace_smul, smul_eq_mul, mul_left_comm, Complex.re_ofReal_mul] }
    exact T.contDiff.contDiffAt.comp p₀ hf
  have e : (fun p => chainAction a (X p)) = fun p =>
      (∑ q : Face L n k 0, (1 - (ComplexMatrix2.halfTrace
        (PeriodicLattice.pathHolonomy (X p).fine q.boundaryBonds)).re)) +
      a * ∑ i : Fin k, ∑ c : PositiveEdge L n k ((i : ℕ) + 1),
        (meanRadius (levelField (X p) i) c.1).re *
          (1 - (ComplexMatrix2.halfTrace ((X p).noise i c)).re) := by
    funext p
    simp only [chainAction, plaquetteAction, PeriodicLattice.wilsonAction,
      finsum_eq_sum_of_fintype, PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteHolonomy,
      traceDefect]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    simp [ComplexMatrix2.halfTrace, Complex.mul_re]
  rw [e]
  refine ContDiffAt.add (ContDiffAt.sum fun q _ => ?_) (contDiffAt_const.mul
    (ContDiffAt.sum fun i _ => ContDiffAt.sum fun c _ => ?_))
  · exact contDiffAt_const.sub (rtC (contDiffAt_pathHolonomy hb _))
  · exact (Complex.reCLM.contDiff.contDiffAt.comp p₀
      (contDiffAt_levelRadius hT hb hn h0 i.2 c.1 c.2)).mul (contDiffAt_const.sub (rtC (hn i c)))
private theorem chainAction_unitPoint (a : ℝ) : chainAction a (unitPoint L n k) = 0 := by apply _root_.YangMills.SharedProofs.p8209 <;> assumption
private abbrev PointCoords (L n k : ℕ) : Type :=
  (Edge L n k 0 → ComplexMatrix2) × ((i : Fin k) → PositiveEdge L n k ((i : ℕ) + 1) → ComplexMatrix2)
private theorem chainAction_nonneg (hSG : PeriodicLattice.ActionNonnegAndGaugeInvariant)
    (hT : TowerFacts L n k) (hk : 1 ≤ k) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {a : ℝ}
    (ha : 0 < a) {X : ChainPoint L n k} (hX : IsCompactValued X) : 0 ≤ chainAction a X := by
  have h1 : 0 ≤ plaquetteAction L n k X.fine :=
    ((hSG L n k hL.1 hL.2 hn hk).2 X.fine (fun _ => 1) (hX.2 0 (Nat.zero_le _))
      (fun _ => ComplexMatrix2.specialUnitary.one_mem)).1
  refine add_nonneg h1 (mul_nonneg ha.le (Finset.sum_nonneg fun i _ => ?_))
  haveI := hT.sites_finite i i.2.le
  refine finsum_nonneg fun c => ?_
  exact mul_nonneg (meanRadius_re_nonneg (hX.2 i i.2.le) _) (traceDefect_compact (hX.1 i c)).1
private theorem matExp_I_mem_compact (hEL : ComplexMatrix2.ExpLogEstimates) {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.matExp_I_smul_mem_compact <;> assumption
end Near
section Second
variable {L n k N : ℕ}
private theorem compact_of_near (hT : TowerFacts L n k) {ρ : ℝ} (hρ : NearOneBounds L n k ρ)
    {X : ChainPoint L n k} (hn : ∀ i c, X.noise i c ∈ PeriodicLattice.compactGaugeGroup)
    (hb : X.fine ∈ fieldSpace L n k 0)
    (hnear : ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ) :
    IsCompactValued X := by
  refine ⟨hn, fun j => ?_⟩
  induction j with
  | zero => exact fun _ => hb
  | succ j ih =>
    intro h
    have hj : j < k := h
    have h1 := ih hj.le
    haveI := hT.sites_finite j hj.le
    have hpos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        levelField X (j + 1) c ∈ PeriodicLattice.compactGaugeGroup := by
      intro c hc
      obtain ⟨-, -, -, hu, -⟩ := hρ j hj _ (mem_fieldsIn_of_mem h1) (hnear j hj.le) c hc
      rw [levelField_succ_pos _ hj c hc]
      exact ComplexMatrix2.specialUnitary.mul_mem (hn _ _) (normalizedMean_mem_compact h1 c hu)
    have hreal : ∀ c : Edge L n k (j + 1), levelField X (j + 1) c ∈
        PeriodicLattice.compactGaugeGroup := by
      intro c
      by_cases hc : c.IsPositivelyOriented
      · exact hpos c hc
      · have hc' := (oriented_or_opposite c).resolve_left hc
        rw [levelField_opposite _ hj c hc hc']
        exact inv_mem_compact (hpos _ hc')
    refine ⟨fun b _ => hreal b, fun b _ => ?_⟩
    by_cases hb' : b.IsPositivelyOriented
    · have hb'' := hT.not_both (j + 1) hj b hb'
      have hbr := (oriented_or_opposite b.opposite).resolve_left hb''
      rw [levelField_opposite _ hj _ hb'' hbr, edge_opposite_opposite]
    · have hbr := (oriented_or_opposite b).resolve_left hb'
      rw [levelField_opposite _ hj b hb' hbr,
        Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_compact (hreal _))]
private theorem expMove_unitPoint_compact (hT : TowerFacts L n k)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    {ρ : ℝ} (hρ : NearOneBounds L n k ρ) (ξ : LevelForms L n k)
    (hnear : ∀ j, j ≤ k → ∀ b,
      ComplexMatrix2.operatorNorm (levelField (expMove ξ (unitPoint L n k)) j b - 1) < ρ) :
    IsCompactValued (expMove ξ (unitPoint L n k)) := by
  refine compact_of_near hT hρ (fun i c => ?_) ?_ hnear
  · simp only [expMove, unitPoint, mul_one]
    exact matExp_I_mem_compact hEL ((ξ.2 i).2.1 c.1 c.2)
  · have h := expTwist_mem_fieldSpace hT (Nat.zero_le k)
      (const_one_mem (L := L) (n := n) (k := k) (j := 0)) ξ.1 1
    rw [one_smul] at h
    exact h
private theorem eventually_chartPoint_compact (hT : TowerFacts L n k)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : NearOneBounds L n k ρ)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) :
    ∀ᶠ w in 𝓝 (0 : Fin N → ℝ), IsCompactValued (chartPoint e w) := by
  filter_upwards [eventually_chartPoint_near hT e hρ0] with w hw
  exact expMove_unitPoint_compact hT hEL hρ _ hw
private theorem expLine_add (X : ComplexMatrix2) (s t : ℝ) :
    ComplexMatrix2.matExp (Complex.I • (s • X)) * ComplexMatrix2.matExp (Complex.I • (t • X)) =
      ComplexMatrix2.matExp (Complex.I • ((s + t) • X)) := by apply _root_.YangMills.SharedProofs.p4363 <;> assumption
private theorem expMove_line (η : LevelForms L n k) (t τ : ℝ) :
    expMove (t • η) (expMove (τ • η) (unitPoint L n k)) = expMove ((t + τ) • η) (unitPoint L n k) := by
  have e1 : (expMove (t • η) (expMove (τ • η) (unitPoint L n k))).fine =
      (expMove ((t + τ) • η) (unitPoint L n k)).fine := by
    funext b
    by_cases hb : b.IsPositivelyOriented
    · show PeriodicLattice.expTwist (t • (η.1 : Edge L n k 0 → ComplexMatrix2))
        (PeriodicLattice.expTwist (τ • (η.1 : Edge L n k 0 → ComplexMatrix2)) fun _ => 1) b =
        PeriodicLattice.expTwist ((t + τ) • (η.1 : Edge L n k 0 → ComplexMatrix2)) (fun _ => 1) b
      simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply, mul_one]
      exact expLine_add _ _ _
    · have hbr := (oriented_or_opposite b).resolve_left hb
      show PeriodicLattice.expTwist (t • (η.1 : Edge L n k 0 → ComplexMatrix2))
        (PeriodicLattice.expTwist (τ • (η.1 : Edge L n k 0 → ComplexMatrix2)) fun _ => 1) b =
        PeriodicLattice.expTwist ((t + τ) • (η.1 : Edge L n k 0 → ComplexMatrix2)) (fun _ => 1) b
      simp only [PeriodicLattice.expTwist, if_neg hb, if_pos hbr, Pi.smul_apply, mul_one]
      rw [expLine_add]
  have e2 : (expMove (t • η) (expMove (τ • η) (unitPoint L n k))).noise =
      (expMove ((t + τ) • η) (unitPoint L n k)).noise := by
    funext i c
    show ComplexMatrix2.matExp (Complex.I •
        (t • (η.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) c.1)) *
      (ComplexMatrix2.matExp (Complex.I •
        (τ • (η.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) c.1)) * 1) =
      ComplexMatrix2.matExp (Complex.I •
        ((t + τ) • (η.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) c.1)) * 1
    rw [mul_one, mul_one]
    exact expLine_add _ _ _
  calc expMove (t • η) (expMove (τ • η) (unitPoint L n k)) =
      ⟨(expMove (t • η) (expMove (τ • η) (unitPoint L n k))).fine,
        (expMove (t • η) (expMove (τ • η) (unitPoint L n k))).noise⟩ := rfl
    _ = ⟨(expMove ((t + τ) • η) (unitPoint L n k)).fine,
        (expMove ((t + τ) • η) (unitPoint L n k)).noise⟩ := by rw [e1, e2]
    _ = expMove ((t + τ) • η) (unitPoint L n k) := rfl
private theorem chainAction_second_order
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n k) (hEL : ComplexMatrix2.ExpLogEstimates)
    (hSG : PeriodicLattice.ActionNonnegAndGaugeInvariant) (hk : 1 ≤ k)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : NearOneBounds L n k ρ) {a : ℝ} (ha : 0 < a)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) :
    ContDiffAt ℝ 2 (fun w => chainAction a (chartPoint e w)) 0 ∧
    chainAction a (chartPoint e 0) = 0 ∧
    fderiv ℝ (fun w => chainAction a (chartPoint e w)) 0 = 0 ∧
    ∀ v, fderiv ℝ (fderiv ℝ fun w => chainAction a (chartPoint e w)) 0 v v =
      hessianAtIdentity a (e v).1 (e v).1 := by
  set f : (Fin N → ℝ) → ℝ := fun w => chainAction a (chartPoint e w) with hf
  have hcd : ContDiffAt ℝ 2 f 0 := by
    have h := contDiffAt_chainAction (p₀ := (0 : Fin N → ℝ)) (m := 2) hT
      (X := familyPoint (0 : (Fin N → ℝ) →ₗ[ℝ] LevelForms L n k) (chartSlot e))
      (contDiffAt_familyPoint_fine _ _) (contDiffAt_familyPoint_noise _ _)
      (familyPoint_zero hT _ _) a
    simpa only [familyPoint_eq_chartPoint hT e] using h
  have h0 : f 0 = 0 := by
    simp only [hf, chartPoint_zero hT e]
    exact chainAction_unitPoint a
  have hmin : IsLocalMin f 0 := by
    filter_upwards [eventually_chartPoint_compact hT hEL hρ0 hρ e] with w hw
    rw [h0]
    exact chainAction_nonneg hSG hT hk hL hn ha hw
  have h1 : fderiv ℝ f 0 = 0 := hmin.fderiv_eq_zero
  refine ⟨hcd, h0, h1, fun v => ?_⟩
  set Φ := fderiv ℝ f with hΦd
  have hΦ : HasFDerivAt Φ (fderiv ℝ Φ 0) 0 :=
    ((hcd.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hl0 : HasDerivAt (fun τ : ℝ => τ • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hΦ' : HasFDerivAt Φ (fderiv ℝ Φ 0) ((0 : ℝ) • v) := by
    rw [zero_smul]
    exact hΦ
  have hline : HasDerivAt (fun τ : ℝ => Φ (τ • v) v) (fderiv ℝ Φ 0 v v) 0 := by
    have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hΦ' hl0
    have h3 := h2.clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa using h3
  have hcurve := hasDerivAt_leftDeriv_chart hd hT hρ0 hρ e (c := fun τ : ℝ => τ • v) (by simp)
    (t := e v) (by simpa using hl0) a (e v).1
  have e2 : ∀ᶠ w in 𝓝 (0 : Fin N → ℝ), ContDiffAt ℝ 2 f w := hcd.eventually (by simp)
  have hlim : Tendsto (fun τ : ℝ => τ • v) (𝓝 0) (𝓝 0) := by
    have := hl0.continuousAt.tendsto
    simpa using this
  refine hline.unique (hcurve.congr_of_eventuallyEq ?_)
  filter_upwards [hlim.eventually e2] with τ hτ
  have hd1 : HasFDerivAt f (Φ (τ • v)) (τ • v) :=
    (hτ.differentiableAt (by norm_num)).hasFDerivAt
  have hg : HasDerivAt (fun t : ℝ => (t + τ) • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).add_const τ).smul_const v
  have hd2 : HasFDerivAt f (Φ (τ • v)) ((0 + τ) • v) := by
    rw [zero_add]
    exact hd1
  have hcomp := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hd2 hg
  have e3 : (f ∘ fun t : ℝ => (t + τ) • v) = fun t : ℝ =>
      chainAction a (expMove (t • (e v).1) (chartPoint e (τ • v))) := by
    funext t
    have p1 : ∀ r : ℝ, chartPoint e (r • v) = expMove (r • (e v).1) (unitPoint L n k) := by
      intro r
      simp only [chartPoint, map_smul, Prod.smul_fst]
    simp only [Function.comp, hf]
    rw [p1, p1, expMove_line]
  rw [e3] at hcomp
  rw [leftDeriv, hcomp.deriv]
end Second
section Pairing
variable {ι : Type*} [Finite ι]
private theorem tracePairing_add_left (f f' g : ι → ComplexMatrix2) :
    traceFinsumPairing (f + f') g = traceFinsumPairing f g + traceFinsumPairing f' g := by apply _root_.YangMills.Construction.Tower.RealQuadraticTransposes.tracePair_add_left <;> assumption
private theorem tracePairing_comm (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = traceFinsumPairing g f := by apply _root_.YangMills.Construction.Tower.RealQuadraticTransposes.tracePair_comm <;> assumption
private theorem tracePairing_smul_left (r : ℝ) (f g : ι → ComplexMatrix2) :
    traceFinsumPairing (r • f) g = (r : ℂ) * traceFinsumPairing f g := by apply _root_.YangMills.SharedProofs.p655 <;> assumption
private theorem tracePairing_zero_right (f : ι → ComplexMatrix2) :
    traceFinsumPairing f (0 : ι → ComplexMatrix2) = 0 := by
  simp [traceFinsumPairing, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
private theorem tracePairing_add_right (f g g' : ι → ComplexMatrix2) :
    traceFinsumPairing f (g + g') = traceFinsumPairing f g + traceFinsumPairing f g' := by
  rw [tracePairing_comm, tracePairing_add_left, tracePairing_comm g, tracePairing_comm g']
private theorem tracePairing_smul_right (r : ℝ) (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f (r • g) = (r : ℂ) * traceFinsumPairing f g := by
  rw [tracePairing_comm, tracePairing_smul_left, tracePairing_comm g]
private theorem tracePairing_self (hI : FaceSums.PairingIsInner ↥(univ : Set ι))
    (g : ι → ComplexMatrix2) (hg : ∀ i, g i ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (traceFinsumPairing g g).re ∧ ((traceFinsumPairing g g).re = 0 → g = 0) := by apply _root_.YangMills.SharedProofs.p120809 <;> assumption
end Pairing
section Forms
variable {L n k j : ℕ}
private theorem edgeForm_value_mem {B : Edge L n k j → ComplexMatrix2}
    (h : B ∈ edgeFormSpace L n k j)
    (b : Edge L n k j) : B b ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.SmoothingIterProof.edgeForm_apply_mem <;> assumption
private theorem edgeForm_eq_zero {B : Edge L n k j → ComplexMatrix2} (h : B ∈ edgeFormSpace L n k j)
    (h0 : restrictToPositiveEdges B = 0) : B = 0 := by apply _root_.YangMills.SharedProofs.p27961 <;> assumption
private theorem vertexCoboundary_add (l l' : Vertex L n k j → ComplexMatrix2) :
    vertexCoboundary (l + l') = vertexCoboundary l + vertexCoboundary l' := by apply _root_.YangMills.SharedProofs.p26773 <;> assumption
private theorem edgeCoboundary_mem {B : Edge L n k j → ComplexMatrix2}
    (h : B ∈ edgeFormSpace L n k j) (p : Face L n k j) :
    edgeCoboundary B p ∈ ComplexMatrix2.hermitianTraceless :=
  ComplexMatrix2.hermitianTraceless.sub_mem (ComplexMatrix2.hermitianTraceless.sub_mem
    (ComplexMatrix2.hermitianTraceless.add_mem (edgeForm_value_mem h _) (edgeForm_value_mem h _))
    (edgeForm_value_mem h _)) (edgeForm_value_mem h _)
abbrev _root_.YangMills.SharedProofs.p81306 := @edgeCoboundary_mem
private theorem coe_toSublattice (hL : 0 < L) {i i' : ℤ} (h : i ≤ i')
    (y : PeriodicLattice.Site L n i) :
    ((y.toSublattice i' : PeriodicLattice.Site L n i') : PeriodicLattice.FourTorus L n) = y := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
private theorem restrictVertexFunction_restrict (hL : 0 < L) (l : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction (j + 1) (restrictVertexFunction j l) = restrictVertexFunction (j + 1) l := by
  funext x
  simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap]
  congr 1
  apply Subtype.ext
  rw [coe_toSublattice hL (by simp [PeriodicLattice.levelDepth] <;> omega),
    coe_toSublattice hL (by simp [PeriodicLattice.levelDepth] <;> omega),
    coe_toSublattice hL (by simp [PeriodicLattice.levelDepth] <;> omega)]
end Forms
section Movements
variable {L n k : ℕ}
private theorem linearTransport_step (ξ : LevelForms L n k) {j : ℕ} (hj : j < k) :
    linearTransport ξ (j + 1) = linearSmoothing L n k j (linearTransport ξ j) +
      (ξ.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) := by
  rw [linearTransport, dif_pos hj]
private theorem linearTransport_of_base (ξ : LevelForms L n k) (hξ : ξ.2 = 0) :
    ∀ j, j ≤ k → linearTransport ξ j = linearSmoothingIter L n k j ξ.1 := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    rw [linearTransport_step ξ hj, ih hj.le, hξ]
    simp only [Pi.zero_apply, ZeroMemClass.coe_zero, add_zero]
    rfl
abbrev _root_.YangMills.SharedProofs.p62364 := @linearTransport_of_base
private theorem linearTransport_of_gauge (hL : 0 < L)
    (hstep : ∀ j, j < k → TrivialLinearization.OneStepIdentities L n k j)
    (l : vertexFunctionSpace L n k 0) (ξ : LevelForms L n k)
    (hξ1 : (ξ.1 : Edge L n k 0 → ComplexMatrix2) =
      vertexCoboundary (l : Vertex L n k 0 → ComplexMatrix2))
    (hξ : ξ.2 = 0) : ∀ j, j ≤ k →
      linearTransport ξ j =
        vertexCoboundary (restrictVertexFunction j (l : Vertex L n k 0 → ComplexMatrix2)) := by
  intro j
  induction j with
  | zero =>
    intro _
    have e : restrictVertexFunction 0 (l : Vertex L n k 0 → ComplexMatrix2) = l := by
      funext x
      simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap]
      exact congrArg _ (Subtype.ext (coe_toSublattice hL le_rfl x))
    rw [e]
    exact hξ1
  | succ j ih =>
    intro h
    have hj : j < k := h
    have hm : restrictVertexFunction j (l : Vertex L n k 0 → ComplexMatrix2) ∈
        vertexFunctionSpace L n k j :=
      fun y _ => l.2 _ trivial
    rw [linearTransport_step ξ hj, ih hj.le, ((hstep j hj).2 _ hm).1,
      restrictVertexFunction_restrict hL, hξ]
    simp only [Pi.zero_apply, ZeroMemClass.coe_zero, add_zero]
abbrev _root_.YangMills.SharedProofs.p55879 := @linearTransport_of_gauge
end Movements
private theorem exists_riesz_rep {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] (p : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hp : ∀ x, p x x = 0 → x = 0)
    (φ : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) : ∃ T : F →ₗ[ℝ] E, ∀ f e, p (T f) e = φ f e := by apply _root_.YangMills.SharedProofs.p13845 <;> assumption
section Chain
variable {L n k : ℕ} {j : ℕ}
private theorem edgePairing_add_right [Finite (PositiveEdge L n k j)]
    (X Y Y' : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing X (Y + Y') = edgeFormPairing X Y + edgeFormPairing X Y' :=
  tracePairing_add_right _ _ _
private theorem edgePairing_smul_right [Finite (PositiveEdge L n k j)] (r : ℝ)
    (X Y : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing X (r • Y) = (r : ℂ) * edgeFormPairing X Y :=
  tracePairing_smul_right _ _ _
private theorem edgePairing_comm [Finite (PositiveEdge L n k j)]
    (X Y : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing X Y = edgeFormPairing Y X :=
  tracePairing_comm _ _
private theorem edgePairing_zero_right [Finite (PositiveEdge L n k j)]
    (X : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing X (0 : Edge L n k j → ComplexMatrix2) = 0 :=
  tracePairing_zero_right _
private theorem edgePairing_self [Finite (PositiveEdge L n k j)]
    (hI : FaceSums.PairingIsInner ↥(univ : Set (PositiveEdge L n k j)))
    (B : edgeFormSpace L n k j) :
    0 ≤ (edgeFormPairing (B : Edge L n k j → ComplexMatrix2) B).re ∧
      ((edgeFormPairing (B : Edge L n k j → ComplexMatrix2) B).re = 0 → B = 0) := by apply _root_.YangMills.SharedProofs.p90865 <;> assumption
variable [hF0 : Finite (PositiveEdge L n k 0)]
  [hF : ∀ i : Fin k, Finite (PositiveEdge L n k ((i : ℕ) + 1))]
private theorem levelPairing_add_left (ξ ξ' η : LevelForms L n k) :
    levelPairing (formValues (ξ + ξ')) (formValues η) =
      levelPairing (formValues ξ) (formValues η) + levelPairing (formValues ξ') (formValues η) := by apply _root_.YangMills.SharedProofs.p57549 <;> assumption
private theorem levelPairing_smul_left (r : ℝ) (ξ η : LevelForms L n k) :
    levelPairing (formValues (r • ξ)) (formValues η) =
      r * levelPairing (formValues ξ) (formValues η) := by apply _root_.YangMills.SharedProofs.p29192 <;> assumption
private theorem levelPairing_comm (ξ η : LevelForms L n k) :
    levelPairing (formValues ξ) (formValues η) = levelPairing (formValues η) (formValues ξ) := by apply _root_.YangMills.SharedProofs.p11971 <;> assumption
private def levelForm : LevelForms L n k →ₗ[ℝ] LevelForms L n k →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun ξ η => levelPairing (formValues ξ) (formValues η)) levelPairing_add_left
    (fun r ξ η => by rw [levelPairing_smul_left, smul_eq_mul])
    (fun ξ η η' => by
      rw [levelPairing_comm, levelPairing_add_left, levelPairing_comm η, levelPairing_comm η'])
    (fun r ξ η => by rw [levelPairing_comm, levelPairing_smul_left, levelPairing_comm η,
      smul_eq_mul])
private theorem levelForm_apply (ξ η : LevelForms L n k) :
    levelForm ξ η = levelPairing (formValues ξ) (formValues η) := rfl
private theorem levelForm_definite
    (hI0 : FaceSums.PairingIsInner ↥(univ : Set (PositiveEdge L n k 0)))
    (hI : ∀ i : Fin k, FaceSums.PairingIsInner
      ↥(univ : Set (PositiveEdge L n k ((i : ℕ) + 1))))
    (ξ : LevelForms L n k) (h : levelForm ξ ξ = 0) : ξ = 0 := by
  rw [levelForm_apply] at h
  simp only [levelPairing, formValues] at h
  have h0 := (edgePairing_self hI0 ξ.1).1
  have hi := fun i => (edgePairing_self (hI i) (ξ.2 i)).1
  have hs : 0 ≤ ∑ i : Fin k,
      (edgeFormPairing (ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) (ξ.2 i)).re :=
    Finset.sum_nonneg fun i _ => hi i
  have e0 : (edgeFormPairing (ξ.1 : Edge L n k 0 → ComplexMatrix2) ξ.1).re = 0 := by linarith
  have es : ∑ i : Fin k,
      (edgeFormPairing (ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) (ξ.2 i)).re = 0 := by
    linarith
  have ei := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hi i).mp es
  refine Prod.ext ((edgePairing_self hI0 ξ.1).2 e0) (funext fun i => ?_)
  exact (edgePairing_self (hI i) (ξ.2 i)).2 (ei i (Finset.mem_univ i))
end Chain
section Fibre
variable {L n m : ℕ}
private def withLastNoise (Y : ChainPoint L n (m + 1))
    (ν : PositiveEdge L n (m + 1) (m + 1) → ComplexMatrix2) : ChainPoint L n (m + 1) :=
  ⟨Y.fine, fun i => Fin.lastCases
    (motive := fun i : Fin (m + 1) => PositiveEdge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2) ν
    (fun i' => Y.noise (Fin.castSucc i')) i⟩
private theorem withLastNoise_last (Y : ChainPoint L n (m + 1))
    (ν : PositiveEdge L n (m + 1) (m + 1) → ComplexMatrix2) (c : PositiveEdge L n (m + 1) (m + 1)) :
    (withLastNoise Y ν).noise (Fin.last m) c = ν c := by
  simp [withLastNoise]
private theorem withLastNoise_castSucc (Y : ChainPoint L n (m + 1))
    (ν : PositiveEdge L n (m + 1) (m + 1) → ComplexMatrix2) (i : Fin m)
    (c : PositiveEdge L n (m + 1) ((i : ℕ) + 1)) :
    (withLastNoise Y ν).noise (Fin.castSucc i) c = Y.noise (Fin.castSucc i) c := by
  simp [withLastNoise]
private theorem levelField_withLastNoise (Y : ChainPoint L n (m + 1))
    (ν : PositiveEdge L n (m + 1) (m + 1) → ComplexMatrix2) :
    ∀ j, j ≤ m → levelField (withLastNoise Y ν) j = levelField Y j := by apply _root_.YangMills.DeltaSharedProofs.p501532 <;> assumption
private theorem fibre_identity {a b D : ComplexMatrix2} (ha : a⁻¹ * a = 1) (hb : b * b⁻¹ = 1) :
    Complex.I • (-(ComplexMatrix2.conjugateBy a (Complex.I⁻¹ • (D * b⁻¹)))) * a =
      (a * b) * (-(b⁻¹ * D * b⁻¹)) := by apply _root_.YangMills.SharedProofs.p6296 <;> assumption
private def lastNoiseTangent (ν : edgeFormSpace L n (m + 1) (m + 1)) : LevelForms L n (m + 1) :=
  (0, Pi.single (Fin.last m) ν)
private theorem exists_chainAction_linear_deriv (hT : TowerFacts L n (m + 1)) (a : ℝ) :
    ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ X : ChainPoint L n (m + 1),
      (∀ b, ComplexMatrix2.operatorNorm (X.fine b - 1) < ε₂) →
      (∀ i c, ComplexMatrix2.operatorNorm (X.noise i c - 1) < ε₂) →
      ∃ Lf : PointCoords L n (m + 1) → ℝ,
        (∀ (Y : ℝ → ChainPoint L n (m + 1)) (v : PointCoords L n (m + 1)), Y 0 = X →
        (∀ b, HasDerivAt (fun t => (Y t).fine b) (v.1 b) 0) →
        (∀ i c, HasDerivAt (fun t => (Y t).noise i c) (v.2 i c) 0) →
        HasDerivAt (fun t => chainAction a (Y t)) (Lf v) 0) ∧
      (∀ v v', Lf (v + v') = Lf v + Lf v') ∧ ∀ (r : ℝ) v, Lf (r • v) = r • Lf v := by
  letI hFb : Fintype (Edge L n (m + 1) 0) :=
    @Fintype.ofFinite _ (hT.edges_finite 0 (Nat.zero_le _))
  letI hFq : ∀ i : Fin (m + 1), Fintype (PositiveEdge L n (m + 1) ((i : ℕ) + 1)) := fun i =>
    @Fintype.ofFinite _ (hT.posEdges_finite _ i.2)
  let toPt : PointCoords L n (m + 1) → ChainPoint L n (m + 1) := fun p => ⟨p.1, p.2⟩
  let p₀ : PointCoords L n (m + 1) := (fun _ => 1, fun _ _ => 1)
  have hb : ∀ b, ContDiffAt ℝ 2 (fun p : PointCoords L n (m + 1) => (toPt p).fine b) p₀ :=
    fun b => ContDiff.contDiffAt (by simp only [toPt]; fun_prop)
  have hn : ∀ i c, ContDiffAt ℝ 2 (fun p : PointCoords L n (m + 1) => (toPt p).noise i c) p₀ :=
    fun i c => ((contDiff_pi.mp ((contDiff_pi.mp contDiff_snd) i)) c).contDiffAt
  have h0 : toPt p₀ = unitPoint L n (m + 1) := rfl
  have hA := contDiffAt_chainAction hT hb hn h0 a
  have hev : ∀ᶠ p in 𝓝 p₀, ContDiffAt ℝ 2 (fun p => chainAction a (toPt p)) p :=
    hA.eventually (by simp)
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε₂, hε₂, fun X h1 h2 => ?_⟩
  have hd : dist ((X.fine, X.noise) : PointCoords L n (m + 1)) p₀ < ε₂ := by
    rw [dist_eq_norm, Prod.norm_def, max_lt_iff]
    exact ⟨(pi_norm_lt_iff hε₂).mpr fun b => h1 b,
      (pi_norm_lt_iff hε₂).mpr fun i => (pi_norm_lt_iff hε₂).mpr fun c => h2 i c⟩
  have hD := ((hball hd).differentiableAt (by norm_num)).hasFDerivAt
  set D := fderiv ℝ (fun p => chainAction a (toPt p))
    ((X.fine, X.noise) : PointCoords L n (m + 1)) with hDd
  refine ⟨fun v => D v, fun Y v hY hb' hn' => ?_, fun v v' => map_add D v v',
    fun r v => map_smul D r v⟩
  have hp : HasDerivAt (fun t => (((Y t).fine, (Y t).noise) : PointCoords L n (m + 1))) v 0 :=
    (hasDerivAt_pi.mpr hb').prodMk
      (hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun c => hn' i c)
  have hD' : HasFDerivAt (fun p => chainAction a (toPt p)) D
      (((Y 0).fine, (Y 0).noise) : PointCoords L n (m + 1)) := by
    rw [hY]
    exact hD
  exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hD' hp
end Fibre
section Zero
variable {L n m : ℕ}
set_option maxHeartbeats 1000000 in
private theorem leftDeriv_fibre_eq_zero
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n (m + 1)) (hEL : ComplexMatrix2.ExpLogEstimates)
    {ρ : ℝ} (hρ : NearOneBounds L n (m + 1) ρ) {a : ℝ} {X : ChainPoint L n (m + 1)}
    (hX : IsCompactValued X)
    (hleast : ∀ X' : ChainPoint L n (m + 1), IsCompactValued X' →
      levelField X' (m + 1) = levelField X (m + 1) → chainAction a X ≤ chainAction a X')
    (hnear : ∀ j, j ≤ m + 1 → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ)
    {Lf : PointCoords L n (m + 1) → ℝ}
    (hLf : ∀ (Y : ℝ → ChainPoint L n (m + 1)) (v : PointCoords L n (m + 1)), Y 0 = X →
      (∀ b, HasDerivAt (fun t => (Y t).fine b) (v.1 b) 0) →
      (∀ i c, HasDerivAt (fun t => (Y t).noise i c) (v.2 i c) 0) →
      HasDerivAt (fun t => chainAction a (Y t)) (Lf v) 0)
    (η₀ : LevelForms L n (m + 1)) (hη₀ : η₀.2 (Fin.last m) = 0)
    (M₀ : edgeFormSpace L n (m + 1) (m + 1))
    (hM₀ : (M₀ : Edge L n (m + 1) (m + 1) → ComplexMatrix2) = tangentTransport X η₀ (m + 1)) :
    leftDeriv (chainAction a) X (η₀ - lastNoiseTangent M₀) = 0 := by
  have hm : m < m + 1 := Nat.lt_succ_self m
  have hX0 : X.fine ∈ fieldSpace L n (m + 1) 0 := hX.2 0 (Nat.zero_le _)
  have hXc := mem_fieldsIn_of_mem hX0
  have hY0 := expMove_zero hXc η₀
  set Y : ℝ → ChainPoint L n (m + 1) := fun t => expMove (t • η₀) X with hY
  have hvel := hasDerivAt_levelField_expMove hd hT hρ hX hnear η₀
  have hnearY : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, j ≤ m + 1 → ∀ b,
      ComplexMatrix2.operatorNorm (levelField (Y t) j b - 1) < ρ := by
    have h : ∀ j ∈ Finset.range (m + 2), ∀ᶠ t in 𝓝 (0 : ℝ), ∀ b,
        ComplexMatrix2.operatorNorm (levelField (Y t) j b - 1) < ρ := by
      intro j hj
      have hj' : j ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      haveI := hT.edges_finite j hj'
      refine Filter.eventually_all.mpr fun b => ?_
      have h1 := ((hvel j hj' b).continuousAt).tendsto
      have h2 : Tendsto (fun t => ‖levelField (Y t) j b - 1‖) (𝓝 0)
          (𝓝 ‖levelField X j b - 1‖) := by
        have h3 := (h1.sub_const (1 : ComplexMatrix2)).norm
        simpa only [hY, hY0] using h3
      exact h2.eventually_lt_const (hnear j hj' b)
    have h' := (Filter.eventually_all_finset _).mpr h
    filter_upwards [h'] with t ht j hj
    exact ht j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  have hYreal : ∀ᶠ t in 𝓝 (0 : ℝ), IsCompactValued (Y t) := by
    filter_upwards [hnearY] with t ht
    refine compact_of_near hT hρ (fun i c => ?_) ?_ ht
    · refine ComplexMatrix2.specialUnitary.mul_mem (matExp_I_mem_compact hEL ?_) (hX.1 i c)
      exact ComplexMatrix2.hermitianTraceless.smul_mem t ((η₀.2 i).2.1 c.1 c.2)
    · exact expTwist_mem_fieldSpace hT (Nat.zero_le _) hX0 η₀.1 t
  set W := levelField X (m + 1) with hW
  have hWc : W ∈ fieldSpace L n (m + 1) (m + 1) := hX.2 _ le_rfl
  let ν : ℝ → PositiveEdge L n (m + 1) (m + 1) → ComplexMatrix2 := fun t c =>
    W c.1 * (normalizedMean (levelField (Y t) m) c.1)⁻¹
  let Γ : ℝ → ChainPoint L n (m + 1) := fun t => withLastNoise (Y t) (ν t)
  haveI := hT.sites_finite m hm.le
  have hΓ : ∀ᶠ t in 𝓝 (0 : ℝ), IsCompactValued (Γ t) ∧ levelField (Γ t) (m + 1) = W := by
    filter_upwards [hYreal, hnearY] with t ht hn
    have hVm := ht.2 m hm.le
    have hVc := mem_fieldsIn_of_mem hVm
    have hu : ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented →
        normalizedMean (levelField (Y t) m) c ∈ PeriodicLattice.compactGaugeGroup := by
      intro c hc
      obtain ⟨-, -, -, hu, -⟩ := hρ m hm _ hVc (hn m hm.le) c hc
      exact normalizedMean_mem_compact hVm c hu
    have hpos : ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented →
        levelField (Γ t) (m + 1) c = W c := by
      intro c hc
      rw [levelField_succ_pos _ hm c hc, levelField_withLastNoise _ _ m le_rfl]
      have e : (Γ t).noise ⟨m, hm⟩ ⟨c, hc⟩ =
          W c * (normalizedMean (levelField (Y t) m) c)⁻¹ :=
        withLastNoise_last (Y t) (ν t) ⟨c, hc⟩
      rw [e, mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_compact (hu c hc)), mul_one]
    have htop : levelField (Γ t) (m + 1) = W := by
      funext c
      by_cases hc : c.IsPositivelyOriented
      · exact hpos c hc
      · have hc' := (oriented_or_opposite c).resolve_left hc
        rw [levelField_opposite _ hm c hc hc', hpos _ hc', hWc.2 c (Set.mem_univ _)]
        exact Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_compact (hWc.1 c (Set.mem_univ _)))
    refine ⟨⟨fun i c => ?_, fun j hj => ?_⟩, htop⟩
    · induction i using Fin.lastCases with
      | last =>
        show (withLastNoise (Y t) (ν t)).noise (Fin.last m) c ∈ _
        rw [withLastNoise_last]
        exact ComplexMatrix2.specialUnitary.mul_mem (hWc.1 _ (Set.mem_univ _)) (inv_mem_compact (hu _ c.2))
      | cast i =>
        show (withLastNoise (Y t) (ν t)).noise (Fin.castSucc i) c ∈ _
        rw [withLastNoise_castSucc]
        exact ht.1 _ c
    · rcases Nat.lt_or_eq_of_le hj with h | h
      · rw [levelField_withLastNoise _ _ j (Nat.lt_succ_iff.mp h)]
        exact ht.2 j h.le
      · subst h
        rw [htop]
        exact hWc
  have hmin : ∀ᶠ t in 𝓝 (0 : ℝ), chainAction a X ≤ chainAction a (Γ t) := by
    filter_upwards [hΓ] with t ht
    exact hleast _ ht.1 ht.2
  set η' : LevelForms L n (m + 1) := η₀ - lastNoiseTangent M₀ with hη'
  have hZ0 : Y 0 = X := hY0
  let v : PointCoords L n (m + 1) := (velocity X.fine η₀.1, fun i c =>
    Complex.I • (η'.2 i : Edge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2) c.1 * X.noise i c)
  have hη'1 : η'.1 = η₀.1 := by simp [hη', lastNoiseTangent]
  have hη'c : ∀ i : Fin m, η'.2 (Fin.castSucc i) = η₀.2 (Fin.castSucc i) := by
    intro i
    simp [hη', lastNoiseTangent, Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne]
  have hη'l : η'.2 (Fin.last m) = -M₀ := by
    simp [hη', lastNoiseTangent, hη₀]
  have h2 := hLf (fun t => expMove (t • η') X) v (expMove_zero hXc η')
    (fun b => by
      show HasDerivAt _ (velocity X.fine η₀.1 b) 0
      rw [← hη'1]
      exact hasDerivAt_expTwist_line hXc η'.1.2.2 b)
    (fun i c => (hasDerivAt_expLine _).mul_const _)
  have hXm := mem_fieldsIn_of_mem (hX.2 m hm.le)
  have hwc : ∀ c : PositiveEdge L n (m + 1) (m + 1),
      normalizedMean (levelField X m) c.1 ∈ PeriodicLattice.compactGaugeGroup ∧
      W c.1 = X.noise (Fin.last m) c * normalizedMean (levelField X m) c.1 := by
    intro c
    obtain ⟨-, -, -, hu, -⟩ := hρ m hm _ hXm (hnear m hm.le) c.1 c.2
    exact ⟨normalizedMean_mem_compact (hX.2 m hm.le) c.1 hu, levelField_succ_pos X hm c.1 c.2⟩
  have hΓ0 : Γ 0 = X := by
    have e1 : (Γ 0).fine = X.fine := by
      show (Y 0).fine = X.fine
      rw [hZ0]
    have e2 : (Γ 0).noise = X.noise := by
      funext i c
      induction i using Fin.lastCases with
      | last =>
        show (withLastNoise (Y 0) (ν 0)).noise (Fin.last m) c = _
        rw [withLastNoise_last]
        show W c.1 * (normalizedMean (levelField (Y 0) m) c.1)⁻¹ = _
        rw [hZ0, (hwc c).2, mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det_compact (hwc c).1),
          mul_one]
      | cast i =>
        show (withLastNoise (Y 0) (ν 0)).noise (Fin.castSucc i) c = _
        rw [withLastNoise_castSucc, hZ0]
    calc Γ 0 = ⟨(Γ 0).fine, (Γ 0).noise⟩ := rfl
      _ = ⟨X.fine, X.noise⟩ := by rw [e1, e2]
      _ = X := rfl
  have hlast : ∀ c : PositiveEdge L n (m + 1) (m + 1), HasDerivAt
      (fun t => (Γ t).noise (Fin.last m) c) (v.2 (Fin.last m) c) 0 := by
    intro c
    obtain ⟨-, -, -, hu, D, hD⟩ := hρ m hm _ hXm (hnear m hm.le) c.1 c.2
    have h1' := hD _ (fun t => levelField (Y t) m) (by simp only [hZ0]) (fun b => hvel m hm.le b)
    have h0 : PeriodicLattice.expTwist ((0 : ℝ) • tangentTransport X η₀ m) (levelField X m) =
        levelField X m := by
      rw [zero_smul]
      exact expTwist_zero hXm
    have h2' := hD _ (fun t => PeriodicLattice.expTwist (t • tangentTransport X η₀ m)
      (levelField X m)) h0
      (fun b => hasDerivAt_expTwist_line hXm (transport_opposite hT X η₀ m hm.le) b)
    have hmd := leftDifferential_eq hd c.2 h2' (by rw [h0]) hu
    have hdet : Matrix.det ((fun t => normalizedMean (levelField (Y t) m) c.1) 0) = 1 := by
      simp only [hZ0]
      exact hu
    have hinv := hasDerivAt_inv_of_det_one hd h1' hdet
    have hν := hinv.const_mul (W c.1)
    have e : (fun t => (Γ t).noise (Fin.last m) c) = fun t =>
        W c.1 * (normalizedMean (levelField (Y t) m) c.1)⁻¹ := by
      funext t
      exact withLastNoise_last (Y t) (ν t) c
    rw [e]
    refine hν.congr_deriv ?_
    simp only [hZ0]
    have hMc : (M₀ : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1 =
        ComplexMatrix2.conjugateBy (X.noise (Fin.last m) c)
        (Complex.I⁻¹ • (D (velocity (levelField X m) (tangentTransport X η₀ m)) *
          (normalizedMean (levelField X m) c.1)⁻¹)) := by
      rw [hM₀]
      have hm1 := transport_succ_pos X η₀ hm c.1 c.2
      rw [hmd] at hm1
      have hz : (η₀.2 ⟨m, hm⟩ : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1 = 0 := by
        have : η₀.2 ⟨m, hm⟩ = 0 := hη₀
        rw [this]
        rfl
      rw [hz, add_zero] at hm1
      exact hm1
    have hv2 : v.2 (Fin.last m) c =
        Complex.I • (-(M₀ : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1) *
        X.noise (Fin.last m) c := by
      have e5 : (η'.2 (Fin.last m)).1 c.1 = -(M₀ : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1 := by
        rw [hη'l]
        rfl
      rw [← e5]
    rw [hv2, hMc, (hwc c).2]
    have hna : (X.noise (Fin.last m) c)⁻¹ * X.noise (Fin.last m) c = 1 :=
      Matrix.nonsing_inv_mul _ (isUnit_det_compact (hX.1 (Fin.last m) c))
    have hub : normalizedMean (levelField X m) c.1 * (normalizedMean (levelField X m) c.1)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (isUnit_det_compact (hwc c).1)
    exact (fibre_identity hna hub).symm
  have h1 := hLf Γ v hΓ0
    (fun b => hasDerivAt_expTwist_line hXc η₀.1.2.2 b)
    (fun i c => by
      induction i using Fin.lastCases with
      | last => exact hlast c
      | cast i =>
        have e : (fun t => (Γ t).noise (Fin.castSucc i) c) =
            fun t => (Y t).noise (Fin.castSucc i) c := by
          funext t
          exact withLastNoise_castSucc (Y t) (ν t) i c
        rw [e]
        show HasDerivAt _ (Complex.I • (η'.2 (Fin.castSucc i) :
          Edge L n (m + 1) (((Fin.castSucc i : Fin (m + 1)) : ℕ) + 1) → ComplexMatrix2) c.1 *
            X.noise _ c) 0
        rw [hη'c]
        exact (hasDerivAt_expLine _).mul_const _)
  have hmin' : IsLocalMin (fun t => chainAction a (Γ t)) 0 := by
    filter_upwards [hmin] with t ht
    simp only [hΓ0]
    exact ht
  have hz := hmin'.hasDerivAt_eq_zero h1
  rw [leftDeriv, h2.deriv, hz]
end Zero
section Lagrange
variable {L n m : ℕ}
private theorem leftDifferential_zero (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {j : ℕ} {V : Edge L n (m + 1) j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n (m + 1) j PeriodicLattice.complexGaugeGroup)
    {c : Edge L n (m + 1) (j + 1)} (hc : c.IsPositivelyOriented)
    (hu : Matrix.det (normalizedMean V c) = 1) :
    leftDifferential normalizedMean V (0 : Edge L n (m + 1) j → ComplexMatrix2) c = 0 := by apply _root_.YangMills.SharedProofs.p6898 <;> assumption
private theorem transport_lastNoiseTangent
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n (m + 1)) {ρ : ℝ} (hρ : NearOneBounds L n (m + 1) ρ)
    {X : ChainPoint L n (m + 1)} (hX : IsCompactValued X)
    (hnear : ∀ j, j ≤ m + 1 → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ)
    (ν : edgeFormSpace L n (m + 1) (m + 1)) :
    tangentTransport X (lastNoiseTangent ν) (m + 1) = ν := by
  have hm : m < m + 1 := Nat.lt_succ_self m
  have hpos : ∀ (j : ℕ) (hj : j < m + 1), tangentTransport X (lastNoiseTangent ν) j = 0 →
      ∀ c : Edge L n (m + 1) (j + 1), ∀ hc : c.IsPositivelyOriented,
        tangentTransport X (lastNoiseTangent ν) (j + 1) c =
          ((lastNoiseTangent ν).2 ⟨j, hj⟩ : Edge L n (m + 1) (j + 1) → ComplexMatrix2) c := by
    intro j hj h0 c hc
    obtain ⟨-, -, -, hu, -⟩ := hρ j hj _ (mem_fieldsIn_of_mem (hX.2 j hj.le)) (hnear j hj.le) c hc
    rw [transport_succ_pos X _ hj c hc, h0,
      leftDifferential_zero hd (mem_fieldsIn_of_mem (hX.2 j hj.le)) hc hu]
    simp [ComplexMatrix2.conjugateBy]
  have hlow : ∀ j, j ≤ m → tangentTransport X (lastNoiseTangent ν) j = 0 := by
    intro j
    induction j with
    | zero => exact fun _ => rfl
    | succ j ih =>
      intro h
      have hj : j < m + 1 := by omega
      have hz : ∀ c : Edge L n (m + 1) (j + 1), c.IsPositivelyOriented →
          tangentTransport X (lastNoiseTangent ν) (j + 1) c = 0 := by
        intro c hc
        rw [hpos j hj (ih (by omega)) c hc]
        have hne : (⟨j, hj⟩ : Fin (m + 1)) ≠ Fin.last m := by
          intro h'
          have := congrArg Fin.val h'
          simp at this
          omega
        simp only [lastNoiseTangent]
        rw [Pi.single_eq_of_ne hne]
        rfl
      funext c
      by_cases hc : c.IsPositivelyOriented
      · exact hz c hc
      · have hc' := (oriented_or_opposite c).resolve_left hc
        have e := transport_opposite hT X (lastNoiseTangent ν) (j + 1) (by omega) c.opposite
        rw [edge_opposite_opposite] at e
        rw [e, hz _ hc']
        simp
  have hp := hpos m hm (hlow m le_rfl)
  funext c
  by_cases hc : c.IsPositivelyOriented
  · rw [hp c hc]
    show ((lastNoiseTangent ν).2 (Fin.last m)).1 c = _
    simp only [lastNoiseTangent, Pi.single_eq_same]
  · have hc' := (oriented_or_opposite c).resolve_left hc
    have e := transport_opposite hT X (lastNoiseTangent ν) (m + 1) le_rfl c.opposite
    rw [edge_opposite_opposite] at e
    have e2 := ν.2.2 c.opposite
    rw [edge_opposite_opposite] at e2
    rw [e, hp _ hc', e2]
    show -((lastNoiseTangent ν).2 (Fin.last m)).1 c.opposite = _
    simp only [lastNoiseTangent, Pi.single_eq_same]
private theorem levelForm_lastNoiseTangent [Finite (PositiveEdge L n (m + 1) 0)]
    [∀ i : Fin (m + 1), Finite (PositiveEdge L n (m + 1) ((i : ℕ) + 1))]
    (J : LevelForms L n (m + 1)) (ν : edgeFormSpace L n (m + 1) (m + 1)) :
    levelForm J (lastNoiseTangent ν) = (edgeFormPairing (J.2 (Fin.last m)).1
      (ν : Edge L n (m + 1) (m + 1) → ComplexMatrix2)).re := by
  rw [levelForm_apply]
  simp only [levelPairing, formValues, lastNoiseTangent]
  have e0 : ((0 : edgeFormSpace L n (m + 1) 0) : Edge L n (m + 1) 0 → ComplexMatrix2) = 0 := rfl
  rw [e0, edgePairing_zero_right]
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi]
    have e1 : ((0 : edgeFormSpace L n (m + 1) ((i : ℕ) + 1)) :
        Edge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2) = 0 := rfl
    rw [e1, edgePairing_zero_right]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h
private theorem isTopMultiplier_of_minimizer
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n (m + 1)) (hEL : ComplexMatrix2.ExpLogEstimates)
    {ρ : ℝ} (hρ : NearOneBounds L n (m + 1) ρ) {a : ℝ} {X : ChainPoint L n (m + 1)}
    (hX : IsCompactValued X)
    (hleast : ∀ X' : ChainPoint L n (m + 1), IsCompactValued X' →
      levelField X' (m + 1) = levelField X (m + 1) → chainAction a X ≤ chainAction a X')
    (hnear : ∀ j, j ≤ m + 1 → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ)
    {Lf : PointCoords L n (m + 1) → ℝ}
    (hLf : ∀ (Y : ℝ → ChainPoint L n (m + 1)) (v : PointCoords L n (m + 1)), Y 0 = X →
      (∀ b, HasDerivAt (fun t => (Y t).fine b) (v.1 b) 0) →
      (∀ i c, HasDerivAt (fun t => (Y t).noise i c) (v.2 i c) 0) →
      HasDerivAt (fun t => chainAction a (Y t)) (Lf v) 0)
    {J : LevelForms L n (m + 1)} (hJ : IsLevelGradient (chainAction a) X J) :
    IsTopMultiplier X J (J.2 (Fin.last m)) := by
  haveI : Finite (PositiveEdge L n (m + 1) 0) := hT.posEdges_finite 0 (Nat.zero_le _)
  haveI : ∀ i : Fin (m + 1), Finite (PositiveEdge L n (m + 1) ((i : ℕ) + 1)) :=
    fun i => hT.posEdges_finite _ i.2
  haveI : Finite (PositiveEdge L n (m + 1) (m + 1)) := hT.posEdges_finite _ le_rfl
  obtain ⟨T, hTv⟩ := exists_transport_linearMap hd hT hρ hX hnear (m + 1) le_rfl
  have hTop : ∀ ξ, (topDeriv X ξ : Edge L n (m + 1) (m + 1) → ComplexMatrix2) = T ξ := fun ξ => by
    rw [topDeriv_eq hd hT hρ hX hnear ξ, hTv]
  have hTi : ∀ ν, T (lastNoiseTangent ν) = ν := fun ν =>
    Subtype.ext (by rw [hTv]; exact transport_lastNoiseTangent hd hT hρ hX hnear ν)
  intro η
  set μ : edgeFormSpace L n (m + 1) (m + 1) := J.2 (Fin.last m) with hμ
  set ηl : edgeFormSpace L n (m + 1) (m + 1) := η.2 (Fin.last m) with hηl
  set η₀ : LevelForms L n (m + 1) := η - lastNoiseTangent ηl with hη₀
  have h0 : η₀.2 (Fin.last m) = 0 := by
    simp [hη₀, lastNoiseTangent, hηl]
  set M₀ := T η₀ with hM₀
  have hz := leftDeriv_fibre_eq_zero hd hT hEL hρ hX hleast hnear hLf η₀ h0 M₀ (hTv η₀)
  have hz' : levelForm J (η₀ - lastNoiseTangent M₀) = 0 := by
    rw [levelForm_apply, hJ, hz]
  have hsum : η = η₀ + lastNoiseTangent ηl := by simp [hη₀]
  have e1 : levelPairing (formValues J) (formValues η) = levelForm J η := rfl
  have e2 : levelForm J η = levelForm J η₀ + levelForm J (lastNoiseTangent ηl) := by
    rw [← map_add, ← hsum]
  have e3 : levelForm J η₀ = levelForm J (lastNoiseTangent M₀) := by
    rw [map_sub, sub_eq_zero] at hz'
    exact hz'
  have e4 : T η = M₀ + ηl := by
    have e5 : T η = T η₀ + T (lastNoiseTangent ηl) := by rw [← map_add, ← hsum]
    rw [e5, hTi]
  rw [e1, e2, e3, levelForm_lastNoiseTangent, levelForm_lastNoiseTangent, hTop, e4,
    Submodule.coe_add, edgePairing_add_right, Complex.add_re]
end Lagrange
section Null
variable {L n k j : ℕ}
private theorem hasDerivAt_linear_of_forms {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [Finite (PositiveEdge L n k j)] [FiniteDimensional ℝ (edgeFormSpace L n k j)]
    (Ξ : edgeFormSpace L n k j →ₗ[ℝ] G) {Y : ℝ → edgeFormSpace L n k j}
    {Y' : edgeFormSpace L n k j}
    (h : ∀ b, b.IsPositivelyOriented → HasDerivAt (fun s => (Y s : Edge L n k j → ComplexMatrix2) b)
      ((Y' : Edge L n k j → ComplexMatrix2) b) 0) :
    HasDerivAt (fun s => Ξ (Y s)) (Ξ Y') 0 := by
  letI := Fintype.ofFinite (PositiveEdge L n k j)
  let ρ : edgeFormSpace L n k j →ₗ[ℝ] (PositiveEdge L n k j → ComplexMatrix2) :=
    { toFun := fun B => restrictToPositiveEdges (B : Edge L n k j → ComplexMatrix2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker ρ = ⊥ := by
    rw [LinearMap.ker_eq_bot, injective_iff_map_eq_zero]
    intro B hB
    exact Subtype.ext (edgeForm_eq_zero B.2 hB)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ρ hker
  let Λ : (PositiveEdge L n k j → ComplexMatrix2) →L[ℝ] G :=
    LinearMap.toContinuousLinearMap (Ξ ∘ₗ g)
  have hρ : HasDerivAt (fun s => ρ (Y s)) (ρ Y') 0 :=
    hasDerivAt_pi.mpr fun b => h b.1 b.2
  have h2 := Λ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hρ
  have e : ∀ B, Λ (ρ B) = Ξ B := by
    intro B
    have := LinearMap.congr_fun hg B
    simp only [Λ, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply]
    exact congrArg Ξ this
  rw [e] at h2
  have e2 : (Λ ∘ fun s => ρ (Y s)) = fun s => Ξ (Y s) := by
    funext s
    exact e _
  rw [e2] at h2
  exact h2
private abbrev unitVector (μ : Fin 4) : Fin 4 → ℤ := Pi.single μ 1
private theorem const_of_unit_steps {α : Type*} (f : (Fin 4 → ℤ) → α)
    (h : ∀ z μ, f (z + unitVector μ) = f z) (z : Fin 4 → ℤ) : f z = f 0 := by
  have hline : ∀ (w : Fin 4 → ℤ) (μ : Fin 4) (n : ℤ), f (w + n • unitVector μ) = f w := by
    intro w μ n
    induction n using Int.induction_on with
    | zero => simp
    | succ m ih =>
      rw [add_smul, one_smul, ← add_assoc, h, ih]
    | pred m ih =>
      rw [← ih, ← h (w + (-(m : ℤ) - 1) • unitVector μ) μ, add_assoc, ← add_one_zsmul]
      simp
  have hz : z = (((0 + z 0 • unitVector 0) + z 1 • unitVector 1) + z 2 • unitVector 2) +
      z 3 • unitVector 3 := by
    funext ρ
    fin_cases ρ <;> simp
  rw [hz, hline, hline, hline, hline]
abbrev _root_.YangMills.DeltaSharedProofs.p501362 := @const_of_unit_steps
private theorem const_of_vertexCoboundary_zero
    (lc : PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k j))
    {g : Vertex L n k j → ComplexMatrix2} (h : vertexCoboundary g = 0) (x : Vertex L n k j) :
    g x = g 0 := by
  let sc : (Fin 4 → ℤ) → Vertex L n k j := fun z =>
    ∑ μ, z μ • PeriodicLattice.unitStep L n _ μ
  have hs : ∀ z μ, sc (z + unitVector μ) = sc z + PeriodicLattice.unitStep L n _ μ := by
    intro z μ
    simp only [sc, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single μ]
    · simp
    · intro ρ _ hr
      simp [Pi.single_eq_of_ne hr]
    · intro hh
      exact absurd (Finset.mem_univ μ) hh
  have hstep : ∀ z μ, g (sc (z + unitVector μ)) = g (sc z) := by
    intro z μ
    have h1 := congrFun h (PeriodicLattice.Bond.forwardFrom (sc z) μ)
    simp only [vertexCoboundary, Pi.zero_apply, PeriodicLattice.Bond.forwardFrom] at h1
    rw [hs]
    exact sub_eq_zero.mp h1
  obtain ⟨z, hz⟩ := lc.2.2.2.1 0 x
  have hz' : x = sc z := by
    simpa only [PeriodicLattice.offsetSite, zero_add, sc] using hz
  have h0 : sc 0 = 0 := by simp [sc]
  rw [hz']
  have := const_of_unit_steps (fun z => g (sc z)) hstep z
  simp only [h0] at this
  exact this
private theorem eq_zero_of_hessian_null {a : ℝ} (ha : 0 < a)
    (hK : Tower.ClosedInSmoothingKernelIsExact)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n)
    [Finite (PositiveEdge L n k 0)] [Finite (Face L n k 0)]
    [∀ i : Fin k, Finite (PositiveEdge L n k ((i : ℕ) + 1))]
    (innP : FaceSums.PairingIsInner ↥(univ : Set (Face L n k 0)))
    (inn0 : FaceSums.PairingIsInner ↥(univ : Set (PositiveEdge L n k 0)))
    (innI : ∀ i : Fin k, FaceSums.PairingIsInner
      ↥(univ : Set (PositiveEdge L n k ((i : ℕ) + 1))))
    (hstep : ∀ j, j < k → TrivialLinearization.OneStepIdentities L n k j)
    (lc : PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k k))
    {ξ : LevelForms L n k} (h1 : hessianAtIdentity a ξ ξ = 0) (h2 : linearTransport ξ k = 0)
    (h3 : ∀ κ ∈ topVanishingGauges L n k,
      (edgeFormPairing (ξ.1 : Edge L n k 0 → ComplexMatrix2)
      (vertexCoboundary (κ : Vertex L n k 0 → ComplexMatrix2))).re = 0) : ξ = 0 := by
  have hLpos : 0 < L := by have := hL.2; omega
  have hA := (tracePairing_self innP (edgeCoboundary (ξ.1 : Edge L n k 0 → ComplexMatrix2))
    (edgeCoboundary_mem ξ.1.2))
  have hi := fun i => (edgePairing_self (innI i) (ξ.2 i)).1
  have hS : 0 ≤ ∑ i : Fin k,
      (edgeFormPairing (ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) (ξ.2 i)).re :=
    Finset.sum_nonneg fun i _ => hi i
  simp only [hessianAtIdentity] at h1
  have hA0 : (traceFinsumPairing (edgeCoboundary (ξ.1 : Edge L n k 0 → ComplexMatrix2))
      (edgeCoboundary (ξ.1 : Edge L n k 0 → ComplexMatrix2))).re = 0 := by
    have := hA.1
    nlinarith
  have hS0 : ∑ i : Fin k,
      (edgeFormPairing (ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) (ξ.2 i)).re = 0 := by
    have := hA.1
    have h4 : 0 ≤ a * ∑ i : Fin k,
        (edgeFormPairing (ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) (ξ.2 i)).re := by
      positivity
    have h5 : a * ∑ i : Fin k,
        (edgeFormPairing (ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) (ξ.2 i)).re = 0 := by
      linarith
    exact (mul_eq_zero.mp h5).resolve_left ha.ne'
  have hclosed : edgeCoboundary (ξ.1 : Edge L n k 0 → ComplexMatrix2) = 0 := hA.2 hA0
  have hei := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hi i).mp hS0
  have hξ2 : ξ.2 = 0 :=
    funext fun i => (edgePairing_self (innI i) (ξ.2 i)).2 (hei i (Finset.mem_univ i))
  have h4 := linearTransport_of_base ξ hξ2 k le_rfl
  rw [h2] at h4
  obtain ⟨l, hl, hd⟩ := hK L hL k n hk hn _ ξ.1.2 hclosed h4.symm
  have h5 := linearTransport_of_gauge hLpos hstep ⟨l, hl⟩ ξ hd.symm hξ2 k le_rfl
  rw [h2] at h5
  set g := restrictVertexFunction k l with hg
  have hc : ∀ y, g y = g 0 := fun y => const_of_vertexCoboundary_zero lc h5.symm y
  have hg0 : g 0 ∈ ComplexMatrix2.hermitianTraceless := hl _ trivial
  let κ : vertexFunctionSpace L n k 0 := ⟨fun x => l x - g 0, fun x _ =>
    ComplexMatrix2.hermitianTraceless.sub_mem (hl x trivial) hg0⟩
  have hκ : κ ∈ topVanishingGauges L n k := by
    intro y
    show l _ - g 0 = 0
    have e : l (y.toSublattice (PeriodicLattice.levelDepth k 0)) = g y := rfl
    rw [e, hc y, sub_self]
  have hdκ : vertexCoboundary (κ : Vertex L n k 0 → ComplexMatrix2) =
      (ξ.1 : Edge L n k 0 → ComplexMatrix2) := by
    rw [← hd]
    funext b
    simp only [vertexCoboundary, κ]
    abel
  have h6 := h3 κ hκ
  rw [hdκ] at h6
  exact Prod.ext ((edgePairing_self inn0 ξ.1).2 h6) hξ2
end Null
section FirstFacts
variable {L n k N : ℕ}
private theorem levelField_chart_facts
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n k) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : NearOneBounds L n k ρ)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {j : ℕ} (hj : j ≤ k) (b : Edge L n k j) :
    DifferentiableAt ℝ (fun w => levelField (chartPoint e w) j b) 0 ∧
    levelField (chartPoint e 0) j b = 1 ∧
    ∀ v, fderiv ℝ (fun w => levelField (chartPoint e w) j b) 0 v =
      Complex.I • linearTransport (e v).1 j b := by
  obtain ⟨h1, h2⟩ := chartPoint_levelFields (m := 2) hT e j hj
  have hdf := (h1 b).differentiableAt (by norm_num)
  refine ⟨hdf, by rw [h2], fun v => ?_⟩
  have hl0 : HasDerivAt (fun τ : ℝ => τ • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hF : HasFDerivAt (fun w => levelField (chartPoint e w) j b)
      (fderiv ℝ (fun w => levelField (chartPoint e w) j b) 0) ((0 : ℝ) • v) := by
    rw [zero_smul]
    exact hdf.hasFDerivAt
  have hc := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hF hl0
  have hcu := hasDerivAt_levelField_chart hd hT hρ0 hρ e (c := fun τ : ℝ => τ • v) (by simp)
    (t := e v) (by simpa using hl0) j hj b
  exact hc.unique hcu
private theorem gaugeVariation_chart_facts
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n k) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : NearOneBounds L n k ρ)
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) {κ : Vertex L n k 0 → ComplexMatrix2}
    (hκ : ∀ x, κ x ∈ ComplexMatrix2.hermitianTraceless) :
    DifferentiableAt ℝ (fun w => distanceGaugeVariation (chartPoint e w).fine κ) 0 ∧
    distanceGaugeVariation (chartPoint e 0).fine κ = 0 ∧
    ∀ v, fderiv ℝ (fun w => distanceGaugeVariation (chartPoint e w).fine κ) 0 v =
      (edgeFormPairing ((e v).1.1 : Edge L n k 0 → ComplexMatrix2) (vertexCoboundary κ)).re := by
  letI hFb : Fintype (PositiveEdge L n k 0) :=
    @Fintype.ofFinite _ (hT.posEdges_finite 0 (Nat.zero_le _))
  have e0 : (fun w => distanceGaugeVariation (chartPoint e w).fine κ) = fun w =>
      ∑ b : PositiveEdge L n k 0,
        reHalfTrace (Complex.I • κ b.1.source * (chartPoint e w).fine b.1 -
        (chartPoint e w).fine b.1 * Complex.I • κ b.1.target) := by
    funext w
    simp only [distanceGaugeVariation, finsum_eq_sum_of_fintype]
    rfl
  have hU := fun b : Edge L n k 0 => levelField_chart_facts hd hT hρ0 hρ e (Nat.zero_le k) b
  have hUd : ∀ b : Edge L n k 0, DifferentiableAt ℝ (fun w => (chartPoint e w).fine b) 0 :=
    fun b => (hU b).1
  have hdiff : DifferentiableAt ℝ (fun w => distanceGaugeVariation (chartPoint e w).fine κ) 0 := by
    rw [e0]
    refine DifferentiableAt.fun_sum fun b _ => ?_
    exact reHalfTrace.differentiableAt.comp _ (((differentiableAt_const _).mul (hUd b.1)).sub
      ((hUd b.1).mul (differentiableAt_const _)))
  have hval : distanceGaugeVariation (chartPoint e 0).fine κ = 0 := by
    refine (congrFun e0 0).trans (Finset.sum_eq_zero fun b _ => ?_)
    have h1 : (chartPoint e 0).fine b.1 = 1 := (hU b.1).2.1
    rw [h1, mul_one, one_mul, ← smul_sub]
    exact reHalfTrace_I_smul (ComplexMatrix2.hermitianTraceless.sub_mem (hκ _) (hκ _))
  refine ⟨hdiff, hval, fun v => ?_⟩
  have hl0 : HasDerivAt (fun τ : ℝ => τ • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hF : HasFDerivAt (fun w => distanceGaugeVariation (chartPoint e w).fine κ)
      (fderiv ℝ (fun w => distanceGaugeVariation (chartPoint e w).fine κ) 0) ((0 : ℝ) • v) := by
    rw [zero_smul]
    exact hdiff.hasFDerivAt
  have hc := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hF hl0
  have hb : ∀ b : Edge L n k 0, HasDerivAt (fun τ : ℝ => (chartPoint e (τ • v)).fine b)
      (Complex.I • ((e v).1.1 : Edge L n k 0 → ComplexMatrix2) b) 0 := fun b =>
    hasDerivAt_levelField_chart hd hT hρ0 hρ e (c := fun τ : ℝ => τ • v) (by simp) (t := e v)
      (by simpa using hl0) 0 (Nat.zero_le _) b
  have hs : HasDerivAt (fun τ : ℝ => ∑ b : PositiveEdge L n k 0,
      reHalfTrace (Complex.I • κ b.1.source * (chartPoint e (τ • v)).fine b.1 -
        (chartPoint e (τ • v)).fine b.1 * Complex.I • κ b.1.target))
      (∑ b : PositiveEdge L n k 0, reHalfTrace (Complex.I • κ b.1.source *
        (Complex.I • ((e v).1.1 : Edge L n k 0 → ComplexMatrix2) b.1) -
        (Complex.I • ((e v).1.1 : Edge L n k 0 → ComplexMatrix2) b.1) *
          Complex.I • κ b.1.target)) 0 :=
    HasDerivAt.fun_sum fun b _ => reHalfTrace.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (((hb b.1).const_mul _).sub ((hb b.1).mul_const _))
  have e2 : ((fun w => distanceGaugeVariation (chartPoint e w).fine κ) ∘ fun τ : ℝ => τ • v) =
      fun τ : ℝ =>
      ∑ b : PositiveEdge L n k 0,
        reHalfTrace (Complex.I • κ b.1.source * (chartPoint e (τ • v)).fine b.1 -
        (chartPoint e (τ • v)).fine b.1 * Complex.I • κ b.1.target) := by
    funext τ
    exact congrFun e0 (τ • v)
  rw [e2] at hc
  rw [hc.unique hs, re_edgeFormPairing]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∀ A C : ComplexMatrix2, reHalfTrace (Complex.I • C * (Complex.I • A) -
      (Complex.I • A) * Complex.I • κ b.1.target)
      = reHalfTrace (A * κ b.1.target) - reHalfTrace (A * C) := by
    intro A C
    rw [map_sub]
    have e3 := neg_reHalfTrace_I_I C A
    have e4 := neg_reHalfTrace_I_I A (κ b.1.target)
    rw [reHalfTrace_mul_comm C A] at e3
    linarith
  rw [h1]
  simp only [vertexCoboundary, mul_sub, map_sub]
end FirstFacts
section CandidatePoint
variable {L n m N : ℕ}
private theorem eventually_expMove_near_compact
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n (m + 1)) (hEL : ComplexMatrix2.ExpLogEstimates)
    {ρ : ℝ} (hρ : NearOneBounds L n (m + 1) ρ) {X : ChainPoint L n (m + 1)}
    (hX : IsCompactValued X)
    (hnear : ∀ j, j ≤ m + 1 → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ)
    (η : LevelForms L n (m + 1)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (∀ j, j ≤ m + 1 → ∀ b,
      ComplexMatrix2.operatorNorm (levelField (expMove (t • η) X) j b - 1) < ρ) ∧
        IsCompactValued (expMove (t • η) X) := by
  have hX0 : X.fine ∈ fieldSpace L n (m + 1) 0 := hX.2 0 (Nat.zero_le _)
  have hY0 := expMove_zero (mem_fieldsIn_of_mem hX0) η
  have hvel := hasDerivAt_levelField_expMove hd hT hρ hX hnear η
  have hnearY : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, j ≤ m + 1 → ∀ b,
      ComplexMatrix2.operatorNorm (levelField (expMove (t • η) X) j b - 1) < ρ := by
    have h : ∀ j ∈ Finset.range (m + 2), ∀ᶠ t in 𝓝 (0 : ℝ), ∀ b,
        ComplexMatrix2.operatorNorm (levelField (expMove (t • η) X) j b - 1) < ρ := by
      intro j hj
      have hj' : j ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      haveI := hT.edges_finite j hj'
      refine Filter.eventually_all.mpr fun b => ?_
      have h1 := ((hvel j hj' b).continuousAt).tendsto
      have h2 : Tendsto (fun t : ℝ => ‖levelField (expMove (t • η) X) j b - 1‖) (𝓝 0)
          (𝓝 ‖levelField X j b - 1‖) := by
        have h3 := (h1.sub_const (1 : ComplexMatrix2)).norm
        simpa only [hY0] using h3
      exact h2.eventually_lt_const (hnear j hj' b)
    have h' := (Filter.eventually_all_finset _).mpr h
    filter_upwards [h'] with t ht j hj
    exact ht j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  filter_upwards [hnearY] with t ht
  refine ⟨ht, compact_of_near hT hρ (fun i c => ?_) ?_ ht⟩
  · refine ComplexMatrix2.specialUnitary.mul_mem (matExp_I_mem_compact hEL ?_) (hX.1 i c)
    exact ComplexMatrix2.hermitianTraceless.smul_mem t ((η.2 i).2.1 c.1 c.2)
  · exact expTwist_mem_fieldSpace hT (Nat.zero_le _) hX0 η.1 t
private theorem linearTransport_low {ξ η : LevelForms L n (m + 1)} (h1 : ξ.1 = η.1)
    (h2 : ∀ i : Fin m, ξ.2 (Fin.castSucc i) = η.2 (Fin.castSucc i)) :
    ∀ j, j ≤ m → linearTransport ξ j = linearTransport η j := by
  intro j
  induction j with
  | zero =>
    intro _
    show (ξ.1 : Edge L n (m + 1) 0 → ComplexMatrix2) = η.1
    rw [h1]
  | succ j ih =>
    intro h
    have hj : j < m + 1 := by omega
    have hjm : j < m := h
    rw [linearTransport_succ ξ hj, linearTransport_succ η hj, ih hjm.le]
    have := h2 ⟨j, hjm⟩
    congr 2
set_option maxHeartbeats 1000000 in
private theorem hasDerivAt_last_noise (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n (m + 1)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : NearOneBounds L n (m + 1) ρ)
    (B : edgeFormSpace L n (m + 1) (m + 1)) (η₀ : LevelForms L n (m + 1))
    (c : Edge L n (m + 1) (m + 1)) (hc : c.IsPositivelyOriented) :
    HasDerivAt (fun s : ℝ => PeriodicLattice.expTwist
        (s • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2))
        (fun _ => 1) c *
          (normalizedMean (levelField (expMove (s • η₀) (unitPoint L n (m + 1))) m) c)⁻¹)
      (Complex.I • ((B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c -
        linearSmoothing L n (m + 1) m (linearTransport η₀ m) c)) 0 := by
  have hm : m < m + 1 := Nat.lt_succ_self m
  have h1c := mem_fieldsIn_of_mem (const_one_mem (L := L) (n := n) (k := m + 1) (j := m + 1))
  have hW := hasDerivAt_expTwist_line h1c B.2.2 c
  rw [velocity_one] at hW
  have hfl := unitPoint_near hT hρ0
  have hfr := unitPoint_compact hT
  have hY0 := expMove_zero (X := unitPoint L n (m + 1))
    (mem_fieldsIn_of_mem (hfr.2 0 (Nat.zero_le _))) η₀
  have hvel := hasDerivAt_levelField_expMove hd hT hρ hfr hfl η₀
  have hf := levelField_unitPoint hT m hm.le
  obtain ⟨-, -, -, hu, D, hD⟩ :=
    hρ m hm _ (mem_fieldsIn_of_mem (hfr.2 m hm.le)) (hfl m hm.le) c hc
  have h1 := hD _ (fun s => levelField (expMove (s • η₀) (unitPoint L n (m + 1))) m)
    (by simp only [hY0]) (fun b => hvel m hm.le b)
  have hMa := transport_opposite hT (unitPoint L n (m + 1)) η₀ m hm.le
  have h0 : PeriodicLattice.expTwist ((0 : ℝ) • tangentTransport (unitPoint L n (m + 1)) η₀ m)
      (levelField (unitPoint L n (m + 1)) m) = levelField (unitPoint L n (m + 1)) m := by
    rw [zero_smul]
    exact expTwist_zero (mem_fieldsIn_of_mem (hfr.2 m hm.le))
  have h2 := hD _ (fun s => PeriodicLattice.expTwist
    (s • tangentTransport (unitPoint L n (m + 1)) η₀ m)
    (levelField (unitPoint L n (m + 1)) m)) h0
    (fun b => hasDerivAt_expTwist_line (mem_fieldsIn_of_mem (hfr.2 m hm.le)) hMa b)
  have hmd := leftDifferential_eq hd hc h2 (by rw [h0]) hu
  have hone : normalizedMean (levelField (unitPoint L n (m + 1)) m) c = 1 := by
    rw [hf]
    exact (hT.at_one m hm c hc).2.2
  have hmap : leftDifferential normalizedMean (levelField (unitPoint L n (m + 1)) m)
      (tangentTransport (unitPoint L n (m + 1)) η₀ m) c =
      linearSmoothing L n (m + 1) m (linearTransport η₀ m) c := by
    rw [hf, transport_unitPoint hT η₀ m hm.le]
    exact hT.deriv_at_one m hm _ (linearTransport_mem hT η₀ m hm.le) c hc
  rw [hmap, hone, inv_one, mul_one] at hmd
  set Dg := D (velocity (levelField (unitPoint L n (m + 1)) m)
    (tangentTransport (unitPoint L n (m + 1)) η₀ m)) with hDg
  have hDg' : Dg = Complex.I • linearSmoothing L n (m + 1) m (linearTransport η₀ m) c := by
    rw [hmd, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
  have hu0 : (fun s : ℝ =>
      normalizedMean (levelField (expMove (s • η₀) (unitPoint L n (m + 1))) m) c) 0 = 1 := by
    simp only [hY0]
    exact hone
  set U : ℝ → ComplexMatrix2 := fun s =>
    normalizedMean (levelField (expMove (s • η₀) (unitPoint L n (m + 1))) m) c with hU
  have hinv : HasDerivAt (fun s => (U s)⁻¹) (-Dg) 0 :=
    ((hd.1 univ U U U Dg Dg Dg Filter.univ_mem h1 h1 h1).2.1 hu0).2.1
  have hp := hW.mul hinv
  refine hp.congr_deriv ?_
  have hW0 : PeriodicLattice.expTwist ((0 : ℝ) • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2))
      (fun _ => 1) c = 1 := by
    rw [zero_smul, expTwist_zero h1c]
  have hU0 : U 0 = 1 := hu0
  simp only [hW0, hU0, inv_one, mul_one, one_mul, smul_sub, hDg']
  rw [← sub_eq_add_neg]
end CandidatePoint
section Cand
variable {L n m N : ℕ}
private def lastNoiseTangentL :
    edgeFormSpace L n (m + 1) (m + 1) →ₗ[ℝ] LevelForms L n (m + 1) where
  toFun := lastNoiseTangent
  map_add' ν ν' := by
    refine Prod.ext (by simp [lastNoiseTangent]) ?_
    simp only [lastNoiseTangent, Prod.snd_add]
    exact Pi.single_add (f := fun i : Fin (m + 1) => edgeFormSpace L n (m + 1) ((i : ℕ) + 1))
      (Fin.last m) ν ν'
  map_smul' r ν := by
    refine Prod.ext (by simp [lastNoiseTangent]) ?_
    simp only [lastNoiseTangent, RingHom.id_apply, Prod.smul_snd]
    exact Pi.single_smul (f := fun i : Fin (m + 1) => edgeFormSpace L n (m + 1) ((i : ℕ) + 1))
      (Fin.last m) r ν
set_option maxHeartbeats 1000000 in
private theorem exists_candidate_curve
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n (m + 1)) (hEL : ComplexMatrix2.ExpLogEstimates)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : NearOneBounds L n (m + 1) ρ)
    [FiniteDimensional ℝ (edgeFormSpace L n (m + 1) (m + 1))]
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n (m + 1)) (B : edgeFormSpace L n (m + 1) (m + 1))
    {ξh : LevelForms L n (m + 1)}
    (hB : linearTransport ξh (m + 1) = (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2)) :
    ∃ wc : ℝ → Fin N → ℝ, wc 0 = 0 ∧ HasDerivAt wc (e.symm (ξh, 0, 0)) 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℝ), IsCompactValued (chartPoint e (wc s)) ∧
        levelField (chartPoint e (wc s)) (m + 1) =
        PeriodicLattice.expTwist (s • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2))
          fun _ => 1 := by
  have hm : m < m + 1 := Nat.lt_succ_self m
  haveI := hT.posEdges_finite (m + 1) le_rfl
  haveI := hT.edges_finite (m + 1) le_rfl
  haveI := hT.sites_finite m hm.le
  set ηl : edgeFormSpace L n (m + 1) (m + 1) := ξh.2 (Fin.last m) with hηl
  set η₀ : LevelForms L n (m + 1) := ξh - lastNoiseTangent ηl with hη₀
  have hη₀l : η₀.2 (Fin.last m) = 0 := by simp [hη₀, lastNoiseTangent, hηl]
  have hη₀1 : ξh.1 = η₀.1 := by simp [hη₀, lastNoiseTangent]
  have hη₀c : ∀ i : Fin m, ξh.2 (Fin.castSucc i) = η₀.2 (Fin.castSucc i) := by
    intro i
    simp [hη₀, lastNoiseTangent, Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne]
  have hfr := unitPoint_compact hT
  have hfl := unitPoint_near hT hρ0
  have hcurve := eventually_expMove_near_compact hd hT hEL hρ hfr hfl η₀
  set Y : ℝ → ChainPoint L n (m + 1) := fun s => expMove (s • η₀) (unitPoint L n (m + 1)) with hY
  set W : ℝ → Edge L n (m + 1) (m + 1) → ComplexMatrix2 := fun s =>
    PeriodicLattice.expTwist (s • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2))
      fun _ => 1 with hW
  have h1c := const_one_mem (L := L) (n := n) (k := m + 1) (j := m + 1)
  have hWr : ∀ s, W s ∈ fieldSpace L n (m + 1) (m + 1) := fun s =>
    expTwist_mem_fieldSpace hT le_rfl h1c B s
  let nn : ℝ → Edge L n (m + 1) (m + 1) → ComplexMatrix2 := fun s c =>
    W s c * (normalizedMean (levelField (Y s) m) c)⁻¹
  have hplain : ∀ c, (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c -
      linearSmoothing L n (m + 1) m (linearTransport η₀ m) c =
      (ηl : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c := by
    intro c
    have h1 := linearTransport_succ ξh hm
    rw [hB, linearTransport_low hη₀1 hη₀c m le_rfl] at h1
    rw [h1]
    simp [hηl]
    rfl
  have hdn : ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented →
      HasDerivAt (fun s => nn s c)
      (Complex.I • (ηl : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c) 0 := by
    intro c hc
    have h := hasDerivAt_last_noise hd hT hρ0 hρ B η₀ c hc
    rw [hplain] at h
    exact h
  have hY0 : Y 0 = unitPoint L n (m + 1) :=
    expMove_zero (mem_fieldsIn_of_mem (hfr.2 0 (Nat.zero_le _))) η₀
  have hn0 : ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented → nn 0 c = 1 := by
    intro c hc
    have e1 : W 0 c = 1 := by
      simp only [hW, zero_smul]
      rw [expTwist_zero (mem_fieldsIn_of_mem h1c)]
    simp only [nn]
    rw [e1, hY0, levelField_unitPoint hT m hm.le, (hT.at_one m hm c hc).2.2]
    simp
  classical
  let Hs : ℝ → Edge L n (m + 1) (m + 1) → ComplexMatrix2 := fun s c =>
    Complex.I⁻¹ • ComplexMatrix2.logSeries (nn s c)
  have hHd : ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented →
      HasDerivAt (fun s => Hs s c)
      ((ηl : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c) 0 := by
    intro c hc
    have hN := hdn c hc
    have hl := ((hd.1 univ (fun s => nn s c) (fun s => nn s c) (fun s => nn s c) _ _ _
      Filter.univ_mem hN hN hN).2.1 (hn0 c hc)).2.2.1
    have h2 := hl.const_smul Complex.I⁻¹
    refine h2.congr_deriv ?_
    rw [smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  have hc1 : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented →
      ComplexMatrix2.operatorNorm (nn s c - 1) < 1 := by
    refine Filter.eventually_all.mpr fun c => ?_
    by_cases hc : c.IsPositivelyOriented
    · have h1 := ((hdn c hc).continuousAt).tendsto
      have h2 : Tendsto (fun s => ‖nn s c - 1‖) (𝓝 0) (𝓝 0) := by
        have h3 := (h1.sub_const (1 : ComplexMatrix2)).norm
        simpa [hn0 c hc] using h3
      filter_upwards [h2.eventually_lt_const one_pos] with s hs _
      exact hs
    · exact Filter.Eventually.of_forall fun s h => absurd h hc
  have hgood : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented →
      nn s c ∈ PeriodicLattice.compactGaugeGroup ∧ ComplexMatrix2.operatorNorm (nn s c - 1) < 1 ∧
      normalizedMean (levelField (Y s) m) c ∈ PeriodicLattice.compactGaugeGroup := by
    filter_upwards [hcurve, hc1] with s hs h2 c hc
    obtain ⟨-, -, -, hu, -⟩ :=
      hρ m hm _ (mem_fieldsIn_of_mem (hs.2.2 m hm.le)) (hs.1 m hm.le) c hc
    have hur := normalizedMean_mem_compact (hs.2.2 m hm.le) c hu
    exact ⟨ComplexMatrix2.specialUnitary.mul_mem ((hWr s).1 c (Set.mem_univ _)) (inv_mem_compact hur),
      h2 c hc, hur⟩
  have hlie : ∀ (s : ℝ) (c : Edge L n (m + 1) (m + 1)),
      nn s c ∈ PeriodicLattice.compactGaugeGroup →
      ComplexMatrix2.operatorNorm (nn s c - 1) < 1 →
      Hs s c ∈ ComplexMatrix2.hermitianTraceless ∧
        ComplexMatrix2.matExp (Complex.I • Hs s c) = nn s c := by
    intro s c h1 h2
    obtain ⟨hu, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp h1
    obtain ⟨H, -, hlog, -, h3, -, h5⟩ := hEL.2.2.2.2.2.2.2.1 (nn s c) hu h2
    have e1 : Hs s c = H := by
      simp only [Hs]
      rw [hlog, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
    rw [e1]
    exact ⟨(h5 hdet).2.1, h3⟩
  have hlog1 : ComplexMatrix2.logSeries 1 = 0 := by
    have h := (hEL.2.2.2.2.1 0 (by
      have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      simpa [ComplexMatrix2.operatorNorm] using this)).2
    have e1 : ComplexMatrix2.matExp 0 = 1 := NormedSpace.exp_zero
    rwa [e1] at h
  let fV : ℝ → Edge L n (m + 1) (m + 1) → ComplexMatrix2 := fun s c =>
    if c.IsPositivelyOriented then Hs s c else 0
  let Ys : ℝ → edgeFormSpace L n (m + 1) (m + 1) := fun s =>
    if h : ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented →
        Hs s c ∈ ComplexMatrix2.hermitianTraceless then
      ⟨extendOddly (fV s), ⟨fun b hb => by
        simp only [extendOddly, if_pos hb, fV]
        exact h b hb, fun b => extendOddly_opposite hT le_rfl _ b⟩⟩
    else 0
  have hYs : ∀ s, (∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented →
      Hs s c ∈ ComplexMatrix2.hermitianTraceless) →
      ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented →
        (Ys s : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c = Hs s c := by
    intro s h c hc
    simp only [Ys, dif_pos h, extendOddly, if_pos hc, fV]
  have hH0 : ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented → Hs 0 c = 0 := by
    intro c hc
    simp only [Hs]
    rw [hn0 c hc, hlog1, smul_zero]
  have hsu0 : ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented →
      Hs 0 c ∈ ComplexMatrix2.hermitianTraceless := fun c hc => by
    rw [hH0 c hc]
    exact ComplexMatrix2.hermitianTraceless.zero_mem
  have hYs0 : Ys 0 = 0 := by
    refine Subtype.ext (edgeForm_eq_zero (Ys 0).2 ?_)
    funext b
    show (Ys 0 : Edge L n (m + 1) (m + 1) → ComplexMatrix2) b.1 = 0
    rw [hYs 0 hsu0 b.1 b.2, hH0 b.1 b.2]
  have hYd : ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented → HasDerivAt
      (fun s => (Ys s : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c)
      ((ηl : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c) 0 := by
    intro c hc
    refine (hHd c hc).congr_of_eventuallyEq ?_
    filter_upwards [hgood] with s hs
    exact hYs s (fun c' hc' => (hlie s c' (hs c' hc').1 (hs c' hc').2.1).1) c hc
  let Λ₀ : LevelForms L n (m + 1) →ₗ[ℝ] (Fin N → ℝ) :=
    e.symm.toLinearMap ∘ₗ LinearMap.inl ℝ _ _
  let Ξ : edgeFormSpace L n (m + 1) (m + 1) →ₗ[ℝ] (Fin N → ℝ) := Λ₀ ∘ₗ lastNoiseTangentL
  have hΞ := hasDerivAt_linear_of_forms Ξ hYd
  refine ⟨fun s => s • Λ₀ η₀ + Ξ (Ys s), ?_, ?_, ?_⟩
  · simp only [zero_smul, zero_add, hYs0, map_zero]
  · have h1 : HasDerivAt (fun s : ℝ => s • Λ₀ η₀) (Λ₀ η₀) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Λ₀ η₀)
    refine (h1.add hΞ).congr_deriv ?_
    have e1 : ξh = η₀ + lastNoiseTangentL ηl := by
      show ξh = η₀ + lastNoiseTangent ηl
      simp [hη₀]
    show _ = e.symm (ξh, 0, 0)
    conv_rhs => rw [e1]
    have e2 : Ξ ηl = Λ₀ (lastNoiseTangentL ηl) := rfl
    rw [e2, ← map_add]
    rfl
  filter_upwards [hcurve, hgood] with s hs hg
  have hsu := fun (c : Edge L n (m + 1) (m + 1)) (hc : c.IsPositivelyOriented) =>
    hlie s c (hg c hc).1 (hg c hc).2.1
  set ζ : LevelForms L n (m + 1) := s • η₀ + lastNoiseTangent (Ys s) with hζ
  have hew : e (s • Λ₀ η₀ + Ξ (Ys s)) = (ζ, 0, 0) := by
    have e1 : s • Λ₀ η₀ + Ξ (Ys s) = Λ₀ ζ := by
      simp only [hζ, map_add, map_smul]
      rfl
    rw [e1]
    simp [Λ₀]
    rfl
  have hζ1 : ζ.1 = (s • η₀).1 := by simp [hζ, lastNoiseTangent]
  have hζl : ζ.2 (Fin.last m) = Ys s := by
    simp [hζ, lastNoiseTangent, hη₀l]
  have hζc : ∀ i : Fin m, ζ.2 (Fin.castSucc i) = (s • η₀).2 (Fin.castSucc i) := by
    intro i
    simp [hζ, lastNoiseTangent, Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne]
  have hpt : chartPoint e (s • Λ₀ η₀ + Ξ (Ys s)) = withLastNoise (Y s) (fun c => nn s c.1) := by
    have e1 : (chartPoint e (s • Λ₀ η₀ + Ξ (Ys s))).fine =
        (withLastNoise (Y s) (fun c => nn s c.1)).fine := by
      simp only [chartPoint, hew]
      show PeriodicLattice.expTwist (ζ.1 : Edge L n (m + 1) 0 → ComplexMatrix2) _ =
        PeriodicLattice.expTwist ((s • η₀).1 : Edge L n (m + 1) 0 → ComplexMatrix2) _
      rw [hζ1]
    have e2 : (chartPoint e (s • Λ₀ η₀ + Ξ (Ys s))).noise =
        (withLastNoise (Y s) (fun c => nn s c.1)).noise := by
      funext i c
      simp only [chartPoint, hew]
      induction i using Fin.lastCases with
      | last =>
        rw [withLastNoise_last]
        show ComplexMatrix2.matExp (Complex.I • (ζ.2 (Fin.last m)).1 c.1) * 1 = _
        rw [hζl, mul_one]
        have e3 : (Ys s).1 c.1 = Hs s c.1 := hYs s (fun c' hc' => (hsu c' hc').1) c.1 c.2
        rw [e3]
        exact (hsu c.1 c.2).2
      | cast i =>
        rw [withLastNoise_castSucc]
        show ComplexMatrix2.matExp (Complex.I • (ζ.2 (Fin.castSucc i)).1 c.1) * 1 =
          ComplexMatrix2.matExp (Complex.I • ((s • η₀).2 (Fin.castSucc i)).1 c.1) * 1
        rw [hζc]
    calc chartPoint e (s • Λ₀ η₀ + Ξ (Ys s)) =
        ⟨(chartPoint e (s • Λ₀ η₀ + Ξ (Ys s))).fine,
          (chartPoint e (s • Λ₀ η₀ + Ξ (Ys s))).noise⟩ := rfl
      _ = ⟨(withLastNoise (Y s) (fun c => nn s c.1)).fine,
          (withLastNoise (Y s) (fun c => nn s c.1)).noise⟩ := by rw [e1, e2]
      _ = withLastNoise (Y s) (fun c => nn s c.1) := rfl
  rw [hpt]
  have hpos : ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented →
      levelField (withLastNoise (Y s) (fun c => nn s c.1)) (m + 1) c = W s c := by
    intro c hc
    rw [levelField_succ_pos _ hm c hc, levelField_withLastNoise _ _ m le_rfl]
    have e : (withLastNoise (Y s) (fun c => nn s c.1)).noise ⟨m, hm⟩ ⟨c, hc⟩ = nn s c :=
      withLastNoise_last (Y s) _ ⟨c, hc⟩
    rw [e]
    simp only [nn]
    rw [mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_compact (hg c hc).2.2), mul_one]
  have htop : levelField (withLastNoise (Y s) (fun c => nn s c.1)) (m + 1) = W s := by
    funext c
    by_cases hc : c.IsPositivelyOriented
    · exact hpos c hc
    · have hc' := (oriented_or_opposite c).resolve_left hc
      rw [levelField_opposite _ hm c hc hc', hpos _ hc', (hWr s).2 c (Set.mem_univ _)]
      exact Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_compact ((hWr s).1 c (Set.mem_univ _)))
  refine ⟨⟨fun i c => ?_, fun j hj => ?_⟩, htop⟩
  · induction i using Fin.lastCases with
    | last =>
      rw [withLastNoise_last]
      exact (hg c.1 c.2).1
    | cast i =>
      rw [withLastNoise_castSucc]
      exact hs.2.1 _ c
  · rcases Nat.lt_or_eq_of_le hj with h | h
    · rw [levelField_withLastNoise _ _ j (Nat.lt_succ_iff.mp h)]
      exact hs.2.2 j h.le
    · subst h
      rw [htop]
      exact hWr s
end Cand
section Minimiser
variable {L n m N : ℕ}
private def entryPartL (q : Fin 2 × Fin 2 × Bool) : ComplexMatrix2 →L[ℝ] ℝ :=
  if q.2.2 then Complex.reCLM.comp (entryL q.1 q.2.1) else Complex.imCLM.comp (entryL q.1 q.2.1)
private theorem eq_zero_of_entryParts {X : ComplexMatrix2} (h : ∀ q, entryPartL q X = 0) :
    X = 0 := by
  ext a b
  have h1 := h (a, b, true)
  have h2 := h (a, b, false)
  simp only [entryPartL, if_true, Bool.false_eq_true, if_false,
    ContinuousLinearMap.comp_apply] at h1 h2
  exact Complex.ext h1 h2
private theorem exists_hessian_minimizer
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n (m + 1)) (hEL : ComplexMatrix2.ExpLogEstimates)
    (hSG : PeriodicLattice.ActionNonnegAndGaugeInvariant)
    (hK : Tower.ClosedInSmoothingKernelIsExact)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : NearOneBounds L n (m + 1) ρ) {a : ℝ} (ha : 0 < a)
    [Finite (PositiveEdge L n (m + 1) 0)] [Finite (Face L n (m + 1) 0)]
    [∀ i : Fin (m + 1), Finite (PositiveEdge L n (m + 1) ((i : ℕ) + 1))]
    [Finite (PositiveEdge L n (m + 1) (m + 1))]
    (innP : FaceSums.PairingIsInner ↥(univ : Set (Face L n (m + 1) 0)))
    (inn0 : FaceSums.PairingIsInner ↥(univ : Set (PositiveEdge L n (m + 1) 0)))
    (innI : ∀ i : Fin (m + 1), FaceSums.PairingIsInner
      ↥(univ : Set (PositiveEdge L n (m + 1) ((i : ℕ) + 1))))
    (hstep : ∀ j, j < m + 1 → TrivialLinearization.OneStepIdentities L n (m + 1) j)
    (lc : PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth (m + 1) (m + 1)))
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n (m + 1))
    {r : ℕ} (κb : Module.Basis (Fin r) ℝ (topVanishingGauges L n (m + 1)))
    (B : edgeFormSpace L n (m + 1) (m + 1)) :
    ∃ vh : Fin N → ℝ, (e vh).2 = 0 ∧
      linearTransport (e vh).1 (m + 1) = (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) ∧
      (∀ j, fderiv ℝ (fun w => distanceGaugeVariation (chartPoint e w).fine
        (((κb j : vertexFunctionSpace L n (m + 1) 0) : Vertex L n (m + 1) 0 → ComplexMatrix2)))
          0 vh = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (v : Fin N → ℝ) (s : ℝ),
        (∀ c : PositiveEdge L n (m + 1) (m + 1),
          ComplexMatrix2.operatorNorm
            (fderiv ℝ (fun w => levelField (chartPoint e w) (m + 1) c.1) 0 (v - s • vh)) ≤
            δ * (‖v‖ + |s|)) →
        (∀ j, |fderiv ℝ (fun w => distanceGaugeVariation (chartPoint e w).fine
          (((κb j : vertexFunctionSpace L n (m + 1) 0) : Vertex L n (m + 1) 0 → ComplexMatrix2)))
            0 (v - s • vh)| ≤ δ * (‖v‖ + |s|)) →
        (e v).2 = 0 →
        fderiv ℝ (fderiv ℝ fun w => chainAction a (chartPoint e w)) 0 v v ≤
          s ^ 2 * fderiv ℝ (fderiv ℝ fun w => chainAction a (chartPoint e w)) 0 vh vh +
            δ * (‖v‖ ^ 2 + s ^ 2) → ‖v - s • vh‖ ≤ ε * |s| := by
  letI hFc : Fintype (PositiveEdge L n (m + 1) (m + 1)) := Fintype.ofFinite _
  obtain ⟨hf2, hf0, hf1, hHdiag⟩ := chainAction_second_order hd hT hEL hSG
    (Nat.succ_le_succ (Nat.zero_le m)) hL hn hρ0 hρ ha e
  set f : (Fin N → ℝ) → ℝ := fun w => chainAction a (chartPoint e w) with hf
  set Hs := fderiv ℝ (fderiv ℝ f) 0 with hHs
  have hsym : ∀ u v, Hs u v = Hs v u := by
    intro u v
    exact (hf2.isSymmSndFDerivAt (by simp)).eq u v
  have hpsd : ∀ v, 0 ≤ Hs v v := by
    intro v
    rw [hHdiag v]
    simp only [hessianAtIdentity]
    have h1 := (tracePairing_self innP
      (edgeCoboundary ((e v).1.1 : Edge L n (m + 1) 0 → ComplexMatrix2))
      (edgeCoboundary_mem (e v).1.1.2)).1
    have h2 : 0 ≤ ∑ i : Fin (m + 1),
        (edgeFormPairing ((e v).1.2 i : Edge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2)
        ((e v).1.2 i)).re := Finset.sum_nonneg fun i _ => (edgePairing_self (innI i) ((e v).1.2 i)).1
    positivity
  let A : PositiveEdge L n (m + 1) (m + 1) → (Fin N → ℝ) →L[ℝ] ComplexMatrix2 := fun c =>
    fderiv ℝ (fun w => levelField (chartPoint e w) (m + 1) c.1) 0
  let D : Fin r → (Fin N → ℝ) →L[ℝ] ℝ := fun j =>
    fderiv ℝ (fun w => distanceGaugeVariation (chartPoint e w).fine
      (((κb j : vertexFunctionSpace L n (m + 1) 0) : Vertex L n (m + 1) 0 → ComplexMatrix2))) 0
  let P3 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := LinearMap.toContinuousLinearMap
    (e.symm.toLinearMap ∘ₗ (LinearMap.inr ℝ _ _) ∘ₗ (LinearMap.snd ℝ _ _) ∘ₗ e.toLinearMap)
  have hA : ∀ c v, A c v = Complex.I • linearTransport (e v).1 (m + 1) c.1 := fun c v =>
    (levelField_chart_facts hd hT hρ0 hρ e le_rfl c.1).2.2 v
  have hD : ∀ j v, D j v = (edgeFormPairing ((e v).1.1 : Edge L n (m + 1) 0 → ComplexMatrix2)
      (vertexCoboundary
        (((κb j : vertexFunctionSpace L n (m + 1) 0) : Vertex L n (m + 1) 0 → ComplexMatrix2)))).re :=
    fun j v => (gaugeVariation_chart_facts hd hT hρ0 hρ e
      (fun x => (κb j : vertexFunctionSpace L n (m + 1) 0).2 x trivial)).2.2 v
  have hP3 : ∀ v, P3 v = e.symm (0, (e v).2) := fun v => rfl
  let ι := (PositiveEdge L n (m + 1) (m + 1) × (Fin 2 × Fin 2 × Bool)) ⊕ (Fin r ⊕ Fin N)
  let ψ : ι → (Fin N → ℝ) →L[ℝ] ℝ := Sum.elim (fun p => (entryPartL p.2).comp (A p.1))
    (Sum.elim D fun i => (ContinuousLinearMap.proj i).comp P3)
  have hP3z : ∀ v, (∀ i, (ψ (Sum.inr (Sum.inr i))) v = 0) → (e v).2 = 0 := by
    intro v h
    have h1 : P3 v = 0 := funext h
    rw [hP3] at h1
    have h2 := e.symm.map_eq_zero_iff.mp h1
    exact congrArg Prod.snd h2
  have hdef : ∀ v, Hs v v = 0 → (∀ i, ψ i v = 0) → v = 0 := by
    intro v h0 hψ
    have h1 : hessianAtIdentity a (e v).1 (e v).1 = 0 := by
      rw [← hHdiag v]
      exact h0
    have hpm : linearTransport (e v).1 (m + 1) = 0 := by
      refine edgeForm_eq_zero (linearTransport_mem hT _ _ le_rfl) ?_
      funext c
      have h2 : A c v = 0 := eq_zero_of_entryParts fun q => hψ (Sum.inl (c, q))
      rw [hA] at h2
      exact (smul_eq_zero.mp h2).resolve_left Complex.I_ne_zero
    have hl : ∀ κ ∈ topVanishingGauges L n (m + 1),
        (edgeFormPairing ((e v).1.1 : Edge L n (m + 1) 0 → ComplexMatrix2)
        (vertexCoboundary (κ : Vertex L n (m + 1) 0 → ComplexMatrix2))).re = 0 := by
      let ℓ : topVanishingGauges L n (m + 1) →ₗ[ℝ] ℝ :=
        { toFun := fun κ => (edgeFormPairing ((e v).1.1 : Edge L n (m + 1) 0 → ComplexMatrix2)
            (vertexCoboundary (((κ : vertexFunctionSpace L n (m + 1) 0)) :
              Vertex L n (m + 1) 0 → ComplexMatrix2))).re
          map_add' := fun x y => by
            simp only [Submodule.coe_add, vertexCoboundary_add, edgePairing_add_right,
              Complex.add_re]
          map_smul' := fun t x => by
            have e1 : vertexCoboundary (((t • x : topVanishingGauges L n (m + 1)) :
                vertexFunctionSpace L n (m + 1) 0) : Vertex L n (m + 1) 0 → ComplexMatrix2) =
                t • vertexCoboundary (((x : vertexFunctionSpace L n (m + 1) 0)) :
                  Vertex L n (m + 1) 0 → ComplexMatrix2) := by
              funext b
              simp [vertexCoboundary, smul_sub]
            simp only [e1, edgePairing_smul_right, RingHom.id_apply, smul_eq_mul,
              Complex.re_ofReal_mul] }
      have hℓ : ℓ = 0 := by
        refine κb.ext fun j => ?_
        have h2 := hψ (Sum.inr (Sum.inl j))
        show (edgeFormPairing _ _).re = 0
        rw [← hD]
        exact h2
      intro κ hκ
      exact LinearMap.congr_fun hℓ ⟨κ, hκ⟩
    have hz := eq_zero_of_hessian_null ha hK hL (Nat.succ_le_succ (Nat.zero_le m)) hn innP inn0
      innI hstep lc h1 hpm hl
    have h3 := hP3z v fun i => hψ (Sum.inr (Sum.inr i))
    have h4 : e v = 0 := Prod.ext hz h3
    exact e.map_eq_zero_iff.mp h4
  let v₀ : Fin N → ℝ := e.symm (lastNoiseTangent B, 0, 0)
  have hv₀ : e v₀ = (lastNoiseTangent B, 0, 0) := e.apply_symm_apply _
  obtain ⟨vh, hvals, hK0, hcore⟩ := quadratic_core Hs hsym hpsd ψ hdef v₀
  have hz2 : (e vh).2 = 0 := by
    refine hP3z vh fun i => ?_
    rw [hvals]
    show (P3 v₀) i = 0
    rw [hP3, hv₀]
    have : e.symm ((0 : LevelForms L n (m + 1)), ((0, 0) : LevelForms L n (m + 1) ×
      edgeFormSpace L n (m + 1) (m + 1))) = 0 := e.symm.map_zero
    show (e.symm (0, (0, 0))) i = 0
    rw [this]
    rfl
  have hinj : linearTransport (lastNoiseTangent B) (m + 1) =
      (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) := by
    rw [← transport_unitPoint hT _ (m + 1) le_rfl]
    exact transport_lastNoiseTangent hd hT hρ (unitPoint_compact hT) (unitPoint_near hT hρ0) B
  have hpm : linearTransport (e vh).1 (m + 1) = (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) := by
    have hm1 := linearTransport_mem hT (e vh).1 (m + 1) le_rfl
    have h0 : linearTransport (e vh).1 (m + 1) -
        (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) = 0 := by
      refine edgeForm_eq_zero ((edgeFormSpace L n (m + 1) (m + 1)).sub_mem hm1 B.2) ?_
      funext c
      have h2 : A c vh - A c v₀ = 0 := eq_zero_of_entryParts fun q => by
        rw [map_sub]
        have h3 := hvals (Sum.inl (c, q))
        simp only [ψ, Sum.elim_inl, ContinuousLinearMap.comp_apply] at h3
        rw [h3, sub_self]
      rw [hA, hA, hv₀, ← smul_sub] at h2
      have h3 := (smul_eq_zero.mp h2).resolve_left Complex.I_ne_zero
      show linearTransport (e vh).1 (m + 1) c.1 -
        (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1 = 0
      simp only at h3
      rw [hinj] at h3
      exact h3
    exact sub_eq_zero.mp h0
  have hDz : ∀ j, D j vh = 0 := by
    intro j
    have h3 := hvals (Sum.inr (Sum.inl j))
    simp only [ψ, Sum.elim_inr, Sum.elim_inl] at h3
    rw [h3, hD, hv₀]
    have e0 : ((lastNoiseTangent B).1 : Edge L n (m + 1) 0 → ComplexMatrix2) = 0 := rfl
    simp only
    rw [e0, edgePairing_comm, edgePairing_zero_right]
    rfl
  refine ⟨vh, hz2, hpm, hDz, fun ε hε => ?_⟩
  obtain ⟨δ₀, hδ₀, hc⟩ := hcore ε hε
  set K : ℝ := 1 + ∑ q : Fin 2 × Fin 2 × Bool, ‖entryPartL q‖ with hK'
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ∑ q : Fin 2 × Fin 2 × Bool, ‖entryPartL q‖ :=
      Finset.sum_nonneg fun q _ => norm_nonneg _
    simp only [hK']
    linarith
  have hK0' : 0 < K := by linarith
  refine ⟨δ₀ / K, by positivity, fun v s h1 h2 h3 h4 => ?_⟩
  have hle : δ₀ / K ≤ δ₀ := div_le_self hδ₀.le hK1
  have hS0 : 0 ≤ ‖v‖ + |s| := by positivity
  have hS1 : 0 ≤ ‖v‖ ^ 2 + s ^ 2 := by positivity
  refine hc v s (fun i => ?_) ?_
  · rcases i with ⟨c, q⟩ | j | i
    · show |entryPartL q (A c (v - s • vh))| ≤ _
      have h5 := (entryPartL q).le_opNorm (A c (v - s • vh))
      have h6 : ‖entryPartL q‖ ≤ K := by
        have := Finset.single_le_sum (f := fun q : Fin 2 × Fin 2 × Bool => ‖entryPartL q‖)
          (fun q _ => norm_nonneg _) (Finset.mem_univ q)
        simp only [hK']
        linarith
      have h7 := h1 c
      simp only [Real.norm_eq_abs] at h5
      calc |entryPartL q (A c (v - s • vh))| ≤ ‖entryPartL q‖ * ‖A c (v - s • vh)‖ := h5
        _ ≤ K * (δ₀ / K * (‖v‖ + |s|)) := by
            gcongr
        _ = δ₀ * (‖v‖ + |s|) := by field_simp
    · exact (h2 j).trans (mul_le_mul_of_nonneg_right hle hS0)
    · show |(P3 (v - s • vh)) i| ≤ _
      have e1 : P3 (v - s • vh) = 0 := by
        rw [map_sub, map_smul, hP3 v, hP3 vh, h3, hz2]
        have : e.symm ((0 : LevelForms L n (m + 1)), ((0 : LevelForms L n (m + 1) ×
          edgeFormSpace L n (m + 1) (m + 1)))) = 0 := e.symm.map_zero
        simp only [this]
        simp
      rw [e1]
      simp only [Pi.zero_apply, abs_zero]
      positivity
  · exact h4.trans (by gcongr)
end Minimiser
section Selected
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
private theorem eventually_quadratic_near (Hs : V →L[ℝ] V →L[ℝ] ℝ)
    (hsym : ∀ u v, Hs u v = Hs v u) {vh : V}
    {wc : ℝ → V} (h0 : wc 0 = 0) (hd : HasDerivAt wc vh 0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ s in 𝓝 (0 : ℝ), Hs (wc s) (wc s) ≤ s ^ 2 * Hs vh vh + δ * s ^ 2 ∧
      ‖wc s‖ ≤ (‖vh‖ + 1) * |s| := by
  set C : ℝ := ‖Hs‖ + 1 with hC
  have hb : ∀ u v : V, |Hs u v| ≤ C * ‖u‖ * ‖v‖ := by
    intro u v
    have h1 := (Hs u).le_opNorm v
    have h2 := Hs.le_opNorm u
    have h3 : ‖Hs u‖ ≤ C * ‖u‖ := h2.trans (by
      simp only [hC]
      nlinarith [norm_nonneg u])
    calc |Hs u v| = ‖Hs u v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖Hs u‖ * ‖v‖ := h1
      _ ≤ (C * ‖u‖) * ‖v‖ := by gcongr
  set η : ℝ := min 1 (δ / (C * (2 * ‖vh‖ + 1))) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η * (C * (2 * ‖vh‖ + 1)) ≤ δ := by
    have h1 : η ≤ δ / (C * (2 * ‖vh‖ + 1)) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at h1
  have hlo := (hasDerivAt_iff_isLittleO_nhds_zero.mp hd).def hη0
  filter_upwards [hlo] with s hs
  simp only [zero_add, h0, sub_zero, Real.norm_eq_abs] at hs
  set r := wc s - s • vh with hr
  have hw : wc s = s • vh + r := by simp [hr]
  have hsv : ‖s • vh‖ = |s| * ‖vh‖ := by rw [norm_smul, Real.norm_eq_abs]
  constructor
  · rw [hw]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hsym r vh]
    have h1 : |Hs vh r| ≤ C * ‖vh‖ * (η * |s|) := by
      refine (hb vh r).trans ?_
      gcongr
    have h2 : |Hs r r| ≤ C * (η * |s|) * (η * |s|) := by
      refine (hb r r).trans ?_
      gcongr
    have h3 : s * Hs vh r ≤ |s| * (C * ‖vh‖ * (η * |s|)) := by
      calc s * Hs vh r ≤ |s * Hs vh r| := le_abs_self _
        _ = |s| * |Hs vh r| := abs_mul _ _
        _ ≤ _ := by gcongr
    have e1 : |s| ^ 2 = s ^ 2 := sq_abs s
    have h4 : C * (η * |s|) * (η * |s|) ≤ C * η * s ^ 2 := by
      have h5 : η * η ≤ η * 1 := by gcongr
      calc C * (η * |s|) * (η * |s|) = C * (η * η) * |s| ^ 2 := by ring
        _ ≤ C * (η * 1) * |s| ^ 2 := by gcongr
        _ = C * η * s ^ 2 := by rw [e1]; ring
    have h6 := le_abs_self (Hs r r)
    have h7 : |s| * (C * ‖vh‖ * (η * |s|)) = C * ‖vh‖ * η * s ^ 2 := by
      rw [← e1]
      ring
    have h8 : (η * (C * (2 * ‖vh‖ + 1))) * s ^ 2 ≤ δ * s ^ 2 :=
      mul_le_mul_of_nonneg_right hη2 (sq_nonneg s)
    nlinarith
  · calc ‖wc s‖ ≤ ‖s • vh‖ + ‖r‖ := by rw [hw]; exact norm_add_le _ _
      _ ≤ |s| * ‖vh‖ + η * |s| := by rw [hsv]; gcongr
      _ ≤ |s| * ‖vh‖ + 1 * |s| := by gcongr
      _ = (‖vh‖ + 1) * |s| := by ring
private theorem exists_near_selection {E : Type*} (Pp : ℝ → E → Prop) (ν : E → ℝ)
    (hν : ∀ ξ, 0 ≤ ν ξ)
    (ξ0 : E) (hν0 : ν ξ0 = 0) (hP0 : Pp 0 ξ0)
    (H : ∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝 (0 : ℝ), ∃ ξ, Pp s ξ ∧ ν ξ < ε) :
    ∃ ξs : ℝ → E, ξs 0 = ξ0 ∧ (∀ᶠ s in 𝓝 (0 : ℝ), Pp s (ξs s)) ∧
      Tendsto (fun s => ν (ξs s)) (𝓝 0) (𝓝 0) := by
  classical
  let A : ℝ → Set ℝ := fun s => {x | ∃ ξ, Pp s ξ ∧ x = ν ξ}
  have hAb : ∀ s, BddBelow (A s) := fun s => ⟨0, by
    rintro x ⟨ξ, -, rfl⟩
    exact hν ξ⟩
  let ξs : ℝ → E := fun s => if s = 0 then ξ0 else
    if h : ∃ ξ, Pp s ξ ∧ ν ξ < sInf (A s) + |s| then h.choose else ξ0
  have hex : ∀ s, s ≠ 0 → (∃ ξ, Pp s ξ) → ∃ ξ, Pp s ξ ∧ ν ξ < sInf (A s) + |s| := by
    intro s hs ⟨ξ, hξ⟩
    have hlt : sInf (A s) < sInf (A s) + |s| := by
      have : 0 < |s| := abs_pos.mpr hs
      linarith
    have hne : (A s).Nonempty := ⟨ν ξ, ξ, hξ, rfl⟩
    obtain ⟨x, ⟨ξ', h1, rfl⟩, h2⟩ := exists_lt_of_csInf_lt hne hlt
    exact ⟨ξ', h1, h2⟩
  refine ⟨ξs, by simp [ξs], ?_, ?_⟩
  · filter_upwards [H 1 one_pos] with s hs
    by_cases h0 : s = 0
    · subst h0
      simpa [ξs] using hP0
    · obtain ⟨ξ, hξ, -⟩ := hs
      have h := hex s h0 ⟨ξ, hξ⟩
      simp only [ξs, if_neg h0, dif_pos h]
      exact h.choose_spec.1
  · rw [Metric.tendsto_nhds]
    intro ε hε
    have hs1 : ∀ᶠ s in 𝓝 (0 : ℝ), |s| < ε / 2 := by
      have := Metric.ball_mem_nhds (0 : ℝ) (half_pos hε)
      filter_upwards [this] with s hs
      simpa [Real.dist_eq] using hs
    filter_upwards [H (ε / 2) (half_pos hε), hs1] with s hs h2
    rw [Real.dist_eq, sub_zero]
    by_cases h0 : s = 0
    · subst h0
      simp only [ξs, if_true, hν0, abs_zero]
      exact hε
    · obtain ⟨ξ, hξ, hlt⟩ := hs
      have h := hex s h0 ⟨ξ, hξ⟩
      simp only [ξs, if_neg h0, dif_pos h]
      have h3 := h.choose_spec.2
      have h4 : sInf (A s) ≤ ν ξ := csInf_le (hAb s) ⟨ξ, hξ, rfl⟩
      rw [abs_of_nonneg (hν _)]
      linarith
end Selected
section SelectedBranch
variable {L n m N : ℕ}
private def chartIncl (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n (m + 1)) :
    LevelForms L n (m + 1) →ₗ[ℝ] (Fin N → ℝ) :=
  e.symm.toLinearMap ∘ₗ LinearMap.inl ℝ _ _
private theorem equiv_chartIncl (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n (m + 1))
    (ξ : LevelForms L n (m + 1)) : e (chartIncl e ξ) = (ξ, 0) := by
  simp [chartIncl]
private theorem chartPoint_chartIncl (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n (m + 1))
    (ξ : LevelForms L n (m + 1)) :
    chartPoint e (chartIncl e ξ) = expMove ξ (unitPoint L n (m + 1)) := by
  simp only [chartPoint, equiv_chartIncl]
private theorem chartIncl_small (hT : TowerFacts L n (m + 1))
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n (m + 1)) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ : LevelForms L n (m + 1),
      (∀ b, ComplexMatrix2.operatorNorm ((ξ.1 : Edge L n (m + 1) 0 → ComplexMatrix2) b) < ε) →
      (∀ (i : Fin (m + 1)) (b : Edge L n (m + 1) ((i : ℕ) + 1)),
        ComplexMatrix2.operatorNorm
          ((ξ.2 i : Edge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2) b) < ε) →
      ‖chartIncl e ξ‖ < ε' := by
  letI hF0 : Fintype (PositiveEdge L n (m + 1) 0) :=
    @Fintype.ofFinite _ (hT.posEdges_finite 0 (Nat.zero_le _))
  letI hFq : ∀ i : Fin (m + 1), Fintype (PositiveEdge L n (m + 1) ((i : ℕ) + 1)) := fun i =>
    @Fintype.ofFinite _ (hT.posEdges_finite _ i.2)
  let PP := (PositiveEdge L n (m + 1) 0 → ComplexMatrix2) ×
    ((i : Fin (m + 1)) → PositiveEdge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2)
  let ρE : LevelForms L n (m + 1) →ₗ[ℝ] PP :=
    { toFun := fun ξ => (fun b => (ξ.1 : Edge L n (m + 1) 0 → ComplexMatrix2) b.1,
        fun i b => (ξ.2 i : Edge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2) b.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker ρE = ⊥ := by
    rw [LinearMap.ker_eq_bot, injective_iff_map_eq_zero]
    intro ξ h
    have h1 : (ξ.1 : Edge L n (m + 1) 0 → ComplexMatrix2) = 0 :=
      edgeForm_eq_zero ξ.1.2 (congrArg Prod.fst h)
    have h2 : ∀ i : Fin (m + 1),
        (ξ.2 i : Edge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2) = 0 := fun i =>
      edgeForm_eq_zero (ξ.2 i).2 (congrFun (congrArg Prod.snd h) i)
    exact Prod.ext (Subtype.ext h1) (funext fun i => Subtype.ext (h2 i))
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ρE hker
  let C : PP →L[ℝ] (Fin N → ℝ) := LinearMap.toContinuousLinearMap (chartIncl e ∘ₗ g)
  have hC : ∀ ξ, C (ρE ξ) = chartIncl e ξ := by
    intro ξ
    have := LinearMap.congr_fun hg ξ
    simp only [C, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply]
    exact congrArg _ this
  refine ⟨ε' / (‖C‖ + 1), by positivity, fun ξ h1 h2 => ?_⟩
  set ε := ε' / (‖C‖ + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hn : ‖ρE ξ‖ ≤ ε := by
    rw [Prod.norm_def, max_le_iff]
    refine ⟨(pi_norm_le_iff_of_nonneg hε0.le).mpr fun b => (h1 b.1).le,
      (pi_norm_le_iff_of_nonneg hε0.le).mpr fun i =>
        (pi_norm_le_iff_of_nonneg hε0.le).mpr fun b => (h2 i b.1).le⟩
  rw [← hC]
  calc ‖C (ρE ξ)‖ ≤ ‖C‖ * ‖ρE ξ‖ := C.le_opNorm _
    _ ≤ ‖C‖ * ε := by gcongr
    _ < (‖C‖ + 1) * ε := by nlinarith [norm_nonneg C]
    _ = ε' := by
      have hne : ‖C‖ + 1 ≠ 0 := by positivity
      simp only [hε]
      field_simp
set_option maxHeartbeats 1000000 in
private theorem exists_selected_branch
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n (m + 1)) (hEL : ComplexMatrix2.ExpLogEstimates)
    (hSG : PeriodicLattice.ActionNonnegAndGaugeInvariant)
    (hK : Tower.ClosedInSmoothingKernelIsExact)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : NearOneBounds L n (m + 1) ρ) {a : ℝ} (ha : 0 < a)
    [Finite (PositiveEdge L n (m + 1) 0)] [Finite (Face L n (m + 1) 0)]
    [∀ i : Fin (m + 1), Finite (PositiveEdge L n (m + 1) ((i : ℕ) + 1))]
    [Finite (PositiveEdge L n (m + 1) (m + 1))]
    [FiniteDimensional ℝ (edgeFormSpace L n (m + 1) (m + 1))]
    (innP : FaceSums.PairingIsInner ↥(univ : Set (Face L n (m + 1) 0)))
    (inn0 : FaceSums.PairingIsInner ↥(univ : Set (PositiveEdge L n (m + 1) 0)))
    (innI : ∀ i : Fin (m + 1), FaceSums.PairingIsInner
      ↥(univ : Set (PositiveEdge L n (m + 1) ((i : ℕ) + 1))))
    (hstep : ∀ j, j < m + 1 → TrivialLinearization.OneStepIdentities L n (m + 1) j)
    (lc : PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth (m + 1) (m + 1)))
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n (m + 1))
    {r : ℕ} (κb : Module.Basis (Fin r) ℝ (topVanishingGauges L n (m + 1)))
    (B : edgeFormSpace L n (m + 1) (m + 1))
    (hP : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      ∃ ξ : LevelForms L n (m + 1),
        (∀ b, ComplexMatrix2.operatorNorm ((ξ.1 : Edge L n (m + 1) 0 → ComplexMatrix2) b) < ε) ∧
        (∀ (i : Fin (m + 1)) (b : Edge L n (m + 1) ((i : ℕ) + 1)),
          ComplexMatrix2.operatorNorm
            ((ξ.2 i : Edge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2) b) < ε) ∧
        IsMinimizerOver a
          (PeriodicLattice.expTwist (s • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2))
            fun _ => 1)
          (expMove ξ (unitPoint L n (m + 1))) ∧
        ∀ κ ∈ topVanishingGauges L n (m + 1),
          distanceGaugeVariation (expMove ξ (unitPoint L n (m + 1))).fine
            (κ : Vertex L n (m + 1) 0 → ComplexMatrix2) = 0) :
    ∃ (w : ℝ → Fin N → ℝ) (vh : Fin N → ℝ), w 0 = 0 ∧ HasDerivAt w vh 0 ∧ (e vh).2 = 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℝ), (e (w s)).2 = 0 ∧
        IsMinimizerOver a
          (PeriodicLattice.expTwist (s • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2))
            fun _ => 1)
          (chartPoint e (w s)) := by
  obtain ⟨vh, hz2, hpm, hDz, hcore⟩ := exists_hessian_minimizer hd hT hEL hSG hK hL hn hρ0 hρ ha
    innP inn0 innI hstep lc e κb B
  have hk1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  obtain ⟨hf2, hf0, hf1, hHd⟩ := chainAction_second_order hd hT hEL hSG hk1 hL hn hρ0 hρ ha e
  set f : (Fin N → ℝ) → ℝ := fun w => chainAction a (chartPoint e w) with hf
  set Hs := fderiv ℝ (fderiv ℝ f) 0 with hHs
  have hsym : ∀ u v, Hs u v = Hs v u := fun u v => (hf2.isSymmSndFDerivAt (by simp)).eq u v
  have hvh : chartIncl e (e vh).1 = vh := by
    apply e.injective
    rw [equiv_chartIncl]
    exact Prod.ext rfl hz2.symm
  let W : ℝ → Edge L n (m + 1) (m + 1) → ComplexMatrix2 := fun s =>
    PeriodicLattice.expTwist (s • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2)) fun _ => 1
  let Pp : ℝ → LevelForms L n (m + 1) → Prop := fun s ξ =>
    IsMinimizerOver a (W s) (expMove ξ (unitPoint L n (m + 1))) ∧
      ∀ κ ∈ topVanishingGauges L n (m + 1),
        distanceGaugeVariation (expMove ξ (unitPoint L n (m + 1))).fine
          (κ : Vertex L n (m + 1) 0 → ComplexMatrix2) = 0
  have h1c := const_one_mem (L := L) (n := n) (k := m + 1) (j := m + 1)
  have hm0 : expMove (0 : LevelForms L n (m + 1)) (unitPoint L n (m + 1)) =
      unitPoint L n (m + 1) := by
    have h := expMove_zero (X := unitPoint L n (m + 1))
      (mem_fieldsIn_of_mem (const_one_mem (L := L) (n := n) (k := m + 1) (j := 0)))
      (0 : LevelForms L n (m + 1))
    simpa only [smul_zero] using h
  have hP0 : Pp 0 0 := by
    refine ⟨?_, fun κ hκ => ?_⟩
    · rw [hm0]
      have hW0 : W 0 = fun _ => 1 := by
        simp only [W, zero_smul]
        exact expTwist_zero (mem_fieldsIn_of_mem h1c)
      refine ⟨unitPoint_compact hT, ?_, fun X' h1 _ => ?_⟩
      · rw [hW0]
        exact levelField_unitPoint hT _ le_rfl
      · rw [chainAction_unitPoint a]
        exact chainAction_nonneg hSG hT hk1 hL hn ha h1
    · rw [hm0]
      have h := (gaugeVariation_chart_facts hd hT hρ0 hρ e
        (κ := (κ : Vertex L n (m + 1) 0 → ComplexMatrix2))
        (fun x => κ.2 x trivial)).2.1
      rwa [chartPoint_zero hT e] at h
  have hH : ∀ ε : ℝ, 0 < ε → ∀ᶠ s in 𝓝 (0 : ℝ), ∃ ξ, Pp s ξ ∧ ‖chartIncl e ξ‖ < ε := by
    intro ε hε
    obtain ⟨ε₂, hε₂, hin⟩ := chartIncl_small hT e hε
    obtain ⟨δ, hδ, hs⟩ := hP ε₂ hε₂
    have hb := Metric.ball_mem_nhds (0 : ℝ) hδ
    filter_upwards [hb] with s hs'
    have hs2 : |s| < δ := by simpa [Real.dist_eq] using hs'
    obtain ⟨ξ, h1, h2, h3, h4⟩ := hs s hs2
    exact ⟨ξ, ⟨h3, h4⟩, hin ξ h1 h2⟩
  obtain ⟨ξs, hξ0, hsel, htend⟩ := exists_near_selection Pp (fun ξ => ‖chartIncl e ξ‖)
    (fun ξ => norm_nonneg _) 0 (by simp) hP0 hH
  set w : ℝ → Fin N → ℝ := fun s => chartIncl e (ξs s) with hw
  have hw0 : w 0 = 0 := by simp [hw, hξ0]
  have hwt : Tendsto w (𝓝 0) (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr htend
  obtain ⟨wc, hwc0, hwcd, hwcev⟩ := exists_candidate_curve hd hT hEL hρ0 hρ e B hpm
  have hwcd' : HasDerivAt wc vh 0 := by
    have e1 : e.symm ((e vh).1, 0, 0) = vh := hvh
    rwa [e1] at hwcd
  have hpw : ∀ s, chartPoint e (w s) = expMove (ξs s) (unitPoint L n (m + 1)) :=
    fun s => chartPoint_chartIncl e (ξs s)
  have hsel' : ∀ᶠ s in 𝓝 (0 : ℝ), IsMinimizerOver a (W s) (chartPoint e (w s)) ∧
      ∀ κ ∈ topVanishingGauges L n (m + 1),
        distanceGaugeVariation (chartPoint e (w s)).fine
          (κ : Vertex L n (m + 1) 0 → ComplexMatrix2) = 0 := by
    filter_upwards [hsel] with s hs
    rw [hpw]
    exact hs
  refine ⟨w, vh, hw0, ?_, hz2, ?_⟩
  · rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    obtain ⟨δ, hδ, hc⟩ := hcore ε hε
    have hδ2 : 0 < δ / 2 := half_pos hδ
    have E1 : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ c : PositiveEdge L n (m + 1) (m + 1),
        ComplexMatrix2.operatorNorm
          (fderiv ℝ (fun x => levelField (chartPoint e x) (m + 1) c.1) 0 (w s - s • vh)) ≤
          δ * (‖w s‖ + |s|) := by
      refine Filter.eventually_all.mpr fun c => ?_
      obtain ⟨td, t1, t2⟩ := levelField_chart_facts hd hT hρ0 hρ e le_rfl c.1
      have lo1 := td.hasFDerivAt.isLittleO.def hδ2
      have hWd : HasDerivAt (fun s => W s c.1)
          (Complex.I • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1) 0 := by
        have h := hasDerivAt_expTwist_line (mem_fieldsIn_of_mem h1c) B.2.2 c.1
        rwa [velocity_one] at h
      have lo2 := (hasDerivAt_iff_isLittleO_nhds_zero.mp hWd).def hδ2
      have hW0 : W 0 c.1 = 1 := by
        have : W 0 = fun _ => 1 := by
          simp only [W, zero_smul]
          exact expTwist_zero (mem_fieldsIn_of_mem h1c)
        rw [this]
      filter_upwards [hwt.eventually lo1, lo2, hsel'] with s g1 g2 g3
      have etop : levelField (chartPoint e (w s)) (m + 1) c.1 = W s c.1 :=
        congrFun g3.1.top_eq c.1
      have eA : fderiv ℝ (fun x => levelField (chartPoint e x) (m + 1) c.1) 0 vh =
          Complex.I • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1 := by
        rw [t2, hpm]
      simp only [zero_add, sub_zero, Real.norm_eq_abs] at g1 g2
      rw [t1, etop] at g1
      rw [hW0] at g2
      rw [map_sub, map_smul, eA]
      set Aw := fderiv ℝ (fun x => levelField (chartPoint e x) (m + 1) c.1) 0 (w s)
      set Bc := Complex.I • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1
      have e3 : Aw - s • Bc = (W s c.1 - 1 - s • Bc) - (W s c.1 - 1 - Aw) := by abel
      calc ComplexMatrix2.operatorNorm (Aw - s • Bc) ≤
            ‖W s c.1 - 1 - s • Bc‖ + ‖W s c.1 - 1 - Aw‖ := by
            rw [e3]
            exact norm_sub_le _ _
        _ ≤ δ / 2 * |s| + δ / 2 * ‖w s‖ := add_le_add g2 g1
        _ ≤ δ * (‖w s‖ + |s|) := by nlinarith [norm_nonneg (w s), abs_nonneg s]
    have E2 : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ j, |fderiv ℝ (fun x => distanceGaugeVariation (chartPoint e x).fine
        (((κb j : vertexFunctionSpace L n (m + 1) 0) : Vertex L n (m + 1) 0 → ComplexMatrix2)))
          0 (w s - s • vh)| ≤ δ * (‖w s‖ + |s|) := by
      refine Filter.eventually_all.mpr fun j => ?_
      obtain ⟨gd, g0, -⟩ := gaugeVariation_chart_facts hd hT hρ0 hρ e
        (κ := ((κb j : vertexFunctionSpace L n (m + 1) 0) : Vertex L n (m + 1) 0 → ComplexMatrix2))
        (fun x => (κb j : vertexFunctionSpace L n (m + 1) 0).2 x trivial)
      have lo := gd.hasFDerivAt.isLittleO.def hδ
      filter_upwards [hwt.eventually lo, hsel'] with s g1 g3
      have ez := g3.2 _ (κb j).2
      simp only [sub_zero, Real.norm_eq_abs] at g1
      rw [ez, g0, sub_zero, zero_sub, abs_neg] at g1
      rw [map_sub, map_smul, hDz j, smul_zero, sub_zero]
      calc _ ≤ δ * ‖w s‖ := g1
        _ ≤ δ * (‖w s‖ + |s|) := by nlinarith [abs_nonneg s]
    have E3 : ∀ᶠ s in 𝓝 (0 : ℝ),
        Hs (w s) (w s) ≤ s ^ 2 * Hs vh vh + δ * (‖w s‖ ^ 2 + s ^ 2) := by
      set R : ℝ := ‖vh‖ + 1 with hR
      have hR1 : 1 ≤ R := by have := norm_nonneg vh; simp only [hR]; linarith
      set ε₁ : ℝ := min (δ / 2) (δ / (4 * R ^ 2)) with hε₁
      have hε₁0 : 0 < ε₁ := lt_min hδ2 (by positivity)
      have hε₁a : 2 * ε₁ ≤ δ := by
        have := min_le_left (δ / 2) (δ / (4 * R ^ 2))
        linarith
      have hε₁b : 2 * ε₁ * R ^ 2 ≤ δ / 2 := by
        have h := min_le_right (δ / 2) (δ / (4 * R ^ 2))
        have h2 : ε₁ * (4 * R ^ 2) ≤ δ := by
          rwa [le_div_iff₀ (by positivity)] at h
        linarith
      obtain ⟨t, ht, htay⟩ := second_order_taylor hf2 hf0 hf1 hε₁0
      have hq := eventually_quadratic_near Hs hsym hwc0 hwcd' hδ2
      have hcw : Tendsto wc (𝓝 0) (𝓝 0) := by
        have := hwcd'.continuousAt.tendsto
        rwa [hwc0] at this
      have hball := Metric.ball_mem_nhds (0 : Fin N → ℝ) ht
      filter_upwards [hwt.eventually hball, hcw.eventually hball, hq, hsel', hwcev] with
        s g1 g2 g3 g4 g5
      have n1 : ‖w s‖ < t := by simpa using g1
      have n2 : ‖wc s‖ < t := by simpa using g2
      have a1 := abs_le.mp (htay (w s) n1)
      have a2 := abs_le.mp (htay (wc s) n2)
      have hle : f (w s) ≤ f (wc s) := g4.1.le _ g5.1 g5.2
      have hb2 : ‖wc s‖ ^ 2 ≤ R ^ 2 * s ^ 2 := by
        have h := pow_le_pow_left₀ (norm_nonneg _) g3.2 2
        rwa [mul_pow, sq_abs] at h
      have h1 : 2 * ε₁ * ‖wc s‖ ^ 2 ≤ δ / 2 * s ^ 2 := by
        have h2 : 2 * ε₁ * ‖wc s‖ ^ 2 ≤ 2 * ε₁ * (R ^ 2 * s ^ 2) := by gcongr
        have h3 : 2 * ε₁ * R ^ 2 * s ^ 2 ≤ δ / 2 * s ^ 2 :=
          mul_le_mul_of_nonneg_right hε₁b (sq_nonneg s)
        nlinarith
      have h2 : 2 * ε₁ * ‖w s‖ ^ 2 ≤ δ * ‖w s‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hε₁a (by positivity)
      have h3 := g3.1
      nlinarith [a1.1, a1.2, a2.1, a2.2]
    filter_upwards [E1, E2, E3, hsel'] with s h1 h2 h3 h4
    have he : (e (w s)).2 = 0 := by simp [hw, equiv_chartIncl]
    have hfin := hc (w s) s h1 h2 he h3
    simp only [zero_add, hw0, sub_zero, Real.norm_eq_abs]
    exact hfin
  · filter_upwards [hsel'] with s hs
    exact ⟨by simp [hw, equiv_chartIncl], hs.1⟩
end SelectedBranch
section Final
variable {L n m N : ℕ}
private theorem exists_levelGradient (hT : TowerFacts L n (m + 1))
    [Finite (PositiveEdge L n (m + 1) 0)]
    [∀ i : Fin (m + 1), Finite (PositiveEdge L n (m + 1) ((i : ℕ) + 1))]
    [FiniteDimensional ℝ (LevelForms L n (m + 1))]
    (hdefE : ∀ ξ : LevelForms L n (m + 1), levelForm ξ ξ = 0 → ξ = 0)
    {a : ℝ} {X : ChainPoint L n (m + 1)}
    (hXc : X.fine ∈ fieldsIn L n (m + 1) 0 PeriodicLattice.complexGaugeGroup)
    {Lf : PointCoords L n (m + 1) → ℝ}
    (hLf : ∀ (Y : ℝ → ChainPoint L n (m + 1)) (v : PointCoords L n (m + 1)), Y 0 = X →
      (∀ b, HasDerivAt (fun t => (Y t).fine b) (v.1 b) 0) →
      (∀ i c, HasDerivAt (fun t => (Y t).noise i c) (v.2 i c) 0) →
      HasDerivAt (fun t => chainAction a (Y t)) (Lf v) 0)
    (hadd : ∀ v v', Lf (v + v') = Lf v + Lf v') (hsm : ∀ (r : ℝ) v, Lf (r • v) = r • Lf v) :
    ∃ J, IsLevelGradient (chainAction a) X J := by
  let vel : LevelForms L n (m + 1) → PointCoords L n (m + 1) := fun η =>
    (velocity X.fine η.1, fun i c =>
      Complex.I • (η.2 i : Edge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2) c.1 * X.noise i c)
  have hderiv : ∀ η, leftDeriv (chainAction a) X η = Lf (vel η) := by
    intro η
    have h := hLf (fun t => expMove (t • η) X) (vel η) (expMove_zero hXc η)
      (fun b => hasDerivAt_expTwist_line hXc η.1.2.2 b)
      (fun i c => (hasDerivAt_expLine _).mul_const _)
    exact h.deriv
  have hvadd : ∀ η η', vel (η + η') = vel η + vel η' := by
    intro η η'
    refine Prod.ext ?_ ?_
    · exact velocity_add _ _ _
    · funext i c
      simp only [vel, Prod.snd_add, Pi.add_apply, Submodule.coe_add, smul_add, add_mul]
  have hvsm : ∀ (r : ℝ) η, vel (r • η) = r • vel η := by
    intro r η
    refine Prod.ext ?_ ?_
    · exact velocity_smul _ _ _
    · funext i c
      simp only [vel, Prod.smul_snd, Pi.smul_apply, Submodule.coe_smul]
      rw [smul_comm, smul_mul_assoc]
  let ℓ : LevelForms L n (m + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun η => Lf (vel η)
      map_add' := fun η η' => by rw [hvadd, hadd]
      map_smul' := fun r η => by rw [hvsm, hsm]; rfl }
  obtain ⟨T, hT'⟩ := exists_riesz_rep levelForm hdefE (LinearMap.toSpanSingleton ℝ _ ℓ)
  refine ⟨T 1, fun ξ => ?_⟩
  have h := hT' 1 ξ
  rw [levelForm_apply] at h
  rw [h, hderiv]
  simp
  rfl
private theorem eventually_chartPoint_small (hT : TowerFacts L n (m + 1))
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n (m + 1)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 (0 : Fin N → ℝ),
      (∀ b, ComplexMatrix2.operatorNorm ((chartPoint e w).fine b - 1) < ε) ∧
      ∀ i c, ComplexMatrix2.operatorNorm ((chartPoint e w).noise i c - 1) < ε := by
  haveI := hT.edges_finite 0 (Nat.zero_le _)
  have h1 : ∀ᶠ w in 𝓝 (0 : Fin N → ℝ),
      ∀ b, ComplexMatrix2.operatorNorm ((chartPoint e w).fine b - 1) < ε := by
    refine Filter.eventually_all.mpr fun b => ?_
    obtain ⟨g1, g2⟩ := chartPoint_levelFields (m := 0) hT e 0 (Nat.zero_le _)
    have h3 : Tendsto (fun w => ‖levelField (chartPoint e w) 0 b - 1‖)
        (𝓝 (0 : Fin N → ℝ)) (𝓝 0) := by
      have h4 := (((g1 b).continuousAt).tendsto.sub_const (1 : ComplexMatrix2)).norm
      simpa [g2] using h4
    exact h3.eventually_lt_const hε
  have h2 : ∀ᶠ w in 𝓝 (0 : Fin N → ℝ),
      ∀ i c, ComplexMatrix2.operatorNorm ((chartPoint e w).noise i c - 1) < ε := by
    refine Filter.eventually_all.mpr fun i => ?_
    haveI := hT.posEdges_finite _ i.2
    refine Filter.eventually_all.mpr fun c => ?_
    have hc := contDiffAt_familyPoint_noise (m := 0)
      (0 : (Fin N → ℝ) →ₗ[ℝ] LevelForms L n (m + 1)) (chartSlot e) i c
    simp only [familyPoint_eq_chartPoint hT e] at hc
    have h3 : Tendsto (fun w => ‖(chartPoint e w).noise i c - 1‖) (𝓝 (0 : Fin N → ℝ)) (𝓝 0) := by
      have h4 := ((hc.continuousAt).tendsto.sub_const (1 : ComplexMatrix2)).norm
      have h5 : (chartPoint e 0).noise i c = 1 := by
        rw [chartPoint_zero hT e]
        rfl
      simpa [h5] using h4
    exact h3.eventually_lt_const hε
  exact h1.and h2
end Final
set_option maxHeartbeats 1000000 in
theorem firstVariation_exists (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hPA : NormalizedMeanNearOne) (hDer : NormalizedMeanAtOne)
    (hCfg : LeftChartFields.Claim) (hS : FaceSums.FacesAndPairings)
    (hV : LinearMapValues.Statement) (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hSG : PeriodicLattice.ActionNonnegAndGaugeInvariant)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    (hP : NearestGaugeMinimizerExists)
    (hK : Tower.ClosedInSmoothingKernelIsExact)
    (hR : TrivialLinearization.AllRelationsStatement)
    (hCo : PeriodicLattice.CoordinateDescription) :
    FirstVariationExists := by
  intro a ha L hL k n hk hn B
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hT : TowerFacts L n (m + 1) := towerFacts hDer hCfg hS hV hA hL hn
  obtain ⟨ρ, hρ0, hρ'⟩ := hPA L hL
  have hρ : NearOneBounds L n (m + 1) ρ := fun j hj V hV hN c hc =>
    hρ' n (m + 1) j hn hj V hV hN c hc
  have hPS := fun (j : ℕ) (hj : j ≤ m + 1) => (hS L hL (m + 1) j hj).1 n hn
  have innB := fun (j : ℕ) (hj : j ≤ m + 1) => ((hPS j hj).2.2.1 univ).1
  have innP := ((hPS 0 (Nat.zero_le _)).2.2.2 univ).1
  haveI finP : Finite (Face L n (m + 1) 0) := hT.faces_finite
  haveI hF0 : Finite (PositiveEdge L n (m + 1) 0) := hT.posEdges_finite 0 (Nat.zero_le _)
  haveI hFk : Finite (PositiveEdge L n (m + 1) (m + 1)) := hT.posEdges_finite _ le_rfl
  haveI hF : ∀ i : Fin (m + 1), Finite (PositiveEdge L n (m + 1) ((i : ℕ) + 1)) :=
    fun i => hT.posEdges_finite _ i.2
  haveI hS0 : Finite (Vertex L n (m + 1) 0) := hT.sites_finite 0 (Nat.zero_le _)
  have hstep : ∀ j, j < m + 1 → TrivialLinearization.OneStepIdentities L n (m + 1) j :=
    fun j hj => ((hR L hL).1 n (m + 1) j j hn hj hj.le).1
  have lc : PeriodicLattice.SublatticeCoordinates L n
      (PeriodicLattice.levelDepth (m + 1) (m + 1)) :=
    (hCo L n hL.1 hL.2 hn).1 _ (by simp only [PeriodicLattice.levelDepth]; omega)
  have fdim : ∀ j, j ≤ m + 1 → FiniteDimensional ℝ (edgeFormSpace L n (m + 1) j) := by
    intro j hj
    haveI := hT.posEdges_finite j hj
    let f : edgeFormSpace L n (m + 1) j →ₗ[ℝ] (PositiveEdge L n (m + 1) j → ComplexMatrix2) :=
      { toFun := fun B => restrictToPositiveEdges (B : Edge L n (m + 1) j → ComplexMatrix2)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine FiniteDimensional.of_injective f ?_
    rw [injective_iff_map_eq_zero]
    intro B hB
    exact Subtype.ext (edgeForm_eq_zero B.2 hB)
  haveI hfd0 := fdim 0 (Nat.zero_le _)
  haveI hfdk := fdim (m + 1) le_rfl
  haveI hfdi : ∀ i : Fin (m + 1), FiniteDimensional ℝ (edgeFormSpace L n (m + 1) ((i : ℕ) + 1)) :=
    fun i => fdim _ i.2
  have hdefE : ∀ ξ : LevelForms L n (m + 1), levelForm ξ ξ = 0 → ξ = 0 :=
    levelForm_definite (innB 0 (Nat.zero_le _)) fun i => innB _ i.2
  haveI hfrT : Module.Free ℝ (LevelTriple L n (m + 1)) := Module.Free.of_divisionRing _ _
  haveI hfrE : Module.Free ℝ (LevelForms L n (m + 1)) := Module.Free.of_divisionRing _ _
  haveI hfrG : Module.Free ℝ (topVanishingGauges L n (m + 1)) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace ℝ (topVanishingGauges L n (m + 1)))
  let e : (Fin (Module.finrank ℝ (LevelTriple L n (m + 1))) → ℝ) ≃ₗ[ℝ] LevelTriple L n (m + 1) :=
    (Module.finBasis ℝ (LevelTriple L n (m + 1))).equivFun.symm
  haveI hfdS : FiniteDimensional ℝ (vertexFunctionSpace L n (m + 1) 0) := inferInstance
  let κb := Module.finBasis ℝ (topVanishingGauges L n (m + 1))
  obtain ⟨w, vh, hw0, hwd, hz2, hev⟩ := exists_selected_branch hd hT hEL hSG hK hL hn hρ0 hρ ha
    innP (innB 0 (Nat.zero_le _)) (fun i => innB _ i.2) hstep lc e κb B
    (hP a ha L hL (m + 1) n (Nat.succ_le_succ (Nat.zero_le m)) hn B)
  have hwt : Tendsto w (𝓝 0) (𝓝 0) := by
    have := hwd.continuousAt.tendsto
    rwa [hw0] at this
  obtain ⟨ε₂, hε₂, hac⟩ := exists_chainAction_linear_deriv hT a
  have hsm := hwt.eventually (eventually_chartPoint_small hT e hε₂)
  have hnr := hwt.eventually (eventually_chartPoint_near hT e hρ0)
  have hG : ∀ᶠ s in 𝓝 (0 : ℝ), ∃ J, IsLevelGradient (chainAction a) (chartPoint e (w s)) J := by
    filter_upwards [hsm] with s hs
    obtain ⟨Lf, h1, h2, h3⟩ := hac _ hs.1 hs.2
    exact exists_levelGradient hT hdefE (chartPoint_fine_mem hT e (w s)) h1 h2 h3
  classical
  let Js : ℝ → LevelForms L n (m + 1) := fun s =>
    if h : ∃ J, IsLevelGradient (chainAction a) (chartPoint e (w s)) J then h.choose else 0
  have hJs : ∀ᶠ s in 𝓝 (0 : ℝ),
      IsLevelGradient (chainAction a) (chartPoint e (w s)) (Js s) := by
    filter_upwards [hG] with s hs
    simp only [Js, dif_pos hs]
    exact hs.choose_spec
  let bE := Module.finBasis ℝ (LevelForms L n (m + 1))
  have hdual : ∀ i, ∃ η, ∀ x, levelForm x η = bE.coord i x := by
    intro i
    obtain ⟨T, hT'⟩ := exists_riesz_rep levelForm hdefE
      (LinearMap.toSpanSingleton ℝ _ (bE.coord i))
    refine ⟨T 1, fun x => ?_⟩
    rw [levelForm_apply, levelPairing_comm, ← levelForm_apply, hT' 1 x]
    simp
  choose η hη using hdual
  let jv : ℝ → (Fin (Module.finrank ℝ (LevelForms L n (m + 1))) → ℝ) := fun s i =>
    bE.coord i (Js s)
  have hjd : ∀ i, HasDerivAt (fun s => jv s i) (hessianAtIdentity a (e vh).1 (η i)) 0 := by
    intro i
    have hc := hasDerivAt_leftDeriv_chart hd hT hρ0 hρ e hw0 (t := e vh) (by simpa using hwd) a
      (η i)
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [hJs] with s hs
    show bE.coord i (Js s) = _
    rw [← hη, levelForm_apply, hs (η i)]
  have hjv := hasDerivAt_pi.mpr hjd
  let Jof : (Fin (Module.finrank ℝ (LevelForms L n (m + 1))) → ℝ) →ₗ[ℝ]
      LevelForms L n (m + 1) := bE.equivFun.symm.toLinearMap
  have hJof : ∀ s, Jof (jv s) = Js s := by
    intro s
    have e1 : jv s = bE.equivFun (Js s) := by
      funext i
      simp [jv]
    simp only [Jof, e1]
    simp
  let Q : LevelForms L n (m + 1) →ₗ[ℝ] LevelTriple L n (m + 1) :=
    { toFun := fun x => (0, x, x.2 (Fin.last m))
      map_add' := fun x y => Prod.ext (by simp) (Prod.ext rfl rfl)
      map_smul' := fun r x => Prod.ext (by simp) (Prod.ext rfl rfl) }
  let C : (Fin (Module.finrank ℝ (LevelForms L n (m + 1))) → ℝ) →L[ℝ]
      (Fin (Module.finrank ℝ (LevelTriple L n (m + 1))) → ℝ) :=
    LinearMap.toContinuousLinearMap (e.symm.toLinearMap ∘ₗ Q ∘ₗ Jof)
  have hCv : ∀ x, e (C x) = Q (Jof x) := by
    intro x
    simp [C]
  set d : Fin (Module.finrank ℝ (LevelForms L n (m + 1))) → ℝ :=
    fun i => hessianAtIdentity a (e vh).1 (η i) with hdd
  have hcder : HasDerivAt (fun s => w s + C (jv s)) (vh + C d) 0 :=
    hwd.add (C.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hjv)
  obtain ⟨hf2, hf0, hf1, -⟩ := chainAction_second_order hd hT hEL hSG
    (Nat.succ_le_succ (Nat.zero_le m)) hL hn hρ0 hρ ha e
  have hJ0 : Js 0 = 0 := by
    have h0 : IsLevelGradient (chainAction a) (chartPoint e (w 0)) (Js 0) := hJs.self_of_nhds
    rw [hw0] at h0
    have hzero : leftDeriv (chainAction a) (chartPoint e 0) (Js 0) = 0 := by
      have hF : HasFDerivAt (fun x => chainAction a (chartPoint e x))
          (0 : (Fin (Module.finrank ℝ (LevelTriple L n (m + 1))) → ℝ) →L[ℝ] ℝ)
          ((0 : ℝ) • chartIncl e (Js 0)) := by
        rw [zero_smul, ← hf1]
        exact (hf2.differentiableAt (by norm_num)).hasFDerivAt
      have hl : HasDerivAt (fun t : ℝ => t • chartIncl e (Js 0)) (chartIncl e (Js 0)) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const (chartIncl e (Js 0))
      have hc := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hF hl
      have e2 : ((fun x => chainAction a (chartPoint e x)) ∘ fun t : ℝ => t • chartIncl e (Js 0)) =
          fun t : ℝ => chainAction a (expMove (t • Js 0) (chartPoint e 0)) := by
        funext t
        simp only [Function.comp]
        rw [← map_smul, chartPoint_chartIncl, chartPoint_zero hT e]
      rw [e2] at hc
      rw [leftDeriv, hc.deriv]
      rfl
    have h1 := h0 (Js 0)
    rw [hzero] at h1
    exact hdefE _ h1
  have hj0 : jv 0 = 0 := by
    funext i
    simp [jv, hJ0]
  refine ⟨e (vh + C d), Module.finrank ℝ (LevelTriple L n (m + 1)), e, fun s => w s + C (jv s),
    ?_, ?_, ?_⟩
  · simp only [hw0, hj0, map_zero, add_zero]
  · simpa using hcder
  · filter_upwards [hev, hJs, hsm, hnr] with s g1 g2 g3 g4
    have he : e (w s + C (jv s)) = ((e (w s)).1, Js s, (Js s).2 (Fin.last m)) := by
      rw [map_add, hCv, hJof]
      refine Prod.ext ?_ ?_
      · simp [Q]
      · have e1 := g1.1
        show (e (w s)).2 + (Q (Js s)).2 = _
        rw [e1, zero_add]
        rfl
    rw [he]
    obtain ⟨Lf, h1, -, -⟩ := hac _ g3.1 g3.2
    exact ⟨g1.2, g2, isTopMultiplier_of_minimizer hd hT hEL hρ g1.2.compact
      (fun X' h2 h3 => g1.2.le X' h2 (h3.trans g1.2.top_eq)) g4 h1 g2⟩
end YangMills.Construction.RunningCouplingSlope.FirstVariationProof
end
