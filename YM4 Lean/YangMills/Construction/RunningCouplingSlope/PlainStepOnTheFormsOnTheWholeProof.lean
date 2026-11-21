import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOneProof
import YangMills.Construction.RunningCouplingSlope.PlainMapsAtOneOnTheWholeProof
import YangMills.Construction.RunningCouplingSlope.PlainStepAtRealConfigurationsOnTheWholeProof
import YangMills.Construction.Towers.AveragedContourOfAPairDoesNotDependOnTheBondProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
open Matrices Tower Tower.FullSpace
namespace MeanStepOnForms
section Matrices
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem analyticAt_matrix_det {f : E → ComplexMatrix2} {x : E} (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun y => Matrix.det (f y)) x := by apply _root_.YangMills.SharedProofs.p3818 <;> assumption
private theorem inv_inv_of_mem_gaugeGroup {X : ComplexMatrix2}
    (h : X ∈ PeriodicLattice.complexGaugeGroup) : X⁻¹⁻¹ = X := by apply _root_.YangMills.SharedProofs.p6288 <;> assumption
private theorem inv_mem_gaugeGroup {X : ComplexMatrix2} (h : X ∈ PeriodicLattice.complexGaugeGroup) :
    X⁻¹ ∈ PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
end Matrices
section Bonds
variable {a : ℝ}
private theorem positive_or_opposite_positive (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
private theorem not_positive_opposite (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
private theorem extendOddly_of_positive (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) : extendOddly f b = f b := if_pos hb
end Bonds
section Average
variable {L k j : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem analyticAt_contourMean {W : E → FullSpace.Edge L k j → ComplexMatrix2} {q : E}
    (hW : ∀ b, AnalyticAt ℂ (fun x => W x b) q) (hdet : ∀ b, Matrix.det (W q b) = 1)
    (c : FullSpace.Edge L k (j + 1)) : AnalyticAt ℂ (fun x => contourMean (W x) c) q := by apply _root_.YangMills.SharedProofs.p59327 <;> assumption
private theorem analyticAt_meanRadius {W : E → FullSpace.Edge L k j → ComplexMatrix2} {q : E}
    (hW : ∀ b, AnalyticAt ℂ (fun x => W x b) q) (hdet : ∀ b, Matrix.det (W q b) = 1)
    {c : FullSpace.Edge L k (j + 1)} (hs : Matrix.det (contourMean (W q) c) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun x => meanRadius (W x) c) q :=
  (analyticAt_matrix_det (analyticAt_contourMean hW hdet c)).cpow analyticAt_const hs
private theorem analyticAt_normalizedMean {W : E → FullSpace.Edge L k j → ComplexMatrix2} {q : E}
    (hW : ∀ b, AnalyticAt ℂ (fun x => W x b) q) (hdet : ∀ b, Matrix.det (W q b) = 1)
    {c : FullSpace.Edge L k (j + 1)} (hs : Matrix.det (contourMean (W q) c) ∈ Complex.slitPlane)
    (hr : meanRadius (W q) c ≠ 0) : AnalyticAt ℂ (fun x => normalizedMean (W x) c) q :=
  ((analyticAt_meanRadius hW hdet hs).inv hr).fun_smul (analyticAt_contourMean hW hdet c)
private theorem normalizedMean_mem {V : FullSpace.Edge L k j → ComplexMatrix2}
    {c : FullSpace.Edge L k (j + 1)} (hr : meanRadius V c ≠ 0) :
    normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.SharedProofs.p29259 <;> assumption
private theorem eventually_normalizedMean_mem {W : E → FullSpace.Edge L k j → ComplexMatrix2}
    {q : E} (hW : ∀ b, AnalyticAt ℂ (fun x => W x b) q) (hdet : ∀ b, Matrix.det (W q b) = 1)
    {c : FullSpace.Edge L k (j + 1)} (hs : Matrix.det (contourMean (W q) c) ∈ Complex.slitPlane)
    (hr : meanRadius (W q) c ≠ 0) :
    ∀ᶠ x in 𝓝 q, normalizedMean (W x) c ∈ PeriodicLattice.complexGaugeGroup :=
  ((analyticAt_meanRadius hW hdet hs).continuousAt.eventually_ne hr).mono fun _ h =>
    normalizedMean_mem h
end Average
section Legs
private abbrev axesInOrder (π : Equiv.Perm (Fin 4)) : List (Fin 4) := (List.finRange 4).map π
private abbrev axesOfOrdering {S : Finset (Fin 4)} (σ : Fin S.card ≃ S) : List (Fin 4) :=
  (List.finRange S.card).map fun i => ((σ i : S) : Fin 4)
private theorem exists_ordering_eq_filter (S : Finset (Fin 4)) (π : Equiv.Perm (Fin 4)) :
    ∃ σ : Fin S.card ≃ S, axesOfOrdering σ = (axesInOrder π).filter (· ∈ S) := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.exists_enumList_eq_filter <;> assumption
private theorem stepsInOrder_filter {a' : ℝ} (d : Fin 4 → ℤ) (S : Finset (Fin 4))
    (hS : ∀ μ, μ ∉ S → d μ = 0) (x : InfiniteLattice.LatticePoint a') (l : List (Fin 4)) :
    stepsInOrder d x l = stepsInOrder d x (l.filter (· ∈ S)) := by apply _root_.YangMills.SharedProofs.p61879 <;> assumption
private theorem leg_eq_contour (L : ℕ) {a a' : ℝ} (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') (π : Equiv.Perm (Fin 4)) :
    ∃ σ : ContourOrder L y x, stepsInOrder (cubeOffset L y x) (toFiner a' y)
      ((List.finRange 4).map π) = contour L y x σ := by
  set S := offsetSupport L y x with hSdef
  have hS : ∀ μ, μ ∉ S → cubeOffset L y x μ = 0 := by
    intro μ hμ
    by_contra h
    exact hμ (by simp [hSdef, offsetSupport, h])
  obtain ⟨σ, hσ⟩ := exists_ordering_eq_filter S π
  refine ⟨σ, ?_⟩
  rw [stepsInOrder_filter _ S hS, ← hσ]
  rfl
variable {L k j : ℕ}
private theorem leg_endpoints_mem_cube (hZ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {y : FullSpace.Vertex L k (j + 1)}
    {x : FullSpace.Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y)
    (π : Equiv.Perm (Fin 4)) {b : FullSpace.Edge L k j} (hb : b ∈ contourLeg y x π) :
    (b.initial : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y ∧
      (b.terminal : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y := by
  have H := (hZ L hL k 1 (j + 1) (by omega) (by omega) (by omega)).2
  have Hb := H.1
  have Hc := H.2.2.2.2.2 (by omega)
  have hx' : (x : InfiniteLattice.AmbientSpace) ∈
      offsetPoint (meshAt L k j) (y : InfiniteLattice.AmbientSpace) '' offsetBox L 1 :=
    (Hb.eq_image y).le hx
  obtain ⟨ν, hν, hxν⟩ := hx'
  obtain ⟨σ, e⟩ := leg_eq_contour L y x π
  have hb' : b ∈ contour L y x σ := by
    rw [← e]
    exact hb
  obtain ⟨-, -, -, -, hz⟩ := (Hc.1.contours y ν hν x hxν.symm).2 _ ⟨σ, rfl⟩
  exact ⟨hz b.initial (Or.inr (Or.inr ⟨b, hb', Or.inl rfl⟩)),
    hz b.terminal (Or.inr (Or.inr ⟨b, hb', Or.inr rfl⟩))⟩
private theorem holonomy_congr_of_eqOn {a : ℝ} {V V' : InfiniteLattice.Link a → ComplexMatrix2}
    {Γ : List (InfiniteLattice.Link a)} (h : ∀ b ∈ Γ, V b = V' b) :
    linkHolonomy V Γ = linkHolonomy V' Γ := by apply _root_.YangMills.Construction.Tower.PairContourIndependence.Infinite.linkHolonomy_congr <;> assumption
private theorem contourMean_congr (hZ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : FullSpace.Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {V V' : FullSpace.Edge L k j → ComplexMatrix2}
    (h : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    contourMean V c = contourMean V' c := by
  have hT := (hZ L hL k 1 (j + 1) (by omega) (by omega) (by omega)).2.2.2.1
  unfold contourMean
  refine congrArg _ (finsum_mem_congr rfl fun x hx => Finset.sum_congr rfl fun π _ => ?_)
  have hx2 : shifted c x ∈ cubeVertices L (meshAt L k j) c.terminal := by
    show ((shifted c x : FullSpace.Vertex L k j) : InfiniteLattice.AmbientSpace) ∈
      cube L (meshAt L k j) c.terminal
    rw [hT.coe_shifted c x hx]
    exact (hT.bijOn c).mapsTo hx
  unfold contourHolonomy
  rw [holonomy_congr_of_eqOn (V := V) (V' := V') (Γ := contourLeg c.initial x π) fun b hb => by
      have e := leg_endpoints_mem_cube hZ hL hj hx π hb
      exact h b ⟨Or.inl e.1, Or.inl e.2⟩,
    holonomy_congr_of_eqOn (V := V) (V' := V') (Γ := crossingPath c x) fun b hb => by
      have e1 := hT.crossingPath_vertex_mem c hc x hx b.initial
        (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩))
      have e2 := hT.crossingPath_vertex_mem c hc x hx b.terminal
        (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩))
      exact h b ⟨e1, e2⟩,
    holonomy_congr_of_eqOn (V := V) (V' := V') (Γ := contourLeg c.terminal (shifted c x) π)
      fun b hb => by
      have e := leg_endpoints_mem_cube hZ hL hj hx2 π hb
      exact h b ⟨Or.inr e.1, Or.inr e.2⟩]
private theorem meanRadius_congr (hZ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : FullSpace.Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {V V' : FullSpace.Edge L k j → ComplexMatrix2}
    (h : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    meanRadius V c = meanRadius V' c := by
  unfold meanRadius
  rw [contourMean_congr hZ hL hj hc h]
private theorem normalizedMean_congr (hZ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : FullSpace.Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {V V' : FullSpace.Edge L k j → ComplexMatrix2}
    (h : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    normalizedMean V c = normalizedMean V' c := by
  unfold normalizedMean
  rw [meanRadius_congr hZ hL hj hc h, contourMean_congr hZ hL hj hc h]
end Legs
section Families
variable {L k j : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
private theorem expTwist_congr {V V' X : FullSpace.Edge L k j → ComplexMatrix2}
    {P : Set (FullSpace.Edge L k j)} (hP : ∀ b ∈ P, b.opposite ∈ P) (h : ∀ b ∈ P, V b = V' b)
    {b : FullSpace.Edge L k j} (hb : b ∈ P) : expTwist X V b = expTwist X V' b := by
  unfold expTwist
  split_ifs
  · rw [h b hb]
  · rw [h _ (hP b hb)]
private theorem expTwist_of_eq_zero {V X : FullSpace.Edge L k j → ComplexMatrix2}
    {P : Set (FullSpace.Edge L k j)} (hP : ∀ b ∈ P, b.opposite ∈ P)
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (h : ∀ b ∈ P, X b = 0) {b : FullSpace.Edge L k j} (hb : b ∈ P) : expTwist X V b = V b := by apply _root_.YangMills.SharedProofs.p9435 <;> assumption
private theorem expTwist_eq_self {V X : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) (h : ∀ b, X b = 0) :
    expTwist X V = V :=
  funext fun b => expTwist_of_eq_zero (P := Set.univ) (fun _ _ => mem_univ _) hV
    (fun b _ => h b) (mem_univ b)
private theorem expTwist_mem (hA : Tower.LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {V X : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hX : X ∈ complexEdgeForms (meshAt L k j)) :
    expTwist X V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := by
  have ha := meshAt_pos hL k j
  have hgp : ∀ b : FullSpace.Edge L k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • X b) * V b ∈ PeriodicLattice.complexGaugeGroup :=
    fun b hb => by
    have h := (((hA.2.2 L k j hL hj.le).2.1.1).2 V hV X hX ⟨b, hb⟩).1 1
    have e : ((1 : ℂ) • X b) = X b := one_smul _ _
    have h' : ComplexMatrix2.matExp (Complex.I • ((1 : ℂ) • X b)) * V b ∈
        PeriodicLattice.complexGaugeGroup := h
    rwa [e] at h'
  have hpos : ∀ b : FullSpace.Edge L k j, b.IsPositivelyOriented →
      expTwist X V b = ComplexMatrix2.matExp (Complex.I • X b) * V b := fun b hb => if_pos hb
  have hneg : ∀ b : FullSpace.Edge L k j, ¬ b.IsPositivelyOriented → expTwist X V b =
      (ComplexMatrix2.matExp (Complex.I • X b.opposite) * V b.opposite)⁻¹ := fun b hb => if_neg hb
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [hpos b hb]
      exact hgp b hb
    · rw [hneg b hb]
      exact inv_mem_gaugeGroup (hgp _ ((positive_or_opposite_positive b).resolve_left hb))
  · by_cases hb : b.IsPositivelyOriented
    · rw [hneg _ (not_positive_opposite ha hb), hpos b hb]
      rfl
    · have hr := (positive_or_opposite_positive b).resolve_left hb
      rw [hpos _ hr, hneg b hb]
      exact (inv_inv_of_mem_gaugeGroup (hgp _ hr)).symm
private theorem analyticAt_expTwist {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hdet : ∀ b, Matrix.det (V b) = 1)
    {X : E → FullSpace.Edge L k j → ComplexMatrix2}
    (hX : ∀ b, ∃ m : E →L[ℂ] ComplexMatrix2, ∀ q, X q b = m q) {q₀ : E}
    (h0 : ∀ b, X q₀ b = 0) (b : FullSpace.Edge L k j) :
    AnalyticAt ℂ (fun q => expTwist (X q) V b) q₀ := by apply _root_.YangMills.SharedProofs.p50643 <;> assumption
end Families
section Contours
variable {L k j : ℕ}
private theorem opposite_mem_doubleCubeLinks {c : FullSpace.Edge L k (j + 1)}
    {b : FullSpace.Edge L k j} (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) :
    b.opposite ∈ doubleCubeLinks L (meshAt L k j) c := ⟨hb.2, hb.1⟩
private theorem mem_polydisc_of_eqOn {ρ : ℝ} {c : FullSpace.Edge L k (j + 1)}
    {V V' : FullSpace.Edge L k j → ComplexMatrix2} (hV : V ∈ nearIdentityPolydisc L k j ρ c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V' b = V b) :
    V' ∈ nearIdentityPolydisc L k j ρ c := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.mem_polydisc_of_eqOn <;> assumption
private theorem complexContourMean_congr (hS : Tower.SmoothingNearIdentity)
    (hQ : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : FullSpace.Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {y : FullSpace.Vertex L k (j + 1)}
    (hy : y = c.initial ∨ y = c.terminal)
    {x : FullSpace.Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {V V' : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (hV' : V' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    complexContourMean L V y x = complexContourMean L V' y x := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.complexContourMean_congr <;> assumption
end Contours
section Derivatives
variable {L k j : ℕ}
private theorem logDeriv_of_curve
    (hlog : ∀ ρ : ℝ, 0 < ρ → Tower.LeftChartFields.CurveLogDerivative ℂ (Metric.ball 0 ρ)
      PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra)
    {φ : (FullSpace.Edge L k j → ComplexMatrix2) → ComplexMatrix2} {W : ComplexMatrix2}
    {B : FullSpace.Edge L k j → ComplexMatrix2} {D : ComplexMatrix2}
    (hγ : HasDerivAt (fun t : ℂ => φ (t • B)) D 0)
    (hg : ∀ᶠ t in 𝓝 (0 : ℂ), φ (t • B) ∈ PeriodicLattice.complexGaugeGroup)
    (h0 : φ ((0 : ℂ) • B) = W) :
    logDirectionalDeriv ℂ φ W B = Complex.I⁻¹ • (D * W⁻¹) ∧
      Complex.I⁻¹ • (D * W⁻¹) ∈ ComplexMatrix2.traceless := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hg
  obtain ⟨-, -, e, e'⟩ := hlog r hr (fun t => φ (t • B)) (fun t ht => hball t ht)
    hγ.differentiableAt
  rw [hγ.deriv] at e e'
  simp only [h0] at e e'
  exact ⟨e, e'⟩
private theorem logDeriv_of_const {φ : (FullSpace.Edge L k j → ComplexMatrix2) → ComplexMatrix2}
    {W : ComplexMatrix2} {B : FullSpace.Edge L k j → ComplexMatrix2}
    (h : ∀ t : ℂ, φ (t • B) = W) :
    logDirectionalDeriv ℂ φ W B = 0 := by
  unfold logDirectionalDeriv
  have e : (fun t : ℂ => ComplexMatrix2.logSeries (φ (algebraMap ℂ ℂ t • B) * W⁻¹)) =
      fun _ => ComplexMatrix2.logSeries (W * W⁻¹) := funext fun t => by
    rw [show algebraMap ℂ ℂ t = t from rfl, h]
  rw [e]
  simp
private theorem logDeriv_congr {φ φ' : (FullSpace.Edge L k j → ComplexMatrix2) → ComplexMatrix2}
    {W : ComplexMatrix2} {B : FullSpace.Edge L k j → ComplexMatrix2}
    (h : ∀ᶠ t in 𝓝 (0 : ℂ), φ (t • B) = φ' (t • B)) :
    logDirectionalDeriv ℂ φ W B = logDirectionalDeriv ℂ φ' W B := by
  unfold logDirectionalDeriv
  refine congrArg _ (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [h] with t ht
  show ComplexMatrix2.logSeries (φ (t • B) * _) = ComplexMatrix2.logSeries (φ' (t • B) * _)
  rw [ht]
private def meanPart (V B : FullSpace.Edge L k j → ComplexMatrix2) (c : FullSpace.Edge L k (j + 1)) :
    ComplexMatrix2 :=
  logDirectionalDeriv ℂ (fun X => normalizedMean (expTwist X V) c) (normalizedMean V c) B
private theorem meanPart_linear (hA : Tower.LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    {c : FullSpace.Edge L k (j + 1)}
    (hs : Matrix.det (contourMean V c) ∈ Complex.slitPlane) (hr : meanRadius V c ≠ 0)
    {B B' : FullSpace.Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j))
    (hB' : B' ∈ complexEdgeForms (meshAt L k j)) :
    ∃ T : ℂ × ℂ →L[ℂ] ComplexMatrix2, ∀ α β : ℂ, meanPart V (α • B + β • B') c = T (α, β) ∧
      T (α, β) ∈ ComplexMatrix2.traceless := by
  have hdet : ∀ b, Matrix.det (V b) = 1 := fun b => hV.1 b
  let X : ℂ × ℂ → FullSpace.Edge L k j → ComplexMatrix2 := fun q => q.1 • B + q.2 • B'
  let W : ℂ × ℂ → FullSpace.Edge L k j → ComplexMatrix2 := fun q => expTwist (X q) V
  have hX0 : ∀ b, X 0 b = 0 := fun b => by simp [X]
  have hXl : ∀ b, ∃ m : ℂ × ℂ →L[ℂ] ComplexMatrix2, ∀ q, X q b = m q := fun b =>
    ⟨(ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight (B b) +
      (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight (B' b), fun q => by simp [X]⟩
  have hW : ∀ b, AnalyticAt ℂ (fun q => W q b) 0 := analyticAt_expTwist hdet hXl hX0
  have hW0 : W 0 = V := expTwist_eq_self hV hX0
  have hdet0 : ∀ b, Matrix.det (W 0 b) = 1 := fun b => by
    rw [hW0]
    exact hdet b
  have hs0 : Matrix.det (contourMean (W 0) c) ∈ Complex.slitPlane := by
    rw [hW0]
    exact hs
  have hr0 : meanRadius (W 0) c ≠ 0 := by
    rw [hW0]
    exact hr
  have hH := analyticAt_normalizedMean hW hdet0 hs0 hr0
  have hg := eventually_normalizedMean_mem hW hdet0 hs0 hr0
  set H : ℂ × ℂ → ComplexMatrix2 := fun q => normalizedMean (W q) c with hHdef
  have hlog := fun (ρ : ℝ) (hρ : 0 < ρ) => hA.2.1 ρ hρ
  refine ⟨(Complex.I⁻¹ • ((ContinuousLinearMap.mul ℂ ComplexMatrix2).flip
    (normalizedMean V c)⁻¹)).comp (fderiv ℂ H 0), fun α β => ?_⟩
  let l : ℂ → ℂ × ℂ := fun t => (t * α, t * β)
  have hl : HasDerivAt l (α, β) 0 := by
    have h1 := (hasDerivAt_id (0 : ℂ)).mul_const α
    have h2 := (hasDerivAt_id (0 : ℂ)).mul_const β
    simpa [l] using h1.prodMk h2
  have hl0 : l 0 = 0 := by simp [l]
  have hd : HasFDerivAt H (fderiv ℂ H 0) (l 0) := by
    rw [hl0]
    exact hH.differentiableAt.hasFDerivAt
  have hHl := HasFDerivAt.comp_hasDerivAt (0 : ℂ) hd hl
  have ef : (fun t : ℂ => normalizedMean (expTwist (t • (α • B + β • B')) V) c) = H ∘ l := by
    funext t
    show normalizedMean (expTwist (t • (α • B + β • B')) V) c =
      normalizedMean (expTwist ((t * α) • B + (t * β) • B') V) c
    rw [smul_add, smul_smul, smul_smul]
  have hγ : HasDerivAt (fun t : ℂ => normalizedMean (expTwist (t • (α • B + β • B')) V) c)
      (fderiv ℂ H 0 (α, β)) 0 := by
    rw [ef]
    exact hHl
  have hgl : ∀ᶠ t in 𝓝 (0 : ℂ), normalizedMean (expTwist (t • (α • B + β • B')) V) c ∈
      PeriodicLattice.complexGaugeGroup := by
    have ht : Tendsto l (𝓝 0) (𝓝 0) := by
      have := hl.continuousAt.tendsto
      rwa [hl0] at this
    filter_upwards [ht.eventually hg] with t h
    rw [show normalizedMean (expTwist (t • (α • B + β • B')) V) c = H (l t) from congrFun ef t]
    exact h
  have h00 : normalizedMean (expTwist ((0 : ℂ) • (α • B + β • B')) V) c = normalizedMean V c := by
    rw [expTwist_eq_self hV fun b => by simp]
  have := logDeriv_of_curve hlog (φ := fun X => normalizedMean (expTwist X V) c) hγ hgl h00
  have e : ((Complex.I⁻¹ • ((ContinuousLinearMap.mul ℂ ComplexMatrix2).flip
      (normalizedMean V c)⁻¹)).comp (fderiv ℂ H 0)) (α, β) =
      Complex.I⁻¹ • (fderiv ℂ H 0 (α, β) * (normalizedMean V c)⁻¹) := rfl
  rw [e]
  exact this
end Derivatives
section Step
variable {L k j : ℕ}
private theorem step_of_positive (V B : FullSpace.Edge L k j → ComplexMatrix2)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented) :
    meanCovariantStep V B c = meanPart V B c +
      (ComplexMatrix2.conjugateBy (normalizedMean V c) (contourLogDrift V B c.terminal) -
        contourLogDrift V B c.initial) := by apply _root_.YangMills.DeltaSharedProofs.p501203 <;> assumption
private theorem extendOddly_opposite {a : ℝ} (ha : 0 < a)
    (f : InfiniteLattice.Link a → ComplexMatrix2) (b : InfiniteLattice.Link a) :
    extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
private theorem step_opposite (hL : Conventions.IsAdmissibleBlockingFactor L)
    (V B : FullSpace.Edge L k j → ComplexMatrix2) (c : FullSpace.Edge L k (j + 1)) :
    meanCovariantStep V B c.opposite = -meanCovariantStep V B c := by
  have ha := meshAt_pos hL k (j + 1)
  unfold meanCovariantStep FullSpace.covDiff
  simp only [Pi.add_apply, extendOddly_opposite ha, neg_add]
private theorem conj_mem_traceless (V : ComplexMatrix2) {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy V A ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
private theorem eventually_expTwist_mem_polydisc (hA : Tower.LeftChartFields.Claim)
    (hPd : Tower.DoubleBlockPolydisc.PolydiscsHold) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    {r : ℝ} (hr : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r)
    {B : FullSpace.Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j))
    {c : FullSpace.Edge L k (j + 1)} (hcp : c.IsPositivelyOriented) :
    ∀ᶠ t in 𝓝 (0 : ℂ), expTwist (t • B) V ∈ nearIdentityPolydisc L k j r c := by
  have hfin := ((hPd L hL k j hj).2 c hcp).finite_open.finite
  have hXl : ∀ b, ∃ m : ℂ →L[ℂ] ComplexMatrix2, ∀ t : ℂ, (t • B) b = m t := fun b =>
    ⟨(ContinuousLinearMap.id ℂ ℂ).smulRight (B b), fun t => by simp⟩
  have hnorm : ∀ᶠ t in 𝓝 (0 : ℂ),
      ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
        ComplexMatrix2.operatorNorm (expTwist (t • B) V b - 1) < r := by
    refine (Filter.eventually_all_finite hfin).2 fun b _ => ?_
    have hcont := (analyticAt_expTwist (fun b => hV.1 b) hXl (q₀ := (0 : ℂ))
      (fun b => by simp) b).continuousAt
    have h0 : expTwist ((0 : ℂ) • B) V b ∈ Metric.ball (1 : ComplexMatrix2) r := by
      rw [expTwist_eq_self hV fun b => by simp, mem_ball_iff_norm]
      exact hr b
    filter_upwards [hcont.eventually (Metric.isOpen_ball.mem_nhds h0)] with t ht
    exact mem_ball_iff_norm.1 ht
  filter_upwards [hnorm] with t h2
  have h3 := expTwist_mem hA hL hj hV (Submodule.smul_mem _ t hB)
  exact ⟨⟨fun b _ => h3.1 b, fun b _ => h3.2 b⟩, h2⟩
abbrev _root_.YangMills.SharedProofs.p8922 := @eventually_expTwist_mem_polydisc
private theorem contourLogDrift_eq_zero (hS : Tower.SmoothingNearIdentity)
    (hQ : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : FullSpace.Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {y : FullSpace.Vertex L k (j + 1)}
    (hy : y = c.initial ∨ y = c.terminal) {V B : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hP : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (hz : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, B b = 0) :
    contourLogDrift V B y = 0 := by
  unfold FullSpace.contourLogDrift
  have : ∀ x ∈ cubeVertices L (meshAt L k j) y,
      logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
        (complexContourMean L V y x) B = 0 := fun x hx => logDeriv_of_const fun t => by
    have he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, expTwist (t • B) V b = V b :=
      fun b hb => expTwist_of_eq_zero (fun _ h => opposite_mem_doubleCubeLinks h) hV
        (fun b' hb' => by simp [hz b' hb']) hb
    exact complexContourMean_congr hS hQ hL hj hc hy hx (mem_polydisc_of_eqOn hP he) hP he
  rw [finsum_mem_congr rfl this]
  simp
private theorem contourLogDrift_congr (hS : Tower.SmoothingNearIdentity)
    (hQ : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hA : Tower.LeftChartFields.Claim)
    (hPd : Tower.DoubleBlockPolydisc.PolydiscsHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : FullSpace.Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {y : FullSpace.Vertex L k (j + 1)}
    (hy : y = c.initial ∨ y = c.terminal) {V V' B : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hr : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L)
    (hP : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b)
    (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    contourLogDrift V B y = contourLogDrift V' B y := by
  unfold FullSpace.contourLogDrift
  refine congrArg _ (finsum_mem_congr rfl fun x hx => ?_)
  have hP' : V' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c :=
    mem_polydisc_of_eqOn hP fun b hb => (he b hb).symm
  rw [complexContourMean_congr hS hQ hL hj hc hy hx hP hP' he]
  refine logDeriv_congr ?_
  filter_upwards [eventually_expTwist_mem_polydisc hA hPd hL hj hV hr hB hc] with t ht
  have he' : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
      expTwist (t • B) V b = expTwist (t • B) V' b := fun b hb =>
    expTwist_congr (fun _ h => opposite_mem_doubleCubeLinks h) he hb
  exact complexContourMean_congr hS hQ hL hj hc hy hx ht
    (mem_polydisc_of_eqOn ht fun b hb => (he' b hb).symm) he'
end Step
end MeanStepOnForms
open MeanStepOnForms in
theorem MeanStepOnForms.holds (hN : NormalizedMeanNearIdentity)
    (hZ : Tower.BlockPathContourPivotStatement)
    (hS : Tower.SmoothingNearIdentity)
    (hQ : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hA : Tower.LeftChartFields.Claim)
    (hPd : Tower.DoubleBlockPolydisc.PolydiscsHold)
    (hLin : Tower.FullSpace.CovariantStepComplexLinear) :
    MeanStepOnForms := by
  intro L hL
  obtain ⟨δ₁, hδ₁, H⟩ := hN L hL 1 one_pos
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  refine ⟨min δ₁ (polydiscRadius L), lt_min hδ₁ hρ, ?_⟩
  intro k j hj V hV
  have hr : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L := fun b =>
    (hV.2 b).trans_le (min_le_right _ _)
  have hsm : V ∈ FullSpace.smallComplexFields L k j := ⟨hV.1, hr⟩
  have hnear := fun (c : FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented) =>
    H k j hj V hV.1 (fun b => (hV.2 b).trans_le (min_le_left _ _)) c hc
  obtain ⟨hL1, hL2, -, -⟩ := hLin L hL k j hj V hsm
  have hPol : ∀ c : FullSpace.Edge L k (j + 1),
      V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c := fun c =>
    ⟨⟨fun b _ => hV.1.1 b, fun b _ => hV.1.2 b⟩, fun b _ => hr b⟩
  have hU : ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
      ∀ B ∈ complexEdgeForms (meshAt L k j), ∀ B' ∈ complexEdgeForms (meshAt L k j),
        ∀ z : ℂ, meanPart V (z • B + B') c = z • meanPart V B c + meanPart V B' c ∧
          meanPart V B c ∈ ComplexMatrix2.traceless := by
    intro c hc B hB B' hB' z
    obtain ⟨T, hT⟩ := meanPart_linear hA hL hj hV.1 (hnear c hc).1 (hnear c hc).2.1 hB hB'
    have e1 : meanPart V (z • B + B') c = T (z, 1) := by
      have := (hT z 1).1
      rwa [one_smul] at this
    have e2 : meanPart V B c = T (1, 0) := by
      have := (hT 1 0).1
      rwa [one_smul, zero_smul, add_zero] at this
    have e3 : meanPart V B' c = T (0, 1) := by
      have := (hT 0 1).1
      rwa [one_smul, zero_smul, zero_add] at this
    refine ⟨?_, e2 ▸ (hT 1 0).2⟩
    rw [e1, e2, e3, ← map_smul, ← map_add]
    congr 1
    simp
  have hAd₁ : ∀ (U X Y : ComplexMatrix2), ComplexMatrix2.conjugateBy U (X + Y) =
      ComplexMatrix2.conjugateBy U X + ComplexMatrix2.conjugateBy U Y := fun U X Y => by
    simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
  have hAd₂ : ∀ (U X : ComplexMatrix2) (z : ℂ), ComplexMatrix2.conjugateBy U (z • X) =
      z • ComplexMatrix2.conjugateBy U X := fun U X z => by
    simp only [ComplexMatrix2.conjugateBy, mul_smul_comm, smul_mul_assoc]
  have ha := meshAt_pos hL k (j + 1)
  refine ⟨fun B hB => ⟨fun c hc => ?_, fun c => step_opposite hL V B c⟩, fun B hB B' hB' z => ?_,
    fun c hc B hB hz => ?_, fun c hc V' hV' he => ?_⟩
  · rw [step_of_positive V B hc]
    exact ComplexMatrix2.traceless.add_mem (hU c hc B hB B hB 0).2
      (ComplexMatrix2.traceless.sub_mem (conj_mem_traceless _ ((hL1 B hB).2 _)) ((hL1 B hB).2 _))
  · have hpos : ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
        meanCovariantStep V (z • B + B') c =
          z • meanCovariantStep V B c + meanCovariantStep V B' c := by
      intro c hc
      rw [step_of_positive _ _ hc, step_of_positive _ _ hc, step_of_positive _ _ hc,
        (hU c hc B hB B' hB' z).1, (hL2 B hB B' hB' z).2]
      simp only [Pi.add_apply, Pi.smul_apply, hAd₁, hAd₂]
      module
    funext c
    by_cases hc : c.IsPositivelyOriented
    · exact hpos c hc
    · have hr' := (positive_or_opposite_positive c).resolve_left hc
      have e : ∀ B₀ : FullSpace.Edge L k j → ComplexMatrix2,
          meanCovariantStep V B₀ c = -meanCovariantStep V B₀ c.opposite := fun B₀ =>
        step_opposite hL V B₀ c.opposite
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [e, e B, e B', hpos _ hr']
      module
  · rw [step_of_positive V B hc,
      contourLogDrift_eq_zero hS hQ hL hj hc (Or.inl rfl) hV.1 (hPol c) hz,
      contourLogDrift_eq_zero hS hQ hL hj hc (Or.inr rfl) hV.1 (hPol c) hz]
    have hu : meanPart V B c = 0 := logDeriv_of_const fun t =>
      normalizedMean_congr hZ hL hj hc fun b hb =>
        expTwist_of_eq_zero (fun _ h => opposite_mem_doubleCubeLinks h) hV.1
          (fun b' hb' => by simp [hz b' hb']) hb
    rw [hu]
    simp [ComplexMatrix2.conjugateBy]
  · refine ⟨meanRadius_congr hZ hL hj hc he, normalizedMean_congr hZ hL hj hc he, fun B hB => ?_,
      fun y hy x hx => complexContourMean_congr hS hQ hL hj hc hy hx (hPol c)
        (mem_polydisc_of_eqOn (hPol c) fun b hb => (he b hb).symm) he⟩
    rw [step_of_positive _ _ hc, step_of_positive _ _ hc,
      contourLogDrift_congr hS hQ hA hPd hL hj hc (Or.inl rfl) hV.1 hr (hPol c) he hB,
      contourLogDrift_congr hS hQ hA hPd hL hj hc (Or.inr rfl) hV.1 hr (hPol c) he hB,
      normalizedMean_congr hZ hL hj hc he]
    have hu : meanPart V B c = meanPart V' B c := by
      unfold meanPart
      rw [normalizedMean_congr hZ hL hj hc he]
      refine logDeriv_congr (Eventually.of_forall fun t => ?_)
      exact normalizedMean_congr hZ hL hj hc fun b hb =>
        expTwist_congr (fun _ h => opposite_mem_doubleCubeLinks h) he hb
    rw [hu]
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
