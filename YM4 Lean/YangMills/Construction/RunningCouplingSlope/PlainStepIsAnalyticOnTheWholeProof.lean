import YangMills.Construction.RunningCouplingSlope.PlainStepAtRealConfigurationsOnTheWholeProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
namespace MeanStepAnalyticity
open YangMills.Construction.Tower YangMills.Construction.Tower.FullSpace YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct
private instance : CompleteSpace ComplexMatrix2 := FiniteDimensional.complete ℂ ComplexMatrix2
section Matrices
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem analyticAt_inv' {f : E → ComplexMatrix2} {x : E} (hf : AnalyticAt ℂ f x)
    (hu : IsUnit (Matrix.det (f x))) : AnalyticAt ℂ (fun y => (f y)⁻¹) x := by apply _root_.YangMills.SharedProofs.p7089 <;> assumption
private theorem analyticAt_det {f : E → ComplexMatrix2} {x : E} (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun y => Matrix.det (f y)) x := by apply _root_.YangMills.SharedProofs.p3818 <;> assumption
private theorem inv_inv_of_mem_gaugeGroup {X : ComplexMatrix2}
    (h : X ∈ PeriodicLattice.complexGaugeGroup) : X⁻¹⁻¹ = X := by apply _root_.YangMills.SharedProofs.p6288 <;> assumption
private theorem inv_mem_gaugeGroup {X : ComplexMatrix2} (h : X ∈ PeriodicLattice.complexGaugeGroup) :
    X⁻¹ ∈ PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
end Matrices
section Logarithms
variable {l : ℕ}
private theorem analyticAt_logDeriv_curve
    (hlog : ∀ ρ : ℝ, 0 < ρ → LeftChartFields.CurveLogDerivative ℂ (Metric.ball 0 ρ)
      PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra)
    {p : Coordinates.ComplexCoordinates l} {F : Coordinates.ComplexCoordinates l × ℂ → ComplexMatrix2}
    (hF : AnalyticAt ℂ F (p, 0))
    (hg : ∀ᶠ q in 𝓝 (p, (0 : ℂ)), F q ∈ PeriodicLattice.complexGaugeGroup) :
    AnalyticAt ℂ (fun z => Complex.I⁻¹ •
      deriv (fun t : ℂ => ComplexMatrix2.logSeries (F (z, t) * (F (z, 0))⁻¹)) 0) p := by
  let ι : Coordinates.ComplexCoordinates l →L[ℂ] Coordinates.ComplexCoordinates l × ℂ :=
    ContinuousLinearMap.inl ℂ _ ℂ
  have hι : ∀ z, ι z = (z, 0) := fun z => rfl
  have hFι : AnalyticAt ℂ (fun z => F (z, 0)) p :=
    AnalyticAt.comp (g := F) (f := ι) (by simpa [hι] using hF) (ι.analyticAt p)
  have hD : AnalyticAt ℂ (fun z => fderiv ℂ F (z, 0) (0, 1)) p := by
    have h1 : AnalyticAt ℂ (fun z => fderiv ℂ F (z, 0)) p :=
      AnalyticAt.comp (g := fderiv ℂ F) (f := ι) (by simpa [hι] using hF.fderiv) (ι.analyticAt p)
    exact ((ContinuousLinearMap.apply ℂ ComplexMatrix2
      ((0, 1) : Coordinates.ComplexCoordinates l × ℂ)).analyticAt _).comp h1
  have hθ : AnalyticAt ℂ
      (fun z => Complex.I⁻¹ • (fderiv ℂ F (z, 0) (0, 1) * (F (z, 0))⁻¹)) p := by
    have hu : IsUnit (Matrix.det (F (p, 0))) := by
      have e : Matrix.det (F (p, 0)) = 1 := hg.self_of_nhds
      rw [e]
      exact isUnit_one
    exact analyticAt_const.fun_smul (hD.fun_mul (analyticAt_inv' hFι hu))
  refine hθ.congr ?_
  have hAn : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ F (z, 0) :=
    hF.eventually_analyticAt.curry_nhds.mono fun z h => h.self_of_nhds
  filter_upwards [hAn, hg.curry_nhds] with z hz ht
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 ht
  have hline : HasDerivAt (fun t : ℂ => ((z, t) : Coordinates.ComplexCoordinates l × ℂ)) (0, 1) 0 :=
    (hasDerivAt_const (0 : ℂ) z).prodMk (hasDerivAt_id (0 : ℂ))
  have hγ : HasDerivAt (fun t : ℂ => F (z, t)) (fderiv ℂ F (z, 0) (0, 1)) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun t : ℂ => ((z, t) : Coordinates.ComplexCoordinates l × ℂ))
      (0 : ℂ) hz.differentiableAt.hasFDerivAt hline
  obtain ⟨-, -, e, -⟩ := hlog r hr (fun t => F (z, t)) (fun t ht' => hball t ht') hγ.differentiableAt
  rw [hγ.deriv] at e
  exact e.symm
end Logarithms
section Bonds
variable {a : ℝ}
private theorem isPos_or_opposite_isPos (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
private theorem not_opposite_isPos (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
private theorem extendOddly_of_pos (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) : extendOddly f b = f b := if_pos hb
private theorem extendOddly_of_not_pos (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : ¬ b.IsPositivelyOriented) :
    extendOddly f b = -f b.opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.CovarianceProof.extendOddly_of_not_pos <;> assumption
private theorem cubeVertices_finite (L : ℕ) {a : ℝ} (a' : ℝ) (y : InfiniteLattice.LatticePoint a) :
    (cubeVertices L a' y : Set (InfiniteLattice.LatticePoint a')).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.cubeVertices_finite <;> assumption
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
  (analyticAt_det (analyticAt_contourMean hW hdet c)).cpow analyticAt_const hs
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
section Moved
variable {L k j : ℕ} {l : ℕ}
private theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
private def twisted (W : Coordinates.ComplexCoordinates l → FullSpace.Edge L k j → ComplexMatrix2)
    (B : FullSpace.Edge L k j → ComplexMatrix2) (q : Coordinates.ComplexCoordinates l × ℂ) :
    FullSpace.Edge L k j → ComplexMatrix2 :=
  expTwist (q.2 • B) (W q.1)
private theorem expTwist_zero {V B : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) :
    expTwist ((0 : ℂ) • B) V = V := by
  funext b
  unfold expTwist
  by_cases hb : b.IsPositivelyOriented
  · simp [hb, ComplexMatrix2.matExp]
  · have h1 : V b.opposite = (V b)⁻¹ := hV.2 b
    simp only [hb, if_false, zero_smul, Pi.zero_apply, smul_zero]
    rw [h1]
    have h2 : ComplexMatrix2.matExp (0 : ComplexMatrix2) = 1 := NormedSpace.exp_zero
    rw [h2, one_mul]
    exact inv_inv_of_mem_gaugeGroup (hV.1 b)
private theorem twisted_zero
    {W : Coordinates.ComplexCoordinates l → FullSpace.Edge L k j → ComplexMatrix2}
    {B : FullSpace.Edge L k j → ComplexMatrix2} {z : Coordinates.ComplexCoordinates l}
    (hV : W z ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) :
    twisted W B (z, 0) = W z := expTwist_zero hV
private theorem twisted_pos_mem (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {V B : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms (meshAt L k j)) (t : ℂ) {b : FullSpace.Edge L k j}
    (hb : b.IsPositivelyOriented) :
    ComplexMatrix2.matExp (Complex.I • (t • B) b) * V b ∈ PeriodicLattice.complexGaugeGroup :=
  (((hA.2.2 L k j hL hj.le).2.1.1).2 V hV B hB ⟨b, hb⟩).1 t
private theorem expTwist_mem (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {V B : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms (meshAt L k j)) (t : ℂ) :
    expTwist (t • B) V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := by
  have ha := meshAt_pos hL k j
  have hpos : ∀ b : FullSpace.Edge L k j, b.IsPositivelyOriented →
      expTwist (t • B) V b = ComplexMatrix2.matExp (Complex.I • (t • B) b) * V b :=
    fun b hb => if_pos hb
  have hneg : ∀ b : FullSpace.Edge L k j, ¬ b.IsPositivelyOriented → expTwist (t • B) V b =
      (ComplexMatrix2.matExp (Complex.I • (t • B) b.opposite) * V b.opposite)⁻¹ :=
    fun b hb => if_neg hb
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [hpos b hb]
      exact twisted_pos_mem hA hL hj hV hB t hb
    · rw [hneg b hb]
      exact inv_mem_gaugeGroup (twisted_pos_mem hA hL hj hV hB t
        ((isPos_or_opposite_isPos b).resolve_left hb))
  · by_cases hb : b.IsPositivelyOriented
    · rw [hneg _ (not_opposite_isPos ha hb), hpos b hb]
      rfl
    · have hr := (isPos_or_opposite_isPos b).resolve_left hb
      rw [hpos _ hr, hneg b hb]
      exact (inv_inv_of_mem_gaugeGroup (twisted_pos_mem hA hL hj hV hB t hr)).symm
private theorem analyticAt_twisted
    {W : Coordinates.ComplexCoordinates l → FullSpace.Edge L k j → ComplexMatrix2}
    {p : Coordinates.ComplexCoordinates l} (hW : ∀ b, AnalyticAt ℂ (fun z => W z b) p)
    (hdet : ∀ b, Matrix.det (W p b) = 1) (B : FullSpace.Edge L k j → ComplexMatrix2)
    (b : FullSpace.Edge L k j) :
    AnalyticAt ℂ (fun q => twisted W B q b) (p, 0) := by
  have hval : ∀ b' : FullSpace.Edge L k j,
      AnalyticAt ℂ (fun q : Coordinates.ComplexCoordinates l × ℂ =>
        ComplexMatrix2.matExp (Complex.I • (q.2 • B) b') * W q.1 b') (p, 0) := fun b' => by
    let m : Coordinates.ComplexCoordinates l × ℂ →L[ℂ] ComplexMatrix2 :=
      (ContinuousLinearMap.snd ℂ (Coordinates.ComplexCoordinates l) ℂ).smulRight (Complex.I • B b')
    have hm : ∀ q : Coordinates.ComplexCoordinates l × ℂ, Complex.I • (q.2 • B) b' = m q :=
      fun q => by
        simp only [Pi.smul_apply, m, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.coe_snd']
        exact smul_comm _ _ _
    have h1 : AnalyticAt ℂ
        (fun q : Coordinates.ComplexCoordinates l × ℂ => ComplexMatrix2.matExp (m q)) (p, 0) :=
      (NormedSpace.exp_analytic (𝕂 := ℂ) (m (p, 0))).comp (m.analyticAt _)
    have h2 : AnalyticAt ℂ (fun q : Coordinates.ComplexCoordinates l × ℂ => W q.1 b') (p, 0) :=
      AnalyticAt.comp (g := fun z => W z b') (f := Prod.fst) (hW b') analyticAt_fst
    simp only [hm]
    exact h1.fun_mul h2
  by_cases hb : b.IsPositivelyOriented
  · refine (hval b).congr (Eventually.of_forall fun q => ?_)
    exact (if_pos hb : expTwist (q.2 • B) (W q.1) b = _).symm
  · have hu : IsUnit (Matrix.det (ComplexMatrix2.matExp (Complex.I •
        (((p, 0) : Coordinates.ComplexCoordinates l × ℂ).2 • B) b.opposite) * W p b.opposite)) := by
      have h2 : ComplexMatrix2.matExp (0 : ComplexMatrix2) = 1 := NormedSpace.exp_zero
      simp only [zero_smul, Pi.zero_apply, smul_zero, h2, one_mul, hdet]
      exact isUnit_one
    refine (analyticAt_inv' (hval b.opposite) hu).congr (Eventually.of_forall fun q => ?_)
    exact (if_neg hb : expTwist (q.2 • B) (W q.1) b = _).symm
end Moved
section Contours
variable {L k j : ℕ}
private theorem extendFromPositive_restrict {c : FullSpace.Edge L k (j + 1)}
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : IsFieldOn PeriodicLattice.complexGaugeGroup (doubleCubeLinks L (meshAt L k j) c) V)
    {b : FullSpace.Edge L k j} (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) :
    extendFromPositive (doubleCubeLinks L (meshAt L k j) c)
      (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V) b = V b := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.extendFromPositive_restrictPositive <;> assumption
private theorem mem_polydisc_of_eqOn {ρ : ℝ} {c : FullSpace.Edge L k (j + 1)}
    {V V' : FullSpace.Edge L k j → ComplexMatrix2} (hV : V ∈ nearIdentityPolydisc L k j ρ c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V' b = V b) :
    V' ∈ nearIdentityPolydisc L k j ρ c := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.mem_polydisc_of_eqOn <;> assumption
private theorem complexContourMean_congr (hS : YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : FullSpace.Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {y : FullSpace.Vertex L k (j + 1)}
    (hy : y = c.initial ∨ y = c.terminal)
    {x : FullSpace.Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {V V' : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (hV' : V' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    complexContourMean L V y x = complexContourMean L V' y x := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.complexContourMean_congr <;> assumption
private theorem complexContourMean_eq_ofValues (hS : YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : FullSpace.Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {y : FullSpace.Vertex L k (j + 1)}
    (hy : y = c.initial ∨ y = c.terminal)
    {x : FullSpace.Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {U' : FullSpace.Edge L k j → ComplexMatrix2}
    (hU' : U' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c) :
    complexContourMean L U' y x =
      complexContourMean L (extendFromPositive
        (doubleCubeLinks L (meshAt L k j) c)
        (restrictPositive (doubleCubeLinks L (meshAt L k j) c) U')) y x := by
  have hv := fun b (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) =>
    extendFromPositive_restrict hU'.1 hb
  exact complexContourMean_congr hS hQ hL hj hc hy hx hU'
    (mem_polydisc_of_eqOn hU' hv) fun b hb => (hv b hb).symm
private def polydiscValues (r : ℝ) (c : FullSpace.Edge L k (j + 1)) :
    Set (PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2) :=
  restrictPositive (doubleCubeLinks L (meshAt L k j) c) '' nearIdentityPolydisc L k j r c
private def contourMeanOfValues (c : FullSpace.Edge L k (j + 1)) (y : FullSpace.Vertex L k (j + 1))
    (x : FullSpace.Vertex L k j)
    (v : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2) : ComplexMatrix2 :=
  complexContourMean L (extendFromPositive (doubleCubeLinks L (meshAt L k j) c) v) y x
private theorem local_analytic_of_holomorphic {σ : Type} [inst : Fintype σ]
    {D : Set (σ → ComplexMatrix2)} {Φ : (σ → ComplexMatrix2) → ComplexMatrix2}
    (h : ∃ _ : Fintype σ, ComplexMatrix2.IsHolomorphicBetween
      (fun _ : σ => ComplexMatrix2.FactorKind.group)
      (fun _ : Unit => ComplexMatrix2.FactorKind.group) D fun v _ => Φ v) :
    MapsTo Φ D PeriodicLattice.complexGaugeGroup ∧
      ∀ x ∈ D, ∃ G : (σ → ComplexMatrix2) → ComplexMatrix2,
        AnalyticAt ℂ G x ∧ ∀ᶠ y in 𝓝[D] x, Φ y = G y := by
  obtain ⟨i, hh⟩ := h
  obtain rfl : i = inst := Subsingleton.elim _ _
  refine ⟨fun v hv => hh.2.1 hv (), fun x hx => ?_⟩
  obtain ⟨F, hFa, hFe⟩ := hh.2.2 x hx
  refine ⟨fun v => F v (),
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Unit => ComplexMatrix2) ()).analyticAt _).comp
      hFa, ?_⟩
  filter_upwards [hFe] with y hy
  exact congrFun hy ()
private theorem analyticAt_complexContourMean (hS : YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : FullSpace.Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {y : FullSpace.Vertex L k (j + 1)}
    (hy : y = c.initial ∨ y = c.terminal)
    {x : FullSpace.Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {W : E → FullSpace.Edge L k j → ComplexMatrix2} {q : E}
    (hW : ∀ b, AnalyticAt ℂ (fun x => W x b) q)
    (hP : ∀ᶠ x in 𝓝 q, W x ∈ nearIdentityPolydisc L k j (polydiscRadius L) c) :
    AnalyticAt ℂ (fun x' => complexContourMean L (W x') y x) q ∧
      ∀ᶠ x' in 𝓝 q, complexContourMean L (W x') y x ∈ PeriodicLattice.complexGaugeGroup := by
  have hserve := (hS.1 L hL).2.2.fullSpace k j hj c hc
  have hy' : y ∈ ({c.initial, c.terminal} : Set (FullSpace.Vertex L k (j + 1))) := hy
  obtain ⟨inst, hhol⟩ := (hserve.holomorphic_contourMean y hy' x hx).1
  obtain ⟨hmaps, hg⟩ := local_analytic_of_holomorphic (Φ := contourMeanOfValues c y x)
    (D := polydiscValues (polydiscRadius L) c)
    ((hserve.holomorphic_contourMean y hy' x hx).1)
  set v : E → PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2 :=
    fun q' => restrictPositive (doubleCubeLinks L (meshAt L k j) c) (W q') with hv
  have hva : AnalyticAt ℂ v q := analyticAt_pi_iff.2 fun b => hW b.1
  have hmem : ∀ᶠ q' in 𝓝 q, v q' ∈ polydiscValues (polydiscRadius L) c :=
    hP.mono fun q' h => ⟨W q', h, rfl⟩
  obtain ⟨G, hG, hGe⟩ := hg _ hmem.self_of_nhds
  have ht : Tendsto v (𝓝 q) (𝓝[polydiscValues (polydiscRadius L) c] (v q)) :=
    tendsto_nhdsWithin_iff.2 ⟨hva.continuousAt.tendsto, hmem⟩
  have hev := ht.eventually hGe
  have hval : ∀ᶠ q' in 𝓝 q,
      complexContourMean L (W q') y x = contourMeanOfValues c y x (v q') :=
    hP.mono fun q' h => complexContourMean_eq_ofValues hS hQ hL hj hc hy hx h
  refine ⟨AnalyticAt.congr (hG.comp hva) ?_, ?_⟩
  · filter_upwards [hev, hval] with q' e1 e2
    rw [e2, e1]
    rfl
  · filter_upwards [hval, hmem] with q' e1 e2
    rw [e1]
    exact hmaps e2
end Contours
section Step
variable {L k j l : ℕ}
private theorem analyticAt_logDirectionalDeriv (hA : LeftChartFields.Claim)
    {Ψ : (FullSpace.Edge L k j → ComplexMatrix2) → ComplexMatrix2}
    {W : Coordinates.ComplexCoordinates l → FullSpace.Edge L k j → ComplexMatrix2}
    {p : Coordinates.ComplexCoordinates l} {B : FullSpace.Edge L k j → ComplexMatrix2}
    (hc : ∀ᶠ z in 𝓝 p, W z ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hF : AnalyticAt ℂ (fun q => Ψ (twisted W B q)) (p, 0))
    (hg : ∀ᶠ q in 𝓝 (p, (0 : ℂ)), Ψ (twisted W B q) ∈ PeriodicLattice.complexGaugeGroup) :
    AnalyticAt ℂ (fun z => logDirectionalDeriv ℂ (fun X => Ψ (expTwist X (W z))) (Ψ (W z)) B)
      p := by
  refine (analyticAt_logDeriv_curve (fun ρ hρ => hA.2.1 ρ hρ) hF hg).congr ?_
  filter_upwards [hc] with z hz
  rw [twisted_zero hz]
  rfl
private theorem eventually_twisted_mem_polydisc (hA : LeftChartFields.Claim)
    (hPd : DoubleBlockPolydisc.PolydiscsHold) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k)
    {W : Coordinates.ComplexCoordinates l → FullSpace.Edge L k j → ComplexMatrix2}
    {p : Coordinates.ComplexCoordinates l}
    (hW : ∀ b, AnalyticAt ℂ (fun z => W z b) p)
    (hc : ∀ᶠ z in 𝓝 p, W z ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    {r : ℝ} (hr : ∀ b, ComplexMatrix2.operatorNorm (W p b - 1) < r)
    {B : FullSpace.Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j))
    {c : FullSpace.Edge L k (j + 1)} (hcp : c.IsPositivelyOriented) :
    ∀ᶠ q in 𝓝 (p, (0 : ℂ)), twisted W B q ∈ nearIdentityPolydisc L k j r c := by
  have hp := hc.self_of_nhds
  have hfin := ((hPd L hL k j hj).2 c hcp).finite_open.finite
  have hconf : ∀ᶠ q : Coordinates.ComplexCoordinates l × ℂ in 𝓝 (p, (0 : ℂ)),
      W q.1 ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
    (continuous_fst.tendsto (p, (0 : ℂ))).eventually hc
  have hnorm : ∀ᶠ q : Coordinates.ComplexCoordinates l × ℂ in 𝓝 (p, (0 : ℂ)),
      ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
        ComplexMatrix2.operatorNorm (twisted W B q b - 1) < r := by
    refine (Filter.eventually_all_finite hfin).2 fun b _ => ?_
    have hcont := (analyticAt_twisted hW (fun b => hp.1 b) B b).continuousAt
    have h0 : twisted W B (p, 0) b ∈ Metric.ball (1 : ComplexMatrix2) r := by
      rw [twisted_zero hp, mem_ball_iff_norm]
      exact hr b
    filter_upwards [hcont.eventually (Metric.isOpen_ball.mem_nhds h0)] with q hq
    exact mem_ball_iff_norm.1 hq
  filter_upwards [hconf, hnorm] with q h1 h2
  have h3 := expTwist_mem hA hL hj h1 hB q.2
  exact ⟨⟨fun b _ => h3.1 b, fun b _ => h3.2 b⟩, h2⟩
private theorem analyticAt_contourLogDrift (hS : YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hA : LeftChartFields.Claim)
    (hPd : DoubleBlockPolydisc.PolydiscsHold) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k)
    {W : Coordinates.ComplexCoordinates l → FullSpace.Edge L k j → ComplexMatrix2}
    {p : Coordinates.ComplexCoordinates l}
    (hW : ∀ b, AnalyticAt ℂ (fun z => W z b) p)
    (hc : ∀ᶠ z in 𝓝 p, W z ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hr : ∀ b, ComplexMatrix2.operatorNorm (W p b - 1) < polydiscRadius L)
    {B : FullSpace.Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j))
    {c : FullSpace.Edge L k (j + 1)} (hcp : c.IsPositivelyOriented)
    {y : FullSpace.Vertex L k (j + 1)} (hy : y = c.initial ∨ y = c.terminal) :
    AnalyticAt ℂ (fun z => contourLogDrift (W z) B y) p := by
  have hp := hc.self_of_nhds
  have hfin := cubeVertices_finite L (meshAt L k j) y
  have hP := eventually_twisted_mem_polydisc hA hPd hL hj hW hc hr hB hcp
  have hdet : ∀ b, Matrix.det (W p b) = 1 := fun b => hp.1 b
  have hs : AnalyticAt ℂ (fun z => ∑ x ∈ hfin.toFinset,
      logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X (W z)) y x)
        (complexContourMean L (W z) y x) B) p :=
    Finset.analyticAt_fun_sum _ fun x hx => by
      obtain ⟨h1, h2⟩ := analyticAt_complexContourMean hS hQ hL hj hcp hy
        (hfin.mem_toFinset.1 hx) (analyticAt_twisted hW hdet B) hP
      exact analyticAt_logDirectionalDeriv (Ψ := fun V => complexContourMean L V y x) hA hc h1 h2
  refine (analyticAt_const (v := PeriodicLattice.inverseFourthPowerWeight L)).fun_smul hs |>.congr
    (Eventually.of_forall fun z => ?_)
  show _ = contourLogDrift (W z) B y
  unfold FullSpace.contourLogDrift
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
end Step
end MeanStepAnalyticity
open MeanStepAnalyticity YangMills.Construction.Tower YangMills.Construction.Tower.FullSpace
  YangMills.Construction.Matrices in
theorem meanStepAnalytic_holds (hN : NormalizedMeanNearIdentity)
    (hS : YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hA : LeftChartFields.Claim)
    (hPd : DoubleBlockPolydisc.PolydiscsHold) : MeanStepAnalytic := by
  intro L hL
  obtain ⟨δ₁, hδ₁, H⟩ := hN L hL 1 one_pos
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  refine ⟨min δ₁ (polydiscRadius L), lt_min hδ₁ hρ, ?_⟩
  intro k j hj l W p hW hsm
  have hp := hsm.self_of_nhds
  have hconf : ∀ᶠ z in 𝓝 p, W z ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
    hsm.mono fun _ h => h.1
  have hdet : ∀ b, Matrix.det (W p b) = 1 := fun b => hp.1.1 b
  have hr : ∀ b, ComplexMatrix2.operatorNorm (W p b - 1) < polydiscRadius L := fun b =>
    (hp.2 b).trans_le (min_le_right _ _)
  have hnear := fun (c : FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented) =>
    H k j hj (W p) hp.1 (fun b => (hp.2 b).trans_le (min_le_left _ _)) c hc
  have hAvg : ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
      AnalyticAt ℂ (fun z => normalizedMean (W z) c) p := fun c hc =>
    analyticAt_normalizedMean hW hdet (hnear c hc).1 (hnear c hc).2.1
  have hUnit : ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
      IsUnit (Matrix.det (normalizedMean (W p) c)) := fun c hc => by
    have e : Matrix.det (normalizedMean (W p) c) = 1 := (hnear c hc).2.2.2.1
    rw [e]
    exact isUnit_one
  have hPol : ∀ c : FullSpace.Edge L k (j + 1), ∀ᶠ z in 𝓝 p,
      W z ∈ nearIdentityPolydisc L k j (polydiscRadius L) c := fun c =>
    hsm.mono fun z h => ⟨⟨fun b _ => h.1.1 b, fun b _ => h.1.2 b⟩,
      fun b _ => (h.2 b).trans_le (min_le_right _ _)⟩
  have hstep : ∀ B ∈ complexEdgeForms (meshAt L k j), ∀ c : FullSpace.Edge L k (j + 1),
      c.IsPositivelyOriented → AnalyticAt ℂ (fun z => meanCovariantStep (W z) B c) p := by
    intro B hB c hc
    have hmz : ∀ b, Matrix.det (twisted W B (p, 0) b) = 1 := fun b => by
      rw [twisted_zero hp.1]
      exact hdet b
    have hs : Matrix.det (contourMean (twisted W B (p, 0)) c) ∈ Complex.slitPlane := by
      rw [twisted_zero hp.1]
      exact (hnear c hc).1
    have hr0 : meanRadius (twisted W B (p, 0)) c ≠ 0 := by
      rw [twisted_zero hp.1]
      exact (hnear c hc).2.1
    have hlog := analyticAt_logDirectionalDeriv (Ψ := fun V => normalizedMean V c) hA hconf
      (analyticAt_normalizedMean (analyticAt_twisted hW hdet B) hmz hs hr0)
      (eventually_normalizedMean_mem (analyticAt_twisted hW hdet B) hmz hs hr0)
    have hh := analyticAt_contourLogDrift hS hQ hA hPd hL hj hW hconf hr hB hc (Or.inr rfl)
    have ht := analyticAt_contourLogDrift hS hQ hA hPd hL hj hW hconf hr hB hc (Or.inl rfl)
    have hAd : AnalyticAt ℂ (fun z => normalizedMean (W z) c * contourLogDrift (W z) B c.terminal *
        (normalizedMean (W z) c)⁻¹) p :=
      ((hAvg c hc).fun_mul hh).fun_mul (analyticAt_inv' (hAvg c hc) (hUnit c hc))
    refine (hlog.fun_add (hAd.fun_sub ht)).congr (Eventually.of_forall fun z => ?_)
    show _ = meanCovariantStep (W z) B c
    unfold meanCovariantStep FullSpace.covDiff
    simp only [Pi.add_apply, extendOddly_of_pos _ hc]
    rfl
  refine ⟨fun c => ?_, fun c hc => ?_, fun B hB c => ?_, fun y x hx => ?_⟩
  · by_cases hc : c.IsPositivelyOriented
    · refine (hAvg c hc).congr (Eventually.of_forall fun z => ?_)
      exact (if_pos hc : nextMeanIterate (W z) c = _).symm
    · have hr' := (isPos_or_opposite_isPos c).resolve_left hc
      refine (analyticAt_inv' (hAvg _ hr') (hUnit _ hr')).congr (Eventually.of_forall fun z => ?_)
      exact (if_neg hc : nextMeanIterate (W z) c = _).symm
  · exact (analyticAt_meanRadius hW hdet (hnear c hc).1).inv (hnear c hc).2.1
  · by_cases hc : c.IsPositivelyOriented
    · exact hstep B hB c hc
    · have hr' := (isPos_or_opposite_isPos c).resolve_left hc
      refine (hstep B hB _ hr').fun_neg.congr (Eventually.of_forall fun z => ?_)
      show -(meanCovariantStep (W z) B c.opposite) = meanCovariantStep (W z) B c
      unfold meanCovariantStep FullSpace.covDiff
      simp only [Pi.add_apply, extendOddly_of_not_pos _ hc, extendOddly_of_pos _ hr', neg_add]
  · let c : FullSpace.Edge L k (j + 1) := InfiniteLattice.Link.forwardFrom y 0
    have hc : c.IsPositivelyOriented := ⟨0, by simp [c, InfiniteLattice.Link.forwardFrom]⟩
    exact (analyticAt_complexContourMean hS hQ hL hj hc (Or.inl rfl) hx hW (hPol c)).1
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
