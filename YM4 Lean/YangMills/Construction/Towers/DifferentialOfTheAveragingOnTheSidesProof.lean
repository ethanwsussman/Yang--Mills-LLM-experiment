import YangMills.Construction.Lattice.BlockAverageLocality
import YangMills.Construction.Lattice.MeanLinearAverageIsTheAbsorbedAverage
import YangMills.Construction.Lattice.OneStepObjectsOfFirstOrderProof
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Towers.DifferentialOfTheAveragingOnTheSides
import YangMills.Construction.Towers.ReverseOfAStraightPathOfATower
import YangMills.Construction.Towers.TrivialConfigurationAtAStep
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.SmoothingDerivOnSides
open PeriodicLattice Matrices
variable {L m K n : ℕ}
private theorem realLine_hasDerivAt {f : ℂ → ComplexMatrix2} {D : ComplexMatrix2}
    (h : HasDerivAt f D 0) :
    HasDerivAt (fun t : ℝ => f (t : ℂ)) D 0 := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.hasDerivAt_ofReal_of_complex <;> assumption
private theorem eval_eq_of_antisymm {P : SymmetricBondSet L m K n} (f : LieBondField P)
    (A : BondAtLevel L m K n → ComplexMatrix2)
    (hf : ∀ e : PositiveBondsOf P, (f e : ComplexMatrix2) = A e.1)
    (hA : ∀ e : BondAtLevel L m K n, A e.opposite = -A e) {e : BondAtLevel L m K n}
    (he : e ∈ P.bonds) : (f.eval e : ComplexMatrix2) = A e := by
  by_cases hpos : e.IsPositivelyOriented
  · have hv : f.eval e = f ⟨e, he, hpos⟩ := LieBondField.eval_of_positive f ⟨e, he, hpos⟩
    rw [hv]
    exact hf ⟨e, he, hpos⟩
  · have hop : e.opposite ∈ P.bonds ∧ e.opposite.IsPositivelyOriented :=
      ⟨P.opposite_mem e he, PeriodicLattice.Bond.opposite_isPositivelyOriented hpos⟩
    have hnot : ¬(e ∈ P.bonds ∧ e.IsPositivelyOriented) := fun x => hpos x.2
    have hv : f.eval e = -f ⟨e.opposite, hop⟩ := by
      simp only [LieBondField.eval]
      rw [dif_neg hnot, dif_pos hop]
    rw [hv, Submodule.coe_neg, hf ⟨e.opposite, hop⟩]
    change -A e.opposite = A e
    rw [hA, neg_neg]
private theorem expBondField_eq_expTwist (c : BondAtLevel L m K (n + 1))
    (f : LieBondField (doubleBlockSymmetricSet c)) (A : BondAtLevel L m K n → ComplexMatrix2)
    (hf : ∀ e : PositiveBondsOf (doubleBlockSymmetricSet c), (f e : ComplexMatrix2) = A e.1)
    (hA : ∀ e : BondAtLevel L m K n, A e.opposite = -A e) {e : BondAtLevel L m K n}
    (he : e ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))) :
    expBondField c f e = expTwist A trivialGaugeField e := by
  have he' := (doubleBlockSymmetricSet c).opposite_mem e he
  unfold expBondField twistedConfig expTwist
  by_cases hpos : e.IsPositivelyOriented
  · simp only [if_pos hpos]
    rw [eval_eq_of_antisymm f A hf hA he]
  · simp only [if_neg hpos]
    rw [eval_eq_of_antisymm f A hf hA he']
private theorem expBondField_smul_eq {B : BondAtLevel L m K n → ComplexMatrix2}
    (hB : ∀ e : BondAtLevel L m K n, B e.opposite = -B e) (c : BondAtLevel L m K (n + 1))
    (f : LieBondField (doubleBlockSymmetricSet c))
    (hf : ∀ e : PositiveBondsOf (doubleBlockSymmetricSet c), (f e : ComplexMatrix2) = B e.1)
    (z : ℂ) {e : BondAtLevel L m K n}
    (he : e ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))) :
    expBondField c (z • f) e = expTwist (z • B) trivialGaugeField e := by
  refine expBondField_eq_expTwist c _ _ (fun e => ?_) (fun e => ?_) he
  · simp only [Pi.smul_apply, Submodule.coe_smul, hf]
  · simp only [Pi.smul_apply, hB, smul_neg]
private theorem contourHolonomies_congr {U V : BondAtLevel L m K n → ComplexMatrix2}
    {y : SiteAtLevel L m K (n + 1)} {x : SiteAtLevel L m K n}
    (h : ∀ σ, ∀ e ∈ orderedContour y x σ, U e = V e) :
    contourHolonomies U y x = contourHolonomies V y x := by
  funext σ
  unfold contourHolonomies pathHolonomy
  rw [List.map_congr_left (h σ)]
private theorem stepBondRadius_pos (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hr : IsStepRadius L (stepRadius L)) : 0 < stepBondRadius L := by
  have hω : 0 < Averaging.smoothingRadius L :=
    (Averaging.isSmoothingRadius_smoothingRadius hL.1 hL.2).1
  have hL' : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have hκ : 0 < Averaging.SingleStep.loopVariableConstant L := by
    unfold Averaging.SingleStep.loopVariableConstant Averaging.SingleStep.loopAngleConstant
    have h3 : 0 < 3 * (L : ℝ) * ((L : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    have h4 : 0 ≤ 2 * (Real.pi / Real.sqrt 3 * ((L : ℝ) - 1) ^ 2) := by positivity
    linarith
  exact lt_min hr.pos (lt_min (by positivity) (by positivity))
private theorem supOperatorNorm_smul {ι : Type} (z : ℂ) (f : ι → ↥ComplexMatrix2.traceless) :
    supOperatorNorm (z • f) = ‖z‖ * supOperatorNorm f := by apply _root_.YangMills.Construction.PeriodicLattice.FirstOrderSteps.supOperatorNorm_smul <;> assumption
private theorem trivialGaugeField_isGaugeField (S : Set (BondAtLevel L m K n)) :
    IsGaugeField compactGaugeGroup S (trivialGaugeField : BondAtLevel L m K n → ComplexMatrix2) :=
  ⟨fun _ _ => ComplexMatrix2.specialUnitary.one_mem, fun _ _ => by simp [trivialGaugeField]⟩
private theorem eventually_line_facts (hCov : stepCovarianceDomainsStatement)
    (hGrow : StepCurvatureGrowth) (hSch : AveragingSchemeProperties)
    (hNear : SmoothingNearTrivialField)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    {B : BondAtLevel L m K n → ComplexMatrix2} (hB : B ∈ edgeFormSpace L m K n)
    (c : BondAtLevel L m K (n + 1)) (hc : c.IsPositivelyOriented)
    (f : LieBondField (doubleBlockSymmetricSet c))
    (hf : ∀ e : PositiveBondsOf (doubleBlockSymmetricSet c), (f e : ComplexMatrix2) = B e.1) :
    ∀ᶠ t : ℝ in 𝓝 0,
      IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) (expBondField c ((t : ℂ) • f)) ∧
        CentredSchemeAgreesWithAverage (expBondField c ((t : ℂ) • f)) c := by
  obtain ⟨-, hrad, hball⟩ := hCov L hL
  have hr0 := stepBondRadius_pos hL hrad
  have hbound : 0 < stepCurvatureBound L :=
    lt_of_lt_of_le (hGrow L hL).1.radius_pos (hGrow L hL).1.radius_le
  have hsize : doubleBlockCurvature (trivialGaugeField : BondAtLevel L m K n → ComplexMatrix2) c ≤
      stepCurvatureBound L := by
    refine Real.iSup_le (fun p => ?_) hbound.le
    have h1 : plaquetteHolonomy (trivialGaugeField : BondAtLevel L m K n → ComplexMatrix2) p.1 = 1 := by
      refine List.prod_eq_one fun x hx => ?_
      obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
      rfl
    rw [h1, sub_self]
    simpa [ComplexMatrix2.operatorNorm] using hbound.le
  obtain ⟨-, -, hfacts⟩ := hball m K n hm hn .centred c hc trivialGaugeField
    (trivialGaugeField_isGaugeField _) hsize
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ‖(t : ℂ)‖ * supOperatorNorm f < stepBondRadius L := by
    have h : Tendsto (fun t : ℝ => ‖(t : ℂ)‖ * supOperatorNorm f) (𝓝 0)
        (𝓝 (‖((0 : ℝ) : ℂ)‖ * supOperatorNorm f)) :=
      ((Complex.continuous_ofReal.norm).tendsto 0).mul_const _
    have h0 : ‖((0 : ℝ) : ℂ)‖ * supOperatorNorm f < stepBondRadius L := by simpa using hr0
    exact h.eventually (gt_mem_nhds h0)
  filter_upwards [hsmall] with t ht
  have hcomp : IsCompactValued ((t : ℂ) • f) := by
    intro e
    rw [Pi.smul_apply, Submodule.coe_smul, hf e, Complex.coe_smul]
    exact ComplexMatrix2.hermitianTraceless.smul_mem t (hB.1 e.1 e.2.2)
  have hform : (t : ℂ) • B ∈ edgeFormSpace L m K n := by
    have h := (edgeFormSpace L m K n).smul_mem t hB
    have heq : (t : ℂ) • B = t • B := by
      funext e
      exact Complex.coe_smul t (B e)
    rwa [heq]
  have hV := (hNear L m K hL hm (by omega)).2 n hn.le ((t : ℂ) • B) hform
    trivialGaugeField (trivialGaugeField_isGaugeField _)
  have hagree : ∀ e ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
      expBondField c ((t : ℂ) • f) e = expTwist ((t : ℂ) • B) trivialGaugeField e :=
    fun e he => expBondField_smul_eq hB.2 c f hf _ he
  have hfield : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c)
      (expBondField c ((t : ℂ) • f)) := by
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · rw [hagree e he]
      exact hV.1 e (mem_univ e)
    · rw [hagree e he, hagree _ ((doubleBlockSymmetricSet c).opposite_mem e he)]
      exact hV.2 e (mem_univ e)
  have hp := (hfacts ((t : ℂ) • f) (by rw [supOperatorNorm_smul]; exact ht) hcomp).plaquettes
  obtain ⟨-, -, -, -, hmap, -⟩ := (hSch L hL m K n hm hn .centred).2.1 c hc
  exact ⟨hfield, hmap _ hfield hp⟩
private theorem logDirectionalDeriv_at_positive (hTriv : TrivialFieldAtStep)
    (hCov : stepCovarianceDomainsStatement)
    (hGrow : StepCurvatureGrowth) (hSch : AveragingSchemeProperties)
    (hNear : SmoothingNearTrivialField)
    (hLin : CentredSchemeLinearAverageEq)
    (hReads : BlockAverageDependsOnDoubleBlock)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    {B : BondAtLevel L m K n → ComplexMatrix2} (hB : B ∈ edgeFormSpace L m K n)
    (hC : IsBondForm complexLieAlgebra B)
    (c : BondAtLevel L m K (n + 1)) (hc : c.IsPositivelyOriented) :
    logDirectionalDeriv ℝ
        (fun X => smoothingStep L m K n (expTwist X (trivialField L m K n)) c)
        (smoothingStep L m K n (trivialField L m K n) c) B =
      linearSmoothing L m K n B c := by
  let f : LieBondField (doubleBlockSymmetricSet c) := fun e => ⟨B e.1, hC.1 e.1 e.2.2⟩
  have hf : ∀ e : PositiveBondsOf (doubleBlockSymmetricSet c), (f e : ComplexMatrix2) = B e.1 :=
    fun _ => rfl
  have h1 : smoothingStep L m K n (trivialField L m K n) c = 1 := by
    rw [(hTriv L m K n hL hm hn).2.1]
  have hd := realLine_hasDerivAt ((hGrow L hL).2 m K n hm hn .centred c hc f).1
  have hlin := hLin L hL m K n hm hn c hc f B hC hf
  have hev : (fun t : ℝ => ComplexMatrix2.logSeries (smoothingStep L m K n
        (expTwist (algebraMap ℝ ℂ t • B) (trivialField L m K n)) c * (1 : ComplexMatrix2)⁻¹)) =ᶠ[𝓝 0]
      fun t : ℝ => Complex.I • blockAverageLog .centred c ((t : ℂ) • f) := by
    filter_upwards [eventually_line_facts hCov hGrow hSch hNear hL hm hn hB c hc f hf] with t ht
    have heq : smoothingStep L m K n
        (expTwist (algebraMap ℝ ℂ t • B) (trivialField L m K n)) c =
        schemeBlockAverage .centred (expBondField c ((t : ℂ) • f)) c := by
      rw [ht.2.average_eq]
      exact hReads L m K n hL hm hn _ c _ _
        fun e he => (expBondField_smul_eq hB.2 c f hf (t : ℂ) he).symm
    rw [heq, inv_one, mul_one, blockAverageLog, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero,
      one_smul]
  have h3 := (hd.const_smul Complex.I).congr_of_eventuallyEq hev
  unfold logDirectionalDeriv
  rw [h1, h3.deriv, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul, hlin]
  rfl
private theorem deriv_contour_eq (hTriv : TrivialFieldAtStep)
    (hCov : stepCovarianceDomainsStatement)
    (hGrow : StepCurvatureGrowth) (hSch : AveragingSchemeProperties)
    (hNear : SmoothingNearTrivialField)
    (hChart : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    {B : BondAtLevel L m K n → ComplexMatrix2} (hB : B ∈ edgeFormSpace L m K n)
    (hC : IsBondForm complexLieAlgebra B)
    (y : SiteAtLevel L m K (n + 1)) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) y) :
    Complex.I⁻¹ • deriv (fun t : ℝ => ComplexMatrix2.logSeries (meanContourHolonomy
        (expTwist ((t : ℂ) • B) (trivialField L m K n)) y x)) 0 =
      contourFormAverage B y x := by
  let c : BondAtLevel L m K (n + 1) := PeriodicLattice.Bond.forwardFrom y 0
  have hc : c.IsPositivelyOriented := ⟨0, by simp [c, PeriodicLattice.Bond.forwardFrom]⟩
  let f : LieBondField (doubleBlockSymmetricSet c) := fun e => ⟨B e.1, hC.1 e.1 e.2.2⟩
  have hf : ∀ e : PositiveBondsOf (doubleBlockSymmetricSet c), (f e : ComplexMatrix2) = B e.1 :=
    fun _ => rfl
  have hy : y ∈ bondEndpoints c := Or.inl rfl
  have hpaths := ((hSch L hL m K n hm hn .centred).1 y x hx).1.contour_within
  have hin : ∀ σ, ∀ e ∈ orderedContour y x σ,
      e ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := fun σ e he =>
    ⟨Or.inl ((hpaths σ).2 e he).1, Or.inl ((hpaths σ).2 e he).2⟩
  have hd := realLine_hasDerivAt
    (((hGrow L hL).2 m K n hm hn .centred c hc f).2.2 y hy x hx)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_line_facts hCov hGrow hSch hNear hL hm hn hB c hc f hf)
  have heq : ∀ t ∈ Metric.ball (0 : ℝ) δ,
      contourHolonomy .centred (expBondField c ((t : ℂ) • f)) y x =
        meanContourHolonomy (expTwist ((t : ℂ) • B) (trivialField L m K n)) y x := by
    intro t ht
    rw [(hball t ht).2.contour_eq y (Or.inl rfl) x hx]
    unfold meanContourHolonomy
    rw [contourHolonomies_congr fun σ e he => expBondField_smul_eq hB.2 c f hf (t : ℂ) (hin σ e he)]
    rfl
  have hzero : expTwist (((0 : ℝ) : ℂ) • B) (trivialField L m K n) =
      trivialField L m K n := by
    funext e
    unfold expTwist
    split_ifs <;> simp [ComplexMatrix2.matExp]
  have hW0 : contourHolonomy .centred (expBondField c (((0 : ℝ) : ℂ) • f)) y x = 1 := by
    rw [heq 0 (Metric.mem_ball_self hδ), hzero]
    exact (hTriv L m K n hL hm hn).1 y x hx
  obtain ⟨-, -, -, hvals, -, -⟩ := (hSch L hL m K n hm hn .centred).2.1 c hc
  have hmem : MapsTo
      (fun t : ℝ => contourHolonomy .centred (expBondField c ((t : ℂ) • f)) y x)
      (Metric.ball (0 : ℝ) δ) compactGaugeGroup := fun t ht =>
    (hvals _ (hball t ht).2.mem_domain (hball t ht).1).contour_mem y (Or.inl rfl) x hx
  have hI : IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) δ) :=
    ⟨Metric.isOpen_ball, by rw [Real.ball_eq_Ioo]; exact Set.ordConnected_Ioo,
      Metric.mem_ball_self hδ⟩
  obtain ⟨-, -, hder, -⟩ := (hChart.1 _ hI).1 _ hmem hd.differentiableAt
  simp only [hW0, inv_one, mul_one] at hder
  have hev : (fun t : ℝ => ComplexMatrix2.logSeries (meanContourHolonomy
        (expTwist ((t : ℂ) • B) (trivialField L m K n)) y x)) =ᶠ[𝓝 0]
      fun t : ℝ => ComplexMatrix2.logSeries
        (contourHolonomy .centred (expBondField c ((t : ℂ) • f)) y x) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    rw [heq t ht]
  rw [hev.deriv_eq, hder, hd.deriv, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  change contourFormAverage (matrixValues f) y x = contourFormAverage B y x
  unfold contourFormAverage
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  unfold bondFormSumAlong
  have hmap : ∀ e ∈ orderedContour y x σ, matrixValues f e = B e :=
    fun e he => eval_eq_of_antisymm f B hf hB.2 (hin σ e he)
  rw [List.map_congr_left hmap]
theorem smoothingDerivAtOneOnAllSides_holds (hAn : SmoothingAnalyticCovariantOnSides)
    (hDiff : AnalyticMapDifferentiableStatement)
    (hTriv : TrivialFieldAtStep)
    (hNear : SmoothingNearTrivialField)
    (hCov : stepCovarianceDomainsStatement)
    (hGrow : StepCurvatureGrowth)
    (hLin : CentredSchemeLinearAverageEq)
    (hSch : AveragingSchemeProperties)
    (hReads : BlockAverageDependsOnDoubleBlock)
    (hRev : AxisPathReversal.MainStatement)
    (hChart : LeftChartFields.Claim) : SmoothingDerivAtOneOnAllSides := by
  intro L hL m K n hm hn
  obtain ⟨hforms, hrev⟩ := (hRev L hL K).1 m hm
  have hC : ∀ B ∈ edgeFormSpace L m K n, IsBondForm complexLieAlgebra B :=
    (hforms n hn.le).1
  refine ⟨?_, fun B hB y x hx =>
    deriv_contour_eq hTriv hCov hGrow hSch hNear hChart hL hm hn hB (hC B hB) y hx⟩
  obtain ⟨U, hU, hanal, -⟩ := (hAn L hL m K n hm hn).analytic
  refine ⟨U, hU, hDiff L m K n (n + 1) hL hm hn.le hn U _ hanal, fun B hB => ?_⟩
  have hpos := fun c hc =>
    logDirectionalDeriv_at_positive hTriv hCov hGrow hSch hNear hLin hReads hL hm hn
      hB (hC B hB) c hc
  funext e
  unfold leftDifferential extendOddly
  by_cases hp : e.IsPositivelyOriented
  · simp only [if_pos hp]
    exact hpos e hp
  · simp only [if_neg hp]
    rw [hpos e.opposite (PeriodicLattice.Bond.opposite_isPositivelyOriented hp),
      (hrev n hn e B (hC B hB)).2, neg_neg]
end YangMills.Construction.Tower.SmoothingDerivOnSides
