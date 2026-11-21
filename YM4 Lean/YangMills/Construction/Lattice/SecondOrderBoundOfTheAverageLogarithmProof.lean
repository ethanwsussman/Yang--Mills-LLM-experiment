import YangMills.Construction.Lattice.AveragesAndContourVariablesOfTheIdentityConfiguration
import YangMills.Construction.Lattice.FirstDerivativeOfTheAverageLogarithm
import YangMills.Construction.Lattice.OneStepObjectsOfFirstOrderProof
import YangMills.Construction.Lattice.SecondOrderBoundOfTheAverageLogarithm
import YangMills.Construction.Matrices.ExpLogEstimates
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices YangMills.Construction.Coordinates
private theorem toTraceless_coe_self (v : ↥ComplexMatrix2.traceless) :
    toTraceless (v : ComplexMatrix2) = v := by apply _root_.YangMills.Construction.PeriodicLattice.FirstOrderSteps.tracelessPart_coe <;> assumption
section ComplexLine
variable {ι : Type}
private theorem supOperatorNorm_smul (z : ℂ) (x : ι → ↥ComplexMatrix2.traceless) :
    supOperatorNorm (z • x) = ‖z‖ * supOperatorNorm x := by apply _root_.YangMills.Construction.PeriodicLattice.FirstOrderSteps.supOperatorNorm_smul <;> assumption
private def matrixEquivCLE : ComplexMatrix2 ≃L[ℂ] ComplexCoordinates 4 :=
  LinearEquiv.toContinuousLinearEquiv
    { ComplexCoordinates.matrixEquiv with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
variable [Fintype ι]
private theorem differentiableAt_along_line
    (hPS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {ρ : ℝ}
    {Ψ : (ι → ↥ComplexMatrix2.traceless) → ComplexMatrix2}
    (hΨ : GroupLieProduct.IsHolomorphicOnTraceless e ComplexCoordinates.matrixEquiv
      (GroupLieProduct.supBall (ι ⊕ ι) ρ) fun X => Ψ (pairFirst X))
    (x : ι → ↥ComplexMatrix2.traceless) (z : ℂ) (hz : supOperatorNorm (z • x) < ρ) :
    DifferentiableAt ℂ (fun t : ℂ => Ψ (t • x)) z := by
  let y : ι ⊕ ι → ↥ComplexMatrix2.traceless := Sum.elim x 0
  let σ := Fintype.equivFin (ι ⊕ ι)
  have hσ := hΨ.2 σ
  let w : ComplexCoordinates (Fintype.card (ι ⊕ ι) * 3) := fun k =>
    e.repr (y (σ.symm (finProdFinEquiv.symm k).1)) (finProdFinEquiv.symm k).2
  have htup : ∀ t : ℂ, GroupLieProduct.tupleOfCoords e σ (t • w) =
      fun i => (((t • y) i : ↥ComplexMatrix2.traceless) : ComplexMatrix2) := by
    intro t
    funext i
    have hcoord : ∀ j : Fin 3, (t • w) (finProdFinEquiv (σ i, j)) = t * e.repr (y i) j := by
      intro j
      show t * e.repr (y (σ.symm (finProdFinEquiv.symm (finProdFinEquiv (σ i, j))).1))
        (finProdFinEquiv.symm (finProdFinEquiv (σ i, j))).2 = _
      rw [Equiv.symm_apply_apply]
      simp
    have hsum := congrArg (fun v : ↥ComplexMatrix2.traceless => (v : ComplexMatrix2))
      (e.sum_repr (y i))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    simp only [GroupLieProduct.tupleOfCoords, ComplexCoordinates.tracelessTuple, hcoord]
    show _ = t • (y i : ComplexMatrix2)
    rw [← hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul]
  have hval : ∀ t : ℂ, (fun X : ι ⊕ ι → ComplexMatrix2 => Ψ (pairFirst X))
      (GroupLieProduct.tupleOfCoords e σ (t • w)) = Ψ (t • x) := by
    intro t
    rw [htup]
    show Ψ (fun b => toTraceless (((t • y) (.inl b) : ↥ComplexMatrix2.traceless) :
      ComplexMatrix2)) = _
    simp only [toTraceless_coe_self]
    rfl
  have hmem : z • w ∈ GroupLieProduct.tupleOfCoords e σ ⁻¹' GroupLieProduct.supBall (ι ⊕ ι) ρ := by
    show GroupLieProduct.tupleOfCoords e σ (z • w) ∈ GroupLieProduct.supBall (ι ⊕ ι) ρ
    rw [htup]
    refine ⟨fun i => ((z • y) i).2, ?_⟩
    unfold GroupLieProduct.supNorm
    refine lt_of_le_of_lt (Real.iSup_le (fun i => ?_)
      (Real.iSup_nonneg fun _ => norm_nonneg _)) hz
    rcases i with b | b
    · exact le_ciSup (f := fun i => ComplexMatrix2.operatorNorm
        (((z • x) i : ↥ComplexMatrix2.traceless) : ComplexMatrix2))
        (Set.finite_range _).bddAbove b
    · have hzero : (((z • y) (.inr b) : ↥ComplexMatrix2.traceless) : ComplexMatrix2) = 0 := by
        simp [y]
      show ‖(((z • y) (.inr b) : ↥ComplexMatrix2.traceless) : ComplexMatrix2)‖ ≤ _
      rw [hzero, norm_zero]
      exact Real.iSup_nonneg fun _ => norm_nonneg _
  obtain ⟨Dv, hDv⟩ := ((hPS.1 _ _ hσ.1).1 4 _ hσ).2.2.1 (z • w) hmem
  have hdiff := (hasFDerivAt_of_restrictScalars ℝ hDv rfl).differentiableAt
  have hlin : DifferentiableAt ℂ (fun t : ℂ => t • w) z :=
    differentiableAt_id.smul_const w
  have hcomp := matrixEquivCLE.symm.differentiableAt.comp z (hdiff.comp z hlin)
  have hfun : (⇑matrixEquivCLE.symm ∘
      ((ComplexCoordinates.matrixEquiv ∘
        (fun X : ι ⊕ ι → ComplexMatrix2 => Ψ (pairFirst X)) ∘
        GroupLieProduct.tupleOfCoords e σ) ∘ fun t : ℂ => t • w)) =
      fun t : ℂ => Ψ (t • x) := by
    funext t
    exact (ComplexCoordinates.matrixEquiv.symm_apply_apply _).trans (hval t)
  rw [hfun] at hcomp
  exact hcomp
end ComplexLine
private theorem logSeries_one_eq_zero : ComplexMatrix2.logSeries 1 = 0 := by
  simp [ComplexMatrix2.logSeries]
variable {L m K n : ℕ}
private theorem eval_zero_field {P : SymmetricBondSet L m K n} (b : BondAtLevel L m K n) :
    ((LieBondField.eval (0 : LieBondField P) b : ↥ComplexMatrix2.traceless) :
      ComplexMatrix2) = 0 := by
  unfold LieBondField.eval
  split_ifs <;> simp
private theorem expBondField_zero_eq (c : BondAtLevel L m K (n + 1)) :
    expBondField c (0 : LieBondField (doubleBlockSymmetricSet c)) = trivialGaugeField := by
  funext b
  have hone : ComplexMatrix2.matExp 0 = 1 := NormedSpace.exp_zero
  simp only [expBondField, twistedConfig, expTwist, eval_zero_field,
    trivialGaugeField, smul_zero, mul_one, hone, inv_one, ite_self]
private theorem blockAverageLog_zero_eq
    (hT : TrivialFieldAverages.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (S : AveragingScheme) (c : BondAtLevel L m K (n + 1)) :
    blockAverageLog S c (0 : LieBondField (doubleBlockSymmetricSet c)) = 0 := by
  have htriv : iteratedAverage S n (trivialGaugeField : BondAtLevel L m K 0 → ComplexMatrix2) =
      trivialGaugeField :=
    funext fun b => (((hT L hL m K hm S).1 n hn.le) b).2
  have hone : schemeBlockAverage S (iteratedAverage S n
      (trivialGaugeField : BondAtLevel L m K 0 → ComplexMatrix2)) c = 1 :=
    (((hT L hL m K hm S).1 (n + 1) hn) c).2
  rw [htriv] at hone
  unfold blockAverageLog
  rw [expBondField_zero_eq, hone, logSeries_one_eq_zero, smul_zero]
theorem blockAverageLog_secondOrderBound (hD : stepCovarianceDomainsStatement)
    (hF : HasDerivBlockAverageLogAtZero)
    (hT : TrivialFieldAverages.Statement)
    (hPS : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ComplexMatrix2.RestatedElementaryInequalitiesStatement)
    (hX : ComplexMatrix2.ExpLogEstimates) : BlockAverageLogSecondOrderBound := by
  intro L hL m K n hm hn S c hc x hx
  have hr : IsStepRadius L (stepRadius L) := (hD L hL).2.1
  set r := stepRadius L with hrdef
  have hr0 : 0 < r := hr.pos
  have hfinS : Finite (SiteAtLevel L m K n) :=
    SeparatedSequences.BaseParameters.site_finite (lt_of_lt_of_le (by norm_num) hL.2) m _
  have hfinB : Finite (BondAtLevel L m K n) := by
    refine Finite.of_injective (fun b : BondAtLevel L m K n => (b.source, b.target)) ?_
    intro b b' hbb
    exact Bond.ext (congrArg Prod.fst hbb) (congrArg Prod.snd hbb)
  let _ : Fintype (PositiveBondsOf (doubleBlockSymmetricSet c)) := Fintype.ofFinite _
  have hzero : supOperatorNorm (0 : LieBondField (doubleBlockSymmetricSet c)) < r := by
    have : supOperatorNorm (0 : LieBondField (doubleBlockSymmetricSet c)) = 0 := by
      simp [supOperatorNorm]
    rw [this]
    exact hr0
  have hball : ∀ b : LieBondField (doubleBlockSymmetricSet c), supOperatorNorm b < r →
      IsSchemeAverageDefined S (expBondField c b) c ∧
        ComplexMatrix2.operatorNorm (schemeBlockAverage S (expBondField c b) c - 1) < 1 ∧
          ComplexMatrix2.operatorNorm (blockAverageLog S c b) ≤ 1 :=
    fun b hb => (hr.bounds m K n hm hn S c hc b 0 hb hzero).average
  have hsup0 : 0 ≤ supOperatorNorm x := Real.iSup_nonneg fun _ => norm_nonneg _
  have hlt : supOperatorNorm x < r := by linarith
  have hexp : ComplexMatrix2.matExp (Complex.I • blockAverageLog S c x) =
      schemeBlockAverage S (expBondField c x) c := by
    have h1 := (hX.2.2.2.1 (schemeBlockAverage S (expBondField c x) c - 1)
      (hball x hlt).2.1).2.2.2.2
    rw [add_sub_cancel] at h1
    unfold blockAverageLog
    rw [smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
    exact h1
  have hΦ0 := blockAverageLog_zero_eq hT hL hm hn S c
  have hhol := ((hr.holomorphic m K n hm hn S c hc) inferInstance
    OneLoop.pauliBasis).2.2.2
  have hderiv := hF L hL m K n hm hn S c hc x
  refine ⟨hexp, ?_⟩
  rcases hsup0.eq_or_lt with hs | hs
  · have hx0 : x = 0 := by
      funext i
      have hle : ComplexMatrix2.operatorNorm (x i : ComplexMatrix2) ≤ supOperatorNorm x :=
        le_ciSup (f := fun i => ComplexMatrix2.operatorNorm (x i : ComplexMatrix2))
          (Set.finite_range _).bddAbove i
      rw [← hs] at hle
      exact Subtype.ext (norm_le_zero_iff.mp hle)
    have hΦ : blockAverageLog S c x = 0 := by rw [hx0]; exact hΦ0
    have hlinear : linearSchemeAverage S (LieBondField.matrixValues x) c = 0 := by
      have hconst : (fun t : ℂ => blockAverageLog S c (t • x)) = fun _ => 0 := by
        funext t
        rw [hx0, smul_zero]
        exact hΦ0
      rw [hconst] at hderiv
      exact hderiv.unique (hasDerivAt_const _ _)
    rw [hΦ, hlinear, ← hs]
    simp [ComplexMatrix2.operatorNorm]
  · set R := r / supOperatorNorm x with hRdef
    have hR4 : 4 ≤ R := by
      rw [hRdef, le_div_iff₀ hs]
      linarith
    have hinside : ∀ z ∈ Metric.ball (0 : ℂ) R, supOperatorNorm (z • x) < r := by
      intro z hz
      rw [supOperatorNorm_smul]
      have hz' : ‖z‖ < R := by simpa using hz
      exact (lt_div_iff₀ hs).1 hz'
    have hdiffOn : DifferentiableOn ℂ (fun t : ℂ => blockAverageLog S c (t • x))
        (Metric.ball 0 R) := fun z hz =>
      (differentiableAt_along_line hPS _ hhol x z (hinside z hz)).differentiableWithinAt
    have hbound : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖blockAverageLog S c (z • x)‖ ≤ 1 :=
      fun z hz => (hball _ (hinside z hz)).2.2
    have hone : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
      simp only [Metric.mem_ball, dist_zero_right, norm_one]
      linarith
    have hat0 : blockAverageLog S c ((0 : ℂ) • x) = 0 := by
      rw [zero_smul]
      exact hΦ0
    obtain ⟨-, hTaylor, hSchwarz⟩ := hE.2.2.2.2.2.1 ℂ ComplexMatrix2 R 1 _ hdiffOn hbound 1 hone
    have hSchwarz' := hSchwarz hat0
    have hfd : fderiv ℂ (fun t : ℂ => blockAverageLog S c (t • x)) 0 1 =
        linearSchemeAverage S (LieBondField.matrixValues x) c := by
      rw [hderiv.hasFDerivAt.fderiv]
      simp
    rw [hat0, hfd] at hTaylor
    simp only [one_smul, norm_one, mul_one, one_pow, sub_zero] at hTaylor hSchwarz'
    have e1 : 1 / R = supOperatorNorm x / r := by
      rw [hRdef]
      field_simp
    have e2 : 2 * supOperatorNorm x ^ 2 / r ^ 2 = 2 / R ^ 2 := by
      rw [hRdef]
      field_simp
    refine ⟨?_, ?_⟩
    · rw [← e1]
      exact hSchwarz'
    · rw [e2]
      refine hTaylor.trans ?_
      rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith
end YangMills.Construction.PeriodicLattice
