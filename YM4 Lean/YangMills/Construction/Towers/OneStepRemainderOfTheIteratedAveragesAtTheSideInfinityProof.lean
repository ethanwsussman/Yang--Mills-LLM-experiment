import YangMills.Construction.Matrices.MatrixLogarithms
import YangMills.Construction.Matrices.SecondOrderSupBallBound
import YangMills.Construction.Towers.CovariantAveragesAsDifferentialsProof
import YangMills.Construction.Towers.IteratedAveragesBoundsAtTheSideInfinityProof
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct
open scoped Topology ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder
section Matrices
theorem logSeries_eq_logOfSeries (X : ComplexMatrix2) :
    ComplexMatrix2.logSeries X = MatrixLog.logOfSeries (N := 2) X := by
  unfold ComplexMatrix2.logSeries MatrixLog.logOfSeries
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  unfold MatrixLog.logTerm
  rcases Nat.even_or_odd (n + 1) with h | h
  · have e₁ : (1 - X) ^ (n + 1) = (X - 1) ^ (n + 1) := by
      rw [← neg_sub X 1, h.neg_pow]
    have e₂ : (-1 : ℂ) ^ (n + 2) = -1 := by
      rw [show n + 2 = (n + 1) + 1 from rfl, pow_succ, h.neg_one_pow]
      ring
    rw [e₁, e₂, neg_div, one_div, neg_smul]
  · have e₁ : (1 - X) ^ (n + 1) = -(X - 1) ^ (n + 1) := by
      rw [← neg_sub X 1, h.neg_pow]
    have e₂ : (-1 : ℂ) ^ (n + 2) = 1 := by
      rw [show n + 2 = (n + 1) + 1 from rfl, pow_succ, h.neg_one_pow]
      ring
    rw [e₁, e₂, one_div, smul_neg, neg_neg]
theorem logSeries_differentiableAt (hS : MatrixLog.MatrixLogarithmsSeriesAndSpectral)
    {X : ComplexMatrix2} (hX : ComplexMatrix2.operatorNorm (X - 1) < 1) :
    DifferentiableAt ℂ ComplexMatrix2.logSeries X := by
  have h := ((hS 2).2.2.2.1 X hX).differentiableAt
  have e : ComplexMatrix2.logSeries = MatrixLog.logOfSeries (N := 2) :=
    funext logSeries_eq_logOfSeries
  rw [e]
  exact h
theorem matExp_differentiableAt (hS : MatrixLog.MatrixLogarithmsSeriesAndSpectral)
    (X : ComplexMatrix2) : DifferentiableAt ℂ ComplexMatrix2.matExp X :=
  ((hS 2).2.2.1 X (mem_univ _)).differentiableAt
theorem real_exp_sub_one_lt_two_mul {u : ℝ} (h₀ : 0 < u) (h₁ : u ≤ 1 / 2) :
    Real.exp u - 1 < 2 * u := by
  have h := Real.exp_bound_div_one_sub_of_interval' h₀ (by linarith)
  have h₂ : 1 / (1 - u) ≤ 1 + 2 * u := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith
theorem operatorNorm_I_smul (X : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (Complex.I • X) = ComplexMatrix2.operatorNorm X := by
  simp [ComplexMatrix2.operatorNorm, norm_smul]
theorem operatorNorm_I_inv_smul (X : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (Complex.I⁻¹ • X) = ComplexMatrix2.operatorNorm X := by
  simp [ComplexMatrix2.operatorNorm, norm_smul]
theorem matrixEquiv_isLinearMap : IsLinearMap ℂ Coordinates.ComplexCoordinates.matrixEquiv := by apply _root_.YangMills.Construction.Tower.AsDifferentials.matrixEquiv_isLinearMap <;> assumption
end Matrices
section Tuples
variable {σ : Type}
theorem mem_tracelessPi_iff {A : σ → ComplexMatrix2} :
    A ∈ tracelessPi σ ↔ ∀ s, A s ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.AsDifferentials.mem_tracelessPi_iff <;> assumption
theorem tupleSup_nonneg (A : σ → ComplexMatrix2) : 0 ≤ supNorm A :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem le_tupleSup [Finite σ] (A : σ → ComplexMatrix2) (s : σ) :
    ComplexMatrix2.operatorNorm (A s) ≤ supNorm A :=
  le_ciSup (f := fun i => ComplexMatrix2.operatorNorm (A i)) (Set.finite_range _).bddAbove s
theorem tupleSup_eq_norm [Fintype σ] (A : σ → ComplexMatrix2) : supNorm A = ‖A‖ := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.TracelessDifferentiable.supNorm_eq_norm <;> assumption
theorem isSupOpen_supBall [Fintype σ] (u : ℝ) : IsSupOpen (supBall σ u) := by
  refine ⟨fun A hA => hA.1, fun A hA => ⟨u - supNorm A, sub_pos.2 hA.2, fun B hB h => ⟨hB, ?_⟩⟩⟩
  rw [tupleSup_eq_norm] at h ⊢
  rw [tupleSup_eq_norm] at h
  have h₁ : ‖B‖ ≤ ‖B - A‖ + ‖A‖ := by simpa using norm_add_le (B - A) A
  have h₂ := hA.2
  rw [tupleSup_eq_norm] at h₂
  linarith
end Tuples
section Links
variable {a : ℝ}
theorem isPositivelyOriented_or_opposite (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (ha : 0 < a) {b : InfiniteLattice.Link a}
    (h : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem opposite_opposite (b : InfiniteLattice.Link a) : b.opposite.opposite = b := rfl
def extendByZero (P : Set (InfiniteLattice.Link a)) (v : PositiveEdgeOf P → ComplexMatrix2)
    (b : InfiniteLattice.Link a) : ComplexMatrix2 :=
  open Classical in
  if h : b ∈ P ∧ b.IsPositivelyOriented then v ⟨b, h⟩
  else if h' : b.opposite ∈ P ∧ b.opposite.IsPositivelyOriented then -v ⟨b.opposite, h'⟩ else 0
variable {P : Set (InfiniteLattice.Link a)} {v w : PositiveEdgeOf P → ComplexMatrix2}
theorem extendByZero_of_positive {b : InfiniteLattice.Link a} (h : b ∈ P)
    (hb : b.IsPositivelyOriented) : _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero P v b = v ⟨b, h, hb⟩ := by
  simp [_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero, h, hb]
theorem extendByZero_opposite (ha : 0 < a) (b : InfiniteLattice.Link a) :
    _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero P v b.opposite = -_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero P v b := by
  classical
  rcases isPositivelyOriented_or_opposite b with hb | hb
  · have hb' := not_isPositivelyOriented_opposite ha hb
    by_cases hP : b ∈ P
    · simp [extendByZero, hb, hb', hP, opposite_opposite]
    · simp [extendByZero, hb, hb', hP, opposite_opposite]
  · have hb' : ¬ b.IsPositivelyOriented := fun h => not_isPositivelyOriented_opposite ha h hb
    by_cases hP : b.opposite ∈ P
    · simp [_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero, hb, hb', hP]
    · simp [extendByZero, hb, hb', hP, opposite_opposite]
theorem extendByZero_add : _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero P (v + w) = _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero P v + _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero P w := by
  funext b
  simp only [_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero, Pi.add_apply]
  split_ifs
  · rfl
  · abel
  · simp
theorem extendByZero_smul (z : ℂ) : _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero P (z • v) = z • _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero P v := by
  funext b
  simp only [_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero, Pi.smul_apply]
  split_ifs
  · rfl
  · rw [smul_neg]
  · simp
theorem extendByZero_zero : _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero P (0 : PositiveEdgeOf P → ComplexMatrix2) = 0 := by
  funext b
  simp [_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero]
theorem extendByZero_mem_forms (ha : 0 < a) (hv : ∀ s, v s ∈ ComplexMatrix2.traceless) :
    _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero P v ∈ complexEdgeForms a := by
  exact show IsEdgeFormIn PeriodicLattice.complexLieAlgebra (extendByZero P v) from by
    refine ⟨fun b hb => ?_, fun b => extendByZero_opposite ha b⟩
    by_cases hP : b ∈ P
    · rw [extendByZero_of_positive hP hb]
      exact hv _
    · have e : _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero P v b = 0 := by
        simp [_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero, hP, not_isPositivelyOriented_opposite ha hb]
      rw [e]
      exact ComplexMatrix2.traceless.zero_mem
theorem operatorNorm_extendByZero_le [Finite (PositiveEdgeOf P)] (b : InfiniteLattice.Link a) :
    ComplexMatrix2.operatorNorm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero P v b) ≤ supNorm v := by
  simp only [_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero]
  split_ifs
  · exact le_tupleSup v _
  · rw [ComplexMatrix2.operatorNorm, norm_neg]
    exact le_tupleSup v _
  · simpa [ComplexMatrix2.operatorNorm] using tupleSup_nonneg v
end Links
section Forms
variable {L k j : ℕ}
theorem expForm_apply {A : Edge L k j → ComplexMatrix2}
    (hA : A ∈ complexEdgeForms (meshAt L k j)) (b : Edge L k j) :
    expForm A b = ComplexMatrix2.matExp (Complex.I • A b) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterBounds.expForm_apply <;> assumption
theorem expForm_mem (hE : ComplexMatrix2.ExpLogEstimates)
    {A : Edge L k j → ComplexMatrix2} (hA : A ∈ complexEdgeForms (meshAt L k j)) :
    expForm A ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.FullSpace.IterBounds.expForm_mem_fieldsValuedIn <;> assumption
theorem expForm_mem_polydisc (hE : ComplexMatrix2.ExpLogEstimates)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) {r ρ : ℝ}
    (hr : ∀ b, ComplexMatrix2.operatorNorm (B b) ≤ r) (h : Real.exp r - 1 < ρ)
    (c : Edge L k (j + 1)) :
    expForm B ∈ nearIdentityPolydisc L k j ρ c := by
  have hc := expForm_mem hE hB
  refine ⟨⟨fun b _ => hc.1 b, fun b _ => hc.2 b⟩, fun b _ => ?_⟩
  rw [expForm_apply hB]
  refine lt_of_le_of_lt (hE.1 _).2 (lt_of_le_of_lt ?_ h)
  rw [operatorNorm_I_smul]
  have := Real.exp_le_exp.2 (hr b)
  linarith
end Forms
section Step
variable {L k j : ℕ}
abbrev linksAround (c : Edge L k (j + 1)) : Set (Edge L k j) :=
  doubleCubeLinks L (meshAt L k j) c
structure StepHypotheses (c : Edge L k (j + 1)) : Prop where
  expLog : ComplexMatrix2.ExpLogEstimates
  logSeries : MatrixLog.MatrixLogarithmsSeriesAndSpectral
  mesh_pos : 0 < meshAt L k j
  radius_pos : 0 < polydiscRadius L
  radius_le : polydiscRadius L ≤ 1
  admissible : PolydiscIsAdmissible L k j (polydiscRadius L) c
  opposite_mem : ∀ b ∈ linksAround c, b.opposite ∈ linksAround c
  nonempty : Nonempty (PositiveEdgeOf (linksAround c))
  smoothing_congr : ∀ V V' : Edge L k j → ComplexMatrix2,
    V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c →
    V' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c →
    (∀ b ∈ linksAround c, V b = V' b) → complexSmoothing L V c = complexSmoothing L V' c
  smoothing_zero : complexSmoothing L (expForm (0 : Edge L k j → ComplexMatrix2)) c = 1
  hasDerivAt : ∀ B ∈ complexEdgeForms (meshAt L k j),
    HasDerivAt (fun t : ℂ =>
        Complex.I⁻¹ • ComplexMatrix2.logSeries (complexSmoothing L (expForm (t • B)) c))
      (linearSmoothing L B c) 0
  linear_add : ∀ B ∈ complexEdgeForms (meshAt L k j), ∀ B' ∈ complexEdgeForms (meshAt L k j),
    linearSmoothing L (B + B') c = linearSmoothing L B c + linearSmoothing L B' c
  linear_smul : ∀ B ∈ complexEdgeForms (meshAt L k j), ∀ z : ℂ,
    linearSmoothing L (z • B) c = z • linearSmoothing L B c
  linear_bound : ∀ B ∈ complexEdgeForms (meshAt L k j), ∀ M : ℝ, 0 ≤ M →
    (∀ b, ComplexMatrix2.operatorNorm (B b) ≤ M) →
    ComplexMatrix2.operatorNorm (linearSmoothing L B c) ≤ 5 * (L : ℝ) * M
variable {c : Edge L k (j + 1)}
theorem StepHypotheses.stepRadius_pos (f : StepHypotheses c) : 0 < stepRemainderRadius L := by
  have := f.radius_pos
  unfold stepRemainderRadius
  linarith
theorem StepHypotheses.exp_sub_one_lt_radius (f : StepHypotheses c) :
    Real.exp (stepRemainderRadius L) - 1 < polydiscRadius L := by
  have h := real_exp_sub_one_lt_two_mul f.stepRadius_pos (by
    have := f.radius_le
    unfold stepRemainderRadius
    linarith)
  have e : 2 * stepRemainderRadius L = polydiscRadius L := by
    unfold stepRemainderRadius
    ring
  linarith
def defect (c : Edge L k (j + 1)) (v : PositiveEdgeOf (linksAround c) → ComplexMatrix2) :
    ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries
      (complexSmoothing L (expForm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v)) c) -
    linearSmoothing L (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v) c
variable [Fintype (PositiveEdgeOf (linksAround c))]
omit [Fintype (PositiveEdgeOf (linksAround c))] in
theorem StepHypotheses.extendByZero_mem (f : StepHypotheses c)
    {v : PositiveEdgeOf (linksAround c) → ComplexMatrix2}
    (hv : v ∈ tracelessPi (PositiveEdgeOf (linksAround c))) :
    _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v ∈ complexEdgeForms (meshAt L k j) :=
  extendByZero_mem_forms f.mesh_pos (mem_tracelessPi_iff.1 hv)
theorem StepHypotheses.expForm_mem_of_supBall (f : StepHypotheses c)
    {v : PositiveEdgeOf (linksAround c) → ComplexMatrix2}
    (hv : v ∈ supBall (PositiveEdgeOf (linksAround c)) (stepRemainderRadius L)) :
    expForm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v) ∈
      nearIdentityPolydisc L k j (polydiscRadius L) c :=
  expForm_mem_polydisc f.expLog (f.extendByZero_mem hv.1)
    (fun b => (operatorNorm_extendByZero_le b).trans hv.2.le) f.exp_sub_one_lt_radius c
def expOfValues (c : Edge L k (j + 1)) (v : PositiveEdgeOf (linksAround c) → ComplexMatrix2) :
    PositiveEdgeOf (linksAround c) → ComplexMatrix2 :=
  fun s => ComplexMatrix2.matExp (Complex.I • v s)
omit [Fintype (PositiveEdgeOf (linksAround c))] in
theorem restrictPositive_expForm {v : PositiveEdgeOf (linksAround c) → ComplexMatrix2}
    (h : _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v ∈ complexEdgeForms (meshAt L k j)) :
    restrictPositive (linksAround c) (expForm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v)) =
      expOfValues c v := by
  funext s
  simp only [restrictPositive, expOfValues]
  rw [expForm_apply h, extendByZero_of_positive s.2.1 s.2.2]
omit [Fintype (PositiveEdgeOf (linksAround c))] in
theorem extendFromPositive_expOfValues
    (hrev : ∀ b ∈ linksAround c, b.opposite ∈ linksAround c)
    {v : PositiveEdgeOf (linksAround c) → ComplexMatrix2}
    (hB : _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v ∈ complexEdgeForms (meshAt L k j)) {b : Edge L k j}
    (hb : b ∈ linksAround c) :
    extendFromPositive (linksAround c) (expOfValues c v) b =
      expForm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v) b := by
  classical
  by_cases hp : b.IsPositivelyOriented
  · rw [expForm_apply hB, extendByZero_of_positive hb hp]
    simp [extendFromPositive, hb, hp, expOfValues]
  · have hr : b.opposite.IsPositivelyOriented := (isPositivelyOriented_or_opposite b).resolve_left hp
    have e₁ : expForm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v) b =
        (ComplexMatrix2.matExp (Complex.I • _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v b.opposite) * 1)⁻¹ := by
      simp [expForm, expTwist, hp]
    rw [e₁, extendByZero_of_positive (hrev b hb) hr]
    simp [extendFromPositive, hp, hr, hrev b hb, expOfValues]
theorem StepHypotheses.smoothing_eq_extend (f : StepHypotheses c)
    {v : PositiveEdgeOf (linksAround c) → ComplexMatrix2}
    (hv : v ∈ supBall (PositiveEdgeOf (linksAround c)) (stepRemainderRadius L)) :
    complexSmoothing L (expForm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v)) c =
      complexSmoothing L (extendFromPositive (linksAround c) (expOfValues c v)) c := by
  have hW := f.expForm_mem_of_supBall hv
  have hag : ∀ b ∈ linksAround c, extendFromPositive (linksAround c) (expOfValues c v) b =
      expForm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v) b := fun b hb =>
    extendFromPositive_expOfValues f.opposite_mem (f.extendByZero_mem hv.1) hb
  refine f.smoothing_congr _ _ hW ?_ fun b hb => (hag b hb).symm
  refine ⟨⟨fun b hb => ?_, fun b hb => ?_⟩, fun b hb => ?_⟩
  · rw [hag b hb]
    exact hW.1.1 b hb
  · rw [hag b hb, hag _ (f.opposite_mem b hb)]
    exact hW.1.2 b hb
  · rw [hag b hb]
    exact hW.2 b hb
def StepHypotheses.linearMap (f : StepHypotheses c) :
    ↥(tracelessPiSubmodule (PositiveEdgeOf (linksAround c))) →ₗ[ℂ] ComplexMatrix2 where
  toFun v := linearSmoothing L
    (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) (v : PositiveEdgeOf (linksAround c) → ComplexMatrix2)) c
  map_add' v w := by
    have hv : (v : PositiveEdgeOf (linksAround c) → ComplexMatrix2) ∈ tracelessPi _ :=
      mem_tracelessPi_iff.2 fun s => v.2 s (mem_univ _)
    have hw : (w : PositiveEdgeOf (linksAround c) → ComplexMatrix2) ∈ tracelessPi _ :=
      mem_tracelessPi_iff.2 fun s => w.2 s (mem_univ _)
    rw [Submodule.coe_add, extendByZero_add]
    exact f.linear_add _ (f.extendByZero_mem hv) _ (f.extendByZero_mem hw)
  map_smul' z v := by
    have hv : (v : PositiveEdgeOf (linksAround c) → ComplexMatrix2) ∈ tracelessPi _ :=
      mem_tracelessPi_iff.2 fun s => v.2 s (mem_univ _)
    rw [Submodule.coe_smul, extendByZero_smul]
    exact f.linear_smul _ (f.extendByZero_mem hv) z
theorem StepHypotheses.differentiableAt_defect (f : StepHypotheses c)
    (hh : ComplexMatrix2.IsHolomorphicBetween
      (fun _ : PositiveEdgeOf (linksAround c) => ComplexMatrix2.FactorKind.group)
      (fun _ : Unit => ComplexMatrix2.FactorKind.group)
      (restrictPositive (linksAround c) '' nearIdentityPolydisc L k j (polydiscRadius L) c)
      fun v _ => complexSmoothing L (extendFromPositive (linksAround c) v) c)
    (v₀ : ↥(tracelessPiSubmodule (PositiveEdgeOf (linksAround c))))
    (hv₀ : (v₀ : PositiveEdgeOf (linksAround c) → ComplexMatrix2) ∈
      supBall (PositiveEdgeOf (linksAround c)) (stepRemainderRadius L)) :
    DifferentiableAt ℂ (fun v : ↥(tracelessPiSubmodule (PositiveEdgeOf (linksAround c))) =>
      defect c (v : PositiveEdgeOf (linksAround c) → ComplexMatrix2)) v₀ := by
  let σ := PositiveEdgeOf (linksAround c)
  let S := ↥(tracelessPiSubmodule σ)
  let ev : S → σ → ComplexMatrix2 := fun v => expOfValues c (v : σ → ComplexMatrix2)
  let D := restrictPositive (linksAround c) '' nearIdentityPolydisc L k j (polydiscRadius L) c
  have he : ∀ v : S, DifferentiableAt ℂ ev v := by
    intro v
    rw [differentiableAt_pi]
    intro s
    have hl : DifferentiableAt ℂ (fun v : S => Complex.I • (v : σ → ComplexMatrix2) s) v :=
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ComplexMatrix2) s).comp
        (Submodule.subtypeL (tracelessPiSubmodule σ))).differentiableAt).const_smul Complex.I
    exact (matExp_differentiableAt f.logSeries _).comp v hl
  have hmem : ∀ v : S, (v : σ → ComplexMatrix2) ∈ tracelessPi σ := fun v =>
    mem_tracelessPi_iff.2 fun s => v.2 s (mem_univ _)
  have hopen : IsOpen {v : S | (v : σ → ComplexMatrix2) ∈ supBall σ (stepRemainderRadius L)} := by
    have e : {v : S | (v : σ → ComplexMatrix2) ∈ supBall σ (stepRemainderRadius L)} =
        {v : S | ‖(v : σ → ComplexMatrix2)‖ < stepRemainderRadius L} := by
      ext v
      constructor
      · intro h
        have := h.2
        rwa [tupleSup_eq_norm] at this
      · intro h
        refine ⟨hmem v, ?_⟩
        rwa [tupleSup_eq_norm]
    rw [e]
    exact isOpen_lt continuous_subtype_val.norm continuous_const
  have hball : ∀ᶠ v : S in 𝓝 v₀, (v : σ → ComplexMatrix2) ∈ supBall σ (stepRemainderRadius L) :=
    hopen.mem_nhds hv₀
  have hD : ∀ v : S, (v : σ → ComplexMatrix2) ∈ supBall σ (stepRemainderRadius L) → ev v ∈ D :=
    fun v hv => ⟨_, f.expForm_mem_of_supBall hv, restrictPositive_expForm (f.extendByZero_mem hv.1)⟩
  obtain ⟨F, hFa, hFe⟩ := hh.2.2 (ev v₀) (hD v₀ hv₀)
  have ht : Tendsto ev (𝓝 v₀) (𝓝[D] (ev v₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨(he v₀).continuousAt, hball.mono hD⟩
  have hev := ht.eventually hFe
  have hdF : DifferentiableAt ℂ (fun v : S => F (ev v) ()) v₀ :=
    (differentiableAt_pi.1 (hFa.differentiableAt.comp v₀ (he v₀))) ()
  have hG : DifferentiableAt ℂ
      (fun v : S =>
        complexSmoothing L (expForm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) (v : σ → ComplexMatrix2))) c)
      v₀ := by
    refine hdF.congr_of_eventuallyEq ?_
    filter_upwards [hev, hball] with v h₁ h₂
    rw [f.smoothing_eq_extend h₂]
    exact congrFun h₁ ()
  have hnear : ComplexMatrix2.operatorNorm (complexSmoothing L (expForm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero
      (linksAround c) (v₀ : σ → ComplexMatrix2))) c - 1) < 1 :=
    (f.admissible.smoothing_near_one _ (f.expForm_mem_of_supBall hv₀)).trans (by norm_num)
  have hlog : DifferentiableAt ℂ (fun v : S => Complex.I⁻¹ • ComplexMatrix2.logSeries
      (complexSmoothing L (expForm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) (v : σ → ComplexMatrix2))) c))
      v₀ :=
    ((logSeries_differentiableAt f.logSeries hnear).comp v₀ hG).const_smul Complex.I⁻¹
  have hlin : DifferentiableAt ℂ (fun v : S => f.linearMap v) v₀ :=
    (LinearMap.toContinuousLinearMap f.linearMap).differentiableAt
  exact hlog.sub hlin
theorem StepHypotheses.defect_bound (f : StepHypotheses c)
    {v : PositiveEdgeOf (linksAround c) → ComplexMatrix2}
    (hv : v ∈ supBall (PositiveEdgeOf (linksAround c)) (stepRemainderRadius L)) :
    ComplexMatrix2.operatorNorm (defect c v) ≤ 1 + 5 * (L : ℝ) * stepRemainderRadius L := by
  have hs := f.admissible.smoothing_near_one _ (f.expForm_mem_of_supBall hv)
  set X := complexSmoothing L (expForm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v)) c with hX
  have hs₁ : ComplexMatrix2.operatorNorm (X - 1) < 1 := hs.trans (by norm_num)
  have hlog := f.expLog.2.2.2.1 (X - 1) hs₁
  rw [add_sub_cancel] at hlog
  have hl : ComplexMatrix2.operatorNorm (ComplexMatrix2.logSeries X) ≤ 1 := by
    refine hlog.1.trans (hlog.2.1.trans ?_)
    rw [div_le_one (by linarith)]
    linarith
  have hq := f.linear_bound _ (f.extendByZero_mem hv.1) (stepRemainderRadius L)
    f.stepRadius_pos.le fun b => (operatorNorm_extendByZero_le b).trans hv.2.le
  calc ComplexMatrix2.operatorNorm (defect c v)
      ≤ ComplexMatrix2.operatorNorm (Complex.I⁻¹ • ComplexMatrix2.logSeries X) +
          ComplexMatrix2.operatorNorm (linearSmoothing L (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v) c) :=
        norm_sub_le _ _
    _ ≤ 1 + 5 * (L : ℝ) * stepRemainderRadius L := by
        rw [operatorNorm_I_inv_smul]
        exact add_le_add hl hq
omit [Fintype (PositiveEdgeOf (linksAround c))] in
theorem StepHypotheses.defect_zero (f : StepHypotheses c) :
    defect c (0 : PositiveEdgeOf (linksAround c) → ComplexMatrix2) = 0 := by
  have hz : (0 : Edge L k j → ComplexMatrix2) ∈ complexEdgeForms (meshAt L k j) :=
    Submodule.zero_mem _
  have h₀ := f.linear_smul 0 hz 0
  simp only [zero_smul] at h₀
  have hlog : ComplexMatrix2.logSeries 1 = 0 := by
    simp [ComplexMatrix2.logSeries]
  simp only [defect, extendByZero_zero]
  rw [f.smoothing_zero, hlog, smul_zero, h₀, sub_zero]
omit [Fintype (PositiveEdgeOf (linksAround c))] in
theorem StepHypotheses.hasDerivAt_defect (f : StepHypotheses c)
    {v : PositiveEdgeOf (linksAround c) → ComplexMatrix2}
    (hv : v ∈ tracelessPi (PositiveEdgeOf (linksAround c))) :
    HasDerivAt (fun z : ℂ => Coordinates.ComplexCoordinates.matrixEquiv (defect c (z • v))) 0 0 := by
  have hB := f.extendByZero_mem hv
  set B := _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v with hBdef
  have e : ∀ z : ℂ, defect c (z • v) =
      Complex.I⁻¹ • ComplexMatrix2.logSeries (complexSmoothing L (expForm (z • B)) c) -
        z • linearSmoothing L B c := fun z => by
    simp only [defect, extendByZero_smul]
    rw [f.linear_smul B hB z]
  have hd : HasDerivAt (fun z : ℂ =>
      Complex.I⁻¹ • ComplexMatrix2.logSeries (complexSmoothing L (expForm (z • B)) c) -
        z • linearSmoothing L B c) 0 0 := by
    have h := (f.hasDerivAt B hB).sub ((hasDerivAt_id (0 : ℂ)).smul_const (linearSmoothing L B c))
    have e₁ : linearSmoothing L B c - (1 : ℂ) • linearSmoothing L B c = 0 := by
      rw [one_smul, sub_self]
    rw [e₁] at h
    exact h
  let ℓ : ComplexMatrix2 →L[ℂ] Coordinates.ComplexCoordinates 4 :=
    LinearMap.toContinuousLinearMap (matrixEquiv_isLinearMap.mk' _)
  have h := ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hd
  have e₀ : ℓ 0 = 0 := map_zero ℓ
  rw [e₀] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  show Coordinates.ComplexCoordinates.matrixEquiv (defect c (z • v)) = _
  rw [e z]
  rfl
end Step
section Form
variable {L k j : ℕ} {c : Edge L k (j + 1)}
theorem le_maxOperatorNorm_toReal {ι : Type*} {g : ι → ComplexMatrix2}
    (h : maxOperatorNorm g ≠ ∞) (i : ι) :
    ComplexMatrix2.operatorNorm (g i) ≤ (maxOperatorNorm g).toReal := by apply _root_.YangMills.Construction.Tower.IteratedMeanBounds.operatorNorm_le_toReal_maxOperatorNorm <;> assumption
theorem StepHypotheses.extendByZero_eq (f : StepHypotheses c) {A : Edge L k j → ComplexMatrix2}
    (hA : A ∈ complexEdgeForms (meshAt L k j)) {b : Edge L k j} (hb : b ∈ linksAround c) :
    _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) (fun s : PositiveEdgeOf (linksAround c) => A s.1) b = A b := by
  have hA' : IsEdgeFormIn PeriodicLattice.complexLieAlgebra A := hA
  by_cases hp : b.IsPositivelyOriented
  · rw [extendByZero_of_positive hb hp]
  · have hr : b.opposite.IsPositivelyOriented := (isPositivelyOriented_or_opposite b).resolve_left hp
    have h₁ := extendByZero_opposite (P := linksAround c)
      (v := fun s : PositiveEdgeOf (linksAround c) => A s.1) f.mesh_pos b.opposite
    rw [opposite_opposite, extendByZero_of_positive (f.opposite_mem b hb) hr] at h₁
    rw [h₁, hA'.2 b, neg_neg]
theorem StepHypotheses.linearSmoothing_eq_of_agree (f : StepHypotheses c)
    {B B' : Edge L k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k j)) (hB' : B' ∈ complexEdgeForms (meshAt L k j))
    (hb : ∀ b, ComplexMatrix2.operatorNorm (B b) ≤ stepRemainderRadius L)
    (hb' : ∀ b, ComplexMatrix2.operatorNorm (B' b) ≤ stepRemainderRadius L)
    (hag : ∀ b ∈ linksAround c, B b = B' b) : linearSmoothing L B c = linearSmoothing L B' c := by
  have small : ∀ {C : Edge L k j → ComplexMatrix2}, C ∈ complexEdgeForms (meshAt L k j) →
      (∀ b, ComplexMatrix2.operatorNorm (C b) ≤ stepRemainderRadius L) → ∀ t : ℂ, ‖t‖ ≤ 1 →
      expForm (t • C) ∈ nearIdentityPolydisc L k j (polydiscRadius L) c := by
    intro C hC hCb t ht
    refine expForm_mem_polydisc f.expLog (Submodule.smul_mem _ t hC) (fun b => ?_)
      f.exp_sub_one_lt_radius c
    have e : ComplexMatrix2.operatorNorm ((t • C) b) = ‖t‖ * ComplexMatrix2.operatorNorm (C b) := by
      simp [ComplexMatrix2.operatorNorm, norm_smul]
    rw [e]
    calc ‖t‖ * ComplexMatrix2.operatorNorm (C b) ≤ 1 * ComplexMatrix2.operatorNorm (C b) :=
          mul_le_mul_of_nonneg_right ht (norm_nonneg _)
      _ ≤ stepRemainderRadius L := by
          rw [one_mul]
          exact hCb b
  refine (f.hasDerivAt B hB).unique ((f.hasDerivAt B' hB').congr_of_eventuallyEq ?_)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with t ht
  have ht' : ‖t‖ ≤ 1 := (mem_ball_zero_iff.1 ht).le
  rw [f.smoothing_congr _ _ (small hB hb t ht') (small hB' hb' t ht') fun b hbP => ?_]
  rw [expForm_apply (Submodule.smul_mem _ t hB), expForm_apply (Submodule.smul_mem _ t hB')]
  simp only [Pi.smul_apply, hag b hbP]
theorem StepHypotheses.quadratic_bound (f : StepHypotheses c)
    (hT : HolomorphicOnTracelessIffDifferentiable)
    (hN : SecondOrderBoundOnSupBall)
    {A : Edge L k j → ComplexMatrix2} (hA : A ∈ complexEdgeForms (meshAt L k j))
    (hsup : maxOperatorNorm A ≤ ENNReal.ofReal (stepRemainderRadius L / 2)) :
    expForm A ∈ nearIdentityPolydisc L k j (polydiscRadius L) c ∧
      ComplexMatrix2.operatorNorm (Complex.I⁻¹ • ComplexMatrix2.logSeries
          (smoothingMap L k j (expForm A) c) - linearSmoothing L A c) ≤
        stepRemainderConstant L * (maxOperatorNorm A).toReal ^ 2 := by
  classical
  have hA' : IsEdgeFormIn PeriodicLattice.complexLieAlgebra A := hA
  have hυ := f.stepRadius_pos
  have hfin : maxOperatorNorm A ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsup
  have htr : (maxOperatorNorm A).toReal ≤ stepRemainderRadius L / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by linarith) hsup
  have hAb : ∀ b, ComplexMatrix2.operatorNorm (A b) ≤ stepRemainderRadius L := fun b =>
    (le_maxOperatorNorm_toReal hfin b).trans (by linarith)
  have hpoly := expForm_mem_polydisc f.expLog hA hAb f.exp_sub_one_lt_radius c
  refine ⟨hpoly, ?_⟩
  obtain ⟨inst, hh⟩ := f.admissible.holomorphic_smoothing.1
  have := f.nonempty
  let σ := PositiveEdgeOf (linksAround c)
  let v : σ → ComplexMatrix2 := fun s => A s.1
  have hv : v ∈ tracelessPi σ := mem_tracelessPi_iff.2 fun s => hA'.1 _ s.2.2
  have hnorm : supNorm v ≤ (maxOperatorNorm A).toReal :=
    Real.iSup_le (fun s => le_maxOperatorNorm_toReal hfin s.1) ENNReal.toReal_nonneg
  have hball : v ∈ supBall σ (stepRemainderRadius L) := ⟨hv, by linarith⟩
  have hcont := f.extendByZero_mem hv
  have hcb : ∀ b, ComplexMatrix2.operatorNorm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v b) ≤
      stepRemainderRadius L :=
    fun b => (operatorNorm_extendByZero_le b).trans hball.2.le
  have hag : ∀ b ∈ linksAround c, _root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v b = A b := fun b hb =>
    f.extendByZero_eq hA hb
  have hM : complexSmoothing L (expForm (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v)) c =
      complexSmoothing L (expForm A) c := by
    refine f.smoothing_congr _ _ (f.expForm_mem_of_supBall hball) hpoly fun b hb => ?_
    rw [expForm_apply hcont, expForm_apply hA, hag b hb]
  have hQ : linearSmoothing L (_root_.YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder.extendByZero (linksAround c) v) c = linearSmoothing L A c :=
    f.linearSmoothing_eq_of_agree hcont hA hcb hAb hag
  have hval : defect c v =
      Complex.I⁻¹ • ComplexMatrix2.logSeries (smoothingMap L k j (expForm A) c) -
        linearSmoothing L A c := by
    simp only [defect]
    rw [hM, hQ]
    rfl
  have hhol : IsHolomorphicOnTraceless OneLoop.pauliBasis
      Coordinates.ComplexCoordinates.matrixEquiv (supBall σ (stepRemainderRadius L))
      (defect c) := by
    refine (hT σ ComplexMatrix2 4 OneLoop.pauliBasis Coordinates.ComplexCoordinates.matrixEquiv
      matrixEquiv_isLinearMap _ _).2 ⟨isSupOpen_supBall _, fun w hw => ?_⟩
    exact (f.differentiableAt_defect hh w hw).differentiableWithinAt
  have hkey := hN σ (stepRemainderRadius L) (1 + 5 * (L : ℝ) * stepRemainderRadius L) hυ
    (by positivity) OneLoop.pauliBasis (defect c) hhol
    (fun w hw => f.defect_bound hw) f.defect_zero
    (fun w hw => f.hasDerivAt_defect hw) v hball
  rw [← hval]
  refine hkey.trans ?_
  have hsq : supNorm v ^ 2 ≤ (maxOperatorNorm A).toReal ^ 2 :=
    pow_le_pow_left₀ (tupleSup_nonneg v) hnorm 2
  have hc₀ : 0 ≤ (1 + 5 * (L : ℝ) * stepRemainderRadius L) * (stepRemainderRadius L ^ 2)⁻¹ := by
    positivity
  calc (1 + 5 * (L : ℝ) * stepRemainderRadius L) * (stepRemainderRadius L ^ 2)⁻¹ *
        supNorm v ^ 2
      ≤ (1 + 5 * (L : ℝ) * stepRemainderRadius L) * (stepRemainderRadius L ^ 2)⁻¹ *
        (maxOperatorNorm A).toReal ^ 2 := mul_le_mul_of_nonneg_left hsq hc₀
    _ = stepRemainderConstant L * (maxOperatorNorm A).toReal ^ 2 := by
        simp only [stepRemainderConstant, inv_pow]
end Form
section Gather
variable {L k j : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (i : ℕ) : 0 < meshAt L k i := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.meshAt_pos <;> assumption
theorem complexSmoothing_congr (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i < k)
    {c : Edge L k (i + 1)} (hc : c.IsPositivelyOriented) {V V' : Edge L k i → ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k i (polydiscRadius L) c)
    (hV' : V' ∈ nearIdentityPolydisc L k i (polydiscRadius L) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k i) c, V b = V' b) :
    complexSmoothing L V c = complexSmoothing L V' c := by apply _root_.YangMills.Construction.Tower.MeanStableFields.Infinite.complexSmoothing_congr <;> assumption
theorem stepHypotheses (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hD : YangMills.Construction.Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hO : RescaledTrivialSteps)
    (hLin : YangMills.Construction.Tower.TwoLevelMaps.Statement)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hLog : MatrixLog.MatrixLogarithmsSeriesAndSpectral)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) : StepHypotheses c := by
  have hk : 1 ≤ k := by omega
  have hρ : IsAdmissiblePolydiscRadius L (polydiscRadius L) := (hS.1 L hL).2.2
  obtain ⟨hU, hstep⟩ := hO L hL k hk
  have hst := hstep j hj
  have hV : (fun _ => 1 : Edge L k j → ComplexMatrix2) ∈ smallComplexFields L k j := by
    refine ⟨⟨fun b => ?_, fun b => ?_⟩, fun b => ?_⟩
    · show Matrix.det (1 : ComplexMatrix2) = 1
      simp
    · simp
    · simpa [ComplexMatrix2.operatorNorm] using hρ.pos
  have hold := (hD L hL k hk).2.1 j hj _ hV _ hU
  have hone : complexSmoothing L (fun _ => 1 : Edge L k j → ComplexMatrix2) c = 1 :=
    congrFun hst.1 c
  have hq : ∀ B ∈ complexEdgeForms (meshAt L k j),
      complexSmoothingDeriv (L := L) (k := k) (j := j) (fun _ => 1) B =
        linearSmoothing (a := meshAt L k (j + 1)) L B :=
    fun B hB => (hst.2.2.1 B hB).1
  have hd := (hP L hL k j hj).2 c hc
  have hfo := hd.finite_open
  refine
    { expLog := hE
      logSeries := hLog
      mesh_pos := meshAt_pos hL j
      radius_pos := hρ.pos
      radius_le := hρ.le_one
      admissible := hρ.fullSpace k j hj c hc
      opposite_mem := hfo.opposite_mem
      nonempty := ?_
      smoothing_congr := fun V V' h₁ h₂ he => complexSmoothing_congr hS hQ hL hj hc h₁ h₂ he
      smoothing_zero := ?_
      hasDerivAt := fun B hB => ?_
      linear_add := fun B hB B' hB' => ?_
      linear_smul := fun B hB z => ?_
      linear_bound := fun B hB M hM hb => ?_ }
  · obtain ⟨b, hb⟩ := hfo.positive_nonempty
    exact ⟨⟨b, hb.1, hb.2⟩⟩
  · have e : expForm (0 : Edge L k j → ComplexMatrix2) = fun _ => 1 := by
      funext b
      by_cases hb : b.IsPositivelyOriented
      · simp [expForm, expTwist, hb]
      · simp [expForm, expTwist, hb]
    rw [e, hone]
  · have h := hold.deriv_mean c hc B hB
    have e : ∀ t : ℂ, FullSpace.AsDifferentials.meanLogRatio
        (fun _ => 1 : Edge L k j → ComplexMatrix2) c (t • B) =
        Complex.I⁻¹ • ComplexMatrix2.logSeries (complexSmoothing L (expForm (t • B)) c) :=
      fun t => by
      simp only [FullSpace.AsDifferentials.meanLogRatio, FullSpace.AsDifferentials.meanRatio]
      rw [hone, inv_one, mul_one]
      rfl
    have h' : HasDerivAt (fun t : ℂ =>
        FullSpace.AsDifferentials.meanLogRatio
          (fun _ => 1 : Edge L k j → ComplexMatrix2) c (t • B))
        (complexSmoothingDeriv (L := L) (k := k) (j := j) (fun _ => 1) B c) 0 := h
    rw [hq B hB] at h'
    simpa only [e] using h'
  · have h := ((hold.linear_mean B hB B' hB' 1).1)
    rw [hq B hB, hq B' hB', hq _ (Submodule.add_mem _ hB hB')] at h
    exact congrFun h c
  · have h := ((hold.linear_mean B hB B hB z).2)
    rw [hq B hB, hq _ (Submodule.smul_mem _ z hB)] at h
    exact congrFun h c
  · have h := (hLin L hL k hk).2.2.1 1 (j + 1) (by omega) (by omega) (by omega)
    have h₁ : maxOperatorNorm (FullSpace.TwoLevelMaps.linearSmoothingBetween L k
        (Nat.le_succ j) B) ≤ 5 * (L : ℝ≥0∞) ^ 1 * maxOperatorNorm B :=
      h.linearSmoothing_norm_le B hB
    have e : FullSpace.TwoLevelMaps.linearSmoothingBetween L k
        (Nat.le_succ j) B = linearSmoothing (a := meshAt L k (j + 1)) L B := by
      simp only [FullSpace.TwoLevelMaps.linearSmoothingBetween]
      rw [levelwiseComposition_succ _ le_rfl (Nat.le_succ j), levelwiseComposition_self]
      rfl
    rw [e] at h₁
    have h₂ : ENNReal.ofReal (ComplexMatrix2.operatorNorm
          (linearSmoothing (a := meshAt L k (j + 1)) L B c)) ≤
        maxOperatorNorm (linearSmoothing (a := meshAt L k (j + 1)) L B) :=
      le_iSup (fun c => ENNReal.ofReal (ComplexMatrix2.operatorNorm
        (linearSmoothing (a := meshAt L k (j + 1)) L B c))) c
    have h₃ : maxOperatorNorm B ≤ ENNReal.ofReal M :=
      iSup_le fun b => ENNReal.ofReal_le_ofReal (hb b)
    have h₄ : 5 * (L : ℝ≥0∞) ^ 1 * maxOperatorNorm B ≤ ENNReal.ofReal (5 * (L : ℝ) * M) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, pow_one]
      have h₅ : (5 : ℝ≥0∞) = ENNReal.ofReal 5 := by simp
      rw [← h₅]
      gcongr
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (h₂.trans (h₁.trans h₄))
end Gather
theorem stepRemainderAtInfiniteSide (hN : SecondOrderBoundOnSupBall)
    (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hD : YangMills.Construction.Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hO : RescaledTrivialSteps)
    (hLin : YangMills.Construction.Tower.TwoLevelMaps.Statement)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hLog : MatrixLog.MatrixLogarithmsSeriesAndSpectral)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hT : HolomorphicOnTracelessIffDifferentiable) :
    StepRemainderAtInfiniteSide := by
  intro L hL k j hj c hc A hA hsup
  exact (stepHypotheses hS hD hO hLin hE hLog hQ hP hL hj hc).quadratic_bound hT hN hA hsup
end YangMills.Construction.Tower.FullSpace.InfiniteSideRemainder
end
