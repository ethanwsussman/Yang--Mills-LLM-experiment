import YangMills.Construction.RunningCouplingSlope.DriftOfALeastPointIsLinearProof
import YangMills.Construction.RunningCouplingSlope.LevelMapOfAChainProof
import Mathlib
import YangMills.Construction.Matrices.SpecialUnitaryTwo
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace TransportTriangular
open Filter Tower Matrices
open scoped Topology
section Smoothness
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
private theorem contDiffAt_det {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀) :
    ContDiffAt ℝ 2 (fun y => (f y).det) y₀ := by apply _root_.YangMills.SharedProofs.p38879 <;> assumption
private theorem contDiffAt_smul {f : Y → ℂ} {g : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀)
    (hg : ContDiffAt ℝ 2 g y₀) : ContDiffAt ℝ 2 (fun y => f y • g y) y₀ := by apply _root_.YangMills.SharedProofs.p3257 <;> assumption
private theorem contDiffAt_cpow_half {f : Y → ℂ} (hf : ContDiffAt ℝ 2 f y₀)
    (hs : f y₀ ∈ Complex.slitPlane) :
    ContDiffAt ℝ 2 (fun y => f y ^ (1 / 2 : ℂ)) y₀ := by apply _root_.YangMills.SharedProofs.p3856 <;> assumption
variable {L n k j : ℕ}
private theorem contDiffAt_contourMean [NeZero L] {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Edge L n k (j + 1)) : ContDiffAt ℝ 2 (fun y => contourMean (V y) c) y₀ := by apply _root_.YangMills.SharedProofs.p1840 <;> assumption
private theorem contDiffAt_meanRadius [NeZero L] {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Edge L n k (j + 1)) (hs : (contourMean (V y₀) c).det ∈ Complex.slitPlane) :
    ContDiffAt ℝ 2 (fun y => meanRadius (V y) c) y₀ :=
  contDiffAt_cpow_half (contDiffAt_det (contDiffAt_contourMean hV hu c)) hs
private theorem contDiffAt_normalizedMean [NeZero L] {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Edge L n k (j + 1)) (hs : (contourMean (V y₀) c).det ∈ Complex.slitPlane)
    (hl : meanRadius (V y₀) c ≠ 0) :
    ContDiffAt ℝ 2 (fun y => normalizedMean (V y) c) y₀ :=
  contDiffAt_smul ((contDiffAt_meanRadius hV hu c hs).inv hl) (contDiffAt_contourMean hV hu c)
end Smoothness
section QuaternionMatrices
private def quaternionMatrices : Submodule ℝ ComplexMatrix2 where
  carrier := {M | M 1 1 = star (M 0 0) ∧ M 1 0 = -star (M 0 1)}
  add_mem' := by
    rintro A B ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · simp [Matrix.add_apply, h1, h3]
    · simp only [Matrix.add_apply, h2, h4, star_add]; ring
  zero_mem' := by simp
  smul_mem' := by
    rintro c A ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · simp [Matrix.smul_apply, h1]
    · simp [Matrix.smul_apply, h2]
private theorem mem_quaternionMatrices_of_mem {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : g ∈ quaternionMatrices :=
  ComplexMatrix2.quaternion_entries_of_mem_specialUnitary hg
private theorem det_eq_normSq_add {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices) :
    M.det = ((Complex.normSq (M 0 0) + Complex.normSq (M 0 1) : ℝ) : ℂ) :=
  ComplexMatrix2.det_quaternionMatrix hM
private theorem det_mem_slitPlane {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices)
    (h : M.det ≠ 0) : M.det ∈ Complex.slitPlane :=
  ComplexMatrix2.det_quaternionMatrix_mem_slitPlane hM h
private theorem normalized_mem_compactGaugeGroup {M : ComplexMatrix2}
    (hM : M ∈ quaternionMatrices) (h : M.det ≠ 0) :
    (M.det ^ (1 / 2 : ℂ))⁻¹ • M ∈ PeriodicLattice.compactGaugeGroup :=
  ComplexMatrix2.normalize_quaternionMatrix_mem_specialUnitary hM h
variable {L n k j : ℕ}
private theorem compact_mul_mem {g h : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hh : h ∈ PeriodicLattice.compactGaugeGroup) :
    g * h ∈ PeriodicLattice.compactGaugeGroup := ComplexMatrix2.specialUnitary.mul_mem hg hh
private theorem compact_inv_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem compact_isUnit_det {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem pathHolonomy_mem_compact {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy V Γ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p6330 <;> assumption
private theorem contourMean_mem_quaternionMatrices [NeZero L] {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) (c : Edge L n k (j + 1)) :
    contourMean V c ∈ quaternionMatrices := by
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  have hs : ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) =
      (((1 / 24 : ℝ) * ((L : ℝ) ^ (-4 : ℤ)) : ℝ) : ℂ) := by
    simp [PeriodicLattice.inverseFourthPowerWeight]
  rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin, hs, Complex.coe_smul]
  refine quaternionMatrices.smul_mem _
    (quaternionMatrices.sum_mem fun x _ => quaternionMatrices.sum_mem fun π _ => ?_)
  exact mem_quaternionMatrices_of_mem (compact_mul_mem
    (compact_mul_mem (pathHolonomy_mem_compact hV _) (pathHolonomy_mem_compact hV _))
    (compact_inv_mem (pathHolonomy_mem_compact hV _)))
end QuaternionMatrices
section OneParameterCurves
private theorem hasDerivAt_inv_at_zero {f : ℝ → ComplexMatrix2} {f' : ComplexMatrix2}
    (hf : HasDerivAt f f' 0) (hu : IsUnit (f 0).det) :
    HasDerivAt (fun t => (f t)⁻¹) (-((f 0)⁻¹ * f' * (f 0)⁻¹)) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.hasDerivAt_inv_matrix <;> assumption
private theorem matExp_I_smul_mem_compact {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
private theorem hasDerivAt_oneParameter (X : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • X)))
      (Complex.I • X) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.hasDerivAt_matExp_smul <;> assumption
private theorem oneParameter_zero (X : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • (((0 : ℝ) : ℂ) • X)) = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.matExp_I_line_zero <;> assumption
end OneParameterCurves
section BasicFacts
variable {L n k j : ℕ}
private theorem meanRadius_ne_zero {X : ChainPoint L n k} (hX : IsCompactValued X) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) : meanRadius (levelField X i) c.1 ≠ 0 := by apply _root_.YangMills.SharedProofs.p17043 <;> assumption
private theorem det_contourMean_ne_zero {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    {c : Edge L n k (j + 1)} (h : meanRadius V c ≠ 0) : (contourMean V c).det ≠ 0 := by apply _root_.YangMills.SharedProofs.p15699 <;> assumption
private theorem isUnit_det_of_mem_fieldSpace {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (b : Edge L n k j) :
    IsUnit (V b).det := compact_isUnit_det (hV.1 b (Set.mem_univ b))
private theorem tangentTransport_succ_apply (X : ChainPoint L n k) (ξ : LevelForms L n k) {j : ℕ}
    (h : j < k) {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    tangentTransport X ξ (j + 1) b =
      ComplexMatrix2.conjugateBy (X.noise ⟨j, h⟩ ⟨b, hb⟩)
        (leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) b) +
      (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) b := by apply _root_.YangMills.SharedProofs.p457 <;> assumption
private theorem expTwist_zero {j : ℕ} {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldSpace L n k j) (M : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • M) W = W := by apply _root_.YangMills.Construction.Tower.DiffAtZeroPaths.expTwist_zero_smul <;> assumption
private theorem I_inv_smul_deriv_mem
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex) {m : ℝ → ComplexMatrix2}
    {m' : ComplexMatrix2} (hm : HasDerivAt m m' 0) (h0 : m 0 = 1)
    (hr : ∀ᶠ r in 𝓝 (0 : ℝ), m r ∈ PeriodicLattice.compactGaugeGroup) :
    Complex.I⁻¹ • m' ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.inv_I_smul_deriv_mem <;> assumption
private theorem edgeForm_ext {A B : edgeFormSpace L n k j}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      (A : Edge L n k j → ComplexMatrix2) b = (B : Edge L n k j → ComplexMatrix2) b) : A = B := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.edgeForm_ext <;> assumption
private theorem extendOddly_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
private theorem extendOddly_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Edge L n k j → ComplexMatrix2)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace L n k j := by apply _root_.YangMills.SharedProofs.p1442 <;> assumption
private theorem conjugateBy_add (g A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (A + B) =
      ComplexMatrix2.conjugateBy g A + ComplexMatrix2.conjugateBy g B := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
private theorem conjugateBy_smul (g : ComplexMatrix2) (r : ℝ) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (r • A) = r • ComplexMatrix2.conjugateBy g A := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.conjugateBy_real_smul <;> assumption
private theorem xor_opposite
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.xor_isPositivelyOriented_opposite <;> assumption
end BasicFacts
section LeftChart
variable {L n k j : ℕ}
private instance [NeZero L] : Fintype (Edge L n k j) := Fintype.ofFinite _
private def twistVelocity (V : Edge L n k j → ComplexMatrix2)
    (f : PositiveEdge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  open Classical in fun b =>
    if hb : b.IsPositivelyOriented then (Complex.I • f ⟨b, hb⟩) * V b
    else -((V b.opposite)⁻¹ *
      ((Complex.I • f ⟨b.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented hb⟩) *
        V b.opposite) * (V b.opposite)⁻¹)
private theorem twistVelocity_add (V : Edge L n k j → ComplexMatrix2)
    (f g : PositiveEdge L n k j → ComplexMatrix2) :
    twistVelocity V (f + g) = twistVelocity V f + twistVelocity V g := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [twistVelocity, dif_pos hb, Pi.add_apply, smul_add, add_mul]
  · simp only [twistVelocity, dif_neg hb, Pi.add_apply, smul_add, add_mul, mul_add, neg_add]
private theorem twistVelocity_smul (V : Edge L n k j → ComplexMatrix2) (r : ℝ)
    (f : PositiveEdge L n k j → ComplexMatrix2) :
    twistVelocity V (r • f) = r • twistVelocity V f := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [twistVelocity, dif_pos hb, Pi.smul_apply]
    rw [smul_comm Complex.I r, smul_mul_assoc]
  · simp only [twistVelocity, dif_neg hb, Pi.smul_apply]
    rw [smul_comm Complex.I r, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_neg]
private theorem hasDerivAt_expTwist {V : Edge L n k j → ComplexMatrix2} (hr : V ∈ fieldSpace L n k j)
    (M : Edge L n k j → ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • M) V)
      (twistVelocity V fun c => M c.1) 0 := by
  refine hasDerivAt_pi.2 fun b => ?_
  by_cases hb : b.IsPositivelyOriented
  · have e : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • M) V b) =
        fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • M b)) * V b := by
      funext t
      simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply]
    rw [e]
    have h1 := (hasDerivAt_oneParameter (M b)).mul_const (V b)
    simpa only [twistVelocity, dif_pos hb] using h1
  · set c := b.opposite with hc
    have e : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • M) V b) =
        fun t : ℝ => (ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • M c)) * V c)⁻¹ := by
      funext t
      simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply, hc]
    have h1 := (hasDerivAt_oneParameter (M c)).mul_const (V c)
    have h0 : ComplexMatrix2.matExp (Complex.I • (((0 : ℝ) : ℂ) • M c)) * V c = V c := by
      simp only [oneParameter_zero, one_mul]
    have h2 := hasDerivAt_inv_at_zero h1 (by rw [h0]; exact isUnit_det_of_mem_fieldSpace hr c)
    rw [e]
    refine h2.congr_deriv ?_
    rw [h0]
    simp only [twistVelocity, dif_neg hb, hc]
private def meanDeriv (V : Edge L n k j → ComplexMatrix2) (b : Edge L n k (j + 1)) :
    (Edge L n k j → ComplexMatrix2) →L[ℝ] ComplexMatrix2 :=
  fderiv ℝ (fun V' : Edge L n k j → ComplexMatrix2 => normalizedMean V' b) V
private theorem normalizedMean_mem_compact [NeZero L] {V : Edge L n k j → ComplexMatrix2}
    (hr : V ∈ fieldSpace L n k j) {b : Edge L n k (j + 1)} (hl : meanRadius V b ≠ 0) :
    normalizedMean V b ∈ PeriodicLattice.compactGaugeGroup :=
  normalized_mem_compactGaugeGroup
    (contourMean_mem_quaternionMatrices (fun b' => hr.1 b' (Set.mem_univ _)) b)
    (det_contourMean_ne_zero hl)
private theorem hasDerivAt_relativeMean [NeZero L] {V : Edge L n k j → ComplexMatrix2}
    (hr : V ∈ fieldSpace L n k j) {b : Edge L n k (j + 1)} (hl : meanRadius V b ≠ 0)
    (M : Edge L n k j → ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist ((t : ℂ) • M) V) b *
        (normalizedMean V b)⁻¹)
      (meanDeriv V b (twistVelocity V fun c => M c.1) * (normalizedMean V b)⁻¹) 0 := by
  have hrr : ∀ b', V b' ∈ PeriodicLattice.compactGaugeGroup := fun b' => hr.1 b' (Set.mem_univ _)
  have hs := det_mem_slitPlane (contourMean_mem_quaternionMatrices hrr b)
    (det_contourMean_ne_zero hl)
  have hP : ContDiffAt ℝ 2 (fun V' : Edge L n k j → ComplexMatrix2 => normalizedMean V' b) V :=
    contDiffAt_normalizedMean (V := fun V => V) (y₀ := V)
      (fun b' => (contDiff_apply ℝ ComplexMatrix2 b').contDiffAt)
      (isUnit_det_of_mem_fieldSpace hr) b hs hl
  have hPd := (hP.differentiableAt (by norm_num)).hasFDerivAt
  have h1 : HasFDerivAt (fun V' : Edge L n k j → ComplexMatrix2 => normalizedMean V' b)
      (meanDeriv V b) (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • M) V) := by
    rw [expTwist_zero hr]
    exact hPd
  have hA := hasDerivAt_expTwist hr M
  have hPA : HasDerivAt
      (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist ((t : ℂ) • M) V) b)
      (meanDeriv V b (twistVelocity V fun c => M c.1)) 0 := by
    have h2 := h1.comp_hasDerivAt (0 : ℝ) hA
    exact h2
  exact hPA.mul_const _
private theorem relativeMean_zero [NeZero L] {V : Edge L n k j → ComplexMatrix2}
    (hr : V ∈ fieldSpace L n k j) {b : Edge L n k (j + 1)} (hl : meanRadius V b ≠ 0)
    (M : Edge L n k j → ComplexMatrix2) :
    normalizedMean (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • M) V) b *
      (normalizedMean V b)⁻¹ = 1 := by
  rw [expTwist_zero hr]
  exact Matrix.mul_nonsing_inv _ (compact_isUnit_det (normalizedMean_mem_compact hr hl))
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
include hd
private theorem leftDifferential_eq [NeZero L] {V : Edge L n k j → ComplexMatrix2}
    (hr : V ∈ fieldSpace L n k j) {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented)
    (hl : meanRadius V b ≠ 0) (M : Edge L n k j → ComplexMatrix2) :
    leftDifferential normalizedMean V M b =
      Complex.I⁻¹ • (meanDeriv V b (twistVelocity V fun c => M c.1) * (normalizedMean V b)⁻¹) := by
  have hY := hasDerivAt_relativeMean hr hl M
  have hlog := ((hd.1 Set.univ _ _ _ _ _ _ Filter.univ_mem hY hY hY).2.1
    (relativeMean_zero hr hl M)).2.2.1
  have e2 : leftDifferential normalizedMean V M b = Complex.I⁻¹ •
      deriv (fun t : ℝ => ComplexMatrix2.logSeries (normalizedMean (PeriodicLattice.expTwist
        ((t : ℂ) • M) V) b * (normalizedMean V b)⁻¹)) 0 := by
    unfold leftDifferential extendOddly
    rw [if_pos hb]
    rfl
  rw [e2, hlog.deriv]
omit hd in
private theorem expTwist_mem_compact {V : Edge L n k j → ComplexMatrix2}
    (hr : V ∈ fieldSpace L n k j) {M : Edge L n k j → ComplexMatrix2}
    (hM : ∀ c : Edge L n k j, c.IsPositivelyOriented → M c ∈ ComplexMatrix2.hermitianTraceless)
    (t : ℝ) (b : Edge L n k j) :
    PeriodicLattice.expTwist ((t : ℂ) • M) V b ∈ PeriodicLattice.compactGaugeGroup := by
  have hx : ∀ c : Edge L n k j, c.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • M c)) * V c ∈
        PeriodicLattice.compactGaugeGroup := fun c hc =>
    compact_mul_mem (matExp_I_smul_mem_compact (by
        rw [Complex.coe_smul]; exact ComplexMatrix2.hermitianTraceless.smul_mem t (hM c hc)))
      (hr.1 c (Set.mem_univ _))
  by_cases hb : b.IsPositivelyOriented
  · simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply]
    exact hx b hb
  · simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply]
    exact compact_inv_mem (hx _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb))
private theorem leftDifferential_mem [NeZero L] {V : Edge L n k j → ComplexMatrix2}
    (hr : V ∈ fieldSpace L n k j) {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented)
    (hl : meanRadius V b ≠ 0) {M : Edge L n k j → ComplexMatrix2}
    (hM : ∀ c : Edge L n k j, c.IsPositivelyOriented → M c ∈ ComplexMatrix2.hermitianTraceless) :
    leftDifferential normalizedMean V M b ∈ ComplexMatrix2.hermitianTraceless := by
  rw [leftDifferential_eq hd hr hb hl M]
  refine I_inv_smul_deriv_mem hd (hasDerivAt_relativeMean hr hl M) (relativeMean_zero hr hl M) ?_
  have hc := (contDiffAt_det (contDiffAt_contourMean
    (V := fun V : Edge L n k j → ComplexMatrix2 => V) (y₀ := V)
    (fun b' => (contDiff_apply ℝ ComplexMatrix2 b').contDiffAt)
    (isUnit_det_of_mem_fieldSpace hr) b)).continuousAt
  have ht : Tendsto (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • M) V) (𝓝 0) (𝓝 V) := by
    have h := (hasDerivAt_expTwist hr M).continuousAt.tendsto
    simp only [expTwist_zero hr] at h
    exact h
  have hne := (hc.tendsto.comp ht).eventually_ne (det_contourMean_ne_zero hl)
  filter_upwards [hne] with t h
  exact compact_mul_mem (normalized_mem_compactGaugeGroup
      (contourMean_mem_quaternionMatrices (expTwist_mem_compact hr hM t) b) h)
    (compact_inv_mem (normalizedMean_mem_compact hr hl))
private theorem exists_linear_leftDifferential [NeZero L] {V : Edge L n k j → ComplexMatrix2}
    (hr : V ∈ fieldSpace L n k j)
    (hl : ∀ c : PositiveEdge L n k (j + 1), meanRadius V c.1 ≠ 0) :
    ∃ G : (PositiveEdge L n k j → ComplexMatrix2) →ₗ[ℝ]
        (PositiveEdge L n k (j + 1) → ComplexMatrix2),
      ∀ (M : Edge L n k j → ComplexMatrix2) (c : PositiveEdge L n k (j + 1)),
        G (fun b => M b.1) c = leftDifferential normalizedMean V M c.1 := by
  refine ⟨{ toFun := fun f c => Complex.I⁻¹ •
              (meanDeriv V c.1 (twistVelocity V f) * (normalizedMean V c.1)⁻¹)
            map_add' := fun f g => ?_
            map_smul' := fun r f => ?_ }, fun M c => ?_⟩
  · funext c
    simp only [twistVelocity_add, map_add, add_mul, smul_add, Pi.add_apply]
  · funext c
    simp only [twistVelocity_smul, map_smul, RingHom.id_apply, Pi.smul_apply, smul_mul_assoc]
    rw [smul_comm]
  · exact (leftDifferential_eq hd hr c.2 (hl c) M).symm
end LeftChart
section TransportOfACompactPoint
variable {L n k : ℕ} [NeZero L]
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
include hd
private theorem exists_transport_step {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ}
    (h : j < k) :
    ∃ G : (PositiveEdge L n k j → ComplexMatrix2) →ₗ[ℝ]
        (PositiveEdge L n k (j + 1) → ComplexMatrix2),
      ∀ (ξ : LevelForms L n k) (c : PositiveEdge L n k (j + 1)),
        tangentTransport X ξ (j + 1) c.1 = G (fun b => tangentTransport X ξ j b.1) c +
          (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) c.1 := by
  obtain ⟨G, hG⟩ := exists_linear_leftDifferential hd (hX.2 j h.le)
    (fun c => meanRadius_ne_zero hX ⟨j, h⟩ c)
  refine ⟨{ toFun := fun f c => ComplexMatrix2.conjugateBy (X.noise ⟨j, h⟩ c) (G f c)
            map_add' := fun f g => ?_
            map_smul' := fun r f => ?_ }, fun ξ c => ?_⟩
  · funext c
    simp only [map_add, Pi.add_apply, conjugateBy_add]
  · funext c
    simp only [map_smul, RingHom.id_apply, Pi.smul_apply, conjugateBy_smul]
  · change _ = ComplexMatrix2.conjugateBy (X.noise ⟨j, h⟩ c)
      (G (fun b => tangentTransport X ξ j b.1) c) + _
    rw [hG (tangentTransport X ξ j) c, tangentTransport_succ_apply X ξ h c.2]
private theorem exists_linear_transport {X : ChainPoint L n k} (hX : IsCompactValued X) :
    ∀ j, j ≤ k → ∃ T : LevelForms L n k →ₗ[ℝ] (PositiveEdge L n k j → ComplexMatrix2),
      (∀ ξ c, T ξ c = tangentTransport X ξ j c.1) ∧
        ∀ (ξ : LevelForms L n k) (b : Edge L n k j), b.IsPositivelyOriented →
          tangentTransport X ξ j b ∈ ComplexMatrix2.hermitianTraceless := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨{ toFun := fun ξ c => (ξ.1 : Edge L n k 0 → ComplexMatrix2) c.1
             map_add' := fun _ _ => rfl
             map_smul' := fun _ _ => rfl }, fun _ _ => rfl, fun ξ b hb => ξ.1.2.1 b hb⟩
  | succ j ih =>
    intro hj
    have h : j < k := hj
    obtain ⟨T, hT, hsu⟩ := ih h.le
    obtain ⟨G, hG⟩ := exists_transport_step hd hX h
    have e : ∀ ξ, T ξ = fun b => tangentTransport X ξ j b.1 := fun ξ => funext (hT ξ)
    refine ⟨G ∘ₗ T +
      { toFun := fun ξ c => (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) c.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }, fun ξ c => ?_, fun ξ b hb => ?_⟩
    · rw [hG ξ c, ← e]
      rfl
    · rw [tangentTransport_succ_apply X ξ h hb]
      exact ComplexMatrix2.hermitianTraceless.add_mem
        (ComplexMatrix2.conjugateBy_mem_hermitianTraceless (hX.1 _ _) _
          (leftDifferential_mem hd (hX.2 j h.le) hb
          (meanRadius_ne_zero hX ⟨j, h⟩ ⟨b, hb⟩) (hsu ξ)))
        ((ξ.2 ⟨j, h⟩).2.1 b hb)
private theorem isTopDeriv_topDeriv {k : ℕ}
    (hxor : ∀ j, j ≤ k + 1 → ∀ b : Edge L n (k + 1) j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n (k + 1)} (hX : IsCompactValued X) :
    IsTopDeriv X (topDeriv X) := by
  obtain ⟨T, hT, hsu⟩ := exists_linear_transport hd hX (k + 1) le_rfl
  have hform : ∀ ξ, tangentTransport X ξ (k + 1) ∈ edgeFormSpace L n (k + 1) (k + 1) := fun ξ => by
    obtain ⟨f, hf⟩ : ∃ f, tangentTransport X ξ (k + 1) = extendOddly f := by
      simp only [tangentTransport, dif_pos (Nat.lt_succ_self k)]
      exact ⟨_, rfl⟩
    rw [hf]
    refine extendOddly_mem (hxor _ le_rfl) f fun b hb => ?_
    rw [← extendOddly_pos f hb, ← hf]
    exact hsu ξ b hb
  refine Classical.epsilon_spec (p := IsTopDeriv X) ⟨
    { toFun := fun ξ => ⟨tangentTransport X ξ (k + 1), hform ξ⟩
      map_add' := fun ξ ξ' => edgeForm_ext fun b hb => ?_
      map_smul' := fun r ξ => edgeForm_ext fun b hb => ?_ }, fun ξ => rfl⟩
  · have e : ∀ ξ, T ξ ⟨b, hb⟩ = tangentTransport X ξ (k + 1) b := fun ξ => hT ξ ⟨b, hb⟩
    change tangentTransport X (ξ + ξ') (k + 1) b =
      tangentTransport X ξ (k + 1) b + tangentTransport X ξ' (k + 1) b
    rw [← e, ← e, ← e, map_add]
    rfl
  · have e : ∀ ξ, T ξ ⟨b, hb⟩ = tangentTransport X ξ (k + 1) b := fun ξ => hT ξ ⟨b, hb⟩
    change tangentTransport X (r • ξ) (k + 1) b = r • tangentTransport X ξ (k + 1) b
    rw [← e, ← e, map_smul]
    rfl
end TransportOfACompactPoint
section LevelCoordinates
private theorem suTwoComponents_add (A B : ComplexMatrix2) :
    suTwoComponents (A + B) = suTwoComponents A + suTwoComponents B := by apply _root_.YangMills.SharedProofs.p37688 <;> assumption
private theorem suTwoComponents_smul (r : ℝ) (A : ComplexMatrix2) :
    suTwoComponents (r • A) = r • suTwoComponents A := by apply _root_.YangMills.SharedProofs.p5119 <;> assumption
private theorem eq_zero_of_suTwoComponents {B : ComplexMatrix2}
    (hB : B ∈ ComplexMatrix2.hermitianTraceless) (h : ∀ i, suTwoComponents B i = 0) :
    B = 0 := by
  obtain ⟨h1, h2⟩ := hB
  have h0 : (B 0 0).re = 0 := by simpa [suTwoComponents] using h 0
  have hi : (B 0 1).im = 0 := by simpa [suTwoComponents] using h 1
  have hr : (B 0 1).re = 0 := by simpa [suTwoComponents] using h 2
  have e00 := congrFun (congrFun h1 0) 0
  have e10 := congrFun (congrFun h1 1) 0
  simp only [Matrix.conjTranspose_apply] at e00 e10
  have b01 : B 0 1 = 0 := Complex.ext hr hi
  have b10 : B 1 0 = 0 := by rw [e10, b01, star_zero]
  have b00 : B 0 0 = 0 := by
    refine Complex.ext h0 ?_
    have := congrArg Complex.im e00
    simp at this
    simp only [Complex.zero_im]
    linarith
  have b11 : B 1 1 = 0 := by
    have : B 0 0 + B 1 1 = 0 := by
      simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using h2
    rw [b00, zero_add] at this
    exact this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [b00, b01, b10, b11]
private theorem torusSideBelow_eq (L s N : ℕ) : torusSideBelow L s N = N * L ^ s := by apply _root_.YangMills.SharedProofs.p41915 <;> assumption
variable {L n K : ℕ}
private theorem period_frameAtStep (j : Fin K) (i : Fin 4) :
    (frameAtStep L n K j).period (frameAtStep L n K j).depth i = 2 * L ^ (n + (K - j)) := by
  have hj := j.2
  have e : K - (j : ℕ) = (K - ((j : ℕ) + 1)) + 1 := by omega
  have h : (frameAtStep L n K j).period (frameAtStep L n K j).depth i =
      torusSideBelow L (K - ((j : ℕ) + 1)) (2 * L ^ n) * L := by
    simp [BlockAverages.BlockFrame.period, frameAtStep, TorusFields.torusFrame, sideAtStep]
  rw [h, torusSideBelow_eq, e]
  ring
abbrev _root_.YangMills.SharedProofs.p118180 := @period_frameAtStep
private def extendByZero (j : ℕ) :
    (PositiveEdge L n K j → ComplexMatrix2) →ₗ[ℝ] (Edge L n K j → ComplexMatrix2) where
  toFun f := open Classical in fun b => if hb : b.IsPositivelyOriented then f ⟨b, hb⟩ else 0
  map_add' f g := by
    funext b
    by_cases hb : b.IsPositivelyOriented <;> simp [hb]
  map_smul' r f := by
    funext b
    by_cases hb : b.IsPositivelyOriented <;> simp [hb]
private theorem extendByZero_pos {j : ℕ} (f : PositiveEdge L n K j → ComplexMatrix2)
    {b : Edge L n K j} (hb : b.IsPositivelyOriented) : extendByZero j f b = f ⟨b, hb⟩ := by
  simp [extendByZero, hb]
private def levelCoordsLinear (j : Fin K) :
    (Edge L n K j → ComplexMatrix2) →ₗ[ℝ] (LevelCoord (frameAtStep L n K j) → ℝ) where
  toFun := levelCoords j
  map_add' A B := by
    funext e
    rcases e with i | i <;> simp [levelCoords, suTwoComponents_add]
  map_smul' r A := by
    funext e
    rcases e with i | i <;> simp [levelCoords, suTwoComponents_smul]
variable (hPB : FramePositiveEdgesBijective) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
include hPB hL hn
private theorem levelCoords_congr (j : Fin K) {B B' : Edge L n K j → ComplexMatrix2}
    (h : ∀ c : Edge L n K j, c.IsPositivelyOriented → B c = B' c) :
    levelCoords j B = levelCoords j B' := by
  have hpos := (hPB L hL n K j hn j.2.le (frameAtStep L n K j) (frameAtStep L n K j).depth
    (period_frameAtStep j)).1
  funext e
  rcases e with i | i <;> simp only [levelCoords, h _ (hpos _)]
private theorem eq_zero_of_levelCoords [NeZero L] (j : Fin K) {B : Edge L n K j → ComplexMatrix2}
    (hB : ∀ c : Edge L n K j, c.IsPositivelyOriented → B c ∈ ComplexMatrix2.hermitianTraceless)
    (h : levelCoords j B = 0) :
    ∀ c : Edge L n K j, c.IsPositivelyOriented → B c = 0 := by
  classical
  intro c hc
  obtain ⟨b, rfl⟩ := (hPB L hL n K j hn j.2.le (frameAtStep L n K j) (frameAtStep L n K j).depth
    (period_frameAtStep j)).2.2 c hc
  have hodd : Odd (frameAtStep L n K j).blockSide := hL.1
  have hpos : ∀ i, 0 < (frameAtStep L n K j).extent i := fun i => by
    change 0 < sideAtStep L n K j
    rw [sideAtStep, torusSideBelow_eq]
    have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hS : ∀ x : (frameAtStep L n K j).Site (frameAtStep L n K j).depth,
      x ∈ BlockAverages.sitesOfCells (ColdStepAtMirrorFrames.finiteCells (frameAtStep L n K j))
        (frameAtStep L n K j).depth := fun x =>
    FrameTorusAction.mem_sitesOfCells_of_forall_mem hodd hpos
      (FrameTorusAction.mem_finiteCells _ hpos) x
  have hb : b ∈ BlockAverages.innerBonds
      (ColdStepAtMirrorFrames.finiteCells (frameAtStep L n K j)) (frameAtStep L n K j).depth :=
    Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hS _, Finset.mem_univ _⟩, hS _⟩
  refine eq_zero_of_suTwoComponents (hB _ hc) fun i => ?_
  by_cases ht : BlockAverages.IsAxialTreeBond b
  · have hm : b ∈ treeEdges (frameAtStep L n K j) := Finset.mem_filter.2 ⟨hb, ht⟩
    exact congrFun h (.inr (⟨b, hm⟩, i))
  · have hm : b ∈ BlockAverages.chordBonds
        (ColdStepAtMirrorFrames.finiteCells (frameAtStep L n K j)) :=
      Finset.mem_filter.2 ⟨hb, ht⟩
    exact congrFun h (.inl (⟨b, hm⟩, i))
end LevelCoordinates
section Triangularity
private theorem exists_factor_of_ker_le {E F G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G] (φ : E →ₗ[ℝ] F) (ψ : E →ₗ[ℝ] G)
    (h : LinearMap.ker φ ≤ LinearMap.ker ψ) : ∃ A : F →ₗ[ℝ] G, ∀ x, A (φ x) = ψ x := by
  obtain ⟨A, hA⟩ := LinearMap.exists_extend
    (((LinearMap.ker φ).liftQ ψ h) ∘ₗ φ.quotKerEquivRange.symm.toLinearMap)
  refine ⟨A, fun x => ?_⟩
  have h1 := LinearMap.congr_fun hA ⟨φ x, LinearMap.mem_range_self φ x⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image] at h1
  rw [h1]
  simp
variable {L n K : ℕ} [NeZero L]
private theorem exists_levelCoords_step
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hPB : FramePositiveEdgesBijective) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {X : ChainPoint L n K} (hX : IsCompactValued X) (j : ℕ) (h : j + 1 < K) :
    ∃ A : (LevelCoord (frameAtStep L n K j) → ℝ) →ₗ[ℝ]
        (LevelCoord (frameAtStep L n K (j + 1)) → ℝ),
      ∀ ξ : LevelForms L n K,
        levelCoords (⟨j + 1, h⟩ : Fin K) (tangentTransport X ξ (j + 1)) =
          A (levelCoords (⟨j, by omega⟩ : Fin K) (tangentTransport X ξ j)) +
            levelCoords (⟨j + 1, h⟩ : Fin K)
              (ξ.2 ⟨j, by omega⟩ : Edge L n K (j + 1) → ComplexMatrix2) := by
  have hj : j < K := by omega
  obtain ⟨T, hT, hsu⟩ := exists_linear_transport hd hX j hj.le
  obtain ⟨G, hG⟩ := exists_transport_step hd hX hj
  have eT : ∀ ξ, T ξ = fun b => tangentTransport X ξ j b.1 := fun ξ => funext (hT ξ)
  have hφ : ∀ ξ, (levelCoordsLinear (⟨j, hj⟩ : Fin K) ∘ₗ extendByZero j ∘ₗ T) ξ =
      levelCoords (⟨j, hj⟩ : Fin K) (tangentTransport X ξ j) := fun ξ =>
    levelCoords_congr hPB hL hn (⟨j, hj⟩ : Fin K) fun c hc => by
      change extendByZero j (T ξ) c = _
      rw [extendByZero_pos _ hc, hT ξ ⟨c, hc⟩]
  obtain ⟨A, hA⟩ := exists_factor_of_ker_le
    (levelCoordsLinear (⟨j, hj⟩ : Fin K) ∘ₗ extendByZero j ∘ₗ T)
    (levelCoordsLinear (⟨j + 1, h⟩ : Fin K) ∘ₗ extendByZero (j + 1) ∘ₗ G ∘ₗ T) (fun ξ hξ => by
      have h0 : levelCoords (⟨j, hj⟩ : Fin K) (tangentTransport X ξ j) = 0 := by
        rw [← hφ ξ]
        exact hξ
      have hz := eq_zero_of_levelCoords hPB hL hn (⟨j, hj⟩ : Fin K) (hsu ξ) h0
      have hT0 : T ξ = 0 := by
        funext c
        rw [hT ξ c]
        exact hz c.1 c.2
      simp [LinearMap.mem_ker, hT0])
  refine ⟨A, fun ξ => ?_⟩
  rw [← hφ ξ, hA ξ]
  have e : levelCoords (⟨j + 1, h⟩ : Fin K) (tangentTransport X ξ (j + 1)) =
      levelCoords (⟨j + 1, h⟩ : Fin K) (extendByZero (j + 1) (G (T ξ)) +
        (ξ.2 ⟨j, hj⟩ : Edge L n K (j + 1) → ComplexMatrix2)) :=
    levelCoords_congr hPB hL hn (⟨j + 1, h⟩ : Fin K) fun c hc => by
      have h1 := hG ξ ⟨c, hc⟩
      rw [← eT ξ] at h1
      rw [Pi.add_apply, extendByZero_pos _ hc]
      exact h1
  rw [e]
  exact (levelCoordsLinear (⟨j + 1, h⟩ : Fin K)).map_add _ _
private def shiftDown (A : ∀ (j : ℕ) (_ : j + 1 < K), (LevelCoord (frameAtStep L n K j) → ℝ) →ₗ[ℝ]
      (LevelCoord (frameAtStep L n K (j + 1)) → ℝ)) (y : ChainCoord L n K → ℝ) :
    ChainCoord L n K → ℝ
  | ⟨⟨0, _⟩, _⟩ => 0
  | ⟨⟨j + 1, h⟩, e⟩ => A j h (fun e' => y ⟨⟨j, by omega⟩, e'⟩) e
private def shiftDownLinear
    (A : ∀ (j : ℕ) (_ : j + 1 < K), (LevelCoord (frameAtStep L n K j) → ℝ) →ₗ[ℝ]
      (LevelCoord (frameAtStep L n K (j + 1)) → ℝ)) :
    (ChainCoord L n K → ℝ) →ₗ[ℝ] (ChainCoord L n K → ℝ) where
  toFun := shiftDown A
  map_add' y y' := by
    funext e
    rcases e with ⟨⟨_ | j, h⟩, e⟩
    · simp [shiftDown]
    · exact congrFun ((A j h).map_add (fun e' => y ⟨⟨j, by omega⟩, e'⟩)
        (fun e' => y' ⟨⟨j, by omega⟩, e'⟩)) e
  map_smul' r y := by
    funext e
    rcases e with ⟨⟨_ | j, h⟩, e⟩
    · simp [shiftDown]
    · exact congrFun ((A j h).map_smul r (fun e' => y ⟨⟨j, by omega⟩, e'⟩)) e
end Triangularity
end TransportTriangular
open TransportTriangular in
theorem transportCoordsTriangular_holds
    (hd : Matrices.ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hPB : FramePositiveEdgesBijective) :
    TransportCoordsTriangular := by
  classical
  intro L hL k n hn X hX
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hxor : ∀ j, j ≤ k + 1 → ∀ b : Tower.Edge L n (k + 1) j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := xor_opposite hb hL hn
  choose A hA using fun (j : ℕ) (h : j + 1 < k + 1) =>
    exists_levelCoords_step hd hPB hL hn hX j h
  refine ⟨LinearMap.toMatrix' (shiftDownLinear A), fun e e' hle => ?_, fun ξ => ?_,
    fun ξ hs => ?_⟩
  · rw [LinearMap.toMatrix'_apply]
    rcases e with ⟨⟨_ | j, h⟩, e⟩
    · rfl
    · have hz : (fun e'' => (Pi.single e' (1 : ℝ) : ChainCoord L n (k + 1) → ℝ)
          ⟨⟨j, by omega⟩, e''⟩) = 0 := by
        funext e''
        refine Pi.single_eq_of_ne ?_ _
        intro he
        have h2 : j + 1 ≤ coordLevel e' := hle
        rw [← he] at h2
        have h3 : j + 1 ≤ j := h2
        omega
      change A j h _ e = 0
      rw [hz, map_zero]
      rfl
  · rw [LinearMap.toMatrix'_mulVec]
    funext e
    rcases e with ⟨⟨_ | j, h⟩, e⟩
    · change _ = levelCoords _ (tangentTransport X ξ 0) e - 0
      rw [sub_zero]
      rfl
    · have h1 := congrFun (hA j h ξ) e
      change levelCoords _
          (ξ.2 ⟨j, by omega⟩ : Tower.Edge L n (k + 1) (j + 1) → Matrices.ComplexMatrix2) e =
        levelCoords (⟨j + 1, h⟩ : Fin (k + 1)) (tangentTransport X ξ (j + 1)) e -
          A j h (levelCoords (⟨j, by omega⟩ : Fin (k + 1)) (tangentTransport X ξ j)) e
      rw [h1, Pi.add_apply]
      ring
  · have hy : ∀ j (h : j < k + 1),
        levelCoords (⟨j, h⟩ : Fin (k + 1)) (tangentTransport X ξ j) = 0 := by
      intro j
      induction j with
      | zero =>
        intro h
        funext e
        exact congrFun hs ⟨⟨0, h⟩, e⟩
      | succ j ih =>
        intro h
        rw [hA j h ξ, ih (by omega), map_zero, zero_add]
        funext e
        exact congrFun hs ⟨⟨j + 1, h⟩, e⟩
    obtain ⟨T, hT, hsu⟩ := exists_linear_transport hd hX k (by omega)
    obtain ⟨G, hG⟩ := exists_transport_step hd hX (Nat.lt_succ_self k)
    have hz := eq_zero_of_levelCoords hPB hL hn (⟨k, by omega⟩ : Fin (k + 1)) (hsu ξ)
      (hy k (by omega))
    have hspec := isTopDeriv_topDeriv hd hxor hX ξ
    refine edgeForm_ext fun c hc => ?_
    rw [hspec]
    have h1 := hG ξ ⟨c, hc⟩
    have e0 : (fun b : Tower.PositiveEdge L n (k + 1) k => tangentTransport X ξ k b.1) = 0 := by
      funext b
      exact hz b.1 b.2
    rw [e0, map_zero, Pi.zero_apply, zero_add] at h1
    exact h1
end YangMills.Construction.RunningCouplingSlope
end
