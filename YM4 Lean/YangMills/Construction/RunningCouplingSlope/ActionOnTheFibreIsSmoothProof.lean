import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreIsSmooth
import YangMills.Construction.RunningCouplingSlope.FlatPointIsLeast
import YangMills.Construction.RunningCouplingSlope.TheMovementsOfTheChainReadNearCellsProof
import Mathlib
import YangMills.Construction.Matrices.SpecialUnitaryTwo
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.ChainActionFibreSmooth
open Filter Tower Matrices
open scoped Topology
section Smooth
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
private theorem contDiff_entry (i j : Fin 2) : ContDiff ℝ 2 (fun M : ComplexMatrix2 => M i j) :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j :
    ComplexMatrix2 →ₗ[ℝ] ℂ)).contDiff
abbrev _root_.YangMills.SharedProofs.p27324 := @contDiff_entry
private theorem contDiffAt_det {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀) :
    ContDiffAt ℝ 2 (fun y => (f y).det) y₀ := by
  have hent : ∀ i j, ContDiffAt ℝ 2 (fun y => f y i j) y₀ := fun i j =>
    (contDiff_entry i j).contDiffAt.comp y₀ hf
  simp only [Matrix.det_fin_two]
  exact ((hent 0 0).mul (hent 1 1)).sub ((hent 0 1).mul (hent 1 0))
abbrev _root_.YangMills.SharedProofs.p38879 := @contDiffAt_det
private theorem contDiffAt_matInv {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀)
    (hu : IsUnit (f y₀).det) :
    ContDiffAt ℝ 2 (fun y => (f y)⁻¹) y₀ := by
  have hunit : IsUnit (f y₀) := (Matrix.isUnit_iff_isUnit_det _).2 hu
  obtain ⟨u, hfu⟩ := hunit
  have hinv : ContDiffAt ℝ 2 Ring.inverse (f y₀) := by
    rw [← hfu]
    exact contDiffAt_ringInverse ℝ u
  have hcomp := hinv.comp y₀ hf
  refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [Matrix.nonsing_inv_eq_ringInverse]
abbrev _root_.YangMills.SharedProofs.p22704 := @contDiffAt_matInv
private theorem contDiffAt_scalar_smul {f : Y → ℂ} {g : Y → ComplexMatrix2}
    (hf : ContDiffAt ℝ 2 f y₀) (hg : ContDiffAt ℝ 2 g y₀) :
    ContDiffAt ℝ 2 (fun y => f y • g y) y₀ := by
  have hbil : ContDiff ℝ 2 (fun p : ℂ × ComplexMatrix2 => p.1 • p.2) :=
    (ContinuousLinearMap.lsmul ℝ ℂ :
      ℂ →L[ℝ] ComplexMatrix2 →L[ℝ] ComplexMatrix2).isBoundedBilinearMap.contDiff
  exact hbil.contDiffAt.comp y₀ (hf.prodMk hg)
abbrev _root_.YangMills.SharedProofs.p3257 := @contDiffAt_scalar_smul
private theorem contDiffAt_sqrt {f : Y → ℂ} (hf : ContDiffAt ℝ 2 f y₀)
    (hs : f y₀ ∈ Complex.slitPlane) :
    ContDiffAt ℝ 2 (fun y => f y ^ (1 / 2 : ℂ)) y₀ := by
  have hexp : ContDiffAt ℂ 2 (fun z : ℂ => Complex.exp (Complex.log z * (1 / 2 : ℂ))) (f y₀) :=
    Complex.contDiff_exp.contDiffAt.comp _
      ((Complex.contDiffAt_log hs).mul contDiffAt_const)
  have hpow : ContDiffAt ℝ 2 (fun z : ℂ => z ^ (1 / 2 : ℂ)) (f y₀) := by
    refine (hexp.restrict_scalars ℝ).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_ne (x := (0 : ℂ))).mem_nhds (Complex.slitPlane_ne_zero hs)] with z hz
    rw [Complex.cpow_def_of_ne_zero hz]
  exact hpow.comp y₀ hf
abbrev _root_.YangMills.SharedProofs.p3856 := @contDiffAt_sqrt
variable {L n k j : ℕ}
private theorem contDiffAt_pathHolonomy {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (γ : List (Edge L n k j)) :
    ContDiffAt ℝ 2 (fun y => PeriodicLattice.pathHolonomy (V y) γ) y₀ := by
  induction γ with
  | nil => simpa [PeriodicLattice.pathHolonomy] using contDiffAt_const
  | cons b γ ih =>
    simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons] at ih ⊢
    exact (hV b).mul ih
abbrev _root_.YangMills.SharedProofs.p6652 := @contDiffAt_pathHolonomy
private theorem isUnit_det_pathHolonomy {V : Edge L n k j → ComplexMatrix2}
    (hu : ∀ b, IsUnit (V b).det) (γ : List (Edge L n k j)) :
    IsUnit (PeriodicLattice.pathHolonomy V γ).det := by
  induction γ with
  | nil => simp [PeriodicLattice.pathHolonomy]
  | cons b γ ih =>
    simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons, Matrix.det_mul] at ih ⊢
    exact (hu b).mul ih
private theorem contDiffAt_contourMean [NeZero L] {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Edge L n k (j + 1)) : ContDiffAt ℝ 2 (fun y => contourMean (V y) c) y₀ := by
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  simp only [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine ContDiffAt.const_smul _ (ContDiffAt.sum fun x _ => ContDiffAt.sum fun π _ => ?_)
  simp only [contourHolonomy]
  exact ((contDiffAt_pathHolonomy hV _).mul (contDiffAt_pathHolonomy hV _)).mul
    (contDiffAt_matInv (contDiffAt_pathHolonomy hV _) (isUnit_det_pathHolonomy hu _))
abbrev _root_.YangMills.SharedProofs.p1840 := @contDiffAt_contourMean
private theorem contDiffAt_meanRadius [NeZero L] {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Edge L n k (j + 1)) (hs : (contourMean (V y₀) c).det ∈ Complex.slitPlane) :
    ContDiffAt ℝ 2 (fun y => meanRadius (V y) c) y₀ :=
  contDiffAt_sqrt (contDiffAt_det (contDiffAt_contourMean hV hu c)) hs
private theorem contDiffAt_normalizedMean [NeZero L] {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Edge L n k (j + 1)) (hs : (contourMean (V y₀) c).det ∈ Complex.slitPlane)
    (hr : meanRadius (V y₀) c ≠ 0) :
    ContDiffAt ℝ 2 (fun y => normalizedMean (V y) c) y₀ :=
  contDiffAt_scalar_smul ((contDiffAt_meanRadius hV hu c hs).inv hr) (contDiffAt_contourMean hV hu c)
end Smooth
section Quaternions
private def quaternionSpan : Submodule ℝ ComplexMatrix2 where
  carrier := {M | M 1 1 = star (M 0 0) ∧ M 1 0 = -star (M 0 1)}
  add_mem' := by
    rintro A B ⟨hA₁, hA₂⟩ ⟨hB₁, hB₂⟩
    refine ⟨?_, ?_⟩
    · simp [Matrix.add_apply, hA₁, hB₁]
    · simp only [Matrix.add_apply, hA₂, hB₂, star_add]; ring
  zero_mem' := by simp
  smul_mem' := by
    rintro c A ⟨hA₁, hA₂⟩
    refine ⟨?_, ?_⟩
    · simp [Matrix.smul_apply, hA₁]
    · simp [Matrix.smul_apply, hA₂]
private theorem mem_quaternionSpan_of_mem_compact {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : g ∈ quaternionSpan :=
  ComplexMatrix2.quaternion_entries_of_mem_specialUnitary hg
private theorem det_eq_normSq_of_mem {M : ComplexMatrix2} (hM : M ∈ quaternionSpan) :
    M.det = ((Complex.normSq (M 0 0) + Complex.normSq (M 0 1) : ℝ) : ℂ) :=
  ComplexMatrix2.det_quaternionMatrix hM
private theorem det_mem_slitPlane_of_mem {M : ComplexMatrix2} (hM : M ∈ quaternionSpan)
    (h : M.det ≠ 0) : M.det ∈ Complex.slitPlane :=
  ComplexMatrix2.det_quaternionMatrix_mem_slitPlane hM h
variable {L n k j : ℕ}
private theorem compact_mul_mem {g h : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hh : h ∈ PeriodicLattice.compactGaugeGroup) : g * h ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
private theorem compact_inv_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem det_eq_one_of_compact {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : g.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
private theorem isUnit_det_of_compact {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem pathHolonomy_mem_compact {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) (γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy V γ ∈ PeriodicLattice.compactGaugeGroup := by
  induction γ with
  | nil => simp [PeriodicLattice.pathHolonomy]
  | cons b γ ih =>
    simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons] at ih ⊢
    exact compact_mul_mem (hV b) ih
abbrev _root_.YangMills.SharedProofs.p6330 := @pathHolonomy_mem_compact
private theorem contourMean_mem_quaternionSpan [NeZero L] {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) (c : Edge L n k (j + 1)) :
    contourMean V c ∈ quaternionSpan := by
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  have hw : ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) =
      (((1 / 24 : ℝ) * ((L : ℝ) ^ (-4 : ℤ)) : ℝ) : ℂ) := by
    simp [PeriodicLattice.inverseFourthPowerWeight]
  rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin, hw, Complex.coe_smul]
  refine quaternionSpan.smul_mem _
    (quaternionSpan.sum_mem fun x _ => quaternionSpan.sum_mem fun π _ => ?_)
  exact mem_quaternionSpan_of_mem_compact (compact_mul_mem
    (compact_mul_mem (pathHolonomy_mem_compact hV _) (pathHolonomy_mem_compact hV _))
    (compact_inv_mem (pathHolonomy_mem_compact hV _)))
end Quaternions
section Values
variable {L n k j : ℕ}
private theorem fieldOfPositiveValues_of_not_pos (w : PositiveEdge L n k j → ComplexMatrix2)
    {b : Edge L n k j} (h : ¬b.IsPositivelyOriented) :
    fieldOfPositiveValues w b =
      (w ⟨b.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented h⟩)⁻¹ := by
  simp [fieldOfPositiveValues, h, PeriodicLattice.Bond.opposite_isPositivelyOriented h]
end Values
section Levels
variable {L n k : ℕ}
private theorem levelField_succ (X : ChainPoint L n k) {j : ℕ} (h : j < k) :
    levelField X (j + 1) =
      fieldOfPositiveValues fun c => X.noise ⟨j, h⟩ c * normalizedMean (levelField X j) c.1 := by
  simp [levelField, h]
private theorem levelField_succ_of_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
private theorem levelField_succ_of_not_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : ¬b.IsPositivelyOriented) :
    levelField X (j + 1) b = (levelField X (j + 1) b.opposite)⁻¹ := by
  rw [levelField_succ_of_pos X h (PeriodicLattice.Bond.opposite_isPositivelyOriented hb),
    levelField_succ X h, fieldOfPositiveValues_of_not_pos _ hb]
abbrev _root_.YangMills.SharedProofs.p5483 := @levelField_succ_of_not_pos
private theorem meanRadius_ne_zero {X : ChainPoint L n k} (hX : IsCompactValued X) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) : meanRadius (levelField X i) c.1 ≠ 0 := by
  intro h0
  have hm := (hX.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)
  rw [levelField_succ_of_pos X i.2 c.2] at hm
  have hz : normalizedMean (levelField X i) c.1 = 0 := by
    simp [normalizedMean, h0]
  rw [hz, mul_zero] at hm
  have := det_eq_one_of_compact hm
  simp at this
abbrev _root_.YangMills.SharedProofs.p17043 := @meanRadius_ne_zero
private theorem det_contourMean_ne_zero {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    {c : Edge L n k (j + 1)} (h : meanRadius V c ≠ 0) :
    (contourMean V c).det ≠ 0 := by
  intro h0
  apply h
  rw [meanRadius, h0]
  simp
abbrev _root_.YangMills.SharedProofs.p15699 := @det_contourMean_ne_zero
end Levels
section Families
variable {L n k : ℕ} [NeZero L] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
  {Z : Y → ChainPoint L n k}
private theorem contDiffAt_fullTrace {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀) :
    ContDiffAt ℝ 2 (fun y => ComplexMatrix2.fullTrace (f y)) y₀ := by
  have hent : ∀ i j, ContDiffAt ℝ 2 (fun y => f y i j) y₀ := fun i j =>
    (contDiff_entry i j).contDiffAt.comp y₀ hf
  simp only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
  exact (hent 0 0).add (hent 1 1)
private theorem contDiffAt_re {f : Y → ℂ} (hf : ContDiffAt ℝ 2 f y₀) :
    ContDiffAt ℝ 2 (fun y => (f y).re) y₀ :=
  Complex.reCLM.contDiff.contDiffAt.comp y₀ hf
private theorem isUnit_det_of_mem_fieldSpace {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (b : Edge L n k j) :
    IsUnit (V b).det := isUnit_det_of_compact (hV.1 b (Set.mem_univ b))
private theorem contDiffAt_levelField_of_pos (hX : IsCompactValued (Z y₀)) {j : ℕ} (h : j < k)
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => levelField (Z y) j b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) {b : Edge L n k (j + 1)}
    (hb : b.IsPositivelyOriented) :
    ContDiffAt ℝ 2 (fun y => levelField (Z y) (j + 1) b) y₀ := by
  have hr := hX.2 j h.le
  have hl := meanRadius_ne_zero hX ⟨j, h⟩ ⟨b, hb⟩
  have hs := det_mem_slitPlane_of_mem
    (contourMean_mem_quaternionSpan (fun b' => hr.1 b' (Set.mem_univ _)) b)
    (det_contourMean_ne_zero hl)
  simp only [levelField_succ_of_pos _ h hb]
  exact (hn _ _).mul (contDiffAt_normalizedMean hV (isUnit_det_of_mem_fieldSpace hr) b hs hl)
private theorem contDiffAt_levelField (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀)) :
    ∀ j, j ≤ k → ∀ b, ContDiffAt ℝ 2 (fun y => levelField (Z y) j b) y₀ := by
  intro j
  induction j with
  | zero => intro _ b; exact hb b
  | succ j ih =>
    intro hj b
    have h : j < k := hj
    have hV := ih h.le
    by_cases hbp : b.IsPositivelyOriented
    · exact contDiffAt_levelField_of_pos hX h hV hn hbp
    · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hbp
      simp only [levelField_succ_of_not_pos _ h hbp]
      exact contDiffAt_matInv (contDiffAt_levelField_of_pos hX h hV hn hp)
        (isUnit_det_of_mem_fieldSpace (hX.2 (j + 1) hj) _)
abbrev _root_.YangMills.SharedProofs.p4722 := @contDiffAt_levelField
private theorem contDiffAt_meanRadius_levelField
    (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀))
    (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun y => meanRadius (levelField (Z y) i) c.1) y₀ := by
  have hr := hX.2 i i.2.le
  exact contDiffAt_meanRadius (contDiffAt_levelField hb hn hX i i.2.le)
    (isUnit_det_of_mem_fieldSpace hr) c.1
    (det_mem_slitPlane_of_mem
      (contourMean_mem_quaternionSpan (fun b' => hr.1 b' (Set.mem_univ _)) c.1)
      (det_contourMean_ne_zero (meanRadius_ne_zero hX i c)))
abbrev _root_.YangMills.SharedProofs.p8907 := @contDiffAt_meanRadius_levelField
private theorem finite_face (j : ℕ) : Finite (Face L n k j) :=
  Finite.of_injective
    (fun p : Face L n k j => (p.origin, p.firstAxis, p.secondAxis)) fun _ _ h =>
    PeriodicLattice.Plaquette.ext (congrArg Prod.fst h) (congrArg (fun y => y.2.1) h)
      (congrArg (fun y => y.2.2) h)
abbrev _root_.YangMills.SharedProofs.p23234 := @finite_face
private theorem contDiffAt_plaquetteAction {U : Y → Edge L n k 0 → ComplexMatrix2}
    (hU : ∀ b, ContDiffAt ℝ 2 (fun y => U y b) y₀) :
    ContDiffAt ℝ 2 (fun y => plaquetteAction L n k (U y)) y₀ := by
  haveI := finite_face (L := L) (n := n) (k := k) 0
  haveI : Fintype (Face L n k 0) := Fintype.ofFinite _
  simp only [plaquetteAction, PeriodicLattice.wilsonAction, finsum_eq_sum_of_fintype]
  refine ContDiffAt.sum fun p _ => ?_
  simp only [PeriodicLattice.plaquetteCost]
  exact contDiffAt_const.sub (contDiffAt_const.mul
    (contDiffAt_re (contDiffAt_fullTrace (contDiffAt_pathHolonomy hU _))))
private theorem contDiffAt_traceDefect {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀) :
    ContDiffAt ℝ 2 (fun y => traceDefect (f y)) y₀ := by
  simp only [traceDefect, ComplexMatrix2.halfTrace]
  exact contDiffAt_const.sub (contDiffAt_re (contDiffAt_const.mul (contDiffAt_fullTrace hf)))
private theorem contDiffAt_chainAction (a : ℝ) (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀)) :
    ContDiffAt ℝ 2 (fun y => chainAction a (Z y)) y₀ := by
  simp only [chainAction]
  refine (contDiffAt_plaquetteAction hb).add (contDiffAt_const.mul (ContDiffAt.sum fun i _ => ?_))
  haveI : Fintype (PositiveEdge L n k (i + 1)) := Fintype.ofFinite _
  simp only [finsum_eq_sum_of_fintype]
  exact ContDiffAt.sum fun c _ =>
    (contDiffAt_re (contDiffAt_meanRadius_levelField hb hn hX i c)).mul
      (contDiffAt_traceDefect (hn i c))
abbrev _root_.YangMills.SharedProofs.p6648 := @contDiffAt_chainAction
end Families
section Fibre
variable {L n k : ℕ} [NeZero L] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
private theorem contDiffAt_matExp {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀) :
    ContDiffAt ℝ 2 (fun y => ComplexMatrix2.matExp (f y)) y₀ :=
  ((NormedSpace.exp_analytic (𝕂 := ℝ) (f y₀)).contDiffAt (n := 2)).comp y₀ hf
private theorem matExp_mul_matExp_neg (A : ComplexMatrix2) :
    ComplexMatrix2.matExp A * ComplexMatrix2.matExp (-A) = 1 := by apply _root_.YangMills.Construction.SpinHarmonics.matExp_mul_matExp_neg <;> assumption
private theorem isUnit_det_matExp (A : ComplexMatrix2) : IsUnit (ComplexMatrix2.matExp A).det := by
  have h := congrArg Matrix.det (matExp_mul_matExp_neg A)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one _ h
private theorem matExp_I_smul_zero :
    ComplexMatrix2.matExp (Complex.I • (0 : ComplexMatrix2)) = 1 := by
  rw [smul_zero, ComplexMatrix2.matExp]
  exact NormedSpace.exp_zero
private theorem contDiffAt_fine_form [FiniteDimensional ℝ Y] (l : Y →ₗ[ℝ] LevelForms L n k)
    (b : Edge L n k 0) :
    ContDiffAt ℝ 2 (fun y => ((l y).1 : Edge L n k 0 → ComplexMatrix2) b) y₀ := by
  let g : Y →ₗ[ℝ] ComplexMatrix2 :=
    { toFun := fun y => ((l y).1 : Edge L n k 0 → ComplexMatrix2) b
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
  exact (LinearMap.toContinuousLinearMap g).contDiff.contDiffAt
private theorem contDiffAt_noise_form [FiniteDimensional ℝ Y] (l : Y →ₗ[ℝ] LevelForms L n k)
    (i : Fin k) (c : Edge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun y => ((l y).2 i : Edge L n k (i + 1) → ComplexMatrix2) c) y₀ := by
  let g : Y →ₗ[ℝ] ComplexMatrix2 :=
    { toFun := fun y => ((l y).2 i : Edge L n k (i + 1) → ComplexMatrix2) c
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
  exact (LinearMap.toContinuousLinearMap g).contDiff.contDiffAt
abbrev _root_.YangMills.SharedProofs.p38354 := @contDiffAt_noise_form
private theorem contDiffAt_expMove_fine [FiniteDimensional ℝ Y] (l : Y →ₗ[ℝ] LevelForms L n k)
    {Z : Y → ChainPoint L n k} (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hu : ∀ b, IsUnit ((Z y₀).fine b).det) (b : Edge L n k 0) :
    ContDiffAt ℝ 2 (fun y => (expMove (l y) (Z y)).fine b) y₀ := by
  have hf : ∀ b' : Edge L n k 0, ContDiffAt ℝ 2
      (fun y => ComplexMatrix2.matExp (Complex.I • ((l y).1 : Edge L n k 0 → ComplexMatrix2) b') *
        (Z y).fine b') y₀ :=
    fun b' => (contDiffAt_matExp (contDiffAt_scalar_smul contDiffAt_const
      (contDiffAt_fine_form l b'))).mul (hb b')
  by_cases h : b.IsPositivelyOriented
  · simp only [expMove, PeriodicLattice.expTwist, if_pos h]
    exact hf b
  · simp only [expMove, PeriodicLattice.expTwist, if_neg h]
    refine contDiffAt_matInv (hf _) ?_
    rw [Matrix.det_mul]
    exact (isUnit_det_matExp _).mul (hu _)
abbrev _root_.YangMills.SharedProofs.p2871 := @contDiffAt_expMove_fine
private theorem contDiffAt_expMove_noise [FiniteDimensional ℝ Y] (l : Y →ₗ[ℝ] LevelForms L n k)
    {Z : Y → ChainPoint L n k} (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀)
    (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun y => (expMove (l y) (Z y)).noise i c) y₀ := by
  simp only [expMove]
  exact (contDiffAt_matExp (contDiffAt_scalar_smul contDiffAt_const
    (contDiffAt_noise_form l i c.1))).mul (hn i c)
private theorem expMove_zero_unitPoint :
    expMove (0 : LevelForms L n k) (unitPoint L n k) = unitPoint L n k := by
  simp only [expMove, unitPoint]
  congr 1
  · funext b
    by_cases h : b.IsPositivelyOriented
    · simp [PeriodicLattice.expTwist, h, matExp_I_smul_zero]
    · simp [PeriodicLattice.expTwist, h, matExp_I_smul_zero]
  · funext i c
    simp [matExp_I_smul_zero]
abbrev _root_.YangMills.SharedProofs.p62410 := @expMove_zero_unitPoint
private theorem normalizedMean_unitPoint (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    normalizedMean (levelField (unitPoint L n k) i) c.1 =
      levelField (unitPoint L n k) (i + 1) c.1 := by
  rw [levelField_succ_of_pos _ i.2 c.2]
  simp [unitPoint]
private theorem fibreMove_unitPoint_zero (hF : IsCompactValued (unitPoint L n k)) :
    fibreMove (unitPoint L n k) 0 = unitPoint L n k := by
  simp only [fibreMove, expMove_zero_unitPoint]
  congr 1
  funext i c
  split_ifs with h
  · rw [normalizedMean_unitPoint i c]
    have hr := (hF.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)
    exact Matrix.mul_nonsing_inv _ (isUnit_det_of_compact hr)
  · rfl
private theorem contDiffAt_chainAction_fibreMove [FiniteDimensional ℝ Y] (a : ℝ)
    (hF : IsCompactValued (unitPoint L n k)) (l₁ l₂ : Y →ₗ[ℝ] LevelForms L n k) :
    ContDiffAt ℝ 2
      (fun y => chainAction a (fibreMove (expMove (l₁ y) (unitPoint L n k)) (l₂ y))) (0 : Y) := by
  set P : Y → ChainPoint L n k := fun y => expMove (l₁ y) (unitPoint L n k) with hP
  set Q : Y → ChainPoint L n k := fun y => expMove (l₂ y) (P y) with hQ
  have hP0 : P 0 = unitPoint L n k := by simp only [hP, map_zero, expMove_zero_unitPoint]
  have hQ0 : Q 0 = unitPoint L n k := by simp only [hQ, hP0, map_zero, expMove_zero_unitPoint]
  have hZ0 : fibreMove (P 0) (l₂ 0) = unitPoint L n k := by
    rw [hP0, map_zero, fibreMove_unitPoint_zero hF]
  have hunit : ∀ b : Edge L n k 0, IsUnit ((unitPoint L n k).fine b).det := fun b => by
    simp [unitPoint]
  have hPb : ∀ b, ContDiffAt ℝ 2 (fun y => (P y).fine b) (0 : Y) := fun b =>
    contDiffAt_expMove_fine (Z := fun _ => unitPoint L n k) l₁ (fun _ => contDiffAt_const) hunit b
  have hPn : ∀ i c, ContDiffAt ℝ 2 (fun y => (P y).noise i c) (0 : Y) := fun i c =>
    contDiffAt_expMove_noise (Z := fun _ => unitPoint L n k) l₁ (fun _ _ => contDiffAt_const) i c
  have hQb : ∀ b, ContDiffAt ℝ 2 (fun y => (Q y).fine b) (0 : Y) := fun b =>
    contDiffAt_expMove_fine (Z := P) l₂ hPb (by rw [hP0]; exact hunit) b
  have hQn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Q y).noise i c) (0 : Y) := fun i c =>
    contDiffAt_expMove_noise (Z := P) l₂ hPn i c
  have hPr : IsCompactValued (P 0) := by rw [hP0]; exact hF
  have hQr : IsCompactValued (Q 0) := by rw [hQ0]; exact hF
  have hPf := contDiffAt_levelField hPb hPn hPr
  have hQf := contDiffAt_levelField hQb hQn hQr
  refine contDiffAt_chainAction (Z := fun y => fibreMove (P y) (l₂ y)) a hQb (fun i c => ?_)
    (by simp only [hZ0]; exact hF)
  by_cases h : i.val + 1 = k
  · simp only [fibreMove, if_pos h]
    have hr := hQr.2 i i.2.le
    have hl := meanRadius_ne_zero hQr i c
    have hs := det_mem_slitPlane_of_mem
      (contourMean_mem_quaternionSpan (fun b' => hr.1 b' (Set.mem_univ _)) c.1)
      (det_contourMean_ne_zero hl)
    refine (hPf (i + 1) i.2 c.1).mul (contDiffAt_matInv
      (contDiffAt_normalizedMean (hQf i i.2.le) (isUnit_det_of_mem_fieldSpace hr) c.1 hs hl) ?_)
    change IsUnit (Matrix.det (normalizedMean (levelField (Q 0) i) c.1))
    rw [hQ0, normalizedMean_unitPoint i c]
    exact isUnit_det_of_compact ((hF.2 (i + 1) i.2).1 c.1 (Set.mem_univ _))
  · simp only [fibreMove, if_neg h]
    exact hQn i c
end Fibre
theorem chainActionFibreContDiff_of_unitPointIsMinimizer (hMin : UnitPointIsMinimizer) :
    ChainActionFibreContDiff := by
  intro a L hL k n hk hn N e
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hF : IsCompactValued (unitPoint L n k) := (hMin 1 one_pos L hL k n hk hn).2.compact
  exact contDiffAt_chainAction_fibreMove a hF (e ∘ₗ LinearMap.fst ℝ (Fin N → ℝ) (Fin N → ℝ))
    (e ∘ₗ LinearMap.snd ℝ (Fin N → ℝ) (Fin N → ℝ))
end YangMills.Construction.RunningCouplingSlope.ChainActionFibreSmooth
end
