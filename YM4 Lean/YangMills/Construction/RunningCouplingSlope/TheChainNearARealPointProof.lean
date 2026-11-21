import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreUnderAGaugeFunctionProof
import YangMills.Construction.RunningCouplingSlope.DriftOfALeastPointIsLinearProof
import YangMills.Construction.RunningCouplingSlope.TheChainNearARealPoint
import Mathlib
import YangMills.Construction.Matrices.SpecialUnitaryTwo
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.CompactPointChain
open Filter Tower Matrices
open scoped Topology
section SecondOrder
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
theorem hasDerivAt_deriv_comp_two {Φ : E → F} {x : E} (hΦ : ContDiffAt ℝ 2 Φ x) {g : ℝ → ℝ → E}
    {v : ℝ → E} {u w : E} (hg0 : g 0 0 = x) (hv : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (g s) (v s) 0)
    (hu : HasDerivAt (fun s => g s 0) u 0) (hw : HasDerivAt v w 0) :
    HasDerivAt (fun s => deriv (fun t => Φ (g s t)) 0)
      (fderiv ℝ (fderiv ℝ Φ) x u (v 0) + fderiv ℝ Φ x w) 0 := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ Φ y :=
    (hΦ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hc : Tendsto (fun s => g s 0) (𝓝 0) (𝓝 x) := by
    have := hu.continuousAt.tendsto
    simpa [hg0] using this
  have heq : (fun s => deriv (fun t => Φ (g s t)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ Φ (g s 0) (v s) := by
    filter_upwards [hc.eventually hd, hv] with s h1 h2
    exact (h1.hasFDerivAt.comp_hasDerivAt 0 h2).deriv
  have hD : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) x) x :=
    ((hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hL : HasDerivAt (fun s => fderiv ℝ Φ (g s 0)) (fderiv ℝ (fderiv ℝ Φ) x u) 0 := by
    have h := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (f := fun s => g s 0)
      (l := fderiv ℝ Φ) (l' := fderiv ℝ (fderiv ℝ Φ) x) (f' := u) (by simpa [hg0] using hD) hu
    exact h
  have h3 := hL.clm_apply hw
  rw [hg0] at h3
  exact h3.congr_of_eventuallyEq heq
theorem hasDerivAt_deriv_line {Φ : E → F} (hΦ : ContDiffAt ℝ 2 Φ 0) (a b : E) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => Φ (s • a + t • b)) 0)
      (fderiv ℝ (fderiv ℝ Φ) 0 a b) 0 := by
  have h := hasDerivAt_deriv_comp_two (g := fun s t => s • a + t • b) (v := fun _ => b) (u := a)
    (w := 0) hΦ
    (by simp) (Eventually.of_forall fun s => by
      have h1 : HasDerivAt (fun t : ℝ => t • b) ((1 : ℝ) • b) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const b
      simpa using h1.const_add (s • a))
    (by
      have h1 : HasDerivAt (fun s : ℝ => s • a) ((1 : ℝ) • a) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const a
      simpa using h1)
    (hasDerivAt_const _ _)
  simpa using h
end SecondOrder
section LeftChart
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
def leftChart (x a : A) : A := NormedSpace.exp a * x
theorem contDiffAt_exp_two (a : A) : ContDiffAt ℝ 2 (NormedSpace.exp : A → A) a :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) a).contDiffAt
theorem contDiffAt_leftChart (x a : A) : ContDiffAt ℝ 2 (leftChart x) a :=
  (contDiffAt_exp_two a).mul contDiffAt_const
theorem leftChart_zero (x : A) : leftChart x 0 = x := by simp [leftChart]
theorem hasDerivAt_leftChart_line (x a : A) (s : ℝ) :
    HasDerivAt (fun t : ℝ => leftChart x ((s + t) • a))
      (NormedSpace.exp (s • a) * a * x) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) a s
  have h2 : HasDerivAt (fun t : ℝ => NormedSpace.exp ((s + t) • a))
      (NormedSpace.exp (s • a) * a) 0 := by
    have := HasDerivAt.comp_const_add (a := s) (x := (0 : ℝ))
      (f := fun u : ℝ => NormedSpace.exp (u • a)) (by simpa using h)
    simpa using this
  exact h2.mul_const x
variable {Φ : A → ℝ} {x : A}
end LeftChart
section SmoothMatrixMaps
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
theorem contDiffAt_det {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀) :
    ContDiffAt ℝ 2 (fun y => (f y).det) y₀ := by apply _root_.YangMills.SharedProofs.p38879 <;> assumption
theorem contDiffAt_inv {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀)
    (hu : IsUnit (f y₀).det) : ContDiffAt ℝ 2 (fun y => (f y)⁻¹) y₀ := by apply _root_.YangMills.SharedProofs.p22704 <;> assumption
theorem contDiffAt_cSmul {f : Y → ℂ} {g : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀)
    (hg : ContDiffAt ℝ 2 g y₀) : ContDiffAt ℝ 2 (fun y => f y • g y) y₀ := by apply _root_.YangMills.SharedProofs.p3257 <;> assumption
theorem contDiffAt_cpow_half {f : Y → ℂ} (hf : ContDiffAt ℝ 2 f y₀)
    (hs : f y₀ ∈ Complex.slitPlane) :
    ContDiffAt ℝ 2 (fun y => f y ^ (1 / 2 : ℂ)) y₀ := by apply _root_.YangMills.SharedProofs.p3856 <;> assumption
variable {L n k j : ℕ}
theorem contDiffAt_contourMean [NeZero L] {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Edge L n k (j + 1)) : ContDiffAt ℝ 2 (fun y => contourMean (V y) c) y₀ := by apply _root_.YangMills.SharedProofs.p1840 <;> assumption
theorem contDiffAt_meanRadius [NeZero L] {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Edge L n k (j + 1)) (hs : (contourMean (V y₀) c).det ∈ Complex.slitPlane) :
    ContDiffAt ℝ 2 (fun y => meanRadius (V y) c) y₀ :=
  contDiffAt_cpow_half (contDiffAt_det (contDiffAt_contourMean hV hu c)) hs
theorem contDiffAt_normalizedMean [NeZero L] {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Edge L n k (j + 1)) (hs : (contourMean (V y₀) c).det ∈ Complex.slitPlane)
    (hl : meanRadius (V y₀) c ≠ 0) :
    ContDiffAt ℝ 2 (fun y => normalizedMean (V y) c) y₀ :=
  contDiffAt_cSmul ((contDiffAt_meanRadius hV hu c hs).inv hl) (contDiffAt_contourMean hV hu c)
end SmoothMatrixMaps
section Quaternions
def quaternionMatrices : Submodule ℝ ComplexMatrix2 where
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
theorem mem_quaternionMatrices_of_compact {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : g ∈ quaternionMatrices :=
  ComplexMatrix2.quaternion_entries_of_mem_specialUnitary hg
theorem det_of_mem_quaternionMatrices {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices) :
    M.det = ((Complex.normSq (M 0 0) + Complex.normSq (M 0 1) : ℝ) : ℂ) :=
  ComplexMatrix2.det_quaternionMatrix hM
theorem det_mem_slitPlane_of_quaternion {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices)
    (h : M.det ≠ 0) : M.det ∈ Complex.slitPlane :=
  ComplexMatrix2.det_quaternionMatrix_mem_slitPlane hM h
theorem normalize_mem_compact {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices) (h : M.det ≠ 0) :
    (M.det ^ (1 / 2 : ℂ))⁻¹ • M ∈ PeriodicLattice.compactGaugeGroup :=
  ComplexMatrix2.normalize_quaternionMatrix_mem_specialUnitary hM h
variable {L n k j : ℕ}
theorem compact_mul_mem {g h : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hh : h ∈ PeriodicLattice.compactGaugeGroup) :
    g * h ∈ PeriodicLattice.compactGaugeGroup := Submonoid.mul_mem _ hg hh
theorem compact_inv_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem isUnit_det_of_compact {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem pathHolonomy_mem_compact {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy V Γ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p6330 <;> assumption
theorem contourMean_mem_quaternionMatrices [NeZero L] {V : Edge L n k j → ComplexMatrix2}
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
  exact mem_quaternionMatrices_of_compact (compact_mul_mem
    (compact_mul_mem (pathHolonomy_mem_compact hV _) (pathHolonomy_mem_compact hV _))
    (compact_inv_mem (pathHolonomy_mem_compact hV _)))
end Quaternions
section PositiveValues
variable {L n k j : ℕ}
theorem fieldOfPositiveValues_pos (w : PositiveEdge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) : fieldOfPositiveValues w b = w ⟨b, h⟩ := by
  simp [fieldOfPositiveValues, h]
theorem fieldOfPositiveValues_neg (w : PositiveEdge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : ¬b.IsPositivelyOriented) :
    fieldOfPositiveValues w b =
      (w ⟨b.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented h⟩)⁻¹ := by
  simp [fieldOfPositiveValues, h, PeriodicLattice.Bond.opposite_isPositivelyOriented h]
theorem fieldOfPositiveValues_mem {w : PositiveEdge L n k j → ComplexMatrix2}
    (hw : ∀ c, w c ∈ PeriodicLattice.compactGaugeGroup)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    fieldOfPositiveValues w ∈ fieldSpace L n k j := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.fieldOfPositiveValues_mem_fieldSpace <;> assumption
end PositiveValues
section LevelFields
variable {L n k : ℕ}
theorem levelField_succ_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k) {b : Edge L n k (j + 1)}
    (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
theorem levelField_succ_neg (X : ChainPoint L n k) {j : ℕ} (h : j < k) {b : Edge L n k (j + 1)}
    (hb : ¬b.IsPositivelyOriented) :
    levelField X (j + 1) b = (levelField X (j + 1) b.opposite)⁻¹ := by apply _root_.YangMills.SharedProofs.p5483 <;> assumption
theorem meanRadius_ne_zero {X : ChainPoint L n k} (hX : IsCompactValued X) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) : meanRadius (levelField X i) c.1 ≠ 0 := by apply _root_.YangMills.SharedProofs.p17043 <;> assumption
theorem det_contourMean_ne_zero {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    {c : Edge L n k (j + 1)} (h : meanRadius V c ≠ 0) : (contourMean V c).det ≠ 0 := by apply _root_.YangMills.SharedProofs.p15699 <;> assumption
end LevelFields
section SmoothFamilies
variable {L n k : ℕ} [NeZero L] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
  {Z : Y → ChainPoint L n k}
theorem isUnit_det_of_mem_fieldSpace {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (b : Edge L n k j) :
    IsUnit (V b).det := isUnit_det_of_compact (hV.1 b (Set.mem_univ b))
theorem contDiffAt_levelField (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀)) :
    ∀ j, j ≤ k → ∀ b, ContDiffAt ℝ 2 (fun y => levelField (Z y) j b) y₀ := by apply _root_.YangMills.SharedProofs.p4722 <;> assumption
theorem contDiffAt_meanRadius_level (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀))
    (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun y => meanRadius (levelField (Z y) i) c.1) y₀ := by apply _root_.YangMills.SharedProofs.p8907 <;> assumption
theorem contDiffAt_chainAction (a : ℝ) (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀)) :
    ContDiffAt ℝ 2 (fun y => chainAction a (Z y)) y₀ := by apply _root_.YangMills.SharedProofs.p6648 <;> assumption
end SmoothFamilies
section Coordinates
variable {L n k : ℕ}
abbrev Coord (L n k : ℕ) : Type :=
  PositiveEdge L n k 0 ⊕ (Σ i : Fin k, PositiveEdge L n k (i + 1))
instance [NeZero L] : Fintype (Coord L n k) := Fintype.ofFinite _
def ofCoords (w : Coord L n k → ComplexMatrix2) : ChainPoint L n k :=
  ⟨fieldOfPositiveValues fun b => w (Sum.inl b), fun i c => w (Sum.inr ⟨i, c⟩)⟩
def coords (X : ChainPoint L n k) : Coord L n k → ComplexMatrix2 :=
  Sum.elim (fun b => X.fine b.1) fun p => X.noise p.1 p.2
theorem ofCoords_coords {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0) :
    ofCoords (coords X) = X := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.ofCoordinates_toCoordinates <;> assumption
variable [NeZero L]
theorem contDiffAt_ofCoords_fine {x : Coord L n k → ComplexMatrix2}
    (hx : ∀ b, IsUnit (x (Sum.inl b)).det) (b : Edge L n k 0) :
    ContDiffAt ℝ 2 (fun w => (ofCoords w).fine b) x := by
  have hc : ∀ ι : Coord L n k, ContDiffAt ℝ 2 (fun w : Coord L n k → ComplexMatrix2 => w ι) x :=
    fun ι => (contDiff_apply ℝ ComplexMatrix2 ι).contDiffAt
  by_cases h : b.IsPositivelyOriented
  · simp only [ofCoords, fieldOfPositiveValues_pos _ h]
    exact hc _
  · simp only [ofCoords, fieldOfPositiveValues_neg _ h]
    exact contDiffAt_inv (hc _) (hx _)
theorem contDiffAt_ofCoords_noise {x : Coord L n k → ComplexMatrix2} (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun w => (ofCoords w).noise i c) x :=
  (contDiff_apply ℝ ComplexMatrix2 (Sum.inr ⟨i, c⟩ : Coord L n k)).contDiffAt
theorem isUnit_det_coords {X : ChainPoint L n k} (hX : IsCompactValued X)
    (b : PositiveEdge L n k 0) : IsUnit (coords X (Sum.inl b)).det := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.isUnit_det_toCoordinates <;> assumption
theorem contDiffAt_levelField_coords {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ}
    (hj : j ≤ k) (b : Edge L n k j) :
    ContDiffAt ℝ 2 (fun w => levelField (ofCoords w) j b) (coords X) := by
  have h0 : ofCoords (coords X) = X := ofCoords_coords (hX.2 0 (Nat.zero_le _))
  exact contDiffAt_levelField (Z := ofCoords) (y₀ := coords X)
    (contDiffAt_ofCoords_fine (isUnit_det_coords hX))
    (fun i c => contDiffAt_ofCoords_noise i c) (by rwa [h0]) j hj b
theorem contDiffAt_chainAction_coords {X : ChainPoint L n k} (hX : IsCompactValued X) (a : ℝ) :
    ContDiffAt ℝ 2 (fun w => chainAction a (ofCoords w)) (coords X) := by
  have h0 : ofCoords (coords X) = X := ofCoords_coords (hX.2 0 (Nat.zero_le _))
  exact contDiffAt_chainAction (Z := ofCoords) (y₀ := coords X) a
    (contDiffAt_ofCoords_fine (isUnit_det_coords hX))
    (fun i c => contDiffAt_ofCoords_noise i c) (by rwa [h0])
theorem contDiffAt_meanRadius_coords {X : ChainPoint L n k} (hX : IsCompactValued X) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun w => meanRadius (levelField (ofCoords w) i) c.1) (coords X) := by
  have h0 : ofCoords (coords X) = X := ofCoords_coords (hX.2 0 (Nat.zero_le _))
  exact contDiffAt_meanRadius_level (Z := ofCoords) (y₀ := coords X)
    (contDiffAt_ofCoords_fine (isUnit_det_coords hX))
    (fun i c => contDiffAt_ofCoords_noise i c) (by rwa [h0]) i c
end Coordinates
section MatrixCurves
theorem hasDerivAt_matrix_inv {f : ℝ → ComplexMatrix2} {f' : ComplexMatrix2}
    (hf : HasDerivAt f f' 0) (hu : IsUnit (f 0).det) :
    HasDerivAt (fun t => (f t)⁻¹) (-((f 0)⁻¹ * f' * (f 0)⁻¹)) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.hasDerivAt_inv_matrix <;> assumption
theorem matExp_I_smul_mem_compact {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
theorem exp_pi_apply {ι : Type*} [Fintype ι] (x : ι → ComplexMatrix2) (i : ι) :
    NormedSpace.exp x i = ComplexMatrix2.matExp (x i) := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.normedExp_pi_apply <;> assumption
theorem hasDerivAt_matExp_I_line (X : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • X)))
      (Complex.I • X) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.hasDerivAt_matExp_smul <;> assumption
theorem matExp_I_line_zero (X : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • (((0 : ℝ) : ℂ) • X)) = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.matExp_I_line_zero <;> assumption
end MatrixCurves
section AlongLeftChart
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem hasDerivAt_leftChart_zero (x a : A) :
    HasDerivAt (fun r : ℝ => leftChart x (r • a)) (a * x) 0 := by
  have h := hasDerivAt_leftChart_line x a 0
  simp only [zero_add, zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h
theorem hasDerivAt_comp_leftChart {Ψ : A → F} {x : A} (hΨ : ContDiffAt ℝ 2 Ψ x) (a : A) :
    HasDerivAt (fun r : ℝ => Ψ (leftChart x (r • a))) (fderiv ℝ Ψ x (a * x)) 0 := by
  have h1 : DifferentiableAt ℝ Ψ x := hΨ.differentiableAt (by norm_num)
  have h3 : HasFDerivAt Ψ (fderiv ℝ Ψ x) (leftChart x ((0 : ℝ) • a)) := by
    simpa [leftChart_zero] using h1.hasFDerivAt
  exact h3.comp_hasDerivAt (0 : ℝ) (hasDerivAt_leftChart_zero x a)
end AlongLeftChart
section Tangents
variable {L n k : ℕ} [NeZero L]
instance {j : ℕ} : Fintype (Edge L n k j) := Fintype.ofFinite _
def tangentCoords : LevelForms L n k →ₗ[ℝ] (Coord L n k → ComplexMatrix2) where
  toFun ξ := Sum.elim (fun b => Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1) fun p =>
    Complex.I • (ξ.2 p.1 : Edge L n k (p.1 + 1) → ComplexMatrix2) p.2.1
  map_add' ξ ξ' := by
    funext ι
    rcases ι with b | p
    · simp [smul_add]
    · simp [smul_add]
  map_smul' r ξ := by
    funext ι
    rcases ι with b | p
    · change Complex.I • (r • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1) =
        r • (Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1)
      rw [smul_comm]
    · change Complex.I • (r • (ξ.2 p.1 : Edge L n k (p.1 + 1) → ComplexMatrix2) p.2.1) =
        r • (Complex.I • (ξ.2 p.1 : Edge L n k (p.1 + 1) → ComplexMatrix2) p.2.1)
      rw [smul_comm]
theorem leftChart_apply (x a : Coord L n k → ComplexMatrix2) (ι : Coord L n k) :
    leftChart x a ι = ComplexMatrix2.matExp (a ι) * x ι := by
  simp only [leftChart, Pi.mul_apply, exp_pi_apply]
theorem ofCoords_leftChart {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0)
    (ξ : LevelForms L n k) : ofCoords (leftChart (coords X) (tangentCoords ξ)) = expMove ξ X := by
  simp only [ofCoords, expMove]
  congr 1
  · funext b
    by_cases h : b.IsPositivelyOriented
    · rw [fieldOfPositiveValues_pos _ h, leftChart_apply]
      simp only [PeriodicLattice.expTwist, if_pos h]
      rfl
    · rw [fieldOfPositiveValues_neg _ h, leftChart_apply]
      simp only [PeriodicLattice.expTwist, if_neg h]
      rfl
  · funext i c
    rw [leftChart_apply]
    rfl
theorem ofCoords_leftChart_line {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0)
    (ξ : LevelForms L n k) (r : ℝ) :
    ofCoords (leftChart (coords X) (r • tangentCoords ξ)) = expMove (r • ξ) X := by
  rw [← ofCoords_leftChart hX, map_smul]
def chainActionCoords (a : ℝ) (w : Coord L n k → ComplexMatrix2) : ℝ := chainAction a (ofCoords w)
def levelFieldDeriv (X : ChainPoint L n k) (j : ℕ) (b : Edge L n k j) :
    (Coord L n k → ComplexMatrix2) →L[ℝ] ComplexMatrix2 :=
  fderiv ℝ (fun w => levelField (ofCoords w) j b) (coords X)
theorem levelField_ofCoords_neg (w : Coord L n k → ComplexMatrix2) {j : ℕ} (hj : j ≤ k)
    {b : Edge L n k j} (hb : ¬b.IsPositivelyOriented) :
    levelField (ofCoords w) j b = (levelField (ofCoords w) j b.opposite)⁻¹ := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.levelField_ofCoords_opposite <;> assumption
theorem tangentTransport_succ_pos (X : ChainPoint L n k) (ξ : LevelForms L n k) {j : ℕ}
    (h : j < k) {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    tangentTransport X ξ (j + 1) b =
      ComplexMatrix2.conjugateBy (X.noise ⟨j, h⟩ ⟨b, hb⟩)
        (leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) b) +
      (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) b := by
  simp only [tangentTransport, dif_pos h, extendOddly, if_pos hb, dif_pos hb]
theorem levelField_leftChart_zero {X : ChainPoint L n k} (hX : IsCompactValued X)
    (a : Coord L n k → ComplexMatrix2) (j : ℕ) :
    levelField (ofCoords (leftChart (coords X) ((0 : ℝ) • a))) j = levelField X j := by
  rw [zero_smul, leftChart_zero, ofCoords_coords (hX.2 0 (Nat.zero_le _))]
theorem hasDerivAt_levelField {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ} (hj : j ≤ k)
    (b : Edge L n k j) (a : Coord L n k → ComplexMatrix2) :
    HasDerivAt (fun r : ℝ => levelField (ofCoords (leftChart (coords X) (r • a))) j b)
      (levelFieldDeriv X j b (a * coords X)) 0 :=
  hasDerivAt_comp_leftChart (contDiffAt_levelField_coords hX hj b) a
theorem expTwist_zero {j : ℕ} {W : Edge L n k j → ComplexMatrix2} (hW : W ∈ fieldSpace L n k j)
    (M : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • M) W = W := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.expTwist_zero <;> assumption
theorem hasDerivAt_expTwist {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ} (hj : j ≤ k)
    (a : Coord L n k → ComplexMatrix2) (M : Edge L n k j → ComplexMatrix2)
    (ih : ∀ b, b.IsPositivelyOriented → levelFieldDeriv X j b (a * coords X) =
      (Complex.I • M b) * levelField X j b) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • M) (levelField X j))
      (fun b => levelFieldDeriv X j b (a * coords X)) 0 := by
  have hr := hX.2 j hj
  refine hasDerivAt_pi.2 fun b => ?_
  by_cases hb : b.IsPositivelyOriented
  · have e : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • M) (levelField X j) b) =
        fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • M b)) * levelField X j b := by
      funext t
      simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply]
    rw [e, ih b hb]
    exact (hasDerivAt_matExp_I_line (M b)).mul_const _
  · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
    set c := b.opposite with hc
    have e : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • M) (levelField X j) b) =
        fun t : ℝ => (ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • M c)) * levelField X j c)⁻¹ := by
      funext t
      simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply, hc]
    have h1 := (hasDerivAt_matExp_I_line (M c)).mul_const (levelField X j c)
    have h0 : ComplexMatrix2.matExp (Complex.I • (((0 : ℝ) : ℂ) • M c)) * levelField X j c =
        levelField X j c := by
      simp only [matExp_I_line_zero, one_mul]
    have h2 := hasDerivAt_matrix_inv h1 (by rw [h0]; exact isUnit_det_of_mem_fieldSpace hr c)
    rw [e]
    refine h2.congr_deriv ?_
    have h3 := hasDerivAt_levelField hX hj c a
    have h4 := hasDerivAt_levelField hX hj b a
    have h5 := hasDerivAt_matrix_inv h3
      (by rw [levelField_leftChart_zero hX a j]; exact isUnit_det_of_mem_fieldSpace hr c)
    have e2 : (fun r : ℝ => levelField (ofCoords (leftChart (coords X) (r • a))) j b) =
        fun r : ℝ => (levelField (ofCoords (leftChart (coords X) (r • a))) j c)⁻¹ := by
      funext r
      exact levelField_ofCoords_neg _ hj hb
    rw [e2] at h4
    have h6 := h4.unique h5
    rw [h6, ih c hp, levelField_leftChart_zero hX a j, h0]
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
include hd
theorem levelFieldDeriv_eq_tangentTransport {X : ChainPoint L n k} (hX : IsCompactValued X)
    (ξ : LevelForms L n k) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j, b.IsPositivelyOriented →
      levelFieldDeriv X j b (tangentCoords ξ * coords X) =
        (Complex.I • tangentTransport X ξ j b) * levelField X j b := by
  intro j
  induction j with
  | zero =>
    intro _ b hb
    have e : (fun w : Coord L n k → ComplexMatrix2 => levelField (ofCoords w) 0 b) =
        fun w => w (Sum.inl ⟨b, hb⟩) := by
      funext w
      have e0 : levelField (ofCoords w) 0 b =
          fieldOfPositiveValues (fun b => w (Sum.inl b)) b := rfl
      rw [e0, fieldOfPositiveValues_pos _ hb]
    have h : fderiv ℝ (fun w : Coord L n k → ComplexMatrix2 => w (Sum.inl ⟨b, hb⟩)) (coords X) =
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Coord L n k => ComplexMatrix2)
          (Sum.inl ⟨b, hb⟩ : Coord L n k) :=
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Coord L n k => ComplexMatrix2)
        (Sum.inl ⟨b, hb⟩ : Coord L n k) (coords X)).fderiv
    have e3 : tangentTransport X ξ 0 b = (ξ.1 : Edge L n k 0 → ComplexMatrix2) b := rfl
    have e4 : levelField X 0 b = X.fine b := rfl
    rw [levelFieldDeriv, e, h, e3, e4]
    rfl
  | succ j ih =>
    intro hj b hb
    have h : j < k := hj
    have hj' : j ≤ k := h.le
    have hr := hX.2 j hj'
    have hrr : ∀ b', levelField X j b' ∈ PeriodicLattice.compactGaugeGroup :=
      fun b' => hr.1 b' (Set.mem_univ _)
    have hl := meanRadius_ne_zero hX ⟨j, h⟩ ⟨b, hb⟩
    have hs := det_mem_slitPlane_of_quaternion (contourMean_mem_quaternionMatrices hrr b)
      (det_contourMean_ne_zero hl)
    set n₀ := X.noise ⟨j, h⟩ ⟨b, hb⟩ with hn₀
    set u := normalizedMean (levelField X j) b with hu
    set d := tangentCoords ξ * coords X with hd'
    have hP : ContDiffAt ℝ 2 (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b)
        (levelField X j) :=
      contDiffAt_normalizedMean (V := fun V => V) (y₀ := levelField X j)
        (fun b' => (contDiff_apply ℝ ComplexMatrix2 b').contDiffAt)
        (isUnit_det_of_mem_fieldSpace hr) b hs hl
    have hPd := (hP.differentiableAt (by norm_num)).hasFDerivAt
    set DP := fderiv ℝ (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b)
      (levelField X j) with hDP
    set vel : Edge L n k j → ComplexMatrix2 := fun b' => levelFieldDeriv X j b' d with hvel
    have hA := hasDerivAt_expTwist hX hj' (tangentCoords ξ) (tangentTransport X ξ j) (ih hj')
    have hB : HasDerivAt
        (fun r : ℝ => levelField (ofCoords (leftChart (coords X) (r • tangentCoords ξ))) j) vel 0 :=
      hasDerivAt_pi.2 fun b' => hasDerivAt_levelField hX hj' b' (tangentCoords ξ)
    have hPA : HasDerivAt (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist
        ((t : ℂ) • tangentTransport X ξ j) (levelField X j)) b) (DP vel) 0 := by
      have h1 : HasFDerivAt (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b) DP
          (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • tangentTransport X ξ j) (levelField X j)) := by
        rw [expTwist_zero hr]; exact hPd
      exact h1.comp_hasDerivAt (0 : ℝ) hA
    have hPB : HasDerivAt (fun r : ℝ => normalizedMean
        (levelField (ofCoords (leftChart (coords X) (r • tangentCoords ξ))) j) b) (DP vel) 0 := by
      have h1 : HasFDerivAt (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b) DP
          (levelField (ofCoords (leftChart (coords X) ((0 : ℝ) • tangentCoords ξ))) j) := by
        rw [levelField_leftChart_zero hX]; exact hPd
      exact h1.comp_hasDerivAt (0 : ℝ) hB
    have hN : HasDerivAt (fun r : ℝ => leftChart (coords X) (r • tangentCoords ξ)
        (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩ : Coord L n k)) (d (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩)) 0 :=
      (hasDerivAt_pi.1 (hasDerivAt_leftChart_zero (coords X) (tangentCoords ξ))) _
    have hL := hN.mul hPB
    have hL0 := hasDerivAt_levelField hX hj b (tangentCoords ξ)
    have e1 : (fun r : ℝ =>
        levelField (ofCoords (leftChart (coords X) (r • tangentCoords ξ))) (j + 1) b) =
        (fun r : ℝ => leftChart (coords X) (r • tangentCoords ξ)
          (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩ : Coord L n k)) *
          fun r : ℝ => normalizedMean
            (levelField (ofCoords (leftChart (coords X) (r • tangentCoords ξ))) j) b := by
      funext r
      rw [levelField_succ_pos _ h hb]
      rfl
    rw [e1] at hL0
    have hval := hL0.unique hL
    have hc0 : leftChart (coords X) ((0 : ℝ) • tangentCoords ξ)
        (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩ : Coord L n k) = n₀ := by
      rw [zero_smul, leftChart_zero]
      rfl
    have hu0 : normalizedMean
        (levelField (ofCoords (leftChart (coords X) ((0 : ℝ) • tangentCoords ξ))) j) b = u := by
      rw [levelField_leftChart_zero hX]
    rw [hc0, hu0] at hval
    have hun : u ∈ PeriodicLattice.compactGaugeGroup := by
      have := normalize_mem_compact (contourMean_mem_quaternionMatrices hrr b)
        (det_contourMean_ne_zero hl)
      exact this
    have hnr : n₀ ∈ PeriodicLattice.compactGaugeGroup := hX.1 _ _
    have huu : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_of_compact hun)
    have huu' : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_of_compact hun)
    have hnn : n₀⁻¹ * n₀ = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_of_compact hnr)
    have hY : HasDerivAt (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist
        ((t : ℂ) • tangentTransport X ξ j) (levelField X j)) b * u⁻¹) (DP vel * u⁻¹) 0 :=
      hPA.mul_const _
    have hY0 : (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist
        ((t : ℂ) • tangentTransport X ξ j) (levelField X j)) b * u⁻¹) 0 = 1 := by
      simp only []
      rw [expTwist_zero hr]
      exact huu
    have hlog := ((hd.1 Set.univ _ _ _ _ _ _ Filter.univ_mem hY hY hY).2.1 hY0).2.2.1
    have e2 : leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) b =
        Complex.I⁻¹ • deriv (fun t : ℝ => ComplexMatrix2.logSeries (normalizedMean
          (PeriodicLattice.expTwist ((t : ℂ) • tangentTransport X ξ j) (levelField X j)) b * u⁻¹))
          0 := by
      unfold leftDifferential extendOddly
      rw [if_pos hb]
      rfl
    have hξ : d (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩) =
        (Complex.I • (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) b) * n₀ := rfl
    rw [hval, hξ, levelField_succ_pos X h hb, tangentTransport_succ_pos X ξ h hb, e2, hlog.deriv,
      ComplexMatrix2.conjugateBy]
    simp only [smul_add, add_mul, smul_smul, Matrix.smul_mul, Matrix.mul_smul,
      mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
    have a1 : n₀ * (DP vel * u⁻¹) * n₀⁻¹ * (n₀ * u) = n₀ * DP vel := by
      calc n₀ * (DP vel * u⁻¹) * n₀⁻¹ * (n₀ * u)
          = n₀ * (DP vel * u⁻¹) * (n₀⁻¹ * n₀) * u := by simp only [mul_assoc]
        _ = n₀ * DP vel * (u⁻¹ * u) := by rw [hnn]; simp only [mul_one, mul_assoc]
        _ = n₀ * DP vel := by rw [huu', mul_one]
    rw [a1]
    simp only [mul_assoc]
    abel
end Tangents
section CompactPoints
variable {L n k : ℕ} [NeZero L]
theorem eventually_isCompactValued
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) {p : ℝ → Coord L n k → ComplexMatrix2}
    (hp : ContinuousAt p 0) (h0 : p 0 = coords X)
    (hr : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ ι, p r ι ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ᶠ r in 𝓝 (0 : ℝ), IsCompactValued (ofCoords (p r)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.eventually_isCompactValued <;> assumption
theorem edgeForm_mem_hermitianTraceless {j : ℕ} (B : edgeFormSpace L n k j) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    (B : Edge L n k j → ComplexMatrix2) b ∈ ComplexMatrix2.hermitianTraceless := B.2.1 b hb
theorem tangentCoords_smul_eq_I_smul (ξ : LevelForms L n k) (r : ℝ) (ι : Coord L n k) :
    ∃ A ∈ ComplexMatrix2.hermitianTraceless, (r • tangentCoords ξ) ι = Complex.I • A := by
  rcases ι with b | p
  · refine ⟨r • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1,
      ComplexMatrix2.hermitianTraceless.smul_mem r (edgeForm_mem_hermitianTraceless ξ.1 b.2), ?_⟩
    change r • (Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1) = _
    rw [smul_comm]
  · refine ⟨r • (ξ.2 p.1 : Edge L n k (p.1 + 1) → ComplexMatrix2) p.2.1,
      ComplexMatrix2.hermitianTraceless.smul_mem r
        (edgeForm_mem_hermitianTraceless (ξ.2 p.1) p.2.2), ?_⟩
    change r • (Complex.I • (ξ.2 p.1 : Edge L n k (p.1 + 1) → ComplexMatrix2) p.2.1) = _
    rw [smul_comm]
theorem coords_mem_compact {X : ChainPoint L n k} (hX : IsCompactValued X) (ι : Coord L n k) :
    coords X ι ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.toCoordinates_mem_compact <;> assumption
theorem continuousAt_leftChart_line (x a : Coord L n k → ComplexMatrix2) :
    ContinuousAt (fun r : ℝ => leftChart x (r • a)) 0 :=
  (hasDerivAt_leftChart_zero x a).continuousAt
theorem eventually_isCompactValued_expMove
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (ξ : LevelForms L n k) :
    ∀ᶠ r in 𝓝 (0 : ℝ),
      IsCompactValued (ofCoords (leftChart (coords X) (r • tangentCoords ξ))) := by
  refine eventually_isCompactValued hxor hX (continuousAt_leftChart_line _ _)
    (by simp [leftChart_zero]) (Eventually.of_forall fun r ι => ?_)
  obtain ⟨A, hA, e⟩ := tangentCoords_smul_eq_I_smul ξ r ι
  rw [leftChart_apply, e]
  exact compact_mul_mem (matExp_I_smul_mem_compact hA) (coords_mem_compact hX ι)
end CompactPoints
section Fibre
variable {L n k' : ℕ} [NeZero L]
def levelRatio (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2)
    (i : Fin (k' + 1)) (c : PositiveEdge L n (k' + 1) (i + 1)) : ComplexMatrix2 :=
  levelField (ofCoords (leftChart (coords X) a)) (i + 1) c.1 * (levelField X (i + 1) c.1)⁻¹
def topCorrection (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2) :
    Coord L n (k' + 1) → ComplexMatrix2 :=
  Sum.elim (fun _ => 1) fun p =>
    open Classical in if p.1 = Fin.last k' then (levelRatio X a p.1 p.2)⁻¹ else 1
def fibreCoords (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2) :
    Coord L n (k' + 1) → ComplexMatrix2 :=
  topCorrection X a * leftChart (coords X) a
theorem ofCoords_fine (w : Coord L n (k' + 1) → ComplexMatrix2) :
    (ofCoords w).fine = fieldOfPositiveValues fun b => w (Sum.inl b) := rfl
theorem fibreCoords_inl (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2)
    (b : PositiveEdge L n (k' + 1) 0) :
    fibreCoords X a (Sum.inl b) = leftChart (coords X) a (Sum.inl b) := by
  simp [fibreCoords, topCorrection]
theorem ofCoords_fibreCoords {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (ξ : LevelForms L n (k' + 1)) : ofCoords (fibreCoords X (tangentCoords ξ)) = fibreMove X ξ := by
  have hb0 := hX.2 0 (Nat.zero_le _)
  have hY := ofCoords_leftChart hb0 ξ
  have hN : ∀ (i : Fin (k' + 1)) (c : PositiveEdge L n (k' + 1) (i + 1)),
      IsUnit (leftChart (coords X) (tangentCoords ξ) (Sum.inr ⟨i, c⟩)).det := by
    intro i c
    obtain ⟨A, hA, e⟩ := tangentCoords_smul_eq_I_smul ξ 1 (Sum.inr ⟨i, c⟩)
    rw [one_smul] at e
    rw [leftChart_apply, e]
    exact isUnit_det_of_compact (compact_mul_mem (matExp_I_smul_mem_compact hA)
      (coords_mem_compact hX _))
  have hbase : (ofCoords (fibreCoords X (tangentCoords ξ))).fine =
      (ofCoords (leftChart (coords X) (tangentCoords ξ))).fine := by
    rw [ofCoords_fine, ofCoords_fine]
    congr 1
    funext b
    exact fibreCoords_inl _ _ _
  have hnoise : (ofCoords (fibreCoords X (tangentCoords ξ))).noise =
      fun (i : Fin (k' + 1)) (c : PositiveEdge L n (k' + 1) (i + 1)) =>
      open Classical in
        if i.val + 1 = k' + 1 then
          levelField X (i + 1) c.1 *
            (normalizedMean (levelField (ofCoords (leftChart (coords X) (tangentCoords ξ))) i)
              c.1)⁻¹
        else (ofCoords (leftChart (coords X) (tangentCoords ξ))).noise i c := by
    funext i c
    by_cases hi : i = Fin.last k'
    · have hv : i.val + 1 = k' + 1 := by rw [hi]; rfl
      rw [if_pos hv]
      change topCorrection X (tangentCoords ξ) (Sum.inr ⟨i, c⟩) *
        leftChart (coords X) (tangentCoords ξ) (Sum.inr ⟨i, c⟩) = _
      have e1 : topCorrection X (tangentCoords ξ) (Sum.inr ⟨i, c⟩) =
          (levelRatio X (tangentCoords ξ) i c)⁻¹ := by
        simp only [topCorrection, Sum.elim_inr, if_pos hi]
      have hWr : levelField X (i + 1) c.1 ∈ PeriodicLattice.compactGaugeGroup :=
        (hX.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)
      rw [e1, levelRatio, levelField_succ_pos _ i.2 c.2]
      have e2 : (ofCoords (leftChart (coords X) (tangentCoords ξ))).noise ⟨i, i.2⟩ ⟨c.1, c.2⟩ =
          leftChart (coords X) (tangentCoords ξ) (Sum.inr ⟨i, c⟩) := rfl
      rw [e2, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_compact hWr)]
      rw [mul_assoc, mul_assoc, Matrix.nonsing_inv_mul _ (hN i c), mul_one]
    · have hv : ¬ i.val + 1 = k' + 1 := by
        intro h
        apply hi
        ext
        simpa using h
      rw [if_neg hv]
      change topCorrection X (tangentCoords ξ) (Sum.inr ⟨i, c⟩) *
        leftChart (coords X) (tangentCoords ξ) (Sum.inr ⟨i, c⟩) = _
      have e1 : topCorrection X (tangentCoords ξ) (Sum.inr ⟨i, c⟩) = 1 := by
        simp only [topCorrection, Sum.elim_inr, if_neg hi]
      rw [e1, one_mul]
      rfl
  have e0 : ofCoords (fibreCoords X (tangentCoords ξ)) =
      (⟨(ofCoords (fibreCoords X (tangentCoords ξ))).fine,
        (ofCoords (fibreCoords X (tangentCoords ξ))).noise⟩ : ChainPoint L n (k' + 1)) := rfl
  rw [e0, hbase, hnoise, hY]
  rfl
theorem contDiffAt_levelField_leftChart {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    {j : ℕ} (hj : j ≤ k' + 1) (b : Edge L n (k' + 1) j) :
    ContDiffAt ℝ 2 (fun a => levelField (ofCoords (leftChart (coords X) a)) j b) 0 := by
  have h : ContDiffAt ℝ 2 (fun w => levelField (ofCoords w) j b) (leftChart (coords X) 0) := by
    rw [leftChart_zero]; exact contDiffAt_levelField_coords hX hj b
  exact h.comp 0 (contDiffAt_leftChart (coords X) 0)
theorem levelRatio_zero {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (i : Fin (k' + 1))
    (c : PositiveEdge L n (k' + 1) (i + 1)) : levelRatio X 0 i c = 1 := by
  have hW : levelField X (i + 1) c.1 ∈ PeriodicLattice.compactGaugeGroup :=
    (hX.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)
  rw [levelRatio, leftChart_zero, ofCoords_coords (hX.2 0 (Nat.zero_le _))]
  exact Matrix.mul_nonsing_inv _ (isUnit_det_of_compact hW)
theorem contDiffAt_levelRatio {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (i : Fin (k' + 1)) (c : PositiveEdge L n (k' + 1) (i + 1)) :
    ContDiffAt ℝ 2 (fun a => levelRatio X a i c) 0 :=
  (contDiffAt_levelField_leftChart hX i.2 c.1).mul contDiffAt_const
theorem contDiffAt_topCorrection {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) :
    ContDiffAt ℝ 2 (topCorrection X) 0 := by
  refine contDiffAt_pi.2 fun ι => ?_
  rcases ι with b | ⟨i, c⟩
  · exact contDiffAt_const
  · by_cases hi : i = Fin.last k'
    · simp only [topCorrection, Sum.elim_inr, if_pos hi]
      exact contDiffAt_inv (contDiffAt_levelRatio hX i c) (by rw [levelRatio_zero hX]; simp)
    · simp only [topCorrection, Sum.elim_inr, if_neg hi]
      exact contDiffAt_const
theorem topCorrection_zero {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) :
    topCorrection X 0 = 1 := by
  funext ι
  rcases ι with b | ⟨i, c⟩
  · rfl
  · by_cases hi : i = Fin.last k'
    · simp only [topCorrection, Sum.elim_inr, if_pos hi, Pi.one_apply]
      rw [levelRatio_zero hX]
      simp
    · simp only [topCorrection, Sum.elim_inr, if_neg hi, Pi.one_apply]
theorem contDiffAt_fibreCoords {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) :
    ContDiffAt ℝ 2 (fibreCoords X) 0 :=
  (contDiffAt_topCorrection hX).mul (contDiffAt_leftChart (coords X) 0)
theorem fibreCoords_zero {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) :
    fibreCoords X 0 = coords X := by
  rw [fibreCoords, topCorrection_zero hX, leftChart_zero, one_mul]
def fibreAction (a : ℝ) (X : ChainPoint L n (k' + 1)) (b : Coord L n (k' + 1) → ComplexMatrix2) :
    ℝ :=
  chainActionCoords a (fibreCoords X b)
theorem contDiffAt_fibreAction {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (a : ℝ) :
    ContDiffAt ℝ 2 (fibreAction a X) 0 := by
  have h : ContDiffAt ℝ 2 (chainActionCoords a) (fibreCoords X 0) := by
    rw [fibreCoords_zero hX]; exact contDiffAt_chainAction_coords hX a
  exact h.comp 0 (contDiffAt_fibreCoords hX)
theorem fibreSecondDeriv_eq_hessian {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (a : ℝ)
    (ξ ξ' : LevelForms L n (k' + 1)) :
    fibreSecondDeriv a X ξ ξ' =
      fderiv ℝ (fderiv ℝ (fibreAction a X)) 0 (tangentCoords ξ) (tangentCoords ξ') := by
  have h := hasDerivAt_deriv_line (contDiffAt_fibreAction hX a) (tangentCoords ξ) (tangentCoords ξ')
  have e : (fun s : ℝ => deriv (fun t : ℝ => chainAction a (fibreMove X (s • ξ + t • ξ'))) 0) =
      fun s : ℝ => deriv (fun t : ℝ =>
        fibreAction a X (s • tangentCoords ξ + t • tangentCoords ξ')) 0 := by
    funext s
    congr 1
    funext t
    rw [← ofCoords_fibreCoords hX, map_add, map_smul, map_smul]
    rfl
  rw [fibreSecondDeriv, e]
  exact h.deriv
theorem fibreHessian_eq {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (a : ℝ)
    (η : LinearMap.ker (topDeriv X)) :
    fibreHessian a X η = fderiv ℝ (fderiv ℝ (fibreAction a X)) 0
      (tangentCoords (η : LevelForms L n (k' + 1))) (tangentCoords (η : LevelForms L n (k' + 1))) := by
  set D := fderiv ℝ (fderiv ℝ (fibreAction a X)) 0 with hD
  have hex : ∃ T : QuadraticForm ℝ (LinearMap.ker (topDeriv X)), IsFibreHessian a X T := by
    refine ⟨LinearMap.BilinMap.toQuadraticMap (LinearMap.mk₂ ℝ
      (fun u v : LinearMap.ker (topDeriv X) =>
        D (tangentCoords (u : LevelForms L n (k' + 1))) (tangentCoords (v : LevelForms L n (k' + 1))))
      ?_ ?_ ?_ ?_), fun ξ => ?_⟩
    · intro u u' v
      simp [map_add]
    · intro c u v
      simp [map_smul]
    · intro u v v'
      simp [map_add]
    · intro c u v
      simp [map_smul]
    · rw [fibreSecondDeriv_eq_hessian hX]
      rfl
  have hs : IsFibreHessian a X (fibreHessian a X) := Classical.epsilon_spec hex
  rw [hs η, fibreSecondDeriv_eq_hessian hX]
end Fibre
theorem xor_isPositive_opposite (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.xor_isPositivelyOriented_opposite <;> assumption
theorem expMoveNearCompactPoint_holds (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction) :
    ExpMoveNearCompactPoint := by
  intro a L hL k n hk hn X hX
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hxor : ∀ j, j ≤ k' + 1 → ∀ b : Edge L n (k' + 1) j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := xor_isPositive_opposite hb hL hn
  have hb0 := hX.2 0 (Nat.zero_le _)
  refine ⟨fun η => ?_, fun ξ => ⟨?_, ?_⟩⟩
  · rw [fibreHessian_eq hX, fibreSecondDeriv_eq_hessian hX]
  · filter_upwards [eventually_isCompactValued_expMove hxor hX ξ] with r hr
    rwa [ofCoords_leftChart_line hb0] at hr
  · intro j hj b hbp
    have h := hasDerivAt_levelField hX hj b (tangentCoords ξ)
    rw [levelFieldDeriv_eq_tangentTransport hd hX ξ j hj b hbp] at h
    simpa only [ofCoords_leftChart_line hb0] using h
end YangMills.Construction.RunningCouplingSlope.CompactPointChain
end
