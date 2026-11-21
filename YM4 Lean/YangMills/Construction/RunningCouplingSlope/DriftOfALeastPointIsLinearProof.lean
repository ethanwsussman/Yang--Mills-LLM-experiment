import YangMills.Construction.Averaging.ArgumentsOfTheBlockAverageLieInTheirDomains
import YangMills.Construction.Lattice.LocalityAndGaugeCovarianceOfTheAveragingMapProof
import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreUnderAGaugeFunctionProof
import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
import YangMills.Construction.RunningCouplingSlope.FieldsAtALeastPointAreSmall
import YangMills.Construction.RunningCouplingSlope.PlainDifferentialAtOneOnComplexFormsProof
import YangMills.Construction.Matrices.SpecialUnitaryTwo
set_option autoImplicit false

section
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def ChainDriftLinearAtMinimizer : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)), ∀ W : Edge L n k k → Matrices.ComplexMatrix2,
      RepresentsTorusField W V →
      ∀ X : ChainPoint L n k, IsMinimizerOver a W X →
        ∃ T : LevelForms L n k →ₗ[ℝ] vertexFunctionSpace L n k k,
          ∀ ξ, (T ξ : Vertex L n k k → Matrices.ComplexMatrix2) = chainDrift X ξ k
end YangMills.Construction.RunningCouplingSlope
end
end

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MinimizerDrift
open Filter YangMills.Construction.Tower YangMills.Construction.Matrices
open scoped Topology
section LeftChart
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
def leftChart (x a : A) : A := NormedSpace.exp a * x
theorem leftChart_zero (x : A) : leftChart x 0 = x := by simp [leftChart]
theorem hasDerivAt_leftChart_shift (x a : A) (s : ℝ) :
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
    (hu : IsUnit (f y₀).det) :
    ContDiffAt ℝ 2 (fun y => (f y)⁻¹) y₀ := by apply _root_.YangMills.SharedProofs.p22704 <;> assumption
theorem contDiffAt_smul {f : Y → ℂ} {g : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀)
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
  contDiffAt_smul ((contDiffAt_meanRadius hV hu c hs).inv hl) (contDiffAt_contourMean hV hu c)
end SmoothMatrixMaps
section QuaternionMatrices
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
theorem compact_of_quaternion {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices)
    (h : M.det ≠ 0) :
    (M.det ^ (1 / 2 : ℂ))⁻¹ • M ∈ PeriodicLattice.compactGaugeGroup :=
  ComplexMatrix2.normalize_quaternionMatrix_mem_specialUnitary hM h
variable {L n k j : ℕ}
theorem compact_mul {g h : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hh : h ∈ PeriodicLattice.compactGaugeGroup) :
    g * h ∈ PeriodicLattice.compactGaugeGroup := ComplexMatrix2.specialUnitary.mul_mem hg hh
theorem compact_inv {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem compact_det {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem compact_isUnit_det {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem compact_pathHolonomy {V : Edge L n k j → ComplexMatrix2}
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
  exact mem_quaternionMatrices_of_compact
    (compact_mul (compact_mul (compact_pathHolonomy hV _) (compact_pathHolonomy hV _))
    (compact_inv (compact_pathHolonomy hV _)))
end QuaternionMatrices
section PositiveValues
variable {L n k j : ℕ}
theorem fieldOfPositiveValues_pos (w : PositiveEdge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) :
    fieldOfPositiveValues w b = w ⟨b, h⟩ := by
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
theorem levelField_succ_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
theorem levelField_succ_neg (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : ¬b.IsPositivelyOriented) :
    levelField X (j + 1) b = (levelField X (j + 1) b.opposite)⁻¹ := by apply _root_.YangMills.SharedProofs.p5483 <;> assumption
theorem meanRadius_ne_zero {X : ChainPoint L n k} (hX : IsCompactValued X) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) : meanRadius (levelField X i) c.1 ≠ 0 := by apply _root_.YangMills.SharedProofs.p17043 <;> assumption
theorem det_contourMean_ne_zero {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    {c : Edge L n k (j + 1)} (h : meanRadius V c ≠ 0) :
    (contourMean V c).det ≠ 0 := by apply _root_.YangMills.SharedProofs.p15699 <;> assumption
end LevelFields
section SmoothFamilies
variable {L n k : ℕ} [NeZero L] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
  {Z : Y → ChainPoint L n k}
theorem isUnit_det_of_mem_fieldSpace {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (b : Edge L n k j) :
    IsUnit (V b).det := compact_isUnit_det (hV.1 b (Set.mem_univ b))
theorem contDiffAt_levelField (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀)) :
    ∀ j, j ≤ k → ∀ b, ContDiffAt ℝ 2 (fun y => levelField (Z y) j b) y₀ := by apply _root_.YangMills.SharedProofs.p4722 <;> assumption
theorem contDiffAt_meanRadius_levelField (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀))
    (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun y => meanRadius (levelField (Z y) i) c.1) y₀ := by apply _root_.YangMills.SharedProofs.p8907 <;> assumption
end SmoothFamilies
section ChainCoordinates
variable {L n k : ℕ}
abbrev ChainIndex (L n k : ℕ) : Type :=
  PositiveEdge L n k 0 ⊕ (Σ i : Fin k, PositiveEdge L n k (i + 1))
instance instFintypeChainIndex [NeZero L] : Fintype (ChainIndex L n k) := Fintype.ofFinite _
def ofCoords (w : ChainIndex L n k → ComplexMatrix2) : ChainPoint L n k :=
  ⟨fieldOfPositiveValues fun b => w (Sum.inl b), fun i c => w (Sum.inr ⟨i, c⟩)⟩
def toCoords (X : ChainPoint L n k) : ChainIndex L n k → ComplexMatrix2 :=
  Sum.elim (fun b => X.fine b.1) fun p => X.noise p.1 p.2
theorem ofCoords_toCoords {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0) :
    ofCoords (toCoords X) = X := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.ofCoordinates_toCoordinates <;> assumption
variable [NeZero L]
theorem contDiffAt_ofCoords_fine {x : ChainIndex L n k → ComplexMatrix2}
    (hx : ∀ b, IsUnit (x (Sum.inl b)).det)
    (b : Edge L n k 0) : ContDiffAt ℝ 2 (fun w => (ofCoords w).fine b) x := by
  have hc : ∀ ι : ChainIndex L n k,
      ContDiffAt ℝ 2 (fun w : ChainIndex L n k → ComplexMatrix2 => w ι) x := fun ι =>
    (contDiff_apply ℝ ComplexMatrix2 ι).contDiffAt
  by_cases h : b.IsPositivelyOriented
  · simp only [ofCoords, fieldOfPositiveValues_pos _ h]
    exact hc _
  · simp only [ofCoords, fieldOfPositiveValues_neg _ h]
    exact contDiffAt_inv (hc _) (hx _)
theorem contDiffAt_ofCoords_noise {x : ChainIndex L n k → ComplexMatrix2} (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun w => (ofCoords w).noise i c) x :=
  (contDiff_apply ℝ ComplexMatrix2 (Sum.inr ⟨i, c⟩ : ChainIndex L n k)).contDiffAt
theorem isUnit_det_toCoords {X : ChainPoint L n k} (hX : IsCompactValued X)
    (b : PositiveEdge L n k 0) :
    IsUnit (toCoords X (Sum.inl b)).det := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.isUnit_det_toCoordinates <;> assumption
theorem contDiffAt_levelField_coords {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ}
    (hj : j ≤ k) (b : Edge L n k j) :
    ContDiffAt ℝ 2 (fun w => levelField (ofCoords w) j b) (toCoords X) := by
  have h0 : ofCoords (toCoords X) = X := ofCoords_toCoords (hX.2 0 (Nat.zero_le _))
  exact contDiffAt_levelField (Z := ofCoords) (y₀ := toCoords X)
    (contDiffAt_ofCoords_fine (isUnit_det_toCoords hX))
    (fun i c => contDiffAt_ofCoords_noise i c) (by rwa [h0]) j hj b
theorem contDiffAt_meanRadius_coords {X : ChainPoint L n k} (hX : IsCompactValued X) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun w => meanRadius (levelField (ofCoords w) i) c.1) (toCoords X) := by
  have h0 : ofCoords (toCoords X) = X := ofCoords_toCoords (hX.2 0 (Nat.zero_le _))
  exact contDiffAt_meanRadius_levelField (Z := ofCoords) (y₀ := toCoords X)
    (contDiffAt_ofCoords_fine (isUnit_det_toCoords hX))
    (fun i c => contDiffAt_ofCoords_noise i c) (by rwa [h0]) i c
end ChainCoordinates
section MatrixCurves
theorem hasDerivAt_inv_matrix {f : ℝ → ComplexMatrix2} {f' : ComplexMatrix2}
    (hf : HasDerivAt f f' 0) (hu : IsUnit (f 0).det) :
    HasDerivAt (fun t => (f t)⁻¹) (-((f 0)⁻¹ * f' * (f 0)⁻¹)) 0 := by
  have hu' : IsUnit (f 0) := (Matrix.isUnit_iff_isUnit_det _).2 hu
  obtain ⟨u, hu2⟩ := hu'
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu2] at h
  have h2 := h.comp_hasDerivAt (0 : ℝ) hf
  have e : (fun t => (f t)⁻¹) = Ring.inverse ∘ f := by
    funext t; simp [Matrix.nonsing_inv_eq_ringInverse]
  rw [e]
  refine h2.congr_deriv ?_
  have e2 : ((u⁻¹ : ComplexMatrix2ˣ) : ComplexMatrix2) = (f 0)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu2, Ring.inverse_unit]
  simp [e2, ContinuousLinearMap.mulLeftRight_apply, mul_assoc]
theorem matExp_I_smul_mem_compact {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
theorem exp_pi_apply {ι : Type*} [Fintype ι] (x : ι → ComplexMatrix2) (i : ι) :
    NormedSpace.exp x i = ComplexMatrix2.matExp (x i) := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.normedExp_pi_apply <;> assumption
theorem hasDerivAt_matExp_I_line (X : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • X)))
      (Complex.I • X) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.hasDerivAt_matExp_smul <;> assumption
theorem matExp_I_line_zero (X : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • (((0 : ℝ) : ℂ) • X)) = 1 := by
  rw [Complex.ofReal_zero, zero_smul, smul_zero]
  exact NormedSpace.exp_zero
end MatrixCurves
section AlongLeftChart
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem hasDerivAt_leftChart_line (x a : A) :
    HasDerivAt (fun r : ℝ => leftChart x (r • a)) (a * x) 0 := by
  have h := hasDerivAt_leftChart_shift x a 0
  simp only [zero_add, zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h
theorem hasDerivAt_comp_leftChart_line {Ψ : A → F} {x : A} (hΨ : ContDiffAt ℝ 2 Ψ x) (a : A) :
    HasDerivAt (fun r : ℝ => Ψ (leftChart x (r • a))) (fderiv ℝ Ψ x (a * x)) 0 := by
  have h1 : DifferentiableAt ℝ Ψ x := hΨ.differentiableAt (by norm_num)
  have h3 : HasFDerivAt Ψ (fderiv ℝ Ψ x) (leftChart x ((0 : ℝ) • a)) := by
    simpa [leftChart_zero] using h1.hasFDerivAt
  exact h3.comp_hasDerivAt (0 : ℝ) (hasDerivAt_leftChart_line x a)
end AlongLeftChart
section TangentCoordinates
variable {L n k : ℕ} [NeZero L]
instance instFintypeEdge {j : ℕ} : Fintype (Edge L n k j) := Fintype.ofFinite _
def tangentCoords : LevelForms L n k →ₗ[ℝ] (ChainIndex L n k → ComplexMatrix2) where
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
theorem leftChart_apply (x a : ChainIndex L n k → ComplexMatrix2) (ι : ChainIndex L n k) :
    leftChart x a ι = ComplexMatrix2.matExp (a ι) * x ι := by
  simp only [leftChart, Pi.mul_apply, exp_pi_apply]
def levelFieldDeriv (X : ChainPoint L n k) (j : ℕ) (b : Edge L n k j) :
    (ChainIndex L n k → ComplexMatrix2) →L[ℝ] ComplexMatrix2 :=
  fderiv ℝ (fun w => levelField (ofCoords w) j b) (toCoords X)
theorem levelField_ofCoords_opposite (w : ChainIndex L n k → ComplexMatrix2) {j : ℕ} (hj : j ≤ k)
    {b : Edge L n k j} (hb : ¬b.IsPositivelyOriented) :
    levelField (ofCoords w) j b = (levelField (ofCoords w) j b.opposite)⁻¹ := by
  cases j with
  | zero =>
    have e : ∀ b' : Edge L n k 0, levelField (ofCoords w) 0 b' =
        fieldOfPositiveValues (fun b => w (Sum.inl b)) b' := fun _ => rfl
    rw [e, e, fieldOfPositiveValues_neg _ hb,
      fieldOfPositiveValues_pos _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb)]
  | succ j => exact levelField_succ_neg _ hj hb
theorem tangentTransport_succ_pos (X : ChainPoint L n k) (ξ : LevelForms L n k) {j : ℕ}
    (h : j < k) {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    tangentTransport X ξ (j + 1) b =
      ComplexMatrix2.conjugateBy (X.noise ⟨j, h⟩ ⟨b, hb⟩)
        (leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) b) +
      (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) b := by
  simp only [tangentTransport, dif_pos h, extendOddly, if_pos hb, dif_pos hb]
theorem levelField_leftChart_zero {X : ChainPoint L n k} (hX : IsCompactValued X)
    (a : ChainIndex L n k → ComplexMatrix2) (j : ℕ) :
    levelField (ofCoords (leftChart (toCoords X) ((0 : ℝ) • a))) j = levelField X j := by
  rw [zero_smul, leftChart_zero, ofCoords_toCoords (hX.2 0 (Nat.zero_le _))]
theorem hasDerivAt_levelField_line {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ}
    (hj : j ≤ k) (b : Edge L n k j) (a : ChainIndex L n k → ComplexMatrix2) :
    HasDerivAt (fun r : ℝ => levelField (ofCoords (leftChart (toCoords X) (r • a))) j b)
      (levelFieldDeriv X j b (a * toCoords X)) 0 :=
  hasDerivAt_comp_leftChart_line (contDiffAt_levelField_coords hX hj b) a
theorem expTwist_zero {j : ℕ} {W : Edge L n k j → ComplexMatrix2} (hW : W ∈ fieldSpace L n k j)
    (M : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • M) W = W := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply, matExp_I_line_zero, one_mul]
  · simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply, matExp_I_line_zero, one_mul]
    exact (hW.2 b.opposite (Set.mem_univ _)).symm
theorem hasDerivAt_expTwist_line {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ}
    (hj : j ≤ k) (a : ChainIndex L n k → ComplexMatrix2) (M : Edge L n k j → ComplexMatrix2)
    (ih : ∀ b, b.IsPositivelyOriented → levelFieldDeriv X j b (a * toCoords X) =
      (Complex.I • M b) * levelField X j b) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • M) (levelField X j))
      (fun b => levelFieldDeriv X j b (a * toCoords X)) 0 := by
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
        fun t : ℝ =>
          (ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • M c)) * levelField X j c)⁻¹ := by
      funext t
      simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply, hc]
    have h1 := (hasDerivAt_matExp_I_line (M c)).mul_const (levelField X j c)
    have h0 : ComplexMatrix2.matExp (Complex.I • (((0 : ℝ) : ℂ) • M c)) * levelField X j c =
        levelField X j c := by
      simp only [matExp_I_line_zero, one_mul]
    have h2 := hasDerivAt_inv_matrix h1 (by rw [h0]; exact isUnit_det_of_mem_fieldSpace hr c)
    rw [e]
    refine h2.congr_deriv ?_
    have h3 := hasDerivAt_levelField_line hX hj c a
    have h4 := hasDerivAt_levelField_line hX hj b a
    have h5 := hasDerivAt_inv_matrix h3
      (by rw [levelField_leftChart_zero hX a j]; exact isUnit_det_of_mem_fieldSpace hr c)
    have e2 : (fun r : ℝ => levelField (ofCoords (leftChart (toCoords X) (r • a))) j b) =
        fun r : ℝ => (levelField (ofCoords (leftChart (toCoords X) (r • a))) j c)⁻¹ := by
      funext r
      exact levelField_ofCoords_opposite _ hj hb
    rw [e2] at h4
    have h6 := h4.unique h5
    rw [h6, ih c hp, levelField_leftChart_zero hX a j, h0]
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
include hd
theorem levelFieldDeriv_eq_tangentTransport {X : ChainPoint L n k} (hX : IsCompactValued X)
    (ξ : LevelForms L n k) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j, b.IsPositivelyOriented →
      levelFieldDeriv X j b (tangentCoords ξ * toCoords X) =
        (Complex.I • tangentTransport X ξ j b) * levelField X j b := by
  intro j
  induction j with
  | zero =>
    intro _ b hb
    have e : (fun w : ChainIndex L n k → ComplexMatrix2 => levelField (ofCoords w) 0 b) =
        fun w => w (Sum.inl ⟨b, hb⟩) := by
      funext w
      have e0 : levelField (ofCoords w) 0 b =
          fieldOfPositiveValues (fun b => w (Sum.inl b)) b := rfl
      rw [e0, fieldOfPositiveValues_pos _ hb]
    have h : fderiv ℝ (fun w : ChainIndex L n k → ComplexMatrix2 => w (Sum.inl ⟨b, hb⟩))
        (toCoords X) =
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ChainIndex L n k => ComplexMatrix2)
          (Sum.inl ⟨b, hb⟩ : ChainIndex L n k) :=
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ChainIndex L n k => ComplexMatrix2)
        (Sum.inl ⟨b, hb⟩ : ChainIndex L n k) (toCoords X)).fderiv
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
    set d := tangentCoords ξ * toCoords X with hd'
    have hP : ContDiffAt ℝ 2 (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b)
        (levelField X j) :=
      contDiffAt_normalizedMean (V := fun V => V) (y₀ := levelField X j)
        (fun b' => (contDiff_apply ℝ ComplexMatrix2 b').contDiffAt)
        (isUnit_det_of_mem_fieldSpace hr) b hs hl
    have hPd := (hP.differentiableAt (by norm_num)).hasFDerivAt
    set DP := fderiv ℝ (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b)
      (levelField X j) with hDP
    set vel : Edge L n k j → ComplexMatrix2 := fun b' => levelFieldDeriv X j b' d with hvel
    have hA := hasDerivAt_expTwist_line hX hj' (tangentCoords ξ) (tangentTransport X ξ j) (ih hj')
    have hB : HasDerivAt
        (fun r : ℝ => levelField (ofCoords (leftChart (toCoords X) (r • tangentCoords ξ))) j)
        vel 0 :=
      hasDerivAt_pi.2 fun b' => hasDerivAt_levelField_line hX hj' b' (tangentCoords ξ)
    have hPA : HasDerivAt (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist
        ((t : ℂ) • tangentTransport X ξ j) (levelField X j)) b) (DP vel) 0 := by
      have h1 : HasFDerivAt (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b) DP
          (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • tangentTransport X ξ j) (levelField X j)) := by
        rw [expTwist_zero hr]; exact hPd
      exact h1.comp_hasDerivAt (0 : ℝ) hA
    have hPB : HasDerivAt (fun r : ℝ => normalizedMean
        (levelField (ofCoords (leftChart (toCoords X) (r • tangentCoords ξ))) j) b)
        (DP vel) 0 := by
      have h1 : HasFDerivAt (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b) DP
          (levelField (ofCoords (leftChart (toCoords X) ((0 : ℝ) • tangentCoords ξ))) j) := by
        rw [levelField_leftChart_zero hX]; exact hPd
      exact h1.comp_hasDerivAt (0 : ℝ) hB
    have hN : HasDerivAt (fun r : ℝ => leftChart (toCoords X) (r • tangentCoords ξ)
        (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩ : ChainIndex L n k)) (d (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩)) 0 :=
      (hasDerivAt_pi.1 (hasDerivAt_leftChart_line (toCoords X) (tangentCoords ξ))) _
    have hL := hN.mul hPB
    have hL0 := hasDerivAt_levelField_line hX hj b (tangentCoords ξ)
    have e1 : (fun r : ℝ =>
        levelField (ofCoords (leftChart (toCoords X) (r • tangentCoords ξ))) (j + 1) b) =
        (fun r : ℝ => leftChart (toCoords X) (r • tangentCoords ξ)
          (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩ : ChainIndex L n k)) *
          fun r : ℝ => normalizedMean
            (levelField (ofCoords (leftChart (toCoords X) (r • tangentCoords ξ))) j) b := by
      funext r
      rw [levelField_succ_pos _ h hb]
      rfl
    rw [e1] at hL0
    have hval := hL0.unique hL
    have hc0 : leftChart (toCoords X) ((0 : ℝ) • tangentCoords ξ)
        (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩ : ChainIndex L n k) = n₀ := by
      rw [zero_smul, leftChart_zero]
      rfl
    have hu0 : normalizedMean
        (levelField (ofCoords (leftChart (toCoords X) ((0 : ℝ) • tangentCoords ξ))) j) b = u := by
      rw [levelField_leftChart_zero hX]
    rw [hc0, hu0] at hval
    have hun : u ∈ PeriodicLattice.compactGaugeGroup := by
      have := compact_of_quaternion (contourMean_mem_quaternionMatrices hrr b)
        (det_contourMean_ne_zero hl)
      exact this
    have hnr : n₀ ∈ PeriodicLattice.compactGaugeGroup := hX.1 _ _
    have huu : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv _ (compact_isUnit_det hun)
    have huu' : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul _ (compact_isUnit_det hun)
    have hnn : n₀⁻¹ * n₀ = 1 := Matrix.nonsing_inv_mul _ (compact_isUnit_det hnr)
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
        Complex.I⁻¹ •
        deriv (fun t : ℝ => ComplexMatrix2.logSeries (normalizedMean (PeriodicLattice.expTwist
          ((t : ℂ) • tangentTransport X ξ j) (levelField X j)) b * u⁻¹)) 0 := by
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
end TangentCoordinates
section CompactPoints
variable {L n k : ℕ} [NeZero L]
theorem isCompactValued_of_meanRadius_ne
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X' : ChainPoint L n k} (hb : X'.fine ∈ fieldSpace L n k 0)
    (hn : ∀ i c, X'.noise i c ∈ PeriodicLattice.compactGaugeGroup)
    (hl : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)), meanRadius (levelField X' i) c.1 ≠ 0) :
    IsCompactValued X' := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.isCompactValued_of_meanRadius_ne_zero <;> assumption
theorem eventually_isCompactValued
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) {p : ℝ → ChainIndex L n k → ComplexMatrix2}
    (hp : ContinuousAt p 0) (h0 : p 0 = toCoords X)
    (hr : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ ι, p r ι ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ᶠ r in 𝓝 (0 : ℝ), IsCompactValued (ofCoords (p r)) := by
  have h1 : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)), ∀ᶠ r in 𝓝 (0 : ℝ),
      meanRadius (levelField (ofCoords (p r)) i) c.1 ≠ 0 := by
    intro i c
    set f : (ChainIndex L n k → ComplexMatrix2) → ℂ :=
      fun w => meanRadius (levelField (ofCoords w) i) c.1 with hf
    have hc : ContinuousAt f (toCoords X) := (contDiffAt_meanRadius_coords hX i c).continuousAt
    have hc' : ContinuousAt f (p 0) := by rw [h0]; exact hc
    have hcomp : ContinuousAt (f ∘ p) 0 := ContinuousAt.comp (f := p) hc' hp
    have hne : (f ∘ p) 0 ≠ 0 := by
      have e : ofCoords (p 0) = X := by rw [h0, ofCoords_toCoords (hX.2 0 (Nat.zero_le _))]
      change meanRadius (levelField (ofCoords (p 0)) i) c.1 ≠ 0
      rw [e]
      exact meanRadius_ne_zero hX i c
    exact hcomp.eventually_ne hne
  have h2 : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      meanRadius (levelField (ofCoords (p r)) i) c.1 ≠ 0 :=
    eventually_all.2 fun i => eventually_all.2 fun c => h1 i c
  filter_upwards [h2, hr] with r h3 h4
  have hb : (ofCoords (p r)).fine ∈ fieldSpace L n k 0 :=
    fieldOfPositiveValues_mem (w := fun b => p r (Sum.inl b)) (fun c => h4 (Sum.inl c))
      (hxor 0 (Nat.zero_le _))
  have hn : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (ofCoords (p r)).noise i c ∈ PeriodicLattice.compactGaugeGroup :=
    fun i c => h4 (Sum.inr ⟨i, c⟩)
  exact isCompactValued_of_meanRadius_ne hxor hb hn h3
theorem edgeForm_apply_mem {j : ℕ} (B : edgeFormSpace L n k j) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    (B : Edge L n k j → ComplexMatrix2) b ∈ ComplexMatrix2.hermitianTraceless := B.2.1 b hb
theorem tangentCoords_smul_apply (ξ : LevelForms L n k) (r : ℝ) (ι : ChainIndex L n k) :
    ∃ A ∈ ComplexMatrix2.hermitianTraceless, (r • tangentCoords ξ) ι = Complex.I • A := by
  rcases ι with b | p
  · refine ⟨r • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1,
      ComplexMatrix2.hermitianTraceless.smul_mem r (edgeForm_apply_mem ξ.1 b.2), ?_⟩
    change r • (Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1) = _
    rw [smul_comm]
  · refine ⟨r • (ξ.2 p.1 : Edge L n k (p.1 + 1) → ComplexMatrix2) p.2.1,
      ComplexMatrix2.hermitianTraceless.smul_mem r (edgeForm_apply_mem (ξ.2 p.1) p.2.2), ?_⟩
    change r • (Complex.I • (ξ.2 p.1 : Edge L n k (p.1 + 1) → ComplexMatrix2) p.2.1) = _
    rw [smul_comm]
theorem toCoords_mem_compact {X : ChainPoint L n k} (hX : IsCompactValued X)
    (ι : ChainIndex L n k) :
    toCoords X ι ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.toCoordinates_mem_compact <;> assumption
theorem continuousAt_leftChart_line (x a : ChainIndex L n k → ComplexMatrix2) :
    ContinuousAt (fun r : ℝ => leftChart x (r • a)) 0 :=
  (hasDerivAt_leftChart_line x a).continuousAt
theorem eventually_isCompactValued_leftChart
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (ξ : LevelForms L n k) :
    ∀ᶠ r in 𝓝 (0 : ℝ),
      IsCompactValued (ofCoords (leftChart (toCoords X) (r • tangentCoords ξ))) := by
  refine eventually_isCompactValued hxor hX (continuousAt_leftChart_line _ _)
    (by simp [leftChart_zero]) (Eventually.of_forall fun r ι => ?_)
  obtain ⟨A, hA, e⟩ := tangentCoords_smul_apply ξ r ι
  rw [leftChart_apply, e]
  exact compact_mul (matExp_I_smul_mem_compact hA) (toCoords_mem_compact hX ι)
end CompactPoints
section LieAlgebra
theorem star_inv_I_smul (A : ComplexMatrix2) : star (Complex.I⁻¹ • A) = Complex.I • star A := by
  rw [star_smul]
  simp [Complex.inv_I]
theorem inv_I_smul_deriv_mem (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {m : ℝ → ComplexMatrix2}
    {m' : ComplexMatrix2} (hm : HasDerivAt m m' 0) (h0 : m 0 = 1)
    (hr : ∀ᶠ r in 𝓝 (0 : ℝ), m r ∈ PeriodicLattice.compactGaugeGroup) :
    Complex.I⁻¹ • m' ∈ ComplexMatrix2.hermitianTraceless := by
  have hs : HasDerivAt (fun r => star (m r)) (star m') 0 := hm.star
  have hp := hm.mul hs
  have hc : (m * fun r => star (m r)) =ᶠ[𝓝 0] fun _ => (1 : ComplexMatrix2) := by
    filter_upwards [hr] with r h
    exact Matrix.mem_unitaryGroup_iff.1 (Matrix.mem_specialUnitaryGroup_iff.1 h).1
  have h1 := (hp.congr_of_eventuallyEq hc.symm).unique
    (hasDerivAt_const (0 : ℝ) (1 : ComplexMatrix2))
  rw [h0] at h1
  simp only [star_one, mul_one, one_mul] at h1
  have h2 : star m' = -m' := eq_neg_of_add_eq_zero_right h1
  have h3 := ((hd.1 {r | m r ∈ PeriodicLattice.compactGaugeGroup} m m m m' m' m' hr hm hm hm).2.1
    h0).2.2.2 (fun t ht => compact_det ht)
  refine ⟨?_, ?_⟩
  · change _ = star _
    rw [star_inv_I_smul, h2, Complex.inv_I]
    simp
  · simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul] at h3 ⊢
    rw [h3.1, smul_zero]
end LieAlgebra
section EdgeForms
variable {L n k j : ℕ}
theorem edgeForm_ext {A B : edgeFormSpace L n k j}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      (A : Edge L n k j → ComplexMatrix2) b = (B : Edge L n k j → ComplexMatrix2) b) : A = B := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.edgeForm_ext <;> assumption
theorem extendOddly_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
theorem extendOddly_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Edge L n k j → ComplexMatrix2)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace L n k j := by apply _root_.YangMills.SharedProofs.p1442 <;> assumption
theorem conjugateBy_mem {g A : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy g A ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p2904 <;> assumption
end EdgeForms
section SecondOrderIdentities
variable {L n k : ℕ} [NeZero L]
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
include hd
theorem tangentTransport_eq {X : ChainPoint L n k} (hX : IsCompactValued X) (ξ : LevelForms L n k)
    {j : ℕ} (hj : j ≤ k) {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    tangentTransport X ξ j b =
      Complex.I⁻¹ • (levelFieldDeriv X j b (tangentCoords ξ * toCoords X) *
        (levelField X j b)⁻¹) := by
  have hW : levelField X j b ∈ PeriodicLattice.compactGaugeGroup :=
    (hX.2 j hj).1 b (Set.mem_univ _)
  rw [levelFieldDeriv_eq_tangentTransport hd hX ξ j hj b hb, mul_assoc,
    Matrix.mul_nonsing_inv _ (compact_isUnit_det hW), mul_one,
    smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
theorem tangentTransport_mem
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (ξ : LevelForms L n k)
    {j : ℕ} (hj : j ≤ k) {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    tangentTransport X ξ j b ∈ ComplexMatrix2.hermitianTraceless := by
  have hW : levelField X j b ∈ PeriodicLattice.compactGaugeGroup :=
    (hX.2 j hj).1 b (Set.mem_univ _)
  rw [tangentTransport_eq hd hX ξ hj hb]
  refine inv_I_smul_deriv_mem hd
    (m := fun r => levelField (ofCoords (leftChart (toCoords X) (r • tangentCoords ξ))) j b *
      (levelField X j b)⁻¹) ((hasDerivAt_levelField_line hX hj b (tangentCoords ξ)).mul_const _)
    ?_ ?_
  · simp only [levelField_leftChart_zero hX]
    exact Matrix.mul_nonsing_inv _ (compact_isUnit_det hW)
  · filter_upwards [eventually_isCompactValued_leftChart hxor hX ξ] with r hr
    exact compact_mul ((hr.2 j hj).1 b (Set.mem_univ _)) (compact_inv hW)
theorem tangentTransport_mem_edgeFormSpace
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (ξ : LevelForms L n k)
    {j : ℕ} (hj : j ≤ k) : tangentTransport X ξ j ∈ edgeFormSpace L n k j := by
  cases j with
  | zero => exact ξ.1.2
  | succ j =>
    have h : j < k := hj
    obtain ⟨f, hf⟩ : ∃ f, tangentTransport X ξ (j + 1) = extendOddly f := by
      simp only [tangentTransport, dif_pos h]
      exact ⟨_, rfl⟩
    rw [hf]
    refine extendOddly_mem (hxor _ hj) f fun b hb => ?_
    rw [← extendOddly_pos f hb, ← hf]
    exact tangentTransport_mem hd hxor hX ξ hj hb
end SecondOrderIdentities
section GaugeConstraints
variable {L n k : ℕ} [NeZero L]
theorem conjugateBy_add (g A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (A + B) =
      ComplexMatrix2.conjugateBy g A + ComplexMatrix2.conjugateBy g B := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (g : ComplexMatrix2) (r : ℝ) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (r • A) = r • ComplexMatrix2.conjugateBy g A := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.conjugateBy_real_smul <;> assumption
theorem vertexFunction_apply_mem {j : ℕ} (l : vertexFunctionSpace L n k j) (x : Vertex L n k j) :
    (l : Vertex L n k j → ComplexMatrix2) x ∈ ComplexMatrix2.hermitianTraceless :=
  l.2 x (Set.mem_univ x)
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
  (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
include hd hxor
end GaugeConstraints
section Reindexing
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
theorem familyDiameter_comp_equiv (e : ι ≃ κ) (V : κ → ComplexMatrix2) :
    ComplexMatrix2.familyDiameter (V ∘ e) = ComplexMatrix2.familyDiameter V := by apply _root_.YangMills.SharedProofs.p70753 <;> assumption
theorem complexLogMean_comp_equiv (e : ι ≃ κ) (V : κ → ComplexMatrix2) :
    PeriodicLattice.complexLogMean (V ∘ e) = PeriodicLattice.complexLogMean V := by apply _root_.YangMills.Construction.Averaging.ExplicitRadiiProof.complexLogMean_comp_equiv <;> assumption
end Reindexing
section HolomorphicCurves
variable {L n k j : ℕ} [NeZero L]
theorem hasDerivAt_inv_matrix_complex {f : ℂ → ComplexMatrix2} {f' : ComplexMatrix2}
    (hf : HasDerivAt f f' 0) (hu : IsUnit (f 0).det) :
    HasDerivAt (fun t => (f t)⁻¹) (-((f 0)⁻¹ * f' * (f 0)⁻¹)) 0 := by
  have hu' : IsUnit (f 0) := (Matrix.isUnit_iff_isUnit_det _).2 hu
  obtain ⟨u, hu2⟩ := hu'
  have h := hasFDerivAt_ringInverse (𝕜 := ℂ) u
  rw [hu2] at h
  have h2 := h.comp_hasDerivAt (0 : ℂ) hf
  have e : (fun t => (f t)⁻¹) = Ring.inverse ∘ f := by
    funext t; simp [Matrix.nonsing_inv_eq_ringInverse]
  rw [e]
  refine h2.congr_deriv ?_
  have e2 : ((u⁻¹ : ComplexMatrix2ˣ) : ComplexMatrix2) = (f 0)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu2, Ring.inverse_unit]
  simp [e2, ContinuousLinearMap.mulLeftRight_apply, mul_assoc]
theorem hasDerivAt_matExp_I_complexLine (M : ComplexMatrix2) :
    HasDerivAt (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • M))) (Complex.I • M) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.HolDifferentialAtOneProof.hasDerivAt_matExp_I_smul <;> assumption
theorem matExp_I_complexLine_zero (M : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • M)) = 1 := by
  rw [zero_smul, smul_zero]
  exact NormedSpace.exp_zero
def expTwistVelocity (W B : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) : ComplexMatrix2 :=
  open Classical in
  if b.IsPositivelyOriented then (Complex.I • B b) * W b
  else -((W b.opposite)⁻¹ * ((Complex.I • B b.opposite) * W b.opposite) * (W b.opposite)⁻¹)
theorem hasDerivAt_expTwist_complexLine (W B : Edge L n k j → ComplexMatrix2)
    (hW : W ∈ fieldSpace L n k j) :
    HasDerivAt (fun t : ℂ => PeriodicLattice.expTwist (t • B) W) (expTwistVelocity W B) 0 := by
  refine hasDerivAt_pi.2 fun b => ?_
  by_cases hb : b.IsPositivelyOriented
  · have e : (fun t : ℂ => PeriodicLattice.expTwist (t • B) W b) =
        fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B b)) * W b := by
      funext t
      simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply]
    rw [e]
    simp only [expTwistVelocity, if_pos hb]
    exact (hasDerivAt_matExp_I_complexLine (B b)).mul_const _
  · set c := b.opposite with hc
    have e : (fun t : ℂ => PeriodicLattice.expTwist (t • B) W b) =
        fun t : ℂ => (ComplexMatrix2.matExp (Complex.I • (t • B c)) * W c)⁻¹ := by
      funext t
      simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply, hc]
    have h1 := (hasDerivAt_matExp_I_complexLine (B c)).mul_const (W c)
    have h0 : ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • B c)) * W c = W c := by
      rw [matExp_I_complexLine_zero, one_mul]
    have h2 := hasDerivAt_inv_matrix_complex h1
      (by rw [h0]; exact isUnit_det_of_mem_fieldSpace hW c)
    rw [e]
    simp only [expTwistVelocity, if_neg hb]
    refine h2.congr_deriv ?_
    rw [h0]
theorem expTwistVelocity_add (W B B' : Edge L n k j → ComplexMatrix2) :
    expTwistVelocity W (B + B') = expTwistVelocity W B + expTwistVelocity W B' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [expTwistVelocity, if_pos hb, Pi.add_apply, smul_add, add_mul]
  · simp only [expTwistVelocity, if_neg hb, Pi.add_apply, smul_add, add_mul, mul_add]
    abel
theorem expTwistVelocity_smul (W B : Edge L n k j → ComplexMatrix2) (r : ℝ) :
    expTwistVelocity W (r • B) = r • expTwistVelocity W B := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [expTwistVelocity, if_pos hb, Pi.smul_apply]
    rw [smul_comm, smul_mul_assoc]
  · simp only [expTwistVelocity, if_neg hb, Pi.smul_apply]
    rw [smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_neg]
theorem differentiableAt_pathHolonomy {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {y₀ : Y}
    {V : Y → Edge L n k j → ComplexMatrix2} (hV : ∀ b, DifferentiableAt ℂ (fun y => V y b) y₀)
    (Γ : List (Edge L n k j)) :
    DifferentiableAt ℂ (fun y => PeriodicLattice.pathHolonomy (V y) Γ) y₀ := by
  induction Γ with
  | nil => simp [PeriodicLattice.pathHolonomy]
  | cons b Γ ih =>
    simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons] at ih ⊢
    exact (hV b).mul ih
theorem det_pathHolonomy_eq_one {V : Edge L n k j → ComplexMatrix2} (hV : ∀ b, (V b).det = 1)
    (Γ : List (Edge L n k j)) : (PeriodicLattice.pathHolonomy V Γ).det = 1 := by
  induction Γ with
  | nil => simp [PeriodicLattice.pathHolonomy]
  | cons b Γ ih =>
    simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons,
      Matrix.det_mul] at ih ⊢
    rw [hV b, ih, one_mul]
theorem det_expTwist (W B : Edge L n k j → ComplexMatrix2) (hW : W ∈ fieldSpace L n k j)
    (hB : B ∈ edgeFormSpace L n k j) (t : ℂ) (b : Edge L n k j) :
    (PeriodicLattice.expTwist (t • B) W b).det = 1 := by
  have htr : ∀ c : Edge L n k j, c.IsPositivelyOriented →
      (ComplexMatrix2.matExp (Complex.I • (t • B c))).det = 1 := by
    intro c hc
    refine SpinHarmonics.det_matExp_of_trace_eq_zero ?_
    have h2 : ComplexMatrix2.fullTrace (B c) = 0 := (hB.1 c hc).2
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul] at h2 ⊢
    simp [h2]
  by_cases hb : b.IsPositivelyOriented
  · simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply, Matrix.det_mul]
    rw [htr b hb, compact_det (hW.1 b (Set.mem_univ _)), one_mul]
  · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
    simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply, Matrix.det_nonsing_inv,
      Matrix.det_mul]
    rw [htr _ hp, compact_det (hW.1 _ (Set.mem_univ _)), one_mul]
    simp
theorem hasDerivAt_ofReal_zero : HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) 0 :=
  (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).congr_deriv (by simp)
theorem hasDerivAt_restrict_real_line {g : ℂ → ComplexMatrix2} {g' : ComplexMatrix2}
    (h : HasDerivAt g g' 0) :
    HasDerivAt (fun r : ℝ => g (r : ℂ)) g' 0 := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.hasDerivAt_ofReal_of_complex <;> assumption
theorem expTwist_real_mem {W B : Edge L n k j → ComplexMatrix2} (hW : W ∈ fieldSpace L n k j)
    (hB : B ∈ edgeFormSpace L n k j) (r : ℝ) (b : Edge L n k j) :
    PeriodicLattice.expTwist ((r : ℂ) • B) W b ∈ PeriodicLattice.compactGaugeGroup := by
  have hw : ∀ c : Edge L n k j, c.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • ((r : ℂ) • B c)) * W c ∈
        PeriodicLattice.compactGaugeGroup := by
    intro c hc
    refine compact_mul (matExp_I_smul_mem_compact ?_) (hW.1 c (Set.mem_univ _))
    rw [Complex.coe_smul]
    exact ComplexMatrix2.hermitianTraceless.smul_mem r (hB.1 c hc)
  by_cases hb : b.IsPositivelyOriented
  · simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply]
    exact hw b hb
  · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
    simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply]
    exact compact_inv (hw _ hp)
section ContourMeans
variable (hMF : ∀ m : ℕ, 1 ≤ m → Averaging.ComplexLogMeanProperties m)
include hMF
variable {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
theorem exists_contourLogMean_deriv {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldSpace L n k j)
    [Nonempty (PeriodicLattice.AxisOrdering y x)]
    (hs : ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies W y x) <
      Averaging.centreOfMassDiameter) :
    ∃ D : (Edge L n k j → ComplexMatrix2) →L[ℂ] ComplexMatrix2, ∀ B ∈ edgeFormSpace L n k j,
      HasDerivAt (fun t : ℂ => PeriodicLattice.complexMeanContourHolonomy
        (PeriodicLattice.expTwist (t • B) W) y x) (D (expTwistVelocity W B)) 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℂ), ComplexMatrix2.familyDiameter
        (PeriodicLattice.contourHolonomies (PeriodicLattice.expTwist (t • B) W) y x) <
          Averaging.centreOfMassDiameter := by
  set m := Fintype.card (PeriodicLattice.AxisOrdering y x) with hm
  have hm1 : 1 ≤ m := Fintype.card_pos
  let e : Fin m ≃ PeriodicLattice.AxisOrdering y x := (Fintype.equivFin _).symm
  let fam : (Edge L n k j → ComplexMatrix2) → Fin m → ComplexMatrix2 :=
    fun V => PeriodicLattice.contourHolonomies V y x ∘ e
  have hfam : ∀ V, PeriodicLattice.complexMeanContourHolonomy V y x =
      PeriodicLattice.complexLogMean (fam V) :=
    fun V => (complexLogMean_comp_equiv e _).symm
  have hx : fam W ∈ Averaging.smallComplexFamilies m := by
    refine ⟨fun i => compact_det (compact_pathHolonomy (fun b => hW.1 b (Set.mem_univ _)) _), ?_⟩
    rw [familyDiameter_comp_equiv]
    exact hs
  obtain ⟨hopen, -, hF⟩ := (hMF m hm1).holomorphicInEntries
  obtain ⟨F, hFa, hFe⟩ := hF _ hx
  obtain ⟨O, hO, hDO⟩ := (hMF m hm1).isOpen
  have hfd : DifferentiableAt ℂ fam W := by
    refine differentiableAt_pi.2 fun i => ?_
    exact differentiableAt_pathHolonomy (V := fun V : Edge L n k j → ComplexMatrix2 => V)
      (fun b => differentiableAt_apply _ _) _
  have hFd : DifferentiableAt ℂ F (fam W) := hFa.differentiableAt
  let h : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2 := fun V => F (fam V) ()
  have hhd : DifferentiableAt ℂ h W := by
    have h1 : DifferentiableAt ℂ (fun V => F (fam V)) W := hFd.comp W hfd
    exact (differentiableAt_pi.1 h1) ()
  refine ⟨fderiv ℂ h W, fun B hB => ?_⟩
  have hA := hasDerivAt_expTwist_complexLine W B hW
  have hA0 : PeriodicLattice.expTwist ((0 : ℂ) • B) W = W := by
    have := expTwist_zero hW B
    simpa using this
  have hh' : HasFDerivAt h (fderiv ℂ h W) (PeriodicLattice.expTwist ((0 : ℂ) • B) W) := by
    rw [hA0]; exact hhd.hasFDerivAt
  have hcomp := hh'.comp_hasDerivAt (0 : ℂ) hA
  have hcont : ContinuousAt (fun t : ℂ => fam (PeriodicLattice.expTwist (t • B) W)) 0 := by
    have h1 : ContinuousAt fam (PeriodicLattice.expTwist ((0 : ℂ) • B) W) := by
      rw [hA0]; exact hfd.continuousAt
    exact ContinuousAt.comp (f := fun t : ℂ => PeriodicLattice.expTwist (t • B) W) h1
      hA.continuousAt
  have hval0 : fam (PeriodicLattice.expTwist ((0 : ℂ) • B) W) = fam W := by rw [hA0]
  have hxO : fam W ∈ O := by
    rw [hDO] at hx; exact hx.1
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), fam (PeriodicLattice.expTwist (t • B) W) ∈
      Averaging.smallComplexFamilies m := by
    have h1 : ∀ᶠ t in 𝓝 (0 : ℂ), fam (PeriodicLattice.expTwist (t • B) W) ∈ O := by
      refine hcont.eventually_mem (hO.mem_nhds ?_)
      rw [hval0]; exact hxO
    filter_upwards [h1] with t ht
    rw [hDO]
    exact ⟨ht, fun i => det_pathHolonomy_eq_one (det_expTwist W B hW hB t) _⟩
  have hF2 : ∀ᶠ t in 𝓝 (0 : ℂ), PeriodicLattice.complexLogMean
      (fam (PeriodicLattice.expTwist (t • B) W)) =
        F (fam (PeriodicLattice.expTwist (t • B) W)) () := by
    have h1 : Tendsto (fun t : ℂ => fam (PeriodicLattice.expTwist (t • B) W)) (𝓝 0)
        (𝓝[Averaging.smallComplexFamilies m] fam W) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, hnear⟩
      have := hcont.tendsto
      rwa [hval0] at this
    have h2 := h1.eventually hFe
    filter_upwards [h2] with t ht
    exact congrFun ht ()
  have hEq : (fun t : ℂ => PeriodicLattice.complexMeanContourHolonomy
      (PeriodicLattice.expTwist (t • B) W) y x) =ᶠ[𝓝 0] h ∘ fun t : ℂ =>
        PeriodicLattice.expTwist (t • B) W := by
    filter_upwards [hF2] with t ht
    rw [hfam, ht]
    rfl
  refine ⟨hcomp.congr_of_eventuallyEq hEq, ?_⟩
  filter_upwards [hnear] with t ht
  have h3 := ht.2
  rwa [familyDiameter_comp_equiv] at h3
theorem complexMeanContourHolonomy_mem {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup)
    [Nonempty (PeriodicLattice.AxisOrdering y x)]
    (hs : ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies V y x) <
      Averaging.centreOfMassDiameter) :
    PeriodicLattice.complexMeanContourHolonomy V y x ∈ PeriodicLattice.compactGaugeGroup := by
  set m := Fintype.card (PeriodicLattice.AxisOrdering y x) with hm
  have hm1 : 1 ≤ m := Fintype.card_pos
  let e : Fin m ≃ PeriodicLattice.AxisOrdering y x := (Fintype.equivFin _).symm
  have h1 : PeriodicLattice.complexMeanContourHolonomy V y x =
      PeriodicLattice.complexLogMean (PeriodicLattice.contourHolonomies V y x ∘ e) :=
    (complexLogMean_comp_equiv e _).symm
  rw [h1]
  refine (hMF m hm1).memRealGroup _ (fun i => compact_pathHolonomy hV _) ?_
  rw [familyDiameter_comp_equiv]
  exact hs
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
include hd
theorem logDirectionalDeriv_contour_eq {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldSpace L n k j)
    [Nonempty (PeriodicLattice.AxisOrdering y x)]
    (hs : ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies W y x) <
      Averaging.centreOfMassDiameter) :
    ∃ D : (Edge L n k j → ComplexMatrix2) →L[ℂ] ComplexMatrix2, ∀ B ∈ edgeFormSpace L n k j,
      logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X W) y x)
        (PeriodicLattice.complexMeanContourHolonomy W y x) B =
        Complex.I⁻¹ • (D (expTwistVelocity W B) *
          (PeriodicLattice.complexMeanContourHolonomy W y x)⁻¹) ∧
      Complex.I⁻¹ • (D (expTwistVelocity W B) *
          (PeriodicLattice.complexMeanContourHolonomy W y x)⁻¹) ∈
        ComplexMatrix2.hermitianTraceless := by
  have hWr : ∀ b, W b ∈ PeriodicLattice.compactGaugeGroup := fun b => hW.1 b (Set.mem_univ _)
  set g₀ := PeriodicLattice.complexMeanContourHolonomy W y x with hg₀
  have hg₀r : g₀ ∈ PeriodicLattice.compactGaugeGroup := complexMeanContourHolonomy_mem hMF hWr hs
  have hgg : g₀ * g₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ (compact_isUnit_det hg₀r)
  obtain ⟨D, hD⟩ := exists_contourLogMean_deriv hMF hW hs
  refine ⟨D, fun B hB => ?_⟩
  obtain ⟨h1, hnear⟩ := hD B hB
  have hA0 : PeriodicLattice.expTwist ((0 : ℂ) • B) W = W := by
    have := expTwist_zero hW B
    simpa using this
  have hY := h1.mul_const g₀⁻¹
  have hY0 : (fun t : ℂ => PeriodicLattice.complexMeanContourHolonomy
      (PeriodicLattice.expTwist (t • B) W) y x * g₀⁻¹) 0 = 1 := by
    simp only []
    rw [hA0]
    exact hgg
  have hlog := ((hd.2 Set.univ _ _ _ _ _ _ Filter.univ_mem hY hY hY).2.1 hY0).2.2.1
  refine ⟨?_, ?_⟩
  · unfold logDirectionalDeriv
    congr 1
    exact hlog.deriv
  · refine inv_I_smul_deriv_mem hd (m := fun r : ℝ => PeriodicLattice.complexMeanContourHolonomy
      (PeriodicLattice.expTwist ((r : ℂ) • B) W) y x * g₀⁻¹)
      (hasDerivAt_restrict_real_line hY) ?_ ?_
    · simp only [Complex.ofReal_zero]
      exact hY0
    · have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝 0) (𝓝 0) := by
        have := hasDerivAt_ofReal_zero.continuousAt.tendsto
        simpa using this
      filter_upwards [ht.eventually hnear] with r hr
      exact compact_mul (complexMeanContourHolonomy_mem hMF (expTwist_real_mem hW hB r) hr)
        (compact_inv hg₀r)
end ContourMeans
section LinearMaps
variable (hMF : ∀ m : ℕ, 1 ≤ m → Averaging.ComplexLogMeanProperties m)
  (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
theorem inverseFourthPowerWeight_smul (L : ℕ) (M : ComplexMatrix2) :
    PeriodicLattice.inverseFourthPowerWeight L • M = ((L : ℝ) ^ (-4 : ℤ)) • M := by
  rw [PeriodicLattice.inverseFourthPowerWeight, Complex.coe_smul]
include hMF in
theorem exists_adjointCubeAverage_linear {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldSpace L n k j)
    (hne : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      Nonempty (PeriodicLattice.AxisOrdering y x))
    (hs : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies W y x) <
        Averaging.centreOfMassDiameter) :
    ∃ A : vertexFunctionSpace L n k j →ₗ[ℝ] vertexFunctionSpace L n k (j + 1), ∀ l,
      (A l : Vertex L n k (j + 1) → ComplexMatrix2) =
        adjointCubeAverage W (l : Vertex L n k j → ComplexMatrix2) := by
  have hWr : ∀ b, W b ∈ PeriodicLattice.compactGaugeGroup := fun b => hW.1 b (Set.mem_univ _)
  have hfin : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := fun y => Set.toFinite _
  have hval : ∀ (l : Vertex L n k j → ComplexMatrix2) (y : Vertex L n k (j + 1)),
      adjointCubeAverage W l y = ((L : ℝ) ^ (-4 : ℤ)) • ∑ x ∈ (hfin y).toFinset,
        ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy W y x) (l x) := by
    intro l y
    rw [adjointCubeAverage, inverseFourthPowerWeight_smul,
      finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  have hmem : ∀ l : vertexFunctionSpace L n k j,
      adjointCubeAverage W (l : Vertex L n k j → ComplexMatrix2) ∈
      vertexFunctionSpace L n k (j + 1) := by
    intro l y _
    rw [hval]
    refine ComplexMatrix2.hermitianTraceless.smul_mem _
      (ComplexMatrix2.hermitianTraceless.sum_mem fun x hx => ?_)
    haveI := hne y x
    exact conjugateBy_mem (complexMeanContourHolonomy_mem hMF hWr (hs y x (by simpa using hx)))
      (vertexFunction_apply_mem l x)
  refine ⟨
    { toFun := fun l => ⟨_, hmem l⟩
      map_add' := fun l l' => ?_
      map_smul' := fun r l => ?_ }, fun l => rfl⟩
  · refine Subtype.ext (funext fun y => ?_)
    change adjointCubeAverage W (l + l' : vertexFunctionSpace L n k j).1 y =
      adjointCubeAverage W l.1 y + adjointCubeAverage W l'.1 y
    rw [hval, hval, hval, ← smul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun x _ => conjugateBy_add _ _ _
  · refine Subtype.ext (funext fun y => ?_)
    change adjointCubeAverage W (r • l : vertexFunctionSpace L n k j).1 y =
      r • adjointCubeAverage W l.1 y
    rw [hval, hval, smul_comm r]
    congr 1
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => conjugateBy_smul _ _ _
include hMF hd in
theorem exists_contourLogDrift_linear {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldSpace L n k j)
    (hne : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      Nonempty (PeriodicLattice.AxisOrdering y x))
    (hs : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies W y x) <
        Averaging.centreOfMassDiameter) :
    ∃ C : edgeFormSpace L n k j →ₗ[ℝ] vertexFunctionSpace L n k (j + 1), ∀ B,
      (C B : Vertex L n k (j + 1) → ComplexMatrix2) =
        contourLogDrift W (B : Edge L n k j → ComplexMatrix2) := by
  have hfin : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := fun y => Set.toFinite _
  let ℓ : (y : Vertex L n k (j + 1)) → Vertex L n k j → (Edge L n k j → ComplexMatrix2) →
      ComplexMatrix2 := fun y x B =>
    logDirectionalDeriv ℂ
      (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X W) y x)
      (PeriodicLattice.complexMeanContourHolonomy W y x) B
  have hval : ∀ (B : Edge L n k j → ComplexMatrix2) (y : Vertex L n k (j + 1)),
      contourLogDrift W B y = ((L : ℝ) ^ (-4 : ℤ)) • ∑ x ∈ (hfin y).toFinset, ℓ y x B := by
    intro B y
    rw [contourLogDrift, inverseFourthPowerWeight_smul,
      finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  have hterm : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      (∀ B ∈ edgeFormSpace L n k j, ℓ y x B ∈ ComplexMatrix2.hermitianTraceless) ∧
      (∀ B ∈ edgeFormSpace L n k j, ∀ B' ∈ edgeFormSpace L n k j,
        ℓ y x (B + B') = ℓ y x B + ℓ y x B') ∧
      ∀ (r : ℝ), ∀ B ∈ edgeFormSpace L n k j, ℓ y x (r • B) = r • ℓ y x B := by
    intro y x hx
    haveI := hne y x
    obtain ⟨D, hD⟩ := logDirectionalDeriv_contour_eq hMF hd hW (hs y x hx)
    refine ⟨fun B hB => ?_, fun B hB B' hB' => ?_, fun r B hB => ?_⟩
    · change logDirectionalDeriv ℂ _ _ B ∈ _
      rw [(hD B hB).1]
      exact (hD B hB).2
    · change logDirectionalDeriv ℂ _ _ (B + B') =
        logDirectionalDeriv ℂ _ _ B + logDirectionalDeriv ℂ _ _ B'
      rw [(hD _ (Submodule.add_mem _ hB hB')).1, (hD B hB).1, (hD B' hB').1,
        expTwistVelocity_add, map_add, add_mul, smul_add]
    · change logDirectionalDeriv ℂ _ _ (r • B) = r • logDirectionalDeriv ℂ _ _ B
      have e : expTwistVelocity W (r • B) = (r : ℂ) • expTwistVelocity W B := by
        rw [expTwistVelocity_smul, Complex.coe_smul]
      rw [(hD _ (Submodule.smul_mem _ r hB)).1, (hD B hB).1, e, map_smul, Complex.coe_smul,
        smul_mul_assoc, smul_comm]
  have hmem : ∀ B : edgeFormSpace L n k j,
      contourLogDrift W (B : Edge L n k j → ComplexMatrix2) ∈
      vertexFunctionSpace L n k (j + 1) := by
    intro B y _
    rw [hval]
    refine ComplexMatrix2.hermitianTraceless.smul_mem _
      (ComplexMatrix2.hermitianTraceless.sum_mem fun x hx => ?_)
    exact (hterm y x (by simpa using hx)).1 B B.2
  refine ⟨
    { toFun := fun B => ⟨_, hmem B⟩
      map_add' := fun B B' => ?_
      map_smul' := fun r B => ?_ }, fun B => rfl⟩
  · refine Subtype.ext (funext fun y => ?_)
    change contourLogDrift W (B + B' : edgeFormSpace L n k j).1 y =
      contourLogDrift W B.1 y + contourLogDrift W B'.1 y
    rw [hval, hval, hval, ← smul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun x hx =>
      (hterm y x ((hfin y).mem_toFinset.1 hx)).2.1 B.1 B.2 B'.1 B'.2
  · refine Subtype.ext (funext fun y => ?_)
    change contourLogDrift W (r • B : edgeFormSpace L n k j).1 y = r • contourLogDrift W B.1 y
    rw [hval, hval, smul_comm r]
    congr 1
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x hx => (hterm y x ((hfin y).mem_toFinset.1 hx)).2.2 r B.1 B.2
end LinearMaps
end HolomorphicCurves
section ChainDrift
variable {L n k : ℕ} [NeZero L]
theorem exists_tangentTransport_linear (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ} (hj : j ≤ k) :
    ∃ M : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k j, ∀ ξ,
      (M ξ : Edge L n k j → ComplexMatrix2) = tangentTransport X ξ j := by
  refine ⟨
    { toFun := fun ξ => ⟨tangentTransport X ξ j, tangentTransport_mem_edgeFormSpace hd hxor hX ξ hj⟩
      map_add' := fun ξ ξ' => edgeForm_ext fun b hb => ?_
      map_smul' := fun r ξ => edgeForm_ext fun b hb => ?_ }, fun ξ => rfl⟩
  · change tangentTransport X (ξ + ξ') j b = tangentTransport X ξ j b + tangentTransport X ξ' j b
    rw [tangentTransport_eq hd hX _ hj hb, tangentTransport_eq hd hX _ hj hb,
      tangentTransport_eq hd hX _ hj hb, map_add, add_mul, map_add, add_mul, smul_add]
  · change tangentTransport X (r • ξ) j b = r • tangentTransport X ξ j b
    rw [tangentTransport_eq hd hX _ hj hb, tangentTransport_eq hd hX _ hj hb, map_smul,
      smul_mul_assoc, map_smul, smul_mul_assoc, smul_comm]
theorem exists_chainDrift_linear (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hMF : ∀ m : ℕ, 1 ≤ m → Averaging.ComplexLogMeanProperties m)
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X)
    (hne : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      Nonempty (PeriodicLattice.AxisOrdering y x))
    (hs : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies (levelField X j) y x) <
        Averaging.centreOfMassDiameter) :
    ∀ j, j ≤ k → ∃ T : LevelForms L n k →ₗ[ℝ] vertexFunctionSpace L n k j, ∀ ξ,
      (T ξ : Vertex L n k j → ComplexMatrix2) = chainDrift X ξ j := by
  intro j
  induction j with
  | zero => intro _; exact ⟨0, fun ξ => rfl⟩
  | succ j ih =>
    intro hj
    have h : j < k := hj
    obtain ⟨T, hT⟩ := ih h.le
    obtain ⟨M, hM⟩ := exists_tangentTransport_linear hd hxor hX h.le
    obtain ⟨A, hA⟩ := exists_adjointCubeAverage_linear hMF (hX.2 j h.le) (hne j h) (hs j h)
    obtain ⟨C, hC⟩ := exists_contourLogDrift_linear hMF hd (hX.2 j h.le) (hne j h) (hs j h)
    refine ⟨A ∘ₗ T + C ∘ₗ M, fun ξ => ?_⟩
    change (A (T ξ) : Vertex L n k (j + 1) → ComplexMatrix2) +
      (C (M ξ) : Vertex L n k (j + 1) → ComplexMatrix2) = _
    rw [hA, hC, hT, hM]
    rfl
end ChainDrift
theorem xor_isPositive_opposite
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.xor_isPositivelyOriented_opposite <;> assumption
theorem chainDriftLinearAtMinimizer_holds (hF : MinimizerFieldsNearOne)
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hA : Averaging.BlockArguments.Holds)
    (hor : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction) :
    ChainDriftLinearAtMinimizer := by
  intro a ha L hL k n hk hn
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    xor_isPositive_opposite hor hL hn
  obtain ⟨-, -, -, hMF, hsm⟩ := hM
  let s : Conventions.StandingParameters := ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩
  obtain ⟨hω, hfam⟩ := hsm s
  have hpos : 0 < PeriodicLattice.averagingRadiusCap L := hω.1
  filter_upwards [hF a ha L hL k n hk hn (PeriodicLattice.averagingRadiusCap L) hpos] with
    V hV W hW X hLeast
  obtain ⟨hpl, -, -⟩ := hV W hW X hLeast
  have hX : IsCompactValued X := hLeast.compact
  have hs : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies (levelField X j) y x) <
        Averaging.centreOfMassDiameter := by
    intro j hj y x hx
    refine hfam (PeriodicLattice.averagingRadiusCap L) ⟨hpos, le_refl _⟩ j hj
      (PeriodicLattice.Bond.forwardFrom y 0) (levelField X j)
      ⟨hX.2 j hj.le, fun p _ => hpl j hj.le p⟩ y (Or.inl rfl) x hx
  have hne : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      Nonempty (PeriodicLattice.AxisOrdering y x) := by
    intro j hj y x
    exact (hA s j hj (PeriodicLattice.Bond.forwardFrom y 0)).axisOrdering_nonempty y (Or.inl rfl) x
  exact exists_chainDrift_linear hd (fun m hm => hMF m hm) hxor hX hne hs k le_rfl
end YangMills.Construction.RunningCouplingSlope.MinimizerDrift
end
