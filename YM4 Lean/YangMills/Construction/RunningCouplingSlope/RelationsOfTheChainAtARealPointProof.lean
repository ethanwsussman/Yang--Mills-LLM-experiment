import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreUnderAGaugeFunctionProof
import YangMills.Construction.RunningCouplingSlope.DriftOfALeastPointIsLinearProof
import YangMills.Construction.RunningCouplingSlope.FibreDirectionsAtALeastPointProof
import YangMills.Construction.RunningCouplingSlope.ChainNumberReadsNoPointProof
import YangMills.Construction.RunningCouplingSlope.MapsOfTheChainAtALeastPointProof
import YangMills.Construction.Towers.AveragingMapCovariantOnTheComplexDomain
import Mathlib
import YangMills.Construction.Matrices.SpecialUnitaryTwo
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.ChainRelationsProof
open Filter Tower Matrices
open scoped Topology
section Chart
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
def leftChart (x a : A) : A := NormedSpace.exp a * x
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
end Chart
section Smooth
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
end Smooth
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
theorem mem_quaternionMatrices_of_mem {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : g ∈ quaternionMatrices :=
  ComplexMatrix2.quaternion_entries_of_mem_specialUnitary hg
theorem det_eq_normSq_add_normSq {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices) :
    M.det = ((Complex.normSq (M 0 0) + Complex.normSq (M 0 1) : ℝ) : ℂ) :=
  ComplexMatrix2.det_quaternionMatrix hM
theorem det_mem_slitPlane {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices) (h : M.det ≠ 0) :
    M.det ∈ Complex.slitPlane :=
  ComplexMatrix2.det_quaternionMatrix_mem_slitPlane hM h
theorem normalize_mem_compact {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices) (h : M.det ≠ 0) :
    (M.det ^ (1 / 2 : ℂ))⁻¹ • M ∈ PeriodicLattice.compactGaugeGroup :=
  ComplexMatrix2.normalize_quaternionMatrix_mem_specialUnitary hM h
variable {L n k j : ℕ}
theorem compact_mul_mem {g h : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hh : h ∈ PeriodicLattice.compactGaugeGroup) :
    g * h ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
theorem compact_inv_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem compact_det {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem compact_isUnit_det {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
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
  exact mem_quaternionMatrices_of_mem (compact_mul_mem
    (compact_mul_mem (pathHolonomy_mem_compact hV _) (pathHolonomy_mem_compact hV _))
    (compact_inv_mem (pathHolonomy_mem_compact hV _)))
end Quaternions
section Values
variable {L n k j : ℕ}
theorem fieldOfPositiveValues_pos (w : PositiveEdge L n k j → ComplexMatrix2)
    {b : Edge L n k j} (h : b.IsPositivelyOriented) :
    fieldOfPositiveValues w b = w ⟨b, h⟩ := by
  simp [fieldOfPositiveValues, h]
theorem fieldOfPositiveValues_neg (w : PositiveEdge L n k j → ComplexMatrix2)
    {b : Edge L n k j} (h : ¬b.IsPositivelyOriented) :
    fieldOfPositiveValues w b =
      (w ⟨b.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented h⟩)⁻¹ := by
  simp [fieldOfPositiveValues, h, PeriodicLattice.Bond.opposite_isPositivelyOriented h]
end Values
section Levels
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
end Levels
section Families
variable {L n k : ℕ} [NeZero L] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
  {Z : Y → ChainPoint L n k}
theorem isUnit_det_of_mem_fieldSpace {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (b : Edge L n k j) :
    IsUnit (V b).det := compact_isUnit_det (hV.1 b (Set.mem_univ b))
theorem contDiffAt_levelField (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀)) :
    ∀ j, j ≤ k → ∀ b, ContDiffAt ℝ 2 (fun y => levelField (Z y) j b) y₀ := by apply _root_.YangMills.SharedProofs.p4722 <;> assumption
end Families
section Coordinates
variable {L n k : ℕ}
abbrev Coord (L n k : ℕ) : Type :=
  PositiveEdge L n k 0 ⊕ (Σ i : Fin k, PositiveEdge L n k (i + 1))
instance instFintypeCoord [NeZero L] : Fintype (Coord L n k) := Fintype.ofFinite _
def pointOfCoords (w : Coord L n k → ComplexMatrix2) : ChainPoint L n k :=
  ⟨fieldOfPositiveValues fun b => w (Sum.inl b), fun i c => w (Sum.inr ⟨i, c⟩)⟩
def coordsOfPoint (X : ChainPoint L n k) : Coord L n k → ComplexMatrix2 :=
  Sum.elim (fun b => X.fine b.1) fun p => X.noise p.1 p.2
theorem pointOfCoords_coordsOfPoint {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0) :
    pointOfCoords (coordsOfPoint X) = X := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.ofCoordinates_toCoordinates <;> assumption
variable [NeZero L]
theorem contDiffAt_pointOfCoords_fine {x : Coord L n k → ComplexMatrix2}
    (hx : ∀ b, IsUnit (x (Sum.inl b)).det)
    (b : Edge L n k 0) : ContDiffAt ℝ 2 (fun w => (pointOfCoords w).fine b) x := by
  have hc : ∀ ι : Coord L n k,
      ContDiffAt ℝ 2 (fun w : Coord L n k → ComplexMatrix2 => w ι) x := fun ι =>
    (contDiff_apply ℝ ComplexMatrix2 ι).contDiffAt
  by_cases h : b.IsPositivelyOriented
  · simp only [pointOfCoords, fieldOfPositiveValues_pos _ h]
    exact hc _
  · simp only [pointOfCoords, fieldOfPositiveValues_neg _ h]
    exact contDiffAt_inv (hc _) (hx _)
theorem contDiffAt_pointOfCoords_noise {x : Coord L n k → ComplexMatrix2} (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun w => (pointOfCoords w).noise i c) x :=
  (contDiff_apply ℝ ComplexMatrix2 (Sum.inr ⟨i, c⟩ : Coord L n k)).contDiffAt
theorem isUnit_det_coordsOfPoint {X : ChainPoint L n k} (hX : IsCompactValued X)
    (b : PositiveEdge L n k 0) :
    IsUnit (coordsOfPoint X (Sum.inl b)).det := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.isUnit_det_toCoordinates <;> assumption
theorem contDiffAt_levelField_coords {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ}
    (hj : j ≤ k) (b : Edge L n k j) :
    ContDiffAt ℝ 2 (fun w => levelField (pointOfCoords w) j b) (coordsOfPoint X) := by
  have h0 : pointOfCoords (coordsOfPoint X) = X :=
    pointOfCoords_coordsOfPoint (hX.2 0 (Nat.zero_le _))
  exact contDiffAt_levelField (Z := pointOfCoords) (y₀ := coordsOfPoint X)
    (contDiffAt_pointOfCoords_fine (isUnit_det_coordsOfPoint hX))
    (fun i c => contDiffAt_pointOfCoords_noise i c) (by rwa [h0]) j hj b
end Coordinates
section Curves
theorem hasDerivAt_matrix_inv {f : ℝ → ComplexMatrix2} {f' : ComplexMatrix2}
    (hf : HasDerivAt f f' 0) (hu : IsUnit (f 0).det) :
    HasDerivAt (fun t => (f t)⁻¹) (-((f 0)⁻¹ * f' * (f 0)⁻¹)) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.hasDerivAt_inv_matrix <;> assumption
theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
theorem matExp_I_smul_mem_compact {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
theorem exp_pi_apply {ι : Type*} [Fintype ι] (x : ι → ComplexMatrix2) (i : ι) :
    NormedSpace.exp x i = ComplexMatrix2.matExp (x i) := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.normedExp_pi_apply <;> assumption
theorem hasDerivAt_matExp_I_line (X : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • X)))
      (Complex.I • X) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.NormalizedMeanAtOneProof.hasDerivAt_matExp_smul <;> assumption
theorem matExp_I_line_zero (X : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • (((0 : ℝ) : ℂ) • X)) = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.matExp_I_line_zero <;> assumption
end Curves
section Along
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
end Along
section Tangents
variable {L n k : ℕ} [NeZero L]
instance instFintypeEdge {j : ℕ} : Fintype (Edge L n k j) := Fintype.ofFinite _
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
def levelDeriv (X : ChainPoint L n k) (j : ℕ) (b : Edge L n k j) :
    (Coord L n k → ComplexMatrix2) →L[ℝ] ComplexMatrix2 :=
  fderiv ℝ (fun w => levelField (pointOfCoords w) j b) (coordsOfPoint X)
theorem levelField_coords_neg (w : Coord L n k → ComplexMatrix2) {j : ℕ} (hj : j ≤ k)
    {b : Edge L n k j} (hb : ¬b.IsPositivelyOriented) :
    levelField (pointOfCoords w) j b = (levelField (pointOfCoords w) j b.opposite)⁻¹ := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.levelField_ofCoords_opposite <;> assumption
theorem tangentTransport_succ_pos (X : ChainPoint L n k) (ξ : LevelForms L n k) {j : ℕ}
    (h : j < k) {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    tangentTransport X ξ (j + 1) b =
      ComplexMatrix2.conjugateBy (X.noise ⟨j, h⟩ ⟨b, hb⟩)
        (leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) b) +
      (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) b := by
  simp only [tangentTransport, dif_pos h, extendOddly, if_pos hb, dif_pos hb]
theorem levelField_coords_leftChart_zero {X : ChainPoint L n k} (hX : IsCompactValued X)
    (a : Coord L n k → ComplexMatrix2) (j : ℕ) :
    levelField (pointOfCoords (leftChart (coordsOfPoint X) ((0 : ℝ) • a))) j =
      levelField X j := by
  rw [zero_smul, leftChart_zero, pointOfCoords_coordsOfPoint (hX.2 0 (Nat.zero_le _))]
theorem hasDerivAt_levelField_leftChart {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ}
    (hj : j ≤ k) (b : Edge L n k j) (a : Coord L n k → ComplexMatrix2) :
    HasDerivAt (fun r : ℝ => levelField (pointOfCoords (leftChart (coordsOfPoint X) (r • a))) j b)
      (levelDeriv X j b (a * coordsOfPoint X)) 0 :=
  hasDerivAt_comp_leftChart (contDiffAt_levelField_coords hX hj b) a
theorem expTwist_zero {j : ℕ} {W : Edge L n k j → ComplexMatrix2} (hW : W ∈ fieldSpace L n k j)
    (M : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • M) W = W := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.expTwist_zero <;> assumption
theorem hasDerivAt_expTwist {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ} (hj : j ≤ k)
    (a : Coord L n k → ComplexMatrix2) (M : Edge L n k j → ComplexMatrix2)
    (ih : ∀ b, b.IsPositivelyOriented → levelDeriv X j b (a * coordsOfPoint X) =
      (Complex.I • M b) * levelField X j b) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • M) (levelField X j))
      (fun b => levelDeriv X j b (a * coordsOfPoint X)) 0 := by
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
    have h2 := hasDerivAt_matrix_inv h1 (by rw [h0]; exact isUnit_det_of_mem_fieldSpace hr c)
    rw [e]
    refine h2.congr_deriv ?_
    have h3 := hasDerivAt_levelField_leftChart hX hj c a
    have h4 := hasDerivAt_levelField_leftChart hX hj b a
    have h5 := hasDerivAt_matrix_inv h3
      (by rw [levelField_coords_leftChart_zero hX a j]; exact isUnit_det_of_mem_fieldSpace hr c)
    have e2 : (fun r : ℝ =>
        levelField (pointOfCoords (leftChart (coordsOfPoint X) (r • a))) j b) =
        fun r : ℝ => (levelField (pointOfCoords (leftChart (coordsOfPoint X) (r • a))) j c)⁻¹ := by
      funext r
      exact levelField_coords_neg _ hj hb
    rw [e2] at h4
    have h6 := h4.unique h5
    rw [h6, ih c hp, levelField_coords_leftChart_zero hX a j, h0]
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
include hd
theorem levelDeriv_tangentCoords {X : ChainPoint L n k} (hX : IsCompactValued X)
    (ξ : LevelForms L n k) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j, b.IsPositivelyOriented →
      levelDeriv X j b (tangentCoords ξ * coordsOfPoint X) =
        (Complex.I • tangentTransport X ξ j b) * levelField X j b := by
  intro j
  induction j with
  | zero =>
    intro _ b hb
    have e : (fun w : Coord L n k → ComplexMatrix2 => levelField (pointOfCoords w) 0 b) =
        fun w => w (Sum.inl ⟨b, hb⟩) := by
      funext w
      have e0 : levelField (pointOfCoords w) 0 b =
          fieldOfPositiveValues (fun b => w (Sum.inl b)) b := rfl
      rw [e0, fieldOfPositiveValues_pos _ hb]
    have h : fderiv ℝ (fun w : Coord L n k → ComplexMatrix2 => w (Sum.inl ⟨b, hb⟩))
        (coordsOfPoint X) =
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Coord L n k => ComplexMatrix2)
          (Sum.inl ⟨b, hb⟩ : Coord L n k) :=
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Coord L n k => ComplexMatrix2)
        (Sum.inl ⟨b, hb⟩ : Coord L n k) (coordsOfPoint X)).fderiv
    have e3 : tangentTransport X ξ 0 b = (ξ.1 : Edge L n k 0 → ComplexMatrix2) b := rfl
    have e4 : levelField X 0 b = X.fine b := rfl
    rw [levelDeriv, e, h, e3, e4]
    rfl
  | succ j ih =>
    intro hj b hb
    have h : j < k := hj
    have hj' : j ≤ k := h.le
    have hr := hX.2 j hj'
    have hrr : ∀ b', levelField X j b' ∈ PeriodicLattice.compactGaugeGroup :=
      fun b' => hr.1 b' (Set.mem_univ _)
    have hl := meanRadius_ne_zero hX ⟨j, h⟩ ⟨b, hb⟩
    have hs := det_mem_slitPlane (contourMean_mem_quaternionMatrices hrr b)
      (det_contourMean_ne_zero hl)
    set n₀ := X.noise ⟨j, h⟩ ⟨b, hb⟩ with hn₀
    set u := normalizedMean (levelField X j) b with hu
    set d := tangentCoords ξ * coordsOfPoint X with hd'
    have hP : ContDiffAt ℝ 2 (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b)
        (levelField X j) :=
      contDiffAt_normalizedMean (V := fun V => V) (y₀ := levelField X j)
        (fun b' => (contDiff_apply ℝ ComplexMatrix2 b').contDiffAt)
        (isUnit_det_of_mem_fieldSpace hr) b hs hl
    have hPd := (hP.differentiableAt (by norm_num)).hasFDerivAt
    set DP := fderiv ℝ (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b)
      (levelField X j) with hDP
    set vel : Edge L n k j → ComplexMatrix2 := fun b' => levelDeriv X j b' d with hvel
    have hA := hasDerivAt_expTwist hX hj' (tangentCoords ξ) (tangentTransport X ξ j) (ih hj')
    have hB : HasDerivAt
        (fun r : ℝ => levelField (pointOfCoords (leftChart (coordsOfPoint X) (r • tangentCoords ξ))) j)
        vel 0 :=
      hasDerivAt_pi.2 fun b' => hasDerivAt_levelField_leftChart hX hj' b' (tangentCoords ξ)
    have hPA : HasDerivAt (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist
        ((t : ℂ) • tangentTransport X ξ j) (levelField X j)) b) (DP vel) 0 := by
      have h1 : HasFDerivAt (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b) DP
          (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • tangentTransport X ξ j) (levelField X j)) := by
        rw [expTwist_zero hr]; exact hPd
      exact h1.comp_hasDerivAt (0 : ℝ) hA
    have hPB : HasDerivAt (fun r : ℝ => normalizedMean
        (levelField (pointOfCoords (leftChart (coordsOfPoint X) (r • tangentCoords ξ))) j) b)
        (DP vel) 0 := by
      have h1 : HasFDerivAt (fun V : Edge L n k j → ComplexMatrix2 => normalizedMean V b) DP
          (levelField (pointOfCoords (leftChart (coordsOfPoint X) ((0 : ℝ) • tangentCoords ξ))) j) := by
        rw [levelField_coords_leftChart_zero hX]; exact hPd
      exact h1.comp_hasDerivAt (0 : ℝ) hB
    have hN : HasDerivAt (fun r : ℝ => leftChart (coordsOfPoint X) (r • tangentCoords ξ)
        (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩ : Coord L n k)) (d (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩)) 0 :=
      (hasDerivAt_pi.1 (hasDerivAt_leftChart_zero (coordsOfPoint X) (tangentCoords ξ))) _
    have hL := hN.mul hPB
    have hL0 := hasDerivAt_levelField_leftChart hX hj b (tangentCoords ξ)
    have e1 : (fun r : ℝ =>
        levelField (pointOfCoords (leftChart (coordsOfPoint X) (r • tangentCoords ξ))) (j + 1) b) =
        (fun r : ℝ => leftChart (coordsOfPoint X) (r • tangentCoords ξ)
          (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩ : Coord L n k)) *
          fun r : ℝ => normalizedMean
            (levelField (pointOfCoords (leftChart (coordsOfPoint X) (r • tangentCoords ξ))) j) b := by
      funext r
      rw [levelField_succ_pos _ h hb]
      rfl
    rw [e1] at hL0
    have hval := hL0.unique hL
    have hc0 : leftChart (coordsOfPoint X) ((0 : ℝ) • tangentCoords ξ)
        (Sum.inr ⟨⟨j, h⟩, ⟨b, hb⟩⟩ : Coord L n k) = n₀ := by
      rw [zero_smul, leftChart_zero]
      rfl
    have hu0 : normalizedMean
        (levelField (pointOfCoords (leftChart (coordsOfPoint X) ((0 : ℝ) • tangentCoords ξ))) j) b =
        u := by
      rw [levelField_coords_leftChart_zero hX]
    rw [hc0, hu0] at hval
    have hun : u ∈ PeriodicLattice.compactGaugeGroup := by
      have := normalize_mem_compact (contourMean_mem_quaternionMatrices hrr b)
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
        Complex.I⁻¹ • deriv (fun t : ℝ => ComplexMatrix2.logSeries (normalizedMean
          (PeriodicLattice.expTwist ((t : ℂ) • tangentTransport X ξ j) (levelField X j)) b *
            u⁻¹)) 0 := by
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
section RealPoints
variable {L n k : ℕ} [NeZero L]
theorem coordsOfPoint_mem_compact {X : ChainPoint L n k} (hX : IsCompactValued X)
    (ι : Coord L n k) :
    coordsOfPoint X ι ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.toCoordinates_mem_compact <;> assumption
end RealPoints
section Gauged
variable {L n k : ℕ} [NeZero L]
theorem restrictVertexFunction_zero (v : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction 0 v = v := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.restrictVertexFunction_zero <;> assumption
variable (hC : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
include hC hL hn in
theorem levelField_gaugeTransformPoint {X' : ChainPoint L n k} (hX' : IsCompactValued X')
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ j, j ≤ k → levelField (gaugeTransformPoint v X') j =
      PeriodicLattice.gaugeTransform (restrictVertexFunction j v) (levelField X' j) := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.levelField_gaugeTransformPoint <;> assumption
end Gauged
section GaugeCoordinates
variable {L n k : ℕ} [NeZero L]
abbrev gaugeFlow {ι : Type*} (l : ι → ComplexMatrix2) (t : ℝ) : ι → ComplexMatrix2 :=
  fun x => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • (-l x)))
theorem gaugeFlow_mem_compact {ι : Type*} {l : ι → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) (t : ℝ) (x : ι) :
    gaugeFlow l t x ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerHessian.gaugeExpCurve_mem_compact <;> assumption
theorem gaugeFlow_inv {ι : Type*} (l : ι → ComplexMatrix2) (t : ℝ) (x : ι) :
    (gaugeFlow l t x)⁻¹ = ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • l x)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerHessian.gaugeExpCurve_inv <;> assumption
def leftGaugeCoords (l : Vertex L n k 0 → ComplexMatrix2) : Coord L n k → ComplexMatrix2 :=
  Sum.elim (fun b => -(Complex.I • l b.1.source))
    fun p => -(Complex.I • restrictVertexFunction (p.1 + 1) l p.2.1.source)
def rightGaugeCoords (l : Vertex L n k 0 → ComplexMatrix2) : Coord L n k → ComplexMatrix2 :=
  Sum.elim (fun b => Complex.I • l b.1.target)
    fun p => Complex.I • restrictVertexFunction (p.1 + 1) l p.2.1.source
theorem real_smul_neg_I_smul (t : ℝ) (Y : ComplexMatrix2) :
    t • -(Complex.I • Y) = Complex.I • ((t : ℂ) • (-Y)) := by
  rw [Complex.coe_smul, smul_neg, smul_neg, smul_neg, smul_comm]
theorem real_smul_I_smul (t : ℝ) (Y : ComplexMatrix2) :
    t • (Complex.I • Y) = Complex.I • ((t : ℂ) • Y) := by
  rw [Complex.coe_smul, smul_comm]
theorem pointOfCoords_twoSided (l : Vertex L n k 0 → ComplexMatrix2)
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    (w : Coord L n k → ComplexMatrix2) (t : ℝ) :
    pointOfCoords (NormedSpace.exp (t • leftGaugeCoords l) * w *
      NormedSpace.exp (t • rightGaugeCoords l)) =
      gaugeTransformPoint (gaugeFlow l t) (pointOfCoords w) := by
  have hval : ∀ ι : Coord L n k,
      (NormedSpace.exp (t • leftGaugeCoords l) * w * NormedSpace.exp (t • rightGaugeCoords l)) ι =
        ComplexMatrix2.matExp (t • leftGaugeCoords l ι) * w ι *
          ComplexMatrix2.matExp (t • rightGaugeCoords l ι) := by
    intro ι
    simp only [Pi.mul_apply, exp_pi_apply, Pi.smul_apply]
  simp only [pointOfCoords, gaugeTransformPoint]
  congr 1
  · funext b
    by_cases hb : b.IsPositivelyOriented
    · rw [fieldOfPositiveValues_pos _ hb, fieldOfPositiveValues_pos _ hb, hval]
      change ComplexMatrix2.matExp (t • -(Complex.I • l b.source)) * w _ *
        ComplexMatrix2.matExp (t • (Complex.I • l b.target)) = _
      rw [real_smul_neg_I_smul, real_smul_I_smul, gaugeFlow_inv]
    · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      rw [fieldOfPositiveValues_neg _ hb, fieldOfPositiveValues_neg _ hb, hval]
      change (ComplexMatrix2.matExp (t • -(Complex.I • l b.opposite.source)) * w _ *
        ComplexMatrix2.matExp (t • (Complex.I • l b.opposite.target)))⁻¹ = _
      rw [real_smul_neg_I_smul, real_smul_I_smul, gaugeFlow_inv, Matrix.mul_inv_rev,
        Matrix.mul_inv_rev, matExp_inv, matExp_inv]
      have e1 : b.opposite.source = b.target := rfl
      have e2 : b.opposite.target = b.source := rfl
      rw [e1, e2]
      simp only [neg_neg, smul_neg, mul_assoc, gaugeFlow]
  · funext i c
    rw [hval]
    change ComplexMatrix2.matExp (t • -(Complex.I • restrictVertexFunction (i + 1) l c.1.source)) *
      w _ * ComplexMatrix2.matExp (t • (Complex.I • restrictVertexFunction (i + 1) l c.1.source)) = _
    rw [real_smul_neg_I_smul, real_smul_I_smul]
    have e : restrictVertexFunction (i + 1) (gaugeFlow l t) c.1.source =
        gaugeFlow (restrictVertexFunction (i + 1) l) t c.1.source := rfl
    rw [e, gaugeFlow_inv]
theorem hasDerivAt_exp_mul_mul_exp {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (x α γ : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • α) * x * NormedSpace.exp (t • γ))
      (α * x + x * γ) 0 := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) α (0 : ℝ)
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) γ (0 : ℝ)
  have h3 := (h1.mul_const x).mul h2
  exact h3.congr_deriv (by simp)
variable (hC : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
include hC hL hn in
theorem levelDeriv_gaugeCoords {X : ChainPoint L n k} (hX : IsCompactValued X)
    (l : Vertex L n k 0 → ComplexMatrix2) (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    {j : ℕ} (hj : j ≤ k) (c : Edge L n k j) :
    levelDeriv X j c (leftGaugeCoords l * coordsOfPoint X + coordsOfPoint X * rightGaugeCoords l) =
      levelField X j c * (Complex.I • restrictVertexFunction j l c.target) -
        (Complex.I • restrictVertexFunction j l c.source) * levelField X j c := by
  have hx0 : pointOfCoords (coordsOfPoint X) = X :=
    pointOfCoords_coordsOfPoint (hX.2 0 (Nat.zero_le _))
  have hc := hasDerivAt_exp_mul_mul_exp (coordsOfPoint X) (leftGaugeCoords l) (rightGaugeCoords l)
  have hΨ := ((contDiffAt_levelField_coords hX hj c).differentiableAt (by norm_num)).hasFDerivAt
  have hΨ' : HasFDerivAt (fun w => levelField (pointOfCoords w) j c) (levelDeriv X j c)
      (NormedSpace.exp ((0 : ℝ) • leftGaugeCoords l) * coordsOfPoint X *
        NormedSpace.exp ((0 : ℝ) • rightGaugeCoords l)) := by
    have hz : NormedSpace.exp ((0 : ℝ) • leftGaugeCoords l) * coordsOfPoint X *
        NormedSpace.exp ((0 : ℝ) • rightGaugeCoords l) = coordsOfPoint X := by simp
    rw [hz]
    exact hΨ
  have h1 := hΨ'.comp_hasDerivAt (0 : ℝ) hc
  have e : ((fun w => levelField (pointOfCoords w) j c) ∘ fun t : ℝ =>
      NormedSpace.exp (t • leftGaugeCoords l) * coordsOfPoint X *
        NormedSpace.exp (t • rightGaugeCoords l)) =
      fun t : ℝ => gaugeFlow (restrictVertexFunction j l) t c.source * levelField X j c *
        ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • restrictVertexFunction j l c.target)) := by
    funext t
    have e1 := _root_.YangMills.Construction.RunningCouplingSlope.ChainRelationsProof.levelField_gaugeTransformPoint hC hL hn hX (gaugeFlow_mem_compact hl t) j hj
    simp only [Function.comp]
    rw [pointOfCoords_twoSided l hl, hx0, e1]
    simp only [PeriodicLattice.gaugeTransform]
    have e2 : restrictVertexFunction j (gaugeFlow l t) c.target =
        gaugeFlow (restrictVertexFunction j l) t c.target := rfl
    rw [e2, gaugeFlow_inv]
    rfl
  rw [e] at h1
  have h2 := ((hasDerivAt_matExp_I_line (-restrictVertexFunction j l c.source)).mul_const
    (levelField X j c)).mul (hasDerivAt_matExp_I_line (restrictVertexFunction j l c.target))
  have h3 := h1.unique h2
  rw [h3, matExp_I_line_zero (restrictVertexFunction j l c.target),
    matExp_I_line_zero (-restrictVertexFunction j l c.source)]
  simp only [one_mul, mul_one, smul_neg, neg_mul]
  abel
end GaugeCoordinates
section Lie
theorem inv_I_smul_deriv_mem_hermitianTraceless
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex) {m : ℝ → ComplexMatrix2}
    {m' : ComplexMatrix2} (hm : HasDerivAt m m' 0) (h0 : m 0 = 1)
    (hr : ∀ᶠ r in 𝓝 (0 : ℝ), m r ∈ PeriodicLattice.compactGaugeGroup) :
    Complex.I⁻¹ • m' ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.inv_I_smul_deriv_mem <;> assumption
end Lie
section Forms
variable {L n k j : ℕ}
theorem edgeForm_ext {A B : edgeFormSpace L n k j}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      (A : Edge L n k j → ComplexMatrix2) b = (B : Edge L n k j → ComplexMatrix2) b) :
    A = B := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.edgeForm_ext <;> assumption
theorem extendOddly_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
theorem extendOddly_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Edge L n k j → ComplexMatrix2)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace L n k j := by apply _root_.YangMills.SharedProofs.p1442 <;> assumption
theorem conjugateBy_mem_hermitianTraceless {g A : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy g A ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p2904 <;> assumption
end Forms
section Tangents
variable {L n k : ℕ} [NeZero L]
theorem exists_gaugeOrbitValues
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (l : Vertex L n k 0 → ComplexMatrix2)
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) :
    ∃ ζ : LevelForms L n k, formValues ζ = gaugeOrbitValues X l := by
  have hU : ∀ b, X.fine b ∈ PeriodicLattice.compactGaugeGroup :=
    fun b => (hX.2 0 (Nat.zero_le _)).1 b (Set.mem_univ _)
  have m0 : (gaugeOrbitValues X l).1 ∈ edgeFormSpace L n k 0 :=
    extendOddly_mem (hxor 0 (Nat.zero_le _)) _ fun b _ =>
      ComplexMatrix2.hermitianTraceless.sub_mem
        (conjugateBy_mem_hermitianTraceless (hU b) (hl _)) (hl _)
  have m1 : ∀ i : Fin k, (gaugeOrbitValues X l).2 i ∈ edgeFormSpace L n k (i + 1) := by
    intro i
    simp only [gaugeOrbitValues]
    refine extendOddly_mem (hxor ((i : ℕ) + 1) i.2) _ fun c hc => ?_
    simp only [dif_pos hc]
    exact ComplexMatrix2.hermitianTraceless.sub_mem
      (conjugateBy_mem_hermitianTraceless (hX.1 _ _) (hl _)) (hl _)
  exact ⟨(⟨_, m0⟩, fun i => ⟨_, m1 i⟩), rfl⟩
theorem tangentCoords_inl (ξ : LevelForms L n k) (b : PositiveEdge L n k 0) :
    tangentCoords ξ (Sum.inl b) = Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1 := rfl
theorem tangentCoords_inr (ξ : LevelForms L n k) (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    tangentCoords ξ (Sum.inr ⟨i, c⟩) =
      Complex.I • (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 := rfl
theorem gaugeOrbit_fine {X : ChainPoint L n k} {l : Vertex L n k 0 → ComplexMatrix2}
    {ζ : LevelForms L n k} (hζ : formValues ζ = gaugeOrbitValues X l) (b : PositiveEdge L n k 0) :
    (ζ.1 : Edge L n k 0 → ComplexMatrix2) b.1 =
      ComplexMatrix2.conjugateBy (X.fine b.1) (l b.1.target) - l b.1.source := by
  have e : (ζ.1 : Edge L n k 0 → ComplexMatrix2) = covDiff X.fine l := congrArg Prod.fst hζ
  rw [e, covDiff, extendOddly_pos _ b.2]
theorem gaugeOrbit_noise {X : ChainPoint L n k} {l : Vertex L n k 0 → ComplexMatrix2}
    {ζ : LevelForms L n k} (hζ : formValues ζ = gaugeOrbitValues X l) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    (ζ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
      ComplexMatrix2.conjugateBy (X.noise i c) (restrictVertexFunction (i + 1) l c.1.source) -
        restrictVertexFunction (i + 1) l c.1.source := by
  have e : (ζ.2 i : Edge L n k (i + 1) → ComplexMatrix2) = (gaugeOrbitValues X l).2 i :=
    congrFun (congrArg Prod.snd hζ) i
  rw [e]
  simp only [gaugeOrbitValues]
  rw [extendOddly_pos _ c.2, dif_pos c.2]
theorem conjugateBy_mul {g A : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    ComplexMatrix2.conjugateBy g A * g = g * A := by
  rw [ComplexMatrix2.conjugateBy, mul_assoc, Matrix.nonsing_inv_mul _ (compact_isUnit_det hg),
    mul_one]
theorem tangentCoords_gaugeOrbit {X : ChainPoint L n k} (hX : IsCompactValued X)
    {l : Vertex L n k 0 → ComplexMatrix2}
    {ζ : LevelForms L n k} (hζ : formValues ζ = gaugeOrbitValues X l) :
    tangentCoords ζ * coordsOfPoint X =
      leftGaugeCoords l * coordsOfPoint X + coordsOfPoint X * rightGaugeCoords l := by
  funext ι
  rcases ι with b | ⟨i, c⟩
  · have hg := coordsOfPoint_mem_compact hX (Sum.inl b)
    have e : coordsOfPoint X (Sum.inl b) = X.fine b.1 := rfl
    simp only [Pi.mul_apply, Pi.add_apply, tangentCoords_inl, gaugeOrbit_fine hζ]
    rw [e] at hg ⊢
    have e1 : leftGaugeCoords l (Sum.inl b) = -(Complex.I • l b.1.source) := rfl
    have e2 : rightGaugeCoords l (Sum.inl b) = Complex.I • l b.1.target := rfl
    rw [e1, e2, smul_sub, sub_mul, Matrix.smul_mul, conjugateBy_mul hg]
    simp only [Matrix.mul_smul, Matrix.smul_mul, neg_mul]
    abel
  · have hg : X.noise i c ∈ PeriodicLattice.compactGaugeGroup := hX.1 i c
    have e : coordsOfPoint X (Sum.inr ⟨i, c⟩) = X.noise i c := rfl
    simp only [Pi.mul_apply, Pi.add_apply, tangentCoords_inr, gaugeOrbit_noise hζ, e]
    have e1 : leftGaugeCoords l (Sum.inr ⟨i, c⟩) =
        -(Complex.I • restrictVertexFunction (i + 1) l c.1.source) := rfl
    have e2 : rightGaugeCoords l (Sum.inr ⟨i, c⟩) =
        Complex.I • restrictVertexFunction (i + 1) l c.1.source := rfl
    rw [e1, e2, smul_sub, sub_mul, Matrix.smul_mul, conjugateBy_mul hg]
    simp only [Matrix.mul_smul, Matrix.smul_mul, neg_mul]
    abel
end Tangents
section Identities
variable {L n k : ℕ} [NeZero L]
theorem I_smul_mul_cancel {W M N : ComplexMatrix2} (hW : IsUnit W.det)
    (h : (Complex.I • M) * W = (Complex.I • N) * W) : M = N := by apply _root_.YangMills.SharedProofs.p6717 <;> assumption
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
include hd
theorem tangentTransport_gaugeOrbit (hC : ContourMeanGaugeCovariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    (l : Vertex L n k 0 → ComplexMatrix2) (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    {ζ : LevelForms L n k}
    (hζ : formValues ζ = gaugeOrbitValues X l) {j : ℕ} (hj : j ≤ k) {c : Edge L n k j}
    (hc : c.IsPositivelyOriented) :
    tangentTransport X ζ j c = covDiff (levelField X j) (restrictVertexFunction j l) c := by
  have hW : levelField X j c ∈ PeriodicLattice.compactGaugeGroup :=
    (hX.2 j hj).1 c (Set.mem_univ _)
  have h1 := levelDeriv_tangentCoords hd hX ζ j hj c hc
  rw [tangentCoords_gaugeOrbit hX hζ, levelDeriv_gaugeCoords hC hL hn hX l hl hj c] at h1
  have e : covDiff (levelField X j) (restrictVertexFunction j l) c =
      ComplexMatrix2.conjugateBy (levelField X j c) (restrictVertexFunction j l c.target) -
        restrictVertexFunction j l c.source := by
    rw [covDiff, extendOddly_pos _ hc]
  rw [e]
  refine I_smul_mul_cancel (compact_isUnit_det hW) ?_
  rw [← h1, smul_sub, sub_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [conjugateBy_mul hW]
theorem tangentTransport_eq {X : ChainPoint L n k} (hX : IsCompactValued X) (ξ : LevelForms L n k)
    {j : ℕ} (hj : j ≤ k) {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    tangentTransport X ξ j b =
      Complex.I⁻¹ • (levelDeriv X j b (tangentCoords ξ * coordsOfPoint X) *
        (levelField X j b)⁻¹) := by
  have hW : levelField X j b ∈ PeriodicLattice.compactGaugeGroup :=
    (hX.2 j hj).1 b (Set.mem_univ _)
  rw [levelDeriv_tangentCoords hd hX ξ j hj b hb, mul_assoc,
    Matrix.mul_nonsing_inv _ (compact_isUnit_det hW), mul_one,
    smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
theorem tangentTransport_mem_edgeFormSpace
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (ξ : LevelForms L n k)
    {j : ℕ} (hj : j ≤ k) : tangentTransport X ξ j ∈ edgeFormSpace L n k j := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.tangentTransport_mem_edgeFormSpace <;> assumption
theorem topDeriv_spec
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) : IsTopDeriv X (topDeriv X) := by
  refine Classical.epsilon_spec (p := IsTopDeriv X) ⟨
    { toFun := fun ξ => ⟨tangentTransport X ξ k, tangentTransport_mem_edgeFormSpace hd hxor hX ξ le_rfl⟩
      map_add' := fun ξ ξ' => edgeForm_ext fun b hb => ?_
      map_smul' := fun r ξ => edgeForm_ext fun b hb => ?_ }, fun ξ => rfl⟩
  · change tangentTransport X (ξ + ξ') k b = tangentTransport X ξ k b + tangentTransport X ξ' k b
    rw [tangentTransport_eq hd hX _ le_rfl hb, tangentTransport_eq hd hX _ le_rfl hb,
      tangentTransport_eq hd hX _ le_rfl hb, map_add, add_mul, map_add, add_mul, smul_add]
  · change tangentTransport X (r • ξ) k b = r • tangentTransport X ξ k b
    rw [tangentTransport_eq hd hX _ le_rfl hb, tangentTransport_eq hd hX _ le_rfl hb, map_smul,
      smul_mul_assoc, map_smul, smul_mul_assoc, smul_comm]
end Identities
section Constraints
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
def covDiffLinear {j : ℕ} (W : Edge L n k j → ComplexMatrix2)
    (hW : ∀ b, W b ∈ PeriodicLattice.compactGaugeGroup)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    vertexFunctionSpace L n k j →ₗ[ℝ] edgeFormSpace L n k j where
  toFun l := ⟨covDiff W l, extendOddly_mem hx _ fun b _ =>
    ComplexMatrix2.hermitianTraceless.sub_mem
      (conjugateBy_mem_hermitianTraceless (hW b) (vertexFunction_apply_mem l _))
      (vertexFunction_apply_mem l _)⟩
  map_add' l l' := edgeForm_ext fun b hb => by
    change covDiff W (l + l' : vertexFunctionSpace L n k j) b =
      covDiff W l b + covDiff W l' b
    simp only [covDiff, extendOddly_pos _ hb]
    change ComplexMatrix2.conjugateBy (W b) ((l : Vertex L n k j → ComplexMatrix2) b.target +
      (l' : Vertex L n k j → ComplexMatrix2) b.target) -
      ((l : Vertex L n k j → ComplexMatrix2) b.source +
        (l' : Vertex L n k j → ComplexMatrix2) b.source) = _
    rw [conjugateBy_add]
    abel
  map_smul' r l := edgeForm_ext fun b hb => by
    change covDiff W (r • l : vertexFunctionSpace L n k j) b =
      r • covDiff W l b
    simp only [covDiff, extendOddly_pos _ hb]
    change ComplexMatrix2.conjugateBy (W b) (r • (l : Vertex L n k j → ComplexMatrix2) b.target) -
      r • (l : Vertex L n k j → ComplexMatrix2) b.source = _
    rw [conjugateBy_smul, smul_sub]
theorem levelForms_ext {ξ ξ' : LevelForms L n k}
    (h1 : ∀ b : PositiveEdge L n k 0,
      (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1 = (ξ'.1 : Edge L n k 0 → ComplexMatrix2) b.1)
    (h2 : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
        (ξ'.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1) :
    ξ = ξ' :=
  Prod.ext (edgeForm_ext fun b hb => h1 ⟨b, hb⟩)
    (funext fun i => edgeForm_ext fun b hb => h2 i ⟨b, hb⟩)
theorem exists_gaugeOrbitMap
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) :
    ∃ O : vertexFunctionSpace L n k 0 →ₗ[ℝ] LevelForms L n k, ∀ l,
      formValues (O l) = gaugeOrbitValues X (l : Vertex L n k 0 → ComplexMatrix2) := by
  have hex := fun l : vertexFunctionSpace L n k 0 =>
    exists_gaugeOrbitValues hxor hX (l : Vertex L n k 0 → ComplexMatrix2)
      (vertexFunction_apply_mem l)
  choose O hO using hex
  refine ⟨{ toFun := O, map_add' := fun l l' => ?_, map_smul' := fun r l => ?_ }, hO⟩
  · refine levelForms_ext (fun b => ?_) fun i c => ?_
    · change (O (l + l')).1.1 b.1 = (O l).1.1 b.1 + (O l').1.1 b.1
      rw [gaugeOrbit_fine (hO _), gaugeOrbit_fine (hO _), gaugeOrbit_fine (hO _)]
      change ComplexMatrix2.conjugateBy _ ((l : Vertex L n k 0 → ComplexMatrix2) b.1.target +
        (l' : Vertex L n k 0 → ComplexMatrix2) b.1.target) -
        ((l : Vertex L n k 0 → ComplexMatrix2) b.1.source +
          (l' : Vertex L n k 0 → ComplexMatrix2) b.1.source) = _
      rw [conjugateBy_add]
      abel
    · change ((O (l + l')).2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
        ((O l).2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 +
          ((O l').2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1
      rw [gaugeOrbit_noise (hO _), gaugeOrbit_noise (hO _), gaugeOrbit_noise (hO _)]
      have e : restrictVertexFunction ((i : ℕ) + 1)
          ((l + l' : vertexFunctionSpace L n k 0) : Vertex L n k 0 → ComplexMatrix2)
          c.1.source =
          restrictVertexFunction ((i : ℕ) + 1) (l : Vertex L n k 0 → ComplexMatrix2) c.1.source +
            restrictVertexFunction ((i : ℕ) + 1) (l' : Vertex L n k 0 → ComplexMatrix2)
              c.1.source := rfl
      rw [e, conjugateBy_add]
      abel
  · refine levelForms_ext (fun b => ?_) fun i c => ?_
    · change (O (r • l)).1.1 b.1 = r • (O l).1.1 b.1
      rw [gaugeOrbit_fine (hO _), gaugeOrbit_fine (hO _)]
      change ComplexMatrix2.conjugateBy _ (r • (l : Vertex L n k 0 → ComplexMatrix2) b.1.target) -
        r • (l : Vertex L n k 0 → ComplexMatrix2) b.1.source = _
      rw [conjugateBy_smul, smul_sub]
    · change ((O (r • l)).2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
        r • ((O l).2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1
      rw [gaugeOrbit_noise (hO _), gaugeOrbit_noise (hO _)]
      have e : restrictVertexFunction ((i : ℕ) + 1)
          ((r • l : vertexFunctionSpace L n k 0) : Vertex L n k 0 → ComplexMatrix2)
          c.1.source =
          r • restrictVertexFunction ((i : ℕ) + 1) (l : Vertex L n k 0 → ComplexMatrix2)
            c.1.source := rfl
      rw [e, conjugateBy_smul, smul_sub]
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
  (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
include hd hxor
theorem shiftedGaugeMap_spec {X : ChainPoint L n k} (hX : IsCompactValued X)
    {T₀ : LevelForms L n k →ₗ[ℝ] vertexFunctionSpace L n k k}
    (hT : ∀ ξ, (T₀ ξ : Vertex L n k k → ComplexMatrix2) = chainDrift X ξ k) :
    IsShiftedGaugeMap X (shiftedGaugeMap X) := by
  have hW : ∀ b, levelField X k b ∈ PeriodicLattice.compactGaugeGroup :=
    fun b => (hX.2 k le_rfl).1 b (Set.mem_univ _)
  refine Classical.epsilon_spec (p := IsShiftedGaugeMap X)
    ⟨topDeriv X + covDiffLinear (levelField X k) hW (hxor k le_rfl) ∘ₗ T₀, fun ξ => ?_⟩
  have h1 := topDeriv_spec hd hxor hX ξ
  change (topDeriv X ξ : Edge L n k k → ComplexMatrix2) +
    covDiff (levelField X k) (T₀ ξ : Vertex L n k k → ComplexMatrix2) = _
  rw [h1, hT]
  rfl
end Constraints
section Reindex
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
theorem familyDiameter_reindex (e : ι ≃ κ) (V : κ → ComplexMatrix2) :
    ComplexMatrix2.familyDiameter (V ∘ e) = ComplexMatrix2.familyDiameter V := by apply _root_.YangMills.SharedProofs.p70753 <;> assumption
theorem complexLogMean_reindex (e : ι ≃ κ) (V : κ → ComplexMatrix2) :
    PeriodicLattice.complexLogMean (V ∘ e) = PeriodicLattice.complexLogMean V := by apply _root_.YangMills.Construction.Averaging.ExplicitRadiiProof.complexLogMean_comp_equiv <;> assumption
end Reindex
section HolomorphicCurve
variable {L n k j : ℕ} [NeZero L]
theorem hasDerivAt_matrix_inv_complex {f : ℂ → ComplexMatrix2} {f' : ComplexMatrix2}
    (hf : HasDerivAt f f' 0) (hu : IsUnit (f 0).det) :
    HasDerivAt (fun t => (f t)⁻¹) (-((f 0)⁻¹ * f' * (f 0)⁻¹)) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.hasDerivAt_inv_matrix_complex <;> assumption
theorem hasDerivAt_matExp_I_complexLine (M : ComplexMatrix2) :
    HasDerivAt (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • M))) (Complex.I • M) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.HolDifferentialAtOneProof.hasDerivAt_matExp_I_smul <;> assumption
theorem matExp_I_complexLine_zero (M : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • M)) = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.matExp_I_complexLine_zero <;> assumption
def twistVelocity (W B : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) : ComplexMatrix2 :=
  open Classical in
  if b.IsPositivelyOriented then (Complex.I • B b) * W b
  else -((W b.opposite)⁻¹ * ((Complex.I • B b.opposite) * W b.opposite) * (W b.opposite)⁻¹)
theorem hasDerivAt_expTwist_complex (W B : Edge L n k j → ComplexMatrix2)
    (hW : W ∈ fieldSpace L n k j) :
    HasDerivAt (fun t : ℂ => PeriodicLattice.expTwist (t • B) W) (twistVelocity W B) 0 := by
  refine hasDerivAt_pi.2 fun b => ?_
  by_cases hb : b.IsPositivelyOriented
  · have e : (fun t : ℂ => PeriodicLattice.expTwist (t • B) W b) =
        fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B b)) * W b := by
      funext t
      simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply]
    rw [e]
    simp only [twistVelocity, if_pos hb]
    exact (hasDerivAt_matExp_I_complexLine (B b)).mul_const _
  · set c := b.opposite with hc
    have e : (fun t : ℂ => PeriodicLattice.expTwist (t • B) W b) =
        fun t : ℂ => (ComplexMatrix2.matExp (Complex.I • (t • B c)) * W c)⁻¹ := by
      funext t
      simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply, hc]
    have h1 := (hasDerivAt_matExp_I_complexLine (B c)).mul_const (W c)
    have h0 : ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • B c)) * W c = W c := by
      rw [matExp_I_complexLine_zero, one_mul]
    have h2 := hasDerivAt_matrix_inv_complex h1
      (by rw [h0]; exact isUnit_det_of_mem_fieldSpace hW c)
    rw [e]
    simp only [twistVelocity, if_neg hb]
    refine h2.congr_deriv ?_
    rw [h0]
theorem differentiableAt_pathHolonomy {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {y₀ : Y} {V : Y → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, DifferentiableAt ℂ (fun y => V y b) y₀)
    (Γ : List (Edge L n k j)) :
    DifferentiableAt ℂ (fun y => PeriodicLattice.pathHolonomy (V y) Γ) y₀ := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.differentiableAt_pathHolonomy <;> assumption
theorem det_pathHolonomy_eq_one {V : Edge L n k j → ComplexMatrix2} (hV : ∀ b, (V b).det = 1)
    (Γ : List (Edge L n k j)) : (PeriodicLattice.pathHolonomy V Γ).det = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.det_pathHolonomy_eq_one <;> assumption
theorem det_expTwist (W B : Edge L n k j → ComplexMatrix2) (hW : W ∈ fieldSpace L n k j)
    (hB : B ∈ edgeFormSpace L n k j) (t : ℂ) (b : Edge L n k j) :
    (PeriodicLattice.expTwist (t • B) W b).det = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.det_expTwist <;> assumption
theorem hasDerivAt_ofReal_zero : HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) 0 :=
  (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).congr_deriv (by simp)
theorem hasDerivAt_comp_ofReal {g : ℂ → ComplexMatrix2} {g' : ComplexMatrix2}
    (h : HasDerivAt g g' 0) :
    HasDerivAt (fun r : ℝ => g (r : ℂ)) g' 0 := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.hasDerivAt_ofReal_of_complex <;> assumption
theorem expTwist_mem_compact {W B : Edge L n k j → ComplexMatrix2} (hW : W ∈ fieldSpace L n k j)
    (hB : B ∈ edgeFormSpace L n k j) (r : ℝ) (b : Edge L n k j) :
    PeriodicLattice.expTwist ((r : ℂ) • B) W b ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.expTwist_real_mem <;> assumption
section Contours
variable (hMF : ∀ m : ℕ, 1 ≤ m → Averaging.ComplexLogMeanProperties m)
include hMF
variable {y : Vertex L n k (j + 1)} {x : Vertex L n k j}
theorem exists_contourMean_deriv {W : Edge L n k j → ComplexMatrix2} (hW : W ∈ fieldSpace L n k j)
    [Nonempty (PeriodicLattice.AxisOrdering y x)]
    (hs : ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies W y x) <
      Averaging.centreOfMassDiameter) :
    ∃ D : (Edge L n k j → ComplexMatrix2) →L[ℂ] ComplexMatrix2, (∀ B ∈ edgeFormSpace L n k j,
      HasDerivAt (fun t : ℂ => PeriodicLattice.complexMeanContourHolonomy
        (PeriodicLattice.expTwist (t • B) W) y x) (D (twistVelocity W B)) 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℂ), ComplexMatrix2.familyDiameter
        (PeriodicLattice.contourHolonomies (PeriodicLattice.expTwist (t • B) W) y x) <
          Averaging.centreOfMassDiameter) ∧
      ∀ (C : ℝ → Edge L n k j → ComplexMatrix2) (v : Edge L n k j → ComplexMatrix2), C 0 = W →
        HasDerivAt C v 0 →
        (∀ᶠ r in 𝓝 (0 : ℝ), ∀ b, (C r b).det = 1) →
        HasDerivAt (fun r : ℝ => PeriodicLattice.complexMeanContourHolonomy (C r) y x) (D v) 0 := by
  set m := Fintype.card (PeriodicLattice.AxisOrdering y x) with hm
  have hm1 : 1 ≤ m := Fintype.card_pos
  let e : Fin m ≃ PeriodicLattice.AxisOrdering y x := (Fintype.equivFin _).symm
  let fam : (Edge L n k j → ComplexMatrix2) → Fin m → ComplexMatrix2 :=
    fun V => PeriodicLattice.contourHolonomies V y x ∘ e
  have hfam : ∀ V, PeriodicLattice.complexMeanContourHolonomy V y x =
      PeriodicLattice.complexLogMean (fam V) :=
    fun V => (complexLogMean_reindex e _).symm
  have hx : fam W ∈ Averaging.smallComplexFamilies m := by
    refine ⟨fun i => compact_det (pathHolonomy_mem_compact (fun b => hW.1 b (Set.mem_univ _)) _),
      ?_⟩
    rw [familyDiameter_reindex]
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
  refine ⟨fderiv ℂ h W, fun B hB => ?_, fun C v hC0 hC hdet => ?_⟩
  rotate_left
  · have hcont : ContinuousAt (fun r : ℝ => fam (C r)) 0 := by
      have h1 : ContinuousAt fam (C 0) := by
        rw [hC0]; exact hfd.continuousAt
      exact ContinuousAt.comp (f := C) h1 hC.continuousAt
    have hval0 : fam (C 0) = fam W := by rw [hC0]
    have hxO : fam W ∈ O := by
      rw [hDO] at hx; exact hx.1
    have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), fam (C r) ∈ Averaging.smallComplexFamilies m := by
      have h1 : ∀ᶠ r in 𝓝 (0 : ℝ), fam (C r) ∈ O := by
        refine hcont.eventually_mem (hO.mem_nhds ?_)
        rw [hval0]; exact hxO
      filter_upwards [h1, hdet] with r hr hr'
      rw [hDO]
      exact ⟨hr, fun i => det_pathHolonomy_eq_one hr' _⟩
    have hF2 : ∀ᶠ r in 𝓝 (0 : ℝ),
        PeriodicLattice.complexLogMean (fam (C r)) = F (fam (C r)) () := by
      have h1 : Tendsto (fun r : ℝ => fam (C r)) (𝓝 0)
          (𝓝[Averaging.smallComplexFamilies m] fam W) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, hnear⟩
        have := hcont.tendsto
        rwa [hval0] at this
      have h2 := h1.eventually hFe
      filter_upwards [h2] with r hr
      exact congrFun hr ()
    have hEq : (fun r : ℝ => PeriodicLattice.complexMeanContourHolonomy (C r) y x) =ᶠ[𝓝 0]
        h ∘ C := by
      filter_upwards [hF2] with r hr
      rw [hfam, hr]
      rfl
    have hh' : HasFDerivAt h (fderiv ℂ h W) (C 0) := by
      rw [hC0]; exact hhd.hasFDerivAt
    exact ((hh'.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hC).congr_of_eventuallyEq hEq
  have hA := hasDerivAt_expTwist_complex W B hW
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
  rwa [familyDiameter_reindex] at h3
theorem complexMeanContourHolonomy_mem_compact {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup)
    [Nonempty (PeriodicLattice.AxisOrdering y x)]
    (hs : ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies V y x) <
      Averaging.centreOfMassDiameter) :
    PeriodicLattice.complexMeanContourHolonomy V y x ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.complexMeanContourHolonomy_mem <;> assumption
variable (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
include hd
theorem logDirectionalDeriv_contour {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldSpace L n k j)
    [Nonempty (PeriodicLattice.AxisOrdering y x)]
    (hs : ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies W y x) <
      Averaging.centreOfMassDiameter) :
    ∃ D : (Edge L n k j → ComplexMatrix2) →L[ℂ] ComplexMatrix2, (∀ B ∈ edgeFormSpace L n k j,
      logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X W) y x)
        (PeriodicLattice.complexMeanContourHolonomy W y x) B =
        Complex.I⁻¹ • (D (twistVelocity W B) *
          (PeriodicLattice.complexMeanContourHolonomy W y x)⁻¹) ∧
      Complex.I⁻¹ • (D (twistVelocity W B) *
        (PeriodicLattice.complexMeanContourHolonomy W y x)⁻¹) ∈
        ComplexMatrix2.hermitianTraceless) ∧
      ∀ (C : ℝ → Edge L n k j → ComplexMatrix2) (v : Edge L n k j → ComplexMatrix2), C 0 = W →
        HasDerivAt C v 0 →
        (∀ᶠ r in 𝓝 (0 : ℝ), ∀ b, (C r b).det = 1) →
        HasDerivAt (fun r : ℝ => PeriodicLattice.complexMeanContourHolonomy (C r) y x) (D v) 0 := by
  have hWr : ∀ b, W b ∈ PeriodicLattice.compactGaugeGroup := fun b => hW.1 b (Set.mem_univ _)
  set g₀ := PeriodicLattice.complexMeanContourHolonomy W y x with hg₀
  have hg₀r : g₀ ∈ PeriodicLattice.compactGaugeGroup :=
    complexMeanContourHolonomy_mem_compact hMF hWr hs
  have hgg : g₀ * g₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ (compact_isUnit_det hg₀r)
  obtain ⟨D, hD, hcurve⟩ := exists_contourMean_deriv hMF hW hs
  refine ⟨D, fun B hB => ?_, hcurve⟩
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
  · refine inv_I_smul_deriv_mem_hermitianTraceless hd (m := fun r : ℝ =>
      PeriodicLattice.complexMeanContourHolonomy
        (PeriodicLattice.expTwist ((r : ℂ) • B) W) y x * g₀⁻¹) (hasDerivAt_comp_ofReal hY) ?_ ?_
    · simp only [Complex.ofReal_zero]
      exact hY0
    · have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝 0) (𝓝 0) := by
        have := hasDerivAt_ofReal_zero.continuousAt.tendsto
        simpa using this
      filter_upwards [ht.eventually hnear] with r hr
      exact compact_mul_mem
        (complexMeanContourHolonomy_mem_compact hMF (expTwist_mem_compact hW hB r) hr)
        (compact_inv_mem hg₀r)
end Contours
end HolomorphicCurve
section Drift
variable {L n k : ℕ} [NeZero L]
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
      (T ξ : Vertex L n k j → ComplexMatrix2) = chainDrift X ξ j := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.exists_chainDrift_linear <;> assumption
end Drift
theorem xor_isPositive_opposite
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.xor_isPositivelyOriented_opposite <;> assumption
section Orbit
variable {L n k j : ℕ} [NeZero L]
theorem hasDerivAt_conj_flow (a c H : ComplexMatrix2) :
    HasDerivAt (fun r : ℝ => ComplexMatrix2.matExp (Complex.I • ((r : ℂ) • (-a))) * H *
        (ComplexMatrix2.matExp (Complex.I • ((r : ℂ) • (-c))))⁻¹)
      ((Complex.I • (-a)) * H + H * (Complex.I • c)) 0 := by
  have e : (fun r : ℝ => ComplexMatrix2.matExp (Complex.I • ((r : ℂ) • (-a))) * H *
      (ComplexMatrix2.matExp (Complex.I • ((r : ℂ) • (-c))))⁻¹) =
      (fun r : ℝ => ComplexMatrix2.matExp (Complex.I • ((r : ℂ) • (-a))) * H) *
        (fun r : ℝ => ComplexMatrix2.matExp (Complex.I • ((r : ℂ) • c))) := by
    funext r
    simp only [Pi.mul_apply]
    rw [matExp_inv]
    congr 2
    simp
  rw [e]
  have h := ((hasDerivAt_matExp_I_line (-a)).mul_const H).mul (hasDerivAt_matExp_I_line c)
  simp only [matExp_I_line_zero, mul_one, one_mul] at h
  exact h
theorem twistVelocity_neg_identity (w a c y : ComplexMatrix2) (h1 : y * w = 1) (h2 : w * y = 1) :
    (Complex.I • (-a)) * y + y * (Complex.I • c) =
      -(y * ((Complex.I • (w * a * y - c)) * w) * y) := by
  have e : y * ((w * a * y - c) * w) * y = a * y - y * c := by
    calc y * ((w * a * y - c) * w) * y = (y * w) * a * (y * w) * y - y * c * (w * y) := by
          noncomm_ring
      _ = a * y - y * c := by rw [h1, h2]; noncomm_ring
  have e' : y * ((Complex.I • (w * a * y - c)) * w) * y =
      Complex.I • (y * ((w * a * y - c) * w) * y) := by
    simp only [smul_mul_assoc, mul_smul_comm]
  rw [e', e]
  simp only [smul_mul_assoc, mul_smul_comm, smul_neg, smul_sub, neg_mul]
  abel
theorem hasDerivAt_gaugeTransform_flow {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldSpace L n k j) (l : Vertex L n k j → ComplexMatrix2) :
    HasDerivAt (fun r : ℝ => PeriodicLattice.gaugeTransform (gaugeFlow l r) W)
      (twistVelocity W (covDiff W l)) 0 := by
  refine hasDerivAt_pi.2 fun b => ?_
  have h := hasDerivAt_conj_flow (l b.source) (l b.target) (W b)
  have hval : twistVelocity W (covDiff W l) b =
      (Complex.I • (-(l b.source))) * W b + W b * (Complex.I • l b.target) := by
    by_cases hb : b.IsPositivelyOriented
    · have hu := compact_isUnit_det (hW.1 b (Set.mem_univ _))
      simp only [twistVelocity, if_pos hb, covDiff, extendOddly_pos _ hb,
        ComplexMatrix2.conjugateBy]
      have e : W b * l b.target * (W b)⁻¹ * W b = W b * l b.target := by
        rw [mul_assoc, Matrix.nonsing_inv_mul _ hu, mul_one]
      simp only [smul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_neg, neg_mul, e]
      abel
    · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      have hu := compact_isUnit_det (hW.1 b.opposite (Set.mem_univ _))
      have hinv : W b = (W b.opposite)⁻¹ := hW.2 b.opposite (Set.mem_univ _)
      simp only [twistVelocity, if_neg hb, covDiff, extendOddly_pos _ hp,
        ComplexMatrix2.conjugateBy]
      rw [hinv]
      exact (twistVelocity_neg_identity (W b.opposite) (l b.source) (l b.target)
        (W b.opposite)⁻¹ (Matrix.nonsing_inv_mul _ hu) (Matrix.mul_nonsing_inv _ hu)).symm
  rw [hval]
  exact h
theorem gaugeTransform_flow_zero (W : Edge L n k j → ComplexMatrix2)
    (l : Vertex L n k j → ComplexMatrix2) :
    PeriodicLattice.gaugeTransform (gaugeFlow l 0) W = W := by
  funext b
  have e : ∀ x, gaugeFlow l 0 x = 1 := fun x => matExp_I_line_zero _
  simp [PeriodicLattice.gaugeTransform, e]
variable (hMF : ∀ m : ℕ, 1 ≤ m → Averaging.ComplexLogMeanProperties m)
  (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
include hMF hd
theorem logDirectionalDeriv_covDiff {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldSpace L n k j)
    {y : Vertex L n k (j + 1)} {x : Vertex L n k j} [Nonempty (PeriodicLattice.AxisOrdering y x)]
    (hs : ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies W y x) <
      Averaging.centreOfMassDiameter)
    (hcv : ∀ u : Vertex L n k j → ComplexMatrix2,
      (∀ z, u z ∈ PeriodicLattice.compactGaugeGroup) →
      PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.gaugeTransform u W) y x =
        u (y.toSublattice (PeriodicLattice.levelDepth k j)) *
          PeriodicLattice.complexMeanContourHolonomy W y x * (u x)⁻¹)
    {l : Vertex L n k j → ComplexMatrix2} (hl : ∀ z, l z ∈ ComplexMatrix2.hermitianTraceless)
    (hDl : covDiff W l ∈ edgeFormSpace L n k j) :
    logDirectionalDeriv ℂ
      (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X W) y x)
      (PeriodicLattice.complexMeanContourHolonomy W y x) (covDiff W l) =
      ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy W y x) (l x) -
        l (y.toSublattice (PeriodicLattice.levelDepth k j)) := by
  obtain ⟨D, hD, hcurve⟩ := logDirectionalDeriv_contour hMF hd hW hs
  rw [(hD _ hDl).1]
  set g₀ := PeriodicLattice.complexMeanContourHolonomy W y x with hg₀
  have hg₀r : g₀ ∈ PeriodicLattice.compactGaugeGroup :=
    complexMeanContourHolonomy_mem_compact hMF (fun b => hW.1 b (Set.mem_univ _)) hs
  have hu := compact_isUnit_det hg₀r
  have hdet : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ b,
      (PeriodicLattice.gaugeTransform (gaugeFlow l r) W b).det = 1 := by
    refine Eventually.of_forall fun r b => ?_
    refine compact_det ?_
    exact compact_mul_mem (compact_mul_mem (gaugeFlow_mem_compact hl r _) (hW.1 b (Set.mem_univ _)))
      (compact_inv_mem (gaugeFlow_mem_compact hl r _))
  have h1 := hcurve _ _ (gaugeTransform_flow_zero W l) (_root_.YangMills.Construction.RunningCouplingSlope.ChainRelationsProof.hasDerivAt_gaugeTransform_flow hW l) hdet
  have e : (fun r : ℝ => PeriodicLattice.complexMeanContourHolonomy
      (PeriodicLattice.gaugeTransform (gaugeFlow l r) W) y x) =
      fun r : ℝ => ComplexMatrix2.matExp (Complex.I • ((r : ℂ) •
          (-(l (y.toSublattice (PeriodicLattice.levelDepth k j)))))) *
        g₀ * (ComplexMatrix2.matExp (Complex.I • ((r : ℂ) • (-(l x)))))⁻¹ :=
    funext fun r => hcv _ (gaugeFlow_mem_compact hl r)
  rw [e] at h1
  have h2 := h1.unique
    (hasDerivAt_conj_flow (l (y.toSublattice (PeriodicLattice.levelDepth k j))) (l x) g₀)
  rw [h2]
  have hI : Complex.I⁻¹ * Complex.I = 1 := inv_mul_cancel₀ Complex.I_ne_zero
  have hgg : g₀ * g₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  simp only [add_mul, smul_mul_assoc, mul_smul_comm, smul_neg, neg_mul, smul_add, smul_smul, hI,
    one_smul, mul_assoc, hgg, mul_one, ComplexMatrix2.conjugateBy]
  abel
theorem weighted_finsum_const (hL : L ≠ 0) {y : Vertex L n k (j + 1)}
    (hsub : PeriodicLattice.unitBlock y ⊆
      (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) :
        Set (PeriodicLattice.FourTorus L n)))
    (hcard : (PeriodicLattice.unitBlock y).ncard = L ^ 4) (v : ComplexMatrix2) :
    (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite ∧
      PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ _x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y, v = v := by
  have hpos : 0 < (PeriodicLattice.unitBlock y).ncard := by
    rw [hcard]
    exact pow_pos (Nat.pos_of_ne_zero hL) 4
  have hb : (PeriodicLattice.unitBlock y).Finite := Set.finite_of_ncard_pos hpos
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite :=
    Set.Finite.of_finite_image (f := Subtype.val)
      (hb.subset (by rintro _ ⟨x, hx, rfl⟩; exact hx)) Subtype.val_injective.injOn
  refine ⟨hfin, ?_⟩
  have himage : Subtype.val '' (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) =
      PeriodicLattice.unitBlock y := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, hsub hp⟩, hp, rfl⟩
  have hn : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).ncard = L ^ 4 := by
    rw [← hcard, ← himage, Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hfin, hn, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have e : PeriodicLattice.inverseFourthPowerWeight L * ((L ^ 4 : ℕ) : ℂ) = 1 := by
    have e' : (L : ℝ) ^ (-4 : ℤ) * ((L ^ 4 : ℕ) : ℝ) = 1 := by
      rw [zpow_neg]
      push_cast
      rw [show ((4 : ℤ)) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact inv_mul_cancel₀ (pow_ne_zero 4 hL')
    unfold PeriodicLattice.inverseFourthPowerWeight
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) e'
  rw [e, one_smul]
theorem contourLogDrift_covDiff (hBlk : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k) {W : Edge L n k j → ComplexMatrix2} (hW : W ∈ fieldSpace L n k j)
    (hne : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      Nonempty (PeriodicLattice.AxisOrdering y x))
    (hs : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies W y x) <
        Averaging.centreOfMassDiameter)
    (hcv : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      ∀ u : Vertex L n k j → ComplexMatrix2, (∀ z, u z ∈ PeriodicLattice.compactGaugeGroup) →
      PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.gaugeTransform u W) y x =
        u (y.toSublattice (PeriodicLattice.levelDepth k j)) *
          PeriodicLattice.complexMeanContourHolonomy W y x * (u x)⁻¹)
    {l : Vertex L n k j → ComplexMatrix2} (hl : ∀ z, l z ∈ ComplexMatrix2.hermitianTraceless)
    (hDl : covDiff W l ∈ edgeFormSpace L n k j) :
    contourLogDrift W (covDiff W l) =
      adjointCubeAverage W l - restrictVertexFunction (j + 1) l := by
  funext y
  have hL0 : L ≠ 0 := NeZero.ne L
  obtain ⟨-, -, hcard, hsub⟩ := ((hBlk L k (j + 1) hL (by omega) (by omega) hj).1 n hn).1 y
  obtain ⟨hfin, hw⟩ := weighted_finsum_const (j := j) hMF hd hL0 hsub hcard
    (restrictVertexFunction (j + 1) l y)
  show PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X W) y x)
        (PeriodicLattice.complexMeanContourHolonomy W y x) (covDiff W l) =
    PeriodicLattice.inverseFourthPowerWeight L •
      (∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy W y x) (l x)) -
      restrictVertexFunction (j + 1) l y
  have hterm : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X W) y x)
        (PeriodicLattice.complexMeanContourHolonomy W y x) (covDiff W l) =
      ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy W y x) (l x) -
        restrictVertexFunction (j + 1) l y := by
    intro x hx
    haveI := hne y x
    exact logDirectionalDeriv_covDiff hMF hd hW (hs y x hx) (hcv y x hx) hl hDl
  rw [finsum_mem_congr rfl hterm, finsum_mem_sub_distrib _ _ hfin, smul_sub, hw]
end Orbit
section GaugeLevels
variable {L n k : ℕ} [NeZero L]
theorem adjointCubeAverage_add {j : ℕ} (W : Edge L n k j → ComplexMatrix2)
    (a b : Vertex L n k j → ComplexMatrix2) :
    adjointCubeAverage W (a + b) = adjointCubeAverage W a + adjointCubeAverage W b := by
  funext y
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  simp only [adjointCubeAverage, Pi.add_apply, conjugateBy_add]
  rw [finsum_mem_add_distrib hfin, smul_add]
theorem restrictVertexFunction_restrictVertexFunction (l : Vertex L n k 0 → ComplexMatrix2)
    {j : ℕ} (hj : j ≤ k) :
    restrictVertexFunction (j + 1) (restrictVertexFunction j l) =
      restrictVertexFunction (j + 1) l := by apply _root_.YangMills.Construction.RunningCouplingSlope.ChainMapsAtMinimizersProof.restrictVertex_restrictVertex <;> assumption
theorem restrictVertexFunction_mem (l : vertexFunctionSpace L n k 0) (j : ℕ) (x : Vertex L n k j) :
    restrictVertexFunction j (l : Vertex L n k 0 → ComplexMatrix2) x ∈
      ComplexMatrix2.hermitianTraceless :=
  vertexFunction_apply_mem l _
theorem gaugeOrbit_levels (hMF : ∀ m : ℕ, 1 ≤ m → Averaging.ComplexLogMeanProperties m)
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hC : ContourMeanGaugeCovariant) (hBlk : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X)
    (hne : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      Nonempty (PeriodicLattice.AxisOrdering y x))
    (hs : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies (levelField X j) y x) <
        Averaging.centreOfMassDiameter)
    (hcv : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      ∀ u : Vertex L n k j → ComplexMatrix2, (∀ z, u z ∈ PeriodicLattice.compactGaugeGroup) →
      PeriodicLattice.complexMeanContourHolonomy
        (PeriodicLattice.gaugeTransform u (levelField X j)) y x =
        u (y.toSublattice (PeriodicLattice.levelDepth k j)) *
          PeriodicLattice.complexMeanContourHolonomy (levelField X j) y x * (u x)⁻¹)
    (l : vertexFunctionSpace L n k 0) {ζ : LevelForms L n k}
    (hζ : formValues ζ = gaugeOrbitValues X (l : Vertex L n k 0 → ComplexMatrix2)) :
    ∀ j, j ≤ k →
      tangentTransport X ζ j = covDiff (levelField X j)
          (restrictVertexFunction j (l : Vertex L n k 0 → ComplexMatrix2)) ∧
        composedCubeAverage X j l =
          restrictVertexFunction j (l : Vertex L n k 0 → ComplexMatrix2) + chainDrift X ζ j := by
  have hmove : ∀ j, j ≤ k → tangentTransport X ζ j = covDiff (levelField X j)
      (restrictVertexFunction j (l : Vertex L n k 0 → ComplexMatrix2)) := by
    intro j hj
    have hWr : ∀ b, levelField X j b ∈ PeriodicLattice.compactGaugeGroup :=
      fun b => (hX.2 j hj).1 b (Set.mem_univ _)
    have h : (⟨tangentTransport X ζ j, tangentTransport_mem_edgeFormSpace hd hxor hX ζ hj⟩ :
        edgeFormSpace L n k j) =
        covDiffLinear (levelField X j) hWr (hxor j hj)
          ⟨restrictVertexFunction j (l : Vertex L n k 0 → ComplexMatrix2),
            fun x _ => restrictVertexFunction_mem l j x⟩ :=
      edgeForm_ext fun b hb =>
        tangentTransport_gaugeOrbit hd hC hL hn hX _ (vertexFunction_apply_mem l) hζ hj hb
    exact congrArg Subtype.val h
  intro j
  induction j with
  | zero =>
    intro hj
    refine ⟨hmove 0 hj, ?_⟩
    rw [restrictVertexFunction_zero]
    change (l : Vertex L n k 0 → ComplexMatrix2) = (l : Vertex L n k 0 → ComplexMatrix2) + 0
    rw [add_zero]
  | succ j ih =>
    intro hj
    have h : j < k := hj
    refine ⟨hmove _ hj, ?_⟩
    have hr : ∀ z, restrictVertexFunction j (l : Vertex L n k 0 → ComplexMatrix2) z ∈
        ComplexMatrix2.hermitianTraceless := restrictVertexFunction_mem l j
    have hWr : ∀ b, levelField X j b ∈ PeriodicLattice.compactGaugeGroup :=
      fun b => (hX.2 j h.le).1 b (Set.mem_univ _)
    have hDl : covDiff (levelField X j)
        (restrictVertexFunction j (l : Vertex L n k 0 → ComplexMatrix2)) ∈
        edgeFormSpace L n k j :=
      (covDiffLinear (levelField X j) hWr (hxor j h.le)
        ⟨restrictVertexFunction j (l : Vertex L n k 0 → ComplexMatrix2), fun x _ => hr x⟩).2
    have hdrift := contourLogDrift_covDiff hMF hd hBlk hL hn h (hX.2 j h.le) (hne j h) (hs j h)
      (hcv j h) hr hDl
    have e1 : composedCubeAverage X (j + 1) l =
        adjointCubeAverage (levelField X j) (composedCubeAverage X j l) := rfl
    have e2 : chainDrift X ζ (j + 1) =
        adjointCubeAverage (levelField X j) (chainDrift X ζ j) +
          contourLogDrift (levelField X j) (tangentTransport X ζ j) := rfl
    rw [e1, e2, (ih h.le).2, adjointCubeAverage_add, (ih h.le).1, hdrift,
      restrictVertexFunction_restrictVertexFunction _ h.le]
    abel
end GaugeLevels
section Onto
variable {L n k' : ℕ}
theorem leftDifferential_zero {j j' : ℕ}
    (m : (Edge L n k' j → ComplexMatrix2) → Edge L n k' j' → ComplexMatrix2)
    (U : Edge L n k' j → ComplexMatrix2) (c : Edge L n k' j') (hc : c.IsPositivelyOriented) :
    leftDifferential m U 0 c = 0 := by
  simp [leftDifferential, extendOddly, hc, logDirectionalDeriv]
def lastNoiseTangent (β : edgeFormSpace L n (k' + 1) (k' + 1)) : LevelForms L n (k' + 1) :=
  (0, Function.update (β := fun i : Fin (k' + 1) => edgeFormSpace L n (k' + 1) (i + 1)) 0
    (Fin.last k') β)
theorem tangentTransport_lastNoiseTangent (X : ChainPoint L n (k' + 1))
    (β : edgeFormSpace L n (k' + 1) (k' + 1)) :
    ∀ j, j ≤ k' → tangentTransport X (lastNoiseTangent β) j = 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    rfl
  | succ j ih =>
    intro hj
    have h : j < k' + 1 := by omega
    have hne : (⟨j, h⟩ : Fin (k' + 1)) ≠ Fin.last k' := by
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    have e : (lastNoiseTangent β).2 ⟨j, h⟩ = 0 := by
      simp only [lastNoiseTangent]
      rw [Function.update_of_ne hne]
      rfl
    simp only [tangentTransport, dif_pos h]
    funext b
    have hf : ∀ c : Edge L n (k' + 1) (j + 1), (open Classical in
        if hc : c.IsPositivelyOriented then
          ComplexMatrix2.conjugateBy (X.noise ⟨j, h⟩ ⟨c, hc⟩)
            (leftDifferential normalizedMean (levelField X j)
              (tangentTransport X (lastNoiseTangent β) j) c)
        else 0) + ((lastNoiseTangent β).2 ⟨j, h⟩ : Edge L n (k' + 1) (j + 1) → ComplexMatrix2) c =
          0 := by
      intro c
      rw [e, ih (by omega)]
      by_cases hc : c.IsPositivelyOriented
      · simp [hc, leftDifferential_zero _ _ _ hc, ComplexMatrix2.conjugateBy]
      · simp [hc]
    simp only [extendOddly, hf]
    split_ifs <;> simp
theorem tangentTransport_lastNoiseTangent_top (X : ChainPoint L n (k' + 1))
    (β : edgeFormSpace L n (k' + 1) (k' + 1))
    {b : Edge L n (k' + 1) (k' + 1)} (hb : b.IsPositivelyOriented) :
    tangentTransport X (lastNoiseTangent β) (k' + 1) b =
      (β : Edge L n (k' + 1) (k' + 1) → ComplexMatrix2) b := by
  have h : k' < k' + 1 := Nat.lt_succ_self k'
  have e : (lastNoiseTangent β).2 ⟨k', h⟩ = β := by
    simp only [lastNoiseTangent]
    exact Function.update_self
      (β := fun i : Fin (k' + 1) => edgeFormSpace L n (k' + 1) (i + 1)) _ _ _
  simp only [tangentTransport, dif_pos h]
  rw [extendOddly_pos _ hb, e, tangentTransport_lastNoiseTangent X β k' le_rfl]
  simp [hb, leftDifferential_zero _ _ _ hb, ComplexMatrix2.conjugateBy]
theorem topDeriv_surjective {X : ChainPoint L n (k' + 1)}
    (hT : IsTopDeriv X (topDeriv X)) :
    Function.Surjective (topDeriv X) := fun β =>
  ⟨lastNoiseTangent β, edgeForm_ext fun b hb => by
    rw [hT]
    exact tangentTransport_lastNoiseTangent_top X β hb⟩
end Onto
theorem chainRelationsAtCompactPoint_holds
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hA : Averaging.BlockArguments.Holds)
    (hor : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hC : ContourMeanGaugeCovariant)
    (hcov : SmoothingCovariantOnComplexDomain.Statement)
    (hBlk : BlockStructure) :
    ChainRelationsAtCompactPoint := by
  intro L hL k n hk hn X hX hpl
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    xor_isPositive_opposite hor hL hn
  obtain ⟨-, -, -, hMF, hsm⟩ := hM
  let s : Conventions.StandingParameters := ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩
  obtain ⟨hω, hfam⟩ := hsm s
  have hpos : 0 < PeriodicLattice.averagingRadiusCap L := hω.1
  have hs : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      ComplexMatrix2.familyDiameter (PeriodicLattice.contourHolonomies (levelField X j) y x) <
        Averaging.centreOfMassDiameter := by
    intro j hj y x hx
    refine hfam (PeriodicLattice.averagingRadiusCap L) ⟨hpos, le_refl _⟩ j hj
      (PeriodicLattice.Bond.forwardFrom y 0) (levelField X j)
      ⟨hX.2 j hj.le, fun p _ => hpl j hj p⟩ y (Or.inl rfl) x hx
  have hne : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      Nonempty (PeriodicLattice.AxisOrdering y x) := by
    intro j hj y x
    exact (hA s j hj (PeriodicLattice.Bond.forwardFrom y 0)).axisOrdering_nonempty y
      (Or.inl rfl) x
  have hcv : ∀ j, j < k → ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      ∀ u : Vertex L n k j → ComplexMatrix2, (∀ z, u z ∈ PeriodicLattice.compactGaugeGroup) →
      PeriodicLattice.complexMeanContourHolonomy
        (PeriodicLattice.gaugeTransform u (levelField X j)) y x =
        u (y.toSublattice (PeriodicLattice.levelDepth k j)) *
          PeriodicLattice.complexMeanContourHolonomy (levelField X j) y x * (u x)⁻¹ := by
    intro j hj y x hx u hu
    have hc : (PeriodicLattice.Bond.forwardFrom y 0 : Edge L n k (j + 1)).IsPositivelyOriented :=
      ⟨0, by show y + PeriodicLattice.unitStep L n _ 0 - y = _; abel⟩
    have hdom := ((hA s j hj (PeriodicLattice.Bond.forwardFrom y 0)).complexDomain_of_small
      (PeriodicLattice.averagingRadiusCap L) ⟨hpos, le_refl _⟩ hc (levelField X j)
      ⟨hX.2 j hj.le, fun p _ => hpl j hj p⟩).1
    exact (((hcov L hL).1 n k j hn hj).2.2.2 _ hc (levelField X j) hdom u
      (fun z _ => hu z)).2.2 y (Or.inl rfl) x hx
  obtain ⟨T, hT⟩ := exists_chainDrift_linear hd (fun m hm => hMF m hm) hxor hX (hne) hs k le_rfl
  obtain ⟨O, hO⟩ := exists_gaugeOrbitMap hxor hX
  have hIO : IsGaugeOrbitMap X (gaugeOrbitMap X) :=
    Classical.epsilon_spec (p := IsGaugeOrbitMap X) ⟨O, fun l => hO l⟩
  have hID : IsChainDriftMap X (chainDriftMap X) :=
    Classical.epsilon_spec (p := IsChainDriftMap X) ⟨T, hT⟩
  have hIT := topDeriv_spec hd hxor hX
  refine ⟨hIT, hIO, shiftedGaugeMap_spec hd hxor hX hT, hID, ?_, fun l j hj => ?_⟩
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact topDeriv_surjective hIT
  · exact gaugeOrbit_levels (fun m hm => hMF m hm) hd hC hBlk hL hn hxor hX hne hs hcv l (hIO l) j hj
end YangMills.Construction.RunningCouplingSlope.ChainRelationsProof
end
