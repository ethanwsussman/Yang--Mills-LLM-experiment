import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreUnderAGaugeFunctionProof
import YangMills.Construction.RunningCouplingSlope.DriftOfALeastPointIsLinearProof
import YangMills.Construction.RunningCouplingSlope.FibreDirectionsAtALeastPoint
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MinimizerHessian
open Filter Tower Matrices
open scoped Topology
section Mix
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
theorem hasDerivAt_mixed_deriv {Φ : E → F} {x : E} (hΦ : ContDiffAt ℝ 2 Φ x) {g : ℝ → ℝ → E}
    {v : ℝ → E} {u w : E} (h0 : g 0 0 = x) (hv : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (g s) (v s) 0)
    (hu : HasDerivAt (fun s => g s 0) u 0) (hw : HasDerivAt v w 0) :
    HasDerivAt (fun s => deriv (fun t => Φ (g s t)) 0)
      (fderiv ℝ (fderiv ℝ Φ) x u (v 0) + fderiv ℝ Φ x w) 0 := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ Φ y :=
    (hΦ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hc : Tendsto (fun s => g s 0) (𝓝 0) (𝓝 x) := by
    have := hu.continuousAt.tendsto
    simpa [h0] using this
  have heq : (fun s => deriv (fun t => Φ (g s t)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ Φ (g s 0) (v s) := by
    filter_upwards [hc.eventually hd, hv] with s h1 h2
    exact (h1.hasFDerivAt.comp_hasDerivAt 0 h2).deriv
  have hD : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) x) x :=
    ((hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hL : HasDerivAt (fun s => fderiv ℝ Φ (g s 0)) (fderiv ℝ (fderiv ℝ Φ) x u) 0 := by
    have h := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (f := fun s => g s 0)
      (l := fderiv ℝ Φ) (l' := fderiv ℝ (fderiv ℝ Φ) x) (f' := u) (by simpa [h0] using hD) hu
    exact h
  have h3 := hL.clm_apply hw
  rw [h0] at h3
  exact h3.congr_of_eventuallyEq heq
theorem hasDerivAt_mixed_deriv_line {Φ : E → F} (hΦ : ContDiffAt ℝ 2 Φ 0) (a b : E) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => Φ (s • a + t • b)) 0)
      (fderiv ℝ (fderiv ℝ Φ) 0 a b) 0 := by
  have h := hasDerivAt_mixed_deriv (g := fun s t => s • a + t • b) (v := fun _ => b) (u := a)
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
end Mix
section Chart
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
def leftExpChart (x a : A) : A := NormedSpace.exp a * x
theorem contDiffAt_two_exp (a : A) : ContDiffAt ℝ 2 (NormedSpace.exp : A → A) a :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) a).contDiffAt
theorem contDiffAt_leftExpChart (x a : A) : ContDiffAt ℝ 2 (leftExpChart x) a :=
  (contDiffAt_two_exp a).mul contDiffAt_const
theorem leftExpChart_zero (x : A) : leftExpChart x 0 = x := by simp [leftExpChart]
theorem hasDerivAt_leftExpChart_line (x a : A) (s : ℝ) :
    HasDerivAt (fun t : ℝ => leftExpChart x ((s + t) • a))
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
theorem contDiff_entry (i j : Fin 2) : ContDiff ℝ 2 (fun M : ComplexMatrix2 => M i j) := by apply _root_.YangMills.SharedProofs.p27324 <;> assumption
theorem contDiffAt_det_comp {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀) :
    ContDiffAt ℝ 2 (fun y => (f y).det) y₀ := by apply _root_.YangMills.SharedProofs.p38879 <;> assumption
theorem contDiffAt_inv_comp {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀)
    (hu : IsUnit (f y₀).det) : ContDiffAt ℝ 2 (fun y => (f y)⁻¹) y₀ := by apply _root_.YangMills.SharedProofs.p22704 <;> assumption
variable {L n k j : ℕ}
end Smooth
section Quaternions
theorem compact_mul_mem {g h : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hh : h ∈ PeriodicLattice.compactGaugeGroup) : g * h ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
theorem compact_inv_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem det_of_mem_compact {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem isUnit_det_of_mem_compact {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
end Quaternions
section Values
variable {L n k j : ℕ}
theorem fieldOfPositiveValues_of_pos (w : PositiveEdge L n k j → ComplexMatrix2)
    {b : Edge L n k j} (h : b.IsPositivelyOriented) :
    fieldOfPositiveValues w b = w ⟨b, h⟩ := by
  simp [fieldOfPositiveValues, h]
theorem fieldOfPositiveValues_of_not_pos (w : PositiveEdge L n k j → ComplexMatrix2)
    {b : Edge L n k j} (h : ¬b.IsPositivelyOriented) :
    fieldOfPositiveValues w b =
      (w ⟨b.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented h⟩)⁻¹ := by
  simp [fieldOfPositiveValues, h, PeriodicLattice.Bond.opposite_isPositivelyOriented h]
theorem fieldOfPositiveValues_mem_fieldSpace {w : PositiveEdge L n k j → ComplexMatrix2}
    (hw : ∀ c, w c ∈ PeriodicLattice.compactGaugeGroup)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    fieldOfPositiveValues w ∈ fieldSpace L n k j := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.fieldOfPositiveValues_mem_fieldSpace <;> assumption
end Values
section Levels
variable {L n k : ℕ}
theorem levelField_succ (X : ChainPoint L n k) {j : ℕ} (h : j < k) :
    levelField X (j + 1) =
      fieldOfPositiveValues fun c => X.noise ⟨j, h⟩ c * normalizedMean (levelField X j) c.1 := by
  simp [levelField, h]
theorem levelField_succ_of_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
theorem levelField_succ_of_not_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : ¬b.IsPositivelyOriented) :
    levelField X (j + 1) b = (levelField X (j + 1) b.opposite)⁻¹ := by apply _root_.YangMills.SharedProofs.p5483 <;> assumption
theorem meanRadius_ne_zero {X : ChainPoint L n k} (hX : IsCompactValued X) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) : meanRadius (levelField X i) c.1 ≠ 0 := by apply _root_.YangMills.SharedProofs.p17043 <;> assumption
end Levels
section Families
variable {L n k : ℕ} [NeZero L] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
  {Z : Y → ChainPoint L n k}
theorem isUnit_det_of_mem_fieldSpace {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (b : Edge L n k j) :
    IsUnit (V b).det := isUnit_det_of_mem_compact (hV.1 b (Set.mem_univ b))
theorem contDiffAt_levelField (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀)) :
    ∀ j, j ≤ k → ∀ b, ContDiffAt ℝ 2 (fun y => levelField (Z y) j b) y₀ := by apply _root_.YangMills.SharedProofs.p4722 <;> assumption
theorem contDiffAt_meanRadius_levelField (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀))
    (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun y => meanRadius (levelField (Z y) i) c.1) y₀ := by apply _root_.YangMills.SharedProofs.p8907 <;> assumption
theorem contDiffAt_chainAction (a : ℝ) (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀)) :
    ContDiffAt ℝ 2 (fun y => chainAction a (Z y)) y₀ := by apply _root_.YangMills.SharedProofs.p6648 <;> assumption
end Families
section Coordinates
variable {L n k : ℕ}
abbrev Coord (L n k : ℕ) : Type :=
  PositiveEdge L n k 0 ⊕ (Σ i : Fin k, PositiveEdge L n k (i + 1))
instance instFintypeCoord [NeZero L] : Fintype (Coord L n k) := Fintype.ofFinite _
def ofCoords (w : Coord L n k → ComplexMatrix2) : ChainPoint L n k :=
  ⟨fieldOfPositiveValues fun b => w (Sum.inl b), fun i c => w (Sum.inr ⟨i, c⟩)⟩
def toCoords (X : ChainPoint L n k) : Coord L n k → ComplexMatrix2 :=
  Sum.elim (fun b => X.fine b.1) fun p => X.noise p.1 p.2
theorem ofCoords_toCoords {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0) :
    ofCoords (toCoords X) = X := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.ofCoordinates_toCoordinates <;> assumption
variable [NeZero L]
theorem contDiffAt_ofCoords_fine {x : Coord L n k → ComplexMatrix2}
    (hx : ∀ b, IsUnit (x (Sum.inl b)).det) (b : Edge L n k 0) :
    ContDiffAt ℝ 2 (fun w => (ofCoords w).fine b) x := by
  have hc : ∀ ι : Coord L n k,
      ContDiffAt ℝ 2 (fun w : Coord L n k → ComplexMatrix2 => w ι) x := fun ι =>
    (contDiff_apply ℝ ComplexMatrix2 ι).contDiffAt
  by_cases h : b.IsPositivelyOriented
  · simp only [ofCoords, fieldOfPositiveValues_of_pos _ h]
    exact hc _
  · simp only [ofCoords, fieldOfPositiveValues_of_not_pos _ h]
    exact contDiffAt_inv_comp (hc _) (hx _)
theorem contDiffAt_ofCoords_noise {x : Coord L n k → ComplexMatrix2} (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun w => (ofCoords w).noise i c) x :=
  (contDiff_apply ℝ ComplexMatrix2 (Sum.inr ⟨i, c⟩ : Coord L n k)).contDiffAt
theorem isUnit_det_toCoords_fine {X : ChainPoint L n k} (hX : IsCompactValued X)
    (b : PositiveEdge L n k 0) : IsUnit (toCoords X (Sum.inl b)).det := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.isUnit_det_toCoordinates <;> assumption
theorem contDiffAt_levelField_ofCoords {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ}
    (hj : j ≤ k) (b : Edge L n k j) :
    ContDiffAt ℝ 2 (fun w => levelField (ofCoords w) j b) (toCoords X) := by
  have h0 : ofCoords (toCoords X) = X := ofCoords_toCoords (hX.2 0 (Nat.zero_le _))
  exact contDiffAt_levelField (Z := ofCoords) (y₀ := toCoords X)
    (contDiffAt_ofCoords_fine (isUnit_det_toCoords_fine hX))
    (fun i c => contDiffAt_ofCoords_noise i c) (by rwa [h0]) j hj b
theorem contDiffAt_chainAction_ofCoords {X : ChainPoint L n k} (hX : IsCompactValued X) (a : ℝ) :
    ContDiffAt ℝ 2 (fun w => chainAction a (ofCoords w)) (toCoords X) := by
  have h0 : ofCoords (toCoords X) = X := ofCoords_toCoords (hX.2 0 (Nat.zero_le _))
  exact contDiffAt_chainAction (Z := ofCoords) (y₀ := toCoords X) a
    (contDiffAt_ofCoords_fine (isUnit_det_toCoords_fine hX))
    (fun i c => contDiffAt_ofCoords_noise i c) (by rwa [h0])
end Coordinates
section Curves
theorem hasDerivAt_matrix_inv {f : ℝ → ComplexMatrix2} {f' : ComplexMatrix2}
    (hf : HasDerivAt f f' 0) (hu : IsUnit (f 0).det) :
    HasDerivAt (fun t => (f t)⁻¹) (-((f 0)⁻¹ * f' * (f 0)⁻¹)) 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.hasDerivAt_inv_matrix <;> assumption
theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
theorem matExp_I_smul_mem_compact {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
theorem exp_pi_apply {ι : Type*} [Fintype ι] (x : ι → ComplexMatrix2) (i : ι) :
    NormedSpace.exp x i = ComplexMatrix2.matExp (x i) := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.normedExp_pi_apply <;> assumption
end Curves
section Along
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem hasDerivAt_leftExpChart_zero (x a : A) :
    HasDerivAt (fun r : ℝ => leftExpChart x (r • a)) (a * x) 0 := by
  have h := hasDerivAt_leftExpChart_line x a 0
  simp only [zero_add, zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h
end Along
section Tangents
variable {L n k : ℕ} [NeZero L]
def coordsOfForms : LevelForms L n k →ₗ[ℝ] (Coord L n k → ComplexMatrix2) where
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
theorem leftExpChart_apply (x a : Coord L n k → ComplexMatrix2) (ι : Coord L n k) :
    leftExpChart x a ι = ComplexMatrix2.matExp (a ι) * x ι := by
  simp only [leftExpChart, Pi.mul_apply, exp_pi_apply]
theorem ofCoords_leftExpChart {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0)
    (ξ : LevelForms L n k) : ofCoords (leftExpChart (toCoords X) (coordsOfForms ξ)) = expMove ξ X := by
  simp only [ofCoords, expMove]
  congr 1
  · funext b
    by_cases h : b.IsPositivelyOriented
    · rw [fieldOfPositiveValues_of_pos _ h, leftExpChart_apply]
      simp only [PeriodicLattice.expTwist, if_pos h]
      rfl
    · rw [fieldOfPositiveValues_of_not_pos _ h, leftExpChart_apply]
      simp only [PeriodicLattice.expTwist, if_neg h]
      rfl
  · funext i c
    rw [leftExpChart_apply]
    rfl
theorem ofCoords_leftExpChart_smul {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0)
    (ξ : LevelForms L n k) (r : ℝ) :
    ofCoords (leftExpChart (toCoords X) (r • coordsOfForms ξ)) = expMove (r • ξ) X := by
  rw [← ofCoords_leftExpChart hX, map_smul]
def coordAction (a : ℝ) (w : Coord L n k → ComplexMatrix2) : ℝ := chainAction a (ofCoords w)
theorem levelField_ofCoords_leftExpChart_zero {X : ChainPoint L n k} (hX : IsCompactValued X)
    (a : Coord L n k → ComplexMatrix2) (j : ℕ) :
    levelField (ofCoords (leftExpChart (toCoords X) ((0 : ℝ) • a))) j = levelField X j := by
  rw [zero_smul, leftExpChart_zero, ofCoords_toCoords (hX.2 0 (Nat.zero_le _))]
end Tangents
section RealPoints
variable {L n k : ℕ} [NeZero L]
theorem isCompactValued_of_meanRadius_ne_zero
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X' : ChainPoint L n k} (hb : X'.fine ∈ fieldSpace L n k 0)
    (hn : ∀ i c, X'.noise i c ∈ PeriodicLattice.compactGaugeGroup)
    (hl : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)), meanRadius (levelField X' i) c.1 ≠ 0) :
    IsCompactValued X' := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.isCompactValued_of_meanRadius_ne_zero <;> assumption
theorem eventually_isCompactValued
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) {p : ℝ → Coord L n k → ComplexMatrix2}
    (hp : ContinuousAt p 0) (h0 : p 0 = toCoords X)
    (hr : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ ι, p r ι ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ᶠ r in 𝓝 (0 : ℝ), IsCompactValued (ofCoords (p r)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.eventually_isCompactValued <;> assumption
theorem edgeForm_mem_hermitianTraceless {j : ℕ} (B : edgeFormSpace L n k j) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    (B : Edge L n k j → ComplexMatrix2) b ∈ ComplexMatrix2.hermitianTraceless := B.2.1 b hb
theorem exists_coordsOfForms_eq_I_smul (ξ : LevelForms L n k) (r : ℝ) (ι : Coord L n k) :
    ∃ A ∈ ComplexMatrix2.hermitianTraceless, (r • coordsOfForms ξ) ι = Complex.I • A := by
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
theorem toCoords_mem_compact {X : ChainPoint L n k} (hX : IsCompactValued X) (ι : Coord L n k) :
    toCoords X ι ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.toCoordinates_mem_compact <;> assumption
theorem continuousAt_leftExpChart_line (x a : Coord L n k → ComplexMatrix2) :
    ContinuousAt (fun r : ℝ => leftExpChart x (r • a)) 0 :=
  (hasDerivAt_leftExpChart_zero x a).continuousAt
theorem eventually_isCompactValued_expMove
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (ξ : LevelForms L n k) :
    ∀ᶠ r in 𝓝 (0 : ℝ),
      IsCompactValued (ofCoords (leftExpChart (toCoords X) (r • coordsOfForms ξ))) := by
  refine eventually_isCompactValued hxor hX (continuousAt_leftExpChart_line _ _)
    (by simp [leftExpChart_zero]) (Eventually.of_forall fun r ι => ?_)
  obtain ⟨A, hA, e⟩ := exists_coordsOfForms_eq_I_smul ξ r ι
  rw [leftExpChart_apply, e]
  exact compact_mul_mem (matExp_I_smul_mem_compact hA) (toCoords_mem_compact hX ι)
end RealPoints
section Gauged
variable {L n k : ℕ} [NeZero L]
variable (hC : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
include hC hL hn in
theorem levelField_gaugeTransformPoint {X' : ChainPoint L n k} (hX' : IsCompactValued X')
    {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ j, j ≤ k → levelField (gaugeTransformPoint v X') j =
      PeriodicLattice.gaugeTransform (restrictVertexFunction j v) (levelField X' j) := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.levelField_gaugeTransformPoint <;> assumption
include hC hL hn in
theorem chainAction_gaugeTransformPoint
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (a : ℝ) {X' : ChainPoint L n k} (hX' : IsCompactValued X') {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    chainAction a (gaugeTransformPoint v X') = chainAction a X' := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.chainAction_gaugeTransformPoint <;> assumption
end Gauged
section GaugeCoordinates
variable {L n k : ℕ} [NeZero L]
abbrev gaugeExpCurve {ι : Type*} (l : ι → ComplexMatrix2) (t : ℝ) : ι → ComplexMatrix2 :=
  fun x => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • (-l x)))
theorem gaugeExpCurve_mem_compact {ι : Type*} {l : ι → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) (t : ℝ) (x : ι) :
    gaugeExpCurve l t x ∈ PeriodicLattice.compactGaugeGroup := by
  refine matExp_I_smul_mem_compact ?_
  rw [Complex.coe_smul]
  exact ComplexMatrix2.hermitianTraceless.smul_mem t
    (ComplexMatrix2.hermitianTraceless.neg_mem (hl x))
theorem gaugeExpCurve_inv {ι : Type*} (l : ι → ComplexMatrix2) (t : ℝ) (x : ι) :
    (gaugeExpCurve l t x)⁻¹ = ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • l x)) := by
  rw [gaugeExpCurve, matExp_inv]
  congr 1
  simp
def leftGaugeGenerator (l : Vertex L n k 0 → ComplexMatrix2) : Coord L n k → ComplexMatrix2 :=
  Sum.elim (fun b => -(Complex.I • l b.1.source))
    fun p => -(Complex.I • restrictVertexFunction (p.1 + 1) l p.2.1.source)
def rightGaugeGenerator (l : Vertex L n k 0 → ComplexMatrix2) : Coord L n k → ComplexMatrix2 :=
  Sum.elim (fun b => Complex.I • l b.1.target)
    fun p => Complex.I • restrictVertexFunction (p.1 + 1) l p.2.1.source
theorem real_smul_neg_I_smul (t : ℝ) (Y : ComplexMatrix2) :
    t • -(Complex.I • Y) = Complex.I • ((t : ℂ) • (-Y)) := by
  rw [Complex.coe_smul, smul_neg, smul_neg, smul_neg, smul_comm]
theorem real_smul_I_smul (t : ℝ) (Y : ComplexMatrix2) :
    t • (Complex.I • Y) = Complex.I • ((t : ℂ) • Y) := by
  rw [Complex.coe_smul, smul_comm]
theorem ofCoords_twoSidedExp (l : Vertex L n k 0 → ComplexMatrix2)
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    (w : Coord L n k → ComplexMatrix2) (t : ℝ) :
    ofCoords (NormedSpace.exp (t • leftGaugeGenerator l) * w *
        NormedSpace.exp (t • rightGaugeGenerator l)) =
      gaugeTransformPoint (gaugeExpCurve l t) (ofCoords w) := by
  have hval : ∀ ι : Coord L n k,
      (NormedSpace.exp (t • leftGaugeGenerator l) * w *
          NormedSpace.exp (t • rightGaugeGenerator l)) ι =
        ComplexMatrix2.matExp (t • leftGaugeGenerator l ι) * w ι *
          ComplexMatrix2.matExp (t • rightGaugeGenerator l ι) := by
    intro ι
    simp only [Pi.mul_apply, exp_pi_apply, Pi.smul_apply]
  simp only [ofCoords, gaugeTransformPoint]
  congr 1
  · funext b
    by_cases hb : b.IsPositivelyOriented
    · rw [fieldOfPositiveValues_of_pos _ hb, fieldOfPositiveValues_of_pos _ hb, hval]
      change ComplexMatrix2.matExp (t • -(Complex.I • l b.source)) * w _ *
        ComplexMatrix2.matExp (t • (Complex.I • l b.target)) = _
      rw [real_smul_neg_I_smul, real_smul_I_smul, gaugeExpCurve_inv]
    · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      rw [fieldOfPositiveValues_of_not_pos _ hb, fieldOfPositiveValues_of_not_pos _ hb, hval]
      change (ComplexMatrix2.matExp (t • -(Complex.I • l b.opposite.source)) * w _ *
        ComplexMatrix2.matExp (t • (Complex.I • l b.opposite.target)))⁻¹ = _
      rw [real_smul_neg_I_smul, real_smul_I_smul, gaugeExpCurve_inv, Matrix.mul_inv_rev,
        Matrix.mul_inv_rev, matExp_inv, matExp_inv]
      have e1 : b.opposite.source = b.target := rfl
      have e2 : b.opposite.target = b.source := rfl
      rw [e1, e2]
      simp only [neg_neg, smul_neg, mul_assoc, gaugeExpCurve]
  · funext i c
    rw [hval]
    change ComplexMatrix2.matExp (t • -(Complex.I • restrictVertexFunction (i + 1) l c.1.source)) *
      w _ * ComplexMatrix2.matExp (t • (Complex.I • restrictVertexFunction (i + 1) l c.1.source)) = _
    rw [real_smul_neg_I_smul, real_smul_I_smul]
    have e : restrictVertexFunction (i + 1) (gaugeExpCurve l t) c.1.source =
        gaugeExpCurve (restrictVertexFunction (i + 1) l) t c.1.source := rfl
    rw [e, gaugeExpCurve_inv]
theorem hasDerivAt_twoSided_exp {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (x α γ : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • α) * x * NormedSpace.exp (t • γ))
      (α * x + x * γ) 0 := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) α (0 : ℝ)
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) γ (0 : ℝ)
  have h3 := (h1.mul_const x).mul h2
  exact h3.congr_deriv (by simp)
end GaugeCoordinates
section Lie
theorem star_I_inv_smul (A : ComplexMatrix2) : star (Complex.I⁻¹ • A) = Complex.I • star A := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerDrift.star_inv_I_smul <;> assumption
section Second
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem eventually_differentiableAt_of_contDiffAt {m : ℝ → ComplexMatrix2}
    (hm : ContDiffAt ℝ 2 m 0) : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ m s :=
  (hm.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
theorem hasDerivAt_deriv_matrix {m : ℝ → ComplexMatrix2} (hm : ContDiffAt ℝ 2 m 0) :
    HasDerivAt (deriv m) (deriv (deriv m) 0) 0 := by
  have : ContDiffAt ℝ 1 (deriv m) 0 := by
    have h := hm.fderiv_right (m := 1) (by norm_num)
    have h2 : deriv m = fun t => fderiv ℝ m t 1 := by
      funext t; simp
    rw [h2]
    exact h.clm_apply contDiffAt_const
  exact (this.differentiableAt (by norm_num)).hasDerivAt
theorem hasDerivAt_mixed_deriv_flat_curve {Φ : ComplexMatrix2 → F} (hΦ : ContDiffAt ℝ 2 Φ 1)
    {m : ℝ → ComplexMatrix2} (hm : ContDiffAt ℝ 2 m 0) (h0 : m 0 = 1) (h1 : deriv m 0 = 0) :
    HasDerivAt (fun s => deriv (fun t => Φ (m (s + t))) 0)
      (fderiv ℝ Φ 1 (deriv (deriv m) 0)) 0 := by
  have hv : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun t => m (s + t)) (deriv m s) 0 := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt hm] with s hs
    have h' : HasDerivAt m (deriv m s) (s + 0) := by rw [add_zero]; exact hs.hasDerivAt
    exact HasDerivAt.comp_const_add (a := s) (x := (0 : ℝ)) (f := m) h'
  have hu : HasDerivAt (fun s => m (s + 0)) 0 0 := by
    have := (eventually_differentiableAt_of_contDiffAt hm).self_of_nhds.hasDerivAt
    rw [h1] at this
    simpa using this
  have h := hasDerivAt_mixed_deriv hΦ (g := fun s t => m (s + t)) (by simpa using h0) hv hu
    (hasDerivAt_deriv_matrix hm)
  simpa using h
theorem fderiv_second_velocity_eq_zero {Φ : ComplexMatrix2 → F} (hΦ : ContDiffAt ℝ 2 Φ 1)
    {m : ℝ → ComplexMatrix2} (hm : ContDiffAt ℝ 2 m 0) (h0 : m 0 = 1) (h1 : deriv m 0 = 0)
    (hc : ∀ᶠ r in 𝓝 (0 : ℝ), Φ (m r) = Φ 1) : fderiv ℝ Φ 1 (deriv (deriv m) 0) = 0 := by
  have h := hasDerivAt_mixed_deriv_flat_curve hΦ hm h0 h1
  have e : (fun s => deriv (fun t => Φ (m (s + t))) 0) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hc.eventually_nhds] with s hs
    have ht : Tendsto (fun t : ℝ => s + t) (𝓝 0) (𝓝 s) := by
      have : ContinuousAt (fun t : ℝ => s + t) 0 := by fun_prop
      simpa [ContinuousAt] using this
    have e2 : (fun t => Φ (m (s + t))) =ᶠ[𝓝 0] fun _ => Φ 1 := ht.eventually hs
    rw [e2.deriv_eq]
    simp
  have h2 : HasDerivAt (fun s : ℝ => deriv (fun t => Φ (m (s + t))) 0) (0 : F) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : F)).congr_of_eventuallyEq e
  exact h.unique h2
theorem hasDerivAt_one_add_smul (y : ComplexMatrix2) :
    HasDerivAt (fun r : ℝ => (1 : ComplexMatrix2) + r • y) y 0 := by
  have h : HasDerivAt (fun r : ℝ => r • y) ((1 : ℝ) • y) 0 := (hasDerivAt_id (0 : ℝ)).smul_const y
  simpa using h.const_add (1 : ComplexMatrix2)
theorem fderiv_at_one_of_line {Φ : ComplexMatrix2 → F} (hΦ : ContDiffAt ℝ 2 Φ 1)
    (y : ComplexMatrix2) {D : F} (h : HasDerivAt (fun r : ℝ => Φ (1 + r • y)) D 0) :
    fderiv ℝ Φ 1 y = D := by
  have h1 : HasFDerivAt Φ (fderiv ℝ Φ 1) ((fun r : ℝ => (1 : ComplexMatrix2) + r • y) 0) := by
    simpa using (hΦ.differentiableAt (by norm_num)).hasFDerivAt
  exact (h1.comp_hasDerivAt (0 : ℝ) (hasDerivAt_one_add_smul y)).unique h
theorem fderiv_det_at_one (y : ComplexMatrix2) :
    fderiv ℝ (fun M : ComplexMatrix2 => M.det) 1 y = ComplexMatrix2.fullTrace y := by
  refine fderiv_at_one_of_line (contDiffAt_det_comp contDiffAt_id) y ?_
  have ent : ∀ i j, HasDerivAt (fun r : ℝ => ((1 : ComplexMatrix2) + r • y) i j) (y i j) 0 := by
    intro i j
    have h := ((contDiff_entry i j).differentiable (by norm_num)).differentiableAt
      (x := ((1 : ComplexMatrix2) + (0 : ℝ) • y))
    have h2 := (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j :
      ComplexMatrix2 →ₗ[ℝ] ℂ)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_one_add_smul y)
    exact h2
  simp only [Matrix.det_fin_two]
  have h := ((ent 0 0).mul (ent 1 1)).sub ((ent 0 1).mul (ent 1 0))
  refine h.congr_deriv ?_
  simp [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
theorem contDiffAt_star_matrix {M₀ : ComplexMatrix2} :
    ContDiffAt ℝ 2 (fun M : ComplexMatrix2 => star M) M₀ :=
  ((starL' ℝ : ComplexMatrix2 ≃L[ℝ] ComplexMatrix2) :
    ComplexMatrix2 →L[ℝ] ComplexMatrix2).contDiff.contDiffAt
theorem fderiv_mul_star_at_one (y : ComplexMatrix2) :
    fderiv ℝ (fun M : ComplexMatrix2 => M * star M) 1 y = y + star y := by
  have hc : ContDiffAt ℝ 2 (fun M : ComplexMatrix2 => M * star M) 1 :=
    contDiffAt_id.mul contDiffAt_star_matrix
  refine fderiv_at_one_of_line hc y ?_
  have h1 := hasDerivAt_one_add_smul y
  have h := h1.mul h1.star
  refine h.congr_deriv ?_
  simp
theorem second_velocity_mem_hermitianTraceless {m : ℝ → ComplexMatrix2} (hm : ContDiffAt ℝ 2 m 0)
    (h0 : m 0 = 1) (h1 : deriv m 0 = 0)
    (hr : ∀ᶠ r in 𝓝 (0 : ℝ), m r ∈ PeriodicLattice.compactGaugeGroup) :
    Complex.I⁻¹ • deriv (deriv m) 0 ∈ ComplexMatrix2.hermitianTraceless := by
  set y := deriv (deriv m) 0 with hy
  have a1 : y + star y = 0 := by
    have hc : ContDiffAt ℝ 2 (fun M : ComplexMatrix2 => M * star M) 1 :=
      contDiffAt_id.mul contDiffAt_star_matrix
    have := fderiv_second_velocity_eq_zero hc hm h0 h1 (by
      filter_upwards [hr] with r h
      have e := Matrix.mem_unitaryGroup_iff.1 (Matrix.mem_specialUnitaryGroup_iff.1 h).1
      simp [e])
    rwa [fderiv_mul_star_at_one] at this
  have a2 : ComplexMatrix2.fullTrace y = 0 := by
    have := fderiv_second_velocity_eq_zero (Φ := fun M : ComplexMatrix2 => M.det)
      (contDiffAt_det_comp contDiffAt_id) hm h0 h1 (by
      filter_upwards [hr] with r h
      simp [det_of_mem_compact h])
    rwa [fderiv_det_at_one] at this
  have a3 : star y = -y := eq_neg_of_add_eq_zero_right a1
  refine ⟨?_, ?_⟩
  · change _ = star _
    rw [star_I_inv_smul, a3, Complex.inv_I]
    simp
  · simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul] at a2 ⊢
    rw [a2, smul_zero]
theorem fderiv_inv_at_one (y : ComplexMatrix2) :
    fderiv ℝ (fun M : ComplexMatrix2 => M⁻¹) 1 y = -y := by
  refine fderiv_at_one_of_line (contDiffAt_inv_comp contDiffAt_id (by simp)) y ?_
  have h := hasDerivAt_matrix_inv (hasDerivAt_one_add_smul y) (by simp)
  refine h.congr_deriv ?_
  simp
theorem flat_curve_inv {m : ℝ → ComplexMatrix2} (hm : ContDiffAt ℝ 2 m 0) (h0 : m 0 = 1)
    (h1 : deriv m 0 = 0) :
    ContDiffAt ℝ 2 (fun r => (m r)⁻¹) 0 ∧ deriv (fun r => (m r)⁻¹) 0 = 0 ∧
      deriv (deriv fun r => (m r)⁻¹) 0 = -deriv (deriv m) 0 := by
  have hu : IsUnit (m 0).det := by rw [h0]; simp
  have hm1 := (eventually_differentiableAt_of_contDiffAt hm).self_of_nhds.hasDerivAt
  refine ⟨contDiffAt_inv_comp hm hu, ?_, ?_⟩
  · rw [(hasDerivAt_matrix_inv hm1 hu).deriv, h1]
    simp
  · have h := hasDerivAt_mixed_deriv_flat_curve (Φ := fun M : ComplexMatrix2 => M⁻¹)
      (contDiffAt_inv_comp contDiffAt_id (by simp)) hm h0 h1
    rw [fderiv_inv_at_one] at h
    have e : (fun s => deriv (fun t => (m (s + t))⁻¹) 0) = deriv fun r => (m r)⁻¹ := by
      funext s
      have := deriv_comp_const_add (f := fun r => (m r)⁻¹) s (0 : ℝ)
      simpa using this
    rw [e] at h
    exact h.deriv
end Second
end Lie
section Forms
variable {L n k j : ℕ}
theorem extendOddly_of_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
theorem extendOddly_mem_edgeFormSpace
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Edge L n k j → ComplexMatrix2)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace L n k j := by apply _root_.YangMills.SharedProofs.p1442 <;> assumption
end Forms
section Tangents
variable {L n k : ℕ} [NeZero L]
theorem coordsOfForms_inl (ξ : LevelForms L n k) (b : PositiveEdge L n k 0) :
    coordsOfForms ξ (Sum.inl b) = Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1 := rfl
theorem coordsOfForms_inr (ξ : LevelForms L n k) (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    coordsOfForms ξ (Sum.inr ⟨i, c⟩) =
      Complex.I • (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 := rfl
theorem gaugeOrbit_fine_value {X : ChainPoint L n k} {l : Vertex L n k 0 → ComplexMatrix2}
    {ζ : LevelForms L n k} (hζ : formValues ζ = gaugeOrbitValues X l) (b : PositiveEdge L n k 0) :
    (ζ.1 : Edge L n k 0 → ComplexMatrix2) b.1 =
      ComplexMatrix2.conjugateBy (X.fine b.1) (l b.1.target) - l b.1.source := by
  have e : (ζ.1 : Edge L n k 0 → ComplexMatrix2) = covDiff X.fine l := congrArg Prod.fst hζ
  rw [e, covDiff, extendOddly_of_pos _ b.2]
theorem gaugeOrbit_noise_value {X : ChainPoint L n k} {l : Vertex L n k 0 → ComplexMatrix2}
    {ζ : LevelForms L n k} (hζ : formValues ζ = gaugeOrbitValues X l) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    (ζ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
      ComplexMatrix2.conjugateBy (X.noise i c) (restrictVertexFunction (i + 1) l c.1.source) -
        restrictVertexFunction (i + 1) l c.1.source := by
  have e : (ζ.2 i : Edge L n k (i + 1) → ComplexMatrix2) = (gaugeOrbitValues X l).2 i :=
    congrFun (congrArg Prod.snd hζ) i
  rw [e]
  simp only [gaugeOrbitValues]
  rw [extendOddly_of_pos _ c.2, dif_pos c.2]
theorem conjugateBy_mul {g A : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    ComplexMatrix2.conjugateBy g A * g = g * A := by
  rw [ComplexMatrix2.conjugateBy, mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_compact hg),
    mul_one]
theorem coordsOfForms_gaugeOrbit_mul {X : ChainPoint L n k} (hX : IsCompactValued X)
    {l : Vertex L n k 0 → ComplexMatrix2}
    {ζ : LevelForms L n k} (hζ : formValues ζ = gaugeOrbitValues X l) :
    coordsOfForms ζ * toCoords X =
      leftGaugeGenerator l * toCoords X + toCoords X * rightGaugeGenerator l := by
  funext ι
  rcases ι with b | ⟨i, c⟩
  · have hg := toCoords_mem_compact hX (Sum.inl b)
    have e : toCoords X (Sum.inl b) = X.fine b.1 := rfl
    simp only [Pi.mul_apply, Pi.add_apply, coordsOfForms_inl, gaugeOrbit_fine_value hζ]
    rw [e] at hg ⊢
    have e1 : leftGaugeGenerator l (Sum.inl b) = -(Complex.I • l b.1.source) := rfl
    have e2 : rightGaugeGenerator l (Sum.inl b) = Complex.I • l b.1.target := rfl
    rw [e1, e2, smul_sub, sub_mul, Matrix.smul_mul, conjugateBy_mul hg]
    simp only [Matrix.mul_smul, Matrix.smul_mul, neg_mul]
    abel
  · have hg : X.noise i c ∈ PeriodicLattice.compactGaugeGroup := hX.1 i c
    have e : toCoords X (Sum.inr ⟨i, c⟩) = X.noise i c := rfl
    simp only [Pi.mul_apply, Pi.add_apply, coordsOfForms_inr, gaugeOrbit_noise_value hζ, e]
    have e1 : leftGaugeGenerator l (Sum.inr ⟨i, c⟩) =
        -(Complex.I • restrictVertexFunction (i + 1) l c.1.source) := rfl
    have e2 : rightGaugeGenerator l (Sum.inr ⟨i, c⟩) =
        Complex.I • restrictVertexFunction (i + 1) l c.1.source := rfl
    rw [e1, e2, smul_sub, sub_mul, Matrix.smul_mul, conjugateBy_mul hg]
    simp only [Matrix.mul_smul, Matrix.smul_mul, neg_mul]
    abel
end Tangents
section Constraints
variable {L n k : ℕ} [NeZero L]
theorem vertexFunction_mem_hermitianTraceless {j : ℕ} (l : vertexFunctionSpace L n k j)
    (x : Vertex L n k j) :
    (l : Vertex L n k j → ComplexMatrix2) x ∈ ComplexMatrix2.hermitianTraceless :=
  l.2 x (Set.mem_univ x)
end Constraints
section Fibre
variable {L n k' : ℕ} [NeZero L]
def levelRatio (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2)
    (i : Fin (k' + 1)) (c : PositiveEdge L n (k' + 1) (i + 1)) : ComplexMatrix2 :=
  levelField (ofCoords (leftExpChart (toCoords X) a)) (i + 1) c.1 * (levelField X (i + 1) c.1)⁻¹
def topCorrection (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2) :
    Coord L n (k' + 1) → ComplexMatrix2 :=
  Sum.elim (fun _ => 1) fun p =>
    open Classical in if p.1 = Fin.last k' then (levelRatio X a p.1 p.2)⁻¹ else 1
def fibreCoords (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2) :
    Coord L n (k' + 1) → ComplexMatrix2 :=
  topCorrection X a * leftExpChart (toCoords X) a
theorem ofCoords_fine (w : Coord L n (k' + 1) → ComplexMatrix2) :
    (ofCoords w).fine = fieldOfPositiveValues fun b => w (Sum.inl b) := rfl
theorem fibreCoords_inl (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2)
    (b : PositiveEdge L n (k' + 1) 0) :
    fibreCoords X a (Sum.inl b) = leftExpChart (toCoords X) a (Sum.inl b) := by
  simp [fibreCoords, topCorrection]
theorem ofCoords_fibreCoords {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (ξ : LevelForms L n (k' + 1)) : ofCoords (fibreCoords X (coordsOfForms ξ)) = fibreMove X ξ := by
  have hb0 := hX.2 0 (Nat.zero_le _)
  have hY := ofCoords_leftExpChart hb0 ξ
  have hN : ∀ (i : Fin (k' + 1)) (c : PositiveEdge L n (k' + 1) (i + 1)),
      IsUnit (leftExpChart (toCoords X) (coordsOfForms ξ) (Sum.inr ⟨i, c⟩)).det := by
    intro i c
    obtain ⟨A, hA, e⟩ := exists_coordsOfForms_eq_I_smul ξ 1 (Sum.inr ⟨i, c⟩)
    rw [one_smul] at e
    rw [leftExpChart_apply, e]
    exact isUnit_det_of_mem_compact
      (compact_mul_mem (matExp_I_smul_mem_compact hA) (toCoords_mem_compact hX _))
  have hbase : (ofCoords (fibreCoords X (coordsOfForms ξ))).fine =
      (ofCoords (leftExpChart (toCoords X) (coordsOfForms ξ))).fine := by
    rw [ofCoords_fine, ofCoords_fine]
    congr 1
    funext b
    exact fibreCoords_inl _ _ _
  have hnoise : (ofCoords (fibreCoords X (coordsOfForms ξ))).noise =
      fun (i : Fin (k' + 1)) (c : PositiveEdge L n (k' + 1) (i + 1)) =>
      open Classical in
        if i.val + 1 = k' + 1 then
          levelField X (i + 1) c.1 *
            (normalizedMean
              (levelField (ofCoords (leftExpChart (toCoords X) (coordsOfForms ξ))) i) c.1)⁻¹
        else (ofCoords (leftExpChart (toCoords X) (coordsOfForms ξ))).noise i c := by
    funext i c
    by_cases hi : i = Fin.last k'
    · have hv : i.val + 1 = k' + 1 := by rw [hi]; rfl
      rw [if_pos hv]
      change topCorrection X (coordsOfForms ξ) (Sum.inr ⟨i, c⟩) *
        leftExpChart (toCoords X) (coordsOfForms ξ) (Sum.inr ⟨i, c⟩) = _
      have e1 : topCorrection X (coordsOfForms ξ) (Sum.inr ⟨i, c⟩) =
          (levelRatio X (coordsOfForms ξ) i c)⁻¹ := by
        simp only [topCorrection, Sum.elim_inr, if_pos hi]
      have hWr : levelField X (i + 1) c.1 ∈ PeriodicLattice.compactGaugeGroup :=
        (hX.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)
      rw [e1, levelRatio, levelField_succ_of_pos _ i.2 c.2]
      have e2 : (ofCoords (leftExpChart (toCoords X) (coordsOfForms ξ))).noise ⟨i, i.2⟩
          ⟨c.1, c.2⟩ = leftExpChart (toCoords X) (coordsOfForms ξ) (Sum.inr ⟨i, c⟩) := rfl
      rw [e2, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_compact hWr)]
      rw [mul_assoc, mul_assoc, Matrix.nonsing_inv_mul _ (hN i c), mul_one]
    · have hv : ¬ i.val + 1 = k' + 1 := by
        intro h
        apply hi
        ext
        simpa using h
      rw [if_neg hv]
      change topCorrection X (coordsOfForms ξ) (Sum.inr ⟨i, c⟩) *
        leftExpChart (toCoords X) (coordsOfForms ξ) (Sum.inr ⟨i, c⟩) = _
      have e1 : topCorrection X (coordsOfForms ξ) (Sum.inr ⟨i, c⟩) = 1 := by
        simp only [topCorrection, Sum.elim_inr, if_neg hi]
      rw [e1, one_mul]
      rfl
  have e0 : ofCoords (fibreCoords X (coordsOfForms ξ)) =
      (⟨(ofCoords (fibreCoords X (coordsOfForms ξ))).fine,
        (ofCoords (fibreCoords X (coordsOfForms ξ))).noise⟩ : ChainPoint L n (k' + 1)) := rfl
  rw [e0, hbase, hnoise, hY]
  rfl
theorem contDiffAt_levelField_leftExpChart {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    {j : ℕ} (hj : j ≤ k' + 1) (b : Edge L n (k' + 1) j) :
    ContDiffAt ℝ 2 (fun a => levelField (ofCoords (leftExpChart (toCoords X) a)) j b) 0 := by
  have h : ContDiffAt ℝ 2 (fun w => levelField (ofCoords w) j b)
      (leftExpChart (toCoords X) 0) := by
    rw [leftExpChart_zero]; exact contDiffAt_levelField_ofCoords hX hj b
  exact h.comp 0 (contDiffAt_leftExpChart (toCoords X) 0)
theorem levelRatio_zero {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (i : Fin (k' + 1))
    (c : PositiveEdge L n (k' + 1) (i + 1)) : levelRatio X 0 i c = 1 := by
  have hW : levelField X (i + 1) c.1 ∈ PeriodicLattice.compactGaugeGroup :=
    (hX.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)
  rw [levelRatio, leftExpChart_zero, ofCoords_toCoords (hX.2 0 (Nat.zero_le _))]
  exact Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_compact hW)
theorem contDiffAt_levelRatio {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (i : Fin (k' + 1)) (c : PositiveEdge L n (k' + 1) (i + 1)) :
    ContDiffAt ℝ 2 (fun a => levelRatio X a i c) 0 :=
  (contDiffAt_levelField_leftExpChart hX i.2 c.1).mul contDiffAt_const
theorem contDiffAt_topCorrection {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) :
    ContDiffAt ℝ 2 (topCorrection X) 0 := by
  refine contDiffAt_pi.2 fun ι => ?_
  rcases ι with b | ⟨i, c⟩
  · exact contDiffAt_const
  · by_cases hi : i = Fin.last k'
    · simp only [topCorrection, Sum.elim_inr, if_pos hi]
      exact contDiffAt_inv_comp (contDiffAt_levelRatio hX i c) (by rw [levelRatio_zero hX]; simp)
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
  (contDiffAt_topCorrection hX).mul (contDiffAt_leftExpChart (toCoords X) 0)
theorem fibreCoords_zero {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) :
    fibreCoords X 0 = toCoords X := by
  rw [fibreCoords, topCorrection_zero hX, leftExpChart_zero, one_mul]
def fibreAction (a : ℝ) (X : ChainPoint L n (k' + 1)) (b : Coord L n (k' + 1) → ComplexMatrix2) :
    ℝ :=
  coordAction a (fibreCoords X b)
theorem contDiffAt_fibreAction {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (a : ℝ) :
    ContDiffAt ℝ 2 (fibreAction a X) 0 := by
  have h : ContDiffAt ℝ 2 (coordAction a) (fibreCoords X 0) := by
    rw [fibreCoords_zero hX]; exact contDiffAt_chainAction_ofCoords hX a
  exact h.comp 0 (contDiffAt_fibreCoords hX)
theorem fibreSecondDeriv_eq_fderiv_fderiv {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (a : ℝ) (ξ ξ' : LevelForms L n (k' + 1)) :
    fibreSecondDeriv a X ξ ξ' =
      fderiv ℝ (fderiv ℝ (fibreAction a X)) 0 (coordsOfForms ξ) (coordsOfForms ξ') := by
  have h := hasDerivAt_mixed_deriv_line (contDiffAt_fibreAction hX a) (coordsOfForms ξ)
    (coordsOfForms ξ')
  have e : (fun s : ℝ => deriv (fun t : ℝ => chainAction a (fibreMove X (s • ξ + t • ξ'))) 0) =
      fun s : ℝ => deriv (fun t : ℝ =>
        fibreAction a X (s • coordsOfForms ξ + t • coordsOfForms ξ')) 0 := by
    funext s
    congr 1
    funext t
    rw [← ofCoords_fibreCoords hX, map_add, map_smul, map_smul]
    rfl
  rw [fibreSecondDeriv, e]
  exact h.deriv
end Fibre
section Pi
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem hasDerivAt_deriv_of_contDiffAt {m : ℝ → F} (hm : ContDiffAt ℝ 2 m 0) :
    HasDerivAt (deriv m) (deriv (deriv m) 0) 0 := by
  have : ContDiffAt ℝ 1 (deriv m) 0 := by
    have h := hm.fderiv_right (m := 1) (by norm_num)
    have h2 : deriv m = fun t => fderiv ℝ m t 1 := by
      funext t; simp
    rw [h2]
    exact h.clm_apply contDiffAt_const
  exact (this.differentiableAt (by norm_num)).hasDerivAt
theorem deriv_pi_apply_and_second {ι : Type*} [Fintype ι] {e : ℝ → ι → ComplexMatrix2}
    (he : ContDiffAt ℝ 2 e 0) :
    (∀ i, deriv e 0 i = deriv (fun r => e r i) 0) ∧
      ∀ i, deriv (deriv e) 0 i = deriv (deriv fun r => e r i) 0 := by
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ e s :=
    (he.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hc : ∀ s, DifferentiableAt ℝ e s → ∀ i, deriv e s i = deriv (fun r => e r i) s := by
    intro s hs i
    have h1 := (hasDerivAt_pi.1 hs.hasDerivAt) i
    exact h1.deriv.symm
  refine ⟨hc 0 hnear.self_of_nhds, fun i => ?_⟩
  have h2 := (hasDerivAt_pi.1 (hasDerivAt_deriv_of_contDiffAt he)) i
  have e2 : (fun s => deriv e s i) =ᶠ[𝓝 0] deriv fun r => e r i := by
    filter_upwards [hnear] with s hs
    exact hc s hs i
  exact (h2.congr_of_eventuallyEq e2.symm).deriv.symm
end Pi
section Last
variable {L n k' : ℕ} [NeZero L]
abbrev topRatioLine (X : ChainPoint L n (k' + 1)) (a : Coord L n (k' + 1) → ComplexMatrix2)
    (c : PositiveEdge L n (k' + 1) (k' + 1)) (r : ℝ) : ComplexMatrix2 :=
  levelField (ofCoords (leftExpChart (toCoords X) (r • a))) (k' + 1) c.1 *
    (levelField X (k' + 1) c.1)⁻¹
theorem contDiffAt_smul_line (a : Coord L n (k' + 1) → ComplexMatrix2) :
    ContDiffAt ℝ 2 (fun r : ℝ => r • a) 0 :=
  (contDiff_id.smul contDiff_const).contDiffAt
theorem contDiffAt_topRatioLine {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (a : Coord L n (k' + 1) → ComplexMatrix2) (c : PositiveEdge L n (k' + 1) (k' + 1)) :
    ContDiffAt ℝ 2 (topRatioLine X a c) 0 := by
  have h : ContDiffAt ℝ 2
      (fun a' => levelField (ofCoords (leftExpChart (toCoords X) a')) (k' + 1) c.1)
      ((fun r : ℝ => r • a) 0) := by
    simpa using contDiffAt_levelField_leftExpChart hX le_rfl c.1
  exact (h.comp 0 (contDiffAt_smul_line a)).mul contDiffAt_const
theorem topRatioLine_zero {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (a : Coord L n (k' + 1) → ComplexMatrix2) (c : PositiveEdge L n (k' + 1) (k' + 1)) :
    topRatioLine X a c 0 = 1 := by
  have hW : levelField X (k' + 1) c.1 ∈ PeriodicLattice.compactGaugeGroup :=
    (hX.2 (k' + 1) le_rfl).1 c.1 (Set.mem_univ _)
  simp only [topRatioLine, levelField_ofCoords_leftExpChart_zero hX]
  exact Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_compact hW)
end Last
theorem xor_isPositivelyOriented_opposite
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.xor_isPositivelyOriented_opposite <;> assumption
section Curves
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
theorem deriv_comp_curve {Φ : E → F} {x : E} (hΦ : DifferentiableAt ℝ Φ x) {p : ℝ → E} {v : E}
    (hp : HasDerivAt p v 0) (h0 : p 0 = x) : deriv (fun r => Φ (p r)) 0 = fderiv ℝ Φ x v := by
  have h : HasFDerivAt Φ (fderiv ℝ Φ x) (p 0) := by
    rw [h0]
    exact hΦ.hasFDerivAt
  exact (h.comp_hasDerivAt (0 : ℝ) hp).deriv
theorem second_deriv_comp_curve {Φ : E → F} {x : E} (hΦ : ContDiffAt ℝ 2 Φ x) {p : ℝ → E}
    (hp : ContDiffAt ℝ 2 p 0) (h0 : p 0 = x) :
    deriv (deriv fun r => Φ (p r)) 0 =
      fderiv ℝ (fderiv ℝ Φ) x (deriv p 0) (deriv p 0) + fderiv ℝ Φ x (deriv (deriv p) 0) := by
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ p s :=
    (hp.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have h := hasDerivAt_mixed_deriv (Φ := Φ) (x := x) (g := fun s t => p (s + t)) (v := deriv p)
    (u := deriv p 0) (w := deriv (deriv p) 0) hΦ (by simp [h0])
    (by
      filter_upwards [hnear] with s hs
      have h1 : HasDerivAt p (deriv p s) (s + 0) := by simpa using hs.hasDerivAt
      exact HasDerivAt.comp_const_add (a := s) (x := (0 : ℝ)) (f := p) h1)
    (by simpa using hnear.self_of_nhds.hasDerivAt) (hasDerivAt_deriv_of_contDiffAt hp)
  have e : (fun s => deriv (fun t => Φ (p (s + t))) 0) = deriv fun r => Φ (p r) := by
    funext s
    have := deriv_comp_const_add (f := fun r => Φ (p r)) s (0 : ℝ)
    simpa using this
  rw [e] at h
  exact h.deriv
theorem second_deriv_comp_sub {Φ : E → F} {x : E} (hΦ : ContDiffAt ℝ 2 Φ x) {p y : ℝ → E}
    (hp : ContDiffAt ℝ 2 p 0) (hy : ContDiffAt ℝ 2 y 0) (hp0 : p 0 = x) (hy0 : y 0 = x)
    (hv : deriv p 0 = deriv y 0) :
    deriv (deriv fun r => Φ (p r)) 0 - deriv (deriv fun r => Φ (y r)) 0 =
      fderiv ℝ Φ x (deriv (deriv p) 0 - deriv (deriv y) 0) := by
  rw [second_deriv_comp_curve hΦ hp hp0, second_deriv_comp_curve hΦ hy hy0, hv, map_sub]
  abel
theorem second_deriv_of_eventually_const {f : ℝ → F} {c : F} (h : f =ᶠ[𝓝 0] fun _ => c) :
    deriv (deriv f) 0 = 0 := by
  have h1 : deriv f =ᶠ[𝓝 0] deriv fun _ => c := h.deriv
  rw [h1.deriv_eq]
  simp
theorem second_deriv_comp_line {Φ : E → F} (hΦ : ContDiffAt ℝ 2 Φ 0) (a : E) :
    deriv (deriv fun r : ℝ => Φ (r • a)) 0 = fderiv ℝ (fderiv ℝ Φ) 0 a a := by
  have hl : ContDiffAt ℝ 2 (fun r : ℝ => r • a) 0 := (contDiff_id.smul contDiff_const).contDiffAt
  have e : deriv (fun r : ℝ => r • a) = fun _ => a := by
    funext r
    have h : HasDerivAt (fun r : ℝ => r • a) ((1 : ℝ) • a) r := (hasDerivAt_id r).smul_const a
    simpa using h.deriv
  rw [second_deriv_comp_curve hΦ hl (by simp), e]
  simp
theorem second_deriv_nonneg_of_isLocalMin {ψ : ℝ → ℝ} (hψ : ContDiffAt ℝ 2 ψ 0)
    (hm : IsLocalMin ψ 0) : 0 ≤ deriv (deriv ψ) 0 := by
  by_contra hne
  have hlt : deriv (deriv ψ) 0 < 0 := not_le.1 hne
  have hmax : IsLocalMax ψ 0 :=
    isLocalMax_of_deriv_deriv_neg hlt hm.deriv_eq_zero hψ.continuousAt
  have hc : ψ =ᶠ[𝓝 0] fun _ => ψ 0 := by
    filter_upwards [hm, hmax] with r h1 h2
    exact le_antisymm h2 h1
  rw [second_deriv_of_eventually_const hc] at hlt
  exact lt_irrefl _ hlt
end Curves
section Product
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
theorem second_deriv_flat_mul {m y : ℝ → A} (hm : ContDiffAt ℝ 2 m 0) (hy : ContDiffAt ℝ 2 y 0)
    (h0 : m 0 = 1) (h1 : deriv m 0 = 0) :
    deriv (deriv fun r => m r * y r) 0 = deriv (deriv m) 0 * y 0 + deriv (deriv y) 0 := by
  have hmn : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ m s :=
    (hm.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hyn : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ y s :=
    (hy.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have e : (deriv fun r => m r * y r) =ᶠ[𝓝 0] fun s => deriv m s * y s + m s * deriv y s := by
    filter_upwards [hmn, hyn] with s h2 h3
    exact (h2.hasDerivAt.mul h3.hasDerivAt).deriv
  rw [e.deriv_eq]
  have h2 := ((hasDerivAt_deriv_of_contDiffAt hm).mul hyn.self_of_nhds.hasDerivAt).add
    (hmn.self_of_nhds.hasDerivAt.mul (hasDerivAt_deriv_of_contDiffAt hy))
  rw [show (fun s => deriv m s * y s + m s * deriv y s) =
    (deriv m * y) + (m * deriv y) from rfl, h2.deriv, h1, h0]
  simp
end Product
section Fibre
variable {L n k' : ℕ} [NeZero L]
theorem exists_coordsOfForms_eq {k : ℕ}
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (q : Coord L n k → ComplexMatrix2)
    (hq : ∀ ι, Complex.I⁻¹ • q ι ∈ ComplexMatrix2.hermitianTraceless) :
    ∃ ζ : LevelForms L n k, coordsOfForms ζ = q := by
  classical
  let f₀ : Edge L n k 0 → ComplexMatrix2 := fun b =>
    if h : b.IsPositivelyOriented then Complex.I⁻¹ • q (Sum.inl ⟨b, h⟩) else 0
  let f : (i : Fin k) → Edge L n k (i + 1) → ComplexMatrix2 := fun i b =>
    if h : b.IsPositivelyOriented then Complex.I⁻¹ • q (Sum.inr ⟨i, ⟨b, h⟩⟩) else 0
  let B₀ : edgeFormSpace L n k 0 :=
    ⟨extendOddly f₀, extendOddly_mem_edgeFormSpace (hxor 0 (Nat.zero_le _)) f₀ fun b hb => by
      simp only [f₀, dif_pos hb]
      exact hq _⟩
  let P : (i : Fin k) → edgeFormSpace L n k (i + 1) := fun i =>
    ⟨extendOddly (f i), extendOddly_mem_edgeFormSpace (hxor _ i.2) (f i) fun b hb => by
      simp only [f, dif_pos hb]
      exact hq _⟩
  refine ⟨(B₀, P), ?_⟩
  funext ι
  rcases ι with b | ⟨i, c⟩
  · rw [coordsOfForms_inl]
    change Complex.I • extendOddly f₀ b.1 = _
    rw [extendOddly_of_pos f₀ b.2]
    simp only [f₀, dif_pos b.2]
    rw [smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
  · rw [coordsOfForms_inr]
    change Complex.I • extendOddly (f i) c.1 = _
    rw [extendOddly_of_pos (f i) c.2]
    simp only [f, dif_pos c.2]
    rw [smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
theorem levelField_fibreMove_of_le (X : ChainPoint L n (k' + 1)) (ξ : LevelForms L n (k' + 1)) :
    ∀ j, j ≤ k' → levelField (fibreMove X ξ) j = levelField (expMove ξ X) j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have h : j < k' + 1 := by omega
    rw [levelField_succ _ h, levelField_succ _ h, ih (by omega)]
    congr 1
    funext c
    have hne : ¬ ((⟨j, h⟩ : Fin (k' + 1)) : ℕ) + 1 = k' + 1 := by
      simp only
      omega
    have e : (fibreMove X ξ).noise ⟨j, h⟩ c = (expMove ξ X).noise ⟨j, h⟩ c := by
      simp only [fibreMove]
      rw [if_neg hne]
    rw [e]
theorem levelField_top_fibreMove {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    {ξ : LevelForms L n (k' + 1)} (hm : IsCompactValued (expMove ξ X)) :
    levelField (fibreMove X ξ) (k' + 1) = levelField X (k' + 1) := by
  have h : k' < k' + 1 := Nat.lt_succ_self k'
  have pos : ∀ b : Edge L n (k' + 1) (k' + 1), b.IsPositivelyOriented →
      levelField (fibreMove X ξ) (k' + 1) b = levelField X (k' + 1) b := by
    intro b hb
    have hu : IsUnit (normalizedMean (levelField (expMove ξ X) k') b).det := by
      have h1 := isUnit_det_of_mem_compact ((hm.2 (k' + 1) le_rfl).1 b (Set.mem_univ _))
      rw [levelField_succ_of_pos _ h hb, Matrix.det_mul] at h1
      exact isUnit_of_mul_isUnit_right h1
    rw [levelField_succ_of_pos _ h hb, levelField_fibreMove_of_le X ξ k' le_rfl]
    have e : (fibreMove X ξ).noise ⟨k', h⟩ ⟨b, hb⟩ = levelField X (k' + 1) b *
        (normalizedMean (levelField (expMove ξ X) k') b)⁻¹ := by
      simp only [fibreMove]
      rw [if_pos trivial]
    rw [e, mul_assoc, Matrix.nonsing_inv_mul _ hu, mul_one]
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact pos b hb
  · rw [levelField_succ_of_not_pos _ h hb, levelField_succ_of_not_pos _ h hb,
      pos _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb)]
theorem eventually_fibreCoords_line_mem_compact
    (hxor : ∀ j, j ≤ k' + 1 → ∀ b : Edge L n (k' + 1) j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (ζ : LevelForms L n (k' + 1)) :
    ∀ᶠ r in 𝓝 (0 : ℝ), ∀ ι,
      fibreCoords X (r • coordsOfForms ζ) ι ∈ PeriodicLattice.compactGaugeGroup := by
  filter_upwards [eventually_isCompactValued_expMove hxor hX ζ] with r hr ι
  have hch : ∀ ι, leftExpChart (toCoords X) (r • coordsOfForms ζ) ι ∈
      PeriodicLattice.compactGaugeGroup := fun ι => by
    obtain ⟨A, hA, e⟩ := exists_coordsOfForms_eq_I_smul ζ r ι
    rw [leftExpChart_apply, e]
    exact compact_mul_mem (matExp_I_smul_mem_compact hA) (toCoords_mem_compact hX ι)
  rcases ι with b | ⟨i, c⟩
  · rw [fibreCoords_inl]
    exact hch _
  · simp only [fibreCoords, Pi.mul_apply, topCorrection, Sum.elim_inr]
    by_cases hi : i = Fin.last k'
    · rw [if_pos hi]
      have hW : levelField X (i + 1) c.1 ∈ PeriodicLattice.compactGaugeGroup :=
        (hX.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)
      refine compact_mul_mem (compact_inv_mem (compact_mul_mem ?_ (compact_inv_mem hW))) (hch _)
      exact (hr.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)
    · rw [if_neg hi, one_mul]
      exact hch _
theorem contDiffAt_fibreCoords_line {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (a : Coord L n (k' + 1) → ComplexMatrix2) :
    ContDiffAt ℝ 2 (fun r : ℝ => fibreCoords X (r • a)) 0 := by
  have h : ContDiffAt ℝ 2 (fibreCoords X) ((fun r : ℝ => r • a) 0) := by
    simpa using contDiffAt_fibreCoords hX
  exact h.comp 0 (contDiffAt_smul_line a)
theorem fibreCoords_line_zero {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (a : Coord L n (k' + 1) → ComplexMatrix2) : fibreCoords X ((0 : ℝ) • a) = toCoords X := by
  rw [zero_smul, fibreCoords_zero hX]
theorem ofCoords_fibreCoords_line {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (ζ : LevelForms L n (k' + 1)) (r : ℝ) :
    ofCoords (fibreCoords X (r • coordsOfForms ζ)) = fibreMove X (r • ζ) := by
  rw [← map_smul, ofCoords_fibreCoords hX]
theorem eventually_fibreMove_line_compact_top
    (hxor : ∀ j, j ≤ k' + 1 → ∀ b : Edge L n (k' + 1) j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (ζ : LevelForms L n (k' + 1)) :
    ∀ᶠ r in 𝓝 (0 : ℝ), IsCompactValued (fibreMove X (r • ζ)) ∧
      levelField (fibreMove X (r • ζ)) (k' + 1) = levelField X (k' + 1) := by
  have h1 := eventually_isCompactValued hxor hX
    (contDiffAt_fibreCoords_line hX (coordsOfForms ζ)).continuousAt
    (fibreCoords_line_zero hX _) (eventually_fibreCoords_line_mem_compact hxor hX ζ)
  filter_upwards [h1, eventually_isCompactValued_expMove hxor hX ζ] with r h2 h3
  rw [ofCoords_fibreCoords_line hX] at h2
  rw [ofCoords_leftExpChart_smul (hX.2 0 (Nat.zero_le _))] at h3
  exact ⟨h2, levelField_top_fibreMove hX h3⟩
theorem deriv_fibreCoords_line {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X)
    (a : Coord L n (k' + 1) → ComplexMatrix2)
    (hz : ∀ c : PositiveEdge L n (k' + 1) (k' + 1),
      fderiv ℝ (fun w => levelField (ofCoords w) (k' + 1) c.1) (toCoords X) (a * toCoords X) = 0) :
    deriv (fun r : ℝ => fibreCoords X (r • a)) 0 = a * toCoords X := by
  set e : ℝ → Coord L n (k' + 1) → ComplexMatrix2 := fun r => topCorrection X (r • a) with he_def
  have he : ContDiffAt ℝ 2 e 0 := by
    have h : ContDiffAt ℝ 2 (topCorrection X) ((fun r : ℝ => r • a) 0) := by
      simpa using contDiffAt_topCorrection hX
    exact ContDiffAt.comp (g := topCorrection X) (f := fun r : ℝ => r • a) 0 h
      (contDiffAt_smul_line a)
  have e0 : e 0 = 1 := by
    simp only [he_def, zero_smul, topCorrection_zero hX]
  obtain ⟨p1, -⟩ := deriv_pi_apply_and_second he
  have dm : ∀ c : PositiveEdge L n (k' + 1) (k' + 1), deriv (topRatioLine X a c) 0 = 0 := by
    intro c
    have h1 : deriv (fun r : ℝ =>
        levelField (ofCoords (leftExpChart (toCoords X) (r • a))) (k' + 1) c.1) 0 = 0 := by
      rw [deriv_comp_curve ((contDiffAt_levelField_ofCoords hX le_rfl c.1).differentiableAt
        (by norm_num)) (hasDerivAt_leftExpChart_zero _ a) (by simp [leftExpChart_zero]), hz c]
    have h2 : DifferentiableAt ℝ
        (fun r : ℝ => levelField (ofCoords (leftExpChart (toCoords X) (r • a))) (k' + 1) c.1) 0 :=
      by
        have hcd : ContDiffAt ℝ 2
            (fun a' => levelField (ofCoords (leftExpChart (toCoords X) a')) (k' + 1) c.1)
            ((fun r : ℝ => r • a) 0) := by
          simpa using contDiffAt_levelField_leftExpChart hX le_rfl c.1
        exact (hcd.comp 0 (contDiffAt_smul_line a)).differentiableAt (by norm_num)
    have h3 := h2.hasDerivAt.mul_const (levelField X (k' + 1) c.1)⁻¹
    rw [h1, zero_mul] at h3
    exact h3.deriv
  have e1 : deriv e 0 = 0 := by
    funext ι
    rw [p1 ι]
    rcases ι with b | ⟨i, c⟩
    · have : (fun r => e r (Sum.inl b)) = fun _ => 1 := by
        funext r
        rfl
      rw [this]
      simp
    · by_cases hi : i = Fin.last k'
      · subst hi
        have : (fun r => e r (Sum.inr ⟨Fin.last k', c⟩)) = fun r => (topRatioLine X a c r)⁻¹ := by
          funext r
          simp only [he_def, topCorrection, Sum.elim_inr, if_true]
          rfl
        rw [this]
        exact (flat_curve_inv (contDiffAt_topRatioLine hX a c) (topRatioLine_zero hX a c)
          (dm c)).2.1
      · have : (fun r => e r (Sum.inr ⟨i, c⟩)) = fun _ => 1 := by
          funext r
          simp only [he_def, topCorrection, Sum.elim_inr, if_neg hi]
        rw [this]
        simp
  have hed : HasDerivAt e 0 0 := by
    have h := (he.differentiableAt (by norm_num)).hasDerivAt
    rwa [e1] at h
  have h := hed.mul (hasDerivAt_leftExpChart_zero (toCoords X) a)
  have eq : (fun r : ℝ => fibreCoords X (r • a)) = e * fun r => leftExpChart (toCoords X) (r • a) :=
    rfl
  rw [eq, h.deriv, e0]
  simp
end Fibre
section Orbit
variable {L n k' : ℕ} [NeZero L]
theorem twoSidedExp_mem_compact {k : ℕ} {X : ChainPoint L n k} (hX : IsCompactValued X)
    {l : Vertex L n k 0 → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) (r : ℝ) (ι : Coord L n k) :
    (NormedSpace.exp (r • leftGaugeGenerator l) * toCoords X *
        NormedSpace.exp (r • rightGaugeGenerator l)) ι ∈
      PeriodicLattice.compactGaugeGroup := by
  have hres : ∀ (j : ℕ) (y : Vertex L n k j),
      restrictVertexFunction j l y ∈ ComplexMatrix2.hermitianTraceless := fun j y => by
    simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap]
    exact hl _
  have hgc : ∀ Y : ComplexMatrix2, Y ∈ ComplexMatrix2.hermitianTraceless →
      ComplexMatrix2.matExp (r • -(Complex.I • Y)) ∈ PeriodicLattice.compactGaugeGroup ∧
      ComplexMatrix2.matExp (r • (Complex.I • Y)) ∈ PeriodicLattice.compactGaugeGroup :=
    fun Y hY => by
    have a1 : (r : ℂ) • (-Y) ∈ ComplexMatrix2.hermitianTraceless := by
      rw [Complex.coe_smul]
      exact ComplexMatrix2.hermitianTraceless.smul_mem r
        (ComplexMatrix2.hermitianTraceless.neg_mem hY)
    have a2 : (r : ℂ) • Y ∈ ComplexMatrix2.hermitianTraceless := by
      rw [Complex.coe_smul]
      exact ComplexMatrix2.hermitianTraceless.smul_mem r hY
    rw [real_smul_neg_I_smul, real_smul_I_smul]
    exact ⟨matExp_I_smul_mem_compact a1, matExp_I_smul_mem_compact a2⟩
  simp only [Pi.mul_apply, exp_pi_apply, Pi.smul_apply]
  rcases ι with b | ⟨i, c⟩
  · exact compact_mul_mem (compact_mul_mem (hgc _ (hl b.1.source)).1 (toCoords_mem_compact hX _))
      (hgc _ (hl b.1.target)).2
  · exact compact_mul_mem (compact_mul_mem (hgc _ (hres _ c.1.source)).1 (toCoords_mem_compact hX _))
      (hgc _ (hres _ c.1.source)).2
theorem exists_fibreSecondDeriv_gaugeOrbit_eq_deriv (hC : ContourMeanGaugeCovariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hxor : ∀ j, j ≤ k' + 1 → ∀ b : Edge L n (k' + 1) j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (a : ℝ)
    {l : Vertex L n (k' + 1) 0 → ComplexMatrix2} (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    (hl0 : ∀ y : Vertex L n (k' + 1) (k' + 1), restrictVertexFunction (k' + 1) l y = 0)
    {ξ : LevelForms L n (k' + 1)} (hξ : formValues ξ = gaugeOrbitValues X l) :
    ∃ ζ : LevelForms L n (k' + 1), fibreSecondDeriv a X ξ ξ =
      deriv (fun r : ℝ => chainAction a (fibreMove X (r • ζ))) 0 := by
  set x := toCoords X with hx
  set h := coordsOfForms ξ with hh
  let y : ℝ → Coord L n (k' + 1) → ComplexMatrix2 := fun r =>
    NormedSpace.exp (r • leftGaugeGenerator l) * x * NormedSpace.exp (r • rightGaugeGenerator l)
  let p : ℝ → Coord L n (k' + 1) → ComplexMatrix2 := fun r => fibreCoords X (r • h)
  have hy : ContDiffAt ℝ 2 y 0 := by
    have h1 : ∀ c : Coord L n (k' + 1) → ComplexMatrix2,
        ContDiffAt ℝ 2 (fun r : ℝ => NormedSpace.exp (r • c)) 0 := fun c => by
      have h2 : ContDiffAt ℝ 2 (NormedSpace.exp : (Coord L n (k' + 1) → ComplexMatrix2) → _)
          ((fun r : ℝ => r • c) 0) := contDiffAt_two_exp _
      exact h2.comp 0 (contDiffAt_smul_line c)
    exact ((h1 _).mul contDiffAt_const).mul (h1 _)
  have hp : ContDiffAt ℝ 2 p 0 := contDiffAt_fibreCoords_line hX h
  have y0 : y 0 = x := by simp [y]
  have p0 : p 0 = x := fibreCoords_line_zero hX h
  have yd : deriv y 0 = h * x :=
    (hasDerivAt_twoSided_exp x _ _).deriv.trans (coordsOfForms_gaugeOrbit_mul hX hξ).symm
  have hb0 := hX.2 0 (Nat.zero_le _)
  have dec : ∀ r, ofCoords (y r) = gaugeTransformPoint (gaugeExpCurve l r) X := fun r => by
    have h1 := ofCoords_twoSidedExp l hl x r
    rwa [hx, ofCoords_toCoords hb0] at h1
  have top : ∀ r, levelField (ofCoords (y r)) (k' + 1) = levelField X (k' + 1) := fun r => by
    rw [dec r, _root_.YangMills.Construction.RunningCouplingSlope.MinimizerHessian.levelField_gaugeTransformPoint hC hL hn hX (gaugeExpCurve_mem_compact hl r) _ le_rfl]
    have e : ∀ s : Vertex L n (k' + 1) (k' + 1),
        restrictVertexFunction (k' + 1) (gaugeExpCurve l r) s = 1 :=
      fun s => by
        have e1 : restrictVertexFunction (k' + 1) (gaugeExpCurve l r) s =
            gaugeExpCurve (restrictVertexFunction (k' + 1) l) r s := rfl
        rw [e1]
        simp only [gaugeExpCurve]
        rw [hl0 s]
        simp [ComplexMatrix2.matExp]
    funext b
    simp only [PeriodicLattice.gaugeTransform, e]
    simp
  have act : ∀ r, coordAction a (y r) = chainAction a X := fun r => by
    rw [coordAction, dec r]
    exact _root_.YangMills.Construction.RunningCouplingSlope.MinimizerHessian.chainAction_gaugeTransformPoint hC hL hn hg a hX (gaugeExpCurve_mem_compact hl r)
  let T : PositiveEdge L n (k' + 1) (k' + 1) → (Coord L n (k' + 1) → ComplexMatrix2) →
      ComplexMatrix2 :=
    fun c w => levelField (ofCoords w) (k' + 1) c.1
  have hT : ∀ c, ContDiffAt ℝ 2 (T c) x := fun c => contDiffAt_levelField_ofCoords hX le_rfl c.1
  have Ty : ∀ c, (fun r => T c (y r)) =ᶠ[𝓝 0] fun _ => levelField X (k' + 1) c.1 := fun c =>
    Eventually.of_forall fun r => congrFun (top r) c.1
  have hyd : HasDerivAt y (deriv y 0) 0 := (hy.differentiableAt (by norm_num)).hasDerivAt
  have hz₁ : ∀ c, fderiv ℝ (T c) x (h * x) = 0 := fun c => by
    rw [← yd, ← deriv_comp_curve ((hT c).differentiableAt (by norm_num)) hyd y0,
      (Ty c).deriv_eq]
    simp
  have pd : deriv p 0 = h * x := deriv_fibreCoords_line hX h hz₁
  have pdy : deriv p 0 = deriv y 0 := pd.trans yd.symm
  let m : ℝ → Coord L n (k' + 1) → ComplexMatrix2 := fun r ι => p r ι * (y r ι)⁻¹
  have yr : ∀ r ι, y r ι ∈ PeriodicLattice.compactGaugeGroup := fun r ι =>
    twoSidedExp_mem_compact hX hl r ι
  have hm : ContDiffAt ℝ 2 m 0 := by
    refine contDiffAt_pi.2 fun ι => ?_
    exact (contDiffAt_pi.1 hp ι).mul
      (contDiffAt_inv_comp (contDiffAt_pi.1 hy ι) (isUnit_det_of_mem_compact (yr 0 ι)))
  have hmy : (fun r => m r * y r) = p := by
    funext r ι
    simp only [m, Pi.mul_apply]
    rw [mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_compact (yr r ι)), mul_one]
  have m0 : m 0 = 1 := by
    funext ι
    simp only [m, Pi.one_apply]
    rw [p0, y0]
    exact Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_compact (toCoords_mem_compact hX ι))
  have m1 : deriv m 0 = 0 := by
    have hmd := (hm.differentiableAt (by norm_num)).hasDerivAt
    have h1 : HasDerivAt (fun r => m r * y r) (deriv m 0 * y 0 + m 0 * deriv y 0) 0 :=
      hmd.mul hyd
    have h2 : deriv m 0 * x = 0 := by
      rw [hmy, m0, y0, one_mul] at h1
      have h3 := h1.deriv
      rw [pdy] at h3
      simpa using h3.symm
    funext ι
    have h3 := congrFun h2 ι
    simp only [Pi.mul_apply, Pi.zero_apply] at h3 ⊢
    have hu := isUnit_det_of_mem_compact (toCoords_mem_compact hX ι)
    calc deriv m 0 ι = deriv m 0 ι * (x ι * (x ι)⁻¹) := by
          rw [hx, Matrix.mul_nonsing_inv _ hu, mul_one]
      _ = 0 := by rw [← mul_assoc, h3, zero_mul]
  obtain ⟨q1, q2⟩ := deriv_pi_apply_and_second hm
  set c' := deriv (deriv m) 0 with hc'
  have hlie : ∀ ι, Complex.I⁻¹ • c' ι ∈ ComplexMatrix2.hermitianTraceless := fun ι => by
    rw [q2 ι]
    refine second_velocity_mem_hermitianTraceless (contDiffAt_pi.1 hm ι) (congrFun m0 ι) ?_ ?_
    · rw [← q1 ι, m1]
      rfl
    · filter_upwards [eventually_fibreCoords_line_mem_compact hxor hX ξ] with r hr
      exact compact_mul_mem (hr ι) (compact_inv_mem (yr r ι))
  obtain ⟨ζ, hζ⟩ := exists_coordsOfForms_eq hxor c' hlie
  have hD : deriv (deriv p) 0 - deriv (deriv y) 0 = c' * x := by
    have h1 := second_deriv_flat_mul hm hy m0 m1
    rw [hmy, y0] at h1
    rw [h1]
    abel
  have hz₂ : ∀ c, fderiv ℝ (T c) x (c' * x) = 0 := fun c => by
    have h1 := second_deriv_comp_sub (hT c) hp hy p0 y0 pdy
    have Tp : (fun r => T c (p r)) =ᶠ[𝓝 0] fun _ => levelField X (k' + 1) c.1 := by
      filter_upwards [eventually_fibreMove_line_compact_top hxor hX ξ] with r hr
      have e : ofCoords (p r) = fibreMove X (r • ξ) := ofCoords_fibreCoords_line hX ξ r
      change levelField (ofCoords (p r)) (k' + 1) c.1 = _
      rw [e, hr.2]
    rw [hD, second_deriv_of_eventually_const (Ty c), second_deriv_of_eventually_const Tp,
      sub_zero] at h1
    exact h1.symm
  have pd₂ : deriv (fun r : ℝ => fibreCoords X (r • c')) 0 = c' * x :=
    deriv_fibreCoords_line hX c' hz₂
  refine ⟨ζ, ?_⟩
  have hΨ : ContDiffAt ℝ 2 (coordAction a) x := contDiffAt_chainAction_ofCoords hX a
  have s1 := second_deriv_comp_sub hΨ hp hy p0 y0 pdy
  have s0 : (fun r => coordAction a (y r)) =ᶠ[𝓝 0] fun _ => chainAction a X :=
    Eventually.of_forall act
  rw [hD, second_deriv_of_eventually_const s0, sub_zero] at s1
  have s2 : fibreSecondDeriv a X ξ ξ = deriv (deriv fun r => coordAction a (p r)) 0 := by
    rw [fibreSecondDeriv_eq_fderiv_fderiv hX]
    exact (second_deriv_comp_line (contDiffAt_fibreAction hX a) h).symm
  have s3 : (fun r : ℝ => chainAction a (fibreMove X (r • ζ))) =
      fun r => coordAction a (fibreCoords X (r • c')) := by
    funext r
    rw [coordAction, ← hζ, ofCoords_fibreCoords_line hX]
  have hpc : HasDerivAt (fun r : ℝ => fibreCoords X (r • c'))
      (deriv (fun r : ℝ => fibreCoords X (r • c')) 0) 0 :=
    ((contDiffAt_fibreCoords_line hX c').differentiableAt (by norm_num)).hasDerivAt
  rw [s2, s1, s3, deriv_comp_curve (hΨ.differentiableAt (by norm_num)) hpc
    (fibreCoords_line_zero hX c'), pd₂]
theorem fibreSecondDeriv_self_nonneg {X : ChainPoint L n (k' + 1)} (hX : IsCompactValued X) (a : ℝ)
    (ξ : LevelForms L n (k' + 1))
    (hmin : IsLocalMin (fun r : ℝ => chainAction a (fibreMove X (r • ξ))) 0) :
    0 ≤ fibreSecondDeriv a X ξ ξ := by
  have e : (fun r : ℝ => chainAction a (fibreMove X (r • ξ))) =
      fun r : ℝ => fibreAction a X (r • coordsOfForms ξ) := by
    funext r
    rw [fibreAction, coordAction, ofCoords_fibreCoords_line hX]
  have hc : ContDiffAt ℝ 2 (fun r : ℝ => fibreAction a X (r • coordsOfForms ξ)) 0 := by
    have h : ContDiffAt ℝ 2 (fibreAction a X) ((fun r : ℝ => r • coordsOfForms ξ) 0) := by
      simpa using contDiffAt_fibreAction hX a
    exact ContDiffAt.comp (g := fibreAction a X) (f := fun r : ℝ => r • coordsOfForms ξ) 0 h
      (contDiffAt_smul_line _)
  rw [e] at hmin
  have h2 := second_deriv_nonneg_of_isLocalMin hc hmin
  rw [second_deriv_comp_line (contDiffAt_fibreAction hX a) (coordsOfForms ξ)] at h2
  rw [fibreSecondDeriv_eq_fderiv_fderiv hX]
  exact h2
theorem isLocalMin_chainAction_fibreMove_line
    (hxor : ∀ j, j ≤ k' + 1 → ∀ b : Edge L n (k' + 1) j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {a : ℝ} {W : Edge L n (k' + 1) (k' + 1) → ComplexMatrix2} {X : ChainPoint L n (k' + 1)}
    (hX : IsMinimizerOver a W X) (ζ : LevelForms L n (k' + 1)) :
    IsLocalMin (fun r : ℝ => chainAction a (fibreMove X (r • ζ))) 0 := by
  have hr : IsCompactValued X := hX.compact
  have e0 : chainAction a (fibreMove X ((0 : ℝ) • ζ)) = chainAction a X := by
    rw [← ofCoords_fibreCoords_line hr, fibreCoords_line_zero hr,
      ofCoords_toCoords (hr.2 0 (Nat.zero_le _))]
  filter_upwards [eventually_fibreMove_line_compact_top hxor hr ζ] with r h1
  change chainAction a (fibreMove X ((0 : ℝ) • ζ)) ≤ chainAction a (fibreMove X (r • ζ))
  rw [e0]
  exact hX.le _ h1.1 (h1.2.trans hX.top_eq)
end Orbit
theorem fibreHessianNonnegAtMinimizer_holds (hC : ContourMeanGaugeCovariant)
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction) :
    FibreHessianNonnegAtMinimizer := by
  intro a ha L hL k n hk hn W X hX
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hxor : ∀ j, j ≤ k' + 1 → ∀ b : Edge L n (k' + 1) j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    xor_isPositivelyOriented_opposite hb hL hn
  have hr : IsCompactValued X := hX.compact
  refine ⟨fun ξ => fibreSecondDeriv_self_nonneg hr a ξ
    (isLocalMin_chainAction_fibreMove_line hxor hX ξ), fun l hl ξ hξ => ?_⟩
  obtain ⟨ζ, hζ⟩ := exists_fibreSecondDeriv_gaugeOrbit_eq_deriv hC hL hn hg hxor hr a
    (fun x => vertexFunction_mem_hermitianTraceless l x) hl hξ
  rw [hζ]
  exact (isLocalMin_chainAction_fibreMove_line hxor hX ζ).deriv_eq_zero
end YangMills.Construction.RunningCouplingSlope.MinimizerHessian
end
