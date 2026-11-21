import YangMills.Construction.Lattice.OppositeBondsAndPositiveValues
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometriesProof
import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreIsSmoothProof
import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreUnderAGaugeFunction
import YangMills.Construction.RunningCouplingSlope.CovarianceOfThePlainAverage
import YangMills.Construction.RunningCouplingSlope.TheOrbitMapReadsNearCellsProof
import Mathlib
import YangMills.Construction.Matrices.SpecialUnitaryTwo
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FibreActionProof
open Filter Tower Matrices
open scoped Topology
section ExpChart
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
def expChart (x a : A) : A := NormedSpace.exp a * x
theorem contDiffAt_normedExp (a : A) : ContDiffAt ℝ 2 (NormedSpace.exp : A → A) a :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) a).contDiffAt
theorem contDiffAt_expChart (x a : A) : ContDiffAt ℝ 2 (expChart x) a :=
  (contDiffAt_normedExp a).mul contDiffAt_const
theorem expChart_zero (x : A) : expChart x 0 = x := by simp [expChart]
end ExpChart
section Smooth
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
theorem contDiffAt_inv {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀)
    (hu : IsUnit (f y₀).det) :
    ContDiffAt ℝ 2 (fun y => (f y)⁻¹) y₀ := by apply _root_.YangMills.SharedProofs.p22704 <;> assumption
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
theorem det_eq_normSq_sum {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices) :
    M.det = ((Complex.normSq (M 0 0) + Complex.normSq (M 0 1) : ℝ) : ℂ) :=
  ComplexMatrix2.det_quaternionMatrix hM
theorem normalize_mem_compactGaugeGroup {M : ComplexMatrix2} (hM : M ∈ quaternionMatrices)
    (h : M.det ≠ 0) :
    (M.det ^ (1 / 2 : ℂ))⁻¹ • M ∈ PeriodicLattice.compactGaugeGroup :=
  ComplexMatrix2.normalize_quaternionMatrix_mem_specialUnitary hM h
variable {L n k j : ℕ}
theorem compact_mul_mem {g h : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hh : h ∈ PeriodicLattice.compactGaugeGroup) :
    g * h ∈ PeriodicLattice.compactGaugeGroup := ComplexMatrix2.specialUnitary.mul_mem hg hh
theorem compact_inv_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem det_eq_one_of_compact {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem isUnit_det_of_compact {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem pathHolonomy_mem_compact {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup)
    (Γ : List (Edge L n k j)) :
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
    fieldOfPositiveValues w ∈ fieldSpace L n k j := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases h : b.IsPositivelyOriented
    · rw [fieldOfPositiveValues_of_pos w h]; exact hw _
    · rw [fieldOfPositiveValues_of_not_pos w h]; exact compact_inv_mem (hw _)
  · by_cases h : b.IsPositivelyOriented
    · have h' : ¬b.opposite.IsPositivelyOriented := by
        rcases hx b with ⟨_, h2⟩ | h2
        · exact h2
        · exact absurd h h2.2
      rw [fieldOfPositiveValues_of_not_pos w h', fieldOfPositiveValues_of_pos w h]
      rfl
    · have h' := PeriodicLattice.Bond.opposite_isPositivelyOriented h
      rw [fieldOfPositiveValues_of_pos w h', fieldOfPositiveValues_of_not_pos w h]
      exact (Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_compact (hw _))).symm
end Values
section Levels
variable {L n k : ℕ}
theorem levelField_succ (X : ChainPoint L n k) {j : ℕ} (h : j < k) :
    levelField X (j + 1) =
      fieldOfPositiveValues fun c =>
        X.noise ⟨j, h⟩ c * normalizedMean (levelField X j) c.1 := by
  simp [levelField, h]
theorem levelField_succ_of_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
theorem levelField_succ_of_not_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k)
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
    IsUnit (V b).det := isUnit_det_of_compact (hV.1 b (Set.mem_univ b))
theorem contDiffAt_meanRadius_levelField (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀))
    (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun y => meanRadius (levelField (Z y) i) c.1) y₀ := by apply _root_.YangMills.SharedProofs.p8907 <;> assumption
end Families
section Coordinates
variable {L n k : ℕ}
abbrev Coordinate (L n k : ℕ) : Type :=
  PositiveEdge L n k 0 ⊕ (Σ i : Fin k, PositiveEdge L n k (i + 1))
instance [NeZero L] : Fintype (Coordinate L n k) := Fintype.ofFinite _
def ofCoordinates (w : Coordinate L n k → ComplexMatrix2) : ChainPoint L n k :=
  ⟨fieldOfPositiveValues fun b => w (Sum.inl b), fun i c => w (Sum.inr ⟨i, c⟩)⟩
def toCoordinates (X : ChainPoint L n k) : Coordinate L n k → ComplexMatrix2 :=
  Sum.elim (fun b => X.fine b.1) fun p => X.noise p.1 p.2
theorem ofCoordinates_toCoordinates {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0) :
    ofCoordinates (toCoordinates X) = X := by
  obtain ⟨U, N⟩ := X
  simp only [ofCoordinates, toCoordinates, Sum.elim_inl, Sum.elim_inr]
  congr 1
  funext b
  by_cases h : b.IsPositivelyOriented
  · rw [fieldOfPositiveValues_of_pos _ h]
  · rw [fieldOfPositiveValues_of_not_pos _ h]
    have := hX.2 b.opposite (Set.mem_univ _)
    exact this.symm
variable [NeZero L]
theorem contDiffAt_ofCoordinates_fine {x : Coordinate L n k → ComplexMatrix2}
    (hx : ∀ b, IsUnit (x (Sum.inl b)).det)
    (b : Edge L n k 0) : ContDiffAt ℝ 2 (fun w => (ofCoordinates w).fine b) x := by
  have hc : ∀ ι : Coordinate L n k,
      ContDiffAt ℝ 2 (fun w : Coordinate L n k → ComplexMatrix2 => w ι) x := fun ι =>
    (contDiff_apply ℝ ComplexMatrix2 ι).contDiffAt
  by_cases h : b.IsPositivelyOriented
  · simp only [ofCoordinates, fieldOfPositiveValues_of_pos _ h]
    exact hc _
  · simp only [ofCoordinates, fieldOfPositiveValues_of_not_pos _ h]
    exact contDiffAt_inv (hc _) (hx _)
theorem contDiffAt_ofCoordinates_noise {x : Coordinate L n k → ComplexMatrix2} (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun w => (ofCoordinates w).noise i c) x :=
  (contDiff_apply ℝ ComplexMatrix2 (Sum.inr ⟨i, c⟩ : Coordinate L n k)).contDiffAt
theorem isUnit_det_toCoordinates {X : ChainPoint L n k} (hX : IsCompactValued X)
    (b : PositiveEdge L n k 0) :
    IsUnit (toCoordinates X (Sum.inl b)).det :=
  isUnit_det_of_mem_fieldSpace (hX.2 0 (Nat.zero_le _)) b.1
theorem contDiffAt_meanRadius_coordinates {X : ChainPoint L n k} (hX : IsCompactValued X)
    (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun w => meanRadius (levelField (ofCoordinates w) i) c.1)
      (toCoordinates X) := by
  have h0 : ofCoordinates (toCoordinates X) = X :=
    ofCoordinates_toCoordinates (hX.2 0 (Nat.zero_le _))
  exact contDiffAt_meanRadius_levelField (Z := ofCoordinates) (y₀ := toCoordinates X)
    (contDiffAt_ofCoordinates_fine (isUnit_det_toCoordinates hX))
    (fun i c => contDiffAt_ofCoordinates_noise i c) (by rwa [h0]) i c
end Coordinates
section Curves
theorem matExp_I_smul_mem_compact {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
theorem normedExp_pi_apply {ι : Type*} [Fintype ι] (x : ι → ComplexMatrix2) (i : ι) :
    NormedSpace.exp x i = ComplexMatrix2.matExp (x i) := by
  letI : NormedAlgebra ℚ ComplexMatrix2 := NormedAlgebra.restrictScalars ℚ ℝ ComplexMatrix2
  exact congrFun (Pi.exp_def x) i
end Curves
section Tangents
variable {L n k : ℕ} [NeZero L]
def toAlgebraValues : LevelForms L n k →ₗ[ℝ] (Coordinate L n k → ComplexMatrix2) where
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
theorem expChart_apply (x a : Coordinate L n k → ComplexMatrix2) (ι : Coordinate L n k) :
    expChart x a ι = ComplexMatrix2.matExp (a ι) * x ι := by
  simp only [expChart, Pi.mul_apply, normedExp_pi_apply]
theorem ofCoordinates_expChart {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0)
    (ξ : LevelForms L n k) :
    ofCoordinates (expChart (toCoordinates X) (toAlgebraValues ξ)) = expMove ξ X := by
  simp only [ofCoordinates, expMove]
  congr 1
  · funext b
    by_cases h : b.IsPositivelyOriented
    · rw [fieldOfPositiveValues_of_pos _ h, expChart_apply]
      simp only [PeriodicLattice.expTwist, if_pos h]
      rfl
    · rw [fieldOfPositiveValues_of_not_pos _ h, expChart_apply]
      simp only [PeriodicLattice.expTwist, if_neg h]
      rfl
  · funext i c
    rw [expChart_apply]
    rfl
end Tangents
section CompactPoints
variable {L n k : ℕ} [NeZero L]
theorem isCompactValued_of_meanRadius_ne_zero
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X' : ChainPoint L n k} (hb : X'.fine ∈ fieldSpace L n k 0)
    (hn : ∀ i c, X'.noise i c ∈ PeriodicLattice.compactGaugeGroup)
    (hl : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      meanRadius (levelField X' i) c.1 ≠ 0) :
    IsCompactValued X' := by
  refine ⟨hn, ?_⟩
  intro j
  induction j with
  | zero => intro _; exact hb
  | succ j ih =>
    intro hj
    have h : j < k := hj
    have hr := ih h.le
    rw [levelField_succ X' h]
    refine fieldOfPositiveValues_mem_fieldSpace (fun c => compact_mul_mem (hn _ _) ?_) (hxor _ hj)
    exact normalize_mem_compactGaugeGroup
      (contourMean_mem_quaternionMatrices (fun b' => hr.1 b' (Set.mem_univ _)) c.1)
      (det_contourMean_ne_zero (hl ⟨j, h⟩ c))
theorem eventually_isCompactValued {T : Type*} [TopologicalSpace T] {t₀ : T}
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) {p : T → Coordinate L n k → ComplexMatrix2}
    (hp : ContinuousAt p t₀) (h0 : p t₀ = toCoordinates X)
    (hr : ∀ᶠ r in 𝓝 t₀, ∀ ι, p r ι ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ᶠ r in 𝓝 t₀, IsCompactValued (ofCoordinates (p r)) := by
  have h1 : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)), ∀ᶠ r in 𝓝 t₀,
      meanRadius (levelField (ofCoordinates (p r)) i) c.1 ≠ 0 := by
    intro i c
    set f : (Coordinate L n k → ComplexMatrix2) → ℂ :=
      fun w => meanRadius (levelField (ofCoordinates w) i) c.1 with hf
    have hc : ContinuousAt f (toCoordinates X) :=
      (contDiffAt_meanRadius_coordinates hX i c).continuousAt
    have hc' : ContinuousAt f (p t₀) := by rw [h0]; exact hc
    have hcomp : ContinuousAt (f ∘ p) t₀ := ContinuousAt.comp (f := p) hc' hp
    have hne : (f ∘ p) t₀ ≠ 0 := by
      have e : ofCoordinates (p t₀) = X := by
        rw [h0, ofCoordinates_toCoordinates (hX.2 0 (Nat.zero_le _))]
      change meanRadius (levelField (ofCoordinates (p t₀)) i) c.1 ≠ 0
      rw [e]
      exact meanRadius_ne_zero hX i c
    exact hcomp.eventually_ne hne
  have h2 : ∀ᶠ r in 𝓝 t₀, ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      meanRadius (levelField (ofCoordinates (p r)) i) c.1 ≠ 0 :=
    eventually_all.2 fun i => eventually_all.2 fun c => h1 i c
  filter_upwards [h2, hr] with r h3 h4
  have hb : (ofCoordinates (p r)).fine ∈ fieldSpace L n k 0 :=
    fieldOfPositiveValues_mem_fieldSpace (w := fun b => p r (Sum.inl b))
      (fun c => h4 (Sum.inl c)) (hxor 0 (Nat.zero_le _))
  have hn : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (ofCoordinates (p r)).noise i c ∈ PeriodicLattice.compactGaugeGroup :=
    fun i c => h4 (Sum.inr ⟨i, c⟩)
  exact isCompactValued_of_meanRadius_ne_zero hxor hb hn h3
theorem edgeForm_mem_hermitianTraceless {j : ℕ} (B : edgeFormSpace L n k j) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    (B : Edge L n k j → ComplexMatrix2) b ∈ ComplexMatrix2.hermitianTraceless := B.2.1 b hb
theorem toAlgebraValues_smul_eq (ξ : LevelForms L n k) (r : ℝ) (ι : Coordinate L n k) :
    ∃ A ∈ ComplexMatrix2.hermitianTraceless, (r • toAlgebraValues ξ) ι = Complex.I • A := by
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
theorem toCoordinates_mem_compact {X : ChainPoint L n k} (hX : IsCompactValued X)
    (ι : Coordinate L n k) :
    toCoordinates X ι ∈ PeriodicLattice.compactGaugeGroup := by
  rcases ι with b | p
  · exact (hX.2 0 (Nat.zero_le _)).1 b.1 (Set.mem_univ _)
  · exact hX.1 _ _
end CompactPoints
section Gauged
variable {L n k : ℕ} [NeZero L]
theorem coe_toSublattice {m : ℕ} {i i' : ℤ} (h : i ≤ i') (y : PeriodicLattice.Site L m i) :
    ((y.toSublattice i' : PeriodicLattice.Site L m i') : PeriodicLattice.FourTorus L m) = y :=
  Classical.epsilon_spec (p := fun x : PeriodicLattice.Site L m i' =>
    (x : PeriodicLattice.FourTorus L m) = y)
    ⟨⟨y.1, PeriodicLattice.sublattice_mono (Nat.pos_of_ne_zero (NeZero.ne L)) m h y.2⟩, rfl⟩
theorem restrictVertexFunction_zero (v : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction 0 v = v := by
  funext x
  simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap]
  congr 1
  exact Subtype.ext (coe_toSublattice le_rfl x)
theorem restrictVertexFunction_toSublattice (v : Vertex L n k 0 → ComplexMatrix2) {j : ℕ}
    (hj : j ≤ k) (y : Vertex L n k (j + 1)) :
    restrictVertexFunction j v (y.toSublattice (PeriodicLattice.levelDepth k j)) =
      restrictVertexFunction (j + 1) v y := by
  simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap]
  congr 1
  refine Subtype.ext ?_
  have h1 : PeriodicLattice.levelDepth k (j + 1) ≤ PeriodicLattice.levelDepth k j := by
    simp only [PeriodicLattice.levelDepth]; omega
  have h2 : PeriodicLattice.levelDepth k j ≤ PeriodicLattice.levelDepth k 0 := by
    simp only [PeriodicLattice.levelDepth]; omega
  have e1 := coe_toSublattice h2 (y.toSublattice (PeriodicLattice.levelDepth k j))
  have e2 := coe_toSublattice h1 y
  have e3 := coe_toSublattice (h1.trans h2) y
  exact (e1.trans e2).trans e3.symm
variable (hC : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
theorem mem_fieldsIn_complex {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
  ⟨fun b hb => det_eq_one_of_compact (hV.1 b hb), hV.2⟩
include hC hL hn in
theorem levelField_gaugeTransformPoint {X' : ChainPoint L n k} (hX' : IsCompactValued X')
    {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ j, j ≤ k → levelField (gaugeTransformPoint v X') j =
      PeriodicLattice.gaugeTransform (restrictVertexFunction j v) (levelField X' j) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [restrictVertexFunction_zero]
    rfl
  | succ j ih =>
    intro hj
    have h : j < k := hj
    have hW := hX'.2 j h.le
    have hvj : ∀ i (x : Vertex L n k i),
        restrictVertexFunction i v x ∈ PeriodicLattice.compactGaugeGroup :=
      fun i x => hv _
    have hpos : ∀ b : Edge L n k (j + 1), b.IsPositivelyOriented →
        levelField (gaugeTransformPoint v X') (j + 1) b =
          PeriodicLattice.gaugeTransform (restrictVertexFunction (j + 1) v)
            (levelField X' (j + 1)) b := by
      intro b hb
      have hcov := (hC L hL n k j hn h _ (mem_fieldsIn_complex hW) (restrictVertexFunction j v)
        (fun x => det_eq_one_of_compact (hvj j x)) b hb).2.2
      rw [restrictVertexFunction_toSublattice v h.le,
        restrictVertexFunction_toSublattice v h.le] at hcov
      rw [levelField_succ_of_pos _ h hb, ih h.le, hcov]
      simp only [PeriodicLattice.gaugeTransform]
      rw [levelField_succ_of_pos X' h hb]
      have e : (gaugeTransformPoint v X').noise ⟨j, h⟩ ⟨b, hb⟩ =
          restrictVertexFunction (j + 1) v b.source * X'.noise ⟨j, h⟩ ⟨b, hb⟩ *
            (restrictVertexFunction (j + 1) v b.source)⁻¹ := rfl
      rw [e]
      have hg : (restrictVertexFunction (j + 1) v b.source)⁻¹ *
          restrictVertexFunction (j + 1) v b.source = 1 :=
        Matrix.nonsing_inv_mul _ (isUnit_det_of_compact (hvj _ _))
      calc _ = restrictVertexFunction (j + 1) v b.source * X'.noise ⟨j, h⟩ ⟨b, hb⟩ *
              ((restrictVertexFunction (j + 1) v b.source)⁻¹ *
                restrictVertexFunction (j + 1) v b.source) *
              normalizedMean (levelField X' j) b *
              (restrictVertexFunction (j + 1) v b.target)⁻¹ := by
            simp only [mul_assoc]
        _ = _ := by rw [hg]; simp only [mul_one, mul_assoc]
    funext b
    by_cases hb : b.IsPositivelyOriented
    · exact hpos b hb
    · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      rw [levelField_succ_of_not_pos _ h hb, hpos _ hp]
      simp only [PeriodicLattice.gaugeTransform]
      have e1 : levelField X' (j + 1) b = (levelField X' (j + 1) b.opposite)⁻¹ :=
        levelField_succ_of_not_pos _ h hb
      have e2 : b.opposite.source = b.target := rfl
      have e3 : b.opposite.target = b.source := rfl
      rw [e1, e2, e3, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_compact (hvj _ _))]
      simp only [mul_assoc]
theorem fullTrace_conj {g M : ComplexMatrix2} (hg : IsUnit g.det) :
    ComplexMatrix2.fullTrace (g * M * g⁻¹) = ComplexMatrix2.fullTrace M := by
  simp only [ComplexMatrix2.fullTrace]
  rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ hg, one_mul]
include hC hL hn in
theorem chainAction_gaugeTransformPoint
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (a : ℝ) {X' : ChainPoint L n k} (hX' : IsCompactValued X')
    {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    chainAction a (gaugeTransformPoint v X') = chainAction a X' := by
  have hU : X'.fine ∈ fieldSpace L n k 0 := hX'.2 0 (Nat.zero_le _)
  have hjm : -(n : ℤ) ≤ PeriodicLattice.levelDepth k 0 := by
    simp only [PeriodicLattice.levelDepth]; omega
  have h1 : plaquetteAction L n k (gaugeTransformPoint v X').fine =
      plaquetteAction L n k X'.fine := by
    have e : (gaugeTransformPoint v X').fine = PeriodicLattice.gaugeTransform v X'.fine := rfl
    rw [e]
    simp only [plaquetteAction, PeriodicLattice.wilsonAction]
    refine finsum_congr fun p => ?_
    have := (hg L n hL.1 hL.2 hn (PeriodicLattice.levelDepth k 0) hjm Set.univ X'.fine v v
      (fun b _ => trivial) (mem_fieldsIn_complex hU) (fun x => det_eq_one_of_compact (hv x))
      (fun x => det_eq_one_of_compact (hv x))).2.2 p (fun _ _ => trivial)
    simp only [PeriodicLattice.plaquetteCost]
    rw [this, fullTrace_conj (isUnit_det_of_compact (hv _))]
  have h2 : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (meanRadius (levelField (gaugeTransformPoint v X') i) c.1).re *
          traceDefect ((gaugeTransformPoint v X').noise i c) =
        (meanRadius (levelField X' i) c.1).re * traceDefect (X'.noise i c) := by
    intro i c
    have hW := hX'.2 i i.2.le
    have hl := (hC L hL n k i hn i.2 _ (mem_fieldsIn_complex hW) (restrictVertexFunction i v)
        (fun x => det_eq_one_of_compact (hv _)) c.1 c.2).2.1
    rw [levelField_gaugeTransformPoint hC hL hn hX' hv i i.2.le, hl]
    congr 1
    have e : (gaugeTransformPoint v X').noise i c =
        restrictVertexFunction (i + 1) v c.1.source * X'.noise i c *
          (restrictVertexFunction (i + 1) v c.1.source)⁻¹ := rfl
    rw [e]
    simp only [traceDefect, ComplexMatrix2.halfTrace]
    rw [fullTrace_conj (g := restrictVertexFunction (i + 1) v c.1.source)
      (isUnit_det_of_compact (hv _))]
  have h3 : ∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
      (meanRadius (levelField (gaugeTransformPoint v X') i) c.1).re *
        traceDefect ((gaugeTransformPoint v X').noise i c) =
      ∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
        (meanRadius (levelField X' i) c.1).re * traceDefect (X'.noise i c) :=
    Finset.sum_congr rfl fun i _ => finsum_congr fun c => h2 i c
  unfold chainAction
  rw [h1, h3]
end Gauged
section Forms
variable {L n k j : ℕ}
theorem edgeForm_ext {A B : edgeFormSpace L n k j}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      (A : Edge L n k j → ComplexMatrix2) b = (B : Edge L n k j → ComplexMatrix2) b) :
    A = B := by
  apply Subtype.ext
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact h b hb
  · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
    have e1 : (A : Edge L n k j → ComplexMatrix2) b =
        -(A : Edge L n k j → ComplexMatrix2) b.opposite := A.2.2 b.opposite
    have e2 : (B : Edge L n k j → ComplexMatrix2) b =
        -(B : Edge L n k j → ComplexMatrix2) b.opposite := B.2.2 b.opposite
    rw [e1, e2, h _ hp]
theorem extendOddly_of_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
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
theorem conjugateBy_add (g A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (A + B) =
      ComplexMatrix2.conjugateBy g A + ComplexMatrix2.conjugateBy g B := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (g : ComplexMatrix2) (r : ℝ) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (r • A) = r • ComplexMatrix2.conjugateBy g A := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.conjugateBy_real_smul <;> assumption
end Forms
theorem xor_isPositivelyOriented_opposite
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
  intro j hj b
  have h := (hb ⟨L, hL, 1, ⟨n, hn⟩⟩ (PeriodicLattice.levelDepth k j) (by
    change -(n : ℤ) < PeriodicLattice.levelDepth k j
    simp only [PeriodicLattice.levelDepth]
    omega)).1 b
  exact h.2.2.2.2.2
section Conjugated
variable {L n k : ℕ} [NeZero L]
def conjugateForm {j : ℕ} (u : Vertex L n k j → ComplexMatrix2)
    (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    edgeFormSpace L n k j →ₗ[ℝ] edgeFormSpace L n k j where
  toFun B := ⟨adjointForm u B, extendOddly_mem hx _ fun b hb =>
    conjugateBy_mem_hermitianTraceless (hu _) (edgeForm_mem_hermitianTraceless B hb)⟩
  map_add' B B' := edgeForm_ext fun b hb => by
    change adjointForm u (B + B' : edgeFormSpace L n k j) b =
      adjointForm u B b + adjointForm u B' b
    simp only [adjointForm, extendOddly_of_pos _ hb]
    change ComplexMatrix2.conjugateBy (u b.source)
      ((B : Edge L n k j → ComplexMatrix2) b + (B' : Edge L n k j → ComplexMatrix2) b) = _
    rw [conjugateBy_add]
  map_smul' r B := edgeForm_ext fun b hb => by
    change adjointForm u (r • B : edgeFormSpace L n k j) b = r • adjointForm u B b
    simp only [adjointForm, extendOddly_of_pos _ hb]
    change ComplexMatrix2.conjugateBy (u b.source) (r • (B : Edge L n k j → ComplexMatrix2) b) = _
    rw [conjugateBy_smul]
theorem conjugateForm_of_pos {j : ℕ} (u : Vertex L n k j → ComplexMatrix2)
    (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (B : edgeFormSpace L n k j) {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    (conjugateForm u hu hx B : Edge L n k j → ComplexMatrix2) b =
      ComplexMatrix2.conjugateBy (u b.source) ((B : Edge L n k j → ComplexMatrix2) b) := by
  change adjointForm u B b = _
  simp only [adjointForm, extendOddly_of_pos _ hb]
theorem conjugateBy_inv_conjugateBy {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g⁻¹ (ComplexMatrix2.conjugateBy g A) = A := by
  simp only [ComplexMatrix2.conjugateBy,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_compact hg)]
  have h : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_of_compact hg)
  calc g⁻¹ * (g * A * g⁻¹) * g = (g⁻¹ * g) * A * (g⁻¹ * g) := by simp only [mul_assoc]
    _ = A := by rw [h]; simp
theorem conjugateBy_conjugateBy_inv {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (ComplexMatrix2.conjugateBy g⁻¹ A) = A := by
  simp only [ComplexMatrix2.conjugateBy,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_compact hg)]
  have h : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_of_compact hg)
  calc g * (g⁻¹ * A * g) * g⁻¹ = (g * g⁻¹) * A * (g * g⁻¹) := by simp only [mul_assoc]
    _ = A := by rw [h]; simp
def conjugateFormEquiv {j : ℕ} (u : Vertex L n k j → ComplexMatrix2)
    (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    edgeFormSpace L n k j ≃ₗ[ℝ] edgeFormSpace L n k j :=
  LinearEquiv.ofLinearMap (conjugateForm u hu hx)
    (conjugateForm (fun x => (u x)⁻¹) (fun x => compact_inv_mem (hu x)) hx)
    (LinearMap.ext fun B => edgeForm_ext fun b hb => by
      change (conjugateForm u hu hx
        (conjugateForm (fun x => (u x)⁻¹) (fun x => compact_inv_mem (hu x)) hx B) :
        Edge L n k j → ComplexMatrix2) b = _
      rw [conjugateForm_of_pos _ _ _ _ hb, conjugateForm_of_pos _ _ _ _ hb]
      exact conjugateBy_conjugateBy_inv (hu _) _)
    (LinearMap.ext fun B => edgeForm_ext fun b hb => by
      change (conjugateForm (fun x => (u x)⁻¹) (fun x => compact_inv_mem (hu x)) hx
        (conjugateForm u hu hx B) : Edge L n k j → ComplexMatrix2) b = _
      rw [conjugateForm_of_pos _ _ _ _ hb, conjugateForm_of_pos _ _ _ _ hb]
      exact conjugateBy_inv_conjugateBy (hu _) _)
def conjugateLevelForms (v : Vertex L n k 0 → ComplexMatrix2)
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (hx : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    LevelForms L n k ≃ₗ[ℝ] LevelForms L n k :=
  (conjugateFormEquiv v hv (hx 0 (Nat.zero_le _))).prodCongr
    (LinearEquiv.piCongrRight fun i : Fin k =>
      conjugateFormEquiv (restrictVertexFunction ((i : ℕ) + 1) v) (fun x => hv _) (hx _ i.2))
theorem matExp_I_smul_conjugateBy {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) (A : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • ComplexMatrix2.conjugateBy g A) =
      g * ComplexMatrix2.matExp (Complex.I • A) * g⁻¹ := by
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (isUnit_det_of_compact hg)
  have e : Complex.I • ComplexMatrix2.conjugateBy g A = g * (Complex.I • A) * g⁻¹ := by
    simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  exact Matrix.exp_conj _ _ hu
variable {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
  (hx : ∀ j, j ≤ k → ∀ b : Edge L n k j,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
theorem expMove_conjugate_fine_of_pos (X : ChainPoint L n k) (ξ : LevelForms L n k)
    {b : Edge L n k 0} (hb : b.IsPositivelyOriented) :
    ComplexMatrix2.matExp (Complex.I • (conjugateLevelForms v hv hx ξ).1.1 b) *
        (v b.source * X.fine b * (v b.target)⁻¹) =
      v b.source * (ComplexMatrix2.matExp (Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b) *
        X.fine b) * (v b.target)⁻¹ := by
  have e : (conjugateLevelForms v hv hx ξ).1.1 b =
      ComplexMatrix2.conjugateBy (v b.source) ((ξ.1 : Edge L n k 0 → ComplexMatrix2) b) :=
    conjugateForm_of_pos v hv (hx 0 (Nat.zero_le _)) ξ.1 hb
  rw [e, matExp_I_smul_conjugateBy (hv _)]
  have h : (v b.source)⁻¹ * v b.source = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_det_of_compact (hv _))
  calc _ = v b.source * ComplexMatrix2.matExp (Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b) *
        ((v b.source)⁻¹ * v b.source) * X.fine b * (v b.target)⁻¹ := by simp only [mul_assoc]
    _ = _ := by rw [h]; simp only [mul_one, mul_assoc]
theorem expMove_conjugateLevelForms (X : ChainPoint L n k) (ξ : LevelForms L n k) :
    expMove (conjugateLevelForms v hv hx ξ) (gaugeTransformPoint v X) =
      gaugeTransformPoint v (expMove ξ X) := by
  simp only [expMove, gaugeTransformPoint]
  congr 1
  · funext b
    by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb]
      exact expMove_conjugate_fine_of_pos hv hx X ξ hb
    · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      simp only [PeriodicLattice.expTwist, if_neg hb, if_pos hp]
      have h := expMove_conjugate_fine_of_pos hv hx X ξ hp
      have e1 : b.opposite.source = b.target := rfl
      have e2 : b.opposite.target = b.source := rfl
      rw [e1, e2] at h
      rw [e1, e2, h, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_compact (hv _))]
      simp only [mul_assoc]
  · funext i c
    have e : ((conjugateLevelForms v hv hx ξ).2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
        ComplexMatrix2.conjugateBy (restrictVertexFunction ((i : ℕ) + 1) v c.1.source)
          ((ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1) :=
      conjugateForm_of_pos (restrictVertexFunction ((i : ℕ) + 1) v) (fun x => hv _) (hx _ i.2)
        (ξ.2 i) c.2
    have hg : restrictVertexFunction ((i : ℕ) + 1) v c.1.source ∈
        PeriodicLattice.compactGaugeGroup := hv _
    rw [e, matExp_I_smul_conjugateBy hg]
    have h := Matrix.nonsing_inv_mul _ (isUnit_det_of_compact hg)
    calc _ = restrictVertexFunction ((i : ℕ) + 1) v c.1.source *
          ComplexMatrix2.matExp (Complex.I • (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1) *
          ((restrictVertexFunction ((i : ℕ) + 1) v c.1.source)⁻¹ *
            restrictVertexFunction ((i : ℕ) + 1) v c.1.source) *
          X.noise i c * (restrictVertexFunction ((i : ℕ) + 1) v c.1.source)⁻¹ := by
            simp only [mul_assoc]
      _ = _ := by rw [h]; simp only [mul_one, mul_assoc]
theorem levelField_fibreMove_of_lt (X : ChainPoint L n k) (ξ : LevelForms L n k) :
    ∀ j, j < k → levelField (fibreMove X ξ) j = levelField (expMove ξ X) j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have h : j < k := by omega
    rw [levelField_succ _ h, levelField_succ _ h, ih h]
    congr 1
    funext c
    have hne : ¬ ((⟨j, h⟩ : Fin k) : ℕ) + 1 = k := by
      change ¬ j + 1 = k
      omega
    have e : (fibreMove X ξ).noise ⟨j, h⟩ c = (expMove ξ X).noise ⟨j, h⟩ c := by
      simp only [fibreMove, if_neg hne]
    rw [e]
include hx in
theorem fibreMove_isCompactValued {X : ChainPoint L n k} (hX : IsCompactValued X)
    {ξ : LevelForms L n k} (hM : IsCompactValued (expMove ξ X)) :
    IsCompactValued (fibreMove X ξ) := by
  refine isCompactValued_of_meanRadius_ne_zero hx (hM.2 0 (Nat.zero_le _)) (fun i c => ?_)
    (fun i c => ?_)
  · by_cases hi : (i : ℕ) + 1 = k
    · have e : (fibreMove X ξ).noise i c =
          levelField X (i + 1) c.1 * (normalizedMean (levelField (expMove ξ X) i) c.1)⁻¹ := by
        simp only [fibreMove, if_pos hi]
      rw [e]
      have hn : (expMove ξ X).noise i c ∈ PeriodicLattice.compactGaugeGroup := hM.1 i c
      have hW := (hM.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)
      rw [levelField_succ_of_pos _ i.2 c.2] at hW
      have hu : normalizedMean (levelField (expMove ξ X) i) c.1 ∈
          PeriodicLattice.compactGaugeGroup := by
        have h1 := compact_mul_mem (compact_inv_mem hn) hW
        have h2 : (expMove ξ X).noise ⟨i, i.2⟩ ⟨c.1, c.2⟩ = (expMove ξ X).noise i c := rfl
        rw [h2, ← mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_compact hn), one_mul] at h1
        exact h1
      exact compact_mul_mem ((hX.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)) (compact_inv_mem hu)
    · have e : (fibreMove X ξ).noise i c = (expMove ξ X).noise i c := by
        simp only [fibreMove, if_neg hi]
      rw [e]
      exact hM.1 i c
  · rw [levelField_fibreMove_of_lt X ξ i i.2]
    exact meanRadius_ne_zero hM i c
end Conjugated
section Fibre
variable {L n k : ℕ} [NeZero L]
theorem chainPoint_ext {Y Z : ChainPoint L n k} (h1 : Y.fine = Z.fine)
    (h2 : ∀ i c, Y.noise i c = Z.noise i c) : Y = Z := by
  obtain ⟨U, N⟩ := Y
  obtain ⟨U', N'⟩ := Z
  simp only at h1 h2
  subst h1
  congr 1
  funext i c
  exact h2 i c
theorem fibreMove_conjugate (hC : ContourMeanGaugeCovariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (hv1 : ∀ y : Vertex L n k k, restrictVertexFunction k v y = 1)
    (hx : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) {ξ : LevelForms L n k}
    (hM : IsCompactValued (expMove ξ X)) :
    fibreMove (gaugeTransformPoint v X) (conjugateLevelForms v hv hx ξ) =
      gaugeTransformPoint v (fibreMove X ξ) := by
  have hmt := expMove_conjugateLevelForms hv hx X ξ
  have htop : ∀ j, j = k → ∀ y : Vertex L n k j, restrictVertexFunction j v y = 1 := by
    rintro j rfl
    exact hv1
  refine chainPoint_ext ?_ fun i c => ?_
  · change (expMove (conjugateLevelForms v hv hx ξ) (gaugeTransformPoint v X)).fine = _
    rw [hmt]
    rfl
  · have e2 : (gaugeTransformPoint v (fibreMove X ξ)).noise i c =
        restrictVertexFunction ((i : ℕ) + 1) v c.1.source * (fibreMove X ξ).noise i c *
          (restrictVertexFunction ((i : ℕ) + 1) v c.1.source)⁻¹ := rfl
    by_cases hi : (i : ℕ) + 1 = k
    · have h1 := htop _ hi
      have e1 : (fibreMove (gaugeTransformPoint v X) (conjugateLevelForms v hv hx ξ)).noise i c =
          levelField (gaugeTransformPoint v X) (i + 1) c.1 * (normalizedMean
            (levelField (expMove (conjugateLevelForms v hv hx ξ) (gaugeTransformPoint v X)) i)
              c.1)⁻¹ := by
        simp only [fibreMove, if_pos hi]
      have e3 : (fibreMove X ξ).noise i c =
          levelField X (i + 1) c.1 * (normalizedMean (levelField (expMove ξ X) i) c.1)⁻¹ := by
        simp only [fibreMove, if_pos hi]
      have hg := levelField_gaugeTransformPoint hC hL hn hX hv (i + 1) i.2
      have hgM := levelField_gaugeTransformPoint hC hL hn hM hv i i.2.le
      have hcov := (hC L hL n k i hn i.2 _ (mem_fieldsIn_complex (hM.2 i i.2.le))
        (restrictVertexFunction i v) (fun x => det_eq_one_of_compact (hv _)) c.1 c.2).2.2
      rw [restrictVertexFunction_toSublattice v i.2.le,
        restrictVertexFunction_toSublattice v i.2.le, h1, h1] at hcov
      rw [e1, e2, e3, hmt, hg, hgM, hcov]
      simp only [PeriodicLattice.gaugeTransform, h1]
      simp
    · have e1 : (fibreMove (gaugeTransformPoint v X) (conjugateLevelForms v hv hx ξ)).noise i c =
          (expMove (conjugateLevelForms v hv hx ξ) (gaugeTransformPoint v X)).noise i c := by
        simp only [fibreMove, if_neg hi]
      have e3 : (fibreMove X ξ).noise i c = (expMove ξ X).noise i c := by
        simp only [fibreMove, if_neg hi]
      rw [e1, e2, e3, hmt]
      rfl
end Fibre
theorem fibreActionGaugeInvariant (hC : ContourMeanGaugeCovariant)
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction) :
    FibreActionGaugeInvariant := by
  intro a L hL k n hk hn X hX v hvr hv1
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hx : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    xor_isPositivelyOriented_opposite hb hL hn
  refine ⟨conjugateLevelForms v hvr hx, fun ξ => rfl, fun N e => ?_⟩
  have hc : Continuous fun w : Fin N → ℝ => toAlgebraValues (e w) :=
    ((toAlgebraValues : LevelForms L n k →ₗ[ℝ] (Coordinate L n k → ComplexMatrix2)) ∘ₗ
      e).continuous_of_finiteDimensional
  have hch : ContinuousAt (expChart (toCoordinates X))
      (toAlgebraValues (e (0 : Fin N → ℝ))) := by
    rw [map_zero, map_zero]
    exact (contDiffAt_expChart (toCoordinates X) 0).continuousAt
  have hp : ContinuousAt
      (fun w : Fin N → ℝ => expChart (toCoordinates X) (toAlgebraValues (e w))) 0 :=
    ContinuousAt.comp (g := expChart (toCoordinates X))
      (f := fun w : Fin N → ℝ => toAlgebraValues (e w)) hch hc.continuousAt
  have hreal := eventually_isCompactValued hx hX hp (by simp [expChart_zero])
    (Eventually.of_forall fun w ι => by
      obtain ⟨A, hA, h⟩ := toAlgebraValues_smul_eq (e w) 1 ι
      rw [one_smul] at h
      rw [expChart_apply, h]
      exact compact_mul_mem (matExp_I_smul_mem_compact hA) (toCoordinates_mem_compact hX ι))
  filter_upwards [hreal] with w hw
  rw [ofCoordinates_expChart (hX.2 0 (Nat.zero_le _))] at hw
  rw [fibreMove_conjugate hC hL hn hvr hv1 hx hX hw]
  exact chainAction_gaugeTransformPoint hC hL hn hg a (fibreMove_isCompactValued hx hX hw) hvr
end YangMills.Construction.RunningCouplingSlope.FibreActionProof
end
