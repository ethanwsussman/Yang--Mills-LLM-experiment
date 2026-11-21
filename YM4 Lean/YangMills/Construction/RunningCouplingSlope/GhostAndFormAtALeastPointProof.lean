import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreUnderAGaugeFunctionProof
import YangMills.Construction.RunningCouplingSlope.FunctionOfTheWholeChainProof
import YangMills.Construction.RunningCouplingSlope.LeastPointsAreGaugeImagesOfSmallTangentsProof
import YangMills.Construction.RunningCouplingSlope.LeastPointsOverAFieldAreOneOrbitProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.GhostQuadraticProof
open Filter Tower Matrices
open scoped Topology
section SecondDerivatives
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
theorem hasDerivAt_deriv_comp_two {Φ : E → F} {x : E} (hΦ : ContDiffAt ℝ 2 Φ x) {g : ℝ → ℝ → E}
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
end SecondDerivatives
section LeftChart
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
def leftChart (x a : A) : A := NormedSpace.exp a * x
theorem contDiffAt_exp_two (a : A) : ContDiffAt ℝ 2 (NormedSpace.exp : A → A) a :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) a).contDiffAt
theorem contDiffAt_leftChart (x a : A) : ContDiffAt ℝ 2 (leftChart x) a :=
  (contDiffAt_exp_two a).mul contDiffAt_const
theorem leftChart_zero (x : A) : leftChart x 0 = x := by simp [leftChart]
variable {Φ : A → ℝ} {x : A}
def inLeftChart (Φ : A → ℝ) (x a : A) : ℝ := Φ (leftChart x a)
theorem contDiffAt_inLeftChart (hΦ : ContDiffAt ℝ 2 Φ x) :
    ContDiffAt ℝ 2 (inLeftChart Φ x) 0 := by
  have h : ContDiffAt ℝ 2 Φ (leftChart x 0) := by simpa [leftChart_zero] using hΦ
  exact h.comp 0 (contDiffAt_leftChart x 0)
end LeftChart
section SmoothMatrixMaps
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
theorem contDiffAt_inv {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀)
    (hu : IsUnit (f y₀).det) : ContDiffAt ℝ 2 (fun y => (f y)⁻¹) y₀ := by apply _root_.YangMills.SharedProofs.p22704 <;> assumption
end SmoothMatrixMaps
section QuaternionSpan
variable {L n k j : ℕ}
theorem compact_inv_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem compact_det {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem compact_isUnit_det {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem pathHolonomy_mem_compact {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy V Γ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p6330 <;> assumption
end QuaternionSpan
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
end PositiveValues
section Levels
variable {L n k : ℕ}
theorem levelField_succ_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k) {b : Edge L n k (j + 1)}
    (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
theorem levelField_succ_neg (X : ChainPoint L n k) {j : ℕ} (h : j < k) {b : Edge L n k (j + 1)}
    (hb : ¬b.IsPositivelyOriented) :
    levelField X (j + 1) b = (levelField X (j + 1) b.opposite)⁻¹ := by apply _root_.YangMills.SharedProofs.p5483 <;> assumption
end Levels
section Families
variable {L n k : ℕ} [NeZero L] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
  {Z : Y → ChainPoint L n k}
theorem isUnit_det_of_mem {j : ℕ} {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j)
    (b : Edge L n k j) :
    IsUnit (V b).det := compact_isUnit_det (hV.1 b (Set.mem_univ b))
theorem contDiffAt_levelField (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀)) :
    ∀ j, j ≤ k → ∀ b, ContDiffAt ℝ 2 (fun y => levelField (Z y) j b) y₀ := by apply _root_.YangMills.SharedProofs.p4722 <;> assumption
theorem finite_face (j : ℕ) : Finite (Face L n k j) := by apply _root_.YangMills.SharedProofs.p23234 <;> assumption
theorem contDiffAt_chainAction (a : ℝ) (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀)) :
    ContDiffAt ℝ 2 (fun y => chainAction a (Z y)) y₀ := by apply _root_.YangMills.SharedProofs.p6648 <;> assumption
end Families
section ValueCoordinates
variable {L n k : ℕ}
abbrev ChainIndex (L n k : ℕ) : Type :=
  PositiveEdge L n k 0 ⊕ (Σ i : Fin k, PositiveEdge L n k (i + 1))
instance [NeZero L] : Fintype (ChainIndex L n k) := Fintype.ofFinite _
def ofValues (w : ChainIndex L n k → ComplexMatrix2) : ChainPoint L n k :=
  ⟨fieldOfPositiveValues fun b => w (Sum.inl b), fun i c => w (Sum.inr ⟨i, c⟩)⟩
def toValues (X : ChainPoint L n k) : ChainIndex L n k → ComplexMatrix2 :=
  Sum.elim (fun b => X.fine b.1) fun p => X.noise p.1 p.2
theorem ofValues_toValues {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0) :
    ofValues (toValues X) = X := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.ofCoordinates_toCoordinates <;> assumption
variable [NeZero L]
theorem contDiffAt_ofValues_fine {x : ChainIndex L n k → ComplexMatrix2}
    (hx : ∀ b, IsUnit (x (Sum.inl b)).det)
    (b : Edge L n k 0) : ContDiffAt ℝ 2 (fun w => (ofValues w).fine b) x := by
  have hc : ∀ ι : ChainIndex L n k,
      ContDiffAt ℝ 2 (fun w : ChainIndex L n k → ComplexMatrix2 => w ι) x := fun ι =>
    (contDiff_apply ℝ ComplexMatrix2 ι).contDiffAt
  by_cases h : b.IsPositivelyOriented
  · simp only [ofValues, fieldOfPositiveValues_pos _ h]
    exact hc _
  · simp only [ofValues, fieldOfPositiveValues_neg _ h]
    exact contDiffAt_inv (hc _) (hx _)
theorem contDiffAt_ofValues_noise {x : ChainIndex L n k → ComplexMatrix2} (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun w => (ofValues w).noise i c) x :=
  (contDiff_apply ℝ ComplexMatrix2 (Sum.inr ⟨i, c⟩ : ChainIndex L n k)).contDiffAt
theorem isUnit_det_toValues {X : ChainPoint L n k} (hX : IsCompactValued X)
    (b : PositiveEdge L n k 0) : IsUnit (toValues X (Sum.inl b)).det := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.isUnit_det_toCoordinates <;> assumption
theorem contDiffAt_level_ofValues {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ}
    (hj : j ≤ k) (b : Edge L n k j) :
    ContDiffAt ℝ 2 (fun w => levelField (ofValues w) j b) (toValues X) := by
  have h0 : ofValues (toValues X) = X := ofValues_toValues (hX.2 0 (Nat.zero_le _))
  exact contDiffAt_levelField (Z := ofValues) (y₀ := toValues X)
    (contDiffAt_ofValues_fine (isUnit_det_toValues hX))
    (fun i c => contDiffAt_ofValues_noise i c) (by rwa [h0]) j hj b
theorem contDiffAt_chainAction_ofValues {X : ChainPoint L n k} (hX : IsCompactValued X) (a : ℝ) :
    ContDiffAt ℝ 2 (fun w => chainAction a (ofValues w)) (toValues X) := by
  have h0 : ofValues (toValues X) = X := ofValues_toValues (hX.2 0 (Nat.zero_le _))
  exact contDiffAt_chainAction (Z := ofValues) (y₀ := toValues X) a
    (contDiffAt_ofValues_fine (isUnit_det_toValues hX))
    (fun i c => contDiffAt_ofValues_noise i c) (by rwa [h0])
end ValueCoordinates
section Tangents
theorem exp_pi_apply {ι : Type*} [Fintype ι] (x : ι → ComplexMatrix2) (i : ι) :
    NormedSpace.exp x i = ComplexMatrix2.matExp (x i) := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.normedExp_pi_apply <;> assumption
variable {L n k : ℕ} [NeZero L]
instance {j : ℕ} : Fintype (Edge L n k j) := Fintype.ofFinite _
def imagEmbed : LevelForms L n k →ₗ[ℝ] (ChainIndex L n k → ComplexMatrix2) where
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
theorem ofValues_leftChart {X : ChainPoint L n k} (hX : X.fine ∈ fieldSpace L n k 0)
    (ξ : LevelForms L n k) : ofValues (leftChart (toValues X) (imagEmbed ξ)) = expMove ξ X := by
  simp only [ofValues, expMove]
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
def chainActionOnValues (a : ℝ) (w : ChainIndex L n k → ComplexMatrix2) : ℝ :=
  chainAction a (ofValues w)
theorem leftSecondDeriv_eq {X : ChainPoint L n k} (hX : IsCompactValued X) (a : ℝ)
    (ξ ξ' : LevelForms L n k) :
    leftSecondDeriv (chainAction a) X ξ ξ' =
      fderiv ℝ (fderiv ℝ (inLeftChart (chainActionOnValues a) (toValues X))) 0
        (imagEmbed ξ) (imagEmbed ξ') := by
  have h := hasDerivAt_deriv_line
    (contDiffAt_inLeftChart (contDiffAt_chainAction_ofValues hX a)) (imagEmbed ξ) (imagEmbed ξ')
  have e : (fun s : ℝ => deriv (fun t : ℝ => chainAction a (expMove (s • ξ + t • ξ') X)) 0) =
      fun s : ℝ => deriv (fun t : ℝ =>
        inLeftChart (chainActionOnValues a) (toValues X) (s • imagEmbed ξ + t • imagEmbed ξ')) 0 := by
    funext s
    congr 1
    funext t
    rw [← ofValues_leftChart (hX.2 0 (Nat.zero_le _)), map_add, map_smul, map_smul]
    rfl
  rw [leftSecondDeriv, e]
  exact h.deriv
end Tangents
section GaugeTransformed
variable {L n k : ℕ} [NeZero L]
theorem restrictVertexFunction_zero (v : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction 0 v = v := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.restrictVertexFunction_zero <;> assumption
theorem restrictVertexFunction_toSublattice (v : Vertex L n k 0 → ComplexMatrix2) {j : ℕ}
    (hj : j ≤ k) (y : Vertex L n k (j + 1)) :
    restrictVertexFunction j v (y.toSublattice (PeriodicLattice.levelDepth k j)) =
      restrictVertexFunction (j + 1) v y := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.restrictVertexFunction_toSublattice <;> assumption
variable (hC : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
theorem mem_fieldsIn_complex {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
  ⟨fun b hb => compact_det (hV.1 b hb), hV.2⟩
include hC hL hn in
theorem levelField_gaugeTransformPoint {X' : ChainPoint L n k} (hX' : IsCompactValued X')
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ j, j ≤ k → levelField (gaugeTransformPoint v X') j =
      PeriodicLattice.gaugeTransform (restrictVertexFunction j v) (levelField X' j) := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.levelField_gaugeTransformPoint <;> assumption
include hC hL hn in
theorem chainAction_gaugeTransformPoint (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (a : ℝ) {X' : ChainPoint L n k} (hX' : IsCompactValued X') {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    chainAction a (gaugeTransformPoint v X') = chainAction a X' := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.chainAction_gaugeTransformPoint <;> assumption
end GaugeTransformed
section GaugeTransformedMore
variable {L n k : ℕ} [NeZero L]
theorem gaugeTransformPoint_compact (hC : ContourMeanGaugeCovariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    IsCompactValued (gaugeTransformPoint v X) := by apply _root_.YangMills.SharedProofs.p17448 <;> assumption
theorem gaugeTransformPoint_inv {X : ChainPoint L n k} {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    gaugeTransformPoint (fun x => (v x)⁻¹) (gaugeTransformPoint v X) = X := by apply _root_.YangMills.SharedProofs.p6932 <;> assumption
end GaugeTransformedMore
theorem exists_radius_of_nearIdentity {ι : Type*} [Finite ι] {D : Set (ι → ComplexMatrix2)}
    {P : (ι → ComplexMatrix2) → Prop}
    (h : EventuallyNearIdentity D P) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ V ∈ D, (∀ b, ‖V b - 1‖ < δ) → P V := by apply _root_.YangMills.SharedProofs.p388 <;> assumption
section OddExtension
variable {L n k j : ℕ}
theorem extendOddly_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
theorem extendOddly_neg (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : ¬b.IsPositivelyOriented) : extendOddly f b = -f b.opposite := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_not_pos <;> assumption
theorem extendOddly_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Edge L n k j → ComplexMatrix2)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace L n k j := by apply _root_.YangMills.SharedProofs.p1442 <;> assumption
end OddExtension
section QuadraticFunctions
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
def IsQuadratic (F : E → ℝ) : Prop := ∃ q : QuadraticForm ℝ E, ∀ ξ, q ξ = F ξ
theorem IsQuadratic.add {F G : E → ℝ} (hF : IsQuadratic F) (hG : IsQuadratic G) :
    IsQuadratic fun ξ => F ξ + G ξ := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  exact ⟨p + q, fun ξ => by simp [hp, hq]⟩
theorem IsQuadratic.sub {F G : E → ℝ} (hF : IsQuadratic F) (hG : IsQuadratic G) :
    IsQuadratic fun ξ => F ξ - G ξ := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq⟩ := hG
  exact ⟨p - q, fun ξ => by simp [hp, hq]⟩
theorem IsQuadratic.const_mul {F : E → ℝ} (c : ℝ) (hF : IsQuadratic F) :
    IsQuadratic fun ξ => c * F ξ := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨c • p, fun ξ => by simp [hp]⟩
theorem IsQuadratic.congr {F G : E → ℝ} (hF : IsQuadratic F) (e : ∀ ξ, F ξ = G ξ) :
    IsQuadratic G := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨p, fun ξ => by rw [hp, e]⟩
theorem isQuadratic_of_bilinear (f : E → E → ℝ)
    (h1 : ∀ x x' y, f (x + x') y = f x y + f x' y) (h2 : ∀ (r : ℝ) x y, f (r • x) y = r * f x y)
    (h3 : ∀ x y y', f x (y + y') = f x y + f x y') (h4 : ∀ (r : ℝ) x y, f x (r • y) = r * f x y) :
    IsQuadratic fun x => f x x :=
  ⟨LinearMap.BilinMap.toQuadraticMap (LinearMap.mk₂ ℝ f h1 (by simpa using h2) h3
    (by simpa using h4)), fun x => by simp⟩
end QuadraticFunctions
section Pairings
theorem traceFinsumPairing_add_right {ι : Type*} [Fintype ι] (f g g' : ι → ComplexMatrix2) :
    traceFinsumPairing f (g + g') = traceFinsumPairing f g + traceFinsumPairing f g' := by
  simp only [traceFinsumPairing, finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, mul_add, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_add]
theorem re_traceFinsumPairing_smul_right {ι : Type*} [Fintype ι] (r : ℝ)
    (f g : ι → ComplexMatrix2) :
    (traceFinsumPairing f (r • g)).re = r * (traceFinsumPairing f g).re := by
  have e : traceFinsumPairing f (r • g) = (r : ℂ) * traceFinsumPairing f g := by
    simp only [traceFinsumPairing, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, mul_smul_comm,
      Matrix.trace_smul]
    rw [Complex.real_smul]
  rw [e, Complex.re_ofReal_mul]
variable {L n k j : ℕ} [NeZero L]
instance {j : ℕ} : Fintype (PositiveEdge L n k j) := Fintype.ofFinite _
theorem edgeFormPairing_add_right (f g g' : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing f (g + g') = edgeFormPairing f g + edgeFormPairing f g' :=
  traceFinsumPairing_add_right _ _ _
theorem edgeFormPairing_smul_right (r : ℝ) (f g : Edge L n k j → ComplexMatrix2) :
    (edgeFormPairing f (r • g)).re = r * (edgeFormPairing f g).re :=
  re_traceFinsumPairing_smul_right r _ _
theorem levelPairing_add_right (x y y' : LevelValues L n k) :
    levelPairing x (y + y') = levelPairing x y + levelPairing x y' := by
  simp only [levelPairing, Prod.fst_add, Prod.snd_add, Pi.add_apply, edgeFormPairing_add_right,
    Complex.add_re, Finset.sum_add_distrib]
  ring
theorem levelPairing_smul_right (r : ℝ) (x y : LevelValues L n k) :
    levelPairing x (r • y) = r * levelPairing x y := by
  simp only [levelPairing, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, edgeFormPairing_smul_right,
    mul_add, Finset.mul_sum]
theorem extendOddly_add (f g : Edge L n k j → ComplexMatrix2) :
    extendOddly (f + g) = extendOddly f + extendOddly g := by
  funext b
  by_cases h : b.IsPositivelyOriented
  · simp [extendOddly, h]
  · simp [extendOddly, h, add_comm]
theorem extendOddly_smul (r : ℝ) (f : Edge L n k j → ComplexMatrix2) :
    extendOddly (r • f) = r • extendOddly f := by
  funext b
  by_cases h : b.IsPositivelyOriented
  · simp [extendOddly, h]
  · simp [extendOddly, h]
def halfBracket (A B : ComplexMatrix2) : ComplexMatrix2 := (Complex.I / 2) • ⁅A, B⁆
theorem halfBracket_add_left (A A' B : ComplexMatrix2) :
    halfBracket (A + A') B = halfBracket A B + halfBracket A' B := by
  simp only [halfBracket, Ring.lie_def, add_mul, mul_add]
  rw [← smul_add]
  congr 1
  abel
theorem halfBracket_add_right (A B B' : ComplexMatrix2) :
    halfBracket A (B + B') = halfBracket A B + halfBracket A B' := by
  simp only [halfBracket, Ring.lie_def, add_mul, mul_add]
  rw [← smul_add]
  congr 1
  abel
theorem halfBracket_smul_left (r : ℝ) (A B : ComplexMatrix2) :
    halfBracket (r • A) B = r • halfBracket A B := by
  simp only [halfBracket, Ring.lie_def, smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [smul_comm]
theorem halfBracket_smul_right (r : ℝ) (A B : ComplexMatrix2) :
    halfBracket A (r • B) = r • halfBracket A B := by
  simp only [halfBracket, Ring.lie_def, smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [smul_comm]
theorem conjugateBy_add (g A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (A + B) =
      ComplexMatrix2.conjugateBy g A + ComplexMatrix2.conjugateBy g B := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (g : ComplexMatrix2) (r : ℝ) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (r • A) = r • ComplexMatrix2.conjugateBy g A := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.conjugateBy_real_smul <;> assumption
theorem chainBracket_eq (X : ChainPoint L n k) (l : Vertex L n k 0 → ComplexMatrix2)
    (y : LevelValues L n k) :
    chainBracket X l y = (extendOddly fun b =>
        halfBracket (l b.source + ComplexMatrix2.conjugateBy (X.fine b) (l b.target)) (y.1 b),
      fun i : Fin k => extendOddly fun c =>
        open Classical in
          if hc : c.IsPositivelyOriented then
            halfBracket (restrictVertexFunction ((i : ℕ) + 1) l c.source +
              ComplexMatrix2.conjugateBy (X.noise i ⟨c, hc⟩)
                (restrictVertexFunction ((i : ℕ) + 1) l c.source)) (y.2 i c)
          else 0) := rfl
theorem restrictVertexFunction_add {i : ℕ} (l l' : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction i (l + l') = restrictVertexFunction i l + restrictVertexFunction i l' :=
  rfl
theorem restrictVertexFunction_smul {i : ℕ} (r : ℝ) (l : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction i (r • l) = r • restrictVertexFunction i l := rfl
theorem chainBracket_add_left (X : ChainPoint L n k) (l l' : Vertex L n k 0 → ComplexMatrix2)
    (y : LevelValues L n k) :
    chainBracket X (l + l') y = chainBracket X l y + chainBracket X l' y := by
  simp only [chainBracket_eq]
  refine Prod.ext ?_ (funext fun i => ?_)
  · simp only [Prod.fst_add]
    rw [← extendOddly_add]
    congr 1
    funext b
    simp only [Pi.add_apply, conjugateBy_add, ← halfBracket_add_left]
    congr 1
    abel
  · simp only [Prod.snd_add, Pi.add_apply]
    rw [← extendOddly_add]
    congr 1
    funext c
    simp only [Pi.add_apply]
    split_ifs with hc
    · rw [restrictVertexFunction_add, ← halfBracket_add_left]
      simp only [Pi.add_apply, conjugateBy_add]
      congr 1
      abel
    · simp
theorem chainBracket_smul_left (X : ChainPoint L n k) (r : ℝ) (l : Vertex L n k 0 → ComplexMatrix2)
    (y : LevelValues L n k) :
    chainBracket X (r • l) y = r • chainBracket X l y := by
  simp only [chainBracket_eq]
  refine Prod.ext ?_ (funext fun i => ?_)
  · simp only [Prod.smul_fst]
    rw [← extendOddly_smul]
    congr 1
    funext b
    simp only [Pi.smul_apply, conjugateBy_smul, ← halfBracket_smul_left, smul_add]
  · simp only [Prod.smul_snd, Pi.smul_apply]
    rw [← extendOddly_smul]
    congr 1
    funext c
    simp only [Pi.smul_apply]
    split_ifs with hc
    · rw [restrictVertexFunction_smul, ← halfBracket_smul_left]
      simp only [Pi.smul_apply, conjugateBy_smul, smul_add]
    · simp
theorem chainBracket_add_right (X : ChainPoint L n k) (l : Vertex L n k 0 → ComplexMatrix2)
    (y y' : LevelValues L n k) :
    chainBracket X l (y + y') = chainBracket X l y + chainBracket X l y' := by
  simp only [chainBracket_eq]
  refine Prod.ext ?_ (funext fun i => ?_)
  · simp only [Prod.fst_add]
    rw [← extendOddly_add]
    congr 1
    funext b
    simp only [Pi.add_apply, halfBracket_add_right]
  · simp only [Prod.snd_add, Pi.add_apply]
    rw [← extendOddly_add]
    congr 1
    funext c
    simp only [Pi.add_apply]
    split_ifs with hc
    · rw [halfBracket_add_right]
    · simp
theorem chainBracket_smul_right (X : ChainPoint L n k) (r : ℝ) (l : Vertex L n k 0 → ComplexMatrix2)
    (y : LevelValues L n k) :
    chainBracket X l (r • y) = r • chainBracket X l y := by
  simp only [chainBracket_eq]
  refine Prod.ext ?_ (funext fun i => ?_)
  · simp only [Prod.smul_fst]
    rw [← extendOddly_smul]
    congr 1
    funext b
    simp only [Pi.smul_apply, halfBracket_smul_right]
  · simp only [Prod.smul_snd, Pi.smul_apply]
    rw [← extendOddly_smul]
    congr 1
    funext c
    simp only [Pi.smul_apply]
    split_ifs with hc
    · rw [halfBracket_smul_right]
    · simp
end Pairings
section RightSide
variable {L n k : ℕ} [NeZero L]
theorem formValues_injective :
    Function.Injective (formValues (L := L) (m := n) (k := k)) := by
  intro ξ ξ' h
  have h₁ : (ξ.1 : Edge L n k 0 → ComplexMatrix2) = ξ'.1 := congrArg Prod.fst h
  have h₂ : ∀ i : Fin k, (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) = ξ'.2 i := fun i =>
    congrFun (congrArg Prod.snd h) i
  exact Prod.ext (Subtype.ext h₁) (funext fun i => Subtype.ext (h₂ i))
theorem formValues_add (ξ ξ' : LevelForms L n k) :
    formValues (ξ + ξ') = formValues ξ + formValues ξ' :=
  rfl
theorem formValues_smul (r : ℝ) (ξ : LevelForms L n k) : formValues (r • ξ) = r • formValues ξ :=
  rfl
def topLogInChart (X : ChainPoint L n k) (c : PositiveEdge L n k k)
    (a : ChainIndex L n k → ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries
    (levelField (ofValues (leftChart (toValues X) a)) k c.1 * (levelField X k c.1)⁻¹)
theorem contDiffAt_topLogInChart (hlog : PeriodicLattice.LogSeriesNearOne) {X : ChainPoint L n k}
    (hX : IsCompactValued X) (c : PositiveEdge L n k k) :
    ContDiffAt ℝ 2 (topLogInChart X c) 0 := by
  have h0 : ofValues (toValues X) = X := ofValues_toValues (hX.2 0 (Nat.zero_le _))
  have h1 : ContDiffAt ℝ 2 (fun w => levelField (ofValues w) k c.1) (leftChart (toValues X) 0) := by
    rw [leftChart_zero]
    exact contDiffAt_level_ofValues hX le_rfl c.1
  have h2 : ContDiffAt ℝ 2 (fun a => levelField (ofValues (leftChart (toValues X) a)) k c.1) 0 :=
    h1.comp 0 (contDiffAt_leftChart (toValues X) 0)
  have h3 : ContDiffAt ℝ 2
      (fun a => levelField (ofValues (leftChart (toValues X) a)) k c.1 * (levelField X k c.1)⁻¹) 0 :=
    h2.mul contDiffAt_const
  have hone : levelField (ofValues (leftChart (toValues X) 0)) k c.1 * (levelField X k c.1)⁻¹ = 1 := by
    rw [leftChart_zero, h0]
    exact Matrix.mul_nonsing_inv _ (isUnit_det_of_mem (hX.2 k le_rfl) c.1)
  have hmem : (1 : ComplexMatrix2) ∈ ComplexMatrix2.logBall := by simp [ComplexMatrix2.logBall]
  have hΦ0 : ContDiffAt ℝ 2 ComplexMatrix2.logSeries 1 :=
    ((hlog.1 1 hmem).contDiffAt (n := 2)).restrict_scalars ℝ
  have hΦ : ContDiffAt ℝ 2 ComplexMatrix2.logSeries
      (levelField (ofValues (leftChart (toValues X) 0)) k c.1 * (levelField X k c.1)⁻¹) := by
    rw [hone]
    exact hΦ0
  exact ContDiffAt.const_smul _ (ContDiffAt.comp (g := ComplexMatrix2.logSeries) 0 hΦ h3)
theorem topSecondVariation_eq (hlog : PeriodicLattice.LogSeriesNearOne)
    {X : ChainPoint L n k} (hX : IsCompactValued X) (ξ ξ' : LevelForms L n k)
    (c : PositiveEdge L n k k) :
    topSecondVariation X ξ ξ' c =
      fderiv ℝ (fderiv ℝ (topLogInChart X c)) 0 (imagEmbed ξ) (imagEmbed ξ') := by
  have h := hasDerivAt_deriv_line (contDiffAt_topLogInChart hlog hX c) (imagEmbed ξ) (imagEmbed ξ')
  have e : (fun s : ℝ => deriv (fun t : ℝ => topLog X (s • ξ + t • ξ') c) 0) =
      fun s : ℝ => deriv (fun t : ℝ => topLogInChart X c (s • imagEmbed ξ + t • imagEmbed ξ')) 0 := by
    funext s
    congr 1
    funext t
    unfold topLog topLogInChart
    rw [← ofValues_leftChart (hX.2 0 (Nat.zero_le _)), map_add, map_smul, map_smul]
  unfold topSecondVariation
  rw [e]
  exact h.deriv
theorem gaugedRightValue_isQuadratic (hlog : PeriodicLattice.LogSeriesNearOne)
    (hS : VertexFunctionsEuclidean L n k 0) {a : ℝ} {X : ChainPoint L n k} (hX : IsCompactValued X)
    (hm : ChainLinearMapsAt X) (J : LevelForms L n k) (μ : edgeFormSpace L n k k) :
    IsQuadratic (gaugedRightValue a X J μ) := by
  set σ : LevelForms L n k →ₗ[ℝ] vertexFunctionSpace L n k 0 :=
    extendFromTopLinear L n k ∘ₗ chainDriftMap X with hσd
  have hσ : ∀ ξ, (σ ξ : Vertex L n k 0 → ComplexMatrix2) = gaugeCorrection X ξ := fun ξ => by
    simp only [hσd, LinearMap.comp_apply]
    rw [hm.extend_apply, hm.drift_spec ξ]
    rfl
  have hgc : IsGaugeTransform X (LinearMap.id + gaugeOrbitMap X ∘ₗ σ) := fun ξ => by
    have h2 := hm.orbit_spec (σ ξ)
    rw [hσ] at h2
    rw [← h2]
    rfl
  let G : vertexFunctionSpace L n k 0 → LevelValues L n k → ℝ := fun l y =>
    levelPairing (formValues J) (chainBracket X (l : Vertex L n k 0 → ComplexMatrix2) y)
  have G1 : ∀ l l' y, G (l + l') y = G l y + G l' y := fun l l' y => by
    simp only [G]
    rw [Submodule.coe_add, chainBracket_add_left, levelPairing_add_right]
  have G2 : ∀ (r : ℝ) l y, G (r • l) y = r * G l y := fun r l y => by
    simp only [G]
    rw [Submodule.coe_smul, chainBracket_smul_left, levelPairing_smul_right]
  have G3 : ∀ l y y', G l (y + y') = G l y + G l y' := fun l y y' => by
    simp only [G]
    rw [chainBracket_add_right, levelPairing_add_right]
  have G4 : ∀ (r : ℝ) l y, G l (r • y) = r * G l y := fun r l y => by
    simp only [G]
    rw [chainBracket_smul_right, levelPairing_smul_right]
  have Q1 : IsQuadratic fun ξ : LevelForms L n k => leftSecondDeriv (chainAction a) X ξ ξ :=
    isQuadratic_of_bilinear (fun ξ ξ' => leftSecondDeriv (chainAction a) X ξ ξ')
      (fun x x' y => by
        simp only [leftSecondDeriv_eq hX, map_add, ContinuousLinearMap.add_apply])
      (fun r x y => by
        simp only [leftSecondDeriv_eq hX, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul])
      (fun x y y' => by simp only [leftSecondDeriv_eq hX, map_add])
      (fun r x y => by simp only [leftSecondDeriv_eq hX, map_smul, smul_eq_mul])
  have Q2 : IsQuadratic fun ξ : LevelForms L n k => G (σ ξ) (formValues ξ) :=
    isQuadratic_of_bilinear (fun ξ ξ' => G (σ ξ) (formValues ξ'))
      (fun x x' y => by simp only [map_add, G1])
      (fun r x y => by simp only [map_smul, G2])
      (fun x y y' => by simp only [formValues_add, G3])
      (fun r x y => by simp only [formValues_smul, G4])
  have Q3 : IsQuadratic fun ξ : LevelForms L n k => G (σ ξ) (formValues (gaugeOrbitMap X (σ ξ))) :=
    isQuadratic_of_bilinear (fun ξ ξ' => G (σ ξ) (formValues (gaugeOrbitMap X (σ ξ'))))
      (fun x x' y => by simp only [map_add, G1])
      (fun r x y => by simp only [map_smul, G2])
      (fun x y y' => by simp only [map_add, formValues_add, G3])
      (fun r x y => by simp only [map_smul, formValues_smul, G4])
  let H : (ChainIndex L n k → ComplexMatrix2) → (ChainIndex L n k → ComplexMatrix2) → ℝ :=
    fun x y =>
    ∑ c : PositiveEdge L n k k,
      (ComplexMatrix2.halfTrace ((μ : Edge L n k k → ComplexMatrix2) c.1 *
        fderiv ℝ (fderiv ℝ (topLogInChart X c)) 0 x y)).re
  have trA : ∀ A B C : ComplexMatrix2, (ComplexMatrix2.halfTrace (A * (B + C))).re =
      (ComplexMatrix2.halfTrace (A * B)).re + (ComplexMatrix2.halfTrace (A * C)).re :=
    fun A B C => by
    simp only [mul_add, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_add,
      Complex.add_re, mul_add]
  have trS : ∀ (r : ℝ) (A B : ComplexMatrix2), (ComplexMatrix2.halfTrace (A * (r • B))).re =
      r * (ComplexMatrix2.halfTrace (A * B)).re := fun r A B => by
    have := re_traceFinsumPairing_smul_right (ι := Unit) r (fun _ => A) (fun _ => B)
    simpa [traceFinsumPairing, finsum_eq_sum_of_fintype] using this
  have Q4 : IsQuadratic fun ξ : LevelForms L n k =>
      (traceFinsumPairing (restrictToPositiveEdges (μ : Edge L n k k → ComplexMatrix2))
        (topSecondVariation X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ) (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ))).re := by
    have h := isQuadratic_of_bilinear (fun ξ ξ' : LevelForms L n k =>
        H (imagEmbed (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ)) (imagEmbed (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ')))
      (fun x x' y => by
        simp only [H, map_add, ContinuousLinearMap.add_apply, trA, Finset.sum_add_distrib])
      (fun r x y => by
        simp only [H, map_smul, ContinuousLinearMap.smul_apply, trS, Finset.mul_sum])
      (fun x y y' => by simp only [H, map_add, trA, Finset.sum_add_distrib])
      (fun r x y => by simp only [H, map_smul, trS, Finset.mul_sum])
    refine h.congr fun ξ => ?_
    simp only [H, traceFinsumPairing, finsum_eq_sum_of_fintype, Complex.re_sum,
      restrictToPositiveEdges]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [topSecondVariation_eq hlog hX]
  obtain ⟨hSf, cG, iG⟩ := hS
  haveI := hSf
  have Q5 : IsQuadratic fun ξ : LevelForms L n k =>
      traceFinsumNorm (gaugeSliceResidual X.fine ξ.1 : Vertex L n k 0 → ComplexMatrix2) ^ 2 := by
    let Lm : LevelForms L n k →ₗ[ℝ] vertexFunctionSpace L n k 0 :=
      (covDiffRealTranspose L n k X.fine -
        ((L : ℝ) ^ (4 * k)) • (iterAverageRealTranspose L n k X.fine ∘ₗ
          iterAverageLinear L n k X.fine ∘ₗ covDiffRealTranspose L n k X.fine)) ∘ₗ
        LinearMap.fst ℝ _ _
    have hLm : ∀ ξ : LevelForms L n k, gaugeSliceResidual X.fine ξ.1 = Lm ξ := fun ξ => rfl
    have cT : ∀ u v : vertexFunctionSpace L n k 0, cG.inner u v = cG.inner v u := fun u v => by
      rw [← cG.conj_inner_symm u v]
      simp only [conj_trivial]
    have cS : ∀ ξ : LevelForms L n k, ∀ v, cG.inner (Lm ξ) v = cG.inner v (Lm ξ) := fun ξ v =>
      cT _ _
    have cS' : ∀ v : vertexFunctionSpace L n k 0, ∀ ξ : LevelForms L n k,
        cG.inner v (Lm ξ) = cG.inner (Lm ξ) v := fun v ξ => cT _ _
    have h := isQuadratic_of_bilinear (fun ξ ξ' : LevelForms L n k => cG.inner (Lm ξ) (Lm ξ'))
      (fun x x' y => by simp only [map_add, cG.add_left])
      (fun r x y => by simp only [map_smul]; simpa using cG.smul_left (Lm x) (Lm y) r)
      (fun x y y' => by
        simp only [map_add]
        rw [cS x (Lm y + Lm y'), cG.add_left, cS' (Lm y), cS' (Lm y')])
      (fun r x y => by
        simp only [map_smul]
        rw [cS x (r • Lm y)]
        have := cG.smul_left (Lm y) (Lm x) r
        simp only [conj_trivial] at this
        rw [this, cS' (Lm y)])
    refine h.congr fun ξ => ?_
    rw [hLm]
    unfold traceFinsumNorm
    rw [Real.sq_sqrt]
    · exact iG _ _
    · have := cG.re_inner_nonneg (Lm ξ)
      rw [iG] at this
      simpa using this
  have hall := (((Q1.add (Q2.const_mul 2)).add Q3).sub Q4).add Q5
  refine hall.congr fun ξ => ?_
  simp only [gaugedRightValue, gaugedFormValue, G]
  rw [hσ]
  have e := hm.orbit_spec (σ ξ)
  rw [hσ] at e
  rw [e]
end RightSide
section LevelFormsInner
variable {L n k : ℕ} [NeZero L]
theorem levelFormsEuclidean (hF : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : LevelFormsEuclidean L n k := by
  have h₀ := hF L n k 0 hL hn (Nat.zero_le k)
  have hi : ∀ i : Fin k, _ := fun i : Fin k => hF L n k (i + 1) hL hn i.2
  haveI := h₀.2.1
  haveI : ∀ i : Fin k, FiniteDimensional ℝ (edgeFormSpace L n k (i + 1)) := fun i => (hi i).2.1
  obtain ⟨c₀, hc₀⟩ := h₀.2.2.2
  choose c hc using fun i => (hi i).2.2.2
  refine ⟨inferInstance, ⟨⟨⟨fun ξ ξ' => c₀.inner ξ.1 ξ'.1 + ∑ i, (c i).inner (ξ.2 i) (ξ'.2 i)⟩,
    ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro ξ ξ'
    simp only [conj_trivial]
    rw [← c₀.conj_inner_symm ξ'.1 ξ.1]
    simp only [conj_trivial]
    refine congrArg₂ _ rfl (Finset.sum_congr rfl fun i _ => ?_)
    simpa using (c i).conj_inner_symm (ξ.2 i) (ξ'.2 i)
  · intro ξ
    simp only [RCLike.re_to_real]
    have h1 := c₀.re_inner_nonneg ξ.1
    simp only [RCLike.re_to_real] at h1
    refine add_nonneg h1 (Finset.sum_nonneg fun i _ => ?_)
    simpa using (c i).re_inner_nonneg (ξ.2 i)
  · intro ξ ξ' ζ
    have h1 := c₀.add_left ξ.1 ξ'.1 ζ.1
    show c₀.inner (ξ.1 + ξ'.1) ζ.1 + ∑ i, (c i).inner (ξ.2 i + ξ'.2 i) (ζ.2 i) =
      (c₀.inner ξ.1 ζ.1 + ∑ i, (c i).inner (ξ.2 i) (ζ.2 i)) +
        (c₀.inner ξ'.1 ζ.1 + ∑ i, (c i).inner (ξ'.2 i) (ζ.2 i))
    rw [h1, Finset.sum_congr rfl fun i _ => (c i).add_left (ξ.2 i) (ξ'.2 i) (ζ.2 i),
      Finset.sum_add_distrib]
    ring
  · intro ξ ξ' r
    have h1 := c₀.smul_left ξ.1 ξ'.1 r
    show c₀.inner (r • ξ.1) ξ'.1 + ∑ i, (c i).inner (r • ξ.2 i) (ξ'.2 i) =
      r * (c₀.inner ξ.1 ξ'.1 + ∑ i, (c i).inner (ξ.2 i) (ξ'.2 i))
    rw [h1, Finset.sum_congr rfl fun i _ => (c i).smul_left (ξ.2 i) (ξ'.2 i) r]
    simp only [conj_trivial, ← Finset.mul_sum]
    ring
  · intro ξ h
    have h1 : 0 ≤ c₀.inner ξ.1 ξ.1 := by simpa using c₀.re_inner_nonneg ξ.1
    have h2 : ∀ i, 0 ≤ (c i).inner (ξ.2 i) (ξ.2 i) := fun i => by
      simpa using (c i).re_inner_nonneg (ξ.2 i)
    have hs : 0 ≤ ∑ i, (c i).inner (ξ.2 i) (ξ.2 i) := Finset.sum_nonneg fun i _ => h2 i
    have h3 : c₀.inner ξ.1 ξ.1 + ∑ i, (c i).inner (ξ.2 i) (ξ.2 i) = 0 := h
    have h4 : c₀.inner ξ.1 ξ.1 = 0 := by linarith
    have h5 : ∑ i, (c i).inner (ξ.2 i) (ξ.2 i) = 0 := by linarith
    have h6 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => h2 i).mp h5
    exact Prod.ext (c₀.definite _ h4) (funext fun i => (c i).definite _ (h6 i (Finset.mem_univ i)))
  · intro ξ ξ'
    show c₀.inner ξ.1 ξ'.1 + ∑ i, (c i).inner (ξ.2 i) (ξ'.2 i) = _
    unfold levelPairing formValues
    simp only [hc₀, hc, Complex.ofReal_re]
end LevelFormsInner
section Conjugation
theorem inv_mul_of_det_one {V : ComplexMatrix2} (h : V.det = 1) : V⁻¹ * V = 1 :=
  Matrix.nonsing_inv_mul V (by rw [h]; exact isUnit_one)
theorem mul_inv_of_det_one {V : ComplexMatrix2} (h : V.det = 1) : V * V⁻¹ = 1 :=
  Matrix.mul_nonsing_inv V (by rw [h]; exact isUnit_one)
theorem inv_inv_of_det_one {V : ComplexMatrix2} (h : V.det = 1) : V⁻¹⁻¹ = V :=
  Matrix.nonsing_inv_nonsing_inv V (by rw [h]; exact isUnit_one)
theorem conjugateBy_sub (g X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (X - Y) =
      ComplexMatrix2.conjugateBy g X - ComplexMatrix2.conjugateBy g Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_sub, sub_mul]
theorem halfTrace_conjugateBy {g : ComplexMatrix2} (hg : g.det = 1) (X Y : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (ComplexMatrix2.conjugateBy g X * ComplexMatrix2.conjugateBy g Y) =
      ComplexMatrix2.halfTrace (X * Y) := by apply _root_.YangMills.Construction.BackgroundGaugeInvariance.halfTrace_conjugateBy <;> assumption
theorem conjugateBy_conjugateBy {g h : ComplexMatrix2} (X A : ComplexMatrix2) (hh : h.det = 1) :
    ComplexMatrix2.conjugateBy (g * X * h⁻¹) (ComplexMatrix2.conjugateBy h A) =
      ComplexMatrix2.conjugateBy g (ComplexMatrix2.conjugateBy X A) := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.conjugateBy_conjugateBy_gauge <;> assumption
theorem conjugateBy_inv_conjugateBy {g : ComplexMatrix2} (hg : g.det = 1) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g⁻¹ (ComplexMatrix2.conjugateBy g A) = A := by
  simp only [ComplexMatrix2.conjugateBy, inv_inv_of_det_one hg]
  calc g⁻¹ * (g * A * g⁻¹) * g = (g⁻¹ * g) * A * (g⁻¹ * g) := by simp only [mul_assoc]
    _ = A := by rw [inv_mul_of_det_one hg, one_mul, mul_one]
theorem conjugateBy_conjugateBy_inv {g : ComplexMatrix2} (hg : g.det = 1) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (ComplexMatrix2.conjugateBy g⁻¹ A) = A := by
  simp only [ComplexMatrix2.conjugateBy, inv_inv_of_det_one hg]
  calc g * (g⁻¹ * A * g) * g⁻¹ = (g * g⁻¹) * A * (g * g⁻¹) := by simp only [mul_assoc]
    _ = A := by rw [mul_inv_of_det_one hg, one_mul, mul_one]
theorem inv_conj_eq {g h X : ComplexMatrix2} (hh : h.det = 1) :
    (g * X * h⁻¹)⁻¹ = h * X⁻¹ * g⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_of_det_one hh, mul_assoc]
theorem conjugateBy_mem_hermitianTraceless {g A : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy g A ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p2904 <;> assumption
end Conjugation
section GaugeTurning
variable {L n k : ℕ} [NeZero L]
instance {j : ℕ} : Fintype (Vertex L n k j) := Fintype.ofFinite _
structure AveragingFacts (L n k : ℕ) : Prop where
  admissible : ∀ i < k, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
    PolydiscIsAdmissible (polydiscRadius L) c
  mem_polydisc : ∀ i < k, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
    ∀ V ∈ smallComplexFields L n k i, V ∈ nearIdentityPolydisc (polydiscRadius L) c
theorem vertexFunction_mem {j : ℕ} (l : vertexFunctionSpace L n k j) (x : Vertex L n k j) :
    (l : Vertex L n k j → ComplexMatrix2) x ∈ ComplexMatrix2.hermitianTraceless :=
  l.2 x (Set.mem_univ x)
theorem complexBlockAverage_opposite {a i : ℕ} (W : Edge L n k i → ComplexMatrix2)
    {c : Edge L n k a} (hc : ¬c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage W c =
      (PeriodicLattice.complexBlockAverage W c.opposite)⁻¹ := by
  have hr := PeriodicLattice.Bond.opposite_isPositivelyOriented hc
  simp only [PeriodicLattice.complexBlockAverage, if_neg hc, if_pos hr]
theorem complexBlockAverageStep_gauge (T : AveragingFacts L n k) {i : ℕ} (hi : i < k)
    {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L n k i) {u : Vertex L n k i → ComplexMatrix2}
    (hu : u ∈ gaugeGroupAt L n k i) :
    PeriodicLattice.complexBlockAverageStep i (PeriodicLattice.gaugeTransform u V) =
      PeriodicLattice.gaugeTransform (restrictVertexFunction (i + 1) u)
        (PeriodicLattice.complexBlockAverageStep i V) := by
  have hr : ∀ x, (restrictVertexFunction (i + 1) u x).det = 1 := fun x => compact_det (hu _)
  have hpos : ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
      PeriodicLattice.complexBlockAverage (PeriodicLattice.gaugeTransform u V) c =
        PeriodicLattice.gaugeTransform (restrictVertexFunction (i + 1) u)
          (PeriodicLattice.complexBlockAverage V) c :=
    fun c hc =>
      ((T.admissible i hi c hc).gauge_covariant V (T.mem_polydisc i hi c hc V hV) u hu).2.1
  funext c
  by_cases hc : c.IsPositivelyOriented
  · exact hpos c hc
  · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hc
    show PeriodicLattice.complexBlockAverage (PeriodicLattice.gaugeTransform u V) c =
      restrictVertexFunction (i + 1) u c.source * PeriodicLattice.complexBlockAverage V c *
        (restrictVertexFunction (i + 1) u c.target)⁻¹
    rw [complexBlockAverage_opposite _ hc, hpos _ hp, complexBlockAverage_opposite V hc]
    exact inv_conj_eq (hr _)
theorem restrictVertexFunction_succ {i : ℕ} (hi : i ≤ k) (l : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction (i + 1) (restrictVertexFunction i l) = restrictVertexFunction (i + 1) l := by
  funext x
  exact restrictVertexFunction_toSublattice l hi x
theorem complexBlockFieldAtLevel_gauge (T : AveragingFacts L n k) {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L n k) {u : Vertex L n k 0 → ComplexMatrix2}
    (hu : u ∈ gaugeGroupAt L n k 0) :
    ∀ i ≤ k, PeriodicLattice.complexBlockFieldAtLevel i (PeriodicLattice.gaugeTransform u U) =
      PeriodicLattice.gaugeTransform (restrictVertexFunction i u)
        (PeriodicLattice.complexBlockFieldAtLevel i U) := by
  intro i
  induction i with
  | zero =>
    intro _
    show PeriodicLattice.gaugeTransform u U =
      PeriodicLattice.gaugeTransform (restrictVertexFunction 0 u) U
    rw [restrictVertexFunction_zero]
  | succ i ih =>
    intro h
    have hi : i < k := h
    show PeriodicLattice.complexBlockAverageStep i
        (PeriodicLattice.complexBlockFieldAtLevel i (PeriodicLattice.gaugeTransform u U)) =
      PeriodicLattice.gaugeTransform (restrictVertexFunction (i + 1) u)
        (PeriodicLattice.complexBlockAverageStep i (PeriodicLattice.complexBlockFieldAtLevel i U))
    rw [ih hi.le, complexBlockAverageStep_gauge T hi (hU.2 i hi)
        (u := restrictVertexFunction i u) (fun x => hu _),
      restrictVertexFunction_succ hi.le]
theorem adjointCubeAverage_gauge (T : AveragingFacts L n k) {i : ℕ} (hi : i < k)
    {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L n k i) {u : Vertex L n k i → ComplexMatrix2}
    (hu : u ∈ gaugeGroupAt L n k i) (l : Vertex L n k i → ComplexMatrix2) :
    adjointCubeAverage (PeriodicLattice.gaugeTransform u V) (adjointVertexFn u l) =
      adjointVertexFn (restrictVertexFunction (i + 1) u) (adjointCubeAverage V l) := by
  funext y
  let c : Edge L n k (i + 1) := PeriodicLattice.Bond.forwardFrom y 0
  have hc : c.IsPositivelyOriented := ⟨0, by simp [c, PeriodicLattice.Bond.forwardFrom]⟩
  have hcov :=
    ((T.admissible i hi c hc).gauge_covariant V (T.mem_polydisc i hi c hc V hV) u hu).2.2 y
      (Set.mem_insert _ _)
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y :
      Set (Vertex L n k i)).Finite := Set.toFinite _
  simp only [adjointCubeAverage, adjointVertexFn, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have e : ∀ x ∈ hfin.toFinset,
      ComplexMatrix2.conjugateBy
          (PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.gaugeTransform u V) y x)
          (ComplexMatrix2.conjugateBy (u x) (l x)) =
        ComplexMatrix2.conjugateBy (u (y.toSublattice (PeriodicLattice.levelDepth k i)))
          (ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy V y x) (l x)) :=
    fun x hx => by
    rw [hcov x (by simpa using hx)]
    exact conjugateBy_conjugateBy _ _ (compact_det (hu x))
  rw [Finset.sum_congr rfl e]
  show _ = ComplexMatrix2.conjugateBy (u (y.toSublattice (PeriodicLattice.levelDepth k i))) _
  simp only [ComplexMatrix2.conjugateBy, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul]
variable (hC : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
include hC hL hn in
theorem composedCubeAverage_gauge (T : AveragingFacts L n k) {X' : ChainPoint L n k}
    (hX' : IsCompactValued X')
    (hs : ∀ j < k, levelField X' j ∈ smallComplexFields L n k j)
    {u : Vertex L n k 0 → ComplexMatrix2} (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup)
    (l : Vertex L n k 0 → ComplexMatrix2) :
    ∀ j ≤ k, composedCubeAverage (gaugeTransformPoint u X') j (adjointVertexFn u l) =
      adjointVertexFn (restrictVertexFunction j u) (composedCubeAverage X' j l) := by
  intro j
  induction j with
  | zero =>
    intro _
    show adjointVertexFn u l = adjointVertexFn (restrictVertexFunction 0 u) l
    rw [restrictVertexFunction_zero]
  | succ j ih =>
    intro h
    have hj : j < k := h
    show adjointCubeAverage (levelField (gaugeTransformPoint u X') j)
        (composedCubeAverage (gaugeTransformPoint u X') j (adjointVertexFn u l)) =
      adjointVertexFn (restrictVertexFunction (j + 1) u)
        (adjointCubeAverage (levelField X' j) (composedCubeAverage X' j l))
    rw [ih hj.le, _root_.YangMills.Construction.RunningCouplingSlope.GhostQuadraticProof.levelField_gaugeTransformPoint hC hL hn hX' hu j hj.le,
      adjointCubeAverage_gauge T hj (hs j hj) (u := restrictVertexFunction j u) (fun x => hu _),
      restrictVertexFunction_succ hj.le]
theorem iterAdjointCubeAverage_gauge (T : AveragingFacts L n k) {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L n k) {u : Vertex L n k 0 → ComplexMatrix2}
    (hu : u ∈ gaugeGroupAt L n k 0) (l : Vertex L n k 0 → ComplexMatrix2) :
    ∀ j ≤ k, iterAdjointCubeAverage L n k (PeriodicLattice.gaugeTransform u U) j
        (adjointVertexFn u l) =
      adjointVertexFn (restrictVertexFunction j u) (iterAdjointCubeAverage L n k U j l) := by
  intro j
  induction j with
  | zero =>
    intro _
    show adjointVertexFn u l = adjointVertexFn (restrictVertexFunction 0 u) l
    rw [restrictVertexFunction_zero]
  | succ j ih =>
    intro h
    have hj : j < k := h
    show adjointCubeAverage
        (PeriodicLattice.complexBlockFieldAtLevel j (PeriodicLattice.gaugeTransform u U))
        (iterAdjointCubeAverage L n k (PeriodicLattice.gaugeTransform u U) j
          (adjointVertexFn u l)) =
      adjointVertexFn (restrictVertexFunction (j + 1) u)
        (adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U)
          (iterAdjointCubeAverage L n k U j l))
    rw [ih hj.le, complexBlockFieldAtLevel_gauge T hU hu j hj.le,
      adjointCubeAverage_gauge T hj (hU.2 j hj) (u := restrictVertexFunction j u) (fun x => hu _),
      restrictVertexFunction_succ hj.le]
def conjVertexFunctions {j : ℕ} (w : Vertex L n k j → ComplexMatrix2)
    (hw : ∀ x, w x ∈ PeriodicLattice.compactGaugeGroup) :
    vertexFunctionSpace L n k j →ₗ[ℝ] vertexFunctionSpace L n k j where
  toFun l := ⟨adjointVertexFn w l,
    fun x _ => conjugateBy_mem_hermitianTraceless (hw x) (vertexFunction_mem l x)⟩
  map_add' l l' := Subtype.ext (funext fun x => conjugateBy_add _ _ _)
  map_smul' r l := Subtype.ext (funext fun x => conjugateBy_smul _ _ _)
theorem linearMapWithValues_apply {α β : Type*} {p : Submodule ℝ (α → ComplexMatrix2)}
    {p' : Submodule ℝ (β → ComplexMatrix2)} {f : (α → ComplexMatrix2) → β → ComplexMatrix2}
    (h : ∃ T : p →ₗ[ℝ] p', ∀ x : p, (T x : β → ComplexMatrix2) = f x) (x : p) :
    (linearMapWithValues p p' f x : β → ComplexMatrix2) = f x := by apply _root_.YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide.linearMapWithValues_apply <;> assumption
theorem traceFinsumPairing_add_left {ι : Type*} [Fintype ι] (f f' g : ι → ComplexMatrix2) :
    traceFinsumPairing (f + f') g = traceFinsumPairing f g + traceFinsumPairing f' g := by
  simp only [traceFinsumPairing, finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, add_mul, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_add, mul_add]
theorem traceFinsumPairing_conjugateBy {ι : Type*} {v : ι → ComplexMatrix2}
    (hv : ∀ x, (v x).det = 1) (f g : ι → ComplexMatrix2) :
    traceFinsumPairing (fun x => ComplexMatrix2.conjugateBy (v x) (f x))
      (fun x => ComplexMatrix2.conjugateBy (v x) (g x)) = traceFinsumPairing f g :=
  finsum_congr fun x => halfTrace_conjugateBy (hv x) _ _
structure DifferenceFacts (L n k : ℕ) : Prop where
  covDiff_linear : ∀ U ∈ fieldSpace L n k 0,
    ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0,
    ∀ l : vertexFunctionSpace L n k 0, (T l : Edge L n k 0 → ComplexMatrix2) =
      covDiff U (l : Vertex L n k 0 → ComplexMatrix2)
  covDiff_transpose : ∀ U ∈ fieldSpace L n k 0,
    ∀ (g : edgeFormSpace L n k 0) (f : vertexFunctionSpace L n k 0),
    traceFinsumPairing (covDiffRealTranspose L n k U g : Vertex L n k 0 → ComplexMatrix2)
        (f : Vertex L n k 0 → ComplexMatrix2) =
      edgeFormPairing (g : Edge L n k 0 → ComplexMatrix2)
        (covDiffLinear L n k U f : Edge L n k 0 → ComplexMatrix2)
structure NearUnitFacts (X : ChainPoint L n k) : Prop where
  compact : IsCompactValued X
  level_small : ∀ j < k, levelField X j ∈ smallComplexFields L n k j
  iter_small : X.fine ∈ smallIterateFields L n k
  composed_linear : ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k,
    ∀ l : vertexFunctionSpace L n k 0,
    (T l : Vertex L n k k → ComplexMatrix2) =
      composedCubeAverage X k (l : Vertex L n k 0 → ComplexMatrix2)
  iter_linear : ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k,
    ∀ l : vertexFunctionSpace L n k 0,
    (T l : Vertex L n k k → ComplexMatrix2) =
      iterAdjointCubeAverage L n k X.fine k (l : Vertex L n k 0 → ComplexMatrix2)
theorem ghostBlockOperator_apply (X : ChainPoint L n k) (l : vertexFunctionSpace L n k 0)
    (g : vertexFunctionSpace L n k k) :
    ghostBlockOperator X (l, g) =
      (covDiffRealTranspose L n k X.fine (covDiffLinear L n k X.fine l) +
        iterAverageRealTranspose L n k X.fine g, composedCubeAverageLinear X l) := rfl
theorem covDiff_gauge {U : Edge L n k 0 → ComplexMatrix2} {u : Vertex L n k 0 → ComplexMatrix2}
    (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup) (l : Vertex L n k 0 → ComplexMatrix2)
    (b : PositiveEdge L n k 0) :
    restrictToPositiveEdges (covDiff (PeriodicLattice.gaugeTransform u U) (adjointVertexFn u l)) b =
      ComplexMatrix2.conjugateBy (u b.1.source) (restrictToPositiveEdges (covDiff U l) b) := by
  simp only [restrictToPositiveEdges, covDiff, extendOddly_pos _ b.2, adjointVertexFn,
    PeriodicLattice.gaugeTransform, conjugateBy_sub]
  rw [conjugateBy_conjugateBy _ _ (compact_det (hu _))]
include hC hL hn in
theorem ghostBlockOperator_injective_gauge (T : AveragingFacts L n k) (Sp : DifferenceFacts L n k)
    (hE : VertexFunctionsEuclidean L n k 0)
    {X' : ChainPoint L n k} (hN : NearUnitFacts X') {u : Vertex L n k 0 → ComplexMatrix2}
    (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup)
    (hm : ChainLinearMapsAt (gaugeTransformPoint u X'))
    (hm' : ChainLinearMapsAt X') (hinj : Function.Injective (ghostBlockOperator X')) :
    Function.Injective (ghostBlockOperator (gaugeTransformPoint u X')) := by
  classical
  have hX' := hN.compact
  have hXr : IsCompactValued (gaugeTransformPoint u X') :=
    gaugeTransformPoint_compact hC hL hn hX' hu
  have hU' : X'.fine ∈ fieldSpace L n k 0 := hX'.2 0 (Nat.zero_le _)
  have hU : (gaugeTransformPoint u X').fine ∈ fieldSpace L n k 0 := hXr.2 0 (Nat.zero_le _)
  have hug : u ∈ gaugeGroupAt L n k 0 := hu
  have hur : ∀ x, (u x)⁻¹ ∈ PeriodicLattice.compactGaugeGroup := fun x => compact_inv_mem (hu x)
  have hrk : ∀ x : Vertex L n k k,
      restrictVertexFunction k u x ∈ PeriodicLattice.compactGaugeGroup := fun x => hu _
  have hrk' : ∀ x : Vertex L n k k,
      (restrictVertexFunction k u x)⁻¹ ∈ PeriodicLattice.compactGaugeGroup :=
    fun x => compact_inv_mem (hrk x)
  set S := conjVertexFunctions u hu with hSd
  set S' := conjVertexFunctions (fun x => (u x)⁻¹) hur with hS'd
  set Sk := conjVertexFunctions (restrictVertexFunction k u) hrk with hSkd
  set Sk' := conjVertexFunctions (fun x => (restrictVertexFunction k u x)⁻¹) hrk' with hSk'd
  have hSS' : ∀ l, S (S' l) = l := fun l =>
    Subtype.ext (funext fun x => conjugateBy_conjugateBy_inv (compact_det (hu x)) _)
  have hSkSk' : ∀ g, Sk (Sk' g) = g := fun g =>
    Subtype.ext (funext fun x => conjugateBy_conjugateBy_inv (compact_det (hrk x)) _)
  have hSk'Sk : ∀ g, Sk' (Sk g) = g := fun g =>
    Subtype.ext (funext fun x => conjugateBy_inv_conjugateBy (compact_det (hrk x)) _)
  obtain ⟨Ta, hTa⟩ := hN.composed_linear
  obtain ⟨Tr, hTr⟩ := hN.iter_linear
  have hcs : ∀ l : vertexFunctionSpace L n k 0,
      composedCubeAverage (gaugeTransformPoint u X') k (S l : Vertex L n k 0 → ComplexMatrix2) =
        (Sk (Ta l) : Vertex L n k k → ComplexMatrix2) := fun l => by
    have h := composedCubeAverage_gauge hC hL hn T hX' hN.level_small hu
      (l : Vertex L n k 0 → ComplexMatrix2) k le_rfl
    show composedCubeAverage (gaugeTransformPoint u X') k (adjointVertexFn u l) =
      adjointVertexFn (restrictVertexFunction k u) (Ta l)
    rw [h, hTa]
  have hci : ∀ l : vertexFunctionSpace L n k 0,
      iterAdjointCubeAverage L n k (gaugeTransformPoint u X').fine k
          (S l : Vertex L n k 0 → ComplexMatrix2) =
        (Sk (Tr l) : Vertex L n k k → ComplexMatrix2) := fun l => by
    have h := iterAdjointCubeAverage_gauge T hN.iter_small hug (l : Vertex L n k 0 → ComplexMatrix2)
      k le_rfl
    show iterAdjointCubeAverage L n k (PeriodicLattice.gaugeTransform u X'.fine) k
        (adjointVertexFn u l) =
      adjointVertexFn (restrictVertexFunction k u) (Tr l)
    rw [h, hTr]
  have hav' : ∀ l, composedCubeAverageLinear X' l = Ta l := fun l =>
    Subtype.ext ((linearMapWithValues_apply ⟨Ta, hTa⟩ l).trans (hTa l).symm)
  have hav : ∀ l, composedCubeAverageLinear (gaugeTransformPoint u X') (S l) = Sk (Ta l) := fun l =>
    Subtype.ext ((linearMapWithValues_apply ⟨Sk ∘ₗ Ta ∘ₗ S', fun m => by
      show (Sk (Ta (S' m)) : Vertex L n k k → ComplexMatrix2) = _
      rw [← hcs (S' m), hSS']⟩ (S l)).trans (hcs l))
  have hr' : ∀ l, iterAverageLinear L n k X'.fine l = Tr l := fun l =>
    Subtype.ext ((linearMapWithValues_apply ⟨Tr, hTr⟩ l).trans (hTr l).symm)
  have hr : ∀ l, iterAverageLinear L n k (gaugeTransformPoint u X').fine (S l) = Sk (Tr l) :=
    fun l => Subtype.ext ((linearMapWithValues_apply ⟨Sk ∘ₗ Tr ∘ₗ S', fun m => by
      show (Sk (Tr (S' m)) : Vertex L n k k → ComplexMatrix2) = _
      rw [← hci (S' m), hSS']⟩ (S l)).trans (hci l))
  have hD' : ∀ l : vertexFunctionSpace L n k 0, (covDiffLinear L n k X'.fine l :
      Edge L n k 0 → ComplexMatrix2) = covDiff X'.fine (l : Vertex L n k 0 → ComplexMatrix2) :=
    fun l => linearMapWithValues_apply (Sp.covDiff_linear _ hU') l
  have hD : ∀ l : vertexFunctionSpace L n k 0,
      (covDiffLinear L n k (gaugeTransformPoint u X').fine l : Edge L n k 0 → ComplexMatrix2) =
        covDiff (gaugeTransformPoint u X').fine (l : Vertex L n k 0 → ComplexMatrix2) := fun l =>
    linearMapWithValues_apply (Sp.covDiff_linear _ hU) l
  have hDbp : ∀ l m : vertexFunctionSpace L n k 0,
      edgeFormPairing (covDiffLinear L n k (gaugeTransformPoint u X').fine (S l) :
          Edge L n k 0 → ComplexMatrix2)
        (covDiffLinear L n k (gaugeTransformPoint u X').fine (S m) :
          Edge L n k 0 → ComplexMatrix2) =
      edgeFormPairing (covDiffLinear L n k X'.fine l : Edge L n k 0 → ComplexMatrix2)
        (covDiffLinear L n k X'.fine m : Edge L n k 0 → ComplexMatrix2) := fun l m => by
    have e : ∀ l : vertexFunctionSpace L n k 0, restrictToPositiveEdges
        (covDiffLinear L n k (gaugeTransformPoint u X').fine (S l) :
          Edge L n k 0 → ComplexMatrix2) =
        fun b => ComplexMatrix2.conjugateBy (u b.1.source)
          (restrictToPositiveEdges (covDiffLinear L n k X'.fine l :
            Edge L n k 0 → ComplexMatrix2) b) :=
      fun l => funext fun b => by
        rw [hD (S l), hD' l]
        exact covDiff_gauge hu _ b
    unfold edgeFormPairing
    rw [e l, e m]
    exact traceFinsumPairing_conjugateBy (fun b => compact_det (hu _)) _ _
  have hpk : ∀ g g' : vertexFunctionSpace L n k k,
      traceFinsumPairing (Sk g : Vertex L n k k → ComplexMatrix2)
        (Sk g' : Vertex L n k k → ComplexMatrix2) =
      traceFinsumPairing (g : Vertex L n k k → ComplexMatrix2) g' := fun g g' =>
    traceFinsumPairing_conjugateBy (fun x => compact_det (hrk x)) _ _
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨l, g⟩ h
  obtain ⟨l', rfl⟩ : ∃ l', S l' = l := ⟨S' l, hSS' l⟩
  obtain ⟨g', rfl⟩ : ∃ g', Sk g' = g := ⟨Sk' g, hSkSk' g⟩
  obtain ⟨hEf, cG, iG⟩ := hE
  rw [ghostBlockOperator_apply] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2
  have e2 : composedCubeAverageLinear X' l' = 0 := by
    rw [hav']
    rw [hav] at h2
    have h3 := congrArg Sk' h2
    rwa [hSk'Sk, map_zero] at h3
  have e1 : covDiffRealTranspose L n k X'.fine (covDiffLinear L n k X'.fine l') +
      iterAverageRealTranspose L n k X'.fine g' = 0 := by
    set y := covDiffRealTranspose L n k X'.fine (covDiffLinear L n k X'.fine l') +
      iterAverageRealTranspose L n k X'.fine g' with hy
    have key : ∀ m : vertexFunctionSpace L n k 0,
        traceFinsumPairing (y : Vertex L n k 0 → ComplexMatrix2)
        (m : Vertex L n k 0 → ComplexMatrix2) = 0 := fun m => by
      have p0 : traceFinsumPairing (((covDiffRealTranspose L n k (gaugeTransformPoint u X').fine
          (covDiffLinear L n k (gaugeTransformPoint u X').fine (S l')) +
          iterAverageRealTranspose L n k (gaugeTransformPoint u X').fine (Sk g') :
            vertexFunctionSpace L n k 0)) : Vertex L n k 0 → ComplexMatrix2)
          (S m : Vertex L n k 0 → ComplexMatrix2) = 0 := by
        rw [h1]
        simp [traceFinsumPairing, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
      rw [Submodule.coe_add, traceFinsumPairing_add_left, Sp.covDiff_transpose _ hU,
        hm.iterTranspose_pairing, hDbp, hr, hpk] at p0
      rw [hy, Submodule.coe_add, traceFinsumPairing_add_left, Sp.covDiff_transpose _ hU',
        hm'.iterTranspose_pairing, hr']
      exact p0
    refine cG.definite y ?_
    rw [iG, key y]
    rfl
  have hz : ((l', g') : vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k) = 0 :=
    (injective_iff_map_eq_zero _).1 hinj _
      (by rw [ghostBlockOperator_apply]; exact Prod.ext e1 e2)
  have hl0 : l' = 0 := congrArg Prod.fst hz
  have hg0 : g' = 0 := congrArg Prod.snd hz
  rw [hl0, hg0, map_zero, map_zero]
  rfl
end GaugeTurning
section UnitPoint
variable {L n k : ℕ} [NeZero L]
theorem levelField_unitPoint (hD : NormalizedMeanAtOne)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j ≤ k, levelField (unitPoint L n k) j = fun _ => 1 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    have hpos : ∀ b : Edge L n k (j + 1), b.IsPositivelyOriented →
        levelField (unitPoint L n k) (j + 1) b = 1 := fun b hb => by
      rw [levelField_succ_pos _ hj hb, ih hj.le,
        (hD L hL n k j hn hj 0 (edgeFormSpace L n k j).zero_mem b hb).2.2.1]
      simp [unitPoint]
    funext b
    by_cases hb : b.IsPositivelyOriented
    · exact hpos b hb
    · rw [levelField_succ_neg _ hj hb,
        hpos _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb)]
      simp
theorem complexBlockFieldAtLevel_trivial (hS : ∀ i < k, PeriodicLattice.complexBlockAverageStep i
      (trivialField L n k i) = trivialField L n k (i + 1)) :
    ∀ j ≤ k, PeriodicLattice.complexBlockFieldAtLevel j (trivialField L n k 0) =
      trivialField L n k j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    show PeriodicLattice.complexBlockAverageStep j (PeriodicLattice.complexBlockFieldAtLevel j _) = _
    rw [ih (Nat.le_of_succ_le h)]
    exact hS j h
theorem composedCubeAverage_unitPoint
    (hfl : ∀ j ≤ k, levelField (unitPoint L n k) j = trivialField L n k j)
    (hit : ∀ j ≤ k, PeriodicLattice.complexBlockFieldAtLevel j (trivialField L n k 0) =
      trivialField L n k j) (l : Vertex L n k 0 → ComplexMatrix2) :
    ∀ j ≤ k, composedCubeAverage (unitPoint L n k) j l =
      iterAdjointCubeAverage L n k (unitPoint L n k).fine j l := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    have hj : j ≤ k := Nat.le_of_succ_le h
    show adjointCubeAverage (levelField (unitPoint L n k) j)
        (composedCubeAverage (unitPoint L n k) j l) =
      adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j (trivialField L n k 0))
        (iterAdjointCubeAverage L n k (unitPoint L n k).fine j l)
    rw [ih hj, hfl j hj, hit j hj]
theorem ghostBlockOperator_injective_unitPoint (Sp : DifferenceFacts L n k)
    (hF : EdgeFormsEuclidean L n k 0)
    (hN : NearUnitFacts (unitPoint L n k)) (hm : ChainLinearMapsAt (unitPoint L n k))
    (hsame : ∀ l : Vertex L n k 0 → ComplexMatrix2, composedCubeAverage (unitPoint L n k) k l =
      iterAdjointCubeAverage L n k (unitPoint L n k).fine k l) :
    Function.Injective (ghostBlockOperator (unitPoint L n k)) := by
  classical
  obtain ⟨-, cF, iF⟩ := hF
  have hU : (unitPoint L n k).fine ∈ fieldSpace L n k 0 := hN.compact.2 0 (Nat.zero_le _)
  obtain ⟨Ta, hTa⟩ := hN.composed_linear
  obtain ⟨Tr, hTr⟩ := hN.iter_linear
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨l, g⟩ h
  rw [ghostBlockOperator_apply] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2
  have hav : composedCubeAverageLinear (unitPoint L n k) l = Ta l :=
    Subtype.ext ((linearMapWithValues_apply ⟨Ta, hTa⟩ l).trans (hTa l).symm)
  have hr : iterAverageLinear L n k (unitPoint L n k).fine l = Tr l :=
    Subtype.ext ((linearMapWithValues_apply ⟨Tr, hTr⟩ l).trans (hTr l).symm)
  have hTT : Ta l = Tr l := Subtype.ext (by rw [hTa, hTr]; exact hsame _)
  have hr0 : iterAverageLinear L n k (unitPoint L n k).fine l = 0 := by
    rw [hr, ← hTT, ← hav, h2]
  have p0 : traceFinsumPairing (((covDiffRealTranspose L n k (unitPoint L n k).fine
      (covDiffLinear L n k (unitPoint L n k).fine l) +
      iterAverageRealTranspose L n k (unitPoint L n k).fine g : vertexFunctionSpace L n k 0)) :
        Vertex L n k 0 → ComplexMatrix2) (l : Vertex L n k 0 → ComplexMatrix2) = 0 := by
    rw [h1]
    simp [traceFinsumPairing, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  rw [Submodule.coe_add, traceFinsumPairing_add_left, Sp.covDiff_transpose _ hU,
    hm.iterTranspose_pairing, hr0] at p0
  have hz : traceFinsumPairing (g : Vertex L n k k → ComplexMatrix2)
      ((0 : vertexFunctionSpace L n k k) : Vertex L n k k → ComplexMatrix2) = 0 := by
    simp [traceFinsumPairing, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  rw [hz, add_zero] at p0
  have hD0 : covDiffLinear L n k (unitPoint L n k).fine l = 0 := by
    refine cF.definite _ ?_
    rw [iF, p0]
    rfl
  have hv : (covDiffLinear L n k (unitPoint L n k).fine l : Edge L n k 0 → ComplexMatrix2) =
      covDiff (unitPoint L n k).fine (l : Vertex L n k 0 → ComplexMatrix2) :=
    linearMapWithValues_apply (Sp.covDiff_linear _ hU) l
  rw [hD0] at hv
  have hO0 : gaugeOrbitMap (unitPoint L n k) l = 0 := formValues_injective (by
    rw [hm.orbit_spec l]
    refine Prod.ext hv.symm (funext fun i => ?_)
    funext c
    have hR : (formValues (0 : LevelForms L n k)).2 i c = 0 := rfl
    rw [hR]
    simp only [gaugeOrbitValues]
    by_cases hc : c.IsPositivelyOriented
    · rw [extendOddly_pos _ hc]
      simp [hc, ComplexMatrix2.conjugateBy, unitPoint]
    · rw [extendOddly_neg _ hc]
      simp [PeriodicLattice.Bond.opposite_isPositivelyOriented hc, ComplexMatrix2.conjugateBy,
        unitPoint])
  have hr1 : restrictToTopLinear L n k l = 0 := by
    have h3 := hm.mean_eq l
    rw [h2, hO0, map_zero, add_zero] at h3
    exact h3.symm
  have hlk : l ∈ topVanishingGauges L n k := fun y => by
    have h3 := hm.restrict_apply l
    rw [hr1] at h3
    exact (congrFun h3 y).symm
  have hl0 : l = 0 := by
    have h3 := hm.orbit_injective (a₁ := ⟨l, hlk⟩) (a₂ := 0) (by
      show gaugeOrbitMap (unitPoint L n k) l = gaugeOrbitMap (unitPoint L n k) 0
      rw [hO0, map_zero])
    exact congrArg Subtype.val h3
  subst hl0
  have ht : iterAverageRealTranspose L n k (unitPoint L n k).fine g = 0 := by
    simpa using h1
  have h3 := hm.iterAverage_transpose g
  rw [ht, map_zero] at h3
  have hc : ((L : ℝ) ^ (4 * k))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L)))
  have hg0 : g = 0 := (smul_eq_zero.1 h3.symm).resolve_left hc
  rw [hg0]
  rfl
end UnitPoint
section NearUnit
variable {L n k : ℕ} [NeZero L]
theorem expMove_zero_unitPoint :
    expMove (0 : LevelForms L n k) (unitPoint L n k) = unitPoint L n k := by apply _root_.YangMills.SharedProofs.p62410 <;> assumption
theorem analyticAt_linearMap_det_prod {A C E : Type} [AddCommGroup A] [Module ℝ A]
    [FiniteDimensional ℝ A]
    [AddCommGroup C] [Module ℝ C] [FiniteDimensional ℝ C] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (cA : InnerProductSpace.Core ℝ A)
    (cC : InnerProductSpace.Core ℝ C) (f : E → (A × C) →ₗ[ℝ] A × C) (x : E)
    (hf : ∀ x' y : A × C, AnalyticAt ℝ (fun w =>
      cA.inner x'.1 (f w y).1 + cC.inner x'.2 (f w y).2) x) :
    AnalyticAt ℝ (fun w => LinearMap.det (f w)) x := by apply _root_.YangMills.SharedProofs.p93035 <;> assumption
def formValuesLinear : LevelForms L n k →ₗ[ℝ] LevelValues L n k where
  toFun := formValues
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem ghostBlockOperator_det_ne_zero_near (hEnt : ChainFunctionEntriesAnalytic) {a : ℝ}
    (ha : 0 < a)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n)
    (hA : LevelFormsEuclidean L n k) (hC : EdgeFormsEuclidean L n k k)
    (h₀ : VertexFunctionsEuclidean L n k 0) (hk' : VertexFunctionsEuclidean L n k k)
    (hG : LinearMap.det (ghostBlockOperator (unitPoint L n k)) ≠ 0) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ξ : LevelForms L n k,
      (∀ b, ComplexMatrix2.operatorNorm ((ξ.1 : Edge L n k 0 → ComplexMatrix2) b) ≤ τ) →
      (∀ (i : Fin k) (b : Edge L n k ((i : ℕ) + 1)),
        ComplexMatrix2.operatorNorm ((ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) b) ≤ τ) →
      LinearMap.det (ghostBlockOperator (expMove ξ (unitPoint L n k))) ≠ 0 := by
  classical
  haveI := hA.1
  haveI := hC.1
  haveI := h₀.1
  haveI := hk'.1
  have iG : IsVertexPairingCore h₀.2.choose := h₀.2.choose_spec
  have iGc : IsVertexPairingCore hk'.2.choose := hk'.2.choose_spec
  let N := Module.finrank ℝ (LevelTriple L n k)
  let e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k :=
    (Module.finBasis ℝ (LevelTriple L n k)).equivFun.symm
  obtain ⟨-, -, -, hGh, -⟩ := hEnt a ha L hL k n hk hn N e
  have hAn : AnalyticAt ℝ (fun w =>
      LinearMap.det (ghostBlockOperator (expMove (e w).1 (unitPoint L n k)))) 0 := by
    refine analyticAt_linearMap_det_prod h₀.2.choose hk'.2.choose _ 0 fun x y => ?_
    refine (hGh x y).congr (Eventually.of_forall fun w => ?_)
    exact congrArg₂ (· + ·) (iG _ _).symm (iGc _ _).symm
  have he0 : e 0 = 0 := map_zero e
  have hne : LinearMap.det (ghostBlockOperator (expMove (e 0).1 (unitPoint L n k))) ≠ 0 := by
    simp only [he0, Prod.fst_zero, expMove_zero_unitPoint]
    exact hG
  have hev := hAn.continuousAt.eventually_ne hne
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  let Tm : (Fin N → ℝ) →ₗ[ℝ]
      LevelValues L n k × LevelValues L n k × (Edge L n k k → ComplexMatrix2) :=
    (formValuesLinear.prodMap (formValuesLinear.prodMap (edgeFormSpace L n k k).subtype)) ∘ₗ
      e.toLinearMap
  have hker : LinearMap.ker Tm = ⊥ := LinearMap.ker_eq_bot.2 fun w w' h => by
    have h1 : formValues (e w).1 = formValues (e w').1 := congrArg Prod.fst h
    have h2 : formValues (e w).2.1 = formValues (e w').2.1 := congrArg (fun p => p.2.1) h
    have h3 : ((e w).2.2 : Edge L n k k → ComplexMatrix2) = (e w').2.2 :=
      congrArg (fun p => p.2.2) h
    exact e.injective (Prod.ext (formValues_injective h1)
      (Prod.ext (formValues_injective h2) (Subtype.ext h3)))
  obtain ⟨K, hK, hanti⟩ := Tm.exists_antilipschitzWith hker
  have hK0 : (0 : ℝ) ≤ K := K.2
  refine ⟨δ / (2 * ((K : ℝ) + 1)), by positivity, fun ξ h1 h2 => ?_⟩
  set τ := δ / (2 * ((K : ℝ) + 1)) with hτ
  have hτ0 : 0 ≤ τ := by positivity
  set w : Fin N → ℝ := e.symm (ξ, 0, 0) with hw
  have hew : e w = (ξ, 0, 0) := e.apply_symm_apply _
  have hTw : Tm w = (formValues ξ, formValues (0 : LevelForms L n k), 0) := by
    show (formValues (e w).1, formValues (e w).2.1, ((e w).2.2 : Edge L n k k → ComplexMatrix2)) = _
    rw [hew]
    rfl
  have hV : ∀ ξ' : LevelForms L n k,
      (∀ b, ComplexMatrix2.operatorNorm ((ξ'.1 : Edge L n k 0 → ComplexMatrix2) b) ≤ τ) →
      (∀ (i : Fin k) (b : Edge L n k ((i : ℕ) + 1)),
        ComplexMatrix2.operatorNorm ((ξ'.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) b) ≤ τ) →
      ‖formValues ξ'‖ ≤ τ := fun ξ' g1 g2 => by
    rw [Prod.norm_def]
    exact max_le ((pi_norm_le_iff_of_nonneg hτ0).2 g1)
      ((pi_norm_le_iff_of_nonneg hτ0).2 fun i => (pi_norm_le_iff_of_nonneg hτ0).2 (g2 i))
  have hz : ‖formValues (0 : LevelForms L n k)‖ ≤ τ := by
    refine hV 0 (fun b => ?_) (fun i b => ?_)
    · simpa [ComplexMatrix2.operatorNorm] using hτ0
    · simpa [ComplexMatrix2.operatorNorm] using hτ0
  have hnorm : ‖Tm w‖ ≤ τ := by
    rw [hTw, Prod.norm_def, Prod.norm_def]
    refine max_le (hV ξ h1 h2) (max_le hz ?_)
    simpa using hτ0
  have hd : dist w 0 < δ := by
    have h3 := hanti.le_mul_dist w 0
    simp only [map_zero, dist_zero_right] at h3
    rw [dist_zero_right]
    have h4 : (K : ℝ) * ‖Tm w‖ ≤ K * τ := mul_le_mul_of_nonneg_left hnorm hK0
    have h5 : (K : ℝ) * τ < δ := by
      have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      rw [hτ, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have h6 := hball hd
  rw [hew] at h6
  exact h6
theorem exists_nearUnitFacts (hY : RealLinearMaps.RealLinearMapsStatement)
    (hE : IterLeftChartExpansion) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) (hρ : 0 < polydiscRadius L)
    (hflat : IsCompactValued (unitPoint L n k))
    (hone : ∀ j ≤ k, levelField (unitPoint L n k) j = fun _ => 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ X : ChainPoint L n k, IsCompactValued X →
      (∀ b, ComplexMatrix2.operatorNorm (X.fine b - 1) < ε) →
      (∀ i c, ComplexMatrix2.operatorNorm (X.noise i c - 1) < ε) →
      NearUnitFacts X := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hAt, -⟩ := hY L n (i + 1) hL hn hk
  have h0 : ofValues (toValues (unitPoint L n (i + 1))) = unitPoint L n (i + 1) :=
    ofValues_toValues (hflat.2 0 (Nat.zero_le _))
  have hev : ∀ j ≤ i + 1, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ w in 𝓝 (toValues (unitPoint L n (i + 1))), ∀ b : Edge L n (i + 1) j,
        ‖levelField (ofValues w) j b - 1‖ < δ := by
    intro j hj δ hδ
    refine eventually_all.2 fun b => ?_
    have hc := (contDiffAt_level_ofValues hflat hj b).continuousAt
    have h3 : Tendsto (fun w => ‖levelField (ofValues w) j b - 1‖)
        (𝓝 (toValues (unitPoint L n (i + 1)))) (𝓝 0) := by
      have h4 := (hc.tendsto.sub_const (1 : ComplexMatrix2)).norm
      simpa [h0, hone j hj] using h4
    exact h3.eventually_lt_const hδ
  have hstep : ∀ j < i + 1, ∃ δ : ℝ, 0 < δ ∧ ∀ V ∈ fieldSpace L n (i + 1) j,
      (∀ b, ‖V b - 1‖ < δ) → V ∈ smallComplexFields L n (i + 1) j ∧
        ∃ A : vertexFunctionSpace L n (i + 1) j →ₗ[ℝ] vertexFunctionSpace L n (i + 1) (j + 1),
          ∀ l : vertexFunctionSpace L n (i + 1) j,
          (A l : Vertex L n (i + 1) (j + 1) → ComplexMatrix2) =
            adjointCubeAverage V (l : Vertex L n (i + 1) j → ComplexMatrix2) := by
    intro j hj
    obtain ⟨δ, hδ, H⟩ := exists_radius_of_nearIdentity (hAt j hj).adjointCubeAverage_isLinear
    refine ⟨min δ (polydiscRadius L), lt_min hδ hρ, fun V hV hs =>
      ⟨⟨mem_fieldsIn_complex hV, fun b => lt_of_lt_of_le (hs b) (min_le_right _ _)⟩,
        H V hV fun b => lt_of_lt_of_le (hs b) (min_le_left _ _)⟩⟩
  choose! δs hδs hstepH using hstep
  have ev1 : ∀ᶠ w in 𝓝 (toValues (unitPoint L n (i + 1))), ∀ j ∈ Finset.range (i + 1),
      ∀ b : Edge L n (i + 1) j, ‖levelField (ofValues w) j b - 1‖ < δs j := by
    refine (Filter.eventually_all_finset _).2 fun j hj => ?_
    have hj' : j < i + 1 := Finset.mem_range.1 hj
    exact hev j hj'.le _ (hδs j hj')
  obtain ⟨δ₂, hδ₂, H2⟩ := exists_radius_of_nearIdentity ((hE L n (i + 1) hL hn hk).and
    (hAt i (Nat.lt_succ_self i)).iterAdjointCubeAverage_isLinear)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 ev1
  refine ⟨min ε δ₂, lt_min hε hδ₂, fun X hX hb hnz => ?_⟩
  have hXe : ofValues (toValues X) = X := ofValues_toValues (hX.2 0 (Nat.zero_le _))
  have hd : dist (toValues X) (toValues (unitPoint L n (i + 1))) < ε := by
    rw [dist_pi_lt_iff hε]
    rintro (b | p)
    · simpa [dist_eq_norm, toValues, unitPoint] using
        lt_of_lt_of_le (hb b.1) (min_le_left _ _)
    · simpa [dist_eq_norm, toValues, unitPoint] using
        lt_of_lt_of_le (hnz p.1 p.2) (min_le_left _ _)
  have hs := hball hd
  rw [hXe] at hs
  have hsl : ∀ j < i + 1, levelField X j ∈ smallComplexFields L n (i + 1) j ∧
      ∃ A : vertexFunctionSpace L n (i + 1) j →ₗ[ℝ] vertexFunctionSpace L n (i + 1) (j + 1),
        ∀ l : vertexFunctionSpace L n (i + 1) j,
        (A l : Vertex L n (i + 1) (j + 1) → ComplexMatrix2) =
          adjointCubeAverage (levelField X j) (l : Vertex L n (i + 1) j → ComplexMatrix2) :=
    fun j hj => hstepH j hj _ (hX.2 j hj.le) (hs j (Finset.mem_range.2 hj))
  have hsoft : ∀ j ≤ i + 1,
      ∃ T : vertexFunctionSpace L n (i + 1) 0 →ₗ[ℝ] vertexFunctionSpace L n (i + 1) j,
      ∀ l : vertexFunctionSpace L n (i + 1) 0, (T l : Vertex L n (i + 1) j → ComplexMatrix2) =
        composedCubeAverage X j (l : Vertex L n (i + 1) 0 → ComplexMatrix2) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨LinearMap.id, fun l => rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨T, hT⟩ := ih (Nat.le_of_succ_le hj)
      obtain ⟨-, A, hA⟩ := hsl j hj
      refine ⟨A ∘ₗ T, fun l => ?_⟩
      show (A (T l) : Vertex L n (i + 1) (j + 1) → ComplexMatrix2) =
        adjointCubeAverage (levelField X j)
          (composedCubeAverage X j (l : Vertex L n (i + 1) 0 → ComplexMatrix2))
      rw [hA, hT]
  obtain ⟨hF, hI⟩ := H2 X.fine (hX.2 0 (Nat.zero_le _))
    fun b => lt_of_lt_of_le (hb b) (min_le_right _ _)
  exact ⟨hX, fun j hj => (hsl j hj).1, hF.1.1, hsoft _ le_rfl, hI⟩
end NearUnit
section TraceDefect
theorem norm_sub_one_sq {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    ‖g - 1‖ ^ 2 = 2 * traceDefect g := by apply _root_.YangMills.SharedProofs.p32894 <;> assumption
theorem traceDefect_nonneg {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    0 ≤ traceDefect g := by apply _root_.YangMills.SharedProofs.p3544 <;> assumption
theorem traceDefect_inv {g : ComplexMatrix2} (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    traceDefect g⁻¹ = traceDefect g := by apply _root_.YangMills.SharedProofs.p3992 <;> assumption
theorem traceDefect_le {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) {ε : ℝ}
    (h1 : ε ≤ 1) (h : ComplexMatrix2.operatorNorm (g - 1) < ε) : traceDefect g ≤ ε := by
  have h2 := norm_sub_one_sq hg
  have h4 := norm_nonneg (g - 1)
  nlinarith
theorem traceDefect_quaternionToMatrix (q : Quaternion ℝ) :
    traceDefect (SoftAverages.quaternionToMatrix q) = 1 - q.re := by apply _root_.YangMills.SharedProofs.p14120 <;> assumption
variable {L n k : ℕ} [NeZero L]
instance {j : ℕ} : Fintype (Face L n k j) := @Fintype.ofFinite _ (finite_face j)
theorem plaquetteCost_eq_traceDefect (U : Edge L n k 0 → ComplexMatrix2) (p : Face L n k 0) :
    PeriodicLattice.plaquetteCost U p = traceDefect (PeriodicLattice.plaquetteHolonomy U p) := by apply _root_.YangMills.SharedProofs.p12545 <;> assumption
theorem plaquetteHolonomy_mem_compact {j : ℕ} {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k j) (p : Face L n k j) :
    PeriodicLattice.plaquetteHolonomy U p ∈ PeriodicLattice.compactGaugeGroup :=
  pathHolonomy_mem_compact (fun b => hU.1 b (Set.mem_univ _)) _
theorem plaquetteAction_eq_sum (U : Edge L n k 0 → ComplexMatrix2) :
    plaquetteAction L n k U =
      ∑ p : Face L n k 0, traceDefect (PeriodicLattice.plaquetteHolonomy U p) := by
  simp only [plaquetteAction, PeriodicLattice.wilsonAction, finsum_eq_sum_of_fintype,
    plaquetteCost_eq_traceDefect]
theorem chainAction_le {a : ℝ} (ha : 0 < a) {X : ChainPoint L n k} (hX : IsCompactValued X)
    {ε : ℝ} (h1 : ε ≤ 1) (hp : ∀ p : Face L n k 0,
      ComplexMatrix2.operatorNorm (PeriodicLattice.plaquetteHolonomy X.fine p - 1) < ε)
    (hnz : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      ComplexMatrix2.operatorNorm (X.noise i c - 1) < ε)
    (hl : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      ‖meanRadius (levelField X i) c.1 - 1‖ < ε) :
    chainAction a X ≤ ((Fintype.card (Face L n k 0) : ℝ) +
      a * ∑ i : Fin k, (Fintype.card (PositiveEdge L n k (i + 1)) : ℝ) * 2) * ε := by
  have hU : X.fine ∈ fieldSpace L n k 0 := hX.2 0 (Nat.zero_le _)
  have a1 : plaquetteAction L n k X.fine ≤ (Fintype.card (Face L n k 0) : ℝ) * ε := by
    rw [plaquetteAction_eq_sum]
    have := Finset.sum_le_card_nsmul Finset.univ
      (fun p : Face L n k 0 => traceDefect (PeriodicLattice.plaquetteHolonomy X.fine p)) ε
      (fun p _ => traceDefect_le (plaquetteHolonomy_mem_compact hU p) h1 (hp p))
    simpa using this
  have a2 : ∀ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
      (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c) ≤
      (Fintype.card (PositiveEdge L n k (i + 1)) : ℝ) * 2 * ε := fun i => by
    rw [finsum_eq_sum_of_fintype]
    have := Finset.sum_le_card_nsmul Finset.univ
      (fun c : PositiveEdge L n k (i + 1) =>
        (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c)) (2 * ε) (fun c _ => by
        have e0 := traceDefect_nonneg (hX.1 i c)
        have e1 := traceDefect_le (hX.1 i c) h1 (hnz i c)
        have e2 : (meanRadius (levelField X i) c.1).re ≤ 2 := by
          have := Complex.re_le_norm (meanRadius (levelField X i) c.1 - 1)
          have h3 := hl i c
          simp only [Complex.sub_re, Complex.one_re] at this
          linarith
        nlinarith)
    simpa [mul_assoc] using this
  have a3 := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => a2 i
  rw [← Finset.sum_mul] at a3
  have a4 := mul_le_mul_of_nonneg_left a3 ha.le
  simp only [chainAction]
  rw [add_mul, mul_assoc a]
  linarith
end TraceDefect
section TopLevel
variable {L n k : ℕ}
theorem exists_forwardFrom_topVertexOf (hlat : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (c : PositiveEdge L n k k) :
    ∃ (z : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4),
      c.1 = PeriodicLattice.Bond.forwardFrom (topVertexOf z) μ := by apply _root_.YangMills.SharedProofs.p10565 <;> assumption
theorem norm_sub_one_sq_le_of_represents (hlat : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {W : Edge L n k k → ComplexMatrix2}
    {V : TorusFields.TorusField (2 * L ^ n)} (hW : RepresentsTorusField W V) {η : ℝ}
    (hV : ∀ (z : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4),
      1 - ((V z μ : BlockAverages.UnitQuaternion) : Quaternion ℝ).re < η) (b : Edge L n k k) :
    ‖W b - 1‖ ^ 2 ≤ 2 * η := by
  have hpos : ∀ c : PositiveEdge L n k k, traceDefect (W c.1) ≤ η := fun c => by
    obtain ⟨z, μ, hz⟩ := exists_forwardFrom_topVertexOf hlat hL hn c
    rw [hz, hW.2 z μ, traceDefect_quaternionToMatrix]
    exact (hV z μ).le
  have hr : ∀ b, W b ∈ PeriodicLattice.compactGaugeGroup := fun b => hW.1.1 b (Set.mem_univ _)
  rw [norm_sub_one_sq (hr b)]
  by_cases hb : b.IsPositivelyOriented
  · have := hpos ⟨b, hb⟩
    simpa using (by linarith : 2 * traceDefect (W b) ≤ 2 * η)
  · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
    have h1 := hpos ⟨b.opposite, hp⟩
    have e : W b = (W b.opposite)⁻¹ := hW.1.2 b.opposite (Set.mem_univ _)
    rw [e, traceDefect_inv (hr _)]
    linarith
end TopLevel
section ExponentialCoordinates
variable {L n k : ℕ}
theorem exists_hermitian_log (hEL : ComplexMatrix2.ExpLogEstimates) {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) (h1 : ComplexMatrix2.operatorNorm (g - 1) < 1) :
    ∃ H ∈ ComplexMatrix2.hermitianTraceless, ComplexMatrix2.matExp (Complex.I • H) = g ∧
      ComplexMatrix2.operatorNorm H ≤ 2 * ComplexMatrix2.operatorNorm (g - 1) := by apply _root_.YangMills.SharedProofs.p26564 <;> assumption
theorem exists_expMove_unitPoint (hEL : ComplexMatrix2.ExpLogEstimates)
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {X : ChainPoint L n k} (hX : IsCompactValued X) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2)
    (hb : ∀ b, ComplexMatrix2.operatorNorm (X.fine b - 1) ≤ τ)
    (hn : ∀ i c, ComplexMatrix2.operatorNorm (X.noise i c - 1) ≤ τ) :
    ∃ ξ : LevelForms L n k, expMove ξ (unitPoint L n k) = X ∧
      (∀ b, ComplexMatrix2.operatorNorm ((ξ.1 : Edge L n k 0 → ComplexMatrix2) b) ≤ 2 * τ) ∧
      ∀ (i : Fin k) (b : Edge L n k ((i : ℕ) + 1)),
        ComplexMatrix2.operatorNorm ((ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) b) ≤
          2 * τ := by
  have hU : X.fine ∈ fieldSpace L n k 0 := hX.2 0 (Nat.zero_le _)
  have hlie : ∀ g : ComplexMatrix2, ∃ H : ComplexMatrix2, g ∈ PeriodicLattice.compactGaugeGroup →
      ComplexMatrix2.operatorNorm (g - 1) ≤ τ →
      H ∈ ComplexMatrix2.hermitianTraceless ∧ ComplexMatrix2.matExp (Complex.I • H) = g ∧
        ComplexMatrix2.operatorNorm H ≤ 2 * τ := by
    intro g
    by_cases h : g ∈ PeriodicLattice.compactGaugeGroup ∧ ComplexMatrix2.operatorNorm (g - 1) ≤ τ
    · obtain ⟨H, h1, h2, h3⟩ := exists_hermitian_log hEL h.1 (by linarith [h.2])
      exact ⟨H, fun _ _ => ⟨h1, h2, h3.trans (by linarith [h.2])⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Hf hHf using hlie
  have hsu : ∀ {j : ℕ} (hj : j ≤ k) (f : Edge L n k j → ComplexMatrix2),
      (∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) →
      extendOddly f ∈ edgeFormSpace L n k j := fun hj f hf =>
    extendOddly_mem (hxor _ hj) f hf
  let A : edgeFormSpace L n k 0 := ⟨extendOddly fun b => Hf (X.fine b),
    hsu (Nat.zero_le _) _ fun b _ => (hHf _ (hU.1 b (Set.mem_univ b)) (hb b)).1⟩
  let fN : (i : Fin k) → Edge L n k ((i : ℕ) + 1) → ComplexMatrix2 := fun i c =>
    open Classical in if hc : c.IsPositivelyOriented then Hf (X.noise i ⟨c, hc⟩) else 0
  let N : (i : Fin k) → edgeFormSpace L n k ((i : ℕ) + 1) := fun i =>
    ⟨extendOddly (fN i), hsu i.2 _ fun c hc => by
      simp only [fN, dif_pos hc]
      exact (hHf _ (hX.1 i _) (hn i _)).1⟩
  refine ⟨(A, N), ?_, fun b => ?_, fun i b => ?_⟩
  · have e1 : (expMove ((A, N) : LevelForms L n k) (unitPoint L n k)).fine = X.fine := by
      funext b
      by_cases hbp : b.IsPositivelyOriented
      · simp only [expMove, unitPoint, PeriodicLattice.expTwist, if_pos hbp, mul_one, A,
          extendOddly]
        exact (hHf _ (hU.1 b (Set.mem_univ b)) (hb b)).2.1
      · have hbr := PeriodicLattice.Bond.opposite_isPositivelyOriented hbp
        simp only [expMove, unitPoint, PeriodicLattice.expTwist, if_neg hbp, if_pos hbr, mul_one,
          A, extendOddly]
        rw [(hHf _ (hU.1 _ (Set.mem_univ _)) (hb _)).2.1]
        exact (hU.2 b.opposite (Set.mem_univ _)).symm
    have e2 : (expMove ((A, N) : LevelForms L n k) (unitPoint L n k)).noise = X.noise := by
      funext i c
      simp only [expMove, unitPoint, mul_one, N, extendOddly, if_pos c.2, fN, dif_pos c.2]
      exact (hHf _ (hX.1 i _) (hn i _)).2.1
    calc expMove ((A, N) : LevelForms L n k) (unitPoint L n k) =
        ⟨(expMove ((A, N) : LevelForms L n k) (unitPoint L n k)).fine,
          (expMove ((A, N) : LevelForms L n k) (unitPoint L n k)).noise⟩ := rfl
      _ = ⟨X.fine, X.noise⟩ := by rw [e1, e2]
      _ = X := rfl
  · show ComplexMatrix2.operatorNorm ((extendOddly fun b => Hf (X.fine b)) b) ≤ _
    by_cases hbp : b.IsPositivelyOriented
    · simp only [extendOddly, if_pos hbp]
      exact (hHf _ (hU.1 b (Set.mem_univ b)) (hb b)).2.2
    · simp only [extendOddly, if_neg hbp, ComplexMatrix2.operatorNorm, norm_neg]
      exact (hHf _ (hU.1 _ (Set.mem_univ _)) (hb _)).2.2
  · show ComplexMatrix2.operatorNorm (extendOddly (fN i) b) ≤ _
    have hbd : ∀ c : Edge L n k ((i : ℕ) + 1), ComplexMatrix2.operatorNorm (fN i c) ≤ 2 * τ := by
      intro c
      by_cases hc : c.IsPositivelyOriented
      · simp only [fN, dif_pos hc]
        exact (hHf _ (hX.1 i _) (hn i _)).2.2
      · simp only [fN, dif_neg hc]
        simp only [ComplexMatrix2.operatorNorm, norm_zero]
        linarith
    by_cases hbp : b.IsPositivelyOriented
    · simp only [extendOddly, if_pos hbp]
      exact hbd b
    · simp only [extendOddly, if_neg hbp, ComplexMatrix2.operatorNorm, norm_neg]
      exact hbd _
end ExponentialCoordinates
theorem det_ne_zero_of_injective {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    {f : M →ₗ[ℝ] M} (h : Function.Injective f) : LinearMap.det f ≠ 0 := fun h0 => by
  have h1 := LinearMap.bot_lt_ker_of_det_eq_zero h0
  rw [LinearMap.ker_eq_bot.2 h] at h1
  exact lt_irrefl _ h1
theorem injective_of_det_ne_zero {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    {f : M →ₗ[ℝ] M} (h : LinearMap.det f ≠ 0) : Function.Injective f := by
  have h1 : IsUnit f := (LinearMap.isUnit_iff_isUnit_det f).2 (isUnit_iff_ne_zero.2 h)
  exact ((Module.End.isUnit_iff f).1 h1).1
theorem xor_isPositivelyOriented (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.xor_isPositivelyOriented_opposite <;> assumption
theorem ghostInvertibleAndQuadraticRightSide (hMaps : ChainMapsAtMinimizers)
    (hEnt : ChainFunctionEntriesAnalytic)
    (hFlat : UnitPointIsMinimizer)
    (hFields : MinimizerFieldsNearOne)
    (hO : SmallActionNearGaugeOrbit)
    (hC : ContourMeanGaugeCovariant)
    (hD : NormalizedMeanAtOne)
    (hAv : SmoothingNearIdentity)
    (hPo : MeanStableFields.MeanStableFieldsHold)
    (hQ : RealQuadraticTransposes.Statement)
    (hY : RealLinearMaps.RealLinearMapsStatement)
    (hE : IterLeftChartExpansion)
    (hSt : RescaledTrivialSteps)
    (hSp : FiniteSideFormSpaces)
    (hSite : FormOnAFibre.VertexFunctionsAreEuclidean.Statement)
    (hmb : PeriodicLattice.ElementaryStepFacts)
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hlat : PeriodicLattice.CoordinateDescription)
    (hEL : ComplexMatrix2.ExpLogEstimates) :
    GhostInvertibleAndQuadraticRightSide := by
  intro a ha L hL k n hk hn
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    xor_isPositivelyOriented hb hL hn
  have hlog : PeriodicLattice.LogSeriesNearOne :=
    (hmb L n 1 0 hL hn (by norm_num)).2.2.1
  have T : AveragingFacts L n k :=
    { admissible := fun i hi c hc => (hAv.1 L hL).2.2.periodic n k i hn hi c hc
      mem_polydisc := fun i hi c hc V hV =>
        ((hPo L hL k (by omega)).1 n hn).mem_polydisc i hi c hc V hV }
  obtain ⟨hDT, -⟩ := hQ L n k hL hn hk
  obtain ⟨-, hTower⟩ := hY L n k hL hn hk
  have Sp : DifferenceFacts L n k :=
    { covDiff_linear := fun U hU => hTower.covDiff_isLinear 0 (Nat.zero_le _) U hU
      covDiff_transpose := fun U hU g f => by
        obtain ⟨T', -, hK⟩ := hDT 0 (Nat.zero_le _) U hU
        exact hK.2.2 g f }
  have hA : LevelFormsEuclidean L n k := levelFormsEuclidean hSp hL hn
  have hCk : EdgeFormsEuclidean L n k k := by
    obtain ⟨-, f, -, c, h⟩ := hSp L n k k hL hn le_rfl
    exact ⟨f, c, fun B B' => by rw [h B B', Complex.ofReal_re]⟩
  have hF0 : EdgeFormsEuclidean L n k 0 := by
    obtain ⟨-, f, -, c, h⟩ := hSp L n k 0 hL hn (Nat.zero_le _)
    exact ⟨f, c, fun B B' => by rw [h B B', Complex.ofReal_re]⟩
  have h₀ : VertexFunctionsEuclidean L n k 0 := hSite L n k 0 hL hn (Nat.zero_le k)
  have hk' : VertexFunctionsEuclidean L n k k := hSite L n k k hL hn le_rfl
  obtain ⟨hread, hleast⟩ := hFlat a ha L hL k n hk hn
  have hM' := hMaps a ha L hL k n hk hn
  have fM : ChainLinearMapsAt (unitPoint L n k) := hM'.self_of_nhds _ hread _ hleast
  have hflatR : IsCompactValued (unitPoint L n k) := hleast.compact
  have hone : ∀ j ≤ k, levelField (unitPoint L n k) j = fun _ => 1 := levelField_unitPoint hD hL hn
  obtain ⟨hsmall1, hsteps⟩ := hSt L hL k hk n hn
  have hρ : 0 < polydiscRadius L :=
    lt_of_le_of_lt (norm_nonneg _)
      ((hsmall1.2 0 (by omega)).2 (PeriodicLattice.Bond.forwardFrom 0 0))
  obtain ⟨ε₁, hε₁, hNear⟩ := exists_nearUnitFacts hY hE hL hn hk hρ hflatR hone
  have hNflat : NearUnitFacts (unitPoint L n k) := hNear _ hflatR
    (fun b => by simpa [unitPoint, ComplexMatrix2.operatorNorm] using hε₁)
    (fun i c => by simpa [unitPoint, ComplexMatrix2.operatorNorm] using hε₁)
  have hit := complexBlockFieldAtLevel_trivial (L := L) (n := n) (k := k)
    fun i hi => (hsteps i hi).1
  have hsame : ∀ l : Vertex L n k 0 → ComplexMatrix2, composedCubeAverage (unitPoint L n k) k l =
      iterAdjointCubeAverage L n k (unitPoint L n k).fine k l := fun l =>
    composedCubeAverage_unitPoint hone hit l k le_rfl
  have hGinj := ghostBlockOperator_injective_unitPoint Sp hF0 hNflat fM hsame
  haveI := h₀.1
  haveI := hk'.1
  obtain ⟨τ, hτ, hGn⟩ := ghostBlockOperator_det_ne_zero_near hEnt ha hL hk hn hA hCk h₀ hk'
    (det_ne_zero_of_injective hGinj)
  set τ' : ℝ := min (τ / 2) (1 / 2) with hτ'd
  have hτ'0 : 0 < τ' := lt_min (by positivity) (by norm_num)
  set ε : ℝ := min ε₁ τ' with hεd
  have hε : 0 < ε := lt_min hε₁ hτ'0
  obtain ⟨δ, hδ, hOd⟩ := hO a ha L hL k n hk hn ε hε
  set Cc : ℝ := (Fintype.card (Face L n k 0) : ℝ) +
    a * ∑ i : Fin k, (Fintype.card (PositiveEdge L n k (i + 1)) : ℝ) * 2 with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  set ε' : ℝ := min 1 (δ / (2 * (Cc + 1))) with hε'd
  have hε' : 0 < ε' := lt_min one_pos (by positivity)
  set η : ℝ := δ ^ 2 / 8 with hηd
  have hη : 0 < η := by positivity
  haveI : NeZero (2 * L ^ n) := ⟨by
    have := hL.2
    positivity⟩
  have hev : ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
      ∀ (z : TorusFields.TorusSite (2 * L ^ n))
      (μ : Fin 4), 1 - ((V z μ : BlockAverages.UnitQuaternion) : Quaternion ℝ).re < η := by
    refine eventually_all.2 fun z => eventually_all.2 fun μ => ?_
    have hc : Continuous fun V : TorusFields.TorusField (2 * L ^ n) =>
        1 - ((V z μ : BlockAverages.UnitQuaternion) : Quaternion ℝ).re :=
      continuous_const.sub (Quaternion.continuous_re.comp (continuous_subtype_val.comp
        ((continuous_apply μ).comp (continuous_apply z))))
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    have h1 : ((TorusFields.trivialField (2 * L ^ n) z μ : BlockAverages.UnitQuaternion) :
        Quaternion ℝ) = 1 :=
      rfl
    have h2 : (1 : Quaternion ℝ).re = 1 := rfl
    simp only [h1, h2, sub_self]
    exact hη
  filter_upwards [hM', hFields a ha L hL k n hk hn ε' hε', hev] with V hV hVF hVη W hW X hLeast
  have hX : IsCompactValued X := hLeast.compact
  obtain ⟨f1, f2, f3⟩ := hVF W hW X hLeast
  have hact : chainAction a X < δ := by
    have h1 := chainAction_le ha hX (min_le_left _ _) (f1 0 (Nat.zero_le _)) f2 f3
    have h2 : Cc * ε' ≤ Cc * (δ / (2 * (Cc + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hCc0
    have h3 : Cc * (δ / (2 * (Cc + 1))) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    exact lt_of_le_of_lt (h1.trans h2) h3
  have hW1 : ∀ b, ComplexMatrix2.operatorNorm (levelField X k b - 1) < δ := fun b => by
    rw [hLeast.top_eq]
    have h1 := norm_sub_one_sq_le_of_represents hlat hL hn hW hVη b
    exact show ‖W b - 1‖ < δ from by
      have h3 : ‖W b - 1‖ ^ 2 < δ ^ 2 := by
        rw [hηd] at h1
        nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hδ.le h3
  obtain ⟨v, hvr, hv1, hvb, hvn⟩ := hOd X hX hW1 hact
  have hX'r : IsCompactValued (gaugeTransformPoint v X) :=
    gaugeTransformPoint_compact hC hL hn hX hvr
  have hXe : gaugeTransformPoint (fun x => (v x)⁻¹) (gaugeTransformPoint v X) = X :=
    gaugeTransformPoint_inv hvr
  have htop : levelField (gaugeTransformPoint v X) k = W := by
    rw [_root_.YangMills.Construction.RunningCouplingSlope.GhostQuadraticProof.levelField_gaugeTransformPoint hC hL hn hX hvr k le_rfl, hLeast.top_eq]
    funext b
    simp [PeriodicLattice.gaugeTransform, hv1]
  have hleast' : IsMinimizerOver a W (gaugeTransformPoint v X) :=
    ⟨hX'r, htop, fun Y hY hYt => by
      rw [_root_.YangMills.Construction.RunningCouplingSlope.GhostQuadraticProof.chainAction_gaugeTransformPoint hC hL hn hg a hX hvr]
      exact hLeast.le Y hY hYt⟩
  have hm' := hV W hW _ hleast'
  have hm := hV W hW X hLeast
  have hN : NearUnitFacts (gaugeTransformPoint v X) := hNear _ hX'r
    (fun b => lt_of_lt_of_le (hvb b) (min_le_left _ _))
    (fun i c => lt_of_lt_of_le (hvn i c) (min_le_left _ _))
  have hle : ε ≤ τ' := min_le_right _ _
  obtain ⟨ξ, hξ, h1, h2⟩ := exists_expMove_unitPoint hEL hxor hX'r hτ'0.le (min_le_right _ _)
    (fun b => (hvb b).le.trans hle) (fun i c => (hvn i c).le.trans hle)
  have hτ2 : 2 * τ' ≤ τ := by
    have := min_le_left (τ / 2) (1 / 2)
    linarith
  have hdet : LinearMap.det (ghostBlockOperator (gaugeTransformPoint v X)) ≠ 0 := by
    rw [← hξ]
    exact hGn ξ (fun b => (h1 b).trans hτ2) (fun i b => (h2 i b).trans hτ2)
  have hinj : Function.Injective (ghostBlockOperator X) := by
    have h3 := ghostBlockOperator_injective_gauge hC hL hn T Sp h₀ hN
      (fun x => compact_inv_mem (hvr x)) (by rw [hXe]; exact hm) hm'
      (injective_of_det_ne_zero hdet)
    rwa [hXe] at h3
  exact ⟨det_ne_zero_of_injective hinj, fun J μ => gaugedRightValue_isQuadratic hlog h₀ hX hm J μ⟩
end YangMills.Construction.RunningCouplingSlope.GhostQuadraticProof
end
