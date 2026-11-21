import YangMills.Construction.Matrices.PointwiseDerivativeRules
import YangMills.Construction.RunningCouplingSlope.FieldsAtALeastPointAreSmall
import YangMills.Construction.RunningCouplingSlope.GradientAndMultiplierAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.MapsOfTheChainAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.TheMovementsOfTheChainReadNearCellsProof
import YangMills.Construction.Towers.QuadraticFormsAndTransposesOnTheRealSpacesProof
import YangMills.Construction.Towers.TheTorusMatricesOfTheMassiveOperatorFunctionsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MinimizerGradient
open YangMills.Construction.Matrices
open YangMills.Construction.Tower
open YangMills.Construction.Tower.LeftChartFields
section Smooth
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P} {m : WithTop ℕ∞}
private theorem contDiffAt_matInv {f : P → ComplexMatrix2} (hf : ContDiffAt ℝ m f p₀)
    (h1 : IsUnit (f p₀)) : ContDiffAt ℝ m (fun p => (f p)⁻¹) p₀ := by
  have e : (fun p => (f p)⁻¹) = fun p => Ring.inverse (f p) := by
    funext p
    exact Matrix.nonsing_inv_eq_ringInverse _
  rw [e]
  obtain ⟨u, hu⟩ := h1
  have h : ContDiffAt ℝ m (Ring.inverse : ComplexMatrix2 → ComplexMatrix2) (f p₀) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact h.comp p₀ hf
private def matrixEntryCLM (a b : Fin 2) : ComplexMatrix2 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
private theorem contDiffAt_det {f : P → ComplexMatrix2} (hf : ContDiffAt ℝ m f p₀) :
    ContDiffAt ℝ m (fun p => Matrix.det (f p)) p₀ := by
  have e : (fun p => Matrix.det (f p)) = fun p =>
      matrixEntryCLM 0 0 (f p) * matrixEntryCLM 1 1 (f p) -
        matrixEntryCLM 0 1 (f p) * matrixEntryCLM 1 0 (f p) := by
    funext p
    exact Matrix.det_fin_two _
  rw [e]
  exact (((matrixEntryCLM 0 0).contDiff.contDiffAt.comp p₀ hf).mul
    ((matrixEntryCLM 1 1).contDiff.contDiffAt.comp p₀ hf)).sub
    (((matrixEntryCLM 0 1).contDiff.contDiffAt.comp p₀ hf).mul
      ((matrixEntryCLM 1 0).contDiff.contDiffAt.comp p₀ hf))
abbrev _root_.YangMills.SharedProofs.p54943 := @contDiffAt_det
private theorem contDiffAt_sqrt {f : P → ℂ} (hf : ContDiffAt ℝ m f p₀)
    (h1 : f p₀ ∈ Complex.slitPlane) : ContDiffAt ℝ m (fun p => f p ^ (1 / 2 : ℂ)) p₀ := by
  have h : ContDiffAt ℝ m (fun z : ℂ => Complex.exp (Complex.log z * (1 / 2 : ℂ))) (f p₀) := by
    have hl : ContDiffAt ℂ m Complex.log (f p₀) := Complex.contDiffAt_log h1
    exact ((Complex.contDiff_exp.contDiffAt.comp (f p₀)
      (hl.mul contDiffAt_const))).restrict_scalars ℝ
  have hc := h.comp p₀ hf
  refine hc.congr_of_eventuallyEq ?_
  have hne : ∀ᶠ p in 𝓝 p₀, f p ≠ 0 :=
    hf.continuousAt.eventually_ne (Complex.slitPlane_ne_zero h1)
  filter_upwards [hne] with p hp
  simp only [Function.comp]
  rw [Complex.cpow_def_of_ne_zero hp]
end Smooth
section Group
variable {L n k j : ℕ}
private theorem isPositivelyOriented_or_opposite {j : ℕ} (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem edge_opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
private theorem mem_fieldsIn_complex {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_fieldsIn_of_mem <;> assumption
private theorem det_eq_one_of_compact {g : ComplexMatrix2}
    (h : g ∈ PeriodicLattice.compactGaugeGroup) : Matrix.det g = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
private theorem isUnit_det_of_eq_one {g : ComplexMatrix2} (h : Matrix.det g = 1) :
    IsUnit (Matrix.det g) := by apply _root_.YangMills.SharedProofs.p11557 <;> assumption
end Group
section Real
private def IsQuaternionic (A : ComplexMatrix2) : Prop :=
  A 1 1 = (starRingEnd ℂ) (A 0 0) ∧ A 1 0 = -(starRingEnd ℂ) (A 0 1)
private theorem isQuaternionic_of_compact {A : ComplexMatrix2}
    (h : A ∈ PeriodicLattice.compactGaugeGroup) : IsQuaternionic A := by
  obtain ⟨h1, h2⟩ := Matrix.mem_specialUnitaryGroup_iff.mp h
  have hu : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp h1
  have e : Matrix.adjugate A = star A := by
    calc Matrix.adjugate A = Matrix.adjugate A * (A * star A) := by rw [hu, mul_one]
      _ = (Matrix.adjugate A * A) * star A := by rw [mul_assoc]
      _ = star A := by rw [Matrix.adjugate_mul, h2, one_smul, one_mul]
  rw [Matrix.adjugate_fin_two] at e
  have e00 := congrFun (congrFun e 0) 0
  have e10 := congrFun (congrFun e 0) 1
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at e00 e10
  refine ⟨e00, ?_⟩
  rw [neg_eq_iff_eq_neg] at e10
  rw [e10]
  simp
private theorem isQuaternionic_add {A B : ComplexMatrix2} (hA : IsQuaternionic A)
    (hB : IsQuaternionic B) : IsQuaternionic (A + B) := by
  refine ⟨?_, ?_⟩
  · simp [hA.1, hB.1]
  · simp [hA.2, hB.2]
    ring
private theorem isQuaternionic_zero : IsQuaternionic 0 := by
  refine ⟨?_, ?_⟩ <;> simp
private theorem isQuaternionic_smul (r : ℝ) {A : ComplexMatrix2} (hA : IsQuaternionic A) :
    IsQuaternionic ((r : ℂ) • A) := by
  refine ⟨?_, ?_⟩
  · simp [hA.1]
  · simp [hA.2]
private theorem compact_of_isQuaternionic {A : ComplexMatrix2} (hA : IsQuaternionic A)
    (hd : Matrix.det A = 1) : A ∈ PeriodicLattice.compactGaugeGroup := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, hd⟩
  have hdet := hd
  rw [Matrix.det_fin_two, hA.1, hA.2] at hdet
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
    linear_combination hdet
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, hA.1, hA.2]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, hA.1, hA.2]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, hA.1, hA.2]
    linear_combination hdet
private theorem inv_mem_compact {A : ComplexMatrix2} (h : A ∈ PeriodicLattice.compactGaugeGroup) :
    A⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
variable {L n k j : ℕ}
private theorem pathHolonomy_mem_compact {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy V Γ ∈ PeriodicLattice.compactGaugeGroup := by
  induction Γ with
  | nil => exact ComplexMatrix2.specialUnitary.one_mem
  | cons b Γ ih =>
    simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons] at ih ⊢
    exact ComplexMatrix2.specialUnitary.mul_mem (hV.1 b (Set.mem_univ b)) ih
abbrev _root_.YangMills.SharedProofs.p2470 := @pathHolonomy_mem_compact
private theorem normalizedMean_mem_compact [Finite (Vertex L n k j)]
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1))
    (hu : Matrix.det (normalizedMean V c) = 1) :
    normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup := by
  have hM : IsQuaternionic (contourMean V c) := by
    simp only [contourMean]
    have e : ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) =
        (((1 / 24 : ℝ) * ((L : ℝ) ^ (-4 : ℤ)) : ℝ) : ℂ) := by
      simp [PeriodicLattice.inverseFourthPowerWeight]
    rw [e]
    refine isQuaternionic_smul _ ?_
    refine finsum_mem_induction IsQuaternionic isQuaternionic_zero
      (fun _ _ => isQuaternionic_add) fun x _ => ?_
    have hs : ∀ s : Finset (Equiv.Perm (Fin 4)),
        IsQuaternionic (∑ π ∈ s, contourHolonomy V c x π) := by
      intro s
      induction s using Finset.cons_induction with
      | empty => simpa using isQuaternionic_zero
      | cons a s ha ih =>
        rw [Finset.sum_cons]
        refine isQuaternionic_add (isQuaternionic_of_compact ?_) ih
        exact ComplexMatrix2.specialUnitary.mul_mem
          (ComplexMatrix2.specialUnitary.mul_mem (pathHolonomy_mem_compact hV _)
            (pathHolonomy_mem_compact hV _))
          (inv_mem_compact (pathHolonomy_mem_compact hV _))
    exact hs _
  have hdet : Matrix.det (contourMean V c) = ((Complex.normSq (contourMean V c 0 0) +
      Complex.normSq (contourMean V c 0 1) : ℝ) : ℂ) := by
    rw [Matrix.det_fin_two, hM.1, hM.2]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    ring
  have hr : meanRadius V c = (((Complex.normSq (contourMean V c 0 0) +
      Complex.normSq (contourMean V c 0 1)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)),
      meanRadius, hdet]
    push_cast
    rfl
  have hq : IsQuaternionic (normalizedMean V c) := by
    simp only [normalizedMean]
    rw [hr, ← Complex.ofReal_inv]
    exact isQuaternionic_smul _ hM
  exact compact_of_isQuaternionic hq hu
abbrev _root_.YangMills.SharedProofs.p11178 := @normalizedMean_mem_compact
end Real
section Family
variable {L n k j : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P} {m : WithTop ℕ∞}
private theorem contDiffAt_pathHolonomy {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (Γ : List (Edge L n k j)) :
    ContDiffAt ℝ m (fun p => PeriodicLattice.pathHolonomy (V p) Γ) p₀ := by
  induction Γ with
  | nil => exact contDiffAt_const
  | cons b Γ ih =>
    simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons] at ih ⊢
    exact (hV b).mul ih
abbrev _root_.YangMills.SharedProofs.p35651 := @contDiffAt_pathHolonomy
private theorem isUnit_pathHolonomy {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (Γ : List (Edge L n k j)) :
    IsUnit (PeriodicLattice.pathHolonomy V Γ) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_det_of_eq_one (det_eq_one_of_compact (pathHolonomy_mem_compact hV Γ)))
private theorem contDiffAt_contourHolonomy {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (h1 : V p₀ ∈ fieldSpace L n k j)
    (c : Edge L n k (j + 1)) (x : Vertex L n k j) (π : Equiv.Perm (Fin 4)) :
    ContDiffAt ℝ m (fun p => contourHolonomy (V p) c x π) p₀ := by
  simp only [contourHolonomy]
  exact ((contDiffAt_pathHolonomy hV _).mul (contDiffAt_pathHolonomy hV _)).mul
    (contDiffAt_matInv (contDiffAt_pathHolonomy hV _) (isUnit_pathHolonomy h1 _))
private theorem contDiffAt_contourMean [Finite (Vertex L n k j)]
    {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (h1 : V p₀ ∈ fieldSpace L n k j)
    (c : Edge L n k (j + 1)) :
    ContDiffAt ℝ m (fun p => contourMean (V p) c) p₀ := by
  simp only [contourMean]
  have hs : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  simp only [finsum_mem_eq_finite_toFinset_sum _ hs]
  refine ContDiffAt.const_smul _ ?_
  exact ContDiffAt.sum fun x _ => ContDiffAt.sum fun π _ =>
    contDiffAt_contourHolonomy hV h1 c x π
private theorem contDiffAt_meanRadius [Finite (Vertex L n k j)]
    {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (h1 : V p₀ ∈ fieldSpace L n k j)
    (c : Edge L n k (j + 1)) (hc : Matrix.det (contourMean (V p₀) c) ∈ Complex.slitPlane) :
    ContDiffAt ℝ m (fun p => meanRadius (V p) c) p₀ :=
  contDiffAt_sqrt (contDiffAt_det (contDiffAt_contourMean hV h1 c)) hc
private theorem meanRadius_sq (V : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1)) :
    meanRadius V c ^ 2 = Matrix.det (contourMean V c) := by
  rw [meanRadius]
  simp [one_div]
private theorem meanRadius_ne_zero {V : Edge L n k j → ComplexMatrix2} {c : Edge L n k (j + 1)}
    (hs : Matrix.det (contourMean V c) ∈ Complex.slitPlane) : meanRadius V c ≠ 0 := by
  intro h
  have h2 := meanRadius_sq V c
  rw [h] at h2
  exact Complex.slitPlane_ne_zero hs (by simpa using h2.symm)
private theorem det_normalizedMean {V : Edge L n k j → ComplexMatrix2} {c : Edge L n k (j + 1)}
    (hs : Matrix.det (contourMean V c) ∈ Complex.slitPlane) :
    Matrix.det (normalizedMean V c) = 1 := by
  have h0 := meanRadius_ne_zero hs
  simp only [normalizedMean]
  rw [Matrix.det_smul, Fintype.card_fin, ← meanRadius_sq]
  field_simp
private theorem det_mem_slitPlane_of_meanRadius {V : Edge L n k j → ComplexMatrix2}
    {c : Edge L n k (j + 1)} (h : ‖meanRadius V c - 1‖ < 1 / 4) :
    Matrix.det (contourMean V c) ∈ Complex.slitPlane := by
  rw [← meanRadius_sq]
  have h1 := abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm _) h)
  have h2 := abs_lt.mp (lt_of_le_of_lt (Complex.abs_im_le_norm _) h)
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h1 h2
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  rw [sq, Complex.mul_re]
  nlinarith [h1.1, h1.2, h2.1, h2.2]
private theorem contDiffAt_normalizedMean [Finite (Vertex L n k j)]
    {V : P → Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ m (fun p => V p b) p₀) (h1 : V p₀ ∈ fieldSpace L n k j)
    (c : Edge L n k (j + 1)) (hc : Matrix.det (contourMean (V p₀) c) ∈ Complex.slitPlane) :
    ContDiffAt ℝ m (fun p => normalizedMean (V p) c) p₀ := by
  simp only [normalizedMean]
  exact ContDiffAt.smul (ContDiffAt.inv (contDiffAt_meanRadius hV h1 c hc) (meanRadius_ne_zero hc))
    (contDiffAt_contourMean hV h1 c)
private theorem normalizedMean_hasDerivAt_curve [Finite (Vertex L n k j)] [Finite (Edge L n k j)]
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1))
    (hs : Matrix.det (contourMean V c) ∈ Complex.slitPlane) :
    ∃ D : (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2,
      ∀ (g : Edge L n k j → ComplexMatrix2) (γ : ℝ → Edge L n k j → ComplexMatrix2), γ 0 = V →
        (∀ b, HasDerivAt (fun t => γ t b) (g b) 0) →
          HasDerivAt (fun t => normalizedMean (γ t) c) (D g) 0 := by
  letI : Fintype (Edge L n k j) := Fintype.ofFinite _
  have hc : ContDiffAt ℝ 1 (fun U : Edge L n k j → ComplexMatrix2 => normalizedMean U c) V :=
    contDiffAt_normalizedMean (fun b => (contDiff_pi.mp contDiff_id b).contDiffAt) hV c hs
  have hD := (hc.differentiableAt (by norm_num)).hasFDerivAt
  refine ⟨(fderiv ℝ (fun U : Edge L n k j → ComplexMatrix2 => normalizedMean U c) V :
    (Edge L n k j → ComplexMatrix2) →L[ℝ] ComplexMatrix2).toLinearMap, fun g γ h0 hg => ?_⟩
  have hp : HasDerivAt γ g 0 := hasDerivAt_pi.mpr hg
  have hD' : HasFDerivAt (fun U : Edge L n k j → ComplexMatrix2 => normalizedMean U c)
      (fderiv ℝ (fun U : Edge L n k j → ComplexMatrix2 => normalizedMean U c) V) (γ 0) := by
    rw [h0]
    exact hD
  exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hD' hp
end Family
section Fields
variable {L n k : ℕ}
private theorem levelField_succ_pos (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    levelField X (j + 1) c = X.noise ⟨j, hj⟩ ⟨c, hc⟩ * normalizedMean (levelField X j) c := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
private theorem levelField_succ_neg (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : ¬c.IsPositivelyOriented)
    (hc' : c.opposite.IsPositivelyOriented) :
    levelField X (j + 1) c =
      (X.noise ⟨j, hj⟩ ⟨c.opposite, hc'⟩ * normalizedMean (levelField X j) c.opposite)⁻¹ := by
  rw [levelField, dif_pos hj]
  simp only [fieldOfPositiveValues, dif_neg hc, dif_pos hc']
abbrev _root_.YangMills.SharedProofs.p3610 := @levelField_succ_neg
private structure TowerFacts (L n k : ℕ) : Prop where
  finiteVertex : ∀ j, j ≤ k → Finite (Vertex L n k j)
  finitePositiveEdge : ∀ j, j ≤ k → Finite (PositiveEdge L n k j)
  finiteEdge : ∀ j, j ≤ k → Finite (Edge L n k j)
  finiteFace : Finite (Face L n k 0)
  not_both_oriented : ∀ j, j ≤ k → ∀ b : Edge L n k j, b.IsPositivelyOriented →
    ¬ b.opposite.IsPositivelyOriented
  leftChart : ∀ j, j ≤ k → (finiteData L n k j).LeftExpMulMemGroup
private def DetsOffSlit (X : ChainPoint L n k) : Prop :=
  ∀ j, j < k → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    Matrix.det (contourMean (levelField X j) c) ∈ Complex.slitPlane
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {p₀ : P} {m : WithTop ℕ∞}
private theorem contDiffAt_levelField (hT : TowerFacts L n k) {X₀ : ChainPoint L n k}
    (hR : IsCompactValued X₀) (hs : DetsOffSlit X₀) {X : P → ChainPoint L n k}
    (hb : ∀ b, ContDiffAt ℝ m (fun p => (X p).fine b) p₀)
    (hn : ∀ i c, ContDiffAt ℝ m (fun p => (X p).noise i c) p₀)
    (h0 : X p₀ = X₀) : ∀ j, j ≤ k →
      ∀ b, ContDiffAt ℝ m (fun p => levelField (X p) j b) p₀ := by
  intro j
  induction j with
  | zero => exact fun _ => hb
  | succ j ih =>
    intro h
    have hj : j < k := h
    have ih1 := ih hj.le
    haveI := hT.finiteVertex j hj.le
    have hcfg : (fun p => levelField (X p) j) p₀ ∈ fieldSpace L n k j := by
      show levelField (X p₀) j ∈ _
      rw [h0]
      exact hR.2 j hj.le
    have hpos : ∀ c : Edge L n k (j + 1), ∀ hc : c.IsPositivelyOriented,
        ContDiffAt ℝ m (fun p => (X p).noise ⟨j, hj⟩ ⟨c, hc⟩ *
          normalizedMean (levelField (X p) j) c) p₀ := by
      intro c hc
      refine (hn _ _).mul (contDiffAt_normalizedMean ih1 hcfg c ?_)
      show Matrix.det (contourMean (levelField (X p₀) j) c) ∈ _
      rw [h0]
      exact hs j hj c hc
    intro c
    by_cases hc : c.IsPositivelyOriented
    · have e : (fun p => levelField (X p) (j + 1) c) = fun p => (X p).noise ⟨j, hj⟩ ⟨c, hc⟩ *
          normalizedMean (levelField (X p) j) c := by
        funext p
        exact levelField_succ_pos _ hj c hc
      rw [e]
      exact hpos c hc
    · have hc' : c.opposite.IsPositivelyOriented :=
        (isPositivelyOriented_or_opposite c).resolve_left hc
      have e : (fun p => levelField (X p) (j + 1) c) = fun p =>
          ((X p).noise ⟨j, hj⟩ ⟨c.opposite, hc'⟩ *
            normalizedMean (levelField (X p) j) c.opposite)⁻¹ := by
        funext p
        exact levelField_succ_neg _ hj c hc hc'
      rw [e]
      refine contDiffAt_matInv (hpos c.opposite hc') ?_
      show IsUnit ((X p₀).noise ⟨j, hj⟩ ⟨c.opposite, hc'⟩ *
        normalizedMean (levelField (X p₀) j) c.opposite)
      rw [h0, ← levelField_succ_pos X₀ hj c.opposite hc']
      exact (Matrix.isUnit_iff_isUnit_det _).mpr
        (isUnit_det_of_eq_one (det_eq_one_of_compact ((hR.2 (j + 1) hj).1 _ (Set.mem_univ _))))
private theorem contDiffAt_meanRadius_level (hT : TowerFacts L n k) {X₀ : ChainPoint L n k}
    (hR : IsCompactValued X₀) (hs : DetsOffSlit X₀) {X : P → ChainPoint L n k}
    (hb : ∀ b, ContDiffAt ℝ m (fun p => (X p).fine b) p₀)
    (hn : ∀ i c, ContDiffAt ℝ m (fun p => (X p).noise i c) p₀)
    (h0 : X p₀ = X₀) {i : ℕ} (hi : i < k) (c : Edge L n k (i + 1))
    (hc : c.IsPositivelyOriented) :
    ContDiffAt ℝ m (fun p => meanRadius (levelField (X p) i) c) p₀ := by
  haveI := hT.finiteVertex i hi.le
  refine contDiffAt_meanRadius (contDiffAt_levelField hT hR hs hb hn h0 i hi.le) ?_ c ?_
  · show levelField (X p₀) i ∈ _
    rw [h0]
    exact hR.2 i hi.le
  · show Matrix.det (contourMean (levelField (X p₀) i) c) ∈ _
    rw [h0]
    exact hs i hi c hc
private theorem contDiffAt_matExp_I {f : P → ComplexMatrix2} (hf : ContDiffAt ℝ m f p₀) :
    ContDiffAt ℝ m (fun p => ComplexMatrix2.matExp (Complex.I • f p)) p₀ := by
  have h : ContDiffAt ℝ m (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2)
      (Complex.I • f p₀) :=
    ((NormedSpace.exp_analytic (𝕂 := ℂ) (Complex.I • f p₀)).contDiffAt).restrict_scalars ℝ
  exact h.comp p₀ (hf.const_smul Complex.I)
abbrev _root_.YangMills.SharedProofs.p25406 := @contDiffAt_matExp_I
private theorem matExp_I_zero : ComplexMatrix2.matExp (Complex.I • (0 : ComplexMatrix2)) = 1 := by
  rw [smul_zero]
  exact NormedSpace.exp_zero
end Fields
section Curves
private theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
private theorem hasDerivAt_expFlow (X : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • (t • X))) (Complex.I • X) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • X) (0 : ℝ)
  have e : (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • (t • X))) =
      fun t : ℝ => NormedSpace.exp (t • Complex.I • X) := by
    funext t
    congr 1
    rw [smul_comm]
  rw [e]
  simpa using h
abbrev _root_.YangMills.SharedProofs.p9756 := @hasDerivAt_expFlow
private theorem expFlow_zero (X : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • ((0 : ℝ) • X)) = 1 := by
  rw [zero_smul, smul_zero]
  exact NormedSpace.exp_zero
abbrev _root_.YangMills.SharedProofs.p11429 := @expFlow_zero
variable {L n k j : ℕ}
private def linkVelocity (V M : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    ComplexMatrix2 :=
  open Classical in
  if b.IsPositivelyOriented then Complex.I • M b * V b else V b * (Complex.I • M b)
private theorem det_of_mem_fieldsIn {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (b : Edge L n k j) :
    Matrix.det (V b) = 1 := hV.1 b (Set.mem_univ b)
private theorem inv_opposite_of_mem_fieldsIn {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (b : Edge L n k j) :
    (V b.opposite)⁻¹ = V b := by
  rw [hV.2 b (Set.mem_univ b)]
  exact Matrix.nonsing_inv_nonsing_inv _
    (by rw [det_of_mem_fieldsIn hV b]; exact isUnit_one)
abbrev _root_.YangMills.SharedProofs.p4213 := @inv_opposite_of_mem_fieldsIn
private theorem hasDerivAt_expTwist {V M : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hM : ∀ b, M b.opposite = -M b) (b : Edge L n k j) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.expTwist (t • M) V b) (linkVelocity V M b) 0 := by
  by_cases hb : b.IsPositivelyOriented
  · have e : (fun t : ℝ => PeriodicLattice.expTwist (t • M) V b) =
        fun t : ℝ => ComplexMatrix2.matExp (Complex.I • (t • M b)) * V b := by
      funext t
      simp only [PeriodicLattice.expTwist, if_pos hb, Pi.smul_apply]
    rw [e]
    simp only [linkVelocity, if_pos hb]
    exact (hasDerivAt_expFlow _).mul_const (V b)
  · have e : (fun t : ℝ => PeriodicLattice.expTwist (t • M) V b) =
        fun t : ℝ => V b * ComplexMatrix2.matExp (Complex.I • (t • M b)) := by
      funext t
      simp only [PeriodicLattice.expTwist, if_neg hb, Pi.smul_apply]
      rw [Matrix.mul_inv_rev, inv_opposite_of_mem_fieldsIn hV, matExp_inv, hM b]
      congr 2
      simp
    rw [e]
    simp only [linkVelocity, if_neg hb]
    simpa using (hasDerivAt_expFlow (M b)).const_mul (V b)
abbrev _root_.YangMills.DeltaSharedProofs.p350 := @hasDerivAt_expTwist
private theorem expTwist_zero {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist (0 : Edge L n k j → ComplexMatrix2) V = V := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [PeriodicLattice.expTwist, if_pos hb, Pi.zero_apply]
    rw [matExp_I_zero, one_mul]
  · simp only [PeriodicLattice.expTwist, if_neg hb, Pi.zero_apply]
    rw [matExp_I_zero, one_mul, inv_opposite_of_mem_fieldsIn hV]
abbrev _root_.YangMills.SharedProofs.p57400 := @expTwist_zero
private theorem hasDerivAt_inv_of_det_one
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {W : ℝ → ComplexMatrix2} {W' : ComplexMatrix2} (hW : HasDerivAt W W' 0)
    (h0 : Matrix.det (W 0) = 1) :
    HasDerivAt (fun t => (W t)⁻¹) (-((W 0)⁻¹ * W' * (W 0)⁻¹)) 0 := by
  have hu : IsUnit (Matrix.det (W 0)) := by rw [h0]; exact isUnit_one
  have hZ : HasDerivAt (fun t => W t * (W 0)⁻¹) (W' * (W 0)⁻¹) 0 := hW.mul_const _
  have h1 := (hd.1 univ (fun t => W t * (W 0)⁻¹) (fun t => W t * (W 0)⁻¹)
    (fun t => W t * (W 0)⁻¹) _ _ _ Filter.univ_mem hZ hZ hZ).2.1
    (Matrix.mul_nonsing_inv _ hu)
  have h2 := h1.2.1.const_mul (W 0)⁻¹
  have e : (fun t => (W t)⁻¹) = fun t => (W 0)⁻¹ * (W t * (W 0)⁻¹)⁻¹ := by
    funext t
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, ← mul_assoc,
      Matrix.nonsing_inv_mul _ hu, one_mul]
  rw [e]
  refine h2.congr_deriv ?_
  rw [mul_neg, mul_assoc]
abbrev _root_.YangMills.SharedProofs.p36414 := @hasDerivAt_inv_of_det_one
end Curves
section Movement
variable {L n k : ℕ}
private theorem extendOddly_opposite (hT : TowerFacts L n k) {j : ℕ} (hj : j ≤ k)
    (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by
  by_cases hb : b.IsPositivelyOriented
  · have hb' := hT.not_both_oriented j hj b hb
    simp only [extendOddly, if_pos hb, if_neg hb', edge_opposite_opposite]
  · have hb' : b.opposite.IsPositivelyOriented :=
      (isPositivelyOriented_or_opposite b).resolve_left hb
    simp only [extendOddly, if_pos hb', if_neg hb, neg_neg]
private theorem tangentTransport_succ_pos (X : ChainPoint L n k) (ξ : LevelForms L n k) {j : ℕ}
    (hj : j < k) (c : Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    tangentTransport X ξ (j + 1) c = ComplexMatrix2.conjugateBy (X.noise ⟨j, hj⟩ ⟨c, hc⟩)
        (leftDifferential normalizedMean (levelField X j) (tangentTransport X ξ j) c) +
      (ξ.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) c := by apply _root_.YangMills.SharedProofs.p457 <;> assumption
private theorem tangentTransport_opposite (hT : TowerFacts L n k) (X : ChainPoint L n k)
    (ξ : LevelForms L n k) : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      tangentTransport X ξ j b.opposite = -tangentTransport X ξ j b := by
  intro j hj b
  cases j with
  | zero => exact ξ.1.2.2 b
  | succ j =>
    have hj' : j < k := hj
    rw [tangentTransport, dif_pos hj']
    exact extendOddly_opposite hT hj _ b
private theorem levelField_succ_opposite (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : Edge L n k (j + 1)) (hc : ¬c.IsPositivelyOriented)
    (hc' : c.opposite.IsPositivelyOriented) :
    levelField X (j + 1) c = (levelField X (j + 1) c.opposite)⁻¹ := by
  rw [levelField_succ_neg X hj c hc hc', levelField_succ_pos X hj c.opposite hc']
private theorem expMove_zero {X : ChainPoint L n k}
    (hX : X.fine ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup) (η : LevelForms L n k) :
    expMove ((0 : ℝ) • η) X = X := by
  have e1 : (expMove ((0 : ℝ) • η) X).fine = X.fine := by
    simp only [expMove, zero_smul, Prod.fst_zero, ZeroMemClass.coe_zero]
    exact expTwist_zero hX
  have e2 : (expMove ((0 : ℝ) • η) X).noise = X.noise := by
    funext i c
    simp only [expMove, zero_smul, Prod.snd_zero, Pi.zero_apply, ZeroMemClass.coe_zero]
    rw [matExp_I_zero, one_mul]
  calc expMove ((0 : ℝ) • η) X =
        ⟨(expMove ((0 : ℝ) • η) X).fine, (expMove ((0 : ℝ) • η) X).noise⟩ := rfl
    _ = ⟨X.fine, X.noise⟩ := by rw [e1, e2]
    _ = X := rfl
abbrev _root_.YangMills.SharedProofs.p18865 := @expMove_zero
private theorem transport_identity (n u D ν : ComplexMatrix2) (hn : n⁻¹ * n = 1)
    (hu : u⁻¹ * u = 1) :
    Complex.I • (ComplexMatrix2.conjugateBy n (Complex.I⁻¹ • (D * u⁻¹)) + ν) * (n * u) =
      (Complex.I • ν * n) * u + n * D := by
  have h1 : Complex.I • ComplexMatrix2.conjugateBy n (Complex.I⁻¹ • (D * u⁻¹)) =
      n * (D * u⁻¹) * n⁻¹ := by
    simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
  rw [smul_add, add_mul, h1]
  have h2 : n * (D * u⁻¹) * n⁻¹ * (n * u) = n * D := by
    calc n * (D * u⁻¹) * n⁻¹ * (n * u) = n * D * u⁻¹ * (n⁻¹ * n) * u := by
          simp only [mul_assoc]
      _ = n * D * (u⁻¹ * u) := by rw [hn, mul_one, mul_assoc]
      _ = n * D := by rw [hu, mul_one]
  rw [h2, add_comm]
  simp only [mul_assoc]
abbrev _root_.YangMills.SharedProofs.p26677 := @transport_identity
private theorem leftDifferential_eq (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {j : ℕ} {V M : Edge L n k j → ComplexMatrix2} {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) {D : ComplexMatrix2}
    (h2 : HasDerivAt (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist (t • M) V) c) D 0)
    (h0 : normalizedMean (PeriodicLattice.expTwist ((0 : ℝ) • M) V) c = normalizedMean V c)
    (hu : Matrix.det (normalizedMean V c) = 1) :
    leftDifferential normalizedMean V M c = Complex.I⁻¹ • (D * (normalizedMean V c)⁻¹) := by
  simp only [leftDifferential, extendOddly, if_pos hc, logDirectionalDeriv]
  congr 1
  have hX : HasDerivAt (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist (t • M) V) c *
      (normalizedMean V c)⁻¹) (D * (normalizedMean V c)⁻¹) 0 := h2.mul_const _
  have h1 : (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist (t • M) V) c *
      (normalizedMean V c)⁻¹) 0 = 1 := by
    simp only
    rw [h0]
    exact Matrix.mul_nonsing_inv _ (isUnit_det_of_eq_one hu)
  have hlog := ((hd.1 univ _ _ _ _ _ _ Filter.univ_mem hX hX hX).2.1 h1).2.2.1
  have e : (fun t : ℝ => ComplexMatrix2.logSeries (normalizedMean (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ t • M) V) c * (normalizedMean V c)⁻¹)) =
      fun t : ℝ => ComplexMatrix2.logSeries (normalizedMean (PeriodicLattice.expTwist (t • M) V) c *
        (normalizedMean V c)⁻¹) := by
    funext t
    rw [algebraMap_smul]
  rw [e]
  exact hlog.deriv
abbrev _root_.YangMills.SharedProofs.p13783 := @leftDifferential_eq
private theorem hasDerivAt_levelField_expMove
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n k) {X : ChainPoint L n k}
    (hX : IsCompactValued X) (hs : DetsOffSlit X) (η : LevelForms L n k) : ∀ j, j ≤ k → ∀ b,
      HasDerivAt (fun t : ℝ => levelField (expMove (t • η) X) j b)
        (linkVelocity (levelField X j) (tangentTransport X η j) b) 0 := by
  have hX0 : X.fine ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup :=
    mem_fieldsIn_complex (hX.2 0 (Nat.zero_le _))
  have hY0 := expMove_zero hX0 η
  intro j
  induction j with
  | zero =>
    intro _ b
    exact hasDerivAt_expTwist hX0 η.1.2.2 b
  | succ j ih =>
    intro h
    have hj : j < k := h
    have ih' := ih hj.le
    have hWc := mem_fieldsIn_complex (hX.2 j hj.le)
    have hMa := tangentTransport_opposite hT X η j hj.le
    have hW1 : ∀ c : Edge L n k (j + 1), Matrix.det (levelField X (j + 1) c) = 1 :=
      det_of_mem_fieldsIn (mem_fieldsIn_complex (hX.2 (j + 1) hj))
    have pos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        HasDerivAt (fun t : ℝ => levelField (expMove (t • η) X) (j + 1) c)
          (Complex.I • tangentTransport X η (j + 1) c * levelField X (j + 1) c) 0 := by
      intro c hc
      haveI := hT.finiteVertex j hj.le
      haveI := hT.finiteEdge j hj.le
      have hu := det_normalizedMean (hs j hj c hc)
      obtain ⟨D, hD⟩ := normalizedMean_hasDerivAt_curve (hX.2 j hj.le) c (hs j hj c hc)
      have h1 := hD _ (fun t => levelField (expMove (t • η) X) j) (by simp only [hY0]) ih'
      have h0 : PeriodicLattice.expTwist ((0 : ℝ) • tangentTransport X η j) (levelField X j) =
          levelField X j := by
        rw [zero_smul]
        exact expTwist_zero hWc
      have h2 := hD _ (fun t => PeriodicLattice.expTwist (t • tangentTransport X η j)
        (levelField X j)) h0 (fun b => hasDerivAt_expTwist hWc hMa b)
      have hmd := leftDifferential_eq hd hc h2 (by rw [h0]) hu
      have hn : HasDerivAt (fun t : ℝ => (expMove (t • η) X).noise ⟨j, hj⟩ ⟨c, hc⟩)
          (Complex.I • (η.2 ⟨j, hj⟩ : Edge L n k (j + 1) → ComplexMatrix2) c *
            X.noise ⟨j, hj⟩ ⟨c, hc⟩) 0 :=
        (hasDerivAt_expFlow _).mul_const _
      have hp := hn.mul h1
      have e : (fun t : ℝ => levelField (expMove (t • η) X) (j + 1) c) =
          fun t : ℝ => (expMove (t • η) X).noise ⟨j, hj⟩ ⟨c, hc⟩ *
            normalizedMean (levelField (expMove (t • η) X) j) c := by
        funext t
        exact levelField_succ_pos _ hj c hc
      rw [e]
      refine hp.congr_deriv ?_
      simp only [hY0]
      rw [tangentTransport_succ_pos X η hj c hc, levelField_succ_pos X hj c hc, hmd]
      exact (transport_identity _ _ _ _
        (Matrix.nonsing_inv_mul _ (isUnit_det_of_eq_one (det_eq_one_of_compact (hX.1 _ _))))
        (Matrix.nonsing_inv_mul _ (isUnit_det_of_eq_one hu))).symm
    intro b
    by_cases hb : b.IsPositivelyOriented
    · simp only [linkVelocity, if_pos hb]
      exact pos b hb
    · have hb' : b.opposite.IsPositivelyOriented :=
        (isPositivelyOriented_or_opposite b).resolve_left hb
      have e : (fun t : ℝ => levelField (expMove (t • η) X) (j + 1) b) =
          fun t : ℝ => (levelField (expMove (t • η) X) (j + 1) b.opposite)⁻¹ := by
        funext t
        exact levelField_succ_opposite _ hj b hb hb'
      rw [e]
      have hdet : Matrix.det ((fun t : ℝ => levelField (expMove (t • η) X) (j + 1) b.opposite) 0)
          = 1 := by
        simp only [hY0]
        exact hW1 _
      refine (hasDerivAt_inv_of_det_one hd (pos b.opposite hb') hdet).congr_deriv ?_
      simp only [hY0, linkVelocity, if_neg hb]
      rw [levelField_succ_opposite X hj b hb hb', tangentTransport_opposite hT X η (j + 1) hj b]
      have hA : levelField X (j + 1) b.opposite * (levelField X (j + 1) b.opposite)⁻¹ = 1 :=
        Matrix.mul_nonsing_inv _ (isUnit_det_of_eq_one (hW1 _))
      simp only [smul_neg, mul_neg, neg_mul, neg_neg]
      rw [mul_assoc ((levelField X (j + 1) b.opposite)⁻¹), mul_assoc (Complex.I • _), hA, mul_one]
end Movement
section RealPoints
variable {L n k j : ℕ}
private theorem expTwist_mem_fieldSpace (hT : TowerFacts L n k) (hj : j ≤ k)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (M : edgeFormSpace L n k j) (t : ℝ) :
    PeriodicLattice.expTwist (t • (M : Edge L n k j → ComplexMatrix2)) V ∈ fieldSpace L n k j := by
  have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • ((t • (M : Edge L n k j → ComplexMatrix2)) b)) * V b ∈
        PeriodicLattice.compactGaugeGroup := by
    intro b hb
    have h := ((hT.leftChart j hj).1 V hV (M : Edge L n k j → ComplexMatrix2) M.2 ⟨b, hb⟩).1 t
    have e : ((t : ℂ) • (M : Edge L n k j → ComplexMatrix2) b) =
        (t • (M : Edge L n k j → ComplexMatrix2)) b :=
      Complex.coe_smul _ _
    simp only [leftExpMul, LatticeData.onPositive, finiteData] at h
    rwa [e] at h
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb]
      exact hpos b hb
    · simp only [PeriodicLattice.expTwist, if_neg hb]
      exact inv_mem_compact (hpos _ ((isPositivelyOriented_or_opposite b).resolve_left hb))
  · by_cases hb : b.IsPositivelyOriented
    · have hb' := hT.not_both_oriented j hj b hb
      simp only [PeriodicLattice.expTwist, if_pos hb, if_neg hb', edge_opposite_opposite]
    · have hb' : b.opposite.IsPositivelyOriented :=
        (isPositivelyOriented_or_opposite b).resolve_left hb
      simp only [PeriodicLattice.expTwist, if_pos hb', if_neg hb]
      rw [Matrix.nonsing_inv_nonsing_inv _
        (isUnit_det_of_eq_one (det_eq_one_of_compact (hpos _ hb')))]
private theorem linkVelocity_add (V M M' : Edge L n k j → ComplexMatrix2) :
    linkVelocity V (M + M') = linkVelocity V M + linkVelocity V M' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [linkVelocity, if_pos hb, Pi.add_apply, smul_add, add_mul]
  · simp only [linkVelocity, if_neg hb, Pi.add_apply, smul_add, mul_add]
abbrev _root_.YangMills.DeltaSharedProofs.p501277 := @linkVelocity_add
private theorem linkVelocity_smul (V M : Edge L n k j → ComplexMatrix2) (r : ℝ) :
    linkVelocity V (r • M) = r • linkVelocity V M := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [linkVelocity, if_pos hb, Pi.smul_apply]
    rw [smul_comm, smul_mul_assoc]
  · simp only [linkVelocity, if_neg hb, Pi.smul_apply]
    rw [smul_comm, mul_smul_comm]
abbrev _root_.YangMills.DeltaSharedProofs.p500676 := @linkVelocity_smul
private theorem isUnit_det_compact {g : ComplexMatrix2}
    (h : g ∈ PeriodicLattice.compactGaugeGroup) : IsUnit (Matrix.det g) := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem matExp_I_mem_compact (hEL : ComplexMatrix2.ExpLogEstimates) {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.matExp_I_smul_mem_compact <;> assumption
private theorem isCompactValued_of_detsOffSlit (hT : TowerFacts L n k) {X : ChainPoint L n k}
    (hn : ∀ i c, X.noise i c ∈ PeriodicLattice.compactGaugeGroup)
    (hb : X.fine ∈ fieldSpace L n k 0) (hs : DetsOffSlit X) : IsCompactValued X := by
  refine ⟨hn, fun j => ?_⟩
  induction j with
  | zero => exact fun _ => hb
  | succ j ih =>
    intro h
    have hj : j < k := h
    have h1 := ih hj.le
    haveI := hT.finiteVertex j hj.le
    have hpos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        levelField X (j + 1) c ∈ PeriodicLattice.compactGaugeGroup := by
      intro c hc
      have hu := det_normalizedMean (hs j hj c hc)
      rw [levelField_succ_pos _ hj c hc]
      exact ComplexMatrix2.specialUnitary.mul_mem (hn _ _) (normalizedMean_mem_compact h1 c hu)
    have hreal : ∀ c : Edge L n k (j + 1),
        levelField X (j + 1) c ∈ PeriodicLattice.compactGaugeGroup := by
      intro c
      by_cases hc : c.IsPositivelyOriented
      · exact hpos c hc
      · have hc' := (isPositivelyOriented_or_opposite c).resolve_left hc
        rw [levelField_succ_opposite _ hj c hc hc']
        exact inv_mem_compact (hpos _ hc')
    refine ⟨fun b _ => hreal b, fun b _ => ?_⟩
    by_cases hb' : b.IsPositivelyOriented
    · have hb'' := hT.not_both_oriented (j + 1) hj b hb'
      have hbr := (isPositivelyOriented_or_opposite b.opposite).resolve_left hb''
      rw [levelField_succ_opposite _ hj _ hb'' hbr, edge_opposite_opposite]
    · have hbr := (isPositivelyOriented_or_opposite b).resolve_left hb'
      rw [levelField_succ_opposite _ hj b hb' hbr,
        Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_compact (hreal _))]
private theorem eventually_detsOffSlit_expMove (hT : TowerFacts L n k) {X : ChainPoint L n k}
    (hR : IsCompactValued X) (hs : DetsOffSlit X) (η : LevelForms L n k) :
    ∀ᶠ t in 𝓝 (0 : ℝ), DetsOffSlit (expMove (t • η) X) := by
  have hX0 : X.fine ∈ fieldSpace L n k 0 := hR.2 0 (Nat.zero_le _)
  have hXc := mem_fieldsIn_complex hX0
  have hY0 : expMove ((0 : ℝ) • η) X = X := expMove_zero hXc η
  have hsm : ∀ A : ComplexMatrix2,
      ContDiffAt ℝ 1 (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • (t • A))) 0 :=
    fun A => contDiffAt_matExp_I (contDiffAt_id.smul contDiffAt_const)
  have hb : ∀ b, ContDiffAt ℝ 1 (fun t : ℝ => (expMove (t • η) X).fine b) 0 := by
    intro b
    by_cases hb : b.IsPositivelyOriented
    · simp only [expMove, PeriodicLattice.expTwist, if_pos hb, Prod.smul_fst, Submodule.coe_smul,
        Pi.smul_apply]
      exact (hsm _).mul contDiffAt_const
    · simp only [expMove, PeriodicLattice.expTwist, if_neg hb, Prod.smul_fst, Submodule.coe_smul,
        Pi.smul_apply]
      refine contDiffAt_matInv ((hsm _).mul contDiffAt_const) ?_
      simp only [expFlow_zero, one_mul]
      exact (Matrix.isUnit_iff_isUnit_det _).mpr
        (isUnit_det_of_eq_one (det_eq_one_of_compact (hX0.1 _ (Set.mem_univ _))))
  have hn : ∀ i c, ContDiffAt ℝ 1 (fun t : ℝ => (expMove (t • η) X).noise i c) 0 := by
    intro i c
    simp only [expMove, Prod.smul_snd, Pi.smul_apply, Submodule.coe_smul]
    exact (hsm _).mul contDiffAt_const
  have hF := contDiffAt_levelField hT hR hs hb hn hY0
  have h : ∀ j ∈ Finset.range k, ∀ᶠ t in 𝓝 (0 : ℝ), ∀ c : Edge L n k (j + 1),
      c.IsPositivelyOriented →
      Matrix.det (contourMean (levelField (expMove (t • η) X) j) c) ∈ Complex.slitPlane := by
    intro j hj
    have hj' : j < k := Finset.mem_range.mp hj
    haveI := hT.finiteVertex j hj'.le
    haveI := hT.finiteEdge (j + 1) hj'
    refine Filter.eventually_all.mpr fun c => ?_
    by_cases hc : c.IsPositivelyOriented
    · have hcfg : (fun t : ℝ => levelField (expMove (t • η) X) j) 0 ∈ fieldSpace L n k j := by
        show levelField (expMove ((0 : ℝ) • η) X) j ∈ _
        rw [hY0]
        exact hR.2 j hj'.le
      have h1 := (contDiffAt_det (contDiffAt_contourMean (hF j hj'.le) hcfg c)).continuousAt
      have h2 : Matrix.det (contourMean (levelField (expMove ((0 : ℝ) • η) X) j) c) ∈
          Complex.slitPlane := by
        rw [hY0]
        exact hs j hj' c hc
      filter_upwards [h1.eventually_mem (Complex.isOpen_slitPlane.mem_nhds h2)] with t ht _
      exact ht
    · exact Filter.Eventually.of_forall fun t h' => absurd h' hc
  filter_upwards [(Filter.eventually_all_finset _).mpr h] with t ht j hj c hc
  exact ht j (Finset.mem_range.mpr hj) c hc
end RealPoints
section Action
variable {L n k j : ℕ}
private theorem contDiffAt_chainAction (hT : TowerFacts L n k) {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {p₀ : P} {m : WithTop ℕ∞} {X₀ : ChainPoint L n k} (hR : IsCompactValued X₀)
    (hs : DetsOffSlit X₀) {X : P → ChainPoint L n k}
    (hb : ∀ b, ContDiffAt ℝ m (fun p => (X p).fine b) p₀)
    (hn : ∀ i c, ContDiffAt ℝ m (fun p => (X p).noise i c) p₀)
    (h0 : X p₀ = X₀) (a : ℝ) :
    ContDiffAt ℝ m (fun p => chainAction a (X p)) p₀ := by
  letI hFq : ∀ i : Fin k, Fintype (PositiveEdge L n k ((i : ℕ) + 1)) := fun i =>
    @Fintype.ofFinite _ (hT.finitePositiveEdge _ i.2)
  letI hFp : Fintype (Face L n k 0) := @Fintype.ofFinite _ hT.finiteFace
  have rtC : ∀ {f : P → ComplexMatrix2}, ContDiffAt ℝ m f p₀ →
      ContDiffAt ℝ m (fun p => (ComplexMatrix2.halfTrace (f p)).re) p₀ := by
    intro f hf
    let T : ComplexMatrix2 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      { toFun := fun A => (ComplexMatrix2.halfTrace A).re
        map_add' := fun A B => by
          simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_add, mul_add]
        map_smul' := fun r A => by
          have e : r • A = (r : ℂ) • A := (Complex.coe_smul r A).symm
          simp only [RingHom.id_apply, smul_eq_mul, ComplexMatrix2.halfTrace,
            ComplexMatrix2.fullTrace]
          rw [e, Matrix.trace_smul, smul_eq_mul, mul_left_comm, Complex.re_ofReal_mul] }
    exact T.contDiff.contDiffAt.comp p₀ hf
  have e : (fun p => chainAction a (X p)) = fun p =>
      (∑ q : Face L n k 0, (1 - (ComplexMatrix2.halfTrace
        (PeriodicLattice.pathHolonomy (X p).fine q.boundaryBonds)).re)) +
      a * ∑ i : Fin k, ∑ c : PositiveEdge L n k ((i : ℕ) + 1),
        (meanRadius (levelField (X p) i) c.1).re *
          (1 - (ComplexMatrix2.halfTrace ((X p).noise i c)).re) := by
    funext p
    simp only [chainAction, plaquetteAction, PeriodicLattice.wilsonAction,
      finsum_eq_sum_of_fintype, PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteHolonomy,
      traceDefect]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    simp [ComplexMatrix2.halfTrace, Complex.mul_re]
  rw [e]
  refine ContDiffAt.add (ContDiffAt.sum fun q _ => ?_) (contDiffAt_const.mul
    (ContDiffAt.sum fun i _ => ContDiffAt.sum fun c _ => ?_))
  · exact contDiffAt_const.sub (rtC (contDiffAt_pathHolonomy hb _))
  · exact (Complex.reCLM.contDiff.contDiffAt.comp p₀
      (contDiffAt_meanRadius_level hT hR hs hb hn h0 i.2 c.1 c.2)).mul
      (contDiffAt_const.sub (rtC (hn i c)))
private abbrev Coords (L n k : ℕ) : Type :=
  (Edge L n k 0 → ComplexMatrix2) × ((i : Fin k) → PositiveEdge L n k ((i : ℕ) + 1) → ComplexMatrix2)
end Action
section Pairing
variable {ι : Type*} [Finite ι]
private theorem tracePairing_add_left (f f' g : ι → ComplexMatrix2) :
    traceFinsumPairing (f + f') g = traceFinsumPairing f g + traceFinsumPairing f' g := by apply _root_.YangMills.Construction.Tower.RealQuadraticTransposes.tracePair_add_left <;> assumption
private theorem tracePairing_comm (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = traceFinsumPairing g f := by apply _root_.YangMills.Construction.Tower.RealQuadraticTransposes.tracePair_comm <;> assumption
private theorem tracePairing_smul_left (r : ℝ) (f g : ι → ComplexMatrix2) :
    traceFinsumPairing (r • f) g = (r : ℂ) * traceFinsumPairing f g := by
  unfold traceFinsumPairing
  rw [mul_finsum]
  refine finsum_congr fun i => ?_
  simp only [Pi.smul_apply, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  rw [show (r • f i) = (r : ℂ) • f i from (Complex.coe_smul r (f i)).symm, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  ring
abbrev _root_.YangMills.SharedProofs.p655 := @tracePairing_smul_left
private theorem tracePairing_zero_right (f : ι → ComplexMatrix2) :
    traceFinsumPairing f (0 : ι → ComplexMatrix2) = 0 := by
  simp [traceFinsumPairing, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
private theorem tracePairing_add_right (f g g' : ι → ComplexMatrix2) :
    traceFinsumPairing f (g + g') = traceFinsumPairing f g + traceFinsumPairing f g' := by
  rw [tracePairing_comm, tracePairing_add_left, tracePairing_comm g, tracePairing_comm g']
private theorem tracePairing_self (hI : FaceSums.PairingIsInner ↥(univ : Set ι))
    (g : ι → ComplexMatrix2) (hg : ∀ i, g i ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (traceFinsumPairing g g).re ∧ ((traceFinsumPairing g g).re = 0 → g = 0) := by
  obtain ⟨c, hc⟩ := hI.2
  let f : FaceSums.finSuppLieFields ↥(univ : Set ι) :=
    ⟨fun p => g p.1, fun p => hg p.1, Set.toFinite _⟩
  have e := hc f f
  have e' : traceFinsumPairing (f : ↥(univ : Set ι) → ComplexMatrix2)
      (f : ↥(univ : Set ι) → ComplexMatrix2) = traceFinsumPairing g g := by
    unfold Tower.traceFinsumPairing
    exact finsum_comp_equiv (Equiv.Set.univ ι)
      (f := fun b => ComplexMatrix2.halfTrace (g b * g b))
  rw [e'] at e
  have hre : (traceFinsumPairing g g).re = c.inner f f := by rw [← e]; simp
  refine ⟨?_, fun h => ?_⟩
  · rw [hre]
    exact c.re_inner_nonneg f
  · have z : c.inner f f = 0 := by rw [← hre, h]
    have f0 : f = 0 := c.definite f z
    funext p
    exact congrFun (congrArg Subtype.val f0) ⟨p, trivial⟩
abbrev _root_.YangMills.SharedProofs.p120809 := @tracePairing_self
end Pairing
section Forms
variable {L n k j : ℕ}
private theorem orientation_cases (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem edgeForm_eq_zero_of_restrict {B : Edge L n k j → ComplexMatrix2}
    (h : B ∈ edgeFormSpace L n k j) (h0 : restrictToPositiveEdges B = 0) : B = 0 := by
  funext b
  rcases orientation_cases b with hb | hb
  · exact congrFun h0 ⟨b, hb⟩
  · have e : B b = -B b.opposite := by rw [h.2 b, neg_neg]
    have e' : B b.opposite = 0 := congrFun h0 ⟨b.opposite, hb⟩
    rw [e, e']
    simp
abbrev _root_.YangMills.SharedProofs.p27961 := @edgeForm_eq_zero_of_restrict
end Forms
private theorem exists_linear_representative {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F] (p : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hp : ∀ x, p x x = 0 → x = 0)
    (φ : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) : ∃ T : F →ₗ[ℝ] E, ∀ f e, p (T f) e = φ f e := by
  have hinj : Function.Injective p := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact hp x (by rw [hx]; rfl)
  have hfr : Module.finrank ℝ E = Module.finrank ℝ (E →ₗ[ℝ] ℝ) :=
    (Subspace.dual_finrank_eq (K := ℝ) (V := E)).symm
  let e := LinearMap.linearEquivOfInjective p hinj hfr
  refine ⟨e.symm.toLinearMap ∘ₗ φ, fun f x => ?_⟩
  have h := e.apply_symm_apply (φ f)
  exact congrArg (fun g : E →ₗ[ℝ] ℝ => g x) h
abbrev _root_.YangMills.SharedProofs.p13845 := @exists_linear_representative
section Chain
variable {L n k : ℕ} {j : ℕ}
private theorem edgePairing_add_left [Finite (PositiveEdge L n k j)]
    (X X' Y : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing (X + X') Y = edgeFormPairing X Y + edgeFormPairing X' Y :=
  tracePairing_add_left _ _ _
private theorem edgePairing_add_right [Finite (PositiveEdge L n k j)]
    (X Y Y' : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing X (Y + Y') = edgeFormPairing X Y + edgeFormPairing X Y' :=
  tracePairing_add_right _ _ _
private theorem edgePairing_smul_left [Finite (PositiveEdge L n k j)] (r : ℝ)
    (X Y : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing (r • X) Y = (r : ℂ) * edgeFormPairing X Y :=
  tracePairing_smul_left _ _ _
private theorem edgePairing_comm [Finite (PositiveEdge L n k j)]
    (X Y : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing X Y = edgeFormPairing Y X :=
  tracePairing_comm _ _
private theorem edgePairing_zero_right [Finite (PositiveEdge L n k j)]
    (X : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing X (0 : Edge L n k j → ComplexMatrix2) = 0 :=
  tracePairing_zero_right _
private theorem edgePairing_self [Finite (PositiveEdge L n k j)]
    (hI : FaceSums.PairingIsInner ↥(univ : Set (PositiveEdge L n k j)))
    (B : edgeFormSpace L n k j) :
    0 ≤ (edgeFormPairing (B : Edge L n k j → ComplexMatrix2) B).re ∧
      ((edgeFormPairing (B : Edge L n k j → ComplexMatrix2) B).re = 0 → B = 0) := by
  obtain ⟨h1, h2⟩ := tracePairing_self hI
    (restrictToPositiveEdges (B : Edge L n k j → ComplexMatrix2)) fun b => B.2.1 b.1 b.2
  refine ⟨h1, fun h => Subtype.ext (edgeForm_eq_zero_of_restrict B.2 (h2 h))⟩
abbrev _root_.YangMills.SharedProofs.p90865 := @edgePairing_self
variable [hF0 : Finite (PositiveEdge L n k 0)]
  [hF : ∀ i : Fin k, Finite (PositiveEdge L n k ((i : ℕ) + 1))]
private theorem levelPairing_add_left (ξ ξ' η : LevelForms L n k) :
    levelPairing (formValues (ξ + ξ')) (formValues η) =
      levelPairing (formValues ξ) (formValues η) + levelPairing (formValues ξ') (formValues η) := by
  simp only [levelPairing, formValues, Prod.fst_add, Prod.snd_add, Submodule.coe_add,
    Pi.add_apply]
  rw [edgePairing_add_left, Complex.add_re]
  simp only [edgePairing_add_left, Complex.add_re, Finset.sum_add_distrib]
  ring
abbrev _root_.YangMills.SharedProofs.p57549 := @levelPairing_add_left
private theorem levelPairing_smul_left (r : ℝ) (ξ η : LevelForms L n k) :
    levelPairing (formValues (r • ξ)) (formValues η) =
      r * levelPairing (formValues ξ) (formValues η) := by
  simp only [levelPairing, formValues, Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul,
    Pi.smul_apply]
  rw [edgePairing_smul_left]
  simp only [edgePairing_smul_left, Complex.re_ofReal_mul, mul_add, Finset.mul_sum]
abbrev _root_.YangMills.SharedProofs.p29192 := @levelPairing_smul_left
private theorem levelPairing_comm (ξ η : LevelForms L n k) :
    levelPairing (formValues ξ) (formValues η) = levelPairing (formValues η) (formValues ξ) := by
  simp only [levelPairing, formValues]
  rw [edgePairing_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [edgePairing_comm]
abbrev _root_.YangMills.SharedProofs.p11971 := @levelPairing_comm
private def levelForm : LevelForms L n k →ₗ[ℝ] LevelForms L n k →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun ξ η => levelPairing (formValues ξ) (formValues η)) levelPairing_add_left
    (fun r ξ η => by rw [levelPairing_smul_left, smul_eq_mul])
    (fun ξ η η' => by
      rw [levelPairing_comm, levelPairing_add_left, levelPairing_comm η, levelPairing_comm η'])
    (fun r ξ η => by rw [levelPairing_comm, levelPairing_smul_left, levelPairing_comm η,
      smul_eq_mul])
private theorem levelForm_apply (ξ η : LevelForms L n k) :
    levelForm ξ η = levelPairing (formValues ξ) (formValues η) := rfl
private theorem levelForm_definite
    (hI0 : FaceSums.PairingIsInner ↥(univ : Set (PositiveEdge L n k 0)))
    (hI : ∀ i : Fin k, FaceSums.PairingIsInner
      ↥(univ : Set (PositiveEdge L n k ((i : ℕ) + 1))))
    (ξ : LevelForms L n k) (h : levelForm ξ ξ = 0) : ξ = 0 := by
  rw [levelForm_apply] at h
  simp only [levelPairing, formValues] at h
  have h0 := (edgePairing_self hI0 ξ.1).1
  have hi := fun i => (edgePairing_self (hI i) (ξ.2 i)).1
  have hs : 0 ≤ ∑ i : Fin k,
      (edgeFormPairing (ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) (ξ.2 i)).re :=
    Finset.sum_nonneg fun i _ => hi i
  have e0 : (edgeFormPairing (ξ.1 : Edge L n k 0 → ComplexMatrix2) ξ.1).re = 0 := by linarith
  have es : ∑ i : Fin k,
      (edgeFormPairing (ξ.2 i : Edge L n k ((i : ℕ) + 1) → ComplexMatrix2) (ξ.2 i)).re = 0 := by
    linarith
  have ei := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hi i).mp es
  refine Prod.ext ((edgePairing_self hI0 ξ.1).2 e0) (funext fun i => ?_)
  exact (edgePairing_self (hI i) (ξ.2 i)).2 (ei i (Finset.mem_univ i))
end Chain
section Fibre
variable {L n m : ℕ}
private def withTopNoise (Y : ChainPoint L n (m + 1))
    (ν : PositiveEdge L n (m + 1) (m + 1) → ComplexMatrix2) : ChainPoint L n (m + 1) :=
  ⟨Y.fine, fun i => Fin.lastCases
    (motive := fun i : Fin (m + 1) => PositiveEdge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2) ν
    (fun i' => Y.noise (Fin.castSucc i')) i⟩
private theorem withTopNoise_last (Y : ChainPoint L n (m + 1))
    (ν : PositiveEdge L n (m + 1) (m + 1) → ComplexMatrix2)
    (c : PositiveEdge L n (m + 1) (m + 1)) :
    (withTopNoise Y ν).noise (Fin.last m) c = ν c := by
  simp [withTopNoise]
private theorem withTopNoise_castSucc (Y : ChainPoint L n (m + 1))
    (ν : PositiveEdge L n (m + 1) (m + 1) → ComplexMatrix2) (i : Fin m)
    (c : PositiveEdge L n (m + 1) ((i : ℕ) + 1)) :
    (withTopNoise Y ν).noise (Fin.castSucc i) c = Y.noise (Fin.castSucc i) c := by
  simp [withTopNoise]
private theorem levelField_withTopNoise (Y : ChainPoint L n (m + 1))
    (ν : PositiveEdge L n (m + 1) (m + 1) → ComplexMatrix2) :
    ∀ j, j ≤ m → levelField (withTopNoise Y ν) j = levelField Y j := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro h
    have hj : j < m + 1 := by omega
    have hjm : j < m := h
    have hpos : ∀ c : Edge L n (m + 1) (j + 1), c.IsPositivelyOriented →
        levelField (withTopNoise Y ν) (j + 1) c = levelField Y (j + 1) c := by
      intro c hc
      rw [levelField_succ_pos _ hj c hc, levelField_succ_pos _ hj c hc, ih hjm.le]
      exact congrArg (· * _) (withTopNoise_castSucc Y ν ⟨j, hjm⟩ ⟨c, hc⟩)
    funext c
    by_cases hc : c.IsPositivelyOriented
    · exact hpos c hc
    · have hc' := (isPositivelyOriented_or_opposite c).resolve_left hc
      rw [levelField_succ_opposite _ hj c hc hc', levelField_succ_opposite Y hj c hc hc',
        hpos _ hc']
abbrev _root_.YangMills.DeltaSharedProofs.p501532 := @levelField_withTopNoise
private theorem fibre_identity {a b D : ComplexMatrix2} (ha : a⁻¹ * a = 1) (hb : b * b⁻¹ = 1) :
    Complex.I • (-(ComplexMatrix2.conjugateBy a (Complex.I⁻¹ • (D * b⁻¹)))) * a =
      (a * b) * (-(b⁻¹ * D * b⁻¹)) := by
  have h1 : Complex.I • ComplexMatrix2.conjugateBy a (Complex.I⁻¹ • (D * b⁻¹)) =
      a * (D * b⁻¹) * a⁻¹ := by
    simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
  rw [smul_neg, h1, neg_mul, mul_neg]
  congr 1
  calc a * (D * b⁻¹) * a⁻¹ * a = a * (D * b⁻¹) * (a⁻¹ * a) := by simp only [mul_assoc]
    _ = a * (D * b⁻¹) := by rw [ha, mul_one]
    _ = a * ((b * b⁻¹) * D * b⁻¹) := by rw [hb, one_mul]
    _ = a * b * (b⁻¹ * D * b⁻¹) := by simp only [mul_assoc]
abbrev _root_.YangMills.SharedProofs.p6296 := @fibre_identity
private def topNoiseTangent (ν : edgeFormSpace L n (m + 1) (m + 1)) : LevelForms L n (m + 1) :=
  (0, Pi.single (Fin.last m) ν)
private theorem exists_chainAction_derivative (hT : TowerFacts L n (m + 1)) (a : ℝ)
    {X : ChainPoint L n (m + 1)} (hR : IsCompactValued X) (hs : DetsOffSlit X) :
    ∃ Lf : Coords L n (m + 1) → ℝ,
      (∀ (Y : ℝ → ChainPoint L n (m + 1)) (v : Coords L n (m + 1)), Y 0 = X →
        (∀ b, HasDerivAt (fun t => (Y t).fine b) (v.1 b) 0) →
        (∀ i c, HasDerivAt (fun t => (Y t).noise i c) (v.2 i c) 0) →
        HasDerivAt (fun t => chainAction a (Y t)) (Lf v) 0) ∧
      (∀ v v', Lf (v + v') = Lf v + Lf v') ∧ ∀ (r : ℝ) v, Lf (r • v) = r • Lf v := by
  letI hFb : Fintype (Edge L n (m + 1) 0) :=
    @Fintype.ofFinite _ (hT.finiteEdge 0 (Nat.zero_le _))
  letI hFq : ∀ i : Fin (m + 1), Fintype (PositiveEdge L n (m + 1) ((i : ℕ) + 1)) := fun i =>
    @Fintype.ofFinite _ (hT.finitePositiveEdge _ i.2)
  let toPt : Coords L n (m + 1) → ChainPoint L n (m + 1) := fun p => ⟨p.1, p.2⟩
  let p₀ : Coords L n (m + 1) := (X.fine, X.noise)
  have hb : ∀ b, ContDiffAt ℝ 1 (fun p : Coords L n (m + 1) => (toPt p).fine b) p₀ := fun b =>
    ContDiff.contDiffAt (by simp only [toPt]; fun_prop)
  have hn : ∀ i c, ContDiffAt ℝ 1 (fun p : Coords L n (m + 1) => (toPt p).noise i c) p₀ :=
    fun i c => ((contDiff_pi.mp ((contDiff_pi.mp contDiff_snd) i)) c).contDiffAt
  have h0 : toPt p₀ = X := rfl
  have hA := contDiffAt_chainAction hT hR hs hb hn h0 a
  have hD := (hA.differentiableAt (by norm_num)).hasFDerivAt
  set D := fderiv ℝ (fun p => chainAction a (toPt p)) p₀ with hDd
  refine ⟨fun v => D v, fun Y v hY hb' hn' => ?_, fun v v' => map_add D v v',
    fun r v => map_smul D r v⟩
  have hp : HasDerivAt (fun t => (((Y t).fine, (Y t).noise) : Coords L n (m + 1))) v 0 :=
    (hasDerivAt_pi.mpr hb').prodMk
      (hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun c => hn' i c)
  have hD' : HasFDerivAt (fun p => chainAction a (toPt p)) D
      (((Y 0).fine, (Y 0).noise) : Coords L n (m + 1)) := by
    rw [hY]
    exact hD
  exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hD' hp
end Fibre
section Zero
variable {L n m : ℕ}
set_option maxHeartbeats 1000000 in
private theorem leftDeriv_fibre_eq_zero
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n (m + 1)) (hEL : ComplexMatrix2.ExpLogEstimates)
    {a : ℝ} {X : ChainPoint L n (m + 1)} (hX : IsCompactValued X) (hs : DetsOffSlit X)
    (hleast : ∀ X' : ChainPoint L n (m + 1), IsCompactValued X' →
      levelField X' (m + 1) = levelField X (m + 1) → chainAction a X ≤ chainAction a X')
    {Lf : Coords L n (m + 1) → ℝ}
    (hLf : ∀ (Y : ℝ → ChainPoint L n (m + 1)) (v : Coords L n (m + 1)), Y 0 = X →
      (∀ b, HasDerivAt (fun t => (Y t).fine b) (v.1 b) 0) →
      (∀ i c, HasDerivAt (fun t => (Y t).noise i c) (v.2 i c) 0) →
      HasDerivAt (fun t => chainAction a (Y t)) (Lf v) 0)
    (η₀ : LevelForms L n (m + 1)) (hη₀ : η₀.2 (Fin.last m) = 0)
    (M₀ : edgeFormSpace L n (m + 1) (m + 1))
    (hM₀ : (M₀ : Edge L n (m + 1) (m + 1) → ComplexMatrix2) = tangentTransport X η₀ (m + 1)) :
    leftDeriv (chainAction a) X (η₀ - topNoiseTangent M₀) = 0 := by
  have hm : m < m + 1 := Nat.lt_succ_self m
  have hX0 : X.fine ∈ fieldSpace L n (m + 1) 0 := hX.2 0 (Nat.zero_le _)
  have hXc := mem_fieldsIn_complex hX0
  have hY0 := expMove_zero hXc η₀
  set Y : ℝ → ChainPoint L n (m + 1) := fun t => expMove (t • η₀) X with hY
  have hvel := hasDerivAt_levelField_expMove hd hT hX hs η₀
  have hoff : ∀ᶠ t in 𝓝 (0 : ℝ), DetsOffSlit (Y t) := eventually_detsOffSlit_expMove hT hX hs η₀
  have hYreal : ∀ᶠ t in 𝓝 (0 : ℝ), IsCompactValued (Y t) := by
    filter_upwards [hoff] with t ht
    refine isCompactValued_of_detsOffSlit hT (fun i c => ?_) ?_ ht
    · refine ComplexMatrix2.specialUnitary.mul_mem (matExp_I_mem_compact hEL ?_) (hX.1 i c)
      exact ComplexMatrix2.hermitianTraceless.smul_mem t ((η₀.2 i).2.1 c.1 c.2)
    · exact expTwist_mem_fieldSpace hT (Nat.zero_le _) hX0 η₀.1 t
  set W := levelField X (m + 1) with hW
  have hWc : W ∈ fieldSpace L n (m + 1) (m + 1) := hX.2 _ le_rfl
  let ν : ℝ → PositiveEdge L n (m + 1) (m + 1) → ComplexMatrix2 := fun t c =>
    W c.1 * (normalizedMean (levelField (Y t) m) c.1)⁻¹
  let Γ : ℝ → ChainPoint L n (m + 1) := fun t => withTopNoise (Y t) (ν t)
  haveI := hT.finiteVertex m hm.le
  haveI := hT.finiteEdge m hm.le
  have hΓ : ∀ᶠ t in 𝓝 (0 : ℝ), IsCompactValued (Γ t) ∧ levelField (Γ t) (m + 1) = W := by
    filter_upwards [hYreal, hoff] with t ht hn
    have hVm := ht.2 m hm.le
    have hu : ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented →
        normalizedMean (levelField (Y t) m) c ∈ PeriodicLattice.compactGaugeGroup := by
      intro c hc
      exact normalizedMean_mem_compact hVm c (det_normalizedMean (hn m hm c hc))
    have hpos : ∀ c : Edge L n (m + 1) (m + 1), c.IsPositivelyOriented →
        levelField (Γ t) (m + 1) c = W c := by
      intro c hc
      rw [levelField_succ_pos _ hm c hc, levelField_withTopNoise _ _ m le_rfl]
      have e : (Γ t).noise ⟨m, hm⟩ ⟨c, hc⟩ =
          W c * (normalizedMean (levelField (Y t) m) c)⁻¹ :=
        withTopNoise_last (Y t) (ν t) ⟨c, hc⟩
      rw [e, mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_compact (hu c hc)), mul_one]
    have htop : levelField (Γ t) (m + 1) = W := by
      funext c
      by_cases hc : c.IsPositivelyOriented
      · exact hpos c hc
      · have hc' := (isPositivelyOriented_or_opposite c).resolve_left hc
        rw [levelField_succ_opposite _ hm c hc hc', hpos _ hc', hWc.2 c (Set.mem_univ _)]
        exact Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_compact (hWc.1 c (Set.mem_univ _)))
    refine ⟨⟨fun i c => ?_, fun j hj => ?_⟩, htop⟩
    · induction i using Fin.lastCases with
      | last =>
        show (withTopNoise (Y t) (ν t)).noise (Fin.last m) c ∈ _
        rw [withTopNoise_last]
        exact ComplexMatrix2.specialUnitary.mul_mem (hWc.1 _ (Set.mem_univ _)) (inv_mem_compact (hu _ c.2))
      | cast i =>
        show (withTopNoise (Y t) (ν t)).noise (Fin.castSucc i) c ∈ _
        rw [withTopNoise_castSucc]
        exact ht.1 _ c
    · rcases Nat.lt_or_eq_of_le hj with h | h
      · rw [levelField_withTopNoise _ _ j (Nat.lt_succ_iff.mp h)]
        exact ht.2 j h.le
      · subst h
        rw [htop]
        exact hWc
  have hmin : ∀ᶠ t in 𝓝 (0 : ℝ), chainAction a X ≤ chainAction a (Γ t) := by
    filter_upwards [hΓ] with t ht
    exact hleast _ ht.1 ht.2
  set η' : LevelForms L n (m + 1) := η₀ - topNoiseTangent M₀ with hη'
  have hZ0 : Y 0 = X := hY0
  let v : Coords L n (m + 1) := (linkVelocity X.fine η₀.1, fun i c =>
    Complex.I • (η'.2 i : Edge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2) c.1 * X.noise i c)
  have hη'1 : η'.1 = η₀.1 := by simp [hη', topNoiseTangent]
  have hη'c : ∀ i : Fin m, η'.2 (Fin.castSucc i) = η₀.2 (Fin.castSucc i) := by
    intro i
    simp [hη', topNoiseTangent, Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne]
  have hη'l : η'.2 (Fin.last m) = -M₀ := by
    simp [hη', topNoiseTangent, hη₀]
  have h2 := hLf (fun t => expMove (t • η') X) v (expMove_zero hXc η')
    (fun b => by
      show HasDerivAt _ (linkVelocity X.fine η₀.1 b) 0
      rw [← hη'1]
      exact hasDerivAt_expTwist hXc η'.1.2.2 b)
    (fun i c => (hasDerivAt_expFlow _).mul_const _)
  have hXm := mem_fieldsIn_complex (hX.2 m hm.le)
  have hwc : ∀ c : PositiveEdge L n (m + 1) (m + 1),
      normalizedMean (levelField X m) c.1 ∈ PeriodicLattice.compactGaugeGroup ∧
      W c.1 = X.noise (Fin.last m) c * normalizedMean (levelField X m) c.1 := by
    intro c
    exact ⟨normalizedMean_mem_compact (hX.2 m hm.le) c.1 (det_normalizedMean (hs m hm c.1 c.2)),
      levelField_succ_pos X hm c.1 c.2⟩
  have hΓ0 : Γ 0 = X := by
    have e1 : (Γ 0).fine = X.fine := by
      show (Y 0).fine = X.fine
      rw [hZ0]
    have e2 : (Γ 0).noise = X.noise := by
      funext i c
      induction i using Fin.lastCases with
      | last =>
        show (withTopNoise (Y 0) (ν 0)).noise (Fin.last m) c = _
        rw [withTopNoise_last]
        show W c.1 * (normalizedMean (levelField (Y 0) m) c.1)⁻¹ = _
        rw [hZ0, (hwc c).2, mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det_compact (hwc c).1),
          mul_one]
      | cast i =>
        show (withTopNoise (Y 0) (ν 0)).noise (Fin.castSucc i) c = _
        rw [withTopNoise_castSucc, hZ0]
    calc Γ 0 = ⟨(Γ 0).fine, (Γ 0).noise⟩ := rfl
      _ = ⟨X.fine, X.noise⟩ := by rw [e1, e2]
      _ = X := rfl
  have hlast : ∀ c : PositiveEdge L n (m + 1) (m + 1), HasDerivAt
      (fun t => (Γ t).noise (Fin.last m) c) (v.2 (Fin.last m) c) 0 := by
    intro c
    have hu := det_normalizedMean (hs m hm c.1 c.2)
    obtain ⟨D, hD⟩ := normalizedMean_hasDerivAt_curve (hX.2 m hm.le) c.1 (hs m hm c.1 c.2)
    have h1' := hD _ (fun t => levelField (Y t) m) (by simp only [hZ0])
      (fun b => hvel m hm.le b)
    have h0 : PeriodicLattice.expTwist ((0 : ℝ) • tangentTransport X η₀ m) (levelField X m) =
        levelField X m := by
      rw [zero_smul]
      exact expTwist_zero hXm
    have h2' := hD _ (fun t => PeriodicLattice.expTwist (t • tangentTransport X η₀ m)
      (levelField X m)) h0
      (fun b => hasDerivAt_expTwist hXm (tangentTransport_opposite hT X η₀ m hm.le) b)
    have hmd := leftDifferential_eq hd c.2 h2' (by rw [h0]) hu
    have hdet : Matrix.det ((fun t => normalizedMean (levelField (Y t) m) c.1) 0) = 1 := by
      simp only [hZ0]
      exact hu
    have hinv := hasDerivAt_inv_of_det_one hd h1' hdet
    have hν := hinv.const_mul (W c.1)
    have e : (fun t => (Γ t).noise (Fin.last m) c) = fun t =>
        W c.1 * (normalizedMean (levelField (Y t) m) c.1)⁻¹ := by
      funext t
      exact withTopNoise_last (Y t) (ν t) c
    rw [e]
    refine hν.congr_deriv ?_
    simp only [hZ0]
    have hMc : (M₀ : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1 =
        ComplexMatrix2.conjugateBy (X.noise (Fin.last m) c)
          (Complex.I⁻¹ • (D (linkVelocity (levelField X m) (tangentTransport X η₀ m)) *
            (normalizedMean (levelField X m) c.1)⁻¹)) := by
      rw [hM₀]
      have hm1 := tangentTransport_succ_pos X η₀ hm c.1 c.2
      rw [hmd] at hm1
      have hz : (η₀.2 ⟨m, hm⟩ : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1 = 0 := by
        have : η₀.2 ⟨m, hm⟩ = 0 := hη₀
        rw [this]
        rfl
      rw [hz, add_zero] at hm1
      exact hm1
    have hv2 : v.2 (Fin.last m) c =
        Complex.I • (-(M₀ : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1) *
          X.noise (Fin.last m) c := by
      have e5 : (η'.2 (Fin.last m)).1 c.1 = -(M₀ : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1 := by
        rw [hη'l]
        rfl
      rw [← e5]
    rw [hv2, hMc, (hwc c).2]
    have hna : (X.noise (Fin.last m) c)⁻¹ * X.noise (Fin.last m) c = 1 :=
      Matrix.nonsing_inv_mul _ (isUnit_det_compact (hX.1 (Fin.last m) c))
    have hub : normalizedMean (levelField X m) c.1 * (normalizedMean (levelField X m) c.1)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (isUnit_det_compact (hwc c).1)
    exact (fibre_identity hna hub).symm
  have h1 := hLf Γ v hΓ0
    (fun b => hasDerivAt_expTwist hXc η₀.1.2.2 b)
    (fun i c => by
      induction i using Fin.lastCases with
      | last => exact hlast c
      | cast i =>
        have e : (fun t => (Γ t).noise (Fin.castSucc i) c) =
            fun t => (Y t).noise (Fin.castSucc i) c := by
          funext t
          exact withTopNoise_castSucc (Y t) (ν t) i c
        rw [e]
        show HasDerivAt _ (Complex.I • (η'.2 (Fin.castSucc i) :
          Edge L n (m + 1) (((Fin.castSucc i : Fin (m + 1)) : ℕ) + 1) → ComplexMatrix2) c.1 *
            X.noise _ c) 0
        rw [hη'c]
        exact (hasDerivAt_expFlow _).mul_const _)
  have hmin' : IsLocalMin (fun t => chainAction a (Γ t)) 0 := by
    filter_upwards [hmin] with t ht
    simp only [hΓ0]
    exact ht
  have hz := hmin'.hasDerivAt_eq_zero h1
  rw [leftDeriv, h2.deriv, hz]
end Zero
section Lagrange
variable {L n m : ℕ}
private theorem leftDifferential_zero (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {j : ℕ} {V : Edge L n (m + 1) j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n (m + 1) j PeriodicLattice.complexGaugeGroup)
    {c : Edge L n (m + 1) (j + 1)} (hc : c.IsPositivelyOriented)
    (hu : Matrix.det (normalizedMean V c) = 1) :
    leftDifferential normalizedMean V (0 : Edge L n (m + 1) j → ComplexMatrix2) c = 0 := by
  have h0 : ∀ t : ℝ,
      PeriodicLattice.expTwist (t • (0 : Edge L n (m + 1) j → ComplexMatrix2)) V = V := by
    intro t
    rw [smul_zero]
    exact expTwist_zero hV
  have h2 : HasDerivAt (fun t : ℝ => normalizedMean (PeriodicLattice.expTwist
      (t • (0 : Edge L n (m + 1) j → ComplexMatrix2)) V) c) 0 0 := by
    simp only [h0]
    exact hasDerivAt_const _ _
  rw [leftDifferential_eq hd hc h2 (by rw [h0]) hu]
  simp
abbrev _root_.YangMills.SharedProofs.p6898 := @leftDifferential_zero
private theorem tangentTransport_topNoiseTangent
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n (m + 1))
    {X : ChainPoint L n (m + 1)} (hX : IsCompactValued X) (hs : DetsOffSlit X)
    (ν : edgeFormSpace L n (m + 1) (m + 1)) :
    tangentTransport X (topNoiseTangent ν) (m + 1) = ν := by
  have hm : m < m + 1 := Nat.lt_succ_self m
  have hpos : ∀ (j : ℕ) (hj : j < m + 1), tangentTransport X (topNoiseTangent ν) j = 0 →
      ∀ c : Edge L n (m + 1) (j + 1), ∀ hc : c.IsPositivelyOriented,
        tangentTransport X (topNoiseTangent ν) (j + 1) c =
          ((topNoiseTangent ν).2 ⟨j, hj⟩ : Edge L n (m + 1) (j + 1) → ComplexMatrix2) c := by
    intro j hj h0 c hc
    have hu := det_normalizedMean (hs j hj c hc)
    rw [tangentTransport_succ_pos X _ hj c hc, h0,
      leftDifferential_zero hd (mem_fieldsIn_complex (hX.2 j hj.le)) hc hu]
    simp [ComplexMatrix2.conjugateBy]
  have hlow : ∀ j, j ≤ m → tangentTransport X (topNoiseTangent ν) j = 0 := by
    intro j
    induction j with
    | zero => exact fun _ => rfl
    | succ j ih =>
      intro h
      have hj : j < m + 1 := by omega
      have hz : ∀ c : Edge L n (m + 1) (j + 1), c.IsPositivelyOriented →
          tangentTransport X (topNoiseTangent ν) (j + 1) c = 0 := by
        intro c hc
        rw [hpos j hj (ih (by omega)) c hc]
        have hne : (⟨j, hj⟩ : Fin (m + 1)) ≠ Fin.last m := by
          intro h'
          have := congrArg Fin.val h'
          simp at this
          omega
        simp only [topNoiseTangent]
        rw [Pi.single_eq_of_ne hne]
        rfl
      funext c
      by_cases hc : c.IsPositivelyOriented
      · exact hz c hc
      · have hc' := (isPositivelyOriented_or_opposite c).resolve_left hc
        have e := tangentTransport_opposite hT X (topNoiseTangent ν) (j + 1) (by omega) c.opposite
        rw [edge_opposite_opposite] at e
        rw [e, hz _ hc']
        simp
  have hp := hpos m hm (hlow m le_rfl)
  funext c
  by_cases hc : c.IsPositivelyOriented
  · rw [hp c hc]
    show ((topNoiseTangent ν).2 (Fin.last m)).1 c = _
    simp only [topNoiseTangent, Pi.single_eq_same]
  · have hc' := (isPositivelyOriented_or_opposite c).resolve_left hc
    have e := tangentTransport_opposite hT X (topNoiseTangent ν) (m + 1) le_rfl c.opposite
    rw [edge_opposite_opposite] at e
    have e2 := ν.2.2 c.opposite
    rw [edge_opposite_opposite] at e2
    rw [e, hp _ hc', e2]
    show -((topNoiseTangent ν).2 (Fin.last m)).1 c.opposite = _
    simp only [topNoiseTangent, Pi.single_eq_same]
private theorem levelForm_topNoiseTangent [Finite (PositiveEdge L n (m + 1) 0)]
    [∀ i : Fin (m + 1), Finite (PositiveEdge L n (m + 1) ((i : ℕ) + 1))]
    (J : LevelForms L n (m + 1)) (ν : edgeFormSpace L n (m + 1) (m + 1)) :
    levelForm J (topNoiseTangent ν) = (edgeFormPairing (J.2 (Fin.last m)).1
      (ν : Edge L n (m + 1) (m + 1) → ComplexMatrix2)).re := by
  rw [levelForm_apply]
  simp only [levelPairing, formValues, topNoiseTangent]
  have e0 : ((0 : edgeFormSpace L n (m + 1) 0) : Edge L n (m + 1) 0 → ComplexMatrix2) = 0 := rfl
  rw [e0, edgePairing_zero_right]
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi]
    have e1 : ((0 : edgeFormSpace L n (m + 1) ((i : ℕ) + 1)) :
        Edge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2) = 0 := rfl
    rw [e1, edgePairing_zero_right]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h
private theorem isTopMultiplier_of_minimizer
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hT : TowerFacts L n (m + 1)) (hEL : ComplexMatrix2.ExpLogEstimates)
    {a : ℝ} {X : ChainPoint L n (m + 1)} (hX : IsCompactValued X) (hs : DetsOffSlit X)
    (hleast : ∀ X' : ChainPoint L n (m + 1), IsCompactValued X' →
      levelField X' (m + 1) = levelField X (m + 1) → chainAction a X ≤ chainAction a X')
    (hMaps : ChainLinearMapsAt X)
    {Lf : Coords L n (m + 1) → ℝ}
    (hLf : ∀ (Y : ℝ → ChainPoint L n (m + 1)) (v : Coords L n (m + 1)), Y 0 = X →
      (∀ b, HasDerivAt (fun t => (Y t).fine b) (v.1 b) 0) →
      (∀ i c, HasDerivAt (fun t => (Y t).noise i c) (v.2 i c) 0) →
      HasDerivAt (fun t => chainAction a (Y t)) (Lf v) 0)
    {J : LevelForms L n (m + 1)} (hJ : IsLevelGradient (chainAction a) X J) :
    IsTopMultiplier X J (J.2 (Fin.last m)) := by
  haveI : Finite (PositiveEdge L n (m + 1) 0) := hT.finitePositiveEdge 0 (Nat.zero_le _)
  haveI : ∀ i : Fin (m + 1), Finite (PositiveEdge L n (m + 1) ((i : ℕ) + 1)) :=
    fun i => hT.finitePositiveEdge _ i.2
  haveI : Finite (PositiveEdge L n (m + 1) (m + 1)) := hT.finitePositiveEdge _ le_rfl
  set T := topDeriv X with hTd
  have hTv : ∀ ξ, (T ξ : Edge L n (m + 1) (m + 1) → ComplexMatrix2) =
      tangentTransport X ξ (m + 1) := hMaps.topDeriv_spec
  have hTop : ∀ ξ, (topDeriv X ξ : Edge L n (m + 1) (m + 1) → ComplexMatrix2) = T ξ :=
    fun ξ => rfl
  have hTi : ∀ ν, T (topNoiseTangent ν) = ν := fun ν =>
    Subtype.ext (by rw [hTv]; exact tangentTransport_topNoiseTangent hd hT hX hs ν)
  intro η
  set μ : edgeFormSpace L n (m + 1) (m + 1) := J.2 (Fin.last m) with hμ
  set ηl : edgeFormSpace L n (m + 1) (m + 1) := η.2 (Fin.last m) with hηl
  set η₀ : LevelForms L n (m + 1) := η - topNoiseTangent ηl with hη₀
  have h0 : η₀.2 (Fin.last m) = 0 := by
    simp [hη₀, topNoiseTangent, hηl]
  set M₀ := T η₀ with hM₀
  have hz := leftDeriv_fibre_eq_zero hd hT hEL hX hs hleast hLf η₀ h0 M₀ (hTv η₀)
  have hz' : levelForm J (η₀ - topNoiseTangent M₀) = 0 := by
    rw [levelForm_apply, hJ, hz]
  have hsum : η = η₀ + topNoiseTangent ηl := by simp [hη₀]
  have e1 : levelPairing (formValues J) (formValues η) = levelForm J η := rfl
  have e2 : levelForm J η = levelForm J η₀ + levelForm J (topNoiseTangent ηl) := by
    rw [← map_add, ← hsum]
  have e3 : levelForm J η₀ = levelForm J (topNoiseTangent M₀) := by
    rw [map_sub, sub_eq_zero] at hz'
    exact hz'
  have e4 : T η = M₀ + ηl := by
    have e5 : T η = T η₀ + T (topNoiseTangent ηl) := by rw [← map_add, ← hsum]
    rw [e5, hTi]
  rw [e1, e2, e3, levelForm_topNoiseTangent, levelForm_topNoiseTangent, hTop, e4,
    Submodule.coe_add, edgePairing_add_right, Complex.add_re]
end Lagrange
section Final
variable {L n m : ℕ}
private theorem exists_levelGradient (hT : TowerFacts L n (m + 1))
    [Finite (PositiveEdge L n (m + 1) 0)]
    [∀ i : Fin (m + 1), Finite (PositiveEdge L n (m + 1) ((i : ℕ) + 1))]
    [FiniteDimensional ℝ (LevelForms L n (m + 1))]
    (hdefE : ∀ ξ : LevelForms L n (m + 1), levelForm ξ ξ = 0 → ξ = 0)
    {a : ℝ} {X : ChainPoint L n (m + 1)}
    (hXc : X.fine ∈ fieldsIn L n (m + 1) 0 PeriodicLattice.complexGaugeGroup)
    {Lf : Coords L n (m + 1) → ℝ}
    (hLf : ∀ (Y : ℝ → ChainPoint L n (m + 1)) (v : Coords L n (m + 1)), Y 0 = X →
      (∀ b, HasDerivAt (fun t => (Y t).fine b) (v.1 b) 0) →
      (∀ i c, HasDerivAt (fun t => (Y t).noise i c) (v.2 i c) 0) →
      HasDerivAt (fun t => chainAction a (Y t)) (Lf v) 0)
    (hadd : ∀ v v', Lf (v + v') = Lf v + Lf v') (hsm : ∀ (r : ℝ) v, Lf (r • v) = r • Lf v) :
    ∃ J, IsLevelGradient (chainAction a) X J := by
  let vel : LevelForms L n (m + 1) → Coords L n (m + 1) := fun η =>
    (linkVelocity X.fine η.1, fun i c =>
      Complex.I • (η.2 i : Edge L n (m + 1) ((i : ℕ) + 1) → ComplexMatrix2) c.1 * X.noise i c)
  have hderiv : ∀ η, leftDeriv (chainAction a) X η = Lf (vel η) := by
    intro η
    have h := hLf (fun t => expMove (t • η) X) (vel η) (expMove_zero hXc η)
      (fun b => hasDerivAt_expTwist hXc η.1.2.2 b)
      (fun i c => (hasDerivAt_expFlow _).mul_const _)
    exact h.deriv
  have hvadd : ∀ η η', vel (η + η') = vel η + vel η' := by
    intro η η'
    refine Prod.ext ?_ ?_
    · exact linkVelocity_add _ _ _
    · funext i c
      simp only [vel, Prod.snd_add, Pi.add_apply, Submodule.coe_add, smul_add, add_mul]
  have hvsm : ∀ (r : ℝ) η, vel (r • η) = r • vel η := by
    intro r η
    refine Prod.ext ?_ ?_
    · exact linkVelocity_smul _ _ _
    · funext i c
      simp only [vel, Prod.smul_snd, Pi.smul_apply, Submodule.coe_smul]
      rw [smul_comm, smul_mul_assoc]
  let ℓ : LevelForms L n (m + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun η => Lf (vel η)
      map_add' := fun η η' => by rw [hvadd, hadd]
      map_smul' := fun r η => by rw [hvsm, hsm]; rfl }
  obtain ⟨T, hT'⟩ := exists_linear_representative levelForm hdefE
    (LinearMap.toSpanSingleton ℝ _ ℓ)
  refine ⟨T 1, fun ξ => ?_⟩
  have h := hT' 1 ξ
  rw [levelForm_apply] at h
  rw [h, hderiv]
  simp
  rfl
end Final
section TowerFactsOfTheTower
private theorem towerFacts_of (hCfg : LeftChartFields.Claim)
    (hS : FaceSums.FacesAndPairings) (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    TowerFacts L n k := by
  have hPS := fun (j : ℕ) (hj : j ≤ k) => (hS L hL k j hj).1 n hn
  have finS : ∀ j, j ≤ k → Finite (Vertex L n k j) := fun j hj =>
    Set.finite_univ_iff.mp ((hPS j hj).2.1 univ).2.1
  refine
    { finiteVertex := finS
      finitePositiveEdge := fun j hj => Set.finite_univ_iff.mp ((hPS j hj).2.2.1 univ).2.1
      finiteEdge := fun j hj => ?_
      finiteFace := Set.finite_univ_iff.mp ((hPS 0 (Nat.zero_le _)).2.2.2 univ).2.1
      not_both_oriented := fun j hj b hb => ?_
      leftChart := fun j hj => ((hCfg.2.2 L k j hL hj).1 n hn).1.1 }
  · haveI := finS j hj
    have h : Function.Injective (fun b : Edge L n k j => (b.source, b.target)) := by
      intro b b' hb
      exact PeriodicLattice.Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
    exact Finite.of_injective _ h
  · obtain ⟨μ, hμ⟩ := hb
    rintro ⟨ν, hν⟩
    have hN := (hA L hL n j k hn hj).2.2.2.2.2.1
    have hs : QuotientLattices.IsSignedAxisStep
        (QuotientLattices.torusAxisSteps L n k j)
        (b.source : PeriodicLattice.FourTorus L n) (b.target : PeriodicLattice.FourTorus L n) 1 μ := by
      have h := congrArg Subtype.val hμ
      simpa [QuotientLattices.IsSignedAxisStep,
        QuotientLattices.torusAxisSteps] using h
    have hs' : QuotientLattices.IsSignedAxisStep
        (QuotientLattices.torusAxisSteps L n k j)
        (b.target : PeriodicLattice.FourTorus L n) (b.source : PeriodicLattice.FourTorus L n) 1 ν := by
      have h := congrArg Subtype.val hν
      simpa [QuotientLattices.IsSignedAxisStep,
        QuotientLattices.torusAxisSteps, PeriodicLattice.Bond.opposite] using h
    have hX := ((hN.2.2 _ b.source.2 _ b.target.2).2 1 μ hs).2
    rcases hX with ⟨-, h⟩ | ⟨-, h⟩
    · exact h ⟨ν, hs'⟩
    · exact h ⟨μ, hs⟩
end TowerFactsOfTheTower
theorem gradientAndMultiplierAtMinimizer_proof
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hCfg : LeftChartFields.Claim) (hS : FaceSums.FacesAndPairings)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    (hF : MinimizerFieldsNearOne)
    (hM : ChainMapsAtMinimizers) :
    GradientAndMultiplierAtMinimizer := by
  intro a ha L hL m n hn
  have hT : TowerFacts L n (m + 1) := towerFacts_of hCfg hS hA hL hn
  have hPS := fun (j : ℕ) (hj : j ≤ m + 1) => (hS L hL (m + 1) j hj).1 n hn
  have innB := fun (j : ℕ) (hj : j ≤ m + 1) => ((hPS j hj).2.2.1 univ).1
  haveI hF0 : Finite (PositiveEdge L n (m + 1) 0) := hT.finitePositiveEdge 0 (Nat.zero_le _)
  haveI hFk : Finite (PositiveEdge L n (m + 1) (m + 1)) := hT.finitePositiveEdge _ le_rfl
  haveI hFi : ∀ i : Fin (m + 1), Finite (PositiveEdge L n (m + 1) ((i : ℕ) + 1)) :=
    fun i => hT.finitePositiveEdge _ i.2
  have fdim : ∀ j, j ≤ m + 1 → FiniteDimensional ℝ (edgeFormSpace L n (m + 1) j) := by
    intro j hj
    haveI := hT.finitePositiveEdge j hj
    let f : edgeFormSpace L n (m + 1) j →ₗ[ℝ] (PositiveEdge L n (m + 1) j → ComplexMatrix2) :=
      { toFun := fun B => restrictToPositiveEdges (B : Edge L n (m + 1) j → ComplexMatrix2)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine FiniteDimensional.of_injective f ?_
    rw [injective_iff_map_eq_zero]
    intro B hB
    exact Subtype.ext (edgeForm_eq_zero_of_restrict B.2 hB)
  haveI hfd0 := fdim 0 (Nat.zero_le _)
  haveI hfdi : ∀ i : Fin (m + 1), FiniteDimensional ℝ (edgeFormSpace L n (m + 1) ((i : ℕ) + 1)) :=
    fun i => fdim _ i.2
  have hdefE : ∀ ξ : LevelForms L n (m + 1), levelForm ξ ξ = 0 → ξ = 0 :=
    levelForm_definite (innB 0 (Nat.zero_le _)) fun i => innB _ i.2
  have hk : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  filter_upwards [hF a ha L hL (m + 1) n hk hn (1 / 4) (by norm_num),
    hM a ha L hL (m + 1) n hk hn] with V h1 h2 W hW X hX
  obtain ⟨-, -, hlen⟩ := h1 W hW X hX
  have hMaps := h2 W hW X hX
  have hR := hX.compact
  have hs : DetsOffSlit X := fun j hj c hc =>
    det_mem_slitPlane_of_meanRadius (hlen ⟨j, hj⟩ ⟨c, hc⟩)
  have hleast : ∀ X' : ChainPoint L n (m + 1), IsCompactValued X' →
      levelField X' (m + 1) = levelField X (m + 1) → chainAction a X ≤ chainAction a X' :=
    fun X' h3 h4 => hX.le X' h3 (h4.trans hX.top_eq)
  obtain ⟨Lf, hLf, hadd, hsm⟩ := exists_chainAction_derivative hT a hR hs
  obtain ⟨J, hJ⟩ := exists_levelGradient hT hdefE
    (mem_fieldsIn_complex (hR.2 0 (Nat.zero_le _))) hLf hadd hsm
  refine ⟨J, J.2 (Fin.last m), hJ,
    isTopMultiplier_of_minimizer hd hT hEL hR hs hleast hMaps hLf hJ, fun B => ?_⟩
  rw [← levelForm_topNoiseTangent, levelForm_apply]
  exact hJ (lastNoiseTangent B)
end YangMills.Construction.RunningCouplingSlope.MinimizerGradient
end
