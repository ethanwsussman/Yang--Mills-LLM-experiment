import YangMills.Construction.RunningCouplingSlope.ChainNumberReadsNoPointProof
import YangMills.Construction.RunningCouplingSlope.GradientAndMultiplierAtALeastPointProof
import YangMills.Construction.RunningCouplingSlope.LeastPointsAreGaugeImagesOfSmallTangentsProof
import YangMills.Construction.RunningCouplingSlope.LeastValueAlongATopForm
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MinimalActionDerivProof
open Matrices
open Tower
open Tower.LeftChartFields
section Envelope
private theorem hasDerivAt_sInf_image {Ω : Type*} {F p : Ω → ℝ} {K : ℝ → Set Ω} {T : ℝ → Ω → Ω}
    {e : ℝ → ℝ} {P₀ : ℝ} {X : Ω} (hbd : ∀ t, ∀ y ∈ K t, 0 ≤ F y)
    (hT : ∀ t, ∀ y ∈ K 0, T t y ∈ K t)
    (hB : ∀ t, ∀ y ∈ K t, T (-t) y ∈ K 0 ∧ T t (T (-t) y) = y)
    (hexp : ∀ s, ∀ y ∈ K 0, |F (T s y) - F y - s * p y| ≤ e s)
    (he : e =o[𝓝 0] fun s => s) (hp : ∀ y ∈ K 0, |p y| ≤ P₀)
    (hX : X ∈ K 0) (hmin : ∀ y ∈ K 0, F X ≤ F y)
    (hZ : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ K 0, F y < F X + δ → |p y - p X| < ε) :
    HasDerivAt (fun t => sInf {s | ∃ y ∈ K t, s = F y}) (p X) 0 := by
  have hbdd : ∀ t, BddBelow {s | ∃ y ∈ K t, s = F y} := by
    intro t
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hbd t y hy
  have hne : ∀ t, {s | ∃ y ∈ K t, s = F y}.Nonempty := fun t => ⟨_, T t X, hT t X hX, rfl⟩
  have hM0 : sInf {s | ∃ y ∈ K 0, s = F y} = F X := by
    refine le_antisymm (csInf_le (hbdd 0) ⟨X, hX, rfl⟩) (le_csInf (hne 0) ?_)
    rintro _ ⟨y, hy, rfl⟩
    exact hmin y hy
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hZδ⟩ := hZ (c / 2) (by positivity)
  have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), ‖e t‖ ≤ c / 4 * ‖t‖ :=
    (Asymptotics.isLittleO_iff.mp he) (by positivity)
  have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), ‖e t‖ ≤ 1 * ‖t‖ :=
    (Asymptotics.isLittleO_iff.mp he) one_pos
  have h3 : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), (2 * P₀ + 2) * |t| < δ / 2 := by
    have hcont : Continuous fun t : ℝ => (2 * P₀ + 2) * |t| := by fun_prop
    have h0 : (2 * P₀ + 2) * |(0 : ℝ)| < δ / 2 := by simpa using half_pos hδ
    exact hcont.continuousAt.eventually_lt continuousAt_const h0
  filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
  rw [zero_add, hM0, smul_eq_mul]
  set M := sInf {s | ∃ y ∈ K t, s = F y} with hM
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at ht1 ht2
  have he1 : e t ≤ c / 4 * |t| := (le_abs_self _).trans ht1
  have he2 : e t ≤ |t| := by simpa using (le_abs_self _).trans ht2
  have hpX : |p X| ≤ P₀ := hp X hX
  have hup : M ≤ F X + t * p X + e t := by
    have h := (abs_le.mp (hexp t X hX)).2
    have h' : M ≤ F (T t X) := csInf_le (hbdd t) ⟨_, hT t X hX, rfl⟩
    linarith
  have htp : ∀ {q : ℝ}, |q| ≤ P₀ → |t * q| ≤ |t| * P₀ := by
    intro q hq
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  have hlow : F X + t * p X - c / 2 * |t| - e t ≤ M := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    set η' := min η (δ / 4) with hη'
    have hη'0 : 0 < η' := lt_min hη (by positivity)
    obtain ⟨_, ⟨y', hy', rfl⟩, hlt⟩ := Real.lt_sInf_add_pos (hne t) hη'0
    rw [← hM] at hlt
    obtain ⟨hy, hyy⟩ := hB t y' hy'
    set y := T (-t) y' with hydef
    have hx := abs_le.mp (hexp t y hy)
    rw [hyy] at hx
    have hpy := hp y hy
    have h5 := abs_le.mp (htp hpy)
    have h6 := abs_le.mp (htp hpX)
    have hη4 : η' ≤ δ / 4 := min_le_right _ _
    have hFy : F y < F X + δ := by
      have : (2 * P₀ + 2) * |t| = 2 * (|t| * P₀) + 2 * |t| := by ring
      linarith
    have hcl := hZδ y hy hFy
    have h7 : |t * (p y - p X)| ≤ |t| * (c / 2) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hcl.le (abs_nonneg _)
    have h8 := abs_le.mp h7
    have h9 := hmin y hy
    have hηle : η' ≤ η := min_le_left _ _
    linarith [h8.1, hx.1]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith
end Envelope
section CompactGroup
private theorem det_of_mem_compact {g : ComplexMatrix2} (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    Matrix.det g = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
private theorem isUnit_det_of_mem_compact {g : ComplexMatrix2}
    (h : g ∈ PeriodicLattice.compactGaugeGroup) : IsUnit (Matrix.det g) := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private def IsQuaternionic (A : ComplexMatrix2) : Prop :=
  A 1 1 = (starRingEnd ℂ) (A 0 0) ∧ A 1 0 = -(starRingEnd ℂ) (A 0 1)
private theorem isQuaternionic_of_mem {A : ComplexMatrix2}
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
private theorem inv_mem_compact {A : ComplexMatrix2} (h : A ∈ PeriodicLattice.compactGaugeGroup) :
    A⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem det_isQuaternionic {A : ComplexMatrix2} (hA : IsQuaternionic A) :
    Matrix.det A = ((Complex.normSq (A 0 0) + Complex.normSq (A 0 1) : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two, hA.1, hA.2]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  ring
private theorem traceDefect_nonneg {g : ComplexMatrix2} (h : g ∈ PeriodicLattice.compactGaugeGroup) :
    0 ≤ traceDefect g := by apply _root_.YangMills.SharedProofs.p3544 <;> assumption
private theorem tendsto_matrix_inv {ι : Type*} {l : Filter ι} {f : ι → ComplexMatrix2}
    {A : ComplexMatrix2} (hf : Tendsto f l (𝓝 A)) (hA : Matrix.det A = 1) :
    Tendsto (fun m => (f m)⁻¹) l (𝓝 A⁻¹) := by
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (by rw [hA]; exact isUnit_one)
  obtain ⟨u, rfl⟩ := hu
  have h := (NormedRing.inverse_continuousAt u).tendsto.comp hf
  have e : (fun m => (f m)⁻¹) = Ring.inverse ∘ f := by
    funext m
    exact Matrix.nonsing_inv_eq_ringInverse _
  rw [e, Matrix.nonsing_inv_eq_ringInverse]
  simpa using h
abbrev _root_.YangMills.SharedProofs.p953 := @tendsto_matrix_inv
private theorem continuous_traceDefect : Continuous traceDefect := by
  unfold traceDefect
  have h : Continuous fun g : ComplexMatrix2 => ComplexMatrix2.halfTrace g := by
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
    exact continuous_const.mul (Continuous.matrix_trace continuous_id)
  exact continuous_const.sub (Complex.continuous_re.comp h)
abbrev _root_.YangMills.SharedProofs.p10480 := @continuous_traceDefect
private theorem isCompact_compactGroup :
    IsCompact (PeriodicLattice.compactGaugeGroup : Set ComplexMatrix2) := by
  have : CompactSpace ComplexMatrix2.specialUnitary := inferInstance
  exact isCompact_iff_compactSpace.2 this
private theorem matExp_I_smul_zero :
    ComplexMatrix2.matExp (Complex.I • (0 : ComplexMatrix2)) = 1 := by
  rw [smul_zero]
  exact NormedSpace.exp_zero
private theorem hasDerivAt_oneParam (X : ComplexMatrix2) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • (t • X))) (Complex.I • X) 0 := by apply _root_.YangMills.SharedProofs.p9756 <;> assumption
private theorem oneParam_zero (X : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • ((0 : ℝ) • X)) = 1 := by apply _root_.YangMills.SharedProofs.p11429 <;> assumption
private theorem oneParam_mul (X : ComplexMatrix2) (s t : ℝ) :
    ComplexMatrix2.matExp (Complex.I • (s • X)) * ComplexMatrix2.matExp (Complex.I • (t • X)) =
      ComplexMatrix2.matExp (Complex.I • ((s + t) • X)) := by
  have ht : ∀ x : ComplexMatrix2,
      x ∈ Metric.eball (0 : ComplexMatrix2) (NormedSpace.expSeries ℂ ComplexMatrix2).radius :=
    fun x => (NormedSpace.expSeries_radius_eq_top ℂ ComplexMatrix2).symm ▸ edist_lt_top _ _
  have hc : Commute (Complex.I • (s • X)) (Complex.I • (t • X)) :=
    (((Commute.refl X).smul_left s).smul_right t).smul_left Complex.I |>.smul_right Complex.I
  rw [ComplexMatrix2.matExp, ComplexMatrix2.matExp, ComplexMatrix2.matExp,
    ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hc (ht _) (ht _), add_smul, smul_add]
abbrev _root_.YangMills.SharedProofs.p4363 := @oneParam_mul
private theorem matExp_mem_compact (hEL : ComplexMatrix2.ExpLogEstimates) {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • A) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.matExp_I_smul_mem_compact <;> assumption
private def reHalfTrace : ComplexMatrix2 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (ComplexMatrix2.halfTrace A).re
      map_add' := fun A B => by
        simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_add, mul_add]
      map_smul' := fun r A => by
        have e : r • A = (r : ℂ) • A := (Complex.coe_smul r A).symm
        simp only [RingHom.id_apply, smul_eq_mul, ComplexMatrix2.halfTrace,
          ComplexMatrix2.fullTrace]
        rw [e, Matrix.trace_smul, smul_eq_mul, mul_left_comm, Complex.re_ofReal_mul] }
private theorem traceDefect_eq (g : ComplexMatrix2) : traceDefect g = 1 - reHalfTrace g := rfl
private theorem norm_of_mem_compact {g : ComplexMatrix2}
    (h : g ∈ PeriodicLattice.compactGaugeGroup) : ‖g‖ = 1 := by apply _root_.YangMills.Construction.PeriodicLattice.CentredAverageSmallFields.norm_eq_one_of_mem_compactGaugeGroup <;> assumption
end CompactGroup
section TowerLevels
variable {L n k j : ℕ}
private theorem edge_opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := rfl
private theorem fieldOfPositiveValues_pos (w : PositiveEdge L n k j → ComplexMatrix2)
    {b : Edge L n k j} (h : b.IsPositivelyOriented) : fieldOfPositiveValues w b = w ⟨b, h⟩ := by
  simp [fieldOfPositiveValues, h]
private theorem fieldOfPositiveValues_neg (w : PositiveEdge L n k j → ComplexMatrix2)
    {b : Edge L n k j} (h : ¬b.IsPositivelyOriented) :
    fieldOfPositiveValues w b =
      (w ⟨b.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented h⟩)⁻¹ := by
  simp [fieldOfPositiveValues, h, PeriodicLattice.Bond.opposite_isPositivelyOriented h]
private theorem levelField_succ (X : ChainPoint L n k) (h : j < k) :
    levelField X (j + 1) =
      fieldOfPositiveValues fun c => X.noise ⟨j, h⟩ c * normalizedMean (levelField X j) c.1 := by
  simp [levelField, h]
private theorem levelField_pos (X : ChainPoint L n k) (h : j < k)
    {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by
  rw [levelField_succ X h, fieldOfPositiveValues_pos _ hb]
private theorem levelField_neg (X : ChainPoint L n k) (h : j < k)
    {b : Edge L n k (j + 1)} (hb : ¬b.IsPositivelyOriented) :
    levelField X (j + 1) b = (levelField X (j + 1) b.opposite)⁻¹ := by
  rw [levelField_pos X h (PeriodicLattice.Bond.opposite_isPositivelyOriented hb), levelField_succ X h,
    fieldOfPositiveValues_neg _ hb]
private theorem chainPoint_ext {X Y : ChainPoint L n k} (h1 : X.fine = Y.fine)
    (h2 : X.noise = Y.noise) : X = Y := by
  cases X
  cases Y
  cases h1
  cases h2
  rfl
private theorem mem_complex_of_mem {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_fieldsIn_of_mem <;> assumption
private theorem pathHolonomy_cons (U : Edge L n k j → ComplexMatrix2) (b : Edge L n k j)
    (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy U (b :: Γ) = U b * PeriodicLattice.pathHolonomy U Γ := by
  simp [PeriodicLattice.pathHolonomy]
private theorem pathHolonomy_mem {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j)
    (Γ : List (Edge L n k j)) :
    PeriodicLattice.pathHolonomy V Γ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p2470 <;> assumption
private theorem tendsto_pathHolonomy {ι : Type*} {l : Filter ι}
    {W : ι → Edge L n k j → ComplexMatrix2} {V : Edge L n k j → ComplexMatrix2}
    (h : ∀ b, Tendsto (fun m => W m b) l (𝓝 (V b))) (Γ : List (Edge L n k j)) :
    Tendsto (fun m => PeriodicLattice.pathHolonomy (W m) Γ) l
      (𝓝 (PeriodicLattice.pathHolonomy V Γ)) := by
  induction Γ with
  | nil => exact tendsto_const_nhds
  | cons b Γ ih =>
    simp only [pathHolonomy_cons]
    exact (h b).mul ih
abbrev _root_.YangMills.SharedProofs.p17103 := @tendsto_pathHolonomy
private theorem tendsto_contourMean [Finite (Vertex L n k j)] {ι : Type*} {l : Filter ι}
    {W : ι → Edge L n k j → ComplexMatrix2} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j)
    (h : ∀ b, Tendsto (fun m => W m b) l (𝓝 (V b))) (c : Edge L n k (j + 1)) :
    Tendsto (fun m => contourMean (W m) c) l (𝓝 (contourMean V c)) := by
  simp only [contourMean]
  have hs : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  simp only [finsum_mem_eq_finite_toFinset_sum _ hs]
  refine Tendsto.const_smul ?_ _
  refine tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun π _ => ?_
  simp only [contourHolonomy]
  exact ((tendsto_pathHolonomy h _).mul (tendsto_pathHolonomy h _)).mul
    (tendsto_matrix_inv (tendsto_pathHolonomy h _) (det_of_mem_compact (pathHolonomy_mem hV _)))
abbrev _root_.YangMills.SharedProofs.p67763 := @tendsto_contourMean
private theorem contourMean_isQuaternionic [Finite (Vertex L n k j)]
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1)) :
    IsQuaternionic (contourMean V c) := by
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
      refine isQuaternionic_add (isQuaternionic_of_mem ?_) ih
      refine ComplexMatrix2.specialUnitary.mul_mem
        (ComplexMatrix2.specialUnitary.mul_mem (pathHolonomy_mem hV _) (pathHolonomy_mem hV _)) ?_
      exact inv_mem_compact (pathHolonomy_mem hV _)
  exact hs _
private theorem meanRadius_eq [Finite (Vertex L n k j)] {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1)) :
    meanRadius V c = (((Complex.normSq (contourMean V c 0 0) +
      Complex.normSq (contourMean V c 0 1)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  have hM := contourMean_isQuaternionic hV c
  rw [Complex.ofReal_cpow (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)),
    meanRadius, det_isQuaternionic hM]
  push_cast
  rfl
private theorem meanRadius_re_nonneg [Finite (Vertex L n k j)] {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1)) :
    0 ≤ (meanRadius V c).re := by
  rw [meanRadius_eq hV c, Complex.ofReal_re]
  exact Real.rpow_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) _
abbrev _root_.YangMills.SharedProofs.p43485 := @meanRadius_re_nonneg
private theorem normalizedMean_mem [Finite (Vertex L n k j)] {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1))
    (hu : Matrix.det (normalizedMean V c) = 1) :
    normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p11178 <;> assumption
private theorem det_contourMean_mem_slitPlane [Finite (Vertex L n k j)]
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j) (c : Edge L n k (j + 1))
    (h : meanRadius V c ≠ 0) : Matrix.det (contourMean V c) ∈ Complex.slitPlane := by
  rw [det_isQuaternionic (contourMean_isQuaternionic hV c)]
  have h0 : 0 ≤ Complex.normSq (contourMean V c 0 0) + Complex.normSq (contourMean V c 0 1) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  rcases h0.lt_or_eq with hp | he
  · exact Complex.ofReal_mem_slitPlane.2 hp
  · exfalso
    apply h
    rw [meanRadius_eq hV c, ← he]
    simp
end TowerLevels
section Limits
variable {L n k j : ℕ}
private structure TowerFacts (L n k : ℕ) : Prop where
  finVertex : ∀ j, j ≤ k → Finite (Vertex L n k j)
  finPositive : ∀ j, j ≤ k → Finite (PositiveEdge L n k j)
  finEdge : ∀ j, j ≤ k → Finite (Edge L n k j)
  finFace : Finite (Face L n k 0)
  xor_opposite : ∀ j, j ≤ k → ∀ b : Edge L n k j,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  mean_one : ∀ j, j < k → ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    normalizedMean (fun _ : Edge L n k j => (1 : ComplexMatrix2)) c = 1
  leftExp : ∀ j, j ≤ k → (finiteData L n k j).LeftExpMulMemGroup
private def MeanNearIdentity (L n k : ℕ) (ρ : ℝ) : Prop :=
  ∀ j, j < k → ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ) → ∀ c : Edge L n k (j + 1),
      c.IsPositivelyOriented →
      meanRadius V c ≠ 0 ∧ normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup
private theorem not_opposite_pos (hT : TowerFacts L n k) (hj : j ≤ k) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by
  rcases hT.xor_opposite j hj b with ⟨_, h⟩ | ⟨_, h⟩
  · exact h
  · exact absurd hb h
private theorem tendsto_levelField_succ (hT : TowerFacts L n k) {ρ : ℝ}
    (hρ : MeanNearIdentity L n k ρ) {ι : Type*}
    {l : Filter ι} {X : ι → ChainPoint L n k} {Y : ChainPoint L n k} (hY : IsCompactValued Y)
    (hj : j < k) (hYn : ∀ b, ComplexMatrix2.operatorNorm (levelField Y j b - 1) < ρ)
    (hn : ∀ c, Tendsto (fun m => (X m).noise ⟨j, hj⟩ c) l (𝓝 (Y.noise ⟨j, hj⟩ c)))
    (hW : ∀ b, Tendsto (fun m => levelField (X m) j b) l (𝓝 (levelField Y j b))) :
    (∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      Tendsto (fun m => meanRadius (levelField (X m) j) c) l
        (𝓝 (meanRadius (levelField Y j) c))) ∧
    ∀ b, Tendsto (fun m => levelField (X m) (j + 1) b) l (𝓝 (levelField Y (j + 1) b)) := by
  have hV := hY.2 j hj.le
  haveI := hT.finVertex j hj.le
  have key : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      Tendsto (fun m => meanRadius (levelField (X m) j) c) l
        (𝓝 (meanRadius (levelField Y j) c)) ∧
      Tendsto (fun m => normalizedMean (levelField (X m) j) c) l
        (𝓝 (normalizedMean (levelField Y j) c)) := by
    intro c hc
    obtain ⟨h0, -⟩ := hρ j hj _ (mem_complex_of_mem hV) hYn c hc
    have hMt := tendsto_contourMean hV hW c
    have hdet : Tendsto (fun m => Matrix.det (contourMean (levelField (X m) j) c)) l
        (𝓝 (Matrix.det (contourMean (levelField Y j) c))) :=
      ((Continuous.matrix_det continuous_id).tendsto _).comp hMt
    have hrt : Tendsto (fun m => meanRadius (levelField (X m) j) c) l
        (𝓝 (meanRadius (levelField Y j) c)) :=
      (continuousAt_cpow_const (b := (1 / 2 : ℂ)) (det_contourMean_mem_slitPlane hV c h0)).tendsto.comp
        hdet
    exact ⟨hrt, (hrt.inv₀ h0).smul hMt⟩
  have hpos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      Tendsto (fun m => levelField (X m) (j + 1) c) l (𝓝 (levelField Y (j + 1) c)) := by
    intro c hc
    have e : (fun m => levelField (X m) (j + 1) c) = fun m =>
        (X m).noise ⟨j, hj⟩ ⟨c, hc⟩ * normalizedMean (levelField (X m) j) c := by
      funext m
      exact levelField_pos _ hj hc
    rw [e, levelField_pos Y hj hc]
    exact (hn _).mul (key c hc).2
  refine ⟨fun c hc => (key c hc).1, fun b => ?_⟩
  by_cases hb : b.IsPositivelyOriented
  · exact hpos b hb
  · have hb' := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
    have e : (fun m => levelField (X m) (j + 1) b) = fun m =>
        (levelField (X m) (j + 1) b.opposite)⁻¹ := by
      funext m
      exact levelField_neg _ hj hb
    rw [e, levelField_neg Y hj hb]
    exact tendsto_matrix_inv (hpos _ hb')
      (det_of_mem_compact ((hY.2 (j + 1) hj).1 _ (Set.mem_univ _)))
private theorem tendsto_levelField (hT : TowerFacts L n k) {ρ : ℝ} (hρ : MeanNearIdentity L n k ρ)
    {ι : Type*} {l : Filter ι} {X : ι → ChainPoint L n k} {Y : ChainPoint L n k}
    (hY : IsCompactValued Y)
    (hYn : ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField Y j b - 1) < ρ)
    (hb : ∀ b, Tendsto (fun m => (X m).fine b) l (𝓝 (Y.fine b)))
    (hn : ∀ i c, Tendsto (fun m => (X m).noise i c) l (𝓝 (Y.noise i c))) :
    ∀ j, j ≤ k → ∀ b, Tendsto (fun m => levelField (X m) j b) l (𝓝 (levelField Y j b)) := by
  intro j
  induction j with
  | zero => exact fun _ => hb
  | succ j ih =>
    intro h
    have hj : j < k := h
    exact (tendsto_levelField_succ hT hρ hY hj (hYn j hj.le) (hn _) (ih hj.le)).2
private theorem tendsto_meanRadius (hT : TowerFacts L n k) {ρ : ℝ} (hρ : MeanNearIdentity L n k ρ)
    {ι : Type*} {l : Filter ι} {X : ι → ChainPoint L n k} {Y : ChainPoint L n k}
    (hY : IsCompactValued Y)
    (hYn : ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField Y j b - 1) < ρ)
    (hb : ∀ b, Tendsto (fun m => (X m).fine b) l (𝓝 (Y.fine b)))
    (hn : ∀ i c, Tendsto (fun m => (X m).noise i c) l (𝓝 (Y.noise i c)))
    (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    Tendsto (fun m => meanRadius (levelField (X m) i) c.1) l
      (𝓝 (meanRadius (levelField Y i) c.1)) :=
  (tendsto_levelField_succ hT hρ hY i.2 (hYn i i.2.le) (hn _)
    (tendsto_levelField hT hρ hY hYn hb hn i i.2.le)).1 c.1 c.2
private theorem tendsto_chainAction (hT : TowerFacts L n k) {ρ : ℝ} (hρ : MeanNearIdentity L n k ρ)
    {ι : Type*} {l : Filter ι} {X : ι → ChainPoint L n k} {Y : ChainPoint L n k}
    (hY : IsCompactValued Y)
    (hYn : ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField Y j b - 1) < ρ)
    (hb : ∀ b, Tendsto (fun m => (X m).fine b) l (𝓝 (Y.fine b)))
    (hn : ∀ i c, Tendsto (fun m => (X m).noise i c) l (𝓝 (Y.noise i c))) (a : ℝ) :
    Tendsto (fun m => chainAction a (X m)) l (𝓝 (chainAction a Y)) := by
  letI hFq : ∀ i : Fin k, Fintype (PositiveEdge L n k ((i : ℕ) + 1)) := fun i =>
    @Fintype.ofFinite _ (hT.finPositive _ i.2)
  letI hFp : Fintype (Face L n k 0) := @Fintype.ofFinite _ hT.finFace
  have e : ∀ Z : ChainPoint L n k, chainAction a Z =
      (∑ q : Face L n k 0, traceDefect (PeriodicLattice.pathHolonomy Z.fine q.boundaryBonds)) +
      a * ∑ i : Fin k, ∑ c : PositiveEdge L n k ((i : ℕ) + 1),
        (meanRadius (levelField Z i) c.1).re * traceDefect (Z.noise i c) := by
    intro Z
    simp only [chainAction, plaquetteAction, PeriodicLattice.wilsonAction,
      finsum_eq_sum_of_fintype, PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteHolonomy]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [traceDefect, ComplexMatrix2.halfTrace, Complex.mul_re]
  simp only [e]
  refine Tendsto.add (tendsto_finsetSum _ fun q _ => ?_) (Tendsto.const_mul _
    (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun c _ => ?_))
  · exact (continuous_traceDefect.tendsto _).comp (tendsto_pathHolonomy hb _)
  · exact ((Complex.continuous_re.tendsto _).comp
      (tendsto_meanRadius hT hρ hY hYn hb hn i c)).mul
      ((continuous_traceDefect.tendsto _).comp (hn i c))
private theorem levelField_unitPoint (hT : TowerFacts L n k) : ∀ j, j ≤ k →
    levelField (unitPoint L n k) j = fun _ => 1 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    have hpos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        levelField (unitPoint L n k) (j + 1) c = 1 := by
      intro c hc
      rw [levelField_pos _ hj hc, ih hj.le, hT.mean_one j hj c hc]
      simp [unitPoint]
    funext c
    by_cases hc : c.IsPositivelyOriented
    · exact hpos c hc
    · rw [levelField_neg _ hj hc, hpos _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hc)]
      simp
private theorem const_one_mem_fieldSpace :
    (fun _ : Edge L n k j => (1 : ComplexMatrix2)) ∈ fieldSpace L n k j :=
  ⟨fun _ _ => ComplexMatrix2.specialUnitary.one_mem, fun _ _ => by simp⟩
private theorem unitPoint_compact (hT : TowerFacts L n k) : IsCompactValued (unitPoint L n k) := by
  refine ⟨fun _ _ => ComplexMatrix2.specialUnitary.one_mem, fun j hj => ?_⟩
  rw [levelField_unitPoint hT j hj]
  exact const_one_mem_fieldSpace
private theorem traceDefect_one : traceDefect 1 = 0 := by
  simp [traceDefect, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
private theorem chainAction_unitPoint (a : ℝ) : chainAction a (unitPoint L n k) = 0 := by
  have h1 : plaquetteAction L n k (unitPoint L n k).fine = 0 := by
    simp only [plaquetteAction, PeriodicLattice.wilsonAction]
    refine finsum_eq_zero_of_forall_eq_zero fun p => ?_
    have e : ∀ Γ : List (Edge L n k 0),
        PeriodicLattice.pathHolonomy (unitPoint L n k).fine Γ = 1 := by
      intro Γ
      induction Γ with
      | nil => rfl
      | cons b Γ ih =>
        rw [pathHolonomy_cons, ih]
        simp [unitPoint]
    simp only [PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteHolonomy, e]
    simp [ComplexMatrix2.fullTrace]
  simp only [chainAction, h1, zero_add]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => ?_)
  refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
  simp only [unitPoint, traceDefect_one, mul_zero]
abbrev _root_.YangMills.SharedProofs.p8209 := @chainAction_unitPoint
private abbrev ChainCoords (L n k : ℕ) : Type :=
  (Edge L n k 0 → ComplexMatrix2) × ((i : Fin k) → PositiveEdge L n k ((i : ℕ) + 1) → ComplexMatrix2)
private theorem near_unitPoint (hT : TowerFacts L n k) {ρ δ : ℝ} (hρ0 : 0 < ρ)
    (hρ : MeanNearIdentity L n k ρ) (hδ : 0 < δ) (a : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ X : ChainPoint L n k,
      (∀ b, ComplexMatrix2.operatorNorm (X.fine b - 1) < ε₀) →
      (∀ i c, ComplexMatrix2.operatorNorm (X.noise i c - 1) < ε₀) →
      (∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ) ∧
        chainAction a X < δ := by
  letI hFb : Fintype (Edge L n k 0) := @Fintype.ofFinite _ (hT.finEdge 0 (Nat.zero_le _))
  letI hFq : ∀ i : Fin k, Fintype (PositiveEdge L n k ((i : ℕ) + 1)) := fun i =>
    @Fintype.ofFinite _ (hT.finPositive _ i.2)
  let toPoint : ChainCoords L n k → ChainPoint L n k := fun p => ⟨p.1, p.2⟩
  let p₀ : ChainCoords L n k := (fun _ => 1, fun _ _ => 1)
  have hYn : ∀ j, j ≤ k → ∀ b,
      ComplexMatrix2.operatorNorm (levelField (unitPoint L n k) j b - 1) < ρ := by
    intro j hj b
    rw [levelField_unitPoint hT j hj]
    simpa [ComplexMatrix2.operatorNorm] using hρ0
  have hb : ∀ b, Tendsto (fun p : ChainCoords L n k => (toPoint p).fine b) (𝓝 p₀)
      (𝓝 ((unitPoint L n k).fine b)) := fun b =>
    (((continuous_apply b).comp continuous_fst).tendsto p₀)
  have hn : ∀ i c, Tendsto (fun p : ChainCoords L n k => (toPoint p).noise i c) (𝓝 p₀)
      (𝓝 ((unitPoint L n k).noise i c)) := fun i c =>
    (((continuous_apply c).comp ((continuous_apply i).comp continuous_snd)).tendsto p₀)
  have hF := tendsto_levelField hT hρ (unitPoint_compact hT) hYn hb hn
  have hA := tendsto_chainAction hT hρ (unitPoint_compact hT) hYn hb hn a
  rw [chainAction_unitPoint] at hA
  have e1 : ∀ᶠ p in 𝓝 p₀, ∀ j ∈ Finset.range (k + 1), ∀ b : Edge L n k j,
      ComplexMatrix2.operatorNorm (levelField (toPoint p) j b - 1) < ρ := by
    refine (Filter.eventually_all_finset _).mpr fun j hj => ?_
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    haveI := hT.finEdge j hj'
    refine Filter.eventually_all.mpr fun b => ?_
    have h3 : Tendsto (fun p => ‖levelField (toPoint p) j b - 1‖) (𝓝 p₀) (𝓝 0) := by
      have h4 := ((hF j hj' b).sub_const (1 : ComplexMatrix2)).norm
      rw [levelField_unitPoint hT j hj'] at h4
      simpa using h4
    exact h3.eventually_lt_const hρ0
  have e2 : ∀ᶠ p in 𝓝 p₀, chainAction a (toPoint p) < δ := hA.eventually_lt_const hδ
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp (e1.and e2)
  refine ⟨ε₀, hε₀, fun X h1 h2 => ?_⟩
  have hd : dist ((X.fine, X.noise) : ChainCoords L n k) p₀ < ε₀ := by
    rw [dist_eq_norm, Prod.norm_def, max_lt_iff]
    exact ⟨(pi_norm_lt_iff hε₀).mpr fun b => h1 b,
      (pi_norm_lt_iff hε₀).mpr fun i => (pi_norm_lt_iff hε₀).mpr fun c => h2 i c⟩
  obtain ⟨r1, r2⟩ := hball hd
  exact ⟨fun j hj b => r1 j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)) b, r2⟩
private theorem compact_of_near (hT : TowerFacts L n k) {ρ : ℝ} (hρ : MeanNearIdentity L n k ρ)
    {X : ChainPoint L n k} (hn : ∀ i c, X.noise i c ∈ PeriodicLattice.compactGaugeGroup)
    (hb : X.fine ∈ fieldSpace L n k 0)
    (hnear : ∀ j, j ≤ k → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ) :
    IsCompactValued X := by
  refine ⟨hn, fun j => ?_⟩
  induction j with
  | zero => exact fun _ => hb
  | succ j ih =>
    intro h
    have hj : j < k := h
    have h1 := ih hj.le
    haveI := hT.finVertex j hj.le
    have hpos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        levelField X (j + 1) c ∈ PeriodicLattice.compactGaugeGroup := by
      intro c hc
      obtain ⟨-, hu⟩ := hρ j hj _ (mem_complex_of_mem h1) (hnear j hj.le) c hc
      rw [levelField_pos _ hj hc]
      exact ComplexMatrix2.specialUnitary.mul_mem (hn _ _) (normalizedMean_mem h1 c hu)
    have hreal : ∀ c : Edge L n k (j + 1),
        levelField X (j + 1) c ∈ PeriodicLattice.compactGaugeGroup := by
      intro c
      by_cases hc : c.IsPositivelyOriented
      · exact hpos c hc
      · rw [levelField_neg _ hj hc]
        exact inv_mem_compact (hpos _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hc))
    refine ⟨fun b _ => hreal b, fun b _ => ?_⟩
    by_cases hb' : b.IsPositivelyOriented
    · have hb'' := not_opposite_pos hT h hb'
      rw [levelField_neg _ hj hb'', edge_opposite_opposite]
    · rw [levelField_neg _ hj hb',
        Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_compact (hreal _))]
private theorem chainAction_nonneg (hT : TowerFacts L n k) {a : ℝ} (ha : 0 < a)
    {X : ChainPoint L n k} (hX : IsCompactValued X) : 0 ≤ chainAction a X := by
  have h1 : 0 ≤ plaquetteAction L n k X.fine := by
    simp only [plaquetteAction, PeriodicLattice.wilsonAction]
    refine finsum_nonneg fun p => ?_
    have e : PeriodicLattice.plaquetteCost X.fine p =
        traceDefect (PeriodicLattice.plaquetteHolonomy X.fine p) := by
      simp only [PeriodicLattice.plaquetteCost, traceDefect, ComplexMatrix2.halfTrace]
      simp [Complex.mul_re]
    rw [e]
    exact traceDefect_nonneg (pathHolonomy_mem (hX.2 0 (Nat.zero_le _)) _)
  refine add_nonneg h1 (mul_nonneg ha.le (Finset.sum_nonneg fun i _ => ?_))
  haveI := hT.finVertex i i.2.le
  refine finsum_nonneg fun c => ?_
  exact mul_nonneg (meanRadius_re_nonneg (hX.2 i i.2.le) _) (traceDefect_nonneg (hX.1 i c))
private theorem isCompact_fieldSpace : IsCompact (fieldSpace L n k j) := by
  have h1 : IsCompact (Set.pi Set.univ fun _ : Edge L n k j =>
      (PeriodicLattice.compactGaugeGroup : Set ComplexMatrix2)) :=
    isCompact_univ_pi fun _ => isCompact_compactGroup
  have h2 : IsClosed {U : Edge L n k j → ComplexMatrix2 | ∀ b, U b.opposite * U b = 1} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun b => isClosed_eq ?_ continuous_const
    exact (continuous_apply _).mul (continuous_apply _)
  have e : fieldSpace L n k j =
      (Set.pi Set.univ fun _ : Edge L n k j =>
        (PeriodicLattice.compactGaugeGroup : Set ComplexMatrix2)) ∩
        {U | ∀ b, U b.opposite * U b = 1} := by
    ext U
    constructor
    · intro h
      refine ⟨fun b _ => h.1 b (Set.mem_univ _), fun b => ?_⟩
      rw [h.2 b (Set.mem_univ _)]
      exact Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_compact (h.1 b (Set.mem_univ _)))
    · rintro ⟨h1, h2⟩
      exact ⟨fun b _ => h1 b (Set.mem_univ _),
        fun b _ => Matrix.inv_eq_left_inv (h2 b) ▸ rfl⟩
  rw [e]
  exact h1.inter_right h2
private theorem meanRadius_bounded [Finite (Vertex L n k j)] (c : Edge L n k (j + 1)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ V ∈ fieldSpace L n k j, (meanRadius V c).re ≤ R := by
  have hcont : ContinuousOn (fun V : Edge L n k j → ComplexMatrix2 => contourMean V c)
      (fieldSpace L n k j) := fun V hV =>
    tendsto_contourMean (l := 𝓝[fieldSpace L n k j] V) (W := fun V => V) hV
      (fun b => ((continuous_apply b).tendsto V).mono_left nhdsWithin_le_nhds) c
  have hf : Continuous fun A : ComplexMatrix2 => Complex.normSq (A 0 0) + Complex.normSq (A 0 1) :=
    (Complex.continuous_normSq.comp (Continuous.matrix_elem continuous_id 0 0)).add
      (Complex.continuous_normSq.comp (Continuous.matrix_elem continuous_id 0 1))
  obtain ⟨C, hC⟩ := isCompact_fieldSpace.exists_bound_of_continuousOn (hf.comp_continuousOn hcont)
  refine ⟨|C| ^ (1 / 2 : ℝ), Real.rpow_nonneg (abs_nonneg _) _, fun V hV => ?_⟩
  haveI : Finite (Vertex L n k j) := inferInstance
  rw [meanRadius_eq hV c, Complex.ofReal_re]
  refine Real.rpow_le_rpow (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) ?_
    (by norm_num)
  exact (le_abs_self _).trans ((hC V hV).trans (le_abs_self _))
end Limits
section GaugeAction
variable {L n k : ℕ} [NeZero L]
variable (hC : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
include hC hL hn in
private theorem levelField_gaugeTransformPoint {Y : ChainPoint L n k}
    (hY : ∀ j, j < k → levelField Y j ∈ fieldSpace L n k j) {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ j, j ≤ k → levelField (gaugeTransformPoint v Y) j =
      PeriodicLattice.gaugeTransform (restrictVertexFunction j v) (levelField Y j) := by apply _root_.YangMills.SharedProofs.p78689 <;> assumption
include hC hL hn in
private theorem meanRadius_gaugeTransformPoint {Y : ChainPoint L n k}
    (hY : ∀ j, j < k → levelField Y j ∈ fieldSpace L n k j) {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    meanRadius (levelField (gaugeTransformPoint v Y) i) c.1 = meanRadius (levelField Y i) c.1 := by apply _root_.YangMills.SharedProofs.p13056 <;> assumption
include hC hL hn in
private theorem chainAction_gaugeTransformPoint (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (a : ℝ) (hk : 0 < k) {Y : ChainPoint L n k}
    (hY : ∀ j, j < k → levelField Y j ∈ fieldSpace L n k j) {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    chainAction a (gaugeTransformPoint v Y) = chainAction a Y := by apply _root_.YangMills.SharedProofs.p8575 <;> assumption
private theorem fine_gaugeTransformPoint_mem {Y : ChainPoint L n k}
    (hU : Y.fine ∈ fieldSpace L n k 0) {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    (gaugeTransformPoint v Y).fine ∈ fieldSpace L n k 0 := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · exact ComplexMatrix2.specialUnitary.mul_mem
      (ComplexMatrix2.specialUnitary.mul_mem (hv _) (hU.1 b (Set.mem_univ _))) (inv_mem_compact (hv _))
  · change v b.target * Y.fine b.opposite * (v b.source)⁻¹ =
      (v b.source * Y.fine b * (v b.target)⁻¹)⁻¹
    rw [hU.2 b (Set.mem_univ _), Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_compact (hv _))]
    simp only [mul_assoc]
end GaugeAction
section ShiftLast
variable {L n m : ℕ}
private theorem inv_opposite_eq {j : ℕ} {V : Edge L n (m + 1) j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n (m + 1) j PeriodicLattice.complexGaugeGroup) (b : Edge L n (m + 1) j) :
    (V b.opposite)⁻¹ = V b :=
  (hV.2 b.opposite (Set.mem_univ _)).symm
private theorem expTwist_zero {j : ℕ} {V : Edge L n (m + 1) j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n (m + 1) j PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist (0 : Edge L n (m + 1) j → ComplexMatrix2) V = V := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [PeriodicLattice.expTwist, if_pos hb, Pi.zero_apply]
    rw [matExp_I_smul_zero, one_mul]
  · simp only [PeriodicLattice.expTwist, if_neg hb, Pi.zero_apply]
    rw [matExp_I_smul_zero, one_mul, inv_opposite_eq hV]
private theorem expTwist_mem (hT : TowerFacts L n (m + 1)) {j : ℕ} (hj : j ≤ m + 1)
    {V : Edge L n (m + 1) j → ComplexMatrix2} (hV : V ∈ fieldSpace L n (m + 1) j)
    (M : edgeFormSpace L n (m + 1) j) (t : ℝ) :
    PeriodicLattice.expTwist (t • (M : Edge L n (m + 1) j → ComplexMatrix2)) V ∈
      fieldSpace L n (m + 1) j := by
  have hpos : ∀ b : Edge L n (m + 1) j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • ((t • (M : Edge L n (m + 1) j → ComplexMatrix2)) b)) *
        V b ∈ PeriodicLattice.compactGaugeGroup := by
    intro b hb
    have h := ((hT.leftExp j hj).1 V hV (M : Edge L n (m + 1) j → ComplexMatrix2) M.2 ⟨b, hb⟩).1 t
    have e : ((t : ℂ) • (M : Edge L n (m + 1) j → ComplexMatrix2) b) =
        (t • (M : Edge L n (m + 1) j → ComplexMatrix2)) b :=
      Complex.coe_smul _ _
    simp only [leftExpMul, LatticeData.onPositive, finiteData] at h
    rwa [e] at h
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb]
      exact hpos b hb
    · simp only [PeriodicLattice.expTwist, if_neg hb]
      exact inv_mem_compact (hpos _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb))
  · by_cases hb : b.IsPositivelyOriented
    · have hb' := not_opposite_pos hT hj hb
      simp only [PeriodicLattice.expTwist, if_pos hb, if_neg hb', edge_opposite_opposite]
    · have hb' : b.opposite.IsPositivelyOriented :=
        PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      simp only [PeriodicLattice.expTwist, if_pos hb', if_neg hb]
      rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_compact (hpos _ hb'))]
private def shiftLast (B : edgeFormSpace L n (m + 1) (m + 1)) (s : ℝ) (Y : ChainPoint L n (m + 1)) :
    ChainPoint L n (m + 1) :=
  expMove (s • lastNoiseTangent B) Y
private theorem shiftLast_fine (B : edgeFormSpace L n (m + 1) (m + 1)) (s : ℝ)
    {Y : ChainPoint L n (m + 1)}
    (hY : Y.fine ∈ fieldsIn L n (m + 1) 0 PeriodicLattice.complexGaugeGroup) :
    (shiftLast B s Y).fine = Y.fine := by
  have e : (((s • lastNoiseTangent B).1 : edgeFormSpace L n (m + 1) 0) :
      Edge L n (m + 1) 0 → ComplexMatrix2) = 0 := by
    simp [lastNoiseTangent]
  simp only [shiftLast, expMove]
  rw [e]
  exact expTwist_zero hY
private theorem shiftLast_noise_of_ne (B : edgeFormSpace L n (m + 1) (m + 1)) (s : ℝ)
    (Y : ChainPoint L n (m + 1)) {i : Fin (m + 1)} (hi : i ≠ Fin.last m)
    (c : PositiveEdge L n (m + 1) (i + 1)) : (shiftLast B s Y).noise i c = Y.noise i c := by
  have e : (((s • lastNoiseTangent B).2 i : edgeFormSpace L n (m + 1) (i + 1)) :
      Edge L n (m + 1) (i + 1) → ComplexMatrix2) = 0 := by
    simp [lastNoiseTangent, Pi.single_eq_of_ne hi]
  simp only [shiftLast, expMove]
  rw [e]
  simp only [Pi.zero_apply]
  rw [matExp_I_smul_zero, one_mul]
private theorem shiftLast_noise_last (B : edgeFormSpace L n (m + 1) (m + 1)) (s : ℝ)
    (Y : ChainPoint L n (m + 1)) (c : PositiveEdge L n (m + 1) (m + 1)) :
    (shiftLast B s Y).noise (Fin.last m) c =
      ComplexMatrix2.matExp (Complex.I • (s • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1)) *
        Y.noise (Fin.last m) c := by
  have e : (s • lastNoiseTangent B).2 (Fin.last m) = s • B := by
    simp only [lastNoiseTangent, Prod.smul_snd, Pi.smul_apply]
    rw [Pi.single_eq_same]
  simp only [shiftLast, expMove]
  rw [e]
  rfl
private theorem levelField_shiftLast_of_le (B : edgeFormSpace L n (m + 1) (m + 1)) (s : ℝ)
    {Y : ChainPoint L n (m + 1)}
    (hY : Y.fine ∈ fieldsIn L n (m + 1) 0 PeriodicLattice.complexGaugeGroup) :
    ∀ j, j ≤ m → levelField (shiftLast B s Y) j = levelField Y j := by
  intro j
  induction j with
  | zero =>
    intro _
    exact shiftLast_fine B s hY
  | succ j ih =>
    intro hj
    have h : j < m + 1 := by omega
    have hne : (⟨j, h⟩ : Fin (m + 1)) ≠ Fin.last m := by
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    rw [levelField_succ _ h, levelField_succ _ h, ih (by omega)]
    congr 1
    funext c
    rw [shiftLast_noise_of_ne B s Y hne]
private theorem levelField_shiftLast_top (B : edgeFormSpace L n (m + 1) (m + 1)) (s : ℝ)
    {Y : ChainPoint L n (m + 1)}
    (hY : Y.fine ∈ fieldsIn L n (m + 1) 0 PeriodicLattice.complexGaugeGroup) :
    levelField (shiftLast B s Y) (m + 1) =
      PeriodicLattice.expTwist (s • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2))
        (levelField Y (m + 1)) := by
  have h : m < m + 1 := Nat.lt_succ_self m
  have hpos : ∀ b : Edge L n (m + 1) (m + 1), b.IsPositivelyOriented →
      levelField (shiftLast B s Y) (m + 1) b =
        ComplexMatrix2.matExp
          (Complex.I • ((s • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2)) b)) *
          levelField Y (m + 1) b := by
    intro b hb
    rw [levelField_pos _ h hb, levelField_shiftLast_of_le B s hY m le_rfl, levelField_pos Y h hb]
    have e := shiftLast_noise_last B s Y ⟨b, hb⟩
    change (shiftLast B s Y).noise (Fin.last m) ⟨b, hb⟩ * _ =
      _ * (Y.noise (Fin.last m) ⟨b, hb⟩ * _)
    rw [e, mul_assoc]
    rfl
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [PeriodicLattice.expTwist, if_pos hb]
    exact hpos b hb
  · simp only [PeriodicLattice.expTwist, if_neg hb]
    rw [levelField_neg _ h hb, hpos _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb)]
private theorem shiftLast_compact (hT : TowerFacts L n (m + 1))
    (hEL : ComplexMatrix2.ExpLogEstimates)
    (B : edgeFormSpace L n (m + 1) (m + 1)) (s : ℝ) {Y : ChainPoint L n (m + 1)}
    (hY : IsCompactValued Y) : IsCompactValued (shiftLast B s Y) := by
  have hU := mem_complex_of_mem (hY.2 0 (Nat.zero_le _))
  refine ⟨fun i c => ?_, fun j hj => ?_⟩
  · by_cases hi : i = Fin.last m
    · subst hi
      rw [shiftLast_noise_last B s Y c]
      refine ComplexMatrix2.specialUnitary.mul_mem (matExp_mem_compact hEL ?_) (hY.1 _ _)
      exact (s • B).2.1 c.1 c.2
    · rw [shiftLast_noise_of_ne B s Y hi]
      exact hY.1 i c
  · rcases Nat.lt_or_ge j (m + 1) with h' | h'
    · rw [levelField_shiftLast_of_le B s hU j (by omega)]
      exact hY.2 j hj
    · obtain rfl : j = m + 1 := by omega
      rw [levelField_shiftLast_top B s hU]
      exact expTwist_mem hT le_rfl (hY.2 _ le_rfl) B s
private theorem shiftLast_shiftLast_neg (B : edgeFormSpace L n (m + 1) (m + 1)) (t : ℝ)
    {Y : ChainPoint L n (m + 1)}
    (hY : Y.fine ∈ fieldsIn L n (m + 1) 0 PeriodicLattice.complexGaugeGroup) :
    shiftLast B t (shiftLast B (-t) Y) = Y := by
  have hb := shiftLast_fine B (-t) hY
  have hY' : (shiftLast B (-t) Y).fine ∈
      fieldsIn L n (m + 1) 0 PeriodicLattice.complexGaugeGroup := by
    rw [hb]
    exact hY
  refine chainPoint_ext ((shiftLast_fine B t hY').trans hb) ?_
  funext i c
  by_cases hi : i = Fin.last m
  · subst hi
    rw [shiftLast_noise_last B t _ c, shiftLast_noise_last B (-t) _ c, ← mul_assoc, oneParam_mul,
      add_neg_cancel, oneParam_zero, one_mul]
  · rw [shiftLast_noise_of_ne B t _ hi, shiftLast_noise_of_ne B (-t) _ hi]
private theorem shiftLast_zero (B : edgeFormSpace L n (m + 1) (m + 1)) {Y : ChainPoint L n (m + 1)}
    (hY : Y.fine ∈ fieldsIn L n (m + 1) 0 PeriodicLattice.complexGaugeGroup) :
    shiftLast B 0 Y = Y := by
  refine chainPoint_ext (shiftLast_fine B 0 hY) ?_
  funext i c
  by_cases hi : i = Fin.last m
  · subst hi
    rw [shiftLast_noise_last B 0 _ c, oneParam_zero, one_mul]
  · rw [shiftLast_noise_of_ne B 0 _ hi]
private theorem expTwist_neg_expTwist (B : edgeFormSpace L n (m + 1) (m + 1)) (t : ℝ)
    {W : Edge L n (m + 1) (m + 1) → ComplexMatrix2}
    (hW : W ∈ fieldsIn L n (m + 1) (m + 1) PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist ((-t) • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2))
      (PeriodicLattice.expTwist (t • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2)) W) = W := by
  have hpos : ∀ b : Edge L n (m + 1) (m + 1), b.IsPositivelyOriented →
      ComplexMatrix2.matExp
          (Complex.I • (((-t) • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2)) b)) *
        (ComplexMatrix2.matExp
          (Complex.I • ((t • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2)) b)) * W b) = W b := by
    intro b _
    simp only [Pi.smul_apply]
    rw [← mul_assoc, oneParam_mul, neg_add_cancel, oneParam_zero, one_mul]
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [PeriodicLattice.expTwist, if_pos hb]
    exact hpos b hb
  · have hb' := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
    simp only [PeriodicLattice.expTwist, if_neg hb, if_pos hb']
    rw [hpos _ hb', inv_opposite_eq hW]
end ShiftLast
section FirstVariation
variable {L n m : ℕ}
private def lastNoise (Y : ChainPoint L n (m + 1)) (c : PositiveEdge L n (m + 1) (m + 1)) :
    ComplexMatrix2 :=
  Y.noise (Fin.last m) c
private def lastRadius (Y : ChainPoint L n (m + 1)) (c : PositiveEdge L n (m + 1) (m + 1)) : ℝ :=
  (meanRadius (levelField Y m) c.1).re
private def firstVariation [Fintype (PositiveEdge L n (m + 1) (m + 1))] (a : ℝ)
    (B : edgeFormSpace L n (m + 1) (m + 1)) (Y : ChainPoint L n (m + 1)) : ℝ :=
  a * ∑ c : PositiveEdge L n (m + 1) (m + 1), lastRadius Y c *
    (-reHalfTrace ((Complex.I • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1) *
      lastNoise Y c))
private def oneParamRemainder (B : edgeFormSpace L n (m + 1) (m + 1))
    (c : PositiveEdge L n (m + 1) (m + 1)) (s : ℝ) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (Complex.I • (s • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1)) -
    1 - s • (Complex.I • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1)
private theorem oneParamRemainder_isLittleO (B : edgeFormSpace L n (m + 1) (m + 1))
    (c : PositiveEdge L n (m + 1) (m + 1)) :
    (oneParamRemainder B c) =o[𝓝 0] fun s : ℝ => s := by
  have h := hasDerivAt_iff_isLittleO_nhds_zero.mp
    (hasDerivAt_oneParam ((B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1))
  simp only [zero_add, oneParam_zero] at h
  exact h
private theorem chainAction_shiftLast [Fintype (PositiveEdge L n (m + 1) (m + 1))] (a : ℝ)
    (B : edgeFormSpace L n (m + 1) (m + 1)) (s : ℝ) {Y : ChainPoint L n (m + 1)}
    (hY : Y.fine ∈ fieldsIn L n (m + 1) 0 PeriodicLattice.complexGaugeGroup) :
    chainAction a (shiftLast B s Y) = chainAction a Y +
      a * ∑ c : PositiveEdge L n (m + 1) (m + 1), lastRadius Y c *
        (traceDefect (ComplexMatrix2.matExp
          (Complex.I • (s • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1)) *
          lastNoise Y c) - traceDefect (lastNoise Y c)) := by
  have key : ∀ Z : ChainPoint L n (m + 1),
      (∑ᶠ c : PositiveEdge L n (m + 1) ((Fin.last m : Fin (m + 1)) + 1),
        (meanRadius (levelField Z (Fin.last m : Fin (m + 1))) c.1).re *
          traceDefect (Z.noise (Fin.last m) c)) =
      ∑ c : PositiveEdge L n (m + 1) (m + 1), lastRadius Z c * traceDefect (lastNoise Z c) :=
    fun Z => finsum_eq_sum_of_fintype (α := PositiveEdge L n (m + 1) (m + 1))
      (fun c => lastRadius Z c * traceDefect (lastNoise Z c))
  have hlow : ∀ i : Fin m,
      (∑ᶠ c : PositiveEdge L n (m + 1) ((Fin.castSucc i : Fin (m + 1)) + 1),
        (meanRadius (levelField (shiftLast B s Y) (Fin.castSucc i : Fin (m + 1))) c.1).re *
          traceDefect ((shiftLast B s Y).noise (Fin.castSucc i) c)) =
      ∑ᶠ c : PositiveEdge L n (m + 1) ((Fin.castSucc i : Fin (m + 1)) + 1),
        (meanRadius (levelField Y (Fin.castSucc i : Fin (m + 1))) c.1).re *
          traceDefect (Y.noise (Fin.castSucc i) c) := by
    intro i
    refine finsum_congr fun c => ?_
    rw [levelField_shiftLast_of_le B s hY _ (Fin.is_le (Fin.castSucc i)),
      shiftLast_noise_of_ne B s Y (Fin.castSucc_lt_last i).ne c]
  have htop : ∀ c, lastRadius (shiftLast B s Y) c * traceDefect (lastNoise (shiftLast B s Y) c) =
      lastRadius Y c * traceDefect (ComplexMatrix2.matExp
        (Complex.I • (s • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1)) *
          lastNoise Y c) := by
    intro c
    simp only [lastRadius, lastNoise]
    rw [levelField_shiftLast_of_le B s hY m le_rfl, shiftLast_noise_last B s Y c]
  unfold chainAction
  rw [shiftLast_fine B s hY, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc,
    Finset.sum_congr rfl fun i _ => hlow i, key, key, Finset.sum_congr rfl fun c _ => htop c]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring
private theorem chainAction_shiftLast_expansion [Fintype (PositiveEdge L n (m + 1) (m + 1))]
    [Finite (Vertex L n (m + 1) m)] {a : ℝ} (ha : 0 < a)
    (B : edgeFormSpace L n (m + 1) (m + 1)) {R : PositiveEdge L n (m + 1) (m + 1) → ℝ}
    (hR0 : ∀ c, 0 ≤ R c)
    (hR : ∀ c, ∀ V ∈ fieldSpace L n (m + 1) m, (meanRadius V c.1).re ≤ R c)
    {Y : ChainPoint L n (m + 1)} (hY : IsCompactValued Y) (s : ℝ) :
    |chainAction a (shiftLast B s Y) - chainAction a Y - s * firstVariation a B Y| ≤
      a * ∑ c : PositiveEdge L n (m + 1) (m + 1),
        R c * (‖reHalfTrace‖ * ‖oneParamRemainder B c s‖) := by
  have hU := mem_complex_of_mem (hY.2 0 (Nat.zero_le _))
  have hterm : ∀ c, lastRadius Y c * (traceDefect (ComplexMatrix2.matExp (Complex.I •
        (s • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1)) * lastNoise Y c) -
          traceDefect (lastNoise Y c)) -
      s * (lastRadius Y c * (-reHalfTrace
        ((Complex.I • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1) * lastNoise Y c))) =
      lastRadius Y c * (-reHalfTrace (oneParamRemainder B c s * lastNoise Y c)) := by
    intro c
    simp only [traceDefect_eq, oneParamRemainder, sub_mul, smul_mul_assoc, one_mul, map_sub,
      map_smul, smul_eq_mul]
    ring
  have e : chainAction a (shiftLast B s Y) - chainAction a Y - s * firstVariation a B Y =
      a * ∑ c : PositiveEdge L n (m + 1) (m + 1),
        lastRadius Y c * (-reHalfTrace (oneParamRemainder B c s * lastNoise Y c)) := by
    rw [chainAction_shiftLast a B s hU, firstVariation, ← Finset.sum_congr rfl fun c _ => hterm c,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [e, abs_mul, abs_of_pos ha]
  refine mul_le_mul_of_nonneg_left ?_ ha.le
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  have hl : 0 ≤ lastRadius Y c := meanRadius_re_nonneg (hY.2 m (Nat.le_succ m)) c.1
  have hle : lastRadius Y c ≤ R c := hR c _ (hY.2 m (Nat.le_succ m))
  have hn : ‖lastNoise Y c‖ = 1 := norm_of_mem_compact (hY.1 _ _)
  have h2 : |reHalfTrace (oneParamRemainder B c s * lastNoise Y c)| ≤
      ‖reHalfTrace‖ * ‖oneParamRemainder B c s‖ := by
    have h3 := reHalfTrace.le_opNorm (oneParamRemainder B c s * lastNoise Y c)
    rw [Real.norm_eq_abs] at h3
    refine h3.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    calc ‖oneParamRemainder B c s * lastNoise Y c‖
        ≤ ‖oneParamRemainder B c s‖ * ‖lastNoise Y c‖ := norm_mul_le _ _
      _ = ‖oneParamRemainder B c s‖ := by rw [hn, mul_one]
  rw [abs_mul, abs_neg, abs_of_nonneg hl]
  exact mul_le_mul hle h2 (abs_nonneg _) (hR0 c)
private theorem abs_firstVariation_le [Fintype (PositiveEdge L n (m + 1) (m + 1))]
    [Finite (Vertex L n (m + 1) m)] {a : ℝ} (ha : 0 < a)
    (B : edgeFormSpace L n (m + 1) (m + 1)) {R : PositiveEdge L n (m + 1) (m + 1) → ℝ}
    (hR0 : ∀ c, 0 ≤ R c)
    (hR : ∀ c, ∀ V ∈ fieldSpace L n (m + 1) m, (meanRadius V c.1).re ≤ R c)
    {Y : ChainPoint L n (m + 1)} (hY : IsCompactValued Y) :
    |firstVariation a B Y| ≤ a * ∑ c : PositiveEdge L n (m + 1) (m + 1),
      R c * (‖reHalfTrace‖ * ‖Complex.I • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1‖) := by
  rw [firstVariation, abs_mul, abs_of_pos ha]
  refine mul_le_mul_of_nonneg_left ?_ ha.le
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  have hl : 0 ≤ lastRadius Y c := meanRadius_re_nonneg (hY.2 m (Nat.le_succ m)) c.1
  have hle : lastRadius Y c ≤ R c := hR c _ (hY.2 m (Nat.le_succ m))
  have hn : ‖lastNoise Y c‖ = 1 := norm_of_mem_compact (hY.1 _ _)
  have h2 : |reHalfTrace ((Complex.I • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1) *
      lastNoise Y c)| ≤
      ‖reHalfTrace‖ * ‖Complex.I • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1‖ := by
    have h3 := reHalfTrace.le_opNorm
      ((Complex.I • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2) c.1) * lastNoise Y c)
    rw [Real.norm_eq_abs] at h3
    refine h3.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine (norm_mul_le _ _).trans ?_
    rw [hn, mul_one]
  rw [abs_mul, abs_neg, abs_of_nonneg hl]
  exact mul_le_mul hle h2 (abs_nonneg _) (hR0 c)
private theorem firstVariation_gaugeTransformPoint [NeZero L]
    [Fintype (PositiveEdge L n (m + 1) (m + 1))]
    (hC : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (a : ℝ) (B : edgeFormSpace L n (m + 1) (m + 1)) {Y : ChainPoint L n (m + 1)}
    (hY : ∀ j, j < m + 1 → levelField Y j ∈ fieldSpace L n (m + 1) j)
    {v : Vertex L n (m + 1) 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (h1 : ∀ y : Vertex L n (m + 1) (m + 1), restrictVertexFunction (m + 1) v y = 1) :
    firstVariation a B (gaugeTransformPoint v Y) = firstVariation a B Y := by
  have hl : ∀ c, lastRadius (gaugeTransformPoint v Y) c = lastRadius Y c := by
    intro c
    have h := meanRadius_gaugeTransformPoint hC hL hn hY hv (Fin.last m) c
    simp only [lastRadius]
    exact congrArg Complex.re h
  have hz : ∀ c, lastNoise (gaugeTransformPoint v Y) c = lastNoise Y c := by
    intro c
    change restrictVertexFunction (m + 1) v c.1.source * Y.noise (Fin.last m) c *
      (restrictVertexFunction (m + 1) v c.1.source)⁻¹ = _
    rw [h1]
    simp [lastNoise]
  simp only [firstVariation, hl, hz]
private theorem levelField_top_gaugeTransformPoint [NeZero L]
    (hC : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {Y : ChainPoint L n (m + 1)}
    (hY : ∀ j, j < m + 1 → levelField Y j ∈ fieldSpace L n (m + 1) j)
    {v : Vertex L n (m + 1) 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (h1 : ∀ y : Vertex L n (m + 1) (m + 1), restrictVertexFunction (m + 1) v y = 1) :
    levelField (gaugeTransformPoint v Y) (m + 1) = levelField Y (m + 1) := by
  rw [levelField_gaugeTransformPoint hC hL hn hY hv (m + 1) le_rfl]
  funext b
  simp [PeriodicLattice.gaugeTransform, h1]
private theorem tendsto_firstVariation [Fintype (PositiveEdge L n (m + 1) (m + 1))]
    (hT : TowerFacts L n (m + 1))
    {ρ : ℝ} (hρ : MeanNearIdentity L n (m + 1) ρ) {ι : Type*} {l : Filter ι}
    {X : ι → ChainPoint L n (m + 1)} {Y : ChainPoint L n (m + 1)} (hY : IsCompactValued Y)
    (hYn : ∀ j, j ≤ m + 1 → ∀ b, ComplexMatrix2.operatorNorm (levelField Y j b - 1) < ρ)
    (hb : ∀ b, Tendsto (fun q => (X q).fine b) l (𝓝 (Y.fine b)))
    (hn : ∀ i c, Tendsto (fun q => (X q).noise i c) l (𝓝 (Y.noise i c)))
    (a : ℝ) (B : edgeFormSpace L n (m + 1) (m + 1)) :
    Tendsto (fun q => firstVariation a B (X q)) l (𝓝 (firstVariation a B Y)) := by
  simp only [firstVariation]
  refine Tendsto.const_mul _ (tendsto_finsetSum _ fun c _ => ?_)
  have h1 : Tendsto (fun q => lastRadius (X q) c) l (𝓝 (lastRadius Y c)) :=
    (Complex.continuous_re.tendsto _).comp (tendsto_meanRadius hT hρ hY hYn hb hn (Fin.last m) c)
  have h2 : Tendsto (fun q => lastNoise (X q) c) l (𝓝 (lastNoise Y c)) := hn (Fin.last m) c
  refine h1.mul (Tendsto.neg ?_)
  exact (reHalfTrace.continuous.tendsto _).comp (tendsto_const_nhds.mul h2)
end FirstVariation
section NearMinimizers
variable {L n m : ℕ} [NeZero L]
private theorem firstVariation_near_minimizers [Fintype (PositiveEdge L n (m + 1) (m + 1))]
    (hT : TowerFacts L n (m + 1)) (hC : ContourMeanGaugeCovariant)
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {a ρ : ℝ}
    (hρ : MeanNearIdentity L n (m + 1) ρ) {ε₀ δ₀ : ℝ} (hε₀ : 0 < ε₀)
    (hnf : ∀ X : ChainPoint L n (m + 1), (∀ b, ComplexMatrix2.operatorNorm (X.fine b - 1) < ε₀) →
      (∀ i c, ComplexMatrix2.operatorNorm (X.noise i c - 1) < ε₀) →
      ∀ j, j ≤ m + 1 → ∀ b, ComplexMatrix2.operatorNorm (levelField X j b - 1) < ρ)
    (hS : ∀ X : ChainPoint L n (m + 1), IsCompactValued X →
      (∀ b, ComplexMatrix2.operatorNorm (levelField X (m + 1) b - 1) < δ₀) →
      chainAction a X < δ₀ →
      ∃ v : Vertex L n (m + 1) 0 → ComplexMatrix2, (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) ∧
        (∀ y : Vertex L n (m + 1) (m + 1), restrictVertexFunction (m + 1) v y = 1) ∧
        (∀ b, ComplexMatrix2.operatorNorm ((gaugeTransformPoint v X).fine b - 1) < ε₀ / 2) ∧
        ∀ i c, ComplexMatrix2.operatorNorm ((gaugeTransformPoint v X).noise i c - 1) < ε₀ / 2)
    {W : Edge L n (m + 1) (m + 1) → ComplexMatrix2}
    (hWn : ∀ b, ComplexMatrix2.operatorNorm (W b - 1) < δ₀)
    {X : ChainPoint L n (m + 1)} (hX : IsMinimizerOver a W X) (hs : chainAction a X < δ₀)
    (hO : ∀ X' : ChainPoint L n (m + 1), IsMinimizerOver a W X' →
      ∃ v : Vertex L n (m + 1) 0 → ComplexMatrix2, (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) ∧
        (∀ y : Vertex L n (m + 1) (m + 1), restrictVertexFunction (m + 1) v y = 1) ∧
        X' = gaugeTransformPoint v X)
    (B : edgeFormSpace L n (m + 1) (m + 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ Y : ChainPoint L n (m + 1), IsCompactValued Y → levelField Y (m + 1) = W →
      chainAction a Y < chainAction a X + δ →
        |firstVariation a B Y - firstVariation a B X| < ε := by
  by_contra hcon
  push Not at hcon
  have hd : ∀ q : ℕ, 0 < min (1 / ((q : ℝ) + 1)) (δ₀ - chainAction a X) := fun q =>
    lt_min (by positivity) (by linarith)
  choose Y hY hYW hYF hbad using fun q : ℕ => hcon _ (hd q)
  have hlt : ∀ q, chainAction a (Y q) < δ₀ := fun q => by
    have h1 := hYF q
    have h2 := min_le_right (1 / ((q : ℝ) + 1)) (δ₀ - chainAction a X)
    linarith
  have hW' : ∀ q b, ComplexMatrix2.operatorNorm (levelField (Y q) (m + 1) b - 1) < δ₀ :=
    fun q b => by
      rw [hYW q]
      exact hWn b
  choose v hvr hv1 hvb hvn using fun q => hS (Y q) (hY q) (hW' q) (hlt q)
  let Z : ℕ → ChainPoint L n (m + 1) := fun q => gaugeTransformPoint (v q) (Y q)
  have hYc : ∀ q j, j < m + 1 → levelField (Y q) j ∈ fieldSpace L n (m + 1) j :=
    fun q j hj => (hY q).2 j hj.le
  have hZF : ∀ q, chainAction a (Z q) = chainAction a (Y q) := fun q =>
    chainAction_gaugeTransformPoint hC hL hn hg a (Nat.succ_pos m) (hYc q) (hvr q)
  have hZW : ∀ q, levelField (Z q) (m + 1) = W := fun q =>
    (levelField_top_gaugeTransformPoint hC hL hn (hYc q) (hvr q) (hv1 q)).trans (hYW q)
  have hZs : ∀ q, firstVariation a B (Z q) = firstVariation a B (Y q) := fun q =>
    firstVariation_gaugeTransformPoint hC hL hn a B (hYc q) (hvr q) (hv1 q)
  letI hFb : Fintype (Edge L n (m + 1) 0) := @Fintype.ofFinite _ (hT.finEdge 0 (Nat.zero_le _))
  letI hFq : ∀ i : Fin (m + 1), Fintype (PositiveEdge L n (m + 1) ((i : ℕ) + 1)) := fun i =>
    @Fintype.ofFinite _ (hT.finPositive _ i.2)
  let p₀ : ChainCoords L n (m + 1) := (fun _ => 1, fun _ _ => 1)
  have hh : 0 ≤ ε₀ / 2 := by positivity
  have hq : ∀ q, (((Z q).fine, (Z q).noise) : ChainCoords L n (m + 1)) ∈
      Metric.closedBall p₀ (ε₀ / 2) := by
    intro q
    rw [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def]
    exact max_le ((pi_norm_le_iff_of_nonneg hh).mpr fun b => (hvb q b).le)
      ((pi_norm_le_iff_of_nonneg hh).mpr fun i =>
        (pi_norm_le_iff_of_nonneg hh).mpr fun c => (hvn q i c).le)
  obtain ⟨p, -, φ, hφ, hlim⟩ := (isCompact_closedBall p₀ (ε₀ / 2)).tendsto_subseq hq
  let Zl : ChainPoint L n (m + 1) := ⟨p.1, p.2⟩
  have hb : ∀ b, Tendsto (fun q => (Z (φ q)).fine b) atTop (𝓝 (Zl.fine b)) := fun b =>
    (((continuous_apply b).comp continuous_fst).tendsto p).comp hlim
  have hnz : ∀ i c, Tendsto (fun q => (Z (φ q)).noise i c) atTop (𝓝 (Zl.noise i c)) :=
    fun i c => by
      have hc : Continuous fun r : ChainCoords L n (m + 1) => r.2 i c :=
        (continuous_apply c).comp ((continuous_apply i).comp continuous_snd)
      exact (hc.tendsto p).comp hlim
  have hbn : ∀ b, ComplexMatrix2.operatorNorm (Zl.fine b - 1) < ε₀ := fun b => by
    have h := le_of_tendsto' ((hb b).sub_const (1 : ComplexMatrix2)).norm
      (fun q => (hvb (φ q) b).le)
    exact lt_of_le_of_lt h (by linarith)
  have hnn : ∀ i c, ComplexMatrix2.operatorNorm (Zl.noise i c - 1) < ε₀ := fun i c => by
    have h := le_of_tendsto' ((hnz i c).sub_const (1 : ComplexMatrix2)).norm
      (fun q => (hvn (φ q) i c).le)
    exact lt_of_le_of_lt h (by linarith)
  have hnear := hnf Zl hbn hnn
  have hnoise : ∀ i c, Zl.noise i c ∈ PeriodicLattice.compactGaugeGroup := fun i c =>
    isCompact_compactGroup.isClosed.mem_of_tendsto (hnz i c) (Eventually.of_forall fun q =>
      ComplexMatrix2.specialUnitary.mul_mem
        (ComplexMatrix2.specialUnitary.mul_mem (hvr _ _) ((hY _).1 i c)) (inv_mem_compact (hvr _ _)))
  have hbase : Zl.fine ∈ fieldSpace L n (m + 1) 0 :=
    isCompact_fieldSpace.isClosed.mem_of_tendsto (tendsto_pi_nhds.2 hb)
      (Eventually.of_forall fun q => fine_gaugeTransformPoint_mem ((hY _).2 0 (Nat.zero_le _)) (hvr _))
  have hZl : IsCompactValued Zl := compact_of_near hT hρ hnoise hbase hnear
  have hFl := tendsto_chainAction hT hρ hZl hnear hb hnz a
  have hFY : Tendsto (fun q => chainAction a (Y q)) atTop (𝓝 (chainAction a X)) := by
    have hup : Tendsto (fun q : ℕ => chainAction a X + 1 / ((q : ℝ) + 1)) atTop
        (𝓝 (chainAction a X)) := by
      simpa using tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun q => hX.le _ (hY q) (hYW q)) (fun q => ?_)
    have h1 := hYF q
    have h2 := min_le_left (1 / ((q : ℝ) + 1)) (δ₀ - chainAction a X)
    change chainAction a (Y q) ≤ chainAction a X + 1 / ((q : ℝ) + 1)
    linarith
  have hFe : chainAction a Zl = chainAction a X := by
    have h1 : Tendsto (fun q => chainAction a (Z (φ q))) atTop (𝓝 (chainAction a X)) := by
      simp only [hZF]
      exact hFY.comp hφ.tendsto_atTop
    exact tendsto_nhds_unique hFl h1
  have htop : levelField Zl (m + 1) = W := by
    funext b
    have h := tendsto_levelField hT hρ hZl hnear hb hnz (m + 1) le_rfl b
    simp only [hZW] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hleast : IsMinimizerOver a W Zl :=
    ⟨hZl, htop, fun X' h1 h2 => by rw [hFe]; exact hX.le X' h1 h2⟩
  obtain ⟨w, hwr, hw1, hw⟩ := hO Zl hleast
  have hse : firstVariation a B Zl = firstVariation a B X := by
    rw [hw]
    exact firstVariation_gaugeTransformPoint hC hL hn a B (fun j hj => hX.compact.2 j hj.le) hwr hw1
  have hsl := tendsto_firstVariation hT hρ hZl hnear hb hnz a B
  have h0 : Tendsto (fun q => |firstVariation a B (Z (φ q)) - firstVariation a B X|) atTop
      (𝓝 0) := by
    have h := (hsl.sub_const (firstVariation a B X)).abs
    rw [hse, sub_self, abs_zero] at h
    exact h
  have h1 : ε ≤ 0 := ge_of_tendsto' h0 fun q => by
    rw [hZs (φ q)]
    exact hbad (φ q)
  linarith
end NearMinimizers
section LastNoiseCarrier
variable {L n m : ℕ}
private def lastNoiseCarrier (W : Edge L n (m + 1) (m + 1) → ComplexMatrix2) :
    ChainPoint L n (m + 1) :=
  ⟨fun _ => 1, fun i => 1 + Pi.single (M := fun i : Fin (m + 1) =>
    PositiveEdge L n (m + 1) (i + 1) → ComplexMatrix2) (Fin.last m) (fun c => W c.1 - 1) i⟩
private theorem lastNoiseCarrier_noise_of_ne (W : Edge L n (m + 1) (m + 1) → ComplexMatrix2)
    {i : Fin (m + 1)} (hi : i ≠ Fin.last m) (c : PositiveEdge L n (m + 1) (i + 1)) :
    (lastNoiseCarrier W).noise i c = 1 := by
  simp [lastNoiseCarrier, Pi.single_eq_of_ne hi]
private theorem lastNoiseCarrier_noise_last (W : Edge L n (m + 1) (m + 1) → ComplexMatrix2)
    (c : PositiveEdge L n (m + 1) (m + 1)) :
    (lastNoiseCarrier W).noise (Fin.last m) c = W c.1 := by
  simp [lastNoiseCarrier]
private theorem fieldOfPositiveValues_one {j : ℕ} :
    fieldOfPositiveValues (fun _ : PositiveEdge L n (m + 1) j => (1 : ComplexMatrix2)) =
      fun _ => 1 := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [fieldOfPositiveValues_pos _ hb]
  · rw [fieldOfPositiveValues_neg _ hb]
    simp
private theorem levelField_lastNoiseCarrier_of_le (hT : TowerFacts L n (m + 1))
    (W : Edge L n (m + 1) (m + 1) → ComplexMatrix2) :
    ∀ j, j ≤ m → levelField (lastNoiseCarrier W) j = fun _ => 1 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have h : j < m + 1 := by omega
    have hne : (⟨j, h⟩ : Fin (m + 1)) ≠ Fin.last m := by
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    rw [levelField_succ _ h, ih (by omega)]
    have e : (fun c : PositiveEdge L n (m + 1) (j + 1) => (lastNoiseCarrier W).noise ⟨j, h⟩ c *
        normalizedMean (fun _ : Edge L n (m + 1) j => (1 : ComplexMatrix2)) c.1) = fun _ => 1 := by
      funext c
      rw [lastNoiseCarrier_noise_of_ne W hne, hT.mean_one j h c.1 c.2, one_mul]
    rw [e, fieldOfPositiveValues_one]
private theorem levelField_lastNoiseCarrier_top (hT : TowerFacts L n (m + 1))
    {W : Edge L n (m + 1) (m + 1) → ComplexMatrix2} (hW : W ∈ fieldSpace L n (m + 1) (m + 1)) :
    levelField (lastNoiseCarrier W) (m + 1) = W := by
  have h : m < m + 1 := Nat.lt_succ_self m
  rw [levelField_succ _ h, levelField_lastNoiseCarrier_of_le hT W m le_rfl]
  funext b
  have hav : ∀ c : PositiveEdge L n (m + 1) (m + 1), (lastNoiseCarrier W).noise ⟨m, h⟩ c *
      normalizedMean (fun _ : Edge L n (m + 1) m => (1 : ComplexMatrix2)) c.1 = W c.1 := by
    intro c
    rw [hT.mean_one m h c.1 c.2, mul_one]
    exact lastNoiseCarrier_noise_last W c
  by_cases hb : b.IsPositivelyOriented
  · rw [fieldOfPositiveValues_pos _ hb, hav ⟨b, hb⟩]
  · rw [fieldOfPositiveValues_neg _ hb, hav]
    exact (hW.2 b.opposite (Set.mem_univ _)).symm
private theorem lastNoiseCarrier_compact (hT : TowerFacts L n (m + 1))
    {W : Edge L n (m + 1) (m + 1) → ComplexMatrix2} (hW : W ∈ fieldSpace L n (m + 1) (m + 1)) :
    IsCompactValued (lastNoiseCarrier W) := by
  refine ⟨fun i c => ?_, fun j hj => ?_⟩
  · by_cases hi : i = Fin.last m
    · subst hi
      rw [lastNoiseCarrier_noise_last]
      exact hW.1 _ (Set.mem_univ _)
    · rw [lastNoiseCarrier_noise_of_ne W hi]
      exact ComplexMatrix2.specialUnitary.one_mem
  · rcases Nat.lt_or_ge j (m + 1) with h' | h'
    · rw [levelField_lastNoiseCarrier_of_le hT W j (by omega)]
      exact const_one_mem_fieldSpace
    · obtain rfl : j = m + 1 := by omega
      rw [levelField_lastNoiseCarrier_top hT hW]
      exact hW
end LastNoiseCarrier
section TopLevel
open scoped Quaternion
variable {L n k : ℕ}
private theorem exists_forwardFrom_topVertexOf (hlat : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (c : PositiveEdge L n k k) :
    ∃ (z : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4),
      c.1 = PeriodicLattice.Bond.forwardFrom (topVertexOf z) μ := by apply _root_.YangMills.SharedProofs.p10565 <;> assumption
private theorem towerFacts (hd : NormalizedMeanAtOne)
    (hCfg : Tower.LeftChartFields.Claim) (hS : Tower.FaceSums.FacesAndPairings)
    (hor : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : TowerFacts L n k := by
  have hPS := fun (j : ℕ) (hj : j ≤ k) => (hS L hL k j hj).1 n hn
  have finVertex : ∀ j, j ≤ k → Finite (Vertex L n k j) := fun j hj =>
    Set.finite_univ_iff.mp ((hPS j hj).2.1 univ).2.1
  refine
    { finVertex := finVertex
      finPositive := fun j hj => Set.finite_univ_iff.mp ((hPS j hj).2.2.1 univ).2.1
      finEdge := fun j hj => ?_
      finFace := Set.finite_univ_iff.mp ((hPS 0 (Nat.zero_le _)).2.2.2 univ).2.1
      xor_opposite := fun j hj b => ?_
      mean_one := fun j hj c hc =>
        (hd L hL n k j hn hj 0 (edgeFormSpace L n k j).zero_mem c hc).2.2.1
      leftExp := fun j hj => ((hCfg.2.2 L k j hL hj).1 n hn).1.1 }
  · haveI := finVertex j hj
    have h : Function.Injective (fun b : Edge L n k j => (b.source, b.target)) := by
      intro b b' hb
      exact PeriodicLattice.Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
    exact Finite.of_injective _ h
  · have h := (hor ⟨L, hL, 1, ⟨n, hn⟩⟩ (PeriodicLattice.levelDepth k j) (by
      change -(n : ℤ) < PeriodicLattice.levelDepth k j
      simp only [PeriodicLattice.levelDepth]
      omega)).1 b
    exact h.2.2.2.2.2
private theorem norm_inv_sub_one_le {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : ‖g⁻¹ - 1‖ ≤ ‖g - 1‖ := by
  have hi : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_compact hg)
  have e : g⁻¹ - 1 = g⁻¹ * (1 - g) := by
    rw [mul_sub, mul_one, hi]
  rw [e, ← norm_neg (g - 1), neg_sub]
  refine (norm_mul_le _ _).trans ?_
  rw [norm_of_mem_compact (inv_mem_compact hg), one_mul]
end TopLevel
open scoped Quaternion in
theorem minimalActionDerivAlongTopForm_holds (hO : MinimizersFormOneGaugeOrbit)
    (hS : SmallActionNearGaugeOrbit)
    (hC : ContourMeanGaugeCovariant)
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hP : NormalizedMeanNearOne)
    (hd : NormalizedMeanAtOne)
    (hCfg : Tower.LeftChartFields.Claim)
    (hPS : Tower.FaceSums.FacesAndPairings)
    (hEL : ComplexMatrix2.ExpLogEstimates)
    (hor : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hlat : PeriodicLattice.CoordinateDescription) :
    MinimalActionDerivAlongTopForm := by
  intro a ha L hL m n hn
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hT : TowerFacts L n (m + 1) := towerFacts hd hCfg hPS hor hL hn
  obtain ⟨ρ, hρ0, hρ'⟩ := hP L hL
  have hρ : MeanNearIdentity L n (m + 1) ρ := fun j hj V hV hVn c hc =>
    ⟨(hρ' n (m + 1) j hn hj V hV hVn c hc).1, (hρ' n (m + 1) j hn hj V hV hVn c hc).2.2.2.1⟩
  obtain ⟨ε₀, hε₀, hnf⟩ := near_unitPoint hT hρ0 hρ one_pos a
  obtain ⟨δ₀, hδ₀, hS'⟩ := hS a ha L hL (m + 1) n (by omega) hn (ε₀ / 2) (by positivity)
  obtain ⟨ε₁, hε₁, hnf₁⟩ := near_unitPoint hT hρ0 hρ hδ₀ a
  set η : ℝ := min δ₀ ε₁ with hη
  have hη0 : 0 < η := lt_min hδ₀ hε₁
  haveI : NeZero (2 * L ^ n) := ⟨by
    have := hL.2
    positivity⟩
  have hev : ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
      ∀ (z : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4),
      ‖SoftAverages.quaternionToMatrix
        ((V z μ : BlockAverages.UnitQuaternion) : Quaternion ℝ) - 1‖ < η := by
    refine eventually_all.2 fun z => eventually_all.2 fun μ => ?_
    have hc : Continuous fun V : TorusFields.TorusField (2 * L ^ n) =>
        ‖SoftAverages.quaternionToMatrix
          ((V z μ : BlockAverages.UnitQuaternion) : Quaternion ℝ) - 1‖ :=
      ((SoftAverages.continuous_quaternionToMatrix.comp (continuous_subtype_val.comp
        ((continuous_apply μ).comp (continuous_apply z)))).sub continuous_const).norm
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    have h1 : ((TorusFields.trivialField (2 * L ^ n) z μ : BlockAverages.UnitQuaternion) :
        Quaternion ℝ) = 1 :=
      rfl
    simp only [h1, SoftAverages.quaternionToMatrix_one, sub_self, norm_zero]
    exact hη0
  filter_upwards [hev, hO a ha L hL (m + 1) n (by omega) hn] with V hV hOV W hW X hX B
  have hWc := hW.1
  have hWp : ∀ b : Edge L n (m + 1) (m + 1), b.IsPositivelyOriented → ‖W b - 1‖ < η := by
    intro b hb
    obtain ⟨z, μ, hz⟩ := exists_forwardFrom_topVertexOf hlat hL hn ⟨b, hb⟩
    have e : b = PeriodicLattice.Bond.forwardFrom (topVertexOf z) μ := hz
    rw [e, hW.2 z μ]
    exact hV z μ
  have hWn : ∀ b : Edge L n (m + 1) (m + 1), ‖W b - 1‖ < η := by
    intro b
    by_cases hb : b.IsPositivelyOriented
    · exact hWp b hb
    · have hb' := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      have e : W b = (W b.opposite)⁻¹ := hWc.2 b.opposite (Set.mem_univ _)
      rw [e]
      exact (norm_inv_sub_one_le (hWc.1 _ (Set.mem_univ _))).trans_lt (hWp _ hb')
  have hWd : ∀ b : Edge L n (m + 1) (m + 1), ComplexMatrix2.operatorNorm (W b - 1) < δ₀ :=
    fun b => (hWn b).trans_le (min_le_left _ _)
  have hs : chainAction a X < δ₀ := by
    have h1 := hX.le (lastNoiseCarrier W) (lastNoiseCarrier_compact hT hWc)
      (levelField_lastNoiseCarrier_top hT hWc)
    have h2 := (hnf₁ (lastNoiseCarrier W) (fun b => ?_) (fun i c => ?_)).2
    · linarith
    · change ComplexMatrix2.operatorNorm ((1 : ComplexMatrix2) - 1) < ε₁
      simpa [ComplexMatrix2.operatorNorm] using hε₁
    · by_cases hi : i = Fin.last m
      · subst hi
        rw [lastNoiseCarrier_noise_last]
        exact (hWn c.1).trans_le (min_le_right _ _)
      · rw [lastNoiseCarrier_noise_of_ne W hi]
        simpa [ComplexMatrix2.operatorNorm] using hε₁
  letI hFt : Fintype (PositiveEdge L n (m + 1) (m + 1)) :=
    @Fintype.ofFinite _ (hT.finPositive _ le_rfl)
  haveI := hT.finVertex m (Nat.le_succ m)
  choose R hR0 hR using fun c : PositiveEdge L n (m + 1) (m + 1) =>
    meanRadius_bounded (L := L) (n := n) (k := m + 1) (j := m) c.1
  have hnm := fun (ε : ℝ) (hε : 0 < ε) => firstVariation_near_minimizers hT hC hg hL hn hρ hε₀
    (fun X h1 h2 => (hnf X h1 h2).1) hS' hWd hX hs (fun X' h => hOV W hW X X' hX h) B hε
  let K : ℝ → Set (ChainPoint L n (m + 1)) := fun t =>
    {Y | IsCompactValued Y ∧ levelField Y (m + 1) =
      PeriodicLattice.expTwist (t • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2)) W}
  have hK0 : ∀ Y, Y ∈ K 0 ↔ IsCompactValued Y ∧ levelField Y (m + 1) = W := by
    have e : PeriodicLattice.expTwist
        ((0 : ℝ) • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2)) W = W := by
      rw [zero_smul]
      exact expTwist_zero (mem_complex_of_mem hWc)
    intro Y
    simp only [K, mem_ofPred_eq, e]
  let e : ℝ → ℝ := fun s =>
    a * ∑ c : PositiveEdge L n (m + 1) (m + 1), R c * (‖reHalfTrace‖ * ‖oneParamRemainder B c s‖)
  have he : e =o[𝓝 0] fun s : ℝ => s := by
    have h : (fun s : ℝ => ∑ c : PositiveEdge L n (m + 1) (m + 1),
        R c * (‖reHalfTrace‖ * ‖oneParamRemainder B c s‖)) =o[𝓝 0] fun s : ℝ => s := by
      have hc : ∀ c ∈ (Finset.univ : Finset (PositiveEdge L n (m + 1) (m + 1))),
          (fun s : ℝ => R c * (‖reHalfTrace‖ * ‖oneParamRemainder B c s‖)) =o[𝓝 0]
            fun s : ℝ => s := fun c _ =>
        ((oneParamRemainder_isLittleO B c).norm_left.const_mul_left ‖reHalfTrace‖).const_mul_left
          (R c)
      refine (Asymptotics.IsLittleO.sum hc).congr_left fun s => ?_
      simp [Finset.sum_apply]
    exact h.const_mul_left a
  have hexp : ∀ s, ∀ y ∈ K 0, |chainAction a (shiftLast B s y) - chainAction a y -
      s * firstVariation a B y| ≤ e s := fun s y hy =>
    chainAction_shiftLast_expansion ha B hR0 hR ((hK0 y).1 hy).1 s
  have hXK : X ∈ K 0 := (hK0 X).2 ⟨hX.compact, hX.top_eq⟩
  have env := hasDerivAt_sInf_image (Ω := ChainPoint L n (m + 1)) (F := chainAction a)
    (p := firstVariation a B) (K := K) (T := shiftLast B) (e := e) (X := X)
    (fun t y hy => chainAction_nonneg hT ha hy.1)
    (fun t y hy => by
      obtain ⟨h1, h2⟩ := (hK0 y).1 hy
      refine ⟨shiftLast_compact hT hEL B t h1, ?_⟩
      rw [levelField_shiftLast_top B t (mem_complex_of_mem (h1.2 0 (Nat.zero_le _))), h2])
    (fun t y hy => by
      obtain ⟨h1, h2⟩ := hy
      have hU := mem_complex_of_mem (h1.2 0 (Nat.zero_le _))
      refine ⟨(hK0 _).2 ⟨shiftLast_compact hT hEL B (-t) h1, ?_⟩, shiftLast_shiftLast_neg B t hU⟩
      rw [levelField_shiftLast_top B (-t) hU, h2]
      exact expTwist_neg_expTwist B t (mem_complex_of_mem hWc))
    hexp he (fun y hy => abs_firstVariation_le ha B hR0 hR ((hK0 y).1 hy).1) hXK
    (fun y hy => hX.le y ((hK0 y).1 hy).1 ((hK0 y).1 hy).2)
    (fun ε hε => by
      obtain ⟨δ, hδ, h⟩ := hnm ε hε
      exact ⟨δ, hδ, fun y hy hF => h y ((hK0 y).1 hy).1 ((hK0 y).1 hy).2 hF⟩)
  have hU := mem_complex_of_mem (hX.compact.2 0 (Nat.zero_le _))
  have hder : HasDerivAt (fun t => chainAction a (shiftLast B t X)) (firstVariation a B X) 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, shiftLast_zero B hU, smul_eq_mul]
    refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound 1
      (Eventually.of_forall fun s => ?_)) he
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hexp s X hXK).trans (le_abs_self _)
  have e1 : leftDeriv (chainAction a) X (lastNoiseTangent B) = firstVariation a B X := hder.deriv
  rw [e1]
  have e2 : (fun t : ℝ => minimalChainAction a (PeriodicLattice.expTwist
      (t • (B : Edge L n (m + 1) (m + 1) → ComplexMatrix2)) W)) =
      fun t => sInf {s | ∃ y ∈ K t, s = chainAction a y} := by
    funext t
    simp only [minimalChainAction]
    congr 1
    ext s
    simp only [K, mem_ofPred_eq, and_assoc]
  rw [e2]
  exact env
end YangMills.Construction.RunningCouplingSlope.MinimalActionDerivProof
end
