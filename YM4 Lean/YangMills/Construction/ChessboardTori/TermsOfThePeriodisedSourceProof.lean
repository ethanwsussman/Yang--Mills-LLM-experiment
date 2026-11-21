import YangMills.Construction.ChessboardTori.ElementsCarryingLayersOfCellsProof
import YangMills.Construction.ChessboardTori.CopiesOfCellFunctionsProof
import YangMills.Construction.ChessboardTori.DistanceToFacePlanesAndOpenCells
import YangMills.Construction.ChessboardTori.ExponentialsOfObservablesOnTheLatticeProof
import YangMills.Construction.ChessboardTori.TermsOfThePeriodisedSource
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace PeriodizedSourceTerms
theorem mesh_lt_one (D : ChessboardSetup) : D.mesh < 1 := by
  have hL := D.one_lt_factor
  have hK : ((D.K : ℕ)) ≠ 0 := D.K.pos.ne'
  have h1 : (1 : ℝ) < (D.L : ℝ) ^ (D.K : ℕ) := one_lt_pow₀ hL hK
  have e : D.mesh = ((D.L : ℝ) ^ (D.K : ℕ))⁻¹ := by
    simp [ChessboardSetup.mesh, PeriodicLattice.meshSize, zpow_neg]
  rw [e]
  exact inv_lt_one_of_one_lt₀ h1
theorem norm_signedConj (σ : ℤˣ) (z : ℂ) : ‖Conventions.signedConj σ z‖ = ‖z‖ := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.norm_signedConj <;> assumption
theorem signedConj_zero (σ : ℤˣ) : Conventions.signedConj σ 0 = 0 := by
  unfold Conventions.signedConj
  split_ifs <;> simp
theorem signedConj_neg (σ : ℤˣ) (z : ℂ) :
    Conventions.signedConj (-σ) z = starRingEnd ℂ (Conventions.signedConj σ z) := by
  rcases Int.units_eq_one_or σ with rfl | rfl <;> simp [Conventions.signedConj]
variable {D : ChessboardSetup}
theorem center_apply (p : D.Plaquette) (μ : Fin 4) :
    p.center μ = (p.corner : AmbientSpace) μ + (if μ = p.lowAxis then D.mesh / 2 else 0) +
      (if μ = p.highAxis then D.mesh / 2 else 0) := by
  simp [InfiniteLattice.ElementaryPlaquette.center, Pi.single_apply]
theorem faceCorner_apply {p : D.Plaquette} {c : InfiniteLattice.LatticePoint D.mesh}
    (hc : c ∈ D.faceCorners p) (μ : Fin 4) :
    ∃ ε : ℝ, (ε = 0 ∨ ε = 1) ∧ (c : AmbientSpace) μ = (p.corner : AmbientSpace) μ + ε * D.mesh ∧
      (μ ≠ p.lowAxis → μ ≠ p.highAxis → ε = 0) := by
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  have e : ∀ ν κ : Fin 4,
      ((InfiniteLattice.axisStep D.mesh ν : InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) κ =
      if κ = ν then D.mesh else 0 := fun ν κ => by
    simp [InfiniteLattice.axisStep, Pi.single_apply]
  simp only [ChessboardSetup.faceCorners, mem_insert_iff, mem_singleton_iff] at hc
  by_cases h1 : μ = p.lowAxis
  · have h2 : μ ≠ p.highAxis := fun h => hne (h1.symm.trans h)
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨0, Or.inl rfl, by simp, fun _ _ => rfl⟩
    · exact ⟨1, Or.inr rfl, by simp [e, h1], fun h => absurd h1 h⟩
    · exact ⟨1, Or.inr rfl, by simp [e, h1, hne], fun h => absurd h1 h⟩
    · exact ⟨0, Or.inl rfl, by simp [e, h2], fun _ _ => rfl⟩
  · by_cases h2 : μ = p.highAxis
    · rcases hc with rfl | rfl | rfl | rfl
      · exact ⟨0, Or.inl rfl, by simp, fun _ _ => rfl⟩
      · exact ⟨0, Or.inl rfl, by simp [e, h1], fun _ _ => rfl⟩
      · exact ⟨1, Or.inr rfl, by simp [e, h2, hne.symm], fun _ h => absurd h2 h⟩
      · exact ⟨1, Or.inr rfl, by simp [e, h2], fun _ h => absurd h2 h⟩
    · rcases hc with rfl | rfl | rfl | rfl
      · exact ⟨0, Or.inl rfl, by simp, fun _ _ => rfl⟩
      · exact ⟨0, Or.inl rfl, by simp [e, h1], fun _ _ => rfl⟩
      · exact ⟨0, Or.inl rfl, by simp [e, h1, h2], fun _ _ => rfl⟩
      · exact ⟨0, Or.inl rfl, by simp [e, h2], fun _ _ => rfl⟩
theorem faceCorner_mem_Icc_center {p : D.Plaquette} {c : InfiniteLattice.LatticePoint D.mesh}
    (hc : c ∈ D.faceCorners p) (μ : Fin 4) :
    (c : AmbientSpace) μ ∈ Icc (p.center μ - D.mesh / 2) (p.center μ + D.mesh / 2) := by
  obtain ⟨ε, hε, h, h0⟩ := faceCorner_apply hc μ
  have ha := D.mesh_pos
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  rw [center_apply, h]
  by_cases h1 : μ = p.lowAxis
  · have h2 : μ ≠ p.highAxis := fun h => hne (h1.symm.trans h)
    rw [if_pos h1, if_neg h2]
    rcases hε with rfl | rfl <;> constructor <;> linarith
  · by_cases h2 : μ = p.highAxis
    · rw [if_neg h1, if_pos h2]
      rcases hε with rfl | rfl <;> constructor <;> linarith
    · rw [if_neg h1, if_neg h2, h0 h1 h2]
      constructor <;> linarith
theorem finite_setOf_center_mem {S : Set AmbientSpace} (hS : Bornology.IsBounded S) :
    {p : D.Plaquette | p.center ∈ S}.Finite := by apply _root_.YangMills.Construction.ChessboardTori.ExponentialObservableRules.finite_setOf_center_mem <;> assumption
variable {g : ReflectionGrid D}
theorem continuous_of_isProductOfCoordMaps (g : ReflectionGrid D) {r : AmbientSpace → AmbientSpace}
    (h : g.IsProductOfCoordMaps r) : Continuous r := by apply _root_.YangMills.Construction.ChessboardTori.CellFunctionCopies.continuous_of_isProductOfCoordMaps <;> assumption
theorem not_mem_walls_of_far {Q : Set AmbientSpace}
    (hfar : ∀ x ∈ Q, ∀ y ∈ g.walls, 1 ≤ TorusMetric.euclidNormVec (x - y))
    {x : AmbientSpace} (hx : x ∈ Q) : x ∉ g.walls := fun h => by
  have h1 := hfar x hx x h
  simp [TorusMetric.euclidNormVec] at h1
  linarith
theorem euclidNormVec_sub_lt_one {x y : AmbientSpace}
    (h : ∀ μ, y μ ∈ Icc (x μ - D.mesh / 2) (x μ + D.mesh / 2)) :
    TorusMetric.euclidNormVec (x - y) < 1 := by
  have ha := D.mesh_pos
  have hs : ∀ μ, (x - y) μ ^ 2 ≤ (D.mesh / 2) ^ 2 := fun μ => by
    have h1 := (h μ).1
    have h2 := (h μ).2
    simp only [Pi.sub_apply]
    exact sq_le_sq' (by linarith) (by linarith)
  have hsum : ∑ μ, (x - y) μ ^ 2 ≤ D.mesh ^ 2 := by
    rw [Fin.sum_univ_four]
    nlinarith [hs 0, hs 1, hs 2, hs 3]
  calc TorusMetric.euclidNormVec (x - y) ≤ Real.sqrt (D.mesh ^ 2) := Real.sqrt_le_sqrt hsum
    _ = D.mesh := Real.sqrt_sq ha.le
    _ < 1 := mesh_lt_one D
theorem faceCorner_mem_interior (hd : g.DistToWalls) {S : Set AmbientSpace} (hS : S ∈ g.cellSet)
    {Q : Set AmbientSpace} (hQS : Q ⊆ interior S)
    (hfar : ∀ x ∈ Q, ∀ y ∈ g.walls, 1 ≤ TorusMetric.euclidNormVec (x - y))
    {p : D.Plaquette} (hp : p.center ∈ Q) {c : InfiniteLattice.LatticePoint D.mesh}
    (hc : c ∈ D.faceCorners p) : (c : AmbientSpace) ∈ interior S := by
  have ha := D.mesh_pos
  let C : Set AmbientSpace :=
    Set.pi univ fun μ => Icc (p.center μ - D.mesh / 2) (p.center μ + D.mesh / 2)
  have hconv : Convex ℝ C := convex_pi fun μ _ => convex_Icc _ _
  have hdisj : Disjoint C g.walls := by
    rw [Set.disjoint_left]
    intro y hy hyP
    have h1 := hfar _ hp y hyP
    have h2 := euclidNormVec_sub_lt_one (D := D) (x := p.center) (y := y)
      fun μ => hy μ (mem_univ μ)
    linarith
  obtain ⟨S', hS', hC⟩ := hd.2.2.2 C hconv hdisj
  have hx : p.center ∈ C := fun μ _ => ⟨by linarith, by linarith⟩
  have hEq : S' = S :=
    (hd.2.1 _ (not_mem_walls_of_far hfar hp)).unique ⟨hS', hC hx⟩ ⟨hS, hQS hp⟩
  rw [← hEq]
  exact hC fun μ _ => faceCorner_mem_Icc_center hc μ
def extendByOne (B : Set D.Link) (u : B → Conventions.StandingParameters.gaugeGroup) (b : D.Link) :
    Conventions.StandingParameters.gaugeGroup :=
  open Classical in if h : b ∈ B then u ⟨b, h⟩ else 1
def energyOfFour
    (t : Conventions.StandingParameters.gaugeGroup × Conventions.StandingParameters.gaugeGroup ×
      Conventions.StandingParameters.gaugeGroup × Conventions.StandingParameters.gaugeGroup) : ℝ :=
  1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
    ((t.1 * t.2.1 * t.2.2.1⁻¹ * t.2.2.2⁻¹ : Conventions.StandingParameters.gaugeGroup) :
      Matrices.ComplexMatrix2)).re
theorem continuous_energyOfFour : Continuous energyOfFour := by
  have hv : Continuous fun t : Conventions.StandingParameters.gaugeGroup ×
      Conventions.StandingParameters.gaugeGroup × Conventions.StandingParameters.gaugeGroup ×
      Conventions.StandingParameters.gaugeGroup =>
      t.1 * t.2.1 * t.2.2.1⁻¹ * t.2.2.2⁻¹ := by fun_prop
  have ht : Continuous fun t : Conventions.StandingParameters.gaugeGroup ×
      Conventions.StandingParameters.gaugeGroup × Conventions.StandingParameters.gaugeGroup ×
      Conventions.StandingParameters.gaugeGroup =>
      Matrices.ComplexMatrix2.fullTrace
        ((t.1 * t.2.1 * t.2.2.1⁻¹ * t.2.2.2⁻¹ : Conventions.StandingParameters.gaugeGroup) :
          Matrices.ComplexMatrix2) :=
    (continuous_subtype_val.comp hv).matrix_trace
  unfold energyOfFour
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp ht))
theorem faceEnergy_eq_energyOfFour (U : D.Link → Conventions.StandingParameters.gaugeGroup)
    (p : D.Plaquette) :
    InfiniteLattice.faceEnergy U p = energyOfFour
      (U (InfiniteLattice.Link.forwardFrom p.corner p.lowAxis),
        U (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep D.mesh p.lowAxis)
          p.highAxis),
        U (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep D.mesh p.highAxis)
          p.lowAxis),
        U (InfiniteLattice.Link.forwardFrom p.corner p.highAxis)) := rfl
theorem measurable_extendByOne (B : Set D.Link) (b : D.Link) :
    Measurable fun u : B → Conventions.StandingParameters.gaugeGroup => extendByOne B u b := by
  unfold extendByOne
  by_cases h : b ∈ B
  · simp only [h, dite_true]
    exact measurable_pi_apply _
  · simp only [h, dite_false]
    exact measurable_const
theorem measurable_faceEnergy_extendByOne (B : Set D.Link) (p : D.Plaquette) :
    Measurable fun u : B → Conventions.StandingParameters.gaugeGroup =>
      InfiniteLattice.faceEnergy (extendByOne B u) p := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Conventions.StandingParameters.gaugeGroup :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have h := continuous_energyOfFour.measurable
  simp only [faceEnergy_eq_energyOfFour]
  exact h.comp ((measurable_extendByOne B _).prodMk ((measurable_extendByOne B _).prodMk
    ((measurable_extendByOne B _).prodMk (measurable_extendByOne B _))))
theorem exp_smeared_mem_cellObservables (hd : g.DistToWalls) {S : Set AmbientSpace}
    (hS : S ∈ g.cellSet) {v : AmbientSpace → ℂ} {Q : Set AmbientSpace}
    (hv0 : ∀ x, x ∉ Q → v x = 0) (hQ : IsCompact Q) (hQS : Q ⊆ interior S)
    (hfar : ∀ x ∈ Q, ∀ y ∈ g.walls, 1 ≤ TorusMetric.euclidNormVec (x - y)) :
    (fun U => Complex.exp (D.smeared v U)) ∈ ReflectionGrid.cellObservables (D := D) S := by
  classical
  have hfin : {p : D.Plaquette | p.center ∈ Q}.Finite := finite_setOf_center_mem hQ.isBounded
  set P : Finset D.Plaquette := hfin.toFinset with hP
  let B : Set D.Link := ReflectionGrid.interiorLinks (D := D) S
  let f : (ReflectionGrid.interiorLinks (D := D) S → Conventions.StandingParameters.gaugeGroup) → ℂ :=
    fun u => Complex.exp (∑ p ∈ P, InfiniteLattice.faceEnergy (extendByOne B u) p • v p.center)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ t, ‖energyOfFour t‖ ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      continuous_energyOfFour.continuousOn
    exact ⟨C, fun t => hC t (mem_univ t)⟩
  refine ⟨f, ?_, ⟨Real.exp (∑ p ∈ P, C * ‖v p.center‖), fun u => ?_⟩, ?_⟩
  · refine Complex.measurable_exp.comp (Finset.measurable_sum _ fun p _ => ?_)
    have h1 : Measurable fun u : ReflectionGrid.interiorLinks (D := D) S →
        Conventions.StandingParameters.gaugeGroup =>
        ((InfiniteLattice.faceEnergy (extendByOne B u) p : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (measurable_faceEnergy_extendByOne B p)
    simpa [Complex.real_smul] using h1.mul_const (v p.center)
  · simp only [f]
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_))
    refine Finset.sum_le_sum fun p _ => ?_
    rw [norm_smul, faceEnergy_eq_energyOfFour]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · funext U
    simp only [Function.comp, f]
    congr 1
    have hsub : Function.support (fun p : D.Plaquette =>
        InfiniteLattice.faceEnergy U p • v p.center) ⊆ (P : Set D.Plaquette) := by
      intro p hp
      rw [hP, Set.Finite.coe_toFinset]
      by_contra hq
      exact hp (by simp [hv0 _ hq])
    simp only [ChessboardSetup.smeared, InfiniteLattice.smearedEnergy]
    rw [finsum_eq_sum_of_support_subset _ hsub]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpQ : p.center ∈ Q := by
      have := hp
      rwa [hP, Set.Finite.mem_toFinset] at this
    have hcorner : ∀ c ∈ D.faceCorners p, (c : AmbientSpace) ∈ interior S := fun c hc =>
      faceCorner_mem_interior hd hS hQS hfar hpQ hc
    have hlink : ∀ b : D.Link, b.initial ∈ D.faceCorners p → b.terminal ∈ D.faceCorners p →
        extendByOne B (ReflectionGrid.restrictField S U) b = U b := fun b ht hh => by
      have hb : b ∈ B := ⟨hcorner _ ht, hcorner _ hh⟩
      simp only [extendByOne, hb, dite_true]
      rfl
    have c0 : p.corner ∈ D.faceCorners p := by simp [ChessboardSetup.faceCorners]
    have c1 : p.corner + InfiniteLattice.axisStep D.mesh p.lowAxis ∈ D.faceCorners p := by
      simp [ChessboardSetup.faceCorners]
    have c2 : p.corner + InfiniteLattice.axisStep D.mesh p.lowAxis +
        InfiniteLattice.axisStep D.mesh p.highAxis ∈ D.faceCorners p := by
      simp [ChessboardSetup.faceCorners]
    have c3 : p.corner + InfiniteLattice.axisStep D.mesh p.highAxis ∈ D.faceCorners p := by
      simp [ChessboardSetup.faceCorners]
    have c2' : p.corner + InfiniteLattice.axisStep D.mesh p.highAxis +
        InfiniteLattice.axisStep D.mesh p.lowAxis ∈ D.faceCorners p := by
      rw [add_right_comm]
      exact c2
    have key := faceEnergy_eq_energyOfFour (extendByOne B (ReflectionGrid.restrictField S U)) p
    rw [hlink (InfiniteLattice.Link.forwardFrom p.corner p.lowAxis) c0 c1,
      hlink (InfiniteLattice.Link.forwardFrom _ p.highAxis) c1 c2,
      hlink (InfiniteLattice.Link.forwardFrom _ p.lowAxis) c3 c2',
      hlink (InfiniteLattice.Link.forwardFrom p.corner p.highAxis) c0 c3] at key
    have hcancelled' : InfiniteLattice.faceEnergy (extendByOne B (ReflectionGrid.restrictField S U)) p =
        InfiniteLattice.faceEnergy U p := key
    rw [hcancelled']
theorem mem_of_signedConj_ne_zero {v : AmbientSpace → ℂ} {Q : Set AmbientSpace}
    (hv0 : ∀ x, x ∉ Q → v x = 0) {σ : ℤˣ} {y : AmbientSpace}
    (h : Conventions.signedConj σ (v y) ≠ 0) : y ∈ Q := by
  by_contra hy
  exact h (by rw [hv0 y hy, signedConj_zero])
theorem eq_one_of_mapsTo_self (hd : g.DistToWalls) (hG : g.ReflectionGroupCoordForm)
    {S : Set AmbientSpace} (hS : S ∈ g.cellSet) {Q : Set AmbientSpace} (hQS : Q ⊆ interior S)
    (hfar : ∀ x ∈ Q, ∀ y ∈ g.walls, 1 ≤ TorusMetric.euclidNormVec (x - y))
    (t : g.reflectionGroup) {y : AmbientSpace} (hy : y ∈ Q) (hty : t.1 y ∈ Q) : t = 1 := by
  let e : AmbientSpace ≃ₜ AmbientSpace :=
    { toEquiv := t.1
      continuous_toFun := continuous_of_isProductOfCoordMaps g (hG.1 t.1 t.2)
      continuous_invFun := continuous_of_isProductOfCoordMaps g (hG.1 _ (inv_mem t.2)) }
  have himg : (t.1 : AmbientSpace → AmbientSpace) '' interior S =
      interior ((t.1 : AmbientSpace → AmbientSpace) '' S) :=
    e.image_interior S
  have hS' : (t.1 : AmbientSpace → AmbientSpace) '' S ∈ g.cellSet := hG.2.2.2.2.2.1 t.1 t.2 S hS
  have hz : t.1 y ∈ interior ((t.1 : AmbientSpace → AmbientSpace) '' S) := by
    rw [← himg]
    exact ⟨y, hQS hy, rfl⟩
  have hEq : (t.1 : AmbientSpace → AmbientSpace) '' S = S :=
    (hd.2.1 _ (not_mem_walls_of_far hfar hty)).unique ⟨hS', hz⟩ ⟨hS, hQS hty⟩
  exact (hG.2.2.2.2.2.2.1 S hS S hS).unique hEq (by simp)
theorem orientationSign_reflectPerm (hG : g.ReflectionGroupCoordForm) (μ : Fin 4) (k : ℤ) :
    orientationSign (g.reflectPerm μ k) = -1 := by apply _root_.YangMills.Construction.ChessboardTori.LayerCarryingElements.orientationSign_reflect <;> assumption
theorem center_mem_wall_of_straddles {p : D.Plaquette} {b : D.Link} (hb : D.IsEdgeOf b p)
    {μ : Fin 4} {k : ℤ} (hc : g.Straddles b μ k) : p.center ∈ g.wall μ k := by
  have ha := D.mesh_pos
  obtain ⟨ε, hε, h1, h1'⟩ := faceCorner_apply hb.1 μ
  obtain ⟨ε', hε', h2, h2'⟩ := faceCorner_apply hb.2 μ
  obtain ⟨n, hn⟩ := p.corner.2
  obtain ⟨i, hi⟩ := g.origin_mem μ
  have hside := g.cellSide_eq
  have hbetween : ((p.corner : AmbientSpace) μ < g.origin μ + k * g.cellSide ∧
      g.origin μ + k * g.cellSide < (p.corner : AmbientSpace) μ + D.mesh) ∧
      (μ = p.lowAxis ∨ μ = p.highAxis) := by
    have hdir : ¬ (μ ≠ p.lowAxis ∧ μ ≠ p.highAxis) → (μ = p.lowAxis ∨ μ = p.highAxis) := by
      tauto
    rcases hc with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h1] at * <;> rw [h2] at * <;>
      rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl
    all_goals first
      | (exfalso; linarith)
      | (refine ⟨⟨by linarith, by linarith⟩, hdir ?_⟩
         rintro ⟨h5, h6⟩
         first
           | exact absurd (h1' h5 h6) one_ne_zero
           | exact absurd (h2' h5 h6) one_ne_zero)
  obtain ⟨⟨h3, h4⟩, hdir⟩ := hbetween
  have hplane : g.origin μ + k * g.cellSide = ((i + k * g.cellRatio : ℤ) + 1 / 2 : ℝ) * D.mesh := by
    rw [hi, hside]
    push_cast
    ring
  rw [hplane, hn μ] at h3 h4
  have h5 : (n μ : ℝ) < ((i + k * g.cellRatio : ℤ) : ℝ) + 1 / 2 := lt_of_mul_lt_mul_right h3 ha.le
  have h6 : ((i + k * g.cellRatio : ℤ) : ℝ) + 1 / 2 < (n μ : ℝ) + 1 :=
    lt_of_mul_lt_mul_right (by linarith) ha.le
  have h7 : n μ < (i + k * g.cellRatio) + 1 := by
    have : (n μ : ℝ) < ((i + k * g.cellRatio : ℤ) : ℝ) + 1 := by linarith
    exact_mod_cast this
  have h8 : (i + k * g.cellRatio) < n μ + 1 := by
    have : ((i + k * g.cellRatio : ℤ) : ℝ) < (n μ : ℝ) + 1 := by linarith
    exact_mod_cast this
  have h9 : i + k * g.cellRatio = n μ := by omega
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  show p.center μ = g.origin μ + k * g.cellSide
  rw [hplane, h9, center_apply, hn μ]
  rcases hdir with h | h
  · have h' : μ ≠ p.highAxis := fun e => hne (h.symm.trans e)
    rw [if_pos h, if_neg h']
    ring
  · have h' : μ ≠ p.lowAxis := fun e => hne (e.symm.trans h)
    rw [if_neg h', if_pos h]
    ring
theorem statement_holds (h₁ : WallDistanceAndOpenCells.Statement)
    (h₂ : ReflectionGroupCoordinates.Statement) : PeriodizedSourceTerms.Statement := by
  intro D g _ S hS v Q hvb hv0 hQ hQS hfar
  have hd := h₁ D g
  have hG := h₂ D g
  have hsub : ∀ x, {r : g.reflectionGroup |
      Conventions.signedConj (orientationSign r.1) (v (r.1⁻¹ x)) ≠ 0}.Subsingleton := by
    intro x r hr s hs
    have hy := mem_of_signedConj_ne_zero hv0 hr
    have hz := mem_of_signedConj_ne_zero hv0 hs
    have hty : (s⁻¹ * r : g.reflectionGroup).1 (r.1⁻¹ x) ∈ Q := by
      have e : (s⁻¹ * r : g.reflectionGroup).1 (r.1⁻¹ x) = s.1⁻¹ x := by simp
      rwa [e]
    exact (inv_mul_eq_one.mp (eq_one_of_mapsTo_self hd hG hS hQS hfar _ hy hty)).symm
  refine ⟨exp_smeared_mem_cellObservables hd hS hv0 hQ hQS hfar, hsub, ?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hvb
    refine ⟨C, fun x => ?_⟩
    change ‖∑ᶠ r : g.reflectionGroup, Conventions.signedConj (orientationSign r.1) (v (r.1⁻¹ x))‖ ≤ C
    by_cases hne : ∃ r : g.reflectionGroup,
        Conventions.signedConj (orientationSign r.1) (v (r.1⁻¹ x)) ≠ 0
    · obtain ⟨r, hr⟩ := hne
      have e : (∑ᶠ s : g.reflectionGroup,
          Conventions.signedConj (orientationSign s.1) (v (s.1⁻¹ x))) =
          Conventions.signedConj (orientationSign r.1) (v (r.1⁻¹ x)) :=
        finsum_eq_single _ r fun s hs => by
          by_contra h
          exact hs (hsub x h hr)
      rw [e, norm_signedConj]
      exact hC _
    · have hz : ∀ r : g.reflectionGroup,
          Conventions.signedConj (orientationSign r.1) (v (r.1⁻¹ x)) = 0 := fun r => by
        by_contra h
        exact hne ⟨r, h⟩
      rw [finsum_eq_zero_of_forall_eq_zero hz, norm_zero]
      exact (norm_nonneg _).trans (hC 0)
  · intro μ k
    funext x
    let θ : g.reflectionGroup := ⟨g.reflectPerm μ k, Subgroup.subset_closure ⟨(μ, k), rfl⟩⟩
    have hfin : (Function.support fun r : g.reflectionGroup =>
        Conventions.signedConj (orientationSign r.1) (v (r.1⁻¹ x))).Finite := (hsub x).finite
    have hconj := (starRingEnd ℂ).toAddMonoidHom.map_finsum hfin
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at hconj
    simp only [Function.comp]
    rw [hconj, ← finsum_comp_equiv (Equiv.mulLeft θ)]
    refine finsum_congr fun r => ?_
    have harg : ((Equiv.mulLeft θ) r).1⁻¹ (g.reflect μ k x) = r.1⁻¹ x := by
      have e : θ.1⁻¹ (g.reflect μ k x) = x := by
        change (g.reflectPerm μ k)⁻¹ ((g.reflectPerm μ k) x) = x
        simp
      change (θ.1 * r.1)⁻¹ (g.reflect μ k x) = r.1⁻¹ x
      rw [mul_inv_rev, Equiv.Perm.mul_apply, e]
    have hsgn : orientationSign ((Equiv.mulLeft θ) r).1 = - orientationSign r.1 := by
      have e := hG.2.2.2.1 θ.1 θ.2 r.1 r.2
      have e' : orientationSign θ.1 = -1 := orientationSign_reflectPerm hG μ k
      change orientationSign (θ.1 * r.1 : Equiv.Perm AmbientSpace) = _
      rw [e, e']
      simp
    rw [harg, hsgn, signedConj_neg]
  · rintro p ⟨b, hb, μ, k, hc⟩
    have hx : p.center ∈ g.walls :=
      mem_iUnion.mpr ⟨μ, mem_iUnion.mpr ⟨k, center_mem_wall_of_straddles hb hc⟩⟩
    refine finsum_eq_zero_of_forall_eq_zero fun r => ?_
    by_contra hne
    have hy := mem_of_signedConj_ne_zero hv0 hne
    have hmem : r.1⁻¹ p.center ∈ g.walls := by
      rw [← hG.2.2.2.2.1 _ (inv_mem r.2)]
      exact ⟨_, hx, rfl⟩
    exact not_mem_walls_of_far hfar hy hmem
end PeriodizedSourceTerms
end YangMills.Construction.ChessboardTori
end
