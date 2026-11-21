import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometriesProof
import YangMills.Construction.Towers.AverageIsDifferentiableOnThePolydiscProof
import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroupProof
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChartProof
import YangMills.Construction.Towers.CovariantAveragesAsDifferentials
import YangMills.Construction.Towers.DerivativeOfTheContourLogarithmAlongCurvesProof
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOfTheLinearMapsProof
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.TheMapsOfOneStepKeepRealFunctions
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RealityOfOneStep
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicLattice (compactGaugeGroup complexGaugeGroup)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
theorem compact_inv_mem {A : ComplexMatrix2} (h : A ∈ compactGaugeGroup) :
    A⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem compact_inv_inv {A : ComplexMatrix2} (h : A ∈ compactGaugeGroup) : A⁻¹⁻¹ = A := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem compact_mul_inv {A : ComplexMatrix2} (h : A ∈ compactGaugeGroup) : A * A⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p16098 <;> assumption
theorem compact_mem_complex {A : ComplexMatrix2} (h : A ∈ compactGaugeGroup) :
    A ∈ complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 h).2
theorem ofReal_smul_mem {r : ℝ} {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    (r : ℂ) • X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_smul_mem_hermitianTraceless <;> assumption
theorem matExp_I_smul_mem {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • Y) ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
theorem logSeries_eq_I_smul (hE : ComplexMatrix2.ExpLogEstimates) {A : ComplexMatrix2}
    (hA : A ∈ compactGaugeGroup) (h₁ : ComplexMatrix2.operatorNorm (A - 1) < 1) :
    ∃ Y ∈ ComplexMatrix2.hermitianTraceless, ComplexMatrix2.logSeries A = Complex.I • Y := by
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.1 hA
  obtain ⟨H, -, -, -, -, -, h⟩ := hE.2.2.2.2.2.2.2.1 A hu h₁
  exact (h hd).2.2.1
theorem I_inv_smul_logSeries_mem (hE : ComplexMatrix2.ExpLogEstimates) {A : ComplexMatrix2}
    (hA : A ∈ compactGaugeGroup) (h₁ : ComplexMatrix2.operatorNorm (A - 1) < 1) :
    Complex.I⁻¹ • ComplexMatrix2.logSeries A ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p12580 <;> assumption
theorem conjugateBy_mem {A X : ComplexMatrix2} (hA : A ∈ compactGaugeGroup)
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy A X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p2904 <;> assumption
theorem mul_inv_near_one {P Q : ComplexMatrix2} (hP : P ∈ compactGaugeGroup)
    (hQ : Q ∈ compactGaugeGroup)
    (h₁ : ComplexMatrix2.operatorNorm (P - 1) < 1 / 2)
    (h₂ : ComplexMatrix2.operatorNorm (Q - 1) < 1 / 2) :
    P * Q⁻¹ ∈ compactGaugeGroup ∧ ComplexMatrix2.operatorNorm (P * Q⁻¹ - 1) < 1 := by
  refine ⟨mul_mem hP (compact_inv_mem hQ), ?_⟩
  have e : P * Q⁻¹ - 1 = (P - Q) * Q⁻¹ := by
    rw [sub_mul, compact_mul_inv hQ]
  have hu : Q⁻¹ ∈ unitary ComplexMatrix2 :=
    (Matrix.mem_specialUnitaryGroup_iff.1 (compact_inv_mem hQ)).1
  rw [e]
  show ‖(P - Q) * Q⁻¹‖ < 1
  rw [CStarRing.norm_mul_mem_unitary _ hu]
  have : P - Q = (P - 1) - (Q - 1) := by abel
  rw [this]
  exact (norm_sub_le _ _).trans_lt (by
    linarith)
theorem operatorNorm_inv_sub_one {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    ComplexMatrix2.operatorNorm (A⁻¹ - 1) = ComplexMatrix2.operatorNorm (A - 1) := by apply _root_.YangMills.Construction.Tower.FullSpace.PolydiscSmoothing.operatorNorm_inv_sub_one <;> assumption
theorem isClosed_hermitianTraceless :
    IsClosed (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.LeftChartFields.isClosed_hermitianTraceless <;> assumption
theorem deriv_mem_of_real_values {φ : ℂ → ComplexMatrix2} {D : ComplexMatrix2}
    (h : HasDerivAt φ D 0)
    (hr : ∀ᶠ t : ℝ in 𝓝 0, φ (t : ℂ) ∈ ComplexMatrix2.hermitianTraceless) :
    D ∈ ComplexMatrix2.hermitianTraceless := by
  have hs := hasDerivAt_iff_tendsto_slope.1 h
  have hc : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 ((0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.tendsto 0
      rw [Complex.ofReal_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  refine isClosed_hermitianTraceless.mem_of_tendsto (hs.comp hc) ?_
  have h₀ : φ 0 ∈ ComplexMatrix2.hermitianTraceless := by
    have := hr.self_of_nhds
    simpa using this
  filter_upwards [hr.filter_mono nhdsWithin_le_nhds] with t ht
  have e : (slope φ 0 ∘ fun t : ℝ => (t : ℂ)) t = ((t⁻¹ : ℝ) : ℂ) • (φ (t : ℂ) - φ 0) := by
    simp [slope_def_module]
  rw [SetLike.mem_coe, e]
  exact ofReal_smul_mem (ComplexMatrix2.hermitianTraceless.sub_mem ht h₀)
theorem complexLogMean_mem_compact (hM : Averaging.ComplexLogMeanOfSmallFamilies) {ι : Type}
    [Fintype ι] [Nonempty ι] (V : ι → ComplexMatrix2) (hV : ∀ i, V i ∈ compactGaugeGroup)
    (hd : ComplexMatrix2.familyDiameter V < Averaging.centreOfMassDiameter) :
    PeriodicLattice.complexLogMean V ∈ compactGaugeGroup := by
  let e := Fintype.equivFin ι
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hF := hM.2.2.2.1 (Fintype.card ι) hn
  let V' : Fin (Fintype.card ι) → ComplexMatrix2 := fun i => V (e.symm i)
  have hdiam : ComplexMatrix2.familyDiameter V' = ComplexMatrix2.familyDiameter V :=
    (Equiv.prodCongr e.symm e.symm).iSup_comp
      (g := fun p : ι × ι => ComplexMatrix2.operatorNorm (V p.1 * (V p.2)⁻¹ - 1))
  have hmem := hF.memRealGroup V' (fun i => hV _) (by rw [hdiam]; exact hd)
  have key : (fun W => ComplexMatrix2.IsLogMean complexGaugeGroup V W ∧
      ∃ i, ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) ≤ PeriodicLattice.complexMeanTolerance) =
      fun W => ComplexMatrix2.IsLogMean complexGaugeGroup V' W ∧
      ∃ i, ComplexMatrix2.operatorNorm (V' i * W⁻¹ - 1) ≤
        PeriodicLattice.complexMeanTolerance := by
    funext W
    apply propext
    constructor
    · rintro ⟨⟨h₀, h₁, h₂⟩, i, hi⟩
      refine ⟨⟨h₀, fun i => h₁ _, ?_⟩, e i, by simpa [V'] using hi⟩
      rw [← h₂]
      exact Equiv.sum_comp e.symm fun i => ComplexMatrix2.logSeries (V i * W⁻¹)
    · rintro ⟨⟨h₀, h₁, h₂⟩, i, hi⟩
      refine ⟨⟨h₀, fun i => by simpa [V'] using h₁ (e i), ?_⟩, e.symm i, hi⟩
      rw [← h₂]
      exact (Equiv.sum_comp e.symm fun i => ComplexMatrix2.logSeries (V i * W⁻¹)).symm
  have e₂ : PeriodicLattice.complexLogMean V = PeriodicLattice.complexLogMean V' := by
    unfold PeriodicLattice.complexLogMean
    rw [key]
  rw [e₂]
  exact hmem
theorem matExp_finsum_mul_mem (hE : ComplexMatrix2.ExpLogEstimates) {X : Type} (s : Set X)
    (W : X → ComplexMatrix2) (T : ComplexMatrix2) (r : ℝ)
    (hW : ∀ x ∈ s, W x ∈ compactGaugeGroup)
    (hW₁ : ∀ x ∈ s, ComplexMatrix2.operatorNorm (W x - 1) < 1) (hTr : T ∈ compactGaugeGroup) :
    ComplexMatrix2.matExp ((r : ℂ) • ∑ᶠ x ∈ s, ComplexMatrix2.logSeries (W x)) * T ∈
      compactGaugeGroup := by
  obtain ⟨Y, hY, hS⟩ : ∃ Y ∈ ComplexMatrix2.hermitianTraceless,
      (∑ᶠ x ∈ s, ComplexMatrix2.logSeries (W x)) = Complex.I • Y := by
    refine finsum_mem_induction (fun Z => ∃ Y ∈ ComplexMatrix2.hermitianTraceless, Z = Complex.I • Y)
      ⟨0, ComplexMatrix2.hermitianTraceless.zero_mem, by simp⟩ ?_
      fun x hx => logSeries_eq_I_smul hE (hW x hx) (hW₁ x hx)
    rintro _ _ ⟨Y, hY, rfl⟩ ⟨Y', hY', rfl⟩
    exact ⟨Y + Y', ComplexMatrix2.hermitianTraceless.add_mem hY hY', (smul_add _ _ _).symm⟩
  rw [hS, smul_comm]
  exact mul_mem (matExp_I_smul_mem (ofReal_smul_mem hY)) hTr
theorem list_map_prod_mem {β : Type} (U : β → ComplexMatrix2) (Γ : List β)
    (h : ∀ b, U b ∈ compactGaugeGroup) : (Γ.map U).prod ∈ compactGaugeGroup := by
  induction Γ with
  | nil => exact one_mem _
  | cons b Γ ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (h b) ih
section NearOne
variable {L k j : ℕ}
private theorem nonempty_contourOrder {a a' : ℝ} (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') : Nonempty (ContourOrder L y x) :=
  ⟨(offsetSupport L y x).equivFin.symm⟩
private theorem coarse_vertex_mem (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hP : CubesOfOrderPartition L k j 1) (w : Vertex L k j) :
    (w : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (meshAt L k (j - 1)) := by apply _root_.YangMills.SharedProofs.p3071 <;> assumption
private theorem coe_toFiner {a a' : ℝ} {y : InfiniteLattice.LatticePoint a}
    (hy : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a') :
    (toFiner a' y : AmbientSpace) = y := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.coe_toFiner <;> assumption
theorem compact_on_domainNearOne (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hY : CubesCorridorsPivotEdgesAndPaths)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : 1 ≤ j) (hjk : j ≤ k)
    (c : Edge L k j) (V : Edge L k (j - 1) → ComplexMatrix2) (hc : c.IsPositivelyOriented)
    (hR : ∀ b, V b ∈ compactGaugeGroup) (hV : V ∈ complexDomainNearOne L c) :
    (∀ y : Vertex L k j, (y = c.initial ∨ y = c.terminal) →
      ∀ x ∈ cubeVertices L (meshAt L k (j - 1)) y,
        complexContourMean L V y x ∈ compactGaugeGroup) ∧
    complexSmoothing L V c ∈ compactGaugeGroup := by
  obtain ⟨hP, -, -, -⟩ := hY L hL k j 1 (hj.trans hjk) hj hjk le_rfl hj
  obtain ⟨⟨-, hdt, hdh⟩, hW₁⟩ := hV
  have hcontour : ∀ y : Vertex L k j, (y = c.initial ∨ y = c.terminal) →
      ∀ x ∈ cubeVertices L (meshAt L k (j - 1)) y,
        complexContourMean L V y x ∈ compactGaugeGroup := by
    intro y hy x hx
    have := nonempty_contourOrder (L := L) y x
    refine complexLogMean_mem_compact hM _ (fun σ => list_map_prod_mem V _ hR) ?_
    rcases hy with rfl | rfl
    · exact hdt x hx
    · exact hdh x hx
  have hdiff : (toFiner (meshAt L k (j - 1)) (c.terminal - c.initial) : AmbientSpace) =
      (c.terminal : AmbientSpace) - (c.initial : AmbientSpace) := by
    rw [coe_toFiner (coarse_vertex_mem hL hP (c.terminal - c.initial)), AddSubgroup.coe_sub]
  have hhead : ∀ x ∈ cubeVertices L (meshAt L k (j - 1)) c.initial,
      shifted c x ∈ cubeVertices L (meshAt L k (j - 1)) c.terminal := by
    intro x hx
    have ht := hP.cube_add c.initial (c.terminal - c.initial)
    rw [add_sub_cancel] at ht
    show ((shifted c x : Vertex L k (j - 1)) : AmbientSpace) ∈
      cubeOfOrder L (meshAt L k (j - 1)) 1 c.terminal
    rw [ht]
    refine ⟨(x : AmbientSpace), hx, ?_⟩
    unfold shifted
    rw [AddSubgroup.coe_add, hdiff, AddSubgroup.coe_sub]
  have htr : transportAlong V c ∈ compactGaugeGroup := list_map_prod_mem V _ hR
  refine ⟨hcontour, ?_⟩
  have hval : complexSmoothing L V c = complexSmoothingPositive L V c := if_pos hc
  rw [hval]
  refine matExp_finsum_mul_mem hE _ _ _ _ (fun x hx => ?_) hW₁ htr
  exact mul_mem (mul_mem (mul_mem (hcontour _ (Or.inl rfl) x hx) (list_map_prod_mem V _ hR))
    (compact_inv_mem (hcontour _ (Or.inr rfl) _ (hhead x hx)))) (compact_inv_mem htr)
theorem compact_on_polydisc (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hY : CubesCorridorsPivotEdgesAndPaths)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hjk : j < k) {ρ : ℝ}
    (c : Edge L k (j + 1)) (hc : c.IsPositivelyOriented) (hS : PolydiscIsAdmissible L k j ρ c)
    (W : Edge L k j → ComplexMatrix2) (hR : ∀ b, W b ∈ compactGaugeGroup)
    (hW : W ∈ nearIdentityPolydisc L k j ρ c) :
    (complexSmoothing L W c ∈ compactGaugeGroup ∧
      ComplexMatrix2.operatorNorm (complexSmoothing L W c - 1) < 1 / 2) ∧
    ∀ y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))),
      ∀ x ∈ cubeVertices L (meshAt L k j) y,
        complexContourMean L W y x ∈ compactGaugeGroup ∧
          ComplexMatrix2.operatorNorm (complexContourMean L W y x - 1) < 1 / 2 := by
  obtain ⟨h₁, h₂⟩ := compact_on_domainNearOne hM hY hE hL (j := j + 1) (by omega) (by omega)
    c W hc hR (hS.subset_complexDomain hW)
  exact ⟨⟨h₂, hS.smoothing_near_one W hW⟩, fun y hy x hx =>
    ⟨h₁ y hy x hx, hS.contourMean_near_one W hW y hy x hx⟩⟩
end NearOne
section Directions
variable {a : ℝ}
theorem opposite_isPositivelyOriented {b : InfiniteLattice.Link a}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem not_opposite_isPositivelyOriented (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem expTwist_isFieldIn (ha : 0 < a) {U B : InfiniteLattice.Link a → ComplexMatrix2}
    (hU : IsFieldIn compactGaugeGroup U) (hB : B ∈ edgeFormSpace a) (t : ℝ) :
    IsFieldIn compactGaugeGroup (expTwist ((t : ℂ) • B) U) := by
  classical
  have hval : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B) b) * U b ∈ compactGaugeGroup :=
    fun b hb => mul_mem (matExp_I_smul_mem (ofReal_smul_mem (hB.1 b hb))) (hU.1 b)
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [expTwist, if_pos hb]
      exact hval b hb
    · simp only [expTwist, if_neg hb]
      exact compact_inv_mem (hval _ (opposite_isPositivelyOriented hb))
  · by_cases hb : b.IsPositivelyOriented
    · simp only [expTwist, if_pos hb, if_neg (not_opposite_isPositivelyOriented ha hb),
        InfiniteLattice.Link.opposite_opposite]
    · have hr := opposite_isPositivelyOriented hb
      simp only [expTwist, if_neg hb, if_pos hr]
      exact (compact_inv_inv (hval _ hr)).symm
theorem eventually_expTwist_near (ha : 0 < a) {U B : InfiniteLattice.Link a → ComplexMatrix2}
    (hU : IsFieldIn compactGaugeGroup U) (hB : B ∈ edgeFormSpace a) {ρ : ℝ}
    (hρ : ∀ b, ComplexMatrix2.operatorNorm (U b - 1) < ρ) (b : InfiniteLattice.Link a) :
    ∀ᶠ t : ℝ in 𝓝 0, ComplexMatrix2.operatorNorm (expTwist ((t : ℂ) • B) U b - 1) < ρ := by
  classical
  have pos : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented →
      ∀ᶠ t : ℝ in 𝓝 0, ComplexMatrix2.operatorNorm (expTwist ((t : ℂ) • B) U b - 1) < ρ := by
    intro b hb
    have he : Continuous fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B b)) := by
      let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
      exact NormedSpace.exp_continuous.comp (by fun_prop)
    have hc : Continuous fun t : ℝ =>
        ComplexMatrix2.operatorNorm
          (ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B b)) * U b - 1) :=
      ((he.mul continuous_const).sub continuous_const).norm
    have ht := hc.tendsto 0
    have h0 : ComplexMatrix2.operatorNorm
        (ComplexMatrix2.matExp (Complex.I • (((0 : ℝ) : ℂ) • B b)) * U b - 1) =
        ComplexMatrix2.operatorNorm (U b - 1) := by
      simp
    rw [h0] at ht
    filter_upwards [ht.eventually_lt_const (hρ b)] with t ht'
    simpa only [expTwist, if_pos hb, Pi.smul_apply] using ht'
  by_cases hb : b.IsPositivelyOriented
  · exact pos b hb
  · filter_upwards [pos _ (opposite_isPositivelyOriented hb)] with t ht
    have hconf := expTwist_isFieldIn ha hU hB t
    have e : expTwist ((t : ℂ) • B) U b = (expTwist ((t : ℂ) • B) U b.opposite)⁻¹ :=
      hconf.2 b.opposite
    rw [e, operatorNorm_inv_sub_one (hconf.1 _)]
    exact ht
theorem deriv_logQuotient_mem (hE : ComplexMatrix2.ExpLogEstimates)
    {Φ : (InfiniteLattice.Link a → ComplexMatrix2) → ComplexMatrix2}
    {V B : InfiniteLattice.Link a → ComplexMatrix2} {D : ComplexMatrix2}
    (hd : HasDerivAt (fun t : ℂ =>
      Complex.I⁻¹ • ComplexMatrix2.logSeries (Φ (expTwist (t • B) V) * (Φ V)⁻¹)) D 0)
    (hev : ∀ᶠ t : ℝ in 𝓝 0, Φ (expTwist ((t : ℂ) • B) V) ∈ compactGaugeGroup ∧
      ComplexMatrix2.operatorNorm (Φ (expTwist ((t : ℂ) • B) V) - 1) < 1 / 2)
    (hV : Φ V ∈ compactGaugeGroup ∧ ComplexMatrix2.operatorNorm (Φ V - 1) < 1 / 2) :
    D ∈ ComplexMatrix2.hermitianTraceless := by
  refine deriv_mem_of_real_values hd ?_
  filter_upwards [hev] with t ht
  obtain ⟨h₁, h₂⟩ := mul_inv_near_one ht.1 hV.1 ht.2 hV.2
  exact I_inv_smul_logSeries_mem hE h₁ h₂
theorem mem_complexEdgeForms_of_mem {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace a) : B ∈ complexEdgeForms a :=
  ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
theorem extendOddly_opposite {f : InfiniteLattice.Link a → ComplexMatrix2} (ha : 0 < a)
    (b : InfiniteLattice.Link a) : extendOddly f b.opposite = -extendOddly f b := by
  classical
  by_cases hb : b.IsPositivelyOriented
  · simp [extendOddly, if_pos hb, if_neg (not_opposite_isPositivelyOriented ha hb),
      InfiniteLattice.Link.opposite_opposite]
  · simp [extendOddly, if_neg hb, if_pos (opposite_isPositivelyOriented hb)]
theorem weight_smul_finsum_mem {X : Type} (L : ℕ) (s : Set X) (f : X → ComplexMatrix2)
    (hf : ∀ x ∈ s, f x ∈ ComplexMatrix2.hermitianTraceless) :
    PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ s, f x ∈
      ComplexMatrix2.hermitianTraceless :=
  ofReal_smul_mem (finsum_mem_induction (· ∈ ComplexMatrix2.hermitianTraceless)
    ComplexMatrix2.hermitianTraceless.zero_mem
    (fun _ _ => ComplexMatrix2.hermitianTraceless.add_mem) hf)
end Directions
theorem holds (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hC : Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hT : RescaledTrivialSteps)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hY : CubesCorridorsPivotEdgesAndPaths)
    (hE : ComplexMatrix2.ExpLogEstimates) : Statement := by
  classical
  intro L hL k j hjk V hVs hVG
  have hk : 1 ≤ k := by omega
  have hL0 : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  have ha : ∀ i, 0 < meshAt L k i := fun i => zpow_pos hL0 _
  have hρ : IsAdmissiblePolydiscRadius L (polydiscRadius L) := (hA.1 L hL).2.2
  have hHold : AsDifferentials.StepConditions j V (fun _ => 1) :=
    (hC L hL k hk).2.1 j hjk V hVs _ (hT L hL k hk).1
  have hfin : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      (doubleCubeLinks L (meshAt L k j) c).Finite :=
    fun c hc => ((hP L hL k j hjk).2 c hc).finite_open.finite
  have hR := hVG.1
  have hdisc : ∀ c : Edge L k (j + 1), V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c :=
    fun c => ⟨⟨fun b _ => compact_mem_complex (hR b), fun b _ => hVG.2 b⟩, fun b _ => hVs.2 b⟩
  have onDisc := fun (c : Edge L k (j + 1)) (hc : c.IsPositivelyOriented) =>
    compact_on_polydisc hM hY hE hL hjk c hc (hρ.fullSpace k j hjk c hc)
  have moved : ∀ B ∈ edgeFormSpace (meshAt L k j), ∀ c : Edge L k (j + 1),
      c.IsPositivelyOriented →
      ∀ᶠ t : ℝ in 𝓝 0, (∀ b, expTwist ((t : ℂ) • B) V b ∈ compactGaugeGroup) ∧
        expTwist ((t : ℂ) • B) V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c := by
    intro B hB c hc
    have h := (eventually_all_finite (hfin c hc)).2 fun b _ =>
      eventually_expTwist_near (ha j) hVG hB hVs.2 b
    filter_upwards [h] with t ht
    have hconf := expTwist_isFieldIn (ha j) hVG hB t
    exact ⟨hconf.1, ⟨fun b _ => compact_mem_complex (hconf.1 b), fun b _ => hconf.2 b⟩, ht⟩
  have initialEdge : ∀ y : Vertex L k (j + 1), ∃ c : Edge L k (j + 1),
      c.IsPositivelyOriented ∧ c.initial = y :=
    fun y => ⟨InfiniteLattice.Link.forwardFrom y 0,
      InfiniteLattice.mem_positiveLinks_iff.1 ⟨y, 0, rfl⟩, rfl⟩
  have hcontour : ∀ (y : Vertex L k (j + 1)), ∀ x ∈ cubeVertices L (meshAt L k j) y,
      complexContourMean L V y x ∈ compactGaugeGroup := by
    intro y x hx
    obtain ⟨c, hc, rfl⟩ := initialEdge y
    exact ((onDisc c hc V hR (hdisc c)).2 _ (Or.inl rfl) x hx).1
  have hdrift : ∀ B ∈ edgeFormSpace (meshAt L k j), ∀ (y : Vertex L k (j + 1)),
      ∀ x ∈ cubeVertices L (meshAt L k j) y,
      logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
        (complexContourMean L V y x) B ∈ ComplexMatrix2.hermitianTraceless := by
    intro B hB y x hx
    obtain ⟨c, hc, rfl⟩ := initialEdge y
    refine deriv_logQuotient_mem hE (Φ := fun W => complexContourMean L W c.initial x) (V := V)
      (hHold.deriv_contour c.initial x hx B (mem_complexEdgeForms_of_mem hB)) ?_
      ((onDisc c hc V hR (hdisc c)).2 _ (Or.inl rfl) x hx)
    filter_upwards [moved B hB c hc] with t ht
    exact (onDisc c hc _ ht.1 ht.2).2 _ (Or.inl rfl) x hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hpos : ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
        complexSmoothing L V c ∈ compactGaugeGroup :=
      fun c hc => (onDisc c hc V hR (hdisc c)).1.1
    have hpos' : ∀ c : Edge L k (j + 1), ¬ c.IsPositivelyOriented →
        complexSmoothing L V c = (complexSmoothing L V c.opposite)⁻¹ := by
      intro c hc
      have e₁ : complexSmoothing L V c = (complexSmoothingPositive L V c.opposite)⁻¹ :=
        if_neg hc
      have e₂ : complexSmoothing L V c.opposite = complexSmoothingPositive L V c.opposite :=
        if_pos (opposite_isPositivelyOriented hc)
      rw [e₁, e₂]
    refine ⟨fun c => ?_, fun c => ?_⟩
    · show complexSmoothing L V c ∈ compactGaugeGroup
      by_cases hc : c.IsPositivelyOriented
      · exact hpos c hc
      · rw [hpos' c hc]
        exact compact_inv_mem (hpos _ (opposite_isPositivelyOriented hc))
    · show complexSmoothing L V c.opposite = (complexSmoothing L V c)⁻¹
      by_cases hc : c.IsPositivelyOriented
      · exact hpos' c.opposite (not_opposite_isPositivelyOriented (ha _) hc)
      · rw [hpos' c hc, compact_inv_inv (hpos _ (opposite_isPositivelyOriented hc))]
  · exact hcontour
  · intro B hB
    refine ⟨fun c hc => ?_, fun c => ?_⟩
    · refine deriv_logQuotient_mem hE (Φ := fun W => complexSmoothing L W c) (V := V)
        (hHold.deriv_mean c hc B (mem_complexEdgeForms_of_mem hB)) ?_
        (onDisc c hc V hR (hdisc c)).1
      filter_upwards [moved B hB c hc] with t ht
      exact (onDisc c hc _ ht.1 ht.2).1
    · unfold complexSmoothingDeriv holLeftDifferential
      exact extendOddly_opposite (ha _) c
  · intro B hB
    refine Submodule.mem_pi.2 fun y _ => ?_
    exact weight_smul_finsum_mem L _ _ (hdrift B hB y)
  · intro l hl
    refine Submodule.mem_pi.2 fun y _ => ?_
    refine weight_smul_finsum_mem L _ _ fun x hx => conjugateBy_mem (hcontour y x hx) ?_
    exact Submodule.mem_pi.1 hl x (Set.mem_univ x)
end YangMills.Construction.Tower.FullSpace.RealityOfOneStep
end
