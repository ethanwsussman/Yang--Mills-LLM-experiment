import YangMills.Construction.Towers.StepKernelsOfTheCovariantAveragesOnASideProof
import YangMills.Construction.Towers.StepKernelsOfTheIteratedAveragesAtTheSideInfinity
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import Mathlib
set_option autoImplicit false
open Set Filter Metric
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.StepKernels
open YangMills.Construction.Matrices (ComplexMatrix2)
open YangMills.Construction.Tower.LeftChartFields
open YangMills.Construction.Tower.AsDifferentials (IsLinearOn HasDerivAtZeroAlong)
open YangMills.Construction.Tower.FullSpace.AsDifferentials
section MatrixFacts
theorem norm_mul_sub_one_le_prod (X Y : ComplexMatrix2) :
    ‖X * Y - 1‖ ≤ (1 + ‖X - 1‖) * (1 + ‖Y - 1‖) - 1 := by apply _root_.YangMills.SharedProofs.p30838 <;> assumption
theorem expI_mul_mem_unitDeterminant (hEL : ComplexMatrix2.ExpLogEstimates)
    {X g : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    ComplexMatrix2.matExp (Complex.I • X) * g ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.Construction.Tower.AsDifferentials.expChart_mem_unitDeterminant <;> assumption
theorem inv_mem_unitDeterminant {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    g⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.unitDeterminant) : (g⁻¹)⁻¹ = g := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
theorem isUnit_and_bounds_of_near_one (hEL : ComplexMatrix2.ExpLogEstimates) {g : ComplexMatrix2}
    (hg : ‖g - 1‖ < 1 / 2) : IsUnit g ∧ ‖g‖ ≤ 3 / 2 ∧ ‖g⁻¹‖ ≤ 2 := by apply _root_.YangMills.Construction.Tower.StepKernels.bounds_of_near_one <;> assumption
theorem norm_conjugateBy_le {g : ComplexMatrix2} (h₁ : ‖g‖ ≤ 3 / 2) (h₂ : ‖g⁻¹‖ ≤ 2)
    (X : ComplexMatrix2) : ‖ComplexMatrix2.conjugateBy g X‖ ≤ 3 * ‖X‖ := by apply _root_.YangMills.SharedProofs.p70374 <;> assumption
theorem conjugateBy_add (g X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (X + Y) =
      ComplexMatrix2.conjugateBy g X + ComplexMatrix2.conjugateBy g Y := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (g : ComplexMatrix2) (z : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (z • X) = z • ComplexMatrix2.conjugateBy g X := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
theorem isBoundedTracelessEndo_of_linear {f : ComplexMatrix2 → ComplexMatrix2} {C : ℝ}
    (maps : ∀ X ∈ ComplexMatrix2.traceless, f X ∈ ComplexMatrix2.traceless)
    (add : ∀ X ∈ ComplexMatrix2.traceless, ∀ Y ∈ ComplexMatrix2.traceless, f (X + Y) = f X + f Y)
    (smul : ∀ z : ℂ, ∀ X ∈ ComplexMatrix2.traceless, f (z • X) = z • f X)
    (bound : ∀ X ∈ ComplexMatrix2.traceless,
      ComplexMatrix2.operatorNorm (f X) ≤ C * ComplexMatrix2.operatorNorm X) :
    IsBoundedTracelessEndo f C := by
  refine ⟨{ toFun := fun X => ⟨f X.1, maps X.1 X.2⟩
            map_add' := fun X Y => Subtype.ext (add X.1 X.2 Y.1 Y.2)
            map_smul' := fun z X => Subtype.ext (smul z X.1 X.2) }, fun X => rfl, fun X => ?_⟩
  exact bound X.1 X.2
theorem isBoundedTracelessEndo_conjugateBy (hEL : ComplexMatrix2.ExpLogEstimates)
    (hA : ComplexMatrix2.ConjugationPreservesTraceless) {g : ComplexMatrix2}
    (hg : ‖g - 1‖ < 1 / 2) :
    IsBoundedTracelessEndo (ComplexMatrix2.conjugateBy g) 3 := by
  obtain ⟨hu, h₁, h₂⟩ := isUnit_and_bounds_of_near_one hEL hg
  exact isBoundedTracelessEndo_of_linear (fun X hX => (hA.2.2 g hu).2.2.2.1 hX)
    (fun X _ Y _ => conjugateBy_add g X Y) (fun z X _ => conjugateBy_smul g z X)
    (fun X _ => norm_conjugateBy_le h₁ h₂ X)
theorem norm_matExp_sub_one_le (hEL : ComplexMatrix2.ExpLogEstimates) {Z : ComplexMatrix2}
    (hZ : ‖Z‖ ≤ 1) : ‖ComplexMatrix2.matExp Z - 1‖ ≤ 2 * ‖Z‖ := by apply _root_.YangMills.SharedProofs.p10567 <;> assumption
end MatrixFacts
section Orientation
variable {a : ℝ}
theorem opposite_positive (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpaceChainRule.opposite_isPositivelyOriented_of_not <;> assumption
theorem not_opposite_positive (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem opposite_opposite (b : InfiniteLattice.Link a) : b.opposite.opposite = b := rfl
theorem expTwist_of_positive {A U : InfiniteLattice.Link a → ComplexMatrix2}
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by
  simp [expTwist, if_pos hb]
theorem expTwist_of_not_positive {A U : InfiniteLattice.Link a → ComplexMatrix2}
    {b : InfiniteLattice.Link a} (hb : ¬ b.IsPositivelyOriented) :
    expTwist A U b = (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by
  simp [expTwist, if_neg hb]
end Orientation
variable {L k j : ℕ}
structure StepData (ρ : ℝ) (V : Edge L k j → ComplexMatrix2) (c : Edge L k (j + 1)) : Prop where
  expLog : ComplexMatrix2.ExpLogEstimates
  logCurves : ∀ r : ℝ, 0 < r →
    CurveLogDerivative ℂ (Metric.ball 0 r) PeriodicLattice.complexGaugeGroup
      PeriodicLattice.complexLieAlgebra
  radius_pos : 0 < ρ
  radius_le_one : ρ ≤ 1
  mesh_pos : 0 < meshAt L k j
  mem_fields : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup
  near_one : ∀ b, ‖V b - 1‖ < 3 / 4 * ρ
  links_finite : (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c).Finite
  opposite_mem : ∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c,
    b.opposite ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c
  admissible : PolydiscIsAdmissible L k j ρ c
  smoothing_local : ∀ W W' : Edge L k j → ComplexMatrix2,
    W ∈ nearIdentityPolydisc L k j ρ c → W' ∈ nearIdentityPolydisc L k j ρ c →
    (∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, W b = W' b) →
    complexSmoothing L W c = complexSmoothing L W' c
  contour_local : ∀ y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))),
    ∀ x ∈ cubeVertices L (meshAt L k j) y,
    ∀ W ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
    W ∈ nearIdentityPolydisc L k j ρ c →
    ∀ W' : Edge L k j → ComplexMatrix2,
      (∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, W' b = W b) →
      complexContourMean L W' y x = complexContourMean L W y x
  cube_finite : ∀ y : Vertex L k (j + 1), (cubeVertices L (meshAt L k j) y).Finite
  cube_ncard_le : ∀ y : Vertex L k (j + 1), (cubeVertices L (meshAt L k j) y).ncard ≤ L ^ 4
  factor_pos : 0 < L
section Twists
variable {ρ : ℝ} {V : Edge L k j → ComplexMatrix2} {c : Edge L k (j + 1)}
theorem StepData.expTwist_mem (S : StepData ρ V c) {C : Edge L k j → ComplexMatrix2}
    (hC : C ∈ complexEdgeForms (meshAt L k j)) :
    expTwist C V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := by
  have ha := S.mesh_pos
  have hval : ∀ b : Edge L k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • C b) * V b ∈ ComplexMatrix2.unitDeterminant :=
    fun b hb => expI_mul_mem_unitDeterminant S.expLog (hC.1 b hb) (S.mem_fields.1 b)
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_of_positive hb]
      exact hval b hb
    · rw [expTwist_of_not_positive hb]
      exact inv_mem_unitDeterminant (hval _ (opposite_positive ha hb))
  · by_cases hb : b.IsPositivelyOriented
    · have hr := not_opposite_positive ha hb
      rw [expTwist_of_not_positive hr, expTwist_of_positive hb, opposite_opposite]
    · have hr := opposite_positive ha hb
      rw [expTwist_of_positive hr, expTwist_of_not_positive hb]
      exact (inv_inv_of_mem_unitDeterminant (hval _ hr)).symm
theorem StepData.self_mem_polydisc (S : StepData ρ V c) : V ∈ nearIdentityPolydisc L k j ρ c :=
  ⟨⟨fun b _ => S.mem_fields.1 b, fun b _ => S.mem_fields.2 b⟩,
    fun b _ => (S.near_one b).trans (by have := S.radius_pos; linarith)⟩
theorem StepData.mem_polydisc_of_eqOn (S : StepData ρ V c) {W W' : Edge L k j → ComplexMatrix2}
    (hW : W ∈ nearIdentityPolydisc L k j ρ c)
    (hag : ∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, W' b = W b) :
    W' ∈ nearIdentityPolydisc L k j ρ c := by
  refine ⟨⟨fun b hb => ?_, fun b hb => ?_⟩, fun b hb => ?_⟩
  · rw [hag b hb]
    exact hW.1.1 b hb
  · rw [hag b hb, hag _ (S.opposite_mem b hb)]
    exact hW.1.2 b hb
  · rw [hag b hb]
    exact hW.2 b hb
theorem StepData.expTwist_zero_smul (S : StepData ρ V c) {B : Edge L k j → ComplexMatrix2} :
    expTwist ((0 : ℂ) • B) V = V := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [expTwist_of_positive hb]
    simp [ComplexMatrix2.matExp]
  · rw [expTwist_of_not_positive hb]
    have h₁ := S.mem_fields.2 b.opposite
    rw [opposite_opposite] at h₁
    simp only [Pi.smul_apply, zero_smul, smul_zero, ComplexMatrix2.matExp, NormedSpace.exp_zero,
      one_mul]
    exact h₁.symm
theorem StepData.expTwist_mem_polydisc (S : StepData ρ V c) {t : ℂ}
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j))
    (hsm : ∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, ‖t‖ * ‖B b‖ ≤ ρ / 16) :
    expTwist (t • B) V ∈ nearIdentityPolydisc L k j ρ c := by
  have hρ := S.radius_pos
  have hρ1 := S.radius_le_one
  have hW := S.expTwist_mem ((complexEdgeForms (meshAt L k j)).smul_mem t hB)
  refine ⟨⟨fun b _ => hW.1 b, fun b _ => hW.2 b⟩, fun b hb => ?_⟩
  have hnZ : ∀ b' ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c,
      ‖Complex.I • (t • B) b'‖ ≤ ρ / 16 := fun b' hb' => by
    have : ‖Complex.I • (t • B) b'‖ = ‖t‖ * ‖B b'‖ := by
      simp [norm_smul]
    rw [this]
    exact hsm b' hb'
  have hexp : ∀ Z : ComplexMatrix2, ‖Z‖ ≤ ρ / 16 → ‖ComplexMatrix2.matExp Z - 1‖ ≤ ρ / 8 :=
    fun Z hZ => by
      have := norm_matExp_sub_one_le S.expLog (Z := Z) (by linarith)
      linarith
  have hfin : ∀ X Y : ComplexMatrix2, ‖X - 1‖ ≤ ρ / 8 → ‖Y - 1‖ ≤ 3 / 4 * ρ →
      ‖X * Y - 1‖ < ρ := by
    intro X Y hX hY
    have h := norm_mul_sub_one_le_prod X Y
    have hx := norm_nonneg (X - 1)
    have hy := norm_nonneg (Y - 1)
    have : (1 + ‖X - 1‖) * (1 + ‖Y - 1‖) ≤ (1 + ρ / 8) * (1 + 3 / 4 * ρ) := by gcongr
    nlinarith
  have hfin' : ∀ X Y : ComplexMatrix2, ‖X - 1‖ ≤ 3 / 4 * ρ → ‖Y - 1‖ ≤ ρ / 8 →
      ‖X * Y - 1‖ < ρ := by
    intro X Y hX hY
    have h := norm_mul_sub_one_le_prod X Y
    have hx := norm_nonneg (X - 1)
    have hy := norm_nonneg (Y - 1)
    have : (1 + ‖X - 1‖) * (1 + ‖Y - 1‖) ≤ (1 + 3 / 4 * ρ) * (1 + ρ / 8) := by gcongr
    nlinarith
  by_cases hp : b.IsPositivelyOriented
  · rw [expTwist_of_positive hp]
    exact hfin _ _ (hexp _ (hnZ b hb)) (S.near_one b).le
  · rw [expTwist_of_not_positive hp, Matrix.mul_inv_rev]
    have h₁ := S.mem_fields.2 b.opposite
    rw [opposite_opposite] at h₁
    rw [← h₁, ← Matrix.exp_neg]
    refine hfin' _ _ (S.near_one b).le (hexp _ ?_)
    rw [norm_neg]
    exact hnZ _ (S.opposite_mem b hb)
def twistedValues (c : Edge L k (j + 1)) (V B : Edge L k j → ComplexMatrix2) (t : ℂ) :
    PositiveEdgeOf (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) → ComplexMatrix2 :=
  restrictPositive _ (expTwist (t • B) V)
theorem twistedValues_apply (B : Edge L k j → ComplexMatrix2) (t : ℂ)
    (b : PositiveEdgeOf (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c)) :
    twistedValues c V B t b = ComplexMatrix2.matExp (t • (Complex.I • B b.1)) * V b.1 := by
  have : Complex.I • (t • B) b.1 = t • (Complex.I • B b.1) := by
    simp only [Pi.smul_apply]
    exact smul_comm _ _ _
  simp only [twistedValues, restrictPositive]
  rw [expTwist_of_positive b.2.2, this]
theorem StepData.extend_restrict_eq (S : StepData ρ V c) {W : Edge L k j → ComplexMatrix2}
    (hW : W ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) :
    ∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c,
      extendFromPositive (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c)
        (restrictPositive _ W) b = W b := by
  classical
  intro b hb
  have ha := S.mesh_pos
  by_cases hp : b.IsPositivelyOriented
  · simp [extendFromPositive, restrictPositive, hb, hp]
  · have hr := opposite_positive ha hp
    have h₁ := hW.2 b.opposite
    rw [opposite_opposite] at h₁
    have hrb := S.opposite_mem b hb
    simp [extendFromPositive, restrictPositive, hb, hp, hr, hrb, h₁]
theorem twistedValues_differentiableAt
    [Fintype (PositiveEdgeOf (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c))]
    (B : Edge L k j → ComplexMatrix2) (t : ℂ) :
    DifferentiableAt ℂ (twistedValues c V B) t := by
  refine differentiableAt_pi.2 fun b => ?_
  have e : (fun s => twistedValues c V B s b) =
      fun s : ℂ => ComplexMatrix2.matExp (s • (Complex.I • B b.1)) * V b.1 := by
    funext s
    exact twistedValues_apply B s b
  rw [e]
  exact ((hasDerivAt_exp_smul_const (𝕂 := ℂ) (Complex.I • B b.1) t).mul_const
    (V b.1)).differentiableAt
theorem StepData.differentiableAt_along_twist (S : StepData ρ V c)
    {Φ : (Edge L k j → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicOnFields
      (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) (nearIdentityPolydisc L k j ρ c) Φ)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) {t₀ : ℂ}
    (ht₀ : expTwist (t₀ • B) V ∈ nearIdentityPolydisc L k j ρ c) :
    DifferentiableAt ℂ (fun t => Φ (extendFromPositive
        (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) (twistedValues c V B t))) t₀ ∧
      Φ (extendFromPositive
        (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) (twistedValues c V B t₀)) ∈
        PeriodicLattice.complexGaugeGroup := by
  obtain ⟨⟨inst, ⟨O', hO', hD⟩, hmaps, hloc⟩, -⟩ := hΦ
  have hx : twistedValues c V B t₀ ∈
      restrictPositive (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) ''
        nearIdentityPolydisc L k j ρ c := ⟨_, ht₀, rfl⟩
  have hxO : twistedValues c V B t₀ ∈ O' := by
    have h := hx
    rw [hD] at h
    exact h.1
  have hprod : ∀ t, twistedValues c V B t ∈
      ComplexMatrix2.complexifiedProduct fun _ : PositiveEdgeOf
        (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) =>
          ComplexMatrix2.FactorKind.group := fun t b =>
    (S.expTwist_mem ((complexEdgeForms (meshAt L k j)).smul_mem t hB)).1 b.1
  have hv := twistedValues_differentiableAt (c := c) (V := V) B t₀
  have hmem : ∀ᶠ t in 𝓝 t₀, twistedValues c V B t ∈
      restrictPositive (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) ''
        nearIdentityPolydisc L k j ρ c := by
    filter_upwards [hv.continuousAt.eventually (hO'.mem_nhds hxO)] with t ht
    rw [hD]
    exact ⟨ht, hprod t⟩
  obtain ⟨F, hF, hev⟩ := hloc _ hx
  have h2 := (tendsto_nhdsWithin_iff.2 ⟨hv.continuousAt, hmem⟩).eventually hev
  have h3 : DifferentiableAt ℂ (fun t => F (twistedValues c V B t)) t₀ :=
    hF.differentiableAt.comp t₀ hv
  have h4 : DifferentiableAt ℂ (fun t => F (twistedValues c V B t) ()) t₀ :=
    differentiableAt_pi.1 h3 ()
  refine ⟨h4.congr_of_eventuallyEq ?_, hmaps hx ()⟩
  filter_upwards [h2] with t ht
  exact congrFun ht ()
theorem StepData.norm_logDirectionalDeriv_le (S : StepData ρ V c)
    {Φ : (Edge L k j → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicOnFields
      (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) (nearIdentityPolydisc L k j ρ c) Φ)
    (hsmall : ∀ W ∈ nearIdentityPolydisc L k j ρ c, ‖Φ W - 1‖ < 1 / 2)
    (hread : ∀ W ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
      W ∈ nearIdentityPolydisc L k j ρ c → ∀ W' : Edge L k j → ComplexMatrix2,
        (∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, W' b = W b) →
        Φ W' = Φ W)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j))
    (hB1 : ∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, ‖B b‖ ≤ 1) :
    ‖logDirectionalDeriv ℂ (fun X => Φ (expTwist X V)) (Φ V) B‖ ≤ 16 * ρ⁻¹ := by
  have hρ := S.radius_pos
  have hr0 : 0 < ρ / 16 := by positivity
  have hin : ∀ t ∈ closedBall (0 : ℂ) (ρ / 16),
      expTwist (t • B) V ∈ nearIdentityPolydisc L k j ρ c := fun t ht =>
    S.expTwist_mem_polydisc hB fun b hb => by
      have h1 : ‖t‖ ≤ ρ / 16 := by simpa using ht
      calc ‖t‖ * ‖B b‖ ≤ ρ / 16 * 1 :=
            mul_le_mul h1 (hB1 b hb) (norm_nonneg _) hr0.le
        _ = ρ / 16 := mul_one _
  have hconf : ∀ t : ℂ, expTwist (t • B) V ∈
      fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := fun t =>
    S.expTwist_mem ((complexEdgeForms (meshAt L k j)).smul_mem t hB)
  let w : ℂ → ComplexMatrix2 := fun t => Φ (expTwist (t • B) V)
  have hagree : ∀ t ∈ closedBall (0 : ℂ) (ρ / 16),
      Φ (extendFromPositive
        (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) (twistedValues c V B t)) = w t :=
    fun t ht => hread _ (hconf t) (hin t ht) _ (S.extend_restrict_eq (hconf t))
  have hdiff : DifferentiableOn ℂ w (closedBall 0 (ρ / 16)) := fun t ht =>
    ((S.differentiableAt_along_twist hΦ hB (hin t ht)).1.differentiableWithinAt).congr
      (fun s hs => (hagree s hs).symm) (hagree t ht).symm
  have hgroup : MapsTo w (ball 0 (ρ / 16)) PeriodicLattice.complexGaugeGroup := fun t ht => by
    have htc := ball_subset_closedBall ht
    have h := (S.differentiableAt_along_twist hΦ hB (hin t htc)).2
    rwa [hagree t htc] at h
  have hw0 : DifferentiableAt ℂ w 0 :=
    (hdiff 0 (mem_closedBall_self hr0.le)).differentiableAt (closedBall_mem_nhds _ hr0)
  obtain ⟨-, -, heq, -⟩ := S.logCurves _ hr0 w hgroup hw0
  have hwV : w 0 = Φ V := by
    simp only [w]
    rw [S.expTwist_zero_smul]
  obtain ⟨-, -, hinv⟩ := isUnit_and_bounds_of_near_one S.expLog (hsmall V S.self_mem_polydisc)
  have hcauchy : ‖deriv w 0‖ ≤ 1 / 2 / (ρ / 16) := by
    have hf : DifferentiableOn ℂ (fun t => w t - 1) (closedBall 0 (ρ / 16)) := hdiff.sub_const 1
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0
      (hf.diffContOnCl_ball subset_rfl) (C := 1 / 2)
      fun z hz => (hsmall _ (hin z (sphere_subset_closedBall hz))).le
    rwa [deriv_sub_const] at h
  simp only [logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
  have e : Complex.I⁻¹ • deriv (fun t : ℂ =>
      ComplexMatrix2.logSeries (Φ (expTwist (t • B) V) * (Φ V)⁻¹)) 0 =
      Complex.I⁻¹ • (deriv w 0 * (w 0)⁻¹) := by
    rw [← hwV]
    exact heq
  rw [e, norm_smul, hwV]
  have hI : ‖(Complex.I⁻¹ : ℂ)‖ = 1 := by simp
  rw [hI, one_mul]
  calc ‖deriv w 0 * (Φ V)⁻¹‖ ≤ ‖deriv w 0‖ * ‖(Φ V)⁻¹‖ := norm_mul_le _ _
    _ ≤ (1 / 2 / (ρ / 16)) * 2 := by gcongr
    _ = 16 * ρ⁻¹ := by field_simp
theorem StepData.norm_contourLogDrift_le (S : StepData ρ V c) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k j))
    (hB1 : ∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, ‖B b‖ ≤ 1)
    {y : Vertex L k (j + 1)} (hy : y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1)))) :
    ‖contourLogDrift V B y‖ ≤ 16 * ρ⁻¹ := by
  have hρ := S.radius_pos
  have hfin := S.cube_finite y
  have hterm : ∀ x ∈ cubeVertices L (meshAt L k j) y,
      ‖logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
        (complexContourMean L V y x) B‖ ≤ 16 * ρ⁻¹ := fun x hx =>
    S.norm_logDirectionalDeriv_le (Φ := fun W => complexContourMean L W y x)
      (S.admissible.holomorphic_contourMean y hy x hx)
      (fun W hW => S.admissible.contourMean_near_one W hW y hy x hx)
      (fun W hW hWp W' h => S.contour_local y hy x hx W hW hWp W' h) hB hB1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast S.factor_pos
  have hw : ‖PeriodicLattice.inverseFourthPowerWeight L‖ = ((L : ℝ) ^ 4)⁻¹ := by
    have e : (L : ℝ) ^ (-4 : ℤ) = ((L : ℝ) ^ 4)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    simp only [PeriodicLattice.inverseFourthPowerWeight, e, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hcard : (hfin.toFinset.card : ℝ) ≤ (L : ℝ) ^ 4 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast S.cube_ncard_le y
  simp only [contourLogDrift]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, norm_smul, hw]
  have hsum := norm_sum_le hfin.toFinset (fun x => logDirectionalDeriv ℂ
    (fun X => complexContourMean L (expTwist X V) y x)
    (complexContourMean L V y x) B)
  have hle : ∑ x ∈ hfin.toFinset, ‖logDirectionalDeriv ℂ
      (fun X => complexContourMean L (expTwist X V) y x)
      (complexContourMean L V y x) B‖ ≤
      (hfin.toFinset.card : ℝ) * (16 * ρ⁻¹) := by
    have := Finset.sum_le_card_nsmul hfin.toFinset _ (16 * ρ⁻¹)
      fun x hx => hterm x (hfin.mem_toFinset.1 hx)
    simpa [nsmul_eq_mul] using this
  have hb : (0 : ℝ) ≤ 16 * ρ⁻¹ := by positivity
  calc ((L : ℝ) ^ 4)⁻¹ * _ ≤ ((L : ℝ) ^ 4)⁻¹ * ((L : ℝ) ^ 4 * (16 * ρ⁻¹)) := by
        refine mul_le_mul_of_nonneg_left (hsum.trans (hle.trans ?_)) (by positivity)
        exact mul_le_mul_of_nonneg_right hcard hb
    _ = 16 * ρ⁻¹ := by field_simp
theorem complexSmoothingDeriv_eq {U : Edge L k 0 → ComplexMatrix2} (step : StepConditions j V U)
    (hc : c.IsPositivelyOriented)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    complexSmoothingDeriv V B c = logDirectionalDeriv ℂ
      (fun X => complexSmoothing L (expTwist X V) c) (complexSmoothing L V c) B := by
  have h : HasDerivAt (fun t : ℂ => meanLogRatio V c (t • B))
      (complexSmoothingDeriv V B c) 0 := step.deriv_mean c hc B hB
  have h₂ : HasDerivAt (fun t : ℂ => Complex.I • meanLogRatio V c (t • B))
      (Complex.I • complexSmoothingDeriv V B c) 0 := h.const_smul Complex.I
  have e : (fun t : ℂ => Complex.I • meanLogRatio V c (t • B)) =
      fun t : ℂ => ComplexMatrix2.logSeries (complexSmoothing L (expTwist (t • B) V) c *
        (complexSmoothing L V c)⁻¹) := by
    funext t
    simp only [meanLogRatio, meanRatio, smul_smul,
      mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
  rw [e] at h₂
  simp only [logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h₂.deriv, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
theorem covariantSmoothingDeriv_eq (hc : c.IsPositivelyOriented) (B : Edge L k j → ComplexMatrix2) :
    covariantSmoothingDeriv V B c = complexSmoothingDeriv V B c +
      (ComplexMatrix2.conjugateBy (complexSmoothing L V c) (contourLogDrift V B c.terminal) -
        contourLogDrift V B c.initial) := by
  simp only [covariantSmoothingDeriv, Pi.add_apply, covDiff, extendOddly, if_pos hc]
  rfl
theorem StepData.norm_covariantSmoothingDeriv_le (S : StepData ρ V c)
    {U : Edge L k 0 → ComplexMatrix2} (step : StepConditions j V U) (hc : c.IsPositivelyOriented)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j))
    (hB1 : ∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, ‖B b‖ ≤ 1) :
    ‖covariantSmoothingDeriv V B c‖ ≤ 80 * ρ⁻¹ := by
  have h₁ : ‖complexSmoothingDeriv V B c‖ ≤ 16 * ρ⁻¹ := by
    rw [complexSmoothingDeriv_eq step hc hB]
    exact S.norm_logDirectionalDeriv_le (Φ := fun W => complexSmoothing L W c)
      S.admissible.holomorphic_smoothing S.admissible.smoothing_near_one
      (fun W _ hWp W' h => S.smoothing_local W' W (S.mem_polydisc_of_eqOn hWp h) hWp h) hB hB1
  have h₂ := S.norm_contourLogDrift_le hB hB1 (y := c.terminal) (Or.inr rfl)
  have h₃ := S.norm_contourLogDrift_le hB hB1 (y := c.initial) (Or.inl rfl)
  obtain ⟨-, hg₁, hg₂⟩ :=
    isUnit_and_bounds_of_near_one S.expLog (S.admissible.smoothing_near_one V S.self_mem_polydisc)
  have h₄ := norm_conjugateBy_le hg₁ hg₂ (contourLogDrift V B c.terminal)
  rw [covariantSmoothingDeriv_eq hc]
  have h₅ := norm_add_le (complexSmoothingDeriv V B c)
    (ComplexMatrix2.conjugateBy (complexSmoothing L V c) (contourLogDrift V B c.terminal) -
      contourLogDrift V B c.initial)
  have h₆ := norm_sub_le (ComplexMatrix2.conjugateBy (complexSmoothing L V c)
    (contourLogDrift V B c.terminal)) (contourLogDrift V B c.initial)
  linarith
theorem StepData.expTwist_eqOn (S : StepData ρ V c) {B B' : Edge L k j → ComplexMatrix2}
    (hag : ∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, B b = B' b) (t : ℂ) :
    ∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c,
      expTwist (t • B) V b = expTwist (t • B') V b := by
  intro b hb
  by_cases hp : b.IsPositivelyOriented
  · rw [expTwist_of_positive hp, expTwist_of_positive hp]
    simp only [Pi.smul_apply, hag b hb]
  · rw [expTwist_of_not_positive hp, expTwist_of_not_positive hp]
    simp only [Pi.smul_apply, hag _ (S.opposite_mem b hb)]
theorem StepData.eventually_expTwist_mem_polydisc (S : StepData ρ V c)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    ∀ᶠ t : ℂ in 𝓝 0, expTwist (t • B) V ∈ nearIdentityPolydisc L k j ρ c := by
  have hρ := S.radius_pos
  obtain ⟨R, hR⟩ := (S.links_finite.image fun b => ‖B b‖).bddAbove
  filter_upwards [ball_mem_nhds (0 : ℂ) (show 0 < ρ / 16 / max R 1 by positivity)] with t ht
  refine S.expTwist_mem_polydisc hB fun b hb => ?_
  have ht' : ‖t‖ ≤ ρ / 16 / max R 1 := by
    have : ‖t‖ < ρ / 16 / max R 1 := by simpa using ht
    exact this.le
  have hb' : ‖B b‖ ≤ max R 1 := (hR ⟨b, hb, rfl⟩).trans (le_max_left _ _)
  calc ‖t‖ * ‖B b‖ ≤ ρ / 16 / max R 1 * max R 1 :=
        mul_le_mul ht' hb' (norm_nonneg _) (by positivity)
    _ = ρ / 16 := by field_simp
theorem StepData.covariantSmoothingDeriv_congr (S : StepData ρ V c)
    {U : Edge L k 0 → ComplexMatrix2} (step : StepConditions j V U) (hc : c.IsPositivelyOriented)
    {B B' : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j))
    (hB' : B' ∈ complexEdgeForms (meshAt L k j))
    (hag : ∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c, B b = B' b) :
    covariantSmoothingDeriv V B c = covariantSmoothingDeriv V B' c := by
  have h₁ : complexSmoothingDeriv V B c = complexSmoothingDeriv V B' c := by
    rw [complexSmoothingDeriv_eq step hc hB, complexSmoothingDeriv_eq step hc hB']
    have e : (fun t : ℂ => ComplexMatrix2.logSeries
          (complexSmoothing L (expTwist (t • B) V) c * (complexSmoothing L V c)⁻¹)) =ᶠ[𝓝 0]
        fun t : ℂ => ComplexMatrix2.logSeries
          (complexSmoothing L (expTwist (t • B') V) c * (complexSmoothing L V c)⁻¹) := by
      filter_upwards [S.eventually_expTwist_mem_polydisc hB,
        S.eventually_expTwist_mem_polydisc hB'] with t ht ht'
      rw [S.smoothing_local _ _ ht ht' (S.expTwist_eqOn hag t)]
    simp only [logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
    rw [e.deriv_eq]
  have h₂ : ∀ y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))),
      contourLogDrift V B y = contourLogDrift V B' y := by
    intro y hy
    have hterm : ∀ x ∈ cubeVertices L (meshAt L k j) y,
        logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
          (complexContourMean L V y x) B =
        logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
          (complexContourMean L V y x) B' := by
      intro x hx
      have e : (fun t : ℂ => ComplexMatrix2.logSeries
            (complexContourMean L (expTwist (t • B) V) y x *
              (complexContourMean L V y x)⁻¹)) =ᶠ[𝓝 0]
          fun t : ℂ => ComplexMatrix2.logSeries
            (complexContourMean L (expTwist (t • B') V) y x *
              (complexContourMean L V y x)⁻¹) := by
        filter_upwards [S.eventually_expTwist_mem_polydisc hB'] with t ht
        rw [S.contour_local y hy x hx _
          (S.expTwist_mem ((complexEdgeForms (meshAt L k j)).smul_mem t hB'))
          ht _ (S.expTwist_eqOn hag t)]
      simp only [logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
      rw [e.deriv_eq]
    exact congrArg (PeriodicLattice.inverseFourthPowerWeight L • ·) (finsum_mem_congr rfl hterm)
  have ht : contourLogDrift V B c.initial = contourLogDrift V B' c.initial := h₂ c.initial (Or.inl rfl)
  have hh : contourLogDrift V B c.terminal = contourLogDrift V B' c.terminal :=
    h₂ c.terminal (Or.inr rfl)
  rw [covariantSmoothingDeriv_eq hc, covariantSmoothingDeriv_eq hc, h₁, ht, hh]
end Twists
section SingleLinks
variable {ρ : ℝ} {V : Edge L k j → ComplexMatrix2} {c : Edge L k (j + 1)}
theorem StepData.extendOddly_opposite (S : StepData ρ V c) (f : Edge L k j → ComplexMatrix2)
    (b : Edge L k j) : extendOddly f b.opposite = -extendOddly f b := by
  have ha := S.mesh_pos
  by_cases hb : b.IsPositivelyOriented
  · have hr := not_opposite_positive ha hb
    simp [extendOddly, hb, hr, opposite_opposite]
  · have hr := opposite_positive ha hb
    simp [extendOddly, hb, hr]
theorem singleLinkForm_same {b : Edge L k j} (hb : b.IsPositivelyOriented) (X : ComplexMatrix2) :
    singleLinkForm b X b = X := by
  simp [singleLinkForm, extendOddly, hb]
theorem singleLinkForm_of_ne {b b' : Edge L k j} (hb' : b'.IsPositivelyOriented) (h : b' ≠ b)
    (X : ComplexMatrix2) : singleLinkForm b X b' = 0 := by
  simp [singleLinkForm, extendOddly, hb', h]
theorem StepData.singleLinkForm_mem (S : StepData ρ V c) {b : Edge L k j} {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) : singleLinkForm b X ∈ complexEdgeForms (meshAt L k j) := by
  refine (⟨fun b' hb' => ?_, fun b' => S.extendOddly_opposite _ b'⟩ :
    IsEdgeFormIn PeriodicLattice.complexLieAlgebra _)
  show singleLinkForm b X b' ∈ ComplexMatrix2.traceless
  by_cases h : b' = b
  · subst h
    rw [singleLinkForm_same hb']
    exact hX
  · rw [singleLinkForm_of_ne hb' h]
    exact ComplexMatrix2.traceless.zero_mem
theorem singleLinkForm_add (b : Edge L k j) (X Y : ComplexMatrix2) :
    singleLinkForm b (X + Y) = singleLinkForm b X + singleLinkForm b Y := by
  funext b'
  simp only [singleLinkForm, extendOddly, Pi.add_apply]
  split_ifs <;> simp [add_comm]
theorem singleLinkForm_smul (b : Edge L k j) (z : ℂ) (X : ComplexMatrix2) :
    singleLinkForm b (z • X) = z • singleLinkForm b X := by
  funext b'
  simp only [singleLinkForm, extendOddly, Pi.smul_apply]
  split_ifs <;> simp
theorem norm_singleLinkForm_le (b b' : Edge L k j) (X : ComplexMatrix2) :
    ‖singleLinkForm b X b'‖ ≤ ‖X‖ := by
  simp only [singleLinkForm, extendOddly]
  split_ifs <;> simp
theorem covariantSmoothingDeriv_add {U : Edge L k 0 → ComplexMatrix2} (step : StepConditions j V U)
    (hc : c.IsPositivelyOriented)
    {B B' : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j))
    (hB' : B' ∈ complexEdgeForms (meshAt L k j)) :
    covariantSmoothingDeriv V (B + B') c =
      covariantSmoothingDeriv V B c + covariantSmoothingDeriv V B' c := by
  rw [covariantSmoothingDeriv_eq hc, covariantSmoothingDeriv_eq hc, covariantSmoothingDeriv_eq hc,
    (step.linear_mean B hB B' hB' 0).1, (step.linear_contour B hB B' hB' 0).1]
  simp only [Pi.add_apply, conjugateBy_add]
  abel
theorem covariantSmoothingDeriv_smul {U : Edge L k 0 → ComplexMatrix2} (step : StepConditions j V U)
    (hc : c.IsPositivelyOriented)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) (z : ℂ) :
    covariantSmoothingDeriv V (z • B) c = z • covariantSmoothingDeriv V B c := by
  rw [covariantSmoothingDeriv_eq hc, covariantSmoothingDeriv_eq hc,
    (step.linear_mean B hB B hB z).2, (step.linear_contour B hB B hB z).2]
  simp only [Pi.smul_apply, conjugateBy_smul, smul_add, smul_sub]
theorem StepData.covariantSmoothingDeriv_mem (S : StepData ρ V c)
    (hA : ComplexMatrix2.ConjugationPreservesTraceless) {U : Edge L k 0 → ComplexMatrix2}
    (step : StepConditions j V U) (hc : c.IsPositivelyOriented) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    covariantSmoothingDeriv V B c ∈ ComplexMatrix2.traceless := by
  obtain ⟨hu, -, -⟩ :=
    isUnit_and_bounds_of_near_one S.expLog (S.admissible.smoothing_near_one V S.self_mem_polydisc)
  rw [covariantSmoothingDeriv_eq hc]
  exact ComplexMatrix2.traceless.add_mem (step.mem_mean c hc B hB)
    (ComplexMatrix2.traceless.sub_mem ((hA.2.2 _ hu).2.2.2.1 (step.mem_contour _ B hB))
      (step.mem_contour _ B hB))
theorem StepData.isBoundedTracelessEndo_stepKernel (S : StepData ρ V c)
    (hA : ComplexMatrix2.ConjugationPreservesTraceless) {U : Edge L k 0 → ComplexMatrix2}
    (step : StepConditions j V U) (hc : c.IsPositivelyOriented) {b : Edge L k j} :
    IsBoundedTracelessEndo (fun X => covariantSmoothingDeriv V (singleLinkForm b X) c)
      (80 * ρ⁻¹) := by
  have hadd : ∀ X ∈ ComplexMatrix2.traceless, ∀ Y ∈ ComplexMatrix2.traceless,
      covariantSmoothingDeriv V (singleLinkForm b (X + Y)) c =
        covariantSmoothingDeriv V (singleLinkForm b X) c +
          covariantSmoothingDeriv V (singleLinkForm b Y) c := fun X hX Y hY => by
    rw [singleLinkForm_add]
    exact covariantSmoothingDeriv_add step hc (S.singleLinkForm_mem hX) (S.singleLinkForm_mem hY)
  have hsmul : ∀ z : ℂ, ∀ X ∈ ComplexMatrix2.traceless,
      covariantSmoothingDeriv V (singleLinkForm b (z • X)) c =
        z • covariantSmoothingDeriv V (singleLinkForm b X) c := fun z X hX => by
    rw [singleLinkForm_smul]
    exact covariantSmoothingDeriv_smul step hc (S.singleLinkForm_mem hX) z
  refine isBoundedTracelessEndo_of_linear
    (fun X hX => S.covariantSmoothingDeriv_mem hA step hc (S.singleLinkForm_mem hX)) hadd
    hsmul fun X hX => ?_
  by_cases h0 : X = 0
  · subst h0
    have h := hsmul 0 0 ComplexMatrix2.traceless.zero_mem
    simp only [zero_smul] at h
    simp [h, ComplexMatrix2.operatorNorm]
  · have hs : 0 < ‖X‖ := norm_pos_iff.2 h0
    have hs' : ((‖X‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hX' : (((‖X‖ : ℝ) : ℂ)⁻¹ • X) ∈ ComplexMatrix2.traceless :=
      ComplexMatrix2.traceless.smul_mem _ hX
    have hn : ‖((‖X‖ : ℝ) : ℂ)⁻¹ • X‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, norm_norm]
      exact inv_mul_cancel₀ hs.ne'
    have hb : ‖covariantSmoothingDeriv V (singleLinkForm b (((‖X‖ : ℝ) : ℂ)⁻¹ • X)) c‖ ≤
        80 * ρ⁻¹ :=
      S.norm_covariantSmoothingDeriv_le step hc (S.singleLinkForm_mem hX') fun b' _ =>
        (norm_singleLinkForm_le b b' _).trans hn.le
    have e : X = ((‖X‖ : ℝ) : ℂ) • (((‖X‖ : ℝ) : ℂ)⁻¹ • X) := by
      rw [smul_smul, mul_inv_cancel₀ hs', one_smul]
    have e' : covariantSmoothingDeriv V (singleLinkForm b X) c =
        ((‖X‖ : ℝ) : ℂ) • covariantSmoothingDeriv V
          (singleLinkForm b (((‖X‖ : ℝ) : ℂ)⁻¹ • X)) c := by
      conv_lhs => rw [e]
      exact hsmul _ _ hX'
    show ‖covariantSmoothingDeriv V (singleLinkForm b X) c‖ ≤ 80 * ρ⁻¹ * ‖X‖
    rw [e', norm_smul, Complex.norm_real, norm_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right hb hs.le
theorem StepData.covariantSmoothingDeriv_eq_finsum (S : StepData ρ V c)
    {U : Edge L k 0 → ComplexMatrix2} (step : StepConditions j V U) (hc : c.IsPositivelyOriented)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    covariantSmoothingDeriv V B c =
      ∑ᶠ b ∈ positiveDoubleCubeLinks c,
        covariantSmoothingDeriv V (singleLinkForm b (B b)) c := by
  classical
  have ha := S.mesh_pos
  have hfin : (positiveDoubleCubeLinks c : Set (Edge L k j)).Finite :=
    S.links_finite.subset fun b hb => hb.1
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hform : ∀ b ∈ hfin.toFinset, singleLinkForm b (B b) ∈ complexEdgeForms (meshAt L k j) :=
    fun b hb => S.singleLinkForm_mem (hB.1 b ((hfin.mem_toFinset.1 hb).2))
  have hsum : ∀ s : Finset (Edge L k j), s ⊆ hfin.toFinset →
      (∑ b ∈ s, singleLinkForm b (B b)) ∈ complexEdgeForms (meshAt L k j) ∧
      covariantSmoothingDeriv V (∑ b ∈ s, singleLinkForm b (B b)) c =
        ∑ b ∈ s, covariantSmoothingDeriv V (singleLinkForm b (B b)) c := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨by simp, ?_⟩
      have h := covariantSmoothingDeriv_smul step hc (complexEdgeForms (meshAt L k j)).zero_mem 0
      simpa using h
    | insert a s ha' ih =>
      intro hs
      obtain ⟨h₁, h₂⟩ := ih fun x hx => hs (Finset.mem_insert_of_mem hx)
      have h₃ := hform a (hs (Finset.mem_insert_self a s))
      rw [Finset.sum_insert ha', Finset.sum_insert ha']
      refine ⟨(complexEdgeForms (meshAt L k j)).add_mem h₃ h₁, ?_⟩
      rw [covariantSmoothingDeriv_add step hc h₃ h₁, h₂]
  obtain ⟨hB', hQ⟩ := hsum _ subset_rfl
  rw [← hQ]
  refine S.covariantSmoothingDeriv_congr step hc hB hB' fun b hb => ?_
  have hpos : ∀ b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c,
      b.IsPositivelyOriented →
      B b = (∑ b' ∈ hfin.toFinset, singleLinkForm b' (B b')) b := by
    intro b hb hp
    rw [Finset.sum_apply, Finset.sum_eq_single b]
    · exact (singleLinkForm_same hp _).symm
    · intro b' _ hne
      exact singleLinkForm_of_ne hp hne.symm _
    · intro hnot
      exact absurd (hfin.mem_toFinset.2 ⟨hb, hp⟩) hnot
  by_cases hp : b.IsPositivelyOriented
  · exact hpos b hb hp
  · have hr := opposite_positive ha hp
    have h₁ := hB.2 b.opposite
    have h₂ := hB'.2 b.opposite
    rw [opposite_opposite] at h₁ h₂
    rw [h₁, h₂, hpos _ (S.opposite_mem b hb) hr]
end SingleLinks
theorem complexSmoothing_congr (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i < k)
    {c : Edge L k (i + 1)} (hc : c.IsPositivelyOriented) {V V' : Edge L k i → ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k i (polydiscRadius L) c)
    (hV' : V' ∈ nearIdentityPolydisc L k i (polydiscRadius L) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k i) c, V b = V' b) :
    complexSmoothing L V c = complexSmoothing L V' c := by apply _root_.YangMills.Construction.Tower.MeanStableFields.Infinite.complexSmoothing_congr <;> assumption
theorem stepKernelBounds_holds
    (hEL : ComplexMatrix2.ExpLogEstimates)
    (hA : ComplexMatrix2.ConjugationPreservesTraceless)
    (hlc : LeftChartFields.Claim)
    (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hC : YangMills.Construction.Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hT : RescaledTrivialSteps)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hB : PairContourIndependence.Statement)
    (hZ : BlockStructure) :
    StepKernelBounds := by
  classical
  intro L hL k j hj c hc V hV hclose
  have hk : 1 ≤ k := by omega
  have hρ := (hS.1 L hL).2.2
  have hd := (hP L hL k j hj).2 c hc
  have hfo := hd.finite_open
  have hLpos : 0 < L := by have := hL.2; omega
  have hspacing : 0 < meshAt L k j := by
    have : (0 : ℝ) < L := by exact_mod_cast hLpos
    exact zpow_pos this _
  have hblock : ∀ y : Vertex L k (j + 1),
      (cube L (meshAt L k j) y).ncard = L ^ 4 ∧
        (cube L (meshAt L k j) y).Finite := fun y => by
    have hb := (hZ L k (j + 1) hL (by omega) (by omega) hj).2.1 y
    have hcard : (cube L (meshAt L k j) y).ncard = L ^ 4 := hb.2.2.1
    exact ⟨hcard, Set.finite_of_ncard_pos (by rw [hcard]; positivity)⟩
  have S : StepData (polydiscRadius L) V c :=
    { expLog := hEL
      logCurves := hlc.2.1
      radius_pos := hρ.pos
      radius_le_one := hρ.le_one
      mesh_pos := hspacing
      mem_fields := hV
      near_one := hclose
      links_finite := hfo.finite
      opposite_mem := hfo.opposite_mem
      admissible := hρ.fullSpace k j hj c hc
      smoothing_local := fun W W' h₁ h₂ he => complexSmoothing_congr hS hQ hL hj hc h₁ h₂ he
      contour_local := fun y hy x hx W hW hWp W' hr =>
        ((hB L hL k j hj).2 y x hx c c hc hc hy hy W hW hWp.2 hWp.2 W' W hr
          (fun _ _ => rfl)).2.2
      cube_finite := fun y =>
        Set.Finite.preimage (f := Subtype.val) Subtype.val_injective.injOn (hblock y).2
      cube_ncard_le := fun y => by
        rw [← (hblock y).1]
        exact Set.ncard_le_ncard_of_injOn Subtype.val (fun x hx => hx)
          Subtype.val_injective.injOn (hblock y).2
      factor_pos := hLpos }
  have hsm : V ∈ smallComplexFields L k j :=
    ⟨hV, fun b => (hclose b).trans (by have := hρ.pos; linarith)⟩
  have step := (hC L hL k hk).2.1 j hj V hsm _ (hT L hL k hk).1
  exact ⟨fun B hB => S.covariantSmoothingDeriv_eq_finsum step hc hB,
    fun b _ => S.isBoundedTracelessEndo_stepKernel hA step hc,
    fun y hy x hx => isBoundedTracelessEndo_conjugateBy hEL hA
      (S.admissible.contourMean_near_one V S.self_mem_polydisc y hy x hx)⟩
end YangMills.Construction.Tower.FullSpace.StepKernels
end
