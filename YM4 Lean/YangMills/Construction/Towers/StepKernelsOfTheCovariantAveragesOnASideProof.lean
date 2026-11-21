import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Matrices.ConjugationOnTraceless
import YangMills.Construction.RunningCouplingSlope.PlainStepNearTheCovariantStepProof
import YangMills.Construction.Towers.StepKernelsOfTheCovariantAveragesOnASide
import Mathlib
set_option autoImplicit false
open Set Filter Metric
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.StepKernels
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.LeftChartFields YangMills.Construction.Tower.AsDifferentials
section Matrices
theorem norm_mul_sub_one_le_prod (X Y : ComplexMatrix2) :
    ‖X * Y - 1‖ ≤ (1 + ‖X - 1‖) * (1 + ‖Y - 1‖) - 1 := by apply _root_.YangMills.SharedProofs.p30838 <;> assumption
theorem expI_mul_mem_unitDet (hEL : ComplexMatrix2.ExpLogEstimates) {X g : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    ComplexMatrix2.matExp (Complex.I • X) * g ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.Construction.Tower.AsDifferentials.expChart_mem_unitDeterminant <;> assumption
theorem inv_mem_unitDet {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    g⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDet {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    (g⁻¹)⁻¹ = g := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
theorem bounds_of_near_one (hEL : ComplexMatrix2.ExpLogEstimates) {g : ComplexMatrix2}
    (hg : ‖g - 1‖ < 1 / 2) : IsUnit g ∧ ‖g‖ ≤ 3 / 2 ∧ ‖g⁻¹‖ ≤ 2 := by
  have h := hEL.2.2.2.1 (g - 1) (by show ‖g - 1‖ < 1; linarith)
  have e : 1 + (g - 1) = g := by abel
  rw [e] at h
  obtain ⟨-, -, hu, hi, -⟩ := h
  have h1 : ‖(1 : ComplexMatrix2)‖ = 1 := norm_one
  refine ⟨hu, ?_, ?_⟩
  · have : g = (g - 1) + 1 := by abel
    calc ‖g‖ = ‖(g - 1) + 1‖ := by rw [← this]
      _ ≤ ‖g - 1‖ + ‖(1 : ComplexMatrix2)‖ := norm_add_le _ _
      _ ≤ 3 / 2 := by rw [h1]; linarith
  · have hi' : ‖g⁻¹ - 1‖ ≤ ‖g - 1‖ / (1 - ‖g - 1‖) := hi
    have hb : ‖g - 1‖ / (1 - ‖g - 1‖) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have : g⁻¹ = (g⁻¹ - 1) + 1 := by abel
    calc ‖g⁻¹‖ = ‖(g⁻¹ - 1) + 1‖ := by rw [← this]
      _ ≤ ‖g⁻¹ - 1‖ + ‖(1 : ComplexMatrix2)‖ := norm_add_le _ _
      _ ≤ 2 := by rw [h1]; linarith
theorem norm_conjugateBy_le {g : ComplexMatrix2} (h₁ : ‖g‖ ≤ 3 / 2) (h₂ : ‖g⁻¹‖ ≤ 2)
    (X : ComplexMatrix2) : ‖ComplexMatrix2.conjugateBy g X‖ ≤ 3 * ‖X‖ := by apply _root_.YangMills.SharedProofs.p70374 <;> assumption
theorem conjugateBy_add (g X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (X + Y) =
      ComplexMatrix2.conjugateBy g X + ComplexMatrix2.conjugateBy g Y := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (g : ComplexMatrix2) (z : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (z • X) = z • ComplexMatrix2.conjugateBy g X := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
theorem isBoundedTracelessEndo_conjugateBy (hEL : ComplexMatrix2.ExpLogEstimates)
    (hA : ComplexMatrix2.ConjugationPreservesTraceless) {g : ComplexMatrix2}
    (hg : ‖g - 1‖ < 1 / 2) : IsBoundedTracelessEndo (ComplexMatrix2.conjugateBy g) 3 := by
  obtain ⟨hu, h₁, h₂⟩ := bounds_of_near_one hEL hg
  exact ⟨fun X hX => (hA.2.2 g hu).2.2.2.1 hX, fun X _ Y _ => conjugateBy_add g X Y,
    fun z X _ => conjugateBy_smul g z X, fun X _ => norm_conjugateBy_le h₁ h₂ X⟩
theorem norm_matExp_sub_one_le (hEL : ComplexMatrix2.ExpLogEstimates) {Z : ComplexMatrix2}
    (hZ : ‖Z‖ ≤ 1) : ‖ComplexMatrix2.matExp Z - 1‖ ≤ 2 * ‖Z‖ := by apply _root_.YangMills.SharedProofs.p10567 <;> assumption
end Matrices
variable {L n k j : ℕ}
structure KernelSetting (ρ : ℝ) (V : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1)) :
    Prop where
  explog : ComplexMatrix2.ExpLogEstimates
  curves : ∀ r : ℝ, 0 < r →
    CurveLogDerivative ℂ (Metric.ball 0 r) PeriodicLattice.complexGaugeGroup
      PeriodicLattice.complexLieAlgebra
  pos : 0 < ρ
  le_one : ρ ≤ 1
  xor : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  reverse : ∀ b : Edge L n k j, b.opposite.opposite = b
  conf : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup
  close : ∀ b, ‖V b - 1‖ < 3 / 4 * ρ
  finite : (DoubleBlockPolydisc.doubleBlockBonds c).Finite
  closed : ∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c,
    b.opposite ∈ DoubleBlockPolydisc.doubleBlockBonds c
  serves : PolydiscIsAdmissible ρ c
  average_reads : ∀ W W' : Edge L n k j → ComplexMatrix2,
    (∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, W b = W' b) →
    PeriodicLattice.complexBlockAverage W c = PeriodicLattice.complexBlockAverage W' c
  contour_reads : ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
    ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup, W ∈ nearIdentityPolydisc ρ c →
    ∀ W' : Edge L n k j → ComplexMatrix2,
      (∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, W' b = W b) →
      PeriodicLattice.complexMeanContourHolonomy W' y x =
        PeriodicLattice.complexMeanContourHolonomy W y x
  block_finite : ∀ y : Vertex L n k (j + 1),
    (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y : Set (Vertex L n k j)).Finite
  block_card : ∀ y : Vertex L n k (j + 1),
    (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).ncard ≤ L ^ 4
  L_pos : 0 < L
section Curves
variable {ρ : ℝ} {V : Edge L n k j → ComplexMatrix2} {c : Edge L n k (j + 1)}
theorem KernelSetting.opposite_positive (S : KernelSetting ρ V c) {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases S.xor b with h | h
  exacts [absurd h.1 hb, h.1]
theorem KernelSetting.not_opposite_positive (S : KernelSetting ρ V c) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  rcases S.xor b with h | h
  exacts [h.2, absurd hb h.2]
theorem expTwist_of_positive {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
theorem expTwist_of_not_positive {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
theorem KernelSetting.expTwist_mem (S : KernelSetting ρ V c) {C : Edge L n k j → ComplexMatrix2}
    (hC : C ∈ complexEdgeForms L n k j) :
    PeriodicLattice.expTwist C V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  have hval : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • C b) * V b ∈ ComplexMatrix2.unitDeterminant :=
    fun b hb => expI_mul_mem_unitDet S.explog (hC.1 b hb) (S.conf.1 b (mem_univ b))
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_of_positive hb]
      exact hval b hb
    · rw [expTwist_of_not_positive hb]
      exact inv_mem_unitDet (hval _ (S.opposite_positive hb))
  · by_cases hb : b.IsPositivelyOriented
    · have hr := S.not_opposite_positive hb
      rw [expTwist_of_not_positive hr, expTwist_of_positive hb, S.reverse b]
    · have hr := S.opposite_positive hb
      rw [expTwist_of_positive hr, expTwist_of_not_positive hb]
      exact (inv_inv_of_mem_unitDet (hval _ hr)).symm
theorem KernelSetting.mem_polydisc_self (S : KernelSetting ρ V c) : V ∈ nearIdentityPolydisc ρ c :=
  ⟨⟨fun b _ => S.conf.1 b (mem_univ b), fun b _ => S.conf.2 b (mem_univ b)⟩,
    fun b _ => (S.close b).trans (by have := S.pos; linarith)⟩
theorem KernelSetting.expTwist_zero_smul (S : KernelSetting ρ V c)
    {B : Edge L n k j → ComplexMatrix2} : PeriodicLattice.expTwist ((0 : ℂ) • B) V = V := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [expTwist_of_positive hb]
    simp [ComplexMatrix2.matExp]
  · rw [expTwist_of_not_positive hb]
    have h₁ := S.conf.2 b.opposite (mem_univ _)
    rw [S.reverse b] at h₁
    simp only [Pi.smul_apply, zero_smul, smul_zero, ComplexMatrix2.matExp, NormedSpace.exp_zero,
      one_mul]
    exact h₁.symm
theorem KernelSetting.expTwist_mem_polydisc (S : KernelSetting ρ V c) {t : ℂ}
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j)
    (hsm : ∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, ‖t‖ * ‖B b‖ ≤ ρ / 16) :
    PeriodicLattice.expTwist (t • B) V ∈ nearIdentityPolydisc ρ c := by
  have hρ := S.pos
  have hρ1 := S.le_one
  have hW := S.expTwist_mem ((complexEdgeForms L n k j).smul_mem t hB)
  refine ⟨⟨fun b _ => hW.1 b (mem_univ b), fun b _ => hW.2 b (mem_univ b)⟩, fun b hb => ?_⟩
  have hnZ : ∀ b' ∈ DoubleBlockPolydisc.doubleBlockBonds c,
      ‖Complex.I • (t • B) b'‖ ≤ ρ / 16 := fun b' hb' => by
    have : ‖Complex.I • (t • B) b'‖ = ‖t‖ * ‖B b'‖ := by
      simp [norm_smul]
    rw [this]
    exact hsm b' hb'
  have hexp : ∀ Z : ComplexMatrix2, ‖Z‖ ≤ ρ / 16 →
      ‖ComplexMatrix2.matExp Z - 1‖ ≤ ρ / 8 := fun Z hZ => by
    have := norm_matExp_sub_one_le S.explog (Z := Z) (by linarith)
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
    exact hfin _ _ (hexp _ (hnZ b hb)) (S.close b).le
  · rw [expTwist_of_not_positive hp, Matrix.mul_inv_rev]
    have h₁ := S.conf.2 b.opposite (mem_univ _)
    rw [S.reverse b] at h₁
    rw [← h₁, ← Matrix.exp_neg]
    refine hfin' _ _ (S.close b).le (hexp _ ?_)
    rw [norm_neg]
    exact hnZ _ (S.closed b hb)
def twistedCurve (c : Edge L n k (j + 1)) (V B : Edge L n k j → ComplexMatrix2) (t : ℂ) :
    PeriodicLattice.PositiveBondOf (DoubleBlockPolydisc.doubleBlockBonds c) → ComplexMatrix2 :=
  PeriodicLattice.restrictToPositive _ (PeriodicLattice.expTwist (t • B) V)
theorem twistedCurve_apply (B : Edge L n k j → ComplexMatrix2) (t : ℂ)
    (b : PeriodicLattice.PositiveBondOf (DoubleBlockPolydisc.doubleBlockBonds c)) :
    twistedCurve c V B t b = ComplexMatrix2.matExp (t • (Complex.I • B b.1)) * V b.1 := by
  have : Complex.I • (t • B) b.1 = t • (Complex.I • B b.1) := by
    simp only [Pi.smul_apply]
    exact smul_comm _ _ _
  simp only [twistedCurve, PeriodicLattice.restrictToPositive]
  rw [expTwist_of_positive b.2.2, this]
theorem KernelSetting.extend_restrict_eq (S : KernelSetting ρ V c)
    {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    ∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c,
      PeriodicLattice.extendFromPositive (DoubleBlockPolydisc.doubleBlockBonds c)
        (PeriodicLattice.restrictToPositive _ W) b = W b := by
  classical
  intro b hb
  by_cases hp : b.IsPositivelyOriented
  · simp [PeriodicLattice.extendFromPositive, PeriodicLattice.restrictToPositive, hb, hp]
  · have hr := S.opposite_positive hp
    have h₁ := hW.2 b.opposite (mem_univ _)
    rw [S.reverse b] at h₁
    have hrb := S.closed b hb
    simp [PeriodicLattice.extendFromPositive, PeriodicLattice.restrictToPositive, hb, hp, hr,
      hrb, h₁]
theorem twistedCurve_differentiableAt
    [Fintype (PeriodicLattice.PositiveBondOf (DoubleBlockPolydisc.doubleBlockBonds c))]
    (B : Edge L n k j → ComplexMatrix2) (t : ℂ) : DifferentiableAt ℂ (twistedCurve c V B) t := by
  refine differentiableAt_pi.2 fun b => ?_
  have e : (fun s => twistedCurve c V B s b) =
      fun s : ℂ => ComplexMatrix2.matExp (s • (Complex.I • B b.1)) * V b.1 := by
    funext s
    exact twistedCurve_apply B s b
  rw [e]
  exact ((hasDerivAt_exp_smul_const (𝕂 := ℂ) (Complex.I • B b.1) t).mul_const
    (V b.1)).differentiableAt
theorem KernelSetting.holomorphic_along_curve (S : KernelSetting ρ V c)
    {Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : PeriodicLattice.IsHolomorphicOnFields
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (nearIdentityPolydisc ρ c) Φ)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) {t₀ : ℂ}
    (ht₀ : PeriodicLattice.expTwist (t₀ • B) V ∈ nearIdentityPolydisc ρ c) :
    DifferentiableAt ℂ (fun t => Φ (PeriodicLattice.extendFromPositive
        (DoubleBlockPolydisc.doubleBlockBonds c) (twistedCurve c V B t))) t₀ ∧
      Φ (PeriodicLattice.extendFromPositive
        (DoubleBlockPolydisc.doubleBlockBonds c) (twistedCurve c V B t₀)) ∈
        PeriodicLattice.complexGaugeGroup := by
  obtain ⟨⟨inst, ⟨O', hO', hD⟩, hmaps, hloc⟩, -⟩ := hΦ
  have hx : twistedCurve c V B t₀ ∈
      PeriodicLattice.restrictToPositive (DoubleBlockPolydisc.doubleBlockBonds c) ''
        nearIdentityPolydisc ρ c := ⟨_, ht₀, rfl⟩
  have hxO : twistedCurve c V B t₀ ∈ O' := by
    have h := hx
    rw [hD] at h
    exact h.1
  have hprod : ∀ t, twistedCurve c V B t ∈
      ComplexMatrix2.complexifiedProduct fun _ : PeriodicLattice.PositiveBondOf
        (DoubleBlockPolydisc.doubleBlockBonds c) => ComplexMatrix2.FactorKind.group := fun t b =>
    (S.expTwist_mem ((complexEdgeForms L n k j).smul_mem t hB)).1 b.1 (mem_univ _)
  have hv := twistedCurve_differentiableAt (c := c) (V := V) B t₀
  have hmem : ∀ᶠ t in 𝓝 t₀, twistedCurve c V B t ∈
      PeriodicLattice.restrictToPositive (DoubleBlockPolydisc.doubleBlockBonds c) ''
        nearIdentityPolydisc ρ c := by
    filter_upwards [hv.continuousAt.eventually (hO'.mem_nhds hxO)] with t ht
    rw [hD]
    exact ⟨ht, hprod t⟩
  obtain ⟨F, hF, hev⟩ := hloc _ hx
  have h2 := (tendsto_nhdsWithin_iff.2 ⟨hv.continuousAt, hmem⟩).eventually hev
  have h3 : DifferentiableAt ℂ (fun t => F (twistedCurve c V B t)) t₀ :=
    hF.differentiableAt.comp t₀ hv
  have h4 : DifferentiableAt ℂ (fun t => F (twistedCurve c V B t) ()) t₀ :=
    differentiableAt_pi.1 h3 ()
  refine ⟨h4.congr_of_eventuallyEq ?_, hmaps hx ()⟩
  filter_upwards [h2] with t ht
  exact congrFun ht ()
theorem KernelSetting.norm_logDirectionalDeriv_le (S : KernelSetting ρ V c)
    {Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : PeriodicLattice.IsHolomorphicOnFields
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (nearIdentityPolydisc ρ c) Φ)
    (hsmall : ∀ W ∈ nearIdentityPolydisc ρ c, ‖Φ W - 1‖ < 1 / 2)
    (hread : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      W ∈ nearIdentityPolydisc ρ c → ∀ W' : Edge L n k j → ComplexMatrix2,
        (∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, W' b = W b) → Φ W' = Φ W)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j)
    (hB1 : ∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, ‖B b‖ ≤ 1) :
    ‖logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B‖ ≤
      16 * ρ⁻¹ := by
  have hρ := S.pos
  have hr0 : 0 < ρ / 16 := by positivity
  have hin : ∀ t ∈ closedBall (0 : ℂ) (ρ / 16),
      PeriodicLattice.expTwist (t • B) V ∈ nearIdentityPolydisc ρ c := fun t ht =>
    S.expTwist_mem_polydisc hB fun b hb => by
      have h1 : ‖t‖ ≤ ρ / 16 := by simpa using ht
      calc ‖t‖ * ‖B b‖ ≤ ρ / 16 * 1 :=
            mul_le_mul h1 (hB1 b hb) (norm_nonneg _) hr0.le
        _ = ρ / 16 := mul_one _
  have hconf : ∀ t : ℂ, PeriodicLattice.expTwist (t • B) V ∈
      fieldsIn L n k j PeriodicLattice.complexGaugeGroup := fun t =>
    S.expTwist_mem ((complexEdgeForms L n k j).smul_mem t hB)
  let w : ℂ → ComplexMatrix2 := fun t => Φ (PeriodicLattice.expTwist (t • B) V)
  have hagree : ∀ t ∈ closedBall (0 : ℂ) (ρ / 16),
      Φ (PeriodicLattice.extendFromPositive
        (DoubleBlockPolydisc.doubleBlockBonds c) (twistedCurve c V B t)) = w t := fun t ht =>
    hread _ (hconf t) (hin t ht) _ (S.extend_restrict_eq (hconf t))
  have hdiff : DifferentiableOn ℂ w (closedBall 0 (ρ / 16)) := fun t ht =>
    ((S.holomorphic_along_curve hΦ hB (hin t ht)).1.differentiableWithinAt).congr
      (fun s hs => (hagree s hs).symm) (hagree t ht).symm
  have hgroup : MapsTo w (ball 0 (ρ / 16)) PeriodicLattice.complexGaugeGroup := fun t ht => by
    have htc := ball_subset_closedBall ht
    have h := (S.holomorphic_along_curve hΦ hB (hin t htc)).2
    rwa [hagree t htc] at h
  have hw0 : DifferentiableAt ℂ w 0 :=
    (hdiff 0 (mem_closedBall_self hr0.le)).differentiableAt (closedBall_mem_nhds _ hr0)
  obtain ⟨-, -, heq, -⟩ := S.curves _ hr0 w hgroup hw0
  have hwV : w 0 = Φ V := by
    simp only [w]
    rw [S.expTwist_zero_smul]
  obtain ⟨-, -, hinv⟩ := bounds_of_near_one S.explog (hsmall V S.mem_polydisc_self)
  have hcauchy : ‖deriv w 0‖ ≤ 1 / 2 / (ρ / 16) := by
    have hf : DifferentiableOn ℂ (fun t => w t - 1) (closedBall 0 (ρ / 16)) := hdiff.sub_const 1
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0
      (hf.diffContOnCl_ball subset_rfl) (C := 1 / 2)
      fun z hz => (hsmall _ (hin z (sphere_subset_closedBall hz))).le
    rwa [deriv_sub_const] at h
  simp only [logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
  have e : Complex.I⁻¹ • deriv (fun t : ℂ =>
      ComplexMatrix2.logSeries (Φ (PeriodicLattice.expTwist (t • B) V) * (Φ V)⁻¹)) 0 =
      Complex.I⁻¹ • (deriv w 0 * (w 0)⁻¹) := by
    rw [← hwV]
    exact heq
  rw [e, norm_smul, hwV]
  have hI : ‖(Complex.I⁻¹ : ℂ)‖ = 1 := by simp
  rw [hI, one_mul]
  calc ‖deriv w 0 * (Φ V)⁻¹‖ ≤ ‖deriv w 0‖ * ‖(Φ V)⁻¹‖ := norm_mul_le _ _
    _ ≤ (1 / 2 / (ρ / 16)) * 2 := by gcongr
    _ = 16 * ρ⁻¹ := by field_simp
theorem KernelSetting.norm_contourLogDrift_le (S : KernelSetting ρ V c)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j)
    (hB1 : ∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, ‖B b‖ ≤ 1)
    {y : Vertex L n k (j + 1)} (hy : y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1)))) :
    ‖contourLogDrift V B y‖ ≤ 16 * ρ⁻¹ := by
  have hρ := S.pos
  have hfin := S.block_finite y
  have hterm : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      ‖logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
        (PeriodicLattice.complexMeanContourHolonomy V y x) B‖ ≤ 16 * ρ⁻¹ := fun x hx =>
    S.norm_logDirectionalDeriv_le
      (Φ := fun W => PeriodicLattice.complexMeanContourHolonomy W y x)
      (S.serves.holomorphic_contourMean y hy x hx)
      (fun W hW => S.serves.contourMean_near_one W hW y hy x hx)
      (fun W hW hWp W' h => S.contour_reads y hy x hx W hW hWp W' h) hB hB1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast S.L_pos
  have hw : ‖PeriodicLattice.inverseFourthPowerWeight L‖ = ((L : ℝ) ^ 4)⁻¹ := by
    have e : (L : ℝ) ^ (-4 : ℤ) = ((L : ℝ) ^ 4)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    simp only [PeriodicLattice.inverseFourthPowerWeight, e, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hcard : (hfin.toFinset.card : ℝ) ≤ (L : ℝ) ^ 4 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast S.block_card y
  simp only [contourLogDrift]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, norm_smul, hw]
  have hsum := norm_sum_le hfin.toFinset (fun x => logDirectionalDeriv ℂ
    (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
    (PeriodicLattice.complexMeanContourHolonomy V y x) B)
  have hle : ∑ x ∈ hfin.toFinset, ‖logDirectionalDeriv ℂ
      (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
      (PeriodicLattice.complexMeanContourHolonomy V y x) B‖ ≤
      (hfin.toFinset.card : ℝ) * (16 * ρ⁻¹) := by
    have := Finset.sum_le_card_nsmul hfin.toFinset _ (16 * ρ⁻¹)
      fun x hx => hterm x (hfin.mem_toFinset.1 hx)
    simpa [nsmul_eq_mul] using this
  have hb : (0 : ℝ) ≤ 16 * ρ⁻¹ := by positivity
  calc ((L : ℝ) ^ 4)⁻¹ * _ ≤ ((L : ℝ) ^ 4)⁻¹ * ((L : ℝ) ^ 4 * (16 * ρ⁻¹)) := by
        refine mul_le_mul_of_nonneg_left (hsum.trans (hle.trans ?_)) (by positivity)
        exact mul_le_mul_of_nonneg_right hcard hb
    _ = 16 * ρ⁻¹ := by field_simp
theorem complexSmoothingDeriv_apply (hc : c.IsPositivelyOriented)
    (B : Edge L n k j → ComplexMatrix2) :
    complexSmoothingDeriv V B c = logDirectionalDeriv ℂ
      (fun X => PeriodicLattice.complexBlockAverage (PeriodicLattice.expTwist X V) c)
      (PeriodicLattice.complexBlockAverage V c) B := by
  simp only [complexSmoothingDeriv, holLeftDifferential, extendOddly, if_pos hc]
  rfl
theorem covariantSmoothingDeriv_apply (hc : c.IsPositivelyOriented)
    (B : Edge L n k j → ComplexMatrix2) :
    covariantSmoothingDeriv V B c = complexSmoothingDeriv V B c +
      (ComplexMatrix2.conjugateBy (PeriodicLattice.complexBlockAverage V c)
        (contourLogDrift V B c.target) - contourLogDrift V B c.source) := by
  simp only [covariantSmoothingDeriv, Pi.add_apply, covDiff, extendOddly, if_pos hc]
  rfl
theorem KernelSetting.norm_covariantSmoothingDeriv_le (S : KernelSetting ρ V c)
    (hc : c.IsPositivelyOriented)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j)
    (hB1 : ∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, ‖B b‖ ≤ 1) :
    ‖covariantSmoothingDeriv V B c‖ ≤ 80 * ρ⁻¹ := by
  have h₁ : ‖complexSmoothingDeriv V B c‖ ≤ 16 * ρ⁻¹ := by
    rw [complexSmoothingDeriv_apply hc]
    exact S.norm_logDirectionalDeriv_le
      (Φ := fun W => PeriodicLattice.complexBlockAverage W c)
      S.serves.holomorphic_smoothing S.serves.smoothing_near_one
      (fun W _ _ W' h => S.average_reads W' W h) hB hB1
  have h₂ := S.norm_contourLogDrift_le hB hB1 (y := c.target) (Or.inr rfl)
  have h₃ := S.norm_contourLogDrift_le hB hB1 (y := c.source) (Or.inl rfl)
  obtain ⟨-, hg₁, hg₂⟩ :=
    bounds_of_near_one S.explog (S.serves.smoothing_near_one V S.mem_polydisc_self)
  have h₄ := norm_conjugateBy_le hg₁ hg₂ (contourLogDrift V B c.target)
  rw [covariantSmoothingDeriv_apply hc]
  have h₅ := norm_add_le (complexSmoothingDeriv V B c)
    (ComplexMatrix2.conjugateBy (PeriodicLattice.complexBlockAverage V c)
      (contourLogDrift V B c.target) - contourLogDrift V B c.source)
  have h₆ := norm_sub_le (ComplexMatrix2.conjugateBy (PeriodicLattice.complexBlockAverage V c)
    (contourLogDrift V B c.target)) (contourLogDrift V B c.source)
  linarith
theorem KernelSetting.expTwist_congr (S : KernelSetting ρ V c)
    {B B' : Edge L n k j → ComplexMatrix2}
    (hag : ∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, B b = B' b) (t : ℂ) :
    ∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c,
      PeriodicLattice.expTwist (t • B) V b = PeriodicLattice.expTwist (t • B') V b := by
  intro b hb
  by_cases hp : b.IsPositivelyOriented
  · rw [expTwist_of_positive hp, expTwist_of_positive hp]
    simp only [Pi.smul_apply, hag b hb]
  · rw [expTwist_of_not_positive hp, expTwist_of_not_positive hp]
    simp only [Pi.smul_apply, hag _ (S.closed b hb)]
theorem KernelSetting.eventually_mem_polydisc (S : KernelSetting ρ V c)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    ∀ᶠ t : ℂ in 𝓝 0, PeriodicLattice.expTwist (t • B) V ∈ nearIdentityPolydisc ρ c := by
  have hρ := S.pos
  obtain ⟨R, hR⟩ := (S.finite.image fun b => ‖B b‖).bddAbove
  filter_upwards [ball_mem_nhds (0 : ℂ) (show 0 < ρ / 16 / max R 1 by positivity)] with t ht
  refine S.expTwist_mem_polydisc hB fun b hb => ?_
  have ht' : ‖t‖ ≤ ρ / 16 / max R 1 := by
    have : ‖t‖ < ρ / 16 / max R 1 := by simpa using ht
    exact this.le
  have hb' : ‖B b‖ ≤ max R 1 := (hR ⟨b, hb, rfl⟩).trans (le_max_left _ _)
  calc ‖t‖ * ‖B b‖ ≤ ρ / 16 / max R 1 * max R 1 :=
        mul_le_mul ht' hb' (norm_nonneg _) (by positivity)
    _ = ρ / 16 := by field_simp
theorem KernelSetting.covariantSmoothingDeriv_congr (S : KernelSetting ρ V c)
    (hc : c.IsPositivelyOriented)
    {B B' : Edge L n k j → ComplexMatrix2} (hB' : B' ∈ complexEdgeForms L n k j)
    (hag : ∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, B b = B' b) :
    covariantSmoothingDeriv V B c = covariantSmoothingDeriv V B' c := by
  have h₁ : complexSmoothingDeriv V B c = complexSmoothingDeriv V B' c := by
    rw [complexSmoothingDeriv_apply hc, complexSmoothingDeriv_apply hc]
    have e : ∀ t : ℂ,
        PeriodicLattice.complexBlockAverage (PeriodicLattice.expTwist (t • B) V) c =
        PeriodicLattice.complexBlockAverage (PeriodicLattice.expTwist (t • B') V) c := fun t =>
      S.average_reads _ _ (S.expTwist_congr hag t)
    simp only [logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply, e]
  have h₂ : ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
      contourLogDrift V B y = contourLogDrift V B' y := by
    intro y hy
    have hterm : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        logDirectionalDeriv ℂ
          (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
          (PeriodicLattice.complexMeanContourHolonomy V y x) B =
        logDirectionalDeriv ℂ
          (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
          (PeriodicLattice.complexMeanContourHolonomy V y x) B' := by
      intro x hx
      have e : (fun t : ℂ => ComplexMatrix2.logSeries
            (PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist (t • B) V) y x *
              (PeriodicLattice.complexMeanContourHolonomy V y x)⁻¹)) =ᶠ[𝓝 0]
          fun t : ℂ => ComplexMatrix2.logSeries
            (PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist (t • B') V) y x *
              (PeriodicLattice.complexMeanContourHolonomy V y x)⁻¹) := by
        filter_upwards [S.eventually_mem_polydisc hB'] with t ht
        rw [S.contour_reads y hy x hx _
          (S.expTwist_mem ((complexEdgeForms L n k j).smul_mem t hB'))
          ht _ (S.expTwist_congr hag t)]
      simp only [logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
      rw [e.deriv_eq]
    exact congrArg (PeriodicLattice.inverseFourthPowerWeight L • ·) (finsum_mem_congr rfl hterm)
  have ht : contourLogDrift V B c.source = contourLogDrift V B' c.source := h₂ c.source (Or.inl rfl)
  have hh : contourLogDrift V B c.target = contourLogDrift V B' c.target := h₂ c.target (Or.inr rfl)
  rw [covariantSmoothingDeriv_apply hc, covariantSmoothingDeriv_apply hc, h₁, ht, hh]
end Curves
section Kernels
variable {ρ : ℝ} {V : Edge L n k j → ComplexMatrix2} {c : Edge L n k (j + 1)}
theorem KernelSetting.extendOddly_opposite (S : KernelSetting ρ V c)
    (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by
  by_cases hb : b.IsPositivelyOriented
  · have hr := S.not_opposite_positive hb
    simp [extendOddly, hb, hr, S.reverse b]
  · have hr := S.opposite_positive hb
    simp [extendOddly, hb, hr]
theorem singleBondForm_self {b : Edge L n k j} (hb : b.IsPositivelyOriented) (X : ComplexMatrix2) :
    singleBondForm b X b = X := by
  simp [singleBondForm, extendOddly, hb]
theorem singleBondForm_of_ne {b b' : Edge L n k j} (hb' : b'.IsPositivelyOriented) (h : b' ≠ b)
    (X : ComplexMatrix2) : singleBondForm b X b' = 0 := by
  simp [singleBondForm, extendOddly, hb', h]
theorem KernelSetting.singleBondForm_mem (S : KernelSetting ρ V c) {b : Edge L n k j}
    {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    singleBondForm b X ∈ complexEdgeForms L n k j := by
  refine (⟨fun b' hb' => ?_, fun b' => S.extendOddly_opposite _ b'⟩ :
    PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra _)
  show singleBondForm b X b' ∈ ComplexMatrix2.traceless
  by_cases h : b' = b
  · subst h
    rw [singleBondForm_self hb']
    exact hX
  · rw [singleBondForm_of_ne hb' h]
    exact ComplexMatrix2.traceless.zero_mem
theorem singleBondForm_add (b : Edge L n k j) (X Y : ComplexMatrix2) :
    singleBondForm b (X + Y) = singleBondForm b X + singleBondForm b Y := by
  funext b'
  simp only [singleBondForm, extendOddly, Pi.add_apply]
  split_ifs <;> simp [add_comm]
theorem singleBondForm_smul (b : Edge L n k j) (z : ℂ) (X : ComplexMatrix2) :
    singleBondForm b (z • X) = z • singleBondForm b X := by
  funext b'
  simp only [singleBondForm, extendOddly, Pi.smul_apply]
  split_ifs <;> simp
theorem norm_singleBondForm_le (b b' : Edge L n k j) (X : ComplexMatrix2) :
    ‖singleBondForm b X b'‖ ≤ ‖X‖ := by
  simp only [singleBondForm, extendOddly]
  split_ifs <;> simp
theorem covariantSmoothingDeriv_add {U : Edge L n k 0 → ComplexMatrix2}
    (step : StepConditions j V U) (hc : c.IsPositivelyOriented)
    {B B' : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j)
    (hB' : B' ∈ complexEdgeForms L n k j) :
    covariantSmoothingDeriv V (B + B') c =
      covariantSmoothingDeriv V B c + covariantSmoothingDeriv V B' c := by
  rw [covariantSmoothingDeriv_apply hc, covariantSmoothingDeriv_apply hc,
    covariantSmoothingDeriv_apply hc,
    (step.linear_mean B hB B' hB' 0).1, (step.linear_contour B hB B' hB' 0).1]
  simp only [Pi.add_apply, conjugateBy_add]
  abel
theorem covariantSmoothingDeriv_smul {U : Edge L n k 0 → ComplexMatrix2}
    (step : StepConditions j V U) (hc : c.IsPositivelyOriented)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) (z : ℂ) :
    covariantSmoothingDeriv V (z • B) c = z • covariantSmoothingDeriv V B c := by
  rw [covariantSmoothingDeriv_apply hc, covariantSmoothingDeriv_apply hc,
    (step.linear_mean B hB B hB z).2, (step.linear_contour B hB B hB z).2]
  simp only [Pi.smul_apply, conjugateBy_smul, smul_add, smul_sub]
theorem KernelSetting.covariantSmoothingDeriv_mem (S : KernelSetting ρ V c)
    (hA : ComplexMatrix2.ConjugationPreservesTraceless) {U : Edge L n k 0 → ComplexMatrix2}
    (step : StepConditions j V U) (hc : c.IsPositivelyOriented) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) :
    covariantSmoothingDeriv V B c ∈ ComplexMatrix2.traceless := by
  obtain ⟨hu, -, -⟩ :=
    bounds_of_near_one S.explog (S.serves.smoothing_near_one V S.mem_polydisc_self)
  rw [covariantSmoothingDeriv_apply hc]
  exact ComplexMatrix2.traceless.add_mem (step.mem_mean c hc B hB)
    (ComplexMatrix2.traceless.sub_mem ((hA.2.2 _ hu).2.2.2.1 (step.mem_contour _ B hB))
      (step.mem_contour _ B hB))
theorem KernelSetting.stepKernel_isBoundedTracelessEndo (S : KernelSetting ρ V c)
    (hA : ComplexMatrix2.ConjugationPreservesTraceless) {U : Edge L n k 0 → ComplexMatrix2}
    (step : StepConditions j V U) (hc : c.IsPositivelyOriented) {b : Edge L n k j} :
    IsBoundedTracelessEndo (stepKernel V c b) (80 * ρ⁻¹) := by
  have hadd : ∀ X ∈ ComplexMatrix2.traceless, ∀ Y ∈ ComplexMatrix2.traceless,
      stepKernel V c b (X + Y) = stepKernel V c b X + stepKernel V c b Y := fun X hX Y hY => by
    simp only [stepKernel, singleBondForm_add]
    exact covariantSmoothingDeriv_add step hc (S.singleBondForm_mem hX) (S.singleBondForm_mem hY)
  have hsmul : ∀ z : ℂ, ∀ X ∈ ComplexMatrix2.traceless,
      stepKernel V c b (z • X) = z • stepKernel V c b X := fun z X hX => by
    simp only [stepKernel, singleBondForm_smul]
    exact covariantSmoothingDeriv_smul step hc (S.singleBondForm_mem hX) z
  refine ⟨fun X hX => S.covariantSmoothingDeriv_mem hA step hc (S.singleBondForm_mem hX), hadd,
    hsmul, fun X hX => ?_⟩
  by_cases h0 : X = 0
  · subst h0
    have h := hsmul 0 0 ComplexMatrix2.traceless.zero_mem
    simp only [zero_smul] at h
    simp [h]
  · have hs : 0 < ‖X‖ := norm_pos_iff.2 h0
    have hs' : ((‖X‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hX' : (((‖X‖ : ℝ) : ℂ)⁻¹ • X) ∈ ComplexMatrix2.traceless :=
      ComplexMatrix2.traceless.smul_mem _ hX
    have hn : ‖((‖X‖ : ℝ) : ℂ)⁻¹ • X‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, norm_norm]
      exact inv_mul_cancel₀ hs.ne'
    have hb : ‖stepKernel V c b (((‖X‖ : ℝ) : ℂ)⁻¹ • X)‖ ≤ 80 * ρ⁻¹ :=
      S.norm_covariantSmoothingDeriv_le hc (S.singleBondForm_mem hX') fun b' _ =>
        (norm_singleBondForm_le b b' _).trans hn.le
    have e : X = ((‖X‖ : ℝ) : ℂ) • (((‖X‖ : ℝ) : ℂ)⁻¹ • X) := by
      rw [smul_smul, mul_inv_cancel₀ hs', one_smul]
    have e' : stepKernel V c b X =
        ((‖X‖ : ℝ) : ℂ) • stepKernel V c b (((‖X‖ : ℝ) : ℂ)⁻¹ • X) := by
      conv_lhs => rw [e]
      exact hsmul _ _ hX'
    show ‖stepKernel V c b X‖ ≤ 80 * ρ⁻¹ * ‖X‖
    rw [e', norm_smul, Complex.norm_real, norm_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right hb hs.le
theorem KernelSetting.covariantSmoothingDeriv_eq_finsum (S : KernelSetting ρ V c)
    {U : Edge L n k 0 → ComplexMatrix2}
    (step : StepConditions j V U) (hc : c.IsPositivelyOriented) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) :
    covariantSmoothingDeriv V B c =
      ∑ᶠ b ∈ positiveDoubleBlockEdges c, stepKernel V c b (B b) := by
  classical
  have hfin : (positiveDoubleBlockEdges c : Set (Edge L n k j)).Finite :=
    S.finite.subset fun b hb => hb.1
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hform : ∀ b ∈ hfin.toFinset, singleBondForm b (B b) ∈ complexEdgeForms L n k j :=
    fun b hb => S.singleBondForm_mem (hB.1 b ((hfin.mem_toFinset.1 hb).2))
  have hsum : ∀ s : Finset (Edge L n k j), s ⊆ hfin.toFinset →
      (∑ b ∈ s, singleBondForm b (B b)) ∈ complexEdgeForms L n k j ∧
      covariantSmoothingDeriv V (∑ b ∈ s, singleBondForm b (B b)) c =
        ∑ b ∈ s, stepKernel V c b (B b) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨by simp, ?_⟩
      have h := covariantSmoothingDeriv_smul step hc (complexEdgeForms L n k j).zero_mem 0
      simpa using h
    | insert a s ha ih =>
      intro hs
      obtain ⟨h₁, h₂⟩ := ih fun x hx => hs (Finset.mem_insert_of_mem hx)
      have h₃ := hform a (hs (Finset.mem_insert_self a s))
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine ⟨(complexEdgeForms L n k j).add_mem h₃ h₁, ?_⟩
      rw [covariantSmoothingDeriv_add step hc h₃ h₁, h₂]
      rfl
  obtain ⟨hB', hQ⟩ := hsum _ subset_rfl
  rw [← hQ]
  refine S.covariantSmoothingDeriv_congr hc hB' fun b hb => ?_
  have hpos : ∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, b.IsPositivelyOriented →
      B b = (∑ b' ∈ hfin.toFinset, singleBondForm b' (B b')) b := by
    intro b hb hp
    rw [Finset.sum_apply, Finset.sum_eq_single b]
    · exact (singleBondForm_self hp _).symm
    · intro b' _ hne
      exact singleBondForm_of_ne hp hne.symm _
    · intro hnot
      exact absurd (hfin.mem_toFinset.2 ⟨hb, hp⟩) hnot
  by_cases hp : b.IsPositivelyOriented
  · exact hpos b hb hp
  · have hr := S.opposite_positive hp
    have h₁ := hB.2 b.opposite
    have h₂ := hB'.2 b.opposite
    rw [S.reverse b] at h₁ h₂
    rw [h₁, h₂, hpos _ (S.closed b hb) hr]
end Kernels
theorem stepKernelBounds_holds
    (hEL : ComplexMatrix2.ExpLogEstimates)
    (hA : ComplexMatrix2.ConjugationPreservesTraceless)
    (hlc : LeftChartFields.Claim)
    (hS : SmoothingNearIdentity)
    (hC : AsDifferentials.CovariantMeansAreDerivatives)
    (hT : RescaledTrivialSteps)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hB : PairContourIndependence.Statement)
    (hZ : BlockStructure) :
    StepKernelBounds := by
  classical
  intro L hL n k j hn hj c hc V hV hclose
  have hk : 1 ≤ k := by omega
  have hρ := (hS.1 L hL).2.2
  have hd := (hP L hL k j hj).1 n hn c hc
  have hfo := hd.finite_open
  have hLpos : 0 < L := by have := hL.2; omega
  have hblock : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.unitBlock y).ncard = L ^ 4 ∧ (PeriodicLattice.unitBlock y).Finite :=
    fun y => by
    have hb := ((hZ L k (j + 1) hL hk (by omega) (by omega)).1 n hn).1 y
    have hcard : (PeriodicLattice.unitBlock y).ncard = L ^ 4 := hb.2.2.1
    exact ⟨hcard, Set.finite_of_ncard_pos (by rw [hcard]; positivity)⟩
  have S : KernelSetting (polydiscRadius L) V c :=
    { explog := hEL
      curves := hlc.2.1
      pos := hρ.pos
      le_one := hρ.le_one
      xor := fun b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj.le).2.2.2 b).2.2.2.2.2
      reverse := fun b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj.le).2.2.2 b).2.2.2.1
      conf := hV
      close := hclose
      finite := hfo.finite
      closed := hfo.opposite_mem
      serves := hρ.periodic n k j hn hj c hc
      average_reads := fun W W' he => by
        unfold PeriodicLattice.complexBlockAverage
        simp only [if_pos hc]
        exact (hR L n k j hL.1 hL.2 hn hj c hc).average_eq _ _ he
      contour_reads := fun y hy x hx W hW hWp W' hr =>
        ((hB L hL k j hj).1 n hn y x hx c c hc hc hy hy W hW hWp.2 hWp.2 W' W hr
          (fun _ _ => rfl)).2.2
      block_finite := fun y =>
        Set.Finite.preimage (f := Subtype.val) Subtype.val_injective.injOn (hblock y).2
      block_card := fun y => by
        rw [← (hblock y).1]
        exact Set.ncard_le_ncard_of_injOn Subtype.val (fun x hx => hx)
          Subtype.val_injective.injOn (hblock y).2
      L_pos := hLpos }
  have hsm : V ∈ smallComplexFields L n k j :=
    ⟨hV, fun b => (hclose b).trans (by have := hρ.pos; linarith)⟩
  have step := ((hC L hL k hk).1 n hn).1 j hj V hsm _ (hT L hL k hk n hn).1
  exact ⟨fun B hB => S.covariantSmoothingDeriv_eq_finsum step hc hB,
    fun b _ => S.stepKernel_isBoundedTracelessEndo hA step hc,
    fun y hy x hx => isBoundedTracelessEndo_conjugateBy hEL hA
      (S.serves.contourMean_near_one V S.mem_polydisc_self y hy x hx)⟩
end YangMills.Construction.Tower.StepKernels
end
