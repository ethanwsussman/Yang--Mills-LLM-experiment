import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.OneLoopLaw.FunctionalsAsTotalFunctionals
import YangMills.Construction.PeriodicLattice.TriplesOnFiniteBondSets
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.OneLoopLaw.TorusFamilies
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.OneLoopLaw.FunctionalStiffness
variable {L : ℕ}
section BondGeometry
variable {m : ℕ} {i : ℤ}
private theorem isPositive_or_opposite (b : PeriodicLattice.Bond L m i) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
private theorem mem_of_isBondForm {B : PeriodicLattice.Bond L m i → ComplexMatrix2}
    (hB : PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra B)
    (b : PeriodicLattice.Bond L m i) :
    B b ∈ ComplexMatrix2.hermitianTraceless := by
  rcases isPositive_or_opposite b with h | h
  · exact hB.1 b h
  · have h₁ : B b.opposite ∈ ComplexMatrix2.hermitianTraceless := hB.1 _ h
    rw [hB.2 b] at h₁
    simpa using ComplexMatrix2.hermitianTraceless.neg_mem h₁
private theorem matExp_neg_inv (X : ComplexMatrix2) :
    (ComplexMatrix2.matExp (-X))⁻¹ = ComplexMatrix2.matExp X := by
  change (NormedSpace.exp (-X))⁻¹ = NormedSpace.exp X
  rw [Matrix.exp_neg]
  exact Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))
private theorem expTwist_one {X : PeriodicLattice.Bond L m i → ComplexMatrix2}
    (hX : ∀ b, X b.opposite = -X b) :
    PeriodicLattice.expTwist X (fun _ => 1) = PeriodicLattice.expGaugeField X := by
  funext b
  by_cases h : b.IsPositivelyOriented
  · simp [PeriodicLattice.expTwist, PeriodicLattice.expGaugeField, h]
  · simp only [PeriodicLattice.expTwist, PeriodicLattice.expGaugeField, if_neg h, mul_one, hX b,
      smul_neg]
    exact matExp_neg_inv _
private def translateBond (c : PeriodicLattice.Site L m i) (b : PeriodicLattice.Bond L m i) :
    PeriodicLattice.Bond L m i :=
  ⟨b.source + c, b.target + c, by
    obtain ⟨μ, h⟩ := b.isNeighbour
    exact ⟨μ, by rwa [add_sub_add_right_eq_sub]⟩⟩
private theorem bondPreimage_translateBy (a : PeriodicLattice.Site L m i)
    (b : PeriodicLattice.Bond L m i) :
    PeriodicLattice.bondPreimage (PeriodicLattice.translateBy a) b = translateBond (-a) b := by
  have hex : ∃ b' : PeriodicLattice.Bond L m i,
      (b'.source : PeriodicLattice.FourTorus L m) = (PeriodicLattice.translateBy a).symm b.source ∧
      (b'.target : PeriodicLattice.FourTorus L m) = (PeriodicLattice.translateBy a).symm b.target :=
    ⟨translateBond (-a) b, by simp [translateBond, PeriodicLattice.translateBy],
      by simp [translateBond, PeriodicLattice.translateBy]⟩
  unfold PeriodicLattice.bondPreimage
  rw [dif_pos hex]
  obtain ⟨h₁, h₂⟩ := hex.choose_spec
  refine PeriodicLattice.Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [h₁]; simp [translateBond, PeriodicLattice.translateBy]
  · rw [h₂]; simp [translateBond, PeriodicLattice.translateBy]
end BondGeometry
private theorem vertexPreimage_add {n : ℕ} (c : Tower.Vertex L n 0 0)
    (x : Tower.Vertex L n 0 0) :
    Tower.vertexPreimage (k := 0) (j := 0) (fun y : PeriodicLattice.FourTorus L n => y + c) x =
      x + -c := by
  have hex : ∃ x' : Tower.Vertex L n 0 0,
      ((fun y : PeriodicLattice.FourTorus L n => y + c) (x' : PeriodicLattice.FourTorus L n)) = x :=
    ⟨x + -c, by simp⟩
  have h := Classical.epsilon_spec hex
  refine Subtype.ext ?_
  have h' : ((Tower.vertexPreimage (k := 0) (j := 0)
      (fun y : PeriodicLattice.FourTorus L n => y + c) x : Tower.Vertex L n 0 0) :
        PeriodicLattice.FourTorus L n) + c = x := h
  rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, ← h']
  abel
private theorem edgePreimage_add {n : ℕ} (c : Tower.Vertex L n 0 0)
    (b : Tower.Edge L n 0 0) :
    Tower.edgePreimage (k := 0) (j := 0) (fun y : PeriodicLattice.FourTorus L n => y + c) b =
      translateBond (-c) b := by
  have hex : ∃ b' : Tower.Edge L n 0 0,
      b'.source = Tower.vertexPreimage (k := 0) (j := 0)
        (fun y : PeriodicLattice.FourTorus L n => y + c) b.source ∧
      b'.target = Tower.vertexPreimage (k := 0) (j := 0)
        (fun y : PeriodicLattice.FourTorus L n => y + c) b.target :=
    ⟨translateBond (-c) b, by rw [vertexPreimage_add]; rfl,
      by rw [vertexPreimage_add]; rfl⟩
  obtain ⟨h₁, h₂⟩ := Classical.epsilon_spec hex
  refine PeriodicLattice.Bond.ext ?_ ?_
  · exact h₁.trans (vertexPreimage_add c b.source)
  · exact h₂.trans (vertexPreimage_add c b.target)
section Rescaling
variable {K j : ℕ} (hL : 0 < L) (hj : j ≤ K) (m : ℕ)
private theorem bondRescale_symm_opposite (b : UnitEdge L (m + (K - j))) :
    (bondRescale hL hj m).symm b.opposite = ((bondRescale hL hj m).symm b).opposite :=
  rfl
private theorem bondRescale_opposite (b : PeriodicLattice.BondAtLevel L m K j) :
    bondRescale hL hj m b.opposite = (bondRescale hL hj m b).opposite :=
  rfl
private theorem bondRescale_symm_translateBond (c : Tower.Vertex L (m + (K - j)) 0 0)
    (b : UnitEdge L (m + (K - j))) :
    (bondRescale hL hj m).symm (translateBond c b) =
      translateBond ((siteRescale hL hj m).symm c) ((bondRescale hL hj m).symm b) := by
  refine PeriodicLattice.Bond.ext ?_ ?_
  · exact map_add (siteRescale hL hj m).symm b.source c
  · exact map_add (siteRescale hL hj m).symm b.target c
private theorem transportGaugeField_translateBy_rescaled (a : PeriodicLattice.SiteAtLevel L m K j)
    (W : PeriodicLattice.BondAtLevel L m K j → ComplexMatrix2) :
    PeriodicLattice.transportGaugeField (PeriodicLattice.translateBy a) W ∘
        (bondRescale hL hj m).symm =
      Tower.pushField (k := 0) (j := 0)
        (fun y : PeriodicLattice.FourTorus L (m + (K - j)) =>
          y + (siteRescale hL hj m a : Tower.Vertex L (m + (K - j)) 0 0))
        (W ∘ (bondRescale hL hj m).symm) := by
  funext b
  simp only [Function.comp, PeriodicLattice.transportGaugeField, Tower.pushField]
  rw [bondPreimage_translateBy, edgePreimage_add, bondRescale_symm_translateBond, map_neg,
    AddEquiv.symm_apply_apply]
end Rescaling
section Hessians
variable {K j : ℕ} (hL : 0 < L) (hj : j ≤ K)
private theorem torusPolarization_torusFamily (F : FieldFamily L) (m : ℕ)
    (B B' : PeriodicLattice.BondAtLevel L m K j → ComplexMatrix2) :
    EffectiveAction.torusPolarization (torusFamily hL hj F) m B B' =
      deriv (fun s : ℝ => deriv (fun s' : ℝ => F (m + (K - j))
        (PeriodicLattice.expGaugeField (s • (B ∘ (bondRescale hL hj m).symm) +
          s' • (B' ∘ (bondRescale hL hj m).symm)))) 0) 0 :=
  rfl
private theorem hessianAtIdentity_zero_left (F : FieldFamily L) (n : ℕ)
    (B : UnitEdge L n → ComplexMatrix2) :
    hessianAtIdentity F n 0 B = 0 := by
  simp [hessianAtIdentity, Tower.leftSecondDeriv, Tower.mixedDirectionalDeriv]
private theorem hessianAtIdentity_zero_right (F : FieldFamily L) (n : ℕ)
    (B : UnitEdge L n → ComplexMatrix2) :
    hessianAtIdentity F n B 0 = 0 := by
  simp [hessianAtIdentity, Tower.leftSecondDeriv, Tower.mixedDirectionalDeriv]
private theorem realComponent_of_mem {n : ℕ} {B : UnitEdge L n → ComplexMatrix2}
    (hB : ∀ b, B b ∈ ComplexMatrix2.hermitianTraceless) :
    realComponent B = B := by
  funext b
  have h : (B b).conjTranspose = B b := (hB b).1.symm
  simp only [realComponent, h, ← two_smul ℂ (B b), smul_smul]
  norm_num
private theorem imagComponent_of_mem {n : ℕ} {B : UnitEdge L n → ComplexMatrix2}
    (hB : ∀ b, B b ∈ ComplexMatrix2.hermitianTraceless) : imagComponent B = 0 := by
  funext b
  have h : (B b).conjTranspose = B b := (hB b).1.symm
  simp [imagComponent, h]
private theorem complexHessian_of_mem (F : FieldFamily L) {n : ℕ}
    {B B' : UnitEdge L n → ComplexMatrix2}
    (hB : ∀ b, B b ∈ ComplexMatrix2.hermitianTraceless)
    (hB' : ∀ b, B' b ∈ ComplexMatrix2.hermitianTraceless) :
    complexHessian F n B B' = ((hessianAtIdentity F n B B' : ℝ) : ℂ) := by
  simp [complexHessian, realComponent_of_mem hB, realComponent_of_mem hB',
    imagComponent_of_mem hB, imagComponent_of_mem hB', hessianAtIdentity_zero_left,
    hessianAtIdentity_zero_right]
private theorem torusPolarizationMatches_of (F : FieldFamily L) :
    TorusPolarizationMatches hL hj F := by
  refine Eventually.of_forall fun m B B' hB hB' => ?_
  have hBm : ∀ b, (rescaledForm hL hj m B) b ∈ ComplexMatrix2.hermitianTraceless :=
    fun b => mem_of_isBondForm hB _
  have hBm' : ∀ b, (rescaledForm hL hj m B') b ∈ ComplexMatrix2.hermitianTraceless :=
    fun b => mem_of_isBondForm hB' _
  rw [complexHessian_of_mem F hBm hBm', torusPolarization_torusFamily]
  congr 1
  simp only [hessianAtIdentity, Tower.leftSecondDeriv, Tower.mixedDirectionalDeriv]
  have key : ∀ s s' : ℝ, PeriodicLattice.expGaugeField
      (s • (B ∘ (bondRescale hL hj m).symm) + s' • (B' ∘ (bondRescale hL hj m).symm)) =
      PeriodicLattice.expTwist (algebraMap ℝ ℂ s • rescaledForm hL hj m B +
        algebraMap ℝ ℂ s' • rescaledForm hL hj m B') (identityField L _) := by
    intro s s'
    change _ = PeriodicLattice.expTwist _ (fun _ => 1)
    rw [expTwist_one]
    · congr 1
    · intro b
      simp only [Pi.add_apply, Pi.smul_apply, rescaledForm, Function.comp,
        bondRescale_symm_opposite, hB.2, hB'.2, smul_neg, neg_add]
  simp only [key]
end Hessians
section KernelLimit
variable {K j : ℕ} (hL : 0 < L) (hj : j ≤ K)
private theorem singleBondForm_rescaled (m : ℕ) (x : PeriodicLattice.BondAtLevel L m K j)
    (A : ComplexMatrix2) :
    EffectiveAction.singleBondForm x A ∘ (bondRescale hL hj m).symm =
      EffectiveAction.singleBondForm (bondRescale hL hj m x) A := by
  funext b
  have h₁ : (bondRescale hL hj m).symm b = x ↔ b = bondRescale hL hj m x :=
    Equiv.symm_apply_eq _
  have h₂ : (bondRescale hL hj m).symm b = x.opposite ↔
      b = (bondRescale hL hj m x).opposite := by
    rw [Equiv.symm_apply_eq, bondRescale_opposite]
  simp only [Function.comp, EffectiveAction.singleBondForm]
  classical
  exact if_congr h₁ rfl (if_congr h₂ rfl rfl)
private def kernelSeq (F : FieldFamily L) (x y : EffectiveAction.IntBond) (A A' : ComplexMatrix2)
    (n : ℕ) : ℝ :=
  deriv (fun s : ℝ => deriv (fun s' : ℝ => F n (PeriodicLattice.expGaugeField
    (s • EffectiveAction.singleBondForm (EffectiveAction.projectBond L n 0 0 x) A +
      s' • EffectiveAction.singleBondForm (EffectiveAction.projectBond L n 0 0 y) A'))) 0) 0
private theorem torusPolarization_singleBondForm (F : FieldFamily L) (m : ℕ)
    (x y : EffectiveAction.IntBond) (A A' : ComplexMatrix2) :
    EffectiveAction.torusPolarization (torusFamily hL hj F) m
        (EffectiveAction.singleBondForm (EffectiveAction.projectBond L m K j x) A)
        (EffectiveAction.singleBondForm (EffectiveAction.projectBond L m K j y) A') =
      kernelSeq F x y A A' (m + (K - j)) := by
  rw [torusPolarization_torusFamily, singleBondForm_rescaled, singleBondForm_rescaled,
    bondRescale_projectBond, bondRescale_projectBond]
  rfl
open Classical in
private theorem hasKernelLimit_iff (F : FieldFamily L) (t : Fin 3 → ComplexMatrix2.LieElement)
    (P : Fin 4 → Fin 4 → EffectiveAction.IntPoint → ℝ) :
    EffectiveAction.HasKernelLimit t (torusFamily hL hj F) P ↔
      ∀ (x y : EffectiveAction.IntBond) (a a' : Fin 3),
        Tendsto (kernelSeq F x y (t a).toMatrix (t a').toMatrix) atTop
          (𝓝 (if a = a' then P x.2 y.2 (y.1 - x.1) else 0)) := by
  unfold EffectiveAction.HasKernelLimit
  refine forall_congr' fun x => forall_congr' fun y => forall_congr' fun a =>
    forall_congr' fun a' => ?_
  simp only [torusPolarization_singleBondForm]
  exact tendsto_add_atTop_iff_nat (f := kernelSeq F x y (t a).toMatrix (t a').toMatrix) (K - j)
end KernelLimit
private theorem kernelStiffnessIndependent_of {K j K' j' : ℕ} (hL : 0 < L) (hj : j ≤ K)
    (hj' : j' ≤ K') (F : FieldFamily L) (t : Fin 3 → ComplexMatrix2.LieElement) :
    KernelStiffnessIndependent hL hj hj' F t := by
  have hk : ∀ P, EffectiveAction.HasKernelLimit t (torusFamily hL hj F) P ↔
      EffectiveAction.HasKernelLimit t (torusFamily hL hj' F) P := fun P => by
    rw [hasKernelLimit_iff, hasKernelLimit_iff]
  refine ⟨hk, fun c => ?_⟩
  simp only [EffectiveAction.IsTorusStiffnessWith, hk]
section ExpChart
variable {n : ℕ}
private theorem matExp_I_smul_mem (hc : PowerExpCharts.ExpChartsStatement) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup := by
  obtain ⟨hch, -⟩ := hc Unit Unit
  have h₁ : (fun _ : Unit => (1 : ComplexMatrix2)) ∈ specialUnitaryPower Unit :=
    fun _ => (1 : ComplexMatrix2.specialUnitary).2
  obtain ⟨-, h₂, -⟩ := hch _ h₁
  obtain ⟨-, h₃, h₄⟩ := h₂ (fun _ => (⟨X, hX⟩ : ComplexMatrix2.hermitianTraceless))
  rw [h₃] at h₄
  have h₅ : ComplexMatrix2.matExp (Complex.I • X) * 1 ∈ PeriodicLattice.compactGaugeGroup := h₄ ()
  simpa using h₅
variable {d : ℕ} {T : (Fin d → ℝ) →ₗ[ℝ] (UnitEdge L n → ComplexMatrix2)}
private theorem continuous_I_smul_apply (b : UnitEdge L n) :
    Continuous fun v : Fin d → ℝ => Complex.I • T v b := by
  have h : Continuous fun v : Fin d → ℝ => T v b :=
    ((LinearMap.proj b : (UnitEdge L n → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2).comp
      T).continuous_of_finiteDimensional
  exact h.const_smul Complex.I
private theorem tendsto_expGaugeField_one (hc : PowerExpCharts.ExpChartsStatement)
    (hmem : ∀ v b, T v b ∈ ComplexMatrix2.hermitianTraceless)
    (hrev : ∀ v (b : UnitEdge L n), T v b.opposite = -T v b) :
    Tendsto (fun v => PeriodicLattice.expGaugeField (T v)) (𝓝 0)
      (𝓝[Tower.fieldSpace L n 0 0] fun _ => (1 : ComplexMatrix2)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun v => ?_⟩
  · refine tendsto_pi_nhds.2 fun b => ?_
    have he : Continuous (ComplexMatrix2.matExp : ComplexMatrix2 → ComplexMatrix2) := by
      let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
      exact NormedSpace.exp_continuous
    have h : Continuous fun v : Fin d → ℝ => PeriodicLattice.expGaugeField (T v) b :=
      he.comp (continuous_I_smul_apply b)
    simpa [PeriodicLattice.expGaugeField] using h.tendsto (0 : Fin d → ℝ)
  · refine ⟨fun b _ => matExp_I_smul_mem hc (hmem v b), fun b _ => ?_⟩
    simp only [PeriodicLattice.expGaugeField, hrev, smul_neg]
    exact Matrix.exp_neg _
private theorem twiceDiff_of_admissible (hc : PowerExpCharts.ExpChartsStatement)
    {f : (UnitEdge L n → ComplexMatrix2) → ℝ} (hf : IsAdmissibleMember f)
    (hmem : ∀ v b, T v b ∈ ComplexMatrix2.hermitianTraceless)
    (hrev : ∀ v (b : UnitEdge L n), T v b.opposite = -T v b) :
    EffectiveAction.TwiceDiffNearOrigin
      fun v => f (PeriodicLattice.expGaugeField (T v)) := by
  obtain ⟨inst, O, hO, h1, hres⟩ := hf.analytic
  let _inst := inst
  have hne : Nonempty (PositiveUnitEdge L n) :=
    ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, 0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩
  obtain ⟨hch, -, -, -, -, -, -, hb⟩ :=
    hc (PositiveUnitEdge L n) (PositiveUnitEdge L n)
  have hp : (fun _ : PositiveUnitEdge L n => (1 : ComplexMatrix2)) ∈
      specialUnitaryPower (PositiveUnitEdge L n) :=
    fun _ => (1 : ComplexMatrix2.specialUnitary).2
  have hread := ((hb OneLoop.pauliBasis).1 O hO).1 _ (hres OneLoop.pauliBasis)
  obtain ⟨N, hN, -, hC, -⟩ := hread.1.1 _ h1
  obtain ⟨-, hform, -⟩ := hch _ hp
  let Y : (Fin d → ℝ) →ₗ[ℝ] (PositiveUnitEdge L n → ComplexMatrix2.LieElement) :=
    { toFun := fun v s => (⟨T v s.1, hmem v s.1⟩ : ComplexMatrix2.hermitianTraceless)
      map_add' := fun v w => by
        funext s
        refine Subtype.ext (p := (· ∈ ComplexMatrix2.hermitianTraceless)) ?_
        change T (v + w) s.1 = T v s.1 + T w s.1
        rw [map_add]
        rfl
      map_smul' := fun c v => by
        funext s
        refine Subtype.ext (p := (· ∈ ComplexMatrix2.hermitianTraceless)) ?_
        change T (c • v) s.1 = c • T v s.1
        rw [map_smul]
        rfl }
  have hval : ∀ v, PeriodicLattice.expGaugeField (T v) =
      Tower.fieldOfPositiveValues (k := 0) (j := 0)
        (PowerExpCharts.expChartI (fun _ => 1) (Y v)) := by
    intro v
    rw [(hform (Y v)).2.1]
    funext b
    by_cases h : b.IsPositivelyOriented
    · have h₁ : (Y v ⟨b, h⟩).toMatrix = T v b := rfl
      simp [Tower.fieldOfPositiveValues, PeriodicLattice.expGaugeField, h, h₁]
    · have h' : b.opposite.IsPositivelyOriented := (isPositive_or_opposite b).resolve_left h
      have h₁ : (Y v ⟨b.opposite, h'⟩).toMatrix = -T v b := hrev v b
      simp only [Tower.fieldOfPositiveValues, PeriodicLattice.expGaugeField, dif_neg h,
        dif_pos h', h₁, mul_one, smul_neg]
      exact (matExp_neg_inv _).symm
  have hg : (fun v => f (PeriodicLattice.expGaugeField (T v))) =
      ((fun w => f (Tower.fieldOfPositiveValues (k := 0) (j := 0) w)) ∘
        PowerExpCharts.expChartI fun _ => 1) ∘ Y := by
    funext v
    simp only [Function.comp, hval v]
  have hYc : Continuous Y := Y.continuous_of_finiteDimensional
  have hev : ∀ᶠ v in 𝓝 (0 : Fin d → ℝ), N ∈ 𝓝 (Y v) := by
    have h₀ : ∀ᶠ y in 𝓝 (Y 0), N ∈ 𝓝 y := by
      rw [map_zero]
      exact eventually_mem_nhds_iff.2 hN
    exact hYc.continuousAt.eventually h₀
  filter_upwards [hev] with v hv
  have hcd : ContDiffAt ℝ ∞ (fun v => f (PeriodicLattice.expGaugeField (T v))) v := by
    rw [hg]
    exact (hC.contDiffAt hv).comp v (LinearMap.toContinuousLinearMap Y).contDiff.contDiffAt
  exact ⟨hcd.differentiableAt (by simp),
    (hcd.fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiableAt
      one_ne_zero⟩
end ExpChart
private theorem eventually_isAdmissibleMember (hL : 0 < L) {F : FieldFamily L}
    (hF : IsLatticeFunctional L F) :
    ∃ m₀ : ℕ, ∀ n, m₀ ≤ n → 0 < n → IsAdmissibleMember (F n) := by
  obtain ⟨s₀, ⟨m₀, -, rfl⟩, h⟩ := hF
  refine ⟨m₀, fun n hn hn₀ => h _ ⟨n, hn₀, rfl⟩ ?_ n hn₀ rfl⟩
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  simpa [PeriodicLattice.torusSide] using pow_le_pow_right₀ hL' hn
private theorem isTorusFunctional_torusFamily (hc : PowerExpCharts.ExpChartsStatement) {K j : ℕ}
    (hL : 0 < L) (hj : j ≤ K) {F : FieldFamily L} (hF : IsLatticeFunctional L F) :
    EffectiveAction.IsTorusFunctional L K j (torusFamily hL hj F) := by
  obtain ⟨m₀, h⟩ := eventually_isAdmissibleMember hL hF
  filter_upwards [eventually_ge_atTop (m₀ + 1)] with m hm
  have hf : IsAdmissibleMember (F (m + (K - j))) := h _ (by omega) (by omega)
  refine ⟨hf.map_identity, fun d T hT => ?_⟩
  let T' : (Fin d → ℝ) →ₗ[ℝ] (UnitEdge L (m + (K - j)) → ComplexMatrix2) :=
    (LinearMap.funLeft ℝ ComplexMatrix2 (bondRescale hL hj m).symm).comp T
  have hmem : ∀ v b, T' v b ∈ ComplexMatrix2.hermitianTraceless :=
    fun v b => mem_of_isBondForm (hT v) _
  have hrev : ∀ v (b : UnitEdge L (m + (K - j))), T' v b.opposite = -T' v b :=
    fun v b => (hT v).2 ((bondRescale hL hj m).symm b)
  refine ⟨twiceDiff_of_admissible hc hf hmem hrev, fun a => ?_⟩
  have hev := (tendsto_expGaugeField_one hc hmem hrev).eventually hf.symmetry
  filter_upwards [hev] with v hv
  have hiso : Tower.IsDistancePreserving (fun y : PeriodicLattice.FourTorus L (m + (K - j)) =>
      y + (siteRescale hL hj m a : Tower.Vertex L (m + (K - j)) 0 0)) := fun x y =>
    congrArg TorusMetric.torusEuclidNorm (add_sub_add_right_eq_sub x y _)
  have hlat : Tower.MapsSublatticeOnto 0 0 (fun y : PeriodicLattice.FourTorus L (m + (K - j)) =>
      y + (siteRescale hL hj m a : Tower.Vertex L (m + (K - j)) 0 0)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact add_mem hx (siteRescale hL hj m a).2
    · intro hy
      exact ⟨y - (siteRescale hL hj m a : Tower.Vertex L (m + (K - j)) 0 0),
        sub_mem hy (siteRescale hL hj m a).2, sub_add_cancel _ _⟩
  have h₁ := hv _ hiso hlat
  change F (m + (K - j)) (PeriodicLattice.transportGaugeField (PeriodicLattice.translateBy a)
      (PeriodicLattice.expGaugeField (T v)) ∘ (bondRescale hL hj m).symm) =
    F (m + (K - j)) (PeriodicLattice.expGaugeField (T' v))
  rw [transportGaugeField_translateBy_rescaled]
  exact h₁
theorem torusFamilyProperties_holds (hc : PowerExpCharts.ExpChartsStatement) :
    TorusFamilyProperties := by
  intro L _ hL F hF
  refine ⟨fun K j _ hj => ⟨fun m hm => ⟨?_, ⟨_, by omega, rfl⟩, siteRescale_projectSite hL hj m⟩,
    isTorusFunctional_torusFamily hc hL hj hF, torusPolarizationMatches_of hL hj F⟩,
    fun K j K' j' _ _ hj hj' t _ => kernelStiffnessIndependent_of hL hj hj' F t⟩
  simp [PeriodicLattice.torusSide, pow_add, mul_assoc]
end YangMills.Construction.OneLoopLaw.TorusFamilies
end
