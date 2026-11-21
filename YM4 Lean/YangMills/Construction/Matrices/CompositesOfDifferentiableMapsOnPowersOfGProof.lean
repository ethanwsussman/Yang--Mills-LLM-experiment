import YangMills.Construction.Matrices.ExponentialChartsOfPowersOfG
import YangMills.Construction.Matrices.SpecialUnitaryPowerComposition
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices.PowerExpCharts
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Matrices
namespace specialUnitaryPower
namespace Composition
variable {α β : Type}
def lieElementMatrixMap : ComplexMatrix2.LieElement →ₗ[ℝ] ComplexMatrix2 where
  toFun := ComplexMatrix2.LieElement.toMatrix
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem ker_lieElementMatrixMap : LinearMap.ker lieElementMatrixMap = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun X hX => ?_
  exact Subtype.ext (p := (· ∈ ComplexMatrix2.hermitianTraceless)) hX
theorem exists_clm_leftInverse_toMatrix :
    ∃ l : ComplexMatrix2 →L[ℝ] ComplexMatrix2.LieElement,
      ∀ X : ComplexMatrix2.LieElement, l X.toMatrix = X := by
  obtain ⟨l, hl⟩ := lieElementMatrixMap.exists_leftInverse_of_injective ker_lieElementMatrixMap
  refine ⟨⟨l, LinearMap.continuous_of_finiteDimensional l⟩, fun X => ?_⟩
  exact LinearMap.congr_fun hl X
theorem exp_half_le_nineteen_tenths : Real.exp (1 / 2) ≤ 19 / 10 := by
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have hone := Real.exp_one_lt_d9
  have hpos := Real.exp_pos (1 / 2 : ℝ)
  nlinarith
theorem expChartI_zero [Fintype α] (hC : PowerCharts α) {x : α → ComplexMatrix2}
    (hx : x ∈ specialUnitaryPower α) : expChartI x 0 = x := by
  rw [(hC x hx).2.1 0 |>.2.1]
  funext i
  have hz : ((0 : α → ComplexMatrix2.LieElement) i).toMatrix = 0 := rfl
  rw [hz, smul_zero]
  simp only [ComplexMatrix2.matExp, NormedSpace.exp_zero, one_mul]
theorem exists_local_inverse_expChartI [Fintype β] (hC : PowerCharts β) {y : β → ComplexMatrix2}
    (hy : y ∈ specialUnitaryPower β) :
    ∃ (Ψ : (β → ComplexMatrix2) → β → ComplexMatrix2.LieElement) (U : Set (β → ComplexMatrix2)),
      IsOpen U ∧ y ∈ U ∧
      (∀ z ∈ U, DifferentiableAt ℝ Ψ z) ∧ Ψ y = 0 ∧
      ∀ z ∈ U, z ∈ specialUnitaryPower β → expChartI y (Ψ z) = z := by
  obtain ⟨-, -, hsmall⟩ := hC y hy
  obtain ⟨-, ⟨U₀, hU₀, himg⟩, hyU, -, hlogOpen, hlogDiff, hsub, hleft, -⟩ :=
    hsmall (1 / 2) (by norm_num) exp_half_le_nineteen_tenths
  obtain ⟨l, hl⟩ := exists_clm_leftInverse_toMatrix
  have hround : ∀ X ∈ smallBall β (1 / 2),
      (fun i => l (logChart y (expChartI y X) i)) = X := by
    intro X hX
    rw [hleft X hX]
    funext i
    exact hl (X i)
  have hzero : (0 : β → ComplexMatrix2.LieElement) ∈ smallBall β (1 / 2) := by
    intro i
    have hz : ((0 : β → ComplexMatrix2.LieElement) i).toMatrix = 0 := rfl
    rw [hz]
    simp [ComplexMatrix2.operatorNorm]
  refine ⟨fun z i => l (logChart y z i), U₀ ∩ logDomain y, hU₀.inter hlogOpen, ?_, ?_, ?_, ?_⟩
  · have hyG : y ∈ U₀ ∩ specialUnitaryPower β := himg ▸ hyU
    exact ⟨hyG.1, hsub hyU⟩
  · intro z hz
    have hdl : DifferentiableAt ℝ (logChart y) z :=
      (hlogDiff.differentiableOn (by simp)).differentiableAt (hlogOpen.mem_nhds hz.2)
    exact differentiableAt_pi.2 fun i =>
      l.differentiableAt.comp z (differentiableAt_pi.1 hdl i)
  · have h := hround 0 hzero
    rwa [expChartI_zero hC hy] at h
  · intro z hz hzG
    have hzimg : z ∈ expChartI y '' smallBall β (1 / 2) := himg ▸ ⟨hz.1, hzG⟩
    obtain ⟨X, hX, rfl⟩ := hzimg
    show expChartI y (fun i => l (logChart y (expChartI y X) i)) = expChartI y X
    rw [hround X hX]
theorem continuousOn_of_differentiableOnOpen [Fintype α] {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hC : PowerCharts α) (hR : ReadInCharts α E)
    {U : Set (α → ComplexMatrix2)} {φ : (α → ComplexMatrix2) → E}
    (hφ : EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower α) U φ) :
    ContinuousOn φ U := by
  have hUsub : U ⊆ specialUnitaryPower α := by
    obtain ⟨B, -, hB⟩ := hφ.1
    exact hB ▸ inter_subset_right
  intro x hx
  obtain ⟨M, hM, -, hdiff⟩ := (hR U φ hφ.1).2.1.1 hφ x hx
  obtain ⟨Ψ, W, hW, hxW, hΨ, hΨ0, hΨinv⟩ := exists_local_inverse_expChartI hC (hUsub hx)
  have hcont0 : ContinuousAt (φ ∘ expChartI x) (Ψ x) := by
    rw [hΨ0]
    exact (hdiff.differentiableAt hM).continuousAt
  have hcont : ContinuousAt (fun z => (φ ∘ expChartI x) (Ψ z)) x :=
    ContinuousAt.comp (g := φ ∘ expChartI x) (f := Ψ) hcont0 (hΨ x hxW).continuousAt
  have hev : (fun z => (φ ∘ expChartI x) (Ψ z)) =ᶠ[𝓝[U] x] φ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hxW), self_mem_nhdsWithin] with z hz hzU
    simp only [Function.comp]
    rw [hΨinv z hz (hUsub hzU)]
  have hval : (φ ∘ expChartI x) (Ψ x) = φ x := by
    simp only [Function.comp]
    rw [hΨinv x hxW (hUsub hx)]
  exact (hcont.continuousWithinAt.congr_of_eventuallyEq hev.symm hval.symm)
theorem coordinateSelectionsDifferentiable [Fintype α] [Fintype β] :
    CoordinateSelectionsDifferentiable α β := by
  intro j
  refine ⟨⟨⟨univ, isOpen_univ, (univ_inter _).symm⟩, fun c => ?_⟩, fun z hz i => hz (j i)⟩
  have hsel : Differentiable ℝ fun z : α → ComplexMatrix2 => fun i => z (j i) :=
    differentiable_pi.2 fun i => differentiable_apply (j i)
  exact hsel.comp_differentiableOn
    ((c.contDiffOn_param.differentiableOn (by simp)).mono inter_subset_left)
theorem compDifferentiable [Fintype α] [Fintype β] {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hCα : PowerCharts α) (hCβ : PowerCharts β) (hRα : ReadInCharts α E)
    (hRβ : ReadInCharts β E) (hRM : ReadInCharts α ComplexMatrix2)
    (hcomp : PowerMapsReadComponentwise α β) : CompDifferentiable α β E := by
  intro U ψ U₂ φ hψ hφ
  have hU := hψ.1.1
  have hUsub : U ⊆ specialUnitaryPower α := by
    obtain ⟨B, -, hB⟩ := hU
    exact hB ▸ inter_subset_right
  have hcomps := (hcomp U ψ hU hψ.2).1 hψ
  have hψc : ContinuousOn ψ U := continuousOn_pi.2 fun i =>
    continuousOn_of_differentiableOnOpen hCα hRM (hcomps i)
  have hPre : IsOpenSubset (U ∩ ψ ⁻¹' U₂) := by
    obtain ⟨B, hB, rfl⟩ := hU
    obtain ⟨B₂, hB₂, rfl⟩ := hφ.1
    obtain ⟨u, hu, huB⟩ := continuousOn_iff'.1 hψc B₂ hB₂
    refine ⟨u ∩ B, hu.inter hB, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hz2⟩
      have hz' : z ∈ ψ ⁻¹' B₂ ∩ (B ∩ specialUnitaryPower α) := ⟨hz2.1, hz⟩
      rw [huB] at hz'
      exact ⟨⟨hz'.1, hz.1⟩, hz.2⟩
    · rintro ⟨⟨hzu, hzB⟩, hzG⟩
      have hz' : z ∈ u ∩ (B ∩ specialUnitaryPower α) := ⟨hzu, hzB, hzG⟩
      rw [← huB] at hz'
      exact ⟨⟨hzB, hzG⟩, hz'.1, hψ.2 ⟨hzB, hzG⟩⟩
  refine ⟨hψc, hPre, ((hRα _ _ hPre).2.1).2 fun x hx => ?_⟩
  obtain ⟨M₀, hM₀, hmaps⟩ := (hRα _ (φ ∘ ψ) hPre).1 x hx
  have hxG := hUsub hx.1
  have hyG : ψ x ∈ specialUnitaryPower β := hψ.2 hx.1
  have hcompAll := fun i => (hRM U (fun p => ψ p i) hU).2.1.1 (hcomps i) x hx.1
  choose Mi hMi _ hdi using hcompAll
  have hM₁ : (⋂ i, Mi i) ∈ 𝓝 (0 : α → ComplexMatrix2.LieElement) := iInter_mem.2 hMi
  obtain ⟨M₂, hM₂, -, hd₂⟩ := (hRβ U₂ φ hφ.1).2.1.1 hφ (ψ x) hx.2
  obtain ⟨Ψ, W, hW, hyW, hΨ, hΨ0, hΨinv⟩ := exists_local_inverse_expChartI hCβ hyG
  set Γ : (α → ComplexMatrix2.LieElement) → β → ComplexMatrix2 := fun X => ψ (expChartI x X)
    with hΓ
  have hΓd : ∀ X ∈ interior (⋂ i, Mi i), DifferentiableAt ℝ Γ X := by
    intro X hX
    refine differentiableAt_pi.2 fun i => ?_
    have hnb : Mi i ∈ 𝓝 X :=
      mem_of_superset (mem_interior_iff_mem_nhds.1 hX) (iInter_subset _ i)
    exact (hdi i).differentiableAt hnb
  have hΓ0 : Γ 0 = ψ x := by
    simp only [hΓ]
    rw [expChartI_zero hCα hxG]
  have hzeroInt : (0 : α → ComplexMatrix2.LieElement) ∈ interior (⋂ i, Mi i) :=
    mem_interior_iff_mem_nhds.2 hM₁
  have hΓc : ContinuousAt Γ 0 := (hΓd 0 hzeroInt).continuousAt
  have hevW : ∀ᶠ X in 𝓝 (0 : α → ComplexMatrix2.LieElement), Γ X ∈ W :=
    hΓc.eventually_mem (by rw [hΓ0]; exact hW.mem_nhds hyW)
  have hΨc : ContinuousAt (fun X => Ψ (Γ X)) 0 :=
    ContinuousAt.comp (by rw [hΓ0]; exact (hΨ _ hyW).continuousAt) hΓc
  have hevM : ∀ᶠ X in 𝓝 (0 : α → ComplexMatrix2.LieElement), Ψ (Γ X) ∈ interior M₂ :=
    hΨc.eventually_mem (by rw [hΓ0, hΨ0]; exact interior_mem_nhds.2 hM₂)
  have hset : {X | X ∈ M₀ ∧ X ∈ interior (⋂ i, Mi i) ∧ Γ X ∈ W ∧ Ψ (Γ X) ∈ interior M₂} ∈
      𝓝 (0 : α → ComplexMatrix2.LieElement) := by
    filter_upwards [hM₀, interior_mem_nhds.2 hM₁, hevW, hevM] with X a b c d using ⟨a, b, c, d⟩
  refine ⟨interior _, interior_mem_nhds.2 hset, fun X hX => hmaps (interior_subset hX).1, ?_⟩
  intro X hX
  have hXS := interior_subset hX
  have hev : (fun X' => (φ ∘ expChartI (ψ x)) (Ψ (Γ X'))) =ᶠ[𝓝 X] ((φ ∘ ψ) ∘ expChartI x) := by
    filter_upwards [isOpen_interior.mem_nhds hX] with X' hX'
    have hS' := interior_subset hX'
    simp only [Function.comp]
    rw [hΨinv _ hS'.2.2.1 (hψ.2 (hmaps hS'.1).1)]
  have hdiff : DifferentiableAt ℝ (fun X' => (φ ∘ expChartI (ψ x)) (Ψ (Γ X'))) X :=
    DifferentiableAt.comp (g := φ ∘ expChartI (ψ x)) (f := fun X' => Ψ (Γ X')) X
      (hd₂.differentiableAt (mem_of_superset (isOpen_interior.mem_nhds hXS.2.2.2) interior_subset))
      ((hΨ _ hXS.2.2.1).comp X (hΓd X hXS.2.1))
  exact (hev.differentiableAt_iff.1 hdiff).differentiableWithinAt
theorem compositionProperties (hE : ExpChartsStatement) : CompositionProperties := by
  intro α β _ _ _ _
  obtain ⟨hCα, hRr, hRc, hRM, -, -, hcomp, -⟩ := hE α β
  obtain ⟨hCβ, -, hβc, hβM, -⟩ := hE β α
  exact ⟨fun U φ hφ => continuousOn_of_differentiableOnOpen hCα hRc hφ,
    fun U φ hφ => continuousOn_of_differentiableOnOpen hCα hRM hφ,
    coordinateSelectionsDifferentiable,
    compDifferentiable hCα hCβ hRc hβc hRM hcomp, compDifferentiable hCα hCβ hRM hβM hRM hcomp⟩
end Composition
end specialUnitaryPower
end Matrices
end YangMills.Construction
end
