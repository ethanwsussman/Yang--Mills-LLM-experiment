import YangMills.Construction.Calculus.CriticalBranchHessian
import YangMills.Construction.Matrices.ExponentialChartsOfPowersOfGProof
import YangMills.Construction.Towers.CoordinatesOfTwoSubmersions
import YangMills.Construction.Towers.HessianOfARestriction
import YangMills.Construction.Towers.NumberOfAConstraintInTwoStages
import YangMills.Construction.Towers.SmoothMapsNearAPointOfASubmanifold
import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import YangMills.Construction.Towers.TwoStagesOfAConstraintDefs
import Mathlib
set_option autoImplicit false

section
open Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction
namespace Geometry.CurveData
variable {X T : Type*} [AddCommGroup T] [Module ℝ T] (R : Geometry.CurveData X T)
def restrictedHessian (N : Set X) (F : X → ℝ) (x : X) : QuadraticForm ℝ (R.tangentSpan N x) :=
  R.hessianForm (S := R.tangentSpan N x) Subtype.val N F x
def IsCriticalPosDefOn (N : Set X) (F : X → ℝ) (x : X) : Prop :=
  R.IsCriticalOn N F x ∧ (R.restrictedHessian N F x).PosDef
end Geometry.CurveData
namespace TwoStageConstraint
open Matrices.EmbeddedSubmanifold
open Manifolds
def GaussianProduct : Prop :=
  ∀ (E V W : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (A : E →ₗ[ℝ] V) (B : V →ₗ[ℝ] W) (Q : QuadraticForm ℝ (LinearMap.ker (B ∘ₗ A))),
    Function.Surjective A → Function.Surjective B → Q.PosDef →
    ∃ Q₂ : QuadraticForm ℝ (LinearMap.ker B), Q₂.PosDef ∧
      ConstraintStages.IsFiberwiseMinimum A B Q Q₂ ∧
      GaussianConstraint.constrainedGaussianNumber (B ∘ₗ A) Q =
        GaussianConstraint.constrainedGaussianNumber A (ConstraintStages.restrictToInnerKernel A B Q) *
          GaussianConstraint.constrainedGaussianNumber B Q₂
def HessianRelations : Prop :=
  ∀ (E₁ E₂ E₃ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    (𝒳 : Set E₁) (𝒴 : Set E₂) (𝒵 : Set E₃) (m : E₁ → E₂) (n : E₂ → E₃) (F : E₁ → ℝ) (g : E₂ → ℝ)
    (𝒰 : Set E₂) (s : E₂ → E₁) (y₀ : E₂),
    IsChartedSubset 𝒳 → IsChartedSubset 𝒴 → IsChartedSubset 𝒵 →
    IsSmoothSubmersion 𝒳 𝒴 m → IsSmoothSubmersion 𝒴 𝒵 n →
    IsSmoothOnOpen 𝒳 𝒳 F → IsSmoothOnOpen 𝒴 𝒴 g →
    y₀ ∈ 𝒰 → IsSmoothOnOpen 𝒴 𝒰 s → MapsTo s 𝒰 𝒳 → (∀ y ∈ 𝒰, m (s y) = y) →
    (∀ y ∈ 𝒰, (vectorCurveData E₁).IsCriticalPosDefOn (fiber 𝒳 m y) F (s y)) →
    (vectorCurveData E₂).IsCriticalPosDefOn (fiber 𝒴 n (n y₀) ∩ 𝒰)
      (fun y => F (s y) + g y) y₀ →
    let x₀ := s y₀
    let P := fiber 𝒳 (n ∘ m) (n y₀)
    let Q := fiber 𝒴 n (n y₀) ∩ 𝒰
    let H := (vectorCurveData E₁).restrictedHessian P (fun p => F p + g (m p)) x₀
    let H₁ := (vectorCurveData E₁).restrictedHessian (fiber 𝒳 m y₀) F x₀
    let H₂ := (vectorCurveData E₂).restrictedHessian Q (fun y => F (s y) + g y) y₀
    (vectorCurveData E₁).IsCriticalOn P (fun p => F p + g (m p)) x₀ ∧ H.PosDef ∧
      (∃ h : (vectorCurveData E₁).tangentSpan (fiber 𝒳 m y₀) x₀ ≤ (vectorCurveData E₁).tangentSpan P x₀,
        H.comp (Submodule.inclusion h) = H₁) ∧
      ∀ ζ : (vectorCurveData E₂).tangentSpan Q y₀,
        IsLeast {t | ∃ (ξ : (vectorCurveData E₁).tangentSpan P x₀) (ξ' : tangentSpace 𝒳 x₀),
          (ξ' : E₁) = ξ ∧ tangentDifferential 𝒳 m x₀ ξ' = (ζ : E₂) ∧ H ξ = t} (H₂ ζ)
def Claim : Prop :=
  GaussianProduct ∧ HessianRelations
end TwoStageConstraint
end YangMills.Construction
end
end

open Set Filter
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction
open Matrices.EmbeddedSubmanifold Manifolds
namespace TwoStageConstraint
section
variable {X T : Type} [AddCommGroup T] [Module ℝ T] (R : Geometry.CurveData X T)
theorem hessianData_at {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {N : Set X} {F : X → ℝ} {φ : P → X} {z : P} {D : P →ₗ[ℝ] T} {p : X}
    (h : R.HessianViaParametrization N F φ z D) (hp : φ z = p) :
    LinearMap.range D = R.tangentSpan N p ∧
    (R.IsCriticalOn N F p ↔ fderiv ℝ (F ∘ φ) z = 0) ∧
    (R.IsCriticalOn N F p → ∀ (a : P) (v : R.tangentSpan N p), (v : T) = D a →
      R.restrictedHessian N F p v = fderiv ℝ (fderiv ℝ (F ∘ φ)) z a a) ∧
    (R.IsCriticalOn N F p → ((R.restrictedHessian N F p).PosDef ↔
      ∀ a : P, a ≠ 0 → 0 < fderiv ℝ (fderiv ℝ (F ∘ φ)) z a a)) := by
  subst hp
  exact ⟨h.range_eq, h.isCriticalOn_iff, h.hessianForm_apply, h.posDef_hessianForm_iff⟩
end
section
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']
theorem param_mem_of_mem_source {M : Set E} (c : Chart M) {u : Fin c.dim → ℝ}
    (hu : u ∈ c.source) : c.param u ∈ M := by apply _root_.YangMills.Construction.Matrices.LocalParametrization.param_mem <;> assumption
theorem isC2OnCharted_of_isSmoothOnOpen {M : Set E} {f : E → ℝ} (h : IsSmoothOnOpen M M f) :
    IsC2OnCharted M f := by
  intro c
  have := h.2 c
  have hsub : c.source ⊆ c.coords M := fun u hu => ⟨hu, param_mem_of_mem_source c hu⟩
  exact (this.mono hsub).of_le (WithTop.coe_le_coe.2 le_top)
end
theorem fderiv_eventuallyEq_of_eventuallyEq_add_const {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {f₁ f₂ : P → ℝ} {z : P} (c : ℝ) (h : f₁ =ᶠ[𝓝 z] fun u => f₂ u + c) :
    fderiv ℝ f₁ =ᶠ[𝓝 z] fderiv ℝ f₂ := by
  filter_upwards [h.eventuallyEq_nhds] with u hu
  rw [hu.fderiv_eq]
  exact fderiv_add_const c
theorem hessianRelations_holds (hY : Tower.RestrictionHessian.Statement)
    (hL : Manifolds.LocalSmoothCalculus)
    (hC : Manifolds.CoordinatesOfTwoSubmersions)
    (hS : Calculus.CriticalBranchHessian) : HessianRelations := by
  intro E₁ E₂ E₃ _ _ _ _ _ _ 𝒳 𝒴 𝒵 m n F g 𝒰 x y₀ h𝒳 h𝒴 h𝒵 hm hn hF hg hy₀ hx hxmaps hmx hcrit
    hcrit₂ x₀ P Q T T₁ T₂
  obtain ⟨hY1, -⟩ := hY
  obtain ⟨hRetr, hComp, hTan, hDiff, hOpen, hChart, hRestr⟩ := hL
  obtain ⟨hFib, hSub, hCoord⟩ := hC
  have hy₀Q : y₀ ∈ fiber 𝒴 n (n y₀) ∩ 𝒰 := hcrit₂.1.1
  have hy₀𝒴 : y₀ ∈ 𝒴 := hy₀Q.1.1
  have hx₀ : x₀ ∈ 𝒳 := hxmaps hy₀
  have hmx₀ : m x₀ = y₀ := hmx y₀ hy₀
  obtain ⟨a, b, c, Ow, Ov, Ou, w₀, v₀, u₀, ε, η, ξ, hw₀, hv₀, hu₀, hξ₀, oOw, oOv, oOu, pε, pη, pξ,
    nη, mξ, fη, fξ, fξ'⟩ := hCoord E₁ E₂ E₃ 𝒳 𝒴 𝒵 m n x₀ h𝒳 h𝒴 h𝒵 hm hn hx₀
  have hη₀ : η (w₀, v₀) = y₀ := by rw [← mξ w₀ hw₀ v₀ hv₀ u₀ hu₀, hξ₀]; exact hmx₀
  have hε₀ : ε w₀ = n y₀ := by rw [← nη w₀ hw₀ v₀ hv₀, hη₀]
  set ψ : (Fin b → ℝ) → E₂ := fun v => η (w₀, v) with hψdef
  set Ψ : (Fin b → ℝ) × (Fin c → ℝ) → E₁ := fun p => ξ (w₀, p) with hΨdef
  set G : E₁ → ℝ := fun p => F p + g (m p) with hGdef
  set f : E₂ → ℝ := fun y => F (x y) + g y with hfdef
  have pψ : IsSmoothParametrization (fiber 𝒴 n (n y₀)) Ov ψ := hε₀ ▸ fη w₀ hw₀
  have pΨ : IsSmoothParametrization (fiber 𝒳 (n ∘ m) (n y₀)) (Ov ×ˢ Ou) Ψ := hε₀ ▸ fξ w₀ hw₀
  have hψ₀ : ψ v₀ = y₀ := hη₀
  have hΨ₀ : Ψ (v₀, u₀) = x₀ := hξ₀
  have oFib : IsChartedSubset (fiber 𝒴 n (n y₀)) := hFib E₂ E₃ 𝒴 𝒵 n _ h𝒴 h𝒵 hn
  have h𝒰open : Matrices.ComplexMatrix2.IsRelativelyOpen 𝒴 𝒰 := hx.1
  have h𝒰 : IsChartedSubset 𝒰 := hOpen E₂ 𝒴 𝒰 h𝒴 h𝒰open
  have h𝒰sub : 𝒰 ⊆ 𝒴 := by
    obtain ⟨O, -, hO⟩ := h𝒰open
    rw [hO]; exact inter_subset_right
  have hQopen : Matrices.ComplexMatrix2.IsRelativelyOpen (fiber 𝒴 n (n y₀)) Q := by
    obtain ⟨O, oO, hO⟩ := h𝒰open
    refine ⟨O, oO, ?_⟩
    ext p
    simp only [Q, hO, mem_inter_iff, fiber, mem_ofPred_eq]
    tauto
  have hQ : IsChartedSubset Q := hOpen E₂ _ Q oFib hQopen
  have pψQ : IsSmoothParametrization Q (Ov ∩ ψ ⁻¹' Q) ψ :=
    hRestr E₂ _ _ _ _ _ pψ hQopen
  have hψmem : ∀ v ∈ Ov, ψ v ∈ 𝒴 := fun v hv => (pψ.1.2.2.2.1 hv).1
  have hv₀Q : v₀ ∈ Ov ∩ ψ ⁻¹' Q := ⟨hv₀, by rw [mem_preimage, hψ₀]; exact hy₀Q⟩
  have oOQ : IsOpen (Ov ∩ ψ ⁻¹' Q) := pψQ.1.1
  have hG : IsSmoothOnOpen 𝒳 𝒳 G := by
    refine ⟨hF.1, fun c' => ?_⟩
    intro u hu
    have hud : u ∈ c'.source := hu.1
    have hcu : ContDiffAt ℝ ∞ c'.param u :=
      c'.contDiffOn_param.contDiffAt (c'.isOpen_source.mem_nhds hud)
    have hev : ∀ᶠ u' in 𝓝 u, c'.param u' ∈ 𝒳 := by
      filter_upwards [c'.isOpen_source.mem_nhds hud] with u' hu' using
        param_mem_of_mem_source c' hu'
    have h1 : ContDiffAt ℝ ∞ (F ∘ c'.param) u :=
      hComp _ _ _ 𝒳 𝒳 F _ u h𝒳 hF hcu hev (param_mem_of_mem_source c' hud)
    have h2 : ContDiffAt ℝ ∞ (m ∘ c'.param) u :=
      hComp _ _ _ 𝒳 𝒳 m _ u h𝒳 hm.smooth hcu hev (param_mem_of_mem_source c' hud)
    have h3 : ContDiffAt ℝ ∞ (g ∘ (m ∘ c'.param)) u :=
      hComp _ _ _ 𝒴 𝒴 g _ u h𝒴 hg h2 (hev.mono fun _ h => hm.mapsTo h)
        (hm.mapsTo (param_mem_of_mem_source c' hud))
    exact (h1.add h3).contDiffWithinAt
  have hf2 : IsC2OnCharted 𝒰 f := by
    intro c' u hud
    have hcu : ContDiffAt ℝ ∞ c'.param u :=
      c'.contDiffOn_param.contDiffAt (c'.isOpen_source.mem_nhds hud)
    have hev : ∀ᶠ u' in 𝓝 u, c'.param u' ∈ 𝒰 := by
      filter_upwards [c'.isOpen_source.mem_nhds hud] with u' hu' using
        param_mem_of_mem_source c' hu'
    have h1 : ContDiffAt ℝ ∞ (x ∘ c'.param) u :=
      hComp _ _ _ 𝒴 𝒰 x _ u h𝒴 hx hcu (hev.mono fun _ h => h𝒰sub h)
        (param_mem_of_mem_source c' hud)
    have h2 : ContDiffAt ℝ ∞ (F ∘ (x ∘ c'.param)) u :=
      hComp _ _ _ 𝒳 𝒳 F _ u h𝒳 hF h1 (hev.mono fun _ h => hxmaps h)
        (hxmaps (param_mem_of_mem_source c' hud))
    have h3 : ContDiffAt ℝ ∞ (g ∘ c'.param) u :=
      hComp _ _ _ 𝒴 𝒴 g _ u h𝒴 hg hcu (hev.mono fun _ h => h𝒰sub h)
        (h𝒰sub (param_mem_of_mem_source c' hud))
    exact ((h2.add h3).of_le (WithTop.coe_le_coe.2 le_top)).contDiffWithinAt
  obtain ⟨Ω, ρ, oΩ, hΩ, smρ, hρ⟩ := hRetr E₁ _ 𝒳 _ ξ (w₀, v₀, u₀) pξ ⟨hw₀, hv₀, hu₀⟩
  rw [hξ₀] at hΩ
  have hψsm : ContDiffAt ℝ ∞ ψ v₀ := pψ.2.contDiffAt (oOv.mem_nhds hv₀)
  have hψ𝒴 : ∀ᶠ v in 𝓝 v₀, ψ v ∈ 𝒴 := by
    filter_upwards [oOv.mem_nhds hv₀] with v hv using hψmem v hv
  have hxψ : ContDiffAt ℝ ∞ (x ∘ ψ) v₀ :=
    hComp _ _ _ 𝒴 𝒰 x ψ v₀ h𝒴 hx hψsm hψ𝒴 (by rw [hψ₀]; exact hy₀)
  have hxψ₀ : (x ∘ ψ) v₀ = x₀ := by simp only [Function.comp, hψ₀, x₀]
  have hρsm : ContDiffAt ℝ ∞ ρ ((x ∘ ψ) v₀) := by
    rw [hxψ₀]; exact smρ.contDiffAt (oΩ.mem_nhds hΩ)
  set bar : (Fin b → ℝ) → Fin c → ℝ := fun v => (ρ (x (ψ v))).2.2 with hbardef
  have hbarsm : ContDiffAt ℝ ∞ bar v₀ :=
    (contDiffAt_snd.comp _ (contDiffAt_snd.comp _ (hρsm.comp v₀ hxψ)))
  have hgood : ∀ᶠ v in 𝓝 v₀, v ∈ Ov ∧ ψ v ∈ Q ∧ bar v ∈ Ou ∧ ξ (w₀, v, bar v) = x (ψ v) := by
    have hpre : ∀ᶠ v in 𝓝 v₀, x (ψ v) ∈ Ω :=
      hxψ.continuousAt.eventually (by rw [hxψ₀]; exact oΩ.mem_nhds hΩ)
    filter_upwards [oOQ.mem_nhds hv₀Q, hpre] with v hvQ hvΩ
    have hv𝒰 : ψ v ∈ 𝒰 := hvQ.2.2
    obtain ⟨h1, h2⟩ := hρ (x (ψ v)) ⟨hxmaps hv𝒰, hvΩ⟩
    obtain ⟨h1a, h1b, h1c⟩ := h1
    have h3 : η ((ρ (x (ψ v))).1, (ρ (x (ψ v))).2.1) = η (w₀, v) := by
      rw [← mξ _ h1a _ h1b _ h1c]
      change m (ξ (ρ (x (ψ v)))) = ψ v
      rw [h2]; exact hmx _ hv𝒰
    have h4 := pη.1.2.2.1 (⟨h1a, h1b⟩ : _ ∈ Ow ×ˢ Ov) (⟨hw₀, hvQ.1⟩ : _ ∈ Ow ×ˢ Ov) h3
    simp only [Prod.mk.injEq] at h4
    refine ⟨hvQ.1, hvQ.2, h1c, ?_⟩
    rw [← h2]
    congr 1
    exact Prod.ext h4.1.symm (Prod.ext h4.2.symm rfl)
  have hbar₀ : bar v₀ = u₀ := by
    obtain ⟨-, -, h1, h2⟩ := hgood.self_of_nhds
    have h3 : ξ (w₀, v₀, bar v₀) = ξ (w₀, v₀, u₀) := by
      rw [h2, hξ₀]; simp only [hψ₀, x₀]
    have h4 := pξ.1.2.2.1 (⟨hw₀, hv₀, h1⟩ : (w₀, v₀, bar v₀) ∈ Ow ×ˢ Ov ×ˢ Ou)
      (⟨hw₀, hv₀, hu₀⟩ : (w₀, v₀, u₀) ∈ Ow ×ˢ Ov ×ˢ Ou) h3
    simpa using h4
  have hp₀ : ((v₀, u₀) : (Fin b → ℝ) × (Fin c → ℝ)) ∈ Ov ×ˢ Ou := ⟨hv₀, hu₀⟩
  have oP : IsOpen (Ov ×ˢ Ou) := oOv.prod oOu
  have hΨ𝒳 : ∀ p ∈ Ov ×ˢ Ou, Ψ p ∈ 𝒳 := fun p hp => (pΨ.1.2.2.2.1 hp).1
  have hΨsm : ContDiffAt ℝ ∞ Ψ (v₀, u₀) := pΨ.2.contDiffAt (oP.mem_nhds hp₀)
  set H : (Fin b → ℝ) × (Fin c → ℝ) → ℝ := G ∘ Ψ with hHdef
  have hHsm : ContDiffAt ℝ 2 H (v₀, bar v₀) := by
    rw [hbar₀]
    refine (hComp _ _ _ 𝒳 𝒳 G Ψ (v₀, u₀) h𝒳 hG hΨsm ?_ (hΨ𝒳 _ hp₀)).of_le
      (WithTop.coe_le_coe.2 le_top)
    filter_upwards [oP.mem_nhds hp₀] with p hp using hΨ𝒳 p hp
  have hHform : ∀ v ∈ Ov, ∀ u ∈ Ou, H (v, u) = F (ξ (w₀, v, u)) + g (ψ v) := by
    intro v hv u hu
    simp only [H, G, Ψ, Function.comp]
    rw [mξ w₀ hw₀ v hv u hu]
  have hevc : ∀ᶠ v in 𝓝 v₀, ∀ k, fderiv ℝ (fun u => H (v, u)) (bar v) k = 0 := by
    filter_upwards [hgood] with v hv
    obtain ⟨hvO, hvQ, hbv, hξv⟩ := hv
    have hv𝒰 : ψ v ∈ 𝒰 := hvQ.2
    have pϕ : IsSmoothParametrization (fiber 𝒳 m (ψ v)) Ou fun u => ξ (w₀, v, u) :=
      fξ' w₀ hw₀ v hvO
    have hN : IsChartedSubsetOf (fiber 𝒳 m (ψ v)) 𝒳 :=
      ⟨fun _ h => h.1, hFib _ _ 𝒳 𝒴 m _ h𝒳 h𝒴 hm⟩
    obtain ⟨-, hcr, -, -⟩ := hessianData_at (vectorCurveData E₁)
      ((hY1 E₁ 𝒳 _ F h𝒳 hN (isC2OnCharted_of_isSmoothOnOpen hF)).1 (Fin c → ℝ) Ou
        (fun u => ξ (w₀, v, u)) (bar v) pϕ.1 hbv) hξv
    have h0 := hcr.1 (hcrit (ψ v) hv𝒰).1
    have heq : (fun u => H (v, u)) =ᶠ[𝓝 (bar v)]
        fun u => (F ∘ fun u => ξ (w₀, v, u)) u + g (ψ v) := by
      filter_upwards [oOu.mem_nhds hbv] with u hu using hHform v hvO u hu
    intro k
    rw [heq.fderiv_eq, fderiv_add_const, h0]
    rfl
  obtain ⟨S1, S2, S3⟩ := hS _ _ H bar v₀ hHsm
    (hbarsm.of_le (WithTop.coe_le_coe.2 le_top)) hevc
  rw [hbar₀] at S1 S2 S3
  have hφeq : (fun v => H (v, bar v)) =ᶠ[𝓝 v₀] f ∘ ψ := by
    filter_upwards [hgood] with v hv
    obtain ⟨hvO, hvQ, hbv, hξv⟩ := hv
    rw [hHform v hvO _ hbv, hξv]
    rfl
  have hφ1 : fderiv ℝ (fun v => H (v, bar v)) v₀ = fderiv ℝ (f ∘ ψ) v₀ := hφeq.fderiv_eq
  have hφ2 : fderiv ℝ (fderiv ℝ fun v => H (v, bar v)) v₀ = fderiv ℝ (fderiv ℝ (f ∘ ψ)) v₀ :=
    hφeq.fderiv.fderiv_eq
  have hQsub : IsChartedSubsetOf Q 𝒰 := ⟨fun _ h => h.2, hQ⟩
  obtain ⟨RQr, RQc, RQh, RQp⟩ := hessianData_at (vectorCurveData E₂)
    ((hY1 E₂ 𝒰 Q f h𝒰 hQsub hf2).1 _ _ ψ v₀ pψQ.1 hv₀Q) hψ₀
  have hcr₂ : (vectorCurveData E₂).IsCriticalOn Q f y₀ := hcrit₂.1
  have hDψ0 : fderiv ℝ (f ∘ ψ) v₀ = 0 := RQc.1 hcr₂
  have posφ := (RQp hcr₂).1 hcrit₂.2
  set ϕ₀ : (Fin c → ℝ) → E₁ := fun u => ξ (w₀, v₀, u) with hϕ₀def
  have pϕ₀ : IsSmoothParametrization (fiber 𝒳 m y₀) Ou ϕ₀ := hη₀ ▸ fξ' w₀ hw₀ v₀ hv₀
  have hN₀ : IsChartedSubsetOf (fiber 𝒳 m y₀) 𝒳 :=
    ⟨fun _ h => h.1, hFib _ _ 𝒳 𝒴 m _ h𝒳 h𝒴 hm⟩
  obtain ⟨RFr, RFc, RFh, RFp⟩ := hessianData_at (vectorCurveData E₁)
    ((hY1 E₁ 𝒳 (fiber 𝒳 m y₀) F h𝒳 hN₀ (isC2OnCharted_of_isSmoothOnOpen hF)).1 _ Ou ϕ₀ u₀
      pϕ₀.1 hu₀) hξ₀
  have hcrF := hcrit y₀ hy₀
  have posF := (RFp hcrF.1).1 hcrF.2
  have hP : IsChartedSubsetOf P 𝒳 :=
    ⟨fun _ h => h.1, hFib _ _ 𝒳 𝒵 (n ∘ m) _ h𝒳 h𝒵 (hSub _ _ _ 𝒳 𝒴 𝒵 m n h𝒳 h𝒴 h𝒵 hm hn)⟩
  obtain ⟨RPr, RPc, RPh, RPp⟩ := hessianData_at (vectorCurveData E₁)
    ((hY1 E₁ 𝒳 P G h𝒳 hP (isC2OnCharted_of_isSmoothOnOpen hG)).1 _ (Ov ×ˢ Ou) Ψ (v₀, u₀)
      pΨ.1 hp₀) hΨ₀
  have hFH : fderiv ℝ (fderiv ℝ (F ∘ ϕ₀)) u₀ = fderiv ℝ (fderiv ℝ fun u => H (v₀, u)) u₀ := by
    have heq : (fun u => H (v₀, u)) =ᶠ[𝓝 u₀] fun u => (F ∘ ϕ₀) u + g (ψ v₀) := by
      filter_upwards [oOu.mem_nhds hu₀] with u hu using hHform v₀ hv₀ u hu
    exact (fderiv_eventuallyEq_of_eventuallyEq_add_const _ heq).fderiv_eq.symm
  have posU : ∀ k : Fin c → ℝ, k ≠ 0 → 0 < fderiv ℝ (fderiv ℝ H) (v₀, u₀) (0, k) (0, k) := by
    intro k hk
    rw [← S2 k k, ← hFH]
    exact posF k hk
  have nonnegU : ∀ k : Fin c → ℝ, 0 ≤ fderiv ℝ (fderiv ℝ H) (v₀, u₀) (0, k) (0, k) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have h00 : (((0 : Fin b → ℝ), (0 : Fin c → ℝ)) : (Fin b → ℝ) × (Fin c → ℝ)) = 0 := rfl
      rw [h00]
      simp
    · exact (posU k hk).le
  have hcrP : (vectorCurveData E₁).IsCriticalOn P G x₀ := RPc.2 (S1 (hφ1.trans hDψ0))
  have posT : T.PosDef := by
    refine (RPp hcrP).2 fun p hp => ?_
    obtain ⟨h, k⟩ := p
    change 0 < fderiv ℝ (fderiv ℝ H) (v₀, u₀) (h, k) (h, k)
    rw [S3 h k]
    by_cases hh : h = 0
    · subst hh
      have hk : k ≠ 0 := fun hk => hp (by rw [hk]; rfl)
      simpa using posU k hk
    · have h1 := posφ h hh
      rw [← hφ2] at h1
      exact add_pos_of_pos_of_nonneg h1 (nonnegU _)
  have hdom : (w₀, v₀, u₀) ∈ Ow ×ˢ Ov ×ˢ Ou := ⟨hw₀, hv₀, hu₀⟩
  have oDom : IsOpen (Ow ×ˢ Ov ×ˢ Ou) := oOw.prod oP
  have hξd : HasFDerivAt ξ (fderiv ℝ ξ (w₀, v₀, u₀)) (w₀, v₀, u₀) :=
    ((pξ.2.contDiffAt (oDom.mem_nhds hdom)).differentiableAt (by simp)).hasFDerivAt
  have hDΨ : ∀ q, fderiv ℝ Ψ (v₀, u₀) q = fderiv ℝ ξ (w₀, v₀, u₀) (0, q) := by
    intro q
    have h1 := (hξd.comp (v₀, u₀) (hasFDerivAt_prodMk_right w₀ (v₀, u₀))).fderiv
    have h2 : fderiv ℝ Ψ (v₀, u₀) = _ := h1
    rw [h2]
    rfl
  have hΨd : HasFDerivAt Ψ (fderiv ℝ Ψ (v₀, u₀)) (v₀, u₀) :=
    (hΨsm.differentiableAt (by simp)).hasFDerivAt
  have hDϕ : ∀ k, fderiv ℝ ϕ₀ u₀ k = fderiv ℝ Ψ (v₀, u₀) (0, k) := by
    intro k
    have h1 := (hΨd.comp u₀ (hasFDerivAt_prodMk_right v₀ u₀)).fderiv
    have h2 : fderiv ℝ ϕ₀ u₀ = _ := h1
    rw [h2]
    rfl
  have oB : IsOpen (Ow ×ˢ Ov) := oOw.prod oOv
  have hb₀ : (w₀, v₀) ∈ Ow ×ˢ Ov := ⟨hw₀, hv₀⟩
  have hηd : HasFDerivAt η (fderiv ℝ η (w₀, v₀)) (w₀, v₀) :=
    ((pη.2.contDiffAt (oB.mem_nhds hb₀)).differentiableAt (by simp)).hasFDerivAt
  have hDψ : ∀ h, fderiv ℝ ψ v₀ h = fderiv ℝ η (w₀, v₀) (0, h) := by
    intro h
    have h1 := (hηd.comp v₀ (hasFDerivAt_prodMk_right w₀ v₀)).fderiv
    have h2 : fderiv ℝ ψ v₀ = _ := h1
    rw [h2]
    rfl
  have hDm : ∀ q : (Fin b → ℝ) × (Fin c → ℝ),
      fderiv ℝ (m ∘ ξ) (w₀, v₀, u₀) (0, q) = fderiv ℝ ψ v₀ q.1 := by
    intro q
    let Lp : (Fin a → ℝ) × (Fin b → ℝ) × (Fin c → ℝ) →L[ℝ] (Fin a → ℝ) × (Fin b → ℝ) :=
      (ContinuousLinearMap.fst ℝ _ _).prod
        ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
    have heq : m ∘ ξ =ᶠ[𝓝 (w₀, v₀, u₀)] η ∘ Lp := by
      filter_upwards [oDom.mem_nhds hdom] with p hp
      obtain ⟨w, v, u⟩ := p
      exact mξ w hp.1 v hp.2.1 u hp.2.2
    have h1 : HasFDerivAt (η ∘ Lp) ((fderiv ℝ η (w₀, v₀)).comp Lp) (w₀, v₀, u₀) :=
      HasFDerivAt.comp (w₀, v₀, u₀) hηd Lp.hasFDerivAt
    rw [heq.fderiv_eq, h1.fderiv, hDψ]
    rfl
  have hTan' : tangentSpace 𝒳 x₀ = LinearMap.range (fderiv ℝ ξ (w₀, v₀, u₀) :
      ((Fin a → ℝ) × (Fin b → ℝ) × (Fin c → ℝ)) →ₗ[ℝ] E₁) :=
    hξ₀ ▸ hTan E₁ _ 𝒳 _ ξ (w₀, v₀, u₀) h𝒳 pξ hdom
  have hDiff' : ∀ (v : tangentSpace 𝒳 x₀) (q), (v : E₁) = fderiv ℝ ξ (w₀, v₀, u₀) q →
      tangentDifferential 𝒳 m x₀ v = fderiv ℝ (m ∘ ξ) (w₀, v₀, u₀) q := by
    have key : ∀ e (he : ξ (w₀, v₀, u₀) = e) (v : tangentSpace 𝒳 e) (q),
        (v : E₁) = fderiv ℝ ξ (w₀, v₀, u₀) q →
        tangentDifferential 𝒳 m e v = fderiv ℝ (m ∘ ξ) (w₀, v₀, u₀) q := by
      intro e he
      subst he
      intro v q hv
      exact hDiff E₁ E₂ _ 𝒳 𝒳 m _ ξ _ q v h𝒳 hm.smooth pξ hdom (by rw [hξ₀]; exact hx₀) hv
    exact key x₀ hξ₀
  refine ⟨hcrP, posT, ?_, ?_⟩
  · have hle : (vectorCurveData E₁).tangentSpan (fiber 𝒳 m y₀) x₀ ≤
        (vectorCurveData E₁).tangentSpan P x₀ := by
      rw [← RFr, ← RPr]
      rintro _ ⟨k, rfl⟩
      exact ⟨(0, k), (hDϕ k).symm⟩
    refine ⟨hle, ?_⟩
    ext v
    have hv : (v : E₁) ∈ LinearMap.range (fderiv ℝ ϕ₀ u₀ : (Fin c → ℝ) →ₗ[ℝ] E₁) := by
      rw [RFr]; exact v.2
    obtain ⟨k, hk⟩ := hv
    have e1 : T₁ v = fderiv ℝ (fderiv ℝ (F ∘ ϕ₀)) u₀ k k := RFh hcrF.1 k v hk.symm
    have e2 : T (Submodule.inclusion hle v) = fderiv ℝ (fderiv ℝ H) (v₀, u₀) (0, k) (0, k) :=
      RPh hcrP (0, k) (Submodule.inclusion hle v) (by
        change (v : E₁) = fderiv ℝ Ψ (v₀, u₀) (0, k)
        rw [← hDϕ k]; exact hk.symm)
    change T (Submodule.inclusion hle v) = T₁ v
    rw [e1, e2, hFH, S2]
  · intro ζ
    have hζ : (ζ : E₂) ∈ LinearMap.range (fderiv ℝ ψ v₀ : (Fin b → ℝ) →ₗ[ℝ] E₂) := by
      rw [RQr]; exact ζ.2
    obtain ⟨h₀, hh₀⟩ := hζ
    have e1 : T₂ ζ = fderiv ℝ (fderiv ℝ fun v => H (v, bar v)) v₀ h₀ h₀ := by
      rw [hφ2]; exact RQh hcr₂ h₀ ζ hh₀.symm
    have hmemP : ∀ q, fderiv ℝ Ψ (v₀, u₀) q ∈ (vectorCurveData E₁).tangentSpan P x₀ := by
      intro q; rw [← RPr]; exact ⟨q, rfl⟩
    have hmem𝒳 : ∀ q, fderiv ℝ Ψ (v₀, u₀) q ∈ tangentSpace 𝒳 x₀ := by
      intro q; rw [hTan', hDΨ]; exact ⟨(0, q), rfl⟩
    have hdiffq : ∀ (q) (ξ' : tangentSpace 𝒳 x₀), (ξ' : E₁) = fderiv ℝ Ψ (v₀, u₀) q →
        tangentDifferential 𝒳 m x₀ ξ' = fderiv ℝ ψ v₀ q.1 := by
      intro q ξ' hq
      rw [hDiff' ξ' (0, q) (by rw [hq, hDΨ]), hDm]
    refine ⟨?_, ?_⟩
    · refine ⟨⟨_, hmemP (h₀, fderiv ℝ bar v₀ h₀)⟩, ⟨_, hmem𝒳 (h₀, fderiv ℝ bar v₀ h₀)⟩, rfl,
        ?_, ?_⟩
      · rw [hdiffq (h₀, fderiv ℝ bar v₀ h₀) _ rfl]; exact hh₀
      · rw [e1]
        have e2 : T ⟨_, hmemP (h₀, fderiv ℝ bar v₀ h₀)⟩ = fderiv ℝ (fderiv ℝ H) (v₀, u₀)
            (h₀, fderiv ℝ bar v₀ h₀) (h₀, fderiv ℝ bar v₀ h₀) := RPh hcrP _ _ rfl
        have h00 : (((0 : Fin b → ℝ), (0 : Fin c → ℝ)) : (Fin b → ℝ) × (Fin c → ℝ)) = 0 := rfl
        rw [e2, S3, sub_self, h00]
        simp
    · rintro t ⟨ξ₁, ξ', hξ', hdm, rfl⟩
      have hξ₁ : (ξ₁ : E₁) ∈ LinearMap.range (fderiv ℝ Ψ (v₀, u₀) :
          ((Fin b → ℝ) × (Fin c → ℝ)) →ₗ[ℝ] E₁) := by
        rw [RPr]; exact ξ₁.2
      obtain ⟨⟨h, k⟩, hq⟩ := hξ₁
      have hq' : (ξ₁ : E₁) = fderiv ℝ Ψ (v₀, u₀) (h, k) := hq.symm
      have e3 := hdiffq (h, k) ξ' (hξ'.trans hq')
      rw [hdm, ← hh₀] at e3
      have hinj : Function.Injective (fderiv ℝ ψ v₀) := pψ.1.2.2.2.2.1 v₀ hv₀
      have hh : h₀ = h := hinj e3
      subst hh
      have e4 : T ξ₁ = fderiv ℝ (fderiv ℝ H) (v₀, u₀) (h₀, k) (h₀, k) := RPh hcrP _ _ hq'
      rw [e1, e4, S3]
      exact le_add_of_nonneg_right (nonnegU _)
theorem claim_holds (hY : Tower.RestrictionHessian.Statement)
    (hL : Manifolds.LocalSmoothCalculus)
    (hC : Manifolds.CoordinatesOfTwoSubmersions)
    (hS : Calculus.CriticalBranchHessian)
    (hN : ConstraintStages.GaussianNumberOfComposite) : Claim :=
  ⟨hN, hessianRelations_holds hY hL hC hS⟩
end TwoStageConstraint
end YangMills.Construction
end
