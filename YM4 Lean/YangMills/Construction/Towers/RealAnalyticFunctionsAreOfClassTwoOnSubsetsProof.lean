import YangMills.Construction.Towers.RealAnalyticFunctionsAlongTwiceDifferentiableCurvesProof
import YangMills.Construction.Towers.RealAnalyticFunctionsAreOfClassTwoOnSubsets
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces Matrices.PowerExpCharts
open Conventions
namespace Tower.AnalyticIsC2OnSubsets
variable {L n k j : ℕ}
private theorem fieldOfPositiveValues_restrict {A : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges A) = A := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
private theorem positiveEdge_nonempty (hP : BondSetFields.ProductStructureHolds)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Nonempty (PositiveEdge L n k j) := by apply _root_.YangMills.SharedProofs.p12312 <;> assumption
private theorem exists_retraction :
    ∃ R : ComplexMatrix2 →L[ℝ] ComplexMatrix2.LieElement,
      ∀ Y : ComplexMatrix2.LieElement, R Y.toMatrix = Y := by apply _root_.YangMills.Construction.Matrices.specialUnitaryPower.Composition.exists_clm_leftInverse_toMatrix <;> assumption
private theorem holomorphicScalar_of_coords {σ : Type} [Fintype σ]
    {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (h : IsHolomorphicToCoords β (Equiv.refl _) W Φ) :
    HolomorphicScalar β W fun q => Φ q 0 := by apply _root_.YangMills.SharedProofs.p9409 <;> assumption
theorem analyticIsC2OnSubsets (hC : ExpChartsStatement)
    (hP : BondSetFields.ProductStructureHolds) : AnalyticIsC2OnSubsetsStatement := by
  intro L n k j hL hn hj inst 𝒰 N F hF hN c
  obtain ⟨hopen, f₁, han⟩ := hF
  obtain rfl : f₁ = inst := Subsingleton.elim _ _
  have := positiveEdge_nonempty hP hL hn hj
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  obtain ⟨hcharts, -, -, -, -, -, -, hpull⟩ := hC (PositiveEdge L n k j) (PositiveEdge L n k j)
  have hO : specialUnitaryPower.IsOpenSubset (restrictToPositiveEdges '' 𝒰) := hopen.2
  have hfield : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => fieldOfPositiveValues_restrict (hopen.1 hU)
  let f : (PositiveEdge L n k j → ComplexMatrix2) → ℝ := fun w => F (fieldOfPositiveValues w)
  have hrest : IsLocallyHolomorphicRestriction (HolomorphicScalar β) Complex.ofReal
      (restrictToPositiveEdges '' 𝒰) f := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
      rw [hfield hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Φ, hΦ, heq⟩ := han.2 _ hq
    refine ⟨𝒳, fun q => Φ q 0, hp𝒳, holomorphicScalar_of_coords (hΦ β), ?_⟩
    rintro _ ⟨U', hU', rfl⟩ hx
    have hval := heq ⟨hx, (Submodule.mem_bot ℝ).2 (funext fun e => e.elim),
      fun c => (hopen.1 hU').1 c (mem_univ _)⟩
    exact congrFun hval 0
  have hinN : ∀ u ∈ c.source, c.param u ∈ restrictToPositiveEdges '' N := by
    intro u hu
    obtain ⟨O, -, hOe⟩ := c.isRelativelyOpen_image c.source subset_rfl c.isOpen_source
    have hm : c.param u ∈ c.param '' c.source := ⟨u, hu, rfl⟩
    rw [hOe] at hm
    exact hm.2
  intro u hu
  have hus : c.source ∈ 𝓝 u := c.isOpen_source.mem_nhds hu
  obtain ⟨V, hVN, hVu⟩ := hinN u hu
  have hV : V ∈ 𝒰 := hN hVN
  let p₀ : PositiveEdge L n k j → ComplexMatrix2 := restrictToPositiveEdges V
  obtain ⟨Nb, hNb, -, hsm, -⟩ :=
    (((hpull β).1 _ hO).1 f hrest).1.1 p₀ ⟨V, hV, rfl⟩
  have hp₀ : p₀ ∈ specialUnitaryPower (PositiveEdge L n k j) :=
    fun e => (hopen.1 hV).1 e (mem_univ _)
  obtain ⟨-, hform, hε⟩ := hcharts p₀ hp₀
  have hεpos : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, ⟨Ω, hΩ, himg⟩, hp₀img, -, hlogopen, hlogsm, hsub, hleft, -⟩ :=
    hε _ hεpos (by rw [Real.exp_log (by norm_num)])
  obtain ⟨R, hR⟩ := exists_retraction
  let G₁ : (PositiveEdge L n k j → ComplexMatrix2) → PositiveEdge L n k j → ComplexMatrix2.LieElement :=
    fun X s => R (logChart p₀ X s)
  have hz : (0 : ComplexMatrix2.LieElement).toMatrix = 0 := rfl
  have hchart0 : expChartI p₀ 0 = p₀ := by
    rw [(hform 0).2.1]
    funext s
    simp [hz]
  have h0small : (0 : PositiveEdge L n k j → ComplexMatrix2.LieElement) ∈
      smallBall (PositiveEdge L n k j) (Real.log (19 / 10)) := by
    intro s
    simpa [hz] using hεpos
  have hG₁0 : G₁ p₀ = 0 := by
    funext s
    have hl := congrFun (hleft 0 h0small) s
    rw [hchart0] at hl
    show R (logChart p₀ p₀ s) = 0
    rw [hl]
    exact hR 0
  have hG₁ : ContDiffAt ℝ 2 G₁ p₀ := by
    have hl : ContDiffAt ℝ 2 (logChart p₀) p₀ :=
      (hlogsm.contDiffAt (hlogopen.mem_nhds (hsub hp₀img))).of_le ENat.LEInfty.out
    exact contDiffAt_pi.2 fun s => R.contDiff.contDiffAt.comp p₀ (contDiffAt_pi.1 hl s)
  have hG₂ : ContDiffAt ℝ 2 (f ∘ expChartI p₀) (G₁ p₀) := by
    rw [hG₁0]
    exact (hsm.contDiffAt hNb).of_le ENat.LEInfty.out
  have hG : ContDiffAt ℝ 2 ((f ∘ expChartI p₀) ∘ G₁) p₀ := hG₂.comp p₀ hG₁
  have hup : c.param u = p₀ := hVu.symm
  have hpar : ContDiffAt ℝ 2 c.param u :=
    (c.contDiffOn_param.contDiffAt hus).of_le ENat.LEInfty.out
  have hcomp : ContDiffAt ℝ 2 (((f ∘ expChartI p₀) ∘ G₁) ∘ c.param) u :=
    ContDiffAt.comp u (by rw [hup]; exact hG) hpar
  have hnear : c.pullback f =ᶠ[𝓝 u] ((f ∘ expChartI p₀) ∘ G₁) ∘ c.param := by
    have hp₀Ω : p₀ ∈ Ω := (himg ▸ hp₀img : p₀ ∈ Ω ∩ _).1
    have hcΩ : ∀ᶠ v in 𝓝 u, c.param v ∈ Ω :=
      hpar.continuousAt.eventually (hΩ.mem_nhds (by rwa [hup]))
    filter_upwards [hcΩ, hus] with v hvΩ hv
    obtain ⟨U, hUN, hUv⟩ := hinN v hv
    have hcG : c.param v ∈ specialUnitaryPower (PositiveEdge L n k j) := by
      rw [← hUv]
      exact fun e => (hopen.1 (hN hUN)).1 e (mem_univ _)
    have hmem : c.param v ∈
        expChartI p₀ '' smallBall (PositiveEdge L n k j) (Real.log (19 / 10)) := by
      rw [himg]
      exact ⟨hvΩ, hcG⟩
    obtain ⟨Y, hY, hYc⟩ := hmem
    have hG₁Y : G₁ (c.param v) = Y := by
      funext s
      show R (logChart p₀ (c.param v) s) = Y s
      rw [← hYc, hleft Y hY]
      exact hR (Y s)
    show f (c.param v) = f (expChartI p₀ (G₁ (c.param v)))
    rw [hG₁Y, hYc]
  exact (hcomp.congr_of_eventuallyEq hnear).contDiffWithinAt
end Tower.AnalyticIsC2OnSubsets
end YangMills.Construction
end
