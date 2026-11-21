import YangMills.Construction.Matrices.CompositesOfDifferentiableMapsOnPowersOfGProof
import YangMills.Construction.Towers.RealAnalyticFunctionsAlongTwiceDifferentiableCurves
import YangMills.Construction.Towers.RealAnalyticMapsOfConfigurationsAreDifferentiableProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Matrices Coordinates Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
  Matrices.PowerExpCharts
open scoped Topology ContDiff Matrix.Norms.L2Operator
namespace Tower.AnalyticAlongC2Curve
variable {L n k j : ℕ}
private theorem fieldOfPositiveValues_restrict {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges U) = U := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
private theorem nonempty_positiveEdge (hS : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Nonempty (PositiveEdge L n k j) := by apply _root_.YangMills.SharedProofs.p12312 <;> assumption
private theorem exists_lieProjection :
    ∃ P : ComplexMatrix2 →L[ℝ] ComplexMatrix2.LieElement,
      ∀ Y : ComplexMatrix2.LieElement, P Y.toMatrix = Y := by apply _root_.YangMills.Construction.Matrices.specialUnitaryPower.Composition.exists_clm_leftInverse_toMatrix <;> assumption
private theorem holomorphicScalar_of_coords {σ : Type} [Fintype σ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → ComplexCoordinates 1}
    (h : IsHolomorphicToCoords b (Equiv.refl _) W Φ) :
    HolomorphicScalar b W fun q => Φ q 0 := by
  have hone : ∀ z : ComplexCoordinates 1, (Equiv.funUnique (Fin 1) ℂ).symm (z 0) = z := by
    intro z
    funext l
    rw [Subsingleton.elim l 0]
    simp
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨h₁, ?_, fun p hp => ?_⟩
  · have he : ((Equiv.funUnique (Fin 1) ℂ).symm ∘ fun q => Φ q 0) = Equiv.refl _ ∘ Φ :=
      funext fun q => hone _
    rw [he]
    exact h₂
  · obtain ⟨O, h0, hO, ht, hh⟩ := h₃ p hp
    refine ⟨O, h0, hO, ht, fun ν => ?_⟩
    convert hh ν using 1
    funext z
    exact hone _
abbrev _root_.YangMills.SharedProofs.p9409 := @holomorphicScalar_of_coords
private theorem differentiable_comp_twice {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] {G : E → E'} {h : ℝ → E}
    (hG : ContDiffAt ℝ 2 G (h 0)) (h1 : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ h t)
    (h2 : DifferentiableAt ℝ (deriv h) 0) :
    (∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ (G ∘ h) t) ∧
      DifferentiableAt ℝ (deriv (G ∘ h)) 0 := by
  have hc : ContinuousAt h 0 := h1.self_of_nhds.continuousAt
  have hGd : ∀ᶠ x in 𝓝 (h 0), DifferentiableAt ℝ G x :=
    (hG.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ G (h t) := hc.eventually hGd
  refine ⟨(hev.and h1).mono fun t ht => ht.1.comp t ht.2, ?_⟩
  have hderiv : deriv (G ∘ h) =ᶠ[𝓝 0] fun t => fderiv ℝ G (h t) (deriv h t) :=
    (hev.and h1).mono fun t ht => (ht.1.hasFDerivAt.comp_hasDerivAt t ht.2.hasDerivAt).deriv
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hderiv
  have hfd : DifferentiableAt ℝ (fderiv ℝ G) (h 0) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcomp : DifferentiableAt ℝ (fun t => fderiv ℝ G (h t)) 0 :=
    hfd.comp (0 : ℝ) h1.self_of_nhds
  exact hcomp.clm_apply h2
theorem analyticAlongC2Curve_holds (hC : ExpChartsStatement)
    (hS : BondSetFields.ProductStructureHolds) : AnalyticAlongC2CurveStatement := by
  intro L n k j hL hn hj 𝒰 F hF V hV I γ hγ hγ0
  obtain ⟨hopen, f₁, hra⟩ := hF
  let := f₁
  have := nonempty_positiveEdge hS hL hn hj
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  obtain ⟨hcharts, -, -, -, -, -, -, hread⟩ := hC (PositiveEdge L n k j) (PositiveEdge L n k j)
  have hO : specialUnitaryPower.IsOpenSubset (restrictToPositiveEdges '' 𝒰) := hopen.2
  have hconf : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => fieldOfPositiveValues_restrict (hopen.1 hU)
  let f : (PositiveEdge L n k j → ComplexMatrix2) → ℝ := fun w => F (fieldOfPositiveValues w)
  have hrest : IsLocallyHolomorphicRestriction (HolomorphicScalar β) Complex.ofReal
      (restrictToPositiveEdges '' 𝒰) f := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
      rw [hconf hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Φ, hΦ, heq⟩ := hra.2 _ hq
    refine ⟨𝒳, fun q => Φ q 0, hp𝒳, holomorphicScalar_of_coords (hΦ β), ?_⟩
    rintro _ ⟨U', hU', rfl⟩ hx
    have hval := heq ⟨hx, (Submodule.mem_bot ℝ).2 (funext fun e => e.elim),
      fun c => (hopen.1 hU').1 c (mem_univ _)⟩
    exact congrFun hval 0
  let p₀ : PositiveEdge L n k j → ComplexMatrix2 := restrictToPositiveEdges V
  obtain ⟨N, hN, -, hsm, -⟩ :=
    (((hread β).1 _ hO).1 f hrest).1.1 p₀ ⟨V, hV, rfl⟩
  have hp₀ : p₀ ∈ specialUnitaryPower (PositiveEdge L n k j) :=
    fun c => (hopen.1 hV).1 c (mem_univ _)
  obtain ⟨-, hform, hε⟩ := hcharts p₀ hp₀
  have hεpos : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, ⟨Ω, hΩ, himg⟩, hp₀img, -, hlogopen, hlogsm, hsub, hleft, -⟩ :=
    hε _ hεpos (by rw [Real.exp_log (by norm_num)])
  obtain ⟨P, hP⟩ := exists_lieProjection
  let G₁ : (PositiveEdge L n k j → ComplexMatrix2) → PositiveEdge L n k j → ComplexMatrix2.LieElement :=
    fun X s => P (logChart p₀ X s)
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
    show P (logChart p₀ p₀ s) = 0
    rw [hl]
    exact hP 0
  have hG₁ : ContDiffAt ℝ 2 G₁ p₀ := by
    have hl : ContDiffAt ℝ 2 (logChart p₀) p₀ :=
      (hlogsm.contDiffAt (hlogopen.mem_nhds (hsub hp₀img))).of_le ENat.LEInfty.out
    exact contDiffAt_pi.2 fun s => P.contDiff.contDiffAt.comp p₀ (contDiffAt_pi.1 hl s)
  have hG₂ : ContDiffAt ℝ 2 (f ∘ expChartI p₀) (G₁ p₀) := by
    rw [hG₁0]
    exact (hsm.contDiffAt hN).of_le ENat.LEInfty.out
  let c : ℝ → PositiveEdge L n k j → ComplexMatrix2 := fun t => restrictToPositiveEdges (γ t)
  have hc0 : c 0 = p₀ := by
    show restrictToPositiveEdges (γ 0) = restrictToPositiveEdges V
    rw [hγ0]
  obtain ⟨⟨hI, hmaps, hd⟩, hdd⟩ := hγ
  have hI0 : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
  have hc1 : ∀ t ∈ I, DifferentiableAt ℝ c t := fun t ht =>
    differentiableAt_pi.2 fun b => (hd b.1 b.2 t ht).differentiableAt (hI.1.mem_nhds ht)
  have hcd : ∀ t ∈ I, deriv c t = fun b => deriv (fun s => γ s b.1) t := fun t ht =>
    deriv_pi fun b => (hd b.1 b.2 t ht).differentiableAt (hI.1.mem_nhds ht)
  have hc2 : DifferentiableAt ℝ (deriv c) 0 := by
    have hb : DifferentiableAt ℝ (fun t (b : PositiveEdge L n k j) =>
        deriv (fun s => γ s b.1) t) 0 :=
      differentiableAt_pi.2 fun b => (hdd b.1 b.2 0 hI.2.2).differentiableAt hI0
    exact hb.congr_of_eventuallyEq (Filter.eventually_of_mem hI0 hcd)
  have hG : ContDiffAt ℝ 2 ((f ∘ expChartI p₀) ∘ G₁) (c 0) := by
    rw [hc0]
    exact hG₂.comp p₀ hG₁
  have hnear : (fun s => F (γ s)) =ᶠ[𝓝 0] ((f ∘ expChartI p₀) ∘ G₁) ∘ c := by
    have hp₀Ω : p₀ ∈ Ω := (himg ▸ hp₀img : p₀ ∈ Ω ∩ _).1
    have hcΩ : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ Ω :=
      (hc1 0 hI.2.2).continuousAt.eventually (hΩ.mem_nhds (by rwa [hc0]))
    filter_upwards [hcΩ, hI0] with t ht htI
    have hcG : c t ∈ specialUnitaryPower (PositiveEdge L n k j) :=
      fun b => (hmaps htI).1 b (mem_univ _)
    have hmem : c t ∈ expChartI p₀ '' smallBall (PositiveEdge L n k j) (Real.log (19 / 10)) := by
      rw [himg]
      exact ⟨ht, hcG⟩
    obtain ⟨Y, hY, hYc⟩ := hmem
    have hG₁Y : G₁ (c t) = Y := by
      funext s
      show P (logChart p₀ (c t) s) = Y s
      rw [← hYc, hleft Y hY]
      exact hP (Y s)
    show F (γ t) = f (expChartI p₀ (G₁ (c t)))
    rw [hG₁Y, hYc]
    show F (γ t) = F (fieldOfPositiveValues (restrictToPositiveEdges (γ t)))
    rw [fieldOfPositiveValues_restrict (hmaps htI)]
  obtain ⟨h1, h2⟩ := differentiable_comp_twice hG (Filter.eventually_of_mem hI0 hc1) hc2
  refine ⟨?_, h2.congr_of_eventuallyEq hnear.deriv⟩
  filter_upwards [hnear.eventuallyEq_nhds, h1] with t ht hdt
  exact hdt.congr_of_eventuallyEq ht
end Tower.AnalyticAlongC2Curve
end YangMills.Construction
end
