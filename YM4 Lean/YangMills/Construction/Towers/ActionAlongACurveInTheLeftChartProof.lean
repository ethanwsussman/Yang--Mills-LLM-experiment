import YangMills.Construction.Towers.CriticalBranchAtTheBottomLevelProof
import YangMills.Construction.Towers.ActionAlongACurveInTheLeftChart
import YangMills.Construction.Towers.HessianOnAFibreOfTheCriticalBranchProof
import Mathlib
set_option autoImplicit false
open Set Filter Asymptotics
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LeftChartCurveAction.SecondVariation
open YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.PowerExpCharts YangMills.Construction.Tower
section Calculus
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']
theorem hasDerivAt_deriv_comp_of_contDiffAt {G : E → E'} {h : ℝ → E} (hG : ContDiffAt ℝ 2 G (h 0))
    (h1 : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ h t) (h2 : DifferentiableAt ℝ (deriv h) 0) :
    (∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ (G ∘ h) t) ∧
      HasDerivAt (deriv (G ∘ h))
        (fderiv ℝ (fderiv ℝ G) (h 0) (deriv h 0) (deriv h 0) +
          fderiv ℝ G (h 0) (deriv (deriv h) 0)) 0 := by apply _root_.YangMills.Construction.Tower.FibreHessian.secondDeriv_comp <;> assumption
theorem isLittleO_taylor_two {x : ℝ → E} (h1 : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ x t)
    (h2 : DifferentiableAt ℝ (deriv x) 0) (h0 : x 0 = 0) :
    (fun t : ℝ => x t - t • deriv x 0 - (t ^ 2 / 2) • deriv (deriv x) 0) =o[𝓝 0]
      fun t : ℝ => t ^ 2 := by apply _root_.YangMills.Construction.Tower.FibreHessian.isLittleO_taylor_two <;> assumption
theorem deriv_mem_of_eventually_mem {S : Submodule ℝ E} (hS : IsClosed (S : Set E)) {f : ℝ → E}
    {a : ℝ} (h : ∀ᶠ t in 𝓝 a, f t ∈ S) : deriv f a ∈ S := by
  by_cases hd : DifferentiableAt ℝ f a
  · have ht := hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt
    refine hS.mem_of_tendsto ht ?_
    filter_upwards [h.filter_mono nhdsWithin_le_nhds] with t hft
    rw [slope_def_module]
    exact S.smul_mem _ (S.sub_mem hft h.self_of_nhds)
  · rw [deriv_zero_of_not_differentiableAt hd]
    exact S.zero_mem
theorem exists_inner_eq_linearMap {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (c : InnerProductSpace.Core ℝ V) (l : V →ₗ[ℝ] ℝ) : ∃ g : V, ∀ v, c.inner g v = l v := by apply _root_.YangMills.Construction.Tower.BottomLevel.exists_inner_eq <;> assumption
end Calculus
section Matrices
theorem contDiffAt_matrix_inv {M : ComplexMatrix2} (hM : IsUnit M) :
    ContDiffAt ℝ 2 (fun A : ComplexMatrix2 => A⁻¹) M := by apply _root_.YangMills.Construction.Tower.BottomLevel.contDiffAt_matrix_inv <;> assumption
theorem contDiff_fullTrace_re :
    ContDiff ℝ 2 (fun M : ComplexMatrix2 => (ComplexMatrix2.fullTrace M).re) := by apply _root_.YangMills.Construction.Tower.BottomLevel.contDiff_re_fullTrace <;> assumption
theorem exists_fullTrace_norm_le :
    ∃ C : ℝ, ∀ M : ComplexMatrix2, ‖ComplexMatrix2.fullTrace M‖ ≤ C * ‖M‖ := by
  let T : ComplexMatrix2 →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
  exact ⟨‖T‖, fun M => T.le_opNorm M⟩
theorem exists_traceFinsumNorm_le {ι : Type} [Fintype ι] :
    ∃ K : ℝ, ∀ w : ι → ComplexMatrix2, traceFinsumNorm w ≤ K * ‖w‖ := by
  obtain ⟨C, hC⟩ := exists_fullTrace_norm_le
  refine ⟨Real.sqrt (Fintype.card ι * (|C| / 2)), fun w => ?_⟩
  have hterm : ∀ i, (ComplexMatrix2.halfTrace (w i * w i)).re ≤ |C| / 2 * ‖w‖ ^ 2 := by
    intro i
    have h1 : ‖w i‖ ≤ ‖w‖ := norm_le_pi_norm w i
    have h2 : ‖w i * w i‖ ≤ ‖w‖ ^ 2 := by
      calc ‖w i * w i‖ ≤ ‖w i‖ * ‖w i‖ := norm_mul_le _ _
        _ ≤ ‖w‖ * ‖w‖ := mul_le_mul h1 h1 (norm_nonneg _) (norm_nonneg _)
        _ = ‖w‖ ^ 2 := (sq _).symm
    have h3 : ‖ComplexMatrix2.fullTrace (w i * w i)‖ ≤ |C| * ‖w‖ ^ 2 :=
      (hC _).trans (mul_le_mul (le_abs_self C) h2 (norm_nonneg _) (abs_nonneg C))
    calc (ComplexMatrix2.halfTrace (w i * w i)).re ≤ ‖ComplexMatrix2.halfTrace (w i * w i)‖ :=
          Complex.re_le_norm _
      _ = 1 / 2 * ‖ComplexMatrix2.fullTrace (w i * w i)‖ := by simp [ComplexMatrix2.halfTrace]
      _ ≤ |C| / 2 * ‖w‖ ^ 2 := by linarith
  have hsum : (traceFinsumPairing w w).re ≤ Fintype.card ι * (|C| / 2) * ‖w‖ ^ 2 := by
    rw [traceFinsumPairing, finsum_eq_sum_of_fintype, Complex.re_sum]
    calc _ ≤ ∑ _i : ι, |C| / 2 * ‖w‖ ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by simp [Finset.card_univ]; ring
  calc traceFinsumNorm w ≤ Real.sqrt (Fintype.card ι * (|C| / 2) * ‖w‖ ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
end Matrices
section Bonds
variable {L n k : ℕ}
theorem isPositivelyOriented_or_opposite (b : Edge L n k 0) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.isPositivelyOriented_or_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (b : Edge L n k 0)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.not_opposite_isPositivelyOriented <;> assumption
theorem edgeFormOfPositiveValues_of_pos (w : PositiveEdge L n k 0 → ComplexMatrix2) {b : Edge L n k 0}
    (h : b.IsPositivelyOriented) : edgeFormOfPositiveValues w b = w ⟨b, h⟩ := by
  simp [edgeFormOfPositiveValues, h]
theorem edgeFormOfPositiveValues_of_opposite (w : PositiveEdge L n k 0 → ComplexMatrix2)
    {b : Edge L n k 0} (h : ¬ b.IsPositivelyOriented) (h' : b.opposite.IsPositivelyOriented) :
    edgeFormOfPositiveValues w b = -w ⟨b.opposite, h'⟩ := by
  simp [edgeFormOfPositiveValues, h, h']
theorem edgeFormOfPositiveValues_mem
    (hnb : ∀ b : Edge L n k 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    {w : PositiveEdge L n k 0 → ComplexMatrix2} (hw : ∀ b, w b ∈ ComplexMatrix2.hermitianTraceless) :
    edgeFormOfPositiveValues w ∈ edgeFormSpace L n k 0 := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [edgeFormOfPositiveValues_of_pos _ hb]
    exact hw _
  · by_cases h : b.IsPositivelyOriented
    · rw [edgeFormOfPositiveValues_of_pos _ h, edgeFormOfPositiveValues_of_opposite _ (hnb b h) h]
      rfl
    · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
      rw [edgeFormOfPositiveValues_of_pos _ h', edgeFormOfPositiveValues_of_opposite _ h h', neg_neg]
theorem expTwist_restrict (X U : Edge L n k 0 → ComplexMatrix2) :
    PeriodicLattice.expTwist (edgeFormOfPositiveValues (restrictToPositiveEdges X)) U =
      PeriodicLattice.expTwist X U := by apply _root_.YangMills.Construction.Tower.BottomLevel.expTwist_restrict <;> assumption
def twistedField (U : Edge L n k 0 → ComplexMatrix2) (y : PositiveEdge L n k 0 → ComplexMatrix2) :
    Edge L n k 0 → ComplexMatrix2 :=
  PeriodicLattice.expTwist (edgeFormOfPositiveValues y) U
variable [Fintype (PositiveEdge L n k 0)]
theorem contDiff_matExp_mul (c : PositiveEdge L n k 0) (V : ComplexMatrix2) :
    ContDiff ℝ 2 (fun y : PositiveEdge L n k 0 → ComplexMatrix2 =>
      ComplexMatrix2.matExp (Complex.I • y c) * V) := by apply _root_.YangMills.Construction.Tower.BottomLevel.contDiff_matExp_mul <;> assumption
theorem contDiffAt_plaquetteAction_twisted [Fintype (Face L n k 0)]
    {U : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0) :
    ContDiffAt ℝ 2 (fun y => plaquetteAction L n k (twistedField U y)) 0 := by apply _root_.YangMills.Construction.Tower.BottomLevel.contDiffAt_plaquetteAction_twisted <;> assumption
end Bonds
section EvaluationMaps
variable {L n k : ℕ} [Fintype (PositiveEdge L n k 0)] [Nonempty (PositiveEdge L n k 0)]
theorem exists_log_chart (hC : ExpChartsStatement)
    (hA : LeftChartFields.Claim) {U : Edge L n k 0 → ComplexMatrix2} {I : Set ℝ}
    {γ : ℝ → Edge L n k 0 → ComplexMatrix2} (hγ : (fieldCurveData L n k 0).IsTwiceDiffCurve I γ)
    (hγ0 : γ 0 = U) {B : Edge L n k 0 → ComplexMatrix2} (hB : curveTangent γ = B) :
    ∃ x : ℝ → PositiveEdge L n k 0 → ComplexMatrix2, x 0 = 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ x t) ∧ DifferentiableAt ℝ (deriv x) 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), (∀ b, x t b ∈ ComplexMatrix2.hermitianTraceless) ∧
        ∀ b : PositiveEdge L n k 0,
          ComplexMatrix2.matExp (Complex.I • x t b) * U b.1 = γ t b.1) ∧
      deriv x 0 = restrictToPositiveEdges B := by
  obtain ⟨hcharts, -⟩ := hC (PositiveEdge L n k 0) (PositiveEdge L n k 0)
  obtain ⟨⟨hI, hmaps, hd⟩, hdd⟩ := hγ
  have hI0 : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
  let p₀ : PositiveEdge L n k 0 → ComplexMatrix2 := restrictToPositiveEdges U
  have hU : U ∈ fieldSpace L n k 0 := hγ0 ▸ hmaps hI.2.2
  have hp₀ : p₀ ∈ specialUnitaryPower (PositiveEdge L n k 0) := fun c => hU.1 c (mem_univ _)
  obtain ⟨-, hform, hε⟩ := hcharts p₀ hp₀
  have hεpos : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, ⟨Ω, hΩ, himg⟩, hp₀img, -, hlogopen, hlogsm, hsub, hleft, -⟩ :=
    hε _ hεpos (by rw [Real.exp_log (by norm_num)])
  have hz : (0 : ComplexMatrix2.LieElement).toMatrix = 0 := rfl
  have hchart0 : expChartI p₀ 0 = p₀ := by
    rw [(hform 0).2.1]
    funext s
    simp [hz]
  have h0small : (0 : PositiveEdge L n k 0 → ComplexMatrix2.LieElement) ∈
      smallBall (PositiveEdge L n k 0) (Real.log (19 / 10)) := by
    intro s
    simpa [hz] using hεpos
  have hlog0 : logChart p₀ p₀ = 0 := by
    have hl := hleft 0 h0small
    rw [hchart0] at hl
    rw [hl]
    rfl
  have hl : ContDiffAt ℝ 2 (logChart p₀) p₀ :=
    (hlogsm.contDiffAt (hlogopen.mem_nhds (hsub hp₀img))).of_le ENat.LEInfty.out
  let c : ℝ → PositiveEdge L n k 0 → ComplexMatrix2 := fun t => restrictToPositiveEdges (γ t)
  have hc0 : c 0 = p₀ := by
    show restrictToPositiveEdges (γ 0) = restrictToPositiveEdges U
    rw [hγ0]
  have hc1 : ∀ t ∈ I, DifferentiableAt ℝ c t := fun t ht =>
    differentiableAt_pi.2 fun b => (hd b.1 b.2 t ht).differentiableAt (hI.1.mem_nhds ht)
  have hcd : ∀ t ∈ I, deriv c t = fun b => deriv (fun s => γ s b.1) t := fun t ht =>
    deriv_pi fun b => (hd b.1 b.2 t ht).differentiableAt (hI.1.mem_nhds ht)
  have hc2 : DifferentiableAt ℝ (deriv c) 0 := by
    have hb : DifferentiableAt ℝ (fun t (b : PositiveEdge L n k 0) =>
        deriv (fun s => γ s b.1) t) 0 :=
      differentiableAt_pi.2 fun b => (hdd b.1 b.2 0 hI.2.2).differentiableAt hI0
    exact hb.congr_of_eventuallyEq (Filter.eventually_of_mem hI0 hcd)
  have hc1' : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ c t := Filter.eventually_of_mem hI0 hc1
  obtain ⟨h1, h2⟩ := hasDerivAt_deriv_comp_of_contDiffAt (G := logChart p₀) (h := c)
    (by rwa [hc0]) hc1' hc2
  refine ⟨logChart p₀ ∘ c, ?_, h1, h2.differentiableAt, ?_, ?_⟩
  · show logChart p₀ (c 0) = 0
    rw [hc0, hlog0]
  · have hp₀Ω : p₀ ∈ Ω := (himg ▸ hp₀img : p₀ ∈ Ω ∩ _).1
    have hcΩ : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ Ω :=
      (hc1 0 hI.2.2).continuousAt.eventually (hΩ.mem_nhds (by rwa [hc0]))
    filter_upwards [hcΩ, hI0] with t ht htI
    have hcG : c t ∈ specialUnitaryPower (PositiveEdge L n k 0) :=
      fun b => (hmaps htI).1 b (mem_univ _)
    have hmem : c t ∈ expChartI p₀ '' smallBall (PositiveEdge L n k 0) (Real.log (19 / 10)) := by
      rw [himg]
      exact ⟨ht, hcG⟩
    obtain ⟨Y, hY, hYc⟩ := hmem
    have hx : (logChart p₀ ∘ c) t = fun s => (Y s).toMatrix := by
      show logChart p₀ (c t) = _
      rw [← hYc, hleft Y hY]
    rw [hx]
    refine ⟨fun b => (Y b).2, fun b => ?_⟩
    have := congrFun ((hform Y).2.1.symm.trans hYc) b
    exact this
  · have hdx : deriv (logChart p₀ ∘ c) 0 =
        fun b => deriv (fun t => (logChart p₀ ∘ c) t b) 0 :=
      deriv_pi fun b => differentiableAt_pi.1 h1.self_of_nhds b
    rw [hdx]
    funext b
    have hW := (hA.1 I hI).1 (fun t => γ t b.1) (fun t ht => (hmaps ht).1 b.1 (mem_univ _))
      ((hd b.1 b.2 0 hI.2.2).differentiableAt hI0)
    obtain ⟨-, hW1, hW2, -⟩ := hW
    have hfun : (fun t => (logChart p₀ ∘ c) t b) =
        fun t => (1 / Complex.I) • ComplexMatrix2.logSeries (γ t b.1 * (U b.1)⁻¹) := rfl
    rw [hfun]
    simp only [hγ0] at hW1 hW2
    have hder : HasDerivAt (fun t => (1 / Complex.I) • ComplexMatrix2.logSeries (γ t b.1 * (U b.1)⁻¹))
        ((1 / Complex.I) • deriv (fun t => ComplexMatrix2.logSeries (γ t b.1 * (U b.1)⁻¹)) 0) 0 :=
      hW1.hasDerivAt.const_smul (1 / Complex.I)
    rw [hder.deriv, one_div, hW2]
    have hval := congrFun hB b.1
    simp only [curveTangent, extendOddly, if_pos b.2, hγ0] at hval
    exact hval
end EvaluationMaps
section Conclusion
variable {L n k : ℕ}
def positiveValuesMap (L n k : ℕ) :
    edgeFormSpace L n k 0 →ₗ[ℝ] PositiveEdge L n k 0 → ComplexMatrix2 where
  toFun B := restrictToPositiveEdges (B : Edge L n k 0 → ComplexMatrix2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem edgeFormPairing_leftGradient (hF : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {U : Edge L n k 0 → ComplexMatrix2}
    (l : edgeFormSpace L n k 0 →ₗ[ℝ] ℝ)
    (hl : ∀ B : edgeFormSpace L n k 0, leftDeriv (fun V => (plaquetteAction L n k V : ℂ)) U
      (B : Edge L n k 0 → ComplexMatrix2) = ((l B : ℝ) : ℂ)) (ξ : edgeFormSpace L n k 0) :
    edgeFormPairing (leftGradient (fieldSpace L n k 0) (fun V => (plaquetteAction L n k V : ℂ)) U)
      (ξ : Edge L n k 0 → ComplexMatrix2) = ((l ξ : ℝ) : ℂ) := by
  obtain ⟨hfin, hfd, -, c, hc⟩ := hF L n k 0 hL hn (Nat.zero_le k)
  obtain ⟨g, hg⟩ := exists_inner_eq_linearMap c l
  have hex : ∃ X, IsLeftGradient (fieldSpace L n k 0) (fun V => (plaquetteAction L n k V : ℂ)) U X := by
    refine ⟨(g : Edge L n k 0 → ComplexMatrix2), ⟨fun b hb => (g.2.1 b hb).2, g.2.2⟩, fun _ => g.2,
      fun B hB _ => ?_⟩
    rw [hl ⟨B, hB⟩, ← hg, ← hc]
  have hspec := Classical.epsilon_spec hex
  have := hspec.2.2 ξ ξ.2 (Set.toFinite _)
  exact this.trans (hl ξ)
theorem leftSecondDeriv_eq_deriv_deriv {U B : Edge L n k 0 → ComplexMatrix2} :
    leftSecondDeriv (plaquetteAction L n k) U B B =
      deriv (deriv fun u : ℝ =>
        plaquetteAction L n k (PeriodicLattice.expTwist (algebraMap ℝ ℂ u • B) U)) 0 := by
  have key : ∀ s : ℝ, deriv (fun t : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B) U)) 0 =
      deriv (fun u : ℝ =>
        plaquetteAction L n k (PeriodicLattice.expTwist (algebraMap ℝ ℂ u • B) U)) s := by
    intro s
    have e : (fun t : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B) U)) = fun t : ℝ =>
        (fun u : ℝ => plaquetteAction L n k
          (PeriodicLattice.expTwist (algebraMap ℝ ℂ u • B) U)) (s + t) := by
      funext t
      simp only [map_add, add_smul]
    rw [e]
    exact (deriv_comp_const_add (fun u : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ u • B) U)) s 0).trans (by rw [add_zero])
  exact congrArg (fun f : ℝ → ℝ => deriv f 0) (funext key)
variable [Fintype (PositiveEdge L n k 0)] [Fintype (Face L n k 0)]
theorem line_hasDerivAt_and_deriv_deriv {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k 0) (B : Edge L n k 0 → ComplexMatrix2) :
    HasDerivAt (fun u : ℝ =>
        plaquetteAction L n k (PeriodicLattice.expTwist (algebraMap ℝ ℂ u • B) U))
      (fderiv ℝ (fun y => plaquetteAction L n k (twistedField U y)) 0
        (restrictToPositiveEdges B)) 0 ∧
    deriv (deriv fun u : ℝ =>
        plaquetteAction L n k (PeriodicLattice.expTwist (algebraMap ℝ ℂ u • B) U)) 0 =
      fderiv ℝ (fderiv ℝ fun y => plaquetteAction L n k (twistedField U y)) 0
        (restrictToPositiveEdges B) (restrictToPositiveEdges B) := by
  set ψ : (PositiveEdge L n k 0 → ComplexMatrix2) → ℝ :=
    fun y => plaquetteAction L n k (twistedField U y) with hψ
  let Bp := restrictToPositiveEdges B
  let h : ℝ → PositiveEdge L n k 0 → ComplexMatrix2 := fun u => u • Bp
  have hh : ∀ u, HasDerivAt h Bp u := fun u => by
    simpa using (hasDerivAt_id u).smul_const Bp
  have hd : deriv h = fun _ => Bp := funext fun u => (hh u).deriv
  have h0 : h 0 = 0 := by simp [h]
  have hcomp : (fun u : ℝ =>
      plaquetteAction L n k (PeriodicLattice.expTwist (algebraMap ℝ ℂ u • B) U)) = ψ ∘ h := by
    funext u
    show _ = plaquetteAction L n k (PeriodicLattice.expTwist (edgeFormOfPositiveValues (u • Bp)) U)
    rw [← expTwist_restrict (algebraMap ℝ ℂ u • B) U]
    congr 3
  have hψ2 : ContDiffAt ℝ 2 ψ (h 0) := by
    rw [h0]
    exact contDiffAt_plaquetteAction_twisted hU
  have hψ1 : DifferentiableAt ℝ ψ (h 0) := hψ2.differentiableAt (by norm_num)
  obtain ⟨-, h2⟩ := hasDerivAt_deriv_comp_of_contDiffAt hψ2
    (Filter.Eventually.of_forall fun u => (hh u).differentiableAt)
    (by rw [hd]; exact differentiableAt_const _)
  rw [hcomp]
  refine ⟨?_, ?_⟩
  · have := hψ1.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hh 0)
    rwa [h0] at this
  · rw [h2.deriv, hd, h0]
    simp
    rfl
end Conclusion
theorem statement_holds (hC : ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds)
    (hA : LeftChartFields.Claim)
    (hF : FiniteSideFormSpaces)
    (hT : QuotientLattices.TorusAndSpaceLatticeProperties) : LeftChartCurveAction.Statement := by
  intro L n k hL hn U hU I γ hγ hγ0 B hB
  obtain ⟨hfin, -⟩ := hF L n k 0 hL hn (Nat.zero_le k)
  let _ : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
  have hplaq : Finite (Face L n k 0) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h⟩ := (hT L hL n 0 k hn (Nat.zero_le k)).2.1
    exact h
  let _ : Fintype (Face L n k 0) := Fintype.ofFinite _
  have hne : Nonempty (PositiveEdge L n k 0) := by
    obtain ⟨-, ⟨b, -⟩, -⟩ := ((hE L hL k 0 (Nat.zero_le k)).1 n hn).2
    rcases isPositivelyOriented_or_opposite b with h | h
    · exact ⟨⟨b, h⟩⟩
    · exact ⟨⟨b.opposite, h⟩⟩
  have hnb := not_isPositivelyOriented_opposite (k := k) hT hL hn
  obtain ⟨x, hx0, hx1, hx2, hxr, hxB⟩ := exists_log_chart hC hA hγ hγ0 (B := B) hB
  have hsu : IsClosed (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2) :=
    Submodule.closed_of_finiteDimensional _
  obtain ⟨⟨hI, hmaps, -⟩, -⟩ := hγ
  have hI0 : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
  have hξ : ∀ b, deriv (deriv x) 0 b ∈ ComplexMatrix2.hermitianTraceless := by
    intro b
    have hdp : deriv (deriv x) 0 = fun b => deriv (fun t => deriv x t b) 0 :=
      deriv_pi fun b => differentiableAt_pi.1 hx2 b
    rw [hdp]
    refine deriv_mem_of_eventually_mem hsu ?_
    filter_upwards [hx1, eventually_eventually_nhds.2 hxr] with t ht1 ht2
    have hdt : deriv x t = fun b => deriv (fun s => x s b) t :=
      deriv_pi fun b => differentiableAt_pi.1 ht1 b
    rw [hdt]
    exact deriv_mem_of_eventually_mem hsu (ht2.mono fun s hs => hs.1 b)
  let ξ : edgeFormSpace L n k 0 :=
    ⟨edgeFormOfPositiveValues (deriv (deriv x) 0), edgeFormOfPositiveValues_mem hnb hξ⟩
  have hξp : restrictToPositiveEdges (ξ : Edge L n k 0 → ComplexMatrix2) = deriv (deriv x) 0 := by
    funext b
    exact edgeFormOfPositiveValues_of_pos _ b.2
  let X : ℝ → edgeFormSpace L n k 0 := fun t => open Classical in
    if h : ∀ b, x t b ∈ ComplexMatrix2.hermitianTraceless then
      ⟨edgeFormOfPositiveValues (x t), edgeFormOfPositiveValues_mem hnb h⟩ else 0
  have hXv : ∀ᶠ t in 𝓝 (0 : ℝ),
      (X t : Edge L n k 0 → ComplexMatrix2) = edgeFormOfPositiveValues (x t) :=
    hxr.mono fun t ht => by
      simp only [X]
      rw [dif_pos ht.1]
  have hread : ∀ᶠ t in 𝓝 (0 : ℝ), γ t = twistedField U (x t) := by
    filter_upwards [hxr, hI0] with t ht htI
    funext b
    by_cases h : b.IsPositivelyOriented
    · simp only [twistedField, PeriodicLattice.expTwist, if_pos h, edgeFormOfPositiveValues_of_pos _ h]
      exact (ht.2 ⟨b, h⟩).symm
    · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
      simp only [twistedField, PeriodicLattice.expTwist, if_neg h, edgeFormOfPositiveValues_of_pos _ h']
      rw [ht.2 ⟨b.opposite, h'⟩]
      exact (hmaps htI).2 b.opposite (mem_univ _)
  refine ⟨X, ξ, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hread, hXv] with t h1 h2
    rw [h1, h2]
    rfl
  · rw [tendsto_subtype_rng]
    have hxc : Tendsto x (𝓝 0) (𝓝 0) := by
      have := hx1.self_of_nhds.continuousAt.tendsto
      rwa [hx0] at this
    refine Tendsto.congr' (hXv.mono fun t ht => ht.symm) ?_
    refine tendsto_pi_nhds.2 fun b => ?_
    by_cases h : b.IsPositivelyOriented
    · simp only [edgeFormOfPositiveValues_of_pos _ h]
      exact tendsto_pi_nhds.1 hxc ⟨b, h⟩
    · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
      simp only [edgeFormOfPositiveValues_of_opposite _ h h']
      simpa using (tendsto_pi_nhds.1 hxc ⟨b.opposite, h'⟩).neg
  · obtain ⟨K, hK⟩ := exists_traceFinsumNorm_le (ι := PositiveEdge L n k 0)
    have hr := isLittleO_taylor_two hx1 hx2 hx0
    refine (IsBigO.of_bound |K| ?_).trans_isLittleO hr
    filter_upwards [hXv] with t hv
    have e : restrictToPositiveEdges ((X t - t • B - (t ^ 2 / 2) • ξ : edgeFormSpace L n k 0) :
        Edge L n k 0 → ComplexMatrix2) = x t - t • deriv x 0 - (t ^ 2 / 2) • deriv (deriv x) 0 := by
      rw [hxB, ← hξp]
      funext b
      simp only [Submodule.coe_sub, Submodule.coe_smul, hv]
      show edgeFormOfPositiveValues (x t) b.1 - _ - _ = _
      rw [edgeFormOfPositiveValues_of_pos _ b.2]
      rfl
    show ‖traceFinsumNorm (restrictToPositiveEdges _)‖ ≤ _
    rw [e, Real.norm_of_nonneg (show 0 ≤ traceFinsumNorm _ from Real.sqrt_nonneg _)]
    exact (hK _).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _))
  · have hψ2 : ContDiffAt ℝ 2 (fun y => plaquetteAction L n k (twistedField U y)) (x 0) := by
      rw [hx0]
      exact contDiffAt_plaquetteAction_twisted hU
    obtain ⟨-, h2⟩ := hasDerivAt_deriv_comp_of_contDiffAt hψ2 hx1 hx2
    have hnear : (fun t => plaquetteAction L n k (γ t)) =ᶠ[𝓝 0]
        (fun y => plaquetteAction L n k (twistedField U y)) ∘ x :=
      hread.mono fun t ht => by
        show plaquetteAction L n k (γ t) = plaquetteAction L n k (twistedField U (x t))
        rw [ht]
    have hlin := line_hasDerivAt_and_deriv_deriv hU
    let l : edgeFormSpace L n k 0 →ₗ[ℝ] ℝ :=
      (fderiv ℝ (fun y => plaquetteAction L n k (twistedField U y)) 0).toLinearMap ∘ₗ
        positiveValuesMap L n k
    have hl : ∀ B' : edgeFormSpace L n k 0, leftDeriv (fun V => (plaquetteAction L n k V : ℂ)) U
        (B' : Edge L n k 0 → ComplexMatrix2) = ((l B' : ℝ) : ℂ) := by
      intro B'
      exact (hlin (B' : Edge L n k 0 → ComplexMatrix2)).1.ofReal_comp.deriv
    rw [edgeFormPairing_leftGradient hF hL hn l hl ξ, leftSecondDeriv_eq_deriv_deriv, (hlin _).2,
      hnear.deriv.deriv_eq, h2.deriv, hx0, hxB]
    show _ = _ + ((fderiv ℝ (fun y => plaquetteAction L n k (twistedField U y)) 0
      (restrictToPositiveEdges (ξ : Edge L n k 0 → ComplexMatrix2)) : ℝ) : ℂ)
    rw [hξp]
    push_cast
    rfl
end YangMills.Construction.Tower.LeftChartCurveAction.SecondVariation
end
