import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSitesProof
import YangMills.Construction.Towers.HessianOfARestriction
import YangMills.Construction.Towers.RealAnalyticFunctionsAlongTwiceDifferentiableCurvesProof
import YangMills.Construction.Towers.TheFormOnAFibreOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Filter Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
  Matrices.PowerExpCharts
open scoped Topology ContDiff Matrix.Norms.L2Operator
namespace Tower
namespace FibreForm
theorem hessianForm_transfer {X T S : Type*} [AddCommGroup T] [Module ℝ T] [AddCommGroup S]
    [Module ℝ S] (R : Geometry.CurveData X T) {N : Set X} {F : X → ℝ} {x : X} (ι : S → T)
    (e : S →ₗ[ℝ] R.tangentSpan N x) (he : ∀ s, (e s : T) = ι s) (hinj : Function.Injective e)
    (hH : R.IsHessianFormAt Subtype.val N F x
      (R.hessianForm (S := R.tangentSpan N x) Subtype.val N F x))
    (hc : ∀ v ∈ R.tangentSpan N x, ∃ (I : Set ℝ) (γ : ℝ → X),
      R.IsTwiceDiffCurve I γ ∧ MapsTo γ I N ∧ γ 0 = x ∧ R.tangent γ = v)
    (hp : (R.hessianForm (S := R.tangentSpan N x) Subtype.val N F x).PosDef) :
    R.IsHessianFormAt ι N F x (R.hessianForm ι N F x) ∧ (R.hessianForm ι N F x).PosDef := by
  let Q₁ : QuadraticForm ℝ S :=
    (R.hessianForm (S := R.tangentSpan N x) Subtype.val N F x).comp e
  have h₁ : R.IsHessianFormAt ι N F x Q₁ := fun I γ v a b c d =>
    hH I γ (e v) a b c (d.trans (he v).symm)
  have h₂ : R.IsHessianFormAt ι N F x (R.hessianForm ι N F x) :=
    Classical.epsilon_spec (p := fun Q : QuadraticForm ℝ S => R.IsHessianFormAt ι N F x Q) ⟨Q₁, h₁⟩
  refine ⟨h₂, fun s hs => ?_⟩
  obtain ⟨I, γ, a, b, c, d⟩ := hc (ι s) (he s ▸ (e s).2)
  have heq : R.hessianForm ι N F x s = Q₁ s := (h₂ I γ s a b c d).trans (h₁ I γ s a b c d).symm
  rw [heq]
  exact hp (e s) fun h => hs (hinj (h.trans (map_zero e).symm))
section Powers
variable {σ : Type} [Fintype σ] [Nonempty σ]
theorem isChartedSubset_of_isOpenSubset (hC : ExpChartsStatement) {M : Set (σ → ComplexMatrix2)}
    (hM : specialUnitaryPower.IsOpenSubset M) : EmbeddedSubmanifold.IsChartedSubset M := by
  obtain ⟨Ω, hΩ, rfl⟩ := hM
  rintro p ⟨hpΩ, hp⟩
  obtain ⟨-, hform, hε⟩ := (hC σ σ).1 p hp
  have hεpos : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, -, c, ν, hdom, hpar⟩ :=
    hε _ hεpos (by rw [Real.exp_log (by norm_num)])
  have hz : (0 : ComplexMatrix2.LieElement).toMatrix = 0 := rfl
  have hfam : ofCoeffs (fun s a => (0 : Fin c.dim → ℝ) (ν (s, a))) =
      (0 : σ → ComplexMatrix2.LieElement) := by
    funext s
    simp [ofCoeffs]
  have h0 : (0 : Fin c.dim → ℝ) ∈ c.source := by
    rw [hdom]
    show ofCoeffs (fun s a => (0 : Fin c.dim → ℝ) (ν (s, a))) ∈
      smallBall σ (Real.log (19 / 10))
    rw [hfam]
    intro s
    simpa [hz] using hεpos
  have hchart0 : c.param 0 = p := by
    rw [hpar 0 h0, hfam, (hform 0).2.1]
    funext s
    simp [hz]
  let c' : EmbeddedSubmanifold.Chart (Ω ∩ specialUnitaryPower σ) :=
    { dim := c.dim
      source := c.source ∩ c.param ⁻¹' Ω
      param := c.param
      isOpen_source := c.contDiffOn_param.continuousOn.isOpen_inter_preimage
        c.isOpen_source hΩ
      contDiffOn_param := c.contDiffOn_param.mono inter_subset_left
      injective_fderiv_param := fun u hu => c.injective_fderiv_param u hu.1
      injOn_param := c.injOn_param.mono inter_subset_left
      isRelativelyOpen_image := by
        intro W hW hWo
        obtain ⟨O', hO', e⟩ := c.isRelativelyOpen_image W (hW.trans inter_subset_left) hWo
        refine ⟨O', hO', ?_⟩
        ext y
        constructor
        · intro hy
          have hy' := hy
          rw [e] at hy'
          obtain ⟨u, hu, rfl⟩ := hy
          exact ⟨hy'.1, (hW hu).2, hy'.2⟩
        · rintro ⟨h₁, -, h₂⟩
          rw [e]
          exact ⟨h₁, h₂⟩ }
  exact ⟨c', (0 : Fin c.dim → ℝ), ⟨h0, by
    show c.param 0 ∈ Ω
    rw [hchart0]
    exact hpΩ⟩, hchart0⟩
theorem isC2OnCharted_of_restriction (hC : ExpChartsStatement) {M : Set (σ → ComplexMatrix2)}
    (hM : specialUnitaryPower.IsOpenSubset M) {f : (σ → ComplexMatrix2) → ℝ}
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (hf : IsLocallyHolomorphicRestriction (HolomorphicScalar β) Complex.ofReal M f) :
    EmbeddedSubmanifold.IsC2OnCharted M f := by
  intro c
  obtain ⟨-, -, -, -, -, -, -, hread⟩ := hC σ σ
  have hs := (((hread β).1 M hM).1 f hf).1.2
  obtain ⟨Ω, hΩ, hMe⟩ := hM
  let c' : EmbeddedSubmanifold.Chart (specialUnitaryPower σ) :=
    { c with
      isRelativelyOpen_image := by
        intro W hW hWo
        obtain ⟨O', hO', e⟩ := c.isRelativelyOpen_image W hW hWo
        refine ⟨O' ∩ Ω, hO'.inter hΩ, ?_⟩
        rw [e, hMe, inter_assoc] }
  have hsub : c.source ⊆ c'.coords M := by
    intro u hu
    refine ⟨hu, ?_⟩
    obtain ⟨O', -, e⟩ := c.isRelativelyOpen_image c.source subset_rfl c.isOpen_source
    have : c.param u ∈ c.param '' c.source := mem_image_of_mem _ hu
    rw [e] at this
    exact this.2
  exact ((hs c').mono hsub).of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
    WithTop.coe_le_coe.2 le_top)
end Powers
section Fields
variable {L n k i j : ℕ}
private theorem fieldOfPositiveValues_restrict {V : Edge L n k i → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k i) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
private theorem nonempty_positiveEdge (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Nonempty (PositiveEdge L n k j) := by apply _root_.YangMills.SharedProofs.p12312 <;> assumption
private theorem holomorphicScalar_of_coords {σ : Type} [Fintype σ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (h : IsHolomorphicToCoords b (Equiv.refl _) W Φ) :
    HolomorphicScalar b W fun q => Φ q 0 := by apply _root_.YangMills.SharedProofs.p9409 <;> assumption
theorem submanifold_and_c2_of_analytic (hC : ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    {F : (Edge L n k j → ComplexMatrix2) → ℝ} (hF : IsAnalyticFieldFunction 𝒰 F) :
    ∃ _ : Fintype (PositiveEdge L n k j), IsFieldSubmanifold 𝒰 ∧
      EmbeddedSubmanifold.IsC2OnCharted (restrictToPositiveEdges '' 𝒰)
        fun w => F (fieldOfPositiveValues w) := by
  obtain ⟨hopen, f₁, hra⟩ := hF
  let := f₁
  have := nonempty_positiveEdge hE hL hn hj
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  have hO : specialUnitaryPower.IsOpenSubset (restrictToPositiveEdges '' 𝒰) := hopen.2
  have hconf : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => fieldOfPositiveValues_restrict (hopen.1 hU)
  refine ⟨f₁, ⟨hopen.1, f₁, isChartedSubset_of_isOpenSubset hC hO⟩,
    isC2OnCharted_of_restriction hC hO β ?_⟩
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
theorem hessian_and_curves_at_critical [Fintype (PositiveEdge L n k j)]
    (hY : RestrictionHessian.Statement)
    {𝒳 N : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h𝒳 : IsFieldSubmanifold 𝒳) (hN : IsFieldSubmanifold N) (hsub : N ⊆ 𝒳)
    (hF : EmbeddedSubmanifold.IsC2OnCharted (restrictToPositiveEdges '' 𝒳)
      fun w => F (fieldOfPositiveValues w))
    {x : Edge L n k j → ComplexMatrix2} (hx : (fieldCurveData L n k j).IsCriticalOn N F x) :
    (fieldCurveData L n k j).IsHessianFormAt Subtype.val N F x
        ((fieldCurveData L n k j).hessianForm (S := (fieldCurveData L n k j).tangentSpan N x)
          Subtype.val N F x) ∧
      ∀ v ∈ (fieldCurveData L n k j).tangentSpan N x, ∃ (I : Set ℝ)
        (γ : ℝ → Edge L n k j → ComplexMatrix2), (fieldCurveData L n k j).IsTwiceDiffCurve I γ ∧
        MapsTo γ I N ∧ γ 0 = x ∧ (fieldCurveData L n k j).tangent γ = v := by
  obtain ⟨hread, hex, -, -⟩ := hY.2 L n k j 𝒳 N F h𝒳 hN hsub hF
  obtain ⟨d, O, φ, z, hφ, hz, rfl⟩ := hex x hx.1
  obtain ⟨D, -, hR⟩ := hread (Fin d → ℝ) O φ z hφ hz
  exact ⟨hR.hessianForm_isHessianFormAt hx, hR.exists_curve hx⟩
private theorem eventually_mem_of_isOpenNhdOfOne {𝒰 : Set (Edge L n k i → ComplexMatrix2)}
    (h : IsOpenNhdOfOne 𝒰) :
    ∀ᶠ V in 𝓝[fieldSpace L n k i] trivialField L n k i, V ∈ 𝒰 := by apply _root_.YangMills.Construction.Tower.ProlongCompositesProof.eventually_mem_of_isOpenNhdOfOne <;> assumption
private theorem continuousOn_of_isAnalyticFieldMap {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k i → ComplexMatrix2}
    (h : IsAnalyticFieldMap 𝒰 m) : ContinuousOn m 𝒰 := by apply _root_.YangMills.Construction.Tower.ProlongCompositesProof.continuousOn_of_isAnalyticFieldMap <;> assumption
theorem tendsto_prolong {b : CriticalBranchData L n k} (hb : b.IsCritical) (hi : i < k) :
    Tendsto (b.prolong i) (𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1))
      (𝓝[fieldSpace L n k i] trivialField L n k i) := by
  obtain ⟨𝒰, hU, hA⟩ := hb.analytic_prolong i hi
  have hnear := eventually_mem_of_isOpenNhdOfOne hU
  have hc := continuousOn_of_isAnalyticFieldMap hA _ hU.2
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, hnear.mono fun W hW => hA.2.1 hW⟩
  have h := hc.tendsto.mono_left
    (nhdsWithin_le_of_mem (Filter.mem_of_superset hnear fun _ h => h))
  rwa [hb.prolong_trivial i hi] at h
end Fields
end FibreForm
open FibreForm in
theorem criticalFibreHessianPosDef_holds (hB : CriticalBranchExists)
    (hN : FibreNeighbourhoodsOfSteps) (hY : RestrictionHessian.Statement)
    (hT : LeftChartStepExpansion)
    (hC : ExpChartsStatement)
    (hE : BondSetFields.ProductStructureHolds) :
    CriticalFibreHessianPosDef := by
  intro L n k hL hn i hi
  have hik : i < k := hi
  have hb : (chosenCriticalBranch L n k).IsCritical := Classical.epsilon_spec (hB L n k hL hn)
  have hU : (chosenCriticalBranch L n k).IsFibreNhd i (chosenFibreNhd L n k i) :=
    Classical.epsilon_spec (hN.2.2.2 L n k hL hn (by omega) _ hb i hik)
  obtain ⟨f₁, h𝒰, hF2⟩ :=
    submanifold_and_c2_of_analytic hC hE hL hn hik.le hU.analytic_gaugeFixedEnergy
  let := f₁
  have hcp := hU.unique_critical
  have htv := hT L n k i hL hn hi
  unfold EventuallyNearIdentity at hcp htv ⊢
  filter_upwards [hcp, self_mem_nhdsWithin, (tendsto_prolong hb hik).eventually htv] with W hcW hW hV
  obtain ⟨⟨hVN, hVc, -⟩, hpd⟩ := hcW
  rcases hU.fibre_structure W hW with he | ⟨hNa, hker⟩
  · rw [he] at hVN
    exact hVN.elim
  have hspec : ∀ B : edgeFormSpace L n k i,
      (constraintDifferential L n k i W B : Edge L n k (i + 1) → ComplexMatrix2) =
        leftDifferential (smoothingStep L n k i) (chosenProlong L n k i W) B :=
    Classical.epsilon_spec hV.2.1.2.1
  let e : LinearMap.ker (constraintDifferential L n k i W) →ₗ[ℝ]
      (fieldCurveData L n k i).tangentSpan (chosenLevelFibre L n k i W)
        (chosenProlong L n k i W) :=
    LinearMap.codRestrict _ ((edgeFormSpace L n k i).subtype ∘ₗ (LinearMap.ker _).subtype)
      fun B => (hker _ hVN B.1.1).2 ⟨B.1.2, (hspec B.1).symm.trans (by
        rw [LinearMap.mem_ker.1 B.2]
        rfl)⟩
  have hinj : Function.Injective e := by
    intro a b h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  obtain ⟨hHv, hcurves⟩ := hessian_and_curves_at_critical hY h𝒰 hNa.1 (fun x hx => hx.1) hF2 hVc
  obtain ⟨hH, hpos⟩ := hessianForm_transfer (fieldCurveData L n k i)
    (fun B : LinearMap.ker (constraintDifferential L n k i W) => B.1.1) e
    (fun _ => rfl) hinj hHv hcurves hpd
  refine ⟨hVc, fun y => ?_, hH, fun B => hcurves B.1.1 (e B).2, hpos⟩
  obtain ⟨B, hBf, hBy⟩ := hU.differential_surjective _ hVN.1 y.1 y.2
  exact ⟨⟨B, hBf⟩, Subtype.ext ((hspec _).trans hBy)⟩
end Tower
end YangMills.Construction
end
