import YangMills.Construction.Lattice.CombSchemeGaugeLawAndConjugationProof
import YangMills.Construction.Towers.AveragingOnSmallFamiliesOfTheChartAtOneProof
import YangMills.Construction.Towers.ChartAtOneOnTheConfigurationsProof
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.CriticalBranchAtTheBottomLevelProof
import YangMills.Construction.Towers.CurvesAtAFiniteSideInTheLeftChart
import YangMills.Construction.Towers.RealAnalyticFunctionsAlongTwiceDifferentiableCurvesProof
import YangMills.Construction.Towers.RealAnalyticMapsAlongPaths
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces YangMills.Construction.Matrices.PowerExpCharts
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.AlongCurvesProof
section Power
variable {σ : Type} [Fintype σ]
private theorem exists_clm_retraction_lieElement :
    ∃ P : ComplexMatrix2 →L[ℝ] ComplexMatrix2.LieElement,
      ∀ Y : ComplexMatrix2.LieElement, P Y.toMatrix = Y := by apply _root_.YangMills.Construction.Matrices.specialUnitaryPower.Composition.exists_clm_leftInverse_toMatrix <;> assumption
private theorem exists_local_inverse_expChartI (hc : PowerCharts σ) {p₀ : σ → ComplexMatrix2}
    (hp₀ : p₀ ∈ specialUnitaryPower σ) :
    ∃ G : (σ → ComplexMatrix2) → σ → ComplexMatrix2.LieElement, DifferentiableAt ℝ G p₀ ∧ G p₀ = 0 ∧
      ∀ᶠ x in 𝓝[specialUnitaryPower σ] p₀, expChartI p₀ (G x) = x := by
  obtain ⟨-, hform, hε⟩ := hc p₀ hp₀
  have hεpos : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, ⟨Ω, hΩ, himg⟩, hp₀img, -, hlogopen, hlogsm, hsub, hleft, -⟩ :=
    hε _ hεpos (by rw [Real.exp_log (by norm_num)])
  obtain ⟨P, hP⟩ := exists_clm_retraction_lieElement
  have hz : (0 : ComplexMatrix2.LieElement).toMatrix = 0 := rfl
  have hchart0 : expChartI p₀ 0 = p₀ := by
    rw [(hform 0).2.1]
    funext s
    simp [hz]
  have h0small : (0 : σ → ComplexMatrix2.LieElement) ∈ smallBall σ (Real.log (19 / 10)) := by
    intro s
    simpa [hz] using hεpos
  refine ⟨fun X s => P (logChart p₀ X s), ?_, ?_, ?_⟩
  · have hl : DifferentiableAt ℝ (logChart p₀) p₀ :=
      (hlogsm.contDiffAt (hlogopen.mem_nhds (hsub hp₀img))).differentiableAt (by simp)
    exact differentiableAt_pi.2 fun s =>
      P.differentiableAt.comp p₀ (differentiableAt_pi.1 hl s)
  · funext s
    have hl := congrFun (hleft 0 h0small) s
    rw [hchart0] at hl
    show P (logChart p₀ p₀ s) = 0
    rw [hl]
    exact hP 0
  · have hp₀Ω : p₀ ∈ Ω := (himg ▸ hp₀img : p₀ ∈ Ω ∩ _).1
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hΩ.mem_nhds hp₀Ω), self_mem_nhdsWithin] with
      x hx hxG
    have hmem : x ∈ expChartI p₀ '' smallBall σ (Real.log (19 / 10)) := by
      rw [himg]
      exact ⟨hx, hxG⟩
    obtain ⟨Y, hY, rfl⟩ := hmem
    have hGY : (fun s => P (logChart p₀ (expChartI p₀ Y) s)) = Y := by
      funext s
      rw [hleft Y hY]
      exact hP (Y s)
    show expChartI p₀ (fun s => P (logChart p₀ (expChartI p₀ Y) s)) = _
    rw [hGY]
private theorem exists_clm_deriv_along_power {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hc : PowerCharts σ) (hr : ReadInCharts σ F) {O : Set (σ → ComplexMatrix2)}
    {f : (σ → ComplexMatrix2) → F} (hO : specialUnitaryPower.IsOpenSubset O)
    (hf : EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) O f)
    {p₀ : σ → ComplexMatrix2} (hp : p₀ ∈ O) (hpG : p₀ ∈ specialUnitaryPower σ) :
    ContinuousWithinAt f (specialUnitaryPower σ) p₀ ∧
      ∃ A : (σ → ComplexMatrix2) →L[ℝ] F, ∀ (c : ℝ → σ → ComplexMatrix2) (v : σ → ComplexMatrix2),
        HasDerivAt c v 0 → c 0 = p₀ → (∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ specialUnitaryPower σ) →
          HasDerivAt (fun t => f (c t)) (A v) 0 := by
  obtain ⟨G, hGd, hG0, hGx⟩ := exists_local_inverse_expChartI hc hpG
  obtain ⟨N, hN, -, hd⟩ := (hr O f hO).2.1.1 hf p₀ hp
  have hφ : DifferentiableAt ℝ (f ∘ expChartI p₀) (G p₀) := by
    rw [hG0]
    exact hd.differentiableAt hN
  refine ⟨?_, (fderiv ℝ (f ∘ expChartI p₀) (G p₀)).comp (fderiv ℝ G p₀), ?_⟩
  · have h1 : ContinuousAt (fun x => (f ∘ expChartI p₀) (G x)) p₀ :=
      ContinuousAt.comp (g := f ∘ expChartI p₀) hφ.continuousAt hGd.continuousAt
    refine h1.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hGx] with x hx
      show f x = f (expChartI p₀ (G x))
      rw [hx]
    · show f p₀ = f (expChartI p₀ (G p₀))
      rw [hGx.self_of_nhdsWithin hpG]
  · intro c v hcv hc0 hev
    have hG' : HasFDerivAt G (fderiv ℝ G p₀) (c 0) := by
      rw [hc0]
      exact hGd.hasFDerivAt
    have h1 : HasDerivAt (fun t => G (c t)) (fderiv ℝ G p₀ v) 0 := hG'.comp_hasDerivAt 0 hcv
    have hφ' : HasFDerivAt (f ∘ expChartI p₀) (fderiv ℝ (f ∘ expChartI p₀) (G p₀)) (G (c 0)) := by
      rw [hc0]
      exact hφ.hasFDerivAt
    have h2 := hφ'.comp_hasDerivAt 0 h1
    refine h2.congr_of_eventuallyEq ?_
    have ht : Tendsto c (𝓝 0) (𝓝[specialUnitaryPower σ] p₀) :=
      tendsto_nhdsWithin_iff.2 ⟨hc0 ▸ hcv.continuousAt.tendsto, hev⟩
    filter_upwards [ht.eventually hGx] with t h
    show f (c t) = f (expChartI p₀ (G (c t)))
    rw [h]
end Power
section Edges
variable {L n k j : ℕ}
private theorem positive_or_opposite_positive (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem positiveEdge_nonempty : Nonempty (PositiveEdge L n k j) := by apply _root_.YangMills.Construction.Tower.IdentityChart.nonempty_positiveEdge <;> assumption
private theorem fieldOfPositiveValues_restrict {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
private theorem edgeForm_ext {A A' : Edge L n k j → ComplexMatrix2} (hA : A ∈ edgeFormSpace L n k j)
    (hA' : A' ∈ edgeFormSpace L n k j)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → A b = A' b) : A = A' := by
  funext b
  rcases positive_or_opposite_positive b with hb | hb
  · exact h b hb
  · have hrr : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
    have h1 := hA.2 b.opposite
    have h2 := hA'.2 b.opposite
    rw [hrr] at h1 h2
    rw [h1, h2, h _ hb]
abbrev _root_.YangMills.SharedProofs.p88895 := @edgeForm_ext
private theorem inv_mul_self_of_mem_gauge {u : ComplexMatrix2}
    (hu : u ∈ PeriodicLattice.compactGaugeGroup) : u⁻¹ * u = 1 := by apply _root_.YangMills.SharedProofs.p14555 <;> assumption
private def rotatedFamily (U B : Edge L n k j → ComplexMatrix2) : PositiveEdge L n k j → ComplexMatrix2 :=
  fun b => (Complex.I • B b) * U b
private theorem rotatedFamily_add (U B B' : Edge L n k j → ComplexMatrix2) :
    rotatedFamily U (B + B') = rotatedFamily U B + rotatedFamily U B' := by
  funext b
  simp [rotatedFamily, smul_add, add_mul]
private theorem rotatedFamily_smul (U B : Edge L n k j → ComplexMatrix2) (r : ℝ) :
    rotatedFamily U (r • B) = r • rotatedFamily U B := by
  funext b
  simp only [rotatedFamily, Pi.smul_apply]
  rw [smul_comm, smul_mul_assoc]
private theorem deriv_apply_of_positive {δ : ℝ → Edge L n k j → ComplexMatrix2}
    (h0 : δ 0 ∈ fieldSpace L n k j) {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    deriv (fun t => δ t b) 0 = (Complex.I • curveTangent δ b) * δ 0 b := by
  have hu : (δ 0 b)⁻¹ * δ 0 b = 1 := inv_mul_self_of_mem_gauge (h0.1 b (mem_univ _))
  simp only [curveTangent, extendOddly, if_pos hb]
  rw [smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, mul_assoc, hu, mul_one]
private theorem eventually_mem_of_isOpenFieldSet (hP : diffAtZeroPathsStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} (h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰)
    {δ : ℝ → Edge L n k j → ComplexMatrix2} (hδ : IsDiffAtZeroPath δ) (h0 : δ 0 ∈ 𝒰) :
    ∀ᶠ t in 𝓝 (0 : ℝ), δ t ∈ 𝒰 := by
  obtain ⟨h1, h2, -⟩ := hP L n k j hL hn hj
  exact (h1 δ hδ).2.eventually_mem (h2 𝒰 h𝒰 _ h0)
private theorem hasDerivAt_comp_of_restrict [Fintype (PositiveEdge L n k j)] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hP : diffAtZeroPathsStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} (h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰)
    {U : Edge L n k j → ComplexMatrix2} (hU : U ∈ 𝒰) {f : (PositiveEdge L n k j → ComplexMatrix2) → F}
    {A : (PositiveEdge L n k j → ComplexMatrix2) →L[ℝ] F}
    (hA : ∀ (c : ℝ → PositiveEdge L n k j → ComplexMatrix2) (v : PositiveEdge L n k j → ComplexMatrix2),
      HasDerivAt c v 0 → c 0 = restrictToPositiveEdges U →
        (∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ specialUnitaryPower (PositiveEdge L n k j)) →
          HasDerivAt (fun t => f (c t)) (A v) 0)
    {g : (Edge L n k j → ComplexMatrix2) → F} (hg : ∀ V ∈ 𝒰, f (restrictToPositiveEdges V) = g V)
    {δ : ℝ → Edge L n k j → ComplexMatrix2} (hδ : IsDiffAtZeroPath δ) (h0 : δ 0 = U) :
    HasDerivAt (fun t => g (δ t)) (A (rotatedFamily U (curveTangent δ))) 0 := by
  have hU' : δ 0 ∈ fieldSpace L n k j := by
    rw [h0]
    exact h𝒰.1 hU
  have hc : HasDerivAt (fun t => restrictToPositiveEdges (δ t))
      (rotatedFamily U (curveTangent δ)) 0 := by
    refine hasDerivAt_pi.2 fun b => ?_
    have h := (hδ.2 b.1 b.2).hasDerivAt
    rw [deriv_apply_of_positive hU' b.2, h0] at h
    exact h
  have hev := eventually_mem_of_isOpenFieldSet hP hL hn hj h𝒰 hδ (h0 ▸ hU)
  refine (hA _ _ hc (by simp only [h0])
    (hδ.1.mono fun t ht b => ht.1 b.1 (mem_univ _))).congr_of_eventuallyEq ?_
  filter_upwards [hev] with t ht
  exact (hg _ ht).symm
end Edges
section Maps
variable {L n k a b : ℕ}
private theorem continuousWithinAt_of_positiveEdges {Y : Type} [TopologicalSpace Y]
    {m : Y → Edge L n k b → ComplexMatrix2} {s : Set Y} {y : Y} (hy : y ∈ s)
    (hconf : MapsTo m s (fieldSpace L n k b))
    (hpos : ∀ c : Edge L n k b, c.IsPositivelyOriented →
      ContinuousWithinAt (fun y => m y c) s y) :
    ContinuousWithinAt m s y := by apply _root_.YangMills.Construction.Tower.IdentityLieBallSmoothing.continuousWithinAt_of_positivelyOriented <;> assumption
private theorem analyticMap_along_curves (hC : ExpChartsStatement)
    (hLc : LeftChartFields.Claim)
    (hCv : FiniteLevelCurveDifferentials.Statement)
    (hD : AnalyticMapDifferentiableStatement)
    (hP : diffAtZeroPathsStatement) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (ha : a ≤ k) (hb : b ≤ k) {𝒰 : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k b → ComplexMatrix2}
    (hm : IsAnalyticFieldMap 𝒰 m) :
    ContinuousOn m 𝒰 ∧ ∀ U ∈ 𝒰,
      (∀ B : edgeFormSpace L n k a,
        (leftDifferentialLinear m U B : Edge L n k b → ComplexMatrix2) = leftDifferential m U B) ∧
      ∀ δ : ℝ → Edge L n k a → ComplexMatrix2, IsDiffAtZeroPath δ → δ 0 = U →
        IsDiffAtZeroPath (fun t => m (δ t)) ∧
          curveTangent (fun t => m (δ t)) = leftDifferential m U (curveTangent δ) := by
  have hdm := hD L n k a b hL hn ha hb 𝒰 m hm
  obtain ⟨hopen, hmaps, f₁, f₂, hInto⟩ := hdm
  let := f₁
  let := f₂
  have : Nonempty (PositiveEdge L n k a) := positiveEdge_nonempty
  have : Nonempty (PositiveEdge L n k b) := positiveEdge_nonempty
  obtain ⟨hcharts, -, -, hrM, -, -, hmem, -⟩ := hC (PositiveEdge L n k a) (PositiveEdge L n k b)
  have hO : specialUnitaryPower.IsOpenSubset (restrictToPositiveEdges '' 𝒰) := hopen.2
  have hconf : ∀ {V}, V ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges V) = V :=
    fun hV => fieldOfPositiveValues_restrict (hopen.1 hV)
  have hpow : ∀ {V}, V ∈ 𝒰 → restrictToPositiveEdges V ∈ specialUnitaryPower (PositiveEdge L n k a) :=
    fun hV c => (hopen.1 hV).1 c (mem_univ _)
  have hgc := (hmem _ _ hO hInto.2).1 hInto
  have hval : ∀ (c : PositiveEdge L n k b), ∀ V ∈ 𝒰,
      restrictToPositiveEdges (m (fieldOfPositiveValues (restrictToPositiveEdges V))) c = m V c.1 := by
    intro c V hV
    rw [hconf hV]
    rfl
  have hder := fun (U) (hU : U ∈ 𝒰) (c : PositiveEdge L n k b) =>
    exists_clm_deriv_along_power hcharts hrM hO (hgc c) (mem_image_of_mem _ hU) (hpow hU)
  refine ⟨fun V hV => continuousWithinAt_of_positiveEdges hV hmaps fun c hc => ?_, fun U hU => ?_⟩
  · have hρ : ContinuousWithinAt
        (restrictToPositiveEdges :
          (Edge L n k a → ComplexMatrix2) → PositiveEdge L n k a → ComplexMatrix2) 𝒰 V :=
      (continuous_pi fun _ => continuous_apply _).continuousWithinAt
    have h2 := ContinuousWithinAt.comp (hder V hV ⟨c, hc⟩).1 hρ fun V' h' => hpow h'
    exact h2.congr (fun V' h' => (hval ⟨c, hc⟩ V' h').symm) (hval ⟨c, hc⟩ V hV).symm
  · choose A hA using fun c => (hder U hU c).2
    have hpath : ∀ δ : ℝ → Edge L n k a → ComplexMatrix2, IsDiffAtZeroPath δ → δ 0 = U →
        ∀ c : PositiveEdge L n k b,
          HasDerivAt (fun t => m (δ t) c.1) (A c (rotatedFamily U (curveTangent δ))) 0 :=
      fun δ hδ h0 c => hasDerivAt_comp_of_restrict (g := fun V => m V c.1)
        (f := fun w => restrictToPositiveEdges (m (fieldOfPositiveValues w)) c) hP hL hn ha hopen hU
        (hA c) (hval c) hδ h0
    have hpathm : ∀ δ : ℝ → Edge L n k a → ComplexMatrix2, IsDiffAtZeroPath δ → δ 0 = U →
        IsDiffAtZeroPath (fun t => m (δ t)) := fun δ hδ h0 =>
      ⟨(eventually_mem_of_isOpenFieldSet hP hL hn ha hopen hδ (h0 ▸ hU)).mono fun t ht => hmaps ht,
        fun c hc => (hpath δ hδ h0 ⟨c, hc⟩).differentiableAt⟩
    have hvalue : ∀ δ : ℝ → Edge L n k a → ComplexMatrix2, IsDiffAtZeroPath δ → δ 0 = U →
        ∀ (c : Edge L n k b) (hc : c.IsPositivelyOriented), curveTangent (fun t => m (δ t)) c =
          Complex.I⁻¹ • (A ⟨c, hc⟩ (rotatedFamily U (curveTangent δ)) * (m U c)⁻¹) := by
      intro δ hδ h0 c hc
      simp only [curveTangent, extendOddly, if_pos hc]
      have h := (hpath δ hδ h0 ⟨c, hc⟩).deriv
      simp only [curveTangent] at h
      rw [h, h0]
    have hT := ((hLc.2.2 L k a hL ha).1 n hn).1.2.1 U (hopen.1 hU)
    have hcurve : ∀ B ∈ edgeFormSpace L n k a, ∃ γ : ℝ → Edge L n k a → ComplexMatrix2,
        IsDiffAtZeroPath γ ∧ γ 0 = U ∧ curveTangent γ = B ∧
          curveTangent (fun t => m (γ t)) = leftDifferential m U B := by
      intro B hB
      have key : ∃ (I : Set ℝ) (γ : ℝ → Edge L n k a → ComplexMatrix2),
          IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ ∧ γ 0 = U ∧
            ∀ c : PositiveEdge L n k a, deriv (fun t => γ t c.1) 0 = rotatedFamily U B c :=
        (hT.1 (rotatedFamily U B)).2 ⟨B, hB, fun c => rfl⟩
      obtain ⟨I, γ, hc, h0, hd⟩ := key
      have hIn : I ∈ 𝓝 (0 : ℝ) := hc.1.1.mem_nhds hc.1.2.2
      have hγ : IsDiffAtZeroPath γ :=
        ⟨eventually_of_mem hIn fun t ht => hc.2.1 ht,
          fun c hc' => (hc.2.2 c hc').differentiableAt hIn⟩
      have hU' : γ 0 ∈ fieldSpace L n k a := by
        rw [h0]
        exact hopen.1 hU
      have htan : curveTangent γ = B := by
        refine hT.2 _ ((hP L n k a hL hn ha).1 γ hγ).1 _ hB fun c => ?_
        have h := deriv_apply_of_positive hU' c.2
        rw [h0] at h
        exact h.symm.trans (hd c)
      refine ⟨γ, hγ, h0, htan, ?_⟩
      have hmt := ((hCv L k a b hL ha hb n hn).1 𝒰 m
        (hD L n k a b hL hn ha hb 𝒰 m hm) U hU I γ hc h0).2
      rw [hmt, htan]
    have hform : ∀ B ∈ edgeFormSpace L n k a, ∀ (c : Edge L n k b) (hc : c.IsPositivelyOriented),
        leftDifferential m U B c =
          Complex.I⁻¹ • (A ⟨c, hc⟩ (rotatedFamily U B) * (m U c)⁻¹) := by
      intro B hB c hc
      obtain ⟨γ, hγ, h0, htan, e⟩ := hcurve B hB
      rw [← e, hvalue γ hγ h0 c hc, htan]
    have hmf : ∀ B ∈ edgeFormSpace L n k a, leftDifferential m U B ∈ edgeFormSpace L n k b := by
      intro B hB
      obtain ⟨γ, hγ, h0, -, e⟩ := hcurve B hB
      rw [← e]
      exact ((hP L n k b hL hn hb).1 _ (hpathm γ hγ h0)).1
    refine ⟨?_, fun δ hδ h0 => ⟨hpathm δ hδ h0, ?_⟩⟩
    · let T : edgeFormSpace L n k a →ₗ[ℝ] edgeFormSpace L n k b :=
        { toFun := fun B => ⟨leftDifferential m U B, hmf B B.2⟩
          map_add' := fun B B' => Subtype.ext (edgeForm_ext (hmf _ (B + B').2)
            (add_mem (hmf _ B.2) (hmf _ B'.2)) fun c hc => by
              show leftDifferential m U ((B : Edge L n k a → ComplexMatrix2) + B') c =
                leftDifferential m U B c + leftDifferential m U B' c
              rw [hform _ (add_mem B.2 B'.2) c hc, hform _ B.2 c hc, hform _ B'.2 c hc,
                rotatedFamily_add, map_add, add_mul, smul_add])
          map_smul' := fun r B => Subtype.ext (edgeForm_ext (hmf _ (r • B).2)
            (Submodule.smul_mem _ r (hmf _ B.2)) fun c hc => by
              show leftDifferential m U (r • (B : Edge L n k a → ComplexMatrix2)) c =
                r • leftDifferential m U B c
              rw [hform _ (Submodule.smul_mem _ r B.2) c hc, hform _ B.2 c hc, rotatedFamily_smul,
                map_smul, smul_mul_assoc, smul_comm]) }
      exact fun B => Classical.epsilon_spec
        (p := fun T : edgeFormSpace L n k a →ₗ[ℝ] edgeFormSpace L n k b =>
          ∀ B : edgeFormSpace L n k a,
            (T B : Edge L n k b → ComplexMatrix2) = leftDifferential m U B)
        ⟨T, fun B => rfl⟩ B
    · have hTf := ((hP L n k a hL hn ha).1 δ hδ).1
      refine edgeForm_ext ((hP L n k b hL hn hb).1 _ (hpathm δ hδ h0)).1 (hmf _ hTf) fun c hc => ?_
      rw [hvalue δ hδ h0 c hc, hform _ hTf c hc]
end Maps
section Functions
variable {L n k j : ℕ}
private theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
private theorem holomorphicScalar_of_coords {σ : Type} [Fintype σ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → Coordinates.ComplexCoordinates 1}
    (h : IsHolomorphicToCoords b (Equiv.refl _) W Φ) :
    HolomorphicScalar b W fun q => Φ q 0 := by apply _root_.YangMills.SharedProofs.p9409 <;> assumption
private theorem exists_inner_representative {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (c : InnerProductSpace.Core ℝ V) (l : V →ₗ[ℝ] ℝ) :
    ∃ X : V, ∀ B : V, c.inner X B = l B := by apply _root_.YangMills.Construction.Tower.BottomLevel.exists_inner_eq <;> assumption
private theorem exists_gradient_along_curves (hC : ExpChartsStatement)
    (hS : FiniteSideFormSpaces) (hP : diffAtZeroPathsStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℝ}
    (hF : IsAnalyticFieldFunction 𝒰 F) {U : Edge L n k j → ComplexMatrix2} (hU : U ∈ 𝒰) :
    ∃ X ∈ edgeFormSpace L n k j, ∀ δ : ℝ → Edge L n k j → ComplexMatrix2, IsDiffAtZeroPath δ →
      δ 0 = U → HasDerivAt (fun t => F (δ t)) (edgeFormPairing X (curveTangent δ)).re 0 := by
  obtain ⟨hopen, f₁, hra⟩ := hF
  let := f₁
  have : Nonempty (PositiveEdge L n k j) := positiveEdge_nonempty
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  obtain ⟨hcharts, hrR, -, -, -, -, -, hread⟩ := hC (PositiveEdge L n k j) (PositiveEdge L n k j)
  have hO : specialUnitaryPower.IsOpenSubset (restrictToPositiveEdges '' 𝒰) := hopen.2
  have hconf : ∀ {V}, V ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges V) = V :=
    fun hV => fieldOfPositiveValues_restrict (hopen.1 hV)
  let f : (PositiveEdge L n k j → ComplexMatrix2) → ℝ := fun w => F (fieldOfPositiveValues w)
  have hrest : IsLocallyHolomorphicRestriction (HolomorphicScalar β) Complex.ofReal
      (restrictToPositiveEdges '' 𝒰) f := by
    rintro _ ⟨V, hV, rfl⟩
    have hq : asGroupFactors (restrictToPositiveEdges V) ∈
        {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges V) ∈ 𝒰
      rw [hconf hV]
      exact hV
    obtain ⟨𝒳, hp𝒳, -, -, Φ, hΦ, heq⟩ := hra.2 _ hq
    refine ⟨𝒳, fun q => Φ q 0, hp𝒳, holomorphicScalar_of_coords (hΦ β), ?_⟩
    rintro _ ⟨V', hV', rfl⟩ hx
    have hval := heq ⟨hx, (Submodule.mem_bot ℝ).2 (funext fun e => e.elim),
      fun c => (hopen.1 hV').1 c (mem_univ _)⟩
    exact congrFun hval 0
  have hdiff := (((hread β).1 _ hO).1 f hrest).2.1
  obtain ⟨-, A, hA⟩ := exists_clm_deriv_along_power hcharts hrR hO hdiff (mem_image_of_mem _ hU)
    fun c => (hopen.1 hU).1 c (mem_univ _)
  obtain ⟨-, hfd, -, c, hc⟩ := hS L n k j hL hn hj
  have := hfd
  let l : edgeFormSpace L n k j →ₗ[ℝ] ℝ :=
    { toFun := fun B => A (rotatedFamily U B)
      map_add' := fun B B' => by
        show A (rotatedFamily U ((B : Edge L n k j → ComplexMatrix2) + B')) = _
        rw [rotatedFamily_add, map_add]
      map_smul' := fun r B => by
        show A (rotatedFamily U (r • (B : Edge L n k j → ComplexMatrix2))) = _
        rw [rotatedFamily_smul, map_smul]
        rfl }
  obtain ⟨X, hX⟩ := exists_inner_representative c l
  refine ⟨X, X.2, fun δ hδ h0 => ?_⟩
  have hTf := ((hP L n k j hL hn hj).1 δ hδ).1
  have h := hasDerivAt_comp_of_restrict hP hL hn hj hopen hU hA
    (g := F) (fun V hV => by
      show F (fieldOfPositiveValues (restrictToPositiveEdges V)) = F V
      rw [hconf hV]) hδ h0
  have e : (edgeFormPairing (X : Edge L n k j → ComplexMatrix2) (curveTangent δ)).re =
      A (rotatedFamily U (curveTangent δ)) := by
    have h1 := hc X ⟨_, hTf⟩
    have h2 := hX ⟨_, hTf⟩
    simp only at h1
    rw [h1, Complex.ofReal_re, h2]
    rfl
  rw [e]
  exact h
end Functions
theorem analyticMapsAlongCurves_of_charts (hC : ExpChartsStatement)
    (hLc : LeftChartFields.Claim)
    (hCv : FiniteLevelCurveDifferentials.Statement)
    (hD : AnalyticMapDifferentiableStatement)
    (hS : FiniteSideFormSpaces) (hP : diffAtZeroPathsStatement) :
    AnalyticMapsAlongCurves := by
  intro L n k a b hL hn ha hb
  exact ⟨fun 𝒰 m hm => analyticMap_along_curves hC hLc hCv hD hP hL hn ha hb hm,
    fun 𝒰 F hF U hU => exists_gradient_along_curves hC hS hP hL hn ha hF hU⟩
end YangMills.Construction.Tower.AlongCurvesProof
end
