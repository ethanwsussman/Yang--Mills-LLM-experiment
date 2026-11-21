import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionFactsProved
import YangMills.Construction.OneLoopLaw.CoefficientOfATemperedFunctional
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctions
import YangMills.Construction.Towers.BoundsOfTheBondTermsOfTheRemainder
import YangMills.Construction.Towers.BoundsOfTheSiteTermsOfTheRemainder
import YangMills.Construction.Towers.FamilyOfTheTotalNormaliserIsTempered
import YangMills.Construction.Towers.TheDeterminantsWithoutConstraint
import YangMills.Construction.Towers.TheFormulaOfTheRemainder
import YangMills.Construction.Towers.TheFreePolarisationIsHolomorphicInThePolydisc
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperatorsAreAdmitted
import YangMills.Construction.Towers.TheRemainderOfTheFreePolarisation
import YangMills.Construction.Towers.TheResponseOperators
import YangMills.Construction.Towers.TheTermsOfTheRemainderAreHolomorphic
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.FreePolarizationRemainder
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Coordinates
open YangMills.Construction.Tower.BackgroundFieldResponse (responseKernel)
open YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets
open YangMills.Construction.PeriodicOperators.EntriesDets
  (HolomorphicFnOn PartialsHolomorphicComm CauchyEstimate multiPartial linCombPartial linComb)
section Holomorphy
variable {N : ℕ}
theorem isHolomorphicScalar_iff_holomorphicFnOn (O : Set (ComplexCoordinates N))
    (u : ComplexCoordinates N → ℂ) :
    ComplexVariables.IsHolomorphicScalar O u ↔ HolomorphicFnOn O u := by
  have h : ((Equiv.funUnique (Fin 1) ℂ).symm ∘ u) = fun z _ => u z := by
    funext z i
    simp
  unfold ComplexVariables.IsHolomorphicScalar
  rw [h]
theorem isHolomorphicScalar_iff_lines (O : Set (ComplexCoordinates N))
    (u : ComplexCoordinates N → ℂ) :
    ComplexVariables.IsHolomorphicScalar O u ↔
      IsOpen O ∧ ContinuousOn u O ∧ ∀ a ∈ O, ∀ j : Fin N, ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ (fun ζ : ℂ => u (a + ζ • ComplexCoordinates.stdBasisVector j)) ζ := by apply _root_.YangMills.Construction.ComplexVariables.HolomorphicFacts.isHolomorphicScalar_iff_lines <;> assumption
theorem eventually_line_mem_of_isOpen {O : Set (ComplexCoordinates N)} (hO : IsOpen O)
    {a : ComplexCoordinates N} (ha : a ∈ O) (j : Fin N) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • ComplexCoordinates.stdBasisVector j ∈ O := by
  have hline : Continuous fun ζ : ℂ =>
      a + ζ • (ComplexCoordinates.stdBasisVector j : ComplexCoordinates N) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have h0 : a + (0 : ℂ) • (ComplexCoordinates.stdBasisVector j : ComplexCoordinates N) ∈ O := by
    simpa using ha
  exact (hline.tendsto 0).eventually (hO.mem_nhds h0)
theorem isHolomorphicScalar_congr {O : Set (ComplexCoordinates N)}
    {u v : ComplexCoordinates N → ℂ}
    (hu : ComplexVariables.IsHolomorphicScalar O u) (h : EqOn v u O) :
    ComplexVariables.IsHolomorphicScalar O v := by
  rw [isHolomorphicScalar_iff_lines] at hu ⊢
  obtain ⟨hO, hc, hd⟩ := hu
  refine ⟨hO, hc.congr h, fun a ha j => ?_⟩
  filter_upwards [hd a ha j, eventually_eventually_nhds.2 (eventually_line_mem_of_isOpen hO ha j)]
    with ζ h1 h2
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [h2] with ζ' h3
  exact h h3
theorem isHolomorphicScalar_add {O : Set (ComplexCoordinates N)} {u v : ComplexCoordinates N → ℂ}
    (hu : ComplexVariables.IsHolomorphicScalar O u) (hv : ComplexVariables.IsHolomorphicScalar O v) :
    ComplexVariables.IsHolomorphicScalar O fun z => u z + v z := by apply _root_.YangMills.DeltaSharedProofs.p502577 <;> assumption
theorem isHolomorphicScalar_sub {O : Set (ComplexCoordinates N)} {u v : ComplexCoordinates N → ℂ}
    (hu : ComplexVariables.IsHolomorphicScalar O u) (hv : ComplexVariables.IsHolomorphicScalar O v) :
    ComplexVariables.IsHolomorphicScalar O fun z => u z - v z := by
  rw [isHolomorphicScalar_iff_lines] at hu hv ⊢
  refine ⟨hu.1, hu.2.1.sub hv.2.1, fun a ha j => ?_⟩
  filter_upwards [hu.2.2 a ha j, hv.2.2 a ha j] with ζ h1 h2
  exact h1.sub h2
theorem isHolomorphicScalar_const_mul {O : Set (ComplexCoordinates N)}
    {u : ComplexCoordinates N → ℂ} (c : ℂ)
    (hu : ComplexVariables.IsHolomorphicScalar O u) :
    ComplexVariables.IsHolomorphicScalar O fun z => c * u z := by
  rw [isHolomorphicScalar_iff_lines] at hu ⊢
  refine ⟨hu.1, continuousOn_const.mul hu.2.1, fun a ha j => ?_⟩
  filter_upwards [hu.2.2 a ha j] with ζ h1
  exact h1.const_mul c
theorem hasDerivAt_line_of_isHolomorphicScalar {O : Set (ComplexCoordinates N)}
    {u : ComplexCoordinates N → ℂ}
    (hu : ComplexVariables.IsHolomorphicScalar O u) {a : ComplexCoordinates N} (ha : a ∈ O)
    (j : Fin N) :
    HasDerivAt (fun ζ : ℂ => u (a + ζ • ComplexCoordinates.stdBasisVector j))
      (EntriesDets.partialDeriv j u a) 0 :=
  (((isHolomorphicScalar_iff_lines O u).1 hu).2.2 a ha j).self_of_nhds.hasDerivAt
theorem tendsto_diffQuot {O : Set (ComplexCoordinates N)} {u : ComplexCoordinates N → ℂ}
    (hu : ComplexVariables.IsHolomorphicScalar O u) {a : ComplexCoordinates N} (ha : a ∈ O)
    (j : Fin N) :
    Tendsto (ComplexVariables.diffQuot u a j) (𝓝[≠] 0)
      (𝓝 (EntriesDets.partialDeriv j u a)) := by
  have h := hasDerivAt_line_of_isHolomorphicScalar hu ha j
  rw [hasDerivAt_iff_tendsto_slope_zero] at h
  refine h.congr fun ζ => ?_
  simp [ComplexVariables.diffQuot]
theorem eqOn_partialDeriv {O : Set (ComplexCoordinates N)} {u : ComplexCoordinates N → ℂ}
    (hu : ComplexVariables.IsHolomorphicScalar O u) (j : Fin N) :
    EqOn (ComplexVariables.partialDeriv j u) (EntriesDets.partialDeriv j u) O :=
  fun _ ha => (tendsto_diffQuot hu ha j).limUnder_eq
theorem diffQuot_eventuallyEq {O : Set (ComplexCoordinates N)} (hO : IsOpen O)
    {f g : ComplexCoordinates N → ℂ} (h : EqOn f g O) {a : ComplexCoordinates N} (ha : a ∈ O)
    (j : Fin N) :
    ComplexVariables.diffQuot f a j =ᶠ[𝓝[≠] 0] ComplexVariables.diffQuot g a j := by
  filter_upwards [nhdsWithin_le_nhds (eventually_line_mem_of_isOpen hO ha j)] with ζ hζ
  simp only [ComplexVariables.diffQuot]
  rw [h hζ, h ha]
end Holomorphy
theorem multiIndexSteps_mixedIndex :
    ComplexVariables.multiIndexSteps mixedIndex = [0, 1] := by
  decide
theorem tendsto_diffQuot_partialDeriv {O : Set (Fin 4 → ℂ)} (hP : PartialsHolomorphicComm O)
    {F : (Fin 4 → ℂ) → ℂ} (hF : ComplexVariables.IsHolomorphicScalar O F) {a : Fin 4 → ℂ}
    (ha : a ∈ O) :
    Tendsto (ComplexVariables.diffQuot (ComplexVariables.partialDeriv 1 F) a 0) (𝓝[≠] 0)
      (𝓝 (EntriesDets.partialDeriv 0 (EntriesDets.partialDeriv 1 F) a)) := by
  have hO : IsOpen O := ((isHolomorphicScalar_iff_lines O F).1 hF).1
  have h1 : ComplexVariables.IsHolomorphicScalar O (EntriesDets.partialDeriv 1 F) :=
    (isHolomorphicScalar_iff_holomorphicFnOn O _).2
      ((hP F ((isHolomorphicScalar_iff_holomorphicFnOn O F).1 hF)).1 1)
  exact (tendsto_diffQuot h1 ha 0).congr'
    (diffQuot_eventuallyEq hO (eqOn_partialDeriv hF 1) ha 0).symm
theorem hasPartialOfIndex_mixedIndex {O : Set (Fin 4 → ℂ)} (hP : PartialsHolomorphicComm O)
    {F : (Fin 4 → ℂ) → ℂ} (hF : ComplexVariables.IsHolomorphicScalar O F) :
    ComplexVariables.HasPartialOfIndex O mixedIndex F := by
  have hO : IsOpen O := ((isHolomorphicScalar_iff_lines O F).1 hF).1
  unfold ComplexVariables.HasPartialOfIndex
  rw [multiIndexSteps_mixedIndex]
  refine ⟨⟨hO, hO, fun z hz => ⟨_, tendsto_diffQuot hF hz 1⟩⟩, hO, fun z hz => ?_⟩
  exact ⟨_, tendsto_diffQuot_partialDeriv hP hF hz⟩
theorem partialOfIndex_mixedIndex_eq {O : Set (Fin 4 → ℂ)} (hP : PartialsHolomorphicComm O)
    {F : (Fin 4 → ℂ) → ℂ} (hF : ComplexVariables.IsHolomorphicScalar O F) {a : Fin 4 → ℂ}
    (ha : a ∈ O) :
    ComplexVariables.partialOfIndex mixedIndex F a =
      EntriesDets.partialDeriv 0 (EntriesDets.partialDeriv 1 F) a := by
  unfold ComplexVariables.partialOfIndex
  rw [multiIndexSteps_mixedIndex]
  exact (tendsto_diffQuot_partialDeriv hP hF ha).limUnder_eq
theorem toComplexVec_single_add_single (s t : ℝ) :
    toComplexVec (Pi.single 0 s + Pi.single 1 t) =
      toComplexVec (Pi.single 0 s) +
        (t : ℂ) • (ComplexCoordinates.stdBasisVector 1 : Fin 4 → ℂ) := by
  funext μ
  by_cases h : μ = 1
  · subst h
    simp [toComplexVec, ComplexCoordinates.stdBasisVector]
  · simp [toComplexVec, ComplexCoordinates.stdBasisVector, h]
theorem toComplexVec_single (s : ℝ) :
    toComplexVec (Pi.single 0 s) =
      (0 : Fin 4 → ℂ) + (s : ℂ) • (ComplexCoordinates.stdBasisVector 0 : Fin 4 → ℂ) := by
  funext μ
  by_cases h : μ = 0
  · subst h
    simp [toComplexVec, ComplexCoordinates.stdBasisVector]
  · simp [toComplexVec, ComplexCoordinates.stdBasisVector, h]
theorem deriv_ofReal_of_hasDerivAt {f : ℂ → ℂ} {d : ℂ} (h : HasDerivAt f d 0) :
    deriv (fun s : ℝ => f (s : ℂ)) 0 = d := by
  have h' : HasDerivAt f d ((0 : ℝ) : ℂ) := by simpa using h
  exact h'.comp_ofReal.deriv
theorem secondPartialAtZero_eq_mixed {O : Set (Fin 4 → ℂ)} (hP : PartialsHolomorphicComm O)
    {F : (Fin 4 → ℂ) → ℂ} (hF : ComplexVariables.IsHolomorphicScalar O F)
    (h0 : (0 : Fin 4 → ℂ) ∈ O) :
    OneLoopLaw.TemperedStiffness.secondPartialAtZero F 0 1 =
      EntriesDets.partialDeriv 0 (EntriesDets.partialDeriv 1 F) 0 := by
  have hO : IsOpen O := ((isHolomorphicScalar_iff_lines O F).1 hF).1
  have h1 : ComplexVariables.IsHolomorphicScalar O (EntriesDets.partialDeriv 1 F) :=
    (isHolomorphicScalar_iff_holomorphicFnOn O _).2
      ((hP F ((isHolomorphicScalar_iff_holomorphicFnOn O F).1 hF)).1 1)
  have hnear : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), toComplexVec (Pi.single 0 s) ∈ O := by
    have hc : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
      simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ))
    filter_upwards [hc.eventually (eventually_line_mem_of_isOpen hO h0 0)] with s hs
    rw [toComplexVec_single]
    exact hs
  have hinner : (fun s : ℝ => deriv (fun t : ℝ =>
        F (toComplexVec (Pi.single 0 s + Pi.single 1 t))) 0) =ᶠ[𝓝 0]
      fun s : ℝ => EntriesDets.partialDeriv 1 F
        ((0 : Fin 4 → ℂ) + (s : ℂ) • (ComplexCoordinates.stdBasisVector 0 : Fin 4 → ℂ)) := by
    filter_upwards [hnear] with s hs
    rw [← toComplexVec_single]
    have h := deriv_ofReal_of_hasDerivAt (hasDerivAt_line_of_isHolomorphicScalar hF hs 1)
    simpa only [toComplexVec_single_add_single] using h
  unfold OneLoopLaw.TemperedStiffness.secondPartialAtZero
  rw [hinner.deriv_eq]
  exact deriv_ofReal_of_hasDerivAt (hasDerivAt_line_of_isHolomorphicScalar h1 h0 0)
theorem norm_mixed_sub_le {δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c)
    {O : Set (Fin 4 → ℂ)} (hO : O = {p | ∀ μ, ‖p μ‖ < δ})
    (hC : CauchyEstimate O (normSeminorm ℂ ℂ)) {F G : (Fin 4 → ℂ) → ℂ}
    (hF : ComplexVariables.IsHolomorphicScalar O F) (hG : ComplexVariables.IsHolomorphicScalar O G)
    (hb : ∀ p ∈ O, ‖F p - G p‖ ≤ c) :
    ‖EntriesDets.partialDeriv 0 (EntriesDets.partialDeriv 1 F) 0 -
        EntriesDets.partialDeriv 0 (EntriesDets.partialDeriv 1 G) 0‖ ≤
      c * δ ^ (-2 : ℤ) := by
  have hpoly : YangMills.Construction.PeriodicOperators.EntriesDets.openPolydisc (n := 4)
      (fun _ => δ) 0 = O := by
    rw [hO]
    ext z
    simp [YangMills.Construction.PeriodicOperators.EntriesDets.openPolydisc]
  have hu : ∀ i, HolomorphicFnOn O ((![F, G] : Fin 2 → (Fin 4 → ℂ) → ℂ) i) := by
    intro i
    fin_cases i
    · exact (isHolomorphicScalar_iff_holomorphicFnOn O F).1 hF
    · exact (isHolomorphicScalar_iff_holomorphicFnOn O G).1 hG
  have hcomb : ∀ z, linComb (![F, G] : Fin 2 → (Fin 4 → ℂ) → ℂ) ![(1 : ℂ), -1] z = F z - G z := by
    intro z
    simp [linComb, Fin.sum_univ_two, sub_eq_add_neg]
  have h := (hC 2 ![(1 : ℂ), -1] ![F, G] hu (fun _ => δ) c (fun _ => hδ) hc).1 0 hpoly.le
    (fun z hz => by
      rw [hcomb]
      exact hb z (hpoly ▸ hz)) ![1, 1, 0, 0]
  have hl : linCombPartial ![1, 1, 0, 0] (![F, G] : Fin 2 → (Fin 4 → ℂ) → ℂ) ![(1 : ℂ), -1] 0 =
      EntriesDets.partialDeriv 0 (EntriesDets.partialDeriv 1 F) 0 -
        EntriesDets.partialDeriv 0 (EntriesDets.partialDeriv 1 G) 0 := by
    have hs : ∀ u : (Fin 4 → ℂ) → ℂ, multiPartial (![1, 1, 0, 0] : Fin 4 → ℕ) u =
        EntriesDets.partialDeriv 0 (EntriesDets.partialDeriv 1 u) := by
      intro u
      have hl : ((List.finRange 4).flatMap fun j => List.replicate ((![1, 1, 0, 0] : Fin 4 → ℕ) j) j) =
          [0, 1] := by decide
      unfold multiPartial
      rw [hl]
      rfl
    simp [linCombPartial, linComb, Fin.sum_univ_two, hs, sub_eq_add_neg]
  have hr : (∏ j : Fin 4, (((![1, 1, 0, 0] : Fin 4 → ℕ) j).factorial : ℝ) *
      δ ^ (-(((![1, 1, 0, 0] : Fin 4 → ℕ) j : ℕ) : ℤ))) = δ ^ (-2 : ℤ) := by
    have hne : δ ≠ 0 := hδ.ne'
    simp [Fin.prod_univ_four, zpow_neg]
    field_simp
  rw [hl] at h
  simpa only [coe_normSeminorm, hr] using h
theorem responseFormDefinedAt_of_rate {L k : ℕ} {υ : ℝ}
    (h : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k 0)
      (responseKernel L k) υ)
    {q : Fin 4 → ℂ} (hq : q ∈ openImStrip υ) (μ : Fin 4) :
    ResponseFormDefinedAt L k q μ := by
  have hact := h.applyKernel_blochWave q hq (constantFormAmplitude L k (axisPauliElement μ 2))
  have hwave : applyKernel (responseKernel L k) (planeWaveOfConstant L k q (axisPauliElement μ 2)) =
      blochWave (colourEdges L k 0) q
        (applyKernel (quotSymbol (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) q)
          (constantFormAmplitude L k (axisPauliElement μ 2))) :=
    funext fun ι' => (hact ι').2
  refine ⟨fun ι' => (hact ι').1, ?_⟩
  have hex : ∃ ψ, blochWave (colourEdges L k 0) q ψ =
      ((finestMesh L k : ℝ) : ℂ) •
        applyKernel (responseKernel L k) (planeWaveOfConstant L k q (axisPauliElement μ 2)) := by
    refine ⟨((finestMesh L k : ℝ) : ℂ) •
      applyKernel (quotSymbol (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) q)
        (constantFormAmplitude L k (axisPauliElement μ 2)), ?_⟩
    rw [hwave]
    funext ι
    simp only [blochWave, Pi.smul_apply, smul_eq_mul]
    ring
  exact Classical.epsilon_spec hex
theorem polarizationDefinedAt_of_width {L k : ℕ} {hL : 0 < L} {υ : ℝ} (hδ : 0 < stripHalfWidth)
    (hυ : 2 * stripHalfWidth < υ)
    (hrate : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k 0)
      (responseKernel L k) υ)
    (hdom : stripHalfWidth ∈ FreeStrip.halfSupRate)
    (hw : IsJointInvertibilityWidth L k hL stripHalfWidth) {p : Fin 4 → ℂ}
    (hp : p ∈ momentumPolydisc stripHalfWidth)
    (μPlus μMinus : Fin 4) : PolarizationDefinedAt L k hL μPlus μMinus p := by
  have him : ∀ (q : Fin 4 → ℂ) (μ : Fin 4), ‖q μ‖ ≤ stripHalfWidth → |(q μ).im| ≤ stripHalfWidth :=
    fun q μ h => (Complex.abs_im_le_norm _).trans h
  have hopen : ∀ q ∈ momentumPolydisc stripHalfWidth, q ∈ openImStrip υ := fun q hq μ => by
    have := him q μ (hq μ)
    linarith
  have hneg : -p ∈ momentumPolydisc stripHalfWidth := fun μ => by simpa using hp μ
  refine ⟨⟨stripHalfWidth, hw, fun μ => him p μ (hp μ), stripHalfWidth, hdom, fun μ => ?_⟩,
    responseFormDefinedAt_of_rate hrate (hopen p hp) μPlus,
    responseFormDefinedAt_of_rate hrate (hopen _ hneg) μMinus⟩
  have := him p μ (hp μ)
  linarith
theorem exists_bound_polarizationMinusMassive (hFormula : Formula.RemainderFormula)
    (hBond : EdgeTermsBounded) (hSite : VertexTermsBounded)
    {L : ℕ} (hL : 0 < L) (hS : Conventions.IsAdmissibleBlockingFactor L) :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ μPlus μMinus : Fin 4, ∀ p ∈ openPolydisc,
      ‖polarizationMinusMassive L k hL μPlus μMinus p‖ ≤ C := by
  obtain ⟨C₁, h₁⟩ := hBond L hS
  obtain ⟨C₂, h₂⟩ := hSite L hS
  refine ⟨1 / 2 * C₁ + C₂ + 1 / 2 * C₁ + C₂, fun k hk μPlus μMinus p hp => ?_⟩
  have hp' : p ∈ momentumPolydisc stripHalfWidth := fun μ => (hp μ).le
  obtain ⟨a₁, a₂⟩ := h₁ k hk p hp' μPlus μMinus
  obtain ⟨b₁, b₂⟩ := h₂ k hk p hp' μPlus μMinus
  have hf := hFormula L hL hS k hk p hp' μPlus μMinus
  unfold polarizationMinusMassive
  rw [hf]
  generalize edgeRemainder L k p μPlus μMinus = x at a₁ ⊢
  generalize vertexRemainder L k p μPlus μMinus = y at b₁ ⊢
  generalize JetQuad.logNumber p (edgeConstraintJet L k p μPlus μMinus) = z at a₂ ⊢
  generalize JetQuad.logNumber p (vertexConstraintJet L k p μPlus μMinus) = w at b₂ ⊢
  have e₁ : ‖(-(1 / 2) : ℂ) * x‖ = 1 / 2 * ‖x‖ := by simp
  have e₂ : ‖(1 / 2 : ℂ) * z‖ = 1 / 2 * ‖z‖ := by simp
  have t₁ := norm_add_le ((-(1 / 2) : ℂ) * x + y - 1 / 2 * z) w
  have t₂ := norm_sub_le ((-(1 / 2) : ℂ) * x + y) (1 / 2 * z)
  have t₃ := norm_add_le ((-(1 / 2) : ℂ) * x) y
  linarith
theorem freePolarizationRemainderBound_holds
    (hNumbers : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hDeterminants : UnconstrainedDeterminants.PolarizationLogDetFormula)
    (hFormula : Formula.RemainderFormula)
    (hBond : EdgeTermsBounded)
    (hSite : VertexTermsBounded)
    (hTerms : TermsHolomorphic.RemainderTermsHolomorphic)
    (hFree : FreePolarizationHolomorphic)
    (hResponse : ResponseOperators.Claim)
    (hEntries : EntriesDets.Claim)
    (hTempered : NormaliserTempered.TemperedAndStiffness)
    (hCoefficient : OneLoopLaw.TemperedStiffness.TemperedStiffnessClaim) :
    FreePolarizationRemainderBound := by
  obtain ⟨-, -, δ₁, hδ₁, C₀, -, hrange, -, -⟩ := hNumbers
  have hdom : stripHalfWidth ∈ FreeStrip.halfSupRate :=
    stripHalfWidth_mem (Part.dom_iff_mem.2 ⟨δ₁, hδ₁⟩)
  have hδ : 0 < stripHalfWidth := by
    rw [Part.mem_unique hdom hδ₁]
    exact hrange.1
  have hOpen : IsOpen openPolydisc := by
    simp only [openPolydisc, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun μ => isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : Fin 4 → ℂ) ∈ openPolydisc := fun μ => by simpa using hδ
  obtain ⟨-, -, -, -, -, -, hFun, -⟩ := hEntries
  obtain ⟨-, -, -, -, -, -, -, hPartials, hAll, -, -⟩ := hFun 4 openPolydisc (by norm_num) hOpen
  have hCauchy := (hAll ℂ (normSeminorm ℂ ℂ)).2
  obtain ⟨δ₂, hδ₂, hResp⟩ := hResponse
  obtain rfl : δ₂ = stripHalfWidth := Part.mem_unique hδ₂ hdom
  obtain ⟨δ₃, -, hTemp⟩ := hTempered
  refine ⟨hdom, fun L hL hS => ?_, fun D l => ⟨remainderBound, fun d => rfl⟩⟩
  obtain ⟨C, hC⟩ := exists_bound_polarizationMinusMassive hFormula hBond hSite hL hS
  have hne : (remainderNorms L).Nonempty := ⟨_, hL, 1, le_rfl, 0, 0, 0, h0, rfl⟩
  have hbdd : BddAbove (remainderNorms L) :=
    ⟨C, by
      rintro x ⟨_, k, hk, μ, ν, p, hp, rfl⟩
      exact hC k hk μ ν p hp⟩
  have hlub : IsLUB (remainderNorms L) (remainderBound L) := isLUB_csSup hne hbdd
  have hnonneg : 0 ≤ remainderBound L :=
    (norm_nonneg _).trans (hlub.1 ⟨hL, 1, le_rfl, 0, 0, 0, h0, rfl⟩)
  refine ⟨fun k hk => ?_, ⟨C, hC⟩, hlub⟩
  have hD := hDeterminants L hL hS k hk
  have hhol : ∀ μPlus μMinus : Fin 4, ComplexVariables.IsHolomorphicScalar openPolydisc
      (polarizationMinusMassive L k hL μPlus μMinus) := by
    intro μPlus μMinus
    obtain ⟨t₁, t₂, t₃, t₄⟩ := hTerms L hS k hk μPlus μMinus
    exact isHolomorphicScalar_congr
      (isHolomorphicScalar_add
        (isHolomorphicScalar_sub
          (isHolomorphicScalar_add (isHolomorphicScalar_const_mul (-(1 / 2)) t₁) t₂)
          (isHolomorphicScalar_const_mul (1 / 2) t₃)) t₄)
      fun p hp => hFormula L hL hS k hk p (fun μ => (hp μ).le) μPlus μMinus
  have hfree : ComplexVariables.IsHolomorphicScalar openPolydisc
      (freePolarizationEntry L k hL 0 1) :=
    hFree L hL hS k hk 0 1
  have hmass : ComplexVariables.IsHolomorphicScalar openPolydisc (massiveAtFirstPair L k) :=
    isHolomorphicScalar_congr (isHolomorphicScalar_sub hfree (hhol 0 1)) fun p _ => by
      simp [massiveAtFirstPair, polarizationMinusMassive]
  obtain ⟨hTem, -, -, hred⟩ := hTemp L hL hS k hk
  obtain ⟨hfun, δt, πt, et, hchoice⟩ := hTem
  obtain ⟨-, -, -, b, -, hcoef, -⟩ := hCoefficient L hL hS _ δt πt et hfun hchoice
  obtain ⟨υ, hυ, -, hrate, -⟩ := (hResp L hS k hk).exists_rate
  refine ⟨hD.1, fun μPlus μMinus p hp =>
      polarizationDefinedAt_of_width hδ hυ hrate hdom hD.1 hp μPlus μMinus,
    hhol, hmass, hasPartialOfIndex_mixedIndex hPartials hmass, hcoef, ?_⟩
  have hbound := norm_mixed_sub_le (O := openPolydisc) hδ hnonneg rfl hCauchy hfree hmass
    fun p hp => hlub.1 ⟨hL, k, hk, 0, 1, p, hp, rfl⟩
  unfold mixedPartialAtZero
  have hflip : ∀ A B : ℂ, -A + B = -(A - B) := fun A B => by ring
  rw [hred, secondPartialAtZero_eq_mixed hPartials hfree h0,
    partialOfIndex_mixedIndex_eq hPartials hmass h0, hflip, norm_neg]
  exact hbound
end YangMills.Construction.Tower.FullSpace.BackgroundJets.FreePolarizationRemainder
end
