import YangMills.Construction.OneLoop.PauliMatrixRelations
import YangMills.Construction.Towers.BackgroundFormOfTheFunctionalOnASideProof
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSites
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.CovariantDifferenceUnderTheChainConstraint
import YangMills.Construction.Towers.DataOfAChangeOfTheGaugeFixingAtAChain
import YangMills.Construction.Towers.FibresOfTheAveragingMaps
import YangMills.Construction.Towers.HessianAlongTheBackgroundShift
import YangMills.Construction.Towers.HessianOnTheFibreAndGaugeDirections
import YangMills.Construction.Towers.InjectiveCovariantDifferenceAtTheBaseOfAChain
import YangMills.Construction.Towers.RealAndCovariantDifferentialsOfTheChain
import YangMills.Construction.Towers.TheChainOfABlockField
import YangMills.Construction.Towers.TheProductOfTheNormalisers
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
namespace TransferAlongChain
open YangMills.Construction.Tower.RealQuadraticTransposes (TransposeProperties
  BackgroundOperatorProperties CovDiffTransposePreservesReal)
variable {L n k : ℕ}
theorem eventuallyNearIdentity_mono {ι : Type*} {D : Set (ι → Matrices.ComplexMatrix2)}
    {P Q : (ι → Matrices.ComplexMatrix2) → Prop} (h : EventuallyNearIdentity D P)
    (f : ∀ V, P V → Q V) : EventuallyNearIdentity D Q :=
  Filter.Eventually.mono h f
theorem eventuallyNearIdentity_and {ι : Type*} {D : Set (ι → Matrices.ComplexMatrix2)}
    {P Q : (ι → Matrices.ComplexMatrix2) → Prop} (h : EventuallyNearIdentity D P)
    (h' : EventuallyNearIdentity D Q) : EventuallyNearIdentity D fun V => P V ∧ Q V :=
  Filter.Eventually.and h h'
theorem eventuallyNearIdentity_mem {ι : Type*} {D : Set (ι → Matrices.ComplexMatrix2)} :
    EventuallyNearIdentity D fun V => V ∈ D :=
  self_mem_nhdsWithin
theorem eventuallyNearIdentity_prolongComp (hC : ProlongItersNearIdentity L n k)
    {P : (Edge L n k 0 → Matrices.ComplexMatrix2) → Prop}
    (h : EventuallyNearIdentity (fieldSpace L n k 0) P) :
    EventuallyNearIdentity (fieldSpace L n k k) fun W => P (chosenProlongComp L n k k W) := by
  have h1 := (hC.tendsto 0 (Nat.zero_le k)).eventually
    (show ∀ᶠ V in 𝓝[fieldSpace L n k 0] trivialField L n k 0, P V from h)
  have h2 : ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k,
      chosenProlongIter L n k (Nat.zero_le k) W = chosenProlongComp L n k k W :=
    hC.comp_zero_eq
  show ∀ᶠ W in 𝓝[fieldSpace L n k k] trivialField L n k k,
    P (chosenProlongComp L n k k W)
  filter_upwards [h1, h2] with W a b
  rwa [b] at a
theorem linearMapWithValues_apply {α β : Type*} {p : Submodule ℝ (α → Matrices.ComplexMatrix2)}
    {p' : Submodule ℝ (β → Matrices.ComplexMatrix2)}
    {f : (α → Matrices.ComplexMatrix2) → β → Matrices.ComplexMatrix2}
    (h : ∃ T : p →ₗ[ℝ] p', ∀ x : p, (T x : β → Matrices.ComplexMatrix2) = f x) (x : p) :
    (linearMapWithValues p p' f x : β → Matrices.ComplexMatrix2) = f x := by apply _root_.YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide.linearMapWithValues_apply <;> assumption
theorem mem_complexEdgeForms_of_mem {B : Edge L n k 0 → Matrices.ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k 0) : B ∈ complexEdgeForms L n k 0 :=
  ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
theorem isPositivelyOriented_or_opposite {j : ℕ} (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem covDiff_congr_positive {j : ℕ} {V V' : Edge L n k j → Matrices.ComplexMatrix2}
    (h : ∀ c : PositiveEdge L n k j, V c = V' c) (l : Vertex L n k j → Matrices.ComplexMatrix2) :
    covDiff V l = covDiff V' l := by
  funext b
  unfold covDiff extendOddly
  by_cases hb : b.IsPositivelyOriented
  · simp only [if_pos hb]
    rw [h ⟨b, hb⟩]
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
    simp only [if_neg hb]
    rw [h ⟨b.opposite, hr⟩]
theorem traceFinsumPairing_self_re_nonneg (hP : OneLoop.PauliMatrixRelations) {ι : Type*}
    (f : ι → Matrices.ComplexMatrix2) (hf : ∀ i, f i ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    0 ≤ (traceFinsumPairing f f).re := by
  have hterm : ∀ i, 0 ≤ (Matrices.ComplexMatrix2.halfTrace (f i * f i)).re := fun i => by
    obtain ⟨-, -, -, -, -, -, -, h, -⟩ := hP
    have h2 := congrArg Complex.re (h ⟨f i, (hf i).2⟩ (hf i))
    rw [Complex.ofReal_re] at h2
    have h3 : (Matrices.ComplexMatrix2.halfTrace (f i * f i)).re =
        Matrices.ComplexMatrix2.operatorNorm (f i) ^ 2 := h2.symm
    rw [h3]
    positivity
  unfold traceFinsumPairing
  by_cases hs : (Function.support fun i => Matrices.ComplexMatrix2.halfTrace (f i * f i)).Finite
  · rw [finsum_eq_sum _ hs, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => hterm i
  · rw [finsum_of_infinite_support hs]
    simp
theorem coe_toSublattice_levelDepth (hL : 0 < L) (y : Vertex L n k k) :
    ((PeriodicLattice.Site.toSublattice y (PeriodicLattice.levelDepth k 0) : Vertex L n k 0) :
      PeriodicLattice.FourTorus L n) = y :=
  Classical.epsilon_spec (p := fun x : Vertex L n k 0 => (x : PeriodicLattice.FourTorus L n) = y)
    ⟨⟨y, PeriodicLattice.sublattice_mono hL n
      (by simp only [PeriodicLattice.levelDepth]; omega) y.2⟩, rfl⟩
theorem mem_vanishingAtTop_iff (hL : 0 < L) (l : Vertex L n k 0 → Matrices.ComplexMatrix2) :
    l ∈ vertexFunctionsVanishingAtTop L n k ↔ l ∈ vertexFunctionsVanishingOnTop L n k := by
  constructor
  · rintro ⟨h, e⟩
    refine ⟨h, fun x hx => ?_⟩
    have e1 := congrFun e (⟨x.1, hx⟩ : Vertex L n k k)
    have e2 : PeriodicLattice.Site.toSublattice (⟨x.1, hx⟩ : Vertex L n k k)
        (PeriodicLattice.levelDepth k 0) = x :=
      Subtype.ext (coe_toSublattice_levelDepth hL _)
    have e3 : l (PeriodicLattice.Site.toSublattice (⟨x.1, hx⟩ : Vertex L n k k)
        (PeriodicLattice.levelDepth k 0)) = 0 := e1
    rwa [e2] at e3
  · rintro ⟨h, v⟩
    refine ⟨h, funext fun y => ?_⟩
    refine v (PeriodicLattice.Site.toSublattice y (PeriodicLattice.levelDepth k 0)) ?_
    rw [coe_toSublattice_levelDepth hL]
    exact y.2
structure BottomHypotheses (U : Edge L n k 0 → Matrices.ComplexMatrix2) : Prop where
  mem : U ∈ fieldSpace L n k 0
  small : U ∈ smallIterateFields L n k
  real : CovariantIterEqRealIterAt U
  onto : HasSurjectiveDifferential (smoothingIter L n k k) U
  deriv : ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k, ∀ B : edgeFormSpace L n k 0,
    (T B : Edge L n k k → Matrices.ComplexMatrix2) =
      leftDifferential (smoothingIter L n k k) U (B : Edge L n k 0 → Matrices.ComplexMatrix2)
  covDeriv : ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k, ∀ B : edgeFormSpace L n k 0,
    (T B : Edge L n k k → Matrices.ComplexMatrix2) =
      iterCovariantDeriv L n k U k (B : Edge L n k 0 → Matrices.ComplexMatrix2)
  drift : ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k,
    ∀ B : edgeFormSpace L n k 0, (T B : Vertex L n k k → Matrices.ComplexMatrix2) =
      iterContourLogDrift L n k U k (B : Edge L n k 0 → Matrices.ComplexMatrix2)
  average : ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k,
    ∀ l : vertexFunctionSpace L n k 0, (T l : Vertex L n k k → Matrices.ComplexMatrix2) =
      iterAdjointCubeAverage L n k U k (l : Vertex L n k 0 → Matrices.ComplexMatrix2)
  transposes : TransposeProperties U
  hessian : BackgroundOperatorProperties U
theorem bottomHypotheses_eventually (hY : RealLinearMaps.RealLinearMapsStatement)
    (hC : ProlongCompositesAndVertexLayers.Statement) (hF : SmoothingFibres)
    (hR : RealQuadraticTransposes.Statement)
    (hE : IterLeftChartExpansion) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) :
    EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
      BottomHypotheses (L := L) (n := n) (k := k) U := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  have step := (hY L n (i + 1) hL hn hk).1 i (Nat.lt_succ_self i)
  refine eventuallyNearIdentity_mono (eventuallyNearIdentity_and eventuallyNearIdentity_mem
    (eventuallyNearIdentity_and (hE L n (i + 1) hL hn hk) (eventuallyNearIdentity_and
    (hF L n (i + 1) i hL hn (Nat.lt_succ_self i)).2.2.1 (eventuallyNearIdentity_and
    ((hC.1 L n (i + 1) hL hn hk).2.1.iterDifferential_linear (i + 1) le_rfl)
    (eventuallyNearIdentity_and step.iterCovariantDeriv_isLinear (eventuallyNearIdentity_and
    step.iterContourLogDrift_isLinear (eventuallyNearIdentity_and
    step.iterAdjointCubeAverage_isLinear (hR L n (i + 1) hL hn hk).2))))))) ?_
  rintro U ⟨a, b, c, d, e, f, g, -, h, h'⟩
  exact ⟨a, b.1.1, b.1.2.1, c, d, e, f, g, h, h'⟩
structure TopHypotheses (W : Edge L n k k → Matrices.ComplexMatrix2) : Prop where
  mem : W ∈ fieldSpace L n k k
  bottom : BottomHypotheses (chainBottom W)
  eq_smoothingIter : W = smoothingIter L n k k (chainBottom W)
  derivs : ∀ B : edgeFormSpace L n k 0,
    (smoothingIterDifferential L n k k (chainBottom W) B : Edge L n k k → Matrices.ComplexMatrix2) =
      complexIterDeriv L n k k (chainBottom W) B
  contour : ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] fineOnlyFamilySpace L n k,
    ∀ B : edgeFormSpace L n k 0, (T B : FineOnlyFamily L n k) = contourFamily W B
  constraint : ∀ (l : vertexFunctionSpace L n k 0) (B : edgeFormSpace L n k 0),
    (B : Edge L n k 0 → Matrices.ComplexMatrix2) = covDiff (chainBottom W) l →
    (topConstraintMap L n k W B : Edge L n k k → Matrices.ComplexMatrix2) =
      covDiff W (restrictVertexFunction k (l : Vertex L n k 0 → Matrices.ComplexMatrix2))
  injective : CovDiffInjective W → CovDiffInjective (chainBottom W)
  directions : FibreGaugeDirections W
  normaliser : TotalNormaliserWellDefined W
  shift : ∀ (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k),
    (J : Edge L n k 0 → Matrices.ComplexMatrix2) =
        leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ)) (chainBottom W) →
      (μ : Edge L n k k → Matrices.ComplexMatrix2) = (chosenCriticalBranch L n k).energyGradient k W →
      ∀ B : edgeFormSpace L n k 0, iterCovariantDerivLinear L n k (chainBottom W) B = 0 →
        ∃ h : backgroundShift L n k (chainBottom W) B ∈ LinearMap.ker (topConstraintMap L n k W),
          fibreRestrictedHessian L n k W ⟨_, h⟩ =
            leftSecondDeriv (plaquetteAction L n k) (chainBottom W) B B +
              sourceQuadraticForm (chainBottom W) J μ B
theorem totalNormaliserWellDefined_eventually (hN : NormaliserProductTheorem)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    EventuallyNearIdentity (fieldSpace L n k k) fun W => TotalNormaliserWellDefined W := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  exact (hN L n i hL hn).wellDefined
theorem topHypotheses_eventually (hY : RealLinearMaps.RealLinearMapsStatement)
    (hC : ProlongCompositesAndVertexLayers.Statement) (hF : SmoothingFibres)
    (hR : RealQuadraticTransposes.Statement)
    (hE : IterLeftChartExpansion)
    (hN : NormaliserProductTheorem) (hK : BlockFieldChainProperties)
    (hD : RealDerivEqComplexAtChainBottom)
    (hI : CovDiffInjectiveAtChainBottom)
    (hG : CovDiffUnderTopConstraint)
    (hH : FibreHessianAndGaugeDirections)
    (hS : HessianAlongBackgroundShift) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) :
    EventuallyNearIdentity (fieldSpace L n k k) fun W =>
      TopHypotheses (L := L) (n := n) (k := k) W := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL.2
  have hb := eventuallyNearIdentity_prolongComp (hC.1 L n k hL hn hk).1
    (bottomHypotheses_eventually hY hC hF hR hE hL hn hk)
  refine eventuallyNearIdentity_mono (eventuallyNearIdentity_and eventuallyNearIdentity_mem
    (eventuallyNearIdentity_and hb (eventuallyNearIdentity_and (hK L n k hL hn hk hL0).1
    (eventuallyNearIdentity_and (hD L n k hL hn hk) (eventuallyNearIdentity_and
    (hY L n k hL hn hk).2.contourFamily_isLinear (eventuallyNearIdentity_and
    (hG L n k hL hn hk) (eventuallyNearIdentity_and (hI L n k hL hn hk)
    (eventuallyNearIdentity_and (hH L n k hL hn hk).2 (eventuallyNearIdentity_and
    (totalNormaliserWellDefined_eventually hN hL hn hk) (hS L n k hL hn hk)))))))))) ?_
  rintro W ⟨a, b, c, d, e, f, g, h, i, j⟩
  refine ⟨a, ?_, ?_, fun B => d k le_rfl B, e, fun l B => f l B, g, h.2, i, ?_⟩
  · rw [chainBottom_eq W]
    exact b
  · have t := (c.1 k le_rfl).2
    rwa [descendingChain_top] at t
  · rw [chainBottom_eq W]
    exact j
structure TowerHypotheses (L n k : ℕ) : Prop where
  pos : 0 < L
  pauli : OneLoop.PauliMatrixRelations
  realTranspose : CovDiffTransposePreservesReal L n k
  linear : RealLinearMaps.TowerLinearity L n k
  layers : VertexLayerDecomposition L n k
  relations : CovariantSmoothingProperties.IterateRelations L n k k
theorem transferData_of_top (hG : TowerHypotheses L n k)
    {W : Edge L n k k → Matrices.ComplexMatrix2} (hT : TopHypotheses W)
    (hinj : CovDiffInjective W) (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k)
    (hJ : (J : Edge L n k 0 → Matrices.ComplexMatrix2) =
      leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ)) (chainBottom W))
    (hμ : (μ : Edge L n k k → Matrices.ComplexMatrix2) =
      (chosenCriticalBranch L n k).energyGradient k W) :
    Nonempty (GaugeFixingTransferData L n k (topConstraintMap L n k W)
      (iterCovariantDerivLinear L n k (chainBottom W)) (augmentedHessian L n k W)
      (backgroundHessian (chainBottom W) J μ) (iterAverageLinear L n k (chainBottom W))
      (covDiffRealTranspose L n k (chainBottom W) ∘ₗ covDiffLinear L n k (chainBottom W))) := by
  obtain ⟨U, hU⟩ : ∃ U, U = chainBottom W := ⟨_, rfl⟩
  have hb : BottomHypotheses U := hU ▸ hT.bottom
  have hQc : ∀ B : edgeFormSpace L n k 0,
      (topConstraintMap L n k W B : Edge L n k k → Matrices.ComplexMatrix2) =
        complexIterDeriv L n k k U B := fun B => by
    rw [hU]
    exact hT.derivs B
  have hQm : ∀ B : edgeFormSpace L n k 0,
      (topConstraintMap L n k W B : Edge L n k k → Matrices.ComplexMatrix2) =
        leftDifferential (smoothingIter L n k k) U (B : Edge L n k 0 → Matrices.ComplexMatrix2) :=
      fun B => by
    rw [hU]
    have hd := hT.bottom.deriv
    exact Classical.epsilon_spec hd B
  have hcon : ∀ (l : vertexFunctionSpace L n k 0) (B : edgeFormSpace L n k 0),
      (B : Edge L n k 0 → Matrices.ComplexMatrix2) = covDiff U l →
      (topConstraintMap L n k W B : Edge L n k k → Matrices.ComplexMatrix2) =
        covDiff W (restrictVertexFunction k (l : Vertex L n k 0 → Matrices.ComplexMatrix2)) :=
    fun l B e => hT.constraint l B (hU ▸ e)
  have hinjU : CovDiffInjective U := hU ▸ hT.injective hinj
  have htop : ∀ l : Vertex L n k k → Matrices.ComplexMatrix2,
      covDiff (PeriodicLattice.complexBlockFieldAtLevel k U) l = covDiff W l := by
    refine fun l => covDiff_congr_positive (fun c => ?_) l
    have e := hb.real c
    rw [e, hU, ← hT.eq_smoothingIter]
  have hshift : ∀ B : edgeFormSpace L n k 0, iterCovariantDerivLinear L n k U B = 0 →
      ∃ h : backgroundShift L n k U B ∈ LinearMap.ker (topConstraintMap L n k W),
        fibreRestrictedHessian L n k W ⟨_, h⟩ = leftSecondDeriv (plaquetteAction L n k) U B B +
          sourceQuadraticForm U J μ B := fun B e => by
    subst hU
    exact hT.shift J μ hJ hμ B e
  have hdirs : FibreGaugeDirections W := hT.directions
  have hkilled : ∀ B : LinearMap.ker (topConstraintMap L n k W),
      IsInCovariantIterKernel W B.1 := fun B => by
    have e := (hQc B.1).symm.trans (congrArg Subtype.val (LinearMap.mem_ker.1 B.2))
    show complexIterDeriv L n k k (chainBottom W) B.1 = 0
    rw [← hU]
    exact e
  have hDirU : ∀ (D₀ : vertexFunctionsVanishingAtTop L n k →ₗ[ℝ] edgeFormSpace L n k 0),
      IsGaugeDirectionEmbedding W D₀ → ∀ κ,
        (D₀ κ : Edge L n k 0 → Matrices.ComplexMatrix2) = covDiff U κ :=
    fun D₀ h κ => by
      rw [hU]
      exact h κ
  rw [← hU]
  clear hU
  have hb' := hb
  obtain ⟨mem, small, -, onto, -, covariant, drift, block, tr, op⟩ := hb'
  have vD : ∀ l : vertexFunctionSpace L n k 0,
      (covDiffLinear L n k U l : Edge L n k 0 → Matrices.ComplexMatrix2) = covDiff U l :=
    linearMapWithValues_apply (hG.linear.covDiff_isLinear 0 (Nat.zero_le k) U mem)
  have vDc : ∀ l : vertexFunctionSpace L n k k,
      (linearMapWithValues (vertexFunctionSpace L n k k) (edgeFormSpace L n k k) (covDiff W) l :
        Edge L n k k → Matrices.ComplexMatrix2) = covDiff W l :=
    linearMapWithValues_apply (hG.linear.covDiff_isLinear k le_rfl W hT.mem)
  have vQ' : ∀ B : edgeFormSpace L n k 0, (iterCovariantDerivLinear L n k U B :
      Edge L n k k → Matrices.ComplexMatrix2) = iterCovariantDeriv L n k U k B :=
    linearMapWithValues_apply covariant
  have vN : ∀ B : edgeFormSpace L n k 0,
      (linearMapWithValues (edgeFormSpace L n k 0) (vertexFunctionSpace L n k k)
        (iterContourLogDrift L n k U k) B : Vertex L n k k → Matrices.ComplexMatrix2) =
        iterContourLogDrift L n k U k B :=
    linearMapWithValues_apply drift
  have vR' : ∀ l : vertexFunctionSpace L n k 0, (iterAverageLinear L n k U l :
      Vertex L n k k → Matrices.ComplexMatrix2) = iterAdjointCubeAverage L n k U k l :=
    linearMapWithValues_apply block
  obtain ⟨r₀, rt, hr, hrtp, hext, hrrt, hrsurj⟩ :
      ∃ (r₀ : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k)
        (rt : vertexFunctionSpace L n k k →ₗ[ℝ] vertexFunctionSpace L n k 0),
        (∀ l : vertexFunctionSpace L n k 0, (r₀ l : Vertex L n k k → Matrices.ComplexMatrix2) =
          restrictVertexFunction k (l : Vertex L n k 0 → Matrices.ComplexMatrix2)) ∧
        (∀ (g : vertexFunctionSpace L n k k) (l : vertexFunctionSpace L n k 0),
          traceFinsumPairing (rt g : Vertex L n k 0 → Matrices.ComplexMatrix2)
              (l : Vertex L n k 0 → Matrices.ComplexMatrix2) =
            traceFinsumPairing (g : Vertex L n k k → Matrices.ComplexMatrix2)
              (r₀ l : Vertex L n k k → Matrices.ComplexMatrix2)) ∧
        (∀ g : vertexFunctionSpace L n k k, (rt g : Vertex L n k 0 → Matrices.ComplexMatrix2) =
          RealLinearMaps.extendByZero (g : Vertex L n k k → Matrices.ComplexMatrix2)) ∧
        (∀ g, r₀ (rt g) = g) ∧ Function.Surjective r₀ := by
    obtain ⟨r, hr, hrt⟩ := hG.linear.exists_restriction
    exact ⟨r, PairedFunctionSpace.realTransposeMap r, hr, hrt.pair_transpose,
      hrt.transpose_eq_extendByZero, hrt.comp_transpose, hrt.surjective⟩
  have hDtp : ∀ (B : edgeFormSpace L n k 0) (l : vertexFunctionSpace L n k 0),
      traceFinsumPairing (covDiffRealTranspose L n k U B : Vertex L n k 0 → Matrices.ComplexMatrix2)
          (l : Vertex L n k 0 → Matrices.ComplexMatrix2) =
        edgeFormPairing (B : Edge L n k 0 → Matrices.ComplexMatrix2)
          (covDiffLinear L n k U l : Edge L n k 0 → Matrices.ComplexMatrix2) := by
    obtain ⟨T, -, -, -, h⟩ := hG.realTranspose 0 (Nat.zero_le k) U mem
    exact fun B l => h B l
  have hR'tp : ∀ (g : vertexFunctionSpace L n k k) (l : vertexFunctionSpace L n k 0),
      traceFinsumPairing (iterAverageRealTranspose L n k U g :
          Vertex L n k 0 → Matrices.ComplexMatrix2)
          (l : Vertex L n k 0 → Matrices.ComplexMatrix2) =
        traceFinsumPairing (g : Vertex L n k k → Matrices.ComplexMatrix2)
          (iterAverageLinear L n k U l : Vertex L n k k → Matrices.ComplexMatrix2) := by
    obtain ⟨T, -, -, -, h⟩ := tr.average_transpose
    exact fun g l => h g l
  have hrel := hG.relations U small
  obtain ⟨P, hP⟩ : ∃ P : vertexFunctionsVanishingAtTop L n k ≃ₗ[ℝ]
      ∀ i : Fin k, fineOnlyFunctions L n k i, ∀ (l : vertexFunctionsVanishingAtTop L n k)
        (i : Fin k), (P l i : FineOnlyVertex L n k i → Matrices.ComplexMatrix2) =
          fineOnlyComponents (l : Vertex L n k 0 → Matrices.ComplexMatrix2) i := by
    obtain ⟨e, he⟩ := hG.layers.restrict_bijective
    have hEq : vertexFunctionsVanishingAtTop L n k = vertexFunctionsVanishingOnTop L n k :=
      Submodule.ext (mem_vanishingAtTop_iff hG.pos)
    exact ⟨(LinearEquiv.ofEq _ _ hEq).trans e, fun l i => he _ i⟩
  have hOff : ∀ x y : vertexFunctionsVanishingAtTop L n k,
      fineOnlyComponents (x : Vertex L n k 0 → Matrices.ComplexMatrix2) =
        fineOnlyComponents (y : Vertex L n k 0 → Matrices.ComplexMatrix2) → x = y :=
    fun x y h =>
      P.injective (funext fun i =>
        Subtype.ext ((hP x i).trans ((congrFun h i).trans (hP y i).symm)))
  obtain ⟨Gf, hGf⟩ : ∃ Gf : LinearMap.ker (topConstraintMap L n k W) →ₗ[ℝ]
      vertexFunctionsVanishingAtTop L n k, ∀ B : LinearMap.ker (topConstraintMap L n k W),
        fineOnlyComponents (Gf B : Vertex L n k 0 → Matrices.ComplexMatrix2) =
          contourFamily W B.1 := by
    obtain ⟨A, hA⟩ := hT.contour
    let C : fineOnlyFamilySpace L n k →ₗ[ℝ] ∀ i : Fin k, fineOnlyFunctions L n k i :=
      LinearMap.pi fun i =>
        { toFun := fun f => ⟨f.1 i, f.2 i (mem_univ i)⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
    refine ⟨P.symm.toLinearMap ∘ₗ C ∘ₗ A ∘ₗ (LinearMap.ker (topConstraintMap L n k W)).subtype,
      fun B => funext fun i => ?_⟩
    have e := hP (P.symm (C (A B.1))) i
    rw [P.apply_symm_apply] at e
    exact e.symm.trans (congrFun (hA B.1) i)
  obtain ⟨D₀, hD₀, ⟨hD, hinv⟩, -, Tm, hTm, hdet⟩ := hdirs
  have hD₀U := hDirU D₀ hD₀
  obtain ⟨σ, hσ⟩ := op.gaugeParameter_linear
  have hX : IsBackgroundHessian U J μ (backgroundHessian U J μ) :=
    Classical.epsilon_spec (op.existsUnique_hessian J μ).exists
  refine ⟨{
    grad := covDiffLinear L n k U
    gradAdjoint := covDiffRealTranspose L n k U
    topGrad := linearMapWithValues (vertexFunctionSpace L n k k) (edgeFormSpace L n k k)
      (covDiff W)
    restr := r₀
    restrAdjoint := rt
    newRestrAdjoint := iterAverageRealTranspose L n k U
    shift := linearMapWithValues (edgeFormSpace L n k 0) (vertexFunctionSpace L n k k)
      (iterContourLogDrift L n k U k)
    hessForm := fibreRestrictedHessian L n k W
    gaugeMap := Gf
    gaugeMapOnKernel := Tm
    grad_injective := ?_
    topGrad_injective := ?_
    constraint_surjective := ?_
    restr_surjective := hrsurj
    restr_apply := hr
    constraint_grad := ?_
    gradAdjoint_pair := hDtp
    restrAdjoint_pair := hrtp
    restr_restrAdjoint := hrrt
    newRestrAdjoint_pair := hR'tp
    newRestr_eq := ?_
    newConstraint_eq := ?_
    newRestr_newRestrAdjoint := tr.average_comp_transpose
    vertexOp_eq := fun _ => rfl
    hessForm_add_grad := ?_
    quadratic_eq := ?_
    posDef := hT.normaliser.2
    gaugeMapOnKernel_apply := ?_
    abs_det_gaugeMapOnKernel := hdet
    edgeOp_symm := hX.1
    edgeOp_quadratic := ?_ }⟩
  · refine (injective_iff_map_eq_zero _).2 fun l hl => ?_
    have e : covDiff U (l : Vertex L n k 0 → Matrices.ComplexMatrix2) = 0 := by
      rw [← vD l, hl]
      rfl
    exact Subtype.ext (hinjU l l.2 e)
  · refine (injective_iff_map_eq_zero _).2 fun l hl => ?_
    have e : covDiff W (l : Vertex L n k k → Matrices.ComplexMatrix2) = 0 := by
      rw [← vDc l, hl]
      rfl
    exact Subtype.ext (hinj l l.2 e)
  · intro B'
    obtain ⟨B, hB, e⟩ := onto B' B'.2
    exact ⟨⟨B, hB⟩, Subtype.ext ((hQm ⟨B, hB⟩).trans e)⟩
  · intro l
    refine Subtype.ext ((hcon l _ (vD l)).trans ?_)
    rw [vDc, hr l]
  · intro l
    refine Subtype.ext ?_
    have e := (hrel.2.1 l fun x => (l.2 x (mem_univ x)).2).1
    show (iterAverageLinear L n k U l : Vertex L n k k → Matrices.ComplexMatrix2) =
      (r₀ l : Vertex L n k k → Matrices.ComplexMatrix2) +
        (linearMapWithValues (edgeFormSpace L n k 0) (vertexFunctionSpace L n k k)
          (iterContourLogDrift L n k U k) (covDiffLinear L n k U l) :
            Vertex L n k k → Matrices.ComplexMatrix2)
    rw [vR' l, hr l, vN, vD l]
    exact e
  · intro B
    refine Subtype.ext ?_
    have e := hrel.1 B (mem_complexEdgeForms_of_mem B.2)
    show (iterCovariantDerivLinear L n k U B : Edge L n k k → Matrices.ComplexMatrix2) =
      (topConstraintMap L n k W B : Edge L n k k → Matrices.ComplexMatrix2) +
        (linearMapWithValues (vertexFunctionSpace L n k k) (edgeFormSpace L n k k) (covDiff W)
          (linearMapWithValues (edgeFormSpace L n k 0) (vertexFunctionSpace L n k k)
            (iterContourLogDrift L n k U k) B) : Edge L n k k → Matrices.ComplexMatrix2)
    rw [vQ' B, hQc B, vDc, vN B, e, htop]
  · intro B κ h
    have hκ : (κ.1 : Vertex L n k 0 → Matrices.ComplexMatrix2) ∈
        vertexFunctionsVanishingAtTop L n k := by
      refine ⟨κ.1.2, ?_⟩
      rw [← hr]
      exact congrArg Subtype.val (LinearMap.mem_ker.1 κ.2)
    obtain ⟨hB, e⟩ := hinv ⟨κ.1.1, hκ⟩ B.1 (hkilled B)
    have e2 : (⟨D₀ ⟨κ.1.1, hκ⟩, hD _⟩ : LinearMap.ker (topConstraintMap L n k W)) =
        ⟨covDiffLinear L n k U κ.1, h⟩ :=
      Subtype.ext (Subtype.ext ((hD₀U _).trans (vD κ.1).symm))
    rw [e2] at e
    exact e
  · intro B
    rw [hT.normaliser.1 B]
    show fibreRestrictedHessian L n k W B + fineOnlyFamilyNorm (contourFamily W B.1) ^ 2 = _
    congr 1
    have hm := (mem_vanishingAtTop_iff hG.pos _).1 (Gf B).2
    have h1 := hG.layers.pairing_eq_sum _ hm _ hm
    have h2 : fineOnlyFamilyPairing (contourFamily W B.1) (contourFamily W B.1) =
        traceFinsumPairing (Gf B : Vertex L n k 0 → Matrices.ComplexMatrix2)
          (Gf B : Vertex L n k 0 → Matrices.ComplexMatrix2) := by
      rw [h1, ← hGf B]
      rfl
    unfold fineOnlyFamilyNorm
    rw [h2]
    exact Real.sq_sqrt
      (traceFinsumPairing_self_re_nonneg hG.pauli _ fun x => (Gf B).2.1 x (mem_univ x))
  · intro κ l h e
    refine hOff _ _ ?_
    rw [hTm κ, hGf]
    have e' : D₀ κ = covDiffLinear L n k U l :=
      Subtype.ext ((hD₀U κ).trans (by rw [vD l, e]))
    show contourFamily W (D₀ κ) = contourFamily W (covDiffLinear L n k U l)
    rw [e']
  · intro B hB h
    have e1 := hX.2 B
    obtain ⟨h', e2⟩ := hshift B hB
    have e3 : (⟨_, h⟩ : LinearMap.ker (topConstraintMap L n k W)) =
        ⟨backgroundShift L n k U B, h'⟩ := by
      refine Subtype.ext (Subtype.ext ?_)
      rw [op.backgroundShift_apply B]
      show (B : Edge L n k 0 → Matrices.ComplexMatrix2) + (covDiffLinear L n k U (rt _) :
        Edge L n k 0 → Matrices.ComplexMatrix2) = _
      rw [vD, hext, vN B, ← (hσ B).1, (hσ B).2]
    rw [e3, e2, e1]
    rfl
end TransferAlongChain
theorem gaugeFixingTransferDataAlongChain_holds
    (hI : CovDiffInjectiveAtChainBottom)
    (hG : CovDiffUnderTopConstraint)
    (hS : HessianAlongBackgroundShift)
    (hY : RealLinearMaps.RealLinearMapsStatement)
    (hC : ProlongCompositesAndVertexLayers.Statement)
    (hF : SmoothingFibres)
    (hR : RealQuadraticTransposes.Statement)
    (hA : CovariantSmoothingProperties.Statement)
    (hH : FibreHessianAndGaugeDirections)
    (hD : RealDerivEqComplexAtChainBottom)
    (hN : NormaliserProductTheorem)
    (hK : BlockFieldChainProperties)
    (hE : IterLeftChartExpansion)
    (hP : OneLoop.PauliMatrixRelations) :
    GaugeFixingTransferDataAlongChain := by
  intro L n k hL hn hk
  have hT := TransferAlongChain.topHypotheses_eventually hY hC hF hR hE hN hK hD hI hG hH hS
    hL hn hk
  have hO : TransferAlongChain.TowerHypotheses L n k :=
    ⟨lt_of_lt_of_le (by norm_num) hL.2, hP, (hR L n k hL hn hk).1, (hY L n k hL hn hk).2,
      (hC.1 L n k hL hn hk).2.2, ((hA L hL).1 n k hn).2 k le_rfl |>.1⟩
  refine TransferAlongChain.eventuallyNearIdentity_mono hT fun W hW hinj J μ hJ hμ => ?_
  rw [← chainBottom_eq W] at hJ ⊢
  exact TransferAlongChain.transferData_of_top hO hW hinj J μ hJ hμ
end YangMills.Construction.Tower
end
