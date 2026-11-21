import YangMills.Construction.LinearAlgebra.AnnihilatorOfKernelInRangeOfTranspose
import YangMills.Construction.Towers.AxialGaugeOfTheLift
import YangMills.Construction.Towers.FibresOfTheAveragingMaps
import YangMills.Construction.Towers.MultiplierOfTheNextLevel
import YangMills.Construction.Towers.PairingOfTheRealTransposeOnForms
import YangMills.Construction.Towers.PropertiesOfTheGaugeFixingFunctions
import YangMills.Construction.Towers.RealAnalyticMapsAlongPaths
import YangMills.Construction.Towers.SpacesOfFormsAtAFiniteSide
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.NextLevelComposite
open PairedFunctionSpace AxialFunctionFacts
open YangMills.Construction.Matrices (ComplexMatrix2)
open YangMills.Construction.Conventions (IsAdmissibleBlockingFactor)
private structure Ingredients : Prop where
  axial : AxialGaugeOfProlongation
  gauge : AxialFunctionFacts.statement
  range : YangMills.Construction.LinearAlgebra.AnnihilatorOfKernel.AnnihilatorSubsetRangeTransposeRealComplex
  fibres : SmoothingFibres
  spaces : FiniteSideFormSpaces
  paths : diffAtZeroPathsStatement
  analytic : AnalyticMapsAlongCurves
  transpose : RealTransposeEdgeFormPairing
variable {L n k j : ℕ}
private theorem exists_symm_nondegenerate_form (H : Ingredients) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) : FiniteDimensional ℝ (edgeFormSpace L n k j) ∧
    Finite (PositiveEdge L n k j) ∧
    ∃ β : LinearMap.BilinForm ℝ (edgeFormSpace L n k j), (∀ x y, β x y = β y x) ∧
      (∀ x, (∀ y, β x y = 0) → x = 0) ∧
      ∀ x y : edgeFormSpace L n k j, edgeFormPairing (x : Edge L n k j → ComplexMatrix2)
        (y : Edge L n k j → ComplexMatrix2) = ((β x y : ℝ) : ℂ) := by
  obtain ⟨hfin, hfd, -, c, hc⟩ := H.spaces L n k j hL hn hj
  have hsym : ∀ x y, c.inner x y = c.inner y x := fun x y => by
    simpa using c.conj_inner_symm y x
  refine ⟨hfd, hfin, LinearMap.mk₂ ℝ (fun x y => c.inner x y) (fun x y z => c.add_left x y z)
    (fun r x y => by simpa using c.smul_left x y r) (fun x y z => ?_) (fun r x y => ?_), ?_, ?_, ?_⟩
  · rw [hsym x (y + z), c.add_left, hsym y x, hsym z x]
  · have := c.smul_left y x r
    rw [hsym x (r • y)]
    simpa [hsym y x] using this
  · exact fun x y => hsym x y
  · exact fun x h => c.definite x (h x)
  · exact fun x y => hc x y
private theorem curveTangent_congr {γ₁ γ₂ : ℝ → Edge L n k j → ComplexMatrix2}
    (h : γ₁ =ᶠ[𝓝 0] γ₂) : curveTangent γ₁ = curveTangent γ₂ := by
  have h0 : γ₁ 0 = γ₂ 0 := h.self_of_nhds
  unfold curveTangent
  congr 1
  funext b
  have e : (fun t => γ₁ t b) =ᶠ[𝓝 0] fun t => γ₂ t b := h.mono fun t ht => congrFun ht b
  rw [e.deriv_eq, h0]
abbrev _root_.YangMills.SharedProofs.p19450 := @curveTangent_congr
private theorem diffAtZero_of_curve {I : Set ℝ} {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (h : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ) : IsDiffAtZeroPath γ := by
  have hI : I ∈ 𝓝 (0 : ℝ) := h.1.1.mem_nhds h.1.2.2
  exact ⟨Filter.mem_of_superset hI fun t ht => h.2.1 ht,
    fun b hb => (h.2.2 b hb).differentiableAt hI⟩
private theorem eventually_along (H : Ingredients) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) {δ : ℝ → Edge L n k j → ComplexMatrix2} (hδ : IsDiffAtZeroPath δ)
    {U : Edge L n k j → ComplexMatrix2} (h0 : δ 0 = U) {P : (Edge L n k j → ComplexMatrix2) → Prop}
    (hP : ∀ᶠ V in 𝓝[fieldSpace L n k j] U, P V) : ∀ᶠ t in 𝓝 (0 : ℝ), P (δ t) := by
  have h := ((H.paths L n k j hL hn hj).1 δ hδ).2
  rw [h0] at h
  exact h.eventually hP
private theorem leftGradient_eq_of (H : Ingredients) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) {F : (Edge L n k j → ComplexMatrix2) → ℝ} {U : Edge L n k j → ComplexMatrix2}
    {X : edgeFormSpace L n k j}
    (hd : ∀ B : edgeFormSpace L n k j, edgeFormPairing (X : Edge L n k j → ComplexMatrix2)
      (B : Edge L n k j → ComplexMatrix2) = leftDeriv (fun V => (F V : ℂ)) U B) :
    leftGradient (fieldSpace L n k j) (fun V => (F V : ℂ)) U = X := by
  obtain ⟨-, hfin, β, -, hnd, hβ⟩ := exists_symm_nondegenerate_form H hL hn hj
  have hG : IsLeftGradient (fieldSpace L n k j) (fun V => (F V : ℂ)) U X :=
    ⟨⟨fun b hb => (X.2.1 b hb).2, X.2.2⟩, fun _ => X.2, fun B hB _ => hd ⟨B, hB⟩⟩
  have hY : IsLeftGradient (fieldSpace L n k j) (fun V => (F V : ℂ)) U
      (leftGradient (fieldSpace L n k j) (fun V => (F V : ℂ)) U) := Classical.epsilon_spec ⟨_, hG⟩
  have hYf : leftGradient (fieldSpace L n k j) (fun V => (F V : ℂ)) U ∈ edgeFormSpace L n k j :=
    hY.2.1 fun V _ => Complex.ofReal_im _
  have hYX : (⟨_, hYf⟩ : edgeFormSpace L n k j) - X = 0 := hnd _ fun y => by
    have h1 := hY.2.2 y y.2 (Set.toFinite _)
    have h2 := hd y
    have h3 : ((β ⟨_, hYf⟩ y : ℝ) : ℂ) = ((β X y : ℝ) : ℂ) := by
      rw [← hβ, ← hβ]
      exact h1.trans h2.symm
    have h4 : β ⟨_, hYf⟩ y = β X y := by exact_mod_cast h3
    simp [h4]
  exact congrArg Subtype.val (sub_eq_zero.mp hYX)
private theorem exists_analytic_leftGradient (H : Ingredients) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) {𝒪 : Set (Edge L n k j → ComplexMatrix2)}
    {F₀ : (Edge L n k j → ComplexMatrix2) → ℝ} {U : Edge L n k j → ComplexMatrix2}
    (hA : IsAnalyticFieldFunction 𝒪 F₀) (hU : U ∈ 𝒪) :
    ∃ X : edgeFormSpace L n k j, ∀ F₁ : (Edge L n k j → ComplexMatrix2) → ℝ,
      (∀ᶠ V in 𝓝[fieldSpace L n k j] U, F₁ V = F₀ V) →
      leftGradient (fieldSpace L n k j) (fun V => (F₁ V : ℂ)) U = X ∧
      ∀ δ : ℝ → Edge L n k j → ComplexMatrix2, IsDiffAtZeroPath δ → δ 0 = U →
        HasDerivAt (fun t => F₁ (δ t))
          (edgeFormPairing (X : Edge L n k j → ComplexMatrix2) (curveTangent δ)).re 0 := by
  obtain ⟨X, hX, hd⟩ := (H.analytic L n k j j hL hn hj hj).2 𝒪 F₀ hA U hU
  refine ⟨⟨X, hX⟩, fun F₁ he => ?_⟩
  have hd₁ : ∀ δ : ℝ → Edge L n k j → ComplexMatrix2, IsDiffAtZeroPath δ → δ 0 = U →
      HasDerivAt (fun t => F₁ (δ t)) (edgeFormPairing X (curveTangent δ)).re 0 := fun δ hδ h0 =>
    (hd δ hδ h0).congr_of_eventuallyEq (eventually_along H hL hn hj hδ h0 he)
  refine ⟨leftGradient_eq_of H hL hn hj fun B => ?_, hd₁⟩
  obtain ⟨-, -, β, -, -, hβ⟩ := exists_symm_nondegenerate_form H hL hn hj
  have hU' : U ∈ fieldSpace L n k j := hA.1.1 hU
  obtain ⟨hE, hE0, hEt⟩ := (H.paths L n k j hL hn hj).2.2 U hU' B B.2
  have h : HasDerivAt (fun t : ℝ => ((F₁ (PeriodicLattice.expTwist
      ((t : ℂ) • (B : Edge L n k j → ComplexMatrix2)) U) : ℝ) : ℂ))
      (((edgeFormPairing X (curveTangent fun t : ℝ => PeriodicLattice.expTwist
        ((t : ℂ) • (B : Edge L n k j → ComplexMatrix2)) U)).re : ℝ) : ℂ) 0 :=
    (hd₁ _ hE hE0).ofReal_comp
  rw [hEt] at h
  have h' := h.deriv
  have hb : edgeFormPairing X (B : Edge L n k j → ComplexMatrix2) = ((β ⟨X, hX⟩ B : ℝ) : ℂ) :=
    hβ ⟨X, hX⟩ B
  rw [hb, Complex.ofReal_re] at h'
  change edgeFormPairing X (B : Edge L n k j → ComplexMatrix2) = deriv (fun t : ℝ =>
    ((F₁ (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k j → ComplexMatrix2)) U) : ℝ) : ℂ)) 0
  rw [hb, h']
private theorem exists_multiplier (H : Ingredients) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {i : ℕ} (hik : i < k) {b : CriticalBranchData L n k} {𝒰 𝒲 𝒪S 𝒪G 𝒪M : Set _}
    {p : (Edge L n k (i + 1) → ComplexMatrix2) → Edge L n k i → ComplexMatrix2}
    {W : Edge L n k (i + 1) → ComplexMatrix2}
    (hpA : IsAnalyticFieldMap 𝒲 p) (hW : W ∈ 𝒲)
    (hSA : IsAnalyticFieldFunction 𝒪S (b.energy i)) (hS : p W ∈ 𝒪S)
    (hGA : IsAnalyticFieldFunction 𝒪G (axialFunction L n k i)) (hG : p W ∈ 𝒪G)
    (hMA : IsAnalyticFieldMap 𝒪M (smoothingStep L n k i)) (hM : p W ∈ 𝒪M)
    (hfix : ∀ᶠ W' in 𝓝[fieldSpace L n k (i + 1)] W,
      b.gaugeFixedEnergy i (p W') = b.energy i (p W'))
    (hsec : ∀ᶠ W' in 𝓝[fieldSpace L n k (i + 1)] W, smoothingStep L n k i (p W') = W')
    (hnon : ∀ᶠ V in 𝓝[fieldSpace L n k i] p W, 0 ≤ axialFunction L n k i V)
    (hzero : axialFunction L n k i (p W) = 0)
    (hcrit : (fieldCurveData L n k i).IsCriticalOn (CriticalBranchData.levelFibre 𝒰 W)
      (b.gaugeFixedEnergy i) (p W))
    (hker : TangentSpacesAreKernels i (CriticalBranchData.levelFibre 𝒰 W)) :
    ∃ (μ : edgeFormSpace L n k (i + 1)) (X : edgeFormSpace L n k i),
      leftGradient (fieldSpace L n k (i + 1)) (fun W' => (b.gaugeFixedEnergy i (p W') : ℂ)) W = μ ∧
      leftGradient (fieldSpace L n k i) (fun V => (b.energy i V : ℂ)) (p W) = X ∧
      ∀ η : edgeFormSpace L n k i, edgeFormPairing (X : Edge L n k i → ComplexMatrix2)
        (η : Edge L n k i → ComplexMatrix2) =
        edgeFormPairing (μ : Edge L n k (i + 1) → ComplexMatrix2)
          (leftDifferentialLinear (smoothingStep L n k i) (p W) η :
            Edge L n k (i + 1) → ComplexMatrix2) := by
  have hi : i ≤ k := hik.le
  have hi' : i + 1 ≤ k := hik
  obtain ⟨hfd, -, β, hs, hnd, hβ⟩ := exists_symm_nondegenerate_form H hL hn hi
  obtain ⟨hfd', -, β', hs', hnd', hβ'⟩ := exists_symm_nondegenerate_form H hL hn hi'
  obtain ⟨X, hX⟩ := exists_analytic_leftGradient H hL hn hi hSA hS
  obtain ⟨Y, hY⟩ := exists_analytic_leftGradient H hL hn hi hGA hG
  obtain ⟨hXg, hXd⟩ := hX _ (Eventually.of_forall fun _ => rfl)
  obtain ⟨-, hYd⟩ := hY _ (Eventually.of_forall fun _ => rfl)
  have hMp := ((H.analytic L n k i (i + 1) hL hn hi hi').1 _ _ hMA).2 _ hM
  have hpp := ((H.analytic L n k (i + 1) i hL hn hi' hi).1 _ _ hpA).2 _ hW
  let T : edgeFormSpace L n k i →ₗ[ℝ] edgeFormSpace L n k (i + 1) :=
    leftDifferentialLinear (smoothingStep L n k i) (p W)
  have hTv : ∀ B : edgeFormSpace L n k i, (T B : Edge L n k (i + 1) → ComplexMatrix2) =
      leftDifferential (smoothingStep L n k i) (p W) B := hMp.1
  let Tt : edgeFormSpace L n k (i + 1) →ₗ[ℝ] edgeFormSpace L n k i :=
    realTransposeMap (S := edgePairedSpace L n k i) (S' := edgePairedSpace L n k (i + 1)) T
  have hTt : ∀ (g : edgeFormSpace L n k (i + 1)) (f : edgeFormSpace L n k i),
      β (Tt g) f = β' g (T f) := by
    intro g f
    have h := H.transpose L n k i (i + 1) hL hn hi hi' T g f
    have h' : ((β (Tt g) f : ℝ) : ℂ) = ((β' g (T f) : ℝ) : ℂ) := by
      rw [← hβ, ← hβ']
      exact h
    exact_mod_cast h'
  have hform : ∀ {δ : ℝ → Edge L n k i → ComplexMatrix2}, IsDiffAtZeroPath δ →
      curveTangent δ ∈ edgeFormSpace L n k i := fun hδ => ((H.paths L n k i hL hn hi).1 _ hδ).1
  have horth : ∀ d : edgeFormSpace L n k i, T d = 0 → β X d = 0 := by
    intro d hd
    have hdt : (d : Edge L n k i → ComplexMatrix2) ∈
        (fieldCurveData L n k i).tangentSpan (CriticalBranchData.levelFibre 𝒰 W) (p W) :=
      (hker (p W) hcrit.1 d).2 ⟨d.2, by rw [← hTv d, hd]; rfl⟩
    suffices hall : ∀ v ∈ (fieldCurveData L n k i).tangentSpan (CriticalBranchData.levelFibre 𝒰 W) (p W),
        ∃ h : v ∈ edgeFormSpace L n k i, β ⟨v, h⟩ X = 0 by
      obtain ⟨h, e⟩ := hall _ hdt
      rw [hs]
      exact e
    intro v hv
    unfold Geometry.CurveData.tangentSpan at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨I, γ, hγ, hmap, h0, rfl⟩ := hv
      have hpath : IsDiffAtZeroPath γ := diffAtZero_of_curve hγ
      have ht : curveTangent γ ∈ edgeFormSpace L n k i := hform hpath
      have d1 := hXd γ hpath h0
      have d2 := hYd γ hpath h0
      have hz : deriv (fun t => b.gaugeFixedEnergy i (γ t)) 0 = 0 := hcrit.2 I γ hγ hmap h0
      have hmin : IsLocalMin (fun t => axialFunction L n k i (γ t)) 0 := by
        have h := eventually_along H hL hn hi hpath h0 hnon
        filter_upwards [h] with t ht'
        simpa [h0, hzero] using ht'
      have h2 := hmin.hasDerivAt_eq_zero d2
      have hsum : HasDerivAt (fun t => b.gaugeFixedEnergy i (γ t))
          ((edgeFormPairing (X : Edge L n k i → ComplexMatrix2) (curveTangent γ)).re +
            (edgeFormPairing (Y : Edge L n k i → ComplexMatrix2) (curveTangent γ)).re) 0 :=
        d1.add d2
      have h1 : (edgeFormPairing (X : Edge L n k i → ComplexMatrix2) (curveTangent γ)).re = 0 := by
        have := hsum.deriv
        rw [hz, h2, add_zero] at this
        exact this.symm
      refine ⟨ht, ?_⟩
      have hb := hβ X ⟨_, ht⟩
      rw [hs]
      rw [hb, Complex.ofReal_re] at h1
      exact h1
    | zero =>
      refine ⟨zero_mem _, ?_⟩
      have : (⟨0, zero_mem _⟩ : edgeFormSpace L n k i) = 0 := rfl
      rw [this]
      simp
    | add x y _ _ hx hy =>
      obtain ⟨h₁, e₁⟩ := hx
      obtain ⟨h₂, e₂⟩ := hy
      refine ⟨add_mem h₁ h₂, ?_⟩
      have : (⟨x + y, add_mem h₁ h₂⟩ : edgeFormSpace L n k i) = ⟨x, h₁⟩ + ⟨y, h₂⟩ := rfl
      rw [this, map_add, LinearMap.add_apply, e₁, e₂, add_zero]
    | smul r x _ hx =>
      obtain ⟨h₁, e₁⟩ := hx
      refine ⟨Submodule.smul_mem _ r h₁, ?_⟩
      have : (⟨r • x, Submodule.smul_mem _ r h₁⟩ : edgeFormSpace L n k i) = r • ⟨x, h₁⟩ := rfl
      rw [this, map_smul, LinearMap.smul_apply, e₁, smul_zero]
  obtain ⟨μ, hμ⟩ := H.range.1 (edgeFormSpace L n k i) (edgeFormSpace L n k (i + 1)) β β' hs hnd hs'
    hnd' T Tt hTt X horth
  refine ⟨μ, X, ?_, hXg, fun η => ?_⟩
  · refine leftGradient_eq_of H hL hn hi' (F := fun W' => b.gaugeFixedEnergy i (p W')) fun B => ?_
    have hWc : W ∈ fieldSpace L n k (i + 1) := hpA.1.1 hW
    obtain ⟨hE, hE0, hEt⟩ := (H.paths L n k (i + 1) hL hn hi').2.2 W hWc B B.2
    obtain ⟨hδ, hδt⟩ := hpp.2 _ hE hE0
    have hδ0 : p (PeriodicLattice.expTwist
        (((0 : ℝ) : ℂ) • (B : Edge L n k (i + 1) → ComplexMatrix2)) W) = p W :=
      congrArg p hE0
    obtain ⟨-, hεt⟩ := hMp.2 _ hδ hδ0
    have hCf := hform hδ
    have hε : curveTangent (fun t : ℝ => smoothingStep L n k i
        (p (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k (i + 1) → ComplexMatrix2)) W))) = B := by
      have he : (fun t : ℝ => smoothingStep L n k i
          (p (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k (i + 1) → ComplexMatrix2)) W))) =ᶠ[𝓝 0]
          fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k (i + 1) → ComplexMatrix2)) W :=
        eventually_along H hL hn hi' hE hE0 (P := fun V => smoothingStep L n k i (p V) = V) hsec
      rw [curveTangent_congr he, hEt]
    have hTC : (T ⟨_, hCf⟩ : Edge L n k (i + 1) → ComplexMatrix2) = B :=
      (hTv _).trans (hεt.symm.trans hε)
    have hTC' : T ⟨_, hCf⟩ = B := Subtype.ext hTC
    have hev : (fun t : ℝ => b.gaugeFixedEnergy i
        (p (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k (i + 1) → ComplexMatrix2)) W))) =ᶠ[𝓝 0]
        fun t : ℝ => b.energy i
          (p (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k (i + 1) → ComplexMatrix2)) W)) :=
      eventually_along H hL hn hi' hE hE0
        (P := fun W' => b.gaugeFixedEnergy i (p W') = b.energy i (p W')) hfix
    have hd := (hXd _ hδ hδ0).congr_of_eventuallyEq hev
    have h : HasDerivAt (fun t : ℝ => ((b.gaugeFixedEnergy i
        (p (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k (i + 1) → ComplexMatrix2)) W)) : ℝ) : ℂ))
        (((edgeFormPairing (X : Edge L n k i → ComplexMatrix2) (curveTangent fun t : ℝ =>
          p (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k (i + 1) → ComplexMatrix2)) W))).re :
            ℝ) : ℂ) 0 :=
      hd.ofReal_comp
    have hval : edgeFormPairing (X : Edge L n k i → ComplexMatrix2) (curveTangent fun t : ℝ =>
          p (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k (i + 1) → ComplexMatrix2)) W)) =
        ((β' μ B : ℝ) : ℂ) := by
      have := hβ X ⟨_, hCf⟩
      rw [show β X ⟨_, hCf⟩ = β' μ B by rw [hμ, hTt, hTC']] at this
      exact this
    rw [hval, Complex.ofReal_re] at h
    change edgeFormPairing (μ : Edge L n k (i + 1) → ComplexMatrix2)
      (B : Edge L n k (i + 1) → ComplexMatrix2) =
      deriv (fun t : ℝ => ((b.gaugeFixedEnergy i
        (p (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L n k (i + 1) → ComplexMatrix2)) W)) : ℝ) :
          ℂ)) 0
    rw [hβ', h.deriv]
  · rw [hβ, hβ', hμ, hTt]
private theorem exists_action_gradient (H : Ingredients) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {i : ℕ} (hik : i < k) {b : CriticalBranchData L n k}
    {𝒪M : Set (Edge L n k i → ComplexMatrix2)}
    {𝒪₀ 𝒪₁ 𝒪₂ : Set (Edge L n k 0 → ComplexMatrix2)} {V : Edge L n k i → ComplexMatrix2}
    {μ : edgeFormSpace L n k (i + 1)} {X : edgeFormSpace L n k i}
    (hXg : leftGradient (fieldSpace L n k i) (fun V => (b.energy i V : ℂ)) V = X)
    (hμ : ∀ η : edgeFormSpace L n k i, edgeFormPairing (X : Edge L n k i → ComplexMatrix2)
      (η : Edge L n k i → ComplexMatrix2) =
      edgeFormPairing (μ : Edge L n k (i + 1) → ComplexMatrix2)
        (leftDifferentialLinear (smoothingStep L n k i) V η : Edge L n k (i + 1) → ComplexMatrix2))
    (hMA : IsAnalyticFieldMap 𝒪M (smoothingStep L n k i)) (hM : V ∈ 𝒪M)
    (h₁A : IsAnalyticFieldMap 𝒪₁ (smoothingIter L n k (i + 1)))
    (h₁ : b.prolongComp i V ∈ 𝒪₁)
    (h₂A : 0 < i → IsAnalyticFieldMap 𝒪₂ (smoothingIter L n k i))
    (h₂ : b.prolongComp i V ∈ 𝒪₂)
    (hIter : smoothingIter L n k i (b.prolongComp i V) = V)
    (hrel : b.SatisfiesMultiplierIdentity i V)
    (hSA : IsAnalyticFieldFunction 𝒪₀ (b.energy 0)) (h₀ : b.prolongComp i V ∈ 𝒪₀)
    (hAU : ∀ᶠ U in 𝓝[fieldSpace L n k 0] b.prolongComp i V, plaquetteAction L n k U = b.energy 0 U) :
    ∃ Z : edgeFormSpace L n k 0,
      leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ)) (b.prolongComp i V) = Z ∧
      ∀ f : edgeFormSpace L n k 0, edgeFormPairing (Z : Edge L n k 0 → ComplexMatrix2)
        (f : Edge L n k 0 → ComplexMatrix2) =
        edgeFormPairing (μ : Edge L n k (i + 1) → ComplexMatrix2)
          (leftDifferentialLinear (smoothingIter L n k (i + 1)) (b.prolongComp i V) f :
            Edge L n k (i + 1) → ComplexMatrix2) := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · obtain ⟨X₀, hX₀⟩ := exists_analytic_leftGradient H hL hn (Nat.zero_le k) hSA h₀
    have e1 := (hX₀ _ hAU).1
    have e2 := (hX₀ (b.energy 0) (Eventually.of_forall fun _ => rfl)).1
    have hXX : X = X₀ := Subtype.ext (hXg.symm.trans e2)
    subst hXX
    exact ⟨X, e1, hμ⟩
  · obtain ⟨g, hg, hT⟩ := hrel
    have hgX : g = X := Subtype.ext (hg.trans hXg)
    subst hgX
    refine ⟨realTransposeMap (S := edgePairedSpace L n k 0) (S' := edgePairedSpace L n k i)
      (leftDifferentialLinear (smoothingIter L n k i) (b.prolongComp i V)) g, hT.symm, fun f => ?_⟩
    have hi : i ≤ k := hik.le
    have hi' : i + 1 ≤ k := hik
    have h0 : 0 ≤ k := Nat.zero_le k
    rw [H.transpose L n k 0 i hL hn h0 hi, hμ]
    have hUc : b.prolongComp i V ∈ fieldSpace L n k 0 := h₁A.1.1 h₁
    obtain ⟨hE, hE0, hEt⟩ := (H.paths L n k 0 hL hn h0).2.2 _ hUc f f.2
    have a2 := ((H.analytic L n k 0 i hL hn h0 hi).1 _ _ (h₂A hpos)).2 _ h₂
    have a1 := ((H.analytic L n k 0 (i + 1) hL hn h0 hi').1 _ _ h₁A).2 _ h₁
    have aM := ((H.analytic L n k i (i + 1) hL hn hi hi').1 _ _ hMA).2 _ hM
    obtain ⟨hδ, hδt⟩ := a2.2 _ hE hE0
    have hδ0 : smoothingIter L n k i (PeriodicLattice.expTwist
        (((0 : ℝ) : ℂ) • (f : Edge L n k 0 → ComplexMatrix2)) (b.prolongComp i V)) = V := by
      rw [hE0, hIter]
    obtain ⟨-, hεt⟩ := aM.2 _ hδ hδ0
    obtain ⟨-, hηt⟩ := a1.2 _ hE hE0
    rw [hEt] at hδt hηt
    have key : leftDifferentialLinear (smoothingStep L n k i) V
        (leftDifferentialLinear (smoothingIter L n k i) (b.prolongComp i V) f) =
        leftDifferentialLinear (smoothingIter L n k (i + 1)) (b.prolongComp i V) f := by
      apply Subtype.ext
      rw [aM.1, a2.1 f, a1.1 f, ← hδt, ← hεt, ← hηt]
      rfl
    rw [key]
private theorem isCriticalOn_fibre (H : Ingredients) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {i : ℕ} (hik : i < k) {b : CriticalBranchData L n k}
    {𝒪₀ 𝒪₁ 𝒱 : Set (Edge L n k 0 → ComplexMatrix2)}
    {U : Edge L n k 0 → ComplexMatrix2} {W : Edge L n k (i + 1) → ComplexMatrix2}
    {μ : edgeFormSpace L n k (i + 1)} {Z : edgeFormSpace L n k 0}
    (hZ : leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ)) U = Z)
    (hpair : ∀ f : edgeFormSpace L n k 0, edgeFormPairing (Z : Edge L n k 0 → ComplexMatrix2)
      (f : Edge L n k 0 → ComplexMatrix2) =
      edgeFormPairing (μ : Edge L n k (i + 1) → ComplexMatrix2)
        (leftDifferentialLinear (smoothingIter L n k (i + 1)) U f : Edge L n k (i + 1) → ComplexMatrix2))
    (h₁A : IsAnalyticFieldMap 𝒪₁ (smoothingIter L n k (i + 1))) (h₁ : U ∈ 𝒪₁)
    (hSA : IsAnalyticFieldFunction 𝒪₀ (b.energy 0)) (h₀ : U ∈ 𝒪₀)
    (hAU : ∀ᶠ U' in 𝓝[fieldSpace L n k 0] U, plaquetteAction L n k U' = b.energy 0 U')
    (hmem : U ∈ 𝒱) (hIt : smoothingIter L n k (i + 1) U = W)
    (hker : HasKernelTangentSpaces (smoothingIter L n k (i + 1))
      (fibreWithin 𝒱 (smoothingIter L n k (i + 1)) W)) :
    (fieldCurveData L n k 0).IsCriticalOn {U | U ∈ 𝒱 ∧ smoothingIter L n k (i + 1) U = W}
      (plaquetteAction L n k) U := by
  refine ⟨⟨hmem, hIt⟩, fun I γ hγ hmap h0 => ?_⟩
  obtain ⟨X₀, hX₀⟩ := exists_analytic_leftGradient H hL hn (Nat.zero_le k) hSA h₀
  obtain ⟨e1, hd⟩ := hX₀ _ hAU
  have hXZ : X₀ = Z := Subtype.ext (e1.symm.trans hZ)
  subst hXZ
  have hpath : IsDiffAtZeroPath γ := diffAtZero_of_curve hγ
  have hv : curveTangent γ ∈ (fieldCurveData L n k 0).tangentSpan
      (fibreWithin 𝒱 (smoothingIter L n k (i + 1)) W) U :=
    Submodule.subset_span ⟨I, γ, hγ, hmap, h0, rfl⟩
  obtain ⟨hvf, hvk⟩ := (hker U ⟨hmem, hIt⟩ _).1 hv
  have a1 := ((H.analytic L n k 0 (i + 1) hL hn (Nat.zero_le k) hik).1 _ _ h₁A).2 _ h₁
  have hT : leftDifferentialLinear (smoothingIter L n k (i + 1)) U ⟨_, hvf⟩ = 0 :=
    Subtype.ext (by rw [a1.1]; exact hvk)
  have hp := hpair ⟨_, hvf⟩
  rw [hT] at hp
  obtain ⟨-, -, β', -, -, hβ'⟩ := exists_symm_nondegenerate_form H hL hn (j := i + 1) hik
  have hzero : edgeFormPairing (μ : Edge L n k (i + 1) → ComplexMatrix2)
      ((0 : edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) = 0 := by
    rw [hβ']
    simp
  rw [hzero] at hp
  rw [(hd γ hpath h0).deriv]
  change (edgeFormPairing (X₀ : Edge L n k 0 → ComplexMatrix2) (curveTangent γ)).re = 0
  change edgeFormPairing (X₀ : Edge L n k 0 → ComplexMatrix2) (curveTangent γ) = 0 at hp
  rw [hp]
  rfl
private theorem tendsto_trivial_of_analytic (H : Ingredients) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {a c : ℕ} (ha : a ≤ k) (hc : c ≤ k) {𝒲 : Set (Edge L n k a → ComplexMatrix2)}
    {m : (Edge L n k a → ComplexMatrix2) → Edge L n k c → ComplexMatrix2} (hO : IsOpenNhdOfOne 𝒲)
    (hm : IsAnalyticFieldMap 𝒲 m)
    (h1 : m (trivialField L n k a) = trivialField L n k c) :
    Tendsto m (𝓝[fieldSpace L n k a] trivialField L n k a)
      (𝓝[fieldSpace L n k c] trivialField L n k c) := by
  have hnear := (H.paths L n k a hL hn ha).2.1 𝒲 hO.1 _ hO.2
  have hcont := ((H.analytic L n k a c hL hn ha hc).1 𝒲 m hm).1 _ hO.2
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.mem_of_superset hnear fun W hW => hm.2.1 hW⟩
  have h := hcont.tendsto.mono_left (nhdsWithin_le_of_mem hnear)
  rwa [h1] at h
private theorem tendsto_prolongComp (H : Ingredients) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {i : ℕ} (hi : i ≤ k) {b : CriticalBranchData L n k} (hb : b.IsCriticalUpTo i) :
    ∀ j, j ≤ i → Tendsto (b.prolongComp j)
      (𝓝[fieldSpace L n k j] trivialField L n k j)
      (𝓝[fieldSpace L n k 0] trivialField L n k 0) := by
  intro j
  induction j with
  | zero => intro _; exact tendsto_id
  | succ j ih =>
    intro hj
    obtain ⟨𝒲, hO, hA⟩ := hb.analytic_prolong j hj
    exact (ih (by omega)).comp
      (tendsto_trivial_of_analytic H hL hn (by omega) (by omega) hO hA (hb.prolong_trivial j hj))
theorem statement_proof (hAx : AxialGaugeOfProlongation)
    (hGF : AxialFunctionFacts.statement)
    (hR : YangMills.Construction.LinearAlgebra.AnnihilatorOfKernel.AnnihilatorSubsetRangeTransposeRealComplex)
    (hFib : SmoothingFibres) (hSp : FiniteSideFormSpaces)
    (hPa : diffAtZeroPathsStatement) (hAn : AnalyticMapsAlongCurves)
    (hTr : RealTransposeEdgeFormPairing) : Statement := by
  intro L n k i hL hn hik b 𝒰 ε p hb hp
  have H : Ingredients := ⟨hAx, hGF, hR, hFib, hSp, hPa, hAn, hTr⟩
  have hi : i ≤ k := hik.le
  have hi' : i + 1 ≤ k := hik
  have h00 : 0 ≤ k := Nat.zero_le k
  obtain ⟨𝒲, hWo, hpA⟩ := hp.analytic_section
  have hpT := tendsto_trivial_of_analytic H hL hn hi' hi hWo hpA hp.section_trivial
  have hcT := tendsto_prolongComp H hL hn hi hb i le_rfl
  have hcpT := hcT.comp hpT
  obtain ⟨𝒪S, hOS, hSA⟩ := hb.analytic_energy i le_rfl
  have gf := H.gauge L n k i hL hn hik
  obtain ⟨𝒪G, hOG, -, hGA⟩ := gf.analytic_near_identity
  obtain ⟨-, -, -, ⟨𝒪M, hOM, -, hMA, -⟩, ⟨𝒪₁, hO1, -, h₁A, -⟩, -, ⟨𝒱, hV, -, hfib⟩⟩ :=
    H.fibres L n k i hL hn hik
  obtain ⟨𝒪₀, hO0, hS0A⟩ := hb.analytic_energy 0 (Nat.zero_le _)
  obtain ⟨𝒪₂, hO2, h₂A⟩ : ∃ 𝒪₂ : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒪₂ ∧
      (0 < i → IsAnalyticFieldMap 𝒪₂ (smoothingIter L n k i)) := by
    rcases i with _ | i'
    · exact ⟨𝒪₀, hO0, fun h => absurd h (lt_irrefl _)⟩
    · obtain ⟨-, -, -, -, ⟨𝒪, hO, -, hA, -⟩, -, -⟩ := H.fibres L n k i' hL hn (by omega)
      exact ⟨𝒪, hO, fun _ => hA⟩
  have nhd : ∀ {j : ℕ}, j ≤ k → ∀ {𝒪 : Set (Edge L n k j → ComplexMatrix2)}, IsOpenNhdOfOne 𝒪 →
      𝒪 ∈ 𝓝[fieldSpace L n k j] trivialField L n k j :=
    fun hj _ hO => (H.paths L n k _ hL hn hj).2.1 _ hO.1 _ hO.2
  have hax := H.axial L n k i hL hn hik b 𝒰 ε p hb hp
  have e1 : ∀ᶠ W in 𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1), W ∈ 𝒲 :=
    nhd hi' hWo
  have e2 := hpT.eventually (nhd hi hOS)
  have e3 := hpT.eventually (nhd hi hOG)
  have e4 := hpT.eventually (nhd hi hOM)
  have e5 := hcpT.eventually (nhd h00 hO1)
  have e6 := hcpT.eventually (nhd h00 hO2)
  have e7 := hcpT.eventually (nhd h00 hO0)
  have e8 := hcpT.eventually (nhd h00 hV)
  have e9 := hpT.eventually (hb.prolongComp_section i le_rfl)
  have eFix := eventually_eventually_nhdsWithin.2 (hax.mono fun W h => h.2)
  have eSec := eventually_eventually_nhdsWithin.2 hp.smoothing_section
  have eNon := hpT.eventually (eventually_eventually_nhdsWithin.2 gf.nonneg)
  have eZ := hpT.eventually gf.eq_zero_iff
  have eAU := hcpT.eventually (eventually_eventually_nhdsWithin.2
    (hb.energy_bottom.mono fun U h => h.symm))
  have hl : (b.extendLevel i p).prolong i = p := by
    simp [CriticalBranchData.extendLevel]
  have hfun : (b.extendLevel i p).energy (i + 1) = fun W => b.gaugeFixedEnergy i (p W) := by
    simp [CriticalBranchData.extendLevel]
  have hlow : ∀ j, j < i → (b.extendLevel i p).prolong j = b.prolong j := by
    intro j hj
    have : j ≠ i := by omega
    simp [CriticalBranchData.extendLevel, Function.update_of_ne this]
  have hc : ∀ j, j ≤ i → (b.extendLevel i p).prolongComp j = b.prolongComp j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      simp only [CriticalBranchData.prolongComp]
      rw [ih (by omega), hlow j (by omega)]
  have hcomp : ∀ W, (b.extendLevel i p).prolongComp (i + 1) W = b.prolongComp i (p W) := by
    intro W
    simp only [CriticalBranchData.prolongComp]
    rw [hc i le_rfl, hl]
    rfl
  have main : ∀ᶠ W in 𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1),
      ∃ (μ : edgeFormSpace L n k (i + 1)) (Z : edgeFormSpace L n k 0),
        leftGradient (fieldSpace L n k (i + 1)) (fun W' => (b.gaugeFixedEnergy i (p W') : ℂ)) W = μ ∧
        leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
          (b.prolongComp i (p W)) = Z ∧
        ∀ f : edgeFormSpace L n k 0, edgeFormPairing (Z : Edge L n k 0 → ComplexMatrix2)
          (f : Edge L n k 0 → ComplexMatrix2) =
          edgeFormPairing (μ : Edge L n k (i + 1) → ComplexMatrix2)
            (leftDifferentialLinear (smoothingIter L n k (i + 1)) (b.prolongComp i (p W)) f :
              Edge L n k (i + 1) → ComplexMatrix2) := by
    filter_upwards [e1, e2, e3, e4, e5, e6, e7, e9, eFix, eSec, eNon, eZ, eAU, hax, hp.unique_critical,
      hp.fibre_structure] with W w1 w2 w3 w4 w5 w6 w7 w9 wFix wSec wNon wZ wAU wax wcrit wfib
    obtain ⟨μ, X, hg, hXg, hmu⟩ := exists_multiplier H hL hn hik hpA w1 hSA w2 hGA w3 hMA w4 wFix
      wSec wNon (wZ.2 wax.1) wcrit.1.2.1 wfib.2
    obtain ⟨Z, hZ, hpair⟩ := exists_action_gradient H hL hn hik hXg hmu hMA w4 h₁A w5 h₂A w6 w9.1
      w9.2.2 hS0A w7 wAU
    exact ⟨μ, Z, hg, hZ, hpair⟩
  have hIter : ∀ᶠ W in 𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1),
      smoothingIter L n k (i + 1) (b.prolongComp i (p W)) = W := by
    filter_upwards [e9, hp.smoothing_section] with W w9 wsec
    change smoothingStep L n k i (smoothingIter L n k i (b.prolongComp i (p W))) = W
    rw [w9.1]
    exact wsec
  obtain ⟨-, -, β₀, -, hnd₀, hβ₀⟩ := exists_symm_nondegenerate_form H hL hn h00
  refine ⟨?_, ?_, 𝒱, hV, ?_⟩
  · filter_upwards [main, e9, hax, hIter] with W wm w9 wax wI
    obtain ⟨μ, Z, hg, hZ, hpair⟩ := wm
    simp only [CriticalBranchData.SatisfiesMultiplierIdentity, CriticalBranchData.energyGradient]
    rw [hcomp W, hfun]
    refine ⟨wI, ?_, μ, hg.symm, ?_⟩
    · change b.gaugeFixedEnergy i (p W) = _
      rw [wax.2]
      exact w9.2.1
    · rw [hZ]
      let R : edgeFormSpace L n k 0 := realTransposeMap (S := edgePairedSpace L n k 0)
        (S' := edgePairedSpace L n k (i + 1))
        (leftDifferentialLinear (smoothingIter L n k (i + 1)) (b.prolongComp i (p W))) μ
      have hzero : R - Z = 0 := hnd₀ _ fun y => by
        have h3 : ((β₀ R y : ℝ) : ℂ) = ((β₀ Z y : ℝ) : ℂ) := by
          rw [← hβ₀, ← hβ₀]
          exact (H.transpose L n k 0 (i + 1) hL hn h00 hi'
            (leftDifferentialLinear (smoothingIter L n k (i + 1)) (b.prolongComp i (p W))) μ y).trans
            (hpair y).symm
        have h4 : β₀ R y = β₀ Z y := by exact_mod_cast h3
        simp [h4]
      exact congrArg Subtype.val (sub_eq_zero.mp hzero)
  · filter_upwards [e9] with W w9
    rw [hcomp W]
    exact w9.1
  · filter_upwards [main, e5, e7, e8, eAU, hIter, hfib] with W wm w5 w7 w8 wAU wI wfib
    obtain ⟨μ, Z, -, hZ, hpair⟩ := wm
    rw [hcomp W]
    exact isCriticalOn_fibre H hL hn hik hZ hpair h₁A w5 hS0A w7 wAU w8 wI wfib.2
end YangMills.Construction.Tower.NextLevelComposite
end
