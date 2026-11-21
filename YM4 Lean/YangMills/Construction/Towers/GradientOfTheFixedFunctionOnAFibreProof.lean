import YangMills.Construction.Towers.GradientOfTheFixedFunctionOnAFibre
import YangMills.Construction.Towers.MultiplierOfTheNextLevelProof
import YangMills.Construction.Towers.TheFixedFamilyOfTheCriticalBranch
import YangMills.Construction.Towers.TheFormOnAFibreOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FibreGradient
open YangMills.Construction.Matrices (ComplexMatrix2)
open PairedFunctionSpace
variable {L m k j : ℕ}
private theorem symmetric_bilinear_exists (hS : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k) :
    FiniteDimensional ℝ (edgeFormSpace L m k j) ∧ Finite (PositiveEdge L m k j) ∧
    ∃ β : LinearMap.BilinForm ℝ (edgeFormSpace L m k j), (∀ x y, β x y = β y x) ∧
      (∀ x, (∀ y, β x y = 0) → x = 0) ∧
      ∀ x y : edgeFormSpace L m k j,
        edgeFormPairing (x : Edge L m k j → ComplexMatrix2) (y : Edge L m k j → ComplexMatrix2) =
          ((β x y : ℝ) : ℂ) := by
  obtain ⟨hfin, hfd, -, c, hc⟩ := hS L m k j hL hm hj
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
private theorem curveTangent_congr {γ₁ γ₂ : ℝ → Edge L m k j → ComplexMatrix2}
    (h : γ₁ =ᶠ[𝓝 0] γ₂) : curveTangent γ₁ = curveTangent γ₂ := by apply _root_.YangMills.SharedProofs.p19450 <;> assumption
private theorem isDiffAtZeroPath_of_curve {I : Set ℝ} {γ : ℝ → Edge L m k j → ComplexMatrix2}
    (h : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ) : IsDiffAtZeroPath γ := by
  have hI : I ∈ 𝓝 (0 : ℝ) := h.1.1.mem_nhds h.1.2.2
  exact ⟨Filter.mem_of_superset hI fun t ht => h.2.1 ht,
    fun e he => (h.2.2 e he).differentiableAt hI⟩
private theorem eventually_along_path (hP : diffAtZeroPathsStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k)
    {δ : ℝ → Edge L m k j → ComplexMatrix2} (hδ : IsDiffAtZeroPath δ)
    {U : Edge L m k j → ComplexMatrix2} (h0 : δ 0 = U) {Q : (Edge L m k j → ComplexMatrix2) → Prop}
    (hQ : ∀ᶠ V in 𝓝[fieldSpace L m k j] U, Q V) : ∀ᶠ t in 𝓝 (0 : ℝ), Q (δ t) := by
  have h := ((hP L m k j hL hm hj).1 δ hδ).2
  rw [h0] at h
  exact h.eventually hQ
private theorem leftGradient_eq_of_deriv (hS : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hj : j ≤ k) {F : (Edge L m k j → ComplexMatrix2) → ℝ} {U : Edge L m k j → ComplexMatrix2}
    {X : edgeFormSpace L m k j}
    (hd : ∀ B : edgeFormSpace L m k j,
      edgeFormPairing (X : Edge L m k j → ComplexMatrix2) (B : Edge L m k j → ComplexMatrix2) =
        leftDeriv (fun V => (F V : ℂ)) U B) :
    leftGradient (fieldSpace L m k j) (fun V => (F V : ℂ)) U = X := by
  obtain ⟨-, hfin, β, -, hnd, hβ⟩ := symmetric_bilinear_exists hS hL hm hj
  have hG : IsLeftGradient (fieldSpace L m k j) (fun V => (F V : ℂ)) U X :=
    ⟨⟨fun e he => (X.2.1 e he).2, X.2.2⟩, fun _ => X.2, fun B hB _ => hd ⟨B, hB⟩⟩
  have hY : IsLeftGradient (fieldSpace L m k j) (fun V => (F V : ℂ)) U
      (leftGradient (fieldSpace L m k j) (fun V => (F V : ℂ)) U) := Classical.epsilon_spec ⟨_, hG⟩
  have hYf : leftGradient (fieldSpace L m k j) (fun V => (F V : ℂ)) U ∈ edgeFormSpace L m k j :=
    hY.2.1 fun V _ => Complex.ofReal_im _
  have hYX : (⟨_, hYf⟩ : edgeFormSpace L m k j) - X = 0 := hnd _ fun y => by
    have h1 := hY.2.2 y y.2 (Set.toFinite _)
    have h2 := hd y
    have h3 : ((β ⟨_, hYf⟩ y : ℝ) : ℂ) = ((β X y : ℝ) : ℂ) := by
      rw [← hβ, ← hβ]
      exact h1.trans h2.symm
    have h4 : β ⟨_, hYf⟩ y = β X y := by exact_mod_cast h3
    simp [h4]
  exact congrArg Subtype.val (sub_eq_zero.mp hYX)
private theorem analytic_leftGradient (hS : FiniteSideFormSpaces)
    (hP : diffAtZeroPathsStatement) (hA : AnalyticMapsAlongCurves)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hj : j ≤ k) {𝒪 : Set (Edge L m k j → ComplexMatrix2)} {F : (Edge L m k j → ComplexMatrix2) → ℝ}
    {U : Edge L m k j → ComplexMatrix2} (hF : IsAnalyticFieldFunction 𝒪 F) (hU : U ∈ 𝒪) :
    ∃ X : edgeFormSpace L m k j,
      leftGradient (fieldSpace L m k j) (fun V => (F V : ℂ)) U = X ∧
      ∀ δ : ℝ → Edge L m k j → ComplexMatrix2, IsDiffAtZeroPath δ → δ 0 = U →
        HasDerivAt (fun t => F (δ t))
          (edgeFormPairing (X : Edge L m k j → ComplexMatrix2) (curveTangent δ)).re 0 := by
  obtain ⟨X, hX, hd⟩ := (hA L m k j j hL hm hj hj).2 𝒪 F hF U hU
  refine ⟨⟨X, hX⟩, leftGradient_eq_of_deriv hS hL hm hj fun B => ?_, hd⟩
  obtain ⟨-, -, β, -, -, hβ⟩ := symmetric_bilinear_exists hS hL hm hj
  have hU' : U ∈ fieldSpace L m k j := hF.1.1 hU
  obtain ⟨hE, hE0, hEt⟩ := (hP L m k j hL hm hj).2.2 U hU' B B.2
  have h : HasDerivAt
      (fun t : ℝ => ((F (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L m k j → ComplexMatrix2)) U) : ℝ) : ℂ))
      (((edgeFormPairing X (curveTangent fun t : ℝ =>
        PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L m k j → ComplexMatrix2)) U)).re : ℝ) : ℂ) 0 :=
    (hd _ hE hE0).ofReal_comp
  rw [hEt] at h
  have h' := h.deriv
  have hb : edgeFormPairing X (B : Edge L m k j → ComplexMatrix2) = ((β ⟨X, hX⟩ B : ℝ) : ℂ) :=
    hβ ⟨X, hX⟩ B
  rw [hb, Complex.ofReal_re] at h'
  change edgeFormPairing X (B : Edge L m k j → ComplexMatrix2) = deriv (fun t : ℝ =>
    ((F (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L m k j → ComplexMatrix2)) U) : ℝ) : ℂ)) 0
  rw [hb, h']
private theorem transpose_gradient_relation (hS : FiniteSideFormSpaces)
    (hP : diffAtZeroPathsStatement) (hA : AnalyticMapsAlongCurves)
    (hT : RealTransposeEdgeFormPairing)
    (hR : LinearAlgebra.AnnihilatorOfKernel.AnnihilatorSubsetRangeTransposeRealComplex)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℕ} (hik : i < k)
    {b : CriticalBranchData L m k} {𝒰 : Set (Edge L m k i → ComplexMatrix2)}
    {𝒲 : Set (Edge L m k (i + 1) → ComplexMatrix2)} {W : Edge L m k (i + 1) → ComplexMatrix2}
    (hpA : IsAnalyticFieldMap 𝒲 (b.prolong i)) (hW : W ∈ 𝒲)
    (hFA : IsAnalyticFieldFunction 𝒰 (b.gaugeFixedEnergy i))
    (hMA : IsAnalyticFieldMap 𝒰 (smoothingStep L m k i)) (hV : b.prolong i W ∈ 𝒰)
    (hfun : ∀ᶠ W' in 𝓝[fieldSpace L m k (i + 1)] W,
      b.energy (i + 1) W' = b.gaugeFixedEnergy i (b.prolong i W'))
    (hsec : ∀ᶠ W' in 𝓝[fieldSpace L m k (i + 1)] W, smoothingStep L m k i (b.prolong i W') = W')
    (hker : ∀ d : edgeFormSpace L m k i,
      leftDifferentialLinear (smoothingStep L m k i) (b.prolong i W) d = 0 →
      ∃ (I : Set ℝ) (γ : ℝ → Edge L m k i → ComplexMatrix2),
        IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ ∧ γ 0 = b.prolong i W ∧
          curveTangent γ = d ∧ deriv (fun t => b.gaugeFixedEnergy i (γ t)) 0 = 0) :
    ∃ g : edgeFormSpace L m k (i + 1),
      (g : Edge L m k (i + 1) → ComplexMatrix2) = b.energyGradient (i + 1) W ∧
        (realTransposeMap (S := edgePairedSpace L m k i) (S' := edgePairedSpace L m k (i + 1))
            (leftDifferentialLinear (smoothingStep L m k i) (b.prolong i W)) g).1 =
          leftGradient (fieldSpace L m k i) (fun V => (b.gaugeFixedEnergy i V : ℂ)) (b.prolong i W) := by
  have hi : i ≤ k := hik.le
  have hi' : i + 1 ≤ k := hik
  obtain ⟨hfd, -, β, hs, hnd, hβ⟩ := symmetric_bilinear_exists hS hL hm hi
  obtain ⟨hfd', -, β', hs', hnd', hβ'⟩ := symmetric_bilinear_exists hS hL hm hi'
  obtain ⟨X, hXg, hXd⟩ := analytic_leftGradient hS hP hA hL hm hi hFA hV
  have hMp := ((hA L m k i (i + 1) hL hm hi hi').1 _ _ hMA).2 _ hV
  have hpp := ((hA L m k (i + 1) i hL hm hi' hi).1 _ _ hpA).2 _ hW
  let T : edgeFormSpace L m k i →ₗ[ℝ] edgeFormSpace L m k (i + 1) :=
    leftDifferentialLinear (smoothingStep L m k i) (b.prolong i W)
  have hTv : ∀ B : edgeFormSpace L m k i, (T B : Edge L m k (i + 1) → ComplexMatrix2) =
      leftDifferential (smoothingStep L m k i) (b.prolong i W) B := hMp.1
  let Tt : edgeFormSpace L m k (i + 1) →ₗ[ℝ] edgeFormSpace L m k i :=
    realTransposeMap (S := edgePairedSpace L m k i) (S' := edgePairedSpace L m k (i + 1)) T
  have hTt : ∀ (g : edgeFormSpace L m k (i + 1)) (f : edgeFormSpace L m k i),
      β (Tt g) f = β' g (T f) := by
    intro g f
    have h := hT L m k i (i + 1) hL hm hi hi' T g f
    have h' : ((β (Tt g) f : ℝ) : ℂ) = ((β' g (T f) : ℝ) : ℂ) := by
      rw [← hβ, ← hβ']
      exact h
    exact_mod_cast h'
  have horth : ∀ d : edgeFormSpace L m k i, T d = 0 → β X d = 0 := by
    intro d hd
    obtain ⟨I, γ, hγ, h0, ht, hz⟩ := hker d hd
    rw [(hXd γ (isDiffAtZeroPath_of_curve hγ) h0).deriv, ht, hβ X d, Complex.ofReal_re] at hz
    exact hz
  obtain ⟨μ, hμ⟩ := hR.1 (edgeFormSpace L m k i) (edgeFormSpace L m k (i + 1)) β β' hs hnd hs' hnd'
    T Tt hTt X horth
  refine ⟨μ, ?_, ?_⟩
  · refine (leftGradient_eq_of_deriv hS hL hm hi' (F := b.energy (i + 1)) fun B => ?_).symm
    have hWc : W ∈ fieldSpace L m k (i + 1) := hpA.1.1 hW
    obtain ⟨hE, hE0, hEt⟩ := (hP L m k (i + 1) hL hm hi').2.2 W hWc B B.2
    obtain ⟨hδ, -⟩ := hpp.2 _ hE hE0
    have hδ0 : b.prolong i
        (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • (B : Edge L m k (i + 1) → ComplexMatrix2)) W) =
          b.prolong i W :=
      congrArg (b.prolong i) hE0
    obtain ⟨-, hεt⟩ := hMp.2 _ hδ hδ0
    have hCf := ((hP L m k i hL hm hi).1 _ hδ).1
    have hε : curveTangent (fun t : ℝ => smoothingStep L m k i
        (b.prolong i (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L m k (i + 1) → ComplexMatrix2)) W))) =
          B := by
      have he : (fun t : ℝ => smoothingStep L m k i
          (b.prolong i (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L m k (i + 1) → ComplexMatrix2)) W)))
            =ᶠ[𝓝 0]
          fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L m k (i + 1) → ComplexMatrix2)) W :=
        eventually_along_path hP hL hm hi' hE hE0
          (Q := fun V => smoothingStep L m k i (b.prolong i V) = V) hsec
      rw [curveTangent_congr he, hEt]
    have hTC : T ⟨_, hCf⟩ = B := Subtype.ext ((hTv _).trans (hεt.symm.trans hε))
    have hev : (fun t : ℝ => b.energy (i + 1)
        (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L m k (i + 1) → ComplexMatrix2)) W)) =ᶠ[𝓝 0]
        fun t : ℝ => b.gaugeFixedEnergy i
          (b.prolong i (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L m k (i + 1) → ComplexMatrix2)) W)) :=
      eventually_along_path hP hL hm hi' hE hE0
        (Q := fun W' => b.energy (i + 1) W' = b.gaugeFixedEnergy i (b.prolong i W')) hfun
    have hd := (hXd _ hδ hδ0).congr_of_eventuallyEq hev
    have h : HasDerivAt (fun t : ℝ => ((b.energy (i + 1)
        (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L m k (i + 1) → ComplexMatrix2)) W) : ℝ) : ℂ))
        (((edgeFormPairing (X : Edge L m k i → ComplexMatrix2) (curveTangent fun t : ℝ =>
          b.prolong i (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L m k (i + 1) → ComplexMatrix2)) W))).re
            : ℝ) : ℂ) 0 :=
      hd.ofReal_comp
    have hval : edgeFormPairing (X : Edge L m k i → ComplexMatrix2) (curveTangent fun t : ℝ =>
          b.prolong i (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L m k (i + 1) → ComplexMatrix2)) W)) =
        ((β' μ B : ℝ) : ℂ) := by
      have := hβ X ⟨_, hCf⟩
      rw [show β X ⟨_, hCf⟩ = β' μ B by rw [hμ, hTt, hTC]] at this
      exact this
    rw [hval, Complex.ofReal_re] at h
    change edgeFormPairing (μ : Edge L m k (i + 1) → ComplexMatrix2)
        (B : Edge L m k (i + 1) → ComplexMatrix2) =
      deriv (fun t : ℝ => ((b.energy (i + 1)
        (PeriodicLattice.expTwist ((t : ℂ) • (B : Edge L m k (i + 1) → ComplexMatrix2)) W) : ℝ) : ℂ)) 0
    rw [hβ', h.deriv]
  · rw [hXg, hμ]
    rfl
end YangMills.Construction.Tower.FibreGradient
namespace YangMills.Construction.Tower
open FibreGradient in
theorem gaugeFixedGradientOnFibre_holds
    (hFix : ChosenBranchIsCritical)
    (hForm : CriticalFibreHessianPosDef)
    (hS : FiniteSideFormSpaces) (hP : diffAtZeroPathsStatement)
    (hA : AnalyticMapsAlongCurves)
    (hT : RealTransposeEdgeFormPairing)
    (hR : LinearAlgebra.AnnihilatorOfKernel.AnnihilatorSubsetRangeTransposeRealComplex) :
    GaugeFixedGradientOnFibre := by
  intro L m k hL hm i hi
  have hik : i < k := hi
  obtain ⟨hb, hUall⟩ := hFix L m k hL hm
  have hU := hUall i hik
  obtain ⟨𝒲, hWo, hpA⟩ := hb.analytic_prolong i hik
  have hnear : 𝒲 ∈ 𝓝[fieldSpace L m k (i + 1)] trivialField L m k (i + 1) :=
    (hP L m k (i + 1) hL hm hi).2.1 _ hWo.1 _ hWo.2
  have eSec := eventually_eventually_nhdsWithin.2 (hb.prolong_section i hik)
  have hform := hForm L m k hL hm i hi
  unfold EventuallyNearIdentity at hform ⊢
  filter_upwards [hnear, eSec, hform] with W wW wSec wForm
  obtain ⟨hcrit, -, -, hcurves, -⟩ := wForm
  refine transpose_gradient_relation hS hP hA hT hR hL hm hik hpA wW hU.analytic_gaugeFixedEnergy
    hU.analytic_smoothing hcrit.1.1 (wSec.mono fun W' h => h.2.2.2)
    (wSec.mono fun W' h => h.1) fun d hd => ?_
  obtain ⟨I, γ, hγ, hmap, h0, ht⟩ := hcurves ⟨d, hd⟩
  exact ⟨I, γ, hγ.1, h0, ht, hcrit.2 I γ hγ.1 hmap h0⟩
end YangMills.Construction.Tower
end
