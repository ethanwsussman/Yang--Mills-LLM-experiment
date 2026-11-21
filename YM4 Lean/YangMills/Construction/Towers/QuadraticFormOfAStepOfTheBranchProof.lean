import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorusProof
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Towers.ClosedFormsOnATorusProof
import YangMills.Construction.Towers.ClosedFormsUnderTheLinearAverageProof
import YangMills.Construction.Towers.IterateOfTheAveragingMapsNearTheTrivialConfigurationProof
import YangMills.Construction.Towers.MapsReadBackFromTheChartAtOneProof
import YangMills.Construction.Towers.QuadraticFormOfAStepOfTheBranch
import YangMills.Construction.Towers.RealAnalyticFunctionsAlongTwiceDifferentiableCurvesProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces Matrices.PowerExpCharts
  Coordinates Conventions
namespace Tower.StepQuadraticFormProof
section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem hasDerivAt_smul_line {φ : E → F} (hφ : DifferentiableAt ℝ φ 0) (u : E) :
    HasDerivAt (fun t : ℝ => φ (t • u)) (fderiv ℝ φ 0 u) 0 := by apply _root_.YangMills.Construction.Tower.IdentityChartPullback.hasDerivAt_comp_smul_line <;> assumption
theorem eventually_differentiableAt_of_contDiffAt_two {φ : E → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) :
    ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ φ y :=
  (hφ.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by norm_num)
theorem differentiableAt_fderiv_of_contDiffAt_two {φ : E → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) :
    DifferentiableAt ℝ (fderiv ℝ φ) 0 :=
  (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
theorem deriv_deriv_eq_fderiv_fderiv {φ : E → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (u v : E) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => φ (s • u + t • v)) 0) 0 =
      fderiv ℝ (fderiv ℝ φ) 0 u v := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.deriv_deriv_two_param <;> assumption
theorem fderiv_fderiv_fun_add {φ₁ φ₂ : E → ℝ} (h₁ : ContDiffAt ℝ 2 φ₁ 0)
    (h₂ : ContDiffAt ℝ 2 φ₂ 0) :
    fderiv ℝ (fderiv ℝ fun w => φ₁ w + φ₂ w) 0 =
      fderiv ℝ (fderiv ℝ φ₁) 0 + fderiv ℝ (fderiv ℝ φ₂) 0 := by
  have heq : (fderiv ℝ fun w => φ₁ w + φ₂ w) =ᶠ[𝓝 0]
      fun y => fderiv ℝ φ₁ y + fderiv ℝ φ₂ y := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt_two h₁,
      eventually_differentiableAt_of_contDiffAt_two h₂] with y hy₁ hy₂
    exact fderiv_fun_add hy₁ hy₂
  rw [heq.fderiv_eq]
  exact fderiv_fun_add (differentiableAt_fderiv_of_contDiffAt_two h₁)
    (differentiableAt_fderiv_of_contDiffAt_two h₂)
end Calculus
section Sums
theorem isRelativelyOpen_inter {X : Type} [TopologicalSpace X] {P D D' : Set X}
    (h : ComplexMatrix2.IsRelativelyOpen P D) (h' : ComplexMatrix2.IsRelativelyOpen P D') :
    ComplexMatrix2.IsRelativelyOpen P (D ∩ D') := by apply _root_.YangMills.SharedProofs.p7081 <;> assumption
theorem isHolomorphicToCoords_add {R : Type} [Fintype R] {l : ℕ}
    {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {𝒳₁ 𝒳₂ : Set (R ⊕ Empty → ComplexMatrix2)}
    {Φ₁ Φ₂ : (R ⊕ Empty → ComplexMatrix2) → ComplexCoordinates l}
    (h₁ : IsHolomorphicToCoords β (Equiv.refl _) 𝒳₁ Φ₁)
    (h₂ : IsHolomorphicToCoords β (Equiv.refl _) 𝒳₂ Φ₂) :
    IsHolomorphicToCoords β (Equiv.refl _) (𝒳₁ ∩ 𝒳₂) fun q => Φ₁ q + Φ₂ q := by
  obtain ⟨o₁, c₁, l₁⟩ := h₁
  obtain ⟨o₂, c₂, l₂⟩ := h₂
  have c₁' : ContinuousOn Φ₁ 𝒳₁ := c₁
  have c₂' : ContinuousOn Φ₂ 𝒳₂ := c₂
  refine ⟨isRelativelyOpen_inter o₁ o₂, ?_, fun p hp => ?_⟩
  · exact (c₁'.mono inter_subset_left).add (c₂'.mono inter_subset_right)
  · obtain ⟨O₁, z₁, m₁, t₁⟩ := l₁ p hp.1
    obtain ⟨O₂, z₂, m₂, t₂⟩ := l₂ p hp.2
    refine ⟨O₁ ∩ O₂, ⟨z₁, z₂⟩, fun A hA => ⟨m₁ A hA.1, m₂ A hA.2⟩, ⟨?_, ?_⟩, fun ν => ?_⟩
    · exact fun A hA => t₁.1.1 hA.1
    · rintro A ⟨hA₁, hA₂⟩
      obtain ⟨s₁, p₁, f₁⟩ := t₁.1.2 A hA₁
      obtain ⟨s₂, p₂, f₂⟩ := t₂.1.2 A hA₂
      exact ⟨min s₁ s₂, lt_min p₁ p₂, fun B hB hs =>
        ⟨f₁ B hB (lt_of_lt_of_le hs (min_le_left _ _)),
          f₂ B hB (lt_of_lt_of_le hs (min_le_right _ _))⟩⟩
    · obtain ⟨a₁, b₁, d₁⟩ := t₁.2 ν
      obtain ⟨a₂, b₂, d₂⟩ := t₂.2 ν
      refine ⟨a₁.inter a₂, ?_, fun a ha j => ?_⟩
      · exact (b₁.mono inter_subset_left).add (b₂.mono inter_subset_right)
      · filter_upwards [d₁ a ha.1 j, d₂ a ha.2 j] with ζ e₁ e₂
        exact e₁.add e₂
variable {L n k j : ℕ}
theorem isPositivelyOriented_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem fieldOfPositiveValues_restrict {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges U) = U := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem isOpenFieldSet_inter {𝒰₁ 𝒰₂ : Set (Edge L n k j → ComplexMatrix2)}
    (h₁ : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰₁)
    (h₂ : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰₂) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup (𝒰₁ ∩ 𝒰₂) := by
  refine ⟨fun U hU => h₁.1 hU.1, ?_⟩
  have himg : restrictToPositiveEdges '' (𝒰₁ ∩ 𝒰₂) =
      restrictToPositiveEdges '' 𝒰₁ ∩ restrictToPositiveEdges '' 𝒰₂ := by
    ext w
    constructor
    · rintro ⟨U, hU, rfl⟩
      exact ⟨⟨U, hU.1, rfl⟩, ⟨U, hU.2, rfl⟩⟩
    · rintro ⟨⟨U, hU, rfl⟩, ⟨U', hU', hw⟩⟩
      have : U' = U := by
        rw [← fieldOfPositiveValues_restrict (h₂.1 hU'), hw,
          fieldOfPositiveValues_restrict (h₁.1 hU)]
      exact ⟨U, ⟨hU, this ▸ hU'⟩, rfl⟩
  rw [himg]
  exact isRelativelyOpen_inter h₁.2 h₂.2
theorem isAnalyticFieldFunction_add {𝒰₁ 𝒰₂ : Set (Edge L n k j → ComplexMatrix2)}
    {f g : (Edge L n k j → ComplexMatrix2) → ℝ}
    (hf : IsAnalyticFieldFunction 𝒰₁ f) (hg : IsAnalyticFieldFunction 𝒰₂ g) :
    IsAnalyticFieldFunction (𝒰₁ ∩ 𝒰₂) fun U => f U + g U := by
  obtain ⟨o₁, i₁, a₁⟩ := hf
  obtain ⟨o₂, i₂, a₂⟩ := hg
  obtain rfl : i₂ = i₁ := Subsingleton.elim _ _
  refine ⟨isOpenFieldSet_inter o₁ o₂, i₂, ⟨a₁.1.1, isRelativelyOpen_inter a₁.1.2 a₂.1.2⟩,
    fun p hp => ?_⟩
  obtain ⟨𝒳₁, p₁, x₁, s₁, Φ₁, h₁, e₁⟩ := a₁.2 p hp.1
  obtain ⟨𝒳₂, p₂, x₂, s₂, Φ₂, h₂, e₂⟩ := a₂.2 p hp.2
  refine ⟨𝒳₁ ∩ 𝒳₂, ⟨p₁, p₂⟩, isRelativelyOpen_inter x₁ x₂,
    fun q hq => ⟨s₁ ⟨hq.1.1, hq.2⟩, s₂ ⟨hq.1.2, hq.2⟩⟩, fun q => Φ₁ q + Φ₂ q,
    fun β => isHolomorphicToCoords_add (h₁ β) (h₂ β), fun q hq => ?_⟩
  show Φ₁ q + Φ₂ q = _
  rw [e₁ ⟨hq.1.1, hq.2⟩, e₂ ⟨hq.1.2, hq.2⟩]
  funext z
  simp
end Sums
section EvaluationMaps
variable {L n k j : ℕ}
theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
theorem nonempty_positiveEdge (hP : BondSetFields.ProductStructureHolds)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Nonempty (PositiveEdge L n k j) := by apply _root_.YangMills.SharedProofs.p12312 <;> assumption
theorem holomorphicScalar_of_coords {σ : Type} [Fintype σ]
    {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → ComplexCoordinates 1}
    (h : IsHolomorphicToCoords β (Equiv.refl _) W Φ) :
    HolomorphicScalar β W fun q => Φ q 0 := by apply _root_.YangMills.SharedProofs.p9409 <;> assumption
def lieValues [Fintype (PositiveEdge L n k j)] :
    edgeFormSpace L n k j →ₗ[ℝ] (PositiveEdge L n k j → ComplexMatrix2.LieElement) where
  toFun B s := (⟨(B : Edge L n k j → ComplexMatrix2) s.1, B.2.1 s.1 s.2⟩ :
    ComplexMatrix2.hermitianTraceless)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
def IsChartObservable (T : edgeFormSpace L n k j →ₗ[ℝ] W) (f : (Edge L n k j → ComplexMatrix2) → ℝ)
    (φ : W → ℝ) : Prop :=
  ContDiffAt ℝ 2 φ 0 ∧ ∀ B : edgeFormSpace L n k j,
    f (PeriodicLattice.expTwist (B : Edge L n k j → ComplexMatrix2) (trivialField L n k j)) =
      φ (T B)
theorem exists_chartCoordinates [inst : Fintype (PositiveEdge L n k j)]
    (hC : ExpChartsStatement)
    (hP : BondSetFields.ProductStructureHolds) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) {𝒰 : Set (Edge L n k j → ComplexMatrix2)} {f : (Edge L n k j → ComplexMatrix2) → ℝ}
    (h1 : trivialField L n k j ∈ 𝒰) (hf : IsAnalyticFieldFunction 𝒰 f) :
    ∃ φ, IsChartObservable (lieValues (L := L) (n := n) (k := k) (j := j)) f φ := by
  obtain ⟨hopen, i₁, hra⟩ := hf
  obtain rfl : i₁ = inst := Subsingleton.elim _ _
  have := nonempty_positiveEdge hP hL hn hj
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
    Module.finBasisOfFinrankEq ℂ ComplexMatrix2.traceless finrank_traceless
  obtain ⟨-, -, -, -, -, -, -, hread⟩ := hC (PositiveEdge L n k j) (PositiveEdge L n k j)
  have hO : specialUnitaryPower.IsOpenSubset (restrictToPositiveEdges '' 𝒰) := hopen.2
  have hfield : ∀ {U}, U ∈ 𝒰 → fieldOfPositiveValues (restrictToPositiveEdges U) = U :=
    fun hU => fieldOfPositiveValues_restrict (hopen.1 hU)
  let g : (PositiveEdge L n k j → ComplexMatrix2) → ℝ := fun w => f (fieldOfPositiveValues w)
  have hrest : IsLocallyHolomorphicRestriction (HolomorphicScalar β) Complex.ofReal
      (restrictToPositiveEdges '' 𝒰) g := by
    rintro _ ⟨U, hU, rfl⟩
    have hq : asGroupFactors (restrictToPositiveEdges U) ∈
        {q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 |
          fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
      show fieldOfPositiveValues (restrictToPositiveEdges U) ∈ 𝒰
      rw [hfield hU]
      exact hU
    obtain ⟨𝒳, hp𝒳, -, -, Φ, hΦ, heq⟩ := hra.2 _ hq
    refine ⟨𝒳, fun q => Φ q 0, hp𝒳, holomorphicScalar_of_coords (hΦ β), ?_⟩
    rintro _ ⟨U', hU', rfl⟩ hx
    have hval := heq ⟨hx, (Submodule.mem_bot ℝ).2 (funext fun e => e.elim),
      fun c => (hopen.1 hU').1 c (mem_univ _)⟩
    exact congrFun hval 0
  let p₀ : PositiveEdge L n k j → ComplexMatrix2 := restrictToPositiveEdges (trivialField L n k j)
  obtain ⟨Nb, hNb, -, hsm, -⟩ :=
    (((hread β).1 _ hO).1 g hrest).1.1 p₀ ⟨_, h1, rfl⟩
  refine ⟨g ∘ expChartI p₀, (hsm.contDiffAt hNb).of_le ENat.LEInfty.out, fun B => ?_⟩
  show f _ = f _
  congr 1
  funext b
  have hoo : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
  by_cases h : b.IsPositivelyOriented
  · simp only [PeriodicLattice.expTwist, fieldOfPositiveValues, if_pos h, dif_pos h]
    rfl
  · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
    simp only [PeriodicLattice.expTwist, fieldOfPositiveValues, if_neg h, dif_neg h, dif_pos h']
    rfl
variable {T : edgeFormSpace L n k j →ₗ[ℝ] W} {f : (Edge L n k j → ComplexMatrix2) → ℝ} {φ : W → ℝ}
theorem chartRepresentation_plane (hφ : IsChartObservable T f φ) (B B' : edgeFormSpace L n k j) (s t : ℝ) :
    f (PeriodicLattice.expTwist (algebraMap ℝ ℂ s • (B : Edge L n k j → ComplexMatrix2) +
        algebraMap ℝ ℂ t • (B' : Edge L n k j → ComplexMatrix2)) (trivialField L n k j)) =
      φ (s • T B + t • T B') := by
  have hsum : algebraMap ℝ ℂ s • (B : Edge L n k j → ComplexMatrix2) +
      algebraMap ℝ ℂ t • (B' : Edge L n k j → ComplexMatrix2) =
      ((s • B + t • B' : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) := by
    rw [algebraMap_smul, algebraMap_smul]
    rfl
  rw [hsum, hφ.2, map_add, map_smul, map_smul]
theorem leftSecondDeriv_eq_of_chartExpression (hφ : IsChartObservable T f φ) (B B' : edgeFormSpace L n k j) :
    leftSecondDeriv f (trivialField L n k j) (B : Edge L n k j → ComplexMatrix2)
        (B' : Edge L n k j → ComplexMatrix2) = fderiv ℝ (fderiv ℝ φ) 0 (T B) (T B') := by
  rw [← deriv_deriv_eq_fderiv_fderiv hφ.1]
  show deriv (fun s : ℝ => deriv (fun t : ℝ => f (PeriodicLattice.expTwist
    (algebraMap ℝ ℂ s • (B : Edge L n k j → ComplexMatrix2) +
      algebraMap ℝ ℂ t • (B' : Edge L n k j → ComplexMatrix2))
    (trivialField L n k j))) 0) 0 = _
  simp only [chartRepresentation_plane hφ]
theorem leftDeriv_eq_of_chartExpression (hφ : IsChartObservable T f φ) (B : edgeFormSpace L n k j) :
    leftDeriv (fun U => (f U : ℂ)) (trivialField L n k j)
        (B : Edge L n k j → ComplexMatrix2) = ((fderiv ℝ φ 0 (T B) : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ φ 0 := hφ.1.differentiableAt (by norm_num)
  have hline : HasDerivAt (fun t : ℝ => ((φ (t • T B) : ℝ) : ℂ))
      ((fderiv ℝ φ 0 (T B) : ℝ) : ℂ) 0 :=
    (hasDerivAt_smul_line hd (T B)).ofReal_comp
  have hfun : (fun t : ℝ => ((f (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ t • (B : Edge L n k j → ComplexMatrix2))
      (trivialField L n k j)) : ℝ) : ℂ)) = fun t => ((φ (t • T B) : ℝ) : ℂ) := by
    funext t
    have hsm : algebraMap ℝ ℂ t • (B : Edge L n k j → ComplexMatrix2) =
        ((t • B : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) := by
      rw [algebraMap_smul]
      rfl
    rw [hsm, hφ.2, map_smul]
  show deriv (fun t : ℝ => ((f (PeriodicLattice.expTwist
    (algebraMap ℝ ℂ t • (B : Edge L n k j → ComplexMatrix2)) (trivialField L n k j)) : ℝ) : ℂ))
    0 = _
  rw [hfun]
  exact hline.deriv
end EvaluationMaps
section Kernel
variable {L n k i : ℕ}
theorem bondFormSumAlong_add {m : ℕ} {j : ℤ} (A A' : PeriodicLattice.Bond L m j → ComplexMatrix2)
    (γ : List (PeriodicLattice.Bond L m j)) :
    PeriodicLattice.bondFormSumAlong (A + A') γ =
      PeriodicLattice.bondFormSumAlong A γ + PeriodicLattice.bondFormSumAlong A' γ := by apply _root_.YangMills.Construction.PeriodicLattice.ClosedFormsSmoothing.bondFormSumAlong_add <;> assumption
theorem contourFormAverage_add {m : ℕ} {j j' : ℤ}
    (A A' : PeriodicLattice.Bond L m j' → ComplexMatrix2)
    (y : PeriodicLattice.Site L m j) (x : PeriodicLattice.Site L m j') :
    PeriodicLattice.contourFormAverage (A + A') y x =
      PeriodicLattice.contourFormAverage A y x + PeriodicLattice.contourFormAverage A' y x := by apply _root_.YangMills.Construction.PeriodicLattice.ClosedFormsSmoothing.contourFormAverage_add <;> assumption
theorem linearSmoothing_add [Finite (Vertex L n k i)] (A A' : Edge L n k i → ComplexMatrix2) :
    linearSmoothing L n k i (A + A') =
      linearSmoothing L n k i A + linearSmoothing L n k i A' := by
  funext c
  show PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum (A + A') c =
    PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum A c +
      PeriodicLattice.inverseFourthPowerWeight L • PeriodicLattice.linearBlockSum A' c
  rw [← smul_add]
  congr 1
  unfold PeriodicLattice.linearBlockSum
  rw [← finsum_mem_add_distrib (Set.toFinite _)]
  refine finsum_mem_congr rfl fun x _ => ?_
  rw [contourFormAverage_add, contourFormAverage_add, bondFormSumAlong_add]
  abel
theorem edgeForm_mem_hermitianTraceless {ξ : Edge L n k i → ComplexMatrix2}
    (hξ : ξ ∈ edgeFormSpace L n k i) (b : Edge L n k i) :
    ξ b ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.SmoothingIterProof.edgeForm_apply_mem <;> assumption
theorem fineOnlyContourAverage_mem {ξ : Edge L n k i → ComplexMatrix2}
    (hξ : ξ ∈ edgeFormSpace L n k i) (x : FineOnlyVertex L n k i) :
    fineOnlyContourAverage L n k i ξ x ∈ ComplexMatrix2.hermitianTraceless := by
  show PeriodicLattice.contourFormAverage ξ (cubeCentre x) x.1 ∈ ComplexMatrix2.hermitianTraceless
  unfold PeriodicLattice.contourFormAverage
  have hpath : ∀ γ : List (Edge L n k i),
      PeriodicLattice.bondFormSumAlong ξ γ ∈ ComplexMatrix2.hermitianTraceless := by
    intro γ
    induction γ with
    | nil => simp [PeriodicLattice.bondFormSumAlong]
    | cons b γ ih =>
      simp only [PeriodicLattice.bondFormSumAlong, List.map_cons, List.sum_cons] at ih ⊢
      exact ComplexMatrix2.hermitianTraceless.add_mem (edgeForm_mem_hermitianTraceless hξ b) ih
  have hsc := algebraMap_smul ℂ
    ((Fintype.card (PeriodicLattice.AxisOrdering (cubeCentre x) x.1) : ℝ)⁻¹)
    (∑ σ : PeriodicLattice.AxisOrdering (cubeCentre x) x.1,
      PeriodicLattice.bondFormSumAlong ξ (PeriodicLattice.orderedContour (cubeCentre x) x.1 σ))
  refine (show _ = _ from hsc) ▸ ComplexMatrix2.hermitianTraceless.smul_mem _
    (ComplexMatrix2.hermitianTraceless.sum_mem fun σ _ => hpath _)
theorem eq_zero_of_traceFinsumNorm_eq_zero {ι : Type*} [Finite ι] {g : ι → ComplexMatrix2}
    (hg : ∀ x, g x ∈ ComplexMatrix2.hermitianTraceless) (h : traceFinsumNorm g = 0) : g = 0 := by
  classical
  cases nonempty_fintype ι
  let Y : ι → ComplexMatrix2.LieElement := fun x => (⟨g x, hg x⟩ : ComplexMatrix2.hermitianTraceless)
  have hre : (traceFinsumPairing g g).re =
      ∑ x, ComplexMatrix2.LieElement.innerProductCore.inner (Y x) (Y x) := by
    unfold traceFinsumPairing
    rw [finsum_eq_sum_of_fintype, Complex.re_sum]
    rfl
  have hnn : ∀ x, 0 ≤ ComplexMatrix2.LieElement.innerProductCore.inner (Y x) (Y x) :=
    fun x => ComplexMatrix2.LieElement.innerProductCore.re_inner_nonneg (Y x)
  have hle : (traceFinsumPairing g g).re ≤ 0 := Real.sqrt_eq_zero'.mp h
  have hs : ∑ x, ComplexMatrix2.LieElement.innerProductCore.inner (Y x) (Y x) = 0 :=
    le_antisymm (hre ▸ hle) (Finset.sum_nonneg fun x _ => hnn x)
  funext x
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hnn x).mp hs x (Finset.mem_univ x)
  have hY := ComplexMatrix2.LieElement.innerProductCore.definite _ h1
  exact congrArg ComplexMatrix2.LieElement.toMatrix hY
theorem eq_of_periodic_zsmul_sum {A : Type*} [AddCommGroup A] {V : Type*} {h : A → V}
    {e : Fin 4 → A} (hi : ∀ ν x, h (x + e ν) = h x) (m : Fin 4 → ℤ) (x : A) :
    h (x + ∑ μ, m μ • e μ) = h x := by
  let H : AddSubgroup A :=
    { carrier := {y | ∀ x, h (x + y) = h x}
      add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
      zero_mem' := fun x => by rw [add_zero]
      neg_mem' := fun {a} ha x => by
        have := ha (x + -a)
        rwa [neg_add_cancel_right, eq_comm] at this }
  have hm : ∑ μ, m μ • e μ ∈ H :=
    H.sum_mem fun μ _ => H.zsmul_mem (fun x => hi μ x) (m μ)
  exact hm x
theorem eq_forwardFrom_of_diff {b : Edge L n k i} {μ : Fin 4}
    (h : b.target - b.source = PeriodicLattice.unitStep L n _ μ) :
    b = PeriodicLattice.Bond.forwardFrom b.source μ := by apply _root_.YangMills.Construction.Tower.ClosedEdgeForms.eq_forwardFrom_of_sub <;> assumption
theorem eq_zero_of_closed_of_kernel (hRel : TrivialLinearization.AllRelationsStatement)
    (hCl : ClosedEdgeFormsOnPeriodicLattice) (hBl : BlockStructure)
    (hLat : PeriodicLattice.CoordinateDescription)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i < k) [Finite (Vertex L n k i)]
    {ξ : Edge L n k i → ComplexMatrix2} (hξ : ξ ∈ edgeFormSpace L n k i) (hcl : IsClosedEdgeForm ξ)
    (hQ : linearSmoothing L n k i ξ = 0) (hLξ : fineOnlyContourAverage L n k i ξ = 0) :
    ξ = 0 := by
  obtain ⟨l, hl, a, ha, hconst, rfl⟩ := ((hCl L n k i hL hn hi.le) ξ hξ).1 hcl
  obtain ⟨hstep, hcs, -⟩ := (hRel L hL).1 n k i i hn hi hi.le
  obtain ⟨-, hsort, -⟩ := (hBl L k (i + 1) hL (by omega) (by omega) hi).1 n hn
  obtain ⟨-, hpos, -, hgen, hmod, -⟩ :=
    (hLat L n hL.1 hL.2 hn).1 (PeriodicLattice.levelDepth k (i + 1))
      (by simp only [PeriodicLattice.levelDepth]; omega)
  let e : Fin 4 → Vertex L n k (i + 1) :=
    PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k (i + 1))
  let N : ℕ := 2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k (i + 1))
  have hNe : ∀ μ, N • e μ = 0 := by
    intro μ
    have h₀ := (hmod 0 (Pi.single μ ((N : ℕ) : ℤ)) 0).2
      (fun ν => by
        by_cases hν : ν = μ
        · subst hν
          simp only [Pi.single_eq_same, Pi.zero_apply]
          exact Int.modEq_zero_iff_dvd.mpr (dvd_refl _)
        · simp [Pi.single_eq_of_ne hν])
    simp only [PeriodicLattice.offsetSite, Pi.single_apply, ite_smul, zero_smul,
      Pi.zero_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero,
      zero_add] at h₀
    rw [← natCast_zsmul]
    exact h₀
  let g : Vertex L n k (i + 1) → ComplexMatrix2 := restrictVertexFunction (i + 1) l
  let av : Fin 4 → ComplexMatrix2 := fun μ => a (PeriodicLattice.Bond.forwardFrom 0 μ)
  have hca := hcs a ha av (fun x μ => hconst μ x 0)
  have hdl := hstep.2 l hl
  have hrel : ∀ y μ, g (y + e μ) - g y + (L : ℂ) • av μ = 0 := by
    intro y μ
    have h₁ := congrFun hQ (PeriodicLattice.Bond.forwardFrom y μ)
    rw [linearSmoothing_add, hdl.1, hca.2.2.1] at h₁
    simp only [Pi.add_apply, Pi.zero_apply, hca.2.2.2.2] at h₁
    exact h₁
  have hline : ∀ μ (r : ℕ), g (r • e μ) = g 0 - r • ((L : ℂ) • av μ) := by
    intro μ r
    induction r with
    | zero => simp
    | succ r ih =>
      have h₁ := hrel (r • e μ) μ
      rw [succ_nsmul, succ_nsmul]
      calc g (r • e μ + e μ)
          = (g (r • e μ + e μ) - g (r • e μ) + (L : ℂ) • av μ) + g (r • e μ) -
              (L : ℂ) • av μ := by abel
        _ = _ := by rw [h₁, ih]; abel
  have hL0 : (L : ℂ) ≠ 0 := by
    have : L ≠ 0 := by have := hL.2; omega
    exact_mod_cast this
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := hpos.ne'
    exact_mod_cast this
  have hav : ∀ μ, av μ = 0 := by
    intro μ
    have h₁ := hline μ N
    rw [hNe μ] at h₁
    have h₂ : N • ((L : ℂ) • av μ) = 0 := sub_eq_self.mp h₁.symm
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul] at h₂
    exact (smul_eq_zero.mp h₂).resolve_left (mul_ne_zero hN0 hL0)
  have ha0 : a = 0 := by
    have hp : ∀ b : Edge L n k i, b.IsPositivelyOriented → a b = 0 := by
      rintro b ⟨μ, hb⟩
      rw [eq_forwardFrom_of_diff hb, hconst μ _ 0]
      exact hav μ
    funext b
    have hoo : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
    rcases isPositivelyOriented_or_opposite b with h | h
    · exact hp b h
    · have h₁ := ha.2 b.opposite
      rw [hoo, hp _ h] at h₁
      simpa using h₁
  subst ha0
  have hinv : ∀ ν y, g (y + e ν) = g y := by
    intro ν y
    have h₁ := hrel y ν
    rw [hav ν, smul_zero, add_zero] at h₁
    exact sub_eq_zero.mp h₁
  have hg : ∀ y, g y = g 0 := by
    intro y
    obtain ⟨m, hm⟩ := hgen 0 y
    have h₁ := eq_of_periodic_zsmul_sum hinv m 0
    have h₂ : y = 0 + ∑ μ, m μ • e μ := hm
    rw [h₂]
    exact h₁
  have hlc : ∀ x, l x = g 0 := by
    intro x
    by_cases hx : (x : PeriodicLattice.FourTorus L n) ∈
        PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1))
    · have h₁ : g ⟨x, hx⟩ = l x := by
        show l (PeriodicLattice.Site.toSublattice _ _) = l x
        congr 1
        exact Subtype.ext (Classical.epsilon_spec (p := fun z : Vertex L n k i =>
          (z : PeriodicLattice.FourTorus L n) = x) ⟨x, rfl⟩)
      rw [← h₁, hg]
    · obtain ⟨y, ⟨hxy, hne⟩, -⟩ := hsort.2.2 x hx
      have h₁ := hdl.2.2.2 y ⟨x, hx⟩ hxy hne
      have h₂ := congrFun hLξ ⟨x, hx⟩
      rw [add_zero, h₁] at h₂
      have h₃ : l x - g y = 0 := h₂
      rw [sub_eq_zero.mp h₃, hg]
  funext b
  simp [vertexCoboundary, hlc]
end Kernel
section Gradient
variable {L n k j : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
theorem exists_inner_eq {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j)}
    [FiniteDimensional ℝ (edgeFormSpace L n k j)] (ℓ : edgeFormSpace L n k j →ₗ[ℝ] ℝ) :
    ∃ X : edgeFormSpace L n k j, ∀ B, c.inner X B = ℓ B := by
  let Φ : edgeFormSpace L n k j →ₗ[ℝ] Module.Dual ℝ (edgeFormSpace L n k j) :=
    LinearMap.mk₂ ℝ (fun X B => c.inner X B)
      (fun X X' B => c.add_left X X' B)
      (fun r X B => by simpa using c.smul_left X B r)
      (fun X B B' => by
        have hsymm : ∀ P Q : edgeFormSpace L n k j, c.inner P Q = c.inner Q P := fun P Q => by
          simpa using (c.conj_inner_symm P Q).symm
        rw [hsymm X, hsymm X, hsymm X, c.add_left])
      (fun r X B => by
        have hsymm : ∀ P Q : edgeFormSpace L n k j, c.inner P Q = c.inner Q P := fun P Q => by
          simpa using (c.conj_inner_symm P Q).symm
        rw [hsymm X, hsymm X]
        simpa using c.smul_left B X r)
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro X hX
    exact c.definite X (LinearMap.congr_fun hX X)
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := edgeFormSpace L n k j)).symm).mp hinj
  obtain ⟨X, hX⟩ := hsurj ℓ
  exact ⟨X, fun B => LinearMap.congr_fun hX B⟩
theorem isLeftGradient_of_coordinates {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j)}
    (hc : ∀ B B' : edgeFormSpace L n k j, edgeFormPairing (B : Edge L n k j → ComplexMatrix2)
      (B' : Edge L n k j → ComplexMatrix2) = ((c.inner B B' : ℝ) : ℂ))
    [FiniteDimensional ℝ (edgeFormSpace L n k j)] {T : edgeFormSpace L n k j →ₗ[ℝ] W}
    {f : (Edge L n k j → ComplexMatrix2) → ℝ} {φ : W → ℝ} (hφ : IsChartObservable T f φ) :
    IsLeftGradient (fieldSpace L n k j) (fun U => (f U : ℂ)) (trivialField L n k j)
      (leftGradient (fieldSpace L n k j) (fun U => (f U : ℂ)) (trivialField L n k j)) := by
  obtain ⟨X, hX⟩ := exists_inner_eq (c := c) ((fderiv ℝ φ 0 : W →ₗ[ℝ] ℝ) ∘ₗ T)
  refine Classical.epsilon_spec (p := IsLeftGradient (fieldSpace L n k j) _ _)
    ⟨(X : Edge L n k j → ComplexMatrix2), ⟨fun b hb => (X.2.1 b hb).2, X.2.2⟩, fun _ => X.2,
      fun B hB _ => ?_⟩
  rw [leftDeriv_eq_of_chartExpression hφ ⟨B, hB⟩, hc X ⟨B, hB⟩, hX]
  rfl
theorem fderiv_apply_eq_zero_of_gradient [Finite (PositiveEdge L n k j)]
    {c : InnerProductSpace.Core ℝ (edgeFormSpace L n k j)}
    (hc : ∀ B B' : edgeFormSpace L n k j, edgeFormPairing (B : Edge L n k j → ComplexMatrix2)
      (B' : Edge L n k j → ComplexMatrix2) = ((c.inner B B' : ℝ) : ℂ))
    [FiniteDimensional ℝ (edgeFormSpace L n k j)] {T : edgeFormSpace L n k j →ₗ[ℝ] W}
    {f : (Edge L n k j → ComplexMatrix2) → ℝ} {φ : W → ℝ} (hφ : IsChartObservable T f φ)
    (h0 : leftGradient (fieldSpace L n k j) (fun U => (f U : ℂ)) (trivialField L n k j) = 0)
    (B : edgeFormSpace L n k j) : fderiv ℝ φ 0 (T B) = 0 := by
  have h₁ := (isLeftGradient_of_coordinates hc hφ).2.2 B B.2 (Set.toFinite _)
  rw [h0, leftDeriv_eq_of_chartExpression hφ B] at h₁
  have h₂ : edgeFormPairing (0 : Edge L n k j → ComplexMatrix2)
      (B : Edge L n k j → ComplexMatrix2) = 0 := by
    have e₁ := c.add_left 0 0 B
    rw [add_zero] at e₁
    have e₂ : c.inner 0 B = 0 := by linarith
    have e₃ := hc 0 B
    rw [e₂] at e₃
    simpa using e₃
  rw [h₂] at h₁
  exact_mod_cast h₁.symm
end Gradient
theorem stepQuadraticForm_holds (hGF : AxialFunctionFacts.statement)
    (hRel : TrivialLinearization.AllRelationsStatement) (hCl : ClosedEdgeFormsOnPeriodicLattice)
    (hBl : BlockStructure)
    (hLat : PeriodicLattice.CoordinateDescription)
    (hSp : FiniteSideFormSpaces) (hC : ExpChartsStatement)
    (hP : BondSetFields.ProductStructureHolds) : StepQuadraticForm := by
  intro L n k i hL hn hi b hb
  have hfacts := hGF L n k i hL hn hi
  obtain ⟨𝒰₁, hN₁, hA₁⟩ := hb.analytic_energy i le_rfl
  obtain ⟨𝒰₂, hN₂, -, hA₂⟩ := hfacts.analytic_near_identity
  have hsum := isAnalyticFieldFunction_add hA₁ hA₂
  obtain ⟨hfin, hfd, -, c, hc⟩ := hSp L n k i hL hn hi.le
  let _ : Fintype (PositiveEdge L n k i) := Fintype.ofFinite _
  have : Finite (Vertex L n k i) := Finite.of_injective
    (fun x => (⟨PeriodicLattice.Bond.forwardFrom x 0,
      ⟨0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩ : PositiveEdge L n k i))
    (fun x x' h => congrArg PeriodicLattice.Bond.source (congrArg Subtype.val h))
  have hone : trivialField L n k i ∈ fieldSpace L n k i := hN₁.1.1 hN₁.2
  obtain ⟨φ₁, hφ₁⟩ := exists_chartCoordinates hC hP hL hn hi.le hN₁.2 hA₁
  obtain ⟨φ₂, hφ₂⟩ := exists_chartCoordinates hC hP hL hn hi.le hN₂.2 hA₂
  have hφ : IsChartObservable (lieValues (L := L) (n := n) (k := k) (j := i))
      (b.gaugeFixedEnergy i) (fun w => φ₁ w + φ₂ w) :=
    ⟨hφ₁.1.add hφ₂.1, fun B => by
      show b.energy i _ + axialFunction L n k i _ = _
      rw [hφ₁.2, hφ₂.2]⟩
  have hax0 : axialFunction L n k i (trivialField L n k i) = 0 :=
    (hfacts.eq_zero_iff.self_of_nhdsWithin hone).2 hfacts.isAxialGaugeAt_trivial
  have haxg := (hfacts.leftGradient_eq_zero.self_of_nhdsWithin hone) hfacts.isAxialGaugeAt_trivial
  have haxs := (hfacts.leftSecondDeriv_eq.self_of_nhdsWithin hone) hfacts.isAxialGaugeAt_trivial
  have hsymm := hφ₁.1.isSymmSndFDerivAt (by simp)
  have hhess : ∀ B B' : edgeFormSpace L n k i, b.hessianAtOne i (B : Edge L n k i → ComplexMatrix2)
      (B' : Edge L n k i → ComplexMatrix2) =
        fderiv ℝ (fderiv ℝ φ₁) 0 (lieValues B) (lieValues B') :=
    fun B B' => leftSecondDeriv_eq_of_chartExpression hφ₁ B B'
  refine ⟨⟨𝒰₁ ∩ 𝒰₂, ⟨hsum.1, ⟨hN₁.2, hN₂.2⟩⟩, hsum⟩, ?_, ?_, ?_, ?_⟩
  · show b.energy i _ + axialFunction L n k i _ = 0
    rw [hb.energy_trivial i le_rfl, hax0, add_zero]
  · have hg := isLeftGradient_of_coordinates hc hφ
    have hX : leftGradient (fieldSpace L n k i) (fun U => (b.gaugeFixedEnergy i U : ℂ))
        (trivialField L n k i) ∈ edgeFormSpace L n k i :=
      hg.2.1 fun U _ => Complex.ofReal_im _
    have h₁ := hg.2.2 _ hX (Set.toFinite _)
    rw [leftDeriv_eq_of_chartExpression hφ ⟨_, hX⟩, hc ⟨_, hX⟩ ⟨_, hX⟩] at h₁
    have hd₁ := hφ₁.1.differentiableAt (by norm_num)
    have hd₂ := hφ₂.1.differentiableAt (by norm_num)
    rw [fderiv_fun_add hd₁ hd₂] at h₁
    have h₂ := fderiv_apply_eq_zero_of_gradient hc hφ₁ (hb.gradient_trivial i le_rfl) ⟨_, hX⟩
    have h₃ := fderiv_apply_eq_zero_of_gradient hc hφ₂ haxg ⟨_, hX⟩
    simp only [add_apply, h₂, h₃, add_zero, Complex.ofReal_zero,
      Complex.ofReal_eq_zero] at h₁
    exact congrArg Subtype.val (c.definite ⟨_, hX⟩ h₁)
  · intro ξ hξ
    calc leftSecondDeriv (b.gaugeFixedEnergy i) (trivialField L n k i) ξ ξ
        = fderiv ℝ (fderiv ℝ fun w => φ₁ w + φ₂ w) 0 (lieValues ⟨ξ, hξ⟩)
            (lieValues ⟨ξ, hξ⟩) :=
          leftSecondDeriv_eq_of_chartExpression hφ ⟨ξ, hξ⟩ ⟨ξ, hξ⟩
      _ = b.hessianAtOne i ξ ξ + leftSecondDeriv (axialFunction L n k i)
            (trivialField L n k i) ξ ξ := by
          rw [fderiv_fderiv_fun_add hφ₁.1 hφ₂.1, add_apply,
            add_apply, ← leftSecondDeriv_eq_of_chartExpression hφ₂ ⟨ξ, hξ⟩ ⟨ξ, hξ⟩,
            ← hhess ⟨ξ, hξ⟩ ⟨ξ, hξ⟩]
      _ = b.stepQuadratic i ξ := by
          rw [haxs ξ hξ, hfacts.contourLogDeriv_trivial ξ hξ]
          rfl
  · intro ξ hξ hQ hne
    by_contra hcon
    have hh := hb.hessianAtOne_nonneg i le_rfl ξ hξ
    have hsq := sq_nonneg (traceFinsumNorm (fineOnlyContourAverage L n k i ξ))
    have hle : b.hessianAtOne i ξ ξ + traceFinsumNorm (fineOnlyContourAverage L n k i ξ) ^ 2 ≤ 0 :=
      not_lt.mp hcon
    have hz : b.hessianAtOne i ξ ξ = 0 := by linarith
    have hnorm : traceFinsumNorm (fineOnlyContourAverage L n k i ξ) = 0 := by
      have : traceFinsumNorm (fineOnlyContourAverage L n k i ξ) ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have : Finite (FineOnlyVertex L n k i) := Subtype.finite
    have hLξ := eq_zero_of_traceFinsumNorm_eq_zero (fineOnlyContourAverage_mem hξ) hnorm
    have hnull : ∀ B' ∈ edgeFormSpace L n k i, b.hessianAtOne i ξ B' = 0 := by
      intro B' hB'
      let Ξ : edgeFormSpace L n k i := ⟨ξ, hξ⟩
      let Η : edgeFormSpace L n k i := ⟨B', hB'⟩
      set D := fderiv ℝ (fderiv ℝ φ₁) 0 with hD
      have hquad : ∀ t : ℝ, 0 ≤ D (lieValues Η) (lieValues Η) * (t * t) +
          2 * D (lieValues Ξ) (lieValues Η) * t + 0 := by
        intro t
        have h₁ := hb.hessianAtOne_nonneg i le_rfl ((Ξ + t • Η : edgeFormSpace L n k i) :
          Edge L n k i → ComplexMatrix2) (Ξ + t • Η).2
        rw [hhess (Ξ + t • Η) (Ξ + t • Η)] at h₁
        have h₂ : D (lieValues Ξ) (lieValues Ξ) = 0 := by
          rw [← hhess Ξ Ξ]
          exact hz
        have h₃ := hsymm (lieValues Η) (lieValues Ξ)
        simp only [map_add, map_smul, add_apply,
          smul_apply, smul_eq_mul] at h₁
        rw [h₂, h₃] at h₁
        linarith
      have hdis := discrim_le_zero hquad
      have h₄ : (2 * D (lieValues Ξ) (lieValues Η)) ^ 2 ≤ 0 := by
        simpa [discrim] using hdis
      have h₅ : 2 * D (lieValues Ξ) (lieValues Η) = 0 :=
        pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h₄ (sq_nonneg _))
      rw [hhess Ξ Η]
      linarith
    have hclosed : IsClosedEdgeForm ξ := (hb.hessianAtOne_null_iff i le_rfl ξ hξ).1 hnull
    exact hne (eq_zero_of_closed_of_kernel hRel hCl hBl hLat hL hn hi hξ hclosed hQ hLξ)
end Tower.StepQuadraticFormProof
end YangMills.Construction
end
