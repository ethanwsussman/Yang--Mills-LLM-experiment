import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMaps
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantOnTheSidesProof
import YangMills.Construction.Towers.FactsOfTheLeftChart
import YangMills.Construction.Towers.IterateOfTheAveragingMapsNearTheTrivialConfiguration
import YangMills.Construction.Towers.PropertiesOfTheGaugeFixingFunctions
import YangMills.Construction.Towers.RealAnalyticMapsOfConfigurationsAreDifferentiable
import YangMills.Construction.Towers.ReverseOfAStraightPathOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces
namespace SmoothingIterProof
theorem isSubspaceAnalyticToProduct_congr {S R S' R' : Type} [Fintype S] [Fintype R]
    {E : Submodule ℝ (S → ComplexMatrix2)} {E' : Submodule ℝ (S' → ComplexMatrix2)}
    {W W' : Set (R ⊕ S → ComplexMatrix2)}
    {f g : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2} (hW : W = W') (hfg : EqOn f g W)
    (hf : IsSubspaceAnalyticToProduct E E' W f) : IsSubspaceAnalyticToProduct E E' W' g := by
  subst hW
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hf
  refine ⟨h₁, h₂, fun p hp => hfg hp ▸ h₃ hp, fun p hp => ?_⟩
  obtain ⟨X, hpX, hO, hsub, Ψ, hΨ, heq⟩ := h₄ p hp
  exact ⟨X, hpX, hO, hsub, Ψ, hΨ, fun q hq => (heq hq).trans (hfg (hsub hq))⟩
theorem isSubspaceAnalyticToProduct_comp_bot {R R' R'' : Type} [Fintype R] [Fintype R']
    [Fintype R''] (hK : AnalyticCalculus.AnalyticCalculusStatement)
    {W : Set (R ⊕ Empty → ComplexMatrix2)} {W' : Set (R' ⊕ Empty → ComplexMatrix2)}
    {f : (R ⊕ Empty → ComplexMatrix2) → R' ⊕ Empty → ComplexMatrix2}
    {f' : (R' ⊕ Empty → ComplexMatrix2) → R'' ⊕ Empty → ComplexMatrix2}
    (hf : IsSubspaceAnalyticToProduct (⊥ : Submodule ℝ (Empty → ComplexMatrix2))
      (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) W f)
    (hf' : IsSubspaceAnalyticToProduct (⊥ : Submodule ℝ (Empty → ComplexMatrix2))
      (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) W' f') :
    IsSubspaceAnalyticToProduct (⊥ : Submodule ℝ (Empty → ComplexMatrix2))
      (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) (W ∩ f ⁻¹' W') (f' ∘ f) := by
  have hcomp := (((hK Empty R Empty R').2.2.2 ⊥ ⊥ bot_le bot_le).2.2.1 W hf.1).2.2.1
  exact ((hcomp f hf).2 W' hf'.1).2.2 Empty R'' ⊥ f' hf'
section Fields
variable {L n k j j' : ℕ}
theorem isPositivelyOriented_or_opposite {m : ℕ} {i : ℤ} (e : PeriodicLattice.Bond L m i) :
    e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
theorem opposite_opposite {m : ℕ} {i : ℤ} (e : PeriodicLattice.Bond L m i) :
    e.opposite.opposite = e := by apply _root_.YangMills.SharedProofs.p1012 <;> assumption
theorem fieldOfPositiveValues_restrict {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges U) = U := by apply _root_.YangMills.SharedProofs.p407 <;> assumption
theorem isAnalyticFieldMap_comp (hK : AnalyticCalculus.AnalyticCalculusStatement)
    {O₁ : Set (Edge L n k 0 → ComplexMatrix2)} {O₂ : Set (Edge L n k j → ComplexMatrix2)}
    {φ₁ : (Edge L n k 0 → ComplexMatrix2) → Edge L n k j → ComplexMatrix2}
    {φ₂ : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (h₁ : IsAnalyticFieldMap O₁ φ₁) (h₂ : IsAnalyticFieldMap O₂ φ₂)
    (hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup (compositeDomain O₁ O₂ φ₁)) :
    IsAnalyticFieldMap (compositeDomain O₁ O₂ φ₁) (φ₂ ∘ φ₁) := by
  obtain ⟨-, hmap₁, i₀, i₁, hA₁⟩ := h₁
  obtain ⟨-, hmap₂, i₁', i₂, hA₂⟩ := h₂
  obtain rfl : i₁' = i₁ := Subsingleton.elim _ _
  refine ⟨hopen, fun U hU => hmap₂ hU.2, i₀, i₂, ?_⟩
  have hback : ∀ q : PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2,
      fieldOfPositiveValues (groupComponent q) ∈ O₁ →
      fieldOfPositiveValues (restrictToPositiveEdges (φ₁ (fieldOfPositiveValues (groupComponent q)))) =
        φ₁ (fieldOfPositiveValues (groupComponent q)) :=
    fun q hq => fieldOfPositiveValues_restrict (hmap₁ hq)
  refine isSubspaceAnalyticToProduct_congr ?_ ?_ (isSubspaceAnalyticToProduct_comp_bot hK hA₁ hA₂)
  · ext q
    constructor
    · rintro ⟨hq, hq'⟩
      refine ⟨hq, ?_⟩
      have hq'' : fieldOfPositiveValues (restrictToPositiveEdges
          (φ₁ (fieldOfPositiveValues (groupComponent q)))) ∈ O₂ := hq'
      rwa [hback q hq] at hq''
    · rintro ⟨hq, hq'⟩
      refine ⟨hq, ?_⟩
      change fieldOfPositiveValues (restrictToPositiveEdges
        (φ₁ (fieldOfPositiveValues (groupComponent q)))) ∈ O₂
      rwa [hback q hq]
  · rintro q ⟨hq, -⟩
    change ofParts (restrictToPositiveEdges (φ₂ (fieldOfPositiveValues (restrictToPositiveEdges
      (φ₁ (fieldOfPositiveValues (groupComponent q))))))) Empty.elim = _
    rw [hback q hq]
    rfl
theorem ofReal_smul_mem_hermitianTraceless {A : ComplexMatrix2} (r : ℝ)
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    (r : ℂ) • A ∈ ComplexMatrix2.hermitianTraceless := by
  have h : (r : ℂ) • A = r • A := by
    ext a b
    simp
  rw [h]
  exact ComplexMatrix2.hermitianTraceless.smul_mem r hA
theorem edgeForm_apply_mem {ω : Edge L n k j → ComplexMatrix2} (hω : ω ∈ edgeFormSpace L n k j)
    (e : Edge L n k j) : ω e ∈ ComplexMatrix2.hermitianTraceless := by
  rcases isPositivelyOriented_or_opposite e with h | h
  · exact hω.1 e h
  · have h₁ : ω e.opposite.opposite = -ω e.opposite := hω.2 e.opposite
    rw [opposite_opposite] at h₁
    rw [h₁]
    exact ComplexMatrix2.hermitianTraceless.neg_mem (hω.1 _ h)
theorem bondFormSumAlong_mem {ω : Edge L n k j → ComplexMatrix2} (hω : ω ∈ edgeFormSpace L n k j)
    (γ : List (Edge L n k j)) :
    PeriodicLattice.bondFormSumAlong ω γ ∈ ComplexMatrix2.hermitianTraceless := by
  refine list_sum_mem fun x hx => ?_
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  exact edgeForm_apply_mem hω e
theorem contourFormAverage_mem {ω : Edge L n k j → ComplexMatrix2}
    (hω : ω ∈ edgeFormSpace L n k j) {i : ℤ} (y : PeriodicLattice.Site L n i)
    (x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)) :
    PeriodicLattice.contourFormAverage ω y x ∈ ComplexMatrix2.hermitianTraceless :=
  ofReal_smul_mem_hermitianTraceless _ (sum_mem fun _ _ => bondFormSumAlong_mem hω _)
theorem linearSmoothing_mem_edgeFormSpace (hF : AxisPathReversal.MainStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    {ω : Edge L n k j → ComplexMatrix2} (hω : ω ∈ edgeFormSpace L n k j) :
    linearSmoothing L n k j ω ∈ edgeFormSpace L n k (j + 1) := by
  have hside := (hF L hL k).1 n hn
  refine ⟨fun c _ => ?_, fun c => ?_⟩
  · refine ofReal_smul_mem_hermitianTraceless _ ?_
    refine finsum_mem_induction (· ∈ ComplexMatrix2.hermitianTraceless)
      ComplexMatrix2.hermitianTraceless.zero_mem
      (fun _ _ h h' => ComplexMatrix2.hermitianTraceless.add_mem h h') fun x _ => ?_
    exact ComplexMatrix2.hermitianTraceless.sub_mem
      (ComplexMatrix2.hermitianTraceless.add_mem (contourFormAverage_mem hω _ _)
        (bondFormSumAlong_mem hω _))
      (contourFormAverage_mem hω _ _)
  · exact (hside.2 j hj c ω ((hside.1 j hj.le).1 ω hω)).2
end Fields
theorem smoothingIter_near_trivial {L n k : ℕ}
    (hA : SmoothingNearIdentity)
    (hC : LeftChartFacts.HoldEverywhere)
    (hD : AnalyticMapDifferentiableStatement)
    (hG : AxialFunctionFacts.statement)
    (hK : AnalyticCalculus.AnalyticCalculusStatement)
    (hF : AxisPathReversal.MainStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (i : ℕ) (hi : i < k) :
    smoothingIter L n k (i + 1) (trivialField L n k 0) = trivialField L n k (i + 1) ∧
      ∃ O : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne O ∧
        IsAnalyticFieldMap O (smoothingIter L n k (i + 1)) ∧
        ∀ ω ∈ edgeFormSpace L n k 0,
          linearSmoothingIter L n k (i + 1) ω ∈ edgeFormSpace L n k (i + 1) ∧
          leftDifferential (smoothingIter L n k (i + 1)) (trivialField L n k 0) ω =
            linearSmoothingIter L n k (i + 1) ω := by
  induction i with
  | zero =>
    have hstep := (hA.1 L hL).1 n k 0 hn hi
    obtain ⟨O, hO, hφ, -⟩ := hstep.1.analytic
    obtain ⟨-, -, -, hQ⟩ := hstep.2.1.deriv_eq_linear
    have he : smoothingIter L n k (0 + 1) = smoothingStep L n k 0 := rfl
    have hl : linearSmoothingIter L n k (0 + 1) = linearSmoothing L n k 0 := rfl
    rw [he, hl]
    exact ⟨(hG L n k 0 hL hn hi).smoothingStep_trivial, O, hO, hφ,
      fun ω hω => ⟨linearSmoothing_mem_edgeFormSpace hF hL hn hi hω, hQ ω hω⟩⟩
  | succ i ih =>
    obtain ⟨hone, O₁, hO₁, hφ₁, hQ₁⟩ := ih (by omega)
    have hstep := (hA.1 L hL).1 n k (i + 1) hn hi
    obtain ⟨O₂, hO₂, hφ₂, -⟩ := hstep.1.analytic
    obtain ⟨-, -, -, hQ₂⟩ := hstep.2.1.deriv_eq_linear
    have hchain := ((hC L k 0 (i + 1) (i + 1 + 1) hL (Nat.zero_le k) (by omega) (by omega)).2.1
      n hn).2.2.1
    have hd₁ := hD L n k 0 (i + 1) hL hn (Nat.zero_le k) (by omega) O₁ _ hφ₁
    have hd₂ := hD L n k (i + 1) (i + 1 + 1) hL hn (by omega) (by omega) O₂ _ hφ₂
    obtain ⟨hdc, hcr⟩ := hchain.1 O₁ O₂ _ _ hd₁ hd₂
    have he : smoothingIter L n k (i + 1 + 1) =
        smoothingStep L n k (i + 1) ∘ smoothingIter L n k (i + 1) := rfl
    have hl : ∀ ω, linearSmoothingIter L n k (i + 1 + 1) ω =
        linearSmoothing L n k (i + 1) (linearSmoothingIter L n k (i + 1) ω) := fun _ => rfl
    have hmem : trivialField L n k 0 ∈ compositeDomain O₁ O₂ (smoothingIter L n k (i + 1)) := by
      refine ⟨hO₁.2, ?_⟩
      change smoothingIter L n k (i + 1) (trivialField L n k 0) ∈ O₂
      rw [hone]
      exact hO₂.2
    rw [he]
    refine ⟨?_, compositeDomain O₁ O₂ (smoothingIter L n k (i + 1)), ⟨hdc.1, hmem⟩,
      isAnalyticFieldMap_comp hK hφ₁ hφ₂ hdc.1, fun ω hω => ?_⟩
    · rw [Function.comp_apply, hone]
      exact (hG L n k (i + 1) hL hn hi).smoothingStep_trivial
    · rw [hl]
      obtain ⟨hform, hdiff⟩ := hQ₁ ω hω
      refine ⟨linearSmoothing_mem_edgeFormSpace hF hL hn hi hform, ?_⟩
      rw [hcr _ hmem ω hω, hone, hdiff]
      exact hQ₂ _ hform
end SmoothingIterProof
theorem smoothingIterAnalyticNearOne_holds
    (hA : SmoothingNearIdentity)
    (hC : LeftChartFacts.HoldEverywhere)
    (hD : AnalyticMapDifferentiableStatement)
    (hG : AxialFunctionFacts.statement)
    (hK : AnalyticCalculus.AnalyticCalculusStatement)
    (hF : AxisPathReversal.MainStatement) :
    SmoothingIterAnalyticNearOne := by
  intro L n k i hL hn hi
  obtain ⟨-, O, hO, hφ, hQ⟩ :=
    SmoothingIterProof.smoothingIter_near_trivial hA hC hD hG hK hF hL hn i hi
  exact ⟨O, hO, hφ, fun ω hω => (hQ ω hω).2⟩
end YangMills.Construction.Tower
end
