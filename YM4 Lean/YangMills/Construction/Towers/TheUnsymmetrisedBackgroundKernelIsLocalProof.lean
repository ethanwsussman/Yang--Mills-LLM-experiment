import YangMills.Construction.PeriodicOperators.OperatorFunctionsThatAgreeOnSmallFieldsProof
import YangMills.Construction.Towers.TheActionAndCurrentTermsOfTheKernelAreLocalProof
import YangMills.Construction.Towers.TheGaugeTermOfTheKernelIsLocal
import YangMills.Construction.Towers.TheSecondOrderTermOfTheKernelIsLocal
import YangMills.Construction.Towers.TheUnsymmetrisedBackgroundKernelIsCovariant
import YangMills.Construction.Towers.TheUnsymmetrisedBackgroundKernelIsLocal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RawHessianLocality
open PeriodicOperators FieldValueFunctions UnsymmetrisedKernelTerms
open PeriodicOperators.HolomorphicCoordinateClosure
open FieldValueFunctions.LocalComponents (hessianEntry)
open TorusMetric (euclidNormVec)
theorem euclidNormVec_le_two_mul {v : Fin 4 → ℝ} {θ : ℝ} (h : ∀ i, |v i| < θ) :
    euclidNormVec v ≤ 2 * θ := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelTermsLocality.euclidNormVec_le_two_mul <;> assumption
theorem isSupBelow_of_le {F : PeriodicData} {ζ : F.Carrier → ℂ} {ρ ρ' : ℝ}
    (h : IsSupBelow F ζ ρ) (hle : ρ ≤ ρ') : IsSupBelow F ζ ρ' := by apply _root_.YangMills.Construction.PeriodicOperators.LocalAgreement.isSupBelow_mono <;> assumption
variable {L k : ℕ} {hL : 0 < L}
theorem rawHessianFn_eq_sum (f : (fieldPeriodicData L k hL).Carrier → ℂ)
    (e' e : Fin 3 × PositiveEdge (meshAt L k 0)) :
    rawHessianFn L k hL f e' e =
      (hessianEntry L k hL e'.1 e'.2 e.1 e.2 f + gaugeFixingPairing L k hL e'.1 e'.2 e.1 e.2 f) +
        (sourceBracketTerm L k hL e'.1 e'.2 e.1 e.2 f +
          sourceBracketCovTerm L k hL e'.1 e'.2 e.1 e.2 f -
          quadraticCoarseTerm L k hL e'.1 e'.2 e.1 e.2 f) := rfl
theorem indicesWithin_union_subset {y' y : InfiniteLattice.AmbientSpace}
    (h : ∀ i, |y i - y' i| < 6) :
    UnsymmetrisedKernelTerms.indicesWithin L k hL y' (9 / 2) ∪
        UnsymmetrisedKernelTerms.indicesWithin L k hL y (7 / 2) ⊆
      nearIndices (fieldPeriodicData L k hL) y' 19 := by
  rintro κ (hκ | hκ)
  · have := euclidNormVec_le_two_mul (v := (fieldPeriodicData L k hL).pos κ - y') (θ := 9 / 2)
      fun i => hκ i
    show euclidNormVec _ ≤ 19
    linarith
  · have := euclidNormVec_le_two_mul (v := (fieldPeriodicData L k hL).pos κ - y') (θ := 19 / 2)
      fun i => by
        have h₁ := hκ i
        have h₂ := h i
        have h₃ := abs_sub_le ((fieldPeriodicData L k hL).pos κ i) (y i) (y' i)
        show |(fieldPeriodicData L k hL).pos κ i - y' i| < 19 / 2
        linarith
    show euclidNormVec _ ≤ 19
    linarith
theorem IsLocalTerm.of_radius_le {ρ ρ' : ℝ} {c' c : PositiveEdge (meshAt L k 0)}
    {g : ((fieldPeriodicData L k hL).Carrier → ℂ) → ℂ} (hC : ClosureHolds)
    (hfin : ∀ y ς, (nearIndices (fieldPeriodicData L k hL) y ς).Finite) (hρ : 0 < ρ)
    (hle : ρ ≤ ρ') (hg : IsLocalTerm L k hL ρ' c' c g) : IsLocalTerm L k hL ρ c' c g where
  eq_zero_of_far := fun h ζ hζ => hg.eq_zero_of_far h ζ (isSupBelow_of_le hζ hle)
  holomorphic_of_near := fun h => (hC _ ρ' _ (hρ.trans_le hle)
    ((hfin c'.1.initial 19).subset (indicesWithin_union_subset h))).of_radius_le ρ g hρ hle
      (hg.holomorphic_of_near h)
theorem holds (hC : ClosureHolds)
    (hFin : CovariantFiniteRange.Claim)
    (hTower : LocalKernels.IndexSetPeriodicity.Statement)
    (hA : KernelTermsLocality.ActionAndSourceTermsLocal)
    (hQ : QuadraticTermLocality.QuadraticTermIsLocal)
    (hG : GaugeTermLocality.Claim)
    (hV : RawHessianCovariance.CovarianceClaim) : Claim := by
  intro L hL hStd k hk
  obtain ⟨ρ₁, h₁, hA⟩ := hA L hL hStd k hk
  obtain ⟨ρ₂, h₂, hQ⟩ := hQ L hL hStd k hk
  obtain ⟨ρ₃, h₃, hG⟩ := hG L hL hStd k hk
  obtain ⟨ρ₄, h₄, hV⟩ := hV L hL hStd k hk
  have hfin : ∀ y ς, (nearIndices (fieldPeriodicData L k hL) y ς).Finite :=
    (hFin.1 _ ((hTower L hStd k).2 _).1).1
  obtain ⟨ρ, hρ, l₁, l₂, l₃, l₄⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₁ ∧ ρ ≤ ρ₂ ∧ ρ ≤ ρ₃ ∧ ρ ≤ ρ₄ :=
    ⟨min (min ρ₁ ρ₂) (min ρ₃ ρ₄), lt_min (lt_min h₁ h₂) (lt_min h₃ h₄),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have far : ∀ e' e : Fin 3 × PositiveEdge (meshAt L k 0),
      (∃ i, 6 ≤ |(e.2.1.initial : InfiniteLattice.AmbientSpace) i -
        (e'.2.1.initial : InfiniteLattice.AmbientSpace) i|) →
      ∀ ζ, IsSupBelow (fieldPeriodicData L k hL) ζ ρ → rawHessianFn L k hL ζ e' e = 0 := by
    intro e' e h ζ hζ
    obtain ⟨a₁, a₂, a₃⟩ := hA e'.1 e'.2 e.1 e.2
    rw [rawHessianFn_eq_sum, a₁.eq_zero_of_far h ζ (isSupBelow_of_le hζ l₁),
      a₂.eq_zero_of_far h ζ (isSupBelow_of_le hζ l₁),
      a₃.eq_zero_of_far h ζ (isSupBelow_of_le hζ l₁),
      (hQ e'.1 e'.2 e.1 e.2).eq_zero_of_far h ζ (isSupBelow_of_le hζ l₂),
      (hG e'.1 e'.2 e.1 e.2).eq_zero_of_far h ζ (isSupBelow_of_le hζ l₃)]
    simp
  have near : ∀ e' e : Fin 3 × PositiveEdge (meshAt L k 0),
      (∀ i, |(e.2.1.initial : InfiniteLattice.AmbientSpace) i -
        (e'.2.1.initial : InfiniteLattice.AmbientSpace) i| < 6) →
      HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
        (nearIndices (fieldPeriodicData L k hL) (e'.2.1.initial : InfiniteLattice.AmbientSpace) 19)
        fun ζ => rawHessianFn L k hL ζ e' e := by
    intro e' e h
    obtain ⟨a₁, a₂, a₃⟩ := hA e'.1 e'.2 e.1 e.2
    have c₁ := (IsLocalTerm.of_radius_le hC hfin hρ l₁ a₁).holomorphic_of_near h
    have c₂ := (IsLocalTerm.of_radius_le hC hfin hρ l₁ a₂).holomorphic_of_near h
    have c₃ := (IsLocalTerm.of_radius_le hC hfin hρ l₁ a₃).holomorphic_of_near h
    have c₄ := (IsLocalTerm.of_radius_le hC hfin hρ l₂ (hQ e'.1 e'.2 e.1 e.2)).holomorphic_of_near h
    have c₅ := (IsLocalTerm.of_radius_le hC hfin hρ l₃ (hG e'.1 e'.2 e.1 e.2)).holomorphic_of_near h
    have hT := hC (fieldPeriodicData L k hL) ρ _ hρ
      ((hfin (e'.2.1.initial : InfiniteLattice.AmbientSpace) 19).subset (indicesWithin_union_subset h))
    have hW := hC (fieldPeriodicData L k hL) ρ _ hρ
      (hfin (e'.2.1.initial : InfiniteLattice.AmbientSpace) 19)
    refine hW.of_subset _ _ (indicesWithin_union_subset h) ?_
    have hneg := hT.mul _ _ (hT.const (-1)) c₄
    refine hT.congr_below _ _ (fun ζ _ => ?_)
      (hT.add _ _ (hT.add _ _ c₁ c₅) (hT.add _ _ (hT.add _ _ c₂ c₃) hneg))
    rw [rawHessianFn_eq_sum]
    ring
  refine ⟨ρ, hρ, ?_, ?_, ?_⟩
  · intro ζ hζ e' e hn
    refine far e' e ?_ ζ hζ
    by_contra hc
    push Not at hc
    have := euclidNormVec_le_two_mul
      (v := (colourEdges L k 0).pos e - (colourEdges L k 0).pos e') (θ := 6) hc
    exact hn (by linarith)
  · intro e' e
    by_cases h : ∀ i, |(e.2.1.initial : InfiniteLattice.AmbientSpace) i -
        (e'.2.1.initial : InfiniteLattice.AmbientSpace) i| < 6
    · exact near e' e h
    · push Not at h
      have hW := hC (fieldPeriodicData L k hL) ρ _ hρ
        (hfin (e'.2.1.initial : InfiniteLattice.AmbientSpace) 19)
      exact hW.congr_below _ _ (fun ζ hζ => (far e' e h ζ hζ).symm) (hW.const 0)
  · exact fun ζ hζ n e' e => hV ζ (isSupBelow_of_le hζ l₄) n e' e
end YangMills.Construction.Tower.FullSpace.RawHessianLocality
end
