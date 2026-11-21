import YangMills.Construction.InfiniteLattice.AllMirrorsAtSpacingOne
import YangMills.Construction.InfiniteLattice.FunctionsStatesSupportsClassesMirrorsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAtASpacing
import YangMills.Construction.InfiniteLattice.PeriodsFoldCompactnessAndLimitsOfTori
import YangMills.Construction.InfiniteLattice.TransportToSpacingOne
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open MeasureTheory Filter NormalFamilies UnitSpacing LatticeConventions
open LatticeConventions.NormalHyperplane
open scoped NNReal ComplexOrder
noncomputable section
namespace InfiniteLattice.PeriodicGibbsAtSpacing
variable {a : ℝ}
theorem norm_ge_of_mem_latticeSubgroup {c : ℝ} (hc : 0 < c) {x : AmbientSpace}
    (hx : x ∈ latticeSubgroup c) (hx0 : x ≠ 0) : c ≤ ‖x‖ := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨μ, hμ⟩ : ∃ μ, k μ ≠ 0 := by
    by_contra hnone
    have hzero : ∀ μ, k μ = 0 := fun μ => by_contra fun h => hnone ⟨μ, h⟩
    exact hx0 (funext fun μ => by simp [hk μ, hzero μ])
  have hone : (1 : ℝ) ≤ |(k μ : ℝ)| := by
    have h : (1 : ℤ) ≤ |k μ| := Int.one_le_abs hμ
    exact_mod_cast h
  calc c = 1 * c := (one_mul c).symm
    _ ≤ |(k μ : ℝ)| * c := mul_le_mul_of_nonneg_right hone hc.le
    _ = ‖x μ‖ := by rw [hk μ, Real.norm_eq_abs, abs_mul, abs_of_pos hc]
    _ ≤ ‖x‖ := norm_le_pi_norm x μ
def cubicPeriodSublattice (ha : 0 < a) (s : ℤ) (hs : 3 ≤ s) : PeriodSublattice a where
  periods := cubicSublattice a ((s : ℝ) * a)
  exists_linearIndependent := by
    have hsa : (s : ℝ) * a ≠ 0 := by
      have : (3 : ℝ) ≤ s := by exact_mod_cast hs
      have : (0 : ℝ) < s := by linarith
      positivity
    refine ⟨fun i => ⟨Pi.single i ((s : ℝ) * a), Pi.single i s, fun μ => ?_⟩, fun i => ?_, ?_⟩
    · by_cases h : μ = i
      · subst h
        simp
      · simp [h]
    · refine AddSubgroup.mem_addSubgroupOf.2 ⟨Pi.single i 1, fun μ => ?_⟩
      by_cases h : μ = i
      · subst h
        simp
      · simp [h]
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h := congrFun hg i
      simp [Finset.sum_apply, Pi.single_apply] at h
      rcases h with h | h
      · exact h
      · exact absurd (by simp [h]) hsa
  le_norm_of_ne_zero := by
    intro γ hγ hγ0
    have hs3 : (3 : ℝ) ≤ s := by exact_mod_cast hs
    have hpos : 0 < (s : ℝ) * a := by
      have : (0 : ℝ) < s := by linarith
      positivity
    have hne : (γ : AmbientSpace) ≠ 0 := fun h => hγ0 (Subtype.ext h)
    have h := norm_ge_of_mem_latticeSubgroup hpos (AddSubgroup.mem_addSubgroupOf.1 hγ) hne
    have hle : minimalPeriodRatio * a ≤ (s : ℝ) * a :=
      mul_le_mul_of_nonneg_right (by simpa [minimalPeriodRatio] using hs3) ha.le
    exact hle.trans h
theorem nonzeroNorms_nonempty (Γ : PeriodSublattice a) :
    {s | ∃ γ ∈ Γ.periods, γ ≠ 0 ∧ s = ‖(γ : AmbientSpace)‖}.Nonempty := by
  obtain ⟨v, hv, hli⟩ := Γ.exists_linearIndependent
  exact ⟨_, v 0, hv 0, fun h => hli.ne_zero 0 (by simp [h]), rfl⟩
theorem le_minNonzeroNorm_cubic (ha : 0 < a) (s : ℤ) (hs : 3 ≤ s) :
    (s : ℝ) * a ≤ (cubicPeriodSublattice ha s hs).minNonzeroNorm := by
  have hs3 : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hpos : 0 < (s : ℝ) * a := by
    have : (0 : ℝ) < s := by linarith
    positivity
  refine le_csInf (nonzeroNorms_nonempty _) ?_
  rintro _ ⟨γ, hγ, hγ0, rfl⟩
  exact norm_ge_of_mem_latticeSubgroup hpos (AddSubgroup.mem_addSubgroupOf.1 hγ)
    fun h => hγ0 (Subtype.ext h)
theorem periodicGibbsSymmetric
    (hMirrors : UnitMeshReflectionPositivity.Statement) (hDil : UnitSpacing.TransportToUnitSpacing)
    (hFacts : BasicStructure.Statement)
    (ha : 0 < a) {β : ℝ} (hβ : 0 < β) : PeriodicGibbsSymmetric a β := by
  intro ν _ hν
  obtain ⟨_, _, hIso, hMir, _, _, hInv, hCl, _⟩ := hDil a β ha hβ
  obtain ⟨_, _, _, _, _, _, hKer, hNames⟩ := hFacts.1 a ha β hβ
  obtain ⟨_, _, hPer, _⟩ := hKer
  have hstate : IsLatticeState ν := (inferInstance : IsProbabilityMeasure ν)
  have hνper : ν ∈ periodicGibbsClass ha β := by
    rw [hPer]
    exact hν
  have hν₁ := ((hCl ν hstate).2.2).1 hνper
  obtain ⟨hM, hSh, hW⟩ := (hMirrors β hβ).1 _ hν₁
  refine ⟨fun v => ?_, fun r w hw hr => ?_, fun Q hQ => ?_⟩
  · exact ((hInv ν hstate).1 (shift v) (shift (pointRescale ha v))
      (hIso.2.2.1 v).symm).2 (hSh _)
  · obtain ⟨r₁, hr₁, _⟩ := hIso.1 r
    have hrw : r.toFun = ⇑w := funext hr
    have hr₁w : r₁.toFun = ⇑w := by
      rw [hr₁, hrw]
      exact hIso.2.2.2 w hw
    exact ((hInv ν hstate).1 r r₁ hr₁).2 (hW r₁ ⟨w, hw, hr₁w⟩)
  · obtain ⟨P, ς, _, _, hrefl, hconj, hplus, hminus⟩ := hNames.2.1 Q hQ
    let P₁ : NormalLevelPair 1 :=
      ⟨P.normal, P.normal_mem, P.level / a, (hMir.1 _ P.normal_mem _).1 P.allowed⟩
    obtain ⟨hθ, _, _⟩ := hMir.2 P P₁ rfl rfl
    have hsymQ : IsSymmetricUnder ν (reflectSymmetry hQ) :=
      ((hInv ν hstate).1 (reflectSymmetry hQ) P₁.reflectSymmetry (by
        change reflectAcross P₁.normal P₁.level = conjugateByScaling a Q.reflect
        rw [hrefl, hθ])).2 fun A hA => (hM P₁).1 A hA
    have hpos : ∀ ε : ℤˣ, ∀ F ∈ halfSpaceObservables a P.normal P.level ε,
        0 ≤ stateEval ν (P.conjReflectObservable F * F) := by
      intro ε
      refine ((hInv ν hstate).2 P P₁ rfl rfl ε).2 fun F hF => (hM P₁).2 F ?_
      rcases Int.units_eq_one_or ε with rfl | rfl
      · exact Or.inl hF
      · exact Or.inr hF
    have hpair : ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        mirrorPairing hQ F = P.conjReflectObservable F * F := by
      intro F hF
      funext U
      have h := congrFun (hconj F hF) U
      simp only [mirrorPairing, Pi.mul_apply]
      rw [← h]
      rfl
    have hupper : ∀ F ∈ regionObservables a Q.upperHalfSpace,
        0 ≤ stateEval ν (mirrorPairing hQ F) := by
      intro F hF
      rw [hpair F hF.1]
      exact hpos ς F (hplus ▸ hF)
    refine ⟨hsymQ, hupper, fun F hF => ?_, fun F => ?_⟩
    · rw [hpair F hF.1]
      exact hpos (-ς) F (hminus ▸ hF)
    · obtain ⟨F, hF⟩ := F
      obtain ⟨B, _, hFB⟩ := Set.mem_iUnion₂.1 hF
      have hobs : F ∈ regionObservables a Q.upperHalfSpace :=
        ⟨hFB.1, hFB.2.mono (biSup_mono fun _ hb => ⟨hb.1.1, hb.2.1⟩) le_rfl⟩
      have h0 := hupper F hobs
      have hval : reflectionForm hQ ν ⟨F, hF⟩ ⟨F, hF⟩ = stateEval ν (mirrorPairing hQ F) := rfl
      rw [hval]
      exact ⟨by simpa using (Complex.le_def.1 h0).2.symm, by simpa using (Complex.le_def.1 h0).1⟩
theorem cubicPeriodsAdmissible (ha : 0 < a) : CubicPeriodsAdmissible a := by
  intro s hs hlim
  have h3 : ∀ i, 3 ≤ max (s i) 3 := fun i => le_max_right _ _
  refine ⟨fun i => cubicPeriodSublattice ha (max (s i) 3) (h3 i), fun i hi => ?_, ?_⟩
  · change cubicSublattice a (((max (s i) 3 : ℤ) : ℝ) * a) = _
    rw [max_eq_left (hs i hi)]
  · have hreal : Tendsto (fun i => (s i : ℝ) * a) atTop atTop :=
      (tendsto_intCast_atTop_atTop.comp hlim).atTop_mul_const ha
    refine tendsto_atTop_mono (fun i => ?_) hreal
    refine le_trans ?_ (le_minNonzeroNorm_cubic ha _ (h3 i))
    refine mul_le_mul_of_nonneg_right ?_ ha.le
    exact_mod_cast le_max_left (s i) 3
theorem torusLimitsAreShiftInvariantGibbs
    (hMirrors : UnitMeshReflectionPositivity.Statement) (hDil : UnitSpacing.TransportToUnitSpacing)
    (hFacts : BasicStructure.Statement)
    (hFold : PeriodicGibbsFoldAndCompactness.Statement)
    (ha : 0 < a) {β : ℝ} (hβ : 0 < β) : TorusLimitsAreShiftInvariantGibbs a β := by
  intro Γ hΓ ν _ hlim
  obtain ⟨hLat, _, _, _, _, hSt, _, hCl, hTori⟩ := hDil a β ha hβ
  obtain ⟨_, _, _, _, _, _, hKer, _⟩ := hFacts.1 a ha β hβ
  obtain ⟨_, _, _, hTop⟩ := hKer
  have hstate : IsLatticeState ν := (inferInstance : IsProbabilityMeasure ν)
  have hex : ∀ i, ∃ Λ : PeriodSublattice 1, Λ.periods = subgroupRescale ha (Γ i).periods :=
    fun i => (hTori.1 _).1 ⟨Γ i, rfl⟩
  choose Λ hΛ using hex
  have hprop := fun i => hTori.2 (Γ i) (Λ i) (hΛ i)
  have hΛlim : MinNonzeroNormTendsToInfinity Λ := by
    have hfun : (fun i => (Λ i).minNonzeroNorm) =
        fun i => a⁻¹ * (Γ i).minNonzeroNorm := funext fun i => (hprop i).2.2.2.2
    unfold MinNonzeroNormTendsToInfinity
    rw [hfun]
    exact hΓ.const_mul_atTop (inv_pos.2 ha)
  have hν₁ : IsWeakClusterPoint (fun i => (Λ i).liftedGibbsMeasure β)
      (dilatedState ha ν) := by
    have h := (hSt.2.2.2.2 ν _ hstate fun i _ => (hprop i).1).1 hlim
    have e : (fun i => dilatedState ha ((Γ i).liftedGibbsMeasure β)) =
        fun i => (Λ i).liftedGibbsMeasure β := funext fun i => (hprop i).2.1
    rwa [e] at h
  have hmem := (hFold β hβ).2.2.2.1.2 Λ hΛlim _ (hSt.1 ν hstate).1 hν₁
  have htop : subgroupRescale ha ⊤ = ⊤ := AddSubgroup.map_top_of_surjective _ hLat.1
  have hcl : ν ∈ subgroupInvariantGibbsClass ha β ⊤ :=
    ((hCl ν hstate).2.1 ⊤).2 (by rw [htop]; exact hmem)
  rw [hTop] at hcl
  obtain ⟨hg, ht⟩ := hcl
  have hper : IsPeriodicGibbs β ν := ⟨hg, ⊤, inferInstance, fun v _ => ht v⟩
  exact ⟨hg, ht, hper, periodicGibbsSymmetric hMirrors hDil hFacts ha hβ ν hper⟩
theorem periodicGibbsSetCharacterization
    (hMirrors : UnitMeshReflectionPositivity.Statement) (hDil : UnitSpacing.TransportToUnitSpacing)
    (hFacts : BasicStructure.Statement)
    (hFold : PeriodicGibbsFoldAndCompactness.Statement)
    (ha : 0 < a) {β : ℝ} (hβ : 0 < β) : PeriodicGibbsSetCharacterization a β := by
  obtain ⟨_, _, _, _, _, _, _, _, hTori⟩ := hDil a β ha hβ
  obtain ⟨_, _, hStates, _, _, _, hKer, _⟩ := hFacts.1 a ha β hβ
  obtain ⟨_, _, _, hTop⟩ := hKer
  have hset : {ν : Measure (GaugeField a) | IsPeriodicGibbs β ν} =
      {ν | IsGibbs β ν ∧ IsShiftInvariant ν} := by
    ext ν
    constructor
    · intro h
      have : IsProbabilityMeasure ν := h.1.1
      exact ⟨h.1, (periodicGibbsSymmetric hMirrors hDil hFacts ha hβ ν h).1⟩
    · rintro ⟨hg, ht⟩
      exact ⟨hg, ⊤, inferInstance, fun v _ => ht v⟩
  have hcls : {ν : Measure (GaugeField a) | IsPeriodicGibbs β ν} =
      subgroupInvariantGibbsClass ha β ⊤ := hset.trans hTop.symm
  obtain ⟨_, hconv, hcomp⟩ := (hFold β hβ).2.2.1 a ha ⊤
  refine ⟨hset, ?_, hcls ▸ hconv, hcls ▸ hcomp⟩
  have hs : Tendsto (fun i : ℕ => (i : ℤ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  obtain ⟨Γ, _, hΓ⟩ := cubicPeriodsAdmissible ha (fun i : ℕ => (i : ℤ) + 3)
    (fun i _ => by omega) hs
  have hst : ∀ i, IsLatticeState ((Γ i).liftedGibbsMeasure β) := fun i => by
    obtain ⟨Λ, hΛ⟩ := (hTori.1 _).1 ⟨Γ i, rfl⟩
    exact (hTori.2 (Γ i) Λ hΛ).1
  obtain ⟨ν₀, hν₀, hl⟩ := hStates.2.2.2.2.1 (fun i => (Γ i).liftedGibbsMeasure β)
    fun i _ => hst i
  have : IsProbabilityMeasure ν₀ := hν₀
  exact ⟨ν₀, (torusLimitsAreShiftInvariantGibbs hMirrors hDil hFacts hFold ha hβ
    Γ hΓ ν₀ hl).2.2.1⟩
theorem statement_holds (hMirrors : UnitMeshReflectionPositivity.Statement)
    (hDil : UnitSpacing.TransportToUnitSpacing)
    (hFacts : BasicStructure.Statement)
    (hFold : PeriodicGibbsFoldAndCompactness.Statement) : Statement :=
  fun _ ha _ hβ =>
    ⟨periodicGibbsSymmetric hMirrors hDil hFacts ha hβ,
      cubicPeriodsAdmissible ha,
      torusLimitsAreShiftInvariantGibbs hMirrors hDil hFacts hFold ha hβ,
      periodicGibbsSetCharacterization hMirrors hDil hFacts hFold ha hβ⟩
end InfiniteLattice.PeriodicGibbsAtSpacing
end
end YangMills.Construction
