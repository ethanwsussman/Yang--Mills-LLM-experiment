import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLattice
import YangMills.Construction.InfiniteLattice.MetricForTheWeakTopologyOfRealTests
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsOnTheInfiniteLattice
import YangMills.Construction.InfiniteLattice.WeakLimitPointsAreLimitsOfSequences
import YangMills.Construction.InfiniteLattice.WeakLimitPointsOfExtensionsAreNonEmptyAndClosed
import YangMills.Construction.SubsequentialLimitSet
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicExtensions.LimitSetNonemptyClosed
theorem torusSide_strictMono {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) :
    StrictMono (PeriodicLattice.torusSide L) := by
  have hone : (1 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 1 < L)
  intro m n hmn
  have := pow_lt_pow_right₀ hone hmn
  simp only [PeriodicLattice.torusSide]
  linarith
theorem sidesTendToInfinity_of_strictMono_exponents {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {e : ℕ → ℕ}
    (he : StrictMono e) (hpos : ∀ n, 1 ≤ e n) :
    SidesTendToInfinity L fun n => PeriodicLattice.torusSide L (e n) := by
  refine ⟨fun n _ => ⟨e n, hpos n, rfl⟩, fun s => ?_⟩
  have hone : (1 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 1 < L)
  have hT : Tendsto (fun n => PeriodicLattice.torusSide L (e n)) atTop atTop :=
    ((tendsto_pow_atTop_atTop_of_one_lt hone).comp he.tendsto_atTop).const_mul_atTop two_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atTop.1 hT s)
  refine (Set.finite_lt_nat N).subset fun n hn => ?_
  by_contra hc
  exact hn.2 (hN n (not_lt.1 hc))
theorem mem_limitsOfLiftedMeasures_of_mem_subsequentialLimits
    (hseq : SequentialLimitCharacterization)
    {L K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) {β : ℝ} (hβ : 0 < β)
    {ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ))}
    (hν : ν ∈ subsequentialLimits L K β) :
    ν ∈ limitsOfLiftedMeasures L K β := by
  obtain ⟨e, ρ, he, hpos, hmeas, hconv⟩ := hν
  exact ((hseq L K hL hK β hβ ν).1).2 ⟨fun n => PeriodicLattice.torusSide L (e n), ρ,
    sidesTendToInfinity_of_strictMono_exponents hL he hpos,
    fun n _ => ⟨e n, hpos n, rfl, hmeas n⟩, hconv⟩
theorem mem_subsequentialLimits_of_mem_limitsOfLiftedMeasures
    (hseq : SequentialLimitCharacterization)
    {L K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) {β : ℝ} (hβ : 0 < β)
    {ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ))}
    (hν : ν ∈ limitsOfLiftedMeasures L K β) :
    ν ∈ subsequentialLimits L K β := by
  obtain ⟨ℓ, ρ, ⟨-, hlift, hconv⟩, hinc⟩ := (hseq L K hL hK β hβ ν).2 hν
  have hexp : ∀ n : ℕ, ∃ m : ℕ, 0 < m ∧ ℓ (n + 1) = PeriodicLattice.torusSide L m ∧
      (ρ (n + 1)).measure = liftedWilsonMeasure L m K β :=
    fun n => hlift (n + 1) (by omega)
  choose e hpos hside hmeas using hexp
  refine ⟨e, fun n => ρ (n + 1), ?_, fun n => hpos n, hmeas, ?_⟩
  · refine strictMono_nat_of_lt_succ fun n => (torusSide_strictMono hL).lt_iff_lt.1 ?_
    rw [← hside, ← hside]
    exact hinc (n + 1) (by omega)
  · rw [RealWeakState.tendstoWeakly_iff_tendsto] at hconv ⊢
    exact (tendsto_add_atTop_iff_nat 1).2 hconv
def liftedStates {L K : ℕ} {β : ℝ}
    (hprob : ∀ n : ℕ, MeasureTheory.IsProbabilityMeasure (liftedWilsonMeasure L (n + 1) K β))
    (n : ℕ) : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)) :=
  ⟨liftedWilsonMeasure L (n + 1) K β, hprob n⟩
theorem subsequentialLimits_eq_subseqLimitSet {L K : ℕ} {β : ℝ}
    (hprob : ∀ n : ℕ, MeasureTheory.IsProbabilityMeasure (liftedWilsonMeasure L (n + 1) K β)) :
    subsequentialLimits L K β = Topology.subseqLimitSet (liftedStates hprob) := by
  ext ν
  constructor
  · rintro ⟨e, ρ, he, hpos, hmeas, hconv⟩
    refine ⟨fun n => e n - 1, fun m n hmn => ?_, ?_⟩
    · have := he hmn
      have := hpos m
      show e m - 1 < e n - 1
      omega
    · have hρ : (fun n => liftedStates hprob (e n - 1)) = ρ := by
        funext n
        apply Subtype.ext
        have hn : e n - 1 + 1 = e n := Nat.sub_add_cancel (hpos n)
        show liftedWilsonMeasure L (e n - 1 + 1) K β = (ρ n).measure
        rw [hn, hmeas n]
      rw [hρ]
      exact (RealWeakState.tendstoWeakly_iff_tendsto ρ ν).1 hconv
  · rintro ⟨φ, hφ, hconv⟩
    exact ⟨fun n => φ n + 1, fun n => liftedStates hprob (φ n),
      fun m n hmn => Nat.add_lt_add_right (hφ hmn) 1, fun n => Nat.le_add_left 1 (φ n), fun n => rfl,
      (RealWeakState.tendstoWeakly_iff_tendsto _ ν).2 hconv⟩
theorem limitSetIsNonemptyClosed_holds (hMetric : WeakMetricStatement)
    (hSequences : SequentialLimitCharacterization)
    (hLimitSet : Topology.SubseqLimitSetNonemptyClosed)
    (hSpace : GaugeFieldSpace.Statement)
    (hCovering : LatticeCovering.CoveringStatement) : LimitSetIsNonemptyClosed := by
  intro s β hβ
  have hL := s.isAdmissible
  have hK : 0 < (s.K : ℕ) := s.K.pos
  have hset : limitsOfLiftedMeasures s.L s.K β = subsequentialLimits s.L s.K β :=
    Set.Subset.antisymm
      (fun ν hν => mem_subsequentialLimits_of_mem_limitsOfLiftedMeasures hSequences hL hK hβ hν)
      (fun ν hν => mem_limitsOfLiftedMeasures_of_mem_subsequentialLimits hSequences hL hK hβ hν)
  obtain ⟨F, hF, -⟩ := (hSpace ⟨s, β, hβ⟩).2.2.2.1
  obtain ⟨-, -, -, -, hcompact, hmetrisable⟩ := hMetric s.L s.K hL hK F hF
  have hprob : ∀ n : ℕ,
      MeasureTheory.IsProbabilityMeasure (liftedWilsonMeasure s.L (n + 1) s.K β) := fun n =>
    (hCovering ⟨{ s with m := ⟨n + 1, n.succ_pos⟩ }, β, hβ⟩).2.2.1.2.2.2.2.2
  have hlimits := hLimitSet (RealWeakState (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)))
    (liftedStates hprob)
  rw [← subsequentialLimits_eq_subseqLimitSet hprob, ← hset] at hlimits
  exact ⟨hset, hlimits⟩
end YangMills.Construction.InfiniteLattice.PeriodicExtensions.LimitSetNonemptyClosed
