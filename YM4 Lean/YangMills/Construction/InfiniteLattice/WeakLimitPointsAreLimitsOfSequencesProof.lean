import YangMills.Construction.InfiniteLattice.MetricForTheWeakTopologyOfRealTests
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsOnTheInfiniteLattice
import YangMills.Construction.InfiniteLattice.WeakLimitPointsAreLimitsOfSequences
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicExtensions.SequentialLimits
variable {L K : ℕ} {β : ℝ}
theorem isLimitOfLiftedMeasures_of_isLimitAlongSideSequence
    {ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ))} {ℓ : ℕ → ℝ}
    {ρ : ℕ → RealWeakState (PeriodicLattice.meshSize L (K : ℤ))}
    (h : IsLimitAlongSideSequence L K β ℓ ρ ν) : IsLimitOfLiftedMeasures L K β ν := by
  obtain ⟨⟨-, hfin⟩, hρ, hlim⟩ := h
  intro N hN t
  have h1 : ∀ᶠ i in atTop, ρ i ∈ N :=
    ((RealWeakState.tendstoWeakly_iff_tendsto ρ ν).1 hlim) hN
  have h2 : ∀ᶠ i : ℕ in atTop, i ∉ {i : ℕ | 1 ≤ i ∧ ¬ t ≤ ℓ i} := by
    rw [← Nat.cofinite_eq_atTop]
    exact (hfin t).compl_mem_cofinite
  obtain ⟨i, hiN, hit, hi1⟩ := (h1.and (h2.and (eventually_ge_atTop 1))).exists
  obtain ⟨m, hm, hℓ, hμ⟩ := hρ i hi1
  have ht : t ≤ ℓ i := by
    by_contra hc
    exact hit ⟨hi1, hc⟩
  exact ⟨m, hm, hℓ ▸ ht, ρ i, hiN, hμ⟩
theorem exists_strictMono_sides_of_isLimitOfLiftedMeasures
    {ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ))} [(𝓝 ν).IsCountablyGenerated]
    (h : IsLimitOfLiftedMeasures L K β ν) :
    ∃ ℓ ρ, IsLimitAlongSideSequence L K β ℓ ρ ν ∧ ∀ i, 1 ≤ i → ℓ i < ℓ (i + 1) := by
  obtain ⟨u, hu⟩ := (𝓝 ν).exists_antitone_basis
  have hmem : ∀ n, u n ∈ 𝓝 ν := fun n => hu.1.mem_of_mem trivial
  have hch : ∀ (n : ℕ) (t : ℝ),
      ∃ x : ℝ × RealWeakState (PeriodicLattice.meshSize L (K : ℤ)),
        t ≤ x.1 ∧ x.2 ∈ u n ∧ IsLiftedMeasureAtSide L K β x.1 x.2 := by
    intro n t
    obtain ⟨m, hm, ht, ρ, hρ, hμ⟩ := h (u n) (hmem n) t
    exact ⟨(PeriodicLattice.torusSide L m, ρ), ht, hρ, m, hm, rfl, hμ⟩
  choose sel hsel1 hsel2 hsel3 using hch
  let g : ℕ → ℝ × RealWeakState (PeriodicLattice.meshSize L (K : ℤ)) :=
    fun n => Nat.rec (0, ν) (fun n x => sel (n + 1) (x.1 + 1)) n
  have g_succ : ∀ n, g (n + 1) = sel (n + 1) ((g n).1 + 1) := fun n => rfl
  have hstep : ∀ n, (g n).1 + 1 ≤ (g (n + 1)).1 := by
    intro n
    rw [g_succ]
    exact hsel1 _ _
  have hge : ∀ n : ℕ, (n : ℝ) ≤ (g n).1 := by
    intro n
    induction n with
    | zero => simp [g]
    | succ n ih =>
      have := hstep n
      push_cast
      linarith
  have hlift : ∀ i, 1 ≤ i → IsLiftedMeasureAtSide L K β (g i).1 (g i).2 := by
    intro i hi
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    rw [g_succ]
    exact hsel3 _ _
  refine ⟨fun i => (g i).1, fun i => (g i).2, ⟨⟨?_, ?_⟩, hlift, ?_⟩, ?_⟩
  · intro i hi
    obtain ⟨m, hm, hℓ, -⟩ := hlift i hi
    exact ⟨m, hm, hℓ⟩
  · intro t
    refine (Set.finite_Iic ⌈t⌉₊).subset ?_
    rintro i ⟨-, hi⟩
    by_contra hc
    have hlt : ⌈t⌉₊ < i := not_le.1 hc
    have hcast : ((⌈t⌉₊ : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast hlt.le
    exact hi ((Nat.le_ceil t).trans (hcast.trans (hge i)))
  · refine (RealWeakState.tendstoWeakly_iff_tendsto _ _).2 (hu.tendsto fun i => ?_)
    cases i with
    | zero => exact mem_of_mem_nhds (hmem 0)
    | succ n =>
      show (g (n + 1)).2 ∈ u (n + 1)
      rw [g_succ]
      exact hsel2 _ _
  · intro i _
    have := hstep i
    show (g i).1 < (g (i + 1)).1
    linarith
theorem metrizableSpace_realWeakState
    (hM : WeakMetricStatement)
    (hS : GaugeFieldSpace.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (hβ : 0 < β) :
    TopologicalSpace.MetrizableSpace (RealWeakState (PeriodicLattice.meshSize L (K : ℤ))) := by
  let d : CutoffLinks.CutoffData :=
    { L := L, isAdmissible := hL, K := ⟨K, hK⟩, m := 1, coupling := β, coupling_pos := hβ }
  have hD : GaugeFieldSpace.ExistsDenseLocalSequence
      (PeriodicLattice.meshSize L (K : ℤ)) := (hS d).2.2.2.1
  obtain ⟨F, hF, -⟩ := hD
  exact (hM L K hL hK F hF).2.2.2.2.2
theorem sequentialLimitCharacterization_holds (hM : WeakMetricStatement)
    (hS : GaugeFieldSpace.Statement) : SequentialLimitCharacterization := by
  intro L K hL hK β hβ ν
  have := metrizableSpace_realWeakState hM hS hL hK hβ
  refine ⟨⟨fun h => ?_, fun ⟨ℓ, ρ, h⟩ => isLimitOfLiftedMeasures_of_isLimitAlongSideSequence h⟩,
    exists_strictMono_sides_of_isLimitOfLiftedMeasures⟩
  obtain ⟨ℓ, ρ, h, -⟩ := exists_strictMono_sides_of_isLimitOfLiftedMeasures h
  exact ⟨ℓ, ρ, h⟩
end YangMills.Construction.InfiniteLattice.PeriodicExtensions.SequentialLimits
