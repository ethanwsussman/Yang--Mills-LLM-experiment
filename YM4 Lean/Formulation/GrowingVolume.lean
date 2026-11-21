import Formulation.ReferenceCoupling
import YangMills.Construction.TheStatementsProvedTogether.FromTimeTranslationOfTheVectorsOfSmoothSequencesProof

set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section

namespace YangMills
open Construction Construction.PeriodicLattice Construction.InfiniteLattice
  Construction.GibbsAtFixedSpacing Formulation

/-- The volume tends to infinity at the stated lattice spacing and inverse coupling.
The same volumes give a weakly convergent sequence of periodic Wilson measures and
convergence of their local observables to those of the reflection-positive Gibbs state. -/
def HasThermodynamicLimit (L K : ℕ) (β : ℝ) : Prop :=
  ∃ (m : ℕ → ℕ) (ν : BorelProb (refinedSpacing L K)),
    SideExponentsTendToInfinity L m ∧ LiftedMeasuresTendstoWeakly L K β m ν ∧
    IsSymmetricReflPosGibbs L K β ν ∧ LocalQuantitiesTendsto L K β m ν

theorem su2_thermodynamic_limit_at_cutoff {L K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hK : 0 < K) {β : ℝ} (hβ : 0 < β) : HasThermodynamicLimit L K β := by
  obtain ⟨hcompact, hgibbs, hlocal, _⟩ :=
    TheStatementsProvedTogether.torus_state_infinite_volume_limit_points L hL K hK β hβ
  obtain ⟨ν, hν⟩ := hcompact.1
  have hs := hgibbs ν hν
  obtain ⟨m, ρ, hpos, htop, hρ, hw⟩ := hν
  exact ⟨m, ν, ⟨hpos, htop⟩, ⟨ρ, hρ, hw⟩, hs, hlocal m ν ⟨hpos, htop⟩ ⟨ρ, hρ, hw⟩⟩

/-- Every diverging sequence of tori has a volume subsequence giving all the same
fixed-cutoff conclusions for its limit. -/
theorem su2_thermodynamic_subsequence_at_cutoff {L K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hK : 0 < K) {β : ℝ} (hβ : 0 < β) (m : ℕ → ℕ) (hm : SideExponentsTendToInfinity L m) :
    ∃ (φ : ℕ → ℕ) (ν : BorelProb (refinedSpacing L K)),
      StrictMono φ ∧ LiftedMeasuresTendstoWeakly L K β (m ∘ φ) ν ∧
      IsSymmetricReflPosGibbs L K β ν ∧ LocalQuantitiesTendsto L K β (m ∘ φ) ν := by
  obtain ⟨hcompact, hgibbs, hlocal, _⟩ :=
    TheStatementsProvedTogether.torus_state_infinite_volume_limit_points L hL K hK β hβ
  obtain ⟨φ, ν, hφ, hw⟩ := hcompact.2.2 m hm
  have hside : SideExponentsTendToInfinity L (m ∘ φ) :=
    ⟨fun i => hm.1 (φ i), hm.2.comp hφ.tendsto_atTop⟩
  obtain ⟨ρ, heq, hlim⟩ := hw
  have hν : ν ∈ cubicTorusLimitStates L K β := ⟨m ∘ φ, ρ, hside.1, hside.2, heq, hlim⟩
  exact ⟨φ, ν, hφ, ⟨ρ, heq, hlim⟩, hgibbs ν hν, hlocal _ ν hside ⟨ρ, heq, hlim⟩⟩

/-- One reference torus selects all the couplings. At each such coupling, growing
volumes yield a reflection-positive infinite-lattice Gibbs state and convergence of
its local correlations. The bare couplings obey a uniform asymptotic upper bound. -/
theorem su2_fixed_observable_thermodynamic_limit :
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ (M : ℕ+) (K : ℕ → ℕ+) (δ : ℝ),
      8 ≤ torusSide L M ∧ StrictMono K ∧ 0 < δ ∧
      (∀ g₀ ∈ Ioo (0 : ℝ) δ,
        (∀ j, let g := renormalizedBareCoupling L M (K j) g₀
              IsLeast {t : ℝ | 0 < t ∧ referenceResponse L M (K j) (t ^ 2)⁻¹ = fixedPhysicalLevel g₀} g ∧
              HasThermodynamicLimit L (K j) (g ^ 2)⁻¹) ∧
        Tendsto (fun j => renormalizedBareCoupling L M (K j) g₀) atTop (𝓝 0)) ∧
      ∀ ε > 0, ∀ᶠ j in atTop, ∀ g₀ ∈ Ioo (0 : ℝ) δ,
        (renormalizedBareCoupling L M (K j) g₀) ^ 2 * (K j : ℝ) * Real.log L <
          3 * Real.pi ^ 2 / 11 + ε := by
  obtain ⟨L₀, hcoupling⟩ := su2_fixed_observable_coupling
  refine ⟨max L₀ 13, ?_⟩
  intro L hodd hL
  obtain ⟨M, K, δ, hM, hK, hδ, hmin, hupper⟩ := hcoupling L hodd ((le_max_left ..).trans hL)
  refine ⟨M, K, δ, hM, hK, hδ, ?_, hupper⟩
  intro g₀ hg₀
  obtain ⟨hselected, hzero⟩ := hmin g₀ hg₀
  refine ⟨?_, hzero⟩
  intro j
  have hg : 0 < renormalizedBareCoupling L M (K j) g₀ := (hselected j).1.1
  exact ⟨hselected j, su2_thermodynamic_limit_at_cutoff ⟨hodd, (le_max_right ..).trans hL⟩
    (K j).property (inv_pos.mpr (sq_pos_of_pos hg))⟩

open MeasureTheory

private theorem isInfiniteVolumeLimit_of_lifted {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (K : ℕ+) {β : ℝ} (hβ : 0 < β) {ν : BorelProb (refinedSpacing L K)} {m : ℕ → ℕ}
    (hm : SideExponentsTendToInfinity L m) (hw : LiftedMeasuresTendstoWeakly L K β m ν) :
    IsInfiniteVolumeLimit L K β ν.1 := by
  have hc := (TheStatementsProvedTogether.cutoff_covering_identifies_torus_measures
    ⟨⟨L, hL, K, 1⟩, β, hβ⟩).2.2.2
  have hs := (TheStatementsProvedTogether.periodicLift_clusterPt_seq_limit L K hL K.pos β hβ).2.1
  apply (Set.ext_iff.1 (hc.trans hs.symm) ν.1).2
  obtain ⟨ρ, hρ, hweak⟩ := hw
  refine ⟨ν.2, m, hm.1, hm.2, fun F hF => (hweak F hF).congr ?_⟩
  intro i
  change ∫ U, F U ∂(ρ i).1 = _
  rw [hρ i]

/-- All centered moments of bounded, compactly supported Borel tests converge along
the same thermodynamic subsequence at fixed spacing. Supports may overlap. -/
theorem su2_thermodynamic_centered_moments {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ+) {β : ℝ}
    {ν : BorelProb (refinedSpacing L K)} {m : ℕ → ℕ}
    (hw : LiftedMeasuresTendstoWeakly L K β m ν) {n : ℕ}
    (f : Fin n → AmbientSpace → ℝ) (hf : ∀ i, f i ∈ compactTestFunctions) :
    Tendsto (fun i => centeredMoment (liftedWilsonMeasure L (m i) K β) f) atTop
      (𝓝 (centeredMoment ν.1 f)) := by
  obtain ⟨ρ, hρ, hweak⟩ := hw
  have he (μ : BorelProb (refinedSpacing L K)) :
      centeredMoment μ.1 f = ursellPartitionSum μ.1 f :=
    (TheStatementsProvedTogether.gibbsState_centered_identity
      ⟨L, hL, K, 1⟩ μ.1 μ.2).2.2 n f hf
  rw [he ν]
  suffices h : Tendsto (fun i => ursellPartitionSum (ρ i).1 f) atTop (𝓝 (ursellPartitionSum ν.1 f)) by
    exact h.congr fun i => by rw [← he, hρ i]
  unfold ursellPartitionSum
  refine tendsto_finsetSum _ fun π hπ => tendsto_finsetProd _ fun J hJ => ?_
  have hJcard := (Finset.mem_filter.1 hπ).2 J hJ
  exact TheStatementsProvedTogether.cumulant_polynomial_in_moments_weak_limit.2.2.1 L K
    (CutoffLattice.spacingAt_pos hL K) ρ ν hweak J.card _ hJcard fun i => hf _

/-- The least coupling is selected on a fixed reference torus. At each cutoff the periodic
Wilson measures have an infinite-volume Gibbs limit. A single growing sequence of physical
tori approximates the corresponding infinite-volume connected correlations at every order. -/
theorem su2_fixed_observable_growing_volume :
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ (M : ℕ+) (K : ℕ+ → ℕ+) (δ : ℝ),
      8 ≤ torusSide L M ∧ StrictMono K ∧ 0 < δ ∧
      (∀ g₀ ∈ Ioo (0 : ℝ) δ,
        let g := fun j => renormalizedBareCoupling L M (K j) g₀
        let β := fun j => (g j ^ 2)⁻¹
        (∀ j, IsLeast {t : ℝ | 0 < t ∧ referenceResponse L M (K j) (t ^ 2)⁻¹ = fixedPhysicalLevel g₀}
          (g j)) ∧ Tendsto g atTop (𝓝 0) ∧
        ∃ (ν : ∀ j, BorelProb (refinedSpacing L (K j))) (m : ℕ+ → ℕ),
          (∀ j, IsInfiniteVolumeLimit L (K j) (β j) (ν j).1 ∧
            IsSymmetricReflPosGibbs L (K j) (β j) (ν j)) ∧
          Tendsto (fun j => torusSide L (m j)) atTop atTop ∧
          ∀ (n : ℕ), 2 ≤ n → ∀ X : TestSpaces.SepTupleOfCard n,
            (∀ᶠ j in atTop, SchwingerFunctions.IsR4TestFamily (torusSide L (m j)) X.1) ∧
            Tendsto (fun j => SchwingerFunctions.connectedSchwingerR4 L (m j) (K j) (β j) X.1 -
              smearedEnergyCumulant (ν j).1 X.1) atTop (𝓝 0)) ∧
      ∀ ε > 0, ∀ᶠ j in atTop, ∀ g₀ ∈ Ioo (0 : ℝ) δ,
        (renormalizedBareCoupling L M (K j) g₀) ^ 2 * (K j : ℝ) * Real.log L <
          3 * Real.pi ^ 2 / 11 + ε := by
  obtain ⟨L₀, h⟩ := su2_fixed_observable_thermodynamic_limit
  refine ⟨max L₀ 13, ?_⟩
  intro L hodd hL
  obtain ⟨M, K, δ, hM, hK, hδ, hcouple, hupper⟩ := h L hodd ((le_max_left ..).trans hL)
  have ha : Conventions.IsAdmissibleBlockingFactor L := ⟨hodd, (le_max_right ..).trans hL⟩
  refine ⟨M, fun j => K j.val, δ, hM, fun i j hij => hK hij, hδ, ?_, ?_⟩
  · intro g₀ h₀
    obtain ⟨hstate, hzero⟩ := hcouple g₀ h₀
    let g := fun j : ℕ+ => renormalizedBareCoupling L M (K j.val) g₀
    let β := fun j : ℕ+ => (g j ^ 2)⁻¹
    have hβ (j : ℕ+) : 0 < β j := inv_pos.mpr (sq_pos_of_pos (hstate j.val).1.1.1)
    choose t ν ht hw hsym _ using fun j : ℕ+ => (hstate j.val).2
    have hv (j : ℕ+) : IsInfiniteVolumeLimit L (K j.val) (β j) (ν j).1 :=
      isInfiniteVolumeLimit_of_lifted ha _ (hβ j) (ht j) (hw j)
    obtain ⟨m, _, hm, hlim⟩ := TheStatementsProvedTogether.infiniteVolume_limit_growing_tori
      L ha univ 0 (fun _ _ _ => mem_univ _) (fun j : ℕ+ => K j.val) β
      (fun j => (ν j).1) hβ hv
    exact ⟨fun j => (hstate j.val).1, hzero.comp tendsto_PNat_val_atTop_atTop,
      ν, m, fun j => ⟨hv j, hsym j⟩, hm, hlim⟩
  · exact fun ε hε => tendsto_PNat_val_atTop_atTop.eventually (hupper ε hε)

end YangMills
