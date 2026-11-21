import Formulation.ContinuumLimit
import Formulation.GrowingVolume
import YangMills.Construction.BoundsOnEverySide.MovingTuplesOfALimitAlongStatesProof
import YangMills.Construction.Continuum.CentredMomentsOfTheCumulantsAndOfTheirLimitsProof
import YangMills.Construction.TheStatementsProvedTogether.FromResponseLessTheActionReturnsProof

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace YangMills
open Construction

private theorem succPNat_tendsto_atTop : Tendsto Nat.succPNat atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ h => Nat.succ_le_succ h)
    (fun b => ⟨b.val, Nat.le_succ _⟩)

/-- A uniform separated-test bound in the infinite-volume Gibbs states at the
fixed-observable couplings gives simultaneous cutoff convergence of their
connected correlations and centered moments on ℝ⁴. -/
theorem su2_fixed_observable_cutoff_limit_of_bound
    {L M : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (g₀ : ℝ)
    (K : ℕ → ℕ+) (hK : StrictMono K)
    (ν : ∀ j, Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K j : ℤ))))
    (hν : ∀ j, ν j ∈ InfiniteLattice.periodicGibbsSet L (K j)
      ((renormalizedBareCoupling L M (K j) g₀) ^ 2)⁻¹)
    (P : ℝ) (hP : 1 ≤ P) (C : ℕ → ℝ → ℝ → ℝ)
    (hbound : ∀ j n, 2 ≤ n → ∀ R δ : ℝ, 0 < R → 0 < δ →
      ∀ X : TestSpaces.SepTupleOfCard n, SeparatedBound.SupportedSeparated R δ X →
        ‖InfiniteLattice.smearedEnergyCumulant (ν j) X.1‖ ≤ C n δ R * SeparatedBound.sharpNormProd P X) :
    ∃ (φ : ℕ → ℕ) (S : (n : ℕ) → 2 ≤ n → TestSpaces.SepTupleOfCard n → ℝ),
      StrictMono φ ∧ Tendsto (fun j => (K (φ j) : ℕ)) atTop atTop ∧
      (∀ n hn (X : TestSpaces.SepTupleOfCard n),
        Tendsto (fun j => InfiniteLattice.smearedEnergyCumulant (ν (φ j)) X.1) atTop
          (𝓝 (S n hn X : ℂ))) ∧
      (∀ n (X : TestSpaces.SepTupleOfCard n),
        Tendsto (fun j => InfiniteLattice.centeredMoment (ν (φ j)) X.1) atTop
          (𝓝 (TestSpaces.centredOfCumulants S ⟨n, X⟩ : ℂ))) := by
  let s : Conventions.StandingParameters := ⟨L, hL, 1, 1⟩
  let Q : BoundsOnEverySide.GibbsStateSequence L :=
    ⟨fun j => K j, fun j => ((renormalizedBareCoupling L M (K j) g₀) ^ 2)⁻¹,
      fun j => ν j, fun j => hν j⟩
  obtain ⟨ψ, T, hT⟩ := TheStatementsProvedTogether.exists_separated_subseq_limit
    L hL P hP Q C (fun j => hbound j) s
  let φ (j : ℕ) : ℕ := ψ (Nat.succPNat j)
  have hφ : StrictMono φ := fun _ _ hij => hT.strictMono (Nat.succ_lt_succ hij)
  have hs := succPNat_tendsto_atTop
  let S := LimitGrowthFromCutoffBound.restrictToTestTuples T
  refine ⟨φ, S, hφ, (show StrictMono (fun j => (K (φ j) : ℕ)) from
    fun _ _ hij => hK (hφ hij)).tendsto_atTop, ?_, ?_⟩
  · intro n hn X
    exact (hT.tendsto n hn ⟨X.1, (AmbientPoints.mem_separatedTuples_r4_iff X.1).2 X.2⟩).comp hs
  · intro n X
    let f : AmbientPoints.separatedTuples s .euclidean n :=
      ⟨X.1, (AmbientPoints.mem_separatedTuples_r4_iff X.1).2 X.2⟩
    have hsum := CumulantLimits.CentredMoments.tendsto_sum_singletonFree T
      (fun j n u => InfiniteLattice.smearedEnergyCumulant (Q.gibbs (ψ j)) u) hT.tendsto f
    have he : CumulantLimits.moments T (AmbientPoints.toAllSeparated f) =
        TestSpaces.centredOfCumulants S ⟨n, X⟩ :=
      AmbientPoints.centredOfMaps_r4 T S (fun _ _ _ => rfl) f
    rw [← he]
    apply (hsum.comp hs).congr
    intro j
    let p : Conventions.StandingParameters := ⟨L, hL, K (φ j), 1⟩
    have hid := (TheStatementsProvedTogether.gibbsState_centered_identity
      p (ν (φ j)) (hν (φ j)).1.1).2.2 n f.1
      (CumulantLimits.CentredMoments.apply_mem_compactTestFunctions f.2)
    exact (hid.trans (CumulantLimits.CentredMoments.ursellPartitionSum_eq_sum _ _)).symm

private theorem reflection_positive_of_infinite_moments
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (K : ℕ → ℕ+) (hK : Tendsto (fun j => (K j : ℕ)) atTop atTop)
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j)
    (ν : ∀ j, Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize L (K j : ℤ))))
    (hν : ∀ j, ν j ∈ InfiniteLattice.periodicGibbsSet L (K j) (β j))
    (S : LimitTheorem.CumulantFamily)
    (hm : ∀ n (X : TestSpaces.SepTupleOfCard n),
        Tendsto (fun j => InfiniteLattice.centeredMoment (ν j) X.1) atTop
          (𝓝 (TestSpaces.centredOfCumulants S ⟨n, X⟩ : ℂ))) :
    HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm
      (LimitTheorem.centredOf S)) := by
  let s : Conventions.StandingParameters := ⟨L, hL, 1, 1⟩
  let k (j : ℕ) := (K j : ℕ)
  let σ (X : R4TupleForms.FinTuple s) := LimitTheorem.centredOf S (R4TupleForms.finTupleEquiv s X)
  have hp : StateLimits.IsPointwiseLimit (s := s) k ν ν σ := by
    intro X
    let f : TestSpaces.SepTupleOfCard X.1.1 :=
      ⟨X.1.2, (AmbientPoints.mem_separatedTuples_r4_iff (s := s) X.1.2).1 X.2⟩
    have he : R4TupleForms.finTupleEquiv s X = TupleLists.toList ⟨X.1.1, f⟩ := Subtype.ext rfl
    have hσ : σ X = TestSpaces.centredOfCumulants S ⟨X.1.1, f⟩ := by
      simp [σ, he, LimitTheorem.centredOf, TupleLists.ofList_toList]
    rw [hσ]
    have hv (j : ℕ) : InfiniteLattice.centeredMoment (ν j) f.1 =
        ((StateLimits.pairedValue (s := s) k ν ν j X : ℝ) : ℂ) := by
      simp only [InfiniteLattice.centeredMoment, Probability.complexExpectation, StateLimits.pairedValue,
        StateLimits.centeredProduct, integral_complex_ofReal, ← Complex.ofReal_sub, ← Complex.ofReal_prod, f]
      rfl
    have ht := (Complex.continuous_re.tendsto _).comp (hm X.1.1 f)
    simpa only [Function.comp_def, hv, Complex.ofReal_re] using ht
  have hseq : StateLimits.IsPeriodicGibbsSeq (s := s) k β ν ν := ⟨hK, hν, hν⟩
  have hfunc := ((TheStatementsProvedTogether.state_maps_limits_separated.1
    s k β ν ν (fun j => (K j).pos) hseq).2 σ ⟨fun j => (K j).pos, hseq, hp⟩).1.1
  have hpos := BoundsOnEverySide.TranslatedTuples.isPosSemidef_of_limit hfunc hβ
    (by have := hL.2; change 2 ≤ L; omega) hK (fun j => (K j).pos) hν hν
    (fun j => (BoundsOnEverySide.TranslatedTuples.periodicGibbs_facts
      TheStatementsProvedTogether.periodic_gibbs_states_all_spacings_couplings hL (K j).pos (hβ j) (hν j)).2.2)
    TheStatementsProvedTogether.cutoff_representative_centered_product
    TheStatementsProvedTogether.gibbsState_centered_identity TheStatementsProvedTogether.reflection_form_nonneg_le_sup
    TheStatementsProvedTogether.translates_of_positive_combinations hp
  have he : R4TupleForms.toTupleFunctional σ hfunc = LimitTheorem.centredOf S := by
    rw [R4TupleForms.toTupleFunctional, LimitTheorem.centredOf, SeparatedTuples.TupleFunctional.mk.injEq]
    funext X
    change LimitTheorem.centredOf S (R4TupleForms.finTupleEquiv s ((R4TupleForms.finTupleEquiv s).symm X)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rwa [he] at hpos

/-- The reference coupling and thermodynamic states exist unconditionally.
If these states satisfy a cutoff-uniform bound, their correlations and those
on the same growing physical tori converge to a common continuum family. Its
centered moments are reflection-positive on separated positive-time test tuples. -/
theorem su2_fixed_observable_joint_limit_of_bound :
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → ∃ (M : ℕ+) (K : ℕ+ → ℕ+) (δ : ℝ),
      8 ≤ PeriodicLattice.torusSide L M ∧ StrictMono K ∧ 0 < δ ∧
      (∀ ε > 0, ∀ᶠ j in atTop, ∀ g₀ ∈ Set.Ioo (0 : ℝ) δ,
        (renormalizedBareCoupling L M (K j) g₀) ^ 2 * (K j : ℝ) * Real.log L <
          3 * Real.pi ^ 2 / 11 + ε) ∧
      ∀ g₀ ∈ Set.Ioo (0 : ℝ) δ,
        let g := fun j => renormalizedBareCoupling L M (K j) g₀
        let β := fun j => (g j ^ 2)⁻¹
        (∀ j, IsLeast {t : ℝ | 0 < t ∧ referenceResponse L M (K j) (t ^ 2)⁻¹ =
          fixedPhysicalLevel g₀} (g j)) ∧ Tendsto g atTop (𝓝 0) ∧
        ∃ (ν : ∀ j, GibbsAtFixedSpacing.BorelProb (InfiniteLattice.refinedSpacing L (K j)))
          (m : ℕ+ → ℕ),
          (∀ j, InfiniteLattice.IsInfiniteVolumeLimit L (K j) (β j) (ν j).1 ∧
            InfiniteLattice.IsSymmetricReflPosGibbs L (K j) (β j) (ν j)) ∧
          Tendsto (fun j => PeriodicLattice.torusSide L (m j)) atTop atTop ∧
          ∀ (P : ℝ), 1 ≤ P → ∀ (C : ℕ → ℝ → ℝ → ℝ),
            (∀ j n, 2 ≤ n → ∀ R d : ℝ, 0 < R → 0 < d →
              ∀ X : TestSpaces.SepTupleOfCard n, SeparatedBound.SupportedSeparated R d X →
                ‖InfiniteLattice.smearedEnergyCumulant (ν j).1 X.1‖ ≤ C n d R * SeparatedBound.sharpNormProd P X) →
            ∃ (φ : ℕ → ℕ+) (S : LimitTheorem.CumulantFamily), StrictMono φ ∧
              (∀ n hn (X : TestSpaces.SepTupleOfCard n), let z : ℂ := S n hn X
                Tendsto (fun j => (InfiniteLattice.smearedEnergyCumulant (ν (φ j)).1 X.1,
                  SchwingerFunctions.connectedSchwingerR4 L (m (φ j)) (K (φ j)) (β (φ j)) X.1))
                  atTop (𝓝 (z, z))) ∧
              (∀ n (X : TestSpaces.SepTupleOfCard n), let z : ℂ := TestSpaces.centredOfCumulants S ⟨n, X⟩
                Tendsto (fun j => (InfiniteLattice.centeredMoment (ν (φ j)).1 X.1,
                  su2_centeredMoment L (m (φ j)) (K (φ j)) (β (φ j)) X)) atTop (𝓝 (z, z))) ∧
              HilbertSpaceBasics.IsPosSemidef
                (ReflectionPositivity.TupleForm.reflectionForm (LimitTheorem.centredOf S)) := by
  obtain ⟨L₀, h⟩ := su2_fixed_observable_growing_volume
  refine ⟨max L₀ 13, ?_⟩
  intro L hodd hlarge
  obtain ⟨M, K, δ, hM, hK, hδ, hroot, hupper⟩ := h L hodd ((le_max_left ..).trans hlarge)
  have hL : Conventions.IsAdmissibleBlockingFactor L := ⟨hodd, (le_max_right ..).trans hlarge⟩
  refine ⟨M, K, δ, hM, hK, hδ, hupper, ?_⟩
  intro g₀ hg₀
  obtain ⟨hmin, hzero, ν, m, hstate, hside, hnear⟩ := hroot g₀ hg₀
  let β (j : ℕ+) := ((renormalizedBareCoupling L M (K j) g₀) ^ 2)⁻¹
  refine ⟨hmin, hzero, ν, m, hstate, hside, ?_⟩
  intro P hP C hbound
  obtain ⟨ψ, S, hψ, hcut, hc, hm⟩ := su2_fixed_observable_cutoff_limit_of_bound hL g₀
    (fun j => K j.succPNat) (fun _ _ hij => hK (Nat.succ_lt_succ hij))
    (fun j => (ν j.succPNat).1) (fun j => (hstate j.succPNat).2.2.2.2.2.2.1)
    P hP C (fun j => hbound j.succPNat)
  let φ (j : ℕ) := (ψ j).succPNat
  have hφ : Tendsto φ atTop atTop := succPNat_tendsto_atTop.comp hψ.tendsto_atTop
  have htor n hn (X : TestSpaces.SepTupleOfCard n) :
      Tendsto (fun j => SchwingerFunctions.connectedSchwingerR4 L (m (φ j)) (K (φ j)) (β (φ j)) X.1)
        atTop (𝓝 (S n hn X : ℂ)) := by
    simpa [φ, β, Function.comp_def] using (((hnear n hn X).2.comp hφ).add (hc n hn X))
  have hmpos : ∀ᶠ j in atTop, 0 < m (φ j) := by
    filter_upwards [(hside.comp hφ).eventually_gt_atTop 2] with j hj
    by_contra! he
    have h0 : m (φ j) = 0 := Nat.eq_zero_of_le_zero he
    change 2 < PeriodicLattice.torusSide L (m (φ j)) at hj
    simp [h0, PeriodicLattice.torusSide] at hj
  have hβ (j : ℕ) : 0 < β (φ j) := inv_pos.mpr (sq_pos_of_pos (hmin (φ j)).1.1)
  exact ⟨φ, S, fun _ _ hij => Nat.succ_lt_succ (hψ hij),
    fun n hn X => (hc n hn X).prodMk_nhds (htor n hn X),
    fun n X => (hm n X).prodMk_nhds (su2_moments_tendsto hL hmpos (Eventually.of_forall hβ) htor n X),
    reflection_positive_of_infinite_moments hL (K ∘ φ) hcut (β ∘ φ) hβ
      (fun j => (ν (φ j)).1) (fun j => (hstate (φ j)).2.2.2.2.2.2.1) S hm⟩

end YangMills
