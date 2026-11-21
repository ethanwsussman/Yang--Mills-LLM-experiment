import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.FinitenessOfATorusNormalisersAndExtendedMeasures
import YangMills.Construction.InfiniteLattice.LowerTangentsAtAConstantFunction
import YangMills.Construction.InfiniteLattice.SubgroupsOfFiniteIndexContainCubicLattices
import YangMills.Construction.InfiniteLattice.TorusInequalitiesPassToTheMeasuresOfAnInvariantClass
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped ComplexOrder Topology Matrix
noncomputable section
namespace YangMills.Construction
open NormalFamilies
namespace InfiniteLattice
namespace InvariantGibbsPeriodicBounds
def singleArray (Q : AddSubgroup (LatticePoint 1)) (hQ : Q.FiniteIndex) (f : GaugeField 1 → ℂ)
    (hf : f ∈ continuousLocalFunctions 1) (him : ∀ U, (f U).im = 0) : LocalObservableArray where
  sublattice := Q
  sublattice_finiteIndex := hQ
  size := 1
  one_le_size := le_rfl
  gen := fun _ => f
  gen_mem := fun _ => hf
  gen_im := fun _ => him
section SingleGenerator
variable (Q : AddSubgroup (LatticePoint 1)) (hQ : Q.FiniteIndex) (f : GaugeField 1 → ℂ)
  (hf : f ∈ continuousLocalFunctions 1) (him : ∀ U, (f U).im = 0) (Λ : PeriodSublattice 1)
theorem periodicSum_singleArray (U : Λ.QuotientField) :
    (singleArray Q hQ f hf him).periodicSum Λ U = Λ.cosetSumOfShifts Q f U :=
  finsum_comp_equiv (Equiv.prodUnique (Q ⧸ Λ.periods.addSubgroupOf Q) (Fin 1))
    (f := fun c : Q ⧸ Λ.periods.addSubgroupOf Q =>
      (Λ.periodize ((shift ((Quotient.out c : Q) : LatticePoint 1)).actOn f) U).re)
theorem tiltedPartition_singleArray_one (β : ℝ) :
    (singleArray Q hQ f hf him).tiltedPartition Λ β 1 =
      ∫ U, Real.exp (Λ.cosetSumOfShifts Q f U) * Λ.boltzmannWeight β U ∂Λ.quotientHaar := by
  unfold LocalObservableArray.tiltedPartition
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp only [LocalObservableArray.tiltedWeight, PeriodSublattice.boltzmannWeight,
    periodicSum_singleArray, one_mul, ← Real.exp_add]
  congr 1
  ring
theorem tiltedPartition_singleArray_zero (β : ℝ) :
    (singleArray Q hQ f hf him).tiltedPartition Λ β 0 =
      ∫ U, Λ.boltzmannWeight β U ∂Λ.quotientHaar := by
  unfold LocalObservableArray.tiltedPartition
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  simp only [LocalObservableArray.tiltedWeight, PeriodSublattice.boltzmannWeight, zero_mul,
    zero_sub, neg_mul]
theorem logTiltRatioPerSite_singleArray_nonpos
    (hP : FiniteTorusPartitionsAndLifts) {β : ℝ} (hβ : 0 < β)
    (hΛ : Λ.periods ≤ Q) (hineq : Λ.ExpShiftSumInequality β Q f) (E : OrthogonalNormalFrame)
    (L : Fin 4 → ℕ+) :
    (singleArray Q hQ f hf him).logTiltRatioPerSite Λ E L β 1 ≤ 0 := by
  have hZ₁ := ((hP β hβ Λ).2 (singleArray Q hQ f hf him) hΛ 1).1.tiltedPartition_pos
  have hZ₀ := ((hP β hβ Λ).2 (singleArray Q hQ f hf him) hΛ 0).1.tiltedPartition_pos
  have hle : (singleArray Q hQ f hf him).tiltedPartition Λ β 1 ≤
      (singleArray Q hQ f hf him).tiltedPartition Λ β 0 := by
    rw [tiltedPartition_singleArray_one, tiltedPartition_singleArray_zero]
    exact hineq
  have hlog : Real.log ((singleArray Q hQ f hf him).tiltedPartition Λ β 1 /
      (singleArray Q hQ f hf him).tiltedPartition Λ β 0) ≤ 0 :=
    Real.log_nonpos (div_nonneg hZ₁.le hZ₀.le) ((div_le_one hZ₀).2 hle)
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hlog
end SingleGenerator
theorem invIndex_mul_le_of_isLowerTangent {𝒜 : LocalObservableArray} {Λ : PeriodSublattice 1}
    {E : OrthogonalNormalFrame} {L : Fin 4 → ℕ+} {r : ℕ+} {A : GaugeField 1 → ℂ}
    {ν : Measure (GaugeField 1)} {β : ℝ}
    (h : 𝒜.IsLowerTangent Λ E L r A ν β 1) (hlog : 𝒜.logTiltRatioPerSite Λ E L β 1 ≤ 0) :
    𝒜.invIndex * (stateEval ν A).re ≤ LocalObservableArray.sideDefect L r A β 1 := by
  obtain ⟨h₁, h₂⟩ := h
  linarith
theorem sideDefect_const (L r : ℕ+) (A : GaugeField 1 → ℂ) (β : ℝ) :
    LocalObservableArray.sideDefect (fun _ => L) r A β 1 =
      (Constants.BoxTorus.tangentSideNumber : ℝ) * (β + observableSupNorm A) * ((r : ℕ) : ℝ) ^ 5 *
        4 / ((L : ℕ) : ℝ) := by
  have hL : (((L : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast L.ne_zero
  simp only [LocalObservableArray.sideDefect, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, abs_one, one_mul, nsmul_eq_mul]
  field_simp
  norm_num
def standardFrame : OrthogonalNormalFrame where
  vec := PeriodicLattice.coordVec
  isNormal := fun i => Or.inl ⟨i, rfl⟩
  pairwise_orthogonal := fun i j h => by
    simp [PeriodicLattice.coordVec, Pi.single_eq_of_ne h.symm]
theorem dual_standardFrame (i : Fin 4) :
    standardFrame.dual i = PeriodicLattice.coordVec i := by
  change NormalFamilies.dualVector (PeriodicLattice.coordVec i) = _
  simp [NormalFamilies.dualVector, normSq_eq_dotProduct, PeriodicLattice.coordVec]
theorem sum_smul_sideVec_apply (k : Fin 4 → ℤ) (L : ℕ+) (μ : Fin 4) :
    (∑ i, (k i : ℝ) • standardFrame.sideVec (fun _ => L) i) μ =
      (k μ : ℝ) * ((L : ℕ) : ℝ) := by
  simp [OrthogonalNormalFrame.sideVec, dual_standardFrame, PeriodicLattice.coordVec,
    Finset.sum_apply, Pi.single_apply]
theorem mem_cubicSublattice_iff {x : LatticePoint 1} {c : ℝ} :
    x ∈ cubicSublattice 1 c ↔ (x : AmbientSpace) ∈ latticeSubgroup c :=
  AddSubgroup.mem_addSubgroupOf
theorem isBoxShaped_standardFrame (Λ : PeriodSublattice 1) (L : ℕ+)
    (hΛ : Λ.periods = cubicSublattice 1 ((L : ℕ) : ℝ)) :
    Λ.IsBoxShaped standardFrame (fun _ => L) := by
  constructor
  · ext v
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      have hγ' : γ ∈ Λ.periods := hγ
      rw [hΛ, mem_cubicSublattice_iff] at hγ'
      obtain ⟨n, hn⟩ := hγ'
      exact ⟨n, funext fun μ => by rw [sum_smul_sideVec_apply]; exact hn μ⟩
    · rintro ⟨k, rfl⟩
      have h₁ : (∑ i, (k i : ℝ) • standardFrame.sideVec (fun _ => L) i) ∈ latticeSubgroup 1 :=
        ⟨fun μ => k μ * ((L : ℕ) : ℤ), fun μ => by rw [sum_smul_sideVec_apply]; push_cast; ring⟩
      refine ⟨⟨_, h₁⟩, ?_, rfl⟩
      change (⟨_, h₁⟩ : LatticePoint 1) ∈ Λ.periods
      rw [hΛ, mem_cubicSublattice_iff]
      exact ⟨k, fun μ => sum_smul_sideVec_apply k L μ⟩
  · intro i
    refine ⟨Pi.single i ((L : ℕ) : ℤ), fun μ => ?_⟩
    by_cases h : μ = i
    · subst h
      simp [OrthogonalNormalFrame.sideVec, dual_standardFrame, PeriodicLattice.coordVec]
    · simp [OrthogonalNormalFrame.sideVec, dual_standardFrame, PeriodicLattice.coordVec,
        Pi.single_eq_of_ne h]
theorem le_norm_of_mem_cubicSublattice (Λ : PeriodSublattice 1) (L : ℕ)
    (hΛ : Λ.periods = cubicSublattice 1 (L : ℝ)) {γ : LatticePoint 1} (hγ : γ ∈ Λ.periods)
    (h0 : γ ≠ 0) :
    (L : ℝ) ≤ ‖(γ : AmbientSpace)‖ := by
  rw [hΛ, mem_cubicSublattice_iff] at hγ
  obtain ⟨n, hn⟩ := hγ
  have hne : ∃ μ, n μ ≠ 0 := by
    by_contra hall
    have hall' : ∀ μ, n μ = 0 := fun μ => by_contra fun h => hall ⟨μ, h⟩
    exact h0 (Subtype.ext (funext fun μ => by simp [hn μ, hall' μ]))
  obtain ⟨μ, hμ⟩ := hne
  have h₁ : (1 : ℝ) ≤ |(n μ : ℝ)| := by exact_mod_cast Int.one_le_abs hμ
  calc (L : ℝ) = 1 * (L : ℝ) := (one_mul _).symm
    _ ≤ |(n μ : ℝ)| * (L : ℝ) := by gcongr
    _ = ‖(γ : AmbientSpace) μ‖ := by
        rw [hn μ, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    _ ≤ ‖(γ : AmbientSpace)‖ := norm_le_pi_norm _ μ
theorem exists_siteCube {S : Set (Link 1)} (hS : S.Finite) :
    ∃ (a : LatticePoint 1) (r : ℕ+),
      LinksLieIn S ((fun x : LatticePoint 1 => (x : AmbientSpace)) '' siteCube a r) := by
  obtain ⟨B, hB⟩ :=
    (hS.image fun b => max ‖(b.initial : AmbientSpace)‖ ‖(b.terminal : AmbientSpace)‖).bddAbove
  obtain ⟨R, hR⟩ := exists_nat_ge B
  let a : LatticePoint 1 := ⟨fun _ => -(R : ℝ), fun _ => -(R : ℤ), fun _ => by simp⟩
  have hsite : ∀ x : LatticePoint 1, ‖(x : AmbientSpace)‖ ≤ R →
      x ∈ siteCube a (Nat.succPNat (2 * R)) := by
    intro x hx
    obtain ⟨n, hn⟩ := x.2
    have hbound : ∀ μ, |n μ| ≤ (R : ℤ) := fun μ => by
      have h₁ : |(x : AmbientSpace) μ| ≤ R := by
        have := norm_le_pi_norm (x : AmbientSpace) μ
        rw [Real.norm_eq_abs] at this
        exact this.trans hx
      rw [hn μ, mul_one] at h₁
      exact_mod_cast h₁
    refine ⟨fun μ => (n μ + R).toNat, fun μ => ?_, fun μ => ?_⟩
    · have := abs_le.mp (hbound μ)
      simp only [Nat.succPNat_coe]
      omega
    · have := abs_le.mp (hbound μ)
      have hk : (((n μ + R).toNat : ℤ)) = n μ + R := Int.toNat_of_nonneg (by omega)
      have hk' : (((n μ + R).toNat : ℕ) : ℝ) = (n μ : ℝ) + R := by exact_mod_cast hk
      rw [hk', hn μ]
      simp [a]
  refine ⟨a, Nat.succPNat (2 * R), fun b hb => ?_⟩
  have hmax : max ‖(b.initial : AmbientSpace)‖ ‖(b.terminal : AmbientSpace)‖ ≤ R :=
    (hB (Set.mem_image_of_mem _ hb)).trans hR
  exact ⟨⟨b.initial, hsite _ ((le_max_left _ _).trans hmax), rfl⟩,
    ⟨b.terminal, hsite _ ((le_max_right _ _).trans hmax), rfl⟩⟩
end InvariantGibbsPeriodicBounds
open InvariantGibbsPeriodicBounds in
theorem PeriodicBoundsPassToInvariantGibbs.holds
    (hT : InvariantGibbsLowerTangent.InvariantGibbsLowerTangentClaim)
    (hC : ConstantTangents.ConstantLowerTangentClaim)
    (hP : FiniteTorusPartitionsAndLifts)
    (hS : FiniteIndexSubgroupsContainCubicSublattices)
    (hE : ElementaryLatticeFacts) :
    PeriodicBoundsPassToInvariantGibbs := by
  rintro β hβ f hf him Q hQ ⟨L₀, hL₀, hI⟩ ν hν
  have hνP : IsProbabilityMeasure ν := hν.1.1
  have himint : (∫ U, f U ∂ν).im = 0 := by
    have h₁ : (fun U => f U) = fun U => (((f U).re : ℝ) : ℂ) :=
      funext fun U => Complex.ext (by simp) (by simp [him U])
    rw [h₁, integral_complex_ofReal]
    simp
  suffices hx : (∫ U, f U ∂ν).re ≤ 0 from
    Complex.le_def.2 ⟨by simpa using hx, by simpa using himint⟩
  have hfin : (observableSupport f).Finite :=
    ((hE 1 β one_pos hβ).2.2.2.1.2.2.2.2.2.2.2 f hf.1 hf.2.1).2.2.1
  obtain ⟨a, r, hcube⟩ := exists_siteCube hfin
  have step : ∀ L : ℕ+, L₀ ≤ (L : ℕ) → (r : ℕ) + 1 < (L : ℕ) → Q.index ∣ (L : ℕ) →
      (singleArray Q hQ f hf him).invIndex * (∫ U, f U ∂ν).re ≤
        (Constants.BoxTorus.tangentSideNumber : ℝ) * (β + observableSupNorm f) *
          ((r : ℕ) : ℝ) ^ 5 * 4 / ((L : ℕ) : ℝ) := by
    intro L hL₁ hL₂ hdvd
    obtain ⟨-, Λ, hΛ, hΛQ⟩ := hS Q hQ (L : ℕ) (by omega) hdvd
    have hineq : Λ.ExpShiftSumInequality β Q f :=
      hI (L : ℕ) hL₁ (hΛ ▸ hΛQ) Λ hΛ
    have hbox := isBoxShaped_standardFrame Λ L hΛ
    have hlog := logTiltRatioPerSite_singleArray_nonpos Q hQ f hf him Λ hP hβ hΛQ hineq
      standardFrame (fun _ => L)
    have htan : (singleArray Q hQ f hf him).IsLowerTangent Λ standardFrame (fun _ => L) r f ν
        β 1 := by
      by_cases hconst : ∃ c : ℂ, ∀ U, f U = c
      · obtain ⟨c, hc⟩ := hconst
        obtain ⟨U₀⟩ : Nonempty (GaugeField 1) := nonempty_of_isProbabilityMeasure ν
        have hcim : c.im = 0 := by rw [← hc U₀]; exact him U₀
        have hfc : f = fun _ => ((c.re : ℝ) : ℂ) :=
          funext fun U => by rw [hc U]; exact Complex.ext (by simp) (by simp [hcim])
        have hsingle : (singleArray Q hQ f hf him).IsSingleGenerated
            (fun _ => ((c.re : ℝ) : ℂ)) := ⟨rfl, fun _ => hfc⟩
        have hholds := hC standardFrame (fun _ => L) Λ hbox (singleArray Q hQ f hf him) hΛQ c.re
          hsingle β hβ 1
        have := hholds.2.2.2.2.1 ν r hνP
        rwa [← hfc] at this
      · let d : BoxTorusComparisonData :=
          { obs := f
            obs_mem := hf
            obs_im := him
            obs_nonconst := hconst
            boxWidth := r
            obsAnchor := a
            obs_support := hcube
            normalFrame := standardFrame
            sideLengths := fun _ => L
            periodSublattice := Λ
            periodSublattice_isBoxShaped := hbox
            no_short_period := fun γ hγ h0 => by
              have h₁ := le_norm_of_mem_cubicSublattice Λ (L : ℕ) hΛ hγ h0
              have h₂ : (((r : ℕ) + 1 : ℕ) : ℝ) < ((L : ℕ) : ℝ) := by exact_mod_cast hL₂
              push_cast at h₂
              linarith
            translationGroup := Q
            periods_le_translationGroup := hΛQ
            translationGroup_finiteIndex := hQ }
        exact hT d β hβ ν hν 1
    have := invIndex_mul_le_of_isLowerTangent htan hlog
    rwa [sideDefect_const] at this
  have hk : 0 < Q.index := Nat.pos_of_ne_zero hQ.index_ne_zero
  set C : ℝ := (Constants.BoxTorus.tangentSideNumber : ℝ) * (β + observableSupNorm f) *
    ((r : ℕ) : ℝ) ^ 5 * 4 with hC'
  set M : ℕ := L₀ + (r : ℕ) + 2 with hM
  have hlim : Tendsto (fun m : ℕ => C / ((Q.index * (M + m) : ℕ) : ℝ)) atTop (𝓝 0) := by
    refine (tendsto_const_div_atTop_nhds_zero_nat C).comp
      (tendsto_atTop_mono (fun m => ?_) tendsto_id)
    change m ≤ Q.index * (M + m)
    nlinarith [Nat.zero_le M, Nat.zero_le m]
  have hle : ∀ m : ℕ, (singleArray Q hQ f hf him).invIndex * (∫ U, f U ∂ν).re ≤
      C / ((Q.index * (M + m) : ℕ) : ℝ) := by
    intro m
    have hpos : 0 < Q.index * (M + m) := Nat.mul_pos hk (by omega)
    have hge : M + m ≤ Q.index * (M + m) := Nat.le_mul_of_pos_left _ hk
    exact step ⟨Q.index * (M + m), hpos⟩ (by simp only [PNat.mk_coe]; omega)
      (by simp only [PNat.mk_coe]; omega) (by simp only [PNat.mk_coe]; exact dvd_mul_right _ _)
  have hκ : 0 < (singleArray Q hQ f hf him).invIndex := by
    change 0 < ((Q.index : ℝ))⁻¹
    exact inv_pos.mpr (by exact_mod_cast hk)
  have hfinal := ge_of_tendsto' hlim hle
  exact nonpos_of_mul_nonpos_right hfinal hκ
end InfiniteLattice
end YangMills.Construction
