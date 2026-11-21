import YangMills.Construction.InfiniteLattice.AlmostEveryConditionalMeasureIsErgodicUnderTheTranslations
import YangMills.Construction.InfiniteLattice.LimitPointsOfTheTorusMeasuresArePeriodicGibbsStates
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.OneInsertionOnTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheBoundsOnTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheLawOnTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheTotalDensitiesGiveASystem
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
open TestFunctions SystemsWithFiveBounds
open InfiniteLattice (localObsAbove periodicGibbsSet reflectionSeminorm smearedEnergyCumulant smearedEnergy timeConj)
open ChessboardTori (GridCell)
open ReflectionsAndOneInsertion (complexSmeared)
private theorem exists_pos_le_zpow_neg_two (y₂ : ℝ) :
    ∃ top : ℝ, 0 < top ∧ ∀ g ∈ Ioc 0 top, y₂ ≤ g ^ (-2 : ℤ) := by
  have hY : (0 : ℝ) < max 1 y₂ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hs : 0 < Real.sqrt (max 1 y₂) := Real.sqrt_pos.2 hY
  refine ⟨(Real.sqrt (max 1 y₂))⁻¹, inv_pos.2 hs, fun g hg => ?_⟩
  have hg0 : 0 < g := hg.1
  have h1 : g * Real.sqrt (max 1 y₂) ≤ 1 := by
    calc g * Real.sqrt (max 1 y₂) ≤ (Real.sqrt (max 1 y₂))⁻¹ * Real.sqrt (max 1 y₂) :=
          mul_le_mul_of_nonneg_right hg.2 hs.le
      _ = 1 := inv_mul_cancel₀ hs.ne'
  have h0 : 0 ≤ g * Real.sqrt (max 1 y₂) := by positivity
  have h2 : g ^ 2 * max 1 y₂ ≤ 1 := by
    have h3 : (g * Real.sqrt (max 1 y₂)) ^ 2 ≤ 1 := by nlinarith
    rwa [mul_pow, Real.sq_sqrt hY.le] at h3
  have hg2 : 0 < g ^ 2 := by positivity
  have h4 : max 1 y₂ ≤ (g ^ 2)⁻¹ := by
    rw [le_inv_comm₀ hY hg2]
    exact (le_div_iff₀ hY).2 (by simpa [one_div] using h2) |>.trans_eq (by simp [one_div])
  have h5 : g ^ (-2 : ℤ) = (g ^ 2)⁻¹ := by
    rw [zpow_neg]; norm_cast
  rw [h5]
  exact le_trans (le_max_right _ _) h4
private theorem sharpNormR4_nonneg (M : ℝ) (f : InfiniteLattice.AmbientSpace → ℝ) : 0 ≤ sharpNormR4 M f := by
  unfold sharpNormR4 uniformNorm
  exact le_trans (Real.iSup_nonneg fun x => norm_nonneg _) (le_max_left _ _)
private theorem factorial_mul_cumulant_le (Ccum R d : ℝ) (hC : 0 < Ccum) (hR : 0 < R) (hd : 0 < d) (n : ℕ) :
    (n.factorial : ℝ) * (Ccum * (1 + R) ^ 4 * ((n : ℝ) / min d 1) ^ 5) ^ n ≤
      (Real.exp 5 * Ccum * max 1 (d ^ (-((5 : ℕ) : ℤ))) * (1 + R) ^ 4) ^ n * (n.factorial : ℝ) ^ (6 : ℝ) := by
  have hX : (1 / min d 1) ^ 5 = max 1 (d ^ (-((5 : ℕ) : ℤ))) := by
    rcases le_total d 1 with h | h
    · have h1 : (1 : ℝ) ≤ d ^ (-((5 : ℕ) : ℤ)) := by
        rw [zpow_neg, zpow_natCast]
        exact (one_le_inv₀ (by positivity)).2 (pow_le_one₀ hd.le h)
      rw [min_eq_left h, max_eq_right h1, zpow_neg, zpow_natCast, one_div, inv_pow]
    · have h1 : d ^ (-((5 : ℕ) : ℤ)) ≤ 1 := by
        rw [zpow_neg, zpow_natCast]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ h)
      rw [min_eq_right h, max_eq_left h1]
      norm_num
  set X := max 1 (d ^ (-((5 : ℕ) : ℤ))) with hXdef
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hnn : ((n : ℝ) ^ n) ≤ Real.exp n * n.factorial := by
    have := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
    rwa [div_le_iff₀ hfac] at this
  have hbase : (n : ℝ) / min d 1 = n * (1 / min d 1) := by ring
  have hpow : (Ccum * (1 + R) ^ 4 * ((n : ℝ) / min d 1) ^ 5) ^ n =
      (Ccum * (1 + R) ^ 4 * X) ^ n * ((n : ℝ) ^ n) ^ 5 := by
    rw [hbase, mul_pow (n : ℝ), hX]
    rw [show Ccum * (1 + R) ^ 4 * ((n : ℝ) ^ 5 * X) = Ccum * (1 + R) ^ 4 * X * (n : ℝ) ^ 5 by ring, mul_pow,
      ← pow_mul, ← pow_mul, mul_comm 5 n]
  have hexp : Real.exp n ^ 5 = Real.exp 5 ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsix : (n.factorial : ℝ) ^ (6 : ℝ) = (n.factorial : ℝ) ^ 6 := by
    exact_mod_cast Real.rpow_natCast (n.factorial : ℝ) 6
  rw [hpow, hsix]
  calc (n.factorial : ℝ) * ((Ccum * (1 + R) ^ 4 * X) ^ n * ((n : ℝ) ^ n) ^ 5)
      ≤ (n.factorial : ℝ) * ((Ccum * (1 + R) ^ 4 * X) ^ n * (Real.exp n * n.factorial) ^ 5) := by
        gcongr
    _ = (Real.exp 5 * Ccum * X * (1 + R) ^ 4) ^ n * (n.factorial : ℝ) ^ 6 := by
        have e1 : Real.exp 5 * Ccum * X * (1 + R) ^ 4 = Real.exp 5 * (Ccum * (1 + R) ^ 4 * X) := by ring
        rw [e1, mul_pow (Real.exp 5), mul_pow (Real.exp n), hexp]
        generalize Ccum * (1 + R) ^ 4 * X = E
        ring
private def windowConstants (Ccum Ctr CI q d₀ : ℝ) (ηBar : ℝ → ℝ) (K₀ : ℝ → ℕ) : BoundConstants where
  aStar := Real.exp 5 * Ccum
  sepExponent := 5
  ballConst R := (1 + R) ^ 4
  factorialExponent := 6
  onePointConst R := Ctr * (1 + R) ^ 4
  insertionConst := CI
  insertionExponent := q
  insertionRadiusRatio := 1 / 4
  lawScale := d₀
  lawError := ηBar
  cutoffThreshold := K₀
private theorem windowConstants_admissible {Ccum Ctr CI q d₀ : ℝ} {ηBar : ℝ → ℝ} (K₀ : ℝ → ℕ) (hC : 0 < Ccum)
    (hT : 0 < Ctr) (hI : 0 ≤ CI) (hq : 0 ≤ q) (hd : WindowScaleModulus d₀ ηBar) :
    (windowConstants Ccum Ctr CI q d₀ ηBar K₀).Admissible where
  aStar_pos := mul_pos (Real.exp_pos 5) hC
  ballConst_pos R hR := by show 0 < (1 + R) ^ 4; positivity
  ballConst_monotoneOn R hR S hS h := by
    show (1 + R) ^ 4 ≤ (1 + S) ^ 4
    have : (0 : ℝ) < R := hR
    gcongr
  factorialExponent_nonneg := by show (0 : ℝ) ≤ 6; norm_num
  onePointConst_nonneg R hR := by show 0 ≤ Ctr * (1 + R) ^ 4; positivity
  onePointConst_monotoneOn R hR S hS h := by
    show Ctr * (1 + R) ^ 4 ≤ Ctr * (1 + S) ^ 4
    have : (0 : ℝ) < R := hR
    gcongr
  insertionConst_nonneg := hI
  insertionExponent_nonneg := hq
  insertionRadiusRatio_mem := by show (1 / 4 : ℝ) ∈ Ioc (0 : ℝ) (1 / 4); norm_num
  lawScale_mem := hd.scale_mem
  lawError_monotoneOn := hd.modulus_monotoneOn
  lawError_mem := hd.modulus_mem
  lawError_tendsto := hd.modulus_tendsto_zero
private structure HasFiveBoundsAt (ℓ : TorusLumps.StepParameters) (Bs M ϑ g : ℝ) (N : BoundConstants) : Prop where
  admissible : N.Admissible
  cumulant : ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePoint ℓ Bs g K β →
    ∀ ν ∈ periodicGibbsSet ℓ.side K β, ∀ n : ℕ, 2 ≤ n → ∀ R d : ℝ, 0 < R → 0 < d →
      ∀ f : Fin n → InfiniteLattice.AmbientSpace → ℝ, (∀ i, IsLipschitzFor euclidDistR4 (f i)) →
        (∀ i, ∃ x, tsupport (f i) ⊆ closedBallR4 x R) → HasSeparatedSupportsR4 f d →
          ‖smearedEnergyCumulant ν f‖ ≤ N.cumulantBound n d R * ∏ i, sharpNormR4 M (f i)
  onePoint : ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePoint ℓ Bs g K β →
    ∀ ν ∈ periodicGibbsSet ℓ.side K β, ∀ ν' ∈ periodicGibbsSet ℓ.side K β, ∀ R : ℝ, 0 < R →
      ∀ f : InfiniteLattice.AmbientSpace → ℝ, IsLipschitzFor euclidDistR4 f → (∃ x, tsupport f ⊆ closedBallR4 x R) →
        |(∫ U, smearedEnergy f U ∂ν) - ∫ U, smearedEnergy f U ∂ν'| ≤ N.onePointConst R * sharpNormR4 M f
  twoPointLaw : TwoPointLawOnWindowAt ℓ Bs g ϑ N.lawScale N.lawError N.cutoffThreshold
  insertion : ∀ (D : ChessboardTori.ChessboardSetup), D.L = ℓ.side → IsFirstPassagePoint ℓ Bs g D.K D.β →
    ∀ (c : GridCell D) (h : InfiniteLattice.AmbientSpace → ℝ), IsLipschitzFor euclidDistR4 h →
      tsupport h ⊆ closedBallR4 c.centre (N.insertionRadiusRatio * c.side) → c.side ≤ 1 →
      ∀ ρ ∈ periodicGibbsSet D.L D.K D.β, ∀ ν ∈ periodicGibbsSet D.L D.K D.β,
      ∀ P ∈ localObsAbove c.baseTime, ∀ Q ∈ localObsAbove c.baseTime,
        ‖∫ U, timeConj c.baseTime Q U *
            (complexSmeared D h U - ∫ V, complexSmeared D h V ∂ν) *
            (c.timeShift 1).actOn P U ∂ρ‖ ≤
          N.insertionConst * c.side ^ (-N.insertionExponent) * sharpNormR4 M h *
            reflectionSeminorm ρ c.baseTime Q * reflectionSeminorm ρ c.baseTime P
private theorem exists_hasFiveBoundsAt {ℓ : TorusLumps.StepParameters} {Bs M ϑ g Ccum Ctr CI q d₀ : ℝ}
    {ηBar : ℝ → ℝ} {K₀ : ℝ → ℕ} (hC : 0 < Ccum) (hT : 0 < Ctr) (hI : 0 ≤ CI) (hq : 0 ≤ q)
    (hd : WindowScaleModulus d₀ ηBar)
    (hb : WindowBounds ℓ Bs g Ccum Ctr M) (hl : TwoPointLawOnWindowAt ℓ Bs g ϑ d₀ ηBar K₀)
    (hi : WindowInsertionBound ℓ Bs g CI q M) :
    ∃ N : BoundConstants, HasFiveBoundsAt ℓ Bs M ϑ g N := by
  refine ⟨windowConstants Ccum Ctr CI q d₀ ηBar K₀, windowConstants_admissible K₀ hC hT hI hq hd, ?_, ?_, hl, hi⟩
  · intro K β hp ν hν n hn R d hR hd' f hf hs hsep
    refine (hb.cumulant_bound K β hp ν hν n hn R d hR hd' f hf hs hsep).trans ?_
    exact mul_le_mul_of_nonneg_right (factorial_mul_cumulant_le Ccum R d hC hR hd' n)
      (Finset.prod_nonneg fun i _ => sharpNormR4_nonneg M (f i))
  · exact hb.onePoint_diff
private theorem tendsto_pnat_val_atTop : Tendsto (fun K : ℕ+ => (K : ℕ)) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨⟨b + 1, Nat.succ_pos b⟩, fun a ha => by
    have h : b + 1 ≤ (a : ℕ) := ha
    omega⟩
private theorem coupling_pos_of_firstPassage {T : RenormalizationStepParameters.ParameterAssignment} {y Bs g β : ℝ} {K : ℕ}
    (hT : T.Admissible) (hBs : 2 * T.B ≤ Bs)
    (hg : 0 < g) (hp : IsFirstPassagePoint (T.stepParameters y) Bs g K β) : 0 < β := by
  have h1 : SequencePassage.passageThreshold Bs g ≤ β := hp.1
  have h2 : 0 < g ^ (-2 : ℤ) := zpow_pos hg _
  have h3 : 1 ≤ T.B := hT.B_ge
  unfold SequencePassage.passageThreshold at h1
  linarith
private theorem ergodicComponents_mem
    (hErg : LatticePhases.AlmostEveryConditionalIsErgodic)
    (D : LatticePhases.Setup) (ν : periodicGibbsSet D.L D.K D.β) :
    AEErgodicComponentsIn D ν (periodicGibbsSet D.L D.K D.β) := by
  intro κ hκ
  obtain ⟨h₁, h₂, h₃⟩ := hErg D ν κ hκ
  let μ : Measure (InfiniteLattice.GaugeField D.mesh) := ν.1
  have hp : IsProbabilityMeasure μ := ν.2.1.1
  have hn : μ (LatticePhases.ergodicConditionalLocus D κ)ᶜ = 0 :=
    (prob_compl_eq_zero_iff h₁.1).2 h₂
  have hae : ∀ᵐ U ∂ν.1, U ∈ LatticePhases.ergodicConditionalLocus D κ :=
    mem_ae_iff.2 hn
  exact hae.mono fun U hU => (h₃ U hU).1
private def flowSystem
    (hLim : InfiniteLattice.TorusWeakLimitsArePeriodicGibbs)
    (hErg : LatticePhases.AlmostEveryConditionalIsErgodic)
    (T : RenormalizationStepParameters.ParameterAssignment) (y Bs top M ϑ : ℝ) (hT : T.Admissible) (hM : 1 ≤ M)
    (hϑ : ϑ ∈ Ioc (0 : ℝ) 1) (hϑ₀ : ϑ ≤ TwoPoints.Shapes.shapeConst) (htop : 0 < top)
    (hBs : 2 * T.B ≤ Bs) (N : ℝ → BoundConstants)
    (hN : ∀ g ∈ Ioc 0 top, HasFiveBoundsAt (T.stepParameters y) Bs M ϑ g (N g))
    (hW : ∀ g ∈ Ioc 0 top, ∃ c₅ lam : ℝ, TotalDensitiesGiveASystem.PassageWindowData (T.stepParameters y) Bs c₅ lam g) :
    FiveBoundSystem where
  L := T.side
  admissibleL := ⟨hT.L_odd, le_trans (by norm_num) hT.L_ge⟩
  M := M
  one_le_M := hM
  ϑ := ϑ
  ϑ_mem := hϑ
  ϑ_le := hϑ₀
  top := top
  top_pos := htop
  IsPair g K β := IsFirstPassagePoint (T.stepParameters y) Bs g K β
  States L' K β := periodicGibbsSet L' K β
  consts := N
  consts_admissible g hg := (hN g hg).admissible
  β_pos g hg K β hp := coupling_pos_of_firstPassage hT hBs hg.1 hp
  states_subset _ _ _ _ _ := subset_rfl
  limits_mem g hg K β hp ν h :=
    (hLim T.side K ⟨hT.L_odd, le_trans (by norm_num) hT.L_ge⟩ K.pos β (coupling_pos_of_firstPassage hT hBs hg.1 hp)).2 h
  components_mem _ _ K β _ hβ ν _ :=
    ergodicComponents_mem hErg ⟨T.side, ⟨hT.L_odd, le_trans (by norm_num) hT.L_ge⟩, K, β, hβ⟩ ν
  infinite_cutoffs g hg := by
    obtain ⟨c₅, lam, hw⟩ := hW g hg
    intro hfin
    refine hw.infinite_cutoffs (((hfin.image fun K : ℕ+ => (K : ℕ)).union (finite_singleton 0)).subset ?_)
    intro K hK
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · exact Or.inr h0
    · exact Or.inl ⟨⟨K, hpos⟩, hK, rfl⟩
  asymptotic_freedom g hg := by
    obtain ⟨c₅, lam, hw⟩ := hW g hg
    obtain ⟨δ, hδ, h⟩ := hw.slope_tendsto
    exact ⟨fun K => δ K, hδ.comp tendsto_pnat_val_atTop, fun K β hp => h K β (PNat.pos K) hp⟩
  cumulant_bound g hg := (hN g hg).cumulant
  onePoint_bound g hg := (hN g hg).onePoint
  twoPoint_law g hg d hd K β hp hK ν hν f h hfh _ _ := (hN g hg).twoPointLaw d hd K β hp hK ν hν f h hfh
  insertion_bound g hg := (hN g hg).insertion
theorem systemFromTotalDensities_holds
    (hR : flowIsChainLaw) (hW : TotalDensitiesGiveASystem.passageWindowDataStatement)
    (hB : WindowBoundsExist.Statement) (hL : twoPointLawOnWindow)
    (hI : WindowInsertion.Statement) (hJ : expansionFlowEqTotalFlow)
    (hF : fourPointLawOnWindow) (hG : fourPointLawInLimits)
    (hLim : InfiniteLattice.TorusWeakLimitsArePeriodicGibbs)
    (hErg : LatticePhases.AlmostEveryConditionalIsErgodic) :
    SystemFromTotalDensities := by
  refine HoldsAtAdmissibleParameters.mono
    (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and
      (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and (HoldsAtAdmissibleParameters.and
        (HoldsAtAdmissibleParameters.and hR hW) hB) hL) hI) hJ) hF) hG) fun T y hT hA => ?_
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hy, hfit, hrun⟩, hWin⟩, hBd⟩, hLw⟩, hIn⟩, hJn⟩, hFn⟩, hGn⟩ := hA
  refine ⟨hy, hfit, hrun, fun Bs hBs => ?_⟩
  obtain ⟨c₅, hc, y₁, fW⟩ := hWin Bs hBs
  have hlam : 0 < 3 / 4 * (asymptoticFreedomSlope * Real.log T.side) := by
    have hL' : (1 : ℝ) < T.side := by
      have h : 2 ^ 40 ≤ T.side := hT.L_ge
      have h' : 1 < T.side := lt_of_lt_of_le (by norm_num) h
      exact_mod_cast h'
    have hlog := Real.log_pos hL'
    have hpi := Real.pi_pos
    unfold asymptoticFreedomSlope
    positivity
  obtain ⟨y₂, fB⟩ := hBd Bs hBs
  obtain ⟨y₃, fL⟩ := hLw Bs hBs
  obtain ⟨y₄, fI⟩ := hIn Bs hBs
  obtain ⟨y₅, fJ⟩ := hJn Bs hBs
  obtain ⟨y₆, fF⟩ := hFn Bs hBs
  obtain ⟨y₇, fG⟩ := hGn Bs hBs
  obtain ⟨top, htop, hfl⟩ :=
    exists_pos_le_zpow_neg_two (max y (max y₁ (max y₂ (max y₃ (max y₄ (max y₅ (max y₆ y₇)))))))
  have hall : ∀ g ∈ Ioc 0 top, y ≤ g ^ (-2 : ℤ) ∧ y₁ ≤ g ^ (-2 : ℤ) ∧ y₂ ≤ g ^ (-2 : ℤ) ∧ y₃ ≤ g ^ (-2 : ℤ) ∧
      y₄ ≤ g ^ (-2 : ℤ) ∧ y₅ ≤ g ^ (-2 : ℤ) ∧ y₆ ≤ g ^ (-2 : ℤ) ∧ y₇ ≤ g ^ (-2 : ℤ) := fun g hg => by
    simpa only [max_le_iff] using hfl g hg
  have f0 : ∀ g ∈ Ioc 0 top, y ≤ g ^ (-2 : ℤ) := fun g hg => (hall g hg).1
  have f1 : ∀ g ∈ Ioc 0 top, y₁ ≤ g ^ (-2 : ℤ) := fun g hg => (hall g hg).2.1
  have f2 : ∀ g ∈ Ioc 0 top, y₂ ≤ g ^ (-2 : ℤ) := fun g hg => (hall g hg).2.2.1
  have f3 : ∀ g ∈ Ioc 0 top, y₃ ≤ g ^ (-2 : ℤ) := fun g hg => (hall g hg).2.2.2.1
  have f4 : ∀ g ∈ Ioc 0 top, y₄ ≤ g ^ (-2 : ℤ) := fun g hg => (hall g hg).2.2.2.2.1
  have f5 : ∀ g ∈ Ioc 0 top, y₅ ≤ g ^ (-2 : ℤ) := fun g hg => (hall g hg).2.2.2.2.2.1
  have f6 : ∀ g ∈ Ioc 0 top, y₆ ≤ g ^ (-2 : ℤ) := fun g hg => (hall g hg).2.2.2.2.2.2.1
  have f7 : ∀ g ∈ Ioc 0 top, y₇ ≤ g ^ (-2 : ℤ) := fun g hg => (hall g hg).2.2.2.2.2.2.2
  refine ⟨c₅, _, top, hc, hlam, htop,
    fun g hg => ⟨f0 g hg, fW g hg.1 (f1 g hg), fJ g hg.1 (f5 g hg), fF g hg.1 (f6 g hg)⟩,
    fun m ϑ hϑ hϑ₀ => ?_⟩
  have hL1 : (1 : ℝ) < (T.side : ℝ) := by
    have h : 2 ^ 40 ≤ T.side := hT.L_ge
    have h' : 1 < T.side := lt_of_lt_of_le (by norm_num) h
    exact_mod_cast h'
  have hM : (1 : ℝ) ≤ (T.side : ℝ) ^ m := one_le_pow₀ hL1.le
  have hex : ∀ g, g ∈ Ioc 0 top →
      ∃ N : BoundConstants, HasFiveBoundsAt (T.stepParameters y) Bs ((T.side : ℝ) ^ m) ϑ g N := by
    intro g hg
    obtain ⟨Ccum, Ctr, hC, hCt, hb⟩ := fB g hg.1 (f2 g hg)
    obtain ⟨d₀, ηBar, K₀, hd, hl⟩ := fL g hg.1 (f3 g hg) ϑ hϑ
    obtain ⟨CI, q, hCI, hq, hi⟩ := fI g hg.1 (f4 g hg)
    exact exists_hasFiveBoundsAt hC hCt hCI hq hd (hb _ hM) hl (hi _ hM)
  have : Nonempty BoundConstants := ⟨windowConstants 0 0 0 0 0 id fun _ => 0⟩
  choose! N hN using hex
  refine ⟨flowSystem hLim hErg T y Bs top ((T.side : ℝ) ^ m) ϑ hT hM hϑ hϑ₀ htop hBs N hN
    (fun g hg => ⟨c₅, _, fW g hg.1 (f1 g hg)⟩),
    ⟨rfl, rfl, rfl, rfl, fun g hg K β => Iff.rfl, fun K β => rfl⟩, fun g hg => fG g hg.1 (f7 g hg)⟩
end YangMills.Construction.TotalDensities
end
