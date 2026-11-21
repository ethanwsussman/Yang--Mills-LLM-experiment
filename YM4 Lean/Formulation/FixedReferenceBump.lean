import YangMills.Construction.TheStatementsProvedTogether.FromTheTopOfTheTrajectoryProof
import YangMills.Construction.QuaternionicWilsonModel.TheClassesHaveMembersAtEveryScaleProof
import YangMills.Construction.TheStatementsProvedTogether.FromMeansAtABondProof
import YangMills.Construction.TheStatementsProvedTogether.FromHeatSumOnALatticeProof
import YangMills.Construction.Torus.GeometryTransportLiftAndDilationOfTestPairsProof

/-! A fixed translated pair on one reference torus has uniformly positive covariance along a sequence with the one-loop inverse-coupling slope. -/

noncomputable section
namespace YangMills
open Filter Set Construction
open scoped Topology
open Construction.TopAux.NonemptyTestClasses Construction.QuadrupleClasses.Collinear

/-- Periodizations of one smooth compact bump and its translate by (5d/2)e₁. -/
def referenceBumpTests (s : Conventions.StandingParameters) (d : ℝ) :
    Fin 2 → s.Torus → ℝ := fun i => periodizedQuad s (bumpQuadruple d) (![0, 2] i)

theorem referenceBumpTests_shaped {C ϑ d : ℝ} (hC : 0 < C)
    (hlip : ∀ u v : Fin 4 → ℝ, |unitBump u - unitBump v| ≤ C * ‖u - v‖)
    (hϑ : ϑ ∈ Ioc (0 : ℝ) 1) (hϑ1 : ϑ ≤ 1 / 32 ^ 4) (hϑ2 : 32 * C * ϑ ≤ 1)
    (hd : 0 < d) (s : Conventions.StandingParameters)
    (h40 : 40 * d ≤ PeriodicLattice.torusSide s.L s.m) :
    ∃ X : AmbientPoints.separatedTuples s .torus 2, X.1 = referenceBumpTests s d ∧
      (X.1 0, X.1 1) ∈ TestFunctions.separatedPairsFourTorus s.L s.m d ϑ ∧
      ∀ i, AmbientPoints.IsSmoothReal (X.1 i) := by
  have hQ := TheStatementsProvedTogether.separated_quadruples_collinear_case
  obtain ⟨-, -, hall⟩ := hQ
  obtain ⟨-, -, -, -, -, htor⟩ := hall d ϑ ⟨hd, hϑ⟩
  obtain ⟨-, -, -, -, htr, -⟩ := htor s h40
  have hq := bumpQuadruple_mem_collinearQuadsR4 hC hlip hϑ.1 hϑ.2 hϑ1 hϑ2 hd
  have ht := (htr (bumpQuadruple d) hq.1).2.2.2 hq
  have hℓ : 0 < PeriodicLattice.torusSide s.L s.m := by linarith
  have hs : ∀ i : Fin 2, AmbientPoints.IsSmoothReal (E := .torus) (s := s)
      (referenceBumpTests s d i) := fun _ =>
    periodize_isSmoothReal s hℓ (scaledBump_contDiff _ _) (scaledBump_hasCompactSupport hd _)
  have inj : Function.Injective (![0, 2] : Fin 2 → Fin 4) := by decide
  refine ⟨⟨referenceBumpTests s d, mem_separatedTuples_torus s hd hℓ _ hs ?_⟩, rfl, ?_, hs⟩
  · intro i j hij
    obtain ⟨_, _, _, _, h, _⟩ := ht.1.2.2.2 _ _ (fun h => hij (inj h))
    exact h
  · exact ht.1.2.2.2 (0 : Fin 4) 2 (by decide)

/-- At any fixed torus volume index there is a single smooth reference observable
which stays above a positive constant as the cutoff tends to infinity along a sequence. -/
theorem su2_fixed_bump_subsequence_lower :
    ∃ Lstar : ℕ, ∀ L : ℕ, Odd L → Lstar ≤ L → ∀ m : ℕ+,
      ∃ (s : Conventions.StandingParameters) (d₀ : ℝ),
        s.L = L ∧ s.m = m ∧ 0 < d₀ ∧ ∀ d ∈ Ioc (0 : ℝ) d₀,
          ∃ (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (ρ : ℝ),
            Tendsto K atTop atTop ∧ (∀ j, 0 < β j) ∧
            Tendsto β atTop atTop ∧
            Tendsto (fun j => β j / Real.log (1 / PeriodicLattice.meshSize L (K j : ℕ)))
              atTop (𝓝 (11 / (3 * Real.pi ^ 2))) ∧ 0 < ρ ∧
            ∀ᶠ j in atTop, ρ < (SchwingerFunctions.connectedSchwinger s.L s.m (K j)
              (β j) (referenceBumpTests s d)).re := by
  obtain ⟨ϑ₀, hϑ₀, J, Lstar, hJ, top⟩ :=
    TheStatementsProvedTogether.top_limits_real_ne_zero
  refine ⟨Lstar, ?_⟩
  intro L hodd hlarge m
  obtain ⟨p, Bs, c₅, γ, Nw, CT, hL, hJ₀, hdat, hBs, hc₅, hγ, hCT, hNw, hg⟩ :=
    top L hodd hlarge
  obtain ⟨conditions, realLimits, nonzero⟩ := hg γ ⟨hγ.1, le_rfl⟩
  obtain ⟨C, hC, hlip⟩ := exists_unitBump_lipschitz
  let ϑ := min ϑ₀ (min (1 / 32 ^ 4) (1 / (32 * C)))
  have hϑ : 0 < ϑ := lt_min hϑ₀.1 (lt_min (by norm_num) (by positivity))
  have hϑl : ϑ ≤ ϑ₀ := min_le_left _ _
  have hϑr : ϑ ≤ min (1 / 32 ^ 4) (1 / (32 * C)) := min_le_right _ _
  have hϑ2 : 32 * C * ϑ ≤ 1 := by
    have hx := (le_div_iff₀ (by positivity : 0 < 32 * C)).mp (hϑr.trans (min_le_right _ _))
    linarith [mul_comm ϑ (32 * C)]
  obtain ⟨d₀, hd₀, hpos⟩ := nonzero ϑ ⟨hϑ,hϑl⟩
  obtain ⟨s, hs, hm⟩ := realLimits.exists_params m
  refine ⟨s, d₀, hs.trans hL, hm, hd₀.1, ?_⟩
  intro d hd
  have h40 := TheStatementsProvedTogether.testClasses_nonempty_all_scales.1 s d (hd.2.trans hd₀.2)
  obtain ⟨X, hX, hshape, _⟩ := referenceBumpTests_shaped hC hlip ⟨hϑ, hϑl.trans hϑ₀.2⟩
    (hϑr.trans (min_le_left _ _)) hϑ2 hd.1 s h40
  obtain ⟨S, hS⟩ := realLimits.exists_torusLimit s hs
  have hp := (hpos d hd).pair_pos_torus s S hs hS X hshape
  obtain ⟨K, β, hpair, hK, hlim⟩ := hS
  have hNK : Tendsto (fun j => (K j : ℕ)) atTop atTop := by
    exact tendsto_PNat_val_atTop_atTop.comp hK
  obtain ⟨δ, hδ, hbound⟩ := conditions.passage.asymptotically_free
  have hratio : Tendsto (fun j => β j / Real.log (1 / PeriodicLattice.meshSize L (K j : ℕ)))
      atTop (𝓝 (11 / (3 * Real.pi ^ 2))) := by
    have hslope : SystemsWithFiveBounds.asymptoticFreedomSlope = 11 / (3 * Real.pi ^ 2) := by
      unfold SystemsWithFiveBounds.asymptoticFreedomSlope
      field_simp
      ring
    rw [← hslope, ← hL, tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun j => hbound _ _ (K j).2 (hpair j)) (hδ.comp hNK)
  have hden : Tendsto (fun j => Real.log (1 / PeriodicLattice.meshSize L (K j : ℕ))) atTop atTop := by
    have hL' : 1 < (L : ℝ) := by
      have hg' := hdat.side_ge
      rw [hL] at hg'
      exact_mod_cast (show 1 < L by omega)
    have hlog := Real.log_pos hL'
    have hx := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hNK
    have hm := hx.atTop_mul_const hlog
    simpa [PeriodicLattice.meshSize, zpow_neg, Real.log_pow, Function.comp_def] using hm
  have hbareTop : Tendsto β atTop atTop := by
    have h := hratio.pos_mul_atTop (by positivity) hden
    apply h.congr'
    filter_upwards [hden.eventually_gt_atTop 0] with j hj
    exact div_mul_cancel₀ _ hj.ne'
  refine ⟨K, β, S 2 le_rfl X / 2, hK, ?_, hbareTop, hratio, by linarith, ?_⟩
  · intro j
    have h := (hpair j).2.1
    change γ ^ (-2 : ℤ) + Bs ≤ β j at h
    have : 0 < γ ^ (-2 : ℤ) := zpow_pos hγ.1 _
    linarith
  · have h := Complex.continuous_re.continuousAt.tendsto.comp (hlim 2 le_rfl X)
    have hh := h.eventually_const_lt (show S 2 le_rfl X / 2 < ((S 2 le_rfl X : ℝ) : ℂ).re by
      simp only [Complex.ofReal_re]; linarith)
    exact (by simpa only [Function.comp_apply, hX] using hh)
end YangMills
end

noncomputable section
namespace YangMills
open Filter Set Construction
open scoped Topology ContDiff
open Construction.TopAux.NonemptyTestClasses Construction.QuadrupleClasses.Collinear
open Construction.TestFunctions Construction.PeriodicLattice

/-- The smooth bump is supported in the ball of radius 3/40, and the other
test is its translate by three units along axis zero. -/
def fixedReferenceBump (x : Fin 4 → ℝ) : ℝ := scaledBump (6 / 5) 0 x

def fixedReferenceTests (L M : ℕ) : Fin 2 → FourTorus L M → ℝ :=
  fun i => periodize (torusSide L M)
    (![fixedReferenceBump, fun x => fixedReferenceBump (x - Pi.single 0 3)] i)

theorem fixedReferenceBump_properties :
    ContDiff ℝ ∞ fixedReferenceBump ∧ HasCompactSupport fixedReferenceBump ∧
    (∀ x, 0 ≤ fixedReferenceBump x) ∧ fixedReferenceBump 0 = 1 ∧
    tsupport fixedReferenceBump ⊆ closedBallR4 0 (1/8) := by
  refine ⟨scaledBump_contDiff _ _, scaledBump_hasCompactSupport (by norm_num) _,
    scaledBump_nonneg _ _, scaledBump_self _ _, ?_⟩
  intro x hx
  have h := tsupport_scaledBump_subset (by norm_num : 0 < (6/5 : ℝ)) 0 hx
  change TorusMetric.euclidNormVec (x - 0) ≤ (1/8 : ℝ)
  change TorusMetric.euclidNormVec (x - 0) ≤ (6/5 : ℝ) / 16 at h
  linarith

private theorem dilate_fixed_bump {L r : ℕ} (hL : 0 < L) (i : Fin 4) :
    dilateR4 L r (bumpQuadruple ((6/5 : ℝ) * meshSize L (r:ℤ)) i) =
      bumpQuadruple (6/5) i := by
  let h := meshSize L (r:ℤ)
  have hpos : 0 < h := zpow_pos (by exact_mod_cast hL) _
  funext x
  apply congrArg unitBump
  funext k
  change 32 / ((6/5) * h) * (h * x k - lineCentre ((6/5) * h) i k) =
    32 / (6/5) * (x k - lineCentre (6/5) i k)
  by_cases hk : k = 0
  · subst k
    simp only [lineCentre_zero]
    field_simp
  · simp [lineCentre, hk]
    field_simp

theorem dilate_fixed_pair (s : Conventions.StandingParameters) {r : ℕ} (hL : 0 < s.L) :
    (fun i : Fin 2 => FourPointBounds.dilateToSide s.L s.m (s.m + r)
      (referenceBumpTests s ((6/5 : ℝ) * meshSize s.L (r:ℤ)) i)) =
      fixedReferenceTests s.L (s.m + r) := by
  have hside : torusSide s.L s.m / torusSide s.L (s.m + r) = meshSize s.L (r:ℤ) := by
    simp only [torusSide, meshSize, zpow_neg, zpow_natCast, pow_add]
    have h : (s.L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    field_simp
  funext i
  have e : ∀ f : FourTorus s.L s.m → ℝ, FourPointBounds.dilateToSide s.L s.m (s.m+r) f =
      dilateTorus s.L s.m r f := by
    intro f
    ext y
    simp only [FourPointBounds.dilateToSide, dilateTorus, contractTorus, hside]
    rfl
  rw [e]
  change dilateTorus s.L s.m r (periodize _ _) = _
  rw [PairTransport.dilateTorus_eq_periodize hL r rfl, dilate_fixed_bump hL]
  fin_cases i <;> apply congrArg (periodize _) <;> funext x <;>
    norm_num [bumpQuadruple, fixedReferenceTests, fixedReferenceBump, scaledBump, lineCentre]


/-- The same smooth bump and the same three-unit translate on a fixed reference torus
have uniformly positive connected correlation along a sequence with the one-loop slope. -/
theorem su2_reference_subsequence :
    ∃ Lstar : ℕ, ∀ L : ℕ, Odd L → Lstar ≤ L →
      ∃ (M : ℕ) (K : ℕ+ → ℕ) (β : ℕ+ → ℝ) (ρ : ℝ),
        8 ≤ torusSide L M ∧ Tendsto K atTop atTop ∧ (∀ j, 0 < β j) ∧ Tendsto β atTop atTop ∧
        Tendsto (fun j => β j / ((K j : ℝ) * Real.log L)) atTop (𝓝 (11 / (3 * Real.pi ^ 2))) ∧
        0 < ρ ∧ ∀ᶠ j in atTop, ρ < (SchwingerFunctions.connectedSchwinger L M (K j)
          (β j) (fixedReferenceTests L M)).re := by
  obtain ⟨Lstar, hLstar⟩ := su2_fixed_bump_subsequence_lower
  refine ⟨max Lstar 4, ?_⟩
  intro L hodd hL
  have hL4 := (le_max_right Lstar 4).trans hL
  have hLNat : 0 < L := by omega
  have hLR : 1 < (L : ℝ) := by exact_mod_cast (show 1 < L by omega)
  obtain ⟨s, d₀, hs, hm, hd₀, hsmall⟩ := hLstar L hodd ((le_max_left _ _).trans hL) 1
  have hh : Tendsto (fun r : ℕ => (6/5 : ℝ) * meshSize L (r:ℤ)) atTop (𝓝 0) := by
    simpa [meshSize, zpow_neg, zpow_natCast] using
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hLR)).const_mul (6/5 : ℝ)
  obtain ⟨r, hr⟩ := (hh.eventually_lt_const hd₀).exists
  have hp : 0 < (6/5 : ℝ) * meshSize L (r:ℤ) := by
    unfold meshSize
    positivity
  obtain ⟨K, β, ρ, hK, hβ, hb, hAF, hρ, hmom⟩ := hsmall _ ⟨hp,hr.le⟩
  let κ : ℕ+ → ℕ := fun j => (K j : ℕ) - r
  have hK' : Tendsto (fun j => (K j : ℕ)) atTop atTop := tendsto_PNat_val_atTop_atTop.comp hK
  have hκ : Tendsto κ atTop atTop := tendsto_atTop.2 fun n => by
    filter_upwards [hK'.eventually_ge_atTop (n+r)] with j hj
    dsimp only [κ]
    omega
  have hpos := Real.log_pos hLR
  have hcorr : Tendsto (fun j => ((K j : ℕ) : ℝ) / (κ j : ℝ)) atTop (𝓝 1) := by
    have hκR : Tendsto (fun j => (κ j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hκ
    have hz := (tendsto_inv_atTop_zero.comp hκR).const_mul (r:ℝ)
    have hn : Tendsto (fun j => 1 + (r:ℝ) * (κ j : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hz
    apply hn.congr'
    filter_upwards [hK'.eventually_ge_atTop r, hκR.eventually_gt_atTop 0] with j hj hn
    have hsum : (K j : ℕ) = κ j + r := (Nat.sub_add_cancel hj).symm
    have hx : ((K j : ℕ) : ℝ) = (κ j : ℝ) + r := by exact_mod_cast hsum
    rw [hx]
    field_simp
  refine ⟨(s.m : ℕ) + r, κ, β, ρ, ?_, hκ, hβ, hb, ?_, hρ, ?_⟩
  · rw [hm]
    change 8 ≤ 2 * (L:ℝ) ^ (1+r)
    rw [pow_add, pow_one]
    have hpow := one_le_pow₀ (le_of_lt hLR) (n:=r)
    have hfour : (4:ℝ) ≤ L := by exact_mod_cast hL4
    nlinarith
  · have hboth := hAF.mul hcorr
    simp only [mul_one] at hboth
    apply hboth.congr'
    filter_upwards [hκ.eventually_gt_atTop 0] with j hj
    simp only [meshSize, zpow_neg, zpow_natCast, one_div, inv_inv, Real.log_pow]
    have ha : (0:ℝ) < κ j := by exact_mod_cast hj
    have hk : (0:ℝ) < (K j : ℕ) := by exact_mod_cast (K j).pos
    field_simp
  · have hc := TheStatementsProvedTogether.four_point_cutoff_rescaling_invariant
    filter_upwards [hmom, hK'.eventually_ge_atTop r] with j hj hk
    have he : ((s.m : ℕ) + r) + κ j = (s.m : ℕ) + (K j : ℕ) := by dsimp only [κ]; omega
    subst L
    have h3 : 3 ≤ s.L := by omega
    have ht := hc s.L s.m (K j) ((s.m:ℕ)+r) (κ j) 2 (β j) h3 he
      (referenceBumpTests s (6/5 * meshSize s.L (r:ℤ)))
    rw [dilate_fixed_pair s (by omega : 0 < s.L)] at ht
    change ρ < (torusUrsellFunction _ _ _ _ _).re at hj ⊢
    rwa [← ht]

end YangMills
end

noncomputable section
namespace YangMills
open Set Construction Construction.TestFunctions Construction.TopAux.NonemptyTestClasses
open MeasureTheory
open scoped Topology

theorem fixedReferenceKernel_pos :
    0 < inverseEighthKernel fixedReferenceBump (fun x => fixedReferenceBump (x - Pi.single 0 3)) := by
  obtain ⟨C, hC, hlip⟩ := exists_unitBump_lipschitz
  let ϑ : ℝ := min (1/32^4) (1 / (32*C))
  have hϑ : 0 < ϑ := lt_min (by norm_num) (by positivity)
  have hϑ1 : ϑ ≤ 1/32^4 := min_le_left _ _
  have hϑ2 : 32*C*ϑ ≤ 1 := by
    rw [mul_comm]
    exact (le_div_iff₀ (by positivity : 0 < 32*C)).mp (min_le_right _ _)
  let d := (6/5 : ℝ)
  have hd : 0 < d := by norm_num [d]
  let f := bumpQuadruple d 0
  let h := bumpQuadruple d 2
  have hsh : (f,h) ∈ separatedPairsR4 d ϑ :=
    bumpQuadruple_pair_mem hC hlip hϑ hϑ1 hϑ2 hd (by decide)
  obtain ⟨_, _, a, b, hab⟩ := (mem_separatedPairs_iff _ _ _ _ _ _ _).mp hsh
  have hchain := (TheStatementsProvedTogether.testPair_geometry_kernel_bounds.1 d ϑ
    ⟨hd, hϑ, hϑ1.trans (by norm_num)⟩ a b f h hsh hab).1.2.2.2.2
  have hh := hchain.1.trans hchain.2.1
  have hf : uniformNorm f = 1 := uniformNorm_scaledBump _
  have hg : uniformNorm h = 1 := uniformNorm_scaledBump _
  rw [hf, hg] at hh
  have hp : 0 < inverseEighthKernel f h := lt_of_lt_of_le (by unfold TestPairs.kernelLowerConst; positivity) hh
  have fe : f = fixedReferenceBump := by
    funext x
    norm_num [f, d, bumpQuadruple, fixedReferenceBump, lineCentre, scaledBump]
  have he : h = fun x => fixedReferenceBump (x-Pi.single 0 3) := by
    funext x
    norm_num [h, d, bumpQuadruple, fixedReferenceBump, lineCentre, scaledBump]
  rwa [fe, he] at hp

/-- The prescribed SU(2) calibration level from the Euclidean reference test. -/
def fixedPhysicalLevel (g₀ : ℝ) : ℝ :=
  (9 * g₀ ^ 4 / Real.pi ^ 4) * ∫ x : Fin 4 → ℝ, ∫ y : Fin 4 → ℝ,
    fixedReferenceBump x * fixedReferenceBump (y - Pi.single 0 3) /
      TorusMetric.euclidNormVec (x - y) ^ 8

theorem fixedPhysicalLevel_eq (g₀ : ℝ) :
    fixedPhysicalLevel g₀ = (9 * g₀ ^ 4 / Real.pi ^ 4) *
      inverseEighthKernel fixedReferenceBump (fun y => fixedReferenceBump (y - Pi.single 0 3)) := by
  unfold fixedPhysicalLevel
  congr 1
  let F (z : (Fin 4 → ℝ) × (Fin 4 → ℝ)) := fixedReferenceBump z.1 *
    fixedReferenceBump (z.2 - Pi.single 0 3) * (TorusMetric.euclidNormVec (z.1-z.2)) ^ (-8 : ℤ)
  have hn : (∫ z, F z) ≠ 0 := fixedReferenceKernel_pos.ne'
  have hi : MeasureTheory.Integrable F := by
    by_contra h
    exact hn (MeasureTheory.integral_undef h)
  change _ = ∫ z, F z
  rw [Measure.volume_eq_prod (Fin 4 → ℝ) (Fin 4 → ℝ), MeasureTheory.integral_prod F hi]
  simp [F, div_eq_mul_inv, zpow_neg]

theorem fixedPhysicalLevel_pos {g₀ : ℝ} (hg₀ : 0 < g₀) : 0 < fixedPhysicalLevel g₀ := by
  rw [fixedPhysicalLevel_eq]
  exact mul_pos (by positivity) fixedReferenceKernel_pos

theorem fixedPhysicalLevel_tendsto_zero : Filter.Tendsto fixedPhysicalLevel (𝓝 0) (𝓝 0) := by
  change Filter.Tendsto (fun g₀ : ℝ => fixedPhysicalLevel g₀) (𝓝 0) (𝓝 0)
  simp_rw [fixedPhysicalLevel_eq]
  have hc : Continuous (fun g₀ : ℝ => (9 * g₀ ^ 4 / Real.pi ^ 4) *
      inverseEighthKernel fixedReferenceBump (fun y => fixedReferenceBump (y - Pi.single 0 3))) := by
    fun_prop
  simpa using (hc.continuousAt (x := 0)).tendsto

theorem fixedPhysicalLevel_small {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ > (0 : ℝ), ∀ g₀ ∈ Ioo (0 : ℝ) δ, fixedPhysicalLevel g₀ ∈ Ioo 0 ρ := by
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1
    (fixedPhysicalLevel_tendsto_zero.eventually_lt_const hρ)
  refine ⟨δ, hδ, fun g₀ hg₀ => ⟨fixedPhysicalLevel_pos hg₀.1, hh ?_⟩⟩
  simpa [Real.dist_eq, abs_of_pos hg₀.1] using hg₀.2

end YangMills
end
