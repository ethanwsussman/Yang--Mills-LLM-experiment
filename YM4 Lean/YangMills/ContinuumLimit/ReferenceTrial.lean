import Formulation.ReferenceCoupling
import YangMills.ContinuumLimit.TunedLimitsAtTheTop
import YangMills.ContinuumLimit.TunedBranch
set_option autoImplicit false
noncomputable section
namespace YangMills.BranchHot
open Filter Set Construction ContinuumLimit Formulation
open scoped Topology ContDiff
open Construction.TopAux.NonemptyTestClasses Construction.QuadrupleClasses.Collinear
open Construction.TestFunctions Construction.PeriodicLattice

theorem all_cutoff_trial {p : TorusLumps.StepParameters} {T : RenormalizationStepParameters.ParameterAssignment}
    {y lam cr Bs G ϑ₀ : ℝ} (hϑ₀ : ϑ₀ ∈ Ioc (0:ℝ) 1)
    (s : Conventions.StandingParameters) (hs : s.L = p.side)
    (hpos : ∀ ϑ ∈ Ioc (0:ℝ) ϑ₀, ∃ d₁ ∈ Ioc (0:ℝ) (1/40), ∀ d ∈ Ioc (0:ℝ) d₁,
      QuaternionicWilsonModel.TopLimitsRealNonzero.ValuesPositiveAt p Bs G ϑ d)
    (hlim : TunedTop.DilatedTopLimits p T y lam cr Bs G)
    (b : ℕ → ℝ) (hb : ∀ k, IsTunedAt T y (SequencePassage.passageThreshold Bs G) k (b k))
    (R₀ : ℕ) :
    ∃ R : ℕ, R₀ ≤ R ∧ ∃ ρ > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      ρ < referenceResponse s.L ((s.m : ℕ)+R) k (b (k+R)) := by
  obtain ⟨C, hC, hlip⟩ := exists_unitBump_lipschitz
  let ϑ := min ϑ₀ (min (1 / 32 ^ 4) (1 / (32 * C)))
  have hϑ : 0 < ϑ := lt_min hϑ₀.1 (lt_min (by norm_num) (by positivity))
  have hϑl : ϑ ≤ ϑ₀ := min_le_left _ _
  have hϑr : ϑ ≤ min (1 / 32 ^ 4) (1 / (32 * C)) := min_le_right _ _
  have hϑ2 : 32 * C * ϑ ≤ 1 := by
    have hx := (le_div_iff₀ (by positivity : 0 < 32 * C)).mp (hϑr.trans (min_le_right _ _))
    linarith [mul_comm ϑ (32 * C)]
  obtain ⟨d₁, hd₁, hpositive⟩ := hpos ϑ ⟨hϑ,hϑl⟩
  have hs13 := s.isAdmissible.2
  have hL : 0 < s.L := by omega
  have hLR : 1 < (s.L:ℝ) := by exact_mod_cast (show 1 < s.L by omega)
  have htiny : Tendsto (fun n : ℕ => (6/5 : ℝ) * meshSize s.L (n:ℤ)) atTop (𝓝 0) := by
    simpa [meshSize, zpow_neg, zpow_natCast] using
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hLR)).const_mul (6/5 : ℝ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htiny.eventually_lt_const hd₁.1)
  let D := runDepth lam cr
  let R := N + D + R₀ + 1
  refine ⟨R, by dsimp [R]; omega, ?_⟩
  by_contra hlow
  have hbad : ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧
      referenceResponse s.L ((s.m:ℕ)+R) k (b (k+R)) ≤ 1 / ((n:ℝ)+1) := by
    intro n
    by_contra! he
    exact hlow ⟨_, by positivity, (eventually_ge_atTop n).mono (fun k hk => he k hk)⟩
  choose κ hκ hsmall using hbad
  let k' (i : ℕ+) : ℕ+ := ⟨κ i + R, by dsimp [R]; omega⟩
  have htop : Tendsto k' atTop atTop := tendsto_atTop_atTop.2 fun n =>
    ⟨n, fun i hi => show (n:ℕ) ≤ κ i + R from (show (n:ℕ) ≤ i from hi).trans ((hκ i).trans (Nat.le_add_right ..))⟩
  obtain ⟨r, hr, φ, k₁, S, hφ, he, _, hS, hc, _, _⟩ := hlim s hs k' (fun i => b (k' i))
    htop (fun i => by change D ≤ κ i + R; dsimp [R]; omega) (fun i => hb (k' i))
  let s' := shiftSide s r
  let u := R - r
  let d := (6/5:ℝ) * meshSize s.L (u:ℤ)
  have hrd : r < D := hr
  have hu : N ≤ u := by dsimp [u,R]; omega
  have hd : 0 < d := by dsimp [d,meshSize]; positivity
  have hdle : d ≤ d₁ := (hN u hu).le
  have hside : 40 * d ≤ torusSide s'.L s'.m :=
    TheStatementsProvedTogether.testClasses_nonempty_all_scales.1 s' d (hdle.trans hd₁.2)
  obtain ⟨X, hX, hshape, _⟩ := referenceBumpTests_shaped hC hlip ⟨hϑ, hϑl.trans hϑ₀.2⟩
    (hϑr.trans (min_le_left _ _)) hϑ2 hd s' hside
  have hpositiveS := (hpositive d ⟨hd, hdle⟩).pair_pos_torus s' S hs hS X hshape
  have hM : (s'.m:ℕ) + u = (s.m:ℕ) + R := by
    change (s.m:ℕ) + r + (R - r) = (s.m:ℕ)+R
    dsimp [R]; omega
  have transfer (j : ℕ+) :
      (SchwingerFunctions.connectedSchwinger s.L ((s.m:ℕ)+r) (k₁ j) (b (k' (φ j))) X.1).re =
        referenceResponse s.L ((s.m:ℕ)+R) (κ (φ j)) (b (κ (φ j)+R)) := by
    have hk := he j
    change (k₁ j:ℕ) + r = κ (φ j) + R at hk
    have heq : (s'.m:ℕ)+(k₁ j:ℕ) = ((s'.m:ℕ)+u)+κ (φ j) := by
      change (s.m:ℕ)+r+(k₁ j:ℕ) = ((s'.m:ℕ)+u)+κ (φ j)
      omega
    have h3 : 3 ≤ s'.L := by change 3 ≤ s.L; omega
    have eq := TheStatementsProvedTogether.four_point_cutoff_rescaling_invariant
      s'.L s'.m (k₁ j) ((s'.m:ℕ)+u) (κ (φ j)) 2 (b (k' (φ j))) h3 heq.symm
      (referenceBumpTests s' d)
    have pair : (fun i : Fin 2 => FourPointBounds.dilateToSide s'.L s'.m ((s'.m:ℕ)+u) (referenceBumpTests s' d i)) = fixedReferenceTests s'.L ((s'.m:ℕ)+u) := dilate_fixed_pair s' (r := u) hL
    rw [pair] at eq

    rw [hX]
    unfold referenceResponse
    rw [← hM]
    exact congrArg Complex.re eq
  have ht := (Complex.continuous_re.continuousAt.tendsto.comp (hc 2 le_rfl X)).congr transfer
  have hhalf : S 2 le_rfl X / 2 < ((S 2 le_rfl X:ℝ):ℂ).re := by simp; linarith
  have hseen := ht.eventually_const_lt hhalf
  have hφtop := LimitsOfATunedSequence.tendsto_of_strictMono_pnat hφ
  have hsqueeze := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_PNat_val_atTop_atTop.comp hφtop)
  have hvanish := hsqueeze.eventually_lt_const (show 0 < S 2 le_rfl X / 2 by linarith)
  obtain ⟨j,h1,h2⟩ := (hseen.and hvanish).exists
  exact (not_lt_of_ge (hsmall (φ j))) (lt_trans h2 h1)

end YangMills.BranchHot
end


