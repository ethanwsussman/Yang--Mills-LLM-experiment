import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheMarkedIntegralOfAllBlocksProof
import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelow
import YangMills.Construction.ResponseInTheExpansion.ColdConditionsHaveOneConstantProof
import YangMills.Construction.ResponseInTheExpansion.NumberOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.PartsOfTheTotalOfTheResponse
import YangMills.Construction.ResponseInTheExpansion.ResponseIsCarried
import YangMills.Construction.ResponseInTheExpansion.ResponseLessTheShareReturns
import YangMills.Construction.SummableBoundsOfTheFlow.NumberOfASmallFamily
import YangMills.Construction.SummableBoundsOfTheFlow.TiltOfTheImageProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ResponseInTheExpansion.ResponseCoefficient
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses FamilyNorms ShareFamilies
private def unitPlaneMatrix : Fin 4 → Fin 4 → ℝ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0
private theorem unitPlaneMatrix_antisymm (i j : Fin 4) : unitPlaneMatrix i j = - unitPlaneMatrix j i := by
  unfold unitPlaneMatrix
  by_cases h1 : i = 0 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := h1
    simp
  · by_cases h2 : i = 1 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h2
      simp
    · have h1' : ¬ (j = 0 ∧ i = 1) := fun h => h2 ⟨h.2, h.1⟩
      have h2' : ¬ (j = 1 ∧ i = 0) := fun h => h1 ⟨h.2, h.1⟩
      simp [h1, h2, h1', h2']
private theorem unitPlaneMatrix_cases (i j : Fin 4) :
    unitPlaneMatrix i j = 0 ∨ unitPlaneMatrix i j = 1 ∨ unitPlaneMatrix i j = -1 := by
  unfold unitPlaneMatrix
  split_ifs <;> simp
private theorem unitPlaneMatrix_integral (i j : Fin 4) : ∃ z : ℤ, ((1 : ℕ) : ℝ) * unitPlaneMatrix i j = z := by
  rcases unitPlaneMatrix_cases i j with h | h | h <;> rw [h]
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp⟩
private theorem abs_unitPlaneMatrix_le_one (i j : Fin 4) : |unitPlaneMatrix i j| ≤ 1 := by
  rcases unitPlaneMatrix_cases i j with h | h | h <;> rw [h] <;> simp
private theorem curvatureAlong_unitPlaneMatrix : curvatureAlong quaternionI unitPlaneMatrix = unitPlaneCurvature := by
  funext i j
  unfold curvatureAlong unitPlaneMatrix unitPlaneCurvature planeCurvature
  by_cases h1 : i = 0 ∧ j = 1
  · simp [h1]
  · by_cases h2 : i = 1 ∧ j = 0
    · simp only [h2, if_true, and_self]
      have hn : ¬ ((1 : Fin 4) = 0 ∧ (0 : Fin 4) = 1) := by simp
      obtain ⟨rfl, rfl⟩ := h2
      simp only [hn, if_false]
      exact neg_one_smul ℝ (quaternionI : BlockAverages.imaginaryQuaternions)
    · simp [h1, h2]
private theorem norm_quaternionI : ‖quaternionI‖ = 1 := by apply _root_.YangMills.SharedProofs.p9532 <;> assumption
private theorem exists_logSq_le_side : ∃ n₄ : ℕ, ∀ n : ℕ, n₄ ≤ n →
    8 * Real.log (1 / (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2)) ^ 2 ≤ (n : ℝ) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).def (c := 1 / 32) (by norm_num)
  have h2 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  obtain ⟨n₄, hn₄⟩ := Filter.eventually_atTop.mp h2
  refine ⟨max n₄ 3, fun n hn => ?_⟩
  have hb := hn₄ n (le_trans (le_max_left _ _) hn)
  have h3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast h3
  have hpi := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  simp only [id, Real.norm_eq_abs] at hb
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)] at hb
  have e : 1 / (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) = (n : ℝ) ^ 2 / (2 * Real.pi) := by
    push_cast
    field_simp
  rw [e]
  have hq1 : 1 ≤ (n : ℝ) ^ 2 / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hq2 : (n : ℝ) ^ 2 / (2 * Real.pi) ≤ (n : ℝ) ^ 2 := by
    apply div_le_self (by positivity)
    linarith
  have l0 : 0 ≤ Real.log ((n : ℝ) ^ 2 / (2 * Real.pi)) := Real.log_nonneg hq1
  have l1 : Real.log ((n : ℝ) ^ 2 / (2 * Real.pi)) ≤ 2 * Real.log n := by
    have := Real.log_le_log (by linarith) hq2
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have l2 : Real.log ((n : ℝ) ^ 2 / (2 * Real.pi)) ^ 2 ≤ (2 * Real.log n) ^ 2 :=
    pow_le_pow_left₀ l0 l1 2
  nlinarith
private theorem centered_near_planeValue (hA : SecondOrderAtAbelianFields) {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} (hf : ℓ.Admissible)
    {C : ℝ} {h : LocalDensity} {v : ℝ} (H : IsCurvatureFamily ℓ C h)
    (hv : HasSum (limitFormTerm h unitPlaneCurvature unitPlaneCurvature) v)
    {ε : ℝ} (hε : 0 < ε) : ∃ n₁ : ℕ, ∀ (n : ℕ) [NeZero n], n₁ ≤ n → ∀ V : TorusField n,
      IsAbelianWithCurvature quaternionI unitPlaneMatrix (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) V →
      ∀ Y : TorusSite n,
      |centered h n Y V - (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) ^ 2 / 2 * v| ≤
        ε * (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2) ^ 2 := by
  obtain ⟨w, hw, hwε⟩ := (hA ℓ hf C h H).2.2.2.2.2.2.2 unitPlaneMatrix 1 quaternionI unitPlaneMatrix_antisymm one_pos
    unitPlaneMatrix_integral norm_quaternionI
  rw [curvatureAlong_unitPlaneMatrix] at hw
  have e1 : w = v := hw.unique hv
  subst e1
  exact hwε ε hε
private theorem abs_sum_sub_card_mul_le {n : ℕ} [NeZero n] (h : TorusSite n → ℝ) {c e : ℝ}
    (hb : ∀ y, |h y - c| ≤ e) :
    |∑ y, h y - ((Finset.univ : Finset (TorusSite n)).card : ℝ) * c| ≤
      ((Finset.univ : Finset (TorusSite n)).card : ℝ) * e := by
  have : ∑ y, h y - ((Finset.univ : Finset (TorusSite n)).card : ℝ) * c = ∑ y : TorusSite n, (h y - c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [this]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun y _ => hb y).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
set_option maxHeartbeats 1000000 in
theorem planeValue_sub_sum_le (hA : SecondOrderAtAbelianFields) (hW : AbelianFieldOfAnglesHasCurvature)
    {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} (hf : ℓ.Admissible) {m : ℕ} {C : ℝ} {C' : Fin m → ℝ} {h r : LocalDensity}
    {g : Fin m → LocalDensity}
    {v al B : ℝ} {w : Fin m → ℝ} (H : IsCurvatureFamily ℓ C h) (G : ∀ i, IsCurvatureFamily ℓ (C' i) (g i))
    (hv : HasSum (limitFormTerm h unitPlaneCurvature unitPlaneCurvature) v)
    (hw : ∀ i, HasSum (limitFormTerm (g i) unitPlaneCurvature unitPlaneCurvature) (w i))
    (htot : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ V : TorusField n, IsCold ℓ.threshold V →
      ∑ y, centered h n y V = ∑ i, ∑ y, centered (g i) n y V + al * ∑ y, centered r n y V)
    (hr : ∀ ε : ℝ, 0 < ε → ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ → ∀ (n : ℕ) [NeZero n],
      8 * Real.log (1 / γ) ^ 2 ≤ n → ∀ (V : TorusField n) (Y : TorusSite n),
        IsAbelianWithCurvature quaternionI unitPlaneMatrix γ V →
        |centered r n Y V| ≤ γ ^ 2 * (B + ε)) :
    |v - ∑ i, w i| ≤ 2 * |al| * B := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε : ℝ := δ / (8 * (1 + |al| + m)) with hεd
  have hden : 0 < 8 * (1 + |al| + (m : ℝ)) := by positivity
  have hε : 0 < ε := div_pos hδ hden
  obtain ⟨n₁, hn₁⟩ := centered_near_planeValue hA hf H hv hε
  choose n₂ hn₂ using fun i => centered_near_planeValue hA hf (G i) (hw i) hε
  obtain ⟨γ₀, hγ₀, hrγ⟩ := hr ε hε
  obtain ⟨n₄, hn₄⟩ := exists_logSq_le_side
  have hσ : 0 < ℓ.threshold := hf.σ_pos
  set s : ℝ := min (min 1 (ℓ.threshold / 2)) γ₀ with hs
  have hs0 : 0 < s := lt_min (lt_min one_pos (by linarith)) hγ₀
  obtain ⟨n₃, hn₃⟩ := exists_nat_gt (2 * Real.pi / s)
  set n : ℕ := max (max (max n₁ (Finset.univ.sup n₂)) (max n₃ ℓ.n₀)) (max n₄ 1) with hn
  have h1n : 1 ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
  have : NeZero n := ⟨by omega⟩
  have l1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have l2 : ∀ i, n₂ i ≤ n := fun i => le_trans (Finset.le_sup (f := n₂) (Finset.mem_univ i))
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
  have l3 : n₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have l4 : ℓ.n₀ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have l5 : n₄ ≤ n := le_trans (le_max_left _ _) (le_max_right _ _)
  set γ : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 with hγ
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast h1n
  have hγ0 : 0 < γ := by
    rw [hγ]
    have := Real.pi_pos
    positivity
  have hγs : γ < s := by
    have a1 : 2 * Real.pi / s < n := lt_of_lt_of_le hn₃ (by exact_mod_cast l3)
    have a2 : 2 * Real.pi < n * s := by
      rwa [div_lt_iff₀ hs0] at a1
    have a3 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have a4 : 2 * Real.pi < (n : ℝ) ^ 2 * s :=
      lt_of_lt_of_le a2 (mul_le_mul_of_nonneg_right a3 hs0.le)
    rw [hγ, div_lt_iff₀ (by positivity)]
    simpa [mul_comm] using a4
  have hγ1 : γ < 1 := lt_of_lt_of_le hγs ((min_le_left _ _).trans (min_le_left _ _))
  have hγ2 : γ < ℓ.threshold / 2 := lt_of_lt_of_le hγs ((min_le_left _ _).trans (min_le_right _ _))
  have hγ3 : γ < γ₀ := lt_of_lt_of_le hγs (min_le_right _ _)
  set V := abelianFieldOfAngles n quaternionI γ unitPlaneMatrix with hV
  have hAb : IsAbelianWithCurvature quaternionI unitPlaneMatrix γ V :=
    hW n quaternionI unitPlaneMatrix 1 norm_quaternionI unitPlaneMatrix_antisymm unitPlaneMatrix_integral
  have hcold : IsCold ℓ.threshold V := by
    intro x μ ν hμν
    have e := hAb.2 x μ ν hμν
    have b := norm_coe_expUnit_smul_sub_one_le quaternionI norm_quaternionI (γ * unitPlaneMatrix μ ν)
    have c : curvature V x μ ν = ‖((BlockAverages.expUnit ((γ * unitPlaneMatrix μ ν) • quaternionI) :
        BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
      unfold curvature
      rw [e]
    rw [c]
    refine lt_of_le_of_lt b ?_
    have q0 := abs_unitPlaneMatrix_le_one μ ν
    have q1 : |γ * unitPlaneMatrix μ ν| ≤ γ := by
      rw [abs_mul, abs_of_pos hγ0]
      nlinarith
    have q2 : (γ * unitPlaneMatrix μ ν) ^ 2 ≤ γ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) q1 2
    nlinarith
  have t := htot n l4 V hcold
  set N : ℝ := ((Finset.univ : Finset (TorusSite n)).card : ℝ) with hN
  have s1 : |∑ y, centered h n y V - N * (γ ^ 2 / 2 * v)| ≤ N * (ε * γ ^ 2) :=
    abs_sum_sub_card_mul_le (fun y => centered h n y V) (hn₁ n l1 V hAb)
  have s2 : ∀ i, |∑ y, centered (g i) n y V - N * (γ ^ 2 / 2 * w i)| ≤ N * (ε * γ ^ 2) := fun i =>
    abs_sum_sub_card_mul_le (fun y => centered (g i) n y V) (hn₂ i n (l2 i) V hAb)
  have s3 : |∑ y, centered r n y V| ≤ N * (γ ^ 2 * (B + ε)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun y _ => hrγ γ hγ0 hγ3 n (hn₄ n l5) V y hAb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have s4 : |∑ i, ∑ y, centered (g i) n y V - N * (γ ^ 2 / 2 * ∑ i, w i)| ≤ (m : ℝ) * (N * (ε * γ ^ 2)) := by
    have e : ∑ i, ∑ y, centered (g i) n y V - N * (γ ^ 2 / 2 * ∑ i, w i) =
        ∑ i : Fin m, (∑ y, centered (g i) n y V - N * (γ ^ 2 / 2 * w i)) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => s2 i).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    simp
  set D : ℝ := v - ∑ i, w i with hD
  have key : N * γ ^ 2 / 2 * |D| ≤ N * γ ^ 2 * (ε + m * ε + |al| * (B + ε)) := by
    have e : N * γ ^ 2 / 2 * D = -(∑ y, centered h n y V - N * (γ ^ 2 / 2 * v)) +
        (∑ i, ∑ y, centered (g i) n y V - N * (γ ^ 2 / 2 * ∑ i, w i)) + al * ∑ y, centered r n y V := by
      rw [t, hD]
      ring
    have e2 : |N * γ ^ 2 / 2 * D| = N * γ ^ 2 / 2 * |D| := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < N * γ ^ 2 / 2)]
    rw [← e2, e]
    have a1 := abs_add_le (-(∑ y, centered h n y V - N * (γ ^ 2 / 2 * v)) +
        (∑ i, ∑ y, centered (g i) n y V - N * (γ ^ 2 / 2 * ∑ i, w i))) (al * ∑ y, centered r n y V)
    have a2 := abs_add_le (-(∑ y, centered h n y V - N * (γ ^ 2 / 2 * v)))
        (∑ i, ∑ y, centered (g i) n y V - N * (γ ^ 2 / 2 * ∑ i, w i))
    rw [abs_neg] at a2
    have a3 : |al * ∑ y, centered r n y V| ≤ |al| * (N * (γ ^ 2 * (B + ε))) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left s3 (abs_nonneg _)
    have e3 : N * γ ^ 2 * (ε + m * ε + |al| * (B + ε)) =
        N * (ε * γ ^ 2) + m * (N * (ε * γ ^ 2)) + |al| * (N * (γ ^ 2 * (B + ε))) := by ring
    rw [e3]
    linarith
  have main2 : |D| ≤ 2 * (ε + m * ε + |al| * (B + ε)) := by
    have : N * γ ^ 2 / 2 * |D| ≤ N * γ ^ 2 / 2 * (2 * (ε + m * ε + |al| * (B + ε))) := by
      have e : N * γ ^ 2 / 2 * (2 * (ε + m * ε + |al| * (B + ε))) =
          N * γ ^ 2 * (ε + m * ε + |al| * (B + ε)) := by ring
      rw [e]
      exact key
    exact le_of_mul_le_mul_left this (by positivity)
  have hfin : 2 * (ε + m * ε + |al| * ε) ≤ δ := by
    have h8 : ε * (8 * (1 + |al| + (m : ℝ))) = δ := by
      rw [hεd]
      field_simp
    have e : 2 * (ε + m * ε + |al| * ε) = 1 / 4 * (ε * (8 * (1 + |al| + (m : ℝ)))) := by ring
    rw [e, h8]
    linarith
  linarith
section SiteTransfer
variable {H : BlockAverages.BlockFrame} {m : ℕ}
private theorem toTorusSite_siteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m) :
    toTorusSite m (StepCosts.torusSiteInFrame H j x) = x := by apply _root_.YangMills.Construction.TorusLevels.toTorusSite_torusSiteInFrame <;> assumption
private theorem siteInFrame_toTorusSite (j : ℕ) (hm : ∀ i, H.period j i = m) (y : H.Site j) :
    StepCosts.torusSiteInFrame H j (toTorusSite m y) = y := by apply _root_.YangMills.Construction.TorusLevels.torusSiteInFrame_toTorusSite <;> assumption
private theorem plaquetteDefect_readAtLevel_eq {H : BlockAverages.BlockFrame} {j m : ℕ}
    (hm : ∀ i, H.period j i = m) (W : TorusField m) (p : H.Site j × Fin 4 × Fin 4) :
    BlockAverages.plaquetteDefect (readAtLevel H j W) p = curvature W (toTorusSite m p.1) p.2.1 p.2.2 := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.plaquetteDefect_readAtLevel_torus <;> assumption
private theorem period_top {n : ℕ} (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.top i = n := by
  simp [BlockAverages.BlockFrame.period, hs]
private theorem isSmallCurvature_readAtLevel {H : BlockAverages.BlockFrame} {j m : ℕ}
    (hm : ∀ i, H.period j i = m) {s s' : ℝ} (hs : s ≤ s') {W : TorusField m}
    (hW : IsCold s W) : ColdStepAtMirrorFrames.IsSmallCurvature s' (readAtLevel H j W) := by
  intro p hp
  rw [plaquetteDefect_readAtLevel_eq hm]
  exact (hW _ _ _ hp).trans_le hs
private theorem sum_torus_eq_sum_finiteCells {L t n : ℕ} [NeZero n] (g : (torusFrame L t n).Cell → ℝ) :
    ∑ Y : TorusSite n, g (StepCosts.torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y) =
      ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells (torusFrame L t n), g Y := by
  have hm : ∀ i, (torusFrame L t n).period (torusFrame L t n).top i = n :=
    fun i => period_top (H := torusFrame L t n) (fun _ => rfl) i
  have hw : ∀ z : (torusFrame L t n).Cell, z ∈ ColdStepAtMirrorFrames.finiteCells (torusFrame L t n) := by
    intro z
    have h : ∀ i, NeZero ((torusFrame L t n).period (torusFrame L t n).top i) :=
      fun i => ⟨by rw [hm i]; exact NeZero.ne n⟩
    have hf : Finite (torusFrame L t n).Cell := by
      show Finite ((i : Fin 4) → ZMod ((torusFrame L t n).period (torusFrame L t n).top i))
      infer_instance
    unfold ColdStepAtMirrorFrames.finiteCells
    rw [dif_pos hf]
    exact @Finset.mem_univ _ (Fintype.ofFinite _) z
  refine Finset.sum_nbij' (StepCosts.torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top)
    (toTorusSite n) (fun _ _ => hw _)
    (fun _ _ => Finset.mem_univ _) (fun x _ => toTorusSite_siteInFrame _ hm x)
    (fun z _ => siteInFrame_toTorusSite _ hm z) (fun _ _ => rfl)
abbrev _root_.YangMills.SharedProofs.p4810 := @sum_torus_eq_sum_finiteCells
end SiteTransfer
section CurvatureFamilies
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters}
private theorem weight_pos_aux (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem isCurvatureFamily_mono {C C' : ℝ} {f : LocalDensity} (hC : C ≤ C')
    (h : IsCurvatureFamily ℓ C f) : IsCurvatureFamily ℓ C' f :=
  ⟨h.smooth, h.gauge, h.translation,
    fun n _ hn y W hW k c X hk1 hk3 hX => (h.decay n hn y W hW k c X hk1 hk3 hX).trans
      (div_le_div_of_nonneg_right hC (weight_pos_aux ℓ _).le),
    fun n n' _ _ hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu =>
      (h.local_density n n' hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu).trans
        (div_le_div_of_nonneg_right hC (weight_pos_aux ℓ _).le)⟩
private theorem isCurvatureFamily_of_half {E η : ℝ} {f : LocalDensity} (hE : 0 ≤ E) (hη : 0 < η) (hη1 : η ≤ 1)
    (h : HalfDensityBounds ℓ E η f) : IsCurvatureFamily ℓ (E / η) f := by
  have hEη : E ≤ E / η := by
    rw [le_div_iff₀ hη]
    nlinarith
  refine ⟨h.admissible.smooth, h.admissible.gauge, h.admissible.translation,
    fun n _ hn y W hW k c X hk1 hk3 hX => (h.decay n hn y W hW k c X hk1 hk3 hX).trans ?_,
    fun n n' _ _ hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu =>
      (h.compare n n' hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu).trans ?_⟩
  · apply div_le_div_of_nonneg_right _ (weight_pos_aux ℓ _).le
    split_ifs <;> linarith
  · apply div_le_div_of_nonneg_right _ (weight_pos_aux ℓ _).le
    linarith
private theorem isCurvatureFamily_of_termBounds {e e₃ c C : ℝ} {f : LocalDensity} (he : e ≤ C) (he₃ : e₃ ≤ C)
    (hc : c ≤ C) (h : TermBounds ℓ e e₃ c f) : IsCurvatureFamily ℓ C f := by
  refine ⟨h.admissible.smooth, h.admissible.gauge, h.admissible.translation,
    fun n _ hn y W hW k c X hk1 hk3 hX => (h.derivDecay n hn y W hW k c X hk1 hk3 hX).trans ?_,
    fun n n' _ _ hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu =>
      (h.centered_compare n n' hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu).trans ?_⟩
  · apply div_le_div_of_nonneg_right _ (weight_pos_aux ℓ _).le
    split_ifs <;> assumption
  · exact div_le_div_of_nonneg_right hc (weight_pos_aux ℓ _).le
private theorem unitPlaneCurvature_antisymm (μ ν : Fin 4) :
    unitPlaneCurvature μ ν = - unitPlaneCurvature ν μ := by apply _root_.YangMills.SharedProofs.p4715 <;> assumption
private theorem isCold_trivialField (hσ : 0 < ℓ.threshold) (n : ℕ) : IsCold ℓ.threshold (trivialField n) := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.trivialField_isCold <;> assumption
private theorem centered_responseSubShare {L t : ℕ} (a al : ℝ) (P : ColdResponse L t) (n : ℕ) [NeZero n]
    (y : TorusSite n) (W : TorusField n) : centered (responseSubShare a P al) n y W =
      centeredResponse P n y W (constOneWeight _) - al * centered (levelShareFamily a L t) n y W := by
  have hn : n ≠ 0 := NeZero.ne n
  simp only [centered, responseSubShare, responseAtOne, levelShareFamily, dif_neg hn, centeredResponse]
  ring
private theorem sum_centeredResponse_invariant {t : ℕ} {P : ColdResponse ℓ.side t} (hσ : 0 < ℓ.threshold)
    (hP : UnitResponseInvariant ℓ P) {n : ℕ} [NeZero n] (hn : ℓ.n₀ ≤ n) (g : TorusIsometry)
    (W W' : TorusField n) (hW : IsCold ℓ.threshold W) (hc : g.Transports W W') :
    ∑ y, centeredResponse P n y W' (constOneWeight _) = ∑ y, centeredResponse P n y W (constOneWeight _) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.CoeffUniqueness.sum_centeredResponse_invariant <;> assumption
private theorem exists_curvatureForm_of_invariant (hON : InvariantFamilyCurvatureForm) (hf : ℓ.Admissible)
    {C : ℝ} {h : LocalDensity} (H : IsCurvatureFamily ℓ C h) (hc : SumInvariantUnderIsometries ℓ h) :
    ∃ b : ℝ, HasCurvatureForm h b := by
  obtain ⟨hT, b, hb⟩ := hON ℓ hf C h H hc
  exact ⟨b, fun c c' X X' => ⟨_, hT c c' X X'⟩, hb⟩
private theorem curvaturePairing_unitPlane : curvaturePairing unitPlaneCurvature unitPlaneCurvature = 1 := by apply _root_.YangMills.SharedProofs.p11741 <;> assumption
private theorem curvatureForm_of_equal_totals (hON : InvariantFamilyCurvatureForm)
    (hOT : equalTotalsEqualLimitStatement)
    (hf : ℓ.Admissible) {C C' b : ℝ} {h G : LocalDensity} (H : IsCurvatureFamily ℓ C h)
    (hc : SumInvariantUnderIsometries ℓ h) (hb : HasCurvatureForm h b) (HG : IsCurvatureFamily ℓ C' G)
    (ht : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ V : TorusField n, IsCold ℓ.threshold V →
      ∑ y, centered G n y V = ∑ y, centered h n y V) :
    HasCurvatureForm G b := by
  have hcG : SumInvariantUnderIsometries ℓ G := by
    intro n _ hn g W W' hW hW' hg
    rw [ht n hn W hW, ht n hn W' hW']
    exact hc n hn g W W' hW hW' hg
  obtain ⟨b', hb'⟩ := exists_curvatureForm_of_invariant hON hf HG hcG
  have s := hb.2 unitPlaneCurvature unitPlaneCurvature unitPlaneCurvature_antisymm unitPlaneCurvature_antisymm
  have s' := hb'.2 unitPlaneCurvature unitPlaneCurvature unitPlaneCurvature_antisymm unitPlaneCurvature_antisymm
  rw [curvaturePairing_unitPlane, mul_one] at s s'
  have e := hOT ℓ hf (max C C') G h b' b (isCurvatureFamily_mono (le_max_right _ _) HG)
    (isCurvatureFamily_mono (le_max_left _ _) H) ht s' s
  rw [← e]
  exact hb'
end CurvatureFamilies
section AtAStep
variable {R : StepSetup} {A : ResponseSetup R}
private theorem centered_totalRemainderOfTerms (n : ℕ) (y : TorusSite n) (V : TorusField n) :
    centered (totalRemainderOfTerms A) n y V = centered (frameTerm A) n y V + centered (linearTerm A) n y V +
      centered (remainderTerm A) n y V + centered (scoreTailTerm A) n y V + centered (gasTerm A) n y V := by
  simp only [centered, totalRemainderOfTerms]
  ring
private theorem sum_centered_subShare_eq_terms (r : LocalDensity)
    (hSum : ∀ n [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold R.params.threshold V →
      ∑ z, centered (levelShareFamily R.params.coupling R.params.side (R.depth + 1)) n z V =
        actionAtLevel R.params.coupling R.params.side (R.depth + 1) Finset.univ V)
    (total : IsTotalRemainder R.params A.coldStep A.coeff (totalRemainderOfTerms A))
    (hSlope : ∀ n [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold R.params.threshold V →
      ∑ y, centered (linearTerm A) n y V = A.coeff * ∑ y, centered r n y V)
    (n : ℕ) [NeZero n] (hn : R.params.n₀ ≤ n) (V : TorusField n) (hV : IsCold R.params.threshold V) :
    ∑ y, centered (responseSubShare R.params.coupling A.coldStep A.coeff) n y V =
      ∑ i, ∑ y, centered ((![frameTerm A, remainderTerm A, scoreTailTerm A, gasTerm A] :
        Fin 4 → LocalDensity) i) n y V + A.coeff * ∑ y, centered r n y V := by
  have e₁ : ∑ y, centered (responseSubShare R.params.coupling A.coldStep A.coeff) n y V =
      ∑ y, centered (totalRemainderOfTerms A) n y V := by
    simp only [centered_responseSubShare]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hSum n hn V hV, total.sum_eq n hn V hV]
    ring
  rw [e₁, ← hSlope n hn V hV]
  simp only [centered_totalRemainderOfTerms, Finset.sum_add_distrib, Fin.sum_univ_four]
  simp
  ring
private theorem abs_planeValue_le_at_step (hA : SecondOrderAtAbelianFields) (hW : AbelianFieldOfAnglesHasCurvature)
    (hSG : smallFamilyValueStatement) (hf : R.params.Admissible) {Ch b e e₁ e₂ e₃ v B : ℝ} {r : LocalDensity}
    (H : IsCurvatureFamily R.params Ch (responseSubShare R.params.coupling A.coldStep A.coeff))
    (hb : HasCurvatureForm (responseSubShare R.params.coupling A.coldStep A.coeff) b) (he : 0 ≤ e)
    (Pf : TermBounds R.params e e e (frameTerm A)) (Pt : TermBounds R.params e e e (scoreTailTerm A))
    (Pg : TermBounds R.params e e e (gasTerm A)) (Pr : TermBounds R.params e₁ e₂ e₃ (remainderTerm A))
    (hv : HasUnitPlaneValue (remainderTerm A) v)
    (htot : ∀ n [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold R.params.threshold V →
      ∑ y, centered (responseSubShare R.params.coupling A.coldStep A.coeff) n y V =
        ∑ i, ∑ y, centered ((![frameTerm A, remainderTerm A, scoreTailTerm A, gasTerm A] :
          Fin 4 → LocalDensity) i) n y V + A.coeff * ∑ y, centered r n y V)
    (hr : ∀ ε : ℝ, 0 < ε → ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ → ∀ (n : ℕ) [NeZero n],
      8 * Real.log (1 / γ) ^ 2 ≤ n → ∀ (V : TorusField n) (Y : TorusSite n),
        IsAbelianWithCurvature quaternionI unitPlaneMatrix γ V →
        |centered r n Y V| ≤ γ ^ 2 * (B + ε)) :
    |b| ≤ 3 * (e * potentialWeightSum R.params.rt R.params.n₁) + |v| + 2 * |A.coeff| * B := by
  have Ff : IsCurvatureFamily R.params e (frameTerm A) := isCurvatureFamily_of_termBounds le_rfl le_rfl le_rfl Pf
  have Ft : IsCurvatureFamily R.params e (scoreTailTerm A) := isCurvatureFamily_of_termBounds le_rfl le_rfl le_rfl Pt
  have Fg : IsCurvatureFamily R.params e (gasTerm A) := isCurvatureFamily_of_termBounds le_rfl le_rfl le_rfl Pg
  have Fr : IsCurvatureFamily R.params (max e₁ (max e₂ e₃)) (remainderTerm A) :=
    isCurvatureFamily_of_termBounds (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)) Pr
  obtain ⟨w₁, ⟨-, s₁⟩, b₁⟩ := hSG R.params e _ hf he Ff
  obtain ⟨w₂, ⟨-, s₂⟩, b₂⟩ := hSG R.params e _ hf he Ft
  obtain ⟨w₃, ⟨-, s₃⟩, b₃⟩ := hSG R.params e _ hf he Fg
  have hb₀ := hb.2 unitPlaneCurvature unitPlaneCurvature unitPlaneCurvature_antisymm unitPlaneCurvature_antisymm
  rw [curvaturePairing_unitPlane, mul_one] at hb₀
  have key := planeValue_sub_sum_le (m := 4) (C' := ![e, max e₁ (max e₂ e₃), e, e])
    (g := ![frameTerm A, remainderTerm A, scoreTailTerm A, gasTerm A])
    (w := ![w₁, v, w₂, w₃]) (r := r) (al := A.coeff) (B := B) hA hW hf H
    (fun i => by fin_cases i <;> first | exact Ff | exact Fr | exact Ft | exact Fg)
    hb₀ (fun i => by fin_cases i <;> first | exact s₁ | exact hv.2 | exact s₂ | exact s₃) htot hr
  have hsum : ∑ i, (![w₁, v, w₂, w₃] : Fin 4 → ℝ) i = w₁ + v + w₂ + w₃ := by
    simp [Fin.sum_univ_four]
  rw [hsum] at key
  have a1 := abs_sub_abs_le_abs_sub b (w₁ + v + w₂ + w₃)
  have a2 : |w₁ + v + w₂ + w₃| ≤ |w₁| + |v| + |w₂| + |w₃| :=
    (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  linarith
end AtAStep
section Conclusion
private theorem isNormBoundedLocalFamily_of_regular {L t n₀ : ℕ} {σ δ E E₃ : ℝ}
    {f : ColdStepAtMirrorFrames.LocalFamily}
    (h : ColdStepAtMirrorFrames.IsRegularFamily L t n₀ σ δ E E₃ f) :
    IsNormBoundedLocalFamily L t n₀ σ δ E E₃ f :=
  ⟨h.smooth, h.gauge_invariant, h.translation_invariant, h.decay, h.locality⟩
private theorem inv_mul_rpow_neg_half {x : ℝ} (hx : 0 < x) :
    x⁻¹ * x ^ (-(1 / 2) : ℝ) = x ^ (-(3 / 2) : ℝ) := by
  have : x ^ (-(3 / 2) : ℝ) = x ^ (-1 : ℝ) * x ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add hx]
    norm_num
  rw [this, Real.rpow_neg_one]
theorem responseCurvatureCoeff_proof (hShare : responseSubShareBoundsStatement)
    (hParts : responseTermDecompositionStatement)
    (hCar : StepResponseIsometryInvariant) (hLab : ClusterExpansionOfAStep.CoarseLabelsStandard)
    (hSh : LevelSharesFormCurvatureFamily)
    (hON : InvariantFamilyCurvatureForm) (hOT : equalTotalsEqualLimitStatement)
    (hA : SecondOrderAtAbelianFields) (hW : AbelianFieldOfAnglesHasCurvature)
    (hSG : smallFamilyValueStatement) (hRow : ColdStepAtMirrorFrames.ColdExpansionRegular) :
    responseCurvatureCoeffStatement := by
  intro a ha
  obtain ⟨L₁, r₁, hr₁, g₁⟩ := hShare a ha
  obtain ⟨L₂, r₂, hr₂, g₂⟩ := hParts a ha
  obtain ⟨r₃, hr₃, g₃⟩ := hCar
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (min (r₂ c) (r₃ c)),
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (hr₃ c)), fun T hTa hLT hT hCS hOn hrt => ?_⟩
  have t₁ := hrt.trans (min_le_left _ _)
  have u₁ := hrt.trans (min_le_right _ _)
  have t₂ := u₁.trans (min_le_left _ _)
  have t₃ := u₁.trans (min_le_right _ _)
  have l₁ : L₁ ≤ T.side := (le_max_left _ _).trans hLT
  have l₂ : L₂ ≤ T.side := (le_max_right _ _).trans hLT
  obtain ⟨C₂, g₁⟩ := g₁ T hTa l₁ hT hCS hOn t₁
  obtain ⟨Cp, hCp0, g₂⟩ := g₂ T hTa l₂ hT hCS hOn t₂
  obtain ⟨c, nss, hties, hall⟩ := id hOn
  have hH : ColdRegimeEstimatesAt (T.stepParamsAt c nss T.yC) := hall T.yC le_rfl
  refine ⟨C₂, fun K hKa hKb => ?_⟩
  obtain ⟨y₁, g₁⟩ := g₁ K hKa hKb
  obtain ⟨y₂, g₂⟩ := g₂ K hKb
  obtain ⟨y₃, g₃⟩ := g₃ T hT t₃ K
  set B₀ : ℝ := (T.stepParamsAt c nss T.yC).CE *
    doublePotentialSum (T.stepParamsAt c nss T.yC) (curvatureAlong quaternionI unitPlaneMatrix) with hB₀
  refine ⟨3 * (Cp * |potentialWeightSum T.rt T.n₁|) + Cp * K.Kb + 4 * |B₀|,
    max (max y₁ y₂) (max y₃ (max T.floorMin (max T.yC (2 * T.B + 1)))), by positivity,
    fun y hy R A hK hAt hArr => ?_⟩
  have e₀ := (le_max_left _ _).trans hy
  have e₀' := (le_max_right _ _).trans hy
  have e₁ : y₁ ≤ y := (le_max_left _ _).trans e₀
  have e₂ : y₂ ≤ y := (le_max_right _ _).trans e₀
  have e₃ : y₃ ≤ y := (le_max_left _ _).trans e₀'
  have e₄ := (le_max_right _ _).trans e₀'
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans e₄
  have e₅ := (le_max_right _ _).trans e₄
  have hyC : T.yC ≤ y := (le_max_left _ _).trans e₅
  have hyB : 2 * T.B + 1 ≤ y := (le_max_right _ _).trans e₅
  have hR := hAt.onFamily
  have hℓ : R.params = T.stepParameters y := hR.params_eq
  have hxy : y ≤ R.coupling := hR.le_coupling
  have hmv := hAt.abs_sub_le
  have hB1 : 1 ≤ T.B := hT.B_ge
  rw [abs_le] at hmv
  have hx0 : 0 < R.coupling := by linarith
  have hx'0 : 0 < R.nextCoupling := by linarith [hmv.1]
  have hfit : R.params.Admissible := by
    rw [hℓ]
    exact hT.fits y hy0
  have hσ : 0 < R.params.threshold := hfit.σ_pos
  have hresp := hAt.admissible
  have hKf : K.Admissible R.params := hK ▸ hresp.params_admissible
  have hL2 : 2 ≤ R.params.side := by
    have := hfit.L_ge
    omega
  have hhalf := g₁ y e₁ R A hK hAt hArr
  have hE : 0 ≤ K.Ka * R.nextCoupling ^ (-(1 / 2) : ℝ) := mul_nonneg hKf.Ka_nonneg (by positivity)
  have H := isCurvatureFamily_of_half hE hKf.η₃_pos hKf.η₃_le hhalf
  have hcar : UnitResponseInvariant R.params A.coldStep := (g₃ y e₃ R A hK hAt (hLab R hL2) hArr).2.2
  have hSc : SumInvariantUnderIsometries R.params
      (levelShareFamily R.params.coupling R.params.side (R.depth + 1)) := by
    rw [hℓ]
    exact (hSh T hT y hy0 R.depth).2.1
  have hSum : ∀ n [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold R.params.threshold V →
      ∑ z, centered (levelShareFamily R.params.coupling R.params.side (R.depth + 1)) n z V =
        actionAtLevel R.params.coupling R.params.side (R.depth + 1) Finset.univ V := by
    rw [hℓ]
    exact (hSh T hT y hy0 R.depth).2.2
  have hcS : SumInvariantUnderIsometries R.params (responseSubShare R.params.coupling A.coldStep A.coeff) := by
    intro n _ hn g W W' hW hW' hg
    simp only [centered_responseSubShare]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_centeredResponse_invariant hσ hcar hn g W W' hW hg, hSc n hn g W W' hW hW' hg]
  obtain ⟨b, hb⟩ := exists_curvatureForm_of_invariant hON hfit H hcS
  have P := g₂ y e₂ R A hK hAt hArr
  obtain ⟨v, hv, hvb⟩ := P.remainder_planeValue
  have hL : T.side = R.params.side := by
    rw [hℓ]
    rfl
  have hQ : coldHalfLawAt (T.stepParamsAt c nss T.yC) R.coupling
      (ColdStepAtMirrorFrames.localFamilyOfDensity R.density) = coldHalfLawOf R := by
    have e₁ : T.coupling = R.params.coupling := by
      rw [hℓ]
      rfl
    have e₂ : c.ρA = R.anchorRadius := hties.2.2.1.trans hR.anchorRadius_eq.symm
    have e₃ : T.threshold / 64 = R.ballRadius := by
      show T.threshold / 64 = R.params.threshold / 64
      rw [hℓ]
      rfl
    have e₄ : T.rt = R.params.rt := by
      rw [hℓ]
      rfl
    have e₅ : T.cutoff = R.barrierFn := hR.barrierFn_eq.symm
    show ColdHalfLaw.mk T.coupling c.ρA (T.threshold / 64) R.coupling T.rt
        (ColdStepAtMirrorFrames.frameRadius R.coupling) T.cutoff
        (ColdStepAtMirrorFrames.localFamilyOfDensity R.density) =
      ColdHalfLaw.mk R.params.coupling R.anchorRadius R.ballRadius R.coupling R.params.rt R.frameReach
        R.barrierFn (ColdStepAtMirrorFrames.localFamilyOfDensity R.density)
    rw [e₁, e₂, e₃, e₄, e₅]
    rfl
  have hrow : ColdStepAtMirrorFrames.IsRegularFamily (T.stepParamsAt c nss T.yC).L R.depth
      (T.stepParamsAt c nss T.yC).n₀ (T.stepParamsAt c nss T.yC).σ
      (T.stepParamsAt c nss T.yC).decayRate (T.stepParamsAt c nss T.yC).E
      (T.stepParamsAt c nss T.yC).energyRatio (ColdStepAtMirrorFrames.localFamilyOfDensity R.density) := by
    have h := hRow R.params R.depth R.coupling R.functional R.density hfit (by rw [hℓ]; rfl) hR.isStep.1.1
    rw [hℓ] at h
    exact h
  have hfl : (T.stepParamsAt c nss T.yC).coupling ≤ R.coupling := hyC.trans hxy
  have hd : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold R.params.threshold V →
      R.coupling * (coldHalfLawOf R).expectation (coldTopField R V)
        (fun η => (coldHalfLawOf R).totalCost η (coldTopField R V) -
          (coldHalfLawOf R).totalCost 0 (coldTopField R V)) =
      3 / 2 * ((BlockAverages.chordBonds
          (ColdStepAtMirrorFrames.finiteCells (torusFrame R.params.side R.depth n))).card : ℝ) +
        R.coupling * ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells (torusFrame R.params.side R.depth n),
          (coldHalfLawOf R).dilationRemainder Y (coldTopField R V) := by
    intro n _ hn V hV
    have hst : IsAdmissibleAt (T.stepParamsAt c nss T.yC) R.depth R.coupling
        (ColdStepAtMirrorFrames.localFamilyOfDensity R.density) (torusFrame R.params.side R.depth n)
        (coldTopField R V) := by
      refine ⟨hfl, isNormBoundedLocalFamily_of_regular hrow, ⟨hL.symm, rfl, n, fun _ => rfl, ?_⟩, ?_⟩
      · have : R.params.n₀ = T.n₀ := by
          rw [hℓ]
          rfl
        show T.n₀ ≤ n
        omega
      · refine isSmallCurvature_readAtLevel
          (fun i => period_top (H := torusFrame R.params.side R.depth n) (fun _ => rfl) i) ?_ hV
        have : R.params.threshold = T.threshold := by
          rw [hℓ]
          rfl
        rw [this]
        have := hT.σ_pos
        show T.threshold ≤ 5 / 4 * T.threshold
        linarith
    have h := hH.dilation R.depth R.coupling (ColdStepAtMirrorFrames.localFamilyOfDensity R.density)
      (torusFrame R.params.side R.depth n) (coldTopField R V) hst hrow
    rw [hQ] at h
    exact h
  have hrq : ∀ (n : ℕ) [NeZero n] (Y : TorusSite n) (V : TorusField n),
      dilationRemainderDensity (T.stepParamsAt c nss T.yC) R.depth R.coupling
          (ColdStepAtMirrorFrames.localFamilyOfDensity R.density) n Y V =
        (coldHalfLawOf R).dilationRemainder
          (StepCosts.torusSiteInFrame (torusFrame R.params.side R.depth n)
            (torusFrame R.params.side R.depth n).top Y) (coldTopField R V) := by
    intro n _ Y V
    show ColdStepAtMirrorFrames.densityOfTopFamily T.side R.depth
      (fun _ Y V => (coldHalfLawAt (T.stepParamsAt c nss T.yC) R.coupling
        (ColdStepAtMirrorFrames.localFamilyOfDensity R.density)).dilationRemainder Y V) n Y V = _
    rw [hQ, hL]
    rfl
  have hSlope : ∀ n [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold R.params.threshold V →
      ∑ y, centered (linearTerm A) n y V =
        A.coeff * ∑ y, centered (dilationRemainderDensity (T.stepParamsAt c nss T.yC) R.depth R.coupling
          (ColdStepAtMirrorFrames.localFamilyOfDensity R.density)) n y V := by
    intro n _ hn V hV
    have hfc := isCold_trivialField hσ n
    have s₁ := P.linear_sum n hn V hV
    have s₂ := P.linear_sum n hn (trivialField n) hfc
    have d₁ := hd n hn V hV
    have d₂ := hd n hn (trivialField n) hfc
    have c₁ := sum_torus_eq_sum_finiteCells (L := R.params.side) (t := R.depth) (n := n)
      fun Y => (coldHalfLawOf R).dilationRemainder Y (coldTopField R V)
    have c₂ := sum_torus_eq_sum_finiteCells (L := R.params.side) (t := R.depth) (n := n)
      fun Y => (coldHalfLawOf R).dilationRemainder Y (coldTopField R (trivialField n))
    simp only [centered, Finset.sum_sub_distrib, hrq]
    rw [s₁, s₂, c₁, c₂]
    have hx : R.coupling ≠ 0 := hx0.ne'
    have key : R.coupling * ((coldHalfLawOf R).expectation (coldTopField R V)
          (fun η => (coldHalfLawOf R).totalCost η (coldTopField R V) -
            (coldHalfLawOf R).totalCost 0 (coldTopField R V)) -
        (coldHalfLawOf R).expectation (coldTopField R (trivialField n))
          (fun η => (coldHalfLawOf R).totalCost η (coldTopField R (trivialField n)) -
            (coldHalfLawOf R).totalCost 0 (coldTopField R (trivialField n)))) =
        R.coupling * (∑ Y ∈ ColdStepAtMirrorFrames.finiteCells (torusFrame R.params.side R.depth n),
            (coldHalfLawOf R).dilationRemainder Y (coldTopField R V) -
          ∑ Y ∈ ColdStepAtMirrorFrames.finiteCells (torusFrame R.params.side R.depth n),
            (coldHalfLawOf R).dilationRemainder Y (coldTopField R (trivialField n))) := by
      rw [mul_sub, mul_sub, d₁, d₂]
      ring
    have hcancelled' := mul_left_cancel₀ hx key
    rw [← mul_sub, hcancelled']
  have htot := sum_centered_subShare_eq_terms (A := A)
    (dilationRemainderDensity (T.stepParamsAt c nss T.yC) R.depth R.coupling
      (ColdStepAtMirrorFrames.localFamilyOfDensity R.density)) hSum P.isTotalRemainder hSlope
  have hsize := abs_planeValue_le_at_step (A := A) (B := B₀ * R.coupling ^ (-(3 / 2) : ℝ)) hA hW hSG hfit H hb
    (by positivity) P.frame_bounds P.scoreTail_bounds P.gas_bounds P.remainder_bounds hv htot
    (hH.atCurvature R.depth R.coupling (ColdStepAtMirrorFrames.localFamilyOfDensity R.density) quaternionI
      unitPlaneMatrix hfl hrow norm_quaternionI unitPlaneMatrix_antisymm)
  refine ⟨b, ?_, hb, fun G hG hTG => ?_⟩
  · have hp : 0 ≤ R.coupling ^ (-(3 / 2) : ℝ) := by positivity
    have hS : potentialWeightSum R.params.rt R.params.n₁ = potentialWeightSum T.rt T.n₁ := by
      rw [hℓ]
      rfl
    rw [hS] at hsize
    have hal : |A.coeff| ≤ 2 := hresp.abs_coeff_le
    have hv' : |v| ≤ Cp * K.Kb * R.coupling ^ (-(3 / 2) : ℝ) := by
      refine hvb.trans (le_of_eq ?_)
      rw [hK, ← inv_mul_rpow_neg_half hx0]
      field_simp
    have a₁ : Cp * R.coupling ^ (-(3 / 2) : ℝ) * potentialWeightSum T.rt T.n₁ ≤
        Cp * |potentialWeightSum T.rt T.n₁| * R.coupling ^ (-(3 / 2) : ℝ) := by
      have := mul_le_mul_of_nonneg_left (le_abs_self (potentialWeightSum T.rt T.n₁)) (mul_nonneg hCp0 hp)
      linarith
    have a₂ : 2 * |A.coeff| * (B₀ * R.coupling ^ (-(3 / 2) : ℝ)) ≤ 4 * |B₀| * R.coupling ^ (-(3 / 2) : ℝ) := by
      have b₁ : B₀ * R.coupling ^ (-(3 / 2) : ℝ) ≤ |B₀| * R.coupling ^ (-(3 / 2) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hp
      have b₂ : 0 ≤ |B₀| * R.coupling ^ (-(3 / 2) : ℝ) := by positivity
      have b₃ : 2 * |A.coeff| * (B₀ * R.coupling ^ (-(3 / 2) : ℝ)) ≤
          2 * |A.coeff| * (|B₀| * R.coupling ^ (-(3 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left b₁ (by positivity)
      linarith [mul_le_mul_of_nonneg_right hal b₂]
    calc |b| ≤ _ := hsize
      _ ≤ _ := by linarith [a₁, hv', a₂]
  · have hE' : 0 ≤ K.Kb * R.nextCoupling⁻¹ := mul_nonneg hKf.Kb_nonneg (by positivity)
    have HG := isCurvatureFamily_of_half hE' hKf.η₃_pos hKf.η₃_le hG
    refine curvatureForm_of_equal_totals hON hOT hfit H hcS hb HG fun n _ hn V hV => ?_
    simp only [centered_responseSubShare]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hSum n hn V hV, hTG.sum_eq n hn V hV]
    ring
end Conclusion
end YangMills.Construction.ResponseInTheExpansion.ResponseCoefficient
end
