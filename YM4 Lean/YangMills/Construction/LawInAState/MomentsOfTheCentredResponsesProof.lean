import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import YangMills.Construction.FreeEnergiesOfTheFlow.FittedResponsesAreMeans
import YangMills.Construction.FreeEnergiesOfTheFlow.ProductsAreHad
import YangMills.Construction.FreeEnergiesOfTheFlow.StatesAlongTheFlowAreGrounds
import YangMills.Construction.LawInAState.MomentsOfTheCentredResponses
import YangMills.Construction.LawInAState.ResponsesAlongTheChainAreBounded
import YangMills.Construction.LawInAState.SitesOfATranslate
import YangMills.Construction.LawInAState.TheCouplingOfTheLevelGrows
import YangMills.Construction.LawInAState.TheLevelOfTheLaw
import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPiecesProof
import YangMills.Construction.ResponseInTheExpansion.ResponseAlongIsTheMeanOfTheMark
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.ResponseInTheExpansion.TwoPointFunctionByTotalCovariance
import YangMills.Construction.TransfersOffTheWalk.MomentsOfTheMajorants
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace YangMills.Construction.StateLaws
open TorusLumps TorusFields RenormalizationStepParameters StepReturn WeightedResponses ResponseInTheExpansion FreeEnergies BoxResponses BoxMarks
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
open TestFunctions (closedBallR4)
private lemma memLp_sub_integral_of_eLpNorm_sub_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} {κ D : ℝ} (hD : 0 ≤ D) (hF : MemLp F 64 μ) (hb : eLpNorm (fun u => F u - κ) 64 μ ≤ ENNReal.ofReal D) :
    MemLp (fun u => F u - ∫ w, F w ∂μ) 64 μ ∧ eLpNorm (fun u => F u - ∫ w, F w ∂μ) 64 μ ≤ ENNReal.ofReal (2 * D) := by
  have hG : MemLp (fun u => F u - κ) 64 μ := hF.sub (memLp_const κ)
  have hFi : Integrable F μ := hF.integrable (by norm_num)
  have e1 : ∫ u, (F u - κ) ∂μ = (∫ w, F w ∂μ) - κ := by
    rw [integral_sub hFi (integrable_const κ)]
    simp
  have h1 : eLpNorm (fun u => F u - κ) 1 μ ≤ ENNReal.ofReal D :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hG.1).trans hb
  have h2 : |∫ u, (F u - κ) ∂μ| ≤ D := by
    have a1 : |∫ u, (F u - κ) ∂μ| ≤ ∫ u, ‖F u - κ‖ ∂μ := abs_integral_le_integral_abs
    have a2 : ∫ u, ‖F u - κ‖ ∂μ = (eLpNorm (fun u => F u - κ) 1 μ).toReal := by
      rw [integral_norm_eq_lintegral_enorm hG.1, eLpNorm_one_eq_lintegral_enorm]
    rw [a2] at a1
    exact a1.trans (ENNReal.toReal_le_of_le_ofReal hD h1)
  refine ⟨hF.sub (memLp_const _), ?_⟩
  have e2 : (fun u => F u - ∫ w, F w ∂μ) = (fun u => F u - κ) - fun _ => ∫ u, (F u - κ) ∂μ := by
    funext u
    simp only [Pi.sub_apply]
    rw [e1]
    ring
  rw [e2]
  refine (eLpNorm_sub_le hG.1 aestronglyMeasurable_const (by norm_num)).trans ?_
  have h3 : eLpNorm (fun _ : Ω => ∫ u, (F u - κ) ∂μ) 64 μ ≤ ENNReal.ofReal D := by
    have := eLpNorm_le_of_ae_bound (μ := μ) (p := 64) (f := fun _ : Ω => ∫ u, (F u - κ) ∂μ) (C := D)
      (Eventually.of_forall fun _ => by simpa [Real.norm_eq_abs] using h2)
    simpa using this
  calc _ ≤ ENNReal.ofReal D + ENNReal.ofReal D := add_le_add hb h3
    _ = ENNReal.ofReal (2 * D) := by rw [← ENNReal.ofReal_add hD hD, two_mul]
abbrev _root_.YangMills.SharedProofs.p1187 := @memLp_sub_integral_of_eLpNorm_sub_le
private lemma eLpNorm_le_of_integral_pow_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : Ω → ℝ} {A : ℝ} (hA : 1 ≤ A)
    (hI : Integrable (fun u => N u ^ 64) μ) (hb : ∫ u, N u ^ 64 ∂μ ≤ A) : eLpNorm N 64 μ ≤ ENNReal.ofReal A := by
  have h64 : ((64 : ℝ≥0∞)).toReal = 64 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h64]
  have e1 : ∀ u, ‖N u‖ₑ ^ (64 : ℝ) = ENNReal.ofReal (N u ^ 64) := by
    intro u
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    congr 1
    have : (64 : ℝ) = ((64 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]
    exact Even.pow_abs (by decide) _
  have e2 : ∫⁻ u, ‖N u‖ₑ ^ (64 : ℝ) ∂μ ≤ ENNReal.ofReal A := by
    simp_rw [e1]
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun u => Even.pow_nonneg (by decide) _)]
    exact ENNReal.ofReal_le_ofReal hb
  have hA0 : 0 < A := by linarith
  calc (∫⁻ u, ‖N u‖ₑ ^ (64 : ℝ) ∂μ) ^ (1 / (64 : ℝ)) ≤ ENNReal.ofReal A ^ (1 / (64 : ℝ)) :=
        ENNReal.rpow_le_rpow e2 (by norm_num)
    _ = ENNReal.ofReal (A ^ (1 / (64 : ℝ))) := ENNReal.ofReal_rpow_of_pos hA0
    _ ≤ ENNReal.ofReal A := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := Real.rpow_le_rpow_of_exponent_le hA (by norm_num : (1 / (64 : ℝ)) ≤ 1)
        simpa using this
abbrev _root_.YangMills.SharedProofs.p13787 := @eLpNorm_le_of_integral_pow_le
private lemma abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (i : Fin 4) : |v i| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private lemma euclidNormVec_le_two_mul (v : Fin 4 → ℝ) {t : ℝ} (ht : 0 ≤ t) (h : ∀ i, |v i| ≤ t) :
    euclidNormVec v ≤ 2 * t := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
private lemma period_eq_of_support_small {g : AmbientSpace → ℝ} {c : AmbientSpace} {d : ℝ} (hd : d < 1 / 4)
    (hs : ∀ x, g x ≠ 0 → euclidNormVec (x - c) ≤ d)
    {e e' : AmbientSpace} {w w' : Fin 4 → ℤ} (he : ∀ i, |e i - e' i| ≤ 1) (h : g (fun i => e i + 2 * (w i : ℝ)) ≠ 0)
    (h' : g (fun i => e' i + 2 * (w' i : ℝ)) ≠ 0) : w = w' := by
  funext i
  have a1 := abs_apply_le_euclidNormVec _ i |>.trans (hs _ h)
  have a2 := abs_apply_le_euclidNormVec _ i |>.trans (hs _ h')
  simp only [Pi.sub_apply] at a1 a2
  have b1 := abs_le.1 a1
  have b2 := abs_le.1 a2
  have b3 := abs_le.1 (he i)
  have c1 : |((w i - w' i : ℤ) : ℝ)| < 1 := by
    push_cast
    rw [abs_lt]
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2]
  have c2 : |w i - w' i| < 1 := by exact_mod_cast c1
  have := Int.abs_lt_one_iff.1 c2
  omega
private lemma exists_single_nonzero_period {g : AmbientSpace → ℝ} {c : AmbientSpace} {d : ℝ} (hd : d < 1 / 4)
    (hs : ∀ x, g x ≠ 0 → euclidNormVec (x - c) ≤ d)
    (a b : AmbientSpace) (hab : ∀ i, |a i - b i| ≤ 1) : ∃ z₀ : Fin 4 → ℤ, ∀ z, z ≠ z₀ →
      g (fun i => a i + 2 * (z i : ℝ)) = 0 ∧ g (fun i => b i + 2 * (z i : ℝ)) = 0 := by
  have haa : ∀ i, |a i - a i| ≤ 1 := fun i => by simp
  have hbb : ∀ i, |b i - b i| ≤ 1 := fun i => by simp
  have hba : ∀ i, |b i - a i| ≤ 1 := fun i => by rw [abs_sub_comm]; exact hab i
  by_cases hex : ∃ z : Fin 4 → ℤ, g (fun i => a i + 2 * (z i : ℝ)) ≠ 0 ∨ g (fun i => b i + 2 * (z i : ℝ)) ≠ 0
  · obtain ⟨z₀, h₀⟩ := hex
    refine ⟨z₀, fun z hz => ?_⟩
    constructor
    · by_contra hn
      apply hz
      rcases h₀ with h₀ | h₀
      · exact period_eq_of_support_small hd hs haa hn h₀
      · exact period_eq_of_support_small hd hs hab hn h₀
    · by_contra hn
      apply hz
      rcases h₀ with h₀ | h₀
      · exact period_eq_of_support_small hd hs hba hn h₀
      · exact period_eq_of_support_small hd hs hbb hn h₀
  · have hex' : ∀ z : Fin 4 → ℤ, g (fun i => a i + 2 * (z i : ℝ)) = 0 ∧ g (fun i => b i + 2 * (z i : ℝ)) = 0 := fun z => by
      by_contra hn
      exact hex ⟨z, by tauto⟩
    exact ⟨0, fun z _ => hex' z⟩
private lemma periodizeUnitTorus_eq_single {g : AmbientSpace → ℝ} {a : AmbientSpace} {z₀ : Fin 4 → ℤ}
    (h : ∀ z, z ≠ z₀ → g (fun i => a i + 2 * (z i : ℝ)) = 0) :
    periodizeUnitTorus g a = g (fun i => a i + 2 * (z₀ i : ℝ)) :=
  finsum_eq_single _ z₀ h
private lemma periodizeUnitTorus_shift (g : AmbientSpace → ℝ) (a : AmbientSpace) (w : Fin 4 → ℤ) :
    periodizeUnitTorus g (fun i => a i + 2 * (w i : ℝ)) = periodizeUnitTorus g a := by
  unfold periodizeUnitTorus
  refine Eq.trans ?_ (finsum_comp_equiv (Equiv.addRight w) (f := fun z : Fin 4 → ℤ => g fun i => a i + 2 * (z i : ℝ)))
  congr 1
  funext z
  congr 1
  funext i
  simp only [Equiv.coe_addRight, Pi.add_apply, Int.cast_add]
  ring
abbrev _root_.YangMills.SharedProofs.p63249 := @periodizeUnitTorus_shift
private lemma weightNorm_unitTorusWeight_le {L K k : ℕ} [NeZero L] (hk : k ≤ K) {g : AmbientSpace → ℝ} {c : AmbientSpace}
    {d Lp : ℝ} (hd : d < 1 / 4) (hs : ∀ x, g x ≠ 0 → euclidNormVec (x - c) ≤ d) (hLp : 0 ≤ Lp)
    (hlip : ∀ x y, |g x - g y| ≤ Lp * euclidNormVec (x - y)) (hsup : ∀ x, |g x| ≤ 1)
    (hsmall : 2 * Lp * (L : ℝ) ^ k ≤ (L : ℝ) ^ K) : weightNorm L k (unitTorusWeight L K k g) ≤ 1 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLK : (0 : ℝ) < (L : ℝ) ^ K := pow_pos hLpos K
  have hM : 2 * fineSide L k (boxSide L K k) = 4 * L ^ K := by
    rw [fineSide_eq]
    unfold boxSide
    have : L ^ (K - k) * L ^ k = L ^ K := by
      rw [← pow_add]
      congr 1
      omega
    calc 2 * (2 * L ^ (K - k) * L ^ k) = 4 * (L ^ (K - k) * L ^ k) := by ring
      _ = 4 * L ^ K := by rw [this]
  unfold weightNorm
  refine max_le (Real.iSup_le (fun p => ?_) zero_le_one) (Real.iSup_le (fun pp => ?_) zero_le_one)
  · obtain ⟨z₀, hz⟩ := exists_single_nonzero_period hd hs (fun i => ((doubledBarycentre p.1 i).val : ℝ) / (2 * (L : ℝ) ^ K))
      (fun i => ((doubledBarycentre p.1 i).val : ℝ) / (2 * (L : ℝ) ^ K)) (fun i => by simp)
    have e : unitTorusWeight L K k g p.1 = _ := periodizeUnitTorus_eq_single fun z hne => (hz z hne).1
    rw [e]
    exact hsup _
  · obtain ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩ := pp
    dsimp only
    unfold barycentreDist
    have : NeZero (2 * fineSide L k (boxSide L K k)) := ⟨mul_ne_zero two_ne_zero (NeZero.ne _)⟩
    obtain ⟨D, hDdef⟩ : ∃ D : ℕ, D = supDist (doubledBarycentre p) (doubledBarycentre p') := ⟨_, rfl⟩
    rw [← hDdef]
    rcases Nat.eq_zero_or_pos D with hD0 | hD0
    · simp [hD0]
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD0
    rw [div_le_one (by positivity)]
    obtain ⟨a, ha⟩ : ∃ a : AmbientSpace, a = fun i => ((doubledBarycentre p i).val : ℝ) / (2 * (L : ℝ) ^ K) := ⟨_, rfl⟩
    obtain ⟨b', hb'⟩ : ∃ b' : AmbientSpace, b' = fun i => ((doubledBarycentre p' i).val : ℝ) / (2 * (L : ℝ) ^ K) :=
      ⟨_, rfl⟩
    have key : ∀ i, ∃ w : ℤ, |a i - (b' i + 2 * (w : ℝ))| ≤ 1 ∧
        |a i - (b' i + 2 * (w : ℝ))| ≤ (D : ℝ) / (2 * (L : ℝ) ^ K) := by
      intro i
      obtain ⟨A, hA⟩ : ∃ A, A = doubledBarycentre p i := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B, B = doubledBarycentre p' i := ⟨_, rfl⟩
      obtain ⟨t, ht⟩ : ∃ t : ℤ, t = (A - B).valMinAbs := ⟨_, rfl⟩
      have ht1 : t.natAbs ≤ D := by
        rw [hDdef, ht, hA, hB]
        exact Finset.le_sup (f := fun i => ((doubledBarycentre p i - doubledBarycentre p' i).valMinAbs).natAbs)
          (Finset.mem_univ i)
      have ht2 : t.natAbs ≤ 2 * fineSide L k (boxSide L K k) / 2 := by
        rw [ht]
        exact ZMod.natAbs_valMinAbs_le _
      have hcast : ((t : ℤ) : ZMod (2 * fineSide L k (boxSide L K k))) = A - B := by
        rw [ht]
        exact ZMod.coe_valMinAbs _
      have hdvd : ((2 * fineSide L k (boxSide L K k) : ℕ) : ℤ) ∣ (A.val : ℤ) - (B.val : ℤ) - t := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hcast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        ring
      obtain ⟨w, hw⟩ := hdvd
      have hMZ : ((2 * fineSide L k (boxSide L K k) : ℕ) : ℤ) = 4 * (L : ℤ) ^ K := by exact_mod_cast hM
      have hw2 : (A.val : ℤ) - (B.val : ℤ) - t = 4 * (L : ℤ) ^ K * w := by rw [hw, hMZ]
      have hw3 : (A.val : ℝ) - (B.val : ℝ) - (t : ℝ) = 4 * (L : ℝ) ^ K * (w : ℝ) := by exact_mod_cast hw2
      refine ⟨w, ?_⟩
      have e : a i - (b' i + 2 * (w : ℝ)) = (t : ℝ) / (2 * (L : ℝ) ^ K) := by
        rw [ha, hb']
        dsimp only
        rw [← hA, ← hB]
        field_simp
        linarith
      have ht3 : |(t : ℝ)| ≤ (D : ℝ) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs]
        exact_mod_cast ht1
      have ht4 : |(t : ℝ)| ≤ 2 * (L : ℝ) ^ K := by
        have h1 : t.natAbs ≤ 2 * L ^ K := by
          have : 2 * fineSide L k (boxSide L K k) / 2 = 2 * L ^ K := by
            rw [hM]
            omega
          omega
        rw [← Int.cast_abs, Int.abs_eq_natAbs]
        exact_mod_cast h1
      rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ K)]
      refine ⟨(div_le_one (by positivity)).2 ht4, ?_⟩
      exact div_le_div_of_nonneg_right ht3 (by positivity)
    choose w hw1 hw2 using key
    obtain ⟨b, hb⟩ : ∃ b : AmbientSpace, b = fun i => b' i + 2 * (w i : ℝ) := ⟨_, rfl⟩
    obtain ⟨z₀, hz⟩ := exists_single_nonzero_period hd hs a b (fun i => by rw [hb]; exact hw1 i)
    have e1 : unitTorusWeight L K k g p = g (fun i => a i + 2 * (z₀ i : ℝ)) := by
      have : unitTorusWeight L K k g p = periodizeUnitTorus g a := by rw [ha]; rfl
      rw [this]
      exact periodizeUnitTorus_eq_single fun z hne => (hz z hne).1
    have e2 : unitTorusWeight L K k g p' = g (fun i => b i + 2 * (z₀ i : ℝ)) := by
      have : unitTorusWeight L K k g p' = periodizeUnitTorus g b' := by rw [hb']; rfl
      rw [this, ← periodizeUnitTorus_shift g b' w, ← hb]
      exact periodizeUnitTorus_eq_single fun z hne => (hz z hne).2
    rw [e1, e2]
    have h1 : euclidNormVec ((fun i => a i + 2 * (z₀ i : ℝ)) - fun i => b i + 2 * (z₀ i : ℝ)) ≤
        2 * ((D : ℝ) / (2 * (L : ℝ) ^ K)) := by
      refine euclidNormVec_le_two_mul _ (by positivity) fun i => ?_
      have : ((fun i => a i + 2 * (z₀ i : ℝ)) - fun i => b i + 2 * (z₀ i : ℝ)) i = a i - (b' i + 2 * (w i : ℝ)) := by
        simp only [Pi.sub_apply, hb]
        ring
      rw [this]
      exact hw2 i
    refine (hlip _ _).trans ((mul_le_mul_of_nonneg_left h1 hLp).trans ?_)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have h2 : Lp * (2 * ((D : ℝ) * (2 * (L : ℝ) ^ K)⁻¹)) = (D : ℝ) * (Lp / (L : ℝ) ^ K) := by
      field_simp
    rw [h2]
    refine mul_le_mul_of_nonneg_left ?_ hDr.le
    rw [div_le_iff₀ hLK, inv_eq_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
abbrev _root_.YangMills.SharedProofs.p33283 := @weightNorm_unitTorusWeight_le
private lemma card_le_of_subset_supBall {N : ℕ} [NeZero N] {W : Finset (TorusSite N)} {o : TorusSite N} {r : ℝ}
    (hr : 0 ≤ r) (hW : W ⊆ supBall o r) : (W.card : ℝ) ≤ (2 * r + 1) ^ 4 := by
  have hinj : ∀ b b' : ZMod N, b.valMinAbs = b'.valMinAbs → b = b' := fun b b' h => by
    rw [← ZMod.coe_valMinAbs b, ← ZMod.coe_valMinAbs b', h]
  have h1 := Finset.card_le_card_of_injOn (s := W)
    (t := Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(⌊r⌋₊ : ℤ)) ⌊r⌋₊) (fun z i => (z i - o i).valMinAbs)
    (fun z hz => by
      have hz' : (supDist z o : ℝ) ≤ r := (Finset.mem_filter.1 (hW hz)).2
      have hz2 : supDist z o ≤ ⌊r⌋₊ := Nat.le_floor hz'
      refine Fintype.mem_piFinset.2 fun i => ?_
      have h3 : ((z i - o i).valMinAbs).natAbs ≤ supDist z o :=
        Finset.le_sup (f := fun i => ((z i - o i).valMinAbs).natAbs) (Finset.mem_univ i)
      rw [Finset.mem_Icc]
      dsimp only
      omega)
    (fun z _ z' _ h => by
      funext i
      have := hinj _ _ (congrFun h i)
      exact sub_left_injective this)
  have h2 : W.card ≤ (2 * ⌊r⌋₊ + 1) ^ 4 := by
    refine h1.trans (le_of_eq ?_)
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  have h3 : (W.card : ℝ) ≤ (2 * (⌊r⌋₊ : ℝ) + 1) ^ 4 := by exact_mod_cast h2
  refine h3.trans (pow_le_pow_left₀ (by positivity) ?_ 4)
  have := Nat.floor_le hr
  linarith
abbrev _root_.YangMills.SharedProofs.p83740 := @card_le_of_subset_supBall
private lemma weightNorm_translate_le {L K k : ℕ} [NeZero L] (hk : k ≤ K) {g : AmbientSpace → ℝ} {c : AmbientSpace}
    {d vt : ℝ} (hd0 : 0 < d) (hd : d < 1 / 4) (hvt : 0 < vt)
    (hslope : ∀ x x', |g x - g x'| ≤ euclidNormVec (x - x') / (vt * d)) (hball : tsupport g ⊆ closedBallR4 c d)
    (habs : ∀ x, |g x| ≤ 1) (hn : 2 / vt ≤ lengthInSites L K k d) (v : Fin 4 → ℤ) :
    weightNorm L k (unitTorusWeight L K k (translateBy L K k v g)) ≤ 1 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLp0 : 0 ≤ 1 / (vt * d) := by positivity
  refine weightNorm_unitTorusWeight_le hk (c := c + latticeShift L K k v) (Lp := 1 / (vt * d)) hd ?_ hLp0 ?_ ?_ ?_
  · intro x hx
    have h1 : x - latticeShift L K k v ∈ tsupport g := subset_tsupport g hx
    have h2 := hball h1
    have e : x - (c + latticeShift L K k v) = x - latticeShift L K k v - c := by abel
    rw [e]
    exact h2
  · intro x y
    have h1 := hslope (x - latticeShift L K k v) (y - latticeShift L K k v)
    have e : x - latticeShift L K k v - (y - latticeShift L K k v) = x - y := by abel
    rw [e] at h1
    refine h1.trans (le_of_eq ?_)
    ring
  · intro x
    exact habs _
  · have e : (L : ℝ) ^ K = (L : ℝ) ^ k * (L : ℝ) ^ (K - k) := by
      rw [← pow_add]
      congr 1
      omega
    unfold lengthInSites at hn
    rw [e]
    have hk0 : (0 : ℝ) < (L : ℝ) ^ k := pow_pos hLpos k
    have h3 : 2 * (1 / (vt * d)) ≤ (L : ℝ) ^ (K - k) := by
      have : 2 * (1 / (vt * d)) = 2 / vt / d := by field_simp
      rw [this, div_le_iff₀ hd0]
      linarith
    nlinarith
private lemma sideBelow_eq (L j n : ℕ) : TransfersOffTheWalk.sideBelow L j n = n * L ^ j := by
  induction j generalizing n with
  | zero => simp [TransfersOffTheWalk.sideBelow]
  | succ j ih =>
    rw [TransfersOffTheWalk.sideBelow, ih, pow_succ]
    ring
abbrev _root_.YangMills.SharedProofs.p47689 := @sideBelow_eq
private lemma followsFlow_mono {Tb : ParameterAssignment} {y : ℝ} {T : StageTower (Tb.stepParameters y)}
    {S : ScoredStageTower T} {β : ℝ} {tp tq : ℕ} (h : S.FollowsFlow β tp) (hq : tq ≤ tp) : S.FollowsFlow β tq :=
  { h with
    isFlowStep := fun u hu => h.isFlowStep u (hu.trans hq)
    score_succ := fun u hu => h.score_succ u (lt_of_lt_of_le hu hq)
    cold_succ := fun u hu => h.cold_succ u (lt_of_lt_of_le hu hq)
    hull_succ := fun u hu => h.hull_succ u (lt_of_lt_of_le hu hq)
    isAdmissible := fun u hu => h.isAdmissible u (hu.trans hq)
    coeff_near_one := fun u hu => h.coeff_near_one u (hu.trans hq) }
abbrev _root_.YangMills.SharedProofs.p16981 := @followsFlow_mono
private lemma eLpNorm_meanSiteScore_le {ℓ : StepParameters} {T : StageTower ℓ} {S : ScoredStageTower T} {β : ℝ} {k : ℕ}
    (N : ℕ) [NeZero N] (B : Finset (TorusSite N)) {A : ℝ} (hA : 1 ≤ A)
    (hI : Integrable (fun u => ∏ _i : Fin 64,
        meanSiteScore (S.setup k).score B (stageState T k N u).2.1 (stageState T k N u).2.2)
      (markedSampleLaw T β k N))
    (hb : ∫ u, ∏ _i : Fin 64, meanSiteScore (S.setup k).score B (stageState T k N u).2.1 (stageState T k N u).2.2
      ∂(markedSampleLaw T β k N) ≤ A) :
    eLpNorm (fun u => meanSiteScore (S.setup k).score B (stageState T k N u).2.1 (stageState T k N u).2.2) 64
      (markedSampleLaw T β k N) ≤ ENNReal.ofReal A := by
  refine eLpNorm_le_of_integral_pow_le hA ?_ ?_
  · simpa [Finset.prod_const, Finset.card_univ] using hI
  · simpa [Finset.prod_const, Finset.card_univ] using hb
section Response
variable {ℓ : StepParameters}
private lemma siteScore_nonneg {Ω : Type} {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) {n : ℕ} (Y : Finset (TorusSite n))
    (ω : Y → Ω) (y : TorusSite n) : 0 ≤ siteScore s Y ω y := by
  unfold siteScore
  split_ifs
  · exact hs _
  · exact le_rfl
abbrev _root_.YangMills.SharedProofs.p22275 := @siteScore_nonneg
private lemma sum_mul_sum_bond_ends {n : ℕ} [NeZero n] (h : TorusSite n → ℝ) (A : TorusBond n → ℝ) :
    ∑ Y : TorusSite n, h Y * ∑ i : Fin 4, (A (Y, i) + A (Y - unitStep n i, i)) =
      ∑ c : TorusBond n, (h c.1 + h (c.1 + unitStep n c.2)) * A c := by
  have e : ∀ i : Fin 4, ∑ Y : TorusSite n, h Y * A (Y - unitStep n i, i) =
      ∑ Y : TorusSite n, h (Y + unitStep n i) * A (Y, i) := by
    intro i
    rw [← Equiv.sum_comp (Equiv.addRight (unitStep n i))]
    refine Finset.sum_congr rfl fun Y _ => ?_
    simp
  rw [Fintype.sum_prod_type]
  calc ∑ Y : TorusSite n, h Y * ∑ i : Fin 4, (A (Y, i) + A (Y - unitStep n i, i))
      = ∑ Y : TorusSite n, ∑ i : Fin 4, h Y * A (Y, i) +
          ∑ Y : TorusSite n, ∑ i : Fin 4, h Y * A (Y - unitStep n i, i) := by
        simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    _ = ∑ Y : TorusSite n, ∑ i : Fin 4, h Y * A (Y, i) +
          ∑ Y : TorusSite n, ∑ i : Fin 4, h (Y + unitStep n i) * A (Y, i) := by
        congr 1
        rw [Finset.sum_comm]
        simp only [e]
        rw [Finset.sum_comm]
    _ = ∑ Y : TorusSite n, ∑ i : Fin 4, (h Y + h (Y + unitStep n i)) * A (Y, i) := by
        simp only [add_mul, Finset.sum_add_distrib]
abbrev _root_.YangMills.SharedProofs.p11136 := @sum_mul_sum_bond_ends
private lemma stepSourceTerm_eq (x al : ℝ) (s : ℕ) {n : ℕ} [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n))
    (W : TorusField (n * ℓ.side)) (d : StepOutcome ℓ n) :
    stepSourceTerm ℓ x al s h W d =
      ∑ c : TorusBond n, ℓ.coupling * al * bondBlockMean ℓ.side (s + 1) n h c * bondScore ℓ x W d.2.1 d.1 c := by
  unfold stepSourceTerm bondBlockMean
  rw [sum_mul_sum_bond_ends (fun Y => blockMean ℓ.side (s + 1) n Y h) (fun c => bondScore ℓ x W d.2.1 d.1 c),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring
abbrev _root_.YangMills.SharedProofs.p51313 := @stepSourceTerm_eq
private lemma finalField_forgetMarks : (s n : ℕ) → (u : MarkedSample ℓ s n) →
    finalField ℓ s n (forgetMarks ℓ s n u) = topField ℓ s n u
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl
private lemma chainMark_forgetMarks (T : StageTower ℓ) (al : ℕ → ℝ) : (s n : ℕ) → [NeZero n] →
    (h : PlaquetteWeight (fineSide ℓ.side s n)) → (u : MarkedSample ℓ s n) →
    chainMark ℓ (fun j => (T.stage j).coupling) al s n h (forgetMarks ℓ s n u) = completedObservable T al s n h u
  | 0, _, _, h, u => by
    show curvatureObservable h u = curvatureObservable h u + 0
    rw [add_zero]
  | s + 1, n, _, h, u => by
    have ih := chainMark_forgetMarks T al s (n * ℓ.side) h u.1
    have e : ∑ c : TorusBond n, ℓ.coupling * al s * bondBlockMean ℓ.side (s + 1) n h c *
        bondScore ℓ (T.stage s).coupling (finalField ℓ s (n * ℓ.side) (forgetMarks ℓ s (n * ℓ.side) u.1))
          u.2.2.1 u.2.1 c =
        sourceTerm T al s n h u := by
      rw [finalField_forgetMarks]
      exact (stepSourceTerm_eq _ _ _ _ _ _).symm
    show chainMark ℓ (fun j => (T.stage j).coupling) al s (n * ℓ.side) h (forgetMarks ℓ s (n * ℓ.side) u.1) +
        ∑ c : TorusBond n, ℓ.coupling * al s * bondBlockMean ℓ.side (s + 1) n h c *
          bondScore ℓ (T.stage s).coupling (finalField ℓ s (n * ℓ.side) (forgetMarks ℓ s (n * ℓ.side) u.1))
            u.2.2.1 u.2.1 c =
      curvatureObservable h (bottomField ℓ s (n * ℓ.side) u.1) +
        (cumulativeSource T al s (n * ℓ.side) h u.1 + sourceTerm T al s n h u)
    rw [ih, e, ← add_assoc]
    rfl
variable {T : StageTower ℓ}
private lemma abs_fittedResponse_le (S : ScoredStageTower T) (F : FinePlaquetteFunction) (k n : ℕ) [NeZero n] {C₀ : ℝ}
    (hC : 0 ≤ C₀) (hs0 : ∀ w, 0 ≤ (S.setup k).score w) (q : StageState T k n)
    (hh : ∀ z, |centeredHullResponse (S.setup k).cold (S.setup k).hull n z q.1 q.2.1 q.2.2 (fineWeight F _)| ≤
      C₀ + siteScore (S.setup k).score q.2.1 q.2.2 z) :
    |fittedResponse S F k n q| ≤ (C₀ + 1) * ((functionSites ℓ.side F k n).card : ℝ) *
      meanSiteScore (S.setup k).score (functionSites ℓ.side F k n) q.2.1 q.2.2 := by
  unfold meanSiteScore
  have h1 : |fittedResponse S F k n q| ≤
      ∑ z ∈ functionSites ℓ.side F k n, (C₀ + siteScore (S.setup k).score q.2.1 q.2.2 z) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => hh z)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have hS : 0 ≤ ∑ z ∈ functionSites ℓ.side F k n, siteScore (S.setup k).score q.2.1 q.2.2 z :=
    Finset.sum_nonneg fun z _ => siteScore_nonneg hs0 _ _ _
  rcases Nat.eq_zero_or_pos (functionSites ℓ.side F k n).card with h0 | h0
  · have hE : functionSites ℓ.side F k n = ∅ := Finset.card_eq_zero.mp h0
    rw [hE] at h1 ⊢
    simpa using h1
  · have hc : (0 : ℝ) < (functionSites ℓ.side F k n).card := by exact_mod_cast h0
    have e : (C₀ + 1) * ((functionSites ℓ.side F k n).card : ℝ) *
        (1 + ((functionSites ℓ.side F k n).card : ℝ)⁻¹ *
          ∑ z ∈ functionSites ℓ.side F k n, siteScore (S.setup k).score q.2.1 q.2.2 z) =
        (C₀ + 1) * ((functionSites ℓ.side F k n).card : ℝ) +
          (C₀ + 1) * ∑ z ∈ functionSites ℓ.side F k n, siteScore (S.setup k).score q.2.1 q.2.2 z := by
      field_simp
    rw [e]
    nlinarith
abbrev _root_.YangMills.DeltaSharedProofs.p501280 := @abs_fittedResponse_le
private lemma abs_response_sub_centering_le (S : ScoredStageTower T) (β : ℝ) (k n : ℕ) [NeZero n]
    (F : FinePlaquetteFunction) {C₀ : ℝ} (hC : 0 ≤ C₀)
    (hle : stageSigma T k n ≤ markedSampleMeasurableSpace ℓ k n)
    (hmean : ∀ᵐ a ∂(markedSampleLaw T β k n), fittedResponse S F k n (stageState T k n a) =
      ((markedSampleLaw T β k n)[completedCentered S F k n | stageSigma T k n]) a)
    (hint : Integrable (completedCentered S F k n) (markedSampleLaw T β k n))
    (hresp : response T β S.coeffs k n (fineWeight F _) =ᵐ[markedSampleLaw T β k n]
      (markedSampleLaw T β k n)[completedObservable T S.coeffs k n (fineWeight F _) | stageSigma T k n])
    (hbd : ∀ᵐ a ∂(markedSampleLaw T β k n), ∀ z,
      |centeredHullResponse (S.setup k).cold (S.setup k).hull n z (stageState T k n a).1 (stageState T k n a).2.1
        (stageState T k n a).2.2 (fineWeight F _)| ≤
        C₀ + siteScore (S.setup k).score (stageState T k n a).2.1 (stageState T k n a).2.2 z)
    (hs0 : ∀ w, 0 ≤ (S.setup k).score w) [IsProbabilityMeasure (markedSampleLaw T β k n)] :
    ∀ᵐ a ∂(markedSampleLaw T β k n), |response T β S.coeffs k n (fineWeight F _) a - centering S F k n| ≤
      (C₀ + 1) * ((functionSites ℓ.side F k n).card : ℝ) *
        meanSiteScore (S.setup k).score (functionSites ℓ.side F k n) (stageState T k n a).2.1
          (stageState T k n a).2.2 := by
  have hO : Integrable (completedObservable T S.coeffs k n (fineWeight F _)) (markedSampleLaw T β k n) := by
    refine (hint.add (integrable_const (centering S F k n))).congr (Eventually.of_forall fun u => ?_)
    show completedObservable T S.coeffs k n (fineWeight F _) u - centering S F k n + centering S F k n = _
    ring
  have hsub := condExp_sub hO (integrable_const (μ := markedSampleLaw T β k n) (centering S F k n)) (stageSigma T k n)
  rw [condExp_const hle] at hsub
  filter_upwards [hmean, hresp, hsub, hbd] with a h1 h2 h3 h5
  have heq : response T β S.coeffs k n (fineWeight F _) a - centering S F k n =
      fittedResponse S F k n (stageState T k n a) := by
    rw [h1, h2]
    have h4 : ((markedSampleLaw T β k n)[completedCentered S F k n | stageSigma T k n]) a =
        ((markedSampleLaw T β k n)[completedObservable T S.coeffs k n (fineWeight F _) - fun _ => centering S F k n |
          stageSigma T k n]) a := rfl
    rw [h4, h3]
    rfl
  rw [heq]
  exact abs_fittedResponse_le S F k n hC hs0 _ h5
abbrev _root_.YangMills.SharedProofs.p26281 := @abs_response_sub_centering_le
end Response
private lemma unitTorusWeight_eq_fineWeight {L K k : ℕ} [NeZero L] (hk : k ≤ K) (G : AmbientSpace → ℝ) :
    unitTorusWeight L K k G = fineWeight (fun b => periodizeUnitTorus G fun a => b a / (L : ℝ) ^ K)
      (fineSide L k (boxSide L K k)) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hM : 2 * fineSide L k (boxSide L K k) = 4 * L ^ K := by
    rw [fineSide_eq]
    unfold boxSide
    have : L ^ (K - k) * L ^ k = L ^ K := by
      rw [← pow_add]
      congr 1
      omega
    calc 2 * (2 * L ^ (K - k) * L ^ k) = 4 * (L ^ (K - k) * L ^ k) := by ring
      _ = 4 * L ^ K := by rw [this]
  have hMr : ((2 * fineSide L k (boxSide L K k) : ℕ) : ℝ) = 4 * (L : ℝ) ^ K := by exact_mod_cast hM
  funext p
  have key : ∀ i, ∃ w : ℤ, ((doubledBarycentre p i).val : ℝ) / (2 * (L : ℝ) ^ K) =
      LevelTestFunctions.barycenterCoord p i / (L : ℝ) ^ K + 2 * (w : ℝ) := by
    intro i
    obtain ⟨v, hv⟩ : ∃ v : ℕ, v = (p.1 i).val := ⟨_, rfl⟩
    obtain ⟨ε, hε⟩ : ∃ ε : ℕ, ε = (if i = p.2.1 then 1 else 0) + (if i = p.2.2 then 1 else 0) := ⟨_, rfl⟩
    have hvm : v < fineSide L k (boxSide L K k) := by
      rw [hv]
      exact ZMod.val_lt _
    have hε2 : ε ≤ 2 := by
      rw [hε]
      split_ifs <;> omega
    have hbar : 2 * LevelTestFunctions.barycenterCoord p i = ((2 * v + ε : ℕ) : ℝ) := by
      unfold LevelTestFunctions.barycenterCoord
      rw [hε, hv]
      split_ifs <;> push_cast <;> ring
    have hval : (doubledBarycentre p i).val = (2 * v + ε) % (2 * fineSide L k (boxSide L K k)) := by
      have e : doubledBarycentre p i = ((2 * v + ε : ℕ) : ZMod (2 * fineSide L k (boxSide L K k))) := by
        unfold doubledBarycentre
        rw [hv, hε, add_assoc]
      rw [e]
      exact ZMod.val_natCast _ _
    by_cases hlt : 2 * v + ε < 2 * fineSide L k (boxSide L K k)
    · refine ⟨0, ?_⟩
      rw [hval, Nat.mod_eq_of_lt hlt]
      have : (((2 * v + ε : ℕ)) : ℝ) = 2 * LevelTestFunctions.barycenterCoord p i := hbar.symm
      rw [this]
      field_simp
      simp
    · refine ⟨-1, ?_⟩
      have h1 : (2 * v + ε) % (2 * fineSide L k (boxSide L K k)) = 2 * v + ε - 2 * fineSide L k (boxSide L K k) := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      have h2 : (((2 * v + ε - 2 * fineSide L k (boxSide L K k) : ℕ)) : ℝ) =
          ((2 * v + ε : ℕ) : ℝ) - ((2 * fineSide L k (boxSide L K k) : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]
      rw [hval, h1, h2, ← hbar, hMr]
      push_cast
      field_simp
      ring
  choose w hw using key
  have e1 : unitTorusWeight L K k G p = periodizeUnitTorus G
      (fun i => LevelTestFunctions.barycenterCoord p i / (L : ℝ) ^ K + 2 * (w i : ℝ)) := by
    have : (fun i => ((doubledBarycentre p i).val : ℝ) / (2 * (L : ℝ) ^ K)) =
        fun i => LevelTestFunctions.barycenterCoord p i / (L : ℝ) ^ K + 2 * (w i : ℝ) := funext hw
    show periodizeUnitTorus G (fun i => ((doubledBarycentre p i).val : ℝ) / (2 * (L : ℝ) ^ K)) = _
    rw [this]
  rw [e1, periodizeUnitTorus_shift]
  rfl
abbrev _root_.YangMills.SharedProofs.p37640 := @unitTorusWeight_eq_fineWeight
private theorem couplingFlow_step {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ)
    (hW : ∀ β : ℝ, ℓ.y₁ ≤ β → HasExpansion ℓ 0 β (wilsonWeight β)) (β : ℝ) (t : ℕ)
    (h : ∀ j ≤ t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) :
    HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2 ∧
      |(couplingFlow ℓ β (t + 1)).1 - (couplingFlow ℓ β t).1| ≤ 2 * ℓ.B := by
  have key : ∀ (t : ℕ) (x : ℝ) (D : TorusFunctional), ℓ.y₁ ≤ x → HasExpansion ℓ t x D →
      HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
        |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by
    intro t x D hy hD
    obtain ⟨x', ⟨hrow, hst⟩, hu⟩ := hR t x D hy hD
    have hex : ∃ x'' : ℝ, HasExpansion ℓ (t + 1) x'' (kernelImage ℓ x D) := ⟨x', hrow⟩
    have hn : expansionCoupling ℓ t x D = x' := by
      unfold expansionCoupling
      rw [dif_pos hex]
      obtain ⟨f, hf, _⟩ := hex.choose_spec.2
      exact hu _ f hf
    rw [hn]
    exact ⟨hrow, hst⟩
  induction t with
  | zero =>
    have h0 : HasExpansion ℓ 0 (couplingFlow ℓ β 0).1 (couplingFlow ℓ β 0).2 := hW β (h 0 le_rfl)
    exact ⟨h0, (key 0 _ _ (h 0 le_rfl) h0).2⟩
  | succ t ih =>
    obtain ⟨hr, _⟩ := ih fun j hj => h j (by omega)
    have hrow : HasExpansion ℓ (t + 1) (couplingFlow ℓ β (t + 1)).1 (couplingFlow ℓ β (t + 1)).2 :=
      (key t _ _ (h t (by omega)) hr).1
    exact ⟨hrow, (key (t + 1) _ _ (h (t + 1) le_rfl) hrow).2⟩
abbrev _root_.YangMills.SharedProofs.p51822 := @couplingFlow_step
private theorem couplingFlow_sub_le {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ)
    (hW : ∀ β : ℝ, ℓ.y₁ ≤ β → HasExpansion ℓ 0 β (wilsonWeight β)) {β : ℝ} {K : ℕ}
    (h : ∀ j ≤ K, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) (e : ℕ) (he : e ≤ K) :
    (couplingFlow ℓ β (K - e)).1 ≤ (couplingFlow ℓ β K).1 + 2 * ℓ.B * e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 := ih (by omega)
    have h2 := (couplingFlow_step hR hW β (K - (e + 1)) fun j hj => h j (by omega)).2
    have h3 : K - (e + 1) + 1 = K - e := by omega
    rw [h3] at h2
    have h4 := (abs_le.mp h2).1
    push_cast
    linarith
abbrev _root_.YangMills.SharedProofs.p54754 := @couplingFlow_sub_le
private lemma two_mul_le_rpow_six {C₀ Lr nn r x c : ℝ} (hC₀ : 0 ≤ C₀) (hL : 1 ≤ Lr) (hx : 1 ≤ x) (hr : r ≤ x + 1)
    (hnn : nn ≤ 2 ^ 13 * Lr * r) (hn0 : 0 ≤ nn) (hc : c ≤ (2 * (nn + 4) + 1) ^ 4)
    (hA : 2 * C₀ * (2 ^ 17 * Lr) ^ 4 ≤ x) : 2 * (C₀ * c * x) ≤ x ^ (6 : ℝ) := by
  have hLx : 1 ≤ Lr * x := by nlinarith
  have h1 : nn ≤ 2 ^ 14 * (Lr * x) := by
    have : 2 ^ 13 * Lr * r ≤ 2 ^ 13 * Lr * (x + 1) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    nlinarith
  have h2 : 2 * (nn + 4) + 1 ≤ 2 ^ 17 * Lr * x := by nlinarith
  have h3 : (2 * (nn + 4) + 1) ^ 4 ≤ (2 ^ 17 * Lr * x) ^ 4 := pow_le_pow_left₀ (by positivity) h2 4
  have h4 : c ≤ (2 ^ 17 * Lr) ^ 4 * x ^ 4 := by
    have : (2 ^ 17 * Lr * x) ^ 4 = (2 ^ 17 * Lr) ^ 4 * x ^ 4 := by ring
    linarith
  have e : x ^ (6 : ℝ) = x ^ 6 := by
    have : (6 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]
  rw [e]
  calc 2 * (C₀ * c * x) ≤ 2 * (C₀ * ((2 ^ 17 * Lr) ^ 4 * x ^ 4) * x) := by gcongr
    _ = (2 * C₀ * (2 ^ 17 * Lr) ^ 4) * x ^ 5 := by ring
    _ ≤ x * x ^ 5 := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = x ^ 6 := by ring
abbrev _root_.YangMills.SharedProofs.p33667 := @two_mul_le_rpow_six
theorem translatedResponseMoments_holds (h₂ : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement)
    (h₃ : ResponseInTheExpansion.StageStatesMeasurableStatement) (h₄ : WeightedResponses.ResponsesBounded)
    (h₅ : fittedResponseIsConditionalMeanStatement) (h₅' : flowStatesAreGroundsStatement)
    (h₅'' : conditionalProductMeansStatement)
    (h₅''' : ResponseInTheExpansion.ResponseIsConditionalExpectation)
    (h₆ : WeightedObservables.majorantMomentsStatement)
    (h₇ : translateSitesStatement) (h₈ : separationLevelStatement) (h₉ : couplingAtSeparation_tendsto_statement) :
    HoldsForShapes fun Tb y Kr Xi vt => ∃ C d₀ : ℝ, 0 ≤ C ∧ 0 < d₀ ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ (K : ℕ) (β : ℝ) (al : ℕ → ℝ) (T : StageTower (Tb.stepParameters y)),
      IsStateChain Tb y Kr Xi d K β al T →
      ∀ (k : ℕ) (x : ℝ), k = separationLevel (Tb.stepParameters y) β K d →
      x = couplingAtSeparation (Tb.stepParameters y) β K d →
      IsProbabilityMeasure (stageLaw T β K k) ∧
      Measurable (stageState T k (boxSide (Tb.stepParameters y).side K k)) ∧
      ∀ (g : AmbientSpace → ℝ) (c : AmbientSpace),
      (∀ a b, |g a - g b| ≤ euclidNormVec (a - b) / (vt * d)) →
      tsupport g ⊆ closedBallR4 c d → (∀ a, |g a| ≤ 1) → ∀ v : Fin 4 → ℤ,
      MemLp (centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v g)) 64
        (stageLaw T β K k) ∧
      eLpNorm (centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v g)) 64
        (stageLaw T β K k) ≤ ENNReal.ofReal (x ^ C) := by
  refine (((((((HoldsForShapes.of_response h₅).and (HoldsForShapes.of_response h₅')).and
    (HoldsForShapes.of_response h₅'')).and (HoldsForShapes.of_response h₆)).and (HoldsForShapes.of_holdsOnParameters h₈)).and
    (HoldsForShapes.of_holdsOnParameters h₉)).and HoldsForShapes.params).mono ?_
  rintro Tb y Kr Xi vt ⟨⟨⟨⟨⟨⟨hFi, hGr⟩, hPr⟩, hM⟩, hLv⟩, hCp⟩, hDr, hy0, hRow, hKr, hXi, hvt0, hvt1⟩
  have hfit : (Tb.stepParameters y).Admissible := hDr.fits y hy0
  have hJ := hfit.depth_lt
  obtain ⟨Cq, hCq1, hq⟩ := hM 64
  have hL2 : 2 ≤ (Tb.stepParameters y).side := by
    have := hfit.L_ge
    omega
  have hLr1 : (1 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ (Tb.stepParameters y).side)
  have hLr2 : (1 : ℝ) < ((Tb.stepParameters y).side : ℝ) := by
    exact_mod_cast (by omega : 1 < (Tb.stepParameters y).side)
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = (Tb.stepParameters y).n₀ + 1 := ⟨_, rfl⟩
  have hNZ : NeZero (2 * (Tb.stepParameters y).side ^ e) := ⟨by positivity⟩
  have hblockE : IsBlockTorusSide (Tb.stepParameters y) (2 * (Tb.stepParameters y).side ^ e) := by
    refine ⟨?_, ?_⟩
    · rw [he, pow_succ]
      exact Dvd.intro_left (2 * (Tb.stepParameters y).side ^ (Tb.stepParameters y).n₀) (by ring)
    · have h1 : (Tb.stepParameters y).n₀ < (Tb.stepParameters y).side ^ (Tb.stepParameters y).n₀ :=
        Nat.lt_pow_self (by omega)
      rw [he, pow_succ]
      nlinarith
  obtain ⟨Xt, hXt⟩ : ∃ Xt : ℝ, Xt = Xi + 2 * (Tb.stepParameters y).B * (e : ℝ) := ⟨_, rfl⟩
  have hy1 : 1 ≤ (Tb.stepParameters y).y₁ := hfit.y₁_ge
  have hB0 : 0 < (Tb.stepParameters y).B := hfit.B_pos
  have hXt1 : 1 ≤ Xt := by
    have : 0 ≤ 2 * (Tb.stepParameters y).B * (e : ℝ) := by positivity
    linarith
  obtain ⟨Ct, hCt⟩ : ∃ Ct : ℝ,
      Ct = Cq * Real.exp (Cq * (1 + Real.log Xt) * ((2 * (Tb.stepParameters y).side ^ e : ℕ) : ℝ) ^ 4) := ⟨_, rfl⟩
  have hlogXt : 0 ≤ Real.log Xt := Real.log_nonneg hXt1
  have hCt1 : 1 ≤ Ct := by
    rw [hCt]
    have : 1 ≤ Real.exp (Cq * (1 + Real.log Xt) * ((2 * (Tb.stepParameters y).side ^ e : ℕ) : ℝ) ^ 4) :=
      Real.one_le_exp (by positivity)
    nlinarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = max (((Tb.stepParameters y).side : ℝ) ^ e) (2 / vt) := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by
    rw [hY]
    exact le_max_of_le_right (by positivity)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * (Kr.C₀ + 1) * (2 ^ 17 * ((Tb.stepParameters y).side : ℝ)) ^ 4 := ⟨_, rfl⟩
  obtain ⟨d₁, hd₁, hgrow⟩ := hCp Xi hXi (max (max A Ct) (max 2 (Y ^ 100)))
  refine ⟨6, min d₁ (1 / 8), by norm_num, lt_min hd₁ (by norm_num), ?_⟩
  intro d hd0 hdd K β al T hCh k x hk hx
  have hdd1 : d ≤ d₁ := hdd.trans (min_le_left _ _)
  have hd8 : d ≤ 1 / 8 := hdd.trans (min_le_right _ _)
  have hXx : max (max A Ct) (max 2 (Y ^ 100)) ≤ x := by
    rw [hx]
    exact hgrow d hd0 hdd1 K β hCh.isFlowDatum hCh.minimalCutoff_le
  have hAx : A ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hXx
  have hCx : Ct ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hXx
  have hx2 : 2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hXx
  have hYx : Y ^ 100 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hXx
  have hx0 : 0 < x := by linarith
  obtain ⟨far, klt, nle⟩ := hLv Xi hXi d hd0 (by linarith) K β hCh.isFlowDatum hCh.minimalCutoff_le
  have hkK : k < K := by
    rw [hk]
    exact klt
  obtain ⟨nn, hnn⟩ : ∃ nn : ℝ, nn = lengthInSites (Tb.stepParameters y).side K k d := ⟨_, rfl⟩
  have far' : 2 ^ 12 * (clusterRange x : ℝ) ≤ nn := by
    rw [hnn, hx, hk]
    exact far
  have nle' : nn ≤ 2 ^ 13 * ((Tb.stepParameters y).side : ℝ) * (clusterRange x : ℝ) := by
    rw [hnn, hx, hk]
    exact nle
  have hYr : Y ≤ (clusterRange x : ℝ) := by
    have h1 : Y ≤ x ^ ((1 : ℝ) / 100) := by
      have e1 : Y = (Y ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hY0]
        norm_num
      rw [e1]
      exact Real.rpow_le_rpow (by positivity) hYx (by norm_num)
    exact h1.trans (Nat.le_ceil _)
  have hr0 : (0 : ℝ) ≤ (clusterRange x : ℝ) := by positivity
  have hnY : Y ≤ nn := by nlinarith
  have hn0 : 0 ≤ nn := hY0.trans hnY
  have hn2 : 2 / vt ≤ lengthInSites (Tb.stepParameters y).side K k d := by
    rw [← hnn]
    exact (hY ▸ le_max_right _ _ : 2 / vt ≤ Y).trans hnY
  have hnL : ((Tb.stepParameters y).side : ℝ) ^ e ≤ nn :=
    (hY ▸ le_max_left _ _ : ((Tb.stepParameters y).side : ℝ) ^ e ≤ Y).trans hnY
  have hlt : nn < ((Tb.stepParameters y).side : ℝ) ^ (K - k) := by
    rw [hnn]
    unfold lengthInSites
    have : (0 : ℝ) < ((Tb.stepParameters y).side : ℝ) ^ (K - k) := by positivity
    nlinarith
  have hgap : e < K - k := (pow_lt_pow_iff_right₀ hLr2).1 (lt_of_le_of_lt hnL hlt)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = K - k - e := ⟨_, rfl⟩
  have hst : IsTowerAtParameters Tb y T β k :=
    ⟨hCh.onFamily.startsAtWilson, fun i hi => hCh.onFamily.coupling_eq i (by omega),
      fun i hi => hCh.onFamily.onFamily i (by omega)⟩
  have hnum : IsChainResponseCoeff (Tb.stepParameters y) Kr β k al := by
    rw [hk]
    exact hCh.isCoeff
  have hside : boxSide (Tb.stepParameters y).side K k =
      TransfersOffTheWalk.sideBelow (Tb.stepParameters y).side j (2 * (Tb.stepParameters y).side ^ e) := by
    rw [sideBelow_eq]
    unfold boxSide
    have : K - k = e + j := by omega
    rw [this, pow_add]
    ring
  have hblock : IsBlockTorusSide (Tb.stepParameters y) (boxSide (Tb.stepParameters y).side K k) := by
    rw [hside, sideBelow_eq]
    have hp : 0 < (Tb.stepParameters y).side ^ j := by positivity
    exact ⟨hblockE.1.mul_right _, hblockE.2.trans (Nat.le_mul_of_pos_right _ hp)⟩
  have hprob : IsProbabilityMeasure (stageLaw T β K k) :=
    (h₂ (Tb.stepParameters y) hfit hJ T hCh.isCutoff_bottom hCh.marksMeasurable β al k
      (boxSide (Tb.stepParameters y).side K k)).1
  have hstate : Measurable (stageState T k (boxSide (Tb.stepParameters y).side K k)) := h₃ (Tb.stepParameters y) hfit T k _
  obtain ⟨S, hSK, hSrun, hSal⟩ := hCh.scored
  subst hSal
  have hSk : S.FollowsFlow β k := followsFlow_mono hSrun (by omega)
  have hrun' : S.FollowsFlow β (k + j) := followsFlow_mono hSrun (by omega)
  have hfloor : ∀ i ≤ K, (Tb.stepParameters y).y₁ ≤ (couplingFlow (Tb.stepParameters y) β i).1 := hCh.isFlowDatum.le_coupling
  have hreach : CouplingsAboveFloor (Tb.stepParameters y) β (k + j) := fun i hi => hfloor i (by omega)
  have htop : (couplingFlow (Tb.stepParameters y) β (k + j)).1 ≤ Xt := by
    have h1 := couplingFlow_sub_le hRow.returns_at hRow.wilson_expansion hfloor e (by omega)
    have h2 : k + j = K - e := by omega
    have h3 : (couplingFlow (Tb.stepParameters y) β K).1 ≤ Xi := hCh.isFlowDatum.coupling_le_top
    rw [h2, hXt]
    linarith
  have hgen : ∀ (N : ℕ) [NeZero N],
      N = TransfersOffTheWalk.sideBelow (Tb.stepParameters y).side j (2 * (Tb.stepParameters y).side ^ e) →
      ∀ B : Finset (TorusSite N), B.Nonempty →
      eLpNorm (fun u => meanSiteScore (S.setup k).score B (stageState T k N u).2.1 (stageState T k N u).2.2) 64
        (markedSampleLaw T β k N) ≤ ENNReal.ofReal Ct := by
    intro N _ hN B hB
    subst hN
    obtain ⟨hI, hb⟩ := hq β T S k j (2 * (Tb.stepParameters y).side ^ e) (fun _ : Fin 64 => B) hSK hrun' hreach hblockE
      (fun _ => hB)
    have hle : Cq * Real.exp (Cq * (1 + Real.log (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β (k + j))) *
        ((2 * (Tb.stepParameters y).side ^ e : ℕ) : ℝ) ^ 4) ≤ Ct := by
      have h0 : 0 < ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β (k + j) := by
        have := hreach (k + j) le_rfl
        linarith
      have h1 : Real.log (ClusterExpansionOfAStep.flowCoupling (Tb.stepParameters y) β (k + j)) ≤ Real.log Xt :=
        Real.log_le_log h0 htop
      rw [hCt]
      gcongr
    exact eLpNorm_meanSiteScore_le _ B hCt1 hI (hb.trans hle)
  have hC₀ : 0 ≤ Kr.C₀ := by
    have h1 := hKr.C₀_eq
    have h2 := hKr.N₀_nonneg
    have h3 := hKr.Kc_ge
    have h4 := hfit.a_ge
    rw [h1]
    linarith
  have hrx : (clusterRange x : ℝ) ≤ x + 1 := by
    have h1 : (clusterRange x : ℝ) < x ^ ((1 : ℝ) / 100) + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : x ^ ((1 : ℝ) / 100) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [Real.rpow_one] at h2
    linarith
  have hreachk : CouplingsAboveFloor (Tb.stepParameters y) β k := fun i hi => hfloor i (by omega)
  have hle : stageSigma T k (boxSide (Tb.stepParameters y).side K k) ≤
      markedSampleMeasurableSpace (Tb.stepParameters y) k (boxSide (Tb.stepParameters y).side K k) :=
    hstate.comap_le
  have hIR := hSk.isAdmissible k le_rfl
  have hKk : (S.setup k).responseParams = Kr := (hSk.params_eq k).trans hSK
  have htk : (T.stage k).depth = k := (hSk.isFlowStep k le_rfl).depth_eq
  have hlive := ((hGr β T S k hSK hSk hreachk).2 (boxSide (Tb.stepParameters y).side K k) hblock).1 k le_rfl
  have one : ∀ (g : AmbientSpace → ℝ) (c : AmbientSpace), (∀ x x', |g x - g x'| ≤ euclidNormVec (x - x') / (vt * d)) →
      tsupport g ⊆ closedBallR4 c d → (∀ x, |g x| ≤ 1) → ∀ v : Fin 4 → ℤ,
      MemLp (centeredBoxResponse T β S.coeffs K k (translateBy (Tb.stepParameters y).side K k v g)) 64 (stageLaw T β K k) ∧
        eLpNorm (centeredBoxResponse T β S.coeffs K k (translateBy (Tb.stepParameters y).side K k v g)) 64
          (stageLaw T β K k) ≤ ENNReal.ofReal (x ^ (6 : ℝ)) := by
    intro g c hl hb hsz v
    have hsize := weightNorm_translate_le hkK.le hd0 (by linarith) hvt0 hl hb hsz hn2 v
    obtain ⟨z, hz⟩ := h₇ (Tb.stepParameters y).side K k hfit.L_odd hkK.le d c g hd0 hb
    have hsites := hz v
    obtain ⟨F, hFdef⟩ : ∃ F : FinePlaquetteFunction, F = fun b =>
        periodizeUnitTorus (translateBy (Tb.stepParameters y).side K k v g)
          fun a => b a / ((Tb.stepParameters y).side : ℝ) ^ K := ⟨_, rfl⟩
    have hEq : unitTorusWeight (Tb.stepParameters y).side K k (translateBy (Tb.stepParameters y).side K k v g) =
        fineWeight F (fineSide (Tb.stepParameters y).side k (boxSide (Tb.stepParameters y).side K k)) := by
      rw [hFdef]
      exact unitTorusWeight_eq_fineWeight hkK.le _
    have hRs : boxResponse T β S.coeffs K k (translateBy (Tb.stepParameters y).side K k v g) =
        response T β S.coeffs k (boxSide (Tb.stepParameters y).side K k) (fineWeight F _) := by
      funext u
      unfold boxResponse
      rw [hEq]
    have hCs : centeredBoxResponse T β S.coeffs K k (translateBy (Tb.stepParameters y).side K k v g) =
        fun u => response T β S.coeffs k (boxSide (Tb.stepParameters y).side K k) (fineWeight F _) u -
          ∫ w, response T β S.coeffs k (boxSide (Tb.stepParameters y).side K k) (fineWeight F _) w ∂stageLaw T β K k := by
      funext u
      unfold centeredBoxResponse
      rw [hRs]
    rw [hCs]
    rw [hEq] at hsize
    have hsites' : functionSites (Tb.stepParameters y).side F k (boxSide (Tb.stepParameters y).side K k) ⊆
        supBall (z + siteOfInt v) (lengthInSites (Tb.stepParameters y).side K k d + 4) := by
      unfold weightSitesOf at hsites
      rw [hEq] at hsites
      exact hsites
    obtain ⟨hmeas, Cb, hCb⟩ := h₄ (Tb.stepParameters y) hfit hJ T hCh.isCutoff_bottom hCh.marksMeasurable β S.coeffs k
      (boxSide (Tb.stepParameters y).side K k) (fineWeight F _)
    have hF : MemLp (response T β S.coeffs k (boxSide (Tb.stepParameters y).side K k) (fineWeight F _)) 64
        (stageLaw T β K k) :=
      MemLp.of_bound hmeas.aestronglyMeasurable Cb (hCb.mono fun u hu => by rw [Real.norm_eq_abs]; exact hu)
    have hmean := (hFi β T S k hSK hSk hreachk F k le_rfl (boxSide (Tb.stepParameters y).side K k) hblock).2.1
    have hprod := (hPr β T S k hSK hSk hreachk 1 (fun _ => F) {0} (boxSide (Tb.stepParameters y).side K k) hblock).1 k
    have hint : Integrable (completedCentered S F k (boxSide (Tb.stepParameters y).side K k))
        (markedSampleLaw T β k (boxSide (Tb.stepParameters y).side K k)) :=
      hprod.1.congr (ae_of_all _ fun u => by simp)
    have hresp := h₅''' (Tb.stepParameters y) hfit hJ T hCh.isCutoff_bottom hCh.marksMeasurable β S.coeffs k
      (boxSide (Tb.stepParameters y).side K k) (fineWeight F _)
    have hmk : (fun u => chainMark (Tb.stepParameters y) (fun j => (T.stage j).coupling) S.coeffs k
        (boxSide (Tb.stepParameters y).side K k)
        (fineWeight F (fineSide (Tb.stepParameters y).side k (boxSide (Tb.stepParameters y).side K k)))
        (forgetMarks (Tb.stepParameters y) k (boxSide (Tb.stepParameters y).side K k) u)) =
        completedObservable T S.coeffs k (boxSide (Tb.stepParameters y).side K k)
          (fineWeight F (fineSide (Tb.stepParameters y).side k (boxSide (Tb.stepParameters y).side K k))) :=
      funext fun u => chainMark_forgetMarks T S.coeffs k _ _ u
    rw [hmk] at hresp
    have hszt : ∀ t, t = k → weightNorm (Tb.stepParameters y).side t
        (fineWeight F (fineSide (Tb.stepParameters y).side t (boxSide (Tb.stepParameters y).side K k))) ≤ 1 := by
      rintro _ rfl
      exact hsize
    have hbd : ∀ᵐ a ∂(markedSampleLaw T β k (boxSide (Tb.stepParameters y).side K k)), ∀ z,
        |centeredHullResponse (S.setup k).cold (S.setup k).hull (boxSide (Tb.stepParameters y).side K k) z
          (stageState T k _ a).1 (stageState T k _ a).2.1 (stageState T k _ a).2.2 (fineWeight F _)| ≤
          Kr.C₀ + siteScore (S.setup k).score (stageState T k _ a).2.1 (stageState T k _ a).2.2 z := by
      filter_upwards [hlive] with a hl z
      have h3 := hIR.bounds.size_hull (boxSide (Tb.stepParameters y).side K k) hblock z _ _ _ hl (fineWeight F _)
      have h4 := hszt _ htk
      rw [hKk] at h3
      have hnn : 0 ≤ Kr.C₀ + siteScore (S.setup k).score (stageState T k _ a).2.1 (stageState T k _ a).2.2 z :=
        add_nonneg hC₀ (siteScore_nonneg hIR.price.nonneg _ _ _)
      exact h3.trans ((mul_le_mul_of_nonneg_left h4 hnn).trans (mul_one _).le)
    have : IsProbabilityMeasure (markedSampleLaw T β k (boxSide (Tb.stepParameters y).side K k)) := hprob
    have hae := abs_response_sub_centering_le S β k (boxSide (Tb.stepParameters y).side K k) F hC₀ hle hmean hint hresp
      hbd hIR.price.nonneg
    have hcard : (((functionSites (Tb.stepParameters y).side F k (boxSide (Tb.stepParameters y).side K k)).card : ℕ) : ℝ) ≤
        (2 * (nn + 4) + 1) ^ 4 := by
      rw [hnn]
      exact card_le_of_subset_supBall (by rw [← hnn]; linarith) hsites'
    obtain ⟨W, hW⟩ : ∃ W, W = functionSites (Tb.stepParameters y).side F k (boxSide (Tb.stepParameters y).side K k) :=
      ⟨_, rfl⟩
    rw [← hW] at hae hcard
    have hc0 : 0 ≤ (Kr.C₀ + 1) * (W.card : ℝ) := by positivity
    have hb1 : eLpNorm (fun u => response T β S.coeffs k (boxSide (Tb.stepParameters y).side K k) (fineWeight F _) u -
        centering S F k (boxSide (Tb.stepParameters y).side K k)) 64 (stageLaw T β K k) ≤
        ENNReal.ofReal ((Kr.C₀ + 1) * (W.card : ℝ) * x) := by
      have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := stageLaw T β K k) (p := 64)
        (f := fun u => response T β S.coeffs k (boxSide (Tb.stepParameters y).side K k) (fineWeight F _) u -
          centering S F k (boxSide (Tb.stepParameters y).side K k))
        (g := fun u => meanSiteScore (S.setup k).score W (stageState T k _ u).2.1 (stageState T k _ u).2.2)
        (c := (Kr.C₀ + 1) * (W.card : ℝ))
        (hae.mono fun u hu => by
          rw [Real.norm_eq_abs, Real.norm_eq_abs]
          exact hu.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hc0))
      rcases W.eq_empty_or_nonempty with hW0 | hW1
      · have hz0 : (Kr.C₀ + 1) * (W.card : ℝ) = 0 := by simp [hW0]
        rw [hz0] at h1 ⊢
        simpa using h1
      · refine h1.trans ?_
        rw [ENNReal.ofReal_mul hc0]
        exact mul_le_mul_right (((hgen _ hside W hW1).trans (ENNReal.ofReal_le_ofReal hCx))) _
    obtain ⟨m1, m2⟩ := memLp_sub_integral_of_eLpNorm_sub_le (mul_nonneg hc0 hx0.le) hF hb1
    refine ⟨m1, m2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hAx' : 2 * (Kr.C₀ + 1) * (2 ^ 17 * ((Tb.stepParameters y).side : ℝ)) ^ 4 ≤ x := hA ▸ hAx
    exact two_mul_le_rpow_six (by linarith) hLr1 (by linarith) hrx nle' hn0 hcard hAx'
  exact ⟨hprob, hstate, one⟩
theorem centeredResponseMoments_holds (h₂ : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement)
    (h₃ : ResponseInTheExpansion.StageStatesMeasurableStatement) (h₄ : WeightedResponses.ResponsesBounded)
    (h₅ : fittedResponseIsConditionalMeanStatement) (h₅' : flowStatesAreGroundsStatement)
    (h₅'' : conditionalProductMeansStatement)
    (h₅''' : ResponseInTheExpansion.ResponseIsConditionalExpectation)
    (h₆ : WeightedObservables.majorantMomentsStatement)
    (h₇ : translateSitesStatement) (h₈ : separationLevelStatement) (h₉ : couplingAtSeparation_tendsto_statement) :
    centeredResponseMomentsStatement := by
  unfold centeredResponseMomentsStatement
  refine (translatedResponseMoments_holds h₂ h₃ h₄ h₅ h₅' h₅'' h₅''' h₆ h₇ h₈ h₉).mono ?_
  rintro Tb y Kr Xi vt ⟨C, d₀, _, hd₀, h⟩
  refine ⟨C, d₀, hd₀, ?_⟩
  intro d hd0 hdd K β al T hCh φ hfam
  let k := separationLevel (Tb.stepParameters y) β K d
  obtain ⟨hprob, _, one⟩ := h d hd0 hdd K β al T hCh k _ rfl rfl
  obtain ⟨c, hc⟩ := hfam.support_in_ball 0
  have habs : ∀ x, |φ x| ≤ 1 := fun x => abs_le.mpr ⟨by linarith [hfam.nonneg 0 x], hfam.le_one 0 x⟩
  have hv := one φ c (hfam.lipschitz 0) hc habs 0
  have hz : translateBy (Tb.stepParameters y).side K k 0 φ = φ := by
    funext a
    have : latticeShift (Tb.stepParameters y).side K k 0 = 0 := by
      funext i
      simp [latticeShift]
    simp [translateBy, this]
  rw [hz] at hv
  have : IsProbabilityMeasure (stageLaw T β K k) := hprob
  exact ⟨hv.1.mono_exponent (by norm_num),
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hv.1.1).trans hv.2⟩

end YangMills.Construction.StateLaws
end
