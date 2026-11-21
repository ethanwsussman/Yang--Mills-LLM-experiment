import YangMills.Construction.FourPointCondition.ConnectedLawOfAPair
import YangMills.Construction.FourPointCondition.LawsWithNoDatum
import YangMills.Construction.FourPointCondition.LevelForEveryScale
import YangMills.Construction.FourPointCondition.LevelReadByTheTwoPointFunction
import YangMills.Construction.FourPointCondition.TransportsOfADilatedPair
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction
open TestFunctions PeriodicLattice TorusLumps WeightedResponses StepReturn
namespace FourPointCondition
private theorem levelMesh_pos {L : ℕ} (hL : 0 < L) (K k : ℕ) : 0 < levelMesh L K k := by
  unfold levelMesh meshSize
  exact zpow_pos (by exact_mod_cast hL) _
private theorem levelMesh_eq_pow_mul {L : ℕ} (hL : 0 < L) (K k : ℕ) :
    levelMesh L K k = (L : ℝ) ^ k * levelMesh L K 0 := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold levelMesh meshSize
  rw [← zpow_natCast (L : ℝ) k, ← zpow_add₀ hL']
  congr 1
  push_cast
  ring
private theorem limsup_coe_mem_Icc {F : Filter ℕ} [F.NeBot] {u : ℕ → ℝ} {A B : ℝ}
    (hA : ∀ᶠ m in F, A ≤ u m) (hB : ∀ᶠ m in F, u m ≤ B) :
    ∃ σ : ℝ, limsup (fun m => ((u m : ℝ) : EReal)) F = ((σ : ℝ) : EReal) ∧ A ≤ σ ∧ σ ≤ B := by
  have h1 : ((A : ℝ) : EReal) ≤ limsup (fun m => ((u m : ℝ) : EReal)) F :=
    le_limsup_of_frequently_le (hA.mono fun m h => EReal.coe_le_coe_iff.2 h).frequently
  have h2 : limsup (fun m => ((u m : ℝ) : EReal)) F ≤ ((B : ℝ) : EReal) :=
    limsup_le_of_le (h := hB.mono fun m h => EReal.coe_le_coe_iff.2 h)
  have ht : limsup (fun m => ((u m : ℝ) : EReal)) F ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
  have hb : limsup (fun m => ((u m : ℝ) : EReal)) F ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1
  refine ⟨(limsup (fun m => ((u m : ℝ) : EReal)) F).toReal, (EReal.coe_toReal ht hb).symm, ?_, ?_⟩
  · rw [← EReal.coe_le_coe_iff, EReal.coe_toReal ht hb]
    exact h1
  · rw [← EReal.coe_le_coe_iff, EReal.coe_toReal ht hb]
    exact h2
private theorem neBot_atTop_inf_sides {L : ℕ} {sides : Set ℝ}
    (hS : ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ torusSide L m ∈ sides) :
    (atTop ⊓ 𝓟 {m : ℕ | torusSide L m ∈ sides}).NeBot := by
  rw [← frequently_mem_iff_neBot, frequently_atTop]
  intro a
  obtain ⟨m, hm, hs⟩ := hS a
  exact ⟨m, hm, hs⟩
private theorem torusSide_eventually_ge {L : ℕ} (hL : 2 ≤ L) (T : ℝ) :
    ∀ᶠ m in atTop, T ≤ torusSide L m := by
  have h1 : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have h := (tendsto_pow_atTop_atTop_of_one_lt h1).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  exact h.eventually_ge_atTop T
private theorem expansionCoupling_step {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} (hx : ℓ.y₁ ≤ x) (hD : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem couplingFlow_hasExpansion {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ)
    (hW : ∀ β : ℝ, ℓ.y₁ ≤ β → HasExpansion ℓ 0 β (wilsonWeight β)) {β : ℝ} (hβ : ℓ.y₁ ≤ β) :
    ∀ t : ℕ, (∀ j < t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) →
      HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2
  | 0, _ => hW β hβ
  | t + 1, h =>
    (expansionCoupling_step hR (h t (Nat.lt_succ_self t))
      (couplingFlow_hasExpansion hR hW hβ t fun j hj => h j (Nat.lt_succ_of_lt hj))).1
private theorem couplingFlow_step_le {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ)
    (hW : ∀ β : ℝ, ℓ.y₁ ≤ β → HasExpansion ℓ 0 β (wilsonWeight β)) {β : ℝ} (hβ : ℓ.y₁ ≤ β) (t : ℕ)
    (h : ∀ j ≤ t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) :
    |(couplingFlow ℓ β (t + 1)).1 - (couplingFlow ℓ β t).1| ≤ 2 * ℓ.B :=
  (expansionCoupling_step hR (h t le_rfl)
    (couplingFlow_hasExpansion hR hW hβ t fun j hj => h j hj.le)).2
private theorem window_le_rpow {L : ℕ} (hL : 1 ≤ L) {u : ℝ}
    (hu : ((2 : ℝ) ^ 15 * (L : ℝ) ^ 2) ^ 900 ≤ u) :
    2 ^ 14 * (L : ℝ) ^ 2 * (clusterRange u : ℝ) ≤ u ^ ((1 : ℝ) / 90) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  set A : ℝ := (2 : ℝ) ^ 15 * (L : ℝ) ^ 2 with hA
  have hA1 : 1 ≤ A := by
    have : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
    rw [hA]
    nlinarith
  have hu1 : 1 ≤ u := le_trans (one_le_pow₀ hA1) hu
  have hu0 : 0 < u := by linarith
  have hp : A ≤ u ^ ((1 : ℝ) / 900) := by
    have h1 : (A ^ 900) ^ ((1 : ℝ) / 900) ≤ u ^ ((1 : ℝ) / 900) :=
      Real.rpow_le_rpow (by positivity) hu (by norm_num)
    have h2 : (A ^ 900) ^ ((1 : ℝ) / 900) = A := by
      rw [← Real.rpow_natCast A 900, ← Real.rpow_mul (by positivity)]
      norm_num
    linarith
  have hq : 1 ≤ u ^ ((1 : ℝ) / 100) := Real.one_le_rpow hu1 (by norm_num)
  have hr : (clusterRange u : ℝ) ≤ 2 * u ^ ((1 : ℝ) / 100) := by
    have := Nat.ceil_lt_add_one (a := u ^ ((1 : ℝ) / 100)) (by positivity)
    unfold clusterRange
    linarith
  have hs : u ^ ((1 : ℝ) / 90) = u ^ ((1 : ℝ) / 900) * u ^ ((1 : ℝ) / 100) := by
    rw [← Real.rpow_add hu0]
    norm_num
  rw [hs]
  calc 2 ^ 14 * (L : ℝ) ^ 2 * (clusterRange u : ℝ)
      ≤ 2 ^ 14 * (L : ℝ) ^ 2 * (2 * u ^ ((1 : ℝ) / 100)) := by gcongr
    _ = A * u ^ ((1 : ℝ) / 100) := by rw [hA]; ring
    _ ≤ u ^ ((1 : ℝ) / 900) * u ^ ((1 : ℝ) / 100) := by gcongr
private theorem mul_rpow_neg_le_half {C μ u : ℝ} (hC : 0 < C) (hμ : 0 < μ) (hu : (2 * C / μ) ^ 100 ≤ u) :
    C * u ^ (-(1 / 100 : ℝ)) ≤ μ / 2 := by
  have hT : 0 < 2 * C / μ := by positivity
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  have h1 : 2 * C / μ ≤ u ^ ((1 : ℝ) / 100) := by
    have h1 : ((2 * C / μ) ^ 100) ^ ((1 : ℝ) / 100) ≤ u ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (by positivity) hu (by norm_num)
    have h2 : ((2 * C / μ) ^ 100) ^ ((1 : ℝ) / 100) = 2 * C / μ := by
      rw [← Real.rpow_natCast (2 * C / μ) 100, ← Real.rpow_mul hT.le]
      norm_num
    linarith
  rw [Real.rpow_neg hu0.le]
  have h2 : (u ^ ((1 : ℝ) / 100))⁻¹ ≤ (2 * C / μ)⁻¹ := inv_anti₀ hT h1
  calc C * (u ^ ((1 : ℝ) / 100))⁻¹ ≤ C * (2 * C / μ)⁻¹ := by gcongr
    _ = μ / 2 := by field_simp
private theorem cumulantLawsOnTorus_mono {ℓ : StepParameters} {vt C C' x al e β : ℝ} {K m : ℕ} {d : ℝ}
    (hCC : C ≤ C') (hx : 0 < x) (he : 0 ≤ e) (h : CumulantLawsOnTorus ℓ vt C x al e β K m d) :
    CumulantLawsOnTorus ℓ vt C' x al e β K m d := by
  intro q hq f hf
  have hp : 0 ≤ x ^ (-(1 / 100 : ℝ)) + e := add_nonneg (Real.rpow_nonneg hx.le _) he
  exact (h q hq f hf).trans (mul_le_mul_of_nonneg_right hCC hp)
private theorem twoPointPeriodized_eventually (hT : dilatedPairPeriodizationStatement)
    (hP : gaussianTwoPointPair) {ℓ : StepParameters} (hfit : ℓ.Admissible) {vt d : ℝ}
    {φ ψ : (Fin 4 → ℝ) → ℝ} (hv0 : 0 < vt) (hv1 : vt ≤ 1) (hd : 0 < d)
    (hcl : (φ, ψ) ∈ separatedPairsR4 1 vt) (h1 : uniformNorm φ = 1) (h2 : uniformNorm ψ = 1) :
    ∀ᶠ m in atTop, ∀ (C x al e β : ℝ) (K : ℕ), CumulantLawsOnTorus ℓ vt C x al e β K m d →
      |x ^ 2 * (twoPointPeriodized ℓ.side K β (rescale d φ) (rescale d ψ) m).re -
        al ^ 2 * (9 / Real.pi ^ 4 * inverseEighthKernel φ ψ)| ≤ C * (x ^ (-(1 / 100 : ℝ)) + e) := by
  obtain ⟨M, hM⟩ := hT ℓ vt d φ ψ hfit hd hv0 hv1 hcl h1 h2
  have hL2 : 2 ≤ ℓ.side := le_trans (by norm_num) hfit.L_ge
  filter_upwards [eventually_ge_atTop M, torusSide_eventually_ge hL2 (40 * d)] with m hm h40 C x al e β K hlaw
  obtain ⟨hc, ht, hk⟩ := hM m hm
  have hlaw2 := hlaw 1 (Or.inl rfl) _ ht
  have hcon := hP ℓ.side m d vt (by omega) hd h40 _ _ hc
  rw [hcon, hk] at hlaw2
  have hre := (Complex.abs_re_le_norm _).trans hlaw2
  rw [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hre
  exact hre
private theorem one_le_window_width {L r : ℝ} (hL : 1 ≤ L) (hr : 1 ≤ r) : 1 ≤ 2 ^ 12 * L * r := by
  have h : 1 ≤ L * r := one_le_mul_of_one_le_of_one_le hL hr
  have h2 : 2 ^ 12 * L * r = 4096 * (L * r) := by ring
  rw [h2]
  linarith
private theorem window_width_le {L r : ℝ} (hL : 1 ≤ L) (hr : 0 ≤ r) :
    2 ^ 12 * L * r ≤ 2 ^ 14 * L ^ 2 * r := by
  have h1 : L ≤ L ^ 2 := by nlinarith
  have h2 : (2 : ℝ) ^ 12 * L ≤ 2 ^ 14 * L ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right h2 hr
private theorem mul_le_one_of_sq_mul_le {x σ : ℝ} (h16 : 16 ≤ x) (hσ : 0 < σ) (h : x ^ 2 * σ ≤ 4) :
    x * σ ≤ 1 := by
  nlinarith
private theorem torusSide_div_eventually_ge {L : ℕ} (hL : 2 ≤ L) {a : ℝ} (ha : 0 < a) (T : ℝ) :
    ∀ᶠ m in atTop, T ≤ torusSide L m / a :=
  (torusSide_eventually_ge hL (T * a)).mono fun _ h => (le_div_iff₀ ha).2 h
private theorem kernelLowerConst_pos : 0 < TestPairs.kernelLowerConst := by
  unfold TestPairs.kernelLowerConst
  positivity
private theorem lawsMargin_pos {vt : ℝ} (hv : 0 < vt) : 0 < lawsMargin vt := by
  unfold lawsMargin
  have h0 := kernelLowerConst_pos
  exact mul_pos (by norm_num) (lt_min (by positivity) (by positivity))
private theorem lawsMargin_le (vt : ℝ) : lawsMargin vt ≤
    (9 / 16 * (9 / Real.pi ^ 4) * TestPairs.kernelLowerConst * vt ^ 2) / 16 := by
  unfold lawsMargin
  have h := min_le_left (9 / 16 * (9 / Real.pi ^ 4) * TestPairs.kernelLowerConst * vt ^ 2)
    ((3 / 4 : ℝ) ^ 4 * (27 * Real.pi ^ (-8 : ℤ) * (25 / 4 : ℝ) ^ (-16 : ℤ) * vt ^ 4))
  have h2 : ((2 : ℝ)⁻¹) ^ 4 = 1 / 16 := by norm_num
  rw [h2]
  linarith
private theorem inverseEighthKernel_mem_Icc (hG : TestPairs.GeometryAndKernelBounds) {vt : ℝ} (hv0 : 0 < vt)
    (hv1 : vt ≤ 1) {φ ψ : (Fin 4 → ℝ) → ℝ} (hcl : (φ, ψ) ∈ separatedPairsR4 1 vt) (h1 : uniformNorm φ = 1)
    (h2 : uniformNorm ψ = 1) :
    inverseEighthKernel φ ψ ∈ Icc (TestPairs.kernelLowerConst * vt ^ 2) TestPairs.kernelUpperConst := by
  obtain ⟨-, -, x₁, x₂, hc⟩ := (mem_separatedPairs_iff euclidDistR4 closedBallR4 setDistR4
    (fun f => ∫ x, f x) 1 vt (φ, ψ)).1 hcl
  obtain ⟨-, -, -, -, c1, c2, c3, c4⟩ := (hG.1 1 vt ⟨one_pos, hv0, hv1⟩ x₁ x₂ φ ψ hcl hc).1
  rw [h1, h2] at c1 c4
  constructor
  · have := c1.trans c2
    simpa using this
  · have := c3.trans c4
    simpa using this
private theorem bounds_of_abs_sq_mul_sub_le {x G η u : ℝ} (hx : 0 < x) (h : |x ^ 2 * u - G| ≤ η) :
    (G - η) / x ^ 2 ≤ u ∧ u ≤ (G + η) / x ^ 2 := by
  rw [abs_le] at h
  have hx2 : 0 < x ^ 2 := by positivity
  constructor
  · rw [div_le_iff₀ hx2]
    nlinarith [h.1]
  · rw [le_div_iff₀ hx2]
    nlinarith [h.2]
private theorem leading_term_bounds {vt al κ : ℝ} (ha1 : 3 / 4 ≤ al) (ha2 : al ≤ 5 / 4)
    (hκ : κ ∈ Icc (TestPairs.kernelLowerConst * vt ^ 2) TestPairs.kernelUpperConst) :
    9 / 16 * (9 / Real.pi ^ 4) * TestPairs.kernelLowerConst * vt ^ 2 ≤
        al ^ 2 * (9 / Real.pi ^ 4 * κ) ∧ al ^ 2 * (9 / Real.pi ^ 4 * κ) ≤ 225 / 64 := by
  have hb : 0 < 9 / Real.pi ^ 4 := by positivity
  have hf := kernelLowerConst_pos
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ.1
  have hal2 : 9 / 16 ≤ al ^ 2 := by nlinarith
  have hal3 : al ^ 2 ≤ 25 / 16 := by nlinarith
  have hbK : 9 / Real.pi ^ 4 * κ ≤ 9 / 4 := by
    have h1 : 9 / Real.pi ^ 4 * κ ≤ 9 / Real.pi ^ 4 * TestPairs.kernelUpperConst :=
      mul_le_mul_of_nonneg_left hκ.2 hb.le
    have h2 : 9 / Real.pi ^ 4 * TestPairs.kernelUpperConst = 9 / 4 := by
      unfold TestPairs.kernelUpperConst
      field_simp
      norm_num
    linarith
  have hbK0 : 0 ≤ 9 / Real.pi ^ 4 * κ := by positivity
  constructor
  · calc 9 / 16 * (9 / Real.pi ^ 4) * TestPairs.kernelLowerConst * vt ^ 2
        = 9 / 16 * (9 / Real.pi ^ 4 * (TestPairs.kernelLowerConst * vt ^ 2)) := by ring
      _ ≤ al ^ 2 * (9 / Real.pi ^ 4 * κ) := by
        apply mul_le_mul hal2 (mul_le_mul_of_nonneg_left hκ.1 hb.le) (by positivity) (by positivity)
  · calc al ^ 2 * (9 / Real.pi ^ 4 * κ) ≤ 25 / 16 * (9 / 4) :=
        mul_le_mul hal3 hbK hbK0 (by norm_num)
      _ = 225 / 64 := by norm_num
set_option maxHeartbeats 1600000 in
private theorem exists_levelReadAtScale (hV : FourPointBounds.ScaleLevelExists)
    (hT : dilatedPairPeriodizationStatement) (hP : gaussianTwoPointPair)
    (hG : TestPairs.GeometryAndKernelBounds) {ℓ : StepParameters} (hfit : ℓ.Admissible)
    (hR : ExpansionReturnsAt ℓ) (hW : ∀ β : ℝ, ℓ.y₁ ≤ β → HasExpansion ℓ 0 β (wilsonWeight β)) {vt C₀ X₀ : ℝ}
    (hv0 : 0 < vt) (hv1 : vt ≤ 1) {Kr : ResponseParameters}
    (hX : ∀ (β : ℝ) (k : ℕ), (∀ j ≤ k, X₀ ≤ (couplingFlow ℓ β j).1) →
      ∃ al : ℕ → ℝ, ResponseInTheExpansion.IsChainResponseCoeff ℓ Kr β k al ∧ 3 / 4 ≤ al k ∧ al k ≤ 5 / 4 ∧
        ∀ (K m : ℕ) (d e : ℝ),
          Real.exp (Real.log (couplingFlow ℓ β k).1 ^ 3) ≤ torusSide ℓ.side m / levelMesh ℓ.side K k →
          IsLevelWindow ℓ (couplingFlow ℓ β k).1 k (d / levelMesh ℓ.side K k) e →
          CumulantLawsOnTorus ℓ vt C₀ (couplingFlow ℓ β k).1 (al k) e β K m d) :
    ∃ βv nv δv C X : ℝ, 1 ≤ nv ∧ 0 < δv ∧ 0 ≤ C ∧ 16 ≤ X ∧
      ∀ (K : ℕ+) (β d : ℝ) (sides : Set ℝ) (φ ψ : (Fin 4 → ℝ) → ℝ),
        (∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ torusSide ℓ.side m ∈ sides) →
        (φ, ψ) ∈ separatedPairsR4 1 vt → uniformNorm φ = 1 → uniformNorm ψ = 1 →
        βv ≤ β → nv ≤ d / levelMesh ℓ.side K 0 →
        (∀ d' ∈ Icc ((ℓ.side : ℝ) ^ (β / (4 * ℓ.B)) * levelMesh ℓ.side K 0) d,
          twoPointLimsupAtScale ℓ.side K β sides φ ψ d' ≤ ((δv : ℝ) : EReal)) →
        ∃ (k : ℕ) (σ al e : ℝ), LevelReadAtScale ℓ vt C X K β d sides φ ψ k σ al e := by
  have hLpos : 0 < ℓ.side := lt_of_lt_of_le (by norm_num) hfit.L_ge
  have hL2 : 2 ≤ ℓ.side := le_trans (by norm_num) hfit.L_ge
  have hL1 : (1 : ℝ) ≤ (ℓ.side : ℝ) := by exact_mod_cast hLpos
  have hB0 := hfit.B_pos
  have hμ : 0 < lawsMargin vt := lawsMargin_pos hv0
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = lawsMargin vt := ⟨_, rfl⟩
  rw [← hμdef] at hμ
  obtain ⟨Pn, hPdef⟩ : ∃ Pn, Pn = 9 / 16 * (9 / Real.pi ^ 4) * TestPairs.kernelLowerConst * vt ^ 2 :=
    ⟨_, rfl⟩
  have hP0 : 0 < Pn := by
    have h0 := kernelLowerConst_pos
    rw [hPdef]
    positivity
  have hμP : μ ≤ Pn / 16 := by
    rw [hμdef, hPdef]
    exact lawsMargin_le vt
  obtain ⟨C, hCdef⟩ : ∃ C, C = |C₀| + 1 := ⟨_, rfl⟩
  have hC : 0 < C := by
    rw [hCdef]
    positivity
  have hCC : C₀ ≤ C := by
    rw [hCdef]
    linarith [le_abs_self C₀]
  obtain ⟨X, hXdef⟩ : ∃ X, X = max (max (max X₀ 16) (max ℓ.B ℓ.y₁))
      (max (((2 : ℝ) ^ 15 * (ℓ.side : ℝ) ^ 2) ^ 900) ((2 * C / μ) ^ 100)) := ⟨_, rfl⟩
  have hXX₀ : X₀ ≤ X := by
    rw [hXdef]
    exact le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have hX16 : 16 ≤ X := by
    rw [hXdef]
    exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have hXB : ℓ.B ≤ X := by
    rw [hXdef]
    exact le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have hXy : ℓ.y₁ ≤ X := by
    rw [hXdef]
    exact le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  have hXw : ((2 : ℝ) ^ 15 * (ℓ.side : ℝ) ^ 2) ^ 900 ≤ X := by
    rw [hXdef]
    exact le_max_of_le_right (le_max_left _ _)
  have hXd : (2 * C / μ) ^ 100 ≤ X := by
    rw [hXdef]
    exact le_max_of_le_right (le_max_right _ _)
  obtain ⟨nv, hnvdef⟩ : ∃ nv, nv = max 1 (2 * C / μ) := ⟨_, rfl⟩
  have hnv1 : 1 ≤ nv := by
    rw [hnvdef]
    exact le_max_left _ _
  have hnvC : 2 * C / μ ≤ nv := by
    rw [hnvdef]
    exact le_max_right _ _
  obtain ⟨δv, hδdef⟩ : ∃ δv, δv = Pn / 2 / (2 * (X + 2 * ℓ.B) ^ 2) := ⟨_, rfl⟩
  have hδ : 0 < δv := by
    rw [hδdef]
    positivity
  refine ⟨2 * X + 4 * ℓ.B, nv, δv, C, X, hnv1, hδ, hC.le, hX16, ?_⟩
  intro K β d sides φ ψ hS hcl h1 h2 hβ hnv hsm
  have ha0 := levelMesh_pos hLpos K 0
  have hd : 0 < d := by
    have h : 0 < d / levelMesh ℓ.side K 0 := by linarith
    exact (div_pos_iff_of_pos_right ha0).1 h
  have hκ := inverseEighthKernel_mem_Icc hG hv0 hv1 hcl h1 h2
  have hne := neBot_atTop_inf_sides hS
  have hpair := twoPointPeriodized_eventually hT hP hfit hv0 hv1 hd hcl h1 h2
  have hyβ : ℓ.y₁ ≤ β := by linarith
  have hstep : ∀ t : ℕ, (∀ j ≤ t, X ≤ (couplingFlow ℓ β j).1) →
      |(couplingFlow ℓ β (t + 1)).1 - (couplingFlow ℓ β t).1| ≤ 2 * ℓ.B :=
    fun t h => couplingFlow_step_le hR hW hyβ t fun j hj => hXy.trans (h j hj)
  have hprem : ∀ t : ℕ, (∀ j ≤ t, X ≤ (couplingFlow ℓ β j).1) → (couplingFlow ℓ β (t + 1)).1 < X →
      d / meshSize ℓ.side (((K : ℕ) : ℤ) - (t : ℤ)) <
        2 ^ 12 * (ℓ.side : ℝ) * (clusterRange (couplingFlow ℓ β t).1 : ℝ) := by
    intro t hall hlt
    by_contra hge
    rw [not_lt] at hge
    have hat := levelMesh_pos hLpos K t
    have hxt : X ≤ (couplingFlow ℓ β t).1 := hall t le_rfl
    have hxpos : 0 < (couplingFlow ℓ β t).1 := by linarith
    have hstept := hstep t hall
    have hxtop : (couplingFlow ℓ β t).1 ≤ X + 2 * ℓ.B := by
      have := (abs_le.1 hstept).1
      linarith
    have hr1 : (1 : ℝ) ≤ (clusterRange (couplingFlow ℓ β t).1 : ℝ) := by
      have h0 : 0 < (couplingFlow ℓ β t).1 ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hxpos _
      have h1' : 0 < clusterRange (couplingFlow ℓ β t).1 := Nat.ceil_pos.2 h0
      exact_mod_cast h1'
    obtain ⟨n', hn'def⟩ : ∃ n', n' = 2 ^ 12 * (ℓ.side : ℝ) * (clusterRange (couplingFlow ℓ β t).1 : ℝ) :=
      ⟨_, rfl⟩
    have hn1 : 1 ≤ n' := by
      rw [hn'def]
      exact one_le_window_width hL1 hr1
    have hn'win : n' ≤ (couplingFlow ℓ β t).1 ^ ((1 : ℝ) / 90) := by
      have hw := window_le_rpow hLpos (hXw.trans hxt)
      refine le_trans ?_ hw
      rw [hn'def]
      exact window_width_le hL1 (by linarith)
    obtain ⟨d', hd'def⟩ : ∃ d', d' = n' * levelMesh ℓ.side K t := ⟨_, rfl⟩
    have hd'pos : 0 < d' := by
      rw [hd'def]
      exact mul_pos (by linarith) hat
    have hd'd : d' ≤ d := by
      rw [hd'def, hn'def]
      exact (le_div_iff₀ hat).1 hge
    have hd'n : d' / levelMesh ℓ.side K t = n' := by
      rw [hd'def]
      field_simp
    have hwin : IsLevelWindow ℓ (couplingFlow ℓ β t).1 t (d' / levelMesh ℓ.side K t) 0 := by
      left
      rw [hd'n]
      exact ⟨hn'def.ge, hn'win, rfl⟩
    obtain ⟨al, -, hal1, hal2, hlaws⟩ := hX β t fun j hj => hXX₀.trans (hall j hj)
    obtain ⟨hGl, -⟩ := leading_term_bounds hal1 hal2 hκ
    rw [← hPdef] at hGl
    have hpair' := twoPointPeriodized_eventually hT hP hfit hv0 hv1 hd'pos hcl h1 h2
    have hdec : C * (couplingFlow ℓ β t).1 ^ (-(1 / 100 : ℝ)) ≤ μ / 2 :=
      mul_rpow_neg_le_half hC hμ (hXd.trans hxt)
    have hlow : ∀ᶠ m in atTop, 2 * δv ≤
        (twoPointPeriodized ℓ.side K β (rescale d' φ) (rescale d' ψ) m).re := by
      filter_upwards [hpair', torusSide_div_eventually_ge hL2 hat
        (Real.exp (Real.log (couplingFlow ℓ β t).1 ^ 3))] with m hp hroom
      have hl := cumulantLawsOnTorus_mono hCC hxpos le_rfl (hlaws K m d' 0 hroom hwin)
      have h3 := hp C (couplingFlow ℓ β t).1 (al t) 0 β K hl
      rw [add_zero] at h3
      have h4 := (bounds_of_abs_sq_mul_sub_le hxpos h3).1
      have h5 : Pn / 2 / (X + 2 * ℓ.B) ^ 2 ≤
          (al t ^ 2 * (9 / Real.pi ^ 4 * inverseEighthKernel φ ψ) -
            C * (couplingFlow ℓ β t).1 ^ (-(1 / 100 : ℝ))) / (couplingFlow ℓ β t).1 ^ 2 := by
        have hnum : Pn / 2 ≤ al t ^ 2 * (9 / Real.pi ^ 4 * inverseEighthKernel φ ψ) -
            C * (couplingFlow ℓ β t).1 ^ (-(1 / 100 : ℝ)) := by linarith
        have hsq : (couplingFlow ℓ β t).1 ^ 2 ≤ (X + 2 * ℓ.B) ^ 2 := by gcongr
        exact div_le_div₀ (by linarith) hnum (by positivity) hsq
      have h6 : 2 * δv = Pn / 2 / (X + 2 * ℓ.B) ^ 2 := by
        rw [hδdef]
        field_simp
      linarith
    have hlim : ((2 * δv : ℝ) : EReal) ≤ twoPointLimsupAtScale ℓ.side K β sides φ ψ d' :=
      le_limsup_of_frequently_le
        ((hlow.filter_mono inf_le_left).mono fun m h => EReal.coe_le_coe_iff.2 h).frequently
    have htel : ∀ i : ℕ, i ≤ t + 1 →
        (couplingFlow ℓ β 0).1 - (couplingFlow ℓ β i).1 ≤ 2 * ℓ.B * (i : ℝ) := by
      intro i
      induction i with
      | zero =>
        intro _
        simp
      | succ i ih =>
        intro hi
        have h1' := ih (by omega)
        have h2' := (abs_le.1 (hstep i fun j hj => hall j (by omega))).1
        push_cast
        linarith
    have hbt : β / (4 * ℓ.B) ≤ (t : ℝ) := by
      have h0 := htel (t + 1) le_rfl
      have h00 : (couplingFlow ℓ β 0).1 = β := rfl
      rw [h00] at h0
      push_cast at h0
      rw [div_le_iff₀ (by positivity)]
      have e1 : 2 * ℓ.B * ((t : ℝ) + 1) = 2 * (ℓ.B * (t : ℝ)) + 2 * ℓ.B := by ring
      have e2 : (t : ℝ) * (4 * ℓ.B) = 4 * (ℓ.B * (t : ℝ)) := by ring
      rw [e1] at h0
      rw [e2]
      linarith
    have hlower : (ℓ.side : ℝ) ^ (β / (4 * ℓ.B)) * levelMesh ℓ.side K 0 ≤ d' := by
      calc (ℓ.side : ℝ) ^ (β / (4 * ℓ.B)) * levelMesh ℓ.side K 0
          ≤ (ℓ.side : ℝ) ^ (t : ℝ) * levelMesh ℓ.side K 0 := by
            have := Real.rpow_le_rpow_of_exponent_le hL1 hbt
            exact mul_le_mul_of_nonneg_right this ha0.le
        _ = levelMesh ℓ.side K t := by
            rw [Real.rpow_natCast, ← levelMesh_eq_pow_mul hLpos]
        _ ≤ d' := by
            rw [hd'def]
            exact le_mul_of_one_le_left hat.le hn1
    have h7 := EReal.coe_le_coe_iff.1 (hlim.trans (hsm d' ⟨hlower, hd'd⟩))
    linarith
  have hspace0 : levelMesh ℓ.side K 0 = meshSize ℓ.side ((K : ℕ) : ℤ) := by
    simp [levelMesh]
  have hnv' : nv ≤ d / meshSize ℓ.side ((K : ℕ) : ℤ) := by
    rw [← hspace0]
    exact hnv
  obtain ⟨k, e, hk, hwin, he0, he1, he2⟩ := hV ℓ X nv d (K : ℕ) (fun j => (couplingFlow ℓ β j).1) hfit
    hX16 hXB hnv1 (fun u hu => window_le_rpow hLpos (hXw.trans hu)) hβ hstep hnv' hprem
  have hxk : X ≤ (couplingFlow ℓ β k).1 := hk k le_rfl
  have hxpos : 0 < (couplingFlow ℓ β k).1 := by linarith
  have hat := levelMesh_pos hLpos K k
  obtain ⟨al, -, hal1, hal2, hlaws⟩ := hX β k fun j hj => hXX₀.trans (hk j hj)
  obtain ⟨hGl, hGu⟩ := leading_term_bounds hal1 hal2 hκ
  rw [← hPdef] at hGl
  obtain ⟨G, hGdef⟩ : ∃ G, G = al k ^ 2 * (9 / Real.pi ^ 4 * inverseEighthKernel φ ψ) := ⟨_, rfl⟩
  rw [← hGdef] at hGl hGu
  have hdec : C * (couplingFlow ℓ β k).1 ^ (-(1 / 100 : ℝ)) ≤ μ / 2 :=
    mul_rpow_neg_le_half hC hμ (hXd.trans hxk)
  have hCe : C * e ≤ μ / 2 := by
    have hnvp : 0 < nv := by linarith
    have h3 : 1 / nv ≤ μ / (2 * C) := by
      rw [div_le_div_iff₀ hnvp (by positivity)]
      have := (div_le_iff₀ hμ).1 hnvC
      linarith
    calc C * e ≤ C * (μ / (2 * C)) := mul_le_mul_of_nonneg_left (he1.trans h3) hC.le
      _ = μ / 2 := by field_simp
  have heps : C * ((couplingFlow ℓ β k).1 ^ (-(1 / 100 : ℝ)) + e) ≤ μ := by
    rw [mul_add]
    linarith
  have hwin' : IsLevelWindow ℓ (couplingFlow ℓ β k).1 k (d / levelMesh ℓ.side K k) e := hwin
  have hev : ∀ᶠ m in atTop,
      |(couplingFlow ℓ β k).1 ^ 2 *
          (twoPointPeriodized ℓ.side K β (rescale d φ) (rescale d ψ) m).re - G| ≤ μ := by
    filter_upwards [hpair, torusSide_div_eventually_ge hL2 hat
      (Real.exp (Real.log (couplingFlow ℓ β k).1 ^ 3))] with m hp hroom
    have hl := cumulantLawsOnTorus_mono hCC hxpos he0 (hlaws K m d e hroom hwin')
    have h3 := hp C (couplingFlow ℓ β k).1 (al k) e β K hl
    rw [← hGdef] at h3
    exact h3.trans heps
  have hev' := hev.filter_mono (inf_le_left (b := 𝓟 {m : ℕ | torusSide ℓ.side m ∈ sides}))
  obtain ⟨σ, hσ, hσA, hσB⟩ := limsup_coe_mem_Icc
    (F := atTop ⊓ 𝓟 {m : ℕ | torusSide ℓ.side m ∈ sides})
    (u := fun m => (twoPointPeriodized ℓ.side K β (rescale d φ) (rescale d ψ) m).re)
    (A := (G - μ) / (couplingFlow ℓ β k).1 ^ 2) (B := (G + μ) / (couplingFlow ℓ β k).1 ^ 2)
    (hev'.mono fun m h => (bounds_of_abs_sq_mul_sub_le hxpos h).1)
    (hev'.mono fun m h => (bounds_of_abs_sq_mul_sub_le hxpos h).2)
  have hx2 : 0 < (couplingFlow ℓ β k).1 ^ 2 := by positivity
  have hGpos : 0 < G := by linarith
  have hσpos : 0 < σ := lt_of_lt_of_le (div_pos (by linarith) hx2) hσA
  have hlo : G - μ ≤ (couplingFlow ℓ β k).1 ^ 2 * σ := by
    have := (div_le_iff₀ hx2).1 hσA
    linarith
  have hhi : (couplingFlow ℓ β k).1 ^ 2 * σ ≤ G + μ := by
    have := (le_div_iff₀ hx2).1 hσB
    linarith
  have hwin1 : 1 ≤ d / levelMesh ℓ.side K k := by
    rcases hwin' with ⟨h3, -, -⟩ | ⟨-, h3, -, -⟩
    · refine le_trans ?_ h3
      have h0 : 0 < (couplingFlow ℓ β k).1 ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hxpos _
      have h1' : 0 < clusterRange (couplingFlow ℓ β k).1 := Nat.ceil_pos.2 h0
      have hr : (1 : ℝ) ≤ (clusterRange (couplingFlow ℓ β k).1 : ℝ) := by exact_mod_cast h1'
      exact one_le_window_width hL1 hr
    · exact h3
  refine ⟨k, σ, al k, e, hk, ⟨hal1, hal2⟩, hwin1, he0, ?_, ?_, hκ, hσpos, hσ, ?_, ?_, ?_⟩
  · rw [hspace0]
    exact he2
  · rw [← hμdef]
    exact heps
  · refine ⟨(couplingFlow ℓ β k).1 ^ 2 * σ / G - 1, ?_, ?_⟩
    · rw [abs_le]
      have h3 : (couplingFlow ℓ β k).1 ^ 2 * σ / G = 1 + ((couplingFlow ℓ β k).1 ^ 2 * σ - G) / G := by
        field_simp
        ring
      have h4 : ((couplingFlow ℓ β k).1 ^ 2 * σ - G) / G ≤ 1 / 4 := by
        rw [div_le_iff₀ hGpos]
        linarith
      have h5 : -(1 / 4) ≤ ((couplingFlow ℓ β k).1 ^ 2 * σ - G) / G := by
        rw [le_div_iff₀ hGpos]
        linarith
      constructor <;> linarith
    · have h3 : (al k / (couplingFlow ℓ β k).1) ^ 2 * (9 / Real.pi ^ 4 * inverseEighthKernel φ ψ) =
          G / (couplingFlow ℓ β k).1 ^ 2 := by
        rw [hGdef, div_pow]
        ring
      rw [h3]
      field_simp
      ring
  · rw [le_div_iff₀ hσpos]
    have h16 : 16 ≤ (couplingFlow ℓ β k).1 := by linarith
    have h3 : (couplingFlow ℓ β k).1 ^ 2 * σ ≤ 4 := by linarith
    exact mul_le_one_of_sq_mul_le h16 hσpos h3
  · intro m hroom
    exact cumulantLawsOnTorus_mono hCC hxpos he0 (hlaws K m d e hroom hwin')
theorem levelReadByTwoPoint_of_flow (hL : cumulantLawsAlongFlow)
    (hV : FourPointBounds.ScaleLevelExists) (hT : dilatedPairPeriodizationStatement)
    (hP : gaussianTwoPointPair) (hG : TestPairs.GeometryAndKernelBounds) :
    levelReadByTwoPointStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := hL a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hLo hLL T hTa hTL hD hCS hCH hrtle hCd => ?_⟩
  obtain ⟨y₀, Hy⟩ := H L hLo hLL T hTa hTL hD hCS hCH hrtle hCd
  refine ⟨max y₀ T.floorMin, fun y hy hR hW => ?_⟩
  have hfit := hD.fits y (le_trans (le_max_right _ _) hy)
  obtain ⟨Kr, -, hvt⟩ := Hy y (le_trans (le_max_left _ _) hy) hR hW
  refine ⟨hfit, fun vt hv0 hv1 => ?_⟩
  obtain ⟨C, X, hX⟩ := hvt vt hv0 hv1
  exact exists_levelReadAtScale hV hT hP hG hfit hR hW hv0 hv1 hX
end FourPointCondition
end YangMills.Construction
end
