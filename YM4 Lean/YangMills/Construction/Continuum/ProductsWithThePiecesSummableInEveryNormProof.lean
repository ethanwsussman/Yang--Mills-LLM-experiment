import YangMills.Construction.ConfigSpace.IteratedPartialRules
import YangMills.Construction.Continuum.FiniteSeminormsOfRapidlyDecreasingFunctions
import YangMills.Construction.Continuum.FlatnessAndDecayOfTheProductsWithThePiecesProof
import YangMills.Construction.Continuum.ProductsWithThePiecesSummableInEveryNorm
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal Topology
noncomputable section
namespace YangMills.Construction.PieceProducts.Summability
open Bumps ConfigSpace PieceScales ShellPieces ShellPieceBounds
variable {n : ℕ}
theorem dyadicScale_pos (j : ℕ) : 0 < dyadicScale j := zpow_pos (by norm_num) _
theorem dyadicScale_pow (j r : ℕ) : dyadicScale j ^ r = (1 / 2 : ℝ) ^ (j * r) := by
  unfold dyadicScale
  rw [zpow_neg, zpow_natCast, inv_pow, ← pow_mul, one_div, inv_pow]
theorem dyadicScale_le_half {j : ℕ} (hj : 1 ≤ j) : dyadicScale j ≤ 1 / 2 := by apply _root_.YangMills.Construction.PieceProducts.dyadicScale_le_half <;> assumption
theorem diagDistConst_le_eight : diagDistConst ≤ 8 := by apply _root_.YangMills.Construction.PieceProducts.diagDistConst_le_eight <;> assumption
theorem derivBound_nonneg (hn : 1 ≤ n) (r : ℕ) : 0 ≤ derivBound n r := by apply _root_.YangMills.Construction.PieceProducts.derivBound_nonneg' <;> assumption
theorem derivBound_mono (hn : 1 ≤ n) {a b : ℕ} (hab : a ≤ b) :
    derivBound n a ≤ derivBound n b := by apply _root_.YangMills.Construction.PieceProducts.derivBound_le_of_le <;> assumption
theorem unitBallVol_nonneg (d : ℕ) : 0 ≤ unitBallVol d := by
  cases d with
  | zero => simp [unitBallVol]
  | succ d => exact ENNReal.toReal_nonneg
theorem countConst_nonneg (n : ℕ) : 0 ≤ countConst n := by
  have h1 : 0 ≤ volumeCountConst := by
    unfold volumeCountConst
    positivity
  have h2 : 0 ≤ max (halfPairs n * unitBallVol (4 * n - 4)) (unitBallVol (4 * n)) :=
    le_max_of_le_right (unitBallVol_nonneg _)
  unfold countConst
  positivity
def taylorConst (n k r : ℕ) : ℝ :=
  5 ^ k * max 1 ((32 * (n : ℝ)) ^ r / (r.factorial : ℝ))
theorem one_le_taylorConst (n k r : ℕ) : 1 ≤ taylorConst n k r := by
  have h1 : (1 : ℝ) ≤ 5 ^ k := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ max 1 ((32 * (n : ℝ)) ^ r / (r.factorial : ℝ)) := le_max_left _ _
  unfold taylorConst
  nlinarith
theorem weighted_iteratedPartial_le_on_box (hn : 2 ≤ n) (hT : taylorBoundNearDiagonal)
    (hmono : TupleFacts.SeminormMonotone n) {j : ℕ} {z : LatticePt n}
    (hcb : BoxGeometry j z) {f : Config n → ℂ} (hf : f ∈ flatSchwartzSet n) {k l r : ℕ}
    (hr : 1 ≤ r) (hN : decaySeminorm k (l + r) f < ⊤) {x : Config n} (hx : x ∈ openBox j z)
    {β : MultiIndex n} (hβ : β.order ≤ l) :
    (1 + euclidNorm x) ^ k * ‖iteratedPartial β f x‖ ≤
      taylorConst n k r * (1 / 2 : ℝ) ^ (j * r) * (decaySeminorm k (l + r) f).toReal := by
  have hNr : 0 ≤ (decaySeminorm k (l + r) f).toReal := ENNReal.toReal_nonneg
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have T : ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖iteratedPartial β f x‖) ≤
        decaySeminorm k l f := by
      unfold decaySeminorm
      exact le_iSup_of_le β (le_iSup_of_le hβ (le_iSup_of_le x le_rfl))
    have T2 := T.trans (hmono f hf.1 k l k (l + r) le_rfl (by omega))
    have hP := (ENNReal.ofReal_le_iff_le_toReal hN.ne).1 T2
    have h1 := one_le_taylorConst n k r
    simp only [zero_mul, pow_zero, mul_one]
    calc _ ≤ (decaySeminorm k (l + r) f).toReal := hP
      _ = 1 * (decaySeminorm k (l + r) f).toReal := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hNr
  · obtain ⟨-, -, -, hnear, -⟩ := hcb
    obtain ⟨-, y, hy, hxy⟩ := hnear hj x hx
    have hsc := dyadicScale_pos j
    have hsc2 := dyadicScale_le_half hj
    have hδ : 0 < 8 * dyadicScale j := by positivity
    have hxy' : euclidNorm (x - y) ≤ 8 * dyadicScale j :=
      hxy.trans (mul_le_mul_of_nonneg_right diagDistConst_le_eight hsc.le)
    have T := (hT n hn f hf y hy x β r hr).2 (8 * dyadicScale j) hδ hxy' k
    have mono := hmono f hf.1 k (β.order + r) k (l + r) le_rfl (by omega)
    have c0 : 0 ≤ (1 + 8 * dyadicScale j) ^ k *
        ((4 * (n : ℝ) * (8 * dyadicScale j)) ^ r / (r.factorial : ℝ)) := by positivity
    have T2 : ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖iteratedPartial β f x‖) ≤
        ENNReal.ofReal (((1 + 8 * dyadicScale j) ^ k *
          ((4 * (n : ℝ) * (8 * dyadicScale j)) ^ r / (r.factorial : ℝ))) *
          (decaySeminorm k (l + r) f).toReal) := by
      rw [ENNReal.ofReal_mul c0, ENNReal.ofReal_toReal hN.ne]
      exact T.trans (by gcongr)
    have T3 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg c0 hNr)).1 T2
    have hb1 : (1 + 8 * dyadicScale j) ^ k ≤ (5 : ℝ) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hq : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (j * r) := by positivity
    have hb2 : (4 * (n : ℝ) * (8 * dyadicScale j)) ^ r / (r.factorial : ℝ) ≤
        max 1 ((32 * (n : ℝ)) ^ r / (r.factorial : ℝ)) * (1 / 2 : ℝ) ^ (j * r) := by
      have e : (4 * (n : ℝ) * (8 * dyadicScale j)) ^ r / (r.factorial : ℝ) =
          (32 * (n : ℝ)) ^ r / (r.factorial : ℝ) * (1 / 2 : ℝ) ^ (j * r) := by
        rw [← dyadicScale_pow, show 4 * (n : ℝ) * (8 * dyadicScale j) = 32 * n * dyadicScale j by ring,
          mul_pow]
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hq
    have hb : (1 + 8 * dyadicScale j) ^ k *
        ((4 * (n : ℝ) * (8 * dyadicScale j)) ^ r / (r.factorial : ℝ)) ≤
        taylorConst n k r * (1 / 2 : ℝ) ^ (j * r) := by
      have := mul_le_mul hb1 hb2 (by positivity) (by positivity)
      unfold taylorConst
      linarith
    exact T3.trans (mul_le_mul_of_nonneg_right hb hNr)
theorem decaySeminorm_pieceMul_le (hn : 1 ≤ n) (hR : IteratedPartialRules)
    {j : ℕ} {z : LatticePt n}
    (hpf : PieceProperties j z) (hcb : BoxGeometry j z) {f : Config n → ℂ} (hf : ContDiff ℝ ∞ f)
    {k l : ℕ} {P : ℝ} (hP : 0 ≤ P)
    (hb : ∀ x ∈ openBox j z, ∀ β : MultiIndex n, β.order ≤ l →
      (1 + euclidNorm x) ^ (k + (4 * n + 2)) * ‖iteratedPartial β f x‖ ≤ P) :
    decaySeminorm k l (pieceMul j z f) ≤
      ENNReal.ofReal (2 ^ l * (derivBound n l * 2 ^ (j * l)) *
        (1 + Real.sqrt n) ^ (4 * n + 2) * P *
        ((1 + euclidNorm (pieceCentre j z)) ^ (4 * n + 2))⁻¹) := by
  obtain ⟨-, -, -, hconst, hlocal, hleib⟩ := hR n
  obtain ⟨hsm, -, hts, hbox, -, -, -, hder⟩ := hpf
  have hC := derivBound_nonneg hn l
  unfold decaySeminorm
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun x => ?_
  have hx0 : 0 ≤ euclidNorm x := Real.sqrt_nonneg _
  by_cases hx : x ∈ tsupport (piece j z)
  · refine ENNReal.ofReal_le_ofReal ?_
    have hxo : x ∈ openBox j z := hbox (hts hx)
    have hw := (hcb.2.2.2.2 x hxo).2.1
    have hy0 : 0 ≤ euclidNorm (pieceCentre j z) := Real.sqrt_nonneg _
    have hX : 0 < 1 + euclidNorm x := by linarith
    have hY : 0 < 1 + euclidNorm (pieceCentre j z) := by linarith
    have hXk : 0 < (1 + euclidNorm x) ^ (k + (4 * n + 2)) := pow_pos hX _
    have hβ : ∀ γ : MultiIndex n, γ.order ≤ l → ‖iteratedPartial γ f x‖ ≤
        P * ((1 + euclidNorm x) ^ (k + (4 * n + 2)))⁻¹ := by
      intro γ hγ
      rw [← div_eq_mul_inv, le_div_iff₀ hXk]
      linarith [hb x hxo γ hγ]
    have hχ : ∀ γ : MultiIndex n, γ.order ≤ l → ‖iteratedPartial γ (pieceC j z) x‖ ≤
        derivBound n l * 2 ^ (j * l) := by
      intro γ hγ
      refine (hder γ x).trans ?_
      exact mul_le_mul (derivBound_mono hn hγ)
        (pow_le_pow_right₀ one_le_two (Nat.mul_le_mul_left j hγ)) (by positivity) hC
    have L := hleib l _ _ (pieceC j z) f x hsm.1 hf hχ hβ α hα
    have e : pieceMul j z f = fun y => pieceC j z y * f y := rfl
    rw [e]
    have hinv : ((1 + euclidNorm x) ^ (4 * n + 2))⁻¹ ≤
        (1 + Real.sqrt n) ^ (4 * n + 2) * ((1 + euclidNorm (pieceCentre j z)) ^ (4 * n + 2))⁻¹ := by
      have hXm : 0 < (1 + euclidNorm x) ^ (4 * n + 2) := pow_pos hX _
      have hYm : 0 < (1 + euclidNorm (pieceCentre j z)) ^ (4 * n + 2) := pow_pos hY _
      have hYX : (1 + euclidNorm (pieceCentre j z)) ^ (4 * n + 2) ≤
          (1 + Real.sqrt n) ^ (4 * n + 2) * (1 + euclidNorm x) ^ (4 * n + 2) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ hY.le hw _
      rw [← div_eq_mul_inv, le_div_iff₀ hYm, inv_mul_le_iff₀ hXm]
      linarith
    have hsplit : (1 + euclidNorm x) ^ k *
        ((1 + euclidNorm x) ^ (k + (4 * n + 2)))⁻¹ =
        ((1 + euclidNorm x) ^ (4 * n + 2))⁻¹ := by
      have h1 : (1 + euclidNorm x) ^ k ≠ 0 := (pow_pos hX _).ne'
      rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ h1, one_mul]
    have hc : 0 ≤ 2 ^ l * (derivBound n l * 2 ^ (j * l)) * P := by positivity
    calc (1 + euclidNorm x) ^ k *
          ‖iteratedPartial α (fun y => pieceC j z y * f y) x‖
        ≤ (1 + euclidNorm x) ^ k * (2 ^ l * (derivBound n l * 2 ^ (j * l)) *
            (P * ((1 + euclidNorm x) ^ (k + (4 * n + 2)))⁻¹)) :=
          mul_le_mul_of_nonneg_left L (by positivity)
      _ = 2 ^ l * (derivBound n l * 2 ^ (j * l)) * P *
            ((1 + euclidNorm x) ^ k * ((1 + euclidNorm x) ^ (k + (4 * n + 2)))⁻¹) := by ring
      _ = 2 ^ l * (derivBound n l * 2 ^ (j * l)) * P *
            ((1 + euclidNorm x) ^ (4 * n + 2))⁻¹ := by rw [hsplit]
      _ ≤ 2 ^ l * (derivBound n l * 2 ^ (j * l)) * P *
            ((1 + Real.sqrt n) ^ (4 * n + 2) *
              ((1 + euclidNorm (pieceCentre j z)) ^ (4 * n + 2))⁻¹) :=
          mul_le_mul_of_nonneg_left hinv hc
      _ = _ := by ring
  · have h0 : piece j z =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
    have h1 : pieceMul j z f =ᶠ[𝓝 x] (0 : Config n → ℂ) :=
      h0.mono fun y hy => by simp [pieceMul, hy]
    have h2 := hlocal α _ _ x h1
    have h3 : iteratedPartial α (0 : Config n → ℂ) x = 0 := by
      have h4 := hconst α 0 (0 : Config n → ℂ) (contDiff_const (c := (0 : ℂ)))
      simp only [smul_zero, zero_smul] at h4
      rw [h4]
      rfl
    rw [h2, h3]
    simp
def annulusBound (n l r : ℕ) (G : ℝ) (j t : ℕ) : ℝ :=
  G * (2 ^ (j * l) * (1 / 2 : ℝ) ^ (j * r)) * ((1 + (t : ℝ)) ^ (4 * n + 2))⁻¹
theorem tsum_inv_one_add_sq_le_two :
    ∑' t : ℕ, ENNReal.ofReal (((1 + (t : ℝ)) ^ 2)⁻¹) ≤ 2 := by
  have h := (hasSum_nat_add_iff' (f := fun m : ℕ => 1 / (m : ℝ) ^ 2) 1).2 hasSum_zeta_two
  have h1 : HasSum (fun t : ℕ => ((1 + (t : ℝ)) ^ 2)⁻¹) (Real.pi ^ 2 / 6) := by
    have h' : (fun t : ℕ => ((1 + (t : ℝ)) ^ 2)⁻¹) = fun t : ℕ => 1 / ((t + 1 : ℕ) : ℝ) ^ 2 := by
      funext t
      push_cast
      rw [add_comm, one_div]
    rw [h']
    simpa using h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => by positivity) h1.summable, h1.tsum_eq]
  have h2 : Real.pi ^ 2 / 6 ≤ 2 := by
    have := Real.pi_lt_d2
    have := Real.pi_pos
    nlinarith
  calc ENNReal.ofReal (Real.pi ^ 2 / 6) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal h2
    _ = 2 := by simp
theorem tsum_half_pow_le_two : ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) ≤ 2 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => by positivity) hasSum_geometric_two.summable,
    hasSum_geometric_two.tsum_eq]
  simp
theorem tsum_tsum_half_pow_mul_inv_sq_le {K : ℝ} (hK : 0 ≤ K) :
    ∑' j : ℕ, ∑' t : ℕ, ENNReal.ofReal (K * (1 / 2 : ℝ) ^ j * ((1 + (t : ℝ)) ^ 2)⁻¹) ≤
      ENNReal.ofReal (4 * K) := by
  have h : ∀ (j t : ℕ), ENNReal.ofReal (K * (1 / 2 : ℝ) ^ j * ((1 + (t : ℝ)) ^ 2)⁻¹) =
      ENNReal.ofReal K * ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
        ENNReal.ofReal (((1 + (t : ℝ)) ^ 2)⁻¹) := by
    intro j t
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hK]
  simp_rw [h, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
  calc ENNReal.ofReal K * (∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j)) *
          ∑' t : ℕ, ENNReal.ofReal (((1 + (t : ℝ)) ^ 2)⁻¹)
      ≤ ENNReal.ofReal K * 2 * 2 := by
        gcongr
        · exact tsum_half_pow_le_two
        · exact tsum_inv_one_add_sq_le_two
    _ = ENNReal.ofReal (4 * K) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), mul_assoc, mul_comm]
        norm_num
theorem tsum_activeIndices_le (F : activeIndices n → ℝ≥0∞) (g : ℕ → ℕ → ℝ≥0∞)
    (hF : ∀ p : activeIndices n, F p ≤ g p.1.1 ⌊euclidNorm (pieceCentre p.1.1 p.1.2)⌋₊) :
    ∑' p, F p ≤ ∑' (j : ℕ) (t : ℕ), (cardOf (centresInAnnulus n j t) : ℝ≥0∞) * g j t := by
  let E : Type := Σ (j : ℕ) (t : ℕ), centresInAnnulus n j t
  have hnonneg : ∀ x : Config n, 0 ≤ euclidNorm x := fun x => Real.sqrt_nonneg _
  let e : activeIndices n → E := fun p =>
    ⟨p.1.1, ⌊euclidNorm (pieceCentre p.1.1 p.1.2)⌋₊, p.1.2, p.2,
      Nat.floor_le (hnonneg _), Nat.lt_floor_add_one _⟩
  have he : Function.Injective e := by
    intro p p' h
    have h1 : (fun s : E => ((s.1, s.2.2.1) : ℕ × LatticePt n)) (e p) =
        (fun s : E => ((s.1, s.2.2.1) : ℕ × LatticePt n)) (e p') :=
      congrArg (fun s : E => ((s.1, s.2.2.1) : ℕ × LatticePt n)) h
    exact Subtype.ext h1
  calc ∑' p, F p ≤ ∑' p, (fun s : E => g s.1 s.2.1) (e p) := ENNReal.tsum_le_tsum hF
    _ ≤ ∑' s : E, g s.1 s.2.1 := ENNReal.tsum_comp_le_tsum_of_injective he _
    _ = ∑' (j : ℕ) (t : ℕ), (cardOf (centresInAnnulus n j t) : ℝ≥0∞) * g j t := by
        rw [ENNReal.tsum_sigma']
        refine tsum_congr fun j => ?_
        rw [ENNReal.tsum_sigma']
        refine tsum_congr fun t => ?_
        exact ENNReal.tsum_set_const (centresInAnnulus n j t) (g j t)
theorem two_pow_mul_half_pow_mul_two_pow (j l m : ℕ) :
    (2 : ℝ) ^ (j * l) * (1 / 2 : ℝ) ^ (j * (l + 4 * m + 5)) * 2 ^ (j * (4 * m + 4)) =
      (1 / 2 : ℝ) ^ j := by
  have h : (1 / 2 : ℝ) ^ (j * (l + 4 * m + 5)) =
      (1 / 2 : ℝ) ^ (j * l) * (1 / 2 : ℝ) ^ (j * (4 * m + 4)) * (1 / 2 : ℝ) ^ j := by
    simp only [← pow_add]
    congr 1
    ring
  have e : ∀ a : ℕ, (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ a = 1 := fun a => by
    rw [← mul_pow]
    norm_num
  rw [h]
  calc (2 : ℝ) ^ (j * l) * ((1 / 2 : ℝ) ^ (j * l) * (1 / 2 : ℝ) ^ (j * (4 * m + 4)) *
        (1 / 2 : ℝ) ^ j) * 2 ^ (j * (4 * m + 4))
      = ((2 : ℝ) ^ (j * l) * (1 / 2 : ℝ) ^ (j * l)) *
          ((2 : ℝ) ^ (j * (4 * m + 4)) * (1 / 2 : ℝ) ^ (j * (4 * m + 4))) * (1 / 2 : ℝ) ^ j := by
        ring
    _ = (1 / 2 : ℝ) ^ j := by rw [e, e, one_mul, one_mul]
theorem dyadicScale_zpow (j m : ℕ) :
    dyadicScale j ^ (4 - 4 * ((m + 2 : ℕ) : ℤ)) = 2 ^ (j * (4 * m + 4)) := by
  have h : (4 - 4 * ((m + 2 : ℕ) : ℤ)) = -((4 * m + 4 : ℕ) : ℤ) := by
    push_cast
    ring
  unfold dyadicScale
  rw [h, ← zpow_mul, neg_mul_neg, ← Nat.cast_mul, zpow_natCast]
theorem cardOf_mul_annulusBound_le {m : ℕ} (hcount : CentreCount (m + 2)) (l : ℕ) {G : ℝ}
    (hG : 0 ≤ G) (j t : ℕ) :
    (cardOf (centresInAnnulus (m + 2) j t) : ℝ≥0∞) *
        ENNReal.ofReal (annulusBound (m + 2) l (l + 4 * m + 5) G j t) ≤
      ENNReal.ofReal (countConst (m + 2) * G * (1 / 2 : ℝ) ^ j *
        ((1 + (t : ℝ)) ^ 2)⁻¹) := by
  have hN := countConst_nonneg (m + 2)
  have hx : (0 : ℝ) < 1 + t := by positivity
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h0 := (hcount 0 t).2 rfl
    have h1 : 0 ≤ countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * (m + 2)) := by positivity
    calc (cardOf (centresInAnnulus (m + 2) 0 t) : ℝ≥0∞) *
          ENNReal.ofReal (annulusBound (m + 2) l (l + 4 * m + 5) G 0 t)
        ≤ ENNReal.ofReal (countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * (m + 2))) *
          ENNReal.ofReal (annulusBound (m + 2) l (l + 4 * m + 5) G 0 t) := by gcongr
      _ = ENNReal.ofReal (countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * (m + 2)) *
            annulusBound (m + 2) l (l + 4 * m + 5) G 0 t) := (ENNReal.ofReal_mul h1).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
          unfold annulusBound
          have h2 : (1 + (t : ℝ)) ^ (4 * (m + 2) + 2) =
              (1 + (t : ℝ)) ^ (4 * (m + 2)) * (1 + (t : ℝ)) ^ 2 := by
            rw [← pow_add]
          have hp : (1 + (t : ℝ)) ^ (4 * (m + 2)) ≠ 0 := (pow_pos hx _).ne'
          rw [h2, mul_inv]
          simp only [zero_mul, pow_zero, mul_one]
          calc countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * (m + 2)) *
                (G * (((1 + (t : ℝ)) ^ (4 * (m + 2)))⁻¹ * ((1 + (t : ℝ)) ^ 2)⁻¹))
              = countConst (m + 2) * G * ((1 + (t : ℝ)) ^ 2)⁻¹ *
                  ((1 + (t : ℝ)) ^ (4 * (m + 2)) * ((1 + (t : ℝ)) ^ (4 * (m + 2)))⁻¹) := by ring
            _ = _ := by rw [mul_inv_cancel₀ hp, mul_one]
  · have h0 := (hcount j t).1 hj
    have hs : 0 < dyadicScale j := dyadicScale_pos j
    have h1 : 0 ≤ countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * (m + 2) - 4) *
        dyadicScale j ^ (4 - 4 * ((m + 2 : ℕ) : ℤ)) := by positivity
    calc (cardOf (centresInAnnulus (m + 2) j t) : ℝ≥0∞) *
          ENNReal.ofReal (annulusBound (m + 2) l (l + 4 * m + 5) G j t)
        ≤ ENNReal.ofReal (countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * (m + 2) - 4) *
            dyadicScale j ^ (4 - 4 * ((m + 2 : ℕ) : ℤ))) *
          ENNReal.ofReal (annulusBound (m + 2) l (l + 4 * m + 5) G j t) := by gcongr
      _ = ENNReal.ofReal (countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * (m + 2) - 4) *
            dyadicScale j ^ (4 - 4 * ((m + 2 : ℕ) : ℤ)) *
            annulusBound (m + 2) l (l + 4 * m + 5) G j t) := (ENNReal.ofReal_mul h1).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          unfold annulusBound
          have h2 : 4 * (m + 2) - 4 = 4 * m + 4 := by omega
          have h3 : (1 + (t : ℝ)) ^ (4 * (m + 2) + 2) =
              (1 + (t : ℝ)) ^ (4 * m + 4) * (1 + (t : ℝ)) ^ 6 := by
            rw [← pow_add]
            congr 1
          have h4 : ((1 + (t : ℝ)) ^ 6)⁻¹ ≤ ((1 + (t : ℝ)) ^ 2)⁻¹ :=
            inv_anti₀ (pow_pos hx 2)
              (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) t]) (by norm_num))
          have hp : (1 + (t : ℝ)) ^ (4 * m + 4) ≠ 0 := (pow_pos hx _).ne'
          rw [h2, dyadicScale_zpow, h3, mul_inv]
          calc countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * m + 4) * 2 ^ (j * (4 * m + 4)) *
                (G * (2 ^ (j * l) * (1 / 2 : ℝ) ^ (j * (l + 4 * m + 5))) *
                  (((1 + (t : ℝ)) ^ (4 * m + 4))⁻¹ * ((1 + (t : ℝ)) ^ 6)⁻¹))
              = countConst (m + 2) * G *
                  ((2 : ℝ) ^ (j * l) * (1 / 2 : ℝ) ^ (j * (l + 4 * m + 5)) *
                    2 ^ (j * (4 * m + 4))) * ((1 + (t : ℝ)) ^ 6)⁻¹ *
                  ((1 + (t : ℝ)) ^ (4 * m + 4) * ((1 + (t : ℝ)) ^ (4 * m + 4))⁻¹) := by ring
            _ = countConst (m + 2) * G * (1 / 2 : ℝ) ^ j * ((1 + (t : ℝ)) ^ 6)⁻¹ := by
                rw [two_pow_mul_half_pow_mul_two_pow, mul_inv_cancel₀ hp, mul_one]
            _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
theorem pieceMulSummableSeminorms_holds (hPieces : ShellPiecesBound)
    (hT : taylorBoundNearDiagonal)
    (hFacts : TupleFacts.BasicFacts)
    (hFin : SchwartzSeminormsFinite)
    (hR : IteratedPartialRules) :
    PieceMulSummableSeminorms := by
  intro n hn f hf k l
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : 1 ≤ m + 2 := by omega
  obtain ⟨-, hPF, -, -, hCB, hcount⟩ := hPieces (m + 2) h1
  have hmono : TupleFacts.SeminormMonotone (m + 2) := (hFacts (m + 2) hn).2.2.1
  obtain ⟨r, hrdef⟩ : ∃ r, r = l + 4 * m + 5 := ⟨_, rfl⟩
  have hr : 1 ≤ r := by omega
  have hN : decaySeminorm (k + (4 * (m + 2) + 2)) (l + r) f < ⊤ :=
    ((hFin (m + 2) h1 (k + (4 * (m + 2) + 2)) (l + r) 0).1 f hf.1).1
  obtain ⟨Nr, hNrdef⟩ : ∃ Nr, Nr = (decaySeminorm (k + (4 * (m + 2) + 2)) (l + r) f).toReal :=
    ⟨_, rfl⟩
  have hNr : 0 ≤ Nr := hNrdef ▸ ENNReal.toReal_nonneg
  obtain ⟨D, hDdef⟩ : ∃ D, D = taylorConst (m + 2) (k + (4 * (m + 2) + 2)) r := ⟨_, rfl⟩
  have hD : 0 ≤ D := by
    rw [hDdef]
    linarith [one_le_taylorConst (m + 2) (k + (4 * (m + 2) + 2)) r]
  have hC := derivBound_nonneg h1 l
  obtain ⟨G, hGdef⟩ : ∃ G, G = 2 ^ l * derivBound (m + 2) l *
      (1 + Real.sqrt ((m + 2 : ℕ) : ℝ)) ^ (4 * (m + 2) + 2) * D * Nr := ⟨_, rfl⟩
  have hG : 0 ≤ G := by
    rw [hGdef]
    positivity
  have hone : ∀ p : activeIndices (m + 2),
      decaySeminorm k l (pieceMul p.1.1 p.1.2 f) ≤
        ENNReal.ofReal (annulusBound (m + 2) l r G p.1.1
          ⌊euclidNorm (pieceCentre p.1.1 p.1.2)⌋₊) := by
    rintro ⟨⟨j, z⟩, hp⟩
    have hcb : BoxGeometry j z := hCB (j, z) hp
    have hP : 0 ≤ D * (1 / 2 : ℝ) ^ (j * r) * Nr := by positivity
    have hb : ∀ x ∈ openBox j z, ∀ β : MultiIndex (m + 2), β.order ≤ l →
        (1 + euclidNorm x) ^ (k + (4 * (m + 2) + 2)) * ‖iteratedPartial β f x‖ ≤
          D * (1 / 2 : ℝ) ^ (j * r) * Nr := by
      intro x hx β hβ
      rw [hDdef, hNrdef]
      exact weighted_iteratedPartial_le_on_box hn hT hmono hcb hf hr hN hx hβ
    refine (decaySeminorm_pieceMul_le h1 hR (hPF j z) hcb hf.1.1 hP hb).trans
      (ENNReal.ofReal_le_ofReal ?_)
    show _ ≤ annulusBound (m + 2) l r G j ⌊euclidNorm (pieceCentre j z)⌋₊
    unfold annulusBound
    have hy0 : 0 ≤ euclidNorm (pieceCentre j z) := Real.sqrt_nonneg _
    have ht : ((⌊euclidNorm (pieceCentre j z)⌋₊ : ℕ) : ℝ) ≤ euclidNorm (pieceCentre j z) :=
      Nat.floor_le hy0
    have hinv : ((1 + euclidNorm (pieceCentre j z)) ^ (4 * (m + 2) + 2))⁻¹ ≤
        ((1 + ((⌊euclidNorm (pieceCentre j z)⌋₊ : ℕ) : ℝ)) ^ (4 * (m + 2) + 2))⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) _)
    have hc : 0 ≤ G * (2 ^ (j * l) * (1 / 2 : ℝ) ^ (j * r)) := by positivity
    calc 2 ^ l * (derivBound (m + 2) l * 2 ^ (j * l)) *
          (1 + Real.sqrt ((m + 2 : ℕ) : ℝ)) ^ (4 * (m + 2) + 2) *
          (D * (1 / 2 : ℝ) ^ (j * r) * Nr) *
          ((1 + euclidNorm (pieceCentre j z)) ^ (4 * (m + 2) + 2))⁻¹
        = G * (2 ^ (j * l) * (1 / 2 : ℝ) ^ (j * r)) *
          ((1 + euclidNorm (pieceCentre j z)) ^ (4 * (m + 2) + 2))⁻¹ := by
          rw [hGdef]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv hc
  have hK : 0 ≤ countConst (m + 2) * G :=
    mul_nonneg (countConst_nonneg _) hG
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := 4 * (countConst (m + 2) * G)))
  refine (ENNReal.tsum_le_tsum hone).trans ?_
  refine (tsum_activeIndices_le _ (fun j t => ENNReal.ofReal (annulusBound (m + 2) l r G j t))
    fun _ => le_rfl).trans ?_
  rw [hrdef]
  exact le_trans (ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun t =>
    cardOf_mul_annulusBound_le hcount l hG j t) (tsum_tsum_half_pow_mul_inv_sq_le hK)
end YangMills.Construction.PieceProducts.Summability
end
