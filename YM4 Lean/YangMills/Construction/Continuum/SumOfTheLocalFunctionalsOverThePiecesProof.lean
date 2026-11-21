import YangMills.Construction.Continuum.LocalFunctionalsLinearBoundedAndValueOnTensors
import YangMills.Construction.Continuum.ProductsWithThePiecesSummableInEveryNormProof
import YangMills.Construction.Continuum.SumOfTheLocalFunctionalsOverThePieces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PieceLocalSum
open ExtensionConstants Bumps PieceSystems ConfigSpace PieceProducts
  PieceScales ShellPieces ShellPieceBounds
open scoped ENNReal
theorem tsum_tsum_geom_inv_sq_le {K : ℝ} (hK : 0 ≤ K) :
    ∑' j : ℕ, ∑' t : ℕ,
        ENNReal.ofReal (K * (1 / 2 : ℝ) ^ j * ((1 + (t : ℝ)) ^ 2)⁻¹) ≤
      ENNReal.ofReal (4 * K) := by apply _root_.YangMills.Construction.PieceProducts.Summability.tsum_tsum_half_pow_mul_inv_sq_le <;> assumption
theorem tsum_activeIndices_le {n : ℕ} (f : activeIndices n → ℝ≥0∞) (g : ℕ → ℕ → ℝ≥0∞)
    (hf : ∀ p : activeIndices n,
      f p ≤ g p.1.1 ⌊euclidNorm (pieceCentre p.1.1 p.1.2)⌋₊) :
    ∑' p, f p ≤ ∑' (j : ℕ) (t : ℕ), (cardOf (centresInAnnulus n j t) : ℝ≥0∞) * g j t := by apply _root_.YangMills.Construction.PieceProducts.Summability.tsum_activeIndices_le <;> assumption
theorem max_one_zpow_neg_le {d : ℝ≥0∞} (a j : ℕ)
    (hd : ENNReal.ofReal (1 / 2 * (2 : ℝ) ^ (-(j : ℤ))) ≤ d) :
    max 1 (d.toReal ^ (-(a : ℤ))) ≤ 2 ^ a * 2 ^ (j * a) := by
  have h1 : (1 : ℝ) ≤ 2 ^ a * 2 ^ (j * a) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  refine max_le h1 ?_
  by_cases htop : d = ⊤
  · subst htop
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · rw [ENNReal.toReal_top, zpow_neg, zpow_natCast, zero_pow ha.ne', inv_zero]
      exact zero_le_one.trans h1
  · have hs : 0 < 1 / 2 * (2 : ℝ) ^ (-(j : ℤ)) := by positivity
    have h2 : 1 / 2 * (2 : ℝ) ^ (-(j : ℤ)) ≤ d.toReal :=
      (ENNReal.ofReal_le_iff_le_toReal htop).1 hd
    have h4 : (2 : ℝ) ^ a * 2 ^ (j * a) = ((1 / 2 * (2 : ℝ) ^ (-(j : ℤ))) ^ a)⁻¹ := by
      simp only [zpow_neg, zpow_natCast, one_div, mul_pow, inv_pow, mul_inv, inv_inv, ← pow_mul]
    rw [zpow_neg, zpow_natCast, h4]
    exact inv_anti₀ (pow_pos hs a) (pow_le_pow_left₀ hs.le h2 a)
theorem pieceSide_zpow_neg (n j : ℕ) :
    pieceSide j ^ (-(n : ℤ)) = (sideConstant ^ n)⁻¹ * 2 ^ (j * n) := by
  unfold pieceSide dyadicScale
  simp only [zpow_neg, zpow_natCast, mul_pow, inv_pow, mul_inv, inv_inv, ← pow_mul]
theorem sideConstant_pos' : 0 < sideConstant := isSideConstant_sideConstant.1
theorem derivConst_nonneg : 0 ≤ derivConst := by
  have h : 2 * twiceGevreyConst * sideConstant⁻¹ ≤
      max DiagonalShells.tupleCutoffConst (2 * twiceGevreyConst * sideConstant⁻¹) :=
    le_max_right _ _
  have h1 : 0 < sideConstant⁻¹ := inv_pos.2 sideConstant_pos'
  have h2 : 0 ≤ 2 * twiceGevreyConst * sideConstant⁻¹ := by
    unfold twiceGevreyConst gevreyConst
    positivity
  unfold derivConst
  linarith
theorem leibnizConst_nonneg (n : ℕ) : 0 ≤ leibnizConst n := by
  have h1 : 0 ≤ normalizerBound := zero_le_one.trans (le_max_left _ _)
  have h2 := derivConst_nonneg
  rw [leibnizConst_eq]
  positivity
theorem taylorConst_nonneg (n : ℕ) : 0 ≤ taylorConst n := by apply _root_.YangMills.Construction.PieceProducts.taylorConst_nonneg' <;> assumption
theorem countConst_nonneg (n : ℕ) : 0 ≤ countConst n := by apply _root_.YangMills.Construction.PieceProducts.Summability.countConst_nonneg <;> assumption
theorem localConst_nonneg : 0 ≤ localConst := by
  have h : 0 ≤ TestFunctions.uniformNorm fun y : Fin 4 → ℝ => (cubeBump y : ℂ) :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  have h1 : 2 * TestFunctions.uniformNorm (fun y : Fin 4 → ℝ => (cubeBump y : ℂ)) ≤ modeConst :=
    le_max_left _ _
  unfold localConst
  linarith
def singlePieceBound (n a : ℕ) (c G : ℝ) (j t : ℕ) : ℝ :=
  (localConst / sideConstant) ^ n * max 1 c ^ n * G * 2 ^ a * (2 ^ (j * a) * 2 ^ (j * n)) *
    (leibnizConst n * taylorConst n * (2 ^ (j * (5 * n + a - 3)))⁻¹ *
      ((1 + (t : ℝ)) ^ (4 * n + 2))⁻¹)
def quarterConst (n a : ℕ) (c G : ℝ) : ℝ :=
  (localConst / sideConstant) ^ n * max 1 c ^ n * G * 2 ^ a *
    (leibnizConst n * taylorConst n) * countConst n
theorem scaledSupNorm_nonneg {n : ℕ} (ν : ℕ) {m : ℝ} (hm : 0 ≤ m) (Ψ : Config n → ℂ) :
    0 ≤ scaledSupNorm ν m Ψ :=
  Real.iSup_nonneg fun _ => mul_nonneg (pow_nonneg hm _) (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem localPairing_piece_le
    (hlocal : LocalPairingProps.LocalPairingProperties)
    (hfacts : TupleFacts.BasicFacts)
    (hflat : ProductBounds)
    {n : ℕ} {c : ℝ} {a : ℕ} {G : ℝ} {T : smoothRealTupleSet n → ℝ}
    (hB : SeparatedBallBound c a G T) {φ : Config n → ℂ} (hφ : φ ∈ flatSchwartzSet n)
    (p : activeIndices n) (t : ℕ) (ht : (t : ℝ) ≤ euclidNorm (pieceCentre p.1.1 p.1.2)) :
    ENNReal.ofReal ‖localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 φ)‖ ≤
      ENNReal.ofReal (singlePieceBound n a c G p.1.1 t) *
        decaySeminorm (4 * n + 2) (10 * n + a - 2) φ := by
  obtain ⟨⟨j, z⟩, hp⟩ := p
  dsimp only at ht ⊢
  have hn : 2 ≤ n := hB.1
  have hG : 0 ≤ G := hB.2.2.1
  obtain ⟨⟨hsep, -, -, -, hdist, hsm⟩, hdecay⟩ := hflat n hn j z hp
  have hφs : φ ∈ SmoothMaps.smoothSet (Config n) := hφ.1.1
  have hΦ := (hsm φ hφs).2.2
  have hbd := (hlocal n c a G T _ hB hsep).2.2.2.1 _ hΦ
  have hside : 0 ≤ pieceSide j := (mul_pos sideConstant_pos' (zpow_pos (by norm_num) _)).le
  have hS : 0 ≤ scaledSupNorm (5 * n + 1) (pieceSide j) (pieceMul j z φ) :=
    scaledSupNorm_nonneg _ hside _
  have hC := localConst_nonneg
  have hM : 0 ≤ max 1 c := le_max_of_le_left zero_le_one
  have hr := sideConstant_pos'
  set E : ℝ := (localConst / sideConstant) ^ n * max 1 c ^ n * G * 2 ^ a *
    (2 ^ (j * a) * 2 ^ (j * n)) with hE
  have hE0 : 0 ≤ E := by positivity
  have h1 : ‖localPairing T (pieceBoxSystem ⟨(j, z), hp⟩) (pieceMul j z φ)‖ ≤
      E * scaledSupNorm (5 * n + 1) (pieceSide j) (pieceMul j z φ) := by
    refine hbd.trans ?_
    have hsd := max_one_zpow_neg_le a j hdist
    change localConst ^ n * max 1 c ^ n * G *
        max 1 ((pieceBoxSystem ⟨(j, z), hp⟩).boxGap.toReal ^ (-(a : ℤ))) *
        pieceSide j ^ (-(n : ℤ)) * scaledSupNorm (5 * n + 1) (pieceSide j) (pieceMul j z φ) ≤ _
    rw [pieceSide_zpow_neg]
    refine mul_le_mul_of_nonneg_right ?_ hS
    calc localConst ^ n * max 1 c ^ n * G *
          max 1 ((pieceBoxSystem ⟨(j, z), hp⟩).boxGap.toReal ^ (-(a : ℤ))) *
          ((sideConstant ^ n)⁻¹ * 2 ^ (j * n))
        ≤ localConst ^ n * max 1 c ^ n * G * (2 ^ a * 2 ^ (j * a)) *
          ((sideConstant ^ n)⁻¹ * 2 ^ (j * n)) := by gcongr
      _ = E := by
          rw [hE, div_pow, div_eq_mul_inv]
          ring
  have hw : ((1 + euclidNorm (pieceCentre j z)) ^ (4 * n + 2))⁻¹ ≤
      ((1 + (t : ℝ)) ^ (4 * n + 2))⁻¹ := by
    have h0 : (0 : ℝ) < 1 + t := by positivity
    exact inv_anti₀ (pow_pos h0 _) (pow_le_pow_left₀ h0.le (by linarith) _)
  have hL := leibnizConst_nonneg n
  have hT := taylorConst_nonneg n
  have h2 : ENNReal.ofReal (scaledSupNorm (5 * n + 1) (pieceSide j) (pieceMul j z φ)) ≤
      ENNReal.ofReal (leibnizConst n * taylorConst n * (2 ^ (j * (5 * n + a - 3)))⁻¹ *
        ((1 + (t : ℝ)) ^ (4 * n + 2))⁻¹) * decaySeminorm (4 * n + 2) (10 * n + a - 2) φ := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · refine ((hdecay φ hφ).2 rfl).trans ?_
      have hmono := (hfacts n hn).2.2.1 φ hφ.1 (4 * n + 2) (5 * n + 1) (4 * n + 2)
        (10 * n + a - 2) le_rfl (by omega)
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) hmono
      simp only [zero_mul, pow_zero, inv_one, mul_one]
      exact mul_le_mul_of_nonneg_left hw (by positivity)
    · have hr1 : 1 ≤ 5 * n + a - 3 := by omega
      have h3 := (hdecay φ hφ).1 hj (5 * n + a - 3) hr1
      have h4 : 5 * n + 1 + (5 * n + a - 3) = 10 * n + a - 2 := by omega
      rw [h4] at h3
      refine h3.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      rw [zpow_neg, zpow_natCast]
      exact mul_le_mul_of_nonneg_left hw (by positivity)
  calc ENNReal.ofReal ‖localPairing T (pieceBoxSystem ⟨(j, z), hp⟩) (pieceMul j z φ)‖
      ≤ ENNReal.ofReal (E * scaledSupNorm (5 * n + 1) (pieceSide j) (pieceMul j z φ)) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal E *
          ENNReal.ofReal (scaledSupNorm (5 * n + 1) (pieceSide j) (pieceMul j z φ)) :=
        ENNReal.ofReal_mul hE0
    _ ≤ ENNReal.ofReal E * (ENNReal.ofReal (leibnizConst n * taylorConst n *
          (2 ^ (j * (5 * n + a - 3)))⁻¹ * ((1 + (t : ℝ)) ^ (4 * n + 2))⁻¹) *
          decaySeminorm (4 * n + 2) (10 * n + a - 2) φ) := by gcongr
    _ = ENNReal.ofReal (singlePieceBound n a c G j t) *
          decaySeminorm (4 * n + 2) (10 * n + a - 2) φ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hE0]
        rfl
theorem two_pow_combination (a j m : ℕ) :
    (2 : ℝ) ^ (j * a) * 2 ^ (j * (m + 2)) * ((2 : ℝ) ^ (j * (5 * m + a + 7)))⁻¹ *
      2 ^ (j * (4 * m + 4)) = (1 / 2) ^ j := by
  have h : (2 : ℝ) ^ (j * (5 * m + a + 7)) =
      2 ^ (j * a) * 2 ^ (j * (m + 2)) * 2 ^ (j * (4 * m + 4)) * 2 ^ j := by
    simp only [← pow_add]
    congr 1
    ring
  rw [h, one_div, inv_pow]
  field_simp
theorem dyadicScale_zpow (j m : ℕ) :
    dyadicScale j ^ (4 - 4 * ((m + 2 : ℕ) : ℤ)) = 2 ^ (j * (4 * m + 4)) := by apply _root_.YangMills.Construction.PieceProducts.Summability.dyadicScale_zpow <;> assumption
theorem cardOf_mul_singlePieceBound_le {n : ℕ} (hn : 2 ≤ n) (hcount : CentreCount n) (a : ℕ)
    (c G : ℝ) (hG : 0 ≤ G) (j t : ℕ) :
    (cardOf (centresInAnnulus n j t) : ℝ≥0∞) * ENNReal.ofReal (singlePieceBound n a c G j t) ≤
      ENNReal.ofReal (quarterConst n a c G * (1 / 2 : ℝ) ^ j * ((1 + (t : ℝ)) ^ 2)⁻¹) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hC := localConst_nonneg
  have hr := sideConstant_pos'
  have hL := leibnizConst_nonneg (m + 2)
  have hT := taylorConst_nonneg (m + 2)
  have hN := countConst_nonneg (m + 2)
  have hK : 0 ≤ quarterConst (m + 2) a c G := by
    unfold quarterConst
    positivity
  have hx : (0 : ℝ) < 1 + t := by positivity
  have hpb : singlePieceBound (m + 2) a c G j t =
      (localConst / sideConstant) ^ (m + 2) * max 1 c ^ (m + 2) * G * 2 ^ a *
        (2 ^ (j * a) * 2 ^ (j * (m + 2))) *
        (leibnizConst (m + 2) * taylorConst (m + 2) * (2 ^ (j * (5 * m + a + 7)))⁻¹ *
          ((1 + (t : ℝ)) ^ (4 * m + 10))⁻¹) := by
    unfold singlePieceBound
    have h1 : 5 * (m + 2) + a - 3 = 5 * m + a + 7 := by omega
    have h2 : 4 * (m + 2) + 2 = 4 * m + 10 := by omega
    rw [h1, h2]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h0 := (hcount 0 t).2 rfl
    have h1 : 0 ≤ countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * (m + 2)) := by positivity
    calc (cardOf (centresInAnnulus (m + 2) 0 t) : ℝ≥0∞) *
          ENNReal.ofReal (singlePieceBound (m + 2) a c G 0 t)
        ≤ ENNReal.ofReal (countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * (m + 2))) *
          ENNReal.ofReal (singlePieceBound (m + 2) a c G 0 t) := by gcongr
      _ = ENNReal.ofReal (countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * (m + 2)) *
            singlePieceBound (m + 2) a c G 0 t) := (ENNReal.ofReal_mul h1).symm
      _ = _ := by
          congr 1
          rw [hpb]
          unfold quarterConst
          have h2 : (1 + (t : ℝ)) ^ (4 * m + 10) =
              (1 + (t : ℝ)) ^ (4 * (m + 2)) * (1 + (t : ℝ)) ^ 2 := by
            rw [← pow_add]
            congr 1
          rw [h2]
          simp only [zero_mul, pow_zero, inv_one, mul_one]
          field_simp
  · have h0 := (hcount j t).1 hj
    have hs : 0 < dyadicScale j := zpow_pos (by norm_num) _
    have h1 : 0 ≤ countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * (m + 2) - 4) *
        dyadicScale j ^ (4 - 4 * ((m + 2 : ℕ) : ℤ)) := by positivity
    calc (cardOf (centresInAnnulus (m + 2) j t) : ℝ≥0∞) *
          ENNReal.ofReal (singlePieceBound (m + 2) a c G j t)
        ≤ ENNReal.ofReal (countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * (m + 2) - 4) *
            dyadicScale j ^ (4 - 4 * ((m + 2 : ℕ) : ℤ))) *
          ENNReal.ofReal (singlePieceBound (m + 2) a c G j t) := by gcongr
      _ = ENNReal.ofReal (countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * (m + 2) - 4) *
            dyadicScale j ^ (4 - 4 * ((m + 2 : ℕ) : ℤ)) * singlePieceBound (m + 2) a c G j t) :=
          (ENNReal.ofReal_mul h1).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 : 4 * (m + 2) - 4 = 4 * m + 4 := by omega
          have h3 : (1 + (t : ℝ)) ^ (4 * m + 10) =
              (1 + (t : ℝ)) ^ (4 * m + 4) * (1 + (t : ℝ)) ^ 6 := by
            rw [← pow_add]
          have h4 : ((1 + (t : ℝ)) ^ 6)⁻¹ ≤ ((1 + (t : ℝ)) ^ 2)⁻¹ :=
            inv_anti₀ (pow_pos hx 2)
              (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) t]) (by norm_num))
          rw [hpb, h2, dyadicScale_zpow, h3]
          have h5 : countConst (m + 2) * (1 + (t : ℝ)) ^ (4 * m + 4) * 2 ^ (j * (4 * m + 4)) *
              ((localConst / sideConstant) ^ (m + 2) * max 1 c ^ (m + 2) * G * 2 ^ a *
                (2 ^ (j * a) * 2 ^ (j * (m + 2))) *
                (leibnizConst (m + 2) * taylorConst (m + 2) * (2 ^ (j * (5 * m + a + 7)))⁻¹ *
                  ((1 + (t : ℝ)) ^ (4 * m + 4) * (1 + (t : ℝ)) ^ 6)⁻¹)) =
              quarterConst (m + 2) a c G *
                ((2 : ℝ) ^ (j * a) * 2 ^ (j * (m + 2)) * ((2 : ℝ) ^ (j * (5 * m + a + 7)))⁻¹ *
                  2 ^ (j * (4 * m + 4))) * ((1 + (t : ℝ)) ^ 6)⁻¹ := by
            unfold quarterConst
            have h6 : (1 + (t : ℝ)) ^ (4 * m + 4) ≠ 0 := (pow_pos hx _).ne'
            rw [mul_inv]
            field_simp
          rw [h5, two_pow_combination]
          exact mul_le_mul_of_nonneg_left h4 (by positivity)
theorem pieceLocalSumBound_holds
    (hlocal : LocalPairingProps.LocalPairingProperties)
    (hpieces : ShellPiecesBound)
    (hfacts : TupleFacts.BasicFacts)
    (hflat : ProductBounds) : PieceLocalSumBound := by
  intro n c a G T hB φ hφ
  have hn : 2 ≤ n := hB.1
  have hG : 0 ≤ G := hB.2.2.1
  have hcount : CentreCount n := (hpieces n (by omega)).2.2.2.2.2
  have hC := localConst_nonneg
  have hr := sideConstant_pos'
  have hL := leibnizConst_nonneg n
  have hT := taylorConst_nonneg n
  have hN := countConst_nonneg n
  have hK : 0 ≤ quarterConst n a c G := by
    unfold quarterConst
    positivity
  have hnonneg : ∀ x : Config n, 0 ≤ euclidNorm x := fun x => Real.sqrt_nonneg _
  calc ∑' p : activeIndices n,
        ENNReal.ofReal ‖localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 φ)‖
      ≤ ∑' p : activeIndices n,
          ENNReal.ofReal (singlePieceBound n a c G p.1.1 ⌊euclidNorm (pieceCentre p.1.1 p.1.2)⌋₊) *
            decaySeminorm (4 * n + 2) (10 * n + a - 2) φ :=
        ENNReal.tsum_le_tsum fun p =>
          localPairing_piece_le hlocal hfacts hflat hB hφ p _ (Nat.floor_le (hnonneg _))
    _ = (∑' p : activeIndices n,
          ENNReal.ofReal (singlePieceBound n a c G p.1.1 ⌊euclidNorm (pieceCentre p.1.1 p.1.2)⌋₊)) *
            decaySeminorm (4 * n + 2) (10 * n + a - 2) φ := ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal (4 * quarterConst n a c G) *
          decaySeminorm (4 * n + 2) (10 * n + a - 2) φ := by
        refine mul_le_mul' ?_ le_rfl
        refine (tsum_activeIndices_le _ (fun j t => ENNReal.ofReal (singlePieceBound n a c G j t))
          fun _ => le_rfl).trans ?_
        refine le_trans (ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun t =>
          cardOf_mul_singlePieceBound_le hn hcount a c G hG j t) (tsum_tsum_geom_inv_sq_le hK)
    _ = ENNReal.ofReal (extConst n a * max 1 c ^ n * G) *
          decaySeminorm (4 * n + 2) (10 * n + a - 2) φ := by
        congr 2
        unfold quarterConst extConst
        ring
end YangMills.Construction.PieceLocalSum
