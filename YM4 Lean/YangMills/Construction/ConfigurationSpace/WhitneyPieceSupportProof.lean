import YangMills.Construction.BumpFunctions.SmoothBumpsGevreyBounds
import YangMills.Construction.ConfigurationSpace.DiagonalCutoffBounds
import YangMills.Construction.ConfigurationSpace.MinSeparationProperties
import YangMills.Construction.ConfigurationSpace.ShellCenterCountProof
import YangMills.Construction.ConfigurationSpace.WhitneyPieceSupport
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace.WhitneyPieceSmooth
open YangMills.Construction.BumpFunctions YangMills.Construction.WhitneyScales
open scoped ContDiff
variable {n : ℕ}
theorem pos_whitneyScale (j : ℕ) : 0 < whitneyScale j := by apply _root_.YangMills.Construction.ConfigurationSpace.ShellCount.scale_pos <;> assumption
theorem pos_whitneySide (j : ℕ) : 0 < whitneySide j :=
  mul_pos isWhitneyRatio_whitneyRatio.1 (pos_whitneyScale j)
theorem mem_translateSet_coordwise_iff (a x : Config n) (T : Set ℝ) :
    x ∈ translateSet a {y | ∀ ι, coords y ι ∈ T} ↔
      ∀ ι, coords x ι - coords a ι ∈ T := by
  constructor
  · rintro ⟨y, hy, rfl⟩ ι
    have h : coords (a + y) ι - coords a ι = coords y ι := by
      simp [coords]
    rw [h]
    exact hy ι
  · intro h
    exact ⟨x - a, fun ι => h ι, by simp⟩
theorem closedCoordBox_eq_pi (a : Config n) (r : ℝ) :
    translateSet a {y | ∀ ι, coords y ι ∈ Set.Icc (-r) r} =
      Set.pi Set.univ fun i => Set.pi Set.univ fun c => Set.Icc (a i c - r) (a i c + r) := by
  ext x
  rw [mem_translateSet_coordwise_iff]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  constructor
  · intro h i c
    have h' := h (toLex (i, c))
    rw [coords_toLex, coords_toLex] at h'
    constructor <;> linarith [h'.1, h'.2]
  · intro h ι
    have h' := h (ofLex ι).1 (ofLex ι).2
    change -r ≤ x (ofLex ι).1 (ofLex ι).2 - a (ofLex ι).1 (ofLex ι).2 ∧
      x (ofLex ι).1 (ofLex ι).2 - a (ofLex ι).1 (ofLex ι).2 ≤ r
    constructor <;> linarith [h'.1, h'.2]
theorem isCompact_closedCoordBox (a : Config n) (r : ℝ) :
    IsCompact (translateSet a {y | ∀ ι, coords y ι ∈ Set.Icc (-r) r}) := by
  rw [closedCoordBox_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
theorem contDiff_coords (ι : CoordIndex n) :
    ContDiff ℝ ∞ fun x : Config n => coords x ι :=
  (contDiff_apply ℝ ℝ (ofLex ι).2).comp (contDiff_apply ℝ (Fin 4 → ℝ) (ofLex ι).1)
theorem contDiff_of_ofRealFun_mem {f : Config n → ℝ}
    (h : ofRealFun f ∈ smoothSet (Config n)) : ContDiff ℝ ∞ f := by
  have hf : f = fun x => Complex.reCLM (ofRealFun f x) := by
    funext x
    simp [ofRealFun]
  rw [hf]
  exact Complex.reCLM.contDiff.comp h
theorem ofRealFun_mem_smoothSet {f : Config n → ℝ} (h : ContDiff ℝ ∞ f) :
    ofRealFun f ∈ smoothSet (Config n) :=
  Complex.ofRealCLM.contDiff.comp h
theorem tsupport_ofRealFun (f : Config n → ℝ) : tsupport (ofRealFun f) = tsupport f := by
  have h : Function.support (ofRealFun f) = Function.support f := by
    ext x
    simp [ofRealFun]
  simp only [tsupport, h]
theorem contDiff_shellDiff (hshells : DiagonalCutoffProperties)
    (hn : 1 ≤ n) (j : ℕ) : ContDiff ℝ ∞ (shellDiff (n := n) j) := by
  have hH : ∀ j : ℕ, ContDiff ℝ ∞ (pairCutoffProd (n := n) j) := fun j =>
    contDiff_of_ofRealFun_mem (hshells n hn j).2.1.1
  cases j with
  | zero => exact hH 0
  | succ j => exact (hH (j + 1)).sub (hH j)
theorem shellDiff_le_one (hshells : DiagonalCutoffProperties)
    (hn : 1 ≤ n) (j : ℕ) (x : Config n) : shellDiff j x ≤ 1 := by
  cases j with
  | zero =>
    obtain ⟨-, h₁, h₂⟩ := (hshells n hn 0).2.1.2.1 x
    exact h₁.trans h₂
  | succ j =>
    obtain ⟨h₀, -, h₂⟩ := (hshells n hn j).2.1.2.1 x
    change pairCutoffProd (j + 1) x - pairCutoffProd j x ≤ 1
    linarith
theorem coords_near_pieceCenter
    (hsupp : tsupport mollifiedUnitIndicator ⊆ Set.Icc (-(3 / 4) : ℝ) (3 / 4))
    (j : ℕ) (z : IntPoint n) (x : Config n) (ι : CoordIndex n)
    (h : mollifiedUnitIndicator (2 * coords x ι / whitneySide j - z ι) ≠ 0) :
    coords x ι - coords (pieceCenter j z) ι ∈
      Set.Icc (-(3 / 8 * whitneySide j)) (3 / 8 * whitneySide j) := by
  have hu := pos_whitneySide j
  have ht := hsupp (subset_tsupport _ (Function.mem_support.2 h))
  have hc : coords (pieceCenter j z) ι = 1 / 2 * whitneySide j * z ι := rfl
  have hx : coords x ι - 1 / 2 * whitneySide j * z ι =
      (2 * coords x ι / whitneySide j - z ι) * whitneySide j / 2 := by
    field_simp
  rw [hc, hx]
  have h₁ := mul_le_mul_of_nonneg_right ht.1 hu.le
  have h₂ := mul_le_mul_of_nonneg_right ht.2 hu.le
  constructor <;> linarith
theorem tsupport_whitneyPiece_subset_closedCoordBox
    (hsupp : tsupport mollifiedUnitIndicator ⊆ Set.Icc (-(3 / 4) : ℝ) (3 / 4))
    (j : ℕ) (z : IntPoint n) :
    tsupport (whitneyPiece j z) ⊆ translateSet (pieceCenter j z)
      {x | ∀ ι, coords x ι ∈ Set.Icc (-(3 / 8 * whitneySide j)) (3 / 8 * whitneySide j)} := by
  refine closure_minimal ?_ (isCompact_closedCoordBox _ _).isClosed
  intro x hx
  rw [mem_translateSet_coordwise_iff]
  intro ι
  have hne : blockProd j z x ≠ 0 := right_ne_zero_of_mul (Function.mem_support.1 hx)
  exact coords_near_pieceCenter hsupp j z x ι
    (Finset.prod_ne_zero_iff.1 hne ι (Finset.mem_univ ι))
theorem closedCoordBox_subset_pieceBox (j : ℕ) (z : IntPoint n) :
    translateSet (pieceCenter j z)
      {x | ∀ ι, coords x ι ∈ Set.Icc (-(3 / 8 * whitneySide j)) (3 / 8 * whitneySide j)} ⊆
      pieceBox j z := by
  intro x hx
  have hu := pos_whitneySide j
  rw [mem_translateSet_coordwise_iff] at hx
  unfold pieceBox
  rw [mem_translateSet_coordwise_iff]
  intro ι
  have h := hx ι
  constructor <;> linarith [h.1, h.2]
theorem pieceBox_subset_boxProduct (j : ℕ) (z : IntPoint n) :
    pieceBox j z ⊆ boxProduct (innerCube j z) := by
  intro x hx
  unfold pieceBox at hx
  rw [mem_translateSet_coordwise_iff] at hx
  intro i
  change maxNorm (x i - pieceCenter j z i) ≤ whitneySide j / 2
  refine ciSup_le fun c => ?_
  have h := hx (toLex (i, c))
  rw [coords_toLex, coords_toLex] at h
  rw [Pi.sub_apply, abs_le]
  constructor <;> linarith [h.1, h.2]
theorem tsupport_whitneyPiece_subset_injectiveTuples
    (hshells : DiagonalCutoffProperties)
    (hminf : MinSeparationProperties) (hn : 1 ≤ n) (j : ℕ) (z : IntPoint n) :
    tsupport (whitneyPiece j z) ⊆ TestFunctions.injectiveTuples (Fin 4 → ℝ) n := by
  have hfacts : FatDiagonalEqZeros n ∧ FatDiagonalComplEqInjective n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      exact hminf.2
    · exact (hminf.1 n h).2
  have hsub : tsupport (whitneyPiece j z) ⊆ tsupport (shellDiff (n := n) j) := by
    refine closure_mono ?_
    intro x hx
    exact left_ne_zero_of_mul (Function.mem_support.1 hx)
  intro x hx
  have hpos : ∃ s : ℝ, 0 < s ∧ ENNReal.ofReal s ≤ minSeparation x := by
    obtain ⟨-, -, -, -, -, h₁, h₀, -, -⟩ := (hshells n hn j).2.2
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨1, one_pos, h₀ (hsub hx)⟩
    · exact ⟨whitneyScale j, pos_whitneyScale j, (h₁ hj (hsub hx)).1⟩
  obtain ⟨s, hs, hsep⟩ := hpos
  have hne : minSeparation x ≠ 0 := by
    intro h0
    rw [h0] at hsep
    exact absurd (ENNReal.ofReal_pos.2 hs) (not_lt.2 hsep)
  have hoff : x ∈ (fatDiagonal n)ᶜ := by
    intro hd
    rw [hfacts.1.1] at hd
    exact hne hd
  rw [hfacts.2.1] at hoff
  exact hoff
theorem whitneyPieceSupportProperties_of_cutoffs (hbumps : BumpFunctions.SmoothBumpsGevreyBounds)
    (hshells : DiagonalCutoffProperties)
    (hminf : MinSeparationProperties) : WhitneyPieceSupportProperties := by
  obtain ⟨-, -, -, ⟨hbsm, hb01, hbsupp, -, -⟩, -, -⟩ := hbumps
  intro n hn j z
  have hsm : ContDiff ℝ ∞ (whitneyPiece (n := n) j z) := by
    have hblock : ContDiff ℝ ∞ (blockProd (n := n) j z) := by
      unfold blockProd
      refine contDiff_prod fun ι _ => hbsm.comp ?_
      exact (((contDiff_const.mul (contDiff_coords ι)).div_const _).sub contDiff_const)
    exact (contDiff_shellDiff hshells hn j).mul hblock
  have hbox := tsupport_whitneyPiece_subset_closedCoordBox hbsupp j z
  have hcompact : IsCompact (tsupport (whitneyPiece j z)) :=
    (isCompact_closedCoordBox _ _).of_isClosed_subset (isClosed_tsupport _) hbox
  refine ⟨⟨ofRealFun_mem_smoothSet hsm, ?_⟩, ?_, hbox, closedCoordBox_subset_pieceBox j z,
    pieceBox_subset_boxProduct j z, hcompact,
    tsupport_whitneyPiece_subset_injectiveTuples hshells hminf hn j z⟩
  · change IsCompact (tsupport (ofRealFun (whitneyPiece j z)))
    rw [tsupport_ofRealFun]
    exact hcompact
  · intro x
    have hU₀ : 0 ≤ shellDiff j x := (hshells n hn j).2.2.1 x
    have hU₁ := shellDiff_le_one hshells hn j x
    have hB₀ : 0 ≤ blockProd j z x := Finset.prod_nonneg fun ι _ => (hb01 _).1
    have hB₁ : blockProd j z x ≤ 1 :=
      Finset.prod_le_one (fun ι _ => (hb01 _).1) fun ι _ => (hb01 _).2
    exact ⟨mul_nonneg hU₀ hB₀, mul_le_one₀ hU₁ hB₀ hB₁⟩
end YangMills.Construction.ConfigurationSpace.WhitneyPieceSmooth
end
