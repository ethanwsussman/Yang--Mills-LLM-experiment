import YangMills.Construction.ConfigSpace.FlatSchwartzDensity
import YangMills.Construction.Continuum.FiniteSeminormsOfRapidlyDecreasingFunctions
import YangMills.Construction.Continuum.FirstFactsOnSmoothTestFunctionsAndTuples
import YangMills.Construction.Continuum.FlatFunctionMinusAFiniteSumOfPieceProducts
import YangMills.Construction.Continuum.PieceProductApproachedByTheTensorSpan
import YangMills.Construction.Continuum.PiecesOfTheShellsAndTheirBounds
import YangMills.Construction.Continuum.ProductsWithThePiecesSummableInEveryNorm
import YangMills.Construction.Continuum.RulesOfThePartialDerivatives
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal Topology
noncomputable section
namespace YangMills.Construction.ConfigSpace
open ShellPieces PieceProducts ShellPieceBounds
theorem tensorSpanDenseInFlatSchwartz_holds
    (hSum : PieceProducts.PieceMulSummableSeminorms)
    (hTail : FlatMinusPieceSumBound)
    (hApprox : pieceMul_mem_closure_tensorSpan)
    (hFacts : TupleFacts.BasicFacts)
    (hNorm : SchwartzSeminormsFinite)
    (hPieces : ShellPieceBounds.ShellPiecesBound)
    (hRules : TestSpaces.DerivRules.Combined) :
    TensorSpanDenseInFlatSchwartz := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, ⟨-, hRT, W, hW, hWflat⟩, hGrow, -⟩ := hFacts n hn
  have hsem : ∀ k l : ℕ, IsSchwartzSeminorm (decaySeminorm (n := n) k l) :=
    fun k l => (hNorm n hn1 k l 0).2.1
  have hWmem : ∀ {g : Config n → ℂ}, g ∈ W → g ∈ flatSchwartzSet n := fun hg => hWflat hg
  have hWrapid : ∀ {g : Config n → ℂ}, g ∈ W → g ∈ schwartzSet n := fun hg => (hWmem hg).1
  have hrapid : ∀ {ψ : Config n → ℂ}, ContDiff ℝ ∞ ψ →
      (∀ k l : ℕ, decaySeminorm k l ψ < ⊤) → ψ ∈ schwartzSet n := by
    intro ψ hψ hfin
    refine ⟨hψ, fun k α => lt_of_le_of_lt ?_ (hfin k α.order)⟩
    exact le_iSup₂ (f := fun (β : MultiIndex n) (_ : β.order ≤ α.order) =>
      ⨆ x, ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖iteratedPartial β ψ x‖)) α le_rfl
  have hadd : ∀ {φ ψ : Config n → ℂ}, φ ∈ schwartzSet n → ψ ∈ schwartzSet n →
      φ + ψ ∈ schwartzSet n := by
    intro φ ψ hφ hψ
    refine hrapid (hφ.1.add hψ.1) fun k l => lt_of_le_of_lt ((hsem k l).2.2 φ hφ ψ hψ) ?_
    exact ENNReal.add_lt_top.2 ⟨(hsem k l).1 φ hφ, (hsem k l).1 ψ hψ⟩
  have hsmul : ∀ (c : ℂ) {φ : Config n → ℂ}, φ ∈ schwartzSet n →
      c • φ ∈ schwartzSet n := by
    intro c φ hφ
    refine hrapid (contDiff_const.smul hφ.1) fun k l => ?_
    rw [(hsem k l).2.1 c φ hφ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((hsem k l).1 φ hφ)
  have hsub : ∀ {φ ψ : Config n → ℂ}, φ ∈ schwartzSet n → ψ ∈ schwartzSet n →
      φ - ψ ∈ schwartzSet n := by
    intro φ ψ hφ hψ
    have e : φ - ψ = φ + (-1 : ℂ) • ψ := by simp [sub_eq_add_neg]
    rw [e]
    exact hadd hφ (hsmul _ hψ)
  have hflatadd : ∀ {φ ψ : Config n → ℂ}, φ ∈ flatSchwartzSet n → ψ ∈ flatSchwartzSet n →
      φ + ψ ∈ flatSchwartzSet n := by
    intro φ ψ hφ hψ
    refine ⟨hadd hφ.1 hψ.1, fun α x hx => ?_⟩
    have h : iteratedPartial α (φ + ψ) = iteratedPartial α φ + iteratedPartial α ψ :=
      (hRules.2.1 n φ hφ.1.1).2.2.2.2.2.1 ψ hψ.1.1 α
    rw [h, Pi.add_apply, hφ.2 α x hx, hψ.2 α x hx, add_zero]
  have hspanW : Submodule.span ℂ (tensorProd '' smoothRealTupleSet n) ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    show tensorProd f ∈ (W : Set (Config n → ℂ))
    rw [hW]
    exact (hRT f hf).1
  have hprod : ∀ (p : activeIndices n) {f : Config n → ℂ}, f ∈ flatSchwartzSet n →
      pieceMul p.1.1 p.1.2 f ∈ W := by
    intro p f hf
    have hP := (hPieces n hn1).2.1 p.1.1 p.1.2
    have hsupp : tsupport (pieceC (n := n) p.1.1 p.1.2) ⊆
        tsupport (piece (n := n) p.1.1 p.1.2) := by
      refine closure_mono fun x hx => ?_
      simpa [pieceC] using hx
    have hmem : pieceMul p.1.1 p.1.2 f ∈ testFnOffDiag n := by
      refine ⟨ContDiff.mul hP.1.1 hf.1.1, HasCompactSupport.mul_right hP.1.2, ?_⟩
      exact (tsupport_mul_subset_left (f := pieceC p.1.1 p.1.2) (g := f)).trans
        (hsupp.trans hP.2.2.2.2.2.2.1)
    have : pieceMul p.1.1 p.1.2 f ∈ (W : Set (Config n → ℂ)) := by
      rw [hW]
      exact hmem
    exact this
  have hzero : ∀ k l : ℕ, decaySeminorm k l (0 : Config n → ℂ) = 0 := by
    intro k l
    have h := (hsem k l).2.1 0 0 (hWrapid W.zero_mem)
    simpa using h
  have hsumle : ∀ (k l : ℕ) (s : Finset (activeIndices n)) (u : activeIndices n → Config n → ℂ),
      (∀ p, u p ∈ W) →
        decaySeminorm k l (∑ p ∈ s, u p) ≤ ∑ p ∈ s, decaySeminorm k l (u p) := by
    intro k l s u hu
    classical
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact ((hsem k l).2.2 _ (hWrapid (hu a)) _
        (hWrapid (W.sum_mem fun p _ => hu p))).trans (add_le_add le_rfl ih)
  have hmain : ∀ f ∈ flatSchwartzSet n, ∀ (k l : ℕ) (ε : ℝ), 0 < ε →
      ∃ g ∈ Submodule.span ℂ (tensorProd '' smoothRealTupleSet n),
        decaySeminorm k l (f - g) < ENNReal.ofReal ε := by
    intro f hf k l ε hε
    have hfin := hSum n hn f hf k l
    have htend := ENNReal.tendsto_tsum_compl_atTop_zero hfin.ne
    have hhalf : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (by positivity)
    obtain ⟨F, hF⟩ := ((tendsto_order.1 htend).2 _ hhalf).exists
    have hc : (0 : ℝ) < 2 * ((F.card : ℝ) + 1) := by positivity
    have hδ : 0 < ε / (2 * ((F.card : ℝ) + 1)) := div_pos hε hc
    have hch := fun p : activeIndices n => hApprox n hn p.1.1 p.1.2 p.2 f hf k l _ hδ
    choose G hGs hGb using hch
    refine ⟨∑ p ∈ F, G p, Submodule.sum_mem _ fun p _ => hGs p, ?_⟩
    have hdecomp : f - ∑ p ∈ F, G p = (f - ∑ p ∈ F, pieceMul p.1.1 p.1.2 f) +
        ∑ p ∈ F, (pieceMul p.1.1 p.1.2 f - G p) := by
      rw [Finset.sum_sub_distrib]
      abel
    have hdW : ∀ p : activeIndices n, pieceMul p.1.1 p.1.2 f - G p ∈ W :=
      fun p => W.sub_mem (hprod p hf) (hspanW (hGs p))
    have hA : f - ∑ p ∈ F, pieceMul p.1.1 p.1.2 f ∈ schwartzSet n :=
      hsub hf.1 (hWrapid (W.sum_mem fun p _ => hprod p hf))
    have hB : ∑ p ∈ F, (pieceMul p.1.1 p.1.2 f - G p) ∈ schwartzSet n :=
      hWrapid (W.sum_mem fun p _ => hdW p)
    have hAle : decaySeminorm k l (f - ∑ p ∈ F, pieceMul p.1.1 p.1.2 f) <
        ENNReal.ofReal (ε / 2) := lt_of_le_of_lt (hTail n hn f hf k l F) hF
    have hcard : (F.card : ℝ) * (ε / (2 * ((F.card : ℝ) + 1))) < ε / 2 := by
      have e : ε / 2 = ((F.card : ℝ) + 1) * (ε / (2 * ((F.card : ℝ) + 1))) := by
        field_simp
      rw [e]
      nlinarith
    have hBle : decaySeminorm k l (∑ p ∈ F, (pieceMul p.1.1 p.1.2 f - G p)) <
        ENNReal.ofReal (ε / 2) := by
      refine lt_of_le_of_lt (hsumle k l F _ hdW) (lt_of_le_of_lt
        (Finset.sum_le_card_nsmul F _ (ENNReal.ofReal (ε / (2 * ((F.card : ℝ) + 1))))
          fun p _ => (hGb p).le) ?_)
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hcard
    rw [hdecomp]
    calc _ ≤ _ := (hsem k l).2.2 _ hA _ hB
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hAle hBle
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
  have hflatRapid : flatSchwartzSet n ⊆ schwartzSet n := fun _ h => h.1
  refine ⟨⟨?_, hflatRapid, fun f hf k l ε hε => ?_⟩,
    ⟨fun g hg => hWmem (hspanW hg), hflatRapid, hmain⟩, ?_⟩
  · rw [← hW]
    exact hWflat
  · obtain ⟨g, hg, hb⟩ := hmain f hf k l ε hε
    refine ⟨g, ?_, hb⟩
    rw [← hW]
    exact hspanW hg
  intro S₁ h₁ S₂ h₂ hag
  obtain ⟨hl₁, k₁, q₁, b₁, hb₁, hB₁⟩ := h₁
  obtain ⟨hl₂, k₂, q₂, b₂, hb₂, hB₂⟩ := h₂
  have hS0 : ∀ (S : flatSchwartzSet n → ℂ), IsLinearOnFlat S →
      ∀ h : (0 : Config n → ℂ) ∈ flatSchwartzSet n, S ⟨0, h⟩ = 0 := by
    intro S hS h
    have := hS.2 0 ⟨0, h⟩ ⟨0, h⟩ (by simp)
    simpa using this
  have hspan : ∀ g ∈ Submodule.span ℂ (tensorProd '' smoothRealTupleSet n),
      ∀ h : g ∈ flatSchwartzSet n, S₁ ⟨g, h⟩ = S₂ ⟨g, h⟩ := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      intro h
      exact hag ⟨_, h⟩ ⟨f, hf, rfl⟩
    | zero =>
      intro h
      rw [hS0 S₁ hl₁ h, hS0 S₂ hl₂ h]
    | add x y hx hy ihx ihy =>
      intro h
      have fx := hWmem (hspanW hx)
      have fy := hWmem (hspanW hy)
      rw [hl₁.1 ⟨x, fx⟩ ⟨y, fy⟩ ⟨x + y, h⟩ rfl, hl₂.1 ⟨x, fx⟩ ⟨y, fy⟩ ⟨x + y, h⟩ rfl,
        ihx fx, ihy fy]
    | smul a x hx ih =>
      intro h
      have fx := hWmem (hspanW hx)
      rw [hl₁.2 a ⟨x, fx⟩ ⟨a • x, h⟩ rfl, hl₂.2 a ⟨x, fx⟩ ⟨a • x, h⟩ rfl, ih fx]
  have hbound : ∀ (S : flatSchwartzSet n → ℂ) (k q K Q : ℕ) (b ε : ℝ), 0 ≤ b → 0 < ε → k ≤ K →
      q ≤ Q → (∀ φ : flatSchwartzSet n,
        ENNReal.ofReal ‖S φ‖ ≤ ENNReal.ofReal b * decaySeminorm k q φ.1) →
      ∀ ψ : flatSchwartzSet n, decaySeminorm K Q ψ.1 < ENNReal.ofReal ε → ‖S ψ‖ ≤ b * ε := by
    intro S k q K Q b ε hb hε hk hq hB ψ hψ
    have h1 : ENNReal.ofReal ‖S ψ‖ ≤ ENNReal.ofReal (b * ε) := by
      rw [ENNReal.ofReal_mul hb]
      exact (hB ψ).trans (mul_le_mul' le_rfl
        ((hGrow ψ.1 ψ.2.1 k q K Q hk hq).trans hψ.le))
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  funext φ
  have hsmall : ∀ ε : ℝ, 0 < ε → ‖S₁ φ - S₂ φ‖ ≤ (b₁ + b₂) * ε := by
    intro ε hε
    obtain ⟨g, hg, hgb⟩ := hmain φ.1 φ.2 (max k₁ k₂) (max q₁ q₂) ε hε
    have hgf : g ∈ flatSchwartzSet n := hWmem (hspanW hg)
    have hng : -g ∈ flatSchwartzSet n := hWmem (W.neg_mem (hspanW hg))
    have hψf : φ.1 - g ∈ flatSchwartzSet n := by
      rw [sub_eq_add_neg]
      exact hflatadd φ.2 hng
    have hsplit : φ.1 = (φ.1 - g) + g := by abel
    have e₁ := hl₁.1 ⟨φ.1 - g, hψf⟩ ⟨g, hgf⟩ φ hsplit
    have e₂ := hl₂.1 ⟨φ.1 - g, hψf⟩ ⟨g, hgf⟩ φ hsplit
    have hgeq := hspan g hg hgf
    have hdiff : S₁ φ - S₂ φ = S₁ ⟨φ.1 - g, hψf⟩ - S₂ ⟨φ.1 - g, hψf⟩ := by
      rw [e₁, e₂, hgeq]
      ring
    rw [hdiff, add_mul]
    exact (norm_sub_le _ _).trans (add_le_add
      (hbound S₁ k₁ q₁ _ _ b₁ ε hb₁ hε (le_max_left _ _) (le_max_left _ _) hB₁ ⟨_, hψf⟩ hgb)
      (hbound S₂ k₂ q₂ _ _ b₂ ε hb₂ hε (le_max_right _ _) (le_max_right _ _) hB₂ ⟨_, hψf⟩ hgb))
  have hb : 0 ≤ b₁ + b₂ := add_nonneg hb₁ hb₂
  by_contra hne
  have hd : 0 < ‖S₁ φ - S₂ φ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have h := hsmall (‖S₁ φ - S₂ φ‖ / (b₁ + b₂ + 1)) (by positivity)
  rw [mul_div_assoc', le_div_iff₀ (by positivity)] at h
  nlinarith
end YangMills.Construction.ConfigSpace
end
