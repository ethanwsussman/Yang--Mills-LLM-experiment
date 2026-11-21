import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperatorsAreAdmitted
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FreeStrip.ConstantsAdmissible
open PeriodicOperators
open FreeResolvents
theorem le_ofReal_csInf {x : ℝ≥0∞} {B : Set ℝ} (hne : B.Nonempty) (hbdd : BddBelow B)
    (h : ∀ C ∈ B, x ≤ ENNReal.ofReal C) : x ≤ ENNReal.ofReal (sInf B) := by
  rw [Monotone.map_csInf_of_continuousAt ENNReal.continuous_ofReal.continuousAt
    ENNReal.ofReal_mono hne hbdd]
  refine le_sInf ?_
  rintro _ ⟨C, hC, rfl⟩
  exact h C hC
theorem symbolBoundedOn_csInf {I I' : PeriodicData} {T : I'.Carrier → I.Carrier → ℂ}
    {D D' : Set (Fin 4 → ℂ)} {B : Set ℝ} (hsub : D' ⊆ D) (hne : B.Nonempty) (hbdd : BddBelow B)
    (h : ∀ C ∈ B, SymbolBoundedOn I I' T D C) : SymbolBoundedOn I I' T D' (sInf B) := by
  obtain ⟨C₁, hC₁⟩ := hne
  exact ⟨fun κ hκ => (h C₁ hC₁).1 κ (hsub hκ), fun κ hκ =>
    le_ofReal_csInf ⟨C₁, hC₁⟩ hbdd fun C hC => (h C hC).2 κ (hsub hκ)⟩
theorem compSymbolBoundedOn_csInf {I I' I'' : PeriodicData} {T : I'.Carrier → I.Carrier → ℂ}
    {S : I.Carrier → I''.Carrier → ℂ} {D D' : Set (Fin 4 → ℂ)} {B : Set ℝ} (hsub : D' ⊆ D)
    (hne : B.Nonempty) (hbdd : BddBelow B)
    (h : ∀ C ∈ B, CompSymbolBoundedOn I I' I'' T S D C) :
    CompSymbolBoundedOn I I' I'' T S D' (sInf B) := by
  obtain ⟨C₁, hC₁⟩ := id hne
  exact ⟨(h C₁ hC₁).1, symbolBoundedOn_csInf hsub hne hbdd fun C hC => (h C hC).2⟩
theorem symbolInvertibleOn_csInf {I : PeriodicData} {T : I.Carrier → I.Carrier → ℂ}
    {D D' : Set (Fin 4 → ℂ)} {B : Set ℝ} (hsub : D' ⊆ D) (hne : B.Nonempty) (hbdd : BddBelow B)
    (h : ∀ C ∈ B, SymbolInvertibleOn I T D C) : SymbolInvertibleOn I T D' (sInf B) := by
  obtain ⟨C₁, hC₁⟩ := hne
  exact ⟨fun κ hκ => (h C₁ hC₁).1 κ (hsub hκ), fun κ hκ => ⟨((h C₁ hC₁).2 κ (hsub hκ)).1,
    le_ofReal_csInf ⟨C₁, hC₁⟩ hbdd fun C hC => ((h C hC).2 κ (hsub hκ)).2⟩⟩
theorem tripleCompSymbolInvertibleOn_csInf {I J : PeriodicData} {T : I.Carrier → J.Carrier → ℂ}
    {A : J.Carrier → J.Carrier → ℂ} {S : J.Carrier → I.Carrier → ℂ} {D D' : Set (Fin 4 → ℂ)}
    {B : Set ℝ} (hsub : D' ⊆ D) (hne : B.Nonempty) (hbdd : BddBelow B)
    (h : ∀ C ∈ B, TripleCompSymbolInvertibleOn I J T A S D C) :
    TripleCompSymbolInvertibleOn I J T A S D' (sInf B) := by
  obtain ⟨C₁, hC₁⟩ := id hne
  exact ⟨(h C₁ hC₁).1, (h C₁ hC₁).2.1,
    symbolInvertibleOn_csInf hsub hne hbdd fun C hC => (h C hC).2.2⟩
theorem AddScalarInvertibleOn.mono {I : PeriodicData} {A : I.Carrier → I.Carrier → ℂ} {τ : ℝ}
    {D D' : Set (Fin 4 → ℂ)} (hsub : D' ⊆ D) (h : AddScalarInvertibleOn I A τ D) :
    AddScalarInvertibleOn I A τ D' where
  periodic := h.periodic
  symbol := fun κ hκ => h.symbol κ (hsub hκ)
  invertible_on_reals := h.invertible_on_reals
  inverse_periodic := h.inverse_periodic
  matrix_invertible := fun κ hκ => h.matrix_invertible κ (hsub hκ)
  inverse_summable := fun κ hκ => h.inverse_summable κ (hsub hκ)
  inverse_symbol := fun κ hκ => h.inverse_symbol κ (hsub hκ)
theorem boundedSymbols_csInf {L k : ℕ} {D D' : Set (Fin 4 → ℂ)} {B : Set ℝ} (hsub : D' ⊆ D)
    (hne : B.Nonempty) (hbdd : BddBelow B) (h : ∀ C ∈ B, BoundedSymbols L k D C) :
    BoundedSymbols L k D' (sInf B) := by
  obtain ⟨C₁, hC₁⟩ := id hne
  exact
    { edge_sqrt := symbolBoundedOn_csInf hsub hne hbdd fun C hC => (h C hC).edge_sqrt
      edge_sqrt_eq := fun κ hκ => (h C₁ hC₁).edge_sqrt_eq κ (hsub hκ)
      vertex_sqrt := symbolBoundedOn_csInf hsub hne hbdd fun C hC => (h C hC).vertex_sqrt
      vertex_sqrt_eq := fun κ hκ => (h C₁ hC₁).vertex_sqrt_eq κ (hsub hκ)
      diff_edge_sqrt := compSymbolBoundedOn_csInf hsub hne hbdd fun C hC => (h C hC).diff_edge_sqrt
      diffT_edge_sqrt :=
        compSymbolBoundedOn_csInf hsub hne hbdd fun C hC => (h C hC).diffT_edge_sqrt
      edge_sqrt_diff := compSymbolBoundedOn_csInf hsub hne hbdd fun C hC => (h C hC).edge_sqrt_diff
      edge_sqrt_diffT :=
        compSymbolBoundedOn_csInf hsub hne hbdd fun C hC => (h C hC).edge_sqrt_diffT
      diff_vertex_sqrt :=
        compSymbolBoundedOn_csInf hsub hne hbdd fun C hC => (h C hC).diff_vertex_sqrt
      vertex_sqrt_diffT :=
        compSymbolBoundedOn_csInf hsub hne hbdd fun C hC => (h C hC).vertex_sqrt_diffT
      edge_avg := symbolBoundedOn_csInf hsub hne hbdd fun C hC => (h C hC).edge_avg
      vertex_avg := symbolBoundedOn_csInf hsub hne hbdd fun C hC => (h C hC).vertex_avg
      edge_avgT := symbolBoundedOn_csInf hsub hne hbdd fun C hC => (h C hC).edge_avgT
      vertex_avgT := symbolBoundedOn_csInf hsub hne hbdd fun C hC => (h C hC).vertex_avgT }
theorem invertibleSymbols_csInf {L k : ℕ} {D D' : Set (Fin 4 → ℂ)} {B : Set ℝ} {t τ : ℝ}
    (hsub : D' ⊆ D) (hne : B.Nonempty) (hbdd : BddBelow B)
    (h : ∀ C ∈ B, InvertibleSymbols L k D C t τ) :
    InvertibleSymbols L k D' (sInf B) t τ := by
  obtain ⟨C₁, hC₁⟩ := id hne
  exact
    { edge_interp :=
        tripleCompSymbolInvertibleOn_csInf hsub hne hbdd fun C hC => (h C hC).edge_interp
      edge_add := tripleCompSymbolInvertibleOn_csInf hsub hne hbdd fun C hC => (h C hC).edge_add
      vertex_interp :=
        tripleCompSymbolInvertibleOn_csInf hsub hne hbdd fun C hC => (h C hC).vertex_interp
      vertex_add := tripleCompSymbolInvertibleOn_csInf hsub hne hbdd fun C hC => (h C hC).vertex_add
      edge_avg := tripleCompSymbolInvertibleOn_csInf hsub hne hbdd fun C hC => (h C hC).edge_avg
      vertex_avg :=
        tripleCompSymbolInvertibleOn_csInf hsub hne hbdd fun C hC => (h C hC).vertex_avg
      edge_inverse := AddScalarInvertibleOn.mono hsub (h C₁ hC₁).edge_inverse
      vertex_inverse := AddScalarInvertibleOn.mono hsub (h C₁ hC₁).vertex_inverse }
theorem stripBounds_csInf {L k : ℕ} {δ δ' : ℝ} {B : Set ℝ} (hδ : δ' ≤ δ) (hne : B.Nonempty)
    (hbdd : BddBelow B) (h : ∀ C ∈ B, StripBounds L k δ C) : StripBounds L k δ' (sInf B) := by
  have hsub : imStrip (2 * δ') ⊆ imStrip (2 * δ) := fun κ hκ μ =>
    (hκ μ).trans (mul_le_mul_of_nonneg_left hδ zero_le_two)
  exact ⟨boundedSymbols_csInf hsub hne hbdd fun C hC => (h C hC).1, fun t ht τ hτ =>
    invertibleSymbols_csInf hsub hne hbdd fun C hC => (h C hC).2 t ht τ hτ⟩
theorem bddBelow_admissibleConstants (δ : ℝ) : BddBelow (admissibleConstants δ) :=
  ⟨1, fun _ hC => hC.2.1⟩
theorem constantsAreAdmissible_of_freeStripEstimate (hstrip : FreeStripEstimate) :
    ConstantsAreAdmissible := by
  obtain ⟨δ, hδ, C, hC, hA⟩ := hstrip
  have hrate : δ ∈ admissibleRates := ⟨C, hδ, hC, hA⟩
  have hne : admissibleRates.Nonempty := ⟨δ, hrate⟩
  have hub : ∀ d ∈ admissibleRates, d ≤ 1 / 32 := fun d ⟨_, h⟩ => h.1.2
  have hbdd : BddAbove admissibleRates := ⟨1 / 32, hub⟩
  have hpos : 0 < sSup admissibleRates := hδ.1.trans_le (le_csSup hbdd hrate)
  have hle : sSup admissibleRates ≤ 1 / 32 := csSup_le hne hub
  have hhalf : 1 / 2 * sSup admissibleRates ∈ Ioc (0 : ℝ) (1 / 64) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨δ', ⟨C', hpair⟩, hlt⟩ :=
    exists_lt_of_lt_csSup hne (show 1 / 2 * sSup admissibleRates < sSup admissibleRates by linarith)
  have hhalf' : 1 / 2 * sSup admissibleRates ∈ Ioc (0 : ℝ) (1 / 32) :=
    ⟨hhalf.1, hhalf.2.trans (by norm_num)⟩
  have hconsts : (admissibleConstants (1 / 2 * sSup admissibleRates)).Nonempty := by
    refine ⟨C', hhalf', hpair.2.1, fun L hL k hk => ?_⟩
    have h := stripBounds_csInf (L := L) (k := k) hlt.le (singleton_nonempty C')
      (bddBelow_singleton) fun c hc => by
        rw [mem_singleton_iff.mp hc]
        exact hpair.2.2 L hL k hk
    rwa [csInf_singleton] at h
  refine ⟨hne, ?_, 1 / 2 * sSup admissibleRates, ⟨hne, rfl⟩,
    sInf (admissibleConstants (1 / 2 * sSup admissibleRates)),
    Part.mem_bind (show 1 / 2 * sSup admissibleRates ∈ halfSupRate from ⟨hne, rfl⟩) ⟨hconsts, rfl⟩,
    hhalf, ?_, hhalf', ?_, fun L hL k hk => ?_⟩
  · rintro _ ⟨_, rfl⟩
    exact hconsts
  · exact le_csInf hconsts fun _ hc => hc.2.1
  · exact le_csInf hconsts fun _ hc => hc.2.1
  · exact stripBounds_csInf le_rfl hconsts (bddBelow_admissibleConstants _)
      fun c hc => hc.2.2 L hL k hk
end YangMills.Construction.Tower.FreeStrip.ConstantsAdmissible
end
