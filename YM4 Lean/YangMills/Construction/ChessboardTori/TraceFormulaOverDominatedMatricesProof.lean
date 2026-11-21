import YangMills.Construction.ChessboardTori.ExpansionOfTheCrossingKernel
import YangMills.Construction.ChessboardTori.TraceFormulaOverDominatedMatrices
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori.DominatedTraceFormula
open TransferSetup
variable {S : ChessboardSetup} {T : TransferSetup S}
theorem isProbabilityMeasure_slabHaar : IsProbabilityMeasure T.slabHaar := by
  unfold slabHaar
  infer_instance
theorem norm_indexMonomial_le (hExp : KernelExpansion.Statement)
    (a : T.WordIndex) (U : T.EdgeField) : ‖T.indexMonomial a U‖ ≤ 1 := by
  unfold indexMonomial
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
    fun b _ => ((hExp S T).1 (U b) (U b)).1 (a b)
theorem norm_averagedMonomial_le (hExp : KernelExpansion.Statement)
    (a : T.WordIndex) (U : T.EdgeField) : ‖T.averagedMonomial a U‖ ≤ 1 := by
  unfold averagedMonomial
  have h := norm_integral_le_of_norm_le_const (μ := T.siteHaar) (C := 1)
    (f := fun V => T.indexMonomial a (T.gaugeAct V U))
    (Filter.Eventually.of_forall fun V => norm_indexMonomial_le hExp a _)
  simpa using h
theorem weightedEntry_le (hExp : KernelExpansion.Statement)
    {Φ : T.SlabConfig → ℂ} {R : ℝ} (hR : ∀ η, ‖Φ η‖ ≤ R)
    (p : T.WordIndex × T.WordIndex) : T.weightedEntry (T.slabKernelMatrix Φ) p ≤ R := by
  obtain ⟨a, a'⟩ := p
  have : IsProbabilityMeasure T.slabHaar := isProbabilityMeasure_slabHaar
  have hc : 0 < T.indexWeight a * T.indexWeight a' :=
    mul_pos (T.indexWeight_pos a) (T.indexWeight_pos a')
  have hI : ‖∫ η, T.averagedMonomial a (T.slabFirst η) * Φ η *
      starRingEnd ℂ (T.averagedMonomial a' (T.slabLast η)) ∂T.slabHaar‖ ≤ R := by
    have h := norm_integral_le_of_norm_le_const (μ := T.slabHaar) (C := R)
      (f := fun η => T.averagedMonomial a (T.slabFirst η) * Φ η *
        starRingEnd ℂ (T.averagedMonomial a' (T.slabLast η)))
      (Filter.Eventually.of_forall fun η => by
        have h0 : 0 ≤ R := (norm_nonneg _).trans (hR η)
        have h1 := norm_averagedMonomial_le hExp a (T.slabFirst η)
        have h2 := norm_averagedMonomial_le hExp a' (T.slabLast η)
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        calc ‖T.averagedMonomial a (T.slabFirst η)‖ * ‖Φ η‖ *
              ‖T.averagedMonomial a' (T.slabLast η)‖
            ≤ 1 * R * 1 := by gcongr; exact hR η
          _ = R := by ring)
    simpa using h
  have hone : (T.indexWeight a * T.indexWeight a') ^ (-(1 / 2) : ℝ) *
      Real.sqrt (T.indexWeight a * T.indexWeight a') = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hc]
    norm_num
  unfold weightedEntry
  simp only
  rw [slabKernelMatrix_eq_integral, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), ← mul_assoc, hone, one_mul]
  exact hI
theorem proof (hTrace : CyclicTraceFormula.Statement) (hExp : KernelExpansion.Statement) :
    DominatedTraceFormula.Statement := by
  intro S T
  obtain ⟨h1, h2, -⟩ := hTrace S T
  refine ⟨fun Φ hΦ => ?_, h2⟩
  obtain ⟨-, C, hC⟩ := id hΦ
  have hb : BddAbove (Set.range fun η => ‖Φ η‖) := ⟨C, by rintro _ ⟨η, rfl⟩; exact hC η⟩
  have hR : ∀ η, ‖Φ η‖ ≤ ⨆ η, ‖Φ η‖ := fun η => le_ciSup hb η
  have hr := weightedEntry_le hExp hR
  refine ⟨⟨_, by rintro _ ⟨p, rfl⟩; exact hr p⟩, ?_, (h1 Φ hΦ).2.2⟩
  exact Real.iSup_le hr (Real.iSup_nonneg fun _ => norm_nonneg _)
end YangMills.Construction.ChessboardTori.DominatedTraceFormula
end
