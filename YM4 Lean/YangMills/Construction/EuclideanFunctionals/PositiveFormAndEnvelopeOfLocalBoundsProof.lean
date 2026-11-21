import YangMills.Construction.EuclideanFunctionals.PositiveFormAndEnvelopeOfLocalBounds
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.PositivityAndEnvelope
open DefinitionComparison
theorem sharpNorm_nonneg (m : SharpScale) (f : R4 → ℝ) : 0 ≤ m.sharpNorm f := by
  have h : 0 ≤ TestFunctions.uniformNorm f := Real.iSup_nonneg (fun _ => norm_nonneg _)
  exact le_trans h (le_max_left _ _)
theorem lowerEnvelope_set_bddBelow (K : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (d R : ℝ) :
    BddBelow ((fun d' => max (K n d' R) 0) '' Set.Ioc 0 d) :=
  ⟨0, by rintro _ ⟨x, _, rfl⟩; exact le_max_right _ _⟩
theorem lowerEnvelope_nonneg (K : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (d R : ℝ) (hd : 0 < d) :
    0 ≤ lowerEnvelope K n d R := by
  refine le_csInf ⟨_, ⟨d, ⟨hd, le_rfl⟩, rfl⟩⟩ ?_
  rintro _ ⟨x, _, rfl⟩; exact le_max_right _ _
theorem holds_proof : Holds := by
  intro m S
  refine ⟨?_, ?_, ?_⟩
  · unfold OSPositive IsOSPositive
    simp only [finCombIn_eq_freeSpanIn]
    refine forall_congr' fun F => imp_congr_right fun _ => ?_
    rw [Complex.le_def]
    simp only [Complex.zero_re, Complex.zero_im]
    constructor
    · rintro ⟨a, b⟩; exact ⟨b.symm, a⟩
    · rintro ⟨a, b⟩; exact ⟨b, a.symm⟩
  · intro K K' n d R _ _ _ h
    unfold lowerEnvelope
    congr 1
    apply Set.image_congr
    intro x hx
    rw [h x hx]
  · intro K hK
    refine ⟨?_, fun n d R _ _ hd => lowerEnvelope_nonneg K n d R hd, ?_⟩
    · intro n hn R d hR hd f hf hb hsep
      have hp : 0 ≤ ∏ i, m.sharpNorm (f i) := Finset.prod_nonneg fun i _ => sharpNorm_nonneg m _
      rcases hp.eq_or_lt with h0 | hpos
      · have := hK n hn R d hR hd f hf hb hsep
        rw [← h0] at this ⊢
        simpa using this
      · rw [← div_le_iff₀ hpos]
        refine le_csInf ⟨_, ⟨d, ⟨hd, le_rfl⟩, rfl⟩⟩ ?_
        rintro _ ⟨x, ⟨hx0, hxd⟩, rfl⟩
        rw [div_le_iff₀ hpos]
        have hsep' : Pairwise fun i j => ENNReal.ofReal x ≤
            TestFunctions.setDistR4 (supp (f i)) (supp (f j)) :=
          fun i j hij => le_trans (ENNReal.ofReal_le_ofReal hxd) (hsep hij)
        have := hK n hn R x hR hx0 f hf hb hsep'
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
    · intro n d₁ d₂ R _ _ h1 h12
      refine csInf_le_csInf (lowerEnvelope_set_bddBelow K n d₂ R) ⟨_, ⟨d₁, ⟨h1, le_rfl⟩, rfl⟩⟩ ?_
      exact Set.image_mono fun x hx => ⟨hx.1, hx.2.trans h12⟩
end YangMills.Construction.EuclideanFunctionals.PositivityAndEnvelope
