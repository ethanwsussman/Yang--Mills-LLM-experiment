import YangMills.Construction.ChessboardTori.OuterConfigurationAgainstTheFreeBox
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionSeesNeitherCornerNorSense
import YangMills.Construction.InfiniteLattice.WilsonKernelOfBondsWithOneOrientation
import YangMills.Construction.ReflectionPositiveLimits.ProductOfTheHaarMeasuresOnTheLinks
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open YangMills.Construction.InfiniteLattice YangMills.Construction.GibbsAtFixedSpacing
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.ChessboardTori.FreeBoxComparison
variable {D : ChessboardSetup} (B : Set AmbientSpace)
def boxLinkSet (D : ChessboardSetup) (B : Set AmbientSpace) : OrientedLinkSet D.mesh :=
  ⟨D.boxLinks B, D.hasNoOppositePairs_boxLinks B⟩
instance isProbabilityMeasure_boxHaar : IsProbabilityMeasure (D.boxHaar B) := by
  unfold ChessboardSetup.boxHaar LinkVariables.haarMeasure Matrices.ComplexMatrix2.haarPi
  infer_instance
instance borelSpace_boxLinkVariables : BorelSpace (D.BoxLinkVariables B) :=
  HaarProductMeasure.borelSpace_linkVariables _
theorem continuous_overwriteBox (ξ : D.GaugeField) :
    Continuous fun V : D.BoxLinkVariables B => D.overwriteBox B V ξ :=
  (boxLinkSet D B).continuous_glue ξ
theorem plaquettesTouching_boxLinks_finite : (plaquettesTouching (D.boxLinks B)).Finite :=
  (boxLinkSet D B).faces_finite.subset fun p hp =>
    (mem_plaquettesTouching_iff D.mesh_pos _ p).mp hp
def boundaryPlaquettes (D : ChessboardSetup) (B : Set AmbientSpace) : Set D.Plaquette :=
  {p : D.Plaquette | (∃ b ∈ p.edges, b ∈ D.boxLinks B) ∧
    ∃ b ∈ p.edges, b ∉ D.boxLinks B}
theorem plaquettesTouching_boxLinks_eq_union :
    plaquettesTouching (D.boxLinks B) = D.interiorPlaquettes B ∪ boundaryPlaquettes D B := by
  ext p
  rw [mem_plaquettesTouching_iff D.mesh_pos]
  constructor
  · rintro ⟨b, hb, h⟩
    have hb' : b ∈ D.boxLinks B := h.resolve_right fun hr =>
      opposite_notMem_positiveLinks D.mesh_pos
        ((mem_edgesOf_iff_mem_edges D.mesh_pos p b).mpr hb).1
        (D.coe_boxLinks_subset_positive B (Finset.mem_coe.mpr hr))
    by_cases hin : p ∈ D.interiorPlaquettes B
    · exact Or.inl hin
    · refine Or.inr ⟨⟨b, hb, hb'⟩, ?_⟩
      simpa [ChessboardSetup.interiorPlaquettes] using hin
  · rintro (h | ⟨⟨b, hb, h⟩, -⟩)
    · have hm : Link.forwardFrom p.corner p.lowAxis ∈ p.edges := by
        simp [ElementaryPlaquette.edges]
      exact ⟨_, hm, Or.inl (h _ hm)⟩
    · exact ⟨b, hb, Or.inl h⟩
theorem disjoint_interior_boundaryPlaquettes :
    Disjoint (D.interiorPlaquettes B) (boundaryPlaquettes D B) := by
  refine Set.disjoint_left.mpr fun p hp hs => ?_
  obtain ⟨-, b, hb, h⟩ := hs
  exact h (hp b hb)
theorem interiorPlaquettes_finite : (D.interiorPlaquettes B).Finite :=
  (plaquettesTouching_boxLinks_finite B).subset (by
    rw [plaquettesTouching_boxLinks_eq_union]
    exact subset_union_left)
theorem boundaryPlaquettes_finite : (boundaryPlaquettes D B).Finite :=
  (plaquettesTouching_boxLinks_finite B).subset (by
    rw [plaquettesTouching_boxLinks_eq_union]
    exact subset_union_right)
variable {B}
theorem continuous_finsum_faceEnergy {s : Set D.Plaquette} (hs : s.Finite)
    (ξ : D.GaugeField) :
    Continuous fun V : D.BoxLinkVariables B =>
      ∑ᶠ p ∈ s, faceEnergy (D.overwriteBox B V ξ) p := by
  simp only [finsum_mem_eq_finite_toFinset_sum _ hs]
  exact continuous_finsetSum _ fun p _ =>
    (continuous_faceEnergy p).comp (continuous_overwriteBox B ξ)
theorem finsum_faceEnergy_nonneg (hE : ∀ (p : D.Plaquette) (U : D.GaugeField),
      0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2)
    {s : Set D.Plaquette} (hs : s.Finite) (U : D.GaugeField) :
    0 ≤ ∑ᶠ p ∈ s, faceEnergy U p := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs]
  exact Finset.sum_nonneg fun p _ => (hE p U).1
theorem integrable_mul_boltzmann (hE : ∀ (p : D.Plaquette) (U : D.GaugeField),
      0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2)
    {s : Set D.Plaquette} (hs : s.Finite) (ξ : D.GaugeField) {f : D.BoxLinkVariables B → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ V, |f V| ≤ C) :
    Integrable (fun V => f V * Real.exp (-D.β *
      ∑ᶠ p ∈ s, faceEnergy (D.overwriteBox B V ξ) p)) (D.boxHaar B) := by
  have hm : Measurable fun V : D.BoxLinkVariables B => Real.exp (-D.β *
      ∑ᶠ p ∈ s, faceEnergy (D.overwriteBox B V ξ) p) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_finsum_faceEnergy hs ξ))).measurable
  refine Integrable.of_bound (hf.mul hm).aestronglyMeasurable C (.of_forall fun V => ?_)
  have h₀ := finsum_faceEnergy_nonneg hE hs (D.overwriteBox B V ξ)
  have hβ := D.beta_pos
  have h₁ : Real.exp (-D.β * ∑ᶠ p ∈ s, faceEnergy (D.overwriteBox B V ξ) p) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have h₂ := Real.exp_pos (-D.β * ∑ᶠ p ∈ s, faceEnergy (D.overwriteBox B V ξ) p)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos h₂]
  calc |f V| * _ ≤ |f V| * 1 := mul_le_mul_of_nonneg_left h₁ (abs_nonneg _)
    _ ≤ C := by simpa using hC V
theorem energy_sums_compare (hE : ∀ (p : D.Plaquette) (U : D.GaugeField),
      0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2)
    (V : D.BoxLinkVariables B) (ξ : D.GaugeField) :
    (∑ᶠ p ∈ D.interiorPlaquettes B,
        D.evalOnBox B (fun U : D.GaugeField => faceEnergy U p) V) ≤
      ∑ᶠ p ∈ plaquettesTouching (D.boxLinks B), faceEnergy (D.overwriteBox B V ξ) p ∧
    (∑ᶠ p ∈ plaquettesTouching (D.boxLinks B), faceEnergy (D.overwriteBox B V ξ) p) ≤
      (∑ᶠ p ∈ D.interiorPlaquettes B,
        D.evalOnBox B (fun U : D.GaugeField => faceEnergy U p) V) +
        2 * (D.boundaryPlaquetteCount B : ℝ) := by
  have hin : (∑ᶠ p ∈ D.interiorPlaquettes B,
        D.evalOnBox B (fun U : D.GaugeField => faceEnergy U p) V) =
      ∑ᶠ p ∈ D.interiorPlaquettes B, faceEnergy (D.overwriteBox B V ξ) p :=
    finsum_mem_congr rfl fun p hp =>
      ChessboardSetup.evalOnBox_eq_overwriteBox
        (ChessboardSetup.dependsOnlyOnLinks_faceEnergy hp) V ξ
  have hunion : (∑ᶠ p ∈ plaquettesTouching (D.boxLinks B),
        faceEnergy (D.overwriteBox B V ξ) p) =
      (∑ᶠ p ∈ D.interiorPlaquettes B, faceEnergy (D.overwriteBox B V ξ) p) +
        ∑ᶠ p ∈ boundaryPlaquettes D B, faceEnergy (D.overwriteBox B V ξ) p := by
    rw [plaquettesTouching_boxLinks_eq_union]
    exact finsum_mem_union (disjoint_interior_boundaryPlaquettes B)
      (interiorPlaquettes_finite B) (boundaryPlaquettes_finite B)
  have hlo := finsum_faceEnergy_nonneg hE (boundaryPlaquettes_finite B) (D.overwriteBox B V ξ)
  have hhi : (∑ᶠ p ∈ boundaryPlaquettes D B, faceEnergy (D.overwriteBox B V ξ) p) ≤
      2 * (D.boundaryPlaquetteCount B : ℝ) := by
    have hcount : D.boundaryPlaquetteCount B =
        (boundaryPlaquettes_finite (D := D) B).toFinset.card :=
      Set.ncard_eq_toFinset_card _ (boundaryPlaquettes_finite B)
    rw [finsum_mem_eq_finite_toFinset_sum _ (boundaryPlaquettes_finite B), hcount]
    calc _ ≤ ∑ _q ∈ (boundaryPlaquettes_finite (D := D) B).toFinset, (2 : ℝ) :=
          Finset.sum_le_sum fun p _ => (hE p _).2
      _ = _ := by simp [mul_comm]
  rw [hin, hunion]
  constructor <;> linarith
theorem boltzmann_weights_compare (hE : ∀ (p : D.Plaquette) (U : D.GaugeField),
      0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2)
    (V : D.BoxLinkVariables B) (ξ : D.GaugeField) :
    Real.exp (-2 * D.β * (D.boundaryPlaquetteCount B : ℝ)) *
        Real.exp (-D.β * ∑ᶠ p ∈ D.interiorPlaquettes B,
          D.evalOnBox B (fun U : D.GaugeField => faceEnergy U p) V) ≤
      Real.exp (-D.β * ∑ᶠ p ∈ plaquettesTouching (D.boxLinks B),
        faceEnergy (D.overwriteBox B V ξ) p) ∧
    Real.exp (-D.β * ∑ᶠ p ∈ plaquettesTouching (D.boxLinks B),
        faceEnergy (D.overwriteBox B V ξ) p) ≤
      Real.exp (-D.β * ∑ᶠ p ∈ D.interiorPlaquettes B,
        D.evalOnBox B (fun U : D.GaugeField => faceEnergy U p) V) := by
  obtain ⟨h₁, h₂⟩ := energy_sums_compare hE V ξ
  have hβ := D.beta_pos
  rw [← Real.exp_add]
  constructor
  · exact Real.exp_le_exp.mpr (by nlinarith)
  · exact Real.exp_le_exp.mpr (by nlinarith)
theorem freeBoxPartition_eq_integral {Ψ : D.GaugeField → ℂ} {f : D.BoxLinkVariables B → ℝ}
    (hval : ∀ V, D.evalOnBox B Ψ V = (f V : ℂ)) :
    D.freeBoxPartition B Ψ =
      ((∫ V, f V * Real.exp (-D.β * ∑ᶠ p ∈ D.interiorPlaquettes B,
        D.evalOnBox B (fun U : D.GaugeField => faceEnergy U p) V)
          ∂D.boxHaar B : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (.of_forall fun V => ?_)
  simp only [hval V, Complex.ofReal_mul]
theorem boundaryConditionPartition_eq_integral {Ψ : D.GaugeField → ℂ}
    {f : D.BoxLinkVariables B → ℝ}
    (hval : ∀ V, D.evalOnBox B Ψ V = (f V : ℂ)) (ξ : D.GaugeField) :
    D.boundaryConditionPartition B ξ Ψ =
      ((∫ V, f V * Real.exp (-D.β * ∑ᶠ p ∈ plaquettesTouching (D.boxLinks B),
        faceEnergy (D.overwriteBox B V ξ) p) ∂D.boxHaar B : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (.of_forall fun V => ?_)
  simp only [hval V, Complex.ofReal_mul]
theorem statement_holds (hface : GibbsAtFixedSpacing.FaceEnergyIndependentOfBasepointAndOrientation) :
    FreeBoxComparison.Statement := by
  intro D g _ _ B _
  have hE : ∀ (p : D.Plaquette) (U : D.GaugeField),
      0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2 :=
    fun p U => ((hface.2 D.mesh D.mesh_pos).2.1 p).2.2.2 U
  have hfin := interiorPlaquettes_finite (D := D) B
  have hout := plaquettesTouching_boxLinks_finite (D := D) B
  refine ⟨?_, fun Ψ hΨ hnn => ?_⟩
  · have hone : D.freeBoxPartition B (fun _ => 1) =
        ((∫ V, (1 : ℝ) * Real.exp (-D.β * ∑ᶠ p ∈ D.interiorPlaquettes B,
          D.evalOnBox B (fun U : D.GaugeField => faceEnergy U p) V)
            ∂D.boxHaar B : ℝ) : ℂ) :=
      freeBoxPartition_eq_integral (f := fun _ => 1) fun V => by
        simp [ChessboardSetup.evalOnBox]
    rw [hone, Complex.zero_lt_real]
    simp only [one_mul]
    have hint := integrable_mul_boltzmann (B := B) hE hfin (trivialField D.mesh)
      (f := fun _ => 1) measurable_const (C := 1) (fun V => by simp)
    simp only [one_mul] at hint
    exact integral_exp_pos hint
  · obtain ⟨hmeas, C, hC⟩ := hΨ.1
    set f : D.BoxLinkVariables B → ℝ := fun V => (D.evalOnBox B Ψ V).re with hfdef
    have hval : ∀ V, D.evalOnBox B Ψ V = (f V : ℂ) := fun V =>
      Complex.ext rfl (by
        simpa [ChessboardSetup.evalOnBox] using
          (Complex.le_def.mp (hnn (D.overwriteBox B V (trivialField D.mesh)))).2.symm)
    have hf0 : ∀ V, 0 ≤ f V := fun V => (Complex.le_def.mp (hnn _)).1
    have hfm : Measurable f :=
      Complex.measurable_re.comp
        (hmeas.comp (continuous_overwriteBox B (trivialField D.mesh)).measurable)
    have hfC : ∀ V, |f V| ≤ C := fun V => (Complex.abs_re_le_norm _).trans (hC _)
    have hIF := integrable_mul_boltzmann (B := B) hE hfin (trivialField D.mesh) hfm hfC
    refine ⟨?_, fun ξ => ?_⟩
    · rw [freeBoxPartition_eq_integral hval, Complex.zero_le_real]
      exact integral_nonneg fun V => mul_nonneg (hf0 V) (Real.exp_pos _).le
    · have hIO := integrable_mul_boltzmann (B := B) hE hout ξ hfm hfC
      rw [freeBoxPartition_eq_integral hval, boundaryConditionPartition_eq_integral hval ξ,
        ← Complex.ofReal_mul]
      constructor
      · rw [Complex.real_le_real, ← integral_const_mul]
        refine integral_mono (hIF.const_mul _) hIO fun V => ?_
        have := mul_le_mul_of_nonneg_left (boltzmann_weights_compare hE V ξ).1 (hf0 V)
        simp only
        nlinarith
      · rw [Complex.real_le_real]
        exact integral_mono hIO hIF fun V =>
          mul_le_mul_of_nonneg_left (boltzmann_weights_compare hE V ξ).2 (hf0 V)
end YangMills.Construction.ChessboardTori.FreeBoxComparison
end
