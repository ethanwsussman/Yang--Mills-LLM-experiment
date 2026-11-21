import YangMills.Construction.Lattice.BondEndpointsAndFiniteness
import YangMills.Construction.Lattice.CovarianceAndBorelMeasurabilityOfTheAveragedContours
import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Lattice.LocalityAndGaugeCovarianceOfTheAveragingMapProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction
noncomputable section
namespace Matrices.ComplexMatrix2
variable {ι : Type} [Fintype ι]
private instance : SecondCountableTopology specialUnitary :=
  haveI : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
private theorem continuous_star_val :
    Continuous fun W : specialUnitary => star (W : ComplexMatrix2) :=
  Continuous.matrix_conjTranspose continuous_subtype_val
private def quotientAt (p : (ι → specialUnitary) × specialUnitary) (i : ι) : ComplexMatrix2 :=
  (p.1 i : ComplexMatrix2) * star (p.2 : ComplexMatrix2)
omit [Fintype ι] in
private theorem continuous_quotientAt (i : ι) :
    Continuous fun p : (ι → specialUnitary) × specialUnitary => quotientAt p i :=
  (continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)).mul
    (continuous_star_val.comp continuous_snd)
private def meanPairs (ι : Type) [Fintype ι] (ε : ℝ) : Set ((ι → specialUnitary) × specialUnitary) :=
  {p | (∀ i, operatorNorm (quotientAt p i - 1) ≤ ε) ∧ ∑ i, logSeries (quotientAt p i) = 0}
private theorem continuousOn_logSeries (E : ExpLogEstimates) {ε : ℝ} (h0 : 0 ≤ ε)
    (h1 : ε < 1) : ContinuousOn logSeries {X : ComplexMatrix2 | operatorNorm (X - 1) ≤ ε} := by
  have hpos : 0 ≤ 1 / (1 - ε) := by
    have : 0 < 1 - ε := by linarith
    positivity
  have hL : LipschitzOnWith (Real.toNNReal (1 / (1 - ε))) logSeries
      {X : ComplexMatrix2 | operatorNorm (X - 1) ≤ ε} := by
    refine LipschitzOnWith.of_dist_le_mul fun A hA B hB => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hpos]
    exact (E.2.2.2.2.2.2.2.2.1 ε A B h0 h1 hA hB).2.2.2
  exact hL.continuousOn
private theorem isClosed_meanPairs (E : ExpLogEstimates) {ε : ℝ} (h0 : 0 ≤ ε)
    (h1 : ε < 1) : IsClosed (meanPairs ι ε) := by
  have hC : IsClosed {p : (ι → specialUnitary) × specialUnitary |
      ∀ i, operatorNorm (quotientAt p i - 1) ≤ ε} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i =>
      isClosed_le (continuous_norm.comp ((continuous_quotientAt i).sub continuous_const))
        continuous_const
  have hsum : ContinuousOn
      (fun p : (ι → specialUnitary) × specialUnitary => ∑ i, logSeries (quotientAt p i))
      {p | ∀ i, operatorNorm (quotientAt p i - 1) ≤ ε} := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact (continuousOn_logSeries E h0 h1).comp (continuous_quotientAt i).continuousOn
      fun p hp => hp i
  exact hsum.preimage_isClosed_of_isClosed hC (isClosed_singleton (x := (0 : ComplexMatrix2)))
private def radiusSeq (h : ℕ) : ℝ := 1 - 1 / ((h : ℝ) + 2)
private theorem radiusSeq_nonneg (h : ℕ) : 0 ≤ radiusSeq h := by
  have : 1 / ((h : ℝ) + 2) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by have : (0 : ℝ) ≤ h := Nat.cast_nonneg h; linarith)
  unfold radiusSeq
  linarith
private theorem radiusSeq_lt_one (h : ℕ) : radiusSeq h < 1 := by
  have : 0 < 1 / ((h : ℝ) + 2) := by positivity
  unfold radiusSeq
  linarith
private theorem radiusSeq_mono {h h' : ℕ} (hh : h ≤ h') : radiusSeq h ≤ radiusSeq h' := by
  have e : (h : ℝ) ≤ h' := by exact_mod_cast hh
  have : 1 / ((h' : ℝ) + 2) ≤ 1 / ((h : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  unfold radiusSeq
  linarith
private theorem meanPairs_mono {h h' : ℕ} (hh : h ≤ h') :
    meanPairs ι (radiusSeq h) ⊆ meanPairs ι (radiusSeq h') :=
  fun _ hp => ⟨fun i => (hp.1 i).trans (radiusSeq_mono hh), hp.2⟩
private abbrev asMatrices (V : ι → specialUnitary) : ι → ComplexMatrix2 :=
  fun i => (V i : ComplexMatrix2)
private theorem isLogMean_iff_mem_meanPairs (V : ι → specialUnitary) (W : specialUnitary) :
    IsLogMean (specialUnitary : Set ComplexMatrix2) (asMatrices V) (W : ComplexMatrix2) ↔
      ∃ h : ℕ, (V, W) ∈ meanPairs ι (radiusSeq h) := by
  have e : ∀ i, (V i : ComplexMatrix2) * (W : ComplexMatrix2)⁻¹ = quotientAt (V, W) i :=
    fun i => by
      rw [inv_eq_star_of_mem_specialUnitary W.2]
      rfl
  simp only [IsLogMean, asMatrices, e]
  constructor
  · rintro ⟨-, hn, hs⟩
    have hex : ∀ i, ∃ h : ℕ, operatorNorm (quotientAt (V, W) i - 1) ≤ radiusSeq h := by
      intro i
      obtain ⟨n, hn'⟩ := exists_nat_one_div_lt (sub_pos.mpr (hn i))
      refine ⟨n, ?_⟩
      have : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      unfold radiusSeq
      linarith
    choose g hg using hex
    exact ⟨Finset.univ.sup g, fun i => (hg i).trans
      (radiusSeq_mono (Finset.le_sup (Finset.mem_univ i))), hs⟩
  · rintro ⟨h, hn, hs⟩
    exact ⟨W.2, fun i => (hn i).trans_lt (radiusSeq_lt_one h), hs⟩
private theorem mem_of_isLogMean {V : ι → ComplexMatrix2} {W : ComplexMatrix2}
    (h : IsLogMean (specialUnitary : Set ComplexMatrix2) V W) : W ∈ specialUnitary := h.1
private def uniqueMeanFamilies (ι : Type) [Fintype ι] : Set (ι → specialUnitary) :=
  {V | HasUniqueLogMean (specialUnitary : Set ComplexMatrix2) (asMatrices V)}
private def twoMeanTriples (ι : Type) [Fintype ι] (h q : ℕ) :
    Set ((ι → specialUnitary) × specialUnitary × specialUnitary) :=
  {p | (p.1, p.2.1) ∈ meanPairs ι (radiusSeq h) ∧ (p.1, p.2.2) ∈ meanPairs ι (radiusSeq h) ∧
    1 / ((q : ℝ) + 1) ≤ operatorNorm ((p.2.1 : ComplexMatrix2) - (p.2.2 : ComplexMatrix2))}
private theorem isClosed_twoMeanTriples (E : ExpLogEstimates) (h q : ℕ) :
    IsClosed (twoMeanTriples ι h q) := by
  have hp := isClosed_meanPairs (ι := ι) E (radiusSeq_nonneg h) (radiusSeq_lt_one h)
  have c1 : Continuous fun p : (ι → specialUnitary) × specialUnitary × specialUnitary =>
      (p.1, p.2.1) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have c2 : Continuous fun p : (ι → specialUnitary) × specialUnitary × specialUnitary =>
      (p.1, p.2.2) :=
    continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  have c3 : Continuous fun p : (ι → specialUnitary) × specialUnitary × specialUnitary =>
      operatorNorm ((p.2.1 : ComplexMatrix2) - (p.2.2 : ComplexMatrix2)) :=
    continuous_norm.comp
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).sub
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  exact (hp.preimage c1).inter ((hp.preimage c2).inter (isClosed_le continuous_const c3))
private theorem measurableSet_uniqueMeanFamilies (E : ExpLogEstimates) :
    MeasurableSet (uniqueMeanFamilies ι) := by
  have hA : MeasurableSet (⋃ h : ℕ, Prod.fst '' meanPairs ι (radiusSeq h)) :=
    MeasurableSet.iUnion fun h =>
      (((isClosed_meanPairs E (radiusSeq_nonneg h) (radiusSeq_lt_one h)).isCompact.image
        continuous_fst).isClosed).measurableSet
  have hB : MeasurableSet (⋃ h : ℕ, ⋃ q : ℕ, Prod.fst '' twoMeanTriples ι h q) :=
    MeasurableSet.iUnion fun h => MeasurableSet.iUnion fun q =>
      (((isClosed_twoMeanTriples E h q).isCompact.image continuous_fst).isClosed).measurableSet
  have e : uniqueMeanFamilies ι = (⋃ h : ℕ, Prod.fst '' meanPairs ι (radiusSeq h)) \
      (⋃ h : ℕ, ⋃ q : ℕ, Prod.fst '' twoMeanTriples ι h q) := by
    ext V
    simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨W, hW, hu⟩
      obtain ⟨h, hh⟩ := (isLogMean_iff_mem_meanPairs V ⟨W, mem_of_isLogMean hW⟩).mp hW
      refine ⟨⟨h, (V, ⟨W, mem_of_isLogMean hW⟩), hh, rfl⟩, ?_⟩
      rintro ⟨h', q, ⟨⟨V', W₁, W₂⟩, ⟨h₁, h₂, h₃⟩, rfl⟩⟩
      have m₁ := (isLogMean_iff_mem_meanPairs V' W₁).mpr ⟨h', h₁⟩
      have m₂ := (isLogMean_iff_mem_meanPairs V' W₂).mpr ⟨h', h₂⟩
      have e₁ : (W₁ : ComplexMatrix2) = W₂ := (hu _ m₁).trans (hu _ m₂).symm
      simp only [e₁, sub_self, norm_zero] at h₃
      have : 0 < 1 / ((q : ℝ) + 1) := by positivity
      linarith
    · rintro ⟨⟨h, ⟨V', W⟩, hp, rfl⟩, hB'⟩
      have hW := (isLogMean_iff_mem_meanPairs V' W).mpr ⟨h, hp⟩
      refine ⟨(W : ComplexMatrix2), hW, fun W' hW' => ?_⟩
      by_contra hne
      have hW'' : (W' : ComplexMatrix2) ∈ specialUnitary := mem_of_isLogMean hW'
      obtain ⟨h', hp'⟩ := (isLogMean_iff_mem_meanPairs V' ⟨W', hW''⟩).mp hW'
      have hpos : 0 < operatorNorm ((W : ComplexMatrix2) - W') :=
        norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
      obtain ⟨q, hq⟩ := exists_nat_one_div_lt hpos
      refine hB' ⟨max h h', q, ⟨V', W, ⟨W', hW''⟩⟩, ⟨meanPairs_mono (le_max_left _ _) hp,
        meanPairs_mono (le_max_right _ _) hp', hq.le⟩, rfl⟩
  rw [e]
  exact hA.diff hB
private theorem logMean_spec {V : ι → specialUnitary} (hV : V ∈ uniqueMeanFamilies ι) :
    IsLogMean (specialUnitary : Set ComplexMatrix2) (asMatrices V)
      (logMean (specialUnitary : Set ComplexMatrix2) (asMatrices V)) :=
  Classical.epsilon_spec (ExistsUnique.exists hV)
private theorem exists_measurable_logMean (E : ExpLogEstimates) :
    ∃ f : uniqueMeanFamilies ι → specialUnitary, Measurable f ∧
      ∀ V : uniqueMeanFamilies ι,
        (f V : ComplexMatrix2) = logMean (specialUnitary : Set ComplexMatrix2) (asMatrices V.1) := by
  refine ⟨fun V => ⟨logMean (specialUnitary : Set ComplexMatrix2) (asMatrices V.1),
    mem_of_isLogMean (logMean_spec V.2)⟩, ?_, fun _ => rfl⟩
  refine measurable_of_isClosed fun C hC => ?_
  have hD : MeasurableSet (⋃ h : ℕ, Prod.fst '' (meanPairs ι (radiusSeq h) ∩ Prod.snd ⁻¹' C)) :=
    MeasurableSet.iUnion fun h =>
      ((((isClosed_meanPairs E (radiusSeq_nonneg h) (radiusSeq_lt_one h)).inter
        (hC.preimage continuous_snd)).isCompact.image continuous_fst).isClosed).measurableSet
  have e : (fun V : uniqueMeanFamilies ι =>
      (⟨logMean (specialUnitary : Set ComplexMatrix2) (asMatrices V.1),
        mem_of_isLogMean (logMean_spec V.2)⟩ : specialUnitary)) ⁻¹' C =
      Subtype.val ⁻¹' (⋃ h : ℕ, Prod.fst '' (meanPairs ι (radiusSeq h) ∩ Prod.snd ⁻¹' C)) := by
    ext V
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Set.mem_inter_iff]
    constructor
    · intro hVC
      obtain ⟨h, hh⟩ := (isLogMean_iff_mem_meanPairs V.1
        ⟨_, mem_of_isLogMean (logMean_spec V.2)⟩).mp (logMean_spec V.2)
      exact ⟨h, _, ⟨hh, hVC⟩, rfl⟩
    · rintro ⟨h, ⟨V', W⟩, ⟨hp, hWC⟩, hV'⟩
      obtain rfl : V' = V.1 := hV'
      have hm := (isLogMean_iff_mem_meanPairs V.1 W).mpr ⟨h, hp⟩
      have eW : (⟨logMean (specialUnitary : Set ComplexMatrix2) (asMatrices V.1),
          mem_of_isLogMean (logMean_spec V.2)⟩ : specialUnitary) = W :=
        Subtype.ext (ExistsUnique.unique V.2 (logMean_spec V.2) hm)
      rw [eW]
      exact hWC
  rw [e]
  exact measurable_subtype_coe hD
end Matrices.ComplexMatrix2
namespace PeriodicLattice
open Matrices
variable {L m K j : ℕ}
private theorem star_mem_compact {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    star V ∈ compactGaugeGroup :=
  ((⟨V, hV⟩ : ComplexMatrix2.specialUnitary)⁻¹).2
private theorem mem_complex_of_mem_compact {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V ∈ complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hV).2
private theorem gaugeFieldOfGroupValues_of_pos (P : SymmetricBondSet L m K j)
    (v : PositiveBondsOf P → ComplexMatrix2.specialUnitary)
    {b : BondAtLevel L m K j} (hb : b ∈ P.bonds) (hp : b.IsPositivelyOriented) :
    gaugeFieldOfGroupValues P v b = (v ⟨b, hb, hp⟩ : ComplexMatrix2) := by
  unfold gaugeFieldOfGroupValues complexGaugeFieldOfValues
  rw [dif_pos (⟨hb, hp⟩ : b ∈ P.bonds ∧ b.IsPositivelyOriented)]
private theorem gaugeFieldOfGroupValues_of_not_pos (P : SymmetricBondSet L m K j)
    (v : PositiveBondsOf P → ComplexMatrix2.specialUnitary)
    {b : BondAtLevel L m K j} (hb : b ∈ P.bonds) (hp : ¬ b.IsPositivelyOriented) :
    gaugeFieldOfGroupValues P v b =
      star (v ⟨b.opposite, P.opposite_mem b hb, Bond.opposite_isPositivelyOriented hp⟩ :
        ComplexMatrix2) := by
  unfold gaugeFieldOfGroupValues complexGaugeFieldOfValues
  rw [dif_neg (fun h : b ∈ P.bonds ∧ b.IsPositivelyOriented => hp h.2),
    dif_pos (⟨P.opposite_mem b hb, Bond.opposite_isPositivelyOriented hp⟩ :
      b.opposite ∈ P.bonds ∧ b.opposite.IsPositivelyOriented)]
  exact ComplexMatrix2.inv_eq_star_of_mem_specialUnitary (v _).2
private theorem isGaugeField_gaugeFieldOfGroupValues (P : SymmetricBondSet L m K j)
    (hnr : ∀ b : BondAtLevel L m K j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (v : PositiveBondsOf P → ComplexMatrix2.specialUnitary) :
    IsGaugeField compactGaugeGroup P.bonds (gaugeFieldOfGroupValues P v) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · by_cases hp : b.IsPositivelyOriented
    · rw [gaugeFieldOfGroupValues_of_pos P v hb hp]
      exact (v _).2
    · rw [gaugeFieldOfGroupValues_of_not_pos P v hb hp]
      exact star_mem_compact (v _).2
  · by_cases hp : b.IsPositivelyOriented
    · rw [gaugeFieldOfGroupValues_of_not_pos P v (P.opposite_mem b hb) (hnr b hp),
        gaugeFieldOfGroupValues_of_pos P v hb hp,
        ComplexMatrix2.inv_eq_star_of_mem_specialUnitary (v _).2]
      rfl
    · rw [gaugeFieldOfGroupValues_of_pos P v (P.opposite_mem b hb)
        (Bond.opposite_isPositivelyOriented hp), gaugeFieldOfGroupValues_of_not_pos P v hb hp,
        ComplexMatrix2.inv_eq_star_of_mem_specialUnitary (star_mem_compact (v _).2), star_star]
private theorem exists_gaugeFieldOfGroupValues_eq (P : SymmetricBondSet L m K j)
    {V : BondAtLevel L m K j → ComplexMatrix2} (hV : IsGaugeField compactGaugeGroup P.bonds V) :
    ∃ v : PositiveBondsOf P → ComplexMatrix2.specialUnitary,
      ∀ b ∈ P.bonds, gaugeFieldOfGroupValues P v b = V b := by
  refine ⟨fun b => ⟨V b.1, hV.1 b.1 b.2.1⟩, fun b hb => ?_⟩
  by_cases hp : b.IsPositivelyOriented
  · rw [gaugeFieldOfGroupValues_of_pos P _ hb hp]
  · rw [gaugeFieldOfGroupValues_of_not_pos P _ hb hp]
    change star (V b.opposite) = V b
    rw [hV.2 b hb, ComplexMatrix2.inv_eq_star_of_mem_specialUnitary (hV.1 b hb), star_star]
private theorem continuous_gaugeFieldOfGroupValues_apply (P : SymmetricBondSet L m K j)
    {b : BondAtLevel L m K j} (hb : b ∈ P.bonds) :
    Continuous fun v : PositiveBondsOf P → ComplexMatrix2.specialUnitary =>
      gaugeFieldOfGroupValues P v b := by
  by_cases hp : b.IsPositivelyOriented
  · have e : (fun v : PositiveBondsOf P → ComplexMatrix2.specialUnitary =>
        gaugeFieldOfGroupValues P v b) = fun v => (v ⟨b, hb, hp⟩ : ComplexMatrix2) :=
      funext fun v => gaugeFieldOfGroupValues_of_pos P v hb hp
    rw [e]
    exact continuous_subtype_val.comp (continuous_apply _)
  · have e : (fun v : PositiveBondsOf P → ComplexMatrix2.specialUnitary =>
        gaugeFieldOfGroupValues P v b) =
        fun v => star (v ⟨b.opposite, P.opposite_mem b hb,
          Bond.opposite_isPositivelyOriented hp⟩ : ComplexMatrix2) :=
      funext fun v => gaugeFieldOfGroupValues_of_not_pos P v hb hp
    rw [e]
    exact Continuous.matrix_conjTranspose (continuous_subtype_val.comp (continuous_apply _))
private theorem continuous_pathHolonomy (P : SymmetricBondSet L m K j) :
    ∀ Γ : List (BondAtLevel L m K j), (∀ b ∈ Γ, b ∈ P.bonds) →
      Continuous fun v : PositiveBondsOf P → ComplexMatrix2.specialUnitary =>
        pathHolonomy (gaugeFieldOfGroupValues P v) Γ
  | [], _ => by simpa [pathHolonomy] using continuous_const
  | b :: Γ, h => by
    have e : (fun v : PositiveBondsOf P → ComplexMatrix2.specialUnitary =>
        pathHolonomy (gaugeFieldOfGroupValues P v) (b :: Γ)) =
        fun v => gaugeFieldOfGroupValues P v b *
          pathHolonomy (gaugeFieldOfGroupValues P v) Γ := by
      funext v
      simp [pathHolonomy]
    rw [e]
    exact (continuous_gaugeFieldOfGroupValues_apply P (h b (by simp))).mul
      (continuous_pathHolonomy P Γ fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
private theorem pathHolonomy_mem {j : ℤ} {U : Bond L m j → ComplexMatrix2} {Γ : List (Bond L m j)}
    (h : ∀ b ∈ Γ, U b ∈ compactGaugeGroup) : pathHolonomy U Γ ∈ compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p53533 <;> assumption
private theorem pathHolonomy_congr {j : ℤ} {U U' : Bond L m j → ComplexMatrix2}
    {Γ : List (Bond L m j)} (h : ∀ b ∈ Γ, U b = U' b) : pathHolonomy U Γ = pathHolonomy U' Γ := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexAverageLocality.pathHolonomy_congr <;> assumption
private theorem orderedContour_spec (hpaths : BlockPaths.Statement) (hL : Odd L)
    (h13 : 13 ≤ L) (hm : 0 < m) (hk : j < K) (y : SiteAtLevel L m K (j + 1))
    {x : SiteAtLevel L m K j} (hx : x ∈ sitesInBlock (levelDepth K j) y) (σ : AxisOrdering y x) :
    IsBondPathFromTo (orderedContour y x σ) (y.toSublattice (levelDepth K j)) x ∧
      ∀ b ∈ orderedContour y x σ, b ∈ (bondsInside (unitBlock y) : Set (BondAtLevel L m K j)) := by
  obtain ⟨⟨⟨-, himg⟩, -, -⟩, -, hp⟩ := (hpaths L m K hL h13 hm j hk).1 y
  have hxb : (x : FourTorus L m) ∈ (fun p =>
      (offsetSite (y.toSublattice (levelDepth K j)) p : FourTorus L m)) '' blockIndexBox L := by
    rw [himg]
    exact hx
  obtain ⟨p, hpQ, hpx⟩ := hxb
  obtain rfl : offsetSite (y.toSublattice (levelDepth K j)) p = x := Subtype.ext hpx
  have h := (hp p hpQ).1 _ ⟨σ, rfl⟩
  exact ⟨h.1, h.2.2.2.2⟩
private theorem toSublattice_mem_sitesInBlock (hpaths : BlockPaths.Statement) (hL : Odd L)
    (h13 : 13 ≤ L) (hm : 0 < m) (hk : j < K) (y : SiteAtLevel L m K (j + 1)) :
    y.toSublattice (levelDepth K j) ∈ sitesInBlock (levelDepth K j) y := by
  obtain ⟨⟨⟨-, himg⟩, -, -⟩, -, -⟩ := (hpaths L m K hL h13 hm j hk).1 y
  have h0 : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := by
    intro ν
    have : 0 ≤ centreToFaceSteps L := by
      unfold centreToFaceSteps
      omega
    simpa using this
  exact show ((y.toSublattice (levelDepth K j) : SiteAtLevel L m K j) : FourTorus L m) ∈
      unitBlock y from by
    rw [← himg]
    exact ⟨0, h0, by simp [offsetSite]⟩
private def contourFamily {P : SymmetricBondSet L m K j}
    {y : SiteAtLevel L m K (j + 1)} {x : SiteAtLevel L m K j}
    (hmem : ∀ (v : PositiveBondsOf P → ComplexMatrix2.specialUnitary) (σ : AxisOrdering y x),
      pathHolonomy (gaugeFieldOfGroupValues P v) (orderedContour y x σ) ∈ compactGaugeGroup)
    (v : PositiveBondsOf P → ComplexMatrix2.specialUnitary) :
    AxisOrdering y x → ComplexMatrix2.specialUnitary :=
  fun σ => ⟨pathHolonomy (gaugeFieldOfGroupValues P v) (orderedContour y x σ), hmem v σ⟩
theorem meanContourCovarianceStatement_holds
    (hpaths : BlockPaths.Statement)
    (hgauge : GaugeCovarianceOfHolonomy)
    (hmean : ComplexMatrix2.LogMeanCovariance)
    (hexp : ComplexMatrix2.ExpLogEstimates)
    (hfin : BondEndpointsAndFiniteness) :
    MeanContourCovarianceStatement := by
  intro L m K hL h13 hm j hj y x hx P
  have hjm : -(m : ℤ) ≤ levelDepth K j := by
    simp only [levelDepth]
    omega
  have hnr : ∀ b : BondAtLevel L m K j, b.IsPositivelyOriented →
      ¬ b.opposite.IsPositivelyOriented := fun b hb =>
    Bond.opposite_not_isPositivelyOriented (by omega) (by simp only [levelDepth]; omega) hb
  have hin : ∀ (σ : AxisOrdering y x), ∀ b ∈ orderedContour y x σ, b ∈ P.bonds := fun σ b hb =>
    (orderedContour_spec hpaths hL h13 hm hj y hx σ).2 b hb
  have hpath := fun σ : AxisOrdering y x => (orderedContour_spec hpaths hL h13 hm hj y hx σ).1
  have hfinite : Finite (BondAtLevel L m K j) :=
    ((hfin ⟨L, ⟨hL, h13⟩, ⟨K, by omega⟩, ⟨m, hm⟩⟩).1 (levelDepth K j) hjm).2.2.2
  have hmem : ∀ (v : PositiveBondsOf P → ComplexMatrix2.specialUnitary) (σ : AxisOrdering y x),
      pathHolonomy (gaugeFieldOfGroupValues P v) (orderedContour y x σ) ∈ compactGaugeGroup :=
    fun v σ => pathHolonomy_mem fun b hb =>
      (isGaugeField_gaugeFieldOfGroupValues P hnr v).1 b (hin σ b hb)
  have hcont : Continuous (contourFamily hmem) :=
    continuous_pi fun σ => (continuous_pathHolonomy P _ (hin σ)).subtype_mk fun v => hmem v σ
  have hΦ : Measurable (contourFamily hmem) := by
    have : Finite (PositiveBondsOf P) := Subtype.finite
    exact hcont.measurable
  have hset : {v : PositiveBondsOf P → ComplexMatrix2.specialUnitary |
      HasContourMean (gaugeFieldOfGroupValues P v) y x} =
      contourFamily hmem ⁻¹' ComplexMatrix2.uniqueMeanFamilies (AxisOrdering y x) := rfl
  refine ⟨fun Γ hΓ b hb => ?_, ⟨Subtype.finite, fun v =>
    ⟨isGaugeField_gaugeFieldOfGroupValues P hnr v, fun b => ?_⟩,
    fun V hV => exists_gaugeFieldOfGroupValues_eq P hV⟩, fun V hV u hu => ?_, ?_, ?_⟩
  · obtain ⟨σ, rfl⟩ := hΓ
    exact hin σ b hb
  · exact gaugeFieldOfGroupValues_of_pos P v b.2.1 b.2.2
  · classical
    let u' : SiteAtLevel L m K j → ComplexMatrix2 := fun z =>
      if z ∈ sitesInBlock (levelDepth K j) y then u z else 1
    have hu' : IsGaugeMap compactGaugeGroup u' := by
      intro z
      by_cases hz : z ∈ sitesInBlock (levelDepth K j) y
      · simpa [u', hz] using hu z hz
      · simp [u', hz]
    have hy := toSublattice_mem_sitesInBlock hpaths hL h13 hm hj y
    have hVc : IsGaugeField complexGaugeGroup P.bonds V :=
      ⟨fun b hb => mem_complex_of_mem_compact (hV.1 b hb), hV.2⟩
    have hValues : contourHolonomies (gaugeTransform u V) y x = fun σ =>
        u (y.toSublattice (levelDepth K j)) * contourHolonomies V y x σ * (u x)⁻¹ := by
      funext σ
      have e₁ : pathHolonomy (gaugeTransform u V) (orderedContour y x σ) =
          pathHolonomy (gaugeTransform u' V) (orderedContour y x σ) := by
        refine pathHolonomy_congr fun b hb => ?_
        have hb' := hin σ b hb
        simp only [gaugeTransform, u', if_pos hb'.1, if_pos hb'.2]
      have e₂ := (hgauge L m hL h13 hm (levelDepth K j) hjm P.bonds V u' u' P.opposite_mem hVc
        (fun z => mem_complex_of_mem_compact (hu' z))
        (fun z => mem_complex_of_mem_compact (hu' z))).2.1
        _ _ _ (hpath σ) (hin σ)
      simp only [contourHolonomies]
      rw [e₁, e₂]
      simp only [u', if_pos hy, if_pos hx]
    have hVm : ∀ σ, contourHolonomies V y x σ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) :=
      fun σ => pathHolonomy_mem fun b hb => hV.1 b (hin σ b hb)
    have hW : u (y.toSublattice (levelDepth K j)) ∈
        (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := hu _ hy
    have hW' : (u x)⁻¹ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
      rw [ComplexMatrix2.inv_eq_star_of_mem_specialUnitary (hu x hx)]
      exact star_mem_compact (hu x hx)
    have hc := hmean (AxisOrdering y x) (contourHolonomies V y x) _ _ hVm hW hW'
    refine ⟨?_, fun hd => ?_⟩
    · unfold HasContourMean
      rw [hValues]
      exact hc.2.1.symm
    · unfold meanContourHolonomy
      rw [hValues]
      exact hc.2.2 hd
  · rw [hset]
    exact hΦ (ComplexMatrix2.measurableSet_uniqueMeanFamilies hexp)
  · obtain ⟨g, hg, hgv⟩ :=
      ComplexMatrix2.exists_measurable_logMean (ι := AxisOrdering y x) hexp
    refine ⟨fun v => g ⟨contourFamily hmem v.1, v.2⟩, ?_, fun v => hgv _⟩
    exact hg.comp (Measurable.subtype_mk (hΦ.comp measurable_subtype_coe))
end PeriodicLattice
end
end YangMills.Construction
