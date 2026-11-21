import YangMills.Construction.TorusOrFourSpace.CompactnessAndLiftsOfClosedBallsAndOriginBallsProof
import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.DistinctPointsAndProductsOfAdmissibleFamilies
import Mathlib
set_option autoImplicit false
open scoped ENNReal
namespace YangMills.Construction.PeriodicSpace.Kind.AdmissibleProducts
open QuotientCompactC1 (QuotDistIsMetricWithLifts)
variable {P : Params} {K : Kind} {k : ℕ+}
theorem params_side_pos (P : Params) : 0 < P.side := by apply _root_.YangMills.SharedProofs.p25685 <;> assumption
theorem isOpenQ_openBallAt (hmet : QuotDistIsMetricWithLifts P K) (x : K.Pt P) (r : ℝ) :
    IsOpenQ P K (openBallAt P K x r) := by apply _root_.YangMills.DeltaSharedProofs.p501249 <;> assumption
theorem isOpenQ_inter {A B : Set (K.Pt P)} (hA : IsOpenQ P K A) (hB : IsOpenQ P K B) :
    IsOpenQ P K (A ∩ B) := by
  intro u hu
  obtain ⟨r, hr, hAr⟩ := hA u hu.1
  obtain ⟨s, hs, hBs⟩ := hB u hu.2
  exact ⟨min r s, lt_min hr hs, fun v hv =>
    ⟨hAr v (hv.trans_le (min_le_left _ _)), hBs v (hv.trans_le (min_le_right _ _))⟩⟩
theorem setDiam_le_ofReal {A : Set (K.Pt P)} {c : ℝ}
    (h : ∀ u ∈ A, ∀ v ∈ A, quotDist P K u v ≤ c) : setDiam P K A ≤ ENNReal.ofReal c :=
  iSup₂_le fun u hu => iSup₂_le fun v hv => ENNReal.ofReal_le_ofReal (h u hu v hv)
theorem setDiam_mono {A B : Set (K.Pt P)} (h : A ⊆ B) : setDiam P K A ≤ setDiam P K B :=
  iSup₂_le fun u hu => iSup₂_le fun v hv =>
    le_iSup₂_of_le u (h hu) (le_iSup₂_of_le v (h hv) le_rfl)
theorem setInfDist_anti {A A' B B' : Set (K.Pt P)} (h : A ⊆ B) (h' : A' ⊆ B') :
    setInfDist P K B B' ≤ setInfDist P K A A' :=
  le_iInf₂ fun u hu => le_iInf₂ fun v hv =>
    iInf₂_le_of_le u (h hu) (iInf₂_le_of_le v (h' hv) le_rfl)
theorem ofReal_le_setInfDist {A A' : Set (K.Pt P)} {c : ℝ}
    (h : ∀ u ∈ A, ∀ v ∈ A', c ≤ quotDist P K u v) :
    ENNReal.ofReal c ≤ setInfDist P K A A' :=
  le_iInf₂ fun u hu => le_iInf₂ fun v hv => ENNReal.ofReal_le_ofReal (h u hu v hv)
theorem balls_admissibleWith (hmet : QuotDistIsMetricWithLifts P K) {δ η : ℝ} (hδ : 0 < δ)
    (hη : 0 < η) (hηδ : η ≤ δ / 3) (hside : 2 * η < P.side / 4) (x : K.Tuple P k)
    (hx : ∀ i j, i ≠ j → δ ≤ quotDist P K (x i) (x j)) :
    AdmissibleWith P K η (δ / 3) fun i => openBallAt P K (x i) η := by
  have hdiam : ∀ i, setDiam P K (openBallAt P K (x i) η) ≤ ENNReal.ofReal (2 * η) := by
    intro i
    refine setDiam_le_ofReal fun u hu v hv => ?_
    have hu' : quotDist P K u (x i) < η := hu
    have hv' : quotDist P K v (x i) < η := hv
    have e1 := hmet.2.2.2.1 u (x i) v
    have e2 := hmet.2.2.1 (x i) v
    linarith
  refine ⟨hη, by positivity, fun i => isOpenQ_openBallAt hmet _ _, hdiam, fun _ i => ?_,
    fun i j hij => ofReal_le_setInfDist fun u hu v hv => ?_⟩
  · have hq : 0 < P.side / 4 := by have := params_side_pos P; positivity
    exact (hdiam i).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hq).2 hside)
  · have hu' : quotDist P K u (x i) < η := hu
    have hv' : quotDist P K v (x j) < η := hv
    have e1 := hmet.2.2.2.1 (x i) u (x j)
    have e2 := hmet.2.2.2.1 u v (x j)
    have e3 := hmet.2.2.1 (x i) u
    have e5 := hx i j hij
    linarith
theorem exists_small_radius (P : Params) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ / 3 ∧ 2 * η < P.side / 4 := by
  have hs := params_side_pos P
  refine ⟨min (δ / 3) (P.side / 16), lt_min (by positivity) (by positivity), min_le_left _ _, ?_⟩
  have := min_le_right (δ / 3) (P.side / 16)
  linarith
theorem boxSet_subset_pairwiseDistinct (hmet : QuotDistIsMetricWithLifts P K)
    {U : Fin (k : ℕ) → Set (K.Pt P)} (hU : Admissible P K U) :
    Tuple.boxSet P K U ⊆ pairwiseDistinct P K k := by
  intro x hx
  have hx' : ∀ i, x i ∈ U i := hx
  show Function.Injective x
  intro i j heq
  by_contra hij
  obtain ⟨R, d, h⟩ := hU
  have e1 := h.sep_le_setInfDist i j hij
  have e2 : setInfDist P K (U i) (U j) ≤ ENNReal.ofReal (quotDist P K (x i) (x j)) :=
    iInf₂_le_of_le _ (hx' i) (iInf₂_le_of_le _ (hx' j) le_rfl)
  have e3 : quotDist P K (x i) (x j) = 0 := (hmet.2.1 _ _).2 heq
  rw [e3, ENNReal.ofReal_zero] at e2
  exact absurd (e1.trans e2) (not_le.2 (ENNReal.ofReal_pos.2 h.sep_pos))
theorem exists_uniform_separation (hmet : QuotDistIsMetricWithLifts P K) {x : K.Tuple P k}
    (hx : Function.Injective x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j, i ≠ j → δ ≤ quotDist P K (x i) (x j) := by
  classical
  let pairs : Finset (Fin (k : ℕ) × Fin (k : ℕ)) := Finset.univ.filter fun q => q.1 ≠ q.2
  by_cases hne : pairs.Nonempty
  · obtain ⟨q, hq, hmin⟩ := pairs.exists_min_image (fun q => quotDist P K (x q.1) (x q.2)) hne
    refine ⟨quotDist P K (x q.1) (x q.2), lt_of_le_of_ne (hmet.1 _ _) fun h0 => ?_,
      fun i j h => hmin (i, j) (by simp [pairs, h])⟩
    exact (Finset.mem_filter.1 hq).2 (hx ((hmet.2.1 _ _).1 h0.symm))
  · exact ⟨1, one_pos, fun i j h => (hne ⟨(i, j), by simp [pairs, h]⟩).elim⟩
theorem exists_admissible_of_mem (hmet : QuotDistIsMetricWithLifts P K) {x : K.Tuple P k}
    (hx : x ∈ pairwiseDistinct P K k) :
    ∃ U : Fin (k : ℕ) → Set (K.Pt P),
      Admissible P K U ∧ x ∈ Tuple.boxSet P K U := by
  obtain ⟨δ, hδ, hsep⟩ := exists_uniform_separation hmet hx
  obtain ⟨η, hη, hηδ, hside⟩ := exists_small_radius P hδ
  refine ⟨fun i => openBallAt P K (x i) η,
    ⟨η, δ / 3, balls_admissibleWith hmet hδ hη hηδ hside x hsep⟩, fun i => ?_⟩
  show quotDist P K (x i) (x i) < η
  rw [(hmet.2.1 _ _).2 rfl]
  exact hη
theorem memberInter_admissibleWith {R d : ℝ}
    {U V : Fin (k : ℕ) → Set (K.Pt P)} (h : AdmissibleWith P K R d U)
    (hV : Admissible P K V) :
    AdmissibleWith P K R d (memberInter P K U V) := by
  obtain ⟨R', d', h'⟩ := hV
  have hsub : ∀ i, memberInter P K U V i ⊆ U i := fun i => Set.inter_subset_left
  exact
    { radius_pos := h.radius_pos
      sep_pos := h.sep_pos
      isOpen_mem := fun i => isOpenQ_inter (h.isOpen_mem i) (h'.isOpen_mem i)
      diam_le := fun i => (setDiam_mono (hsub i)).trans (h.diam_le i)
      diam_lt_quarter_of_torus := fun ht i =>
        (setDiam_mono (hsub i)).trans_lt (h.diam_lt_quarter_of_torus ht i)
      sep_le_setInfDist := fun i j hij =>
        (h.sep_le_setInfDist i j hij).trans (setInfDist_anti (hsub i) (hsub j)) }
theorem boxSet_memberInter (U V : Fin (k : ℕ) → Set (K.Pt P)) :
    Tuple.boxSet P K (memberInter P K U V) =
      Tuple.boxSet P K U ∩ Tuple.boxSet P K V := by
  ext x
  exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩
theorem admissibleProductFacts_of (hquot : QuotientCompactC1.Claim)
    (htup : TupleFacts.AllFacts) :
    AdmissibleProductFacts := by
  intro P K k
  have hmet : QuotDistIsMetricWithLifts P K := (hquot P K).1
  have hopen : ∀ U : Fin (k : ℕ) → Set (K.Pt P), Admissible P K U →
      Tuple.IsOpenT P K (Tuple.boxSet P K U) := by
    rintro U ⟨R, d, h⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbox, -⟩ := htup P K k
    exact (hbox U).1 h.isOpen_mem
  refine ⟨?_, fun U hU => ⟨hopen U hU, boxSet_subset_pairwiseDistinct hmet hU⟩, ?_,
    fun x hx => exists_admissible_of_mem hmet hx, fun R d U V h hV =>
      ⟨memberInter_admissibleWith h hV, boxSet_memberInter U V⟩⟩
  · intro x hx
    obtain ⟨U, hU, hxU⟩ := exists_admissible_of_mem hmet hx
    obtain ⟨r, hr, hball⟩ := hopen U hU x hxU
    exact ⟨r, hr, fun z hz => boxSet_subset_pairwiseDistinct hmet hU (hball z hz)⟩
  · intro δ hδ
    obtain ⟨η, hη, hηδ, hside⟩ := exists_small_radius P hδ
    exact ⟨η, hη, fun x hx => balls_admissibleWith hmet hδ hη hηδ hside x hx⟩
end YangMills.Construction.PeriodicSpace.Kind.AdmissibleProducts
