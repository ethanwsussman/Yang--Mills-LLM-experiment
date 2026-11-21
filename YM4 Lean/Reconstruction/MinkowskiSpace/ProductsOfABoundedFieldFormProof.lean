import Reconstruction.MinkowskiSpace.AcrossTheSpacelikePointsProof
import Reconstruction.MinkowskiSpace.MatrixElementsOfTheFieldVectorsOnTheTubeProof
import Reconstruction.MinkowskiSpace.TranslationOperatorsOfABoundedFieldFormProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.FieldForms
namespace FieldProductProof
open MinkowskiSpace OneLoopNotation ComplexHilbert HilbertToolkit ProjectionMeasures PVMCalculus
  WightmanTheory Coordinates
open FieldFormTranslations (IsContractionSemigroup LipschitzInTube HolomorphicMatrixCoeffs
  ImInClosedCone complexEucNorm)
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem imPart_imagTimeShift (a : ℝ) :
    MinkowskiSpace.imPart (imagTimeShift a) = a • timeUnit := by
  funext μ
  simp [MinkowskiSpace.imPart, imagTimeShift, toComplex]
theorem spacePart_timeUnit : spacePart timeUnit = 0 := by apply _root_.YangMills.Construction.MinkowskiSpace.ConeTubeLorentz.spacePart_timeUnit <;> assumption
theorem timeUnit_zero : timeUnit 0 = 1 := by
  simp [timeUnit, mkTimeSpace]
theorem spaceNorm_zero : spaceNorm (0 : Fin 3 → ℝ) = 0 := by
  simp [spaceNorm]
theorem tubeGap_sub_imagTimeShift (ζ : ComplexVec4) (a : ℝ) :
    tubeGap (ζ - imagTimeShift a) = tubeGap ζ - a := by
  have h : MinkowskiSpace.imPart (ζ - imagTimeShift a) =
      MinkowskiSpace.imPart ζ - a • timeUnit := by
    rw [← imPart_imagTimeShift]
    funext μ
    simp [MinkowskiSpace.imPart]
  have hs : spacePart (MinkowskiSpace.imPart ζ - a • timeUnit) =
      spacePart (MinkowskiSpace.imPart ζ) := by
    funext i
    have := congrFun spacePart_timeUnit i
    simp only [spacePart, Pi.zero_apply] at this
    simp [spacePart, this]
  unfold tubeGap coneGap
  rw [h, hs]
  simp [timeUnit_zero]
  ring
theorem tubeGap_imagTimeShift (a : ℝ) : tubeGap (imagTimeShift a) = a := by
  unfold tubeGap coneGap
  rw [imPart_imagTimeShift]
  have hs : spacePart (a • timeUnit) = 0 := by
    funext i
    have := congrFun spacePart_timeUnit i
    simp only [spacePart, Pi.zero_apply] at this
    simp [spacePart, this]
  rw [hs, spaceNorm_zero]
  simp [timeUnit_zero]
theorem imagTimeShift_add (a b : ℝ) :
    imagTimeShift (a + b) = imagTimeShift a + imagTimeShift b := by
  funext μ
  simp [imagTimeShift, toComplex, add_smul, mul_add]
theorem imPart_neg_conjPoint (ζ : ComplexVec4) :
    MinkowskiSpace.imPart (-MinkowskiSpace.conjPoint ζ) = MinkowskiSpace.imPart ζ := by
  funext μ
  simp [MinkowskiSpace.imPart, MinkowskiSpace.conjPoint, toComplex, MinkowskiSpace.rePart]
theorem tubeGap_neg_conjPoint (ζ : ComplexVec4) :
    tubeGap (-MinkowskiSpace.conjPoint ζ) = tubeGap ζ := by
  unfold tubeGap
  rw [imPart_neg_conjPoint]
theorem neg_conjPoint_sub_imagTimeShift (ζ : ComplexVec4) (a : ℝ) :
    -MinkowskiSpace.conjPoint (ζ - imagTimeShift a) =
      -MinkowskiSpace.conjPoint ζ - imagTimeShift a := by
  funext μ
  apply Complex.ext <;>
    simp [MinkowskiSpace.conjPoint, toComplex, MinkowskiSpace.rePart, MinkowskiSpace.imPart,
      imagTimeShift]
theorem neg_conjPoint_imagTimeShift (a : ℝ) :
    -MinkowskiSpace.conjPoint (imagTimeShift a) = imagTimeShift a := by
  funext μ
  apply Complex.ext <;>
    simp [MinkowskiSpace.conjPoint, toComplex, MinkowskiSpace.rePart, MinkowskiSpace.imPart,
      imagTimeShift]
structure Hyps (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K)
    (℘ C : ℝ) : Prop where
  bdd : IsBoundedFieldForm E Ω A ℘ C
  semigroup : IsContractionSemigroup E Ω
  lip : LipschitzInTube E
  holo : HolomorphicMatrixCoeffs E
  coneGap_add : ∀ y y' : RealVec4, coneGap (y + y') ≥ coneGap y + coneGap y'
  tubeTuples_convex : ∀ b : ℕ, Convex ℝ (tubeTuples b)
  powerSeries : ComplexCoordinates.PowerSeriesHolomorphy.Properties
variable {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K} {℘ C : ℝ}
theorem Hyps.spectralTranslation_mul (h : Hyps E Ω A ℘ C) {ζ ζ' : ComplexVec4}
    (hζ : 0 ≤ tubeGap ζ) (hζ' : 0 ≤ tubeGap ζ') :
    spectralTranslation E ζ * spectralTranslation E ζ' = spectralTranslation E (ζ + ζ') :=
  (h.semigroup.1 ζ ζ' hζ hζ').2.1
theorem Hyps.norm_spectralTranslation_le (h : Hyps E Ω A ℘ C) {ζ : ComplexVec4}
    (hζ : 0 ≤ tubeGap ζ) : ‖spectralTranslation E ζ‖ ≤ 1 :=
  (h.semigroup.1 ζ ζ hζ hζ).1
theorem Hyps.adjointOp_spectralTranslation (h : Hyps E Ω A ℘ C) {ζ : ComplexVec4}
    (hζ : 0 ≤ tubeGap ζ) :
    adjointOp (spectralTranslation E ζ) = spectralTranslation E (-MinkowskiSpace.conjPoint ζ) :=
  (h.semigroup.1 ζ ζ hζ hζ).2.2.1
theorem Hyps.spectralTranslation_vacuum (h : Hyps E Ω A ℘ C) {ζ : ComplexVec4}
    (hζ : 0 ≤ tubeGap ζ) : spectralTranslation E ζ Ω = Ω :=
  (h.semigroup.1 ζ ζ hζ hζ).2.2.2.2
theorem Hyps.tubeGap_add (h : Hyps E Ω A ℘ C) (ζ ζ' : ComplexVec4) :
    tubeGap (ζ + ζ') ≥ tubeGap ζ + tubeGap ζ' := by
  have := h.coneGap_add (MinkowskiSpace.imPart ζ) (MinkowskiSpace.imPart ζ')
  have he : MinkowskiSpace.imPart (ζ + ζ') =
      MinkowskiSpace.imPart ζ + MinkowskiSpace.imPart ζ' := by
    funext μ
    simp [MinkowskiSpace.imPart]
  unfold tubeGap
  rw [he]
  exact this
def midProd (E : FourBorelSet → BddOp K) (A : ℝ → BddOp K) (s : ℝ)
    (l : List ComplexVec4) : BddOp K :=
  (l.map fun m => spectralTranslation E (m - imagTimeShift (2 * s)) * A s).prod
def chainProd (E : FourBorelSet → BddOp K) (A : ℝ → BddOp K) (s : ℝ)
    (a : ComplexVec4) (l : List ComplexVec4) (b : ComplexVec4) : BddOp K :=
  spectralTranslation E (a - imagTimeShift s) * A s * midProd E A s l *
    spectralTranslation E (b - imagTimeShift s)
theorem midProd_nil (s : ℝ) : midProd E A s [] = 1 := rfl
theorem midProd_cons (s : ℝ) (m : ComplexVec4) (l : List ComplexVec4) :
    midProd E A s (m :: l) =
      spectralTranslation E (m - imagTimeShift (2 * s)) * A s * midProd E A s l := by
  simp [midProd]
theorem midProd_append (s : ℝ) (l l' : List ComplexVec4) :
    midProd E A s (l ++ l') = midProd E A s l * midProd E A s l' := by
  simp [midProd]
def GapFits (s : ℝ) (a : ComplexVec4) (l : List ComplexVec4) (b : ComplexVec4) : Prop :=
  0 < s ∧ s ≤ tubeGap a ∧ s ≤ tubeGap b ∧ ∀ m ∈ l, 2 * s ≤ tubeGap m
theorem Hyps.chainTail_eq_of_lt (h : Hyps E Ω A ℘ C) {s s' : ℝ} (hs' : 0 < s') (hlt : s' < s)
    (b : ComplexVec4) (hb : s ≤ tubeGap b) (l : List ComplexVec4)
    (hl : ∀ m ∈ l, 2 * s ≤ tubeGap m) :
    A s * midProd E A s l * spectralTranslation E (b - imagTimeShift s) =
      spectralTranslation E (imagTimeShift (s - s')) * A s' * midProd E A s' l *
        spectralTranslation E (b - imagTimeShift s') := by
  have hc : 0 < s - s' := sub_pos.2 hlt
  have hA : A s = spectralTranslation E (imagTimeShift (s - s')) * A s' *
      spectralTranslation E (imagTimeShift (s - s')) := by
    have := h.bdd.shift_conj s' (s - s') hs' hc
    rw [this]
    congr 1
    ring
  have ht : 0 ≤ tubeGap (imagTimeShift (s - s')) := by
    rw [tubeGap_imagTimeShift]
    exact hc.le
  induction l with
  | nil =>
    have hT : spectralTranslation E (imagTimeShift (s - s')) *
        spectralTranslation E (b - imagTimeShift s) =
        spectralTranslation E (b - imagTimeShift s') := by
      rw [h.spectralTranslation_mul ht (by rw [tubeGap_sub_imagTimeShift]; linarith)]
      congr 1
      have : imagTimeShift s = imagTimeShift (s - s') + imagTimeShift s' := by
        rw [← imagTimeShift_add]
        congr 1
        ring
      rw [this]
      abel
    simp only [midProd_nil, mul_one]
    rw [← hT]
    nth_rewrite 1 [hA]
    simp only [mul_assoc]
  | cons m l ih =>
    have ih' := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hm := hl m List.mem_cons_self
    have hT : spectralTranslation E (imagTimeShift (s - s')) *
        (spectralTranslation E (m - imagTimeShift (2 * s)) *
          spectralTranslation E (imagTimeShift (s - s'))) =
        spectralTranslation E (m - imagTimeShift (2 * s')) := by
      rw [h.spectralTranslation_mul (by rw [tubeGap_sub_imagTimeShift]; linarith) ht,
        h.spectralTranslation_mul ht (by
          have := h.tubeGap_add (m - imagTimeShift (2 * s))
            (imagTimeShift (s - s'))
          rw [tubeGap_sub_imagTimeShift, tubeGap_imagTimeShift] at this
          linarith)]
      congr 1
      have : imagTimeShift (2 * s) = imagTimeShift (s - s') +
          imagTimeShift (s - s') + imagTimeShift (2 * s') := by
        rw [← imagTimeShift_add, ← imagTimeShift_add]
        congr 1
        ring
      rw [this]
      abel
    rw [midProd_cons, midProd_cons]
    calc A s * (spectralTranslation E (m - imagTimeShift (2 * s)) * A s *
            midProd E A s l) * spectralTranslation E (b - imagTimeShift s)
        = A s * spectralTranslation E (m - imagTimeShift (2 * s)) *
            (A s * midProd E A s l * spectralTranslation E (b - imagTimeShift s)) := by
          simp only [mul_assoc]
      _ = _ := by
          rw [ih']
          nth_rewrite 1 [hA]
          rw [← hT]
          simp only [mul_assoc]
theorem Hyps.chainProd_eq_of_lt (h : Hyps E Ω A ℘ C) {s s' : ℝ} (hs' : 0 < s') (hlt : s' < s)
    {a b : ComplexVec4} {l : List ComplexVec4} (hf : GapFits s a l b) :
    chainProd E A s a l b = chainProd E A s' a l b := by
  obtain ⟨_, ha, hb, hl⟩ := hf
  have hc : 0 < s - s' := sub_pos.2 hlt
  have ht : 0 ≤ tubeGap (imagTimeShift (s - s')) := by
    rw [tubeGap_imagTimeShift]
    exact hc.le
  have hT : spectralTranslation E (a - imagTimeShift s) *
      spectralTranslation E (imagTimeShift (s - s')) =
      spectralTranslation E (a - imagTimeShift s') := by
    rw [h.spectralTranslation_mul (by rw [tubeGap_sub_imagTimeShift]; linarith) ht]
    congr 1
    have : imagTimeShift s = imagTimeShift (s - s') + imagTimeShift s' := by
      rw [← imagTimeShift_add]
      congr 1
      ring
    rw [this]
    abel
  have := h.chainTail_eq_of_lt hs' hlt b hb l hl
  unfold chainProd
  calc _ = spectralTranslation E (a - imagTimeShift s) *
        (A s * midProd E A s l * spectralTranslation E (b - imagTimeShift s)) := by
        simp only [mul_assoc]
    _ = _ := by
        rw [this, ← hT]
        simp only [mul_assoc]
theorem Hyps.chainProd_indep (h : Hyps E Ω A ℘ C) {s s' : ℝ} {a b : ComplexVec4}
    {l : List ComplexVec4} (hf : GapFits s a l b) (hf' : GapFits s' a l b) :
    chainProd E A s a l b = chainProd E A s' a l b := by
  rcases lt_trichotomy s s' with hlt | rfl | hlt
  · exact (h.chainProd_eq_of_lt hf.1 hlt hf').symm
  · rfl
  · exact h.chainProd_eq_of_lt hf'.1 hlt hf
theorem ofFn_snocPoint {n : ℕ} (ζ : Fin n → ComplexVec4) (ω : ComplexVec4) :
    List.ofFn (snocPoint ζ ω) = List.ofFn ζ ++ [ω] := by
  unfold snocPoint
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]
theorem ofFn_consPoint {n : ℕ} (ω : ComplexVec4) (ζ : Fin n → ComplexVec4) :
    List.ofFn (consPoint ω ζ) = ω :: List.ofFn ζ := by
  simp [consPoint, List.ofFn_succ]
theorem ofFn_eq_ends {n : ℕ} (ζ : Fin (n + 2) → ComplexVec4) :
    List.ofFn ζ = ζ 0 :: ((List.ofFn fun k : Fin n => ζ k.castSucc.succ) ++
      [ζ (Fin.last (n + 1))]) := by
  rw [List.ofFn_succ, List.ofFn_succ']
  simp [List.concat_eq_append]
theorem ofFn_joinAt {n n' : ℕ} (ζ : Fin n → ComplexVec4) (β : ComplexVec4)
    (ζ' : Fin n' → ComplexVec4) :
    List.ofFn (joinAt ζ β ζ') = List.ofFn ζ ++ β :: List.ofFn ζ' := by
  have h : n + n' + 1 = n + 1 + n' := by omega
  unfold joinAt
  rw [List.ofFn_congr h]
  have : (fun i : Fin (n + 1 + n') => Fin.append (snocPoint ζ β) ζ'
      (Fin.cast (by omega) (Fin.cast h.symm i))) = Fin.append (snocPoint ζ β) ζ' := by
    funext i
    rfl
  rw [this, List.ofFn_fin_append, ofFn_snocPoint]
  simp
theorem mem_ofFn_apply {m : ℕ} (ζ : Fin m → ComplexVec4) (k : Fin m) : ζ k ∈ List.ofFn ζ :=
  List.mem_ofFn.2 ⟨k, rfl⟩
def reflectList (l : List ComplexVec4) : List ComplexVec4 :=
  (l.map fun m => -MinkowskiSpace.conjPoint m).reverse
theorem ofFn_reflectTuple {m : ℕ} (ζ : Fin m → ComplexVec4) :
    List.ofFn (reflectTuple ζ) = reflectList (List.ofFn ζ) := by
  apply List.ext_getElem
  · simp [reflectList]
  · intro i h₁ h₂
    simp only [List.length_ofFn] at h₁
    simp only [reflectList, List.getElem_ofFn, List.getElem_reverse, List.getElem_map,
      reflectTuple]
    congr 3
    simp [Fin.rev]
    omega
theorem fieldProductAt_eq_chainProd {n : ℕ} {ζ : Fin (n + 2) → ComplexVec4} {a b : ComplexVec4}
    {l : List ComplexVec4} (hl : List.ofFn ζ = a :: (l ++ [b])) (s : ℝ) :
    fieldProductAt E A s ζ = chainProd E A s a l b := by
  rw [ofFn_eq_ends] at hl
  obtain ⟨h₀, h₁⟩ := List.cons.inj hl
  obtain ⟨h₂, hb⟩ := List.append_inj' h₁ rfl
  obtain h₃ := (List.cons.inj hb).1
  subst h₀ h₂ h₃
  unfold fieldProductAt chainProd midProd
  rw [List.map_ofFn]
  rfl
theorem gapFits_of_isAdmissibleGap {n : ℕ} {ζ : Fin (n + 2) → ComplexVec4} {a b : ComplexVec4}
    {l : List ComplexVec4} (hl : List.ofFn ζ = a :: (l ++ [b])) {s : ℝ}
    (hm : IsAdmissibleGap ζ s) : GapFits s a l b := by
  rw [ofFn_eq_ends] at hl
  obtain ⟨h₀, h₁⟩ := List.cons.inj hl
  obtain ⟨h₂, hb⟩ := List.append_inj' h₁ rfl
  obtain h₃ := (List.cons.inj hb).1
  subst h₀ h₂ h₃
  refine ⟨hm.1, hm.2.1, hm.2.2.1, fun m hm' => ?_⟩
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hm'
  exact hm.2.2.2 k
theorem isAdmissibleGap_halfMin {n : ℕ} {ζ : Fin (n + 2) → ComplexVec4}
    (hζ : ζ ∈ tubeTuples (n + 2)) : IsAdmissibleGap ζ (halfMinTubeGap ζ) := by
  have hpos : ∀ k, 0 < tubeGap (ζ k) := fun k => hζ k (Set.mem_univ k)
  have hmin : 0 < Finset.univ.inf' Finset.univ_nonempty fun k => tubeGap (ζ k) :=
    (Finset.lt_inf'_iff _).2 fun k _ => hpos k
  have hle : ∀ k, (Finset.univ.inf' Finset.univ_nonempty fun k => tubeGap (ζ k)) ≤
      tubeGap (ζ k) := fun k => Finset.inf'_le _ (Finset.mem_univ k)
  unfold IsAdmissibleGap halfMinTubeGap
  refine ⟨by positivity, ?_, ?_, fun k => ?_⟩
  · linarith [hle 0]
  · linarith [hle (Fin.last (n + 1))]
  · linarith [hle k.castSucc.succ]
theorem mem_tubeTuples_of_gapFits {n : ℕ} {ζ : Fin (n + 2) → ComplexVec4} {a b : ComplexVec4}
    {l : List ComplexVec4} (hl : List.ofFn ζ = a :: (l ++ [b])) {s : ℝ} (hf : GapFits s a l b) :
    ζ ∈ tubeTuples (n + 2) := by
  intro k _
  have hk : ζ k ∈ List.ofFn ζ := mem_ofFn_apply ζ k
  rw [hl] at hk
  obtain ⟨hs, ha, hb, hm⟩ := hf
  change 0 < tubeGap (ζ k)
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hk
  rcases hk with h | h | h
  · rw [h]; linarith
  · linarith [hm _ h]
  · rw [h]; linarith
theorem Hyps.fieldProduct_eq_chainProd (h : Hyps E Ω A ℘ C) {n : ℕ}
    {ζ : Fin (n + 2) → ComplexVec4} {a b : ComplexVec4} {l : List ComplexVec4}
    (hl : List.ofFn ζ = a :: (l ++ [b])) {s : ℝ}
    (hf : GapFits s a l b) : fieldProduct E A (n + 1) ζ = chainProd E A s a l b := by
  rw [fieldProduct_succ_eq, fieldProductAt_eq_chainProd hl]
  exact h.chainProd_indep
    (gapFits_of_isAdmissibleGap hl (isAdmissibleGap_halfMin (mem_tubeTuples_of_gapFits hl hf))) hf
theorem fieldProduct_zero_eq {ζ : Fin 1 → ComplexVec4} {v : ComplexVec4}
    (hl : List.ofFn ζ = [v]) : fieldProduct E A 0 ζ = spectralTranslation E v := by
  have : ζ 0 = v := by simpa [List.ofFn_succ] using hl
  rw [← this]
  rfl
theorem exists_gap_le (L : List ComplexVec4) (hL : ∀ x ∈ L, x ∈ futureTube) :
    ∃ s : ℝ, 0 < s ∧ ∀ x ∈ L, 2 * s ≤ tubeGap x := by
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons x L ih =>
    obtain ⟨s, hs, hx⟩ := ih fun y hy => hL y (List.mem_cons_of_mem _ hy)
    have hpos : 0 < tubeGap x := hL x List.mem_cons_self
    refine ⟨min s (tubeGap x / 2), lt_min hs (by positivity), fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · linarith [min_le_right s (tubeGap y / 2)]
    · linarith [min_le_left s (tubeGap x / 2), hx y hy]
theorem gapFits_of_le {s : ℝ} (hs : 0 < s) {a b : ComplexVec4} {l : List ComplexVec4}
    (ha : 2 * s ≤ tubeGap a) (hb : 2 * s ≤ tubeGap b) (hl : ∀ m ∈ l, 2 * s ≤ tubeGap m) :
    GapFits s a l b :=
  ⟨hs, by linarith, by linarith, hl⟩
theorem mem_futureTube_of_mem_ofFn {m : ℕ} {ζ : Fin m → ComplexVec4} (hζ : ζ ∈ tubeTuples m) :
    ∀ x ∈ List.ofFn ζ, x ∈ futureTube := by
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  exact hζ k (Set.mem_univ k)
theorem Hyps.fieldProductIndepOfGap (h : Hyps E Ω A ℘ C) :
    FieldProductIndepOfGap E A := by
  intro n ζ _ s s' hs hs'
  rw [fieldProductAt_eq_chainProd (ofFn_eq_ends ζ), fieldProductAt_eq_chainProd (ofFn_eq_ends ζ)]
  exact h.chainProd_indep (gapFits_of_isAdmissibleGap (ofFn_eq_ends ζ) hs)
    (gapFits_of_isAdmissibleGap (ofFn_eq_ends ζ) hs')
theorem Hyps.mul_chainProd (h : Hyps E Ω A ℘ C) {s : ℝ} {a b ω : ComplexVec4}
    {l : List ComplexVec4} (ha : s ≤ tubeGap a) (hω : 0 ≤ tubeGap ω) :
    spectralTranslation E ω * chainProd E A s a l b = chainProd E A s (a + ω) l b := by
  have hT : spectralTranslation E ω * spectralTranslation E (a - imagTimeShift s) =
      spectralTranslation E (a + ω - imagTimeShift s) := by
    rw [h.spectralTranslation_mul hω (by rw [tubeGap_sub_imagTimeShift]; linarith)]
    congr 1
    abel
  unfold chainProd
  rw [← hT]
  simp only [mul_assoc]
theorem Hyps.chainProd_mul (h : Hyps E Ω A ℘ C) {s : ℝ} {a b ω : ComplexVec4}
    {l : List ComplexVec4} (hb : s ≤ tubeGap b) (hω : 0 ≤ tubeGap ω) :
    chainProd E A s a l b * spectralTranslation E ω = chainProd E A s a l (b + ω) := by
  have hT : spectralTranslation E (b - imagTimeShift s) * spectralTranslation E ω =
      spectralTranslation E (b + ω - imagTimeShift s) := by
    rw [h.spectralTranslation_mul (by rw [tubeGap_sub_imagTimeShift]; linarith) hω]
    congr 1
    abel
  unfold chainProd
  rw [← hT]
  simp only [mul_assoc]
theorem Hyps.gapFits_add_ends (h : Hyps E Ω A ℘ C) {s : ℝ} {a b ω ω' : ComplexVec4}
    {l : List ComplexVec4} (hf : GapFits s a l b) (hω : 0 ≤ tubeGap ω)
    (hω' : 0 ≤ tubeGap ω') : GapFits s (a + ω) l (b + ω') := by
  obtain ⟨hs, ha, hb, hl⟩ := hf
  exact ⟨hs, by linarith [h.tubeGap_add a ω], by linarith [h.tubeGap_add b ω'], hl⟩
theorem Hyps.fieldProductTranslateEnds (h : Hyps E Ω A ℘ C) : FieldProductTranslateEnds E A := by
  intro n a b ζ ha hζ hb ω ω' hω hω'
  obtain ⟨s, hs, hsm⟩ := exists_gap_le (a :: b :: List.ofFn ζ) (by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact ha
    · exact hb
    · exact mem_futureTube_of_mem_ofFn hζ x hx)
  have hf : GapFits s a (List.ofFn ζ) b :=
    gapFits_of_le hs (hsm a (by simp)) (hsm b (by simp)) fun m hm => hsm m (by simp [hm])
  have hl : ∀ a' b', List.ofFn (consPoint a' (snocPoint ζ b')) =
      a' :: (List.ofFn ζ ++ [b']) := fun a' b' => by
    rw [ofFn_consPoint, ofFn_snocPoint]
  have hω₀ : 0 ≤ tubeGap ω := hω
  have hω₀' : 0 ≤ tubeGap ω' := hω'
  rw [h.fieldProduct_eq_chainProd (hl a b) hf,
    h.fieldProduct_eq_chainProd (hl _ _) (h.gapFits_add_ends hf hω₀ hω₀'),
    h.mul_chainProd hf.2.1 hω₀, h.chainProd_mul hf.2.2.1 hω₀']
theorem Hyps.chainProd_mul_chainProd (h : Hyps E Ω A ℘ C) {s : ℝ} {a b α α' : ComplexVec4}
    {l l' : List ComplexVec4} (hα : s ≤ tubeGap α) (hα' : s ≤ tubeGap α') :
    chainProd E A s a l α * chainProd E A s α' l' b =
      chainProd E A s a (l ++ (α + α') :: l') b := by
  have hT : spectralTranslation E (α - imagTimeShift s) *
      spectralTranslation E (α' - imagTimeShift s) =
      spectralTranslation E (α + α' - imagTimeShift (2 * s)) := by
    rw [h.spectralTranslation_mul (by rw [tubeGap_sub_imagTimeShift]; linarith)
      (by rw [tubeGap_sub_imagTimeShift]; linarith)]
    congr 1
    rw [two_mul, imagTimeShift_add]
    abel
  unfold chainProd
  rw [midProd_append, midProd_cons, ← hT]
  simp only [mul_assoc]
theorem Hyps.fieldProductMulJoin (h : Hyps E Ω A ℘ C) : FieldProductMulJoin E A := by
  intro n n' ζ α α' ζ' hζ hα hα' hζ'
  have hα₀ : 0 < tubeGap α := hα
  have hα₀' : 0 < tubeGap α' := hα'
  obtain ⟨s, hs, hsm⟩ := exists_gap_le (α :: α' :: (List.ofFn ζ ++ List.ofFn ζ')) (by
    intro x hx
    simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | rfl | hx | hx
    · exact hα
    · exact hα'
    · exact mem_futureTube_of_mem_ofFn hζ x hx
    · exact mem_futureTube_of_mem_ofFn hζ' x hx)
  have hαs := hsm α (by simp)
  have hαs' := hsm α' (by simp)
  have hζs : ∀ x ∈ List.ofFn ζ, 2 * s ≤ tubeGap x := fun x hx => hsm x (by simp [hx])
  have hζs' : ∀ x ∈ List.ofFn ζ', 2 * s ≤ tubeGap x := fun x hx => hsm x (by simp [hx])
  have hadd : 2 * s ≤ tubeGap (α + α') := by
    linarith [h.tubeGap_add α α']
  have hl₁ := ofFn_snocPoint ζ α
  have hl₂ := ofFn_consPoint α' ζ'
  have hl₃ := ofFn_joinAt ζ (α + α') ζ'
  cases n with
  | zero =>
    cases n' with
    | zero =>
      have e₁ : List.ofFn ζ = [] := by simp
      have e₂ : List.ofFn ζ' = [] := by simp
      rw [e₁] at hl₁ hl₃
      rw [e₂] at hl₂ hl₃
      rw [fieldProduct_zero_eq hl₁, fieldProduct_zero_eq hl₂]
      have := fieldProduct_zero_eq (E := E) (A := A) (ζ := joinAt ζ (α + α') ζ') hl₃
      exact (h.spectralTranslation_mul (le_of_lt hα) (le_of_lt hα')).trans this.symm
    | succ q =>
      have e₁ : List.ofFn ζ = [] := by simp
      have e₂ : List.ofFn ζ' = List.ofFn (fun i : Fin q => ζ' i.castSucc) ++ [ζ' (Fin.last q)] := by
        rw [List.ofFn_succ']
        simp [List.concat_eq_append]
      rw [e₁] at hl₁ hl₃
      rw [e₂] at hl₂ hl₃ hζs'
      have f₁ : GapFits s α' (List.ofFn fun i : Fin q => ζ' i.castSucc) (ζ' (Fin.last q)) :=
        gapFits_of_le hs hαs' (hζs' _ (by simp)) fun m hm => hζs' m (by simp [hm])
      have f₂ : GapFits s (α' + α) (List.ofFn fun i : Fin q => ζ' i.castSucc) (ζ' (Fin.last q)) :=
        ⟨f₁.1, by linarith [h.tubeGap_add α' α, f₁.2.1], f₁.2.2.1, f₁.2.2.2⟩
      rw [fieldProduct_zero_eq hl₁, h.fieldProduct_eq_chainProd hl₂ f₁,
        h.mul_chainProd f₁.2.1 hα₀.le]
      rw [add_comm α' α] at f₂ ⊢
      have hh : ∀ y : Fin (0 + q + 2) → ComplexVec4, List.ofFn y = _ →
          fieldProduct E A (0 + q + 1) y = _ := fun y hy => h.fieldProduct_eq_chainProd hy f₂
      exact (hh _ hl₃).symm
  | succ p =>
    have e₁ : List.ofFn ζ = ζ 0 :: List.ofFn (fun i : Fin p => ζ i.succ) := by
      rw [List.ofFn_succ]
    rw [e₁] at hl₁ hl₃ hζs
    cases n' with
    | zero =>
      have e₂ : List.ofFn ζ' = [] := by simp
      rw [e₂] at hl₂ hl₃
      have f₁ : GapFits s (ζ 0) (List.ofFn fun i : Fin p => ζ i.succ) α :=
        gapFits_of_le hs (hζs _ (by simp)) hαs fun m hm => hζs m (by simp [hm])
      have f₂ : GapFits s (ζ 0) (List.ofFn fun i : Fin p => ζ i.succ) (α + α') :=
        gapFits_of_le hs (hζs _ (by simp)) hadd f₁.2.2.2
      have l₁ : List.ofFn (snocPoint ζ α) = ζ 0 :: ((List.ofFn fun i : Fin p => ζ i.succ) ++ [α]) :=
        hl₁
      have l₃ : List.ofFn (joinAt ζ (α + α') ζ') =
          ζ 0 :: ((List.ofFn fun i : Fin p => ζ i.succ) ++ [α + α']) := by
        rw [hl₃]
        simp
      rw [h.fieldProduct_eq_chainProd l₁ f₁, fieldProduct_zero_eq hl₂,
        h.chainProd_mul f₁.2.2.1 (le_of_lt hα')]
      have hh : ∀ y : Fin (p + 2) → ComplexVec4, List.ofFn y = _ →
          fieldProduct E A (p + 1) y = _ := fun y hy => h.fieldProduct_eq_chainProd hy f₂
      exact (hh _ l₃).symm
    | succ q =>
      have e₂ : List.ofFn ζ' = List.ofFn (fun i : Fin q => ζ' i.castSucc) ++ [ζ' (Fin.last q)] := by
        rw [List.ofFn_succ']
        simp [List.concat_eq_append]
      rw [e₂] at hl₂ hl₃ hζs'
      have f₁ : GapFits s (ζ 0) (List.ofFn fun i : Fin p => ζ i.succ) α :=
        gapFits_of_le hs (hζs _ (by simp)) hαs fun m hm => hζs m (by simp [hm])
      have f₂ : GapFits s α' (List.ofFn fun i : Fin q => ζ' i.castSucc) (ζ' (Fin.last q)) :=
        gapFits_of_le hs hαs' (hζs' _ (by simp)) fun m hm => hζs' m (by simp [hm])
      have f₃ : GapFits s (ζ 0) ((List.ofFn fun i : Fin p => ζ i.succ) ++
          (α + α') :: List.ofFn fun i : Fin q => ζ' i.castSucc) (ζ' (Fin.last q)) := by
        refine gapFits_of_le hs (hζs _ (by simp)) (hζs' _ (by simp)) fun m hm => ?_
        simp only [List.mem_append, List.mem_cons] at hm
        rcases hm with hm | rfl | hm
        · exact hζs m (by simp [hm])
        · exact hadd
        · exact hζs' m (by simp [hm])
      have l₃ : List.ofFn (joinAt ζ (α + α') ζ') =
          ζ 0 :: (((List.ofFn fun i : Fin p => ζ i.succ) ++
            (α + α') :: List.ofFn fun i : Fin q => ζ' i.castSucc) ++ [ζ' (Fin.last q)]) := by
        rw [hl₃]
        simp
      rw [h.fieldProduct_eq_chainProd hl₁ f₁, h.fieldProduct_eq_chainProd hl₂ f₂,
        h.chainProd_mul_chainProd f₁.2.2.1 f₂.2.1]
      have hh : ∀ y : Fin (p + 1 + q + 2) → ComplexVec4, List.ofFn y = _ →
          fieldProduct E A (p + 1 + q + 1) y = _ := fun y hy => h.fieldProduct_eq_chainProd hy f₃
      exact (hh _ l₃).symm
theorem adjointOp_eq_star (X : BddOp K) : adjointOp X = star X := by
  have hex : ∃ B, IsAdjointOp X B := ⟨star X, fun χ χ' => by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]⟩
  have hs : IsAdjointOp X (adjointOp X) := Classical.epsilon_spec hex
  ext χ
  refine ext_inner_right ℂ fun χ' => ?_
  rw [hs χ χ', ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
theorem Hyps.star_spectralTranslation (h : Hyps E Ω A ℘ C) {ζ : ComplexVec4}
    (hζ : 0 ≤ tubeGap ζ) :
    star (spectralTranslation E ζ) = spectralTranslation E (-MinkowskiSpace.conjPoint ζ) := by
  rw [← adjointOp_eq_star, h.adjointOp_spectralTranslation hζ]
theorem Hyps.star_fieldOp (h : Hyps E Ω A ℘ C) {s : ℝ} (hs : 0 < s) : star (A s) = A s := by
  rw [← adjointOp_eq_star, h.bdd.isSelfAdjoint s hs]
theorem reflectList_cons (m : ComplexVec4) (l : List ComplexVec4) :
    reflectList (m :: l) = reflectList l ++ [-MinkowskiSpace.conjPoint m] := by
  simp [reflectList]
theorem reflectList_ends (a b : ComplexVec4) (l : List ComplexVec4) :
    reflectList (a :: (l ++ [b])) =
      -MinkowskiSpace.conjPoint b :: (reflectList l ++ [-MinkowskiSpace.conjPoint a]) := by
  simp [reflectList]
theorem Hyps.star_midProd_mul (h : Hyps E Ω A ℘ C) {s : ℝ} (hs : 0 < s) (l : List ComplexVec4)
    (hl : ∀ m ∈ l, 2 * s ≤ tubeGap m) :
    star (midProd E A s l) * A s = A s * midProd E A s (reflectList l) := by
  induction l with
  | nil =>
    simp [midProd_nil, reflectList]
  | cons m l ih =>
    have ih' := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hm := hl m List.mem_cons_self
    have hT := h.star_spectralTranslation (ζ := m - imagTimeShift (2 * s))
      (by rw [tubeGap_sub_imagTimeShift]; linarith)
    rw [neg_conjPoint_sub_imagTimeShift] at hT
    rw [midProd_cons, reflectList_cons, midProd_append, midProd_cons,
      midProd_nil, mul_one]
    simp only [star_mul, h.star_fieldOp hs, hT]
    calc star (midProd E A s l) * (A s * spectralTranslation E
            (-MinkowskiSpace.conjPoint m - imagTimeShift (2 * s))) * A s
        = star (midProd E A s l) * A s * (spectralTranslation E
            (-MinkowskiSpace.conjPoint m - imagTimeShift (2 * s)) * A s) := by
          simp only [mul_assoc]
      _ = _ := by
          rw [ih']
          simp only [mul_assoc]
theorem Hyps.star_chainProd (h : Hyps E Ω A ℘ C) {s : ℝ} {a b : ComplexVec4}
    {l : List ComplexVec4} (hf : GapFits s a l b) :
    star (chainProd E A s a l b) = chainProd E A s (-MinkowskiSpace.conjPoint b)
      (reflectList l) (-MinkowskiSpace.conjPoint a) := by
  obtain ⟨hs, ha, hb, hl⟩ := hf
  have hTa := h.star_spectralTranslation (ζ := a - imagTimeShift s)
    (by rw [tubeGap_sub_imagTimeShift]; linarith)
  have hTb := h.star_spectralTranslation (ζ := b - imagTimeShift s)
    (by rw [tubeGap_sub_imagTimeShift]; linarith)
  rw [neg_conjPoint_sub_imagTimeShift] at hTa hTb
  unfold chainProd
  simp only [star_mul, h.star_fieldOp hs, hTa, hTb]
  calc spectralTranslation E (-MinkowskiSpace.conjPoint b - imagTimeShift s) *
        (star (midProd E A s l) * (A s *
          spectralTranslation E (-MinkowskiSpace.conjPoint a - imagTimeShift s)))
      = spectralTranslation E (-MinkowskiSpace.conjPoint b - imagTimeShift s) *
        (star (midProd E A s l) * A s) *
          spectralTranslation E (-MinkowskiSpace.conjPoint a - imagTimeShift s) := by
        simp only [mul_assoc]
    _ = _ := by
        rw [h.star_midProd_mul hs l hl]
        simp only [mul_assoc]
theorem gapFits_reflect {s : ℝ} {a b : ComplexVec4} {l : List ComplexVec4}
    (hf : GapFits s a l b) :
    GapFits s (-MinkowskiSpace.conjPoint b) (reflectList l) (-MinkowskiSpace.conjPoint a) := by
  obtain ⟨hs, ha, hb, hl⟩ := hf
  refine ⟨hs, by rwa [tubeGap_neg_conjPoint], by rwa [tubeGap_neg_conjPoint], fun m hm => ?_⟩
  simp only [reflectList, List.mem_reverse, List.mem_map] at hm
  obtain ⟨x, hx, rfl⟩ := hm
  rw [tubeGap_neg_conjPoint]
  exact hl x hx
theorem gapFits_of_eq {s : ℝ} (hs : 0 < s) {L : List ComplexVec4} {a b : ComplexVec4}
    {l : List ComplexVec4} (hL : L = a :: (l ++ [b])) (hm : ∀ x ∈ L, 2 * s ≤ tubeGap x) :
    GapFits s a l b := by
  subst hL
  exact gapFits_of_le hs (hm a (by simp)) (hm b (by simp)) fun x hx => hm x (by simp [hx])
theorem Hyps.fieldProductAdjoint (h : Hyps E Ω A ℘ C) :
    FieldProductAdjoint E A := by
  intro n ζ hζ
  rw [adjointOp_eq_star]
  cases n with
  | zero =>
    have hl : List.ofFn ζ = [ζ 0] := by simp [List.ofFn_succ]
    have hr : List.ofFn (reflectTuple ζ) = [-MinkowskiSpace.conjPoint (ζ 0)] := by
      rw [ofFn_reflectTuple, hl]
      simp [reflectList]
    rw [fieldProduct_zero_eq hl, fieldProduct_zero_eq hr]
    exact h.star_spectralTranslation (hζ 0 (Set.mem_univ 0)).le
  | succ n =>
    obtain ⟨s, hs, hm⟩ := exists_gap_le (List.ofFn ζ) (mem_futureTube_of_mem_ofFn hζ)
    have hl := ofFn_eq_ends ζ
    have hf := gapFits_of_eq hs hl hm
    have hr : List.ofFn (reflectTuple ζ) = -MinkowskiSpace.conjPoint (ζ (Fin.last (n + 1))) ::
        (reflectList (List.ofFn fun k : Fin n => ζ k.castSucc.succ) ++
          [-MinkowskiSpace.conjPoint (ζ 0)]) := by
      rw [ofFn_reflectTuple, hl, reflectList_ends]
    rw [h.fieldProduct_eq_chainProd hl hf, h.star_chainProd hf]
    exact (h.fieldProduct_eq_chainProd hr (gapFits_reflect hf)).symm
theorem Hyps.chainProd_vacuum (h : Hyps E Ω A ℘ C) {s : ℝ} {a b : ComplexVec4}
    {l : List ComplexVec4} (hb : s ≤ tubeGap b) (hs : 0 < s) :
    chainProd E A s a l b Ω =
      (spectralTranslation E (a - imagTimeShift s) * A s * midProd E A s l) Ω := by
  have := h.spectralTranslation_vacuum (ζ := b - imagTimeShift s)
    (by rw [tubeGap_sub_imagTimeShift]; linarith)
  unfold chainProd
  change (spectralTranslation E (a - imagTimeShift s) * A s * midProd E A s l)
    (spectralTranslation E (b - imagTimeShift s) Ω) = _
  rw [this]
theorem Hyps.stateIndepOfLast (h : Hyps E Ω A ℘ C) :
    StateIndepOfLast E Ω A := by
  intro n ζ hζ ω ω' hω hω'
  cases n with
  | zero =>
    have hl : ∀ x, List.ofFn (snocPoint ζ x) = [x] := fun x => by
      rw [ofFn_snocPoint]
      simp
    rw [fieldProduct_zero_eq (hl ω), fieldProduct_zero_eq (hl ω'),
      h.spectralTranslation_vacuum (le_of_lt hω), h.spectralTranslation_vacuum (le_of_lt hω')]
  | succ p =>
    obtain ⟨s, hs, hm⟩ := exists_gap_le (ω :: ω' :: List.ofFn ζ) (by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact hω
      · exact hω'
      · exact mem_futureTube_of_mem_ofFn hζ x hx)
    have e₁ : List.ofFn ζ = ζ 0 :: List.ofFn (fun i : Fin p => ζ i.succ) := by
      rw [List.ofFn_succ]
    have hl : ∀ x, List.ofFn (snocPoint ζ x) =
        ζ 0 :: ((List.ofFn fun i : Fin p => ζ i.succ) ++ [x]) := fun x => by
      rw [ofFn_snocPoint, e₁]
      simp
    rw [e₁] at hm
    have hf : ∀ x, 2 * s ≤ tubeGap x →
        GapFits s (ζ 0) (List.ofFn fun i : Fin p => ζ i.succ) x := fun x hx =>
      gapFits_of_le hs (hm _ (by simp)) hx fun y hy => hm y (by simp [hy])
    have f₁ := hf ω (hm ω (by simp))
    have f₂ := hf ω' (hm ω' (by simp))
    rw [h.fieldProduct_eq_chainProd (hl ω) f₁, h.fieldProduct_eq_chainProd (hl ω') f₂,
      h.chainProd_vacuum f₁.2.2.1 hs, h.chainProd_vacuum f₂.2.2.1 hs]
theorem Hyps.norm_midProd_le (h : Hyps E Ω A ℘ C) {s : ℝ} (l : List ComplexVec4)
    (hl : ∀ m ∈ l, 2 * s ≤ tubeGap m) (hs : 0 < s) :
    ‖midProd E A s l‖ ≤ ‖A s‖ ^ l.length := by
  induction l with
  | nil =>
    simp only [midProd_nil, List.length_nil, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | cons m l ih =>
    have ih' := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hm := hl m List.mem_cons_self
    have hT := h.norm_spectralTranslation_le (ζ := m - imagTimeShift (2 * s))
      (by rw [tubeGap_sub_imagTimeShift]; linarith)
    rw [midProd_cons, List.length_cons, pow_succ']
    calc _ ≤ ‖spectralTranslation E (m - imagTimeShift (2 * s)) * A s‖ *
          ‖midProd E A s l‖ := norm_mul_le _ _
      _ ≤ (‖spectralTranslation E (m - imagTimeShift (2 * s))‖ * ‖A s‖) *
          ‖midProd E A s l‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ (1 * ‖A s‖) * ‖A s‖ ^ l.length := by gcongr
      _ = _ := by ring
theorem Hyps.norm_chainProd_le (h : Hyps E Ω A ℘ C) {s : ℝ} {a b : ComplexVec4}
    {l : List ComplexVec4} (hf : GapFits s a l b) :
    ‖chainProd E A s a l b‖ ≤ ‖A s‖ ^ (l.length + 1) := by
  obtain ⟨hs, ha, hb, hl⟩ := hf
  have hTa := h.norm_spectralTranslation_le (ζ := a - imagTimeShift s)
    (by rw [tubeGap_sub_imagTimeShift]; linarith)
  have hTb := h.norm_spectralTranslation_le (ζ := b - imagTimeShift s)
    (by rw [tubeGap_sub_imagTimeShift]; linarith)
  have hM := h.norm_midProd_le l hl hs
  unfold chainProd
  calc _ ≤ ‖spectralTranslation E (a - imagTimeShift s) * A s * midProd E A s l‖ *
        ‖spectralTranslation E (b - imagTimeShift s)‖ := norm_mul_le _ _
    _ ≤ ((‖spectralTranslation E (a - imagTimeShift s)‖ * ‖A s‖) *
          ‖midProd E A s l‖) * ‖spectralTranslation E (b - imagTimeShift s)‖ := by
        gcongr
        exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ ((1 * ‖A s‖) * ‖A s‖ ^ l.length) * 1 := by gcongr
    _ = _ := by ring
theorem one_le_zpow_neg_of_le_one {m : ℝ} (hm : 0 < m) (hm' : m ≤ 1) {q : ℤ} (hq : 0 ≤ q) :
    1 ≤ m ^ (-q) := by
  have := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hm hm'
    (z := ((-q : ℤ) : ℝ)) (by push_cast; exact_mod_cast neg_nonpos.2 hq)
  rwa [Real.rpow_intCast] at this
theorem pow_le_of_gap_bound {N M : ℕ} {℘ C s B : ℝ} (h℘ : 0 ≤ ℘) (hC : 1 ≤ C) (δ : Fin N → ℝ)
    (k₀ : Fin N) (hs : 0 < s) (hk₀ : δ k₀ = 2 * s) (hδ : ∀ k, 0 < δ k) (hB₀ : 0 ≤ B)
    (hB : B ≤ C * min 1 s ^ (-℘)) (q : ℤ) (hq : (M : ℝ) * ℘ ≤ q) (hq₀ : 0 ≤ q) :
    B ^ M ≤ ((2 : ℝ) ^ ℘ * C) ^ M * ∏ k, min 1 (δ k) ^ (-q) := by
  set μ : ℝ := min 1 (δ k₀) with hμ
  have hμ₀ : 0 < μ := lt_min one_pos (hδ k₀)
  have hμ₁ : μ ≤ 1 := min_le_left _ _
  have hhalf : μ / 2 ≤ min 1 s := by
    apply le_min
    · linarith
    · have : μ ≤ δ k₀ := min_le_right _ _
      linarith
  have h₁ : min 1 s ^ (-℘) ≤ (2 : ℝ) ^ ℘ * μ ^ (-℘) := by
    have := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < μ / 2) hhalf (neg_nonpos.2 h℘)
    refine this.trans (le_of_eq ?_)
    rw [div_eq_mul_inv, Real.mul_rpow hμ₀.le (by positivity), Real.inv_rpow (by positivity),
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2), inv_inv, mul_comm]
  have h₂ : B ≤ ((2 : ℝ) ^ ℘ * C) * μ ^ (-℘) := by
    refine hB.trans ?_
    calc C * min 1 s ^ (-℘) ≤ C * ((2 : ℝ) ^ ℘ * μ ^ (-℘)) := by gcongr
      _ = _ := by ring
  have h₃ : (μ ^ (-℘)) ^ M ≤ μ ^ (-q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμ₀.le, ← Real.rpow_intCast]
    apply Real.rpow_le_rpow_of_exponent_ge hμ₀ hμ₁
    push_cast
    linarith
  have h₄ : μ ^ (-q) ≤ ∏ k, min 1 (δ k) ^ (-q) := by
    have hone : ∀ k, 1 ≤ min 1 (δ k) ^ (-q) := fun k =>
      one_le_zpow_neg_of_le_one (lt_min one_pos (hδ k)) (min_le_left _ _) hq₀
    calc μ ^ (-q) = ∏ k, if k = k₀ then min 1 (δ k) ^ (-q) else 1 := by
          simp [hμ]
      _ ≤ _ := by
          apply Finset.prod_le_prod
          · intro k _
            split_ifs
            · exact zero_le_one.trans (hone k)
            · exact zero_le_one
          · intro k _
            split_ifs
            · exact le_rfl
            · exact hone k
  calc B ^ M ≤ (((2 : ℝ) ^ ℘ * C) * μ ^ (-℘)) ^ M := by gcongr
    _ = ((2 : ℝ) ^ ℘ * C) ^ M * (μ ^ (-℘)) ^ M := mul_pow _ _ _
    _ ≤ _ := by
        gcongr
        exact h₃.trans h₄
theorem Hyps.fieldProductNormBound (h : Hyps E Ω A ℘ C) : FieldProductNormBound E A ℘ C := by
  intro n ζ hζ
  have hpos : ∀ k, 0 < tubeGap (ζ k) := fun k => hζ k (Set.mem_univ k)
  cases n with
  | zero =>
    have hl : List.ofFn ζ = [ζ 0] := by simp [List.ofFn_succ]
    rw [fieldProduct_zero_eq hl]
    have := h.norm_spectralTranslation_le (hpos 0).le
    simpa [opNormOf, ceilExponent] using this
  | succ n =>
    have hl := ofFn_eq_ends ζ
    have hm := isAdmissibleGap_halfMin hζ
    have hf := gapFits_of_isAdmissibleGap hl hm
    have hnorm := h.norm_chainProd_le hf
    have hs := hm.1
    obtain ⟨k₀, _, hk₀⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
      Finset.univ_nonempty fun k => tubeGap (ζ k)
    rw [h.fieldProduct_eq_chainProd hl hf]
    have hlen : (List.ofFn fun k : Fin n => ζ k.castSucc.succ).length + 1 = n + 1 := by simp
    rw [hlen] at hnorm
    refine hnorm.trans ?_
    refine pow_le_of_gap_bound h.bdd.exponent_nonneg h.bdd.one_le_const
      (fun k => tubeGap (ζ k)) k₀ hs ?_ hpos (norm_nonneg _)
      (h.bdd.opNorm_le _ hs) _ ?_ ?_
    · unfold halfMinTubeGap
      rw [hk₀]
      ring
    · exact Int.le_ceil _
    · exact Int.ceil_nonneg (mul_nonneg (Nat.cast_nonneg _) h.bdd.exponent_nonneg)
theorem continuous_tubeGap : Continuous tubeGap := by apply _root_.YangMills.Construction.FieldForms.SpacelikeExtension.continuous_tubeGap <;> assumption
theorem isOpen_futureTube : IsOpen futureTube :=
  isOpen_lt continuous_const continuous_tubeGap
theorem isOpen_tubeTuples (m : ℕ) : IsOpen (tubeTuples m) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_futureTube
theorem continuous_coordsToTuple {m : ℕ} :
    Continuous (coordsToTuple : ComplexCoordinates (m * 4) → Fin m → ComplexVec4) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_apply _
theorem Hyps.continuousOn_spectralTranslation (h : Hyps E Ω A ℘ C) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (spectralTranslation E) {ζ | ε ≤ tubeGap ζ} := by
  intro ζ₀ h₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous fun ζ : ComplexVec4 => ε⁻¹ * complexEucNorm (ζ - ζ₀) := by
    unfold complexEucNorm
    fun_prop
  have h₁ : Filter.Tendsto (fun ζ : ComplexVec4 => ε⁻¹ * complexEucNorm (ζ - ζ₀))
      (nhdsWithin ζ₀ {ζ | ε ≤ tubeGap ζ}) (nhds 0) := by
    have := (hc.tendsto ζ₀).mono_left (nhdsWithin_le_nhds (s := {ζ | ε ≤ tubeGap ζ}))
    simpa [complexEucNorm] using this
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun ζ hζ => ?_) h₁
  have hζ' : ε ≤ tubeGap ζ := hζ
  have h₀' : ε ≤ tubeGap ζ₀ := h₀
  exact h.lip ζ ζ₀ ε (hε.le.trans hζ') (hε.le.trans h₀') hε hζ' h₀'
theorem Hyps.continuousOn_fieldProductAt (h : Hyps E Ω A ℘ C) {s : ℝ} (hs : 0 < s)
    (n : ℕ) : ContinuousOn (fieldProductAt (n := n) E A s)
      {ζ | ∀ k, 3 * s ≤ tubeGap (ζ k)} := by
  have hT : ∀ (k : Fin (n + 2)) (c : ℝ), c ≤ 2 * s →
      ContinuousOn (fun ζ : Fin (n + 2) → ComplexVec4 =>
        spectralTranslation E (ζ k - imagTimeShift c))
        {ζ | ∀ k, 3 * s ≤ tubeGap (ζ k)} := by
    intro k c hc
    refine ContinuousOn.comp (g := spectralTranslation E)
      (f := fun ζ : Fin (n + 2) → ComplexVec4 => ζ k - imagTimeShift c)
      (h.continuousOn_spectralTranslation hs) (Continuous.continuousOn (by fun_prop)) fun ζ hζ => ?_
    have := hζ k
    change s ≤ tubeGap (ζ k - imagTimeShift c)
    rw [tubeGap_sub_imagTimeShift]
    linarith
  have hmid : ContinuousOn (fun ζ : Fin (n + 2) → ComplexVec4 =>
      (List.ofFn fun k : Fin n => spectralTranslation E
        (ζ k.castSucc.succ - imagTimeShift (2 * s)) * A s).prod)
      {ζ | ∀ k, 3 * s ≤ tubeGap (ζ k)} := by
    simp_rw [List.ofFn_eq_map]
    exact continuousOn_list_prod _ fun i _ =>
      (hT _ _ le_rfl).mul continuousOn_const
  unfold fieldProductAt
  exact (((hT 0 s (by linarith)).mul continuousOn_const).mul hmid).mul
    (hT _ s (by linarith))
theorem Hyps.fieldProduct_eq_fieldProductAt (h : Hyps E Ω A ℘ C) {s : ℝ} (hs : 0 < s) {n : ℕ}
    {ζ : Fin (n + 2) → ComplexVec4} (hζ : ∀ k, 2 * s ≤ tubeGap (ζ k)) :
    fieldProduct E A (n + 1) ζ = fieldProductAt E A s ζ := by
  have hl := ofFn_eq_ends ζ
  have hf : GapFits s _ _ _ := gapFits_of_eq hs hl fun x hx => by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    exact hζ k
  rw [h.fieldProduct_eq_chainProd hl hf, fieldProductAt_eq_chainProd hl]
theorem exists_quarter_gap {m : ℕ} {ζ : Fin m → ComplexVec4} (hζ : ζ ∈ tubeTuples m) :
    ∃ s : ℝ, 0 < s ∧ ∀ k, 4 * s ≤ tubeGap (ζ k) := by
  obtain ⟨s, hs, hm⟩ := exists_gap_le (List.ofFn ζ) (mem_futureTube_of_mem_ofFn hζ)
  refine ⟨s / 2, by positivity, fun k => ?_⟩
  have := hm _ (mem_ofFn_apply ζ k)
  linarith
theorem isOpen_gapGT {m : ℕ} (c : ℝ) :
    IsOpen {ζ : Fin m → ComplexVec4 | ∀ k, c < tubeGap (ζ k)} := by
  have : {ζ : Fin m → ComplexVec4 | ∀ k, c < tubeGap (ζ k)} =
      ⋂ k, {ζ | c < tubeGap (ζ k)} := by
    ext ζ
    simp
  rw [this]
  exact isOpen_iInter_of_finite fun k =>
    isOpen_lt continuous_const (continuous_tubeGap.comp (continuous_apply k))
theorem Hyps.continuousOn_fieldProduct (h : Hyps E Ω A ℘ C) (n : ℕ) :
    ContinuousOn (fieldProduct E A n) (tubeTuples (n + 1)) := by
  intro ζ₀ hζ₀
  obtain ⟨s, hs, hm⟩ := exists_quarter_gap hζ₀
  have hV : {ζ : Fin (n + 1) → ComplexVec4 | ∀ k, 3 * s < tubeGap (ζ k)} ∈ nhds ζ₀ :=
    (isOpen_gapGT _).mem_nhds fun k => by linarith [hm k]
  cases n with
  | zero =>
    have hc : ContinuousAt (fun ζ : Fin 1 → ComplexVec4 => spectralTranslation E (ζ 0)) ζ₀ := by
      have h₁ : ContinuousOn (spectralTranslation E) {ζ | s ≤ tubeGap ζ} :=
        h.continuousOn_spectralTranslation hs
      have h₂ : {ζ : ComplexVec4 | s ≤ tubeGap ζ} ∈ nhds (ζ₀ 0) :=
        Filter.mem_of_superset ((isOpen_lt continuous_const continuous_tubeGap).mem_nhds
          (show s < tubeGap (ζ₀ 0) by linarith [hm 0]))
          fun ζ hζ => le_of_lt (show s < tubeGap ζ from hζ)
      exact ContinuousAt.comp (f := fun ζ : Fin 1 → ComplexVec4 => ζ 0)
        (h₁.continuousAt h₂) (continuous_apply 0).continuousAt
    exact hc.continuousWithinAt
  | succ n =>
    have hc : ContinuousAt (fieldProductAt (n := n) E A s) ζ₀ :=
      (h.continuousOn_fieldProductAt hs n).continuousAt
        (Filter.mem_of_superset hV fun ζ hζ k => (hζ k).le)
    have he : fieldProduct E A (n + 1) =ᶠ[nhds ζ₀] fieldProductAt E A s :=
      Filter.mem_of_superset hV fun ζ hζ =>
        h.fieldProduct_eq_fieldProductAt hs fun k => by linarith [hζ k]
    exact (hc.congr he.symm).continuousWithinAt
theorem coordsToTuple_add_smul_basis {m : ℕ} (a : ComplexCoordinates (m * 4)) (k : Fin m)
    (μ : Fin 4) (t : ℂ) :
    coordsToTuple (a + t • ComplexCoordinates.stdBasisVector (finProdFinEquiv (k, μ))) =
      Function.update (coordsToTuple a) k
        (coordsToTuple a k + t • ComplexCoordinates.stdBasisVector μ) := by
  funext k' μ'
  by_cases hk : k' = k
  · subst hk
    by_cases hμ : μ' = μ
    · subst hμ
      simp [coordsToTuple, ComplexCoordinates.stdBasisVector]
    · have : finProdFinEquiv (k', μ') ≠ finProdFinEquiv (k', μ) := fun e => hμ (by
        simpa using finProdFinEquiv.injective e)
      simp [coordsToTuple, ComplexCoordinates.stdBasisVector, Pi.single_apply, hμ, this]
  · have : finProdFinEquiv (k', μ') ≠ finProdFinEquiv (k, μ) := fun e => hk (by
      simpa using congrArg Prod.fst (finProdFinEquiv.injective e))
    simp [coordsToTuple, ComplexCoordinates.stdBasisVector, Pi.single_apply, hk, this,
      Function.update_apply]
theorem ofFn_update_eq_append {N : ℕ} (ζ : Fin N → ComplexVec4) (k : Fin N) :
    ∃ P Q : List ComplexVec4, ∀ y, List.ofFn (Function.update ζ k y) = P ++ y :: Q := by
  induction N with
  | zero => exact k.elim0
  | succ N ih =>
    refine Fin.cases ?_ (fun k' => ?_) k
    · exact ⟨[], List.ofFn fun i => ζ i.succ, fun y => by
        simp [List.ofFn_succ, Function.update_apply, Fin.succ_ne_zero]⟩
    · obtain ⟨P, Q, hPQ⟩ := ih (fun i => ζ i.succ) k'
      refine ⟨ζ 0 :: P, Q, fun y => ?_⟩
      have e : (fun i : Fin N => Function.update ζ k'.succ y i.succ) =
          Function.update (fun i => ζ i.succ) k' y := by
        funext i
        simp [Function.update_apply, Fin.succ_inj]
      rw [List.ofFn_succ, e, hPQ]
      simp [Function.update_apply, (Fin.succ_ne_zero k').symm]
theorem fieldProductAt_update_factor {n : ℕ} (ζ : Fin (n + 2) → ComplexVec4) (k : Fin (n + 2))
    (s : ℝ) :
    ∃ (L R : BddOp K) (c : ℝ), (c = s ∨ c = 2 * s) ∧ ∀ y,
      fieldProductAt E A s (Function.update ζ k y) =
        L * spectralTranslation E (y - imagTimeShift c) * R := by
  obtain ⟨P, Q, hPQ⟩ := ofFn_update_eq_append ζ k
  have hlen : (P ++ (0 : ComplexVec4) :: Q).length = n + 2 := by
    rw [← hPQ 0]
    simp
  rcases P with _ | ⟨a, P⟩
  · rcases List.eq_nil_or_concat Q with rfl | ⟨Q, b, rfl⟩
    · simp at hlen
    · refine ⟨1, A s * midProd E A s Q * spectralTranslation E (b - imagTimeShift s),
        s, Or.inl rfl, fun y => ?_⟩
      rw [fieldProductAt_eq_chainProd (a := y) (l := Q) (b := b) (by rw [hPQ]; simp)]
      unfold chainProd
      simp only [mul_assoc, one_mul]
  · rcases List.eq_nil_or_concat Q with rfl | ⟨Q, b, rfl⟩
    · refine ⟨spectralTranslation E (a - imagTimeShift s) * A s * midProd E A s P, 1,
        s, Or.inl rfl, fun y => ?_⟩
      rw [fieldProductAt_eq_chainProd (a := a) (l := P) (b := y) (by rw [hPQ]; simp)]
      unfold chainProd
      simp only [mul_one]
    · refine ⟨spectralTranslation E (a - imagTimeShift s) * A s * midProd E A s P,
        A s * midProd E A s Q * spectralTranslation E (b - imagTimeShift s),
        2 * s, Or.inr rfl, fun y => ?_⟩
      rw [fieldProductAt_eq_chainProd (a := a) (l := P ++ y :: Q) (b := b) (by rw [hPQ]; simp)]
      unfold chainProd
      rw [midProd_append, midProd_cons]
      simp only [mul_assoc]
theorem Hyps.eventually_differentiableAt_inner_translation (h : Hyps E Ω A ℘ C) (χ χ' : K)
    {x : ComplexVec4} (hx : x ∈ futureTube) (μ : Fin 4) :
    ∀ᶠ t in nhds (0 : ℂ), DifferentiableAt ℂ (fun t : ℂ => inner ℂ χ
      (spectralTranslation E (x + t • ComplexCoordinates.stdBasisVector μ) χ')) t := by
  have := (h.holo χ χ').2.2 x hx μ
  exact this.mono fun t ht => differentiableAt_pi.1 ht 0
theorem inner_mul_mul_apply (L R X : BddOp K) (χ χ' : K) :
    inner ℂ χ ((L * X * R) χ') = inner ℂ (star L χ) (X (R χ')) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rfl
theorem eventually_lt_tubeGap_shift (x : ComplexVec4) (μ : Fin 4) {c : ℝ} (hc : c < tubeGap x) :
    ∀ᶠ t in nhds (0 : ℂ), c < tubeGap (x + t • ComplexCoordinates.stdBasisVector μ) := by
  have hcont : Continuous fun t : ℂ => tubeGap (x + t • ComplexCoordinates.stdBasisVector μ) :=
    continuous_tubeGap.comp (by fun_prop)
  have : c < tubeGap (x + (0 : ℂ) • ComplexCoordinates.stdBasisVector μ) := by simpa using hc
  exact hcont.continuousAt.eventually (lt_mem_nhds this)
theorem Hyps.eventually_differentiableAt_inner_fieldProduct (h : Hyps E Ω A ℘ C) (n : ℕ)
    (χ χ' : K) {ζ : Fin (n + 1) → ComplexVec4} (hζ : ζ ∈ tubeTuples (n + 1)) (k : Fin (n + 1))
    (μ : Fin 4) :
    ∀ᶠ t in nhds (0 : ℂ), DifferentiableAt ℂ (fun t : ℂ => inner ℂ χ
      (fieldProduct E A n (Function.update ζ k
        (ζ k + t • ComplexCoordinates.stdBasisVector μ)) χ')) t := by
  cases n with
  | zero =>
    have hk : k = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst hk
    refine (h.eventually_differentiableAt_inner_translation χ χ' (hζ 0 (Set.mem_univ 0)) μ).mono
      fun t ht => ?_
    simpa [fieldProduct] using ht
  | succ n =>
    obtain ⟨s, hs, hm⟩ := exists_quarter_gap hζ
    obtain ⟨L, R, c, hc, hform⟩ := fieldProductAt_update_factor (E := E) (A := A) ζ k s
    have hc' : c ≤ 2 * s := by rcases hc with rfl | rfl <;> linarith
    have hx : ζ k - imagTimeShift c ∈ futureTube := by
      change 0 < tubeGap _
      rw [tubeGap_sub_imagTimeShift]
      linarith [hm k]
    have hd := h.eventually_differentiableAt_inner_translation (star L χ) (R χ') hx μ
    have hnear := eventually_lt_tubeGap_shift (ζ k) μ (c := 3 * s) (by linarith [hm k])
    filter_upwards [hd, hnear.eventually_nhds] with t ht ht'
    refine ht.congr_of_eventuallyEq (ht'.mono fun t' ht'' => ?_)
    have hmarg : ∀ k', 2 * s ≤ tubeGap (Function.update ζ k
        (ζ k + t' • ComplexCoordinates.stdBasisVector μ) k') := by
      intro k'
      by_cases hk : k' = k
      · subst hk
        simp only [Function.update_self]
        linarith
      · simp only [Function.update_of_ne hk]
        linarith [hm k']
    simp only []
    rw [h.fieldProduct_eq_fieldProductAt hs hmarg, hform, inner_mul_mul_apply]
    congr 3
    abel
theorem Hyps.fieldProductHolomorphic (h : Hyps E Ω A ℘ C) :
    FieldProductHolomorphic E A := by
  intro n
  refine ⟨h.continuousOn_fieldProduct n, fun χ χ' => ?_⟩
  refine ⟨(isOpen_tubeTuples _).preimage continuous_coordsToTuple, ?_, ?_⟩
  · refine continuousOn_pi.2 fun _ => ?_
    have hc : ContinuousOn (fun ζ : Fin (n + 1) → ComplexVec4 =>
        inner ℂ χ (fieldProduct E A n ζ χ')) (tubeTuples (n + 1)) :=
      ContinuousOn.inner continuousOn_const
        ((h.continuousOn_fieldProduct n).clm_apply continuousOn_const)
    exact hc.comp continuous_coordsToTuple.continuousOn fun z hz => hz
  · intro a ha j
    obtain ⟨⟨k, μ⟩, rfl⟩ := finProdFinEquiv.surjective j
    refine (h.eventually_differentiableAt_inner_fieldProduct n χ χ' ha k μ).mono fun t ht => ?_
    refine differentiableAt_pi.2 fun _ => ?_
    simpa only [coordsToTuple_add_smul_basis] using ht
theorem imagTimeShift_one_mem : imagTimeShift 1 ∈ futureTube := by apply _root_.YangMills.Construction.MinkowskiSpace.InvariantEuclideanProof.imagTimeShift_one_mem_futureTube <;> assumption
theorem snocPoint_mem {n : ℕ} {ζ : Fin n → ComplexVec4} (hζ : ζ ∈ tubeTuples n)
    {c : ComplexVec4} (hc : c ∈ futureTube) : snocPoint ζ c ∈ tubeTuples (n + 1) := by apply _root_.YangMills.Construction.TubeMatrixElements.snocPoint_mem_tubeTuples <;> assumption
theorem consPoint_mem {n : ℕ} {ζ : Fin n → ComplexVec4} (hζ : ζ ∈ tubeTuples n)
    {c : ComplexVec4} (hc : c ∈ futureTube) : consPoint c ζ ∈ tubeTuples (n + 1) := by
  intro k _
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa [consPoint] using hc
  · simpa [consPoint] using hζ i (Set.mem_univ i)
section Differentiable
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
theorem differentiable_snocPoint {n : ℕ} {f : X → Fin n → ComplexVec4}
    (hf : Differentiable ℂ f) (c : ComplexVec4) :
    Differentiable ℂ fun x => snocPoint (f x) c := by
  refine differentiable_pi.2 fun k => ?_
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp [snocPoint]
  · simpa [snocPoint] using differentiable_pi.1 hf i
theorem differentiable_consPoint {n : ℕ} {f : X → Fin n → ComplexVec4}
    (hf : Differentiable ℂ f) (c : ComplexVec4) :
    Differentiable ℂ fun x => consPoint c (f x) := by
  refine differentiable_pi.2 fun k => ?_
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [consPoint]
  · simpa [consPoint] using differentiable_pi.1 hf i
end Differentiable
theorem differentiable_diffCoords {n : ℕ} :
    Differentiable ℂ (diffCoords : (Fin (n + 1) → ComplexVec4) → Fin (n + 1) → ComplexVec4) := by
  refine differentiable_pi.2 fun k => ?_
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa [diffCoords] using differentiable_apply (𝕜 := ℂ) (0 : Fin (n + 1))
      (F' := fun _ => ComplexVec4)
  · simp only [diffCoords, Fin.cons_succ, successiveDiffs]
    exact (differentiable_apply (𝕜 := ℂ) i.succ (F' := fun _ => ComplexVec4)).sub
      (differentiable_apply (𝕜 := ℂ) i.castSucc (F' := fun _ => ComplexVec4))
theorem isHolomorphicIn_of_differentiable {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    (hO : IsOpen O) {g : ComplexCoordinates N → ComplexCoordinates N'} (hg : Differentiable ℂ g) :
    ComplexCoordinates.IsHolomorphicIn O g :=
  ⟨hO, hg.continuous.continuousOn, fun a _ j => Filter.Eventually.of_forall fun t =>
    (hg.comp (by fun_prop :
      Differentiable ℂ fun t : ℂ => a + t • ComplexCoordinates.stdBasisVector j)) t⟩
def tupleToCoords {m : ℕ} (ξ : Fin m → ComplexVec4) : ComplexCoordinates (m * 4) :=
  fun j => ξ (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
theorem coordsToTuple_tupleToCoords {m : ℕ} (ξ : Fin m → ComplexVec4) :
    coordsToTuple (tupleToCoords ξ) = ξ := by apply _root_.YangMills.Construction.FieldForms.SpacelikeExtension.coordsToTuple_tupleCoords <;> assumption
theorem differentiable_coordsToTuple {m : ℕ} :
    Differentiable ℂ (coordsToTuple : ComplexCoordinates (m * 4) → Fin m → ComplexVec4) :=
  differentiable_pi.2 fun _ => differentiable_pi.2 fun _ => differentiable_apply _
theorem differentiable_tupleToCoords {m : ℕ} :
    Differentiable ℂ (tupleToCoords : (Fin m → ComplexVec4) → ComplexCoordinates (m * 4)) :=
  differentiable_pi.2 fun j =>
    (differentiable_pi.1 (differentiable_apply (𝕜 := ℂ) (finProdFinEquiv.symm j).1
      (F' := fun _ => ComplexVec4))) _
theorem isHolomorphicIn_comp (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {m m' : ℕ} {O' : Set (Fin m → ComplexVec4)} {O : Set (Fin m' → ComplexVec4)}
    (hO' : IsOpen (coordsToTuple ⁻¹' O')) (Φ : (Fin m → ComplexVec4) → Fin m' → ComplexVec4)
    (hΦ : Differentiable ℂ Φ) (hmaps : Set.MapsTo Φ O' O) (w : (Fin m' → ComplexVec4) → ℂ)
    (hw : ComplexCoordinates.IsHolomorphicIn (N' := 1) (coordsToTuple ⁻¹' O)
      fun z _ => w (coordsToTuple z)) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) (coordsToTuple ⁻¹' O')
      fun z _ => w (Φ (coordsToTuple z)) := by
  have hg : ComplexCoordinates.IsHolomorphicIn (coordsToTuple ⁻¹' O')
      fun z => tupleToCoords (Φ (coordsToTuple z)) :=
    isHolomorphicIn_of_differentiable hO'
      (differentiable_tupleToCoords.comp (hΦ.comp differentiable_coordsToTuple))
  have := ((hP.1 _ _ hw.1).1 _ _ hw).2.2.2.1 _ _ _ hg fun z hz => by
    change coordsToTuple (tupleToCoords (Φ (coordsToTuple z))) ∈ O
    rw [coordsToTuple_tupleToCoords]
    exact hmaps hz
  simpa [Function.comp_def, coordsToTuple_tupleToCoords] using this
theorem diffCoords_linear {n : ℕ} (x y : Fin (n + 1) → ComplexVec4) (a b : ℝ) :
    diffCoords (a • x + b • y) = a • diffCoords x + b • diffCoords y := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [diffCoords]
  · simp only [diffCoords, Fin.cons_succ, successiveDiffs, Pi.add_apply, Pi.smul_apply]
    module
theorem isOpen_diffCoordsInTube (n : ℕ) : IsOpen (diffCoordsInTube (n + 1)) :=
  (isOpen_tubeTuples _).preimage differentiable_diffCoords.continuous
theorem Hyps.expectationsStatesHolomorphic (h : Hyps E Ω A ℘ C) :
    ExpectationsStatesHolomorphic E Ω A := by
  intro n
  have hΦ : Differentiable ℂ fun z : Fin (n + 1) → ComplexVec4 =>
      snocPoint (diffCoords z) (imagTimeShift 1) :=
    differentiable_snocPoint differentiable_diffCoords _
  have hmaps : Set.MapsTo (fun z : Fin (n + 1) → ComplexVec4 =>
      snocPoint (diffCoords z) (imagTimeShift 1)) (diffCoordsInTube (n + 1))
      (tubeTuples (n + 1 + 1)) := fun z hz => snocPoint_mem hz imagTimeShift_one_mem
  refine ⟨?_, ?_, isOpen_diffCoordsInTube n, fun χ => ?_, ?_⟩
  · exact isHolomorphicIn_comp h.powerSeries
      ((isOpen_tubeTuples _).preimage continuous_coordsToTuple)
      (fun ζ : Fin n → ComplexVec4 =>
        consPoint (imagTimeShift 1) (snocPoint ζ (imagTimeShift 1)))
      (differentiable_consPoint (differentiable_snocPoint differentiable_id _) _)
      (fun ζ hζ => consPoint_mem (snocPoint_mem hζ imagTimeShift_one_mem)
        imagTimeShift_one_mem) (fun ζ => inner ℂ Ω (fieldProduct E A (n + 1) ζ Ω))
      ((h.fieldProductHolomorphic (n + 1)).2 Ω Ω)
  · intro x hx y hy a b ha hb hab
    change diffCoords (a • x + b • y) ∈ tubeTuples (n + 1)
    rw [diffCoords_linear]
    exact h.tubeTuples_convex _ hx hy ha hb hab
  · exact isHolomorphicIn_comp h.powerSeries
      ((isOpen_diffCoordsInTube n).preimage continuous_coordsToTuple) _ hΦ hmaps
      (fun ζ => inner ℂ χ (fieldProduct E A (n + 1) ζ Ω))
      ((h.fieldProductHolomorphic (n + 1)).2 χ Ω)
  · exact ((h.continuousOn_fieldProduct (n + 1)).comp hΦ.continuous.continuousOn hmaps).clm_apply
      continuousOn_const
theorem prod_snocPoint {M : Type} [CommMonoid M] {n : ℕ} (f : ComplexVec4 → M)
    (ζ : Fin n → ComplexVec4) (c : ComplexVec4) :
    ∏ k, f (snocPoint ζ c k) = (∏ k, f (ζ k)) * f c := by
  rw [Fin.prod_univ_castSucc]
  simp [snocPoint]
theorem prod_consPoint {M : Type} [CommMonoid M] {n : ℕ} (f : ComplexVec4 → M)
    (ζ : Fin n → ComplexVec4) (c : ComplexVec4) :
    ∏ k, f (consPoint c ζ k) = f c * ∏ k, f (ζ k) := by
  rw [Fin.prod_univ_succ]
  simp [consPoint]
theorem min_one_tubeGap_imagTimeShift_one_zpow (q : ℤ) :
    min 1 (tubeGap (imagTimeShift 1)) ^ q = 1 := by
  rw [tubeGap_imagTimeShift]
  simp
theorem Hyps.expectationsStatesBounded (h : Hyps E Ω A ℘ C) :
    ExpectationsStatesBounded E Ω A ℘ C := by
  intro n
  have hΩ : ‖Ω‖ = 1 := h.bdd.norm_vacuum
  constructor
  · intro ζ hζ
    cases n with
    | zero => simp [vacuumExpectation]
    | succ p =>
      have hb := h.fieldProductNormBound (p + 1)
        (consPoint (imagTimeShift 1) (snocPoint ζ (imagTimeShift 1)))
        (consPoint_mem (snocPoint_mem hζ imagTimeShift_one_mem)
          imagTimeShift_one_mem)
      rw [prod_consPoint (fun x => min 1 (tubeGap x) ^ (-ceilExponent ℘ (p + 1))),
        prod_snocPoint (fun x => min 1 (tubeGap x) ^ (-ceilExponent ℘ (p + 1))),
        min_one_tubeGap_imagTimeShift_one_zpow, one_mul, mul_one] at hb
      refine le_trans ?_ hb
      change ‖inner ℂ Ω (fieldProduct E A (p + 1) _ Ω)‖ ≤ ‖fieldProduct E A (p + 1) _‖
      refine (norm_inner_le_norm _ _).trans ?_
      rw [hΩ, one_mul]
      simpa [hΩ] using (fieldProduct E A (p + 1) _).le_opNorm Ω
  · intro z hz
    cases n with
    | zero => simp [stateVector, hΩ]
    | succ p =>
      have hb := h.fieldProductNormBound (p + 1) (snocPoint (diffCoords z) (imagTimeShift 1))
        (snocPoint_mem hz imagTimeShift_one_mem)
      rw [prod_snocPoint (fun x => min 1 (tubeGap x) ^ (-ceilExponent ℘ (p + 1))),
        min_one_tubeGap_imagTimeShift_one_zpow, mul_one] at hb
      refine le_trans ?_ hb
      change ‖fieldProduct E A (p + 1) _ Ω‖ ≤ ‖fieldProduct E A (p + 1) _‖
      simpa [hΩ] using (fieldProduct E A (p + 1) _).le_opNorm Ω
theorem ofFn_diffCoords {n : ℕ} (z : Fin (n + 1) → ComplexVec4) :
    List.ofFn (diffCoords z) = z 0 :: List.ofFn (successiveDiffs z) :=
  ofFn_consPoint (z 0) (successiveDiffs z)
theorem ofFn_snocPoint_diffCoords {n : ℕ} (z : Fin (n + 1) → ComplexVec4) (c : ComplexVec4) :
    List.ofFn (snocPoint (diffCoords z) c) = z 0 :: (List.ofFn (successiveDiffs z) ++ [c]) := by
  rw [ofFn_snocPoint, ofFn_diffCoords]
  rfl
theorem gapFits_diffCoords {p : ℕ} {z : Fin (p + 1) → ComplexVec4} {s : ℝ} (hs : 0 < s)
    (h₁ : 2 * s ≤ tubeGap (imagTimeShift 1))
    (hm : ∀ x ∈ List.ofFn (diffCoords z), 2 * s ≤ tubeGap x) :
    GapFits s (z 0) (List.ofFn (successiveDiffs z)) (imagTimeShift 1) := by
  rw [ofFn_diffCoords] at hm
  exact gapFits_of_le hs (hm _ (by simp)) h₁ fun x hx => hm x (by simp [hx])
theorem exists_gapFits_diffCoords {p : ℕ} {z : Fin (p + 1) → ComplexVec4}
    (hz : z ∈ diffCoordsInTube (p + 1)) :
    ∃ s : ℝ, 0 < s ∧ GapFits s (z 0) (List.ofFn (successiveDiffs z)) (imagTimeShift 1) := by
  obtain ⟨s, hs, hm⟩ := exists_gap_le (imagTimeShift 1 :: List.ofFn (diffCoords z)) (by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact imagTimeShift_one_mem
    · exact mem_futureTube_of_mem_ofFn hz x hx)
  exact ⟨s, hs, gapFits_diffCoords hs (hm _ (by simp)) fun x hx => hm x (List.mem_cons_of_mem _ hx)⟩
theorem Hyps.stateVector_eq_chainProd (h : Hyps E Ω A ℘ C) {p : ℕ}
    {z : Fin (p + 1) → ComplexVec4} {s : ℝ}
    (hf : GapFits s (z 0) (List.ofFn (successiveDiffs z)) (imagTimeShift 1)) :
    stateVector E Ω A (p + 1) z =
      chainProd E A s (z 0) (List.ofFn (successiveDiffs z)) (imagTimeShift 1) Ω := by
  change fieldProduct E A (p + 1) (snocPoint (diffCoords z) (imagTimeShift 1)) Ω = _
  rw [h.fieldProduct_eq_chainProd (ofFn_snocPoint_diffCoords z _) hf]
theorem Hyps.spectralTranslation_stateVector (h : Hyps E Ω A ℘ C) {n : ℕ}
    {z : Fin n → ComplexVec4} (hz : z ∈ diffCoordsInTube n) {ω : ComplexVec4}
    (hω : 0 ≤ tubeGap ω) :
    spectralTranslation E ω (stateVector E Ω A n z) = stateVector E Ω A n fun k => z k + ω := by
  cases n with
  | zero => exact h.spectralTranslation_vacuum hω
  | succ p =>
    obtain ⟨s, hs, hf⟩ := exists_gapFits_diffCoords hz
    have hd : successiveDiffs (fun k => z k + ω) = successiveDiffs z := by
      funext i
      simp [successiveDiffs]
    have hf' : GapFits s ((fun k => z k + ω) 0) (List.ofFn (successiveDiffs fun k => z k + ω))
        (imagTimeShift 1) := by
      rw [hd]
      exact ⟨hs, by linarith [h.tubeGap_add (z 0) ω, hf.2.1], hf.2.2.1, hf.2.2.2⟩
    rw [h.stateVector_eq_chainProd hf, h.stateVector_eq_chainProd hf', hd]
    change (spectralTranslation E ω * chainProd E A s (z 0) _ _) Ω = _
    rw [h.mul_chainProd hf.2.1 hω]
theorem Hyps.inner_vacuum_spectralTranslation (h : Hyps E Ω A ℘ C) {y : ComplexVec4}
    (hy : 0 ≤ tubeGap y) (χ : K) :
    inner ℂ Ω (spectralTranslation E y χ) = inner ℂ Ω χ := by
  have e : inner ℂ Ω (spectralTranslation E y χ) =
      inner ℂ (star (spectralTranslation E y) Ω) χ := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rw [e, h.star_spectralTranslation hy,
    h.spectralTranslation_vacuum (by rw [tubeGap_neg_conjPoint]; exact hy)]
theorem Hyps.inner_vacuum_chainProd (h : Hyps E Ω A ℘ C) {s : ℝ} {a a' b : ComplexVec4}
    {l : List ComplexVec4} (ha : s ≤ tubeGap a) (ha' : s ≤ tubeGap a') (χ : K) :
    inner ℂ Ω (chainProd E A s a l b χ) = inner ℂ Ω (chainProd E A s a' l b χ) := by
  have key : ∀ x, s ≤ tubeGap x → inner ℂ Ω (chainProd E A s x l b χ) =
      inner ℂ Ω ((A s * midProd E A s l * spectralTranslation E
        (b - imagTimeShift s)) χ) := by
    intro x hx
    have e : chainProd E A s x l b = spectralTranslation E (x - imagTimeShift s) *
        (A s * midProd E A s l * spectralTranslation E (b - imagTimeShift s)) := by
      unfold chainProd
      simp only [mul_assoc]
    rw [e]
    exact h.inner_vacuum_spectralTranslation (by rw [tubeGap_sub_imagTimeShift]; linarith) _
  rw [key a ha, key a' ha']
theorem Hyps.vacuumExpectation_eq_chainProd (h : Hyps E Ω A ℘ C) {p : ℕ}
    {ζ : Fin p → ComplexVec4} {l : List ComplexVec4} (hl : List.ofFn ζ = l) {s : ℝ}
    (hf : GapFits s (imagTimeShift 1) l (imagTimeShift 1)) :
    vacuumExpectation E Ω A (p + 1) ζ =
      inner ℂ Ω (chainProd E A s (imagTimeShift 1) l (imagTimeShift 1) Ω) := by
  change inner ℂ Ω (fieldProduct E A (p + 1) (consPoint (imagTimeShift 1)
    (snocPoint ζ (imagTimeShift 1))) Ω) = _
  rw [h.fieldProduct_eq_chainProd (by rw [ofFn_consPoint, ofFn_snocPoint, hl]) hf]
theorem Hyps.inner_vacuum_stateVector (h : Hyps E Ω A ℘ C) {n : ℕ} {z : Fin n → ComplexVec4}
    (hz : z ∈ diffCoordsInTube n) :
    inner ℂ Ω (stateVector E Ω A n z) =
      vacuumExpectation E Ω A n (successiveDiffsOfLength n z) := by
  cases n with
  | zero =>
    change inner ℂ Ω Ω = 1
    rw [inner_self_eq_norm_sq_to_K, h.bdd.norm_vacuum]
    simp
  | succ p =>
    obtain ⟨s, hs, hf⟩ := exists_gapFits_diffCoords hz
    have hf' : GapFits s (imagTimeShift 1) (List.ofFn (successiveDiffs z)) (imagTimeShift 1) :=
      ⟨hs, hf.2.2.1, hf.2.2.1, hf.2.2.2⟩
    rw [h.stateVector_eq_chainProd hf]
    change _ = vacuumExpectation E Ω A (p + 1) (successiveDiffs z)
    rw [h.vacuumExpectation_eq_chainProd rfl hf']
    exact h.inner_vacuum_chainProd hf.2.1 hf.2.2.1 _
theorem inner_apply_eq_inner_star (X : BddOp K) (χ χ' : K) :
    inner ℂ (X χ) χ' = inner ℂ χ (star X χ') := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
theorem Hyps.conj_vacuumExpectation (h : Hyps E Ω A ℘ C) {p : ℕ} {ζ : Fin p → ComplexVec4}
    (hζ : ζ ∈ tubeTuples p) :
    (starRingEnd ℂ) (vacuumExpectation E Ω A (p + 1) ζ) =
      vacuumExpectation E Ω A (p + 1) (reflectTuple ζ) := by
  obtain ⟨s, hs, hm⟩ := exists_gap_le (imagTimeShift 1 :: List.ofFn ζ) (by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact imagTimeShift_one_mem
    · exact mem_futureTube_of_mem_ofFn hζ x hx)
  have hf : GapFits s (imagTimeShift 1) (List.ofFn ζ) (imagTimeShift 1) :=
    gapFits_of_le hs (hm _ (by simp)) (hm _ (by simp)) fun x hx => hm x (by simp [hx])
  have hr := gapFits_reflect hf
  rw [neg_conjPoint_imagTimeShift] at hr
  rw [h.vacuumExpectation_eq_chainProd rfl hf,
    h.vacuumExpectation_eq_chainProd (ζ := reflectTuple ζ) (ofFn_reflectTuple ζ) hr,
    inner_conj_symm, inner_apply_eq_inner_star, h.star_chainProd hf, neg_conjPoint_imagTimeShift]
theorem Hyps.expectationConj (h : Hyps E Ω A ℘ C) : ExpectationConj E Ω A := by
  intro n ζ hζ
  cases n with
  | zero => simp [vacuumExpectation]
  | succ p => exact h.conj_vacuumExpectation hζ
theorem conjPoint_apply_eq_conj (ζ : ComplexVec4) (μ : Fin 4) :
    MinkowskiSpace.conjPoint ζ μ = (starRingEnd ℂ) (ζ μ) := by apply _root_.YangMills.Construction.FieldFormTranslations.conjPoint_coord <;> assumption
theorem successiveDiffs_conj_rev {q : ℕ} (w : Fin (q + 1) → ComplexVec4) :
    successiveDiffs (fun k => MinkowskiSpace.conjPoint (w (Fin.rev k))) =
      reflectTuple (successiveDiffs w) := by
  funext i μ
  simp only [successiveDiffs, reflectTuple, Fin.rev_succ, Fin.rev_castSucc, Pi.sub_apply,
    Pi.neg_apply, conjPoint_apply_eq_conj, map_sub]
  abel
def diffList : List ComplexVec4 → List ComplexVec4
  | [] => []
  | [_] => []
  | x :: y :: l => (y - x) :: diffList (y :: l)
theorem ofFn_successiveDiffs {M : ℕ} (y : Fin (M + 1) → ComplexVec4) :
    List.ofFn (successiveDiffs y) = diffList (List.ofFn y) := by
  induction M with
  | zero => simp [List.ofFn_succ, diffList]
  | succ M ih =>
    have e : (fun i : Fin M => successiveDiffs y i.succ) = successiveDiffs fun i => y i.succ := by
      funext i
      simp only [successiveDiffs]
      rw [Fin.succ_castSucc]
    rw [List.ofFn_succ (f := successiveDiffs y), e, ih, List.ofFn_succ (f := y),
      List.ofFn_succ (f := fun i : Fin (M + 1) => y i.succ)]
    rfl
theorem diffList_append_cons_cons (l : List ComplexVec4) (u v : ComplexVec4)
    (r : List ComplexVec4) :
    diffList (l ++ u :: v :: r) =
      diffList (l ++ [u]) ++ (v - u) :: diffList (v :: r) := by
  induction l with
  | nil => simp [diffList]
  | cons x l ih =>
    cases l with
    | nil => simp [diffList]
    | cons y l => simpa [diffList] using ih
theorem stateVector_zero (z : Fin 0 → ComplexVec4) : stateVector E Ω A 0 z = Ω := rfl
theorem successiveDiffsOfLength_succ {p : ℕ} (z : Fin (p + 1) → ComplexVec4) :
    successiveDiffsOfLength (p + 1) z = successiveDiffs z := rfl
theorem Hyps.inner_stateVector_stateVector (h : Hyps E Ω A ℘ C) {n n' : ℕ}
    {z : Fin n → ComplexVec4} {w : Fin n' → ComplexVec4} (hz : z ∈ diffCoordsInTube n)
    (hw : w ∈ diffCoordsInTube n') {N : ℕ} (y : Fin N → ComplexVec4)
    (hy : List.ofFn y = List.ofFn (fun k => MinkowskiSpace.conjPoint (w (Fin.rev k))) ++
      List.ofFn z) :
    inner ℂ (stateVector E Ω A n' w) (stateVector E Ω A n z) =
      vacuumExpectation E Ω A N (successiveDiffsOfLength N y) := by
  cases n' with
  | zero =>
    have e : List.ofFn (fun k : Fin 0 => MinkowskiSpace.conjPoint (w (Fin.rev k))) = [] := by simp
    rw [e, List.nil_append] at hy
    have hN : N = n := by simpa using congrArg List.length hy
    subst hN
    obtain rfl : y = z := List.ofFn_injective hy
    exact h.inner_vacuum_stateVector hz
  | succ q =>
    cases n with
    | zero =>
      have e : List.ofFn z = [] := by simp
      rw [e, List.append_nil] at hy
      have hN : N = q + 1 := by simpa using congrArg List.length hy
      subst hN
      obtain rfl := List.ofFn_injective hy
      have hconj := h.expectationConj (q + 1) (successiveDiffs w) (by
        intro k _
        exact hw k.succ (Set.mem_univ _))
      have hv := h.inner_vacuum_stateVector hw
      rw [successiveDiffsOfLength_succ, successiveDiffs_conj_rev, stateVector_zero, ← hconj,
        ← successiveDiffsOfLength_succ w, ← hv, inner_conj_symm]
    | succ p =>
      have hN : N = (q + 1 + p) + 1 := by
        have := congrArg List.length hy
        simp at this
        omega
      subst hN
      rw [successiveDiffsOfLength_succ]
      obtain ⟨s, hs, hm⟩ := exists_gap_le
        (imagTimeShift 1 :: (List.ofFn (diffCoords w) ++ List.ofFn (diffCoords z))) (by
        intro x hx
        simp only [List.mem_cons, List.mem_append] at hx
        rcases hx with rfl | hx | hx
        · exact imagTimeShift_one_mem
        · exact mem_futureTube_of_mem_ofFn hw x hx
        · exact mem_futureTube_of_mem_ofFn hz x hx)
      have h₁ := hm _ (List.mem_cons_self)
      have hfw : GapFits s (w 0) (List.ofFn (successiveDiffs w)) (imagTimeShift 1) :=
        gapFits_diffCoords hs h₁ fun x hx => hm x (by simp only [List.mem_cons, List.mem_append]; tauto)
      have hfz : GapFits s (z 0) (List.ofFn (successiveDiffs z)) (imagTimeShift 1) :=
        gapFits_diffCoords hs h₁ fun x hx => hm x (by simp only [List.mem_cons, List.mem_append]; tauto)
      have hw₀ : 2 * s ≤ tubeGap (w 0) :=
        hm _ (by
          simp only [List.mem_cons, List.mem_append]
          exact Or.inr (Or.inl (mem_ofFn_apply (diffCoords w) 0)))
      have hz₀ : 2 * s ≤ tubeGap (z 0) :=
        hm _ (by
          simp only [List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr (mem_ofFn_apply (diffCoords z) 0)))
      have hsum : 2 * s ≤ tubeGap (-MinkowskiSpace.conjPoint (w 0) + z 0) := by
        have := h.tubeGap_add (-MinkowskiSpace.conjPoint (w 0)) (z 0)
        rw [tubeGap_neg_conjPoint] at this
        linarith
      have hfr := gapFits_reflect hfw
      rw [neg_conjPoint_imagTimeShift] at hfr
      have hj : GapFits s (imagTimeShift 1) (reflectList (List.ofFn (successiveDiffs w)) ++
          (-MinkowskiSpace.conjPoint (w 0) + z 0) :: List.ofFn (successiveDiffs z))
          (imagTimeShift 1) := by
        refine ⟨hs, hfr.2.1, hfz.2.2.1, fun m hm' => ?_⟩
        simp only [List.mem_append, List.mem_cons] at hm'
        rcases hm' with hm' | rfl | hm'
        · exact hfr.2.2.2 m hm'
        · exact hsum
        · exact hfz.2.2.2 m hm'
      have hW : List.ofFn (fun k => MinkowskiSpace.conjPoint (w (Fin.rev k))) =
          List.ofFn (fun i : Fin q => MinkowskiSpace.conjPoint (w (Fin.rev i.castSucc))) ++
            [MinkowskiSpace.conjPoint (w 0)] := by
        rw [List.ofFn_succ']
        simp [List.concat_eq_append, Fin.rev_last]
      have hZ : List.ofFn z = z 0 :: List.ofFn (fun i : Fin p => z i.succ) := by
        rw [List.ofFn_succ]
      have e₁ : diffList (List.ofFn fun k => MinkowskiSpace.conjPoint (w (Fin.rev k))) =
          reflectList (List.ofFn (successiveDiffs w)) := by
        rw [← ofFn_successiveDiffs, successiveDiffs_conj_rev, ofFn_reflectTuple]
      have e₂ : diffList (List.ofFn z) = List.ofFn (successiveDiffs z) :=
        (ofFn_successiveDiffs z).symm
      have hl : List.ofFn (successiveDiffs y) = reflectList (List.ofFn (successiveDiffs w)) ++
          (-MinkowskiSpace.conjPoint (w 0) + z 0) :: List.ofFn (successiveDiffs z) := by
        have e₃ : List.ofFn (fun k => MinkowskiSpace.conjPoint (w (Fin.rev k))) ++ List.ofFn z =
            List.ofFn (fun i : Fin q => MinkowskiSpace.conjPoint (w (Fin.rev i.castSucc))) ++
              MinkowskiSpace.conjPoint (w 0) :: z 0 :: List.ofFn (fun i : Fin p => z i.succ) := by
          rw [hW, hZ]
          simp
        rw [ofFn_successiveDiffs, hy, e₃, diffList_append_cons_cons, ← hW, ← hZ, e₁, e₂,
          sub_eq_neg_add]
      have hprod : star (chainProd E A s (w 0) (List.ofFn (successiveDiffs w))
            (imagTimeShift 1)) *
          chainProd E A s (z 0) (List.ofFn (successiveDiffs z)) (imagTimeShift 1) =
          chainProd E A s (imagTimeShift 1) (reflectList (List.ofFn (successiveDiffs w)) ++
            (-MinkowskiSpace.conjPoint (w 0) + z 0) :: List.ofFn (successiveDiffs z))
            (imagTimeShift 1) := by
        rw [h.star_chainProd hfw, neg_conjPoint_imagTimeShift,
          h.chainProd_mul_chainProd hfr.2.2.1 hfz.2.1]
      rw [h.vacuumExpectation_eq_chainProd (p := q + 1 + p) hl hj, h.stateVector_eq_chainProd hfw,
        h.stateVector_eq_chainProd hfz, inner_apply_eq_inner_star, ← hprod]
      rfl
theorem Hyps.statesTranslateInner (h : Hyps E Ω A ℘ C) :
    StatesTranslateInner E Ω A := by
  intro n n' z w ω hz hw hω
  refine ⟨h.spectralTranslation_stateVector hz hω, h.inner_vacuum_stateVector hz, ?_⟩
  exact h.inner_stateVector_stateVector hz hw _ (List.ofFn_fin_append _ _)
end FieldProductProof
theorem FieldProductProperties.of_translations
    (hT : FieldFormTranslations.TranslationOperatorFacts)
    (hC : MinkowskiSpace.ConeTubeLorentz.Statement)
    (hP : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    FieldProductProperties := by
  intro K _ _ _ E Ω A ℘ C hF
  obtain ⟨hc, hl, hm⟩ := hT K E Ω A ℘ C hF
  have h : FieldProductProof.Hyps E Ω A ℘ C :=
    ⟨hF, hc, hl, hm, hC.1.2.1, hC.2.1.2.2.2.2.2.2, hP⟩
  exact ⟨h.fieldProductIndepOfGap, h.fieldProductTranslateEnds, h.fieldProductMulJoin,
    h.fieldProductAdjoint, h.stateIndepOfLast, h.fieldProductNormBound,
    h.fieldProductHolomorphic, h.expectationsStatesHolomorphic,
    h.expectationsStatesBounded, h.statesTranslateInner,
    h.expectationConj⟩
end YangMills.Construction.FieldForms
