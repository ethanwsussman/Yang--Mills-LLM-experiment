import YangMills.Construction.InfiniteLattice.FactsOfTheSignsAtACutoffProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.TorusOrFourSpace.ChartsOfAnAdmissibleFamily
import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.SmallFactsOnLiftsProductsAndDistributions
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefinedProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.AdmissibleCharts
section IsoMatchSection
open MetricNotions
variable {X Y : Type*}
structure DistLike (d : X → X → ℝ) : Prop where
  refl : ∀ x, d x x = 0
  eq_of_eq_zero : ∀ x y, d x y = 0 → x = y
  nonneg : ∀ x y, 0 ≤ d x y
  comm : ∀ x y, d x y = d y x
  tri : ∀ x y z, d x z ≤ d x y + d y z
structure IsoMatch (d : X → X → ℝ) (d' : Y → Y → ℝ) (A : Set X) (B : Set Y) (f : X → Y)
    (g : Y → X) : Prop where
  mapsTo : ∀ a ∈ A, f a ∈ B
  mapsFrom : ∀ b ∈ B, g b ∈ A
  inv_left : ∀ a ∈ A, g (f a) = a
  inv_right : ∀ b ∈ B, f (g b) = b
  dist_eq : ∀ a ∈ A, ∀ a' ∈ A, d' (f a) (f a') = d a a'
variable {d : X → X → ℝ} {d' : Y → Y → ℝ} {A : Set X} {B : Set Y} {f : X → Y} {g : Y → X}
theorem IsoMatch.symm (h : IsoMatch d d' A B f g) : IsoMatch d' d B A g f where
  mapsTo := h.mapsFrom
  mapsFrom := h.mapsTo
  inv_left := h.inv_right
  inv_right := h.inv_left
  dist_eq b hb b' hb' := by
    rw [← h.dist_eq _ (h.mapsFrom b hb) _ (h.mapsFrom b' hb'), h.inv_right b hb, h.inv_right b' hb']
theorem IsoMatch.image_eq_inter_preimage (h : IsoMatch d d' A B f g) {K : Set Y} (hK : K ⊆ B) :
    g '' K = A ∩ f ⁻¹' K := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨h.mapsFrom k (hK hk), by simpa [h.inv_right k (hK hk)] using hk⟩
  · rintro ⟨hx, hk⟩
    exact ⟨f x, hk, h.inv_left x hx⟩
theorem IsoMatch.isCompactWrt_image (h : IsoMatch d d' A B f g) (hA : IsOpenWrt d A)
    {Z : Set X} (hZA : Z ⊆ A) (hZ : IsCompactWrt d Z) : IsCompactWrt d' (f '' Z) := by
  intro 𝒰 h𝒰 hcov
  have hopen : ∀ V ∈ (fun U => A ∩ f ⁻¹' U) '' 𝒰, IsOpenWrt d V := by
    rintro _ ⟨U, hU, rfl⟩ a ⟨haA, haU⟩
    obtain ⟨r, hr, hball⟩ := h𝒰 U hU (f a) haU
    obtain ⟨r', hr', hball'⟩ := hA a haA
    refine ⟨min r r', lt_min hr hr', fun y hy => ?_⟩
    have hyA := hball' y (lt_of_lt_of_le hy (min_le_right _ _))
    refine ⟨hyA, hball _ ?_⟩
    rw [h.dist_eq a haA y hyA]
    exact lt_of_lt_of_le hy (min_le_left _ _)
  have hcov' : Z ⊆ ⋃₀ ((fun U => A ∩ f ⁻¹' U) '' 𝒰) := by
    intro a ha
    obtain ⟨U, hU, hfa⟩ := hcov ⟨a, ha, rfl⟩
    exact ⟨_, ⟨U, hU, rfl⟩, hZA ha, hfa⟩
  obtain ⟨𝒱, h𝒱, hfin, hsub⟩ := hZ _ hopen hcov'
  obtain ⟨t, ht, htfin, hsub'⟩ :=
    (Set.exists_subset_image_finite_and (p := fun s => Z ⊆ ⋃₀ s)).1 ⟨𝒱, h𝒱, hfin, hsub⟩
  refine ⟨t, ht, htfin, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, _, hfa⟩ := hsub' ha
  exact ⟨U, hU, hfa⟩
theorem subset_closureWrt (hd : DistLike d) (S : Set X) : S ⊆ closureWrt d S :=
  fun x hx r hr => ⟨x, hx, by rwa [hd.refl]⟩
theorem closureWrt_mono {S S' : Set X} (h : S ⊆ S') : closureWrt d S ⊆ closureWrt d S' := by apply _root_.YangMills.Construction.AtCutoff.SignFacts.closureWrt_mono <;> assumption
theorem isOpenWrt_compl_closureWrt (hd : DistLike d) (S : Set X) :
    IsOpenWrt d (closureWrt d S)ᶜ := by
  intro x hx
  have hx' : ∃ r : ℝ, 0 < r ∧ ∀ y ∈ S, r ≤ d x y := by
    by_contra hcon
    push Not at hcon
    exact hx fun r hr => hcon r hr
  obtain ⟨r, hr, hS⟩ := hx'
  refine ⟨r / 2, by positivity, fun y hy hcl => ?_⟩
  obtain ⟨w, hw, hyw⟩ := hcl (r / 2) (by positivity)
  have := hd.tri x y w
  have := hS w hw
  linarith
theorem closureWrt_subset_of_isCompactWrt (hd : DistLike d) {Z : Set X}
    (hZ : IsCompactWrt d Z) : closureWrt d Z ⊆ Z := by
  intro x hx
  by_contra hxZ
  have hopen : ∀ U ∈ {U : Set X | ∃ r : ℝ, 0 < r ∧ U = {y | r < d x y}}, IsOpenWrt d U := by
    rintro _ ⟨r, hr, rfl⟩ y hy
    refine ⟨d x y - r, sub_pos.2 hy, fun y' hy' => ?_⟩
    have := hd.tri x y' y
    have h2 := hd.comm y' y
    simp only [Set.mem_ofPred_eq]
    linarith
  have hcov : Z ⊆ ⋃₀ {U : Set X | ∃ r : ℝ, 0 < r ∧ U = {y | r < d x y}} := by
    intro y hy
    have hne : d x y ≠ 0 := fun h0 => hxZ (by rwa [hd.eq_of_eq_zero x y h0])
    have hpos : 0 < d x y := lt_of_le_of_ne (hd.nonneg x y) (Ne.symm hne)
    exact ⟨_, ⟨d x y / 2, by positivity, rfl⟩, by simp only [Set.mem_ofPred_eq]; linarith⟩
  obtain ⟨𝒰', h𝒰', hfin, hsub⟩ := hZ _ hopen hcov
  have key : ∀ S : Set (Set X), S.Finite →
      S ⊆ {U : Set X | ∃ r : ℝ, 0 < r ∧ U = {y | r < d x y}} →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ U ∈ S, ∀ y ∈ U, ρ < d x y := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨1, one_pos, by simp⟩
    | @insert U S _ _ ih =>
      intro hsub'
      obtain ⟨ρ, hρ, h⟩ := ih fun V hV => hsub' (Set.mem_insert_of_mem _ hV)
      obtain ⟨r, hr, rfl⟩ := hsub' (Set.mem_insert _ _)
      refine ⟨min ρ r, lt_min hρ hr, ?_⟩
      rintro V (rfl | hV) y hy
      · exact lt_of_le_of_lt (min_le_right _ _) hy
      · exact lt_of_le_of_lt (min_le_left _ _) (h V hV y hy)
  obtain ⟨ρ, hρ, h⟩ := key 𝒰' hfin h𝒰'
  obtain ⟨y, hy, hxy⟩ := hx ρ hρ
  obtain ⟨U, hU, hyU⟩ := hsub hy
  have := h U hU y hyU
  linarith
theorem IsoMatch.closureWrt_support_eq (h : IsoMatch d d' A B f g) (hd : DistLike d)
    (hd' : DistLike d') (hB : IsOpenWrt d' B) {Φ : X → ℂ} {Ψ : Y → ℂ}
    (hon : ∀ a ∈ A, Φ a = Ψ (f a)) (hoff : ∀ x, x ∉ A → Φ x = 0)
    (hK : IsCompactWrt d' (closureWrt d' {y | Ψ y ≠ 0}))
    (hKB : closureWrt d' {y | Ψ y ≠ 0} ⊆ B) :
    closureWrt d {x | Φ x ≠ 0} = g '' closureWrt d' {y | Ψ y ≠ 0} := by
  have hcomp := h.symm.isCompactWrt_image hB hKB hK
  apply Set.Subset.antisymm
  · refine (closureWrt_mono ?_).trans (closureWrt_subset_of_isCompactWrt hd hcomp)
    intro x hx
    have hxA : x ∈ A := by
      by_contra hxA
      exact hx (hoff x hxA)
    refine ⟨f x, subset_closureWrt hd' _ ?_, h.inv_left x hxA⟩
    simpa [← hon x hxA] using hx
  · rintro _ ⟨k, hk, rfl⟩ r hr
    obtain ⟨y, hy, hky⟩ := hk r hr
    have hyB : y ∈ B := hKB (subset_closureWrt hd' _ hy)
    refine ⟨g y, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      rw [hon _ (h.mapsFrom y hyB), h.inv_right y hyB]
      exact hy
    · rw [h.symm.dist_eq k (hKB hk) y hyB]
      exact hky
end IsoMatchSection
section Translates
variable {p : ℕ+}
def LocallyTranslate (T : Set (Set (Coords p) × Coords p)) (Z : Set (Coords p))
    (G G' : Coords p → ℂ) : Prop :=
  (∀ t ∈ T, ∀ x ∈ t.1, G x = G' (x + t.2)) ∧ ∀ x ∈ Z, G x = 0
variable {T : Set (Set (Coords p) × Coords p)} {Z : Set (Coords p)}
theorem eventuallyEq_translate {G G' : Coords p → ℂ} {U : Set (Coords p)}
    {w x : Coords p} (hU : IsOpen U) (hx : x ∈ U) (h : ∀ x ∈ U, G x = G' (x + w)) :
    G =ᶠ[𝓝 x] fun x => G' (x + w) :=
  Filter.eventually_of_mem (hU.mem_nhds hx) h
theorem eventuallyEq_zero {G : Coords p → ℂ} {x : Coords p} (hZ : IsOpen Z) (hx : x ∈ Z)
    (h : ∀ x ∈ Z, G x = 0) : G =ᶠ[𝓝 x] fun _ => 0 :=
  Filter.eventually_of_mem (hZ.mem_nhds hx) h
theorem lineDeriv_comp_add_const (G' : Coords p → ℂ) (w x v : Coords p) :
    lineDeriv ℝ (fun x => G' (x + w)) x v = lineDeriv ℝ G' (x + w) v := by
  have h : (fun t : ℝ => G' (x + t • v + w)) = fun t : ℝ => G' (x + w + t • v) := by
    funext t
    rw [add_right_comm]
  simp only [lineDeriv, h]
theorem lineDifferentiableAt_comp_add_const {G' : Coords p → ℂ} {w x v : Coords p}
    (h : LineDifferentiableAt ℝ G' (x + w) v) :
    LineDifferentiableAt ℝ (fun x => G' (x + w)) x v := by
  unfold LineDifferentiableAt at h ⊢
  have : (fun t : ℝ => G' (x + t • v + w)) = fun t : ℝ => G' (x + w + t • v) := by
    funext t
    rw [add_right_comm]
  simpa [this] using h
theorem LocallyTranslate.partialAlong (hT : ∀ t ∈ T, IsOpen t.1) (hZ : IsOpen Z)
    {G G' : Coords p → ℂ} (h : LocallyTranslate T Z G G') (j : Fin (4 * (p : ℕ))) :
    LocallyTranslate T Z (Coords.partialAlong j G) (Coords.partialAlong j G') := by
  constructor
  · intro t ht x hx
    have := (eventuallyEq_translate (hT t ht) hx (h.1 t ht)).lineDeriv_eq (𝕜 := ℝ)
      (v := Pi.single j 1)
    simp only [Coords.partialAlong]
    rw [this, lineDeriv_comp_add_const]
  · intro x hx
    have := (eventuallyEq_zero hZ hx h.2).lineDeriv_eq (𝕜 := ℝ) (v := Pi.single j 1)
    simp only [Coords.partialAlong]
    rw [this]
    simp [lineDeriv]
theorem LocallyTranslate.iterPartial (hT : ∀ t ∈ T, IsOpen t.1) (hZ : IsOpen Z)
    {G G' : Coords p → ℂ} (h : LocallyTranslate T Z G G') (α : CoordIndex p) :
    LocallyTranslate T Z (Coords.iterPartial α G) (Coords.iterPartial α G') := by
  unfold Coords.iterPartial
  induction List.finRange (4 * (p : ℕ)) with
  | nil => exact h
  | cons j l ih =>
    simp only [List.foldr_cons]
    generalize l.foldr (fun j H => (Coords.partialAlong j)^[α j] H) G = A at ih
    generalize l.foldr (fun j H => (Coords.partialAlong j)^[α j] H) G' = B at ih
    induction α j generalizing A B with
    | zero => exact ih
    | succ k ihk =>
      simp only [Function.iterate_succ, Function.comp]
      exact ihk _ _ (ih.partialAlong hT hZ j)
theorem LocallyTranslate.contPartialsUpTo (hT : ∀ t ∈ T, IsOpen t.1) (hZ : IsOpen Z)
    (hcov : ∀ x, x ∈ Z ∨ ∃ t ∈ T, x ∈ t.1) (ν : ℕ) {G G' : Coords p → ℂ}
    (h : LocallyTranslate T Z G G') (hG' : Coords.ContPartialsUpTo ν G') :
    Coords.ContPartialsUpTo ν G := by
  have hcont : ∀ {G G' : Coords p → ℂ}, LocallyTranslate T Z G G' → Continuous G' →
      Continuous G := by
    intro G G' h hc
    refine continuous_iff_continuousAt.2 fun x => ?_
    rcases hcov x with hx | ⟨t, ht, hx⟩
    · exact (continuousAt_const).congr (eventuallyEq_zero hZ hx h.2).symm
    · have : ContinuousAt (fun x => G' (x + t.2)) x := by fun_prop
      exact this.congr (eventuallyEq_translate (hT t ht) hx (h.1 t ht)).symm
  induction ν generalizing G G' with
  | zero => exact hcont h hG'
  | succ ν ih =>
    refine ⟨hcont h hG'.1, fun j => ⟨fun x => ?_, ih (h.partialAlong hT hZ j) (hG'.2 j).2⟩⟩
    rcases hcov x with hx | ⟨t, ht, hx⟩
    · have h0 : LineDifferentiableAt ℝ (fun _ : Coords p => (0 : ℂ)) x (Pi.single j 1) := by
        unfold LineDifferentiableAt
        exact differentiableAt_const _
      exact h0.congr_of_eventuallyEq (eventuallyEq_zero hZ hx h.2)
    · exact (lineDifferentiableAt_comp_add_const ((hG'.2 j).1 _)).congr_of_eventuallyEq
        (eventuallyEq_translate (hT t ht) hx (h.1 t ht))
end Translates
open Tuple
open TorusMetric (euclidNormVec)
section EuclidNorm
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_add_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v + w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem euclidNormVec_sub_comm (v w : Fin 4 → ℝ) :
    euclidNormVec (v - w) = euclidNormVec (w - v) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem euclidNormVec_zero : euclidNormVec 0 = 0 := by simp [euclidNormVec]
theorem eq_zero_of_euclidNormVec_eq_zero {v : Fin 4 → ℝ} (h : euclidNormVec v = 0) : v = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.eq_zero_of_euclidNormVec_eq_zero <;> assumption
theorem euclidNormVec_single_zero (τ : ℝ) (hτ : 0 ≤ τ) :
    euclidNormVec (Pi.single 0 τ) = τ := by
  simp [euclidNormVec, Fin.sum_univ_four, Real.sqrt_sq hτ]
end EuclidNorm
section Chart
variable (D : Params) (E : Kind) {n : ℕ+}
theorem quotDist_euclidean (hF : LiftsProductsDistributions.Statement) (u u' : euclidean.Pt D) :
    Kind.quotDist D euclidean u u' = euclidNormVec (u - u') := by
  refine ((hF D euclidean).1 u u').2 ?_
  have : 2 * periodQuarter D euclidean = ⊤ := ENNReal.mul_top two_ne_zero
  rw [this]
  exact ENNReal.ofReal_lt_top
theorem translateChart_zero (z : Fin 4 → ℝ) : translateChart D E z 0 = E.quotMap D z := by
  show E.quotMap D (z + 0) = _
  rw [add_zero]
theorem translateChart_sub (z x : Fin 4 → ℝ) :
    translateChart D E z (show euclidean.Pt D from x - z) = E.quotMap D x := by
  show E.quotMap D (z + (x - z)) = _
  rw [add_sub_cancel]
theorem quotDist_add_add_le (hF : LiftsProductsDistributions.Statement) (z u u' : Fin 4 → ℝ) :
    Kind.quotDist D E (E.quotMap D (z + u)) (E.quotMap D (z + u')) ≤
      euclidNormVec (u - u') := by
  have := ((hF D E).1 (z + u) (z + u')).1
  rwa [add_sub_add_left_eq_sub] at this
theorem quotDist_translateChart_le (hF : LiftsProductsDistributions.Statement) (z : Fin 4 → ℝ)
    (u u' : euclidean.Pt D) :
    Kind.quotDist D E (translateChart D E z u) (translateChart D E z u') ≤
      euclidNormVec (u - u') :=
  quotDist_add_add_le D E hF z u u'
theorem quotDist_add_add_eq (hF : LiftsProductsDistributions.Statement) (z u u' : Fin 4 → ℝ)
    (hu : ENNReal.ofReal (euclidNormVec u) < periodQuarter D E)
    (hu' : ENNReal.ofReal (euclidNormVec u') < periodQuarter D E) :
    Kind.quotDist D E (E.quotMap D (z + u)) (E.quotMap D (z + u')) =
      euclidNormVec (u - u') := by
  have h := ((hF D E).1 (z + u) (z + u')).2
  rw [add_sub_add_left_eq_sub] at h
  refine h ?_
  have h1 : euclidNormVec (u - u') ≤ euclidNormVec u + euclidNormVec u' := by
    have := euclidNormVec_add_le u (-u')
    rwa [euclidNormVec_neg, ← sub_eq_add_neg] at this
  calc ENNReal.ofReal (euclidNormVec (u - u'))
      ≤ ENNReal.ofReal (euclidNormVec u + euclidNormVec u') := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal (euclidNormVec u) + ENNReal.ofReal (euclidNormVec u') :=
        ENNReal.ofReal_add (euclidNormVec_nonneg _) (euclidNormVec_nonneg _)
    _ < periodQuarter D E + periodQuarter D E := ENNReal.add_lt_add hu hu'
    _ = 2 * periodQuarter D E := (two_mul _).symm
theorem quotDist_translateChart (hF : LiftsProductsDistributions.Statement) (z : Fin 4 → ℝ)
    (u u' : euclidean.Pt D)
    (hu : ENNReal.ofReal (euclidNormVec u) < periodQuarter D E)
    (hu' : ENNReal.ofReal (euclidNormVec u') < periodQuarter D E) :
    Kind.quotDist D E (translateChart D E z u) (translateChart D E z u') =
      euclidNormVec (u - u') :=
  quotDist_add_add_eq D E hF z u u' hu hu'
theorem ofReal_quotDist_le_setDiam {S : Set (E.Pt D)} {y y' : E.Pt D} (hy : y ∈ S)
    (hy' : y' ∈ S) : ENNReal.ofReal (Kind.quotDist D E y y') ≤ setDiam D E S :=
  le_iSup₂_of_le y hy (le_iSup₂_of_le y' hy' le_rfl)
theorem setDiam_le_maxMemberDiam (G : Fin (n : ℕ) → Set (E.Pt D)) (i : Fin (n : ℕ)) :
    setDiam D E (G i) ≤ maxMemberDiam D E G :=
  Finset.le_sup' (fun i => setDiam D E (G i)) (Finset.mem_univ i)
theorem maxMemberDiam_le {R d : ℝ} {G : Fin (n : ℕ) → Set (E.Pt D)}
    (hG : AdmissibleWith D E R d G) : maxMemberDiam D E G ≤ ENNReal.ofReal (2 * R) :=
  Finset.sup'_le _ _ fun i _ => hG.diam_le i
theorem maxMemberDiam_lt_periodQuarter {R d : ℝ} {G : Fin (n : ℕ) → Set (E.Pt D)}
    (hG : AdmissibleWith D E R d G) : maxMemberDiam D E G < periodQuarter D E := by
  cases E with
  | euclidean => exact lt_of_le_of_lt (maxMemberDiam_le D euclidean hG) ENNReal.ofReal_lt_top
  | torus => exact (Finset.sup'_lt_iff _).2 fun i _ => hG.diam_lt_quarter_of_torus rfl i
theorem maxMemberDiam_pos (hF : LiftsProductsDistributions.Statement) {R d : ℝ}
    {G : Fin (n : ℕ) → Set (E.Pt D)}
    {z : Fin (n : ℕ) → Fin 4 → ℝ} (hG : AdmissibleWith D E R d G)
    (hz : ∀ i, E.quotMap D (z i) ∈ G i) : 0 < maxMemberDiam D E G := by
  let i : Fin (n : ℕ) := ⟨0, n.pos⟩
  obtain ⟨r₀, hr₀, hball⟩ := hG.isOpen_mem i _ (hz i)
  have hρ : 0 < periodQuarter D E := lt_of_le_of_lt zero_le (maxMemberDiam_lt_periodQuarter D E hG)
  have hmin : 0 < min (ENNReal.ofReal r₀) (periodQuarter D E) :=
    lt_min (ENNReal.ofReal_pos.2 hr₀) hρ
  obtain ⟨c, hc0, hc1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hmin
  have hτ : 0 < (c : ℝ) := by exact_mod_cast hc0
  have hc2 : (c : ℝ) < r₀ := by
    have := lt_of_lt_of_le hc1 (min_le_left _ _)
    exact (ENNReal.ofReal_lt_ofReal_iff hr₀).1 (by simpa using this)
  have hc3 : ENNReal.ofReal (c : ℝ) < periodQuarter D E := by
    simpa using lt_of_lt_of_le hc1 (min_le_right _ _)
  let e : euclidean.Pt D := (Pi.single 0 (c : ℝ) : Fin 4 → ℝ)
  have hv : euclidNormVec e = c := euclidNormVec_single_zero _ hτ.le
  have h0 : ENNReal.ofReal (euclidNormVec (0 : euclidean.Pt D)) < periodQuarter D E := by
    have : euclidNormVec (0 : euclidean.Pt D) = 0 := euclidNormVec_zero
    simpa [this] using hρ
  have hd : Kind.quotDist D E (translateChart D E (z i) 0) (translateChart D E (z i) e) = c := by
    rw [quotDist_translateChart D E hF _ _ _ h0 (by rwa [hv])]
    have : euclidNormVec ((0 : euclidean.Pt D) - e) = euclidNormVec e := by
      rw [zero_sub]
      exact euclidNormVec_neg _
    rw [this, hv]
  rw [translateChart_zero] at hd
  have hmem := hball (translateChart D E (z i) e) (by rw [hd]; exact hc2)
  have := ofReal_quotDist_le_setDiam D E (hz i) hmem
  rw [hd] at this
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hτ) (this.trans (setDiam_le_maxMemberDiam D E G i))
theorem factorIsometricCharts (hF : LiftsProductsDistributions.Statement) {R d : ℝ}
    {G : Fin (n : ℕ) → Set (E.Pt D)}
    {z : Fin (n : ℕ) → Fin 4 → ℝ} (hG : AdmissibleWith D E R d G)
    (hz : ∀ i, E.quotMap D (z i) ∈ G i) : FactorIsometricCharts D E R z G := by
  have hρ := maxMemberDiam_lt_periodQuarter D E hG
  have hle := maxMemberDiam_le D E hG
  have hpos : 0 < periodQuarter D E := lt_of_le_of_lt zero_le hρ
  refine ⟨maxMemberDiam_pos D E hF hG hz, hle, hρ, fun i => ?_⟩
  have hdiam := setDiam_le_maxMemberDiam D E G i
  have hzero : (0 : euclidean.Pt D) ∈ chartSource D E (z i) (G i) := by
    refine ⟨by simpa [show euclidNormVec (0 : euclidean.Pt D) = 0 from euclidNormVec_zero]
      using hpos, ?_⟩
    show translateChart D E (z i) 0 ∈ G i
    rw [translateChart_zero]
    exact hz i
  have hiso : ∀ u ∈ chartSource D E (z i) (G i), ∀ u' ∈ chartSource D E (z i) (G i),
      Kind.quotDist D E (translateChart D E (z i) u) (translateChart D E (z i) u') =
        euclidNormVec (u - u') :=
    fun u hu u' hu' => quotDist_translateChart D E hF _ _ _ hu.1 hu'.1
  have hsub : chartSource D E (z i) (G i) ⊆
      {u | ENNReal.ofReal (euclidNormVec u) ≤ maxMemberDiam D E G} := by
    intro u hu
    have h1 := hiso u hu 0 hzero
    have h2 : euclidNormVec (u - (0 : euclidean.Pt D)) = euclidNormVec u := by
      rw [sub_zero]
    rw [h2] at h1
    have := ofReal_quotDist_le_setDiam D E hu.2 hzero.2
    rw [h1] at this
    exact this.trans hdiam
  refine ⟨?_, hzero, ⟨fun u hu => hu.2, ?_, ?_⟩, hiso, hsub, ?_, ?_⟩
  · intro u hu
    obtain ⟨r₁, hr₁, hball⟩ := hG.isOpen_mem i _ hu.2
    obtain ⟨c, hc0, hc1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hu.1
    have hc0' : euclidNormVec u < c :=
      (ENNReal.ofReal_lt_coe_iff (euclidNormVec_nonneg _)).1 hc0
    refine ⟨min r₁ (c - euclidNormVec u), lt_min hr₁ (sub_pos.2 hc0'), fun y hy => ?_⟩
    rw [quotDist_euclidean D hF] at hy
    have hy1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 := lt_of_lt_of_le hy (min_le_right _ _)
    refine ⟨?_, hball _ (lt_of_le_of_lt (quotDist_translateChart_le D E hF _ _ _) hy1)⟩
    have h3 : euclidNormVec y ≤ euclidNormVec u + euclidNormVec (u - y) := by
      have h4 : euclidNormVec (u - y) = euclidNormVec (y - u) := euclidNormVec_sub_comm u y
      have h5 : euclidNormVec (u + (y - u)) ≤ euclidNormVec u + euclidNormVec (y - u) :=
        euclidNormVec_add_le u (y - u)
      rw [add_sub_cancel] at h5
      rwa [h4]
    refine lt_of_le_of_lt ?_ hc1
    rw [ENNReal.ofReal_le_coe]
    linarith
  · intro u hu u' hu' h
    have h1 := hiso u hu u' hu'
    have h2 := hiso u' hu' u' hu'
    rw [h] at h1
    rw [h1, sub_self] at h2
    have h3 : euclidNormVec (u - u') = 0 := by
      rw [h2]
      exact euclidNormVec_zero
    exact sub_eq_zero.1 (eq_zero_of_euclidNormVec_eq_zero h3)
  · intro y hy
    obtain ⟨x', hx', hd⟩ := (hF D E).2.1 (z i) y
    have hzmem := hz i
    have hle' : ENNReal.ofReal (euclidNormVec (x' - z i)) ≤ maxMemberDiam D E G := by
      rw [euclidNormVec_sub_comm, hd]
      exact (ofReal_quotDist_le_setDiam D E hzmem hy).trans hdiam
    have hmap := translateChart_sub D E (z i) x'
    rw [show E.quotMap D x' = y from hx'] at hmap
    exact ⟨_, ⟨lt_of_le_of_lt hle' hρ, by rw [hmap]; exact hy⟩, hmap⟩
  · intro u hu
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith [hG.radius_pos])).1 (le_trans hu hle)
  · intro y hy
    have h1 := ofReal_quotDist_le_setDiam D E hy (hz i)
    have hfin : maxMemberDiam D E G ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 (h1.trans hdiam)
end Chart
section Maps
variable (D : Params) (E : Kind) {n : ℕ+}
theorem distLike_tupleDist (hP : TupleFacts.AllFacts) (E : Kind) (p : ℕ+) :
    DistLike (Tuple.tupleDist D E (p := p)) := by
  obtain ⟨h0, h1, h2, h3⟩ := (hP D E p).2.2.1
  exact ⟨fun x => (h1 x x).2 rfl, fun x y => (h1 x y).1, h0, h2, h3⟩
structure ChartData (z : Fin (n : ℕ) → Fin 4 → ℝ) (G : Fin (n : ℕ) → Set (E.Pt D)) : Prop where
  src_open : ∀ i, Kind.IsOpenQ D euclidean (chartSource D E (z i) (G i))
  tgt_open : ∀ i, Kind.IsOpenQ D E (G i)
  bijOn_single : ∀ i, Set.BijOn (translateChart D E (z i)) (chartSource D E (z i) (G i)) (G i)
  dist_single : ∀ i, ∀ u ∈ chartSource D E (z i) (G i), ∀ u' ∈ chartSource D E (z i) (G i),
    Kind.quotDist D E (translateChart D E (z i) u) (translateChart D E (z i) u') =
      euclidNormVec (u - u')
variable {D E} {z : Fin (n : ℕ) → Fin 4 → ℝ} {G : Fin (n : ℕ) → Set (E.Pt D)}
theorem ChartData.bijOn_prodChart (hS : ChartData D E z G) :
    Set.BijOn (prodChart D E z) (chartSources D E z G) (boxSet D E G) := by
  refine ⟨fun u hu i => (hS.bijOn_single i).mapsTo (hu i), ?_, ?_⟩
  · exact fun u hu u' hu' h =>
      funext fun i => (hS.bijOn_single i).injOn (hu i) (hu' i) (congrFun h i)
  · intro y hy
    have h : ∀ i, ∃ u ∈ chartSource D E (z i) (G i), translateChart D E (z i) u = y i :=
      fun i => (hS.bijOn_single i).surjOn (hy i)
    choose u hu hy' using h
    exact ⟨u, hu, funext hy'⟩
theorem ChartData.isoMatch (hS : ChartData D E z G) (hF : LiftsProductsDistributions.Statement) :
    IsoMatch (Tuple.tupleDist D euclidean) (Tuple.tupleDist D E)
      (chartSources D E z G) (boxSet D E G) (prodChart D E z)
      (Function.invFunOn (prodChart D E z) (chartSources D E z G)) where
  mapsTo := hS.bijOn_prodChart.mapsTo
  mapsFrom := hS.bijOn_prodChart.surjOn.mapsTo_invFunOn
  inv_left := hS.bijOn_prodChart.invOn_invFunOn.1
  inv_right := hS.bijOn_prodChart.invOn_invFunOn.2
  dist_eq u hu u' hu' := by
    unfold Tuple.tupleDist
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hS.dist_single i (u i) (hu i) (u' i) (hu' i)
    have h2 := quotDist_euclidean D hF (u i) (u' i)
    show Kind.quotDist D E (translateChart D E (z i) (u i)) (translateChart D E (z i) (u' i)) ^ 2 = _
    rw [h1, h2]
theorem ChartData.isOpenT_chartSources (hS : ChartData D E z G) (hP : TupleFacts.AllFacts) :
    Tuple.IsOpenT D euclidean (chartSources D E z G) :=
  (((hP D euclidean n).2.2.2.2.2.2.2.2.2.2.2.1 _).1 hS.src_open)
theorem ChartData.isOpenT_boxSet (hS : ChartData D E z G) (hP : TupleFacts.AllFacts) :
    Tuple.IsOpenT D E (boxSet D E G) :=
  (((hP D E n).2.2.2.2.2.2.2.2.2.2.2.1 _).1 hS.tgt_open)
theorem isOpen_preimage_proj (hP : TupleFacts.AllFacts) (E : Kind) (Ω : Set (E.Tuple D n))
    (h : Tuple.IsOpenT D E Ω) : IsOpen (Tuple.proj D E ⁻¹' Ω) :=
  ((hP D E n).2.2.2.2.2.2.2.2.1 Ω).1 h
theorem proj_surjective (hP : TupleFacts.AllFacts) (E : Kind) :
    Function.Surjective (Tuple.proj D E (p := n)) := (hP D E n).1.1
theorem exists_coords_lift (D : Params) (hP : TupleFacts.AllFacts) (z : Fin (n : ℕ) → Fin 4 → ℝ) :
    ∃ w : Coords n, ∀ i, w.block i = z i := by
  obtain ⟨x, hx⟩ := proj_surjective (D := D) hP euclidean (n := n) z
  exact ⟨x, fun i => congrFun hx i⟩
theorem prodChart_proj {w : Coords n} (hw : ∀ i, w.block i = z i) (x : Coords n) :
    prodChart D E z (Tuple.proj D euclidean x) = Tuple.proj D E (w + x) := by
  funext i
  show E.quotMap D (z i + x.block i) = E.quotMap D ((w + x).block i)
  rw [← hw i]
  rfl
theorem pullback_of_mem (F : E.Tuple D n → ℂ) {u : euclidean.Tuple D n}
    (hu : u ∈ chartSources D E z G) : pullback D E z G F u = F (prodChart D E z u) :=
  Set.indicator_of_mem hu _
theorem pullback_of_notMem (F : E.Tuple D n → ℂ) {u : euclidean.Tuple D n}
    (hu : u ∉ chartSources D E z G) : pullback D E z G F u = 0 :=
  Set.indicator_of_notMem hu _
theorem pushforward_of_mem (H : euclidean.Tuple D n → ℂ) {y : E.Tuple D n}
    (hy : y ∈ boxSet D E G) : pushforward D E z G H y =
      H (Function.invFunOn (prodChart D E z) (chartSources D E z G) y) :=
  Set.indicator_of_mem hy _
theorem pushforward_of_notMem (H : euclidean.Tuple D n → ℂ) {y : E.Tuple D n}
    (hy : y ∉ boxSet D E G) : pushforward D E z G H y = 0 :=
  Set.indicator_of_notMem hy _
theorem ChartData.pushforward_prodChart (hS : ChartData D E z G) (H : euclidean.Tuple D n → ℂ)
    {u : euclidean.Tuple D n} (hu : u ∈ chartSources D E z G) :
    pushforward D E z G H (prodChart D E z u) = H u := by
  rw [pushforward_of_mem H (hS.bijOn_prodChart.mapsTo hu), hS.bijOn_prodChart.invOn_invFunOn.1 hu]
theorem ChartData.supportT_pullback (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement)
    {F : E.Tuple D n → ℂ} (h : HasCompactSupportWithin D E (boxSet D E G) F) :
    Tuple.supportT D euclidean (pullback D E z G F) =
      Function.invFunOn (prodChart D E z) (chartSources D E z G) '' Tuple.supportT D E F :=
  (hS.isoMatch hF).closureWrt_support_eq (distLike_tupleDist D hP euclidean n)
    (distLike_tupleDist D hP E n) (hS.isOpenT_boxSet hP) (fun _ ha => pullback_of_mem F ha)
    (fun _ hx => pullback_of_notMem F hx) h.1 h.2
theorem ChartData.supportT_pushforward (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement) {H : euclidean.Tuple D n → ℂ}
    (h : HasCompactSupportWithin D euclidean (chartSources D E z G) H) :
    Tuple.supportT D E (pushforward D E z G H) =
      prodChart D E z '' Tuple.supportT D euclidean H :=
  (hS.isoMatch hF).symm.closureWrt_support_eq (distLike_tupleDist D hP E n)
    (distLike_tupleDist D hP euclidean n) (hS.isOpenT_chartSources hP)
    (fun _ ha => pushforward_of_mem H ha) (fun _ hx => pushforward_of_notMem H hx) h.1 h.2
theorem ChartData.isCompactT_invImage (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement)
    {K : Set (E.Tuple D n)} (hK : Tuple.IsCompactT D E K)
    (hKG : K ⊆ boxSet D E G) : Tuple.IsCompactT D euclidean
      (Function.invFunOn (prodChart D E z) (chartSources D E z G) '' K) :=
  (hS.isoMatch hF).symm.isCompactWrt_image (hS.isOpenT_boxSet hP) hKG hK
theorem ChartData.isCompactT_chartImage (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement)
    {K : Set (euclidean.Tuple D n)} (hK : Tuple.IsCompactT D euclidean K)
    (hKO : K ⊆ chartSources D E z G) :
    Tuple.IsCompactT D E (prodChart D E z '' K) :=
  (hS.isoMatch hF).isCompactWrt_image (hS.isOpenT_chartSources hP) hKO hK
theorem ChartData.invImage_subset (hS : ChartData D E z G)
    (hF : LiftsProductsDistributions.Statement) {K : Set (E.Tuple D n)}
    (hKG : K ⊆ boxSet D E G) :
    Function.invFunOn (prodChart D E z) (chartSources D E z G) '' K ⊆ chartSources D E z G := by
  rintro _ ⟨k, hk, rfl⟩
  exact (hS.isoMatch hF).mapsFrom k (hKG hk)
theorem ChartData.chartImage_subset (hS : ChartData D E z G) {K : Set (euclidean.Tuple D n)}
    (hKO : K ⊆ chartSources D E z G) : prodChart D E z '' K ⊆ boxSet D E G := by
  rintro _ ⟨k, hk, rfl⟩
  exact hS.bijOn_prodChart.mapsTo (hKO hk)
theorem ChartData.compactSupport_pullback (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement)
    {F : E.Tuple D n → ℂ} (h : HasCompactSupportWithin D E (boxSet D E G) F) :
    HasCompactSupportWithin D euclidean (chartSources D E z G) (pullback D E z G F) := by
  unfold HasCompactSupportWithin
  rw [hS.supportT_pullback hP hF h]
  exact ⟨hS.isCompactT_invImage hP hF h.1 h.2, hS.invImage_subset hF h.2⟩
theorem ChartData.compactSupport_pushforward (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement) {H : euclidean.Tuple D n → ℂ}
    (h : HasCompactSupportWithin D euclidean (chartSources D E z G) H) :
    HasCompactSupportWithin D E (boxSet D E G) (pushforward D E z G H) := by
  unfold HasCompactSupportWithin
  rw [hS.supportT_pushforward hP hF h]
  exact ⟨hS.isCompactT_chartImage hP hF h.1 h.2, hS.chartImage_subset h.2⟩
theorem eq_zero_of_supportT_subset {E : Kind} {F : E.Tuple D n → ℂ}
    {Ω : Set (E.Tuple D n)} (hP : TupleFacts.AllFacts) (h : Tuple.supportT D E F ⊆ Ω)
    {y : E.Tuple D n} (hy : y ∉ Ω) : F y = 0 := by
  by_contra hne
  exact hy (h (subset_closureWrt (distLike_tupleDist D hP E n) _ hne))
theorem ChartData.pullbackPushforwardInverse (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement) :
    PullbackPushforwardInverse D E z G := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b F F' _ _
    funext u
    by_cases hu : u ∈ chartSources D E z G
    · simp [pullback_of_mem _ hu]
    · simp [pullback_of_notMem _ hu]
  · intro a b H H' _ _
    funext y
    by_cases hy : y ∈ boxSet D E G
    · simp [pushforward_of_mem _ hy]
    · simp [pushforward_of_notMem _ hy]
  · intro F h
    refine ⟨hS.compactSupport_pullback hP hF h, ?_, ?_⟩
    · funext y
      by_cases hy : y ∈ boxSet D E G
      · rw [pushforward_of_mem _ hy,
          pullback_of_mem F ((hS.isoMatch hF).mapsFrom y hy),
          (hS.isoMatch hF).inv_right y hy]
      · rw [pushforward_of_notMem _ hy, eq_zero_of_supportT_subset hP h.2 hy]
    · rw [hS.supportT_pullback hP hF h, (hS.isoMatch hF).image_eq_inter_preimage h.2]
  · intro H h
    refine ⟨hS.compactSupport_pushforward hP hF h, ?_, hS.supportT_pushforward hP hF h⟩
    funext u
    by_cases hu : u ∈ chartSources D E z G
    · rw [pullback_of_mem _ hu, hS.pushforward_prodChart H hu]
    · rw [pullback_of_notMem _ hu, eq_zero_of_supportT_subset hP h.2 hu]
theorem partialDeriv_comp_proj (hP : TupleFacts.AllFacts) (E : Kind) {ν : ℕ}
    {F : E.Tuple D n → ℂ}
    (h : IsClassC D E ν F) {α : CoordIndex n} (hα : α.degree ≤ ν) :
    Tuple.partialDeriv D E α F ∘ Tuple.proj D E =
      Coords.iterPartial α (F ∘ Tuple.proj D E) :=
  ((hP D E n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ν F h α hα).2.1
theorem ChartData.pullback_classC (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement) {ν : ℕ}
    {F : E.Tuple D n → ℂ} (h : HasCompactSupportWithin D E (boxSet D E G) F)
    (hc : IsClassC D E ν F) : IsClassC D euclidean ν (pullback D E z G F) ∧
      ∀ α : CoordIndex n, α.degree ≤ ν →
        Tuple.partialDeriv D euclidean α (pullback D E z G F) =
          pullback D E z G (Tuple.partialDeriv D E α F) := by
  obtain ⟨w, hw⟩ := exists_coords_lift D hP z
  have hsupp := (hS.compactSupport_pullback hP hF h).2
  set π₄ := Tuple.proj D euclidean (p := n) with hπ₄
  set A : Set (Coords n) := π₄ ⁻¹' chartSources D E z G with hA
  set Z : Set (Coords n) :=
    π₄ ⁻¹' (Tuple.supportT D euclidean (pullback D E z G F))ᶜ with hZ
  have hAo : IsOpen A := isOpen_preimage_proj hP euclidean _ (hS.isOpenT_chartSources hP)
  have hZo : IsOpen Z :=
    isOpen_preimage_proj hP euclidean _
      (isOpenWrt_compl_closureWrt (distLike_tupleDist D hP euclidean n) _)
  have hT : ∀ t ∈ ({(A, w)} : Set (Set (Coords n) × Coords n)), IsOpen t.1 := by
    rintro _ rfl
    exact hAo
  have hM : LocallyTranslate {(A, w)} Z (pullback D E z G F ∘ π₄) (F ∘ Tuple.proj D E) := by
    constructor
    · rintro _ rfl x hx
      simp only [Function.comp]
      rw [pullback_of_mem F hx, hπ₄, prodChart_proj hw, add_comm]
    · intro x hx
      by_contra hne
      exact hx (subset_closureWrt (distLike_tupleDist D hP euclidean n) _ hne)
  have hcov : ∀ x, x ∈ Z ∨ ∃ t ∈ ({(A, w)} : Set (Set (Coords n) × Coords n)), x ∈ t.1 := by
    intro x
    by_cases hx : π₄ x ∈ chartSources D E z G
    · exact Or.inr ⟨_, rfl, hx⟩
    · exact Or.inl fun hs => hx (hsupp hs)
  have hclass : IsClassC D euclidean ν (pullback D E z G F) :=
    hM.contPartialsUpTo hT hZo hcov ν hc
  refine ⟨hclass, fun α hα => ?_⟩
  funext u
  obtain ⟨x, rfl⟩ := proj_surjective (D := D) hP euclidean u
  have e1 := congrFun (partialDeriv_comp_proj hP euclidean hclass hα) x
  have e2 := congrFun (partialDeriv_comp_proj hP E hc hα) (x + w)
  have hI := hM.iterPartial hT hZo α
  simp only [Function.comp] at e1 e2
  rw [e1]
  by_cases hx : π₄ x ∈ chartSources D E z G
  · have := hI.1 _ rfl x hx
    simp only at this
    rw [this, pullback_of_mem _ hx, hπ₄, prodChart_proj hw, add_comm w x, e2]
  · rw [pullback_of_notMem _ hx]
    exact hI.2 x fun hs => hx (hsupp hs)
end Maps
section MapsOnTestFns
variable {D : Params} {E : Kind} {n : ℕ+} {z : Fin (n : ℕ) → Fin 4 → ℝ}
  {G : Fin (n : ℕ) → Set (E.Pt D)}
theorem ChartData.pushforward_classC (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement) {ν : ℕ}
    {H : euclidean.Tuple D n → ℂ}
    (h : HasCompactSupportWithin D euclidean (chartSources D E z G) H)
    (hc : IsClassC D euclidean ν H) : IsClassC D E ν (pushforward D E z G H) ∧
      ∀ α : CoordIndex n, α.degree ≤ ν →
        Tuple.partialDeriv D E α (pushforward D E z G H) =
          pushforward D E z G (Tuple.partialDeriv D euclidean α H) := by
  obtain ⟨w, hw⟩ := exists_coords_lift D hP z
  have hsupp := (hS.compactSupport_pushforward hP hF h).2
  set π₄ := Tuple.proj D euclidean (p := n) with hπ₄
  set πE := Tuple.proj D E (p := n) with hπE
  set A : Set (Coords n) := π₄ ⁻¹' chartSources D E z G with hA
  set T : Set (Set (Coords n) × Coords n) :=
    {t | ∃ k ∈ Tuple.periodSet D E n, t = ((fun x => x + (-w + k)) ⁻¹' A, -w + k)} with hTdef
  set Z : Set (Coords n) := πE ⁻¹' (Tuple.supportT D E (pushforward D E z G H))ᶜ with hZ
  have hAo : IsOpen A := isOpen_preimage_proj hP euclidean _ (hS.isOpenT_chartSources hP)
  have hZo : IsOpen Z :=
    isOpen_preimage_proj hP E _ (isOpenWrt_compl_closureWrt (distLike_tupleDist D hP E n) _)
  have hT : ∀ t ∈ T, IsOpen t.1 := by
    rintro _ ⟨k, _, rfl⟩
    exact hAo.preimage (by fun_prop)
  have key : ∀ x, ∀ k ∈ Tuple.periodSet D E n,
      prodChart D E z (π₄ (x + (-w + k))) = πE x := by
    intro x k hk
    rw [hπ₄, prodChart_proj hw]
    refine ((hP D E n).1.2 _ _).2 ?_
    have : w + (x + (-w + k)) - x = k := by abel
    rw [this]
    exact hk
  have hM : LocallyTranslate T Z (pushforward D E z G H ∘ πE) (H ∘ π₄) := by
    constructor
    · rintro _ ⟨k, hk, rfl⟩ x hx
      simp only [Function.comp]
      rw [← key x k hk, hS.pushforward_prodChart H hx]
    · intro x hx
      by_contra hne
      exact hx (subset_closureWrt (distLike_tupleDist D hP E n) _ hne)
  have zone : ∀ x, πE x ∈ boxSet D E G → ∃ t ∈ T, x ∈ t.1 := by
    intro x hx
    have hu := (hS.isoMatch hF).mapsFrom _ hx
    obtain ⟨v, hv⟩ := proj_surjective (D := D) hP euclidean
      (Function.invFunOn (prodChart D E z) (chartSources D E z G) (πE x))
    have h1 : πE (w + v) = πE x := by
      rw [hπE, ← prodChart_proj hw, hv]
      exact (hS.isoMatch hF).inv_right _ hx
    have hk := ((hP D E n).1.2 _ _).1 h1
    refine ⟨_, ⟨_, hk, rfl⟩, ?_⟩
    show π₄ (x + (-w + (w + v - x))) ∈ chartSources D E z G
    have : x + (-w + (w + v - x)) = v := by abel
    rw [this, hπ₄, hv]
    exact hu
  have hcov : ∀ x, x ∈ Z ∨ ∃ t ∈ T, x ∈ t.1 := by
    intro x
    by_cases hx : πE x ∈ boxSet D E G
    · exact Or.inr (zone x hx)
    · exact Or.inl fun hs => hx (hsupp hs)
  have hclass : IsClassC D E ν (pushforward D E z G H) :=
    hM.contPartialsUpTo hT hZo hcov ν hc
  refine ⟨hclass, fun α hα => ?_⟩
  funext y
  obtain ⟨x, rfl⟩ := proj_surjective (D := D) hP E y
  have e1 := congrFun (partialDeriv_comp_proj hP E hclass hα) x
  have hI := hM.iterPartial hT hZo α
  simp only [Function.comp] at e1
  rw [e1]
  by_cases hx : πE x ∈ boxSet D E G
  · obtain ⟨_, ⟨k, hk, rfl⟩, hxt⟩ := zone x hx
    have e2 := congrFun (partialDeriv_comp_proj hP euclidean hc hα) (x + (-w + k))
    simp only [Function.comp] at e2
    have h3 := hI.1 _ ⟨k, hk, rfl⟩ x hxt
    simp only at h3
    have h4 := hS.pushforward_prodChart (Tuple.partialDeriv D euclidean α H)
      (show π₄ (x + (-w + k)) ∈ chartSources D E z G from hxt)
    rw [key x k hk] at h4
    rw [h3, h4]
    exact e2.symm
  · rw [pushforward_of_notMem _ hx]
    exact hI.2 x fun hs => hx (hsupp hs)
theorem ChartData.commuteDeriv (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement) :
    PullbackPushforwardCommuteDeriv D E z G :=
  ⟨fun _ _ h hc => hS.pullback_classC hP hF h hc, fun _ _ h hc => hS.pushforward_classC hP hF h hc⟩
theorem ChartData.cNorm_pullback (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement) {ν : ℕ}
    {F : E.Tuple D n → ℂ} (h : HasCompactSupportWithin D E (boxSet D E G) F)
    (hc : IsClassC D E ν F) :
    cNorm D euclidean ν (pullback D E z G F) = cNorm D E ν F := by
  unfold cNorm
  refine iSup_congr fun α => iSup_congr fun hα => ?_
  rw [(hS.pullback_classC hP hF h hc).2 α hα]
  apply le_antisymm
  · refine iSup_le fun u => ?_
    by_cases hu : u ∈ chartSources D E z G
    · rw [pullback_of_mem _ hu]
      exact le_iSup (fun y => ENNReal.ofReal ‖Tuple.partialDeriv D E α F y‖) _
    · rw [pullback_of_notMem _ hu]
      simp
  · refine iSup_le fun y => ?_
    by_cases hy : y ∈ boxSet D E G
    · obtain ⟨u, hu, rfl⟩ := hS.bijOn_prodChart.surjOn hy
      rw [← pullback_of_mem (Tuple.partialDeriv D E α F) hu]
      exact le_iSup (fun u => ENNReal.ofReal ‖pullback D E z G (Tuple.partialDeriv D E α F) u‖) u
    · have hsub := ((hP D E n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ν F hc α hα).2.2.2.2.2
      rw [eq_zero_of_supportT_subset hP (hsub.trans h.2) hy]
      simp
theorem ChartData.pullback_mem_testFns (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement)
    {F : E.Tuple D n → ℂ} (h : F ∈ testFns D E (boxSet D E G)) :
    pullback D E z G F ∈ testFns D euclidean (chartSources D E z G) :=
  ⟨fun ν => (hS.pullback_classC hP hF h.2 (h.1 ν)).1, hS.compactSupport_pullback hP hF h.2⟩
theorem ChartData.pushforward_mem_testFns (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement) {H : euclidean.Tuple D n → ℂ}
    (h : H ∈ testFns D euclidean (chartSources D E z G)) :
    pushforward D E z G H ∈ testFns D E (boxSet D E G) :=
  ⟨fun ν => (hS.pushforward_classC hP hF h.2 (h.1 ν)).1,
    hS.compactSupport_pushforward hP hF h.2⟩
theorem ChartData.pushforward_pullback (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement)
    {F : E.Tuple D n → ℂ} (h : HasCompactSupportWithin D E (boxSet D E G) F) :
    pushforward D E z G (pullback D E z G F) = F :=
  ((hS.pullbackPushforwardInverse hP hF).2.2.1 F h).2.1
theorem ChartData.pullback_pushforward (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement) {H : euclidean.Tuple D n → ℂ}
    (h : HasCompactSupportWithin D euclidean (chartSources D E z G) H) :
    pullback D E z G (pushforward D E z G H) = H :=
  ((hS.pullbackPushforwardInverse hP hF).2.2.2 H h).2.1
theorem ChartData.pullbackIsometry (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement) :
    PullbackIsometryOnTestFns D E z G := by
  refine ⟨⟨fun F h => hS.pullback_mem_testFns hP hF h, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro F h F' h' he
    rw [← hS.pushforward_pullback hP hF h.2, he, hS.pushforward_pullback hP hF h'.2]
  · intro H h
    exact ⟨_, hS.pushforward_mem_testFns hP hF h, hS.pullback_pushforward hP hF h.2⟩
  · exact fun F h => hS.pushforward_pullback hP hF h.2
  · exact fun H h => hS.pullback_pushforward hP hF h.2
  · exact fun F h ν => hS.cNorm_pullback hP hF h.2 (h.1 ν)
theorem pullback_sub (F F' : E.Tuple D n → ℂ) :
    pullback D E z G (F - F') = pullback D E z G F - pullback D E z G F' := by
  funext u
  by_cases hu : u ∈ chartSources D E z G
  · simp [pullback_of_mem _ hu]
  · simp [pullback_of_notMem _ hu]
theorem pullback_add (F F' : E.Tuple D n → ℂ) :
    pullback D E z G (F + F') = pullback D E z G F + pullback D E z G F' := by
  funext u
  by_cases hu : u ∈ chartSources D E z G
  · simp [pullback_of_mem _ hu]
  · simp [pullback_of_notMem _ hu]
theorem pullback_smul (c : ℂ) (F : E.Tuple D n → ℂ) :
    pullback D E z G (c • F) = c • pullback D E z G F := by
  funext u
  by_cases hu : u ∈ chartSources D E z G
  · simp [pullback_of_mem _ hu]
  · simp [pullback_of_notMem _ hu]
theorem pushforward_add (H H' : euclidean.Tuple D n → ℂ) :
    pushforward D E z G (H + H') = pushforward D E z G H + pushforward D E z G H' := by
  funext y
  by_cases hy : y ∈ boxSet D E G
  · simp [pushforward_of_mem _ hy]
  · simp [pushforward_of_notMem _ hy]
theorem pushforward_smul (c : ℂ) (H : euclidean.Tuple D n → ℂ) :
    pushforward D E z G (c • H) = c • pushforward D E z G H := by
  funext y
  by_cases hy : y ∈ boxSet D E G
  · simp [pushforward_of_mem _ hy]
  · simp [pushforward_of_notMem _ hy]
theorem sub_mem_testFns (hP : TupleFacts.AllFacts) {Ω : Set (E.Tuple D n)}
    (hΩ : Tuple.IsOpenT D E Ω) {F F' : E.Tuple D n → ℂ}
    (h : F ∈ testFns D E Ω) (h' : F' ∈ testFns D E Ω) :
    F - F' ∈ testFns D E Ω := by
  obtain ⟨S, hSs⟩ := ((hP D E n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Ω hΩ).1
  rw [← hSs] at h h' ⊢
  exact S.sub_mem h h'
theorem ChartData.tendsto_iff (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement)
    (Fs : ℕ+ → testFns D E (boxSet D E G))
    (F : testFns D E (boxSet D E G))
    (Hs : ℕ+ → testFns D euclidean (chartSources D E z G))
    (H : testFns D euclidean (chartSources D E z G))
    (hs : ∀ t, (Hs t).1 = pullback D E z G (Fs t).1) (h : H.1 = pullback D E z G F.1) :
    TendstoInTestFns Fs F ↔ TendstoInTestFns Hs H := by
  have hnorm : ∀ ν t, cNorm D euclidean ν ((Hs t).1 - H.1) =
      cNorm D E ν ((Fs t).1 - F.1) := by
    intro ν t
    rw [hs t, h, ← pullback_sub]
    have hm := sub_mem_testFns hP (hS.isOpenT_boxSet hP) (Fs t).2 F.2
    exact hS.cNorm_pullback hP hF hm.2 (hm.1 ν)
  have hsuppF : ∀ F' : testFns D E (boxSet D E G),
      Tuple.supportT D euclidean (pullback D E z G F'.1) =
        Function.invFunOn (prodChart D E z) (chartSources D E z G) ''
          Tuple.supportT D E F'.1 := fun F' => hS.supportT_pullback hP hF F'.2.2
  have hsuppH : ∀ F' : testFns D E (boxSet D E G),
      Tuple.supportT D E F'.1 =
        prodChart D E z '' Tuple.supportT D euclidean (pullback D E z G F'.1) := by
    intro F'
    have := hS.supportT_pushforward hP hF (hS.compactSupport_pullback hP hF F'.2.2)
    rwa [hS.pushforward_pullback hP hF F'.2.2] at this
  constructor
  · rintro ⟨⟨K, hK, hKG, hFK, hFsK⟩, hconv⟩
    refine ⟨⟨_, hS.isCompactT_invImage hP hF hK hKG, hS.invImage_subset hF hKG, ?_,
      fun t => ?_⟩, fun ν => ?_⟩
    · rw [h, hsuppF F]
      exact Set.image_mono hFK
    · rw [hs t, hsuppF (Fs t)]
      exact Set.image_mono (hFsK t)
    · exact (hconv ν).congr fun t => (hnorm ν t).symm
  · rintro ⟨⟨K, hK, hKO, hHK, hHsK⟩, hconv⟩
    refine ⟨⟨_, hS.isCompactT_chartImage hP hF hK hKO, hS.chartImage_subset hKO, ?_,
      fun t => ?_⟩, fun ν => ?_⟩
    · rw [hsuppH F, ← h]
      exact Set.image_mono hHK
    · rw [hsuppH (Fs t), ← hs t]
      exact Set.image_mono (hHsK t)
    · exact (hconv ν).congr fun t => hnorm ν t
theorem composePullback_apply (T : testFns D euclidean (chartSources D E z G) → ℂ)
    (F : testFns D E (boxSet D E G))
    (hm : pullback D E z G F.1 ∈ testFns D euclidean (chartSources D E z G)) :
    composePullback D E z G T F = T ⟨_, hm⟩ := dif_pos hm
theorem composePushforward_apply (T : testFns D E (boxSet D E G) → ℂ)
    (H : testFns D euclidean (chartSources D E z G))
    (hm : pushforward D E z G H.1 ∈ testFns D E (boxSet D E G)) :
    composePushforward D E z G T H = T ⟨_, hm⟩ := dif_pos hm
theorem ChartData.hasOrderBound_composePullback (hS : ChartData D E z G)
    (hP : TupleFacts.AllFacts) (hF : LiftsProductsDistributions.Statement)
    {T : testFns D euclidean (chartSources D E z G) → ℂ}
    {K : Set (E.Tuple D n)} {ν : ℕ}
    (hs : HasOrderBoundOn T (Function.invFunOn (prodChart D E z) (chartSources D E z G) '' K) ν) :
    HasOrderBoundOn (composePullback D E z G T) K ν := by
  obtain ⟨C, hC⟩ := hs
  refine ⟨C, fun F hFK => ?_⟩
  have hm := hS.pullback_mem_testFns hP hF F.2
  rw [composePullback_apply T F hm]
  have h1 := hC ⟨_, hm⟩ (by
    show Tuple.supportT D euclidean (pullback D E z G F.1) ⊆ _
    rw [hS.supportT_pullback hP hF F.2.2]
    exact Set.image_mono hFK)
  rwa [show cNorm D euclidean ν (pullback D E z G F.1) = cNorm D E ν F.1 from
    hS.cNorm_pullback hP hF F.2.2 (F.2.1 ν)] at h1
theorem ChartData.hasOrderBound_composePushforward (hS : ChartData D E z G)
    (hP : TupleFacts.AllFacts) (hF : LiftsProductsDistributions.Statement)
    {T : testFns D E (boxSet D E G) → ℂ}
    {K : Set (euclidean.Tuple D n)} {ν : ℕ}
    (hs : HasOrderBoundOn T (prodChart D E z '' K) ν) :
    HasOrderBoundOn (composePushforward D E z G T) K ν := by
  obtain ⟨C, hC⟩ := hs
  refine ⟨C, fun H hHK => ?_⟩
  have hm := hS.pushforward_mem_testFns hP hF H.2
  rw [composePushforward_apply T H hm]
  have h1 := hC ⟨_, hm⟩ (by
    show Tuple.supportT D E (pushforward D E z G H.1) ⊆ _
    rw [hS.supportT_pushforward hP hF H.2.2]
    exact Set.image_mono hHK)
  have h2 := hS.cNorm_pullback hP hF hm.2 (hm.1 ν)
  rw [hS.pullback_pushforward hP hF H.2.2] at h2
  rwa [show cNorm D E ν (pushforward D E z G H.1) = cNorm D euclidean ν H.1 from
    h2.symm] at h1
theorem ChartData.linear_composePullback (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement)
    {T : testFns D euclidean (chartSources D E z G) → ℂ} (hT : IsComplexLinearForm T) :
    IsComplexLinearForm (composePullback D E z G T) := by
  constructor
  · intro A B C hC
    rw [composePullback_apply T A (hS.pullback_mem_testFns hP hF A.2),
      composePullback_apply T B (hS.pullback_mem_testFns hP hF B.2),
      composePullback_apply T C (hS.pullback_mem_testFns hP hF C.2)]
    refine hT.1 _ _ _ ?_
    show pullback D E z G C.1 = pullback D E z G A.1 + pullback D E z G B.1
    rw [hC, pullback_add]
  · intro c A C hC
    rw [composePullback_apply T A (hS.pullback_mem_testFns hP hF A.2),
      composePullback_apply T C (hS.pullback_mem_testFns hP hF C.2)]
    refine hT.2 _ _ _ ?_
    show pullback D E z G C.1 = c • pullback D E z G A.1
    rw [hC, pullback_smul]
theorem ChartData.linear_composePushforward (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement)
    {T : testFns D E (boxSet D E G) → ℂ} (hT : IsComplexLinearForm T) :
    IsComplexLinearForm (composePushforward D E z G T) := by
  constructor
  · intro A B C hC
    rw [composePushforward_apply T A (hS.pushforward_mem_testFns hP hF A.2),
      composePushforward_apply T B (hS.pushforward_mem_testFns hP hF B.2),
      composePushforward_apply T C (hS.pushforward_mem_testFns hP hF C.2)]
    refine hT.1 _ _ _ ?_
    show pushforward D E z G C.1 = pushforward D E z G A.1 + pushforward D E z G B.1
    rw [hC, pushforward_add]
  · intro c A C hC
    rw [composePushforward_apply T A (hS.pushforward_mem_testFns hP hF A.2),
      composePushforward_apply T C (hS.pushforward_mem_testFns hP hF C.2)]
    refine hT.2 _ _ _ ?_
    show pushforward D E z G C.1 = c • pushforward D E z G A.1
    rw [hC, pushforward_smul]
theorem ChartData.composePushforward_composePullback (hS : ChartData D E z G)
    (hP : TupleFacts.AllFacts) (hF : LiftsProductsDistributions.Statement)
    (T : testFns D euclidean (chartSources D E z G) → ℂ) :
    composePushforward D E z G (composePullback D E z G T) = T := by
  funext H
  have hm := hS.pushforward_mem_testFns hP hF H.2
  rw [composePushforward_apply _ H hm,
    composePullback_apply T _ (hS.pullback_mem_testFns hP hF hm)]
  congr 1
  exact Subtype.ext (hS.pullback_pushforward hP hF H.2.2)
theorem ChartData.composePullback_composePushforward (hS : ChartData D E z G)
    (hP : TupleFacts.AllFacts) (hF : LiftsProductsDistributions.Statement)
    (T : testFns D E (boxSet D E G) → ℂ) :
    composePullback D E z G (composePushforward D E z G T) = T := by
  funext F
  have hm := hS.pullback_mem_testFns hP hF F.2
  rw [composePullback_apply _ F hm,
    composePushforward_apply T _ (hS.pushforward_mem_testFns hP hF hm)]
  congr 1
  exact Subtype.ext (hS.pushforward_pullback hP hF F.2.2)
theorem ChartData.isDistrib_composePullback (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement)
    {T : testFns D euclidean (chartSources D E z G) → ℂ} (hT : IsDistrib T) :
    IsDistrib (composePullback D E z G T) := by
  refine ⟨hS.linear_composePullback hP hF hT.1, fun K hK hKG => ?_⟩
  obtain ⟨ν, hν⟩ := hT.2 _ (hS.isCompactT_invImage hP hF hK hKG) (hS.invImage_subset hF hKG)
  exact ⟨ν, hS.hasOrderBound_composePullback hP hF hν⟩
theorem ChartData.isDistrib_composePushforward (hS : ChartData D E z G)
    (hP : TupleFacts.AllFacts) (hF : LiftsProductsDistributions.Statement)
    {T : testFns D E (boxSet D E G) → ℂ} (hT : IsDistrib T) :
    IsDistrib (composePushforward D E z G T) := by
  refine ⟨hS.linear_composePushforward hP hF hT.1, fun K hK hKO => ?_⟩
  obtain ⟨ν, hν⟩ := hT.2 _ (hS.isCompactT_chartImage hP hF hK hKO) (hS.chartImage_subset hKO)
  exact ⟨ν, hS.hasOrderBound_composePushforward hP hF hν⟩
theorem ChartData.convergenceDistribCorrespond (hS : ChartData D E z G)
    (hP : TupleFacts.AllFacts) (hF : LiftsProductsDistributions.Statement) :
    ConvergenceDistribCorrespond D E z G := by
  refine ⟨hS.tendsto_iff hP hF, ⟨fun T hT => hS.isDistrib_composePullback hP hF hT, ?_, ?_⟩,
    ⟨fun T _ => hS.composePushforward_composePullback hP hF T,
      fun T _ => hS.composePullback_composePushforward hP hF T⟩, ?_⟩
  · intro T _ T' _ he
    rw [← hS.composePushforward_composePullback hP hF T, he,
      hS.composePushforward_composePullback hP hF T']
  · intro T' hT'
    exact ⟨_, hS.isDistrib_composePushforward hP hF hT',
      hS.composePullback_composePushforward hP hF T'⟩
  · intro T hT ν₀
    constructor
    · intro h
      refine ⟨hT, fun K hK hKO => ?_⟩
      have h1 := h.2 _ (hS.isCompactT_chartImage hP hF hK hKO) (hS.chartImage_subset hKO)
      have h2 := hS.hasOrderBound_composePushforward hP hF h1
      rwa [hS.composePushforward_composePullback hP hF T] at h2
    · intro h
      refine ⟨hS.isDistrib_composePullback hP hF hT, fun K hK hKG => ?_⟩
      exact hS.hasOrderBound_composePullback hP hF
        (h.2 _ (hS.isCompactT_invImage hP hF hK hKG) (hS.invImage_subset hF hKG))
end MapsOnTestFns
section SingleFactor
variable {D : Params} {E : Kind} {n : ℕ+} {z : Fin (n : ℕ) → Fin 4 → ℝ}
  {G : Fin (n : ℕ) → Set (E.Pt D)}
theorem fin_one_eta {Z : Type*} (u : Fin ((1 : ℕ+) : ℕ) → Z) :
    (fun _ => u ⟨0, (1 : ℕ+).pos⟩) = u := by
  funext j
  congr 1
  exact Subsingleton.elim (α := Fin 1) _ _
theorem quotDist_nonneg (D : Params) (E : Kind) (y y' : E.Pt D) : 0 ≤ Kind.quotDist D E y y' := by apply _root_.YangMills.Construction.PeriodicSpace.QuotientGeometry.quotDist_nonneg <;> assumption
theorem isoMatch_single (D : Params) (E : Kind) :
    IsoMatch (Kind.quotDist D E) (Tuple.tupleDist D E (p := 1)) Set.univ Set.univ
      (fun y _ => y) (fun u => u ⟨0, (1 : ℕ+).pos⟩) where
  mapsTo _ _ := trivial
  mapsFrom _ _ := trivial
  inv_left _ _ := rfl
  inv_right u _ := fin_one_eta u
  dist_eq a _ b _ := by
    show Real.sqrt (∑ _i : Fin 1, Kind.quotDist D E a b ^ 2) = _
    simp [Real.sqrt_sq (quotDist_nonneg D E a b)]
theorem isOpenWrt_univ {X : Type*} (d : X → X → ℝ) : MetricNotions.IsOpenWrt d Set.univ :=
  fun _ _ => ⟨1, one_pos, fun _ _ => trivial⟩
theorem singleSet_eq_image (D : Params) (E : Kind) (S : Set (E.Pt D)) :
    singleSet D E S = (fun y _ => y) '' S := by
  ext u
  constructor
  · intro hu
    exact ⟨_, hu, fin_one_eta u⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy
theorem image_singleSet (D : Params) (E : Kind) (S : Set (E.Pt D)) :
    (fun u : E.Tuple D 1 => u ⟨0, (1 : ℕ+).pos⟩) '' singleSet D E S = S := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro hy
    exact ⟨fun _ => y, hy, rfl⟩
theorem isCompactT_singleSet_iff (D : Params) (E : Kind) (S : Set (E.Pt D)) :
    Tuple.IsCompactT D E (singleSet D E S) ↔ Kind.IsCompactQ D E S := by
  constructor
  · intro h
    have := (isoMatch_single D E).symm.isCompactWrt_image (isOpenWrt_univ _)
      (Set.subset_univ _) h
    rwa [image_singleSet] at this
  · intro h
    have := (isoMatch_single D E).isCompactWrt_image (isOpenWrt_univ _)
      (Set.subset_univ _) h
    rwa [← singleSet_eq_image] at this
theorem boxSet_one (D : Params) (E : Kind) (S : Set (E.Pt D)) :
    boxSet D E (n := 1) (fun _ => S) = singleSet D E S := by
  ext u
  constructor
  · intro hu
    exact hu _
  · intro hu j
    rw [← fin_one_eta u]
    exact hu
theorem mem_c1SupportedIn_iff (hP : TupleFacts.AllFacts) (D : Params) (E : Kind)
    (S : Set (E.Pt D)) (h : E.Pt D → ℝ) : h ∈ c1SupportedIn D E S ↔
      HasCompactSupportWithin D E (boxSet D E (n := 1) fun _ => S)
        (ofSingle D E fun y => (h y : ℂ)) ∧
      IsClassC D E 1 (ofSingle D E fun y => (h y : ℂ)) := by
  have hTwo := (hP D E 1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h
  rw [boxSet_one]
  constructor
  · rintro ⟨hc, hK, hs⟩
    have hsupp := (hTwo.2 hc).2
    refine ⟨?_, hTwo.1.2 hc⟩
    unfold HasCompactSupportWithin
    rw [hsupp]
    exact ⟨(isCompactT_singleSet_iff D E _).2 hK, fun u hu => hs hu⟩
  · rintro ⟨⟨hK, hs⟩, hc⟩
    have hc' : IsC1Fn D E h := hTwo.1.1 hc
    have hsupp := (hTwo.2 hc').2
    rw [hsupp] at hK hs
    refine ⟨hc', (isCompactT_singleSet_iff D E _).1 hK, fun y hy => ?_⟩
    exact hs (show (fun _ => y) ∈ singleSet D E (Kind.supportQ D E h) from hy)
theorem ofSingle_singlePullback (z : Fin 4 → ℝ) (S : Set (E.Pt D)) (φ : E.Pt D → ℂ) :
    ofSingle D euclidean (singlePullback D E z S φ) =
      pullback D E (n := 1) (fun _ => z) (fun _ => S) (ofSingle D E φ) := by
  funext u
  show pullback D E (n := 1) (fun _ => z) (fun _ => S) (ofSingle D E φ)
    (fun _ => u ⟨0, (1 : ℕ+).pos⟩) = _
  rw [fin_one_eta]
theorem ofSingle_singlePushforward (z : Fin 4 → ℝ) (S : Set (E.Pt D))
    (h : euclidean.Pt D → ℂ) :
    ofSingle D E (singlePushforward D E z S h) =
      pushforward D E (n := 1) (fun _ => z) (fun _ => S) (ofSingle D euclidean h) := by
  funext y
  show pushforward D E (n := 1) (fun _ => z) (fun _ => S) (ofSingle D euclidean h)
    (fun _ => y ⟨0, (1 : ℕ+).pos⟩) = _
  rw [fin_one_eta]
theorem ofSingle_const_apply {E : Kind} {Z : Type*} (F : E.Tuple D 1 → Z) :
    ofSingle D E (fun y => F fun _ => y) = F := by
  funext u
  show F (fun _ => u ⟨0, (1 : ℕ+).pos⟩) = _
  rw [fin_one_eta]
theorem ofSingle_injective {E : Kind} {Z : Type*} {φ ψ : E.Pt D → Z}
    (h : ofSingle D E φ = ofSingle D E ψ) : φ = ψ :=
  funext fun y => congrFun h fun _ => y
theorem singlePullback_eq_indicator (z : Fin 4 → ℝ) (S : Set (E.Pt D)) (φ : E.Pt D → ℂ)
    (u : euclidean.Pt D) : singlePullback D E z S φ u =
      (chartSource D E z S).indicator (φ ∘ translateChart D E z) u := by
  show pullback D E (n := 1) (fun _ => z) (fun _ => S) (ofSingle D E φ) (fun _ => u) = _
  by_cases hu : u ∈ chartSource D E z S
  · rw [pullback_of_mem _ (fun _ => hu), Set.indicator_of_mem hu]
    rfl
  · rw [pullback_of_notMem _ (fun h => hu (h ⟨0, (1 : ℕ+).pos⟩)), Set.indicator_of_notMem hu]
theorem ChartData.single (hS : ChartData D E z G) (i : Fin (n : ℕ)) :
    ChartData D E (n := 1) (fun _ => z i) (fun _ => G i) :=
  ⟨fun _ => hS.src_open i, fun _ => hS.tgt_open i, fun _ => hS.bijOn_single i,
    fun _ => hS.dist_single i⟩
theorem im_singlePushforward_ofReal (z : Fin 4 → ℝ) (S : Set (E.Pt D))
    (g : euclidean.Pt D → ℝ) (y : E.Pt D) :
    ((singlePushforward D E z S fun u => (g u : ℂ)) y).im = 0 := by
  show (pushforward D E (n := 1) (fun _ => z) (fun _ => S)
    (ofSingle D euclidean fun u => (g u : ℂ)) fun _ => y).im = 0
  by_cases hy : (fun _ => y) ∈ boxSet D E (n := 1) fun _ => S
  · rw [pushforward_of_mem _ hy]
    simp [ofSingle]
  · rw [pushforward_of_notMem _ hy]
    simp
theorem ofReal_re_of_im_eq_zero {X : Type*} {φ : X → ℂ} (h : ∀ y, (φ y).im = 0) :
    (fun y => (((φ y).re : ℝ) : ℂ)) = φ :=
  funext fun y => Complex.ext (by simp) (by simp [h y])
theorem ChartData.singleMapsOnClasses (hS : ChartData D E z G) (hP : TupleFacts.AllFacts)
    (hF : LiftsProductsDistributions.Statement) :
    SingleMapsOnClasses D E z G := by
  refine ⟨fun i => ⟨?_, ?_⟩, ?_, fun i => ⟨?_, ?_, ?_⟩⟩
  · have h1 := hS.single i
    ext ψ
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      show ofSingle D euclidean _ ∈ testFns D euclidean _
      rw [ofSingle_singlePullback, ← boxSet_one]
      refine h1.pullback_mem_testFns hP hF ?_
      rw [boxSet_one]
      exact hφ
    · intro hψ
      have hψ' : ofSingle D euclidean ψ ∈
          testFns D euclidean (chartSources D E (n := 1) (fun _ => z i) fun _ => G i) := by
        show _ ∈ testFns D euclidean (boxSet D euclidean fun _ => _)
        rw [boxSet_one]
        exact hψ
      have hm := h1.pushforward_mem_testFns hP hF hψ'
      refine ⟨fun y => pushforward D E (n := 1) (fun _ => z i) (fun _ => G i)
        (ofSingle D euclidean ψ) fun _ => y, ?_, ?_⟩
      · show ofSingle D E _ ∈ testFns D E _
        rw [ofSingle_const_apply, ← boxSet_one]
        exact hm
      · apply ofSingle_injective (E := euclidean)
        rw [ofSingle_singlePullback, ofSingle_const_apply, h1.pullback_pushforward hP hF hψ'.2]
  · intro φ _ hre u
    rw [singlePullback_eq_indicator]
    by_cases hu : u ∈ chartSource D E (z i) (G i)
    · rw [Set.indicator_of_mem hu]
      exact hre _
    · rw [Set.indicator_of_notMem hu]
      simp
  · intro φ _
    funext u
    by_cases hu : u ∈ chartSources D E z G
    · rw [pullback_of_mem _ hu]
      refine Finset.prod_congr rfl fun i _ => ?_
      beta_reduce
      rw [singlePullback_eq_indicator, Set.indicator_of_mem (hu i)]
      rfl
    · rw [pullback_of_notMem _ hu]
      have hex : ∃ i, u i ∉ chartSource D E (z i) (G i) := by
        by_contra hcon
        push Not at hcon
        exact hu hcon
      obtain ⟨i, hi⟩ := hex
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      beta_reduce
      rw [singlePullback_eq_indicator, Set.indicator_of_notMem hi]
  · have h1 := hS.single i
    ext ψ
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨hgs, hgc⟩ := (mem_c1SupportedIn_iff hP D euclidean _ g).1 hg
      have hreal := im_singlePushforward_ofReal (E := E) (z i) (G i) g
      refine ⟨fun y => ((singlePushforward D E (z i) (G i) fun u => (g u : ℂ)) y).re, ?_,
        ofReal_re_of_im_eq_zero hreal⟩
      refine (mem_c1SupportedIn_iff hP D E _ _).2 ?_
      rw [ofReal_re_of_im_eq_zero hreal, ofSingle_singlePushforward]
      exact ⟨h1.compactSupport_pushforward hP hF hgs, (h1.pushforward_classC hP hF hgs hgc).1⟩
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨hhs, hhc⟩ := (mem_c1SupportedIn_iff hP D E _ h).1 hh
      set H := pullback D E (n := 1) (fun _ => z i) (fun _ => G i)
        (ofSingle D E fun y => (h y : ℂ)) with hH
      have hHs := h1.compactSupport_pullback hP hF hhs
      have hHc := (h1.pullback_classC hP hF hhs hhc).1
      have hreal : ∀ u : euclidean.Pt D, (H fun _ => u).im = 0 := by
        intro u
        by_cases hu : (fun _ => u) ∈
            chartSources D E (n := 1) (fun _ => z i) fun _ => G i
        · rw [hH, pullback_of_mem _ hu]
          simp [ofSingle]
        · rw [hH, pullback_of_notMem _ hu]
          simp
      have hback : (ofSingle D euclidean fun u => ((((H fun _ => u).re : ℝ)) : ℂ)) = H := by
        rw [ofReal_re_of_im_eq_zero hreal, ofSingle_const_apply]
      refine ⟨fun u => (H fun _ => u).re, ?_, ?_⟩
      · refine (mem_c1SupportedIn_iff hP D euclidean _ _).2 ?_
        rw [hback]
        exact ⟨hHs, hHc⟩
      · apply ofSingle_injective (E := E)
        show ofSingle D E (singlePushforward D E (z i) (G i) _) = _
        rw [ofSingle_singlePushforward, hback, hH, h1.pushforward_pullback hP hF hhs]
  · intro a b g _ g' _
    funext y
    show pushforward D E (n := 1) (fun _ => z i) (fun _ => G i) _ (fun _ => y) =
      (a : ℂ) * pushforward D E (n := 1) (fun _ => z i) (fun _ => G i) _ (fun _ => y) +
      (b : ℂ) * pushforward D E (n := 1) (fun _ => z i) (fun _ => G i) _ (fun _ => y)
    by_cases hy : (fun _ => y) ∈ boxSet D E (n := 1) fun _ => G i
    · rw [pushforward_of_mem _ hy, pushforward_of_mem _ hy, pushforward_of_mem _ hy]
      simp [ofSingle]
    · rw [pushforward_of_notMem _ hy, pushforward_of_notMem _ hy, pushforward_of_notMem _ hy]
      simp
  · intro g hg
    have h1 := hS.single i
    obtain ⟨hgs, hgc⟩ := (mem_c1SupportedIn_iff hP D euclidean _ g).1 hg
    show cNorm D E 1 (ofSingle D E _) = cNorm D euclidean 1 _
    rw [ofSingle_singlePushforward]
    have h2 := h1.cNorm_pullback hP hF (h1.compactSupport_pushforward hP hF hgs)
      (h1.pushforward_classC hP hF hgs hgc).1
    rw [h1.pullback_pushforward hP hF hgs] at h2
    exact h2.symm
end SingleFactor
theorem claim_holds (hP : TupleFacts.AllFacts) (hF : LiftsProductsDistributions.Statement) :
    Claim := by
  intro D E n R d G z hG _ hz
  have hf := factorIsometricCharts D E hF hG hz
  have hS : ChartData D E z G :=
    ⟨fun i => (hf.2.2.2 i).1, hG.isOpen_mem, fun i => (hf.2.2.2 i).2.2.1,
      fun i => (hf.2.2.2 i).2.2.2.1⟩
  have hc := hS.isoMatch hF
  refine ⟨hf, ?_, hS.pullbackPushforwardInverse hP hF, hS.commuteDeriv hP hF,
    hS.pullbackIsometry hP hF, hS.convergenceDistribCorrespond hP hF,
    hS.singleMapsOnClasses hP hF⟩
  refine ⟨⟨fun u => ⟨_, hc.mapsTo u.1 u.2⟩, fun y => ⟨_, hc.mapsFrom y.1 y.2⟩,
    fun u => Subtype.ext (hc.inv_left u.1 u.2), fun y => Subtype.ext (hc.inv_right y.1 y.2)⟩,
    fun _ => rfl, ?_, ?_⟩
  · intro a ε hε
    refine ⟨ε, hε, fun b hb => ?_⟩
    show Tuple.tupleDist D E (prodChart D E z a.1) (prodChart D E z b.1) < ε
    rwa [hc.dist_eq _ a.2 _ b.2]
  · intro a ε hε
    refine ⟨ε, hε, fun b hb => ?_⟩
    show Tuple.tupleDist D euclidean
      (Function.invFunOn (prodChart D E z) (chartSources D E z G) a.1)
      (Function.invFunOn (prodChart D E z) (chartSources D E z G) b.1) < ε
    rwa [hc.symm.dist_eq _ a.2 _ b.2]
end YangMills.Construction.PeriodicSpace.Kind.AdmissibleCharts
