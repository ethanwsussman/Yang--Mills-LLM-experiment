import YangMills.Construction.Towers.TheDensityUnderAGradient
import YangMills.Construction.Towers.TheExpansionOfTheDensityInAFieldOfBoundedAngles
import YangMills.Construction.Towers.TheRowSumsOfTheSecondDerivativesOfTheDensityVanish
import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensityAreSymmetric
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.RowSums
section Abstract
theorem quadratic_coeff_unique {φ : ℝ → ℂ} {a Q Q' : ℂ} {D ε : ℝ} (hε : 0 < ε)
    (hQ : ∀ t : ℝ, 4 * |t| ≤ ε → ‖φ t - a - ((1 / 2 * t ^ 2 : ℝ) : ℂ) * Q‖ ≤ D * |t| ^ 3)
    (hQ' : ∀ t : ℝ, 4 * |t| ≤ ε → ‖φ t - a - ((1 / 2 * t ^ 2 : ℝ) : ℂ) * Q'‖ ≤ D * |t| ^ 3) :
    Q = Q' := by
  by_contra hne
  have hgap : 0 < ‖Q - Q'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set gap := ‖Q - Q'‖ with hgapdef
  set M := |D| + 1 with hMdef
  set t := min (ε / 4) (gap / (8 * M)) with htdef
  have ht : 0 < t := lt_min (by linarith) (by positivity)
  have ht1 : 4 * |t| ≤ ε := by
    rw [abs_of_pos ht]
    have := min_le_left (ε / 4) (gap / (8 * M))
    linarith
  have ht2 : t * (8 * M) ≤ gap := by
    have := min_le_right (ε / 4) (gap / (8 * M))
    exact (le_div_iff₀ (by positivity)).mp this
  have hdiff : ((1 / 2 * t ^ 2 : ℝ) : ℂ) * (Q - Q') =
      (φ t - a - ((1 / 2 * t ^ 2 : ℝ) : ℂ) * Q') - (φ t - a - ((1 / 2 * t ^ 2 : ℝ) : ℂ) * Q) := by
    ring
  have hbound : 1 / 2 * t ^ 2 * gap ≤ 2 * (D * t ^ 3) := by
    have e1 := hQ t ht1
    have e2 := hQ' t ht1
    rw [abs_of_pos ht] at e1 e2
    have e3 := norm_sub_le (φ t - a - ((1 / 2 * t ^ 2 : ℝ) : ℂ) * Q')
      (φ t - a - ((1 / 2 * t ^ 2 : ℝ) : ℂ) * Q)
    rw [← hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at e3
    linarith
  have hDM : D * t ^ 3 ≤ M * t ^ 3 := by
    have : D ≤ M := by
      have := le_abs_self D
      linarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have ht3 : 0 < t ^ 2 := by positivity
  have hlast : t ^ 2 * gap ≤ t ^ 2 * (gap / 2) := by
    have e4 : t ^ 3 * (8 * M) ≤ t ^ 2 * gap := by
      have := mul_le_mul_of_nonneg_left ht2 ht3.le
      calc t ^ 3 * (8 * M) = t ^ 2 * (t * (8 * M)) := by ring
        _ ≤ t ^ 2 * gap := this
    nlinarith
  have := le_of_mul_le_mul_left hlast ht3
  linarith
variable {E : Type}
theorem hasSum_row_zero_of_symm_sums_eq {K : E → E → ℂ} (hK : ∀ u v, K u v = K v u) {e : E}
    {ι v : E → ℝ} (hιe : ι e = 1) (hι : ∀ c, c ≠ e → ι c = 0) {T : ℂ}
    (hadd : HasSum (fun q : E × E => K q.1 q.2 * ((ι q.1 + v q.1 : ℝ) : ℂ) *
      ((ι q.2 + v q.2 : ℝ) : ℂ)) T)
    (hsub : HasSum (fun q : E × E => K q.1 q.2 * ((ι q.1 - v q.1 : ℝ) : ℂ) *
      ((ι q.2 - v q.2 : ℝ) : ℂ)) T) :
    HasSum (fun c => K e c * (v c : ℂ)) 0 := by
  have hdif := hadd.sub hsub
  rw [sub_self] at hdif
  have hshape : ∀ q : E × E, K q.1 q.2 * ((ι q.1 + v q.1 : ℝ) : ℂ) * ((ι q.2 + v q.2 : ℝ) : ℂ) -
      K q.1 q.2 * ((ι q.1 - v q.1 : ℝ) : ℂ) * ((ι q.2 - v q.2 : ℝ) : ℂ) =
      2 * K q.1 q.2 * (ι q.1 : ℂ) * (v q.2 : ℂ) + 2 * K q.1 q.2 * (v q.1 : ℂ) * (ι q.2 : ℂ) := by
    intro q
    push_cast
    ring
  simp only [hshape] at hdif
  have hleft : Function.Injective (fun c : E => (e, c)) := fun c c' h => (Prod.ext_iff.mp h).2
  have hright : Function.Injective (fun c : E => (c, e)) := fun c c' h => (Prod.ext_iff.mp h).1
  have hsumm : Summable (fun c => K e c * (v c : ℂ)) := by
    have s1 := hdif.summable.comp_injective hleft
    have s2 : Summable (fun c => 2 * K e c * (v e : ℂ) * (ι c : ℂ)) :=
      summable_of_ne_finset_zero (s := {e}) fun c hc => by
        have : c ≠ e := by simpa using hc
        simp [hι c this]
    have s3 := (s1.sub s2).mul_left (1 / 2 : ℂ)
    refine s3.congr fun c => ?_
    simp only [Function.comp, hιe]
    push_cast
    ring
  obtain ⟨R, hR⟩ := hsumm
  have k1 : HasSum (fun q : E × E => 2 * K q.1 q.2 * (ι q.1 : ℂ) * (v q.2 : ℂ)) (2 * R) := by
    refine (hleft.hasSum_iff ?_).mp ?_
    · rintro ⟨u, w⟩ hx
      have hu : u ≠ e := by
        rintro rfl
        exact hx ⟨w, rfl⟩
      simp [hι u hu]
    · have eq : ((fun q : E × E => 2 * K q.1 q.2 * (ι q.1 : ℂ) * (v q.2 : ℂ)) ∘ fun c : E => (e, c)) =
          fun c => 2 * (K e c * (v c : ℂ)) := by
        funext c
        simp only [Function.comp, hιe]
        push_cast
        ring
      rw [eq]
      exact hR.mul_left 2
  have k2 : HasSum (fun q : E × E => 2 * K q.1 q.2 * (v q.1 : ℂ) * (ι q.2 : ℂ)) (2 * R) := by
    refine (hright.hasSum_iff ?_).mp ?_
    · rintro ⟨u, w⟩ hx
      have hw : w ≠ e := by
        rintro rfl
        exact hx ⟨u, rfl⟩
      simp [hι w hw]
    · have eq : ((fun q : E × E => 2 * K q.1 q.2 * (v q.1 : ℂ) * (ι q.2 : ℂ)) ∘ fun c : E => (c, e)) =
          fun c => 2 * (K e c * (v c : ℂ)) := by
        funext c
        simp only [Function.comp, hιe, hK c e]
        push_cast
        ring
      rw [eq]
      exact hR.mul_left 2
  have k0 : 2 * R + 2 * R = 0 := (k1.add k2).unique hdif
  have hR0 : R = 0 := by
    have : (4 : ℂ) * R = 0 := by
      rw [← k0]
      ring
    simpa using this
  rw [hR0] at hR
  exact hR
end Abstract
theorem hasSum_congr_pointwise {α : Type} {u w : α → ℂ} {s : ℂ} (h : HasSum u s) (e : ∀ x, w x = u x) :
    HasSum w s := by
  rwa [show w = u from funext e]
section Lattice
variable {L : ℕ}
theorem meshAt_zero_zero (L : ℕ) : meshAt L 0 0 = 1 := by
  simp [meshAt]
def coordOne (x : FullSpace.Vertex L 0 0) : ℝ := (x : InfiniteLattice.AmbientSpace) 1
def coordOneGrad : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ :=
  FullSpace.vertexDifference (coordOne (L := L))
theorem coordOneGrad_forwardEdge (y : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    coordOneGrad (FullSpace.forwardEdge y μ) = if μ = 1 then 1 else 0 := by
  simp only [coordOneGrad, FullSpace.vertexDifference, coordOne, FullSpace.forwardEdge,
    InfiniteLattice.Link.forwardFrom, InfiniteLattice.axisStep]
  by_cases h : μ = 1
  · subst h
    simp [meshAt_zero_zero]
  · simp [h]
theorem exists_eq_forwardEdge (c : FullSpace.PositiveEdge (meshAt L 0 0)) :
    ∃ (y : FullSpace.Vertex L 0 0) (μ : Fin 4), c = FullSpace.forwardEdge y μ := by
  obtain ⟨⟨x, x', adj⟩, μ, hμ⟩ := c
  refine ⟨x, μ, ?_⟩
  apply Subtype.ext
  apply InfiniteLattice.Link.ext
  · rfl
  · have : x' = x + InfiniteLattice.axisStep _ μ := by
      rw [← hμ]
      abel
    simpa [FullSpace.forwardEdge, InfiniteLattice.Link.forwardFrom] using this
theorem abs_coordOneGrad_le (c : FullSpace.PositiveEdge (meshAt L 0 0)) :
    |coordOneGrad c| ≤ 1 := by
  obtain ⟨y, μ, rfl⟩ := exists_eq_forwardEdge c
  rw [coordOneGrad_forwardEdge]
  split_ifs <;> simp
theorem abs_edgeIndicator_le (e c : FullSpace.PositiveEdge (meshAt L 0 0)) :
    |edgeIndicator e c| ≤ 1 := by
  unfold edgeIndicator
  split_ifs <;> simp
theorem faceAngle_coordOneGrad (p : FullSpace.Face L 0 0) :
    FullSpace.faceAngle coordOneGrad p = 0 := by
  simp only [FullSpace.faceAngle, FullSpace.edgeDifference, coordOneGrad,
    FullSpace.vertexDifference, FullSpace.forwardEdge, InfiniteLattice.Link.forwardFrom]
  rw [add_right_comm p.corner (InfiniteLattice.axisStep _ p.highAxis)
    (InfiniteLattice.axisStep _ p.lowAxis)]
  ring
theorem hasBoundedAngles_indicator_add_smul (e : FullSpace.PositiveEdge (meshAt L 0 0)) {s : ℝ}
    (hs : |s| ≤ 1) : HasBoundedAngles fun c => edgeIndicator e c + s * coordOneGrad c := by
  have hval : ∀ c, |edgeIndicator e c + s * coordOneGrad c| ≤ 2 := fun c => by
    have a1 := abs_edgeIndicator_le e c
    have a2 : |s * coordOneGrad c| ≤ 1 := by
      rw [abs_mul]
      exact mul_le_one₀ hs (abs_nonneg _) (abs_coordOneGrad_le c)
    have := abs_add_le (edgeIndicator e c) (s * coordOneGrad c)
    linarith
  refine ⟨fun c => (hval c).trans ?_, fun p => ?_⟩
  · have : 0 ≤ TorusMetric.euclidNormVec (c.1.initial : InfiniteLattice.AmbientSpace) := by
      unfold TorusMetric.euclidNormVec
      positivity
    linarith
  · have hz := faceAngle_coordOneGrad (L := L) p
    simp only [FullSpace.faceAngle, FullSpace.edgeDifference] at hz ⊢
    set c₁ := FullSpace.forwardEdge p.corner p.lowAxis
    set c₂ := FullSpace.forwardEdge (p.corner + InfiniteLattice.axisStep _ p.lowAxis) p.highAxis
    set c₃ := FullSpace.forwardEdge (p.corner + InfiniteLattice.axisStep _ p.highAxis) p.lowAxis
    set c₄ := FullSpace.forwardEdge p.corner p.highAxis
    have eq : edgeIndicator e c₁ + s * coordOneGrad c₁ + (edgeIndicator e c₂ + s * coordOneGrad c₂) -
        (edgeIndicator e c₃ + s * coordOneGrad c₃) - (edgeIndicator e c₄ + s * coordOneGrad c₄) =
        edgeIndicator e c₁ + edgeIndicator e c₂ - edgeIndicator e c₃ - edgeIndicator e c₄ +
          s * (coordOneGrad c₁ + coordOneGrad c₂ - coordOneGrad c₃ - coordOneGrad c₄) := by
      ring
    rw [eq, hz, mul_zero, add_zero, abs_le]
    have a1 := abs_le.mp (abs_edgeIndicator_le e c₁)
    have a2 := abs_le.mp (abs_edgeIndicator_le e c₂)
    have a3 := abs_le.mp (abs_edgeIndicator_le e c₃)
    have a4 := abs_le.mp (abs_edgeIndicator_le e c₄)
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
theorem forwardEdge_one_injective :
    Function.Injective fun y : FullSpace.Vertex L 0 0 => FullSpace.forwardEdge y 1 := by
  intro y y' h
  exact congrArg (fun c : FullSpace.PositiveEdge (meshAt L 0 0) => c.1.initial) h
end Lattice
theorem secondDerivative_rowSum_vanishes (hExp : QuadraticExpansionOfDensity)
    (hGauge : DensityGaugeInvariant) (hSymm : SecondDerivativeSymm) :
    SecondDerivativeRowSumZero := by
  intro z hz L hL e
  obtain ⟨D, hD⟩ := hExp z hz
  have hadd := hD L hL _ (hasBoundedAngles_indicator_add_smul e (s := 1) (by simp))
  have hsub := hD L hL _ (hasBoundedAngles_indicator_add_smul e (s := -1) (by simp))
  have hε : 0 < min (Real.pi / 2) (z / 48) := lt_min (by positivity) (by positivity)
  have hequal : ∀ t : ℝ, 4 * |t| ≤ min (Real.pi / 2) (z / 48) →
      densityAt z (fun c => t * (edgeIndicator e c + -1 * coordOneGrad c))
          (0 : FullSpace.Vertex L 0 0) =
        densityAt z (fun c => t * (edgeIndicator e c + 1 * coordOneGrad c))
          (0 : FullSpace.Vertex L 0 0) := by
    intro t ht
    have h := (hGauge z hz L hL (fun x => 2 * t * coordOne x) _ (hsub t ht).1).2 0
    rw [← h]
    congr 1
    funext c
    simp only [FullSpace.vertexDifference, coordOneGrad]
    ring
  have hcoef := quadratic_coeff_unique hε (fun t ht => (hadd t ht).2.2)
    (fun t ht => by
      have h := (hsub t ht).2.2
      rwa [hequal t ht] at h)
  have h0 : 4 * |(0 : ℝ)| ≤ min (Real.pi / 2) (z / 48) := by simpa using hε.le
  have hsa : HasSum _ (secondDerivativeSum z _) := (hadd 0 h0).2.1.hasSum
  have hss : HasSum _ (secondDerivativeSum z _) := (hsub 0 h0).2.1.hasSum
  rw [← hcoef] at hss
  have hrow := hasSum_row_zero_of_symm_sums_eq (K := secondDerivative z (0 : FullSpace.Vertex L 0 0))
    (hSymm z hz L hL 0) (e := e) (ι := edgeIndicator e) (v := coordOneGrad)
    (by simp [edgeIndicator]) (fun c hc => by simp [edgeIndicator, hc])
    (hasSum_congr_pointwise hsa fun q => by simp [secondDerivativeTerm])
    (hasSum_congr_pointwise hss fun q => by simp [secondDerivativeTerm, sub_eq_add_neg])
  have hvanish : ∀ c ∉ Set.range fun y : FullSpace.Vertex L 0 0 => FullSpace.forwardEdge y 1,
      secondDerivative z (0 : FullSpace.Vertex L 0 0) e c * (coordOneGrad c : ℂ) = 0 := by
    intro c hc
    obtain ⟨y, μ, rfl⟩ := exists_eq_forwardEdge c
    have hμ : μ ≠ 1 := by
      rintro rfl
      exact hc ⟨y, rfl⟩
    simp [coordOneGrad_forwardEdge, hμ]
  have hres := (forwardEdge_one_injective.hasSum_iff hvanish).mpr hrow
  refine hasSum_congr_pointwise hres fun y => ?_
  simp [coordOneGrad_forwardEdge]
end YangMills.Construction.Tower.AbelianFieldDensity.RowSums
end
