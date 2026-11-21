import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAHolonomyProof
import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfTheGeneratorsProof
import YangMills.Construction.ColdStepAtMirrorFrames.CompositesAtAPoint
import YangMills.Construction.ColdStepAtMirrorFrames.ContourOfAChartFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.FitsAlongMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff Topology
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace FitAlongTranslates
open BlockOffsets
def leibnizBound (a b : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a i * b (j - i)
theorem leibnizBound_nonneg {a b : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    0 ≤ leibnizBound a b j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HolonomyDerivatives.leibnizConvolution_nonneg <;> assumption
theorem norm_iteratedFDeriv_mul_le_leibnizBound {k : ℕ} {u v : (Fin k → ℝ) → ℍ[ℝ]} {a b : ℕ → ℝ}
    (hu : ContDiff ℝ ω u) (hv : ContDiff ℝ ω v) (ha : ∀ j, ‖iteratedFDeriv ℝ j u 0‖ ≤ a j)
    (hb : ∀ j, ‖iteratedFDeriv ℝ j v 0‖ ≤ b j) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun τ => u τ * v τ) 0‖ ≤ leibnizBound a b j := by
  have h := norm_iteratedFDeriv_mul_le (N := ω) hu hv (0 : Fin k → ℝ) (n := j) le_top
  refine h.trans (Finset.sum_le_sum fun i _ => ?_)
  have h1 := ha i
  have h2 := hb (j - i)
  have n1 := norm_nonneg (iteratedFDeriv ℝ i u 0)
  have n2 := norm_nonneg (iteratedFDeriv ℝ (j - i) v 0)
  have hc : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 n2 (mul_nonneg hc (n1.trans h1))
def constBound (j : ℕ) : ℝ := if j = 0 then 1 else 0
theorem constBound_nonneg (j : ℕ) : 0 ≤ constBound j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HolonomyDerivatives.constantBound_nonneg <;> assumption
theorem norm_iteratedFDeriv_const_le_constBound {k : ℕ} {g : ℍ[ℝ]} (hg : ‖g‖ = 1) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun _ : Fin k → ℝ => g) 0‖ ≤ constBound j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HolonomyDerivatives.norm_iteratedFDeriv_const_le <;> assumption
def conjCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] := LinearMap.toContinuousLinearMap
  { toFun := star
    map_add' := star_add
    map_smul' := fun c q => by simp }
theorem conjCLM_apply (q : ℍ[ℝ]) : conjCLM q = star q := rfl
theorem norm_conjCLM_le : ‖conjCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
  rw [conjCLM_apply, norm_star, one_mul]
theorem norm_iteratedFDeriv_star_le {k : ℕ} {u : (Fin k → ℝ) → ℍ[ℝ]} (hu : ContDiff ℝ ω u) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun σ => star (u σ)) 0‖ ≤ ‖iteratedFDeriv ℝ j u 0‖ := by
  have h1 := conjCLM.iteratedFDeriv_comp_left (f := u) (x := 0) (n := ω) hu.contDiffAt (i := j) le_top
  have h2 : (fun σ => star (u σ)) = conjCLM ∘ u := rfl
  rw [h2, h1]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  calc ‖conjCLM‖ * ‖iteratedFDeriv ℝ j u 0‖ ≤ 1 * ‖iteratedFDeriv ℝ j u 0‖ :=
        mul_le_mul_of_nonneg_right norm_conjCLM_le (norm_nonneg _)
    _ = _ := one_mul _
theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
section Holonomy
variable {F : BlockFrame} {k : ℕ} (X : (Fin k → ℝ) → F.GaugeField F.depth)
theorem contDiff_linkValue (hX : ∀ x i, ContDiff ℝ ω (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ])))
    (x : F.Site F.depth) (st : PathStep) :
    ContDiff ℝ ω (fun σ => ((linkValue (X σ) x st : UnitQuaternion) : ℍ[ℝ])) := by
  unfold linkValue
  by_cases h : st.2 = true
  · simp only [h, if_true]
    exact hX _ _
  · simp only [h, Bool.false_eq_true, if_false]
    exact conjCLM.contDiff.comp (hX _ _)
theorem norm_iteratedFDeriv_linkValue_le
    (hX : ∀ x i, ContDiff ℝ ω (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ]))) {B : ℕ → ℝ}
    (hB : ∀ x i j, ‖iteratedFDeriv ℝ j (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ])) 0‖ ≤ B j)
    (x : F.Site F.depth) (st : PathStep) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun σ => ((linkValue (X σ) x st : UnitQuaternion) : ℍ[ℝ])) 0‖ ≤ B j := by
  unfold linkValue
  by_cases h : st.2 = true
  · simp only [h, if_true]
    exact hB _ _ _
  · simp only [h, Bool.false_eq_true, if_false]
    exact (norm_iteratedFDeriv_star_le (hX _ _) j).trans (hB _ _ _)
theorem contDiff_pathHolonomy (hX : ∀ x i, ContDiff ℝ ω (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ])))
    (p : List PathStep) (x : F.Site F.depth) :
    ContDiff ℝ ω (fun σ => ((pathHolonomy (X σ) x p : UnitQuaternion) : ℍ[ℝ])) := by
  induction p generalizing x with
  | nil => exact contDiff_const
  | cons st r ih => exact (contDiff_linkValue X hX x st).mul (ih _)
def holonomyBound (B : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => constBound
  | n + 1 => leibnizBound B (holonomyBound B n)
theorem holonomyBound_nonneg {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (n j : ℕ) : 0 ≤ holonomyBound B n j := by
  induction n generalizing j with
  | zero => exact constBound_nonneg j
  | succ n ih => exact leibnizBound_nonneg hB ih j
theorem norm_iteratedFDeriv_pathHolonomy_le
    (hX : ∀ x i, ContDiff ℝ ω (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ]))) {B : ℕ → ℝ}
    (hB : ∀ x i j, ‖iteratedFDeriv ℝ j (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ])) 0‖ ≤ B j)
    (p : List PathStep) (x : F.Site F.depth) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun σ => ((pathHolonomy (X σ) x p : UnitQuaternion) : ℍ[ℝ])) 0‖ ≤
      holonomyBound B p.length j := by
  induction p generalizing x j with
  | nil => exact norm_iteratedFDeriv_const_le_constBound (g := ((1 : UnitQuaternion) : ℍ[ℝ])) (norm_unitQuaternion 1) j
  | cons st r ih =>
    exact norm_iteratedFDeriv_mul_le_leibnizBound (contDiff_linkValue X hX x st) (contDiff_pathHolonomy X hX r _)
      (norm_iteratedFDeriv_linkValue_le X hX hB x st) (ih _) j
end Holonomy
section Walks
variable {F : BlockFrame}
def offsetSite (z : F.Cell) (u : Fin 4 → ℤ) : F.Site F.depth := cellCentre F.depth z + siteOfCoords F.depth u
theorem offsetSite_add_stepDisplacement (z : F.Cell) (u : Fin 4 → ℤ) (st : PathStep) :
    offsetSite z u + stepDisplacement F.depth st = offsetSite z (u + stepShift st) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedFieldContour.offsetSite_add_stepDisplacement <;> assumption
theorem offsetSite_zero (z : F.Cell) : offsetSite z 0 = _root_.YangMills.Construction.BlockAverages.refineSite z := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedFieldContour.offsetSite_zero <;> assumption
def axisLeg (h : Fin 4 → ℤ) (d : Fin 4) : List PathStep := List.replicate (h d).natAbs (d, decide (0 ≤ h d))
theorem walkStaysIn_flatMap_axisLeg {M : ℕ} (h : Fin 4 → ℤ) (hh : h ∈ centredCube M) (D : List (Fin 4))
    (hD : D.Nodup) (u : Fin 4 → ℤ) (hu : ∀ l, (u l = 0 ∨ u l = h l)) (h0 : (0 : Fin 4 → ℤ) ∈ centredCube M)
    (hz : ∀ d ∈ D, u d = 0) :
    WalkStaysIn M u (D.flatMap (axisLeg h)) ∧
      (∀ l, walkTarget u (D.flatMap (axisLeg h)) l = if l ∈ D then h l else u l) ∧
      (((D.flatMap (axisLeg h)).length : ℤ) ≤ D.length * halfSide M) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedFieldContour.axisSegments_walk <;> assumption
theorem axisPath_eq_flatMap_axisLeg (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    axisPath h π = ((List.finRange 4).map π).flatMap (axisLeg h) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedFieldContour.axisPath_eq_flatMap <;> assumption
theorem siteOfCoords_add_coords (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem bondContour_split (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (c : F.Site F.top × Fin 4)
    (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (hh : h ∈ centredCube F.blockSide) :
    ∃ (pre post : List PathStep) (u₁ u₂ : Fin 4 → ℤ),
      bondContour F.blockSide h π c.2 = pre ++ (c.2, true) :: post ∧
      WalkStaysIn F.blockSide 0 pre ∧ walkTarget 0 pre = u₁ ∧ u₁ ∈ centredCube F.blockSide ∧
      u₂ ∈ centredCube F.blockSide ∧ WalkStaysIn F.blockSide u₂ post ∧
      offsetSite c.1 u₁ + stepDisplacement F.depth (c.2, true) = offsetSite (c.1 + unitStep F.top c.2) u₂ ∧
      pre.length + 1 + post.length ≤ 5 * F.blockSide := by
  set z : F.Cell := c.1 with hz
  set i : Fin 4 := c.2 with hi
  set l : List PathStep := axisPath h π with hl
  obtain ⟨k, hk⟩ := id hL
  have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hhalf : halfSide F.blockSide = k := by
    unfold halfSide
    rw [hLz]
    omega
  have hc := (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff h).mp hh
  rw [hhalf] at hc
  have h0 : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
    rw [mem_centredCube_iff, hhalf]
    intro l
    simp only [Pi.zero_apply]
    omega
  obtain ⟨w1, w2, w3⟩ := walkStaysIn_flatMap_axisLeg h hh ((List.finRange 4).map π)
    ((List.nodup_finRange 4).map π.injective) 0 (fun _ => Or.inl rfl) h0 (fun _ _ => rfl)
  rw [← axisPath_eq_flatMap_axisLeg] at w1 w2 w3
  have hend : walkTarget 0 l = h := funext fun x => by
    rw [w2 x, if_pos (List.mem_map.mpr ⟨π.symm x, List.mem_finRange _, π.apply_symm_apply x⟩)]
  have hlen : (l.length : ℤ) ≤ 4 * k := by
    have : (((List.finRange 4).map π).length : ℤ) = 4 := by simp
    rw [this, hhalf] at w3
    exact w3
  set j₀ : ℕ := (k - h i).toNat with hj₀
  set j₁ : ℕ := (k + h i).toNat with hj₁
  have ej₀ : (j₀ : ℤ) = k - h i := Int.toNat_of_nonneg (by have := hc i; omega)
  have ej₁ : (j₁ : ℤ) = k + h i := Int.toNat_of_nonneg (by have := hc i; omega)
  have hLj : F.blockSide = j₀ + (1 + j₁) := by
    have : (F.blockSide : ℤ) = (j₀ : ℤ) + (1 + j₁) := by
      rw [ej₀, ej₁, hLz]
      ring
    exact_mod_cast this
  have hs1 : stepShift (i, true) = Pi.single i 1 := by simp [stepShift]
  set u₁ : Fin 4 → ℤ := h + (j₀ : ℤ) • stepShift (i, true) with hu₁
  have hu₁i : u₁ i = k := by
    simp only [hu₁, hs1, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, ej₀]
    ring
  have hu₁l : ∀ x, x ≠ i → u₁ x = h x := fun x hx => by
    simp [hu₁, hs1, Pi.single_eq_of_ne hx]
  have hu₁c : u₁ ∈ centredCube F.blockSide := by
    rw [mem_centredCube_iff, hhalf]
    intro x
    by_cases hx : x = i
    · subst hx
      rw [hu₁i]
      omega
    · rw [hu₁l x hx]
      exact hc x
  obtain ⟨r1, r2⟩ := walkStaysIn_replicate (M := F.blockSide) i true j₀ hh hu₁c
  set pre : List PathStep := l ++ List.replicate j₀ (i, true) with hpre
  have wpre : WalkStaysIn F.blockSide 0 pre := walkStaysIn_append w1 (by rw [hend]; exact r1)
  have epre : walkTarget 0 pre = u₁ := by
    rw [hpre, walkTarget_append, hend, r2]
  set z' : F.Cell := z + unitStep F.top i with hz'
  set u₂ : Fin 4 → ℤ := u₁ + Pi.single i (1 - (F.blockSide : ℤ)) with hu₂
  have hu₂i : u₂ i = -k := by
    simp only [hu₂, Pi.add_apply, Pi.single_eq_same, hu₁i, hLz]
    ring
  have hu₂l : ∀ x, x ≠ i → u₂ x = h x := fun x hx => by
    simp [hu₂, Pi.single_eq_of_ne hx, hu₁l x hx]
  have hu₂c : u₂ ∈ centredCube F.blockSide := by
    rw [mem_centredCube_iff, hhalf]
    intro x
    by_cases hx : x = i
    · subst hx
      rw [hu₂i]
      omega
    · rw [hu₂l x hx]
      exact hc x
  have hsite : offsetSite z u₁ + stepDisplacement F.depth (i, true) = offsetSite z' u₂ := by
    rw [offsetSite_add_stepDisplacement]
    unfold offsetSite
    rw [hz', cellCentre_add_unitStep hs z i, add_assoc (cellCentre F.depth z), ← siteOfCoords_add_coords]
    congr 2
    funext x
    by_cases hx : x = i
    · subst hx
      simp only [Pi.add_apply, hs1, hu₂, Pi.single_eq_same]
      ring
    · simp only [Pi.add_apply, hs1, hu₂, Pi.single_eq_of_ne hx]
      ring
  have etarget : u₂ + (j₁ : ℤ) • stepShift (i, true) = h := by
    funext x
    by_cases hx : x = i
    · subst hx
      simp only [hs1, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, hu₂i, ej₁]
      ring
    · simp [hs1, Pi.single_eq_of_ne hx, hu₂l x hx]
  obtain ⟨r3, r4⟩ := walkStaysIn_replicate (M := F.blockSide) i true j₁ hu₂c (by rw [etarget]; exact hh)
  rw [etarget] at r4
  obtain ⟨v1, -⟩ := walkStaysIn_reversePath h0 w1
  rw [hend] at v1
  set post : List PathStep := List.replicate j₁ (i, true) ++ reversePath l with hpost
  have wpost : WalkStaysIn F.blockSide u₂ post := walkStaysIn_append r3 (by rw [r4]; exact v1)
  have econt : bondContour F.blockSide h π i = pre ++ (i, true) :: post := by
    unfold bondContour
    rw [← hl, hLj, List.replicate_add, List.replicate_add]
    simp [hpre, hpost, List.append_assoc]
  have hlpre : pre.length = l.length + j₀ := by simp [hpre]
  have hlpost : post.length = j₁ + l.length := by simp [hpost, reversePath]
  refine ⟨pre, post, u₁, u₂, econt, wpre, epre, hu₁c, hu₂c, wpost, hsite, ?_⟩
  have : ((pre.length + 1 + post.length : ℕ) : ℤ) ≤ ((5 * F.blockSide : ℕ) : ℤ) := by
    push_cast
    rw [hlpre, hlpost]
    push_cast
    rw [hLz]
    have e1 : (j₀ : ℤ) + j₁ = 2 * k := by rw [ej₀, ej₁]; ring
    linarith
  exact_mod_cast this
theorem pathHolonomy_append (X : F.GaugeField F.depth) (z : F.Cell) (u : Fin 4 → ℤ) (l l' : List PathStep) :
    pathHolonomy X (offsetSite z u) (l ++ l') =
      pathHolonomy X (offsetSite z u) l * pathHolonomy X (offsetSite z (walkTarget u l)) l' := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedFieldContour.pathHolonomy_append <;> assumption
theorem pathHolonomy_congr_of_walkStaysIn (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    {X X' : F.GaugeField F.depth} (z : F.Cell)
    (hX : ∀ b : F.Site F.depth × Fin 4, enclosingCell b.1 = z → X b.1 b.2 = X' b.1 b.2) {u : Fin 4 → ℤ}
    (hu : u ∈ centredCube F.blockSide) {l : List PathStep} (h : WalkStaysIn F.blockSide u l) :
    pathHolonomy X (offsetSite z u) l = pathHolonomy X' (offsetSite z u) l := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih =>
    simp only [pathHolonomy]
    rw [offsetSite_add_stepDisplacement, ih h.1 h.2]
    congr 1
    rcases st with ⟨i, b⟩
    cases b with
    | true =>
      simpa [linkValue] using hX (offsetSite z u, i) (enclosingCell_offset hL hs z u hu)
    | false =>
      have e : offsetSite z u - unitStep F.depth i = offsetSite z (u + stepShift (i, false)) := by
        rw [← offsetSite_add_stepDisplacement z u (i, false)]
        simp [stepDisplacement, sub_eq_add_neg]
      simp only [linkValue, Bool.false_eq_true, if_false]
      rw [e, hX (offsetSite z (u + stepShift (i, false)), i) (enclosingCell_offset hL hs z _ h.1)]
theorem pathHolonomy_bondContour_congr (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    {X X' : F.GaugeField F.depth} (c : F.Site F.top × Fin 4)
    (hX : ∀ b : F.Site F.depth × Fin 4,
      (enclosingCell b.1 = c.1 ∨ enclosingCell b.1 = c.1 + unitStep F.top c.2) → X b.1 b.2 = X' b.1 b.2)
    (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (hh : h ∈ centredCube F.blockSide) :
    pathHolonomy X (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) =
      pathHolonomy X' (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) := by
  obtain ⟨pre, post, u₁, u₂, econt, wpre, epre, hu₁, hu₂, wpost, hsite, -⟩ := bondContour_split hL hs c h π hh
  have h0 : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
    rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff]
    intro l
    obtain ⟨m, hm⟩ := hL
    have hm' : (F.blockSide : ℤ) = 2 * m + 1 := by exact_mod_cast hm
    unfold halfSide
    simp only [Pi.zero_apply]
    omega
  have key : ∀ Y : F.GaugeField F.depth, pathHolonomy Y (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) =
      pathHolonomy Y (offsetSite c.1 0) pre * (linkValue Y (offsetSite c.1 u₁) (c.2, true) *
        pathHolonomy Y (offsetSite (c.1 + unitStep F.top c.2) u₂) post) := by
    intro Y
    rw [← offsetSite_zero, econt, pathHolonomy_append, epre]
    simp only [pathHolonomy, hsite]
  rw [key X, key X', pathHolonomy_congr_of_walkStaysIn hL hs c.1 (fun b hb => hX b (Or.inl hb)) h0 wpre,
    pathHolonomy_congr_of_walkStaysIn hL hs _ (fun b hb => hX b (Or.inr hb)) hu₂ wpost]
  congr 2
  simpa [linkValue] using hX (offsetSite c.1 u₁, c.2) (Or.inl (enclosingCell_offset hL hs c.1 u₁ hu₁))
theorem length_bondContour_le (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (c : F.Site F.top × Fin 4)
    (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (hh : h ∈ centredCube F.blockSide) :
    (bondContour F.blockSide h π c.2).length ≤ 5 * F.blockSide := by
  obtain ⟨pre, post, u₁, u₂, econt, -, -, -, -, -, -, hlen⟩ := bondContour_split hL hs c h π hh
  rw [econt]
  simp only [List.length_append, List.length_cons]
  omega
end Walks
section Means
theorem card_centredCube {L : ℕ} (hL : Odd L) : ((centredCube L).card : ℝ) = (L : ℝ) ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.card_centredCube_real <;> assumption
theorem card_perm_fin_four : (Fintype.card (Equiv.Perm (Fin 4)) : ℝ) = 24 := by
  simp [Fintype.card_perm, Nat.factorial]
theorem exists_norm_iteratedFDeriv_norm_le (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℍ[ℝ], 1 / 2 ≤ ‖u‖ → ‖u‖ ≤ 2 →
      ‖iteratedFDeriv ℝ p (norm : ℍ[ℝ] → ℝ) u‖ ≤ C := by
  have hU : IsOpen {u : ℍ[ℝ] | u ≠ 0} := isOpen_ne
  have hn : ContDiffOn ℝ ω (norm : ℍ[ℝ] → ℝ) {u : ℍ[ℝ] | u ≠ 0} := fun x hx =>
    (contDiffAt_norm ℝ hx).contDiffWithinAt
  have hc : ContinuousOn (iteratedFDeriv ℝ p (norm : ℍ[ℝ] → ℝ)) {u : ℍ[ℝ] | u ≠ 0} := by
    have h1 := ContDiffOn.continuousOn_iteratedFDerivWithin (m := p) hn (by exact_mod_cast le_top) hU.uniqueDiffOn
    exact h1.congr fun x hx => (iteratedFDerivWithin_of_isOpen p hU hx).symm
  have hK : IsCompact (Metric.closedBall (0 : ℍ[ℝ]) 2 \ Metric.ball (0 : ℍ[ℝ]) (1 / 2)) :=
    (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hsub : Metric.closedBall (0 : ℍ[ℝ]) 2 \ Metric.ball (0 : ℍ[ℝ]) (1 / 2) ⊆ {u : ℍ[ℝ] | u ≠ 0} := by
    intro u hu h0
    apply hu.2
    rw [h0]
    simp
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono hsub)
  refine ⟨max C 0, le_max_right _ _, fun u h1 h2 => (hC u ?_).trans (le_max_left _ _)⟩
  refine ⟨by simpa using h2, ?_⟩
  simp only [Metric.mem_ball, dist_zero_right, not_lt]
  exact h1
def normDerivBound (p : ℕ) : ℝ := (exists_norm_iteratedFDeriv_norm_le p).choose
theorem normDerivBound_nonneg (p : ℕ) : 0 ≤ normDerivBound p :=
  (exists_norm_iteratedFDeriv_norm_le p).choose_spec.1
theorem norm_iteratedFDeriv_norm_le_normDerivBound (p : ℕ) {u : ℍ[ℝ]} (h1 : 1 / 2 ≤ ‖u‖) (h2 : ‖u‖ ≤ 2) :
    ‖iteratedFDeriv ℝ p (norm : ℍ[ℝ] → ℝ) u‖ ≤ normDerivBound p :=
  (exists_norm_iteratedFDeriv_norm_le p).choose_spec.2 u h1 h2
theorem norm_iteratedFDeriv_sum_le {k : ℕ} {ι : Type} (u : Finset ι) (f : ι → (Fin k → ℝ) → ℍ[ℝ])
    (hf : ∀ i ∈ u, ContDiff ℝ ω (f i)) (j : ℕ) (b : ℝ) (h : ∀ i ∈ u, ‖iteratedFDeriv ℝ j (f i) 0‖ ≤ b) :
    ‖iteratedFDeriv ℝ j (fun σ => ∑ i ∈ u, f i σ) 0‖ ≤ u.card * b := by
  rw [iteratedFDeriv_sum (fun i hi => (hf i hi).of_le le_top), Finset.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  simpa using Finset.sum_le_sum h
variable {F : BlockFrame} {k : ℕ} (X : (Fin k → ℝ) → F.GaugeField F.depth)
theorem contDiff_contourAverage (hX : ∀ x i, ContDiff ℝ ω (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ])))
    (c : F.Site F.top × Fin 4) : ContDiff ℝ ω (fun σ => _root_.YangMills.Construction.BlockAverages.contourAverage (X σ) c) := by
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage
  exact ContDiff.const_smul _ (ContDiff.sum fun h _ => ContDiff.sum fun π _ => contDiff_pathHolonomy X hX _ _)
def holonomyBoundUpTo (B : ℕ → ℝ) (n j : ℕ) : ℝ := ∑ m ∈ Finset.range (n + 1), holonomyBound B m j
theorem holonomyBoundUpTo_nonneg {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (n j : ℕ) : 0 ≤ holonomyBoundUpTo B n j :=
  Finset.sum_nonneg fun m _ => holonomyBound_nonneg hB m j
theorem norm_iteratedFDeriv_contourAverage_le (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (hX : ∀ x i, ContDiff ℝ ω (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ]))) {B : ℕ → ℝ} (hB0 : ∀ j, 0 ≤ B j)
    (hB : ∀ x i j, ‖iteratedFDeriv ℝ j (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ])) 0‖ ≤ B j)
    (c : F.Site F.top × Fin 4) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun σ => _root_.YangMills.Construction.BlockAverages.contourAverage (X σ) c) 0‖ ≤ holonomyBoundUpTo B (5 * F.blockSide) j := by
  have hLpos : (0 : ℝ) < F.blockSide := by
    obtain ⟨m, hm⟩ := hL
    have : 0 < F.blockSide := by omega
    exact_mod_cast this
  set a : ℝ := 1 / (24 * (F.blockSide : ℝ) ^ 4) with ha
  have hsum : ContDiff ℝ ω (fun σ => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy (X σ) (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])) :=
    ContDiff.sum fun h _ => ContDiff.sum fun π _ => contDiff_pathHolonomy X hX _ _
  have e : (fun σ => _root_.YangMills.Construction.BlockAverages.contourAverage (X σ) c) = a • fun σ => ∑ h ∈ centredCube F.blockSide,
      ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy (X σ) (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) := rfl
  rw [e, iteratedFDeriv_const_smul_apply (hsum.contDiffAt.of_le le_top), norm_smul]
  have hinner : ∀ h ∈ centredCube F.blockSide, ‖iteratedFDeriv ℝ j (fun σ => ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy (X σ) (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])) 0‖ ≤
        24 * holonomyBoundUpTo B (5 * F.blockSide) j := by
    intro h hh
    have := norm_iteratedFDeriv_sum_le (k := k) (Finset.univ : Finset (Equiv.Perm (Fin 4)))
      (fun π σ => ((pathHolonomy (X σ) (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]))
      (fun π _ => contDiff_pathHolonomy X hX _ _) j (holonomyBoundUpTo B (5 * F.blockSide) j) (fun π _ => by
        refine (norm_iteratedFDeriv_pathHolonomy_le X hX hB _ _ j).trans ?_
        exact Finset.single_le_sum (f := fun m => holonomyBound B m j) (fun m _ => holonomyBound_nonneg hB0 m j)
          (Finset.mem_range.mpr (by have := length_bondContour_le hL hs c h π hh; omega)))
    rw [Finset.card_univ, card_perm_fin_four] at this
    exact this
  have h2 := norm_iteratedFDeriv_sum_le (k := k) (centredCube F.blockSide) (fun h σ => ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy (X σ) (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]))
      (fun h _ => ContDiff.sum fun π _ => contDiff_pathHolonomy X hX _ _) j _ hinner
  rw [card_centredCube hL] at h2
  have ha0 : 0 ≤ a := by positivity
  calc ‖a‖ * _ ≤ a * ((F.blockSide : ℝ) ^ 4 * (24 * holonomyBoundUpTo B (5 * F.blockSide) j)) := by
        rw [Real.norm_of_nonneg ha0]
        exact mul_le_mul_of_nonneg_left h2 ha0
    _ = holonomyBoundUpTo B (5 * F.blockSide) j := by
        rw [ha]
        field_simp
theorem norm_contourAverage_near_one (hcont : ChartedFieldContourBound) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (hw : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ 1 / (64 * (F.blockSide : ℝ)))
    (c : F.Site F.top × Fin 4) :
    1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w V) c‖ ∧ ‖_root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w V) c‖ ≤ 2 := by
  have hLpos : (0 : ℝ) < F.blockSide := by
    obtain ⟨m, hm⟩ := hL
    have : 0 < F.blockSide := by omega
    exact_mod_cast this
  set gi : ℍ[ℝ] := (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hgi
  set H : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π =>
    ((pathHolonomy (chartedField w V) (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])
    with hH
  have hnear : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖H h π * gi - 1‖ ≤ 5 / 64 := by
    intro h hh π
    have h1 := hcont F w V (1 / (64 * (F.blockSide : ℝ))) hL hs (by positivity) hw c h π hh
    have h2 : 5 * (F.blockSide : ℝ) * (1 / (64 * (F.blockSide : ℝ))) = 5 / 64 := by
      field_simp
    rw [h2] at h1
    exact h1
  set a : ℝ := 1 / (24 * (F.blockSide : ℝ) ^ 4) with ha
  have hcount : a * ((centredCube F.blockSide).card * 24) = 1 := by
    rw [card_centredCube hL, ha]
    field_simp
  have e1 : ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (H h π * gi - 1) =
      (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), H h π) * gi -
        (((centredCube F.blockSide).card * 24 : ℝ)) • (1 : ℍ[ℝ]) := by
    have e2 : ∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℍ[ℝ]) =
        (((centredCube F.blockSide).card * 24 : ℝ)) • (1 : ℍ[ℝ]) := by
      simp only [Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, card_perm_fin_four, smul_smul]
    rw [← e2, Finset.sum_mul]
    simp only [Finset.sum_mul, Finset.sum_sub_distrib]
  have e3 : _root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w V) c * gi - 1 =
      a • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (H h π * gi - 1) := by
    have e4 : _root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w V) c =
        a • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), H h π := rfl
    rw [e1, smul_sub, smul_smul, hcount, one_smul, e4, smul_mul_assoc]
  have hnorm : ‖_root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w V) c * gi - 1‖ ≤ 5 / 64 := by
    rw [e3, norm_smul, Real.norm_of_nonneg (by positivity)]
    have b1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (H h π * gi - 1)‖ ≤
        (centredCube F.blockSide).card * (24 * (5 / 64)) := by
      have := norm_sum_le_of_le (centredCube F.blockSide) (n := fun _ => (24 : ℝ) * (5 / 64))
        (f := fun h => ∑ π : Equiv.Perm (Fin 4), (H h π * gi - 1)) (fun h hh => by
          have := norm_sum_le_of_le (Finset.univ : Finset (Equiv.Perm (Fin 4))) (n := fun _ => (5 / 64 : ℝ))
            (f := fun π => H h π * gi - 1) (fun π _ => hnear h hh π)
          simpa [Finset.card_univ, card_perm_fin_four] using this)
      simpa using this
    calc a * _ ≤ a * ((centredCube F.blockSide).card * (24 * (5 / 64))) :=
          mul_le_mul_of_nonneg_left b1 (by positivity)
      _ = (a * ((centredCube F.blockSide).card * 24)) * (5 / 64) := by ring
      _ = 5 / 64 := by rw [hcount, one_mul]
  have hM : ‖_root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w V) c * gi‖ = ‖_root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w V) c‖ := by
    rw [norm_mul, hgi, norm_unitQuaternion, mul_one]
  have t1 := norm_sub_norm_le (1 : ℍ[ℝ]) (_root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w V) c * gi)
  have t2 := norm_sub_norm_le (_root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w V) c * gi) (1 : ℍ[ℝ])
  rw [norm_sub_rev] at t1
  rw [hM, norm_one] at t1 t2
  constructor <;> linarith
end Means
def reCLM : ℍ[ℝ] →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  { toFun := fun q => q.re
    map_add' := fun a b => by simp
    map_smul' := fun c a => by simp }
end FitAlongTranslates
open FitAlongTranslates BlockOffsets in
theorem blockFitAnalyticAlongTranslates_holds (hB : TranslatedChartAnalytic) (hcover : BlocksCoverLowerLevel)
    (hcont : ChartedFieldContourBound) (hC : Calculus.CompositeDerivativesAtPoint) :
    BlockFitAnalyticAlongTranslates := by
  classical
  obtain ⟨D, hD0, hD⟩ := hB
  obtain ⟨-, -, hComp, -⟩ := hC
  intro L hLo
  set Hk : ℕ → ℕ → ℝ := fun k j => holonomyBoundUpTo (D k) (5 * L) j with hHk
  have hHk0 : ∀ k j, 0 ≤ Hk k j := fun k j => holonomyBoundUpTo_nonneg (hD0 k) _ j
  set NB : ℕ → ℝ := fun j => ∑ p ∈ Finset.range (j + 1), normDerivBound p with hNB
  have hNB0 : ∀ j, 0 ≤ NB j := fun j => Finset.sum_nonneg fun p _ => normDerivBound_nonneg p
  set Dm : ℕ → ℕ → ℝ := fun k j => ∑ s ∈ Finset.range (j + 1), Hk k s with hDm
  have hDm0 : ∀ k j, 0 ≤ Dm k j := fun k j => Finset.sum_nonneg fun s _ => hHk0 k s
  refine ⟨fun k j => (Fintype.card (OrderedFinpartition j) : ℝ) * NB j * (Dm k j + 1) ^ j +
    ‖reCLM‖ * leibnizBound (Hk k) (D k) j, fun k j => ?_, ?_⟩
  · have h1 := hNB0 j
    have h2 := hDm0 k j
    have h3 := leibnizBound_nonneg (hHk0 k) (hD0 k) j
    have h4 : 0 ≤ ‖reCLM‖ := ContinuousLinearMap.opNorm_nonneg _
    positivity
  intro F w V k ξ μ c hFL hs hw
  subst hFL
  have hDc := (hD F w V k ξ μ).1
  have hDb := (hD F w V k ξ μ).2
  set X : (Fin k → ℝ) → F.GaugeField F.depth := fun σ => translatedChart w V ξ μ σ with hXdef
  have hX : ∀ x i, ContDiff ℝ ω (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ])) := fun x i => (hDb x i).1
  set M : (Fin k → ℝ) → ℍ[ℝ] := fun σ => _root_.YangMills.Construction.BlockAverages.contourAverage (X σ) c with hM
  have hMc : ContDiff ℝ ω M := contDiff_contourAverage X hX c
  have hM0 : M 0 = _root_.YangMills.Construction.BlockAverages.contourAverage (chartedField w V) c := by
    have e1 : shiftedCoords w ξ 0 = w := by
      funext x i
      simp [shiftedCoords]
    have e0 : expUnit (0 : imaginaryQuaternions) = 1 := by
      apply Subtype.ext
      show NormedSpace.exp (((0 : imaginaryQuaternions)) : ℍ[ℝ]) = 1
      simp
    have e2 : translatedTop V μ 0 = V := by
      funext y i
      simp [translatedTop, leftTranslate, e0]
    simp only [hM, hXdef, translatedChart, e1, e2]
  obtain ⟨n1, n2⟩ := norm_contourAverage_near_one hcont hLo hs w V hw c
  rw [← hM0] at n1 n2
  have hne : M 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at n1
    norm_num at n1
  set T : (Fin k → ℝ) → ℍ[ℝ] := fun σ => star ((translatedTop V μ σ c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) with hT
  have hTc : ContDiff ℝ ω T := conjCLM.contDiff.comp (hDc c.1 c.2).1
  have hfit : (fun σ : Fin k → ℝ => blockFit (X σ) (translatedTop V μ σ) c) =
      (fun σ => ‖M σ‖) - fun σ => reCLM (M σ * T σ) := rfl
  have hNa : AnalyticAt ℝ (norm : ℍ[ℝ] → ℝ) (M 0) := (contDiffAt_norm ℝ hne (n := ω)).analyticAt
  have hMa : AnalyticAt ℝ M 0 := hMc.contDiffAt.analyticAt
  have hAN : AnalyticAt ℝ (fun σ => ‖M σ‖) 0 := hNa.comp hMa
  have hRc : ContDiff ℝ ω (fun σ => reCLM (M σ * T σ)) := reCLM.contDiff.comp (hMc.mul hTc)
  have hAR : AnalyticAt ℝ (fun σ => reCLM (M σ * T σ)) 0 := hRc.contDiffAt.analyticAt
  refine ⟨?_, ?_, ?_⟩
  · rw [hfit]
    exact hAN.sub hAR
  · intro hξ hμ j v hv
    have hBx : ∀ x i j', ‖iteratedFDeriv ℝ j' (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ])) 0‖ ≤ D k j' := by
      intro x i j'
      refine (hDb x i).2.1 ?_ (fun l => hξ l (x, i)) (fun l => hμ l _ _) j'
      by_cases ht : IsAxialTreeBond (x, i)
      · exact Or.inr ht
      · left
        have hmem : (x, i) ∈ chordBonds (finiteCells F) := by
          have hpos : ∀ i, 0 < F.extent i := fun i => by
            have := hs i
            omega
          unfold chordBonds innerBonds
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hcover F hLo hpos _, Finset.mem_univ _⟩, hcover F hLo hpos _⟩, ht⟩
        have h1 := hw _ hmem
        refine h1.trans ?_
        have hL1 : (1 : ℝ) ≤ F.blockSide := by
          obtain ⟨m, hm⟩ := hLo
          have : 1 ≤ F.blockSide := by omega
          exact_mod_cast this
        rw [div_le_one (by positivity)]
        linarith
    have hMb : ∀ j', ‖iteratedFDeriv ℝ j' M 0‖ ≤ Hk k j' := fun j' =>
      norm_iteratedFDeriv_contourAverage_le X hLo hs hX (hD0 k) hBx c j'
    have hTb : ∀ j', ‖iteratedFDeriv ℝ j' T 0‖ ≤ D k j' := fun j' =>
      (norm_iteratedFDeriv_star_le (hDc c.1 c.2).1 j').trans ((hDc c.1 c.2).2 (fun l => hμ l _ _) j')
    have hcompo := hComp j (Fin k → ℝ) ℍ[ℝ] ℝ (norm : ℍ[ℝ] → ℝ) M 0 (NB j) (Dm k j) (hNB0 j) (hDm0 k j) hMa hNa
      (fun p hp => (norm_iteratedFDeriv_norm_le_normDerivBound p n1 n2).trans
        (Finset.single_le_sum (f := fun p => normDerivBound p) (fun p _ => normDerivBound_nonneg p)
          (Finset.mem_range.mpr (by omega))))
      (fun s _ hs' => (hMb s).trans
        (Finset.single_le_sum (f := fun s => Hk k s) (fun s _ => hHk0 k s) (Finset.mem_range.mpr (by omega))))
      v hv
    have hR : |iteratedFDeriv ℝ j (fun σ => reCLM (M σ * T σ)) 0 v| ≤ ‖reCLM‖ * leibnizBound (Hk k) (D k) j := by
      have h1 := reCLM.iteratedFDeriv_comp_left (f := fun σ => M σ * T σ) (x := 0) (n := ω)
        (hMc.mul hTc).contDiffAt (i := j) le_top
      have h2 : (fun σ => reCLM (M σ * T σ)) = reCLM ∘ fun σ => M σ * T σ := rfl
      rw [h2, h1]
      have h3 : ‖(reCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fun σ => M σ * T σ) 0)) v‖ ≤
          ‖reCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fun σ => M σ * T σ) 0)‖ * ∏ m, ‖v m‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      have h4 : ∏ m, ‖v m‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) fun m _ => hv m
      have h5 : ‖reCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fun σ => M σ * T σ) 0)‖ ≤
          ‖reCLM‖ * leibnizBound (Hk k) (D k) j :=
        (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
          (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le_leibnizBound hMc hTc hMb hTb j)
            (ContinuousLinearMap.opNorm_nonneg _))
      have h6 := norm_nonneg (reCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fun σ => M σ * T σ) 0))
      have h7 : 0 ≤ ∏ m, ‖v m‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
      calc |_| = ‖(reCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fun σ => M σ * T σ) 0)) v‖ := rfl
        _ ≤ _ := h3
        _ ≤ ‖reCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fun σ => M σ * T σ) 0)‖ * 1 :=
            mul_le_mul_of_nonneg_left h4 h6
        _ ≤ _ := by rw [mul_one]; exact h5
    have hsplit : iteratedFDeriv ℝ j (fun σ : Fin k → ℝ => blockFit (X σ) (translatedTop V μ σ) c) 0 v =
        iteratedFDeriv ℝ j (fun σ => ‖M σ‖) 0 v - iteratedFDeriv ℝ j (fun σ => reCLM (M σ * T σ)) 0 v := by
      rw [hfit, iteratedFDeriv_sub_apply (hAN.contDiffAt) (hAR.contDiffAt)]
      rfl
    rw [hsplit]
    have hN' : |iteratedFDeriv ℝ j (fun σ => ‖M σ‖) 0 v| ≤
        (Fintype.card (OrderedFinpartition j) : ℝ) * NB j * (Dm k j + 1) ^ j := hcompo
    exact (abs_sub _ _).trans (add_le_add hN' hR)
  · intro σ σ' h
    have hcell : ∀ b : F.Site F.depth × Fin 4,
        (enclosingCell b.1 = c.1 ∨ enclosingCell b.1 = c.1 + unitStep F.top c.2) →
        X σ b.1 b.2 = X σ' b.1 b.2 := fun b hb =>
      (hDb b.1 b.2).2.2 σ σ' fun l hl => h l (Or.inr ⟨b, hb, hl⟩)
    have hmean : _root_.YangMills.Construction.BlockAverages.contourAverage (X σ) c = _root_.YangMills.Construction.BlockAverages.contourAverage (X σ') c := by
      unfold _root_.YangMills.Construction.BlockAverages.contourAverage
      congr 1
      refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun π _ => ?_
      rw [pathHolonomy_bondContour_congr hLo hs c hcell p π hp]
    have htop : translatedTop V μ σ c.1 c.2 = translatedTop V μ σ' c.1 c.2 := by
      have e : ∑ l, σ l • μ l c.1 c.2 = ∑ l, σ' l • μ l c.1 c.2 :=
        Finset.sum_congr rfl fun l _ => by
          by_cases hl : μ l c.1 c.2 = 0
          · simp [hl]
          · rw [h l (Or.inl hl)]
      show expUnit (∑ l, σ l • μ l c.1 c.2) * V c.1 c.2 = expUnit (∑ l, σ' l • μ l c.1 c.2) * V c.1 c.2
      rw [e]
    show blockFit (X σ) (translatedTop V μ σ) c = blockFit (X σ') (translatedTop V μ σ') c
    unfold blockFit
    rw [hmean, htop]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
