import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdChainAtEveryLevel.FactsOfTheLogarithm
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOverContoursOfAFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages YangMills.Construction.LatticePaths
variable {F : BlockFrame}
def componentAlong (X : imaginaryQuaternions) (q : ℍ[ℝ]) : ℝ := - (q * (X : ℍ[ℝ])).re
def componentForm (X : imaginaryQuaternions) {j : ℕ} (W : F.GaugeField j) : LevelForm F j :=
  fun x i => componentAlong X (W x i : ℍ[ℝ])
def abelianField (X : imaginaryQuaternions) {j : ℕ} (θ : LevelForm F j) : F.GaugeField j :=
  fun x i => expUnit (θ x i • X)
theorem componentAlong_eq_imParts (X : imaginaryQuaternions) (q : ℍ[ℝ]) :
    componentAlong X q = q.imI * (X : ℍ[ℝ]).imI + q.imJ * (X : ℍ[ℝ]).imJ + q.imK * (X : ℍ[ℝ]).imK := by
  have hX : (X : ℍ[ℝ]).re = 0 := X.2
  simp [componentAlong, hX]
  ring
theorem componentAlong_add (X : imaginaryQuaternions) (p q : ℍ[ℝ]) :
    componentAlong X (p + q) = componentAlong X p + componentAlong X q := by
  simp only [componentAlong_eq_imParts]
  simp
  ring
theorem componentAlong_sub (X : imaginaryQuaternions) (p q : ℍ[ℝ]) :
    componentAlong X (p - q) = componentAlong X p - componentAlong X q := by
  simp only [componentAlong_eq_imParts]
  simp
  ring
theorem componentAlong_smul (X : imaginaryQuaternions) (r : ℝ) (q : ℍ[ℝ]) :
    componentAlong X (r • q) = r * componentAlong X q := by
  simp only [componentAlong_eq_imParts]
  simp
  ring
theorem componentAlong_one (X : imaginaryQuaternions) : componentAlong X 1 = 0 := by
  simp [componentAlong_eq_imParts]
theorem componentAlong_zero (X : imaginaryQuaternions) : componentAlong X 0 = 0 := by
  simp [componentAlong_eq_imParts]
theorem componentAlong_sum {ι : Type} (X : imaginaryQuaternions) (s : Finset ι) (f : ι → ℍ[ℝ]) :
    componentAlong X (∑ k ∈ s, f k) = ∑ k ∈ s, componentAlong X (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [componentAlong_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, componentAlong_add, ih]
theorem componentAlong_star (X : imaginaryQuaternions) (q : ℍ[ℝ]) :
    componentAlong X (star q) = - componentAlong X q := by
  simp only [componentAlong_eq_imParts]
  simp
  ring
theorem componentAlong_inv (X : imaginaryQuaternions) (g : UnitQuaternion) :
    componentAlong X ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = - componentAlong X (g : ℍ[ℝ]) := by
  rw [coe_unitQuaternion_inv, componentAlong_star]
theorem componentAlong_self {X : imaginaryQuaternions} (hX : ‖X‖ = 1) : componentAlong X (X : ℍ[ℝ]) = 1 := by
  have h : (X : ℍ[ℝ]).re = 0 := X.2
  have h1 : Quaternion.normSq (X : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self]
    have : ‖(X : ℍ[ℝ])‖ = 1 := hX
    rw [this]
    norm_num
  rw [Quaternion.normSq_def'] at h1
  rw [componentAlong_eq_imParts]
  rw [h] at h1
  nlinarith
theorem componentAlong_sq_add_re_sq_le {X : imaginaryQuaternions} (hX : ‖X‖ = 1) (q : ℍ[ℝ]) :
    componentAlong X q ^ 2 + q.re ^ 2 ≤ ‖q‖ ^ 2 := by
  have h : (X : ℍ[ℝ]).re = 0 := X.2
  have h1 : Quaternion.normSq (X : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self]
    have : ‖(X : ℍ[ℝ])‖ = 1 := hX
    rw [this]
    norm_num
  rw [Quaternion.normSq_def', h] at h1
  have h2 : ‖q‖ ^ 2 = Quaternion.normSq q := by rw [Quaternion.normSq_eq_norm_mul_self, sq]
  rw [h2, Quaternion.normSq_def', componentAlong_eq_imParts]
  set u := (X : ℍ[ℝ]).imI
  set v := (X : ℍ[ℝ]).imJ
  set w := (X : ℍ[ℝ]).imK
  set b := q.imI
  set c := q.imJ
  set d := q.imK
  have key : (b * u + c * v + d * w) ^ 2 ≤ b ^ 2 + c ^ 2 + d ^ 2 := by
    have e : (b ^ 2 + c ^ 2 + d ^ 2) * (u ^ 2 + v ^ 2 + w ^ 2) - (b * u + c * v + d * w) ^ 2 =
        (b * v - c * u) ^ 2 + (b * w - d * u) ^ 2 + (c * w - d * v) ^ 2 := by ring
    have e1 : u ^ 2 + v ^ 2 + w ^ 2 = 1 := by linarith
    rw [e1] at e
    nlinarith [sq_nonneg (b * v - c * u), sq_nonneg (b * w - d * u), sq_nonneg (c * w - d * v)]
  linarith
theorem abs_componentAlong_le {X : imaginaryQuaternions} (hX : ‖X‖ = 1) (q : ℍ[ℝ]) :
    |componentAlong X q| ≤ ‖q‖ := by
  have := componentAlong_sq_add_re_sq_le hX q
  apply abs_le_of_sq_le_sq _ (norm_nonneg q)
  nlinarith [sq_nonneg q.re]
theorem abs_componentAlong_mul_sub_le {X : imaginaryQuaternions} (hX : ‖X‖ = 1) (p q : ℍ[ℝ]) :
    |componentAlong X (p * q) - componentAlong X p - componentAlong X q| ≤ ‖p - 1‖ * ‖q - 1‖ := by
  have e : p * q = p + q - 1 + (p - 1) * (q - 1) := by noncomm_ring
  have e2 : componentAlong X (p * q) - componentAlong X p - componentAlong X q =
      componentAlong X ((p - 1) * (q - 1)) := by
    rw [e, componentAlong_add, componentAlong_sub, componentAlong_add, componentAlong_one]
    ring
  rw [e2]
  refine (abs_componentAlong_le hX _).trans ?_
  rw [norm_mul]
theorem componentAlong_sq_div_two_le {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {q : ℍ[ℝ]} (hq : ‖q‖ ≤ 1) :
    componentAlong X q ^ 2 / 2 ≤ ‖q‖ - q.re := by
  have h := componentAlong_sq_add_re_sq_le hX q
  have h1 : q.re ≤ ‖q‖ := quaternion_re_le_norm q
  have h2 : ‖q‖ ^ 2 - q.re ^ 2 ≤ 2 * (‖q‖ - q.re) := by
    have : -‖q‖ ≤ q.re := by
      have := quaternion_re_le_norm (-q)
      simp at this
      linarith
    nlinarith
  linarith
theorem norm_linkValue_sub_one_le {j : ℕ} (W : F.GaugeField j) {ε : ℝ}
    (hW : ∀ x i, ‖(W x i : ℍ[ℝ]) - 1‖ ≤ ε) (x : F.Site j)
    (st : PathStep) : ‖(linkValue W x st : ℍ[ℝ]) - 1‖ ≤ ε := by
  unfold linkValue
  by_cases h : st.2 = true
  · simp only [h, if_true]
    exact hW _ _
  · simp only [h, Bool.false_eq_true, if_false]
    rw [norm_coe_inv_sub_one]
    exact hW _ _
theorem pathHolonomy_near_one_and_componentAlong {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {j : ℕ}
    (W : F.GaugeField j) {ε : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ x i, ‖(W x i : ℍ[ℝ]) - 1‖ ≤ ε) (x : F.Site j) (l : List PathStep) :
    ‖(pathHolonomy W x l : ℍ[ℝ]) - 1‖ ≤ l.length * ε ∧
      |componentAlong X (pathHolonomy W x l : ℍ[ℝ]) - pathSum (componentForm X W) x l| ≤
        (l.length : ℝ) ^ 2 * ε ^ 2 := by
  induction l generalizing x with
  | nil =>
    simp [pathHolonomy, pathSum, componentAlong_one]
  | cons st r ih =>
    obtain ⟨h1, h2⟩ := ih (x + stepDisplacement j st)
    have hp := norm_linkValue_sub_one_le W hW x st
    have hh : pathHolonomy W x (st :: r) =
        linkValue W x st * pathHolonomy W (x + stepDisplacement j st) r := rfl
    have hc : componentAlong X (linkValue W x st : ℍ[ℝ]) =
        (if st.2 then componentForm X W x st.1 else - componentForm X W (x - unitStep j st.1) st.1) := by
      unfold linkValue componentForm
      by_cases h : st.2 = true
      · simp only [h, if_true]
      · simp only [h, Bool.false_eq_true, if_false]
        rw [componentAlong_inv]
    have hf : pathSum (componentForm X W) x (st :: r) =
        (if st.2 then componentForm X W x st.1 else - componentForm X W (x - unitStep j st.1) st.1) +
          pathSum (componentForm X W) (x + stepDisplacement j st) r := rfl
    have hm := abs_componentAlong_mul_sub_le hX (linkValue W x st : ℍ[ℝ])
      (pathHolonomy W (x + stepDisplacement j st) r : ℍ[ℝ])
    have hcoe : ((linkValue W x st * pathHolonomy W (x + stepDisplacement j st) r : UnitQuaternion) : ℍ[ℝ]) =
        (linkValue W x st : ℍ[ℝ]) * (pathHolonomy W (x + stepDisplacement j st) r : ℍ[ℝ]) := rfl
    have hn : (((st :: r).length : ℕ) : ℝ) = (r.length : ℝ) + 1 := by simp
    rw [hh, hf, hn, hcoe, ← hc]
    set n : ℝ := (r.length : ℝ) with hndef
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    constructor
    · have := norm_coe_mul_sub_one_le (linkValue W x st) (pathHolonomy W (x + stepDisplacement j st) r)
      rw [hcoe] at this
      nlinarith
    · have h3 : ‖(linkValue W x st : ℍ[ℝ]) - 1‖ *
          ‖(pathHolonomy W (x + stepDisplacement j st) r : ℍ[ℝ]) - 1‖ ≤ ε * (n * ε) :=
        mul_le_mul hp h1 (norm_nonneg _) hε
      have e : componentAlong X ((linkValue W x st : ℍ[ℝ]) *
            (pathHolonomy W (x + stepDisplacement j st) r : ℍ[ℝ])) -
          (componentAlong X (linkValue W x st : ℍ[ℝ]) +
            pathSum (componentForm X W) (x + stepDisplacement j st) r) =
          (componentAlong X ((linkValue W x st : ℍ[ℝ]) *
              (pathHolonomy W (x + stepDisplacement j st) r : ℍ[ℝ])) -
            componentAlong X (linkValue W x st : ℍ[ℝ]) -
            componentAlong X (pathHolonomy W (x + stepDisplacement j st) r : ℍ[ℝ])) +
          (componentAlong X (pathHolonomy W (x + stepDisplacement j st) r : ℍ[ℝ]) -
            pathSum (componentForm X W) (x + stepDisplacement j st) r) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      nlinarith [sq_nonneg ε]
theorem pathSum_plaquetteLoop {j : ℕ} (B : LevelForm F j) (x : F.Site j) (μ ν : Fin 4) :
    pathSum B x [(μ, true), (ν, true), (μ, false), (ν, false)] = plaquetteCurl B x μ ν := by
  have e1 : x + unitStep j μ + unitStep j ν - unitStep j μ = x + unitStep j ν := by abel
  have e2 : x + unitStep j μ + unitStep j ν + - unitStep j μ - unitStep j ν = x := by abel
  simp [pathSum, stepDisplacement, plaquetteCurl, e1, e2]
  ring
theorem norm_contourAverage_le_one (hL : Odd F.blockSide) {j : ℕ} (W : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) :
    ‖BlockAverages.contourAverage W c‖ ≤ 1 := by
  have hL0 : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hL.pos.ne'
  unfold BlockAverages.contourAverage
  rw [norm_smul]
  have h1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy W (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤
        24 * (F.blockSide : ℝ) ^ 4 := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ h ∈ centredCube F.blockSide, ‖∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy W (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤ 24 := by
      intro h _
      refine (norm_sum_le _ _).trans ?_
      simp only [norm_coe_unitQuaternion, Finset.sum_const, card_perm_fin_four]
      norm_num
    refine (Finset.sum_le_sum this).trans ?_
    simp only [Finset.sum_const, card_centredCube hL, nsmul_eq_mul]
    push_cast
    linarith
  have h2 : ‖(1 / (24 * (F.blockSide : ℝ) ^ 4))‖ = 1 / (24 * (F.blockSide : ℝ) ^ 4) := by
    rw [Real.norm_of_nonneg]
    positivity
  rw [h2]
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤
        1 / (24 * (F.blockSide : ℝ) ^ 4) * (24 * (F.blockSide : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 := by field_simp
theorem componentAlong_sq_div_two_le_blockFit {X : imaginaryQuaternions} (hX : ‖X‖ = 1)
    (hL : Odd F.blockSide) {j : ℕ} (W : F.GaugeField j) (Y : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) :
    componentAlong X (BlockAverages.contourAverage W c * ((Y c.1 c.2)⁻¹ : UnitQuaternion)) ^ 2 / 2 ≤
      blockFit W Y c := by
  have h1 : ‖BlockAverages.contourAverage W c * ((Y c.1 c.2)⁻¹ : UnitQuaternion)‖ =
      ‖BlockAverages.contourAverage W c‖ := by
    rw [norm_mul, norm_coe_unitQuaternion, mul_one]
  have h2 := componentAlong_sq_div_two_le hX
    (q := BlockAverages.contourAverage W c * ((Y c.1 c.2)⁻¹ : UnitQuaternion))
    (by rw [h1]; exact norm_contourAverage_le_one hL W c)
  unfold blockFit
  rw [h1] at h2
  exact h2
theorem componentAlong_sq_div_two_le_plaquette {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {j : ℕ}
    (W : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4) :
    componentAlong X (plaquetteHolonomy W p : ℍ[ℝ]) ^ 2 / 2 ≤
      1 - ((plaquetteHolonomy W p : UnitQuaternion) : ℍ[ℝ]).re := by
  have h := componentAlong_sq_div_two_le hX (q := (plaquetteHolonomy W p : ℍ[ℝ]))
    (by rw [norm_coe_unitQuaternion])
  rwa [norm_coe_unitQuaternion] at h
theorem abs_componentAlong_plaquetteHolonomy_sub_curl_le {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {j : ℕ}
    (W : F.GaugeField j) {ε : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ x i, ‖(W x i : ℍ[ℝ]) - 1‖ ≤ ε) (x : F.Site j) (μ ν : Fin 4) :
    |componentAlong X (plaquetteHolonomy W (x, μ, ν) : ℍ[ℝ]) - plaquetteCurl (componentForm X W) x μ ν| ≤
      16 * ε ^ 2 := by
  have h := (pathHolonomy_near_one_and_componentAlong hX W hε hW x
    [(μ, true), (ν, true), (μ, false), (ν, false)]).2
  rw [pathSum_plaquetteLoop] at h
  have e : (([(μ, true), (ν, true), (μ, false), (ν, false)] : List PathStep).length : ℝ) ^ 2 = 16 := by
    norm_num
  rw [e] at h
  exact h
theorem abs_componentAlong_contourAverage_sub_le {X : imaginaryQuaternions} (hX : ‖X‖ = 1)
    (hL : Odd F.blockSide) {j : ℕ} (W : F.GaugeField j) (Y : F.GaugeField (j + 1))
    {ε : ℝ} (hε : 0 ≤ ε) (hW : ∀ x i, ‖(W x i : ℍ[ℝ]) - 1‖ ≤ ε) (hY : ∀ x i, ‖(Y x i : ℍ[ℝ]) - 1‖ ≤ ε)
    (c : F.Site (j + 1) × Fin 4) :
    |componentAlong X (BlockAverages.contourAverage W c * ((Y c.1 c.2)⁻¹ : UnitQuaternion)) -
        (ColdStepAtMirrorFrames.contourAverage (componentForm X W) c.1 c.2 - componentForm X Y c.1 c.2)| ≤
      (25 * (F.blockSide : ℝ) ^ 2 + 5 * (F.blockSide : ℝ)) * ε ^ 2 := by
  have hL0 : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hL.pos.ne'
  have hL1 : 1 ≤ F.blockSide := hL.pos
  set g : ℍ[ℝ] := (((Y c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hg
  set N : ℝ := 24 * (F.blockSide : ℝ) ^ 4 with hN
  have hNp : 0 < N := by positivity
  set H : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π =>
    ((pathHolonomy W (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) with hH
  set T : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℝ := fun h π =>
    pathSum (componentForm X W) (refineSite c.1) (bondContour F.blockSide h π c.2) with hT
  have e1 : componentAlong X (BlockAverages.contourAverage W c * g) =
      (1 / N) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), componentAlong X (H h π * g) := by
    unfold BlockAverages.contourAverage
    rw [smul_mul_assoc, componentAlong_smul, Finset.sum_mul, componentAlong_sum]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_mul, componentAlong_sum]
  have e2 : ColdStepAtMirrorFrames.contourAverage (componentForm X W) c.1 c.2 =
      (1 / N) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), T h π := rfl
  have e3 : componentForm X Y c.1 c.2 =
      (1 / N) * ∑ h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), componentForm X Y c.1 c.2 := by
    simp only [Finset.sum_const, card_perm_fin_four, card_centredCube hL, nsmul_eq_mul, hN]
    push_cast
    field_simp
  have e4 : componentAlong X (BlockAverages.contourAverage W c * g) -
      (ColdStepAtMirrorFrames.contourAverage (componentForm X W) c.1 c.2 - componentForm X Y c.1 c.2) =
      (1 / N) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        (componentAlong X (H h π * g) - (T h π - componentForm X Y c.1 c.2)) := by
    rw [e1, e2]
    simp only [Finset.sum_sub_distrib, mul_sub]
    rw [← e3]
  rw [e4, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
  set C : ℝ := (25 * (F.blockSide : ℝ) ^ 2 + 5 * (F.blockSide : ℝ)) * ε ^ 2 with hC
  have hterm : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      |componentAlong X (H h π * g) - (T h π - componentForm X Y c.1 c.2)| ≤ C := by
    intro h hh π
    obtain ⟨n1, n2⟩ := pathHolonomy_near_one_and_componentAlong hX W hε hW (refineSite c.1)
      (bondContour F.blockSide h π c.2)
    have hlen : ((bondContour F.blockSide h π c.2).length : ℝ) ≤ 5 * (F.blockSide : ℝ) := by
      exact_mod_cast length_bondContour_le π c.2 hL1 hh
    have hlen0 : (0 : ℝ) ≤ ((bondContour F.blockSide h π c.2).length : ℝ) := Nat.cast_nonneg _
    have hg1 : ‖g - 1‖ ≤ ε := by
      rw [hg, norm_coe_inv_sub_one]
      exact hY _ _
    have hm := abs_componentAlong_mul_sub_le hX (H h π) g
    have hgc : componentAlong X g = - componentForm X Y c.1 c.2 := componentAlong_inv X _
    have hH1 : ‖H h π - 1‖ ≤ 5 * (F.blockSide : ℝ) * ε :=
      n1.trans (mul_le_mul_of_nonneg_right hlen hε)
    have hH2 : |componentAlong X (H h π) - T h π| ≤ (5 * (F.blockSide : ℝ)) ^ 2 * ε ^ 2 := by
      refine n2.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg ε))
      exact pow_le_pow_left₀ hlen0 hlen 2
    have hprod : ‖H h π - 1‖ * ‖g - 1‖ ≤ 5 * (F.blockSide : ℝ) * ε * ε :=
      mul_le_mul hH1 hg1 (norm_nonneg _) (by positivity)
    have e : componentAlong X (H h π * g) - (T h π - componentForm X Y c.1 c.2) =
        (componentAlong X (H h π * g) - componentAlong X (H h π) - componentAlong X g) +
          (componentAlong X (H h π) - T h π) := by
      rw [hgc]
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [hC]
    nlinarith
  have hsum : |∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      (componentAlong X (H h π * g) - (T h π - componentForm X Y c.1 c.2))| ≤ N * C := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ h ∈ centredCube F.blockSide, |∑ π : Equiv.Perm (Fin 4),
        (componentAlong X (H h π * g) - (T h π - componentForm X Y c.1 c.2))| ≤ 24 * C := by
      intro h hh
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun π _ => hterm h hh π).trans ?_
      simp only [Finset.sum_const, card_perm_fin_four, nsmul_eq_mul]
      norm_num
    refine (Finset.sum_le_sum this).trans ?_
    simp only [Finset.sum_const, card_centredCube hL, nsmul_eq_mul, hN]
    push_cast
    linarith
  calc 1 / N * _ ≤ 1 / N * (N * C) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C := by field_simp
theorem coe_expUnit_smul {X : imaginaryQuaternions} (hX : ‖X‖ = 1) (θ : ℝ) :
    ((expUnit (θ • X) : UnitQuaternion) : ℍ[ℝ]) = (Real.cos θ : ℍ[ℝ]) + Real.sin θ • (X : ℍ[ℝ]) := by
  have hw : (((θ • X : imaginaryQuaternions)) : ℍ[ℝ]).re = 0 := (θ • X).2
  have hn : ‖(((θ • X : imaginaryQuaternions)) : ℍ[ℝ])‖ = |θ| := by
    have : ‖(X : ℍ[ℝ])‖ = 1 := hX
    rw [Submodule.coe_smul, norm_smul, this, mul_one, Real.norm_eq_abs]
  show NormedSpace.exp (((θ • X : imaginaryQuaternions)) : ℍ[ℝ]) = _
  rw [Quaternion.exp_of_re_eq_zero _ hw, hn, Real.cos_abs, Submodule.coe_smul, smul_smul]
  congr 2
  by_cases h0 : θ = 0
  · simp [h0]
  · rcases lt_or_gt_of_ne h0 with h | h
    · rw [abs_of_neg h, Real.sin_neg]
      field_simp
    · rw [abs_of_pos h]
      field_simp
theorem expUnit_smul_mul {X : imaginaryQuaternions} (hX : ‖X‖ = 1) (θ θ' : ℝ) :
    expUnit (θ • X) * expUnit (θ' • X) = expUnit ((θ + θ') • X) := by
  apply Subtype.ext
  show ((expUnit (θ • X) : UnitQuaternion) : ℍ[ℝ]) * ((expUnit (θ' • X) : UnitQuaternion) : ℍ[ℝ]) = _
  have h1 : ((X : ℍ[ℝ])) * (X : ℍ[ℝ]) = -1 := by
    have hr : (X : ℍ[ℝ]).re = 0 := X.2
    have := componentAlong_self hX
    have e : star (X : ℍ[ℝ]) = - (X : ℍ[ℝ]) := by
      ext <;> simp [hr]
    have e2 : (X : ℍ[ℝ]) * star (X : ℍ[ℝ]) = 1 := by
      rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self]
      have : ‖(X : ℍ[ℝ])‖ = 1 := hX
      rw [this]
      norm_num
    rw [e] at e2
    have : -((X : ℍ[ℝ]) * (X : ℍ[ℝ])) = 1 := by rw [← mul_neg]; exact e2
    rw [← this, neg_neg]
  rw [coe_expUnit_smul hX, coe_expUnit_smul hX, coe_expUnit_smul hX, Real.cos_add, Real.sin_add]
  set x : ℍ[ℝ] := (X : ℍ[ℝ])
  have hc : ∀ r : ℝ, (r : ℍ[ℝ]) * x = r • x := fun r => by
    ext <;> simp
  have hc' : ∀ r : ℝ, x * (r : ℍ[ℝ]) = r • x := fun r => by
    ext <;> simp [mul_comm]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hc, hc', h1, smul_smul]
  ext <;> simp <;> ring
theorem expUnit_zero_eq_one : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem inv_expUnit_smul {X : imaginaryQuaternions} (hX : ‖X‖ = 1) (θ : ℝ) :
    (expUnit (θ • X))⁻¹ = expUnit ((-θ) • X) := by
  apply inv_eq_of_mul_eq_one_right
  rw [expUnit_smul_mul hX, add_neg_cancel, zero_smul, expUnit_zero_eq_one]
theorem pathHolonomy_abelianField {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {j : ℕ} (θ : LevelForm F j)
    (x : F.Site j) (l : List PathStep) :
    pathHolonomy (abelianField X θ) x l = expUnit (pathSum θ x l • X) := by
  induction l generalizing x with
  | nil =>
    simp [pathHolonomy, pathSum, expUnit_zero_eq_one]
  | cons st r ih =>
    have hs : linkValue (abelianField X θ) x st =
        expUnit ((if st.2 then θ x st.1 else - θ (x - unitStep j st.1) st.1) • X) := by
      unfold linkValue abelianField
      by_cases h : st.2 = true
      · simp only [h, if_true]
      · simp only [h, Bool.false_eq_true, if_false]
        rw [inv_expUnit_smul hX]
    show linkValue (abelianField X θ) x st *
      pathHolonomy (abelianField X θ) (x + stepDisplacement j st) r = _
    rw [ih, hs, expUnit_smul_mul hX]
    rfl
theorem plaquette_abelianField_le {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {j : ℕ} (θ : LevelForm F j)
    (x : F.Site j) (μ ν : Fin 4) :
    1 - ((plaquetteHolonomy (abelianField X θ) (x, μ, ν) : UnitQuaternion) : ℍ[ℝ]).re ≤
      plaquetteCurl θ x μ ν ^ 2 / 2 := by
  have h : plaquetteHolonomy (abelianField X θ) (x, μ, ν) = expUnit (plaquetteCurl θ x μ ν • X) := by
    show pathHolonomy _ x [(μ, true), (ν, true), (μ, false), (ν, false)] = _
    rw [pathHolonomy_abelianField hX, pathSum_plaquetteLoop]
  have hr : (X : ℍ[ℝ]).re = 0 := X.2
  rw [h, coe_expUnit_smul hX]
  have := Real.one_sub_sq_div_two_le_cos (x := plaquetteCurl θ x μ ν)
  simp [hr]
  linarith
def cosineAverage {j : ℕ} (θ : LevelForm F j) (y : ℝ) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    Real.cos (pathSum θ (refineSite c.1) (bondContour F.blockSide h π c.2) - y)
def sineAverage {j : ℕ} (θ : LevelForm F j) (y : ℝ) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    Real.sin (pathSum θ (refineSite c.1) (bondContour F.blockSide h π c.2) - y)
theorem quaternion_coe_sum {ι : Type} (s : Finset ι) (f : ι → ℝ) :
    ((∑ k ∈ s, f k : ℝ) : ℍ[ℝ]) = ∑ k ∈ s, (f k : ℍ[ℝ]) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Quaternion.coe_add, ih]
theorem smul_quaternion_coe (r s : ℝ) : r • (s : ℍ[ℝ]) = ((r * s : ℝ) : ℍ[ℝ]) := by
  ext <;> simp
theorem blockFit_abelianField_le {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {j : ℕ} (θ : LevelForm F j)
    (θ' : LevelForm F (j + 1))
    (c : F.Site (j + 1) × Fin 4) (hA : 0 < cosineAverage θ (θ' c.1 c.2) c) :
    blockFit (abelianField X θ) (abelianField X θ') c ≤
      sineAverage θ (θ' c.1 c.2) c ^ 2 / (2 * cosineAverage θ (θ' c.1 c.2) c) := by
  set A := cosineAverage θ (θ' c.1 c.2) c with hAdef
  set B := sineAverage θ (θ' c.1 c.2) c with hBdef
  set M := BlockAverages.contourAverage (abelianField X θ) c with hM
  set g : UnitQuaternion := (abelianField X θ' c.1 c.2)⁻¹ with hg
  have hr : (X : ℍ[ℝ]).re = 0 := X.2
  have hq : M * (g : ℍ[ℝ]) = (A : ℍ[ℝ]) + B • (X : ℍ[ℝ]) := by
    have hg' : g = expUnit ((- θ' c.1 c.2) • X) := inv_expUnit_smul hX _
    rw [hM]
    unfold BlockAverages.contourAverage
    rw [smul_mul_assoc, Finset.sum_mul]
    have e1 : ∀ h ∈ centredCube F.blockSide, (∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy (abelianField X θ) (refineSite c.1) (bondContour F.blockSide h π c.2) :
          UnitQuaternion) : ℍ[ℝ])) * (g : ℍ[ℝ]) =
        ∑ π : Equiv.Perm (Fin 4),
          (((Real.cos (pathSum θ (refineSite c.1) (bondContour F.blockSide h π c.2) - θ' c.1 c.2) : ℝ) :
              ℍ[ℝ]) +
            Real.sin (pathSum θ (refineSite c.1) (bondContour F.blockSide h π c.2) - θ' c.1 c.2) •
              (X : ℍ[ℝ])) := by
      intro h _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun π _ => ?_
      rw [pathHolonomy_abelianField hX, hg']
      show (((expUnit _ * expUnit _ : UnitQuaternion)) : ℍ[ℝ]) = _
      rw [expUnit_smul_mul hX, coe_expUnit_smul hX]
      rfl
    rw [Finset.sum_congr rfl e1]
    simp only [Finset.sum_add_distrib, ← Finset.sum_smul, smul_add]
    rw [hAdef, hBdef]
    unfold cosineAverage sineAverage
    congr 1
    · simp_rw [← quaternion_coe_sum]
      exact smul_quaternion_coe _ _
    · rw [smul_smul]
  have hnorm : ‖M‖ = ‖M * (g : ℍ[ℝ])‖ := by
    rw [norm_mul, norm_coe_unitQuaternion, mul_one]
  have hsq : ‖M * (g : ℍ[ℝ])‖ ^ 2 = A ^ 2 + B ^ 2 := by
    have h1 : Quaternion.normSq (X : ℍ[ℝ]) = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self]
      have : ‖(X : ℍ[ℝ])‖ = 1 := hX
      rw [this]
      norm_num
    rw [Quaternion.normSq_def', hr] at h1
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, hq, Quaternion.normSq_def']
    simp [hr]
    nlinarith
  have hre : (M * (g : ℍ[ℝ])).re = A := by
    rw [hq]
    simp [hr]
  unfold blockFit
  show ‖M‖ - (M * (g : ℍ[ℝ])).re ≤ _
  rw [hre, hnorm]
  have ht : 0 ≤ A + B ^ 2 / (2 * A) := by positivity
  have hle : ‖M * (g : ℍ[ℝ])‖ ≤ A + B ^ 2 / (2 * A) := by
    apply (sq_le_sq₀ (norm_nonneg _) ht).1
    rw [hsq]
    have e : (A + B ^ 2 / (2 * A)) ^ 2 = A ^ 2 + B ^ 2 + (B ^ 2 / (2 * A)) ^ 2 := by
      field_simp
      ring
    rw [e]
    nlinarith [sq_nonneg (B ^ 2 / (2 * A))]
  linarith
theorem pathSum_const_mul {j : ℕ} (r : ℝ) (B : LevelForm F j) (x : F.Site j) (l : List PathStep) :
    pathSum (fun x i => r * B x i) x l = r * pathSum B x l := by
  induction l generalizing x with
  | nil => simp [pathSum]
  | cons st r' ih =>
    simp only [pathSum, ih]
    by_cases h : st.2 = true
    · simp only [h, if_true]; ring
    · simp only [h, Bool.false_eq_true, if_false]; ring
theorem plaquetteCurl_const_mul {j : ℕ} (r : ℝ) (B : LevelForm F j) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteCurl (fun x i => r * B x i) x μ ν = r * plaquetteCurl B x μ ν := by
  unfold plaquetteCurl
  ring
theorem mem_sitesOfCells_finiteCells (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {k : ℕ}
    (hk : k ≤ F.top) (x : F.Site k) : x ∈ sitesOfCells (finiteCells F) k := by
  have hLpos : 0 < F.blockSide := hodd.pos
  obtain ⟨m, hm⟩ := hodd.pow (n := F.top - k)
  set M : ℕ := F.blockSide ^ (F.top - k) with hMdef
  have hMpos : 0 < M := by positivity
  have hper1 : ∀ i, F.period F.top i = F.extent i := by
    intro i
    simp [BlockFrame.period]
  have hper0 : ∀ i, F.period k i = F.extent i * M := fun i => rfl
  have hne1 : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by rw [hper1]; exact (hs i).ne'⟩
  have hfin : Finite F.Cell := by
    have : ∀ i, Finite (ZMod (F.period F.top i)) := fun i => by
      have := hne1 i
      exact inferInstance
    exact Pi.finite
  have hmem : ∀ z : F.Cell, z ∈ finiteCells F := by
    intro z
    unfold finiteCells
    rw [dif_pos hfin]
    exact @Finset.mem_univ _ (Fintype.ofFinite _) z
  set c : Fin 4 → ℤ := siteCoords x with hc
  set q : Fin 4 → ℤ := fun i => (c i + m) / (M : ℤ) with hq
  set h : Fin 4 → ℤ := fun i => c i - (M : ℤ) * q i with hh
  have hLz : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hMpos
  have hLk : (M : ℤ) = 2 * m + 1 := by exact_mod_cast hm
  unfold sitesOfCells
  rw [Finset.mem_biUnion]
  refine ⟨siteOfCoords F.top q, hmem _, ?_⟩
  rw [Finset.mem_image]
  refine ⟨h, ?_, ?_⟩
  · unfold centredCube
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have e1 := Int.emod_add_mul_ediv (c i + m) (M : ℤ)
    have e2 := Int.emod_nonneg (c i + m) hLz.ne'
    have e3 := Int.emod_lt_of_pos (c i + m) hLz
    have e4 : ((M : ℤ) - 1) / 2 = m := by
      rw [hLk]
      omega
    rw [e4]
    simp only [hh, hq]
    constructor <;> nlinarith
  · have hcent : (cellCentre k (siteOfCoords F.top q : F.Cell) : F.Site k) =
        siteOfCoords k fun i => (M : ℤ) * q i := by
      unfold cellCentre
      apply siteOfCoords_eq_of_dvd
      intro i
      have := period_dvd_sub_siteCoords (F := F) (j := F.top) q i
      rw [hper1 i] at this
      obtain ⟨d, hd⟩ := this
      refine ⟨d, ?_⟩
      rw [hper0 i]
      push_cast
      have : ((F.blockSide : ℤ) ^ (F.top - k)) = (M : ℤ) := by rw [hMdef]; push_cast; rfl
      rw [this, ← mul_sub, hd]
      ring
    rw [hcent, ← siteOfCoords_map_add]
    have : (fun i => (M : ℤ) * q i) + h = c := by
      funext i
      simp only [hh, Pi.add_apply]
      ring
    rw [this, hc, siteOfCoords_siteCoords_self]
theorem sum_innerBonds_finiteCells (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {k : ℕ}
    (hk : k ≤ F.top) (f : F.Site k × Fin 4 → ℝ) :
    ∑ b ∈ innerBonds (finiteCells F) k, f b =
      ∑ y ∈ sitesOfCells (finiteCells F) k, ∑ i : Fin 4, f (y, i) := by
  have : innerBonds (finiteCells F) k = sitesOfCells (finiteCells F) k ×ˢ Finset.univ := by
    unfold innerBonds
    exact Finset.filter_true_of_mem fun b _ => mem_sitesOfCells_finiteCells hodd hs hk _
  rw [this, Finset.sum_product]
theorem sum_innerPlaquettes_finiteCells (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {k : ℕ}
    (hk : k ≤ F.top) (f : F.Site k × Fin 4 × Fin 4 → ℝ) :
    ∑ p ∈ innerPlaquettes (finiteCells F) k, f p =
      ∑ x ∈ sitesOfCells (finiteCells F) k, ∑ e ∈ orientedPlanes, f (x, e.1, e.2) := by
  have : innerPlaquettes (finiteCells F) k = sitesOfCells (finiteCells F) k ×ˢ orientedPlanes := by
    ext p
    unfold innerPlaquettes orientedPlanes
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true]
    constructor
    · exact fun h => ⟨h.1, h.2.1⟩
    · exact fun h => ⟨h.1, h.2, fun x _ => mem_sitesOfCells_finiteCells hodd hs hk x⟩
  rw [this, Finset.sum_product]
theorem norm_pathHolonomy_sub_one_le {j : ℕ} (W : F.GaugeField j) {ε : ℝ}
    (hW : ∀ x i, ‖(W x i : ℍ[ℝ]) - 1‖ ≤ ε)
    (x : F.Site j) (l : List PathStep) : ‖(pathHolonomy W x l : ℍ[ℝ]) - 1‖ ≤ l.length * ε := by
  induction l generalizing x with
  | nil => simp [pathHolonomy]
  | cons st r ih =>
    have h1 := ih (x + stepDisplacement j st)
    have hp := norm_linkValue_sub_one_le W hW x st
    have h2 := norm_coe_mul_sub_one_le (linkValue W x st) (pathHolonomy W (x + stepDisplacement j st) r)
    have hh : pathHolonomy W x (st :: r) =
        linkValue W x st * pathHolonomy W (x + stepDisplacement j st) r := rfl
    have hn : (((st :: r).length : ℕ) : ℝ) = (r.length : ℝ) + 1 := by simp
    rw [hh, hn]
    linarith
theorem isSmallCurvature_of_near_one {j : ℕ} (Y : F.GaugeField j) {m s : ℝ} (hs : 4 * m < s)
    (hY : ∀ x i, ‖(Y x i : ℍ[ℝ]) - 1‖ ≤ m) : IsSmallCurvature s Y := by
  intro p _
  have h := norm_pathHolonomy_sub_one_le Y hY p.1
    [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)]
  have e : (([(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : List PathStep).length : ℝ) = 4 := by
    norm_num
  rw [e] at h
  exact lt_of_le_of_lt h hs
theorem norm_chartedField_sub_one_le {G : BlockFrame} (w : G.Site G.depth → Fin 4 → imaginaryQuaternions)
    (V : G.GaugeField G.top) {r m : ℝ} (hr : 0 ≤ r) (hm : 0 ≤ m)
    (hw : ∀ x i, ‖w x i‖ ≤ r) (hV : ∀ x i, ‖(V x i : ℍ[ℝ]) - 1‖ ≤ m) (x : G.Site G.depth) (i : Fin 4) :
    ‖(chartedField w V x i : ℍ[ℝ]) - 1‖ ≤ r + m := by
  have he : ‖((expUnit (w x i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ r :=
    (norm_exp_sub_one_le (w x i).2).trans (hw x i)
  unfold chartedField
  split_ifs with h1 h2
  · have := norm_coe_mul_sub_one_le (expUnit (w x i)) (V (enclosingCell x) i)
    linarith [hV (enclosingCell x) i]
  · simp
    linarith
  · linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
