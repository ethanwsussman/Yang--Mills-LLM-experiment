import YangMills.Construction.ClusterExpansionOfAStep.ContoursOnTheTorus
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfAContour
import YangMills.Construction.ClusterExpansionOfAStep.PlainFitsOfNearFields
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.NearFields
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.TorusLumps YangMills.Construction.TorusFrame YangMills.Construction.TorusContours YangMills.Construction.ContourOffsets
variable {F : BlockFrame} [∀ j i, NeZero (F.period j i)]
theorem norm_pathHolonomy_sub_le {j : ℕ} {X X' : F.GaugeField j} {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ x i, ‖(X x i : ℍ[ℝ]) - X' x i‖ ≤ ε) :
    ∀ (l : List PathStep) (x : F.Site j),
      ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) - pathHolonomy X' x l‖ ≤ l.length * ε := by
  intro l
  induction l with
  | nil =>
    intro x
    simp [pathHolonomy]
  | cons st r ih =>
    intro x
    simp only [pathHolonomy, List.length_cons]
    refine (norm_mul_sub_mul_le _ _ _ _).trans ?_
    have h1 : ‖((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) - linkValue X' x st‖ ≤ ε := by
      unfold linkValue
      split_ifs
      · exact hc _ _
      · rw [norm_inv_sub_inv]
        exact hc _ _
    have h2 := ih (x + stepDisplacement j st)
    push_cast
    linarith
theorem length_axisPath_le (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (M : ℕ) (hh : ∀ k, (h k).natAbs ≤ M) :
    (axisPath h π).length ≤ 4 * M := by apply _root_.YangMills.Construction.TorusContours.length_axisPath_le <;> assumption
theorem bondContour_eq_contourSteps (L : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    bondContour L h π i = ContourOffsets.contourSteps L 0 0 h π i := by
  simp [bondContour, ContourOffsets.contourSteps]
theorem length_bondContour_le {L : ℕ} {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube L) (π : Equiv.Perm (Fin 4))
    (i : Fin 4) : (bondContour L ξ π i).length ≤ 9 * L := by
  have hb : ∀ k, (ξ k).natAbs ≤ L := by
    intro k
    have b := _root_.YangMills.Construction.TorusContours.mem_centredCube_iff.mp hξ k
    omega
  have e1 := length_axisPath_le ξ π L hb
  unfold bondContour reversePath
  simp only [List.length_append, List.length_replicate, List.length_map, List.length_reverse]
  omega
theorem card_centredCube {L : ℕ} (hodd : Odd L) : (centredCube L).card = L ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem refineSite_eq_siteAtOffset (y : F.Cell) : _root_.YangMills.Construction.BlockAverages.refineSite (j := F.depth) y = siteAtOffset y 0 := by
  rw [siteAtOffset, _root_.YangMills.Construction.TorusContours.siteOfCoords_zero, add_zero, cellCentre_eq]
  rfl
theorem siteAtOffset_mem_sitesBelow_of_inSlab {y : F.Cell} {i : Fin 4} {u : Fin 4 → ℤ}
    (hu : InSlab F.blockSide i u) (hL : Odd F.blockSide) :
    (siteAtOffset y u : F.Site F.depth) ∈ sitesBelow F.depth y ∨
      (siteAtOffset y u : F.Site F.depth) ∈ sitesBelow F.depth (y + unitStep F.top i) := by
  obtain ⟨s, hs⟩ := hL
  have ht : ((F.blockSide : ℤ) - 1) / 2 = s := by omega
  have hs₁ : ∀ k, k ≠ i → -(s : ℤ) ≤ u k ∧ u k ≤ s := by
    intro k hk
    have := hu k
    simp only [slabLower, slabUpper, Pi.single_eq_of_ne hk, ht] at this
    omega
  by_cases hc : u i ≤ s
  · left
    refine (_root_.YangMills.Construction.TorusContours.mem_sitesBelow_iff y _).mpr ⟨u, _root_.YangMills.Construction.TorusContours.mem_centredCube_iff.mpr fun k => ?_, rfl⟩
    rw [ht]
    by_cases hk : k = i
    · subst hk
      have := hu k
      simp only [slabLower, ht] at this
      omega
    · exact hs₁ k hk
  · right
    refine (_root_.YangMills.Construction.TorusContours.mem_sitesBelow_iff _ _).mpr
      ⟨u - Pi.single i (F.blockSide : ℤ), _root_.YangMills.Construction.TorusContours.mem_centredCube_iff.mpr fun k => ?_, ?_⟩
    · rw [ht]
      by_cases hk : k = i
      · subst hk
        have := hu k
        simp only [slabUpper, slabLower, ht, Pi.single_eq_same] at this
        simp only [Pi.sub_apply, Pi.single_eq_same]
        omega
      · simp only [Pi.sub_apply, Pi.single_eq_of_ne hk, sub_zero]
        exact hs₁ k hk
    · rw [siteAtOffset_shift, sub_add_cancel]
theorem siteAtOffset_add_unitStep {y : F.Cell} (i k : Fin 4) (u : Fin 4 → ℤ) :
    (siteAtOffset y u : F.Site F.depth) + unitStep F.depth k = siteAtOffset y (u + Pi.single k 1) := by
  simp only [siteAtOffset, unitStep, _root_.YangMills.Construction.TorusContours.siteOfCoords_add, add_assoc]
theorem abs_fit_sub_fit_le {m m' : ℍ[ℝ]} (g : UnitQuaternion) :
    |(‖m‖ - (m * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) - (‖m'‖ - (m' * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re)| ≤
      2 * ‖m - m'‖ := by
  have h1 : |‖m‖ - ‖m'‖| ≤ ‖m - m'‖ := abs_norm_sub_norm_le _ _
  have h2 : |(m * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re - (m' * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re| ≤
      ‖m - m'‖ := by
    have e : (m * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re - (m' * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
        ((m - m') * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by
      rw [sub_mul]
      simp
    rw [e]
    refine (abs_re_le_norm _).trans ?_
    rw [norm_mul, _root_.YangMills.Construction.TorusContours.norm_coe_unitQuaternion, mul_one]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
end YangMills.Construction.NearFields
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.TorusFrame YangMills.Construction.TorusContours YangMills.Construction.ContourOffsets YangMills.Construction.NearFields
theorem plainFitsOfNearFields : PlainFitsOfNearFields := by
  classical
  intro L n _ _ hodd h16 W W' V y i ε hε hclose
  have hL1 : 1 ≤ L := hodd.pos
  set P : (stepBlockFrame L n).Site 0 → Fin 4 → Prop := fun x k =>
    (x ∈ sitesBelow 0 y ∨ x ∈ sitesBelow 0 (y + unitStep 1 i)) ∧
      (x + unitStep 0 k ∈ sitesBelow 0 y ∨ x + unitStep 0 k ∈ sitesBelow 0 (y + unitStep 1 i)) with hP
  set W₃ : (stepBlockFrame L n).GaugeField 0 := fun x k => if P x k then W x k else W' x k with hW₃
  have hclose₃ : ∀ x k, ‖(W₃ x k : ℍ[ℝ]) - W' x k‖ ≤ ε := by
    intro x k
    by_cases hp : P x k
    · simp only [hW₃]
      rw [if_pos hp]
      exact hclose x k hp.1 hp.2
    · simp only [hW₃]
      rw [if_neg hp]
      simpa using hε
  have hz : (0 : Fin 4 → ℤ) ∈ centredCube L := zero_mem_centredCube hL1
  have hcongr : ∀ ξ ∈ centredCube L, ∀ π : Equiv.Perm (Fin 4),
      pathHolonomy W (_root_.YangMills.Construction.BlockAverages.refineSite (j := 0) y) (bondContour L ξ π i) =
        pathHolonomy W₃ (_root_.YangMills.Construction.BlockAverages.refineSite (j := 0) y) (bondContour L ξ π i) := by
    intro ξ hξ π
    have hh := pathHolonomy_eq_of_agree (F := stepBlockFrame L n) (F' := stepBlockFrame L n) (InSlab L i)
      W W₃ y y ?_ (ContourOffsets.contourSteps L 0 0 ξ π i) 0 (contourSteps_inSlab hz hz hξ π i)
    · rw [← refineSite_eq_siteAtOffset (F := stepBlockFrame L n) y, ← bondContour_eq_contourSteps] at hh
      exact hh
    · intro u k hu hu'
      have h3 := siteAtOffset_mem_sitesBelow_of_inSlab (F := stepBlockFrame L n) (y := y) hu' hodd
      rw [← siteAtOffset_add_unitStep (F := stepBlockFrame L n) (y := y) i k u] at h3
      simp only [hW₃]
      rw [if_pos ⟨siteAtOffset_mem_sitesBelow_of_inSlab (F := stepBlockFrame L n) hu hodd, h3⟩]
  have hcard : ((centredCube L).card : ℝ) = (L : ℝ) ^ 4 := by
    have := _root_.YangMills.Construction.NearFields.card_centredCube hodd
    exact_mod_cast this
  have hmean : ‖_root_.YangMills.Construction.BlockAverages.contourAverage W (y, i) - _root_.YangMills.Construction.BlockAverages.contourAverage W' (y, i)‖ ≤ 9 * L * ε := by
    unfold _root_.YangMills.Construction.BlockAverages.contourAverage
    rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖∑ ξ ∈ centredCube (stepBlockFrame L n).blockSide, ((∑ π : Equiv.Perm (Fin 4),
          ((pathHolonomy W (_root_.YangMills.Construction.BlockAverages.refineSite (j := 0) y) (bondContour (stepBlockFrame L n).blockSide ξ π i) :
            UnitQuaternion) : ℍ[ℝ])) -
        ∑ π : Equiv.Perm (Fin 4), ((pathHolonomy W' (_root_.YangMills.Construction.BlockAverages.refineSite (j := 0) y)
          (bondContour (stepBlockFrame L n).blockSide ξ π i) : UnitQuaternion) : ℍ[ℝ]))‖ ≤
        ((centredCube L).card : ℝ) * (24 * (9 * L * ε)) := by
      refine (norm_sum_le _ _).trans ?_
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun ξ hξ => ?_
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      have h2 : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin 4))),
          ‖((pathHolonomy W (_root_.YangMills.Construction.BlockAverages.refineSite (j := 0) y) (bondContour (stepBlockFrame L n).blockSide ξ π i) :
              UnitQuaternion) : ℍ[ℝ]) -
            pathHolonomy W' (_root_.YangMills.Construction.BlockAverages.refineSite (j := 0) y) (bondContour (stepBlockFrame L n).blockSide ξ π i)‖ ≤
            9 * L * ε := by
        intro π _
        have e := hcongr ξ hξ π
        have e' : pathHolonomy W (_root_.YangMills.Construction.BlockAverages.refineSite (j := 0) y) (bondContour (stepBlockFrame L n).blockSide ξ π i) =
            pathHolonomy W₃ (_root_.YangMills.Construction.BlockAverages.refineSite (j := 0) y) (bondContour (stepBlockFrame L n).blockSide ξ π i) := e
        rw [e']
        refine (norm_pathHolonomy_sub_le (F := stepBlockFrame L n) hε hclose₃ _ _).trans ?_
        have hl := length_bondContour_le hξ π i
        have : ((bondContour (stepBlockFrame L n).blockSide ξ π i).length : ℝ) ≤ 9 * L := by exact_mod_cast hl
        exact mul_le_mul_of_nonneg_right this hε
      refine (Finset.sum_le_card_nsmul _ _ _ h2).trans (le_of_eq ?_)
      simp [Fintype.card_perm, Nat.factorial]
    have hFL : ((stepBlockFrame L n).blockSide : ℝ) = L := rfl
    rw [hFL]
    rw [hcard] at h1
    calc 1 / (24 * (L : ℝ) ^ 4) * _ ≤ 1 / (24 * (L : ℝ) ^ 4) * ((L : ℝ) ^ 4 * (24 * (9 * L * ε))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 9 * L * ε := by
          field_simp
  unfold blockFit
  have h5 := abs_fit_sub_fit_le (m := _root_.YangMills.Construction.BlockAverages.contourAverage W (y, i)) (m' := _root_.YangMills.Construction.BlockAverages.contourAverage W' (y, i)) (V y i)
  refine h5.trans ?_
  linarith
end YangMills.Construction.TorusLumps
end
