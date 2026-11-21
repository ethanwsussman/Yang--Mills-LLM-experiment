import YangMills.Construction.ColdChainAtEveryLevel.FirstOrderOnAPlaquette
import YangMills.Construction.ColdChainAtEveryLevel.PoincareOnACell
import YangMills.Construction.ColdChainAtEveryLevel.PotentialsInAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.CellPoincare
open BlockAverages GaugeMap LatticeFractionalIntegration PatchPoints PatchFrames LatticePaths
variable {F : BlockFrame} {S : Finset F.Cell} {y : F.Cell}
section Chart
theorem mem_cellOffsets_iff {x : Lattice4} : x ∈ cellOffsets F ↔ ∀ i, 0 ≤ x i ∧ x i < cellSideLength F := by
  simp [cellOffsets, Fintype.mem_piFinset]
theorem exists_centredCube_of_mem_cellOffsets (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) {x : Lattice4} (hx : x ∈ cellOffsets F) :
    ∃ h ∈ centredCube (F.blockSide ^ F.top), patchSite S y x = cellCentre 0 y + siteOfCoords 0 h := by
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  refine ⟨fun i => closedOrthant S y i * (x i - (cellSideLength F - 1) / 2), ?_, rfl⟩
  rw [PatchPoints.mem_centredCube_iff]
  intro i
  have := mem_cellOffsets_iff.1 hx i
  rcases he i with hs | hs <;> simp only [hs] <;> constructor <;> omega
theorem exists_cellOffsets_of_mem_centredCube (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) {h : Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) :
    ∃ x ∈ cellOffsets F, patchSite S y x = cellCentre 0 y + siteOfCoords 0 h := by
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  have hb := (mem_centredCube_iff h).1 hh
  refine ⟨fun i => closedOrthant S y i * h i + (cellSideLength F - 1) / 2, mem_cellOffsets_iff.2 fun i => ?_, ?_⟩
  · have := hb i
    rcases he i with hs | hs <;> simp only [hs] <;> constructor <;> omega
  · unfold patchSite
    congr 2
    funext i
    have := closedOrthant_mul_self he i
    simp only
    linear_combination (h i) * this
theorem cellSites_eq_image (hy : y ∈ S) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) :
    cellSites S y = (cellOffsets F).image (patchSite S y) := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨hs, hc⟩ := Finset.mem_filter.1 ht
    obtain ⟨y', hy', h, hh, rfl⟩ := mem_sitesOfCells.1 hs
    have e : y' = y := by
      rw [← hc]
      exact (enclosingCell_cellCentre_add hodd y' h hh).symm
    subst e
    obtain ⟨x, hx, ex⟩ := exists_cellOffsets_of_mem_centredCube hodd he (h := h) (by simpa using hh)
    exact Finset.mem_image.2 ⟨x, hx, ex⟩
  · intro ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨h, hh, e⟩ := exists_centredCube_of_mem_cellOffsets hodd he hx
    rw [e]
    refine Finset.mem_filter.2 ⟨mem_sitesOfCells.2 ⟨y, hy, h, by simpa using hh, rfl⟩, ?_⟩
    exact enclosingCell_cellCentre_add hodd y h (by simpa using hh)
theorem cellOffsets_coord_bounds (hodd : Odd F.blockSide) {x : Lattice4} (hx : x ∈ cellOffsets F) (i : Fin 4) :
    -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F := by
  have hN := cellSideLength_pos (F := F) hodd.pos
  have := mem_cellOffsets_iff.1 hx i
  constructor <;> omega
theorem patchChart_patchSite_of_mem (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) {x : Lattice4}
    (hx : x ∈ cellOffsets F) : patchChart S y (patchSite S y x) = x :=
  patchChart_patchSite hamb hodd he (cellOffsets_coord_bounds hodd hx)
theorem injOn_patchSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) :
    Set.InjOn (patchSite S y) (cellOffsets F : Set Lattice4) := by
  intro a ha b hb h
  rw [← patchChart_patchSite_of_mem hamb hodd he ha, h, patchChart_patchSite_of_mem hamb hodd he hb]
theorem sum_cellSites_eq {M : Type} [AddCommMonoid M] (hy : y ∈ S) (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) (g : F.Site 0 → M) :
    ∑ t ∈ cellSites S y, g t = ∑ x ∈ cellOffsets F, g (patchSite S y x) := by
  classical
  rw [cellSites_eq_image hy hodd he, Finset.sum_image (injOn_patchSite hamb hodd he)]
theorem cellSupDist_self_eq_zero (y : F.Cell) : cellSupDist y y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem mem_patchDomain_of_mem_cellOffsets (hy : y ∈ S) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) {x : Lattice4} (hx : x ∈ cellOffsets F) :
    x ∈ patchDomain S y := by
  obtain ⟨h, hh, e⟩ := exists_centredCube_of_mem_cellOffsets hodd he hx
  have h1 := patchChart_mem_patchDomain hamb hodd he hy (by rw [cellSupDist_self_eq_zero]; omega) hh
  rwa [← e, patchChart_patchSite_of_mem hamb hodd he hx] at h1
theorem patchCubicKernel_patchSite (hy : y ∈ S) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) {f : F.Site 0 → ℝ}
    (hf : ∀ t, t ∉ cellSites S y → f t = 0) {x : Lattice4} (hx : x ∈ cellOffsets F) :
    patchCubicKernel S y f (patchSite S y x) =
      ∑ a ∈ cellOffsets F, cubicKernel (x - a) * f (patchSite S y a) := by
  classical
  have hsub : cellSites S y ⊆ patchSiteSet S y := by
    intro t ht
    rw [cellSites_eq_image hy hodd he] at ht
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
    exact Finset.mem_image.2 ⟨a, mem_patchDomain_of_mem_cellOffsets hy hamb hodd he ha, rfl⟩
  have hxs : patchSite S y x ∈ patchSiteSet S y :=
    Finset.mem_image.2 ⟨x, mem_patchDomain_of_mem_cellOffsets hy hamb hodd he hx, rfl⟩
  simp only [patchCubicKernel, if_pos hxs]
  rw [← Finset.sum_subset hsub (fun t _ ht => by rw [hf t ht, mul_zero]), sum_cellSites_eq hy hamb hodd he]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [patchChart_patchSite_of_mem hamb hodd he hx, patchChart_patchSite_of_mem hamb hodd he ha]
theorem card_cellOffsets (hL : 0 < F.blockSide) :
    ((cellOffsets F).card : ℝ) = (cellSideLength F : ℝ) ^ 4 := by apply _root_.YangMills.Construction.PatchDifferences.card_cellOffsets_eq <;> assumption
end Chart
section Frame
variable {V : F.GaugeField F.top}
theorem referenceFieldChain_zero (x : F.Site 0) (i : Fin 4) :
    referenceFieldChain S V 0 x i = leadingTransport S V x (x + unitStep 0 i) := by apply _root_.YangMills.Construction.PatchDifferences.referenceFieldChain_zero_apply <;> assumption
theorem adjointAction_sub (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p - q) = adjointAction g p - adjointAction g q := by apply _root_.YangMills.Construction.BlockLines.adjointAction_sub <;> assumption
theorem norm_adjointAction_sub_self_le (T : UnitQuaternion) (a : ℍ[ℝ]) :
    ‖adjointAction T a - a‖ ≤ 2 * ‖(T : ℍ[ℝ]) - 1‖ * ‖a‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction_sub_le <;> assumption
theorem norm_localSection_step_le {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r : ℝ}
    (hF : IsPatchFrame S V y R Cs r) (hr : 1 ≤ r * cellSideLength F)
    (ξ : F.Site 0 → ℍ[ℝ]) {a b : Lattice4} (ha : a ∈ patchDomain S y) (hb : b ∈ patchDomain S y)
    (hlen : supNorm (b - a) = 1) {i : Fin 4} (hs : patchSite S y b = patchSite S y a + unitStep 0 i) :
    ‖PatchDifferences.localSection S V y ξ b - PatchDifferences.localSection S V y ξ a‖ ≤
      ‖covariantDiff (referenceFieldChain S V 0) ξ (patchSite S y a) i‖ +
        2 * (Cs / (cellSideLength F : ℝ)) * ‖PatchDifferences.localSection S V y ξ b‖ := by
  have hd : ((supNorm (b - a) : ℕ) : ℝ) ≤ r * cellSideLength F := by rw [hlen]; simpa using hr
  have hlink := hF.leadingTransport_eq a ha b hb hd
  have hnear := hF.norm_sub_one_le a ha b hb hd
  rw [hlen] at hnear
  have hnear' : ‖((R a b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Cs / (cellSideLength F : ℝ) := by
    refine hnear.trans (le_of_eq ?_)
    push_cast
    ring
  set f := frameChange S V y (patchSite S y a) with hf
  set f' := frameChange S V y (patchSite S y b) with hf'
  have hT : referenceFieldChain S V 0 (patchSite S y a) i = f * R a b * f'⁻¹ := by
    rw [referenceFieldChain_zero, ← hs, hlink]
  have hD : adjointAction f⁻¹ (covariantDiff (referenceFieldChain S V 0) ξ (patchSite S y a) i) =
      adjointAction (R a b) (PatchDifferences.localSection S V y ξ b) - PatchDifferences.localSection S V y ξ a := by
    simp only [covariantDiff, adjointAction_sub, PatchDifferences.localSection]
    rw [← hs, hT, ← hf, ← hf', ← PlaquetteLinearization.adjointAction_mul,
      ← PlaquetteLinearization.adjointAction_mul]
    congr 2
    group
  have e : PatchDifferences.localSection S V y ξ b - PatchDifferences.localSection S V y ξ a =
      adjointAction f⁻¹ (covariantDiff (referenceFieldChain S V 0) ξ (patchSite S y a) i) -
        (adjointAction (R a b) (PatchDifferences.localSection S V y ξ b) -
          PatchDifferences.localSection S V y ξ b) := by
    rw [hD]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [PlaquetteLinearization.norm_adjointAction]
  have h2 := norm_adjointAction_sub_self_le (R a b) (PatchDifferences.localSection S V y ξ b)
  have h3 := mul_le_mul_of_nonneg_right hnear' (norm_nonneg (PatchDifferences.localSection S V y ξ b))
  nlinarith
end Frame
section Sums
theorem zero_le_cubicKernel (v : Lattice4) : 0 ≤ cubicKernel v := by apply _root_.YangMills.Construction.PatchDifferences.cubicKernel_nonneg_apply <;> assumption
theorem cubicKernel_le_eight_mul_sub (v e : Lattice4) (he : supNorm e = 1) :
    cubicKernel v ≤ 8 * cubicKernel (v - e) := by
  have h1 : supNorm (v - e) ≤ supNorm v + 1 := by
    have := supNorm_add_le v (-e)
    rw [supNorm_neg, he, ← sub_eq_add_neg] at this
    exact this
  unfold cubicKernel
  set M : ℕ := max 1 (supNorm v) with hM
  set M' : ℕ := max 1 (supNorm (v - e)) with hM'
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM'1 : 1 ≤ M' := le_max_left _ _
  have hsv : supNorm v ≤ M := le_max_right _ _
  have hle : M' ≤ 2 * M := max_le (by omega) (by omega)
  have a1 : (0 : ℝ) < M' := by exact_mod_cast hM'1
  have a2 : (M' : ℝ) ≤ 2 * M := by exact_mod_cast hle
  have a3 : (M' : ℝ) ^ 3 ≤ (2 * (M : ℝ)) ^ 3 := pow_le_pow_left₀ a1.le a2 3
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith
theorem sum_shift_le (P : Finset Lattice4) (i : Fin 4) (g : Lattice4 → ℝ) (hg : ∀ a, 0 ≤ g a) :
    ∑ a ∈ P, (if a + basisVector i ∈ P then g (a + basisVector i) else 0) ≤ ∑ a ∈ P, g a := by
  classical
  rw [← Finset.sum_filter]
  have e : ∑ a ∈ P.filter (fun a => a + basisVector i ∈ P), g (a + basisVector i) =
      ∑ b ∈ (P.filter (fun a => a + basisVector i ∈ P)).image (fun a => a + basisVector i), g b :=
    (Finset.sum_image fun a _ b _ h => add_right_cancel h).symm
  rw [e]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => hg b
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
  exact (Finset.mem_filter.1 ha).2
theorem sum_bondsOf_eq_sum_sum {P : Finset Lattice4} (g : Lattice4 × Fin 4 → ℝ) :
    ∑ b ∈ bondsOf P, g b = ∑ y ∈ P, ∑ i, if y + basisVector i ∈ P then g (y, i) else 0 := by apply _root_.YangMills.Construction.PatchDifferences.sum_bondsOf <;> assumption
theorem sum_bondsOf_cubicKernel_le (P : Finset Lattice4) (x : Lattice4) (h : Lattice4 → ℝ) (hh : ∀ a, 0 ≤ h a) :
    ∑ b ∈ bondsOf P, cubicKernel (x - b.1) * (h b.1 + h (b.1 + basisVector b.2)) ≤
      36 * ∑ a ∈ P, cubicKernel (x - a) * h a := by
  classical
  rw [sum_bondsOf_eq_sum_sum, Finset.sum_comm]
  set T : ℝ := ∑ a ∈ P, cubicKernel (x - a) * h a with hT
  have hi : ∀ i : Fin 4, ∑ a ∈ P, (if a + basisVector i ∈ P then
      cubicKernel (x - a) * (h a + h (a + basisVector i)) else 0) ≤ 9 * T := by
    intro i
    have h1 : ∀ a ∈ P, (if a + basisVector i ∈ P then cubicKernel (x - a) * (h a + h (a + basisVector i)) else 0) ≤
        cubicKernel (x - a) * h a +
          8 * (if a + basisVector i ∈ P then cubicKernel (x - (a + basisVector i)) * h (a + basisVector i)
            else 0) := by
      intro a _
      have h2 := cubicKernel_le_eight_mul_sub (x - a) (basisVector i) (supNorm_basisVector i)
      have e : x - a - basisVector i = x - (a + basisVector i) := by abel
      rw [e] at h2
      have h3 := zero_le_cubicKernel (x - a)
      have h4 := hh a
      have h5 := hh (a + basisVector i)
      split_ifs
      · have h6 := mul_le_mul_of_nonneg_right h2 h5
        nlinarith
      · simp only [mul_zero, add_zero]
        exact mul_nonneg h3 h4
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h2 := sum_shift_le P i (fun a => cubicKernel (x - a) * h a)
      (fun a => mul_nonneg (zero_le_cubicKernel _) (hh a))
    linarith
  refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
  simp
  ring
theorem norm_sub_endpointMean_le {l : ℕ} {c : Lattice4} {P : Finset Lattice4} {G : Lattice4 → Lattice4 × Fin 4 → ℝ}
    {CH : ℝ} (hCH : 0 ≤ CH)
    (hG : ∀ x b, |G x b| ≤ CH * cubicKernel (x - b.1))
    (hpm : ∀ (w : Lattice4 → Fin 4 → ℍ[ℝ]), ∀ x ∈ P,
      randomPathMean l c w x = ∑ b ∈ bondsOf P, G x b • w b.1 b.2)
    (hend : ∀ (φ : Lattice4 → ℍ[ℝ]), ∀ x ∈ P,
      φ x - endpointMean l c φ = - randomPathMean l c (latticeDifference φ) x)
    (φ : Lattice4 → ℍ[ℝ]) (h : Lattice4 → ℝ) (hh : ∀ a, 0 ≤ h a)
    (hstep : ∀ a ∈ P, ∀ i, a + basisVector i ∈ P → ‖φ (a + basisVector i) - φ a‖ ≤ h a + h (a + basisVector i))
    {x : Lattice4} (hx : x ∈ P) :
    ‖φ x - endpointMean l c φ‖ ≤ 36 * CH * ∑ a ∈ P, cubicKernel (x - a) * h a := by
  rw [hend φ x hx, norm_neg, hpm _ x hx]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ b ∈ bondsOf P, ‖G x b • latticeDifference φ b.1 b.2‖ ≤
      CH * (cubicKernel (x - b.1) * (h b.1 + h (b.1 + basisVector b.2))) := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
    have hb0 : b.1 ∈ P := (Finset.mem_product.1 hb1).1
    rw [norm_smul, Real.norm_eq_abs]
    have h2 := hstep b.1 hb0 b.2 hb2
    have h3 : ‖latticeDifference φ b.1 b.2‖ ≤ h b.1 + h (b.1 + basisVector b.2) := h2
    calc |G x b| * ‖latticeDifference φ b.1 b.2‖ ≤
          (CH * cubicKernel (x - b.1)) * (h b.1 + h (b.1 + basisVector b.2)) :=
          mul_le_mul (hG x b) h3 (norm_nonneg _) (mul_nonneg hCH (zero_le_cubicKernel _))
      _ = _ := by ring
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have h2 := sum_bondsOf_cubicKernel_le P x h hh
  nlinarith
theorem norm_le_of_sum_eq_zero {P : Finset Lattice4} (hP : 0 < P.card) {φ : Lattice4 → ℍ[ℝ]}
    (hm : ∑ x ∈ P, φ x = 0) {m : ℍ[ℝ]}
    {B : Lattice4 → ℝ} (hB : ∀ x ∈ P, ‖φ x - m‖ ≤ B x) {x : Lattice4} (hx : x ∈ P) :
    ‖φ x‖ ≤ B x + (1 / (P.card : ℝ)) * ∑ a ∈ P, B a := by
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hP
  have e1 : ∑ a ∈ P, (φ a - m) = - ((P.card : ℝ) • m) := by
    rw [Finset.sum_sub_distrib, hm, Finset.sum_const, zero_sub, Nat.cast_smul_eq_nsmul]
  have h1 : (P.card : ℝ) * ‖m‖ ≤ ∑ a ∈ P, B a := by
    have h2 : ‖∑ a ∈ P, (φ a - m)‖ ≤ ∑ a ∈ P, B a := (norm_sum_le _ _).trans (Finset.sum_le_sum hB)
    rw [e1, norm_neg, norm_smul, Real.norm_of_nonneg hc.le] at h2
    exact h2
  have h2 : ‖m‖ ≤ (1 / (P.card : ℝ)) * ∑ a ∈ P, B a := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hc]
    linarith
  have h3 : ‖φ x‖ ≤ ‖φ x - m‖ + ‖m‖ := by
    have := norm_add_le (φ x - m) m
    simpa using this
  have h4 := hB x hx
  linarith
end Sums
section Bonds
variable {V : F.GaugeField F.top}
theorem patchSite_add_basisVector (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1)
    (a : Lattice4) (i : Fin 4) :
    (closedOrthant S y i = 1 → patchSite S y (a + basisVector i) = patchSite S y a + unitStep 0 i) ∧
      (closedOrthant S y i = -1 → patchSite S y a = patchSite S y (a + basisVector i) + unitStep 0 i) := by apply _root_.YangMills.Construction.PatchDifferences.patchSite_add_basisVector <;> assumption
theorem sectionNormOn_patchSite (hy : y ∈ S) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1)
    (ξ : F.Site 0 → ℍ[ℝ]) {x : Lattice4} (hx : x ∈ cellOffsets F) :
    PatchDifferences.sectionNormOn S ξ (patchSite S y x) = ‖PatchDifferences.localSection S V y ξ x‖ := by
  classical
  have h1 : patchSite S y x ∈ cellSites S y := by
    rw [cellSites_eq_image hy hodd he]
    exact Finset.mem_image.2 ⟨x, hx, rfl⟩
  have h2 : patchSite S y x ∈ sitesOfCells S 0 := (Finset.mem_filter.1 h1).1
  simp only [PatchDifferences.sectionNormOn, if_pos h2, PatchDifferences.localSection,
    PlaquetteLinearization.norm_adjointAction]
theorem zero_le_sectionNormOn (ξ : F.Site 0 → ℍ[ℝ]) (t : F.Site 0) :
    0 ≤ PatchDifferences.sectionNormOn S ξ t := by apply _root_.YangMills.Construction.PatchDifferences.sectionNormOn_nonneg <;> assumption
theorem zero_le_formNormOn (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (t : F.Site 0) :
    0 ≤ PatchDifferences.formNormOn S f t := by apply _root_.YangMills.Construction.PatchDifferences.formNormOn_nonneg <;> assumption
theorem norm_le_formNormOn (f : F.Site 0 → Fin 4 → ℍ[ℝ]) {t : F.Site 0} {i : Fin 4}
    (h : (t, i) ∈ innerBonds S 0) : ‖f t i‖ ≤ PatchDifferences.formNormOn S f t := by apply _root_.YangMills.Construction.PatchForms.norm_le_formNormOn <;> assumption
def poincareSource (S : Finset F.Cell) (V : F.GaugeField F.top) (κ : ℝ) (ξ : F.Site 0 → ℍ[ℝ]) :
    F.Site 0 → ℝ :=
  fun t => PatchDifferences.formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ) t +
    κ * PatchDifferences.sectionNormOn S ξ t
theorem poincareSource_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (ξ : F.Site 0 → ℍ[ℝ]) (t : F.Site 0) :
    0 ≤ poincareSource S V κ ξ t :=
  add_nonneg (zero_le_formNormOn _ _) (mul_nonneg hκ (zero_le_sectionNormOn _ _))
theorem norm_localSection_bond_le {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r : ℝ} (hy : y ∈ S)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) (hF : IsPatchFrame S V y R Cs r)
    (hr : 1 ≤ r * cellSideLength F)
    (hC : 0 ≤ Cs) (ξ : F.Site 0 → ℍ[ℝ]) {a : Lattice4} (ha : a ∈ cellOffsets F) {i : Fin 4}
    (hb : a + basisVector i ∈ cellOffsets F) :
    ‖PatchDifferences.localSection S V y ξ (a + basisVector i) - PatchDifferences.localSection S V y ξ a‖ ≤
      poincareSource S V (2 * (Cs / (cellSideLength F : ℝ))) ξ (patchSite S y a) +
        poincareSource S V (2 * (Cs / (cellSideLength F : ℝ))) ξ (patchSite S y (a + basisVector i)) := by
  classical
  have hNp : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hodd.pos
  have hκ : 0 ≤ 2 * (Cs / (cellSideLength F : ℝ)) := by positivity
  have pa := mem_patchDomain_of_mem_cellOffsets hy hamb hodd he ha
  have pb := mem_patchDomain_of_mem_cellOffsets hy hamb hodd he hb
  have sa : patchSite S y a ∈ sitesOfCells S 0 := by
    have : patchSite S y a ∈ cellSites S y := by
      rw [cellSites_eq_image hy hodd he]
      exact Finset.mem_image.2 ⟨a, ha, rfl⟩
    exact (Finset.mem_filter.1 this).1
  have sb : patchSite S y (a + basisVector i) ∈ sitesOfCells S 0 := by
    have : patchSite S y (a + basisVector i) ∈ cellSites S y := by
      rw [cellSites_eq_image hy hodd he]
      exact Finset.mem_image.2 ⟨_, hb, rfl⟩
    exact (Finset.mem_filter.1 this).1
  have n1 := sectionNormOn_patchSite (V := V) hy hodd he ξ ha
  have n2 := sectionNormOn_patchSite (V := V) hy hodd he ξ hb
  have f1 := zero_le_formNormOn (S := S) (covariantDiff (referenceFieldChain S V 0) ξ) (patchSite S y a)
  have f2 := zero_le_formNormOn (S := S) (covariantDiff (referenceFieldChain S V 0) ξ)
    (patchSite S y (a + basisVector i))
  have g1 := mul_nonneg hκ (zero_le_sectionNormOn (S := S) ξ (patchSite S y a))
  have g2 := mul_nonneg hκ (zero_le_sectionNormOn (S := S) ξ (patchSite S y (a + basisVector i)))
  obtain ⟨c1, c2⟩ := patchSite_add_basisVector he a i
  simp only [poincareSource]
  rcases he i with hs | hs
  · have hst := c1 hs
    have h1 := norm_localSection_step_le hF hr ξ pa pb
      (by rw [add_sub_cancel_left, supNorm_basisVector]) hst
    have hbond : (patchSite S y a, i) ∈ innerBonds S 0 :=
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨sa, Finset.mem_univ _⟩, by rw [← hst]; exact sb⟩
    have h2 := norm_le_formNormOn (covariantDiff (referenceFieldChain S V 0) ξ) hbond
    rw [← n2] at h1
    linarith
  · have hst := c2 hs
    have h1 := norm_localSection_step_le hF hr ξ pb pa
      (by rw [sub_add_cancel_left, supNorm_neg, supNorm_basisVector]) hst
    have hbond : (patchSite S y (a + basisVector i), i) ∈ innerBonds S 0 :=
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨sb, Finset.mem_univ _⟩, by rw [← hst]; exact sa⟩
    have h2 := norm_le_formNormOn (covariantDiff (referenceFieldChain S V 0) ξ) hbond
    rw [← n1] at h1
    rw [norm_sub_rev]
    linarith
end Bonds
section Norms
def restrictToCell (S : Finset F.Cell) (y : F.Cell) (g : F.Site 0 → ℝ) : F.Site 0 → ℝ := by
  classical exact fun t => if t ∈ cellSites S y then g t else 0
theorem restrictToCell_of_mem {g : F.Site 0 → ℝ} {t : F.Site 0} (h : t ∈ cellSites S y) :
    restrictToCell S y g t = g t := by
  classical
  simp only [restrictToCell, if_pos h]
theorem restrictToCell_of_not_mem {g : F.Site 0 → ℝ} {t : F.Site 0} (h : t ∉ cellSites S y) :
    restrictToCell S y g t = 0 := by
  classical
  simp only [restrictToCell, if_neg h]
theorem restrictToCell_nonneg {g : F.Site 0 → ℝ} (hg : ∀ t, 0 ≤ g t) (t : F.Site 0) :
    0 ≤ restrictToCell S y g t := by
  classical
  by_cases h : t ∈ cellSites S y
  · rw [restrictToCell_of_mem h]
    exact hg t
  · rw [restrictToCell_of_not_mem h]
theorem zero_le_patchCubicKernel {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t) (t : F.Site 0) :
    0 ≤ patchCubicKernel S y f t := by apply _root_.YangMills.Construction.PatchPotentials.patchCubicKernel_nonneg <;> assumption
theorem seminorm_eq_zero_of_vanish {M : (F.Site 0 → ℝ) → F.Cell → ℝ} (hM : IsCellSeminorm S M)
    {f : F.Site 0 → ℝ} {y : F.Cell} (h : ∀ x ∈ cellSites S y, f x = 0) : M f y = 0 := by apply _root_.YangMills.Construction.PatchDifferences.cellSeminorm_eq_zero_of_vanish <;> assumption
theorem restrictToPatch_restrictToCell_of_not_mem {g : F.Site 0 → ℝ} {t : F.Site 0} (h : t ∉ cellSites S y) :
    restrictToPatch S y (restrictToCell S y g) t = 0 := by
  classical
  simp only [restrictToPatch, restrictToCell_of_not_mem h]
  split_ifs <;> rfl
theorem abs_restrictToPatch_restrictToCell_le {g : F.Site 0 → ℝ} (hg : ∀ t, 0 ≤ g t) (t : F.Site 0) :
    |restrictToPatch S y (restrictToCell S y g) t| ≤ |g t| := by
  classical
  by_cases h : t ∈ cellSites S y
  · simp only [restrictToPatch, restrictToCell_of_mem h]
    split_ifs
    · exact le_refl _
    · simp
  · rw [restrictToPatch_restrictToCell_of_not_mem h]
    simp
theorem target_patchCubicKernel_le {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
    (hN : CellNormFamily S Md Lf Sr σ K) (hy : y ∈ S) (g : F.Site 0 → ℝ) :
    Lf (patchCubicKernel S y (restrictToCell S y g)) y ≤ K * Sr (restrictToPatch S y (restrictToCell S y g)) y := by
  classical
  have h1 := hN.kernel_le y hy (restrictToCell S y g) y
  have hyb : y ∈ cellBall S y 20 := Finset.mem_filter.2 ⟨hy, by rw [cellSupDist_self_eq_zero]; omega⟩
  rwa [Finset.sum_eq_single_of_mem y hyb] at h1
  intro x _ hxy
  refine seminorm_eq_zero_of_vanish hN.isSeminorm_source fun t ht =>
    restrictToPatch_restrictToCell_of_not_mem fun h2 => hxy ?_
  rw [← (Finset.mem_filter.1 ht).2, ← (Finset.mem_filter.1 h2).2]
theorem seminorm_le_of_pointwise {M : (F.Site 0 → ℝ) → F.Cell → ℝ} (hM : IsCellSeminorm S M)
    {g Kt : F.Site 0 → ℝ} {A C3 : ℝ}
    (hC3 : 0 ≤ C3) (hKt : ∀ t, 0 ≤ Kt t) (hA : 0 ≤ A) (hpt : ∀ t ∈ cellSites S y, |g t| ≤ C3 * (Kt t + A)) :
    M g y ≤ C3 * (M Kt y + M (fun _ => A) y) := by
  have h1 : M g y ≤ M (fun t => C3 * (Kt t + A)) y := hM.mono_abs _ _ _ fun t ht => by
    have h2 : 0 ≤ C3 * (Kt t + A) := mul_nonneg hC3 (add_nonneg (hKt t) hA)
    rw [abs_of_nonneg h2]
    exact hpt t ht
  rw [hM.smul, abs_of_nonneg hC3] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (hM.add_le _ _ _) hC3)
theorem base_le_of_pointwise {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
    (hN : CellNormFamily S Md Lf Sr σ K) (hK : 0 < K) (hy : y ∈ S) (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) {g H : F.Site 0 → ℝ} (hH : ∀ t, 0 ≤ H t)
    {C3 : ℝ} (hC3 : 0 ≤ C3)
    (hpt : ∀ t ∈ cellSites S y, |g t| ≤ C3 * (patchCubicKernel S y (restrictToCell S y H) t +
      (1 / (cellSideLength F : ℝ) ^ 4) * ∑ t' ∈ cellSites S y, patchCubicKernel S y (restrictToCell S y H) t')) :
    Md g y ≤ C3 * (1 + K ^ 2) * K ^ 2 * (cellSideLength F : ℝ) * Md H y := by
  have hNp : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hodd.pos
  set N : ℝ := (cellSideLength F : ℝ) with hNd
  set Kt := patchCubicKernel S y (restrictToCell S y H) with hKtd
  have hKt : ∀ t, 0 ≤ Kt t := zero_le_patchCubicKernel (restrictToCell_nonneg hH)
  set T : ℝ := ∑ t' ∈ cellSites S y, Kt t' with hTd
  have hT : 0 ≤ T := Finset.sum_nonneg fun t _ => hKt t
  set A : ℝ := (1 / N ^ 4) * T with hAd
  have hA : 0 ≤ A := by positivity
  have h1 := seminorm_le_of_pointwise hN.isSeminorm_base hC3 hKt hA hpt
  have hσ := hN.scale_pos y
  have h2 : Md (fun _ => A) y ≤ K ^ 2 * Md Kt y := by
    have e1 : Md (fun _ => A) y = A * Md (fun _ => 1) y := by
      have := hN.isSeminorm_base.smul A (fun _ => 1) y
      simp only [mul_one] at this
      rw [this, abs_of_nonneg hA]
    have h3 : Md (fun _ => 1) y ≤ K * N * σ y := (hN.base_le_target _ _).trans (hN.const_le y)
    have h4 : σ y * T ≤ K * N ^ 3 * Md Kt y := by
      have := hN.mean_le Kt y
      have e2 : ∑ x ∈ cellSites S y, |Kt x| = T := Finset.sum_congr rfl fun t _ => abs_of_nonneg (hKt t)
      rwa [e2] at this
    rw [e1]
    calc A * Md (fun _ => 1) y ≤ A * (K * N * σ y) := mul_le_mul_of_nonneg_left h3 hA
      _ = (K / N ^ 3) * (σ y * T) := by
        rw [hAd]
        field_simp
      _ ≤ (K / N ^ 3) * (K * N ^ 3 * Md Kt y) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = K ^ 2 * Md Kt y := by
        field_simp
  have h5 : Md Kt y ≤ K ^ 2 * N * Md H y := by
    have a1 := (hN.base_le_target Kt y).trans (target_patchCubicKernel_le hN hy H)
    have a2 := hN.source_le (restrictToPatch S y (restrictToCell S y H)) y
    have a3 : Md (restrictToPatch S y (restrictToCell S y H)) y ≤ Md H y :=
      hN.isSeminorm_base.mono_abs _ _ _ fun t _ => abs_restrictToPatch_restrictToCell_le hH t
    calc Md Kt y ≤ K * Sr (restrictToPatch S y (restrictToCell S y H)) y := a1
      _ ≤ K * (K * N * Md (restrictToPatch S y (restrictToCell S y H)) y) := mul_le_mul_of_nonneg_left a2 hK.le
      _ ≤ K * (K * N * Md H y) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left a3 (by positivity)) hK.le
      _ = _ := by ring
  calc Md g y ≤ C3 * (Md Kt y + Md (fun _ => A) y) := h1
    _ ≤ C3 * (Md Kt y + K ^ 2 * Md Kt y) := mul_le_mul_of_nonneg_left (by linarith) hC3
    _ = C3 * (1 + K ^ 2) * Md Kt y := by ring
    _ ≤ C3 * (1 + K ^ 2) * (K ^ 2 * N * Md H y) := mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := by ring
theorem card_cellSites (hy : y ∈ S) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) :
    ((cellSites S y).card : ℝ) = (cellSideLength F : ℝ) ^ 4 := by
  classical
  rw [cellSites_eq_image hy hodd he, Finset.card_image_of_injOn (injOn_patchSite hamb hodd he),
    card_cellOffsets hodd.pos]
theorem weightedLpNormOnCell_le_of_lt (hy : y ∈ S) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1)
    {Q P : ℝ} (hQ : 0 < Q) (hQP : Q < P) (f : F.Site 0 → ℝ) :
    weightedLpNormOnCell Q S (fun _ => 1) f y ≤
      ((cellSideLength F : ℝ) ^ 4) ^ (1 / Q - 1 / P) * weightedLpNormOnCell P S (fun _ => 1) f y := by
  unfold weightedLpNormOnCell
  rw [← card_cellSites hy hamb hodd he]
  exact lpNorm_le_card_rpow_mul_lpNorm (cellSites S y) (fun x => |1 * f x|) (fun _ => abs_nonneg _) hQ hQP
theorem weightedLpNormOnCell_twelve_le {CL : ℝ} (hCL0 : 0 ≤ CL)
    (hCL : ∀ (D E : Finset Lattice4) (f : Lattice4 → ℝ),
      (∑ x ∈ E, |∑ y ∈ D, cubicKernel (x - y) * f y| ^ (12 : ℝ)) ^ (1 / (12 : ℝ)) ≤
        CL * (∑ y ∈ D, |f y| ^ (3 : ℝ)) ^ (1 / (3 : ℝ)))
    (hy : y ∈ S) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) {g H : F.Site 0 → ℝ} (hH : ∀ t, 0 ≤ H t)
    {C3 : ℝ} (hC3 : 0 ≤ C3)
    (hpt : ∀ t ∈ cellSites S y, |g t| ≤ C3 * (patchCubicKernel S y (restrictToCell S y H) t +
      (1 / (cellSideLength F : ℝ) ^ 4) * ∑ t' ∈ cellSites S y, patchCubicKernel S y (restrictToCell S y H) t')) :
    weightedLpNormOnCell 12 S (fun _ => 1) g y ≤ 2 * C3 * CL * weightedLpNormOnCell 3 S (fun _ => 1) H y := by
  have hNp : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hodd.pos
  set X : ℝ := (cellSideLength F : ℝ) ^ 4 with hXd
  have hX : 0 < X := by positivity
  set Kt := patchCubicKernel S y (restrictToCell S y H) with hKtd
  have hKt : ∀ t, 0 ≤ Kt t := zero_le_patchCubicKernel (restrictToCell_nonneg hH)
  set T : ℝ := ∑ t' ∈ cellSites S y, Kt t' with hTd
  have hT : 0 ≤ T := Finset.sum_nonneg fun t _ => hKt t
  set A : ℝ := (1 / X) * T with hAd
  have hA : 0 ≤ A := by positivity
  have M12 := weightedLpNormOnCell_isCellSeminorm (by norm_num : (1 : ℝ) ≤ 12) S (fun _ : F.Site 0 => (1 : ℝ))
  have M3 := weightedLpNormOnCell_isCellSeminorm (by norm_num : (1 : ℝ) ≤ 3) S (fun _ : F.Site 0 => (1 : ℝ))
  have h1 := seminorm_le_of_pointwise M12 hC3 hKt hA hpt
  have h2 : weightedLpNormOnCell 12 S (fun _ => 1) (fun _ => A) y ≤ weightedLpNormOnCell 12 S (fun _ => 1) Kt y := by
    have e1 : weightedLpNormOnCell 12 S (fun _ => 1) (fun _ => A) y = X ^ (1 / (12 : ℝ)) * A := by
      unfold weightedLpNormOnCell
      simp only [one_mul, abs_of_nonneg hA, Finset.sum_const, nsmul_eq_mul]
      rw [card_cellSites hy hamb hodd he, Real.mul_rpow hX.le (Real.rpow_nonneg hA _), ← Real.rpow_mul hA]
      norm_num
    have e2 : weightedLpNormOnCell 1 S (fun _ => 1) Kt y = T := by
      unfold weightedLpNormOnCell
      simp only [one_mul, Real.rpow_one, div_one]
      exact Finset.sum_congr rfl fun t _ => abs_of_nonneg (hKt t)
    have h3 := weightedLpNormOnCell_le_of_lt hy hamb hodd he (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 12) Kt
    rw [e2] at h3
    have e3 : X ^ (1 / (12 : ℝ)) * X ^ (1 / (1 : ℝ) - 1 / 12) = X := by
      rw [← Real.rpow_add hX]
      norm_num
    rw [e1, hAd]
    calc X ^ (1 / (12 : ℝ)) * (1 / X * T) ≤ X ^ (1 / (12 : ℝ)) * (1 / X * (X ^ (1 / (1 : ℝ) - 1 / 12) *
          weightedLpNormOnCell 12 S (fun _ => 1) Kt y)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
      _ = (X ^ (1 / (12 : ℝ)) * X ^ (1 / (1 : ℝ) - 1 / 12)) * (1 / X) *
          weightedLpNormOnCell 12 S (fun _ => 1) Kt y := by ring
      _ = _ := by
        rw [e3]
        field_simp
  have h3 : weightedLpNormOnCell 12 S (fun _ => 1) Kt y ≤
      CL * weightedLpNormOnCell 3 S (fun _ => 1) (restrictToCell S y H) y := by
    have h4 := hCL (cellOffsets F) (cellOffsets F) (fun a => restrictToCell S y H (patchSite S y a))
    unfold weightedLpNormOnCell
    simp only [one_mul]
    rw [sum_cellSites_eq hy hamb hodd he, sum_cellSites_eq hy hamb hodd he]
    have e1 : ∑ x ∈ cellOffsets F, |Kt (patchSite S y x)| ^ (12 : ℝ) =
        ∑ x ∈ cellOffsets F,
          |∑ a ∈ cellOffsets F, cubicKernel (x - a) * restrictToCell S y H (patchSite S y a)| ^ (12 : ℝ) :=
      Finset.sum_congr rfl fun x hx => by
        rw [hKtd, patchCubicKernel_patchSite hy hamb hodd he (fun t ht => restrictToCell_of_not_mem ht) hx]
    rw [e1]
    exact h4
  have h4 : weightedLpNormOnCell 3 S (fun _ => 1) (restrictToCell S y H) y ≤
      weightedLpNormOnCell 3 S (fun _ => 1) H y :=
    M3.mono_abs _ _ _ fun t ht => by rw [restrictToCell_of_mem ht]
  calc weightedLpNormOnCell 12 S (fun _ => 1) g y ≤ C3 * (weightedLpNormOnCell 12 S (fun _ => 1) Kt y +
        weightedLpNormOnCell 12 S (fun _ => 1) (fun _ => A) y) := h1
    _ ≤ C3 * (2 * weightedLpNormOnCell 12 S (fun _ => 1) Kt y) := mul_le_mul_of_nonneg_left (by linarith) hC3
    _ ≤ C3 * (2 * (CL * weightedLpNormOnCell 3 S (fun _ => 1) H y)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h3.trans ?_) (by norm_num)) hC3
        exact mul_le_mul_of_nonneg_left h4 hCL0
    _ = _ := by ring
end Norms
section Pointwise
variable {V : F.GaugeField F.top}
theorem abs_sectionNormOn_le {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r CH : ℝ}
    {G : Lattice4 → Lattice4 × Fin 4 → ℝ} {l : ℕ} {c : Lattice4} (hy : y ∈ S)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1)
    (hF : IsPatchFrame S V y R Cs r) (hr : 1 ≤ r * cellSideLength F) (hC : 0 ≤ Cs) (hCH : 0 ≤ CH)
    (hG : ∀ x b, |G x b| ≤ CH * cubicKernel (x - b.1))
    (hpm : ∀ (w : Lattice4 → Fin 4 → ℍ[ℝ]), ∀ x ∈ cellOffsets F,
      randomPathMean l c w x = ∑ b ∈ bondsOf (cellOffsets F), G x b • w b.1 b.2)
    (hend : ∀ (φ : Lattice4 → ℍ[ℝ]), ∀ x ∈ cellOffsets F,
      φ x - endpointMean l c φ = - randomPathMean l c (latticeDifference φ) x)
    {ξ : F.Site 0 → ℍ[ℝ]} (hξ : CellMeanFree S V ξ) :
    ∀ t ∈ cellSites S y, |PatchDifferences.sectionNormOn S ξ t| ≤ (36 * CH) *
      (patchCubicKernel S y (restrictToCell S y (poincareSource S V (2 * (Cs / (cellSideLength F : ℝ))) ξ)) t +
        (1 / (cellSideLength F : ℝ) ^ 4) * ∑ t' ∈ cellSites S y,
          patchCubicKernel S y (restrictToCell S y (poincareSource S V (2 * (Cs / (cellSideLength F : ℝ))) ξ)) t') := by
  classical
  have hNp : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hodd.pos
  set κ : ℝ := 2 * (Cs / (cellSideLength F : ℝ)) with hκd
  have hκ : 0 ≤ κ := by positivity
  set H := poincareSource S V κ ξ with hHd
  have hH : ∀ t, 0 ≤ H t := poincareSource_nonneg hκ ξ
  set Kt := patchCubicKernel S y (restrictToCell S y H) with hKtd
  set φ := PatchDifferences.localSection S V y ξ with hφd
  have hcard : ((cellOffsets F).card : ℝ) = (cellSideLength F : ℝ) ^ 4 := card_cellOffsets hodd.pos
  have hcp : 0 < (cellOffsets F).card := by
    have : (0 : ℝ) < ((cellOffsets F).card : ℝ) := by
      rw [hcard]
      positivity
    exact_mod_cast this
  have hmean : ∑ x ∈ cellOffsets F, φ x = 0 := by
    have h1 := hξ y hy
    simp only [frameCellMean] at h1
    have h2 : (1 / (cellSideLength F : ℝ) ^ 4) ≠ 0 := by positivity
    exact (smul_eq_zero.1 h1).resolve_left h2
  have hKx : ∀ x ∈ cellOffsets F, Kt (patchSite S y x) =
      ∑ a ∈ cellOffsets F, cubicKernel (x - a) * H (patchSite S y a) := by
    intro x hx
    rw [hKtd, patchCubicKernel_patchSite hy hamb hodd he (fun t ht => restrictToCell_of_not_mem ht) hx]
    refine Finset.sum_congr rfl fun a ha => ?_
    have : patchSite S y a ∈ cellSites S y := by
      rw [cellSites_eq_image hy hodd he]
      exact Finset.mem_image.2 ⟨a, ha, rfl⟩
    rw [restrictToCell_of_mem this]
  have hB : ∀ x ∈ cellOffsets F, ‖φ x - endpointMean l c φ‖ ≤ (36 * CH) * Kt (patchSite S y x) := by
    intro x hx
    rw [hKx x hx]
    exact norm_sub_endpointMean_le hCH hG hpm hend φ (fun a => H (patchSite S y a)) (fun a => hH _)
      (fun a ha i hb => norm_localSection_bond_le hy hamb hodd he hF hr hC ξ ha hb) hx
  intro t ht
  rw [cellSites_eq_image hy hodd he] at ht
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ht
  rw [abs_of_nonneg (zero_le_sectionNormOn ξ _), sectionNormOn_patchSite (V := V) hy hodd he ξ hx,
    sum_cellSites_eq hy hamb hodd he]
  have h1 := norm_le_of_sum_eq_zero hcp hmean hB hx
  rw [hcard, ← Finset.mul_sum] at h1
  refine h1.trans (le_of_eq ?_)
  ring
end Pointwise
theorem cellPoincareStatement_holds (hHF : randomStaircaseHomotopyStatement)
    (hFr : patchFrameExistenceStatement)
    (hLH : hardyLittlewoodSobolevStatement) : cellPoincareStatement := by
  intro K hK
  obtain ⟨CH, hCH, hHF⟩ := hHF
  obtain ⟨C0, r, c0, hC0, hr, hc0, hFr⟩ := hFr
  obtain ⟨CL, hCL0, hCL⟩ := hLH 3 12 (by norm_num) (by norm_num) (by norm_num)
  set C3 : ℝ := 36 * CH with hC3d
  have hC3 : 0 < C3 := by positivity
  set C4 : ℝ := C3 * (1 + K ^ 2) * K ^ 2 with hC4d
  have hC4 : 0 < C4 := by positivity
  set C5 : ℝ := 2 * C3 * CL with hC5d
  have hC5 : 0 < C5 := by positivity
  refine ⟨2 * C4 + 2 * C5, min c0 (1 / (4 * (C4 + C5) * C0)), ⌈1 / r⌉₊ + 1, by positivity,
    lt_min hc0 (by positivity), ?_⟩
  intro F m S hodd hL1 hamb hm hreg s V hs hsc hcold ξ hξ y hy
  classical
  have hL := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  have hNp : (0 : ℝ) < cellSideLength F := by exact_mod_cast hN
  have hsc0 : s ≤ c0 := hsc.trans (min_le_left _ _)
  have hsc1 : s ≤ 1 / (4 * (C4 + C5) * C0) := hsc.trans (min_le_right _ _)
  have hsmall : 4 * (C4 + C5) * (C0 * s) ≤ 1 := by
    have h1 : (4 * (C4 + C5) * C0) * s ≤ (4 * (C4 + C5) * C0) * (1 / (4 * (C4 + C5) * C0)) :=
      mul_le_mul_of_nonneg_left hsc1 (by positivity)
    rw [mul_one_div_cancel (by positivity)] at h1
    linarith
  obtain ⟨he, -⟩ := closedOrthant_spec (S := S) hreg (show 32 ≤ m by omega) y
  obtain ⟨R, hR⟩ := hFr F m S hodd hamb hm hreg s V hs hsc0 hcold y hy
  have hrN : 1 ≤ r * cellSideLength F := by
    have h2 : (1 / r) ≤ (F.blockSide : ℝ) := by
      have h3 := Nat.le_ceil (1 / r)
      have h4 : ((⌈1 / r⌉₊ + 1 : ℕ) : ℝ) ≤ F.blockSide := by exact_mod_cast hL1
      push_cast at h4
      linarith
    have h3 : (F.blockSide : ℝ) ≤ cellSideLength F := by
      have h4 : F.blockSide ≤ F.blockSide ^ F.top := Nat.le_self_pow (by simp) _
      have h5 : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
      have h6 : ((F.blockSide : ℤ)) ≤ cellSideLength F := by rw [← h5]; exact_mod_cast h4
      exact_mod_cast h6
    have h4 : 1 / r ≤ cellSideLength F := h2.trans h3
    rw [div_le_iff₀ hr] at h4
    linarith
  have hl : ((F.blockSide ^ F.top : ℕ) : ℤ) = cellSideLength F := by simp [cellSideLength]
  have hcube : ∀ q ∈ cornerCube (F.blockSide ^ F.top) (0 : Lattice4), q ∈ cellOffsets F := by
    intro q hq
    refine mem_cellOffsets_iff.2 fun i => ?_
    have h1 := Fintype.mem_piFinset.1 hq i
    rw [Finset.mem_Ico] at h1
    simp only [Pi.zero_apply, zero_add] at h1
    omega
  have hfill : IsFilledToward (F.blockSide ^ F.top) (0 : Lattice4) (cellOffsets F) := by
    refine ⟨hcube, fun x hx i => ?_, fun x hx q hq w hw => ?_⟩
    · have h1 := mem_cellOffsets_iff.1 hx i
      simp only [Pi.zero_apply, sub_zero]
      rw [abs_of_nonneg h1.1, hl]
      omega
    · refine mem_cellOffsets_iff.2 fun i => ?_
      have h1 := mem_cellOffsets_iff.1 hx i
      have h2 := mem_cellOffsets_iff.1 (hcube q hq) i
      have h3 := hw i
      constructor
      · exact le_trans (le_min h1.1 h2.1) h3.1
      · exact lt_of_le_of_lt h3.2 (max_lt h1.2 h2.2)
  have hl1 : 1 ≤ F.blockSide ^ F.top := Nat.one_le_pow _ _ hL
  obtain ⟨Hk, G, -, hG, hE⟩ := hHF (F.blockSide ^ F.top) 0 (cellOffsets F) hl1 hfill
  obtain ⟨hpm, -, hend⟩ := hE ℍ[ℝ]
  set Cs : ℝ := C0 * s with hCsd
  have hCs : 0 ≤ Cs := by positivity
  have hpt := abs_sectionNormOn_le (V := V) hy hamb hodd he hR hrN hCs hCH.le hG hpm hend hξ
  set κ : ℝ := 2 * (Cs / (cellSideLength F : ℝ)) with hκd
  have hκ : 0 ≤ κ := by positivity
  have hH : ∀ t, 0 ≤ poincareSource S V κ ξ t := poincareSource_nonneg hκ ξ
  set D := covariantDiff (referenceFieldChain S V 0) ξ with hDd
  constructor
  · intro Md Lf Sr σ hNo
    have h1 := base_le_of_pointwise hNo hK hy hamb hodd he hH hC3.le hpt
    have h2 : Md (poincareSource S V κ ξ) y ≤
        Md (PatchDifferences.formNormOn S D) y + κ * Md (PatchDifferences.sectionNormOn S ξ) y := by
      have a1 := hNo.isSeminorm_base.add_le (PatchDifferences.formNormOn S D)
        (fun t => κ * PatchDifferences.sectionNormOn S ξ t) y
      have a2 := hNo.isSeminorm_base.smul κ (PatchDifferences.sectionNormOn S ξ) y
      rw [a2, abs_of_nonneg hκ] at a1
      exact a1
    have hA0 := hNo.isSeminorm_base.nonneg (PatchDifferences.sectionNormOn S ξ) y
    have hB0 := hNo.isSeminorm_base.nonneg (PatchDifferences.formNormOn S D) y
    set A0 := Md (PatchDifferences.sectionNormOn S ξ) y
    set B0 := Md (PatchDifferences.formNormOn S D) y
    have h3 : A0 ≤ C4 * (cellSideLength F : ℝ) * (B0 + κ * A0) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    have e : C4 * (cellSideLength F : ℝ) * (κ * A0) = (2 * C4 * Cs) * A0 := by
      rw [hκd]
      field_simp
    have h4 : 2 * C4 * Cs ≤ 1 / 2 := by
      have : 4 * C4 * Cs ≤ 4 * (C4 + C5) * Cs := by
        have := mul_nonneg hC5.le hCs
        nlinarith
      linarith
    have h5 : (2 * C4 * Cs) * A0 ≤ (1 / 2) * A0 := mul_le_mul_of_nonneg_right h4 hA0
    have h6 : A0 ≤ C4 * (cellSideLength F : ℝ) * B0 + (1 / 2) * A0 := by
      have : C4 * (cellSideLength F : ℝ) * (B0 + κ * A0) =
          C4 * (cellSideLength F : ℝ) * B0 + C4 * (cellSideLength F : ℝ) * (κ * A0) := by ring
      rw [this, e] at h3
      linarith
    have h7 : 0 ≤ C5 * (cellSideLength F : ℝ) * B0 := by positivity
    have e2 : (2 * C4 + 2 * C5) * (cellSideLength F : ℝ) * B0 =
        2 * (C4 * (cellSideLength F : ℝ) * B0) + 2 * (C5 * (cellSideLength F : ℝ) * B0) := by ring
    rw [e2]
    linarith
  · have h1 := weightedLpNormOnCell_twelve_le hCL0.le hCL hy hamb hodd he hH hC3.le hpt
    have M3 := weightedLpNormOnCell_isCellSeminorm (by norm_num : (1 : ℝ) ≤ 3) S (fun _ : F.Site 0 => (1 : ℝ))
    have M12 := weightedLpNormOnCell_isCellSeminorm (by norm_num : (1 : ℝ) ≤ 12) S (fun _ : F.Site 0 => (1 : ℝ))
    have h2 : weightedLpNormOnCell 3 S (fun _ => 1) (poincareSource S V κ ξ) y ≤
        weightedLpNormOnCell 3 S (fun _ => 1) (PatchDifferences.formNormOn S D) y +
          κ * weightedLpNormOnCell 3 S (fun _ => 1) (PatchDifferences.sectionNormOn S ξ) y := by
      have a1 := M3.add_le (PatchDifferences.formNormOn S D) (fun t => κ * PatchDifferences.sectionNormOn S ξ t) y
      have a2 := M3.smul κ (PatchDifferences.sectionNormOn S ξ) y
      rw [a2, abs_of_nonneg hκ] at a1
      exact a1
    have h3 := weightedLpNormOnCell_le_of_lt hy hamb hodd he (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (3 : ℝ) < 12) (PatchDifferences.sectionNormOn S ξ)
    have e1 : (((cellSideLength F : ℝ) ^ 4) ^ (1 / (3 : ℝ) - 1 / 12)) = (cellSideLength F : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
      norm_num
    rw [e1] at h3
    have hE0 := M12.nonneg (PatchDifferences.sectionNormOn S ξ) y
    have hB0 := M3.nonneg (PatchDifferences.formNormOn S D) y
    set E0 := weightedLpNormOnCell 12 S (fun _ => 1) (PatchDifferences.sectionNormOn S ξ) y
    set B0 := weightedLpNormOnCell 3 S (fun _ => 1) (PatchDifferences.formNormOn S D) y
    have h4 : κ * weightedLpNormOnCell 3 S (fun _ => 1) (PatchDifferences.sectionNormOn S ξ) y ≤
        (2 * Cs) * E0 := by
      calc _ ≤ κ * ((cellSideLength F : ℝ) * E0) := mul_le_mul_of_nonneg_left h3 hκ
        _ = _ := by
          rw [hκd]
          field_simp
    have h5 : E0 ≤ C5 * (B0 + (2 * Cs) * E0) := by
      refine h1.trans (mul_le_mul_of_nonneg_left (h2.trans ?_) hC5.le)
      linarith
    have h6 : 2 * C5 * Cs ≤ 1 / 2 := by
      have : 4 * C5 * Cs ≤ 4 * (C4 + C5) * Cs := by
        have := mul_nonneg hC4.le hCs
        nlinarith
      linarith
    have h7 : (2 * C5 * Cs) * E0 ≤ (1 / 2) * E0 := mul_le_mul_of_nonneg_right h6 hE0
    have h8 : 0 ≤ C4 * B0 := by positivity
    nlinarith
end YangMills.Construction.CellPoincare
end
