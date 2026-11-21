import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMotionsOfAChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BondHull
open BlockAverages LatticePaths BlockLines FlatPairing LatticeFractionalIntegration
variable {F : BlockFrame} {j : ℕ}
def linkRatio (X R : F.GaugeField j) (x : F.Site j) (st : PathStep) : UnitQuaternion :=
  linkValue X x st * (linkValue R x st)⁻¹
def pathRatio (X R : F.GaugeField j) (x : F.Site j) (l : List PathStep) : UnitQuaternion :=
  pathHolonomy X x l * (pathHolonomy R x l)⁻¹
theorem pathRatio_cons (X R : F.GaugeField j) (x : F.Site j) (st : PathStep) (l : List PathStep) :
    pathRatio X R x (st :: l) = linkRatio X R x st *
      (linkValue R x st * pathRatio X R (x + BlockAverages.stepDisplacement j st) l * (linkValue R x st)⁻¹) := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.pathDiscrepancy_cons <;> assumption
theorem stepDisplacement_eq_siteOfCoords (st : PathStep) :
    BlockAverages.stepDisplacement (F := F) j st = siteOfCoords j (FlatPairing.stepDisplacement st) := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords <;> assumption
theorem distFromOne_pathRatio_le (X R : F.GaugeField j) (x₀ : F.Site j) (p : Lattice4 → Prop) (t : ℝ)
    (ht0 : 0 ≤ t)
    (ht : ∀ u st, p u → p (u + FlatPairing.stepDisplacement st) →
      distFromOne (linkRatio X R (x₀ + siteOfCoords j u) st) ≤ t) :
    ∀ (l : List PathStep) (u : Lattice4), AllAlong p u l →
      distFromOne (pathRatio X R (x₀ + siteOfCoords j u) l) ≤ l.length * t := by
  intro l
  induction l with
  | nil =>
    intro u _
    simp [pathRatio, pathHolonomy, distFromOne]
  | cons st r ih =>
    intro u hu
    have e : x₀ + siteOfCoords j u + BlockAverages.stepDisplacement j st =
        x₀ + siteOfCoords j (u + FlatPairing.stepDisplacement st) := by
      rw [stepDisplacement_eq_siteOfCoords, siteOfCoords_add, add_assoc]
    rw [pathRatio_cons, e]
    have h1 := ht u st hu.1 (allAlong_head hu.2)
    have h2 := ih _ hu.2
    have h3 := norm_coe_mul_sub_one_le (linkRatio X R (x₀ + siteOfCoords j u) st)
      (linkValue R (x₀ + siteOfCoords j u) st *
        pathRatio X R (x₀ + siteOfCoords j (u + FlatPairing.stepDisplacement st)) r *
        (linkValue R (x₀ + siteOfCoords j u) st)⁻¹)
    rw [norm_coe_conj_sub_one] at h3
    have hl : (((st :: r).length : ℕ) : ℝ) * t = (r.length : ℝ) * t + t := by
      simp only [List.length_cons]
      push_cast
      ring
    rw [hl]
    unfold distFromOne at *
    linarith
theorem distFromOne_linkRatio_le (X R : F.GaugeField j) (x₀ : F.Site j) (H : Set Lattice4) (t : ℝ)
    (hcl : ∀ a ∈ H, ∀ k, a + basisVector k ∈ H →
      distFromOne (X (x₀ + siteOfCoords j a) k * (R (x₀ + siteOfCoords j a) k)⁻¹) ≤ t)
    (u : Lattice4) (st : PathStep) (hu : u ∈ H) (hv : u + FlatPairing.stepDisplacement st ∈ H) :
    distFromOne (linkRatio X R (x₀ + siteOfCoords j u) st) ≤ t := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.normSubOne_linkDiscrepancy_le <;> assumption
theorem le_of_mem_twoBlockHull (hodd : Odd F.blockSide) (hj : j + 1 ≤ F.top) {f : F.Site j → Fin 4 → ℝ}
    {b : F.Site (j + 1) × Fin 4} {t : ℝ} (hB : BoundedOnAdjacentBlocks f b t) :
    ∀ a ∈ twoBlockHull F.blockSide b.2, ∀ k, a + basisVector k ∈ twoBlockHull F.blockSide b.2 →
      f (refineSite b.1 + siteOfCoords j a) k ≤ t := by
  intro a ha k ha'
  obtain ⟨m, hm⟩ := hodd
  have hLz : (F.blockSide : ℤ) = 2 * (m : ℤ) + 1 := by rw [hm]; push_cast; ring
  have hmm : ((F.blockSide : ℤ) - 1) / 2 = m := by omega
  have hcube : ∀ g : Lattice4, g ∈ centredCube F.blockSide ↔ ∀ i, -(m : ℤ) ≤ g i ∧ g i ≤ m := by
    intro g
    rw [mem_centredCube_iff, hmm]
  have hh : ∀ μ, -(m : ℤ) ≤ a μ ∧ a μ ≤ m + if μ = b.2 then (F.blockSide : ℤ) else 0 := by
    intro μ
    have := ha μ
    rwa [hmm] at this
  have hh' : ∀ μ, -(m : ℤ) ≤ (a + basisVector k) μ ∧
      (a + basisVector k) μ ≤ m + if μ = b.2 then (F.blockSide : ℤ) else 0 := by
    intro μ
    have := ha' μ
    rwa [hmm] at this
  have hother : ∀ μ, μ ≠ b.2 → -(m : ℤ) ≤ a μ ∧ a μ ≤ m := by
    intro μ hμ
    have := hh μ
    rwa [if_neg hμ, add_zero] at this
  have hother' : ∀ μ, μ ≠ b.2 → -(m : ℤ) ≤ (a + basisVector k) μ ∧ (a + basisVector k) μ ≤ m := by
    intro μ hμ
    have := hh' μ
    rwa [if_neg hμ, add_zero] at this
  have hu : ∀ μ, (a + basisVector k) μ = a μ + if μ = k then 1 else 0 := by
    intro μ
    simp [basisVector, Pi.single_apply]
  by_cases h1 : a b.2 ≤ m
  · by_cases h2 : (a + basisVector k) b.2 ≤ m
    · have c1 : a ∈ centredCube F.blockSide := (hcube a).2 fun μ => by
        by_cases hμ : μ = b.2
        · subst hμ
          exact ⟨(hh _).1, h1⟩
        · exact hother μ hμ
      have c2 : a + Pi.single k 1 ∈ centredCube F.blockSide := (hcube _).2 fun μ => by
        by_cases hμ : μ = b.2
        · subst hμ
          exact ⟨(hh' _).1, h2⟩
        · exact hother' μ hμ
      exact (hB.1 a c1 k c2).1
    · have hk : k = b.2 := by
        by_contra hne
        apply h2
        rw [hu, if_neg (Ne.symm hne), add_zero]
        exact h1
      subst hk
      have c1 : a ∈ centredCube F.blockSide := (hcube a).2 fun μ => by
        by_cases hμ : μ = b.2
        · subst hμ
          exact ⟨(hh _).1, h1⟩
        · exact hother μ hμ
      have := hB.2 a c1 0 (Finset.mem_range.2 (by omega))
      simpa using this
  · have hs : (siteOfCoords j a : F.Site j) =
        siteOfCoords j (fun i => (F.blockSide : ℤ) * basisVector b.2 i) +
          siteOfCoords j (a - (F.blockSide : ℤ) • basisVector b.2) := by
      rw [← siteOfCoords_add]
      congr 1
      funext i
      simp
    have hd : refineSite (b.1 + unitStep (j + 1) b.2) =
        refineSite b.1 + siteOfCoords j (fun i => (F.blockSide : ℤ) * basisVector b.2 i) := by
      rw [unitStep_eq]
      exact refineSite_add j hj b.1 (basisVector b.2)
    set g : Lattice4 := a - (F.blockSide : ℤ) • basisVector b.2 with hg
    have hgv : ∀ μ, g μ = a μ - if μ = b.2 then (F.blockSide : ℤ) else 0 := by
      intro μ
      simp [hg, basisVector, Pi.single_apply]
    have c1 : g ∈ centredCube F.blockSide := (hcube g).2 fun μ => by
      rw [hgv]
      by_cases hμ : μ = b.2
      · rw [hμ, if_pos rfl]
        have h3 := (hh b.2).2
        rw [if_pos rfl] at h3
        constructor <;> omega
      · rw [if_neg hμ, sub_zero]
        exact hother μ hμ
    have c2 : g + Pi.single k 1 ∈ centredCube F.blockSide := (hcube _).2 fun μ => by
      have hv : (g + Pi.single k 1 : Lattice4) μ =
          (a + basisVector k) μ - if μ = b.2 then (F.blockSide : ℤ) else 0 := by
        rw [Pi.add_apply, hgv, Pi.add_apply]
        simp only [basisVector]
        ring
      rw [hv]
      by_cases hμ : μ = b.2
      · rw [hμ, if_pos rfl]
        have h3 := (hh' b.2).2
        rw [if_pos rfl] at h3
        have h4 : a b.2 ≤ (a + basisVector k) b.2 := by
          rw [hu]
          split_ifs <;> omega
        constructor <;> omega
      · rw [if_neg hμ, sub_zero]
        exact hother' μ hμ
    have := (hB.1 g c1 k c2).2
    rwa [hd, add_assoc, ← hs] at this
theorem norm_smul_sum_perm_le (hodd : Odd F.blockSide) (φ : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) (B : ℝ)
    (hB : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖φ h π‖ ≤ B) :
    ‖(1 / (24 * (F.blockSide : ℝ) ^ 4)) •
      ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), φ h π‖ ≤ B := by
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hcard : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
    rw [card_centredCube hodd]
    push_cast
    rfl
  have hperm : (Fintype.card (Equiv.Perm (Fin 4)) : ℝ) = 24 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  have h1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), φ h π‖ ≤
      (F.blockSide : ℝ) ^ 4 * (24 * B) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ h ∈ centredCube F.blockSide, ‖∑ π : Equiv.Perm (Fin 4), φ h π‖ ≤ 24 * B := by
      intro h hh
      refine (norm_sum_le _ _).trans ?_
      have := Finset.sum_le_sum (s := Finset.univ) fun π _ => hB h hh π
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hperm] at this
      exact this
    have h2 := Finset.sum_le_sum this
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at h2
    exact h2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) *
        ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), φ h π‖
      ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) * ((F.blockSide : ℝ) ^ 4 * (24 * B)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = B := by field_simp
theorem smul_sum_perm_const (hodd : Odd F.blockSide) (q : ℍ[ℝ]) :
    (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), q = q := by
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hcard : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
    rw [card_centredCube hodd]
    push_cast
    rfl
  have hperm : (Fintype.card (Equiv.Perm (Fin 4)) : ℝ) = 24 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul, hcard, hperm]
  have : 1 / (24 * (F.blockSide : ℝ) ^ 4) * (F.blockSide : ℝ) ^ 4 * 24 = 1 := by field_simp
  rw [this, one_smul]
theorem length_axisPath_le {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (π : Equiv.Perm (Fin 4)) :
    ((axisPath h π).length : ℝ) ≤ 2 * L := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.length_axisPath_le <;> assumption
theorem polarUnit_near_one {q : ℍ[ℝ]} {e : ℝ} (h : ‖q - 1‖ ≤ e) (he : e ≤ 1 / 4) :
    q ≠ 0 ∧ ‖((polarUnit q : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 3 * e := by
  have h1 : 3 / 4 ≤ ‖q‖ := by
    have := norm_sub_norm_le (1 : ℍ[ℝ]) q
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hq : q ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1
    linarith
  have hre : 3 / 4 ≤ q.re := by
    have h2 := quaternion_re_le_norm (1 - q)
    have h3 : (1 - q).re = 1 - q.re := by simp
    rw [h3, norm_sub_rev] at h2
    linarith
  have hp : ‖pureComponent q‖ ≤ e := by
    have : pureComponent q = pureComponent (q - 1) := by
      rw [pureComponent_sub, pureComponent_one, sub_zero]
    rw [this]
    exact (norm_pureComponent_le _).trans h
  refine ⟨hq, (norm_polarUnit_sub_one_le (by linarith) hq).trans ?_⟩
  have he0 : 0 ≤ e := (norm_nonneg _).trans h
  rw [div_le_iff₀ (by linarith)]
  nlinarith
theorem distFromOne_pathHolonomy_le (Y : F.GaugeField j) (x₀ : F.Site j) (p : Lattice4 → Prop) (t : ℝ)
    (ht0 : 0 ≤ t)
    (ht : ∀ u st, p u → p (u + FlatPairing.stepDisplacement st) →
      distFromOne (linkValue Y (x₀ + siteOfCoords j u) st) ≤ t) :
    ∀ (l : List PathStep) (u : Lattice4), AllAlong p u l →
      distFromOne (pathHolonomy Y (x₀ + siteOfCoords j u) l) ≤ l.length * t := by
  intro l
  induction l with
  | nil =>
    intro u _
    simp [pathHolonomy, distFromOne]
  | cons st r ih =>
    intro u hu
    have e : x₀ + siteOfCoords j u + BlockAverages.stepDisplacement j st =
        x₀ + siteOfCoords j (u + FlatPairing.stepDisplacement st) := by
      rw [stepDisplacement_eq_siteOfCoords, siteOfCoords_add, add_assoc]
    simp only [pathHolonomy]
    rw [e]
    have h1 := ht u st hu.1 (allAlong_head hu.2)
    have h2 := ih _ hu.2
    have h3 := norm_coe_mul_sub_one_le (linkValue Y (x₀ + siteOfCoords j u) st)
      (pathHolonomy Y (x₀ + siteOfCoords j (u + FlatPairing.stepDisplacement st)) r)
    have hl : (((st :: r).length : ℕ) : ℝ) * t = (r.length : ℝ) * t + t := by
      simp only [List.length_cons]
      push_cast
      ring
    rw [hl]
    unfold distFromOne at *
    linarith
theorem distFromOne_linkValue_le (Y : F.GaugeField j) (x₀ : F.Site j) (H : Set Lattice4) (t : ℝ)
    (hcl : ∀ a ∈ H, ∀ k, a + basisVector k ∈ H → distFromOne (Y (x₀ + siteOfCoords j a) k) ≤ t)
    (u : Lattice4) (st : PathStep) (hu : u ∈ H) (hv : u + FlatPairing.stepDisplacement st ∈ H) :
    distFromOne (linkValue Y (x₀ + siteOfCoords j u) st) ≤ t := by
  obtain ⟨k, b⟩ := st
  cases b with
  | true =>
    simp only [linkValue, if_true]
    exact hcl u hu k (by simpa [FlatPairing.stepDisplacement] using hv)
  | false =>
    have hv' : u - basisVector k ∈ H := by
      simpa [FlatPairing.stepDisplacement, sub_eq_add_neg] using hv
    have e : x₀ + siteOfCoords j u - unitStep j k = x₀ + siteOfCoords j (u - basisVector k) := by
      rw [unitStep_eq, siteOfCoords_sub, add_sub_assoc]
    simp only [linkValue, Bool.false_eq_true, if_false]
    rw [e]
    unfold distFromOne
    rw [norm_coe_inv_sub_one]
    exact hcl _ hv' k (by simpa using hu)
theorem allAlong_axisPath_twoBlockHull {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (hL : 1 ≤ L)
    (i : Fin 4) (π : Equiv.Perm (Fin 4)) :
    AllAlong (fun v => v ∈ twoBlockHull L i) 0 (axisPath h π) :=
  allAlong_mono (fun _ hv => mem_twoBlockHull_of_between hh hv hL) (axisPath_spec h π).1
theorem allAlong_axisPath_append_line {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (hL : 1 ≤ L)
    (i : Fin 4) (π : Equiv.Perm (Fin 4)) {r : ℕ} (hr : r ≤ L) :
    AllAlong (fun v => v ∈ twoBlockHull L i) 0 (axisPath h π ++ List.replicate r (i, true)) ∧
      endpoint 0 (axisPath h π ++ List.replicate r (i, true)) = h + (r : ℤ) • basisVector i := by
  have e0 := (axisPath_spec h π).2
  have hs : FlatPairing.stepDisplacement ((i, true) : PathStep) = basisVector i := by
    simp [FlatPairing.stepDisplacement]
  refine ⟨allAlong_append (allAlong_axisPath_twoBlockHull hh hL i π) ?_, ?_⟩
  · rw [e0]
    refine allAlong_replicate fun k hk => ?_
    rw [hs]
    exact add_smul_basisVector_mem_twoBlockHull hh i (hk.trans hr)
  · rw [endpoint_append, e0, endpoint_replicate, hs]
theorem length_axisPath_append_line_le {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (i : Fin 4)
    (π : Equiv.Perm (Fin 4)) {r : ℕ} (hr : r ≤ L) :
    ((axisPath h π ++ List.replicate r (i, true)).length : ℝ) ≤ 3 * L := by
  have h1 := length_axisPath_le hh π
  have h2 : (r : ℝ) ≤ L := by exact_mod_cast hr
  rw [List.length_append, List.length_replicate]
  push_cast
  linarith
theorem pathHolonomy_gaugeTransform_zero (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (x0 : F.Site j) (l : List PathStep) :
    pathHolonomy (gaugeTransform γ X) x0 l =
      γ x0 * pathHolonomy X x0 l * (γ (x0 + siteOfCoords j (endpoint 0 l)))⁻¹ := by apply _root_.YangMills.Construction.GaugeMotions.pathHolonomy_gaugeTransform_of_base <;> assumption
theorem allAlong_axisPath_centredCube {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L)
    (π : Equiv.Perm (Fin 4)) :
    AllAlong (fun v => v ∈ centredCube L) 0 (axisPath h π) := by
  refine allAlong_mono (fun v hv => ?_) (axisPath_spec h π).1
  rw [mem_centredCube_iff] at hh ⊢
  intro μ
  have h1 := hh μ
  have h2 := hv μ
  have hk : (0 : ℤ) ≤ ((L : ℤ) - 1) / 2 ∨ L = 0 := by omega
  rcases hk with hk | hk
  · have a1 : min 0 (h μ) ≥ -(((L : ℤ) - 1) / 2) := le_min (by omega) h1.1
    have a2 : max 0 (h μ) ≤ ((L : ℤ) - 1) / 2 := max_le hk h1.2
    constructor <;> omega
  · subst hk
    simp at h1
    omega
theorem norm_relativePathAverage_sub_one_le (hodd : Odd F.blockSide) (X R : F.GaugeField j)
    (y : F.Site (j + 1)) (t : ℝ) (ht0 : 0 ≤ t)
    (hcl : ∀ a ∈ centredCube F.blockSide, ∀ k, a + basisVector k ∈ centredCube F.blockSide →
      distFromOne (X (refineSite y + siteOfCoords j a) k * (R (refineSite y + siteOfCoords j a) k)⁻¹) ≤ t) :
    ‖relativePathAverage X R y - 1‖ ≤ 2 * F.blockSide * t := by
  have e : relativePathAverage X R y - 1 = (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
      ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      (((pathHolonomy X (refineSite y) (axisPath h π) *
        (pathHolonomy R (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) := by
    simp only [Finset.sum_sub_distrib, smul_sub]
    rw [smul_sum_perm_const hodd]
    rfl
  rw [e]
  refine norm_smul_sum_perm_le hodd _ _ fun h hh π => ?_
  have h1 := distFromOne_pathRatio_le X R (refineSite y) (fun v => v ∈ centredCube F.blockSide) t ht0
    (distFromOne_linkRatio_le X R (refineSite y) {v | v ∈ centredCube F.blockSide} t hcl)
    (axisPath h π) 0 (allAlong_axisPath_centredCube hh π)
  rw [siteOfCoords_zero, add_zero] at h1
  have h2 := length_axisPath_le hh π
  have h3 : ((axisPath h π).length : ℝ) * t ≤ 2 * F.blockSide * t := mul_le_mul_of_nonneg_right h2 ht0
  exact h1.trans h3
theorem distFromOne_balancingGauge_le (hodd : Odd F.blockSide) (X R : F.GaugeField j) (y : F.Site (j + 1))
    (t : ℝ) (ht0 : 0 ≤ t) (ht : 2 * F.blockSide * t ≤ 1 / 4)
    (hcl : ∀ a ∈ centredCube F.blockSide, ∀ k, a + basisVector k ∈ centredCube F.blockSide →
      distFromOne (X (refineSite y + siteOfCoords j a) k * (R (refineSite y + siteOfCoords j a) k)⁻¹) ≤ t) :
    distFromOne (balancingGauge X R y) ≤ 6 * F.blockSide * t := by
  have h1 := norm_relativePathAverage_sub_one_le hodd X R y t ht0 hcl
  obtain ⟨-, h2⟩ := polarUnit_near_one h1 ht
  unfold balancingGauge distFromOne
  rw [norm_coe_inv_sub_one]
  calc _ ≤ 3 * (2 * F.blockSide * t) := h2
    _ = 6 * F.blockSide * t := by ring
theorem contourAverage_near_one (hodd : Odd F.blockSide) (Y : F.GaugeField j) (c : F.Site (j + 1) × Fin 4)
    (τ : ℝ) (hτ : τ ≤ 1 / 4)
    (hc : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      distFromOne (pathHolonomy Y (refineSite c.1) (bondContour F.blockSide h π c.2)) ≤ τ) :
    contourAverage Y c ≠ 0 ∧ distFromOne (polarUnit (contourAverage Y c)) ≤ 3 * τ := by
  have e : contourAverage Y c - 1 = (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
      ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      (((pathHolonomy Y (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) - 1) := by
    simp only [Finset.sum_sub_distrib, smul_sub]
    rw [smul_sum_perm_const hodd]
    rfl
  have h1 : ‖contourAverage Y c - 1‖ ≤ τ := by
    rw [e]
    exact norm_smul_sum_perm_le hodd _ _ hc
  exact polarUnit_near_one h1 hτ
theorem distFromOne_mul_le (a b : UnitQuaternion) : distFromOne (a * b) ≤ distFromOne a + distFromOne b := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
theorem distFromOne_conj (a b : UnitQuaternion) : distFromOne (a * b * a⁻¹) = distFromOne b := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem distFromOne_inv (a : UnitQuaternion) : distFromOne a⁻¹ = distFromOne a := norm_coe_inv_sub_one a
theorem distFromOne_nonneg (a : UnitQuaternion) : 0 ≤ distFromOne a := norm_nonneg _
end BondHull
end YangMills.Construction
end
