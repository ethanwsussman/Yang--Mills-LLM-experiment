import YangMills.Construction.ColdChainAtEveryLevel.CellsOfAPatch
import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainIsLeast
import YangMills.Construction.ColdChainAtEveryLevel.CriticalValueIsTheLeastAction
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMotionsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.ShareOfAMinimalChainIsItsEvaluation
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace MinimalChainShare
open ChartCoordinates LatticePaths LatticeFractionalIntegration FlatPairing
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem baseSite_of_level_zero (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem re_unit_conj (g : UnitQuaternion) (q : ℍ[ℝ]) :
    ((g : ℍ[ℝ]) * q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = q.re := by apply _root_.YangMills.Construction.GaugedCriticality.re_conj_unit <;> assumption
def patchSitesAtLevel (S : Finset F.Cell) (z : F.Cell) (j : ℕ) : Set (F.Site j) :=
  {x | x ∈ sitesOfCells S j ∧ baseSite x ∈ patchBaseSites S z}
section Gauging
variable {a C : ℝ} {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain} {k Γ : F.SiteGauge}
theorem gaugedChainFields_eq (hP : IsPinnedGauge a C S z W kW X k Γ) (hE : relativeEnergy a S z W kW X k Γ = 0)
    {j : ℕ} (hj : j < F.top) {x : F.Site j} {i : Fin 4} (h1 : x ∈ patchSitesAtLevel S z j)
    (h2 : x + unitStep j i ∈ patchSitesAtLevel S z j) : gaugedChainFields X Γ j x i = W j x i := by
  classical
  have hs := hP.2.2.1 j hj
  rw [hE, Real.sqrt_zero, mul_zero] at hs
  have hzero : (0 : ℝ) ^ 4 = 0 := by norm_num
  rw [hzero] at hs
  have hnn : ∀ b ∈ innerBonds S j, 0 ≤ (if baseSite b.1 ∈ patchBaseSites S z ∧
      baseSite (b.1 + unitStep j b.2) ∈ patchBaseSites S z then
      ‖((gaugedChainFields X Γ j b.1 b.2 * (W j b.1 b.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 else 0) := by
    intro b _
    split_ifs <;> positivity
  have hb : (x, i) ∈ innerBonds S j := mem_innerBonds h1.1 h2.1
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hs (Finset.sum_nonneg hnn)) (x, i) hb
  simp only at h3
  rw [if_pos ⟨h1.2, h2.2⟩] at h3
  have h4 : ‖((gaugedChainFields X Γ j x i * (W j x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = 0 := by
    simpa using h3
  have h5 : ((gaugedChainFields X Γ j x i * (W j x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 :=
    sub_eq_zero.1 (norm_eq_zero.1 h4)
  have h6 : gaugedChainFields X Γ j x i * (W j x i)⁻¹ = 1 := Subtype.ext h5
  exact mul_inv_eq_one.1 h6
theorem allAlong_plaquette {Q : Set (F.Site 0)} {p : F.Site 0 × Fin 4 × Fin 4}
    (hc : ∀ x ∈ plaquetteCorners p, x ∈ Q) :
    AllAlong (fun v => p.1 + siteOfCoords 0 v ∈ Q) 0
      [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] := by
  have c1 := hc p.1 (by simp [plaquetteCorners])
  have c2 := hc (p.1 + unitStep 0 p.2.1) (by simp [plaquetteCorners])
  have c3 := hc (p.1 + unitStep 0 p.2.2) (by simp [plaquetteCorners])
  have c4 := hc (p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2) (by simp [plaquetteCorners])
  simp only [AllAlong]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert c1 using 1
    simp [_root_.YangMills.Construction.BlockAverages.siteOfCoords_zero]
  · convert c2 using 1
    simp [FlatPairing.stepDisplacement, unitStep_eq]
  · convert c4 using 1
    simp [FlatPairing.stepDisplacement, siteOfCoords_add, unitStep_eq]
    abel
  · convert c3 using 1
    simp [FlatPairing.stepDisplacement, unitStep_eq]
  · convert c1 using 1
    have h : (0 : Lattice4) + FlatPairing.stepDisplacement (p.2.1, true) + FlatPairing.stepDisplacement (p.2.2, true) +
        FlatPairing.stepDisplacement (p.2.1, false) + FlatPairing.stepDisplacement (p.2.2, false) = 0 := by
      simp only [FlatPairing.stepDisplacement, ↓reduceIte, Bool.false_eq_true]
      abel
    rw [h, add_siteOfCoords_zero]
theorem plaquetteHolonomy_re_eq (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide)
    (hP : IsPinnedGauge a C S z W kW X k Γ) (hE : relativeEnergy a S z W kW X k Γ = 0)
    {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ patchPlaquettes S z) :
    ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re =
      ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).re := by
  classical
  have hp' := Finset.mem_filter.1 hp
  have hcS := (Finset.mem_filter.1 hp'.1).2.2
  have hc : ∀ x ∈ plaquetteCorners p, x ∈ patchSitesAtLevel S z 0 := fun x hx =>
    ⟨hcS hx, by rw [baseSite_of_level_zero]; exact hp'.2 hx⟩
  have h0 : 0 < F.top := Nat.succ_pos _
  have e := pathHolonomy_congr (D := patchSitesAtLevel S z 0) (X := gaugedChainFields X Γ 0) (X' := W 0)
    (fun x i h1 h2 => gaugedChainFields_eq hP hE h0 h1 h2) p.1 _ 0 (allAlong_plaquette hc)
  rw [add_siteOfCoords_zero] at e
  have hcov := (hG F 0 h0 hL).2.2.1 (Γ 0) (X 0) p
  have e' : plaquetteHolonomy (W 0) p = Γ 0 p.1 * plaquetteHolonomy (X 0) p * (Γ 0 p.1)⁻¹ := by
    rw [← hcov]
    exact e.symm
  rw [e']
  exact (re_unit_conj (Γ 0 p.1) _).symm
end Gauging
section Fits
variable {a C : ℝ} {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain} {Γ : F.SiteGauge}
theorem scaled_mem_centredCube_pow {L : ℕ} (hodd : Odd L) (j : ℕ) {a : Lattice4} (ha : a ∈ centredCube L) :
    (fun i => (L : ℤ) ^ j * a i) ∈ centredCube (L ^ (j + 1)) := by
  have hpos : (0 : ℤ) < L := by exact_mod_cast hodd.pos
  obtain ⟨B, hB⟩ : ∃ B : ℤ, (L : ℤ) = 2 * B + 1 := by
    obtain ⟨B, hB⟩ := hodd
    exact ⟨B, by rw [hB]; push_cast; ring⟩
  obtain ⟨A, hA⟩ : ∃ A : ℤ, ((L ^ j : ℕ) : ℤ) = 2 * A + 1 := by
    obtain ⟨A, hA⟩ := hodd.pow (n := j)
    exact ⟨A, by rw [hA]; push_cast; ring⟩
  have hA' : (L : ℤ) ^ j = 2 * A + 1 := by rw [← hA]; push_cast; ring
  have hA0 : 0 ≤ A := by
    have : (0 : ℤ) < (L : ℤ) ^ j := by positivity
    omega
  have eB : ((L : ℤ) - 1) / 2 = B := by rw [hB]; omega
  have eAB : (((L ^ (j + 1) : ℕ) : ℤ) - 1) / 2 = 2 * A * B + A + B := by
    have e1 : ((L ^ (j + 1) : ℕ) : ℤ) = (2 * A + 1) * (2 * B + 1) := by
      rw [pow_succ]; push_cast; rw [hA', hB]
    have e2 : (2 * A + 1) * (2 * B + 1) - 1 = 2 * (2 * A * B + A + B) := by ring
    rw [e1, e2]; simp
  rw [_root_.YangMills.Construction.LatticePaths.mem_centredCube_iff] at ha ⊢
  intro i
  have h2 := ha i
  rw [eB] at h2
  rw [eAB, hA']
  constructor <;> nlinarith [h2.1, h2.2]
theorem refineSite_add_mem_patchSitesAtLevel (hodd : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {y : F.Site (j + 1)} (hy : y ∈ sitesOfCells S (j + 1))
    (hb : ∀ h ∈ centredCube (F.blockSide ^ (j + 1)), baseSite y + siteOfCoords 0 h ∈ patchBaseSites S z)
    {a : Lattice4} (ha : a ∈ centredCube F.blockSide) :
    refineSite y + siteOfCoords j a ∈ patchSitesAtLevel S z j := by
  refine ⟨refineSite_add_mem_sitesOfCells hodd hj hy ha, ?_⟩
  rw [baseSite_add j (by omega), baseSite_refineSite j hj]
  exact hb _ (scaled_mem_centredCube_pow hodd j ha)
theorem allAlong_axisPath_patch (hodd : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top) {y : F.Site (j + 1)}
    (hy : y ∈ sitesOfCells S (j + 1))
    (hb : ∀ h ∈ centredCube (F.blockSide ^ (j + 1)), baseSite y + siteOfCoords 0 h ∈ patchBaseSites S z)
    {h : Lattice4} (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    AllAlong (fun v => refineSite y + siteOfCoords j v ∈ patchSitesAtLevel S z j) 0 (axisPath h π) := by
  refine allAlong_mono (fun v hv => ?_) (axisPath_spec h π).1
  refine refineSite_add_mem_patchSitesAtLevel hodd hj hy hb ((_root_.YangMills.Construction.LatticePaths.mem_centredCube_iff _ _).2 fun μ => ?_)
  have h1 := ((_root_.YangMills.Construction.LatticePaths.mem_centredCube_iff _ _).1 hh) μ
  have h2 := hv μ
  have a1 : min 0 (h μ) ≥ -(((F.blockSide : ℤ) - 1) / 2) := le_min (by omega) h1.1
  have a2 : max 0 (h μ) ≤ ((F.blockSide : ℤ) - 1) / 2 := max_le (by omega) h1.2
  omega
theorem twoBlockHull_mem_patchSitesAtLevel (hodd : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds S (j + 1))
    (hb : ∀ h ∈ centredCube (F.blockSide ^ (j + 1)),
      baseSite c.1 + siteOfCoords 0 h ∈ patchBaseSites S z ∧
        baseSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords 0 h ∈ patchBaseSites S z)
    {a : Lattice4} (ha : a ∈ twoBlockHull F.blockSide c.2) :
    refineSite c.1 + siteOfCoords j a ∈ patchSitesAtLevel S z j := by
  by_cases hcase : a c.2 ≤ ((F.blockSide : ℤ) - 1) / 2
  · refine refineSite_add_mem_patchSitesAtLevel hodd hj (innerBonds_ends hc).1 (fun h hh => (hb h hh).1)
      ((mem_centredCube_iff _ _).2 fun μ => ?_)
    have := ha μ
    by_cases hμ : μ = c.2
    · subst hμ
      simp only [if_true] at this
      exact ⟨this.1, hcase⟩
    · simpa [hμ] using this
  · have e : refineSite c.1 + siteOfCoords j a =
        refineSite (c.1 + unitStep (j + 1) c.2) + siteOfCoords j (a - (F.blockSide : ℤ) • basisVector c.2) := by
      rw [unitStep_eq, refineSite_add j hj, add_assoc, ← siteOfCoords_add]
      congr 2
      funext μ
      simp [basisVector]
    rw [e]
    refine refineSite_add_mem_patchSitesAtLevel hodd hj (innerBonds_ends hc).2 (fun h hh => (hb h hh).2)
      ((mem_centredCube_iff _ _).2 fun μ => ?_)
    have := ha μ
    obtain ⟨m, hm⟩ := hodd
    have hL : ((F.blockSide : ℤ) - 1) / 2 = m := by rw [hm]; push_cast; omega
    have hL2 : (F.blockSide : ℤ) = 2 * m + 1 := by rw [hm]; push_cast; ring
    rw [hL] at this hcase ⊢
    by_cases hμ : μ = c.2
    · subst hμ
      simp only [if_true] at this
      simp [basisVector]
      constructor <;> omega
    · simp only [hμ, if_false] at this
      simp [basisVector, hμ]
      simpa using this
theorem balancingGauge_eq_one (hodd : Odd F.blockSide) {j : ℕ} {G R : F.GaugeField j} {y : F.Site (j + 1)}
    (h : ∀ a ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      pathHolonomy G (refineSite y) (axisPath a π) = pathHolonomy R (refineSite y) (axisPath a π)) :
    balancingGauge G R y = 1 := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hcard : 0 < (centredCube F.blockSide).card := by
    refine Finset.card_pos.2 ⟨0, (_root_.YangMills.Construction.LatticePaths.mem_centredCube_iff _ _).2 fun i => ?_⟩
    have : (0 : ℤ) ≤ ((F.blockSide : ℤ) - 1) / 2 := by
      have : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hodd.pos
      omega
    simpa using this
  have e : relativePathAverage G R y = (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
      (((centredCube F.blockSide).card : ℝ) • ((24 : ℝ) • (1 : ℍ[ℝ]))) := by
    unfold relativePathAverage
    have e1 : ∀ a ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy G (refineSite y) (axisPath a π) *
          (pathHolonomy R (refineSite y) (axisPath a π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
          (24 : ℝ) • (1 : ℍ[ℝ]) := by
      intro a ha
      have : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin 4))),
          ((pathHolonomy G (refineSite y) (axisPath a π) *
            (pathHolonomy R (refineSite y) (axisPath a π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
        intro π _
        rw [h a ha π, mul_inv_cancel]
        rfl
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℝ]
      norm_num [Nat.factorial]
    rw [Finset.sum_congr rfl e1, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  have e2 : ∀ r : ℝ, r • (1 : ℍ[ℝ]) = (r : ℍ[ℝ]) := fun r => by
    ext <;> simp
  unfold balancingGauge
  rw [e, smul_smul, smul_smul, e2, polarUnit_coe (by positivity), inv_one]
theorem blockFit_conj (A B : UnitQuaternion) (m : ℍ[ℝ]) (g : UnitQuaternion) :
    ‖(A : ℍ[ℝ]) * m * ((B⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ - ((A : ℍ[ℝ]) * m * ((B⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
      (((A * g * B⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
      ‖m‖ - (m * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by apply _root_.YangMills.Construction.GaugeMotions.norm_sub_re_conj <;> assumption
theorem gaugedAverage_conj (A B P Q : UnitQuaternion) (m : ℍ[ℝ]) :
    ((A * P⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((P : ℍ[ℝ]) * m * ((Q⁻¹ : UnitQuaternion) : ℍ[ℝ])) *
      (((B * Q⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (A : ℍ[ℝ]) * m * ((B⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  have e : (B * Q⁻¹)⁻¹ = Q * B⁻¹ := by group
  rw [e]
  simp only [Submonoid.coe_mul]
  have hP : ((P⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (P : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl
  have hQ : ((Q⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (Q : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl
  calc (A : ℍ[ℝ]) * ((P⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((P : ℍ[ℝ]) * m * ((Q⁻¹ : UnitQuaternion) : ℍ[ℝ])) *
        ((Q : ℍ[ℝ]) * ((B⁻¹ : UnitQuaternion) : ℍ[ℝ]))
      = (A : ℍ[ℝ]) * (((P⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (P : ℍ[ℝ])) * m *
          (((Q⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (Q : ℍ[ℝ])) * ((B⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
        simp only [mul_assoc]
    _ = _ := by
        rw [hP, hQ]
        simp only [mul_one]
theorem zero_mem_centredCube {L : ℕ} (hodd : Odd L) : (0 : Lattice4) ∈ centredCube L := by apply _root_.YangMills.Construction.BlockAverages.zero_mem_centredCube <;> assumption
variable (hodd : Odd F.blockSide) (hP : IsPinnedGauge a C S z W kW X (fun _ _ => 1) Γ)
  (hE : relativeEnergy a S z W kW X (fun _ _ => 1) Γ = 0)
include hP hE
include hodd in
theorem chartGauge_eq_of_pinned {j : ℕ} (hj : j < F.top) {y : F.Site (j + 1)} (hy : y ∈ sitesOfCells S (j + 1))
    (hb : ∀ h ∈ centredCube (F.blockSide ^ (j + 1)), baseSite y + siteOfCoords 0 h ∈ patchBaseSites S z) :
    kW (j + 1) y = Γ (j + 1) y * (Γ j (refineSite y))⁻¹ := by
  have hj' : j + 1 ≤ F.top := hj
  have hbal : balancingGauge (gaugedChainFields X Γ j) (W j) y = 1 := by
    refine balancingGauge_eq_one hodd fun a' ha π => ?_
    have := pathHolonomy_congr (D := patchSitesAtLevel S z j) (X := gaugedChainFields X Γ j) (X' := W j)
      (fun x i h1 h2 => gaugedChainFields_eq hP hE hj h1 h2) (refineSite y) _ 0
      (allAlong_axisPath_patch hodd hj' hy hb ha π)
    rwa [add_siteOfCoords_zero] at this
  have hy0 : baseSite y ∈ patchBaseSites S z := by
    have := hb 0 (zero_mem_centredCube (hodd.pow))
    rwa [siteOfCoords_zero, add_zero] at this
  by_cases hjt : j + 1 < F.top
  · have h1 := hP.2.1 j hjt y hy0
    simp only [gaugedLink, balancedLinkAgainst, hbal, mul_one] at h1
    exact h1.symm
  · obtain rfl : j = F.depth := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    have h1 := hP.2.2.2 y hy0
    rw [hE, Real.sqrt_zero, mul_zero] at h1
    have h2 : topCorrection W kW X (fun _ _ => 1) Γ y = 1 :=
      Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm h1 (norm_nonneg _))))
    simp only [topCorrection, balancedLinkAgainst, gaugedLink, hbal, mul_one] at h2
    exact mul_inv_eq_one.1 h2
theorem upperField_eq (hW : W F.top = X F.top) {j : ℕ} (hj : j < F.top) {x : F.Site (j + 1)} {i : Fin 4}
    (h1 : x ∈ patchSitesAtLevel S z (j + 1)) (h2 : x + unitStep (j + 1) i ∈ patchSitesAtLevel S z (j + 1)) :
    W (j + 1) x i = Γ (j + 1) x * X (j + 1) x i * (Γ (j + 1) (x + unitStep (j + 1) i))⁻¹ := by
  by_cases hjt : j + 1 < F.top
  · exact (gaugedChainFields_eq hP hE hjt h1 h2).symm
  · obtain rfl : j = F.depth := by
      have hn : F.top = F.depth + 1 := rfl
      omega
    have hΓ := hP.1
    show W F.top x i = Γ F.top x * X F.top x i * (Γ F.top (x + unitStep F.top i))⁻¹
    rw [hW, hΓ, hΓ]
    simp
include hodd in
theorem blockFit_eq_gaugedBlockFit (hG : gaugeCovarianceStatement) (hW : W F.top = X F.top) {j : ℕ}
    (hj : j < F.top) {c : F.Site (j + 1) × Fin 4} (hc : c ∈ patchFitBonds S z j) :
    blockFit (X j) (X (j + 1)) c = gaugedBlockFit (W j) (kW (j + 1)) (W (j + 1)) c := by
  classical
  have hj' : j + 1 ≤ F.top := hj
  have hcb := (Finset.mem_filter.1 hc).1
  have hb := (Finset.mem_filter.1 hc).2
  have hends := innerBonds_ends hcb
  have hL : 0 < F.blockSide := hodd.pos
  have e1 : _root_.YangMills.Construction.BlockAverages.contourAverage (W j) c = _root_.YangMills.Construction.BlockAverages.contourAverage (gaugedChainFields X Γ j) c := by
    unfold _root_.YangMills.Construction.BlockAverages.contourAverage
    congr 1
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
    have := pathHolonomy_congr (D := patchSitesAtLevel S z j) (X := gaugedChainFields X Γ j) (X' := W j)
      (fun x i h1 h2 => gaugedChainFields_eq hP hE hj h1 h2) (refineSite c.1) _ 0
      (allAlong_mono (fun _ hv => twoBlockHull_mem_patchSitesAtLevel hodd hj' hcb hb hv)
        (bondContour_spec π c.2 hodd.pos hh).1)
    rw [add_siteOfCoords_zero] at this
    rw [this]
  have e2 := (hG F j hj hL).2.1 (Γ j) (X j) c
  have k1 := chartGauge_eq_of_pinned hodd hP hE hj hends.1 fun h hh => (hb h hh).1
  have k2 := chartGauge_eq_of_pinned hodd hP hE hj hends.2 fun h hh => (hb h hh).2
  have p1 : c.1 ∈ patchSitesAtLevel S z (j + 1) := by
    refine ⟨hends.1, ?_⟩
    have := (hb 0 (zero_mem_centredCube hodd.pow)).1
    rwa [siteOfCoords_zero, add_zero] at this
  have p2 : c.1 + unitStep (j + 1) c.2 ∈ patchSitesAtLevel S z (j + 1) := by
    refine ⟨hends.2, ?_⟩
    have := (hb 0 (zero_mem_centredCube hodd.pow)).2
    rwa [siteOfCoords_zero, add_zero] at this
  have u1 := upperField_eq hP hE hW hj p1 p2
  have hm : gaugedContourAverage (W j) (kW (j + 1)) c = (Γ (j + 1) c.1 : ℍ[ℝ]) * _root_.YangMills.Construction.BlockAverages.contourAverage (X j) c *
      (((Γ (j + 1) (c.1 + unitStep (j + 1) c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    unfold gaugedContourAverage
    rw [e1, k1, k2]
    show _ * _root_.YangMills.Construction.BlockAverages.contourAverage (gaugeTransform (Γ j) (X j)) c * _ = _
    rw [e2]
    exact gaugedAverage_conj _ _ _ _ _
  unfold gaugedBlockFit blockFit
  rw [hm, u1]
  exact (blockFit_conj _ _ _ _).symm
end Fits
end MinimalChainShare
theorem minimalChainShareEqAverage (hT : criticalChainMinimalityStatement)
    (hVal : criticalValueEqMinimalActionStatement) (hV : minimalChainExistenceStatement)
    (hF : gaugedChainLowerBoundStatement) (hG : gaugeCovarianceStatement) :
    minimalChainShareEqAverageStatement := by
  classical
  intro a θ δ Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₀, h⟩ := hT a θ δ Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₁, hv⟩ := hVal a θ δ Ca ha hθ hθ8 hd hd8 hCa
  refine ⟨max L₀ L₁, fun L hL hge C₁ hC₁ => ?_⟩
  obtain ⟨e0, σ, C, c, he0, hσ, hC, hc, h'⟩ := h L hL (le_of_max_le_left hge) C₁ hC₁
  obtain ⟨σ', hσ', hv'⟩ := hv L hL (le_of_max_le_right hge) C₁ hC₁
  refine ⟨min σ σ', lt_min hσ hσ', ?_⟩
  intro F m S hFL hamb hm hreg s V v hs hsσ hcold hvs U hU X hX Y
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hLpos : 0 < F.blockSide := hodd.pos
  have hleast := (hv' F m S hFL hamb hm hreg s V v hs (hsσ.trans (min_le_right _ _)) hcold hvs U hU).1
  set W := chartChain (referenceFieldChain S V) U (rotatedField v V) with hWdef
  set kW := chartGauge (referenceFieldChain S V) U with hkW
  have hWtop : W F.top = X F.top := by
    rw [hX.1, hWdef]
    unfold chartChain
    exact Function.update_self _ _ _
  obtain ⟨X₀, hmin, htot⟩ := (hV F a S ha.le).2.2.2 (rotatedField v V)
  have t1 : chainAction a S X ≤ chainAction a S X₀ := hX.2 X₀ hmin.1
  have t2 := (hF F a S ha.le hLpos).1 X (fun _ _ => 1)
  rw [hX.1, (hF F a S ha.le hLpos).2 X] at t2
  have t3 : gaugedChainAction a S X (fun _ _ => 1) =
      chartAction a S (referenceFieldChain S V) U (rotatedField v V) := by
    rw [(hF F a S ha.le hLpos).2 X, ← hleast]
    linarith
  obtain ⟨Γ, hpin, hexc⟩ := h' F m S hFL hamb hm hreg s V v hs (hsσ.trans (min_le_left _ _)) hcold hvs U hU X
    (fun _ _ => 1) hX.1
  rw [t3, sub_self] at hexc
  have hrel : ∀ z, 0 ≤ relativeEnergy a S z W kW X (fun _ _ => 1) (Γ z) := fun z => by
    unfold relativeEnergy
    refine add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (mul_nonneg ha.le ?_)
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : (((highEnergyCells a e0 S X (fun _ _ => 1)).card : ℝ) +
      ∑ z ∈ cellsFarFromHighEnergy a e0 S X (fun _ _ => 1),
      relativeEnergy a S z W kW X (fun _ _ => 1) (Γ z)) ≤ 0 := by
    by_contra hcon
    have := mul_pos hc (not_le.1 hcon)
    linarith
  have hs0 : 0 ≤ ∑ z ∈ cellsFarFromHighEnergy a e0 S X (fun _ _ => 1),
      relativeEnergy a S z W kW X (fun _ _ => 1) (Γ z) :=
    Finset.sum_nonneg fun z _ => hrel z
  have hcard : (highEnergyCells a e0 S X (fun _ _ => 1)).card = 0 := by
    have : ((highEnergyCells a e0 S X (fun _ _ => 1)).card : ℝ) ≤ 0 := by linarith
    exact_mod_cast le_antisymm this (by positivity)
  have hbad : highEnergyCells a e0 S X (fun _ _ => 1) = ∅ := Finset.card_eq_zero.1 hcard
  have hfar : ∀ z ∈ S, z ∈ cellsFarFromHighEnergy a e0 S X (fun _ _ => 1) := fun z hz =>
    Finset.mem_filter.2 ⟨hz, fun y hy => by rw [hbad] at hy; simp at hy⟩
  have hzero : ∀ z ∈ S, relativeEnergy a S z W kW X (fun _ _ => 1) (Γ z) = 0 := by
    intro z hz
    have h1 : ∑ z ∈ cellsFarFromHighEnergy a e0 S X (fun _ _ => 1),
        relativeEnergy a S z W kW X (fun _ _ => 1) (Γ z) = 0 := by
      have : ((highEnergyCells a e0 S X (fun _ _ => 1)).card : ℝ) = 0 := by exact_mod_cast hcard
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hrel z).1 h1 z (hfar z hz)
  have hterm : ∀ t ∈ actionTerms S, ∃ z ∈ S, t ∈ patchActionTerms S z := by
    intro t ht
    obtain ⟨hz, h₁, hh, e⟩ := PatchLocality.enclosingCell_actionTermSite hodd ht
    obtain ⟨he, -⟩ := closedOrthant_spec (S := S) hreg (by omega) (enclosingCell (actionTermSite t))
    refine ⟨_, hz, PatchLocality.mem_patchActionTerms_of_cellCutoff_ne_zero hamb hodd he ht ?_⟩
    have := cellCutoff_self hamb hodd (enclosingCell (actionTermSite t)) hh
    rw [← e] at this
    rw [this]
    norm_num
  unfold cellShare localCellShare gaugedCellShare
  congr 1
  · refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨z, hz, hzp⟩ := hterm (Sum.inl p) (Finset.inl_mem_disjSum.2 hp)
    rw [MinimalChainShare.plaquetteHolonomy_re_eq hG hLpos (hpin z (hfar z hz)) (hzero z hz)
      (Finset.inl_mem_disjSum.1 hzp)]
  · congr 1
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c₁ hc₁ => ?_
    obtain ⟨z, hz, hzp⟩ := hterm (Sum.inr ⟨j, c₁⟩) (Finset.inr_mem_disjSum.2 (Finset.mem_sigma.2 ⟨hj, hc₁⟩))
    rw [MinimalChainShare.blockFit_eq_gaugedBlockFit hodd (hpin z (hfar z hz)) (hzero z hz) hG hWtop
      (Finset.mem_range.1 hj) (Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 hzp)).2]
end YangMills.Construction.BlockAverages
end
