import YangMills.Construction.ColdChainAtEveryLevel.GapsOfAFramingOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.MisfitsOfAFraming
import YangMills.Construction.ColdChainAtEveryLevel.MorreyOfTheCriticalChainOnAPatchProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsBetweenTheCellsOfAPatch
import YangMills.Construction.ColdChainAtEveryLevel.QuarticGaugeOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.SizesAtAGoodCell
import YangMills.Construction.ColdChainAtEveryLevel.StartOfAFramingOnAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace PinnedGaugeStart
variable {F : BlockFrame} {j : ℕ}
theorem sum_le_of_sum_pow_four_le {ι : Type} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) {M c : ℝ} (hM : 0 ≤ M)
    (hc : 0 ≤ c) (hcard : (s.card : ℝ) ≤ M ^ 4) (h4 : ∑ i ∈ s, f i ^ 4 ≤ c ^ 4) : ∑ i ∈ s, f i ≤ M ^ 3 * c := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]
    positivity
  have hcp : (0 : ℝ) < s.card := by exact_mod_cast hne.card_pos
  have h1 := pow_sum_div_card_le_sum_pow (s := s) (f := f) (fun i _ => hf i) 3
  rw [div_le_iff₀ (by positivity)] at h1
  have h2 : (∑ i ∈ s, f i) ^ 4 ≤ (M ^ 3 * c) ^ 4 := by
    calc (∑ i ∈ s, f i) ^ 4 ≤ (∑ i ∈ s, f i ^ (3 + 1)) * (s.card : ℝ) ^ 3 := h1
      _ ≤ c ^ 4 * (M ^ 4) ^ 3 := by
          refine mul_le_mul h4 (pow_le_pow_left₀ hcp.le hcard 3) (by positivity) (by positivity)
      _ = (M ^ 3 * c) ^ 4 := by ring
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h2
theorem distFromOne_conjSides_le (u g v κ : UnitQuaternion) :
    _root_.YangMills.Construction.BlockAverages.distFromOne (u * g * v * κ⁻¹) ≤ _root_.YangMills.Construction.BlockAverages.distFromOne (g * κ⁻¹) + _root_.YangMills.Construction.BlockAverages.distFromOne u + _root_.YangMills.Construction.BlockAverages.distFromOne v := by
  have e : u * g * v * κ⁻¹ = u * (g * κ⁻¹) * (κ * v * κ⁻¹) := by group
  rw [e]
  have h1 := BondHull.distFromOne_mul_le (u * (g * κ⁻¹)) (κ * v * κ⁻¹)
  have h2 := BondHull.distFromOne_mul_le u (g * κ⁻¹)
  rw [BondHull.distFromOne_conj] at h1
  linarith
theorem distFromOne_sub_le (a b : UnitQuaternion) : _root_.YangMills.Construction.BlockAverages.distFromOne a - _root_.YangMills.Construction.BlockAverages.distFromOne b ≤ _root_.YangMills.Construction.BlockAverages.distFromOne (a * b⁻¹) := by
  have e : a = (a * b⁻¹) * b := by group
  have h := BondHull.distFromOne_mul_le (a * b⁻¹) b
  rw [← e] at h
  linarith
theorem gaugeTransform_gaugeTransform {j : ℕ} (g g' : F.Site j → UnitQuaternion) (X : F.GaugeField j) :
    gaugeTransform (fun x => g' x * (g x)⁻¹) (gaugeTransform g X) = gaugeTransform g' X := by
  funext x i
  simp only [gaugeTransform]
  group
theorem distFromOne_gaugeChange_le (hodd : Odd F.blockSide) (T R : F.GaugeField j) (δ : F.Site j → UnitQuaternion)
    (kl fy fx κ : UnitQuaternion) (y : F.Site (j + 1)) {h : LatticeFractionalIntegration.Lattice4}
    (hh : h ∈ centredCube F.blockSide) (t t' E : ℝ) (ht0 : 0 ≤ t) (ht'0 : 0 ≤ t') (hE0 : 0 ≤ E)
    (hsm : 2 * (F.blockSide : ℝ) * t ≤ 1 / 4) (hsm' : 2 * (F.blockSide : ℝ) * t' ≤ 1 / 4)
    (hT : ∀ a ∈ centredCube F.blockSide, ∀ k, a + LatticeFractionalIntegration.basisVector k ∈ centredCube F.blockSide →
      _root_.YangMills.Construction.BlockAverages.distFromOne (T (refineSite y + siteOfCoords j a) k * (R (refineSite y + siteOfCoords j a) k)⁻¹) ≤ t)
    (hT' : ∀ a ∈ centredCube F.blockSide, ∀ k, a + LatticeFractionalIntegration.basisVector k ∈ centredCube F.blockSide →
      _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform δ T (refineSite y + siteOfCoords j a) k *
        (R (refineSite y + siteOfCoords j a) k)⁻¹) ≤ t')
    (hk : _root_.YangMills.Construction.BlockAverages.distFromOne kl ≤ E)
    (hleg : _root_.YangMills.Construction.BlockAverages.distFromOne (fy⁻¹ * pathHolonomy R (refineSite y) (axisPath h 1) * fx) ≤ E) :
    _root_.YangMills.Construction.BlockAverages.distFromOne (fy⁻¹ * (kl * balancingGauge (gaugeTransform δ T) R y * δ (refineSite y) *
        (kl * balancingGauge T R y)⁻¹) * fy * κ⁻¹) ≤
      _root_.YangMills.Construction.BlockAverages.distFromOne (fx⁻¹ * δ (refineSite y + siteOfCoords j h) * fx * κ⁻¹) + 4 * E +
        8 * (F.blockSide : ℝ) * (t + t') := by
  set bal := balancingGauge T R y with hbal
  set bal' := balancingGauge (gaugeTransform δ T) R y with hbal'
  set l := axisPath h (1 : Equiv.Perm (Fin 4)) with hl
  set dy := refineSite y with hdy
  set x := dy + siteOfCoords j h with hx
  set Hw := pathHolonomy R dy l with hHw
  set Ht := pathHolonomy T dy l with hHt
  have hgt : pathHolonomy (gaugeTransform δ T) dy l = δ dy * Ht * (δ x)⁻¹ := by
    have := BondHull.pathHolonomy_gaugeTransform_zero δ T dy l
    rwa [(LatticePaths.axisPath_spec h 1).2] at this
  have hs1 := BondHull.distFromOne_balancingGauge_le hodd T R y t ht0 hsm hT
  have hs2 := BondHull.distFromOne_balancingGauge_le hodd (gaugeTransform δ T) R y t' ht'0 hsm' hT'
  have hp1 : _root_.YangMills.Construction.BlockAverages.distFromOne (BondHull.pathRatio T R dy l) ≤ 2 * F.blockSide * t := by
    have h1 := BondHull.distFromOne_pathRatio_le T R dy (fun v => v ∈ centredCube F.blockSide) t ht0
      (BondHull.distFromOne_linkRatio_le T R dy {v | v ∈ centredCube F.blockSide} t hT) l 0
      (BondHull.allAlong_axisPath_centredCube hh 1)
    rw [siteOfCoords_zero, add_zero] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (BondHull.length_axisPath_le hh 1) ht0)
  have hp2 : _root_.YangMills.Construction.BlockAverages.distFromOne (BondHull.pathRatio (gaugeTransform δ T) R dy l) ≤ 2 * F.blockSide * t' := by
    have h1 := BondHull.distFromOne_pathRatio_le (gaugeTransform δ T) R dy (fun v => v ∈ centredCube F.blockSide) t'
      ht'0 (BondHull.distFromOne_linkRatio_le (gaugeTransform δ T) R dy {v | v ∈ centredCube F.blockSide} t' hT') l 0
      (BondHull.allAlong_axisPath_centredCube hh 1)
    rw [siteOfCoords_zero, add_zero] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (BondHull.length_axisPath_le hh 1) ht'0)
  set b := bal * BondHull.pathRatio T R dy l with hb
  set b' := bal' * BondHull.pathRatio (gaugeTransform δ T) R dy l with hb'
  have hbs : _root_.YangMills.Construction.BlockAverages.distFromOne b ≤ 8 * F.blockSide * t := by
    have := BondHull.distFromOne_mul_le bal (BondHull.pathRatio T R dy l)
    linarith
  have hbs' : _root_.YangMills.Construction.BlockAverages.distFromOne b' ≤ 8 * F.blockSide * t' := by
    have := BondHull.distFromOne_mul_le bal' (BondHull.pathRatio (gaugeTransform δ T) R dy l)
    linarith
  set A := fy⁻¹ * kl * fy with hA
  set τ := fy⁻¹ * Hw * fx with hτ
  set B := fy⁻¹ * b * fy with hB
  set B' := fy⁻¹ * b' * fy with hB'
  have eb : b = bal * (Ht * Hw⁻¹) := rfl
  have eb' : b' = bal' * (δ dy * Ht * (δ x)⁻¹ * Hw⁻¹) := by
    rw [hb', ← hgt]
    rfl
  have ident : fy⁻¹ * (kl * bal' * δ dy * (kl * bal)⁻¹) * fy =
      (A * B' * τ) * (fx⁻¹ * δ x * fx) * (τ⁻¹ * B⁻¹ * A⁻¹) := by
    rw [hA, hB', hτ, hB, eb, eb']
    group
  rw [ident]
  refine (_root_.YangMills.Construction.BlockAverages.PinnedGaugeStart.distFromOne_conjSides_le _ _ _ _).trans ?_
  have u1 := BondHull.distFromOne_mul_le (A * B') τ
  have u2 := BondHull.distFromOne_mul_le A B'
  have v1 := BondHull.distFromOne_mul_le (τ⁻¹ * B⁻¹) A⁻¹
  have v2 := BondHull.distFromOne_mul_le τ⁻¹ B⁻¹
  have sA : _root_.YangMills.Construction.BlockAverages.distFromOne A = _root_.YangMills.Construction.BlockAverages.distFromOne kl := by
    have := BondHull.distFromOne_conj fy⁻¹ kl
    rwa [inv_inv] at this
  have sB : _root_.YangMills.Construction.BlockAverages.distFromOne B = _root_.YangMills.Construction.BlockAverages.distFromOne b := by
    have := BondHull.distFromOne_conj fy⁻¹ b
    rwa [inv_inv] at this
  have sB' : _root_.YangMills.Construction.BlockAverages.distFromOne B' = _root_.YangMills.Construction.BlockAverages.distFromOne b' := by
    have := BondHull.distFromOne_conj fy⁻¹ b'
    rwa [inv_inv] at this
  rw [BondHull.distFromOne_inv] at v1 v2
  rw [BondHull.distFromOne_inv] at v2
  nlinarith
theorem blockSum_le_lowerSum (hodd : Odd F.blockSide) (hj : j < F.top) {z : F.Cell} (d : F.Site j → ℝ)
    (d' Est : F.Site (j + 1) → ℝ) (hd0 : ∀ x, 0 ≤ d x) (hE0 : ∀ y, 0 ≤ Est y) {c : ℝ} (hc0 : 0 ≤ c)
    (hst : ∀ y ∈ sitesOfCells ({z} : Finset F.Cell) (j + 1), ∀ h ∈ centredCube F.blockSide,
      d' y ≤ d (refineSite y + siteOfCoords j h) + Est y)
    (hE4 : ∑ y ∈ sitesOfCells ({z} : Finset F.Cell) (j + 1), Est y ^ 4 ≤ c ^ 4) :
    (F.blockSide : ℝ) ^ 4 * ∑ y ∈ sitesOfCells ({z} : Finset F.Cell) (j + 1), d' y ≤
      ∑ x ∈ sitesOfCells ({z} : Finset F.Cell) j, d x +
        (F.blockSide : ℝ) ^ 4 * (((F.blockSide : ℝ) ^ (F.top - (j + 1))) ^ 3 * c) := by
  classical
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  set Y := sitesOfCells ({z} : Finset F.Cell) (j + 1) with hY
  have hcardc : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
    rw [LatticePaths.card_centredCube hodd]
    push_cast
    rfl
  have h1 : ∀ y ∈ Y, (F.blockSide : ℝ) ^ 4 * d' y ≤
      ∑ h ∈ centredCube F.blockSide, d (refineSite y + siteOfCoords j h) + (F.blockSide : ℝ) ^ 4 * Est y := by
    intro y hy
    have h2 : ∑ _h ∈ centredCube F.blockSide, d' y ≤
        ∑ h ∈ centredCube F.blockSide, (d (refineSite y + siteOfCoords j h) + Est y) :=
      Finset.sum_le_sum fun h hh => hst y hy h hh
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hcardc] at h2
    exact h2
  have h3 : ∑ y ∈ Y, ∑ h ∈ centredCube F.blockSide, d (refineSite y + siteOfCoords j h) ≤
      ∑ x ∈ sitesOfCells ({z} : Finset F.Cell) j, d x := by
    rw [← Finset.sum_product']
    have himg : Set.InjOn (fun p : F.Site (j + 1) × LatticeFractionalIntegration.Lattice4 =>
        refineSite p.1 + siteOfCoords j p.2) (Y ×ˢ centredCube F.blockSide : Finset _) := by
      intro p hp q hq e
      have hp' := Finset.mem_product.1 hp
      have hq' := Finset.mem_product.1 hq
      obtain ⟨a1, a2⟩ := BlockLines.refineSite_add_injective hj hodd p.1 q.1 p.2 q.2 hp'.2 hq'.2 e
      exact Prod.ext a1 a2
    rw [← Finset.sum_image (f := d) himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hd0 _
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    have hp' := Finset.mem_product.1 hp
    exact BlockLines.refineSite_add_mem_sitesOfCells hj hodd p.1 hp'.1 p.2 hp'.2
  have h4 : ∑ y ∈ Y, Est y ≤ ((F.blockSide : ℝ) ^ (F.top - (j + 1))) ^ 3 * c := by
    refine sum_le_of_sum_pow_four_le Y Est hE0 (by positivity) hc0 ?_ hE4
    have := BlockLines.card_sitesOfCells_le hodd ({z} : Finset F.Cell) (j + 1)
    have h5 : (Y.card : ℝ) ≤ (1 : ℝ) * ((F.blockSide : ℝ) ^ (F.top - (j + 1))) ^ 4 := by
      have h6 : Y.card ≤ 1 * (F.blockSide ^ (F.top - (j + 1))) ^ 4 := by simpa using this
      exact_mod_cast h6
    linarith
  calc (F.blockSide : ℝ) ^ 4 * ∑ y ∈ Y, d' y = ∑ y ∈ Y, (F.blockSide : ℝ) ^ 4 * d' y := by rw [Finset.mul_sum]
    _ ≤ ∑ y ∈ Y, (∑ h ∈ centredCube F.blockSide, d (refineSite y + siteOfCoords j h) +
          (F.blockSide : ℝ) ^ 4 * Est y) := Finset.sum_le_sum h1
    _ = ∑ y ∈ Y, ∑ h ∈ centredCube F.blockSide, d (refineSite y + siteOfCoords j h) +
          (F.blockSide : ℝ) ^ 4 * ∑ y ∈ Y, Est y := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := add_le_add h3 (mul_le_mul_of_nonneg_left h4 (by positivity))
theorem pow_four_add_pow_four_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) : A ^ 4 + B ^ 4 ≤ (A + B) ^ 4 := by apply _root_.YangMills.Construction.PatchMorrey.pow_four_add_pow_four_le <;> assumption
theorem add_pow_four_le_eight_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by apply _root_.YangMills.Construction.BlockAverages.SplitCriticalPointBounds.add_pow_four_le <;> assumption
theorem sqrt_sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) ^ 4 = x := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sqrt_sqrt_pow_four <;> assumption
theorem sqrt_sqrt_le_of_le_pow_four {a x : ℝ} (ha : 0 ≤ a) (h : x ≤ a ^ 4) : Real.sqrt (Real.sqrt x) ≤ a := by
  have e : Real.sqrt (Real.sqrt (a ^ 4)) = a := by
    have e1 : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [e1, Real.sqrt_sq (by positivity), Real.sqrt_sq ha]
  calc Real.sqrt (Real.sqrt x) ≤ Real.sqrt (Real.sqrt (a ^ 4)) := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)
    _ = a := e
end PinnedGaugeStart
set_option maxHeartbeats 3200000 in
open PinnedGaugeStart in
theorem pinnedGaugeStart_holds (hGaps : framingDefectsOnPatchStatement)
    (hR : criticalChainPatchRatesStatement) (hS : lowCostPatchBoundsStatement)
    (hQ : patchQuarticGaugeStatement) (hA : averagesAndLocalSizesStatement) :
    pinnedGaugeStartStatement := by
  intro a θ del Ca ha hθ hθ' hd hd' hCa
  obtain ⟨LG, hGp⟩ := hGaps a θ del Ca ha hθ hθ' hd hd' hCa
  obtain ⟨LR, hRt⟩ := hR a θ del Ca ha hθ hθ' hd hd' hCa
  obtain ⟨LS, hSz⟩ := hS a ha
  obtain ⟨Cq, cq, hCq, hcq, hQg⟩ := hQ
  refine ⟨max (max LG LR) (max LS 5), fun L hLodd hLL C₁ hC₁ => ?_⟩
  have hLG : LG ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL
  have hLRl : LR ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL
  have hLS : LS ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLL
  have hL5 : 5 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLL
  obtain ⟨cS, hcS, hSz'⟩ := hSz L hLodd hLS
  obtain ⟨CG, cG, hCG, hcG, hGp'⟩ := hGp L hLodd hLG C₁ hC₁
  obtain ⟨Cr, cr, hCr, hcr, hRt'⟩ := hRt L hLodd hLRl C₁ hC₁
  have hLr5 : (5 : ℝ) ≤ L := by exact_mod_cast hL5
  have hLp : (0 : ℝ) < L := by linarith
  set Q₁ : ℝ := 4 * Cq + 2 * Cr with hQ₁
  have hQ₁p : 0 < Q₁ := by positivity
  set Q₂ : ℝ := CG * (Q₁ + 2) with hQ₂
  have hQ₂p : 0 < Q₂ := by positivity
  set Q₃ : ℝ := 12 * Cr + 288 * (L : ℝ) ^ 2 * Q₂ with hQ₃
  have hQ₃p : 0 < Q₃ := by positivity
  refine ⟨Q₁ + 2 * Q₃ + 344 * (Q₂ + 2 * Cr),
    min cG (min cS (min (cq / 2) (min (cG / Q₁) (1 / (48 * (L : ℝ) ^ 2 * Q₂))))),
    by positivity, lt_min hcG (lt_min hcS (lt_min (by positivity) (lt_min (by positivity) (by positivity)))), ?_⟩
  intro e0 he0 he0c
  have hc1 : e0 ≤ cG := he0c.trans (min_le_left _ _)
  have hc2 : e0 ≤ cS := he0c.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc3 : e0 ≤ cq / 2 := he0c.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc4 : Q₁ * e0 ≤ cG := by
    have h1 : e0 ≤ cG / Q₁ :=
      he0c.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    rw [le_div_iff₀ hQ₁p] at h1
    linarith
  have hc5 : 48 * (L : ℝ) ^ 2 * (Q₂ * e0) ≤ 1 := by
    have h1 : e0 ≤ 1 / (48 * (L : ℝ) ^ 2 * Q₂) :=
      he0c.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  obtain ⟨σG, hσG, hGd⟩ := hGp' e0 he0 hc1
  refine ⟨min σG (min cr e0), lt_min hσG (lt_min hcr he0), ?_⟩
  intro F m S hFL hamb hm hreg s V v hs hsσ hcold hv U hcrit X k z hXn hz hterms
  subst hFL
  have hodd : Odd F.blockSide := hLodd
  have hLR1 : (1 : ℝ) ≤ F.blockSide := by linarith
  have hsG : s ≤ σG := hsσ.trans (min_le_left _ _)
  have hscr : s ≤ cr := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hse : s ≤ e0 := hsσ.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨he, -⟩ := closedOrthant_spec hreg (by omega) z
  obtain ⟨hlev, htopV, hframe⟩ := hRt' F m S rfl hamb hm hreg s V v hs hscr hcold U hcrit z hz
  choose! Er er hEr0 her0 hEr4 her4 hm2 hrt using hlev
  obtain ⟨-, -, hpl⟩ := hSz' e0 he0 hc2 F m S rfl hamb hm hreg X k z hz hterms
  obtain ⟨Γ₀, hΓ₀⟩ := hQg F m S hodd hamb hm hreg z (X 0) (2 * e0) hz (by positivity) (by linarith)
    (hpl.trans (by nlinarith))
  set W := criticalFieldChain S V v U with hW
  set kW := criticalGauge S V U with hkW
  set P := patchCells S z with hP
  have hbp : ∀ j, j ≤ F.top → innerBonds P j = patchInnerBonds S z j :=
    fun j hj => innerBonds_patchCells hamb hodd he hj
  have hzP : z ∈ P := by
    refine Finset.mem_filter.2 ⟨hz, ?_⟩
    rw [baseSite_eq_cellCentre_zero]
    have := PatchLocality.mem_patchBaseSites_of_cellSupDist_le hamb hodd he hz
      (by rw [PatchLocality.cellSupDist_self]; omega) (zero_mem_centredCube hodd.pow)
    rwa [_root_.YangMills.Construction.BlockAverages.siteOfCoords_zero, add_zero] at this
  set γ : UnitQuaternion → F.Site 0 → UnitQuaternion := fun κ x => patchFrame S V z x * κ * Γ₀ x with hγ
  set e₁ : ℝ := 2 * (Cq * (2 * e0) + Cr * s) with he₁
  have he₁0 : 0 ≤ e₁ := by positivity
  have hgap : ∀ κ, quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (γ κ)) 0 ≤ e₁ := by
    intro κ
    have hpt : ∀ b : F.Site 0 × Fin 4,
        _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X (pinnedGaugeOfBase W kW X k (γ κ)) 0 b.1 b.2) ≤
          _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform Γ₀ (X 0) b.1 b.2) +
            _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform (fun x => (patchFrame S V z x)⁻¹) (W 0) b.1 b.2) := by
      intro b
      have e : relativeDefect W X (pinnedGaugeOfBase W kW X k (γ κ)) 0 b.1 b.2 =
          patchFrame S V z b.1 * (κ * gaugeTransform Γ₀ (X 0) b.1 b.2 * κ⁻¹ *
            (gaugeTransform (fun x => (patchFrame S V z x)⁻¹) (W 0) b.1 b.2)⁻¹) * (patchFrame S V z b.1)⁻¹ := by
        simp only [relativeDefect, gaugedChainFields, pinnedGaugeOfBase_zero, gaugeTransform, hγ]
        group
      rw [e, BondHull.distFromOne_conj]
      refine (BondHull.distFromOne_mul_le _ _).trans ?_
      rw [BondHull.distFromOne_inv, BondHull.distFromOne_conj]
    have h0 : 0 < F.top := Nat.succ_pos _
    have hw4 := hframe 0 h0
    rw [hbp 0 (Nat.zero_le _)] at hw4
    refine sqrt_sqrt_le_of_le_pow_four (by positivity) ?_
    calc ∑ b ∈ patchInnerBonds S z 0,
          _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X (pinnedGaugeOfBase W kW X k (γ κ)) 0 b.1 b.2) ^ 4
        ≤ ∑ b ∈ patchInnerBonds S z 0, 8 * (_root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform Γ₀ (X 0) b.1 b.2) ^ 4 +
            _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform (fun x => (patchFrame S V z x)⁻¹) (W 0) b.1 b.2) ^ 4) :=
          Finset.sum_le_sum fun b _ => (pow_le_pow_left₀ (BondHull.distFromOne_nonneg _) (hpt b) 4).trans
            (add_pow_four_le_eight_mul (BondHull.distFromOne_nonneg _) (BondHull.distFromOne_nonneg _))
      _ = 8 * (∑ b ∈ patchInnerBonds S z 0, _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform Γ₀ (X 0) b.1 b.2) ^ 4 +
            ∑ b ∈ patchInnerBonds S z 0,
              _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform (fun x => (patchFrame S V z x)⁻¹) (W 0) b.1 b.2) ^ 4) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 8 * ((Cq * (2 * e0)) ^ 4 + (Cr * s) ^ 4) := by
          have hΓ₀' : ∑ b ∈ patchInnerBonds S z 0, _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform Γ₀ (X 0) b.1 b.2) ^ 4 ≤
              (Cq * (2 * e0)) ^ 4 := hΓ₀
          have := add_le_add hΓ₀' hw4
          linarith
      _ ≤ e₁ ^ 4 := by
          have h1 := pow_four_add_pow_four_le (by positivity : 0 ≤ Cq * (2 * e0)) (by positivity : 0 ≤ Cr * s)
          have e2 : e₁ ^ 4 = 16 * (Cq * (2 * e0) + Cr * s) ^ 4 := by
            rw [he₁]
            ring
          rw [e2]
          have h2 : 0 ≤ (Cq * (2 * e0) + Cr * s) ^ 4 := by positivity
          linarith
  have he₁Q : e₁ ≤ Q₁ * e0 := by
    have h1 : Cr * s ≤ Cr * e0 := mul_le_mul_of_nonneg_left hse hCr.le
    simp only [he₁, hQ₁]
    nlinarith
  have he₁c : e₁ ≤ cG := he₁Q.trans hc4
  set B₁ : ℝ := CG * (e₁ + e0 + s) with hB₁
  have hB₁0 : 0 ≤ B₁ := by positivity
  have hB₁Q : B₁ ≤ Q₂ * e0 := by
    have h1 : e₁ + e0 + s ≤ (Q₁ + 2) * e0 := by nlinarith
    calc B₁ ≤ CG * ((Q₁ + 2) * e0) := mul_le_mul_of_nonneg_left h1 hCG.le
      _ = Q₂ * e0 := by rw [hQ₂]; ring
  have hGκ := fun κ => hGd F m S rfl hamb hm hreg s V v hs hsG hcold hv U hcrit X k z hXn hz hterms (γ κ)
    ((hgap κ).trans he₁c)
  have hlevelB : ∀ κ j, j < F.top → ∑ b ∈ innerBonds P j,
      _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X (pinnedGaugeOfBase W kW X k (γ κ)) j b.1 b.2) ^ 4 ≤ B₁ ^ 4 := by
    intro κ j hj
    obtain ⟨-, g2, -⟩ := hGκ κ
    have h1 := g2 j hj
    have h2 : quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (γ κ)) j ≤ B₁ := by
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hCG.le)
      have := hgap κ
      linarith
    have hS0 : 0 ≤ ∑ b ∈ patchInnerBonds S z j,
        _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X (pinnedGaugeOfBase W kW X k (γ κ)) j b.1 b.2) ^ 4 :=
      Finset.sum_nonneg fun b _ => pow_nonneg (BondHull.distFromOne_nonneg _) 4
    have h3 : quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (γ κ)) j ^ 4 ≤ B₁ ^ 4 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 4
    have e3 : quarticDefectNorm S z W X (pinnedGaugeOfBase W kW X k (γ κ)) j ^ 4 =
        ∑ b ∈ patchInnerBonds S z j,
          _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X (pinnedGaugeOfBase W kW X k (γ κ)) j b.1 b.2) ^ 4 :=
      sqrt_sqrt_pow_four hS0
    rw [hbp j hj.le, ← e3]
    exact h3
  set Γ₁ := pinnedGaugeOfBase W kW X k (γ 1) with hΓ₁
  set K₁ := topCorrection W kW X k Γ₁ z with hK₁
  set fz := patchFrame S V z z with hfz
  set κ : UnitQuaternion := fz⁻¹ * K₁⁻¹ * fz with hκ
  set Γ₂ := pinnedGaugeOfBase W kW X k (γ κ) with hΓ₂
  set low : (j : ℕ) → F.Site j → UnitQuaternion := fun j x => Γ₂ j x * (Γ₁ j x)⁻¹ with hlow
  set up : (j : ℕ) → F.Site (j + 1) → UnitQuaternion := fun j y =>
    rotationAboveLevel W kW X k Γ₂ j y * (rotationAboveLevel W kW X k Γ₁ j y)⁻¹ with hup
  set d : (j : ℕ) → F.Site j → ℝ := fun j x =>
    _root_.YangMills.Construction.BlockAverages.distFromOne ((patchFrame S V z x)⁻¹ * low j x * patchFrame S V z x * κ⁻¹) with hd
  set du : (j : ℕ) → F.Site (j + 1) → ℝ := fun j y =>
    _root_.YangMills.Construction.BlockAverages.distFromOne ((patchFrame S V z y)⁻¹ * up j y * patchFrame S V z y * κ⁻¹) with hdu
  set cc : ℝ := 12 * Cr * s + 288 * (F.blockSide : ℝ) ^ 2 * B₁ with hcc
  have hcc0 : 0 ≤ cc := by positivity
  have hd0 : ∀ j x, 0 ≤ d j x := fun j x => BondHull.distFromOne_nonneg _
  have hdu0 : ∀ j y, 0 ≤ du j y := fun j y => BondHull.distFromOne_nonneg _
  have hEst : ∀ j, j < F.top → ∃ Est : F.Site (j + 1) → ℝ, (∀ y, 0 ≤ Est y) ∧
      ∑ y ∈ sitesOfCells ({z} : Finset F.Cell) (j + 1), Est y ^ 4 ≤ cc ^ 4 ∧
      ∀ y ∈ sitesOfCells ({z} : Finset F.Cell) (j + 1), ∀ h ∈ centredCube F.blockSide,
        du j y ≤ d j (refineSite y + siteOfCoords j h) + Est y := by
    intro j hj
    have hj1 : j + 1 ≤ F.top := hj
    obtain ⟨-, -, -, T₁, hT₁0, -, hT₁s, hT₁p, -, hT₁4⟩ := hA F P j
      (fun x i => _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X Γ₁ j x i)) hodd hj1 (fun x i => BondHull.distFromOne_nonneg _)
    obtain ⟨-, -, -, T₂, hT₂0, -, hT₂s, hT₂p, -, hT₂4⟩ := hA F P j
      (fun x i => _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X Γ₂ j x i)) hodd hj1 (fun x i => BondHull.distFromOne_nonneg _)
    have hB1 := hlevelB 1 j hj
    have hB2 := hlevelB κ j hj
    have hTsmall : ∀ {T : F.Site (j + 1) → ℝ} {Sm : ℝ}, Sm ≤ B₁ ^ 4 →
        (∀ y, T y ^ 4 ≤ 4 * (3 * (F.blockSide : ℝ)) ^ 4 * Sm) → ∀ y, T y ≤ 6 * F.blockSide * B₁ := by
      intro T Sm hSm hTp y
      have h2 := mul_le_mul_of_nonneg_left hSm (by positivity : 0 ≤ 4 * (3 * (F.blockSide : ℝ)) ^ 4)
      have h3 : 4 * (3 * (F.blockSide : ℝ)) ^ 4 * B₁ ^ 4 ≤ (6 * (F.blockSide : ℝ) * B₁) ^ 4 := by
        have h4 : 0 ≤ ((F.blockSide : ℝ) * B₁) ^ 4 := by positivity
        have e1 : 4 * (3 * (F.blockSide : ℝ)) ^ 4 * B₁ ^ 4 = 324 * ((F.blockSide : ℝ) * B₁) ^ 4 := by ring
        have e2 : (6 * (F.blockSide : ℝ) * B₁) ^ 4 = 1296 * ((F.blockSide : ℝ) * B₁) ^ 4 := by ring
        rw [e1, e2]
        linarith
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) ((hTp y).trans (h2.trans h3))
    have hT₁le := hTsmall hB1 hT₁p
    have hT₂le := hTsmall hB2 hT₂p
    have hsmallB : 12 * (F.blockSide : ℝ) ^ 2 * B₁ ≤ 1 / 4 := by
      have h1 : 48 * (F.blockSide : ℝ) ^ 2 * B₁ ≤ 48 * (F.blockSide : ℝ) ^ 2 * (Q₂ * e0) :=
        mul_le_mul_of_nonneg_left hB₁Q (by positivity)
      linarith
    have hsm : ∀ {T : F.Site (j + 1) → ℝ}, (∀ y, T y ≤ 6 * F.blockSide * B₁) →
        ∀ y, 2 * (F.blockSide : ℝ) * T y ≤ 1 / 4 := by
      intro T hT y
      have h1 := mul_le_mul_of_nonneg_left (hT y) (by positivity : 0 ≤ 2 * (F.blockSide : ℝ))
      have e : 2 * (F.blockSide : ℝ) * (6 * F.blockSide * B₁) = 12 * (F.blockSide : ℝ) ^ 2 * B₁ := by ring
      rw [e] at h1
      linarith
    have hsub : sitesOfCells ({z} : Finset F.Cell) (j + 1) ⊆ sitesOfCells P (j + 1) := by
      intro y hy
      obtain ⟨y', hy', g, hg, e⟩ := mem_sitesOfCells.1 hy
      rw [Finset.mem_singleton.1 hy'] at e
      exact mem_sitesOfCells.2 ⟨z, hzP, g, hg, e⟩
    set Est : F.Site (j + 1) → ℝ := fun y => 4 * Er j y + 8 * (F.blockSide : ℝ) * (T₁ y + T₂ y) with hEstD
    have hEst0 : ∀ y, 0 ≤ Est y := fun y => add_nonneg (mul_nonneg (by norm_num) (hEr0 j hj y))
      (mul_nonneg (by positivity) (add_nonneg (hT₁0 y) (hT₂0 y)))
    refine ⟨Est, hEst0, ?_, ?_⟩
    · have h1 : ∑ y ∈ sitesOfCells ({z} : Finset F.Cell) (j + 1), Est y ^ 4 ≤
          ∑ y ∈ sitesOfCells P (j + 1), Est y ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun y _ _ => pow_nonneg (hEst0 y) 4
      refine h1.trans ?_
      have hp : ∀ y, Est y ^ 4 ≤ 8 * (4 ^ 4 * Er j y ^ 4) + 64 * ((8 * (F.blockSide : ℝ)) ^ 4 * T₁ y ^ 4) +
          64 * ((8 * (F.blockSide : ℝ)) ^ 4 * T₂ y ^ 4) := by
        intro y
        have a0 : 0 ≤ 4 * Er j y := mul_nonneg (by norm_num) (hEr0 j hj y)
        have b0 : 0 ≤ 8 * (F.blockSide : ℝ) * T₁ y := mul_nonneg (by positivity) (hT₁0 y)
        have c0 : 0 ≤ 8 * (F.blockSide : ℝ) * T₂ y := mul_nonneg (by positivity) (hT₂0 y)
        have h2 := add_pow_four_le_eight_mul a0 (add_nonneg b0 c0)
        have h3 := add_pow_four_le_eight_mul b0 c0
        have e1 : Est y = 4 * Er j y + (8 * (F.blockSide : ℝ) * T₁ y + 8 * (F.blockSide : ℝ) * T₂ y) := by
          simp only [hEstD]
          ring
        rw [e1]
        have e2 : (4 * Er j y) ^ 4 = 4 ^ 4 * Er j y ^ 4 := by ring
        have e3 : (8 * (F.blockSide : ℝ) * T₁ y) ^ 4 = (8 * (F.blockSide : ℝ)) ^ 4 * T₁ y ^ 4 := by ring
        have e4 : (8 * (F.blockSide : ℝ) * T₂ y) ^ 4 = (8 * (F.blockSide : ℝ)) ^ 4 * T₂ y ^ 4 := by ring
        rw [e2] at h2
        rw [e3, e4] at h3
        linarith
      have hT14 : ∑ y ∈ sitesOfCells P (j + 1), T₁ y ^ 4 ≤ 4 * (3 * (F.blockSide : ℝ)) ^ 4 * B₁ ^ 4 :=
        hT₁4.trans (mul_le_mul_of_nonneg_left hB1 (by positivity))
      have hT24 : ∑ y ∈ sitesOfCells P (j + 1), T₂ y ^ 4 ≤ 4 * (3 * (F.blockSide : ℝ)) ^ 4 * B₁ ^ 4 :=
        hT₂4.trans (mul_le_mul_of_nonneg_left hB2 (by positivity))
      have hE4 := hEr4 j hj
      refine (Finset.sum_le_sum fun y _ => hp y).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      have x1 : (4 : ℝ) ^ 4 * ∑ y ∈ sitesOfCells P (j + 1), Er j y ^ 4 ≤ 4 ^ 4 * (Cr * s) ^ 4 :=
        mul_le_mul_of_nonneg_left hE4 (by positivity)
      have x2 := mul_le_mul_of_nonneg_left hT14 (by positivity : 0 ≤ (8 * (F.blockSide : ℝ)) ^ 4)
      have x3 := mul_le_mul_of_nonneg_left hT24 (by positivity : 0 ≤ (8 * (F.blockSide : ℝ)) ^ 4)
      have hA0 : 0 ≤ 8 * Cr * s := by positivity
      have hB0 : 0 ≤ 192 * (F.blockSide : ℝ) ^ 2 * B₁ := by positivity
      have x4 := pow_four_add_pow_four_le hA0 hB0
      have x5 : (8 * Cr * s + 192 * (F.blockSide : ℝ) ^ 2 * B₁) ^ 4 ≤ cc ^ 4 := by
        refine pow_le_pow_left₀ (by positivity) ?_ 4
        simp only [hcc]
        have : 0 ≤ Cr * s := by positivity
        have : 0 ≤ (F.blockSide : ℝ) ^ 2 * B₁ := by positivity
        nlinarith
      have e5 : (8 * Cr * s) ^ 4 = 16 * (4 ^ 4 * (Cr * s) ^ 4) := by ring
      have e6 : (192 * (F.blockSide : ℝ) ^ 2 * B₁) ^ 4 =
          1024 * ((8 * (F.blockSide : ℝ)) ^ 4 * (4 * (3 * (F.blockSide : ℝ)) ^ 4 * B₁ ^ 4)) := by ring
      have p1 : 0 ≤ (4 : ℝ) ^ 4 * (Cr * s) ^ 4 := by positivity
      have p2 : 0 ≤ (8 * (F.blockSide : ℝ)) ^ 4 * (4 * (3 * (F.blockSide : ℝ)) ^ 4 * B₁ ^ 4) := by positivity
      linarith
    · intro y hy h hh
      have hyP := hsub hy
      set T := gaugedChainFields X Γ₁ j with hT
      set R := W j with hR'
      have hg : gaugeTransform (low j) T = gaugedChainFields X Γ₂ j :=
        gaugeTransform_gaugeTransform (Γ₁ j) (Γ₂ j) (X j)
      have hfd : patchFrame S V z (refineSite y) = patchFrame S V z y := by
        unfold patchFrame
        rw [baseSite_refineSite _ hj1]
      have hps := _root_.YangMills.Construction.BlockAverages.PinnedGaugeStart.distFromOne_gaugeChange_le hodd T R (low j) (kW (j + 1) y) (patchFrame S V z (refineSite y))
        (patchFrame S V z (refineSite y + siteOfCoords j h)) κ y hh (T₁ y) (T₂ y) (Er j y) (hT₁0 y) (hT₂0 y)
        (hEr0 j hj y) (hsm hT₁le y) (hsm hT₂le y)
        (fun g hg' k' hk' => hT₁s y hyP g hg' k' hk')
        (fun g hg' k' hk' => by
          rw [hg]
          exact hT₂s y hyP g hg' k' hk')
        ((hrt j hj).gauge_le y hyP) ((hrt j hj).axisPath_le y hyP h hh 1)
      rw [hg] at hps
      have hup' : up j y = (kW (j + 1) y * balancingGauge (gaugedChainFields X Γ₂ j) R y) * low j (refineSite y) *
          (kW (j + 1) y * balancingGauge T R y)⁻¹ := by
        have e₂ := balancedLinkAgainst_eq_rotationAboveLevel W kW X k Γ₂ j y
        have e₁' := balancedLinkAgainst_eq_rotationAboveLevel W kW X k Γ₁ j y
        have f₂ : kW (j + 1) y * balancingGauge (gaugedChainFields X Γ₂ j) R y =
            balancedLinkAgainst W kW (gaugedChainFields X Γ₂) j y := rfl
        have f₁ : kW (j + 1) y * balancingGauge T R y = balancedLinkAgainst W kW (gaugedChainFields X Γ₁) j y := rfl
        rw [f₂, f₁, e₂, e₁']
        simp only [hup, hlow]
        group
      have e3 : du j y = _root_.YangMills.Construction.BlockAverages.distFromOne ((patchFrame S V z (refineSite y))⁻¹ *
          ((kW (j + 1) y * balancingGauge (gaugedChainFields X Γ₂ j) R y) * low j (refineSite y) *
            (kW (j + 1) y * balancingGauge T R y)⁻¹) * patchFrame S V z (refineSite y) * κ⁻¹) := by
        simp only [hdu]
        rw [hup', hfd]
      rw [e3]
      refine hps.trans (le_of_eq ?_)
      simp only [hEstD, hd]
      ring
  have hnum : ∀ j, j < F.top →
      ∑ x ∈ sitesOfCells ({z} : Finset F.Cell) j, d j x ≤ 2 * cc * ((F.blockSide : ℝ) ^ (F.top - j)) ^ 3 →
      ∑ y ∈ sitesOfCells ({z} : Finset F.Cell) (j + 1), du j y ≤
        2 * cc * ((F.blockSide : ℝ) ^ (F.top - (j + 1))) ^ 3 := by
    intro j hj hAj
    obtain ⟨Est, hE0, hE4, hst⟩ := hEst j hj
    have h1 := blockSum_le_lowerSum hodd hj (d j) (du j) Est (hd0 j) hE0 hcc0 hst hE4
    set M : ℝ := (F.blockSide : ℝ) ^ (F.top - (j + 1)) with hM
    have hM0 : 0 ≤ M := by positivity
    have e1 : (F.blockSide : ℝ) ^ (F.top - j) = F.blockSide * M := by
      have : F.top - j = (F.top - (j + 1)) + 1 := by omega
      rw [this, pow_succ, hM]
      ring
    rw [e1] at hAj
    have h2 : (F.blockSide : ℝ) ^ 4 * ∑ y ∈ sitesOfCells ({z} : Finset F.Cell) (j + 1), du j y ≤
        (F.blockSide : ℝ) ^ 4 * (2 * cc * M ^ 3) := by
      have h3 : 2 * cc * ((F.blockSide : ℝ) * M) ^ 3 + (F.blockSide : ℝ) ^ 4 * (M ^ 3 * cc) ≤
          (F.blockSide : ℝ) ^ 4 * (2 * cc * M ^ 3) := by
        have p : 0 ≤ cc * M ^ 3 * (F.blockSide : ℝ) ^ 3 := by positivity
        have e2 : (F.blockSide : ℝ) ^ 4 * (2 * cc * M ^ 3) -
            (2 * cc * ((F.blockSide : ℝ) * M) ^ 3 + (F.blockSide : ℝ) ^ 4 * (M ^ 3 * cc)) =
            cc * M ^ 3 * (F.blockSide : ℝ) ^ 3 * ((F.blockSide : ℝ) - 2) := by ring
        have h4 : 0 ≤ cc * M ^ 3 * (F.blockSide : ℝ) ^ 3 * ((F.blockSide : ℝ) - 2) := mul_nonneg p (by linarith)
        linarith
      linarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  have hAll : ∀ j, j < F.top →
      ∑ x ∈ sitesOfCells ({z} : Finset F.Cell) j, d j x ≤ 2 * cc * ((F.blockSide : ℝ) ^ (F.top - j)) ^ 3 := by
    intro j
    induction j with
    | zero =>
      intro _
      have h0 : ∑ x ∈ sitesOfCells ({z} : Finset F.Cell) 0, d 0 x = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        have e : (patchFrame S V z x)⁻¹ * low 0 x * patchFrame S V z x * κ⁻¹ = 1 := by
          simp only [hlow, hΓ₁, hΓ₂, pinnedGaugeOfBase_zero, hγ]
          group
        simp only [hd]
        rw [e]
        simp [_root_.YangMills.Construction.BlockAverages.distFromOne]
      rw [h0]
      positivity
    | succ j ih =>
      intro hj
      have hj' : j < F.top := by omega
      have h1 := hnum j hj' (ih hj')
      refine le_trans (le_of_eq ?_) h1
      refine Finset.sum_congr rfl fun y _ => ?_
      have e : low (j + 1) y = up j y := by
        have hb₁ := gaugedLink_pinnedGaugeOfBase W kW X k (γ 1) hj y
        have hb₂ := gaugedLink_pinnedGaugeOfBase W kW X k (γ κ) hj y
        simp only [hup, hlow, rotationAboveLevel, balancedRotation]
        rw [← hΓ₁, ← hΓ₂] at *
        rw [← hb₁, ← hb₂, mul_inv_cancel, mul_inv_cancel, one_mul, one_mul]
      simp only [hd, hdu, e]
  have hjt : F.depth < F.top := Nat.lt_succ_self _
  have hUp := hnum F.depth hjt (hAll F.depth hjt)
  have hzs : z ∈ sitesOfCells ({z} : Finset F.Cell) (F.depth + 1) :=
    mem_sitesOfCells_top.2 (Finset.mem_singleton_self z)
  have hdz : du F.depth z ≤ 2 * cc := by
    have h1 := Finset.single_le_sum (f := fun y => du F.depth y) (fun y _ => hdu0 F.depth y) hzs
    have e : (F.top - (F.depth + 1)) = 0 := by
      have : F.top = F.depth + 1 := rfl
      omega
    rw [e] at hUp
    simp only [pow_zero, one_pow, mul_one] at hUp
    exact h1.trans hUp
  have hturn : ∀ (Γ : F.SiteGauge), (∀ y, Γ F.top y = 1) →
      ∀ y : F.Site F.top, rotationAboveLevel W kW X k Γ F.depth y = topCorrection W kW X k Γ y := by
    intro Γ htop y
    have : Γ (F.depth + 1) y = 1 := htop y
    unfold rotationAboveLevel balancedRotation topCorrection
    rw [this, mul_one]
  have htop₁ : ∀ y, Γ₁ F.top y = 1 := pinnedGaugeOfBase_top W kW X k (γ 1)
  have htop₂ : ∀ y, Γ₂ F.top y = 1 := pinnedGaugeOfBase_top W kW X k (γ κ)
  set K₂ : F.Cell → UnitQuaternion := fun y => topCorrection W kW X k Γ₂ y with hK₂
  have hKz : _root_.YangMills.Construction.BlockAverages.distFromOne (K₂ z) ≤ 2 * cc := by
    have eU : up F.depth z = K₂ z * K₁⁻¹ := by
      show rotationAboveLevel W kW X k Γ₂ F.depth z * (rotationAboveLevel W kW X k Γ₁ F.depth z)⁻¹ = _
      rw [hturn Γ₁ htop₁, hturn Γ₂ htop₂]
    have e : fz⁻¹ * up F.depth z * fz * κ⁻¹ = fz⁻¹ * K₂ z * fz := by
      rw [eU, hκ]
      group
    have e2 : du F.depth z = _root_.YangMills.Construction.BlockAverages.distFromOne (K₂ z) := by
      show _root_.YangMills.Construction.BlockAverages.distFromOne (fz⁻¹ * up F.depth z * fz * κ⁻¹) = _
      rw [e]
      have := BondHull.distFromOne_conj fz⁻¹ (K₂ z)
      rwa [inv_inv] at this
    rw [← e2]
    exact hdz
  have hXW : X F.top = W F.top := by
    rw [hXn, hW]
    unfold criticalFieldChain chartChain
    exact (Function.update_self _ _ _).symm
  set η₂ : ℝ := B₁ + 2 * (Cr * s) with hη₂
  have hη₂0 : 0 ≤ η₂ := by positivity
  have hbal₂ : ∀ j', j' + 1 < F.top → ∀ y,
      gaugedLink k Γ₂ j' y = balancedLinkAgainst W kW (gaugedChainFields X Γ₂) j' y :=
    fun j' hj' y => gaugedLink_pinnedGaugeOfBase W kW X k (γ κ) hj' y
  have hup₂ := framedUpperField_eq_gaugeTransform W kW X k Γ₂ hjt htop₂ hbal₂
  obtain ⟨-, -, g3, -, -⟩ := hGκ κ
  have hΦ : ∀ c ∈ innerBonds P F.top,
      |_root_.YangMills.Construction.BlockAverages.distFromOne (K₂ c.1) - _root_.YangMills.Construction.BlockAverages.distFromOne (K₂ (c.1 + unitStep F.top c.2))| ≤ η₂ := by
    intro c hc
    have hg := g3 c (by rw [← hbp _ (le_refl _)]; exact hc)
    have hg2 : _root_.YangMills.Construction.BlockAverages.distFromOne (topDefect W kW X k Γ₂ c.1 c.2) ≤ B₁ := by
      refine hg.trans (mul_le_mul_of_nonneg_left ?_ hCG.le)
      have := hgap κ
      linarith
    set Vc := W F.top c.1 c.2 with hVc
    set f₁ := patchFrame S V z c.1 with hf₁
    set f₂ := patchFrame S V z (c.1 + unitStep F.top c.2) with hf₂
    set k₁ := K₂ c.1 with hk₁
    set k₂ := K₂ (c.1 + unitStep F.top c.2) with hk₂
    have eg : topDefect W kW X k Γ₂ c.1 c.2 = k₁ * Vc * k₂⁻¹ * Vc⁻¹ := by
      unfold topDefect
      rw [hup₂]
      simp only [gaugeTransform]
      rw [hturn Γ₂ htop₂, hturn Γ₂ htop₂]
      have : X (F.depth + 1) c.1 c.2 = Vc := by
        exact show X F.top c.1 c.2 = W F.top c.1 c.2 from by rw [hXW]
      rw [this]
    have hV := htopV c hc
    set Vt := f₁⁻¹ * Vc * f₂ with hVt
    set p := f₁⁻¹ * k₁ * f₁ with hp
    set q := f₂⁻¹ * k₂ * f₂ with hq
    have sp : _root_.YangMills.Construction.BlockAverages.distFromOne p = _root_.YangMills.Construction.BlockAverages.distFromOne k₁ := by
      have := BondHull.distFromOne_conj f₁⁻¹ k₁
      rwa [inv_inv] at this
    have sq : _root_.YangMills.Construction.BlockAverages.distFromOne q = _root_.YangMills.Construction.BlockAverages.distFromOne k₂ := by
      have := BondHull.distFromOne_conj f₂⁻¹ k₂
      rwa [inv_inv] at this
    have ident : p * q⁻¹ = (f₁⁻¹ * topDefect W kW X k Γ₂ c.1 c.2 * f₁) * Vt * (q * Vt⁻¹ * q⁻¹) := by
      rw [eg, hp, hq, hVt]
      group
    have hsz : _root_.YangMills.Construction.BlockAverages.distFromOne (p * q⁻¹) ≤ η₂ := by
      rw [ident]
      have u1 := BondHull.distFromOne_mul_le ((f₁⁻¹ * topDefect W kW X k Γ₂ c.1 c.2 * f₁) * Vt) (q * Vt⁻¹ * q⁻¹)
      have u2 := BondHull.distFromOne_mul_le (f₁⁻¹ * topDefect W kW X k Γ₂ c.1 c.2 * f₁) Vt
      have u3 := BondHull.distFromOne_conj f₁⁻¹ (topDefect W kW X k Γ₂ c.1 c.2)
      rw [inv_inv] at u3
      rw [BondHull.distFromOne_conj, BondHull.distFromOne_inv] at u1
      rw [u3] at u2
      simp only [hη₂]
      linarith
    have hsz' : _root_.YangMills.Construction.BlockAverages.distFromOne (q * p⁻¹) ≤ η₂ := by
      have e : q * p⁻¹ = (p * q⁻¹)⁻¹ := by group
      rw [e, BondHull.distFromOne_inv]
      exact hsz
    have a1 := _root_.YangMills.Construction.BlockAverages.PinnedGaugeStart.distFromOne_sub_le p q
    have a2 := _root_.YangMills.Construction.BlockAverages.PinnedGaugeStart.distFromOne_sub_le q p
    rw [sp, sq] at a1 a2
    rw [abs_le]
    constructor <;> linarith
  refine ⟨γ κ, ?_, ?_⟩
  · refine (hgap κ).trans (he₁Q.trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ he0.le
    have h1 : 0 ≤ 2 * Q₃ := by positivity
    have h2 : 0 ≤ 344 * (Q₂ + 2 * Cr) := by positivity
    linarith
  · intro y hy
    have hyP : y ∈ P := by
      obtain ⟨x', hx', e⟩ := Finset.mem_image.1 hy
      have h1 := (PatchPoints.enclosingCell_patchSite hamb hodd hreg (by omega) hx').1
      rw [e, baseSite_eq_cellCentre_zero] at h1
      have h2 := PatchPoints.enclosingCell_cellCentre_add (j := 0) hodd y 0
        (by simpa using zero_mem_centredCube hodd.pow)
      rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_zero, add_zero] at h2
      rw [h2] at h1
      exact Finset.mem_filter.2 ⟨h1, hy⟩
    have h1 := PatchPaths.abs_sub_le_of_mem_patchCells hamb hodd hreg (by omega : 32 ≤ m) he
      (fun y => _root_.YangMills.Construction.BlockAverages.distFromOne (K₂ y)) η₂ hη₂0 hΦ hzP hyP
    have h2 : _root_.YangMills.Construction.BlockAverages.distFromOne (K₂ y) ≤ _root_.YangMills.Construction.BlockAverages.distFromOne (K₂ z) + 344 * η₂ := by
      have := (abs_le.1 h1).2
      linarith
    have hcc1 : cc ≤ Q₃ * e0 := by
      have p1 : Cr * s ≤ Cr * e0 := mul_le_mul_of_nonneg_left hse hCr.le
      have p2 : 288 * (F.blockSide : ℝ) ^ 2 * B₁ ≤ 288 * (F.blockSide : ℝ) ^ 2 * (Q₂ * e0) :=
        mul_le_mul_of_nonneg_left hB₁Q (by positivity)
      have e1 : Q₃ * e0 = 12 * (Cr * e0) + 288 * (F.blockSide : ℝ) ^ 2 * (Q₂ * e0) := by
        rw [hQ₃]
        ring
      have e2 : cc = 12 * (Cr * s) + 288 * (F.blockSide : ℝ) ^ 2 * B₁ := by
        rw [hcc]
        ring
      rw [e1, e2]
      linarith
    have hη : η₂ ≤ (Q₂ + 2 * Cr) * e0 := by
      have p1 : Cr * s ≤ Cr * e0 := mul_le_mul_of_nonneg_left hse hCr.le
      have e1 : (Q₂ + 2 * Cr) * e0 = Q₂ * e0 + 2 * (Cr * e0) := by ring
      rw [e1, hη₂]
      linarith
    have e2 : (Q₁ + 2 * Q₃ + 344 * (Q₂ + 2 * Cr)) * e0 =
        Q₁ * e0 + 2 * (Q₃ * e0) + 344 * ((Q₂ + 2 * Cr) * e0) := by ring
    have p3 : 0 ≤ Q₁ * e0 := by positivity
    show _root_.YangMills.Construction.BlockAverages.distFromOne (K₂ y) ≤ _
    rw [e2]
    linarith [hKz]
end YangMills.Construction.BlockAverages
end
