import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfACellForm
import YangMills.Construction.ColdChainAtEveryLevel.FormsInAPatch
import YangMills.Construction.ColdChainAtEveryLevel.GeneratorNearItsBlockMean
import YangMills.Construction.ColdChainAtEveryLevel.GeneratorsOfAFramingOnACell
import YangMills.Construction.ColdChainAtEveryLevel.HolonomiesOnTheHullOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.CellGenerators
variable {F : BlockFrame} {j : ℕ}
def linkQuotient (X R : F.GaugeField j) (x : F.Site j) (s : PathStep) : UnitQuaternion :=
  linkValue X x s * (linkValue R x s)⁻¹
def pathQuotient (X R : F.GaugeField j) (x : F.Site j) (l : List PathStep) : UnitQuaternion :=
  pathHolonomy X x l * (pathHolonomy R x l)⁻¹
theorem stepDisplacement_eq_siteOfCoords (s : PathStep) :
    stepDisplacement (F := F) j s = siteOfCoords j (FlatPairing.stepDisplacement s) := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords <;> assumption
theorem linkQuotient_forward (X R : F.GaugeField j) (x : F.Site j) (μ : Fin 4) :
    linkQuotient X R x (μ, true) = X x μ * (R x μ)⁻¹ := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.linkDiscrepancy_forward <;> assumption
theorem distFromOne_linkQuotient_backward (X R : F.GaugeField j) (x : F.Site j) (μ : Fin 4) :
    _root_.YangMills.Construction.BlockAverages.distFromOne (linkQuotient X R x (μ, false)) =
      _root_.YangMills.Construction.BlockAverages.distFromOne (X (x - unitStep j μ) μ * (R (x - unitStep j μ) μ)⁻¹) := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.normSubOne_linkDiscrepancy_backward <;> assumption
theorem distFromOne_mul_le (a b : UnitQuaternion) : _root_.YangMills.Construction.BlockAverages.distFromOne (a * b) ≤ _root_.YangMills.Construction.BlockAverages.distFromOne a + _root_.YangMills.Construction.BlockAverages.distFromOne b := by apply _root_.YangMills.Construction.BondHull.distFromOne_mul_le <;> assumption
theorem distFromOne_pathQuotient_le (X R : F.GaugeField j) (x₀ : F.Site j) (p : LatticeFractionalIntegration.Lattice4 → Prop)
    (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ u s, p u → p (u + FlatPairing.stepDisplacement s) →
      _root_.YangMills.Construction.BlockAverages.distFromOne (linkQuotient X R (x₀ + siteOfCoords j u) s) ≤ c) :
    ∀ (l : List PathStep) (u : LatticeFractionalIntegration.Lattice4), LatticePaths.AllAlong p u l →
      _root_.YangMills.Construction.BlockAverages.distFromOne (pathQuotient X R (x₀ + siteOfCoords j u) l) ≤ l.length * c := by apply _root_.YangMills.Construction.BondHull.distFromOne_pathRatio_le <;> assumption
theorem sitesOfCells_mono {D D' : Finset F.Cell} (h : D ⊆ D') (j : ℕ) :
    sitesOfCells D j ⊆ sitesOfCells D' j := by apply _root_.YangMills.Construction.BlockLines.sitesOfCells_mono <;> assumption
theorem add_pow_four_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.add_pow_four_le_eight_mul <;> assumption
theorem sqrt_sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) ^ 4 = x := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sqrt_sqrt_pow_four <;> assumption
set_option maxHeartbeats 2000000 in
theorem cellGeneratorNearBlockMean (hEnergyPreserved : pinnedGaugeVariationStatement)
    (hNear : generatorNearBlockMeanStatement)
    (hComp : CompositeMean.compositeMeanBoundStatement) : cellGeneratorNearBlockMeanStatement := by
  classical
  intro F m S V W kW X k γ ξ z y₀ q r E hodd h5 hamb hm hreg hy₀ hq hr he8 hE0 hEs hk hleg hgap hne
  obtain ⟨hs, -⟩ := closedOrthant_spec hreg (by omega : 32 ≤ m) z
  set D := patchCells S z with hD
  set Γ := pinnedGaugeOfBase W kW X k γ with hΓ
  set gen := pinnedGaugeGenerator W kW X k γ (fun x => (ξ x : ℍ[ℝ])) with hgen
  obtain ⟨hlev, htop⟩ := hEnergyPreserved F W kW X k γ ξ D hodd hne
  have hsub : ({y₀} : Finset F.Cell) ⊆ D := Finset.singleton_subset_iff.2 hy₀
  let G : (j : ℕ) → F.Site j → ℝ := fun j x => ∑ i : Fin 4,
    if (x, i) ∈ innerBonds D j then _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X Γ j x i) ^ 4 else 0
  have hG0 : ∀ j x, 0 ≤ G j x := fun j x => Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
  let Tq : (j : ℕ) → F.Site (j + 1) → ℝ := fun j y =>
    ∑ h ∈ centredCube F.blockSide, G j (refineSite y + siteOfCoords j h)
  have hTq0 : ∀ j y, 0 ≤ Tq j y := fun j y => Finset.sum_nonneg fun _ _ => hG0 _ _
  have hGsum : ∀ j, j < F.top → ∑ x ∈ sitesOfCells D j, G j x ≤ q ^ 4 := by
    intro j hj
    have e1 : ∑ x ∈ sitesOfCells D j, G j x =
        ∑ b ∈ innerBonds D j, _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X Γ j b.1 b.2) ^ 4 := by
      rw [← Finset.sum_product' (s := sitesOfCells D j) (t := Finset.univ)
        (f := fun x i => if (x, i) ∈ innerBonds D j then _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X Γ j x i) ^ 4 else 0)]
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun b _ => rfl
      ext b
      simp only [Finset.mem_filter, Prod.mk.eta]
      exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.1 h).1, h⟩⟩
    rw [e1, hD, innerBonds_patchCells hamb hodd hs (by omega)]
    exact hgap j hj
  have hTsum : ∀ j, j < F.top → ∑ y ∈ sitesOfCells ({y₀} : Finset F.Cell) (j + 1), Tq j y ≤ q ^ 4 := by
    intro j hj
    have h1 := CompositeMean.sum_sum_refineSite_le hodd (D := {y₀}) (j := j) hj (G := G j) (hG0 j)
    have h2 : ∑ x ∈ sitesOfCells ({y₀} : Finset F.Cell) j, G j x ≤ ∑ x ∈ sitesOfCells D j, G j x :=
      Finset.sum_le_sum_of_subset_of_nonneg (sitesOfCells_mono hsub j) fun _ _ _ => hG0 _ _
    exact h1.trans (h2.trans (hGsum j hj))
  let τ : (j : ℕ) → F.Site (j + 1) → ℝ := fun j y => Real.sqrt (Real.sqrt (Tq j y))
  have hτ0 : ∀ j y, 0 ≤ τ j y := fun j y => Real.sqrt_nonneg _
  have hτ4 : ∀ j y, τ j y ^ 4 = Tq j y := fun j y => sqrt_sqrt_pow_four (hTq0 j y)
  let t : (j : ℕ) → F.Site (j + 1) → ℝ := fun j y => 2 * (F.blockSide : ℝ) * τ j y
  have ht0 : ∀ j y, 0 ≤ t j y := fun j y => by
    have := hτ0 j y
    positivity
  have hlegGap : ∀ j, j < F.top → ∀ y ∈ sitesOfCells D (j + 1), ∀ h ∈ centredCube F.blockSide,
      ∀ π : Equiv.Perm (Fin 4),
      _root_.YangMills.Construction.BlockAverages.distFromOne (pathHolonomy (gaugeTransform (pinnedGaugeLevel W kW X k γ j) (X j)) (refineSite y) (axisPath h π) *
        (pathHolonomy (W j) (refineSite y) (axisPath h π))⁻¹) ≤ t j y := by
    intro j hj y hy h hh π
    have hj1 : j + 1 ≤ F.top := hj
    have hstep : ∀ u s, u ∈ centredCube F.blockSide →
        u + FlatPairing.stepDisplacement s ∈ centredCube F.blockSide →
        _root_.YangMills.Construction.BlockAverages.distFromOne (linkQuotient (gaugeTransform (pinnedGaugeLevel W kW X k γ j) (X j)) (W j)
          (refineSite y + siteOfCoords j u) s) ≤ τ j y := by
      intro u s hu hv
      have hbound : ∀ (a : LatticeFractionalIntegration.Lattice4) (i : Fin 4), a ∈ centredCube F.blockSide →
          a + LatticeFractionalIntegration.basisVector i ∈ centredCube F.blockSide →
          _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform (pinnedGaugeLevel W kW X k γ j) (X j) (refineSite y + siteOfCoords j a) i *
            (W j (refineSite y + siteOfCoords j a) i)⁻¹) ≤ τ j y := by
        intro a i ha hb
        have m1 := ChartCoordinates.refineSite_add_mem_sitesOfCells hodd hj1 hy ha
        have m2 := ChartCoordinates.refineSite_add_mem_sitesOfCells hodd hj1 hy hb
        have hbd : (refineSite y + siteOfCoords j a, i) ∈ innerBonds D j := by
          refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨m1, Finset.mem_univ _⟩, ?_⟩
          have e : refineSite y + siteOfCoords j a + unitStep j i =
              refineSite y + siteOfCoords j (a + LatticeFractionalIntegration.basisVector i) := by
            rw [siteOfCoords_add, unitStep_eq, add_assoc]
          show refineSite y + siteOfCoords j a + unitStep j i ∈ _
          rw [e]
          exact m2
        have h1 : _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X Γ j (refineSite y + siteOfCoords j a) i) ^ 4 ≤
            G j (refineSite y + siteOfCoords j a) := by
          have := Finset.single_le_sum (f := fun i' : Fin 4 =>
            if (refineSite y + siteOfCoords j a, i') ∈ innerBonds D j then
            _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X Γ j (refineSite y + siteOfCoords j a) i') ^ 4 else 0)
            (fun i' _ => by split_ifs <;> positivity) (Finset.mem_univ i)
          simpa [hbd] using this
        have h2 : G j (refineSite y + siteOfCoords j a) ≤ Tq j y :=
          Finset.single_le_sum (f := fun a => G j (refineSite y + siteOfCoords j a)) (fun _ _ => hG0 _ _) ha
        have h3 : _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X Γ j (refineSite y + siteOfCoords j a) i) ^ 4 ≤ τ j y ^ 4 := by
          rw [hτ4]
          exact h1.trans h2
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hτ0 j y) (by norm_num)).1 h3
      obtain ⟨i, b⟩ := s
      cases b with
      | true =>
        rw [linkQuotient_forward]
        exact hbound u i hu (by simpa [FlatPairing.stepDisplacement] using hv)
      | false =>
        rw [_root_.YangMills.Construction.BlockAverages.CellGenerators.distFromOne_linkQuotient_backward]
        have e : refineSite y + siteOfCoords j u - unitStep j i =
            refineSite y + siteOfCoords j (u + FlatPairing.stepDisplacement (i, false)) := by
          have : FlatPairing.stepDisplacement (i, false) = - LatticeFractionalIntegration.basisVector i := by
            simp [FlatPairing.stepDisplacement]
          rw [this, siteOfCoords_add, siteOfCoords_neg, unitStep_eq]
          abel
        rw [e]
        refine hbound _ i hv ?_
        have : u + FlatPairing.stepDisplacement (i, false) + LatticeFractionalIntegration.basisVector i = u := by
          simp [FlatPairing.stepDisplacement]
        rwa [this]
    have hpath : LatticePaths.AllAlong (fun v => v ∈ centredCube F.blockSide) 0 (axisPath h π) := by
      refine LatticePaths.allAlong_mono (fun v hv => ?_) (LatticePaths.axisPath_spec h π).1
      refine (LatticePaths.mem_centredCube_iff _ _).2 fun μ => ?_
      have h1 := ((LatticePaths.mem_centredCube_iff _ _).1 hh) μ
      have h2 := hv μ
      have a1 : min 0 (h μ) ≥ -(((F.blockSide : ℤ) - 1) / 2) := le_min (by omega) h1.1
      have a2 : max 0 (h μ) ≤ ((F.blockSide : ℤ) - 1) / 2 := max_le (by omega) h1.2
      omega
    have h1 := _root_.YangMills.Construction.BlockAverages.CellGenerators.distFromOne_pathQuotient_le (gaugeTransform (pinnedGaugeLevel W kW X k γ j) (X j)) (W j)
      (refineSite y) (fun v => v ∈ centredCube F.blockSide) (τ j y) (hτ0 j y) hstep (axisPath h π) 0 hpath
    rw [ChartCoordinates.add_siteOfCoords_zero] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right (BondHull.length_axisPath_le hh π) (hτ0 j y)
  set e := 36 * (F.blockSide : ℝ) * q + 8 * r with he
  have he0 : 0 ≤ e := by positivity
  let β : (j : ℕ) → F.Site (j + 1) → ℝ := fun j y => 9 * t j y + 4 * E j y
  have hβ0 : ∀ j y, 0 ≤ β j y := fun j y => by
    have := ht0 j y
    have := hE0 j y
    positivity
  have hβs : ∀ j, j < F.top → ∑ y ∈ sitesOfCells ({y₀} : Finset F.Cell) (j + 1), β j y ^ 4 ≤ e ^ 4 := by
    intro j hj
    have h1 : ∑ y ∈ sitesOfCells ({y₀} : Finset F.Cell) (j + 1), E j y ^ 4 ≤ r ^ 4 :=
      (Finset.sum_le_sum_of_subset_of_nonneg (sitesOfCells_mono hsub (j + 1)) fun _ _ _ => by
        have := hE0 j ‹_›
        positivity).trans (hEs j hj)
    have h2 := hTsum j hj
    have e1 : ∀ y, (9 * t j y) ^ 4 = (18 * (F.blockSide : ℝ)) ^ 4 * Tq j y := fun y => by
      rw [← hτ4]
      show (9 * (2 * (F.blockSide : ℝ) * τ j y)) ^ 4 = _
      ring
    have h3 : ∑ y ∈ sitesOfCells ({y₀} : Finset F.Cell) (j + 1), β j y ^ 4 ≤
        8 * ((18 * (F.blockSide : ℝ)) ^ 4 * q ^ 4 + 4 ^ 4 * r ^ 4) := by
      calc ∑ y ∈ sitesOfCells ({y₀} : Finset F.Cell) (j + 1), β j y ^ 4
          ≤ ∑ y ∈ sitesOfCells ({y₀} : Finset F.Cell) (j + 1),
            8 * ((18 * (F.blockSide : ℝ)) ^ 4 * Tq j y + 4 ^ 4 * E j y ^ 4) := by
            refine Finset.sum_le_sum fun y _ => ?_
            refine (add_pow_four_le _ _).trans (le_of_eq ?_)
            rw [e1]
            ring
        _ = 8 * ((18 * (F.blockSide : ℝ)) ^ 4 * ∑ y ∈ sitesOfCells ({y₀} : Finset F.Cell) (j + 1), Tq j y +
            4 ^ 4 * ∑ y ∈ sitesOfCells ({y₀} : Finset F.Cell) (j + 1), E j y ^ 4) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ _ := by gcongr
    refine h3.trans ?_
    have ha : 0 ≤ 18 * (F.blockSide : ℝ) * q := by positivity
    have hb : 0 ≤ 4 * r := by positivity
    have e2 : e = 2 * (18 * (F.blockSide : ℝ) * q + 4 * r) := by rw [he]; ring
    rw [e2]
    have e3 : 8 * ((18 * (F.blockSide : ℝ)) ^ 4 * q ^ 4 + 4 ^ 4 * r ^ 4) =
        8 * ((18 * (F.blockSide : ℝ) * q) ^ 4 + (4 * r) ^ 4) := by ring
    rw [e3]
    set a := 18 * (F.blockSide : ℝ) * q
    set b := 4 * r
    have e4 : (2 * (a + b)) ^ 4 = 16 * (a + b) ^ 4 := by ring
    rw [e4]
    have h4 : a ^ 4 + b ^ 4 ≤ (a + b) ^ 4 := by
      have : (a + b) ^ 4 - (a ^ 4 + b ^ 4) = 4 * a ^ 3 * b + 6 * a ^ 2 * b ^ 2 + 4 * a * b ^ 3 := by ring
      have h5 : 0 ≤ 4 * a ^ 3 * b + 6 * a ^ 2 * b ^ 2 + 4 * a * b ^ 3 := by positivity
      linarith
    have h6 : 0 ≤ (a + b) ^ 4 := by positivity
    linarith
  let f : (j : ℕ) → F.Site j → ℍ[ℝ] := fun j x => adjointAction (patchFrame S V z x)⁻¹ (gen j x)
  have hfn : ∀ j x, ‖f j x‖ = ‖gen j x‖ := fun j x => PatchForms.norm_adjointAction_apply _ _
  have hrec : ∀ j, j < F.top → ∀ y ∈ sitesOfCells ({y₀} : Finset F.Cell) (j + 1),
      ‖f (j + 1) y - (1 / (F.blockSide : ℝ) ^ 4) • ∑ h ∈ centredCube F.blockSide, f j (refineSite y + siteOfCoords j h)‖ ≤
        β j y * ((1 / (F.blockSide : ℝ) ^ 4) *
          ∑ h ∈ centredCube F.blockSide, ‖f j (refineSite y + siteOfCoords j h)‖) := by
    intro j hj y hy
    have hj1 : j + 1 ≤ F.top := hj
    have hyD := sitesOfCells_mono hsub (j + 1) hy
    have hτq : τ j y ≤ q := by
      have h1 : Tq j y ≤ q ^ 4 := (Finset.single_le_sum (f := fun y => Tq j y)
        (fun y _ => hTq0 j y) hy).trans (hTsum j hj)
      rw [← hτ4] at h1
      exact (pow_le_pow_iff_left₀ (hτ0 j y) hq (by norm_num)).1 h1
    have htc : t j y ≤ 1 / 8 := by
      have h1 : t j y ≤ 2 * (F.blockSide : ℝ) * q := mul_le_mul_of_nonneg_left hτq (by positivity)
      have h2 : 0 ≤ (F.blockSide : ℝ) * q := by positivity
      have h3 : 0 ≤ r := hr
      nlinarith
    have hb : ∀ {h : LatticeFractionalIntegration.Lattice4}, h ∈ centredCube F.blockSide →
        refineSite y + siteOfCoords j h ∈ sitesOfCells D j :=
      fun hh => ChartCoordinates.refineSite_add_mem_sitesOfCells hodd hj1 hyD hh
    have h1 := hNear F j (pinnedGaugeLevel W kW X k γ j) (X j) (W j) (kW (j + 1) y) (gen j)
      (fun x => patchFrame S V z x) y (t j y) (E j y) hodd (ht0 j y) htc (hE0 j y) (hlegGap j hj y hyD)
      (hk j hj y hyD) (hleg j hj y hyD) (fun h hh => (hlev j hj _ (hb hh)).1)
    have e1 : patchFrame S V z y = patchFrame S V z (refineSite y) := by
      unfold patchFrame
      rw [baseSite_refineSite j hj1]
    have e2 : ∀ h, ‖f j (refineSite y + siteOfCoords j h)‖ = ‖gen j (refineSite y + siteOfCoords j h)‖ :=
      fun h => hfn _ _
    simp only [e2]
    show ‖adjointAction (patchFrame S V z y)⁻¹
      (coarseGenerator (pinnedGaugeLevel W kW X k γ j) (X j) (W j) (kW (j + 1) y) (gen j) y) - _‖ ≤ _
    rw [e1]
    exact h1
  have hfin := hComp F y₀ f β e hodd h5 he0 he8 hβ0 hβs hrec
  have e0 : ∀ x : F.Site 0, f 0 x = adjointAction (GaugeMap.frameChange S V z x)⁻¹ (ξ x : ℍ[ℝ]) := by
    intro x
    show adjointAction (GaugeMap.frameChange S V z (baseSite x))⁻¹ _ = _
    rw [PatchForms.baseSite_depth_zero]
    rfl
  have e5 : ∀ x, ‖f 0 x‖ = ‖(ξ x : ℍ[ℝ])‖ := fun x => hfn 0 x
  have e6 : ∑ h ∈ centredCube (F.blockSide ^ F.top), f 0 (cellCentre 0 y₀ + siteOfCoords 0 h) =
      ∑ h ∈ centredCube (F.blockSide ^ F.top),
        adjointAction (GaugeMap.frameChange S V z (cellCentre 0 y₀ + siteOfCoords 0 h))⁻¹
          (ξ (cellCentre 0 y₀ + siteOfCoords 0 h) : ℍ[ℝ]) :=
    Finset.sum_congr rfl fun h _ => e0 _
  have e7 : ∑ x ∈ sitesOfCells ({y₀} : Finset F.Cell) 0, ‖f 0 x‖ ^ 4 =
      ∑ x ∈ sitesOfCells ({y₀} : Finset F.Cell) 0, ‖(ξ x : ℍ[ℝ])‖ ^ 4 :=
    Finset.sum_congr rfl fun x _ => by rw [e5]
  rw [e6, e7] at hfin
  exact hfin
end YangMills.Construction.BlockAverages.CellGenerators
end
