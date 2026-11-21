import YangMills.Construction.ColdChainAtEveryLevel.GaugeCovarianceOfAContour
import YangMills.Construction.HoleBesideASecondHole.ContoursOfABondAreMostlyGood
import YangMills.Construction.HoleBesideASecondHole.CountsNearACut
import YangMills.Construction.HoleBesideASecondHole.DistancesBlocksAndLumps
import YangMills.Construction.HoleBesideASecondHole.ElementsOnCellsLieOverThem
import YangMills.Construction.HoleBesideASecondHole.FitOfANearMean
import YangMills.Construction.HoleBesideASecondHole.LeastSumsOfTheLevels
import YangMills.Construction.HoleBesideASecondHole.LegsAndMeans
import YangMills.Construction.HoleBesideASecondHole.MeansAtACoreBond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours HoleSavings Holes PathHolonomy GroupMeans BondMeans CoreBondMeans
  SquareDescent ChainGauges ChainEnergies BondContours HoleFilling HoleBounds
namespace ContourMeans
variable {F : BlockFrame}
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem cellCentre_eq_refineSite (y : F.Cell) : cellCentre F.depth y = _root_.YangMills.Construction.BlockAverages.refineSite y := by
  funext k
  simp only [cellCentre, _root_.YangMills.Construction.BlockAverages.refineSite, siteOfCoords, top_sub_depth, pow_one]
theorem mem_cutBelow {X : Finset F.Cell} {u : F.Cell} {x : F.Site F.depth} (hu : u ∈ X)
    (hx : x ∈ sitesBelow F.depth u) : x ∈ cutBelow F.depth X := by
  unfold cutBelow
  exact Finset.mem_biUnion.2 ⟨u, hu, hx⟩
theorem cutBelow_mono {X Y : Finset F.Cell} (h : X ⊆ Y) : cutBelow F.depth X ⊆ cutBelow F.depth Y := by
  unfold cutBelow
  exact Finset.biUnion_subset_biUnion_of_subset_left _ h
theorem exists_mem_of_mem_cutBelow {X : Finset F.Cell} {x : F.Site F.depth} (hx : x ∈ cutBelow F.depth X) :
    ∃ u ∈ X, x ∈ sitesBelow F.depth u := by
  unfold cutBelow at hx
  exact Finset.mem_biUnion.1 hx
theorem cellSupDist_self (y : F.Cell) : cellSupDist y y = 0 := by
  simp [cellSupDist]
theorem offsetInBlock_zero (hL : Odd F.blockSide) : OffsetInBlock F.blockSide 0 := by
  intro m
  obtain ⟨k, hk⟩ := hL
  simp only [Pi.zero_apply, abs_zero]
  rw [hk]
  push_cast
  omega
theorem mem_cutBonds_of_subset {j : ℕ} {A B : Finset (F.Site j)} (h : A ⊆ B) {b : F.Site j × Fin 4}
    (hb : b ∈ cutBonds A) : b ∈ cutBonds B := by
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hb
  obtain ⟨a, c⟩ := Finset.mem_product.1 h1
  exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h a, c⟩, h h2⟩
theorem cutBonds_ends_mem {j : ℕ} {A : Finset (F.Site j)} {b : F.Site j × Fin 4} (hb : b ∈ cutBonds A) :
    b.1 ∈ A ∧ b.1 + unitStep j b.2 ∈ A := by
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hb
  exact ⟨(Finset.mem_product.1 h1).1, h2⟩
theorem minimalOffset_add_siteOfCoords (hL : Odd F.blockSide) (hS : ∀ i, 64 ≤ F.extent i)
    (x : F.Site F.depth) {o : Fin 4 → ℤ} (ho : o ∈ centredCube F.blockSide) :
    minimalOffset x (x + siteOfCoords F.depth o) = o := by
  funext i
  have hpos := hL.pos
  have hs := hS i
  have hper : F.period F.depth i = F.extent i * F.blockSide := by simp [BlockFrame.period, top_sub_depth]
  have hp : (64 : ℤ) * F.blockSide ≤ (F.period F.depth i : ℤ) := by
    rw [hper]
    push_cast
    have : (64 : ℤ) ≤ F.extent i := by exact_mod_cast hs
    nlinarith
  haveI : NeZero (F.period F.depth i) := ⟨by
    intro h0
    rw [h0] at hp
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hpos
    simp at hp
    omega⟩
  have a2 := abs_le.1 (offsetInBlock_of_mem_centredCube ho i)
  have e : (x + siteOfCoords F.depth o - x : F.Site F.depth) i = ((o i : ℤ) : ZMod (F.period F.depth i)) := by
    simp [siteOfCoords]
  show ((x + siteOfCoords F.depth o - x : F.Site F.depth) i).valMinAbs = o i
  rw [e]
  refine (ZMod.valMinAbs_spec _ _).2 ⟨rfl, ?_⟩
  obtain ⟨k, hk⟩ := hL
  have hhalf : ((F.blockSide : ℤ) - 1) / 2 = k := by
    rw [hk]
    push_cast
    omega
  rw [hhalf] at a2
  simp only [Set.mem_Ioc]
  constructor <;> omega
theorem norm_smul_polarPart (q : ℍ[ℝ]) : (‖q‖ : ℝ) • ((polarPart q : UnitQuaternion) : ℍ[ℝ]) = q := by
  by_cases h : q = 0
  · simp [h]
  · have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 h
    simp only [polarPart, dif_neg h]
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
theorem norm_polarPart_sub_le (x y : ℍ[ℝ]) (hx : 1 / 2 ≤ ‖x‖) :
    ‖((polarPart x : UnitQuaternion) : ℍ[ℝ]) - (polarPart y : UnitQuaternion)‖ ≤ 4 * ‖x - y‖ := by
  set ux := ((polarPart x : UnitQuaternion) : ℍ[ℝ]) with hux
  set uy := ((polarPart y : UnitQuaternion) : ℍ[ℝ]) with huy
  have e1 : (‖x‖ : ℝ) • ux = x := norm_smul_polarPart x
  have e2 : (‖y‖ : ℝ) • uy = y := norm_smul_polarPart y
  have e3 : (‖x‖ : ℝ) • (ux - uy) = (x - y) + (‖y‖ - ‖x‖ : ℝ) • uy := by
    rw [smul_sub, e1, sub_smul, e2]
    abel
  have hn : ‖(‖x‖ : ℝ) • (ux - uy)‖ = ‖x‖ * ‖ux - uy‖ := by
    rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
  have hu : ‖uy‖ = 1 := unitQuaternion_norm _
  have h1 : ‖x‖ * ‖ux - uy‖ ≤ 2 * ‖x - y‖ := by
    rw [← hn, e3]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs]
    have := abs_norm_sub_norm_le y x
    rw [norm_sub_rev y x] at this
    linarith
  have h0 := norm_nonneg (ux - uy)
  nlinarith
theorem norm_mul_mul_unitQuaternion (u v : UnitQuaternion) (x : ℍ[ℝ]) :
    ‖(u : ℍ[ℝ]) * x * (v : ℍ[ℝ])‖ = ‖x‖ := by
  rw [norm_mul, norm_mul, unitQuaternion_norm, unitQuaternion_norm]
  ring
theorem pathHolonomy_congr {j : ℕ} (X Y : F.GaugeField j) (Q : Finset (F.Site j))
    (h : ∀ b ∈ cutBonds Q, X b.1 b.2 = Y b.1 b.2) (P : List PathStep) (x : F.Site j)
    (hp : ∀ z ∈ pathSites x P, z ∈ Q) : pathHolonomy X x P = pathHolonomy Y x P := by
  have hsn : LinksClose X Y ∅ Q 0 := by
    refine linksClose_of_cutBonds X Y ∅ Q 0 (fun b hb => ?_) (fun b hb _ _ => h b hb)
    rw [h b hb]
    simp
  have h0 := norm_pathHolonomy_sub_le X Y ∅ Q 0 le_rfl hsn P x hp
  rw [zero_mul] at h0
  have h1 : ‖((pathHolonomy X x P : UnitQuaternion) : ℍ[ℝ]) - (pathHolonomy Y x P : UnitQuaternion)‖ = 0 :=
    le_antisymm h0 (norm_nonneg _)
  exact Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 h1))
theorem meanDirection_eq_one {E : Type} (I : Finset E) (hI : I.Nonempty) (f : E → UnitQuaternion)
    (hf : ∀ e ∈ I, f e = 1) : meanDirection I f = 1 := by
  have hc : (I.card : ℝ) ≠ 0 := by
    have : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
    exact this.ne'
  have e : quatAverage I (fun e => (f e : ℍ[ℝ])) = 1 := by
    unfold quatAverage
    have : ∑ e ∈ I, (f e : ℍ[ℝ]) = ∑ _e ∈ I, (1 : ℍ[ℝ]) := Finset.sum_congr rfl fun e he => by
      rw [hf e he]
      rfl
    rw [this, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [one_div, inv_mul_cancel₀ hc, one_smul]
  unfold meanDirection
  rw [e]
  apply Subtype.ext
  have h1 : (1 : ℍ[ℝ]) ≠ 0 := one_ne_zero
  simp [polarPart, h1]
theorem quatAverage_allContours (X : F.GaugeField F.depth) (c : F.Cell × Fin 4) (hL : Odd F.blockSide) :
    quatAverage (allContours F) (fun e => (contourHolonomy X c e : ℍ[ℝ])) = _root_.YangMills.Construction.BlockAverages.contourAverage X c := by
  have hc : (allContours F).card = F.blockSide ^ 4 * 24 := by
    simp [allContours, card_centredCube hL, Finset.card_product, Finset.card_univ, Fintype.card_perm,
      Nat.factorial]
  unfold quatAverage _root_.YangMills.Construction.BlockAverages.contourAverage
  rw [hc]
  have e1 : ∑ e ∈ allContours F, ((contourHolonomy X c e : UnitQuaternion) : ℍ[ℝ]) =
      ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy X (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) := by
    unfold allContours
    rw [Finset.sum_product]
    rfl
  rw [e1]
  congr 1
  push_cast
  ring_nf
theorem norm_quatAverage_le_one {E : Type} (I : Finset E) (hI : I.Nonempty) (f : E → UnitQuaternion) :
    ‖quatAverage I fun e => (f e : ℍ[ℝ])‖ ≤ 1 := by
  unfold quatAverage
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖∑ e ∈ I, (f e : ℍ[ℝ])‖ ≤ I.card := by
    refine (norm_sum_le _ _).trans ?_
    simp only [unitQuaternion_norm]
    simp
  calc 1 / (I.card : ℝ) * ‖∑ e ∈ I, (f e : ℍ[ℝ])‖ ≤ 1 / (I.card : ℝ) * I.card :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 := by field_simp
open Classical in
theorem excludedBoxes_eq_empty (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell)
    (hy : nearbyLumps h y = ∅) : excludedBoxes J₀ h y = ∅ := by
  unfold excludedBoxes
  by_cases hcr : IsCrowded J₀ h y
  · rw [if_pos hcr]
  · rw [if_neg hcr, hy, Finset.image_empty]
    unfold mergedBoxes
    by_cases hz : ∃ Z : Finset (Finset (F.Site F.depth)), IsLeastSeparatedCover ∅ Z
    · rw [dif_pos hz]
      have hs := hz.choose_spec
      have hc : IsSeparatedCover (F := F) (j := F.depth) ∅ (∅ : Finset (Finset (F.Site F.depth))) := by
        refine ⟨?_, ?_, ?_⟩ <;> simp
      refine Finset.eq_empty_of_forall_notMem fun B hB => ?_
      obtain ⟨B', hB', _⟩ := hs.2 ∅ hc B hB
      simp at hB'
    · rw [dif_neg hz]
theorem cutChainEnergy_update_top (a : ℝ) (Y : Finset (F.Site F.depth)) (U : F.FieldChain)
    (V : F.GaugeField F.top) :
    cutChainEnergy a F.depth Y (Function.update U F.top V) = cutChainEnergy a F.depth Y U := by
  unfold cutChainEnergy
  have h0 : Function.update U F.top V 0 = U 0 := Function.update_of_ne (by simp [BlockFrame.top]) _ _
  rw [h0]
  have hs : ∀ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) Y),
      blockFit (Function.update U F.top V i) (Function.update U F.top V (i + 1)) c =
      ∑ c ∈ cutBonds (cutBelow (i + 1) Y), blockFit (U i) (U (i + 1)) c := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have h1 : Function.update U F.top V i = U i :=
      Function.update_of_ne (by simp [BlockFrame.top]; omega) _ _
    have h2 : Function.update U F.top V (i + 1) = U (i + 1) :=
      Function.update_of_ne (by simp [BlockFrame.top]; omega) _ _
    rw [h1, h2]
  rw [Finset.sum_congr rfl hs]
theorem card_cellBall_le (z : F.Cell) (r : ℕ) : (_root_.YangMills.Construction.LumpContours.cellBall z r).card ≤ (2 * r + 1) ^ 4 := by
  refine Finset.card_image_le.trans ?_
  rw [card_centredCube (⟨r, rfl⟩ : Odd (2 * r + 1))]
end ContourMeans
attribute [local irreducible] _root_.YangMills.Construction.LumpContours.cellBall
namespace ContourMeans
theorem re_le_norm (q : ℍ[ℝ]) : q.re ≤ ‖q‖ := by
  have h1 := Quaternion.normSq_eq_norm_mul_self q
  have h2 : q.re * q.re ≤ Quaternion.normSq q := by
    rw [Quaternion.normSq_def']
    nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK]
  have h3 := norm_nonneg q
  by_contra hlt
  push_neg at hlt
  nlinarith
open Classical in
set_option maxHeartbeats 16000000 in
theorem exists_meanMatchingChain (hT : GaugeChainPreservesEnergy) (hCB : CoreBondMeanEstimate)
    (hCN : countsNearCutStatement) (hEO : energyOnLeEnergyOverStatement)
    (hFit : NearMeanFitEstimate) (hG : MostContoursGoodStatement)
    (hD : TorusDistanceBlockLumpFacts) (hLS : minimalChainEnergiesStatement)
    (hGC : gaugeCovarianceStatement)
    (F : BlockFrame) (g : LumpGrid F.blockSide) (a s θ C C₀ CJb CJ ε Dn ρ : ℝ) (J₀ : ℕ)
    (D : HoleData F g a s θ J₀)
    (idx : Finset (Finset (F.Site F.depth)) → ℕ) (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth)
    (U2 : F.FieldChain) (Wt : F.GaugeField F.depth) (γ : F.Site F.depth → UnitQuaternion)
    (ha : 1 ≤ a) (hs : 0 < s) (hC : 0 < C) (hC₀ : 0 < C₀) (hCJb : 0 < CJb) (hJ : 1 ≤ J₀)
    (hL : Odd F.blockSide)
    (hTor : IsCubicTorus F 4096) (hbox : excludedBoxSide J₀ < F.blockSide)
    (hbox3 : 8 * (2 * excludedBoxSide J₀) ^ 3 < F.blockSide ^ 3)
    (hS : D.IsHoleFamily C idx o) (hFi : D.IsHoleFillingChain C C₀ idx o U2)
    (hB : D.IsBoxFilling C CJb idx o U2 Wt γ)
    (hη : coreOscillation F.blockSide J₀ C C₀ CJb s ≤ 1 / 8)
    (hD0 : 2 * ((J₀ * Nat.sqrt F.blockSide : ℕ) : ℝ) ^ 4 * (CJb * Real.sqrt F.blockSide * s) /
          (F.blockSide : ℝ) ^ 3 +
          12 * coreOscillation F.blockSide J₀ C C₀ CJb s ^ 2 +
          14 * coreOscillation F.blockSide J₀ C C₀ CJb s *
            (8 * (2 * excludedBoxSide J₀ : ℝ) ^ 3 / (F.blockSide : ℝ) ^ 3) ≤ Dn / 8)
    (hη2 : coreOscillation F.blockSide J₀ C C₀ CJb s ^ 2 ≤ Dn / 8)
    (hDn0 : 0 ≤ Dn) (hDn : Dn ≤ 1 / 8) (hDnCJ : Dn ≤ CJ * s / Real.sqrt F.blockSide) (hρ0 : 0 ≤ ρ)
    (hfitn : ∀ f : ℝ, 0 ≤ f → f ≤ C * s ^ 2 → f * (1 + 2 * Dn) + 2 * Dn * Real.sqrt f + Dn ^ 2 ≤ f + ρ)
    (hA0 : 0 ≤ C₀ * C * s ^ 2 / ((topScaleIndex J₀ F.blockSide : ℝ) - J₀))
    (hn1 : C₀ * C * s ^ 2 / ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) + a * ρ * 9604 ≤ ε * s ^ 2)
    (hn2 : C * s ^ 2 + C₀ * C * s ^ 2 / ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) * J₀ + a * ρ * 324 ≤
      CJ * s ^ 2) :
    ∃ U3 : F.FieldChain, D.IsMeanMatchingChain C CJ ε U3 := by
  have hside : ∀ k, 64 ≤ F.extent k := fun k => by
    have h1 := hTor.1 k
    have h2 := hTor.2
    omega
  have hs0 : ∀ k, 0 < F.extent k := fun k => by
    have := hside k
    omega
  have hLpos := hL.pos
  have hj : F.depth < F.top := by simp [BlockFrame.top]
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨dcomm, dtri, denl, dunder, dcell, ctri, ccomm, cball, dlump⟩ := hD F hLpos hs0
  set Wp := gaugeChain γ U2 F.depth with hWp
  set gc : F.Cell → UnitQuaternion := cellRotation Wt Wp D.base with hgc
  let gam : F.Site F.depth → UnitQuaternion := fun x =>
    if x = _root_.YangMills.Construction.BlockAverages.refineSite (enclosingCell x) ∧ enclosingCell x ∈ D.coreCells C 5 then gc (enclosingCell x) else 1
  let U' : F.FieldChain := gaugeChain gam (gaugeChain γ U2)
  let U3 : F.FieldChain := Function.update U' F.top D.topField
  obtain ⟨t1, t2, t3⟩ := hT F gam (gaugeChain γ U2) hLpos hs0
  have hU3t : U3 F.depth = _root_.YangMills.Construction.BlockAverages.gaugeTransform gam Wp :=
    (Function.update_of_ne (by simp [BlockFrame.top]) _ _).trans t1
  have hU3n : U3 F.top = D.topField := Function.update_self _ _ _
  have hcost : ∀ Y : Finset (F.Site F.depth), cutChainEnergy a F.depth Y U3 = cutChainEnergy a F.depth Y U2 := by
    intro Y
    rw [cutChainEnergy_update_top]
    exact (t3 a Y).trans (hB.cutChainEnergy_eq Y)
  have hcore : ∀ {x : F.Site F.depth}, x ∈ cutBelow F.depth (D.coreCells C 5) →
      enclosingCell x ∈ D.coreCells C 5 ∧ x ∈ sitesBelow F.depth (enclosingCell x) := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := exists_mem_of_mem_cutBelow hx
    have e : enclosingCell x = u := (dunder hL x u).1 hxu
    rw [e]
    exact ⟨hu, hxu⟩
  have hqbond : ∀ b ∈ cutBonds (cutBelow F.depth (D.coreCells C 5)),
      nearbyLumps D.hotFineLumps (enclosingCell b.1) = ∅ →
      nearbyLumps D.hotFineLumps (enclosingCell (b.1 + unitStep F.depth b.2)) = ∅ →
      Wp b.1 b.2 = D.fineField b.1 b.2 ∧ Wt b.1 b.2 = D.fineField b.1 b.2 := by
    intro b hb q1 q2
    obtain ⟨e1, e2⟩ := cutBonds_ends_mem hb
    obtain ⟨u1, v1⟩ := hcore e1
    obtain ⟨u2, v2⟩ := hcore e2
    have off : ∀ {x : F.Site F.depth}, x ∈ sitesBelow F.depth (enclosingCell x) →
        enclosingCell x ∈ D.coreCells C 5 →
        nearbyLumps D.hotFineLumps (enclosingCell x) = ∅ → x ∉ holeSupport (D.holesAt C idx o) := by
      intro x hx hc hq hh
      obtain ⟨H, hH, hxH⟩ := Finset.mem_biUnion.1 hh
      have h0 := (hB.disjoint_of_nearbyLumps_empty _ hc hq).1 H hH
      have : x ∈ H.outerBox ∩ sitesBelow F.depth (enclosingCell x) := Finset.mem_inter.2 ⟨hxH, hx⟩
      rw [h0] at this
      simp at this
    have g1 := off v1 u1 q1
    have g2 := off v2 u2 q2
    obtain ⟨a1, a2⟩ := hB.eq_off_holes b hb g1 g2
    refine ⟨?_, a1⟩
    have t0 : Wp = _root_.YangMills.Construction.BlockAverages.gaugeTransform γ (U2 F.depth) := hB.gaugeChain_top
    rw [t0]
    simp only [gaugeTransform]
    rw [hB.gauge_eq_one _ g1, hB.gauge_eq_one _ g2, a2]
    simp
  have hgc1 : ∀ y ∈ D.coreCells C 5, nearbyLumps D.hotFineLumps y = ∅ → gc y = 1 := by
    intro y hy q
    have hby : D.base y = cellCentre F.depth y := (D.isBaseChoice y).1 (Or.inl q)
    have hbond : ∀ b ∈ cutBonds (sitesBelow F.depth y), Wt b.1 b.2 = Wp b.1 b.2 := by
      intro b hb
      obtain ⟨e1, e2⟩ := cutBonds_ends_mem hb
      have c1 : enclosingCell b.1 = y := (dunder hL _ y).1 e1
      have c2 : enclosingCell (b.1 + unitStep F.depth b.2) = y := (dunder hL _ y).1 e2
      have hsub : sitesBelow F.depth y ⊆ cutBelow F.depth (D.coreCells C 5) := fun x hx => mem_cutBelow hy hx
      obtain ⟨p1, p2⟩ := hqbond b (mem_cutBonds_of_subset hsub hb) (by rw [c1]; exact q) (by rw [c2]; exact q)
      rw [p1, p2]
    refine meanDirection_eq_one _ ⟨(0, 1), Finset.mem_product.2 ⟨by
      refine mem_centredCube_of_offsetInBlock (offsetInBlock_zero hL), Finset.mem_univ _⟩⟩ _ fun e he => ?_
    have hξ : e.1 ∈ centredCube F.blockSide := (Finset.mem_product.1 he).1
    unfold legRotation baseLeg
    rw [hby, cellCentre_eq_refineSite, minimalOffset_add_siteOfCoords hL hside _ hξ]
    have hin : ∀ z ∈ pathSites (_root_.YangMills.Construction.BlockAverages.refineSite y) (axisPath e.1 e.2), z ∈ sitesBelow F.depth y := by
      intro z hz
      have h := axisPath_sites_mem_sitesBelow F.depth y (offsetInBlock_zero hL)
        (offsetInBlock_of_mem_centredCube hξ) e.2
      simp only [_root_.YangMills.Construction.PathHolonomy.siteOfCoords_zero, add_zero, sub_zero] at h
      exact h z hz
    rw [pathHolonomy_congr Wt Wp _ hbond _ _ hin]
    group
  have hgdown : ∀ y ∈ D.coreCells C 5, gam (_root_.YangMills.Construction.BlockAverages.refineSite y) = gc y := by
    intro y hy
    have hmem : _root_.YangMills.Construction.BlockAverages.refineSite y ∈ sitesBelow F.depth y := by
      have := refineSite_add_mem_sitesBelow F.depth y (offsetInBlock_zero hL)
      simpa [_root_.YangMills.Construction.PathHolonomy.siteOfCoords_zero] using this
    have e : enclosingCell (_root_.YangMills.Construction.BlockAverages.refineSite y) = y := (dunder hL _ y).1 hmem
    show (if _root_.YangMills.Construction.BlockAverages.refineSite y = _root_.YangMills.Construction.BlockAverages.refineSite (enclosingCell (_root_.YangMills.Construction.BlockAverages.refineSite y)) ∧
        enclosingCell (_root_.YangMills.Construction.BlockAverages.refineSite y) ∈ D.coreCells C 5 then gc (enclosingCell (_root_.YangMills.Construction.BlockAverages.refineSite y)) else 1) = gc y
    rw [e]
    exact if_pos ⟨rfl, hy⟩
  have hgam1 : ∀ x : F.Site F.depth, nearbyLumps D.hotFineLumps (enclosingCell x) = ∅ → gam x = 1 := by
    intro x q
    simp only [gam]
    split_ifs with h
    · exact hgc1 _ h.2 q
    · rfl
  have hW2 : ∀ b ∈ cutBonds (cutBelow F.depth (D.coreCells C 5)),
      nearbyLumps D.hotFineLumps (enclosingCell b.1) = ∅ →
      nearbyLumps D.hotFineLumps (enclosingCell (b.1 + unitStep F.depth b.2)) = ∅ →
      _root_.YangMills.Construction.BlockAverages.gaugeTransform gam Wp b.1 b.2 = D.fineField b.1 b.2 := by
    intro b hb q1 q2
    simp only [gaugeTransform]
    rw [hgam1 _ q1, hgam1 _ q2, (hqbond b hb q1 q2).1]
    simp
  have hquiet : ∀ c : F.Cell × Fin 4, c.1 ∈ D.coreCells C 5 → c.1 + unitStep F.top c.2 ∈ D.coreCells C 5 →
      nearbyLumps D.hotFineLumps c.1 = ∅ → nearbyLumps D.hotFineLumps (c.1 + unitStep F.top c.2) = ∅ →
      _root_.YangMills.Construction.BlockAverages.contourAverage (gaugeTransform gam Wp) c = contourMean J₀ D.hotFineLumps D.base D.fineField c := by
    intro c hc1 hc2 q1 q2
    obtain ⟨y, i⟩ := c
    simp only at hc1 hc2 q1 q2
    set y' := y + unitStep F.top i with hy'
    have hby : D.base y = cellCentre F.depth y := (D.isBaseChoice y).1 (Or.inl q1)
    have hby' : D.base y' = cellCentre F.depth y' := (D.isBaseChoice y').1 (Or.inl q2)
    have hz1 := excludedBoxes_eq_empty J₀ D.hotFineLumps y q1
    have hz2 := excludedBoxes_eq_empty J₀ D.hotFineLumps y' q2
    have hused : usedContours J₀ D.hotFineLumps D.base (y, i) = allContours F := by
      unfold usedContours
      split_ifs with hif
      · rfl
      · refine Finset.filter_true_of_mem fun e _ x _ B hB => ?_
        have : B ∈ excludedBoxes J₀ D.hotFineLumps y ∪ excludedBoxes J₀ D.hotFineLumps y' := hB
        rw [hz1, hz2] at this
        simp at this
    have hpath := (hG F J₀ 0 D.hotFineLumps D.base (y, i) hL hside D.isBaseChoice).1
    have hsteps : ∀ e ∈ allContours F,
        contourPath D.base (y, i) e.1 e.2 = bondContour F.blockSide e.1 e.2 i := by
      intro e he
      have hξ : e.1 ∈ centredCube F.blockSide := (Finset.mem_product.1 he).1
      unfold contourPath bondContour
      show axisPath (minimalOffset (D.base y) (cellCentre F.depth y + siteOfCoords F.depth e.1)) e.2 ++
        List.replicate F.blockSide (i, true) ++
        reversePath (axisPath (minimalOffset (D.base y') (cellCentre F.depth y' + siteOfCoords F.depth e.1)) e.2) = _
      rw [hby, hby', cellCentre_eq_refineSite, cellCentre_eq_refineSite,
        minimalOffset_add_siteOfCoords hL hside _ hξ, minimalOffset_add_siteOfCoords hL hside _ hξ]
    have hbonds : ∀ b ∈ cutBonds (sitesBelow F.depth y ∪ sitesBelow F.depth y'),
        _root_.YangMills.Construction.BlockAverages.gaugeTransform gam Wp b.1 b.2 = D.fineField b.1 b.2 := by
      intro b hb
      have hsub : sitesBelow F.depth y ∪ sitesBelow F.depth y' ⊆ cutBelow F.depth (D.coreCells C 5) :=
        Finset.union_subset (fun x hx => mem_cutBelow hc1 hx) (fun x hx => mem_cutBelow hc2 hx)
      have hq : ∀ {x : F.Site F.depth}, x ∈ sitesBelow F.depth y ∪ sitesBelow F.depth y' →
          nearbyLumps D.hotFineLumps (enclosingCell x) = ∅ := by
        intro x hx
        rcases Finset.mem_union.1 hx with h | h
        · rw [(dunder hL _ y).1 h]
          exact q1
        · rw [(dunder hL _ y').1 h]
          exact q2
      obtain ⟨e1, e2⟩ := cutBonds_ends_mem hb
      exact hW2 b (mem_cutBonds_of_subset hsub hb) (hq e1) (hq e2)
    have key : ∀ e ∈ allContours F,
        ((contourHolonomy (_root_.YangMills.Construction.BlockAverages.gaugeTransform gam Wp) (y, i) e : UnitQuaternion) : ℍ[ℝ]) =
        (pathHolonomy D.fineField (D.base y) (contourPath D.base (y, i) e.1 e.2) : UnitQuaternion) := by
      intro e he
      have hp := hpath e he
      simp only at hp
      rw [hsteps e he] at hp ⊢
      rw [hby, cellCentre_eq_refineSite] at hp ⊢
      show ((pathHolonomy (_root_.YangMills.Construction.BlockAverages.gaugeTransform gam Wp) (refineSite y) (bondContour F.blockSide e.1 e.2 i) :
        UnitQuaternion) : ℍ[ℝ]) = _
      rw [pathHolonomy_congr _ _ _ hbonds _ _ hp]
    rw [← quatAverage_allContours _ _ hL]
    unfold contourMean
    rw [hused]
    unfold quatAverage
    congr 1
    exact Finset.sum_congr rfl key
  have hmean : ∀ c : F.Cell × Fin 4, c.1 ∈ D.coreCells C 5 → c.1 + unitStep F.top c.2 ∈ D.coreCells C 5 →
      ‖((polarPart (contourMean J₀ D.hotFineLumps D.base D.fineField c) : UnitQuaternion) : ℍ[ℝ]) -
        (polarPart (_root_.YangMills.Construction.BlockAverages.contourAverage (gaugeTransform gam Wp) c) : UnitQuaternion)‖ ≤ Dn ∧
      1 - ‖contourMean J₀ D.hotFineLumps D.base D.fineField c‖ ≤ Dn ∧
      1 - ‖_root_.YangMills.Construction.BlockAverages.contourAverage (gaugeTransform gam Wp) c‖ ≤ Dn ∧
      ‖contourMean J₀ D.hotFineLumps D.base D.fineField c‖ ≤ 1 := by
    intro c hc1 hc2
    obtain ⟨m1, m2, m3⟩ := hCB F g a s θ C C₀ CJb J₀ D idx o U2 Wt γ c hL hTor hJ hs hC hC₀ hCJb hbox hbox3
      hS hFi hB hc1 hc2 hη
    have hcov := (hGC F F.depth hj hLpos).2.1 gam Wp c
    have hd2 : _root_.YangMills.Construction.BlockAverages.refineSite (c.1 + unitStep (F.depth + 1) c.2) = _root_.YangMills.Construction.BlockAverages.refineSite (c.1 + unitStep F.top c.2) := rfl
    rw [hd2, hgdown _ hc1, hgdown _ hc2] at hcov
    set Q := contourMean J₀ D.hotFineLumps D.base D.fineField c with hQ
    set P := _root_.YangMills.Construction.BlockAverages.contourAverage Wp c with hP
    set Q' := _root_.YangMills.Construction.BlockAverages.contourAverage (gaugeTransform gam Wp) c with hQ'
    set u := gc c.1 with hu
    set v := gc (c.1 + unitStep F.top c.2) with hv
    have hbound : ‖((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) * Q * (v : ℍ[ℝ]) - P‖ ≤ Dn / 8 := m1.trans hD0
    have e1 : Q - Q' = (u : ℍ[ℝ]) * (((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) * Q * (v : ℍ[ℝ]) - P) *
        ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      have h1 : (u : ℍ[ℝ]) * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := unitQuaternion_coe_mul_inv u
      have h2 : (v : ℍ[ℝ]) * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := unitQuaternion_coe_mul_inv v
      have e2 : (u : ℍ[ℝ]) * (((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) * Q * (v : ℍ[ℝ]) - P) *
          ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
          ((u : ℍ[ℝ]) * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])) * Q * ((v : ℍ[ℝ]) * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])) -
            (u : ℍ[ℝ]) * P * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
        noncomm_ring
      rw [e2, h1, h2, hcov]
      simp
    have hQQ : ‖Q - Q'‖ ≤ Dn / 8 := by
      rw [e1, norm_mul_mul_unitQuaternion]
      exact hbound
    have hnQ' : ‖Q'‖ = ‖P‖ := by
      rw [hcov, norm_mul_mul_unitQuaternion]
    have h1Q' : 1 - ‖Q'‖ ≤ Dn / 8 := by
      rw [hnQ']
      exact m2.trans hη2
    have hnorm : ‖Q'‖ - ‖Q‖ ≤ Dn / 8 := by
      have := norm_sub_norm_le Q' Q
      rw [norm_sub_rev] at this
      linarith
    have hhalf : 1 / 2 ≤ ‖Q‖ := by linarith only [h1Q', hnorm, hDn]
    have hdir := norm_polarPart_sub_le Q Q' hhalf
    refine ⟨by linarith only [hdir, hQQ, hDn0], by linarith only [h1Q', hnorm, hDn0],
      by linarith only [h1Q', hDn0], m3⟩
  have hf0 : ∀ c, 0 ≤ D.topBondFit c := by
    intro c
    have h1 := re_le_norm (contourMean J₀ D.hotFineLumps D.base D.fineField c *
      (((D.topField c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))
    rw [norm_mul, unitQuaternion_norm, mul_one] at h1
    have : D.topBondFit c = ‖contourMean J₀ D.hotFineLumps D.base D.fineField c‖ -
        (contourMean J₀ D.hotFineLumps D.base D.fineField c *
          (((D.topField c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := rfl
    rw [this]
    linarith
  have hsmall : ∀ y ∈ D.coreCells C 5, D.energyOver (_root_.YangMills.Construction.LumpContours.cellBall y 3) < C * s ^ 2 := by
    intro y hy
    by_contra hnot
    push_neg at hnot
    obtain ⟨hyS, hall⟩ := Finset.mem_filter.1 hy
    have hex : y ∈ D.excitedCells C := Finset.mem_filter.2 ⟨hyS, hnot⟩
    have := hall y (Finset.mem_union_left _ hex)
    rw [cellSupDist_self] at this
    omega
  obtain ⟨he1, he2⟩ := hEO F F.blockSide g a s θ J₀ D ha0 hL hs0
  have hfitb : ∀ c : F.Cell × Fin 4, c.1 ∈ D.coreCells C 5 → c.1 + unitStep F.top c.2 ∈ D.coreCells C 5 →
      blockFit (_root_.YangMills.Construction.BlockAverages.gaugeTransform gam Wp) D.topField c ≤ D.topBondFit c +
        (if ¬ (nearbyLumps D.hotFineLumps c.1 = ∅ ∧
          nearbyLumps D.hotFineLumps (c.1 + unitStep F.top c.2) = ∅) then ρ else 0) := by
    intro c hc1 hc2
    by_cases q : nearbyLumps D.hotFineLumps c.1 = ∅ ∧ nearbyLumps D.hotFineLumps (c.1 + unitStep F.top c.2) = ∅
    · rw [if_neg (not_not.2 q), add_zero]
      unfold blockFit HoleData.topBondFit contourFit
      rw [hquiet c hc1 hc2 q.1 q.2]
    · rw [if_pos q]
      obtain ⟨n1, n2, n3, n4⟩ := hmean c hc1 hc2
      have hcS : c ∈ cutBonds D.cells :=
        Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨(Finset.mem_filter.1 hc1).1, Finset.mem_univ _⟩,
          (Finset.mem_filter.1 hc2).1⟩
      have hsm := he2 (_root_.YangMills.Construction.LumpContours.cellBall c.1 3) c hcS (Or.inl ((cball _ 3 _).2 (by rw [cellSupDist_self]; omega)))
      have hf := hf0 c
      have hle : D.topBondFit c ≤ C * s ^ 2 := by
        have h1 := hsmall c.1 hc1
        nlinarith only [h1, hsm, hf, ha]
      have hQ1 : ‖_root_.YangMills.Construction.BlockAverages.contourAverage (gaugeTransform gam Wp) c‖ ≤ 1 := by
        rw [← quatAverage_allContours _ _ hL]
        refine norm_quatAverage_le_one _ ⟨(0, 1), Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩⟩ _
        exact mem_centredCube_of_offsetInBlock (offsetInBlock_zero hL)
      have h1 := hFit (contourMean J₀ D.hotFineLumps D.base D.fineField c)
        (_root_.YangMills.Construction.BlockAverages.contourAverage (gaugeTransform gam Wp) c) (D.topField c.1 c.2) Dn hDn0
        (by linarith) n4 hQ1 n2 n3 n1
      exact h1.trans (hfitn _ hf hle)
  set A := C₀ * C * s ^ 2 / ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) with hA
  have hb1 : ∀ X ⊆ D.coreCells C 5, cutChainEnergy a F.depth (cutBelow F.depth X) U3 +
      a * ∑ c ∈ cutBonds X, blockFit (U3 F.depth) D.topField c ≤
      D.energyOn X + A * (D.componentsMeeting C idx o (cutBelow F.depth X)).card +
        a * (((cutBonds X).filter fun c =>
          ¬ (nearbyLumps D.hotFineLumps c.1 = ∅ ∧
            nearbyLumps D.hotFineLumps (c.1 + unitStep F.top c.2) = ∅)).card * ρ) := by
    intro X hX
    have hX4 : X ⊆ D.coreCells C 4 := fun x hx => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 (hX hx)
      exact Finset.mem_filter.2 ⟨h1, fun z hz => (by norm_num : 4 ≤ 5).trans (h2 z hz)⟩
    have hXS : X ⊆ D.cells := fun x hx => (Finset.mem_filter.1 (hX hx)).1
    have h1 : cutChainEnergy a F.depth (cutBelow F.depth X) U2 ≤
        cutChainEnergy a F.depth (cutBelow F.depth X \ lumpsNeighbourhood D.hotFineLumps) D.chain +
        A * (D.componentsMeeting C idx o (cutBelow F.depth X)).card := hFi.energy_le _ (cutBelow_mono hX4)
    have hlow : D.chainSites ∩ cutBelow F.depth X = cutBelow F.depth X \ lumpsNeighbourhood D.hotFineLumps := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff, HoleData.chainSites]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h2, h3⟩
        exact ⟨⟨cutBelow_mono hXS h2, h3⟩, h2⟩
    have hsum : ∑ c ∈ cutBonds X, blockFit (U3 F.depth) D.topField c ≤ ∑ c ∈ cutBonds X, D.topBondFit c +
        ((cutBonds X).filter fun c =>
          ¬ (nearbyLumps D.hotFineLumps c.1 = ∅ ∧
            nearbyLumps D.hotFineLumps (c.1 + unitStep F.top c.2) = ∅)).card * ρ := by
      have e2 : ∑ c ∈ cutBonds X,
          (if ¬ (nearbyLumps D.hotFineLumps c.1 = ∅ ∧
            nearbyLumps D.hotFineLumps (c.1 + unitStep F.top c.2) = ∅) then ρ else 0) =
          ((cutBonds X).filter fun c =>
            ¬ (nearbyLumps D.hotFineLumps c.1 = ∅ ∧
              nearbyLumps D.hotFineLumps (c.1 + unitStep F.top c.2) = ∅)).card * ρ := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [← e2, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun c hc => ?_
      obtain ⟨e3, e4⟩ := cutBonds_ends_mem hc
      rw [hU3t]
      exact hfitb c (hX e3) (hX e4)
    rw [hcost]
    unfold HoleData.energyOn
    rw [hlow]
    have h2 := mul_le_mul_of_nonneg_left hsum ha0
    rw [mul_add] at h2
    linarith only [h1, h2]
  obtain ⟨k1, k2, k3⟩ := hCN F g a s θ C J₀ D idx o hL hTor hS
  obtain ⟨-, -, l3, -⟩ := hLS F a ha0 hL
  have hupd : Function.update U3 F.top D.topField = U3 := by
    rw [← hU3n]
    exact Function.update_eq_self _ _
  have htopn : ∀ X : Finset F.Cell, cutChainEnergy a F.top X U3 ≤
      cutChainEnergy a F.depth (cutBelow F.depth X) U3 + a * ∑ c ∈ cutBonds X, blockFit (U3 F.depth) D.topField c := by
    intro X
    have := l3 X U3 D.topField
    rwa [hupd] at this
  have hbelow : ∀ X ⊆ D.coreCells C 5, cutChainEnergy a F.depth (cutBelow F.depth X) U3 +
      a * ∑ c ∈ cutBonds X, blockFit (U3 F.depth) D.topField c ≤
      D.energyOn X + ε * s ^ 2 * (D.nearbyFineLumps X).card := by
    intro X hX
    have h1 := hb1 X hX
    have c1 : ((D.componentsMeeting C idx o (cutBelow F.depth X)).card : ℝ) ≤ (D.nearbyFineLumps X).card := by
      exact_mod_cast k1 X
    have c3 : (((cutBonds X).filter fun c =>
        ¬ (nearbyLumps D.hotFineLumps c.1 = ∅ ∧
          nearbyLumps D.hotFineLumps (c.1 + unitStep F.top c.2) = ∅)).card : ℝ) ≤
        9604 * (D.nearbyFineLumps X).card := by
      exact_mod_cast k3 X
    have hn0 : (0 : ℝ) ≤ (D.nearbyFineLumps X).card := by positivity
    have m1 := mul_le_mul_of_nonneg_left c1 hA0
    have m2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right c3 hρ0) ha0
    have m3 := mul_le_mul_of_nonneg_right hn1 hn0
    linarith only [h1, m1, m2, m3]
  have hplaces : ∀ y ∈ D.coreCells C 6, ∀ X ⊆ _root_.YangMills.Construction.LumpContours.cellBall y 1 ∩ D.coreCells C 5,
      cutChainEnergy a F.depth (cutBelow F.depth X) U3 + a * ∑ c ∈ cutBonds X, blockFit (U3 F.depth) D.topField c ≤
        CJ * s ^ 2 := by
    intro y hy X hX
    have hX5 : X ⊆ D.coreCells C 5 := fun x hx => (Finset.mem_inter.1 (hX hx)).2
    have hXb : X ⊆ _root_.YangMills.Construction.LumpContours.cellBall y 1 := fun x hx => (Finset.mem_inter.1 (hX hx)).1
    have hXS : X ⊆ D.cells := fun x hx => (Finset.mem_filter.1 (hX5 hx)).1
    have hy5 : y ∈ D.coreCells C 5 := by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hy
      exact Finset.mem_filter.2 ⟨h1, fun z hz => (by norm_num : 5 ≤ 6).trans (h2 z hz)⟩
    have hnc : ¬ IsCrowded J₀ D.hotFineLumps y := by
      intro hcr
      obtain ⟨huS, hall⟩ := Finset.mem_filter.1 hy
      have := hall y (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨huS, hcr⟩))
      rw [cellSupDist_self] at this
      omega
    have h1 := hb1 X hX5
    have hsub3 : X ⊆ _root_.YangMills.Construction.LumpContours.cellBall y 3 := fun x hx =>
      (cball y 3 x).2 (((cball y 1 x).1 (hXb hx)).trans (by norm_num))
    have hel := he1 X (_root_.YangMills.Construction.LumpContours.cellBall y 3) hXS hsub3
    have hsm := hsmall y hy5
    have c2 : ((D.componentsMeeting C idx o (cutBelow F.depth X)).card : ℝ) ≤ J₀ := by
      exact_mod_cast k2 y hnc X hXb
    have c3 : (((cutBonds X).filter fun c =>
        ¬ (nearbyLumps D.hotFineLumps c.1 = ∅ ∧
          nearbyLumps D.hotFineLumps (c.1 + unitStep F.top c.2) = ∅)).card : ℝ) ≤ 324 := by
      have hball : X.card ≤ (2 * 1 + 1) ^ 4 := (Finset.card_le_card hXb).trans (card_cellBall_le y 1)
      have hcb : (cutBonds X).card ≤ X.card * 4 := by
        have : cutBonds X ⊆ X ×ˢ (Finset.univ : Finset (Fin 4)) := Finset.filter_subset _ _
        refine (Finset.card_le_card this).trans ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      have : ((cutBonds X).filter fun c =>
          ¬ (nearbyLumps D.hotFineLumps c.1 = ∅ ∧
            nearbyLumps D.hotFineLumps (c.1 + unitStep F.top c.2) = ∅)).card ≤ 324 := by
        refine (Finset.card_filter_le _ _).trans ?_
        omega
      exact_mod_cast this
    have m1 := mul_le_mul_of_nonneg_left c2 hA0
    have m2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right c3 hρ0) ha0
    linarith only [h1, m1, m2, hel, hsm, hn2]
  refine ⟨U3, ⟨hU3n, ?_, hbelow, ?_, hplaces, ?_, ?_⟩⟩
  · intro c hc1 hc2
    obtain ⟨n1, n2, n3, -⟩ := hmean c hc1 hc2
    rw [hU3t]
    exact ⟨n1.trans hDnCJ, n2.trans hDnCJ, n3.trans hDnCJ⟩
  · intro X hX
    exact (htopn X).trans (hbelow X hX)
  · intro y hy X hX
    exact (htopn X).trans (hplaces y hy X hX)
  · intro b hb q1 q2
    rw [hU3t]
    exact hW2 b hb q1 q2
end ContourMeans
open ContourMeans in
set_option maxHeartbeats 8000000 in
theorem ContourMeans.contourMeansStatement_holds (hF : holesAwayFromBadCellsStatement)
    (hB : boxFillingStatement)
    (hT : GaugeChainPreservesEnergy) (hCB : CoreBondMeanEstimate)
    (hCN : countsNearCutStatement) (hEO : energyOnLeEnergyOverStatement)
    (hFit : NearMeanFitEstimate) (hG : MostContoursGoodStatement)
    (hD : TorusDistanceBlockLumpFacts) (hLS : minimalChainEnergiesStatement)
    (hGC : gaugeCovarianceStatement) : contourMeansStatement := by
  intro a C J₀ ha hC hJ
  obtain ⟨C₀, hC₀, hFJ⟩ := hF
  obtain ⟨hgrow, L₁, hF1⟩ := hFJ J₀ hJ
  obtain ⟨CJb, hCJb, L₂, hB1⟩ := hB C₀ J₀ a C hC₀ hJ ha hC
  have hJr : (1 : ℝ) ≤ J₀ := by exact_mod_cast hJ
  set cκ := Real.sqrt (CJb + C₀ * C) with hcκ
  set c₁ : ℝ := 72 * cκ + 16 * J₀ * CJb with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set c₂ : ℝ := 8 * (2 * excludedBoxSide J₀ : ℝ) ^ 3 with hc₂
  have hc₂0 : 0 ≤ c₂ := by positivity
  set c₃ : ℝ := 2 * (J₀ : ℝ) ^ 4 * CJb + 1 + 14 * c₁ * c₂ with hc₃
  set CJ1 : ℝ := 8 * (c₃ + 1) with hCJ1
  have hCJ10 : 0 < CJ1 := by positivity
  set E : ℝ := 2 * CJ1 * C + 2 * CJ1 * Real.sqrt C + CJ1 ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  set CJ : ℝ := CJ1 + C + C₀ * C + 324 * a * E with hCJ
  have hCJ0 : 0 < CJ := by positivity
  refine ⟨CJ, hCJ0, fun ε hε => ?_⟩
  obtain ⟨L₃, hL₃⟩ := hgrow (J₀ + ⌈2 * C₀ * C / ε⌉₊ + 1)
  refine ⟨L₁ + L₂ + L₃ + ⌈(2 * 9604 * a * E / ε) ^ 2⌉₊ + excludedBoxSide J₀ + 1 + ⌈c₂⌉₊,
    fun L hL hL0 g => ?_⟩
  have hLL₁ : L₁ ≤ L := by omega
  have hLL₂ : L₂ ≤ L := by omega
  have hLL₃ : L₃ ≤ L := by omega
  have hLL₄ : ⌈(2 * 9604 * a * E / ε) ^ 2⌉₊ ≤ L := by omega
  have hLbox : excludedBoxSide J₀ < L := by omega
  have hLc₂ : ⌈c₂⌉₊ < L := by omega
  obtain ⟨h2J, hF2⟩ := hF1 L hL hLL₁
  obtain ⟨s₁, hs₁, hF3⟩ := hF2 g a C ha hC
  obtain ⟨s₂, hs₂, hB2⟩ := hB1 L hL hLL₂ g
  have hLpos : 0 < L := hL.pos
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  set T : ℝ := 16 * (c₁ ^ 2 + 1) * (CJ1 + 1) * (L : ℝ) ^ 3 with hTd
  have hT0 : 0 < T := by positivity
  refine ⟨min (min s₁ s₂) (min 1 (1 / T)), by positivity, fun s hs hs0 θ F D hFL hTor => ?_⟩
  have hss₁ : s ≤ s₁ := (hs0.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hss₂ : s ≤ s₂ := (hs0.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hs1 : s ≤ 1 := (hs0.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hsT : s * T ≤ 1 := by
    have h1 : s ≤ 1 / T := (hs0.trans (min_le_right _ _)).trans (min_le_right _ _)
    rwa [le_div_iff₀ hT0] at h1
  obtain ⟨idx, o, U2, hS, hFi⟩ := hF3 s hs hss₁ θ F D hFL hTor
  obtain ⟨Wt, γ, hBx⟩ := hB2 s hs hss₂ θ F D hFL hTor idx o U2 hS hFi
  subst hFL
  set q := Real.sqrt (F.blockSide : ℝ) with hq
  have hq1 : 1 ≤ q := by
    rw [hq]
    exact Real.one_le_sqrt.2 hLr
  have hq0 : 0 < q := by linarith
  have hqq : q * q = (F.blockSide : ℝ) := Real.mul_self_sqrt (by positivity)
  have hqL : q ≤ (F.blockSide : ℝ) := by nlinarith only [hq1, hqq, hq0]
  set osc := coreOscillation F.blockSide J₀ C C₀ CJb s with hoscd
  have hN : ((J₀ * Nat.sqrt F.blockSide : ℕ) : ℝ) ≤ J₀ * q := by
    push_cast
    exact mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by positivity)
  have hN0 : (0 : ℝ) ≤ ((J₀ * Nat.sqrt F.blockSide : ℕ) : ℝ) := by positivity
  have hosc : osc ≤ c₁ * F.blockSide * s := by
    rw [hoscd]
    unfold coreOscillation coreCurvatureBound
    rw [← hq, ← hcκ]
    have h1 : 16 * ((J₀ * Nat.sqrt F.blockSide : ℕ) : ℝ) * (CJb * q * s) ≤ 16 * (J₀ * q) * (CJb * q * s) := by
      have h0 : 0 ≤ CJb * q * s := by positivity
      have := mul_le_mul_of_nonneg_right hN h0
      linarith only [this]
    have e : 16 * (J₀ * q) * (CJb * q * s) = 16 * J₀ * CJb * (q * q) * s := by ring
    rw [e, hqq] at h1
    rw [hc₁]
    linarith only [h1]
  have hosc0 : 0 ≤ osc := by
    rw [hoscd]
    unfold coreOscillation coreCurvatureBound
    positivity
  have hL3 : (F.blockSide : ℝ) ≤ (F.blockSide : ℝ) ^ 3 := le_self_pow₀ hLr (by norm_num)
  have hL31 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ 3 := hLr.trans hL3
  have hc1sq : c₁ ≤ c₁ ^ 2 + 1 := by nlinarith only [sq_nonneg (c₁ - 1)]
  have hcL : c₁ * F.blockSide * s ≤ 1 / 16 := by
    have h1 : 16 * c₁ * F.blockSide ≤ T := by
      rw [hTd]
      have a1 : 16 * c₁ * (F.blockSide : ℝ) ≤ 16 * (c₁ ^ 2 + 1) * (F.blockSide : ℝ) ^ 3 := by
        have := mul_le_mul hc1sq hL3 (by positivity) (by positivity)
        linarith only [this]
      have a2 : 16 * (c₁ ^ 2 + 1) * (F.blockSide : ℝ) ^ 3 ≤
          16 * (c₁ ^ 2 + 1) * (CJ1 + 1) * (F.blockSide : ℝ) ^ 3 := by
        have h0 : 0 ≤ 16 * (c₁ ^ 2 + 1) * (F.blockSide : ℝ) ^ 3 := by positivity
        nlinarith only [h0, hCJ10]
      linarith only [a1, a2]
    have h2 := mul_le_mul_of_nonneg_left h1 hs.le
    linarith only [h2, hsT]
  have hη : osc ≤ 1 / 8 := by linarith only [hosc, hcL]
  set t := s / q with ht
  have ht0 : 0 < t := by positivity
  have hts : t ≤ s := by
    rw [ht]
    exact div_le_self hs.le hq1
  have h12 : 12 * osc ^ 2 ≤ t := by
    have h1 : osc ^ 2 ≤ (c₁ * F.blockSide * s) ^ 2 := pow_le_pow_left₀ hosc0 hosc 2
    have h2 : 12 * c₁ ^ 2 * (F.blockSide : ℝ) ^ 3 ≤ T := by
      rw [hTd]
      have h0 : 0 ≤ c₁ ^ 2 * (F.blockSide : ℝ) ^ 3 := by positivity
      have h3 : 0 ≤ (F.blockSide : ℝ) ^ 3 := by positivity
      nlinarith only [h0, h3, hCJ10, mul_nonneg h0 hCJ10.le, mul_nonneg h3 hCJ10.le]
    have h3 : 12 * c₁ ^ 2 * (F.blockSide : ℝ) ^ 3 * s ≤ 1 := by
      have h4 := mul_le_mul_of_nonneg_right h2 hs.le
      linarith only [h4, hsT]
    have h4 : 12 * (c₁ * F.blockSide * s) ^ 2 * q ≤ s := by
      have e : 12 * (c₁ * F.blockSide * s) ^ 2 * q = (12 * c₁ ^ 2 * (F.blockSide : ℝ) ^ 2 * q * s) * s := by ring
      rw [e]
      have h5 : 12 * c₁ ^ 2 * (F.blockSide : ℝ) ^ 2 * q * s ≤ 12 * c₁ ^ 2 * (F.blockSide : ℝ) ^ 3 * s := by
        have h0 : 0 ≤ 12 * c₁ ^ 2 * (F.blockSide : ℝ) ^ 2 * s := by positivity
        have h6 := mul_le_mul_of_nonneg_left hqL h0
        linarith only [h6]
      have h6 : 12 * c₁ ^ 2 * (F.blockSide : ℝ) ^ 2 * q * s ≤ 1 := h5.trans h3
      have h7 := mul_le_mul_of_nonneg_right h6 hs.le
      linarith only [h7]
    have h5 : 12 * (c₁ * F.blockSide * s) ^ 2 ≤ t := by
      rw [ht, le_div_iff₀ hq0]
      exact h4
    linarith only [h1, h5]
  have hterm1 : 2 * ((J₀ * Nat.sqrt F.blockSide : ℕ) : ℝ) ^ 4 * (CJb * q * s) / (F.blockSide : ℝ) ^ 3 ≤
      2 * (J₀ : ℝ) ^ 4 * CJb * t := by
    have h1 : ((J₀ * Nat.sqrt F.blockSide : ℕ) : ℝ) ^ 4 ≤ (J₀ * q) ^ 4 := pow_le_pow_left₀ hN0 hN 4
    have h2 : 2 * ((J₀ * Nat.sqrt F.blockSide : ℕ) : ℝ) ^ 4 * (CJb * q * s) ≤
        2 * (J₀ * q) ^ 4 * (CJb * q * s) := by
      have h0 : 0 ≤ CJb * q * s := by positivity
      have h3 := mul_le_mul_of_nonneg_right h1 h0
      linarith only [h3]
    have e : 2 * (J₀ * q) ^ 4 * (CJb * q * s) / (F.blockSide : ℝ) ^ 3 = 2 * (J₀ : ℝ) ^ 4 * CJb * t := by
      rw [← hqq, ht]
      field_simp
    rw [← e]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have hterm3 : 14 * osc * (c₂ / (F.blockSide : ℝ) ^ 3) ≤ 14 * c₁ * c₂ * t := by
    have h1 : c₁ * F.blockSide * s * (c₂ / (F.blockSide : ℝ) ^ 3) ≤ c₁ * c₂ * t := by
      have e1 : c₁ * F.blockSide * s * (c₂ / (F.blockSide : ℝ) ^ 3) = c₁ * c₂ * (s / (F.blockSide : ℝ) ^ 2) := by
        field_simp
      rw [e1, ht]
      have h3 : s / (F.blockSide : ℝ) ^ 2 ≤ s / q := by
        have h4 : q ≤ (F.blockSide : ℝ) ^ 2 := hqL.trans (le_self_pow₀ hLr (by norm_num))
        exact div_le_div_of_nonneg_left hs.le hq0 h4
      have h5 : 0 ≤ c₁ * c₂ := by positivity
      exact mul_le_mul_of_nonneg_left h3 h5
    have h2 : 0 ≤ c₂ / (F.blockSide : ℝ) ^ 3 := by positivity
    have h3 := mul_le_mul_of_nonneg_right hosc h2
    linarith only [h1, h3]
  set Dn := CJ1 * t with hDnd
  have hDn0 : 0 ≤ Dn := by positivity
  have hD0 : 2 * ((J₀ * Nat.sqrt F.blockSide : ℕ) : ℝ) ^ 4 * (CJb * q * s) / (F.blockSide : ℝ) ^ 3 +
      12 * osc ^ 2 + 14 * osc * (c₂ / (F.blockSide : ℝ) ^ 3) ≤ Dn / 8 := by
    have e : Dn / 8 = (c₃ + 1) * t := by
      rw [hDnd, hCJ1]
      ring
    rw [e, hc₃]
    have h1 := hterm1
    have h3 := hterm3
    linarith only [h1, h3, h12, ht0, mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 14 * c₁) hc₂0) ht0.le]
  have hη2 : osc ^ 2 ≤ Dn / 8 := by
    have e : Dn / 8 = (c₃ + 1) * t := by
      rw [hDnd, hCJ1]
      ring
    rw [e]
    have h1 : 0 ≤ osc ^ 2 := by positivity
    have h2 : 0 ≤ c₃ * t := by positivity
    linarith only [h12, h1, h2]
  have h16 : 16 * CJ1 * s ≤ 1 := by
    have h1 : 16 * CJ1 ≤ T := by
      rw [hTd]
      have b1 : 1 ≤ c₁ ^ 2 + 1 := by nlinarith only [sq_nonneg c₁]
      have b3 : CJ1 ≤ (c₁ ^ 2 + 1) * (CJ1 + 1) := by nlinarith only [b1, hCJ10]
      have b4 : CJ1 ≤ (c₁ ^ 2 + 1) * (CJ1 + 1) * (F.blockSide : ℝ) ^ 3 := by
        have h0 : 0 ≤ (c₁ ^ 2 + 1) * (CJ1 + 1) := by positivity
        nlinarith only [b3, h0, hL31]
      linarith only [b4]
    have h2 := mul_le_mul_of_nonneg_left h1 hs.le
    linarith only [h2, hsT]
  have hDn : Dn ≤ 1 / 8 := by
    rw [hDnd]
    have h1 := mul_le_mul_of_nonneg_left hts hCJ10.le
    linarith only [h1, h16]
  have hDnCJ : Dn ≤ CJ * s / Real.sqrt F.blockSide := by
    have e : CJ * s / Real.sqrt F.blockSide = CJ * t := by
      rw [ht, ← hq]
      ring
    rw [e, hDnd]
    have : CJ1 ≤ CJ := by
      rw [hCJ]
      have h0 : 0 ≤ 324 * a * E := by positivity
      have h1 : 0 ≤ C₀ * C := by positivity
      linarith only [h0, h1, hC]
    exact mul_le_mul_of_nonneg_right this ht0.le
  set w := s ^ 2 / q with hw
  have hw0 : 0 ≤ w := by positivity
  have hts' : t * s = w := by
    rw [ht, hw]
    ring
  set ρ := E * w with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hfitn : ∀ f : ℝ, 0 ≤ f → f ≤ C * s ^ 2 → f * (1 + 2 * Dn) + 2 * Dn * Real.sqrt f + Dn ^ 2 ≤ f + ρ := by
    intro f hf0 hfC
    have hsq : Real.sqrt f ≤ Real.sqrt C * s := by
      have h1 := Real.sqrt_le_sqrt hfC
      rwa [Real.sqrt_mul hC.le, Real.sqrt_sq hs.le] at h1
    have a1 : Dn * f ≤ CJ1 * C * w := by
      have h1 : t * f ≤ t * (C * s ^ 2) := mul_le_mul_of_nonneg_left hfC ht0.le
      have e : t * (C * s ^ 2) = C * (t * s) * s := by ring
      rw [e, hts'] at h1
      have h2 : C * w * s ≤ C * w := by
        have h0 : 0 ≤ C * w := by positivity
        have h3 := mul_le_mul_of_nonneg_left hs1 h0
        linarith only [h3]
      rw [hDnd]
      have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hCJ10.le
      linarith only [h3]
    have a2 : Dn * Real.sqrt f ≤ CJ1 * Real.sqrt C * w := by
      have h1 : t * Real.sqrt f ≤ t * (Real.sqrt C * s) := mul_le_mul_of_nonneg_left hsq ht0.le
      have e : t * (Real.sqrt C * s) = Real.sqrt C * (t * s) := by ring
      rw [e, hts'] at h1
      rw [hDnd]
      have h3 := mul_le_mul_of_nonneg_left h1 hCJ10.le
      linarith only [h3]
    have a3 : Dn ^ 2 ≤ CJ1 ^ 2 * w := by
      have h1 : t ^ 2 ≤ w := by
        rw [← hts']
        have h3 := mul_le_mul_of_nonneg_left hts ht0.le
        linarith only [h3]
      rw [hDnd, mul_pow]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hρ, hE]
    linarith only [a1, a2, a3]
  have hI₁ := hL₃ F.blockSide hLL₃
  set I := topScaleIndex J₀ F.blockSide with hI
  set den : ℝ := (I : ℝ) - J₀ with hden
  have hden1 : 2 * C₀ * C / ε ≤ den := by
    have h1 : ((J₀ + ⌈2 * C₀ * C / ε⌉₊ + 1 : ℕ) : ℝ) ≤ I := by exact_mod_cast hI₁
    have h2 := Nat.le_ceil (2 * C₀ * C / ε)
    push_cast at h1
    rw [hden]
    linarith only [h1, h2]
  have hden2 : (J₀ : ℝ) ≤ den := by
    have h1 : ((2 * J₀ : ℕ) : ℝ) ≤ I := by exact_mod_cast h2J
    push_cast at h1
    rw [hden]
    linarith only [h1]
  have hden0 : 0 < den := by linarith only [hden2, hJr]
  have hA0 : 0 ≤ C₀ * C * s ^ 2 / den := by positivity
  have hA1 : C₀ * C * s ^ 2 / den ≤ ε / 2 * s ^ 2 := by
    rw [div_le_iff₀ hden0]
    have h1 : 2 * C₀ * C ≤ den * ε := by
      rwa [div_le_iff₀ hε] at hden1
    have h2 : 0 ≤ s ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    linarith only [h3]
  have hρa : a * ρ * 9604 ≤ ε / 2 * s ^ 2 := by
    have hx : 2 * 9604 * a * E / ε ≤ q := by
      have h1 := Nat.le_ceil ((2 * 9604 * a * E / ε) ^ 2)
      have h2 : ((⌈(2 * 9604 * a * E / ε) ^ 2⌉₊ : ℕ) : ℝ) ≤ F.blockSide := by exact_mod_cast hLL₄
      exact Real.le_sqrt_of_sq_le (h1.trans h2)
    have h3 : 2 * 9604 * a * E ≤ q * ε := by
      rwa [div_le_iff₀ hε] at hx
    have e : a * ρ * 9604 = (9604 * a * E) * s ^ 2 / q := by
      rw [hρ, hw]
      ring
    rw [e, div_le_iff₀ hq0]
    have h2 : 0 ≤ s ^ 2 := by positivity
    have h4 := mul_le_mul_of_nonneg_right h3 h2
    linarith only [h4]
  have hn1 : C₀ * C * s ^ 2 / den + a * ρ * 9604 ≤ ε * s ^ 2 := by linarith only [hA1, hρa]
  have hwle : w ≤ s ^ 2 := by
    rw [hw]
    exact div_le_self (by positivity) hq1
  have hn2 : C * s ^ 2 + C₀ * C * s ^ 2 / den * J₀ + a * ρ * 324 ≤ CJ * s ^ 2 := by
    have b1 : C₀ * C * s ^ 2 / den * J₀ ≤ C₀ * C * s ^ 2 := by
      have h1 : C₀ * C * s ^ 2 / den * J₀ ≤ C₀ * C * s ^ 2 / den * den :=
        mul_le_mul_of_nonneg_left hden2 hA0
      have e : C₀ * C * s ^ 2 / den * den = C₀ * C * s ^ 2 := by field_simp
      linarith only [h1, e]
    have b2 : a * ρ * 324 ≤ 324 * a * E * s ^ 2 := by
      have h1 : ρ ≤ E * s ^ 2 := by
        rw [hρ]
        exact mul_le_mul_of_nonneg_left hwle hE0
      have h0 : 0 ≤ a * 324 := by positivity
      have h3 := mul_le_mul_of_nonneg_left h1 h0
      linarith only [h3]
    rw [hCJ]
    have h2 : 0 ≤ CJ1 * s ^ 2 := by positivity
    linarith only [b1, b2, h2]
  have hbox3 : 8 * (2 * excludedBoxSide J₀) ^ 3 < F.blockSide ^ 3 := by
    have h1 : 8 * (2 * excludedBoxSide J₀) ^ 3 ≤ ⌈c₂⌉₊ := by
      have h2 := Nat.le_ceil c₂
      rw [hc₂] at h2
      have h3 : ((8 * (2 * excludedBoxSide J₀) ^ 3 : ℕ) : ℝ) ≤ (⌈8 * (2 * excludedBoxSide J₀ : ℝ) ^ 3⌉₊ : ℝ) := by
        push_cast
        exact h2
      rw [hc₂]
      exact_mod_cast h3
    have h4 : F.blockSide ≤ F.blockSide ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  exact exists_meanMatchingChain hT hCB hCN hEO hFit hG hD hLS hGC F g a s θ C C₀ CJb CJ ε Dn ρ J₀ D idx o
    U2 Wt γ ha hs hC hC₀ hCJb hJ hL hTor hLbox hbox3 hS hFi hBx hη hD0 hη2 hDn0 hDn hDnCJ hρ0 hfitn hA0
    hn1 hn2
end YangMills.Construction
end
