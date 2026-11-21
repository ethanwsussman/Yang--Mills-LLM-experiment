import YangMills.Construction.HoleBesideASecondHole.BoxesAreFilled
import YangMills.Construction.HoleBesideASecondHole.CoreAndHolesAsSites
import YangMills.Construction.HoleBesideASecondHole.GaugeInTheHoles
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.HoleSavings
open BlockAverages LumpContours Holes HoleSites BlockSites ChainGauges
attribute [local irreducible] LumpContours.cellBall
theorem boxFillingStatement_holds (hField : filledFieldStatement) (hHoles : HoleGauge.holeGaugeStatement)
    (hEnergyPreserved : GaugeChainPreservesEnergy) : boxFillingStatement := by
  classical
  intro C₀ J₀ a C hC₀ hJ ha hC
  obtain ⟨CJ₁, hCJ₁, L₁, hF⟩ := hField J₀ a C hJ ha hC
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = Real.sqrt (C₀ * C + CJ₁) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ]; exact Real.sqrt_nonneg _
  have hρsq : ρ ^ 2 = C₀ * C + CJ₁ := by
    rw [hρ, Real.sq_sqrt (by positivity)]
  refine ⟨CJ₁ + ρ + 1, by positivity, L₁, fun L hodd hL g => ?_⟩
  obtain ⟨s₀, hs₀, hS⟩ := hF L hodd hL g
  refine ⟨s₀, hs₀, fun s hs hss θ F D hFL hcub idx o U2 hst hch => ?_⟩
  obtain ⟨Wt, hW⟩ := hS s hs hss θ F D hFL hcub idx o hst
  subst hFL
  have hside : ∀ i, 4096 ≤ F.extent i := fun i => by
    have h1 := hcub.1 i
    have h2 := hcub.2
    omega
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    have := hside i
    omega
  have hLpos := hodd.pos
  haveI : ∀ i, NeZero (F.period F.depth i) := fun i => ⟨by
    rw [period_depth]
    exact Nat.mul_ne_zero (hpos i).ne' hLpos.ne'⟩
  haveI : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    rw [period_top]
    exact (hpos i).ne'⟩
  have hturn := fun (γ : F.Site F.depth → UnitQuaternion) => hEnergyPreserved F γ U2 hLpos hpos
  have hE : 0 ≤ ρ * s := by positivity
  have hsq : (ρ * s) ^ 2 = (C₀ * C + CJ₁) * s ^ 2 := by
    rw [mul_pow, hρsq]
  have hs2 : 0 ≤ s ^ 2 := by positivity
  have hsub54 := D.coreCells_antitone (C := C) (show 4 ≤ 5 by omega)
  have hagreeW : ∀ b ∈ cutBonds (cutBelow F.depth (D.coreCells C 5)), b.1 ∉ holeSupport (D.holesAt C idx o) →
      b.1 + unitStep F.depth b.2 ∉ holeSupport (D.holesAt C idx o) →
        Wt b.1 b.2 = D.fineField b.1 b.2 ∧ U2 F.depth b.1 b.2 = D.fineField b.1 b.2 := by
    intro b hb h₁ h₂
    refine ⟨hW.eq_of_not_touches b fun Z hZ hm => ?_, hch.top_eq_off_holes b ?_ h₁ h₂⟩
    · obtain ⟨H, hH, hZH⟩ := hW.exists_hole_superset Z hZ
      rcases hm with hm | hm
      · exact h₁ (Finset.mem_biUnion.mpr ⟨H, hH, innerBox_subset_outerBox H (hZH hm)⟩)
      · exact h₂ (Finset.mem_biUnion.mpr ⟨H, hH, innerBox_subset_outerBox H (hZH hm)⟩)
    · obtain ⟨m₁, m₂⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.biUnion_subset_biUnion_of_subset_left _ hsub54 (Finset.mem_product.mp m₁).1, by simp⟩,
        Finset.biUnion_subset_biUnion_of_subset_left _ hsub54 m₂⟩
  have hball : ∀ y ∈ D.coreCells C 5, ∀ y' ∈ D.coreCells C 5, cellSupDist y y' ≤ 1 →
      sitesBelow F.depth y ∪ sitesBelow F.depth y' ⊆ cutBelow F.depth (cellBall y 1 ∩ D.coreCells C 4) := by
    intro y hy y' hy' hd x hx
    have hyb : y ∈ cellBall y 1 := mem_cellBall_iff.mpr ⟨0, fun i => by simp, by
      have : (siteOfCoords F.top (0 : Fin 4 → ℤ) : F.Cell) = 0 := by
        funext i
        simp [siteOfCoords]
      rw [this, add_zero]⟩
    have hyb' : y' ∈ cellBall y 1 := by
      obtain ⟨c, hc, e⟩ := exists_offset_of_supDist_le hd
      exact mem_cellBall_iff.mpr ⟨c, hc, e⟩
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_inter.mpr ⟨hyb, hsub54 hy⟩, h⟩
    · exact Finset.mem_biUnion.mpr ⟨y', Finset.mem_inter.mpr ⟨hyb', hsub54 hy'⟩, h⟩
  have hmono : ∀ {X Y : Finset (F.Site F.depth)}, X ⊆ Y → cutPlaquettes X ⊆ cutPlaquettes Y := by
    intro X Y h p hp
    obtain ⟨h₁, h₂, h₃⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h (Finset.mem_product.mp h₁).1, (Finset.mem_product.mp h₁).2⟩,
      h₂, h₃.trans h⟩
  have hCC : 0 ≤ C₀ * C := by positivity
  obtain ⟨γ, hγ₁, hγ₂⟩ := hHoles F (D.holesAt C idx o) (D.coreCells C 5) (U2 F.depth) Wt (ρ * s) hodd hside hE
    hst.radius_bounds hst.pairwise_apart
    (fun b hb h₁ h₂ => by rw [(hagreeW b hb h₁ h₂).2, (hagreeW b hb h₁ h₂).1])
    (fun y hy y' hy' hd => by
      have h1 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p => plaquetteDefect (U2 F.depth) p ^ 2)
        (hmono (hball y hy y' hy' hd)) (fun _ _ _ => sq_nonneg _)
      have h2 := hch.curvature_le y hy
      rw [hsq]
      nlinarith)
    (fun y hy y' hy' hd => by
      have h2 := hW.curvature_le y hy y' hy' hd
      rw [hsq]
      nlinarith)
  refine ⟨Wt, γ, ⟨hW.mem_excludedBoxes_of_adj, hW.pairwise_apart, hW.exists_hole_superset, ?_,
    hW.eq_of_not_touches, ?_, hagreeW, hγ₁, (hturn γ).1, ?_, ?_, ?_, hW.disjoint_of_nearbyLumps_empty⟩⟩
  · obtain ⟨G, hG⟩ := hW.exists_gauge
    refine ⟨G, fun Z hZ => ⟨(hG Z hZ).1, (hG Z hZ).2.1, fun b h₁ h₂ => ((hG Z hZ).2.2 b h₁ h₂).trans ?_⟩⟩
    nlinarith
  · intro y hy y' hy' hd
    have := hW.curvature_le y hy y' hy' hd
    nlinarith
  · intro y hy y' hy' hd b hb
    obtain ⟨m₁, m₂⟩ := Finset.mem_filter.mp hb
    have inC : ∀ x ∈ sitesBelow F.depth y ∪ sitesBelow F.depth y', enclosingCell x ∈ D.coreCells C 5 := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · rwa [enclosingCell_eq_of_mem_sitesBelow hodd hpos h]
      · rwa [enclosingCell_eq_of_mem_sitesBelow hodd hpos h]
    have h1 := hγ₂ b (inC _ (Finset.mem_product.mp m₁).1) (inC _ m₂)
    rw [(hturn γ).1]
    refine h1.trans ?_
    have hq : 0 ≤ Real.sqrt F.blockSide := Real.sqrt_nonneg _
    have : Real.sqrt F.blockSide * (ρ * s) ≤ (CJ₁ + ρ + 1) * Real.sqrt F.blockSide * s := by
      have : 0 ≤ (CJ₁ + 1) * Real.sqrt F.blockSide * s := by positivity
      nlinarith
    exact this
  · exact fun Y => (hturn γ).2.2 a Y
  · exact (hturn γ).2.1
end YangMills.Construction.HoleSavings
end
