import YangMills.Construction.HoleBesideASecondHole.BadCellsPay
import YangMills.Construction.HoleBesideASecondHole.CellsKeptOffTheSpots
import YangMills.Construction.HoleBesideASecondHole.CellsPutBack
import YangMills.Construction.HoleBesideASecondHole.CrowdedCellsAreFew
import YangMills.Construction.HoleBesideASecondHole.ExcitedCellsPay
import YangMills.Construction.HoleBesideASecondHole.HolesAreFilled
import YangMills.Construction.HoleBesideASecondHole.LeastSumsOfTheLevels
import YangMills.Construction.HoleBesideASecondHole.TopHotPlaquettesPay
import YangMills.Construction.HoleBesideASecondHole.WhatAHoleSaves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HoleBounds
open BlockAverages LumpContours HoleSavings HoleFilling ChainEnergies
theorem cellsNear_eq_thickening {F : BlockFrame} (S D : Finset F.Cell) (m : ℕ) :
    cellsNear S D m = thickening S D m := by
  unfold cellsNear thickening
  congr
theorem isFillingChain_mono {F : BlockFrame} {L : ℕ} {g : LumpGrid L} {a s θ C ε ε' CJ : ℝ} {J₀ : ℕ}
    (D : HoleData F g a s θ J₀) (hle : ε ≤ ε') (U : F.FieldChain) (hU : D.IsFillingChain C ε CJ U) :
    D.IsFillingChain C ε' CJ U := by
  refine ⟨hU.1, fun X hX => (hU.2.1 X hX).trans ?_, hU.2.2⟩
  have h0 : (0 : ℝ) ≤ s ^ 2 * ((D.nearbyFineLumps X).card : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_right hle h0
  linarith
theorem mem_sitesOfCells_top {F : BlockFrame} (S : Finset F.Cell) (hL : Odd F.blockSide) :
    ∀ x ∈ S, x ∈ sitesOfCells S F.top := by
  intro x hx
  simp only [sitesOfCells, Finset.mem_biUnion, Finset.mem_image]
  refine ⟨x, hx, 0, ?_, ?_⟩
  · simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    simp
  · funext k
    simp [cellCentre, siteOfCoords, siteCoords]
theorem holeSaving_arith {σ κ cP Cb B cE A' A1 T1 E Ein x c hh v v1 bad : ℝ} (hσ : 0 ≤ σ) (hκ : 0 < κ)
    (hcP : 8 * κ ≤ cP / 2)
    (hCb : 0 ≤ Cb) (hB : B = Cb + 128 * κ + 2) (hx : 0 ≤ x) (hc : 0 ≤ c) (hh0 : 0 ≤ hh) (hv1 : 0 ≤ v1)
    (h1 : A' ≤ A1 + Cb * σ * (x + c))
    (h2 : 4 * B * σ * x ≤ E - Ein)
    (h3 : cP * σ * v1 ≤ E - Ein) (h3' : v ≤ v1 + 16 * (x + c))
    (h4 : T1 ≤ Ein + (κ / 8) * σ * hh)
    (h5 : cE * bad ≤ (κ / 4) * σ * hh + σ * x + (T1 - A1))
    (h6 : (Cb + 128 * κ) * c ≤ (κ / 8) * hh) :
    A' + 8 * κ * σ * v + (κ / 2) * σ * hh + cE * bad ≤ E + κ * σ * hh := by
  have a1 : 8 * κ * σ * v ≤ 8 * κ * σ * v1 + 128 * κ * σ * (x + c) := by
    have : 8 * κ * σ * v ≤ 8 * κ * σ * (v1 + 16 * (x + c)) :=
      mul_le_mul_of_nonneg_left h3' (by positivity)
    linarith
  have a2 : 8 * κ * σ * v1 ≤ (cP * σ * v1) / 2 := by
    have := mul_le_mul_of_nonneg_right hcP (mul_nonneg hσ hv1)
    nlinarith
  have a3 : (Cb + 128 * κ) * σ * c ≤ (κ / 8) * σ * hh := by
    have := mul_le_mul_of_nonneg_left h6 hσ
    nlinarith
  have a4 : σ * x + (Cb + 128 * κ) * σ * x ≤ (E - Ein) / 2 := by
    have e : 4 * B * σ * x / 2 = (σ * x + (Cb + 128 * κ) * σ * x) + (Cb + 128 * κ + 3) * (σ * x) := by
      rw [hB]
      ring
    have : 0 ≤ (Cb + 128 * κ + 3) * (σ * x) := by positivity
    linarith
  linarith
set_option maxHeartbeats 1600000 in
theorem holeSavingInequality_of_data (hX : excitedCellsPayStatement) (hC : KeptCellsAwayFromBad)
    (hR : CrowdedCellsBound) (hS : minimalChainEnergiesStatement)
    {F : BlockFrame} {L : ℕ} {g : LumpGrid L} {a s Θ κ ε cP Cb Ca C CJ cE r₀ : ℝ} {J₀ : ℕ}
    (hodd : Odd L) (hFL : F.blockSide = L) (hTor : IsCubicTorus F 4096)
    (ha : 1 ≤ a) (hs : 0 < s) (hΘ : 1 ≤ Θ) (hκ : 0 < κ) (hκcP : 8 * κ ≤ cP / 2) (hCa : 0 < Ca)
    (hCb : Cb = Ca * Θ ^ 2 * 2 ^ 72) (hC' : C = 4 * 10 ^ 4 * (Cb + 128 * κ + 2))
    (hJ : (Cb + 128 * κ + 2) * 2 ^ 13 ≤ κ * J₀) (hε : ε ≤ κ / 8) (hε0 : 0 < ε)
    (hr : Θ * s ≤ r₀)
    (hPut : ∀ (S S₁ : Finset F.Cell) (V : F.GaugeField F.top) (r : ℝ), 0 < r → r ≤ r₀ →
      IsOrthantRegular S 1024 → IsOrthantRegular S₁ 1024 → S₁ ⊆ S → IsCold S F.top r V →
      cutEffectiveAction a F.top S V ≤ cutEffectiveAction a F.top S₁ V + Ca * r ^ 2 * (thickening S (S \ S₁) 330).card)
    (D : HoleData F g a s (Θ * s) J₀) (hD : D.IsAdmissibleDomain) (U2 : F.FieldChain)
    (hU2 : D.IsFillingChain C ε CJ U2)
    (hTop : ∀ S₁ : Finset F.Cell, S₁ ⊆ D.keptCells → ∃ v : ℕ, D.HasCoreHotLumps C v ∧
      cP * s ^ 2 * v ≤ D.totalEnergy - D.energyOn S₁ ∧
      D.hotTopLumps.card ≤ v + 16 * ((D.excitedCells C).card + (D.crowdedCells).card))
    (hBad : ∀ (S₁ : Finset F.Cell) (Wl : F.GaugeField F.depth), S₁ ⊆ D.keptCells → IsOrthantRegular S₁ 1024 →
      (∀ y ∈ S₁, ∀ z ∈ D.badCells C, 10 < cellSupDist y z) →
      (∀ m : ℕ, (thickening D.keptCells (D.keptCells \ S₁) m).card ≤
        max ((2 ^ 17 + 2 * m) ^ 4) (2 ^ 72) * ((D.excitedCells C).card + (D.crowdedCells).card)) →
      IsMinimizingField a D.keptCells D.topField Wl →
      cE * (badCells (s / 128) D.keptCells D.topField D.fineField Wl).card ≤
        (κ / 4) * s ^ 2 * D.hotFineLumps.card + s ^ 2 * (D.excitedCells C).card +
        (plainBlockEnergy a S₁ (U2 F.depth) D.topField - cutEffectiveAction a F.top S₁ D.topField))
    (Wl : F.GaugeField F.depth) (hWl : IsMinimizingField a D.keptCells D.topField Wl) :
    HoleSavingInequality g a κ s cE J₀ D.cells D.keptCells D.hotTopLumps D.topField D.fineField D.base Wl := by
  classical
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hCa0 : 0 ≤ Ca * Θ ^ 2 * 2 ^ 72 := by positivity
  obtain ⟨hreg, hcold, S₁, hsub, hreg1, hdist, hcount⟩ := hC F L g a s (Θ * s) C J₀ D hFL hodd hTor hD
  obtain ⟨v, -, hv1, hv2⟩ := hTop S₁ hsub
  have hkS : D.keptCells ⊆ D.cells := Finset.sdiff_subset
  have hSsub : S₁ ⊆ D.cells := hsub.trans hkS
  have p1 := hPut D.keptCells S₁ D.topField (Θ * s) (by positivity) hr hreg hreg1 hsub hcold
  have p2 := hX F L g a s (Θ * s) C J₀ D S₁ ha0 hFL hodd hTor hSsub hdist
  have p3 := hBad S₁ Wl hsub hreg1 hdist hcount hWl
  have p4 := hR F L g a s (Θ * s) J₀ D hFL hodd hTor
  have hcore : S₁ ⊆ D.coreCells C 5 := by
    intro y hy
    refine Finset.mem_filter.2 ⟨hSsub hy, fun z hz => ?_⟩
    have := hdist y hy z hz
    omega
  have p5 := hU2.2.1 S₁ hcore
  have p6 : plainBlockEnergy a S₁ (U2 F.depth) D.topField ≤ D.energyOn S₁ + (κ / 8) * s ^ 2 * D.hotFineLumps.card := by
    have hpl := (hS F a ha0 (hFL ▸ hodd)).2.2.2.1 S₁ U2
    rw [hU2.1] at hpl
    have hnear : ((D.nearbyFineLumps S₁).card : ℝ) ≤ (D.hotFineLumps.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hq : ε * s ^ 2 * ((D.nearbyFineLumps S₁).card : ℝ) ≤ (κ / 8) * s ^ 2 * (D.hotFineLumps.card : ℝ) := by
      have h0 : (0 : ℝ) ≤ ((D.nearbyFineLumps S₁).card : ℝ) := by positivity
      have hs2 : (0 : ℝ) ≤ s ^ 2 := by positivity
      calc ε * s ^ 2 * ((D.nearbyFineLumps S₁).card : ℝ) ≤ (κ / 8) * s ^ 2 * ((D.nearbyFineLumps S₁).card : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε hs2) h0
        _ ≤ _ := mul_le_mul_of_nonneg_left hnear (by positivity)
    linarith
  have e_left : D.totalEnergy = cutEffectiveAction a F.depth D.chainSites D.fineField +
      a * ∑ c ∈ cutBonds D.cells, D.topBondFit c := by
    have e1 : D.chainSites ∩ cutBelow F.depth D.cells = D.chainSites := Finset.inter_eq_left.2 Finset.sdiff_subset
    unfold HoleData.totalEnergy HoleData.energyOn
    rw [e1]
    congr 1
    exact D.chain_minimal
  set x : ℝ := ((D.excitedCells C).card : ℝ) with hx
  set c : ℝ := ((D.crowdedCells).card : ℝ) with hc
  set hh : ℝ := (D.hotFineLumps.card : ℝ) with hhh
  set B := Cb + 128 * κ + 2 with hBdef
  have hCb0 : 0 ≤ Cb := by rw [hCb]; exact hCa0
  have hx0 : 0 ≤ x := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hh0 : 0 ≤ hh := by positivity
  have h1 : cutEffectiveAction a F.top D.keptCells D.topField ≤
      cutEffectiveAction a F.top S₁ D.topField + Cb * s ^ 2 * (x + c) := by
    refine p1.trans ?_
    have hcr : ((thickening D.keptCells (D.keptCells \ S₁) 330).card : ℝ) ≤ 2 ^ 72 * (x + c) := by
      have h330 := hcount 330
      have hmax : max ((2 ^ 17 + 2 * 330) ^ 4) (2 ^ 72) = 2 ^ 72 := max_eq_right (by norm_num)
      rw [hmax] at h330
      rw [hx, hc]
      exact_mod_cast h330
    have e : Cb * s ^ 2 * (x + c) = Ca * (Θ * s) ^ 2 * (2 ^ 72 * (x + c)) := by
      rw [hCb]
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hcr (by positivity : 0 ≤ Ca * (Θ * s) ^ 2)
    linarith
  have h2 : 4 * B * s ^ 2 * x ≤ D.totalEnergy - D.energyOn S₁ := by
    rw [hC'] at p2
    linarith only [p2]
  have h3' : (D.hotTopLumps.card : ℝ) ≤ (v : ℝ) + 16 * (x + c) := by
    rw [hx, hc]
    exact_mod_cast hv2
  have h6 : (Cb + 128 * κ) * c ≤ (κ / 8) * hh := by
    have q1 : (J₀ : ℝ) * c ≤ 625 * hh := by
      rw [hc, hhh]
      exact_mod_cast p4
    have q2 : B * 2 ^ 13 * c ≤ κ * (J₀ * c) := by
      have := mul_le_mul_of_nonneg_right hJ hc0
      linarith
    have q3 : κ * (J₀ * c) ≤ κ * (625 * hh) := mul_le_mul_of_nonneg_left q1 hκ.le
    have q4 : (Cb + 128 * κ) * c ≤ B * c := by
      have : Cb + 128 * κ ≤ B := by rw [hBdef]; linarith
      exact mul_le_mul_of_nonneg_right this hc0
    have q5 : 0 ≤ κ * hh := by positivity
    linarith only [q2, q3, q4, q5]
  have hfinal := holeSaving_arith (σ := s ^ 2) (κ := κ) (cP := cP) (Cb := Cb) (B := B) (cE := cE)
    (A' := cutEffectiveAction a F.top D.keptCells D.topField) (A1 := cutEffectiveAction a F.top S₁ D.topField)
    (T1 := plainBlockEnergy a S₁ (U2 F.depth) D.topField) (E := D.totalEnergy) (Ein := D.energyOn S₁)
    (x := x) (c := c)
    (hh := hh) (v := (D.hotTopLumps.card : ℝ)) (v1 := (v : ℝ))
    (bad := ((badCells (s / 128) D.keptCells D.topField D.fineField Wl).card : ℝ))
    (by positivity) hκ hκcP hCb0 rfl hx0 hc0 hh0 (by positivity) h1 h2 hv1 h3' p6 p3 h6
  unfold HoleSavingInequality
  change cutEffectiveAction a F.top D.keptCells D.topField + 8 * κ * s ^ 2 * (D.hotTopLumps.card : ℝ) +
      (κ / 2) * s ^ 2 * hh +
      cE * ((badCells (s / 128) D.keptCells D.topField D.fineField Wl).card : ℝ) ≤
    cutEffectiveAction a F.depth D.chainSites D.fineField + κ * s ^ 2 * hh +
      a * ∑ c ∈ cutBonds D.cells, D.topBondFit c
  rw [e_left] at hfinal
  linarith
theorem holeSavingStatement_proof (hE : ReinsertionCostEstimate) (hX : excitedCellsPayStatement)
    (hF : holesFilledStatement) (hT : topHotPlaquettesPaidStatement) (hC : KeptCellsAwayFromBad)
    (hB : BadCellsBound) (hR : CrowdedCellsBound) (hS : minimalChainEnergiesStatement) :
    holeSavingStatement := by
  intro a ha
  obtain ⟨cP, hcP, hT1⟩ := hT
  have hκ : 0 < min (cP / 16) (1 / 8) := lt_min (by positivity) (by norm_num)
  refine ⟨min (cP / 16) (1 / 8), hκ, min_le_right _ _, fun Θ hΘ => ?_⟩
  have hκ16 : min (cP / 16) (1 / 8) ≤ cP / 16 := min_le_left _ _
  set κ := min (cP / 16) (1 / 8) with hκdef
  obtain ⟨Ca, hCa, L₁, hE1⟩ := hE a (by linarith)
  set Cb := Ca * Θ ^ 2 * 2 ^ 72 with hCb
  set C := 4 * 10 ^ 4 * (Cb + 128 * κ + 2) with hC'
  have hC0 : 0 < C := by positivity
  refine ⟨max 625 ⌈(Cb + 128 * κ + 2) * 2 ^ 13 / κ⌉₊, fun J₀ hJ₀ => ?_⟩
  have hJ625 : 625 ≤ J₀ := (le_max_left _ _).trans hJ₀
  have hJ : (Cb + 128 * κ + 2) * 2 ^ 13 ≤ κ * J₀ := by
    have h1 : (Cb + 128 * κ + 2) * 2 ^ 13 / κ ≤ J₀ :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hJ₀)
    rw [div_le_iff₀ hκ] at h1
    linarith
  obtain ⟨εT, hεT, hT1'⟩ := hT1 J₀ hJ625
  have hε : 0 < min εT (κ / 8) := lt_min hεT (by positivity)
  obtain ⟨CJ, hCJ, L₂, hF1⟩ := hF a (min εT (κ / 8)) Θ C J₀ ha hε hΘ hC0 hJ625
  obtain ⟨L₃, hT2⟩ := hT1' a Θ C CJ ha hΘ hC0 hCJ
  obtain ⟨L₄, hB1⟩ := hB a κ (min εT (κ / 8)) Θ C CJ J₀ ha hκ hε hΘ hC0 hCJ hJ625
  refine ⟨max (max L₁ L₂) (max L₃ L₄), fun L hodd hL g => ?_⟩
  have l1 : L₁ ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have l2 : L₂ ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have l3 : L₃ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have l4 : L₄ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  obtain ⟨CL, r₀, hCL, hr₀, hE2⟩ := hE1 L hodd l1
  obtain ⟨s₁, hs₁, hF2⟩ := hF1 L hodd l2 g
  obtain ⟨s₂, hs₂, hT3⟩ := hT2 L hodd l3 g
  obtain ⟨s₃, hs₃, hB2⟩ := hB1 L hodd l4 g
  have hΘ0 : 0 < Θ := by linarith
  refine ⟨min (min s₁ s₂) (min s₃ (r₀ / Θ)), by positivity, fun s hs hs₀ => ?_⟩
  have m1 : s ≤ s₁ := hs₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have m2 : s ≤ s₂ := hs₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have m3 : s ≤ s₃ := hs₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have m4 : s ≤ r₀ / Θ := hs₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr : Θ * s ≤ r₀ := by
    rw [le_div_iff₀ hΘ0] at m4
    linarith
  obtain ⟨cE, hcE, hB3⟩ := hB2 s hs m3
  have hκcP : 8 * κ ≤ cP / 2 := by linarith
  have ha0 : (0 : ℝ) ≤ a := by linarith
  refine ⟨cE, hcE, fun F hFL hTor => ?_⟩
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have hAmb : IsAdmissibleAmbient F := Or.inr fun i => by
    have := hTor.2
    rw [hTor.1 i]
    omega
  have key : ∀ (D : HoleData F g a s (Θ * s) J₀), D.IsAdmissibleDomain → ∀ Wl : F.GaugeField F.depth,
      IsMinimizingField a D.keptCells D.topField Wl →
      HoleSavingInequality g a κ s cE J₀ D.cells D.keptCells D.hotTopLumps D.topField D.fineField D.base Wl := by
    intro D hD Wl hWl
    obtain ⟨U2, hU2⟩ := hF2 s hs m1 F D hFL hTor hD
    have hU2' : D.IsFillingChain C εT CJ U2 := isFillingChain_mono D (min_le_left _ _) U2 hU2
    exact holeSavingInequality_of_data hX hC hR hS hodd hFL hTor ha hs hΘ hκ hκcP hCa rfl rfl hJ
      (min_le_right _ _) hε hr
      (fun S S₁ V r h1 h2 h3 h4 h5 h6 => by
        have := (hE2 F S S₁ hFL hAmb h5 h3 h4 r V h1 h2 h6).1
        rw [← cellsNear_eq_thickening]
        exact this)
      D hD U2 hU2 (fun S₁ h => hT3 s hs m2 F D U2 S₁ hFL hTor hD hU2' h)
      (fun S₁ Wl' h1 h2 h3 h4 h5 => hB3 F D U2 S₁ Wl' hFL hTor hD hU2 h1 h2 h3 h4 h5) Wl hWl
  have leastChain := (hS F a ha0 hoddF).1
  constructor
  · intro hdvd H hH V W b Wl hWall hBases hWl
    obtain ⟨U, hU1, hU2⟩ := leastChain F.depth
      (cutBelow F.depth (cellsOffLumps F H) \
        lumpsNeighbourhood (hotLumps g s (cutBelow F.depth (cellsOffLumps F H)) W)) W (by simp)
    exact key ⟨cellsOffLumps F H, V, W, b, U, hU1, hU2, hWall, hBases⟩ (Or.inl ⟨H, hH, hdvd, rfl⟩) Wl hWl
  · intro V W b Wl hCold hBases hWl
    obtain ⟨U, hU1, hU2⟩ := leastChain F.depth
      (cutBelow F.depth (torusCells F) \
        lumpsNeighbourhood (hotLumps g s (cutBelow F.depth (torusCells F)) W)) W (by simp)
    have hwall : HasLumpWall (torusCells F) (hotLumps g s (cutBelow F.depth (torusCells F)) W) := by
      intro l _ y _ _ z hz
      simp at hz
    let D : HoleData F g a s (Θ * s) J₀ := ⟨torusCells F, V, W, b, U, hU1, hU2, hwall, hBases⟩
    have hempty : D.hotTopLumps = ∅ := by
      have hf : ((cutPlaquettes (torusCells F)).filter fun p => Θ * s ≤ plaquetteDefect V p) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun p hp h => ?_
        have hp' := Finset.mem_filter.1 hp
        have hin : ∀ x ∈ torusCells F, x ∈ sitesOfCells (torusCells F) F.top :=
          mem_sitesOfCells_top _ hoddF
        have hq : p ∈ innerPlaquettes (torusCells F) F.top := by
          refine Finset.mem_filter.2 ⟨?_, hp'.2.1, hp'.2.2.trans hin⟩
          have h3 := Finset.mem_product.1 hp'.1
          exact Finset.mem_product.2 ⟨hin _ h3.1, h3.2⟩
        exact absurd h (not_le.2 (hCold p hq))
      show hotLumps g (Θ * s) (torusCells F) V = ∅
      unfold hotLumps
      rw [hf]
      simp
    have hkept : D.keptCells = torusCells F := by
      simp [HoleData.keptCells, hempty, lumpsNeighbourhood]
      rfl
    have h1 := key D (Or.inr ⟨rfl, hCold⟩) Wl (by rw [hkept]; exact hWl)
    rw [hkept, hempty] at h1
    exact h1
end YangMills.Construction.HoleBounds
end
