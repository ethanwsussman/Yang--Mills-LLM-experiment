import YangMills.Construction.ClusterExpansionOfAStep.PlainFitsAlongMoves
import YangMills.Construction.ColdStepAtMirrorFrames.ColdChainOneLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.CompositesAtAPoint
import YangMills.Construction.ColdStepAtMirrorFrames.FitsAlongMoves
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheBlockEnergy
import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.ThroughTheMovedChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace CellEnergyKernels
open BlockOffsets
theorem ediv_add_bounds {L : ℤ} (hL : 0 < L) (u d : ℤ) (hd : 0 ≤ d) : u / L ≤ (u + d) / L ∧ (u + d) / L ≤ u / L + d := by
  refine ⟨Int.ediv_le_ediv hL (by linarith), ?_⟩
  have h1 : (u + d) / L ≤ (u + d * L) / L := Int.ediv_le_ediv hL (by nlinarith)
  rwa [Int.add_mul_ediv_right _ _ hL.ne'] at h1
theorem natAbs_ediv_add_sub_le {L : ℤ} (hL : 0 < L) (u d : ℤ) : ((u + d) / L - u / L).natAbs ≤ d.natAbs := by
  rcases le_total 0 d with hd | hd
  · obtain ⟨h1, h2⟩ := ediv_add_bounds hL u d hd
    omega
  · obtain ⟨h1, h2⟩ := ediv_add_bounds hL (u + d) (-d) (by omega)
    have e : u + d + -d = u := by ring
    rw [e] at h1 h2
    omega
theorem natAbs_valMinAbs_intCast_le {n : ℕ} [NeZero n] (e : ℤ) : ((e : ZMod n)).valMinAbs.natAbs ≤ e.natAbs := by apply _root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le <;> assumption
variable {F : BlockFrame} {k : ℕ}
theorem neZero_period_top (hs : ∀ i, 2 ≤ F.extent i) (i : Fin 4) : NeZero (F.period F.top i) := ⟨by
  rw [period_top]
  have := hs i
  omega⟩
theorem neZero_period_depth (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (i : Fin 4) :
    NeZero (F.period F.depth i) := ⟨by
  rw [period_depth]
  have h1 := hs i
  obtain ⟨m, hm⟩ := hL
  have h2 : 0 < F.blockSide := by omega
  have h3 : 0 < F.extent i := by omega
  exact (Nat.mul_pos h3 h2).ne'⟩
theorem cellSupDist_enclosingCell_le (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x y : F.Site F.depth) :
    cellSupDist (enclosingCell x) (enclosingCell y) ≤ siteSupDist x y := by
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  have hb : ((x i - y i).valMinAbs).natAbs ≤ siteSupDist x y :=
    Finset.le_sup (f := fun i => ((x i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
  refine le_trans ?_ hb
  haveI := neZero_period_top hs i
  haveI := neZero_period_depth hL hs i
  have hLpos : (0 : ℤ) < F.blockSide := by
    obtain ⟨m, hm⟩ := hL
    have : 0 < F.blockSide := by omega
    exact_mod_cast this
  set d : ℤ := (x i - y i).valMinAbs with hd
  set X : ℤ := siteCoords x i with hX
  set Y : ℤ := siteCoords y i with hY
  set hh : ℤ := ((F.blockSide : ℤ) - 1) / 2 with hhh
  have hxy : ((X : ℤ) : ZMod (F.period F.depth i)) = ((Y + d : ℤ) : ZMod (F.period F.depth i)) := by
    have e1 : ((X : ℤ) : ZMod (F.period F.depth i)) = x i := ZMod.intCast_zmod_cast (x i)
    have e2 : ((Y : ℤ) : ZMod (F.period F.depth i)) = y i := ZMod.intCast_zmod_cast (y i)
    have e3 : ((d : ℤ) : ZMod (F.period F.depth i)) = x i - y i := ZMod.coe_valMinAbs _
    push_cast
    rw [e1, e2, e3]
    ring
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hxy
  obtain ⟨m, hm⟩ := hxy
  have hP : ((F.period F.depth i : ℕ) : ℤ) = (F.extent i : ℤ) * F.blockSide := by
    rw [period_depth]
    push_cast
    ring
  rw [hP] at hm
  have eX : X = Y + d - (F.extent i : ℤ) * F.blockSide * m := by linarith
  have hc : ∀ z : F.Site F.depth, enclosingCell z i =
      ((((siteCoords z i + hh) / (F.blockSide : ℤ) : ℤ)) : ZMod (F.period F.top i)) := by
    intro z
    change (((siteCoords z i + ((F.blockSide : ℤ) ^ (F.top - F.depth) - 1) / 2) /
      (F.blockSide : ℤ) ^ (F.top - F.depth) : ℤ) : ZMod (F.period F.top i)) = _
    rw [top_sub_depth, pow_one]
  have eA : (X + hh) / (F.blockSide : ℤ) = (Y + hh + d) / (F.blockSide : ℤ) - (F.extent i : ℤ) * m := by
    have e : X + hh = (Y + hh + d) + (-((F.extent i : ℤ) * m)) * F.blockSide := by
      rw [eX]
      ring
    rw [e, Int.add_mul_ediv_right _ _ hLpos.ne']
    ring
  have hdiff : enclosingCell x i - enclosingCell y i =
      ((((Y + hh + d) / (F.blockSide : ℤ) - (Y + hh) / (F.blockSide : ℤ) : ℤ)) : ZMod (F.period F.top i)) := by
    rw [hc x, hc y, eA]
    push_cast
    rw [extent_cast_eq_zero, zero_mul, sub_zero]
  change (((enclosingCell x i - enclosingCell y i)).valMinAbs).natAbs ≤ _
  rw [hdiff]
  exact (natAbs_valMinAbs_intCast_le _).trans (natAbs_ediv_add_sub_le hLpos _ _)
theorem cellSupDist_self (y : F.Cell) : cellSupDist y y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_add_unitStep_le (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (i : Fin 4) :
    cellSupDist z (z + unitStep F.top i) ≤ 1 := by
  unfold cellSupDist
  refine Finset.sup_le fun l _ => ?_
  haveI := neZero_period_top hs l
  have e : z l - (z + unitStep F.top i : F.Cell) l =
      (((-(Pi.single i 1 : Fin 4 → ℤ) l : ℤ)) : ZMod (F.period F.top l)) := by
    simp [unitStep, siteOfCoords]
  rw [e]
  refine (natAbs_valMinAbs_intCast_le _).trans ?_
  by_cases hl : l = i
  · subst hl
    simp
  · simp [Pi.single_eq_of_ne hl]
open Classical in
def directionBonds : ChartDirection F → Finset (F.Site F.depth × Fin 4)
  | .inl p => {(p.1, p.2.1)}
  | .inr p => (centredCube F.blockSide).image fun h => (cellCentre F.depth p.1 + siteOfCoords F.depth h, p.2.1)
theorem card_directionBonds_le (q : ChartDirection F) :
    (directionBonds q).card ≤ (centredCube F.blockSide).card + 1 := by
  rcases q with p | p
  · simp [directionBonds]
  · exact Finset.card_image_le.trans (Nat.le_succ _)
theorem enclosingCell_of_mem_directionBonds (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    {q : ChartDirection F} {b : F.Site F.depth × Fin 4}
    (hb : b ∈ directionBonds q) : enclosingCell b.1 = directionCell q := by
  rcases q with p | p
  · have : b = (p.1, p.2.1) := by simpa [directionBonds] using hb
    subst this
    rfl
  · obtain ⟨h, hh, e⟩ := Finset.mem_image.mp hb
    subst e
    exact enclosingCell_offset hL hs p.1 h hh
theorem mem_directionBonds_of_moves (hsites : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (q₀ : ChartDirection F) (b : F.Site F.depth × Fin 4)
    (h : directionCoordinate q₀ b.1 b.2 ≠ 0 ∨ (IsCrossingBond b ∧ directionMove q₀ (enclosingCell b.1) b.2 ≠ 0)) :
    b ∈ directionBonds q₀ := by
  classical
  rcases q₀ with p | p
  · rcases h with h | ⟨-, h⟩
    · simp only [directionCoordinate] at h
      split_ifs at h with e
      · simp only [directionBonds, Finset.mem_singleton]
        exact Prod.ext e.1.symm e.2.symm
      · exact absurd rfl h
    · simp [directionMove] at h
  · rcases h with h | ⟨-, h⟩
    · simp [directionCoordinate] at h
    · simp only [directionMove] at h
      split_ifs at h with e
      · obtain ⟨-, h2, -, -⟩ := hsites F hL hs
        have hx := h2 b.1
        refine Finset.mem_image.mpr ⟨cellOffset b.1, hx.2, ?_⟩
        show (cellCentre F.depth p.1 + siteOfCoords F.depth (cellOffset b.1), p.2.1) = b
        rw [e.1, e.2, hx.1]
      · exact absurd rfl h
theorem norm_directionCoordinate_le (q₀ : ChartDirection F) (h : ‖directionVector q₀‖ = 1) (x : F.Site F.depth)
    (i : Fin 4) : ‖directionCoordinate q₀ x i‖ ≤ 1 := by
  rcases q₀ with p | p
  · simp only [directionCoordinate]
    split_ifs
    · exact h.le
    · simp
  · simp [directionCoordinate]
theorem norm_directionMove_le (q₀ : ChartDirection F) (h : ‖directionVector q₀‖ = 1) (y : F.Site F.top) (i : Fin 4) :
    ‖directionMove q₀ y i‖ ≤ 1 := by
  rcases q₀ with p | p
  · simp [directionMove]
  · simp only [directionMove]
    split_ifs
    · exact h.le
    · simp
theorem norm_piSingle_one_le (l : Fin k) : ‖(Pi.single l (1 : ℝ) : Fin k → ℝ)‖ ≤ 1 := by apply _root_.YangMills.Construction.PlainAlignment.norm_single_le_one <;> assumption
def bondsAtCell (y : F.Cell) : Finset (F.Cell × Fin 4) := by
  classical exact (Finset.univ.image fun i : Fin 4 => (y, i)) ∪
    (Finset.univ.image fun i : Fin 4 => (y - unitStep F.top i, i))
theorem card_bondsAtCell_le (y : F.Cell) : (bondsAtCell y).card ≤ 8 := by
  classical
  unfold bondsAtCell
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : (Finset.univ.image fun i : Fin 4 => (y, i)).card ≤ 4 := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 4))) (f := fun i : Fin 4 => (y, i))
  have h2 : (Finset.univ.image fun i : Fin 4 => (y - unitStep F.top i, i)).card ≤ 4 := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 4)))
      (f := fun i : Fin 4 => (y - unitStep F.top i, i))
  omega
theorem mem_bondsAtCell {y : F.Cell} {c : F.Cell × Fin 4} (h : y = c.1 ∨ y = c.1 + unitStep F.top c.2) :
    c ∈ bondsAtCell y := by
  classical
  unfold bondsAtCell
  rw [Finset.mem_union]
  rcases h with h | h
  · left
    exact Finset.mem_image.mpr ⟨c.2, Finset.mem_univ _, by rw [h]⟩
  · right
    exact Finset.mem_image.mpr ⟨c.2, Finset.mem_univ _, by rw [h]; simp⟩
end CellEnergyKernels
open CellEnergyKernels BlockOffsets in
theorem cellEnergyKernelBound_of_estimates (hch : ColdEstimatesAtEveryDepth) (hth : TranslatedChartCompositeBound)
    (hfit : BlockFitAnalyticAlongTranslates) (hcp : YangMills.Construction.Calculus.CompositeDerivativesAtPoint)
    (hsites : SiteDecomposition) (hcover : BlocksCoverLowerLevel) : CellEnergyKernelBound := by
  classical
  obtain ⟨-, hNot, -, -⟩ := hcp
  obtain ⟨C1, hC10, hth⟩ := hth
  intro a L c ha hLo hL40 hc
  obtain ⟨N, hN0, hNc⟩ := hch a L c ha hLo hL40 hc
  obtain ⟨C2, hC20, hfit⟩ := hfit L hLo
  have hδ : 0 < c.δ₁ := hc.positivity.1
  have ha0 : 0 < a := by linarith
  set M : ℕ := (centredCube L).card + 1 with hM
  set Nx : ℕ → ℝ := fun k => ∑ p ∈ Finset.range (k + 1), N p with hNx
  have hNx0 : ∀ k, 0 ≤ Nx k := fun k => Finset.sum_nonneg fun p _ => (hN0 p).le
  refine ⟨fun k => (M : ℝ) * (C1 k M * Nx k) + a * (8 * C2 k k * Real.exp c.δ₁) + 1, fun k => ?_, ?_⟩
  · have h1 := hC10 k M
    have h2 := hNx0 k
    have h3 := hC20 k k
    have h4 := Real.exp_pos c.δ₁
    positivity
  intro F w V hF hS Y k q
  have hFL : F.blockSide = L := hF.1
  obtain ⟨nside, h64, hside⟩ := hF.2
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside i]
    omega
  have hLF : Odd F.blockSide := by rw [hFL]; exact hLo
  set ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions := fun l => directionCoordinate (q l) with hξdef
  set μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions := fun l => directionMove (q l) with hμdef
  set fitc : F.Site F.top × Fin 4 → (Fin k → ℝ) → ℝ := fun cb σ =>
    blockFit (translatedChart w V ξ μ σ) (translatedTop V μ σ) cb with hfitc
  set Ys := (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y) with hYs
  set B := (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y ∨ c.1 + unitStep F.top c.2 = Y) with hBdef
  have hblock : cellEnergyAlong a Y w V q = fun σ =>
      (∑ y ∈ Ys, minimalSiteShare a y (translatedChart w V ξ μ σ)) + a / 2 * ∑ cb ∈ B, fitc cb σ := rfl
  have hJ : ∀ l b, ParameterMovesBond ξ μ l b → b ∈ directionBonds (q l) := fun l b h =>
    mem_directionBonds_of_moves hsites hLF hs (q l) b h
  have hHold : ColdEstimatesBelow a c.δ₁ c.σA N (chartedField w V) :=
    hNc.1 F c.σA _ ⟨hFL, nside, h64, hside⟩ hc.positivity.2.2.2.1 le_rfl hS.small_curvature
  set e : ℝ := Real.exp (-(c.δ₁ * (directionReach Y q : ℝ))) with he
  have he0 : 0 < e := Real.exp_pos _
  have hthy := fun y => hth F (minimalSiteShare a y) w V k ξ μ (fun l => directionBonds (q l)) M (Nx k * e) hJ
    (fun n b X => hHold.siteShare_analytic y n b X)
  have hA1 : ∀ y, AnalyticAt ℝ (fun σ => minimalSiteShare a y (translatedChart w V ξ μ σ)) 0 := fun y => (hthy y).1
  have hfc := fun cb => hfit F w V k ξ μ cb hFL hs hS.coord_small
  have hA2 : ∀ cb, AnalyticAt ℝ (fitc cb) 0 := fun cb => (hfc cb).1
  have hSumY : AnalyticAt ℝ (fun σ => ∑ y ∈ Ys, minimalSiteShare a y (translatedChart w V ξ μ σ)) 0 :=
    Finset.analyticAt_fun_sum _ fun y _ => hA1 y
  have hSum : AnalyticAt ℝ (fun σ => ∑ cb ∈ B, fitc cb σ) 0 :=
    Finset.analyticAt_fun_sum _ fun cb _ => hA2 cb
  have hAS : AnalyticAt ℝ (fun σ => a / 2 * ∑ cb ∈ B, fitc cb σ) 0 := analyticAt_const.mul hSum
  refine ⟨?_, ?_⟩
  · rw [hblock]
    exact hSumY.add hAS
  intro hk1 hu
  have hξ : ∀ l (b : F.Site F.depth × Fin 4), ‖ξ l b.1 b.2‖ ≤ 1 := fun l b =>
    norm_directionCoordinate_le _ (hu l) _ _
  have hμ : ∀ l y i, ‖μ l y i‖ ≤ 1 := fun l y i => norm_directionMove_le _ (hu l) _ _
  have hL1 : (1 : ℝ) ≤ L := by
    have : 1 ≤ L := by omega
    exact_mod_cast this
  have hw1 : ∀ b : F.Site F.depth × Fin 4, ‖w b.1 b.2‖ ≤ 1 ∨ IsAxialTreeBond b := by
    intro b
    by_cases ht : IsAxialTreeBond b
    · exact Or.inr ht
    · left
      have hpos : ∀ i, 0 < F.extent i := fun i => by
        have := hs i
        omega
      have hmem : b ∈ chordBonds (finiteCells F) := by
        unfold chordBonds innerBonds
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hcover F hLF hpos _, Finset.mem_univ _⟩, hcover F hLF hpos _⟩, ht⟩
      refine (hS.coord_small b hmem).trans ?_
      rw [div_le_one (by positivity)]
      linarith
  have hcard : ∀ l, (directionBonds (q l)).card ≤ M := fun l => by
    have := card_directionBonds_le (q l)
    rw [hFL] at this
    exact this
  have hcell : ∀ l b, b ∈ directionBonds (q l) → enclosingCell b.1 = directionCell (q l) := fun l b hb =>
    enclosingCell_of_mem_directionBonds hLF hs hb
  have hbound : ∀ y ∈ Ys, ∀ (p : ℕ) (b : Fin p → F.Site F.depth × Fin 4) (X : Fin p → imaginaryQuaternions),
      1 ≤ p → p ≤ k → AreUnitVectors X →
      (∀ l, ∃ m, b m ∈ directionBonds (q l)) → |bondDeriv (minimalSiteShare a y) (chartedField w V) b X| ≤ Nx k * e := by
    intro y hy p b X hp hpk hX hcomp
    have h1 := hHold.siteShare_deriv_decay y p b X hp hX
    have hyY : enclosingCell y = Y := (Finset.mem_filter.mp hy).2
    have hd : directionReach Y q ≤ bondListDist y b := by
      unfold directionReach
      refine Finset.sup_le fun l _ => ?_
      obtain ⟨m, hm⟩ := hcomp l
      rw [← hcell l _ hm, ← hyY]
      refine (cellSupDist_enclosingCell_le hLF hs _ _).trans ?_
      unfold bondListDist
      exact Finset.le_sup (f := fun m => siteSupDist y (b m).1) (Finset.mem_univ m)
    have h2 : Real.exp (-c.δ₁ * (bondListDist y b : ℝ)) ≤ e := by
      refine Real.exp_le_exp.mpr ?_
      have : (directionReach Y q : ℝ) ≤ bondListDist y b := by exact_mod_cast hd
      nlinarith
    have h3 : N p ≤ Nx k := Finset.single_le_sum (f := fun p => N p) (fun p _ => (hN0 p).le)
      (Finset.mem_range.mpr (by omega))
    refine h1.trans ?_
    exact mul_le_mul h3 h2 (Real.exp_pos _).le (hNx0 k)
  have hYcard : Ys.card ≤ M := by
    obtain ⟨-, h2, -, -⟩ := hsites F hLF hs
    have h3 : Ys.card ≤ (centredCube F.blockSide).card := by
      refine Finset.card_le_card_of_injOn cellOffset (fun y _ => (h2 y).2) ?_
      intro y hy y' hy' e1
      have hy1 : enclosingCell y = Y := (Finset.mem_filter.mp hy).2
      have hy2 : enclosingCell y' = Y := (Finset.mem_filter.mp hy').2
      rw [← (h2 y).1, ← (h2 y').1, hy1, hy2, e1]
    rw [hFL] at h3
    omega
  set units : Fin k → Fin k → ℝ := fun l => Pi.single l 1 with hunits
  have hsplit : cellEnergyKernel a Y w V q =
      (∑ y ∈ Ys, iteratedFDeriv ℝ k (fun σ => minimalSiteShare a y (translatedChart w V ξ μ σ)) 0 units) +
      a / 2 * ∑ cb ∈ B, iteratedFDeriv ℝ k (fitc cb) 0 units := by
    unfold cellEnergyKernel
    rw [hblock]
    have e1 : (fun σ => (∑ y ∈ Ys, minimalSiteShare a y (translatedChart w V ξ μ σ)) + a / 2 * ∑ cb ∈ B, fitc cb σ) =
        (fun σ => ∑ y ∈ Ys, minimalSiteShare a y (translatedChart w V ξ μ σ)) +
          fun σ => a / 2 * ∑ cb ∈ B, fitc cb σ := rfl
    have e2 : (fun σ : Fin k → ℝ => a / 2 * ∑ cb ∈ B, fitc cb σ) = (a / 2) • fun σ => ∑ cb ∈ B, fitc cb σ := rfl
    rw [e1, iteratedFDeriv_add_apply hSumY.contDiffAt hAS.contDiffAt, e2,
      iteratedFDeriv_const_smul_apply hSum.contDiffAt,
      iteratedFDeriv_fun_sum_apply fun cb _ => (hA2 cb).contDiffAt,
      iteratedFDeriv_fun_sum_apply fun y _ => (hA1 y).contDiffAt]
    simp only [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
      ContinuousMultilinearMap.sum_apply]
    rfl
  have hy1 : ∀ y ∈ Ys, |iteratedFDeriv ℝ k (fun σ => minimalSiteShare a y (translatedChart w V ξ μ σ)) 0 units| ≤
      C1 k M * (Nx k * e) :=
    fun y hy => (hthy y).2 hw1 hξ hμ hcard (mul_nonneg (hNx0 k) he0.le) hk1 (hbound y hy)
  have hle : ∀ cb, |iteratedFDeriv ℝ k (fitc cb) 0 units| ≤ C2 k k := fun cb =>
    (hfc cb).2.1 hξ hμ k units fun m => norm_piSingle_one_le m
  have hz : ∀ cb l, ¬ ParameterTouchesBond ξ μ l cb → iteratedFDeriv ℝ k (fitc cb) 0 units = 0 := by
    intro cb l hl
    refine hNot k k ℝ (fitc cb) l units l (hA2 cb) (fun σ s => ?_) rfl
    refine (hfc cb).2.2 _ _ fun l' hl' => ?_
    have hne : l' ≠ l := fun e' => hl (e' ▸ hl')
    simp [Function.update_of_ne hne]
  have htouch : ∀ l cb, ParameterTouchesBond ξ μ l cb →
      directionCell (q l) = cb.1 ∨ directionCell (q l) = cb.1 + unitStep F.top cb.2 := by
    intro l cb h
    rcases h with h | ⟨b, hb, hr⟩
    · left
      rcases hq : q l with p | p
      · simp [hμdef, hq, directionMove] at h
      · have h' : directionMove (q l) cb.1 cb.2 ≠ 0 := h
        rw [hq] at h'
        simp only [directionMove] at h'
        split_ifs at h' with e'
        · exact e'.1
        · exact absurd rfl h'
    · have := hcell l b (hJ l b hr)
      rw [← this]
      exact hb
  set R := B.filter fun cb => ∀ l, ParameterTouchesBond ξ μ l cb with hR
  have hsumR : ∑ cb ∈ B, iteratedFDeriv ℝ k (fitc cb) 0 units = ∑ cb ∈ R, iteratedFDeriv ℝ k (fitc cb) 0 units := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun cb hb hnot => ?_
    have : ¬ ∀ l, ParameterTouchesBond ξ μ l cb := fun h => hnot (Finset.mem_filter.mpr ⟨hb, h⟩)
    push Not at this
    obtain ⟨l, hl⟩ := this
    exact hz cb l hl
  have hRsub : R ⊆ bondsAtCell Y := fun cb hb => by
    have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
    exact mem_bondsAtCell (by
      rcases h1 with h1 | h1
      · exact Or.inl h1.symm
      · exact Or.inr h1.symm)
  have hRcard : (R.card : ℝ) ≤ 8 := by
    have := (Finset.card_le_card hRsub).trans (card_bondsAtCell_le _)
    exact_mod_cast this
  have hsum2 : |∑ cb ∈ B, iteratedFDeriv ℝ k (fitc cb) 0 units| ≤ 8 * C2 k k * Real.exp c.δ₁ * e := by
    rw [hsumR]
    have hE : 0 ≤ 8 * C2 k k * Real.exp c.δ₁ * e := by
      have := hC20 k k
      positivity
    rcases R.eq_empty_or_nonempty with h0 | ⟨cb, hcb⟩
    · rw [h0]
      simpa using hE
    have hdiam : directionReach Y q ≤ 1 := by
      unfold directionReach
      refine Finset.sup_le fun l _ => ?_
      have t1 := htouch l cb ((Finset.mem_filter.mp hcb).2 l)
      have t2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hcb).1).2
      rcases t1 with t1 | t1 <;> rcases t2 with t2 | t2 <;> rw [t1, ← t2]
      · rw [cellSupDist_self]
        omega
      · rw [cellSupDist_comm]
        exact cellSupDist_add_unitStep_le hs _ _
      · exact cellSupDist_add_unitStep_le hs _ _
      · rw [cellSupDist_self]
        omega
    have h1 : (1 : ℝ) ≤ Real.exp c.δ₁ * e := by
      rw [he, ← Real.exp_add]
      refine Real.one_le_exp ?_
      have : (directionReach Y q : ℝ) ≤ 1 := by exact_mod_cast hdiam
      nlinarith
    have h2 : |∑ cb ∈ R, iteratedFDeriv ℝ k (fitc cb) 0 units| ≤ R.card * C2 k k := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ cb ∈ R, |iteratedFDeriv ℝ k (fitc cb) 0 units| ≤ ∑ _cb ∈ R, C2 k k :=
            Finset.sum_le_sum fun cb _ => hle cb
        _ = R.card * C2 k k := by simp
    have hC := hC20 k k
    calc _ ≤ R.card * C2 k k := h2
      _ ≤ 8 * C2 k k := mul_le_mul_of_nonneg_right hRcard hC
      _ = 8 * C2 k k * 1 := by ring
      _ ≤ 8 * C2 k k * (Real.exp c.δ₁ * e) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hsum1 : |∑ y ∈ Ys, iteratedFDeriv ℝ k (fun σ => minimalSiteShare a y (translatedChart w V ξ μ σ)) 0 units| ≤
      (M : ℝ) * (C1 k M * (Nx k * e)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hC0 : 0 ≤ C1 k M * (Nx k * e) := mul_nonneg (hC10 k M) (mul_nonneg (hNx0 k) he0.le)
    calc ∑ y ∈ Ys, |iteratedFDeriv ℝ k (fun σ => minimalSiteShare a y (translatedChart w V ξ μ σ)) 0 units|
        ≤ ∑ _y ∈ Ys, C1 k M * (Nx k * e) := Finset.sum_le_sum hy1
      _ = Ys.card * (C1 k M * (Nx k * e)) := by simp
      _ ≤ (M : ℝ) * (C1 k M * (Nx k * e)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hYcard) hC0
  rw [hsplit]
  have habs := abs_add_le
    (∑ y ∈ Ys, iteratedFDeriv ℝ k (fun σ => minimalSiteShare a y (translatedChart w V ξ μ σ)) 0 units)
    (a / 2 * ∑ cb ∈ B, iteratedFDeriv ℝ k (fitc cb) 0 units)
  rw [abs_mul, abs_of_pos (by positivity : 0 < a / 2)] at habs
  refine habs.trans ?_
  have h3 := mul_le_mul_of_nonneg_left hsum2 (by positivity : 0 ≤ a / 2)
  have hp : 0 ≤ a * (8 * C2 k k * Real.exp c.δ₁ * e) := by
    have := hC20 k k
    positivity
  have h4 : (M : ℝ) * (C1 k M * (Nx k * e)) + a / 2 * (8 * C2 k k * Real.exp c.δ₁ * e) ≤
      ((M : ℝ) * (C1 k M * Nx k) + a * (8 * C2 k k * Real.exp c.δ₁) + 1) * e := by
    nlinarith
  linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
