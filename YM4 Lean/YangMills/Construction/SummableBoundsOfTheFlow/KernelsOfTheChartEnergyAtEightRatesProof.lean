import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheBlockEnergyProof
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheChartEnergyAtEightRates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Estimates
private theorem int_ediv_sub_natAbs_mul_le {L : ℤ} (hL : 0 < L) (u d : ℤ) :
    L * (((u + d) / L - u / L).natAbs : ℤ) ≤ (d.natAbs : ℤ) + L := by
  have h1 := Int.ediv_mul_le (u + d) hL.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (u + d) hL
  have h3 := Int.ediv_mul_le u hL.ne'
  have h4 := Int.lt_ediv_add_one_mul_self u hL
  set A := (u + d) / L
  set B := u / L
  have hd : d ≤ (d.natAbs : ℤ) ∧ -d ≤ (d.natAbs : ℤ) := by omega
  rcases le_total 0 (A - B) with h | h
  · rw [Int.natAbs_of_nonneg h]
    nlinarith [hd.1]
  · have e : ((A - B).natAbs : ℤ) = -(A - B) := by omega
    rw [e]
    nlinarith [hd.2]
private theorem natAbs_valMinAbs_intCast_le {n : ℕ} [NeZero n] (e : ℤ) :
    ((e : ZMod n)).valMinAbs.natAbs ≤ e.natAbs := by apply _root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le <;> assumption
variable {F : BlockFrame} {k : ℕ}
private theorem period_top_neZero (hs : ∀ i, 2 ≤ F.extent i) (i : Fin 4) : NeZero (F.period F.top i) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellEnergyKernels.neZero_period_top <;> assumption
private theorem period_depth_neZero (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (i : Fin 4) :
    NeZero (F.period F.depth i) := ⟨by
  rw [BlockOffsets.period_depth]
  have h1 := hs i
  obtain ⟨m, hm⟩ := hL
  have h2 : 0 < F.blockSide := by omega
  have h3 : 0 < F.extent i := by omega
  exact (Nat.mul_pos h3 h2).ne'⟩
private theorem cellSupDist_enclosingCell_le (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x y : F.Site F.depth) :
    cellSupDist (enclosingCell x) (enclosingCell y) ≤ (siteSupDist x y + F.blockSide) / F.blockSide := by
  have hLn : 0 < F.blockSide := hL.pos
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  rw [Nat.le_div_iff_mul_le hLn]
  have hb : ((x i - y i).valMinAbs).natAbs ≤ siteSupDist x y :=
    Finset.le_sup (f := fun i => ((x i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
  have := period_top_neZero hs i
  have := period_depth_neZero hL hs i
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
    rw [BlockOffsets.period_depth]
    push_cast
    ring
  rw [hP] at hm
  have eX : X = Y + d - (F.extent i : ℤ) * F.blockSide * m := by linarith
  have hc : ∀ z : F.Site F.depth, enclosingCell z i =
      ((((siteCoords z i + hh) / (F.blockSide : ℤ) : ℤ)) : ZMod (F.period F.top i)) := by
    intro z
    change (((siteCoords z i + ((F.blockSide : ℤ) ^ (F.top - F.depth) - 1) / 2) /
      (F.blockSide : ℤ) ^ (F.top - F.depth) : ℤ) : ZMod (F.period F.top i)) = _
    rw [BlockOffsets.top_sub_depth, pow_one]
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
    rw [BlockOffsets.extent_cast_eq_zero, zero_mul, sub_zero]
  change (((enclosingCell x i - enclosingCell y i)).valMinAbs).natAbs * F.blockSide ≤ _
  rw [hdiff]
  have h1 := natAbs_valMinAbs_intCast_le (n := F.period F.top i)
    ((Y + hh + d) / (F.blockSide : ℤ) - (Y + hh) / (F.blockSide : ℤ))
  have h2 := int_ediv_sub_natAbs_mul_le hLpos (Y + hh) d
  have h2' : F.blockSide * ((Y + hh + d) / (F.blockSide : ℤ) - (Y + hh) / (F.blockSide : ℤ)).natAbs ≤
      d.natAbs + F.blockSide := by
    exact_mod_cast h2
  calc _ ≤ ((Y + hh + d) / (F.blockSide : ℤ) - (Y + hh) / (F.blockSide : ℤ)).natAbs * F.blockSide :=
        Nat.mul_le_mul_right _ h1
    _ = F.blockSide * ((Y + hh + d) / (F.blockSide : ℤ) - (Y + hh) / (F.blockSide : ℤ)).natAbs := Nat.mul_comm _ _
    _ ≤ d.natAbs + F.blockSide := h2'
    _ ≤ siteSupDist x y + F.blockSide := by omega
private theorem cellSupDist_self (y : F.Cell) : cellSupDist y y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
private theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
private theorem cellSupDist_add_unitStep_le (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (i : Fin 4) :
    cellSupDist z (z + unitStep F.top i) ≤ 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellEnergyKernels.cellSupDist_add_unitStep_le <;> assumption
open Classical in
private def directionBonds : ChartDirection F → Finset (F.Site F.depth × Fin 4)
  | .inl p => {(p.1, p.2.1)}
  | .inr p => (centredCube F.blockSide).image fun h => (cellCentre F.depth p.1 + siteOfCoords F.depth h, p.2.1)
private theorem card_directionBonds_le (q : ChartDirection F) :
    (directionBonds q).card ≤ (centredCube F.blockSide).card + 1 := by
  rcases q with p | p
  · simp [directionBonds]
  · exact Finset.card_image_le.trans (Nat.le_succ _)
private theorem enclosingCell_of_mem_directionBonds (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    {q : ChartDirection F} {b : F.Site F.depth × Fin 4}
    (hb : b ∈ directionBonds q) : enclosingCell b.1 = directionCell q := by
  rcases q with p | p
  · have : b = (p.1, p.2.1) := by simpa [directionBonds] using hb
    subst this
    rfl
  · obtain ⟨h, hh, e⟩ := Finset.mem_image.mp hb
    subst e
    exact BlockOffsets.enclosingCell_offset hL hs p.1 h hh
private theorem mem_directionBonds_of_moves (hsites : SiteDecomposition) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (q₀ : ChartDirection F) (b : F.Site F.depth × Fin 4)
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
private theorem norm_directionCoordinate_le (q₀ : ChartDirection F) (h : ‖directionVector q₀‖ = 1)
    (x : F.Site F.depth) (i : Fin 4) : ‖directionCoordinate q₀ x i‖ ≤ 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellEnergyKernels.norm_directionCoordinate_le <;> assumption
private theorem norm_directionMove_le (q₀ : ChartDirection F) (h : ‖directionVector q₀‖ = 1)
    (y : F.Site F.top) (i : Fin 4) : ‖directionMove q₀ y i‖ ≤ 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellEnergyKernels.norm_directionMove_le <;> assumption
private theorem norm_piSingle_one_le (l : Fin k) : ‖(Pi.single l (1 : ℝ) : Fin k → ℝ)‖ ≤ 1 := by apply _root_.YangMills.Construction.PlainAlignment.norm_single_le_one <;> assumption
private def bondsAtCell (y : F.Cell) : Finset (F.Cell × Fin 4) := by
  classical exact (Finset.univ.image fun i : Fin 4 => (y, i)) ∪
    (Finset.univ.image fun i : Fin 4 => (y - unitStep F.top i, i))
private theorem card_bondsAtCell_le (y : F.Cell) : (bondsAtCell y).card ≤ 8 := by
  classical
  unfold bondsAtCell
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : (Finset.univ.image fun i : Fin 4 => (y, i)).card ≤ 4 := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 4))) (f := fun i : Fin 4 => (y, i))
  have h2 : (Finset.univ.image fun i : Fin 4 => (y - unitStep F.top i, i)).card ≤ 4 := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 4)))
      (f := fun i : Fin 4 => (y - unitStep F.top i, i))
  omega
private theorem mem_bondsAtCell {y : F.Cell} {c : F.Cell × Fin 4}
    (h : y = c.1 ∨ y = c.1 + unitStep F.top c.2) : c ∈ bondsAtCell y := by
  classical
  unfold bondsAtCell
  rw [Finset.mem_union]
  rcases h with h | h
  · left
    exact Finset.mem_image.mpr ⟨c.2, Finset.mem_univ _, by rw [h]⟩
  · right
    exact Finset.mem_image.mpr ⟨c.2, Finset.mem_univ _, by rw [h]; simp⟩
theorem chartEnergyKernelDecay_of_coldEstimates (hch : ColdEstimatesAtEveryDepth)
    (hth : TranslatedChartCompositeBound) (hfit : BlockFitAnalyticAlongTranslates)
    (hcp : Calculus.CompositeDerivativesAtPoint) (hsites : SiteDecomposition)
    (hcover : BlocksCoverLowerLevel) : ChartEnergyKernelDecay := by
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
  refine ⟨fun k => C1 k M * (Nx k * Real.exp (8 * c.δ₁)) + a * (8 * C2 k k * Real.exp (8 * c.δ₁)) + 1,
    fun k => ?_, ?_⟩
  · have h1 := hC10 k M
    have h2 := hNx0 k
    have h3 := hC20 k k
    have h4 := Real.exp_pos (8 * c.δ₁)
    positivity
  intro F w V hF hS k q hk hu
  have hFL : F.blockSide = L := hF.1
  obtain ⟨nside, h64, hside⟩ := hF.2
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside i]
    omega
  have hLF : Odd F.blockSide := by rw [hFL]; exact hLo
  set ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions := fun l => directionCoordinate (q l) with hξdef
  set μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions := fun l => directionMove (q l) with hμdef
  set f : F.GaugeField F.depth → ℝ := minimalAction a (finiteCells F) F.depth with hf
  set fitc : F.Site F.top × Fin 4 → (Fin k → ℝ) → ℝ := fun cb σ =>
    blockFit (translatedChart w V ξ μ σ) (translatedTop V μ σ) cb with hfitc
  set B := innerBonds (finiteCells F) F.top with hBdef
  have hchart : chartRestriction a w V q = fun σ => f (translatedChart w V ξ μ σ) + a * ∑ cb ∈ B, fitc cb σ := rfl
  have hJ : ∀ l b, ParameterMovesBond ξ μ l b → b ∈ directionBonds (q l) := fun l b h =>
    mem_directionBonds_of_moves hsites hLF hs (q l) b h
  have hHold : ColdEstimatesBelow a c.δ₁ c.σA N (chartedField w V) :=
    hNc.1 F c.σA _ ⟨hFL, nside, h64, hside⟩ hc.positivity.2.2.2.1 le_rfl hS.small_curvature
  have hAna : ∀ (n : ℕ) (b : Fin n → F.Site F.depth × Fin 4) (X : Fin n → imaginaryQuaternions),
      AnalyticAt ℝ (fun τ : Fin n → ℝ => f (leftTranslate (bondSpread b X τ) (chartedField w V))) 0 :=
    fun n b X => hHold.minimalAction_analytic n b X
  set e : ℝ := Real.exp (-(8 * c.δ₁ * (directionDiameter q : ℝ))) with he
  have he0 : 0 < e := Real.exp_pos _
  obtain ⟨hA1, hB1⟩ := hth F f w V k ξ μ (fun l => directionBonds (q l)) M (Nx k * Real.exp (8 * c.δ₁) * e) hJ hAna
  have hfc := fun cb => hfit F w V k ξ μ cb hFL hs hS.coord_small
  have hA2 : ∀ cb, AnalyticAt ℝ (fitc cb) 0 := fun cb => (hfc cb).1
  have hSum : AnalyticAt ℝ (fun σ => ∑ cb ∈ B, fitc cb σ) 0 :=
    Finset.analyticAt_fun_sum _ fun cb _ => hA2 cb
  have hAS : AnalyticAt ℝ (fun σ => a * ∑ cb ∈ B, fitc cb σ) 0 := analyticAt_const.mul hSum
  have hk1 : 1 ≤ k := by omega
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
  have hbound : ∀ (p : ℕ) (b : Fin p → F.Site F.depth × Fin 4) (X : Fin p → imaginaryQuaternions), 1 ≤ p → p ≤ k →
      AreUnitVectors X → (∀ l, ∃ m, b m ∈ directionBonds (q l)) →
      |bondDeriv f (chartedField w V) b X| ≤ Nx k * Real.exp (8 * c.δ₁) * e := by
    intro p b X hp hpk hX hcomp
    have h1 := hHold.minimalAction_deriv_decay p b X hp hX
    have hL8 : 8 ≤ F.blockSide := by
      rw [hFL]
      have : (8 : ℕ) ≤ 2 ^ 40 := by norm_num
      omega
    have hd : directionDiameter q ≤ (ColdStepAtMirrorFrames.bondListDiameter b + 8) / 8 := by
      unfold directionDiameter
      refine Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_
      obtain ⟨m, hm⟩ := hcomp l
      obtain ⟨m', hm'⟩ := hcomp l'
      rw [← hcell l _ hm, ← hcell l' _ hm']
      have hsd : siteSupDist (b m).1 (b m').1 ≤ ColdStepAtMirrorFrames.bondListDiameter b := by
        unfold ColdStepAtMirrorFrames.bondListDiameter
        exact (Finset.le_sup (f := fun l' => siteSupDist (b m).1 (b l').1) (Finset.mem_univ m')).trans
          (Finset.le_sup (f := fun l => Finset.univ.sup fun l' => siteSupDist (b l).1 (b l').1) (Finset.mem_univ m))
      refine (cellSupDist_enclosingCell_le hLF hs _ _).trans ?_
      rw [Nat.add_div_right _ (by omega), Nat.add_div_right _ (by norm_num)]
      exact Nat.succ_le_succ ((Nat.div_le_div_left hL8 (by norm_num)).trans (Nat.div_le_div_right hsd))
    have hd8 : (8 : ℝ) * directionDiameter q ≤ ColdStepAtMirrorFrames.bondListDiameter b + 8 := by
      have h8 := Nat.div_mul_le_self (ColdStepAtMirrorFrames.bondListDiameter b + 8) 8
      have : 8 * directionDiameter q ≤ ColdStepAtMirrorFrames.bondListDiameter b + 8 := by omega
      exact_mod_cast this
    have h2 : Real.exp (-c.δ₁ * (ColdStepAtMirrorFrames.bondListDiameter b : ℝ)) ≤ Real.exp (8 * c.δ₁) * e := by
      rw [he, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have h3 : N p ≤ Nx k := Finset.single_le_sum (f := fun p => N p) (fun p _ => (hN0 p).le)
      (Finset.mem_range.mpr (by omega))
    refine h1.trans ?_
    rw [mul_assoc]
    exact mul_le_mul h3 h2 (Real.exp_pos _).le (hNx0 k)
  have b1 := hB1 hw1 hξ hμ hcard (mul_nonneg (mul_nonneg (hNx0 k) (Real.exp_pos _).le) he0.le) hk1 hbound
  set units : Fin k → Fin k → ℝ := fun l => Pi.single l 1 with hunits
  have hsplit : chartMixedDeriv a w V q = iteratedFDeriv ℝ k (fun σ => f (translatedChart w V ξ μ σ)) 0 units +
      a * ∑ cb ∈ B, iteratedFDeriv ℝ k (fitc cb) 0 units := by
    unfold chartMixedDeriv
    rw [hchart]
    have e1 : (fun σ => f (translatedChart w V ξ μ σ) + a * ∑ cb ∈ B, fitc cb σ) =
        (fun σ => f (translatedChart w V ξ μ σ)) + fun σ => a * ∑ cb ∈ B, fitc cb σ := rfl
    have e2 : (fun σ : Fin k → ℝ => a * ∑ cb ∈ B, fitc cb σ) = a • fun σ => ∑ cb ∈ B, fitc cb σ := rfl
    rw [e1, iteratedFDeriv_add_apply hA1.contDiffAt hAS.contDiffAt, e2,
      iteratedFDeriv_const_smul_apply hSum.contDiffAt,
      iteratedFDeriv_fun_sum_apply fun cb _ => (hA2 cb).contDiffAt]
    simp only [add_apply, smul_apply, smul_eq_mul,
      sum_apply]
    rfl
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
  have hsumR : ∑ cb ∈ B, iteratedFDeriv ℝ k (fitc cb) 0 units =
      ∑ cb ∈ R, iteratedFDeriv ℝ k (fitc cb) 0 units := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun cb hb hnot => ?_
    have : ¬ ∀ l, ParameterTouchesBond ξ μ l cb := fun h => hnot (Finset.mem_filter.mpr ⟨hb, h⟩)
    push Not at this
    obtain ⟨l, hl⟩ := this
    exact hz cb l hl
  set l₀ : Fin k := ⟨0, by omega⟩ with hl₀
  have hRsub : R ⊆ bondsAtCell (directionCell (q l₀)) := fun cb hb =>
    mem_bondsAtCell (htouch l₀ cb ((Finset.mem_filter.mp hb).2 l₀))
  have hRcard : (R.card : ℝ) ≤ 8 := by
    have := (Finset.card_le_card hRsub).trans (card_bondsAtCell_le _)
    exact_mod_cast this
  have hsum2 : |∑ cb ∈ B, iteratedFDeriv ℝ k (fitc cb) 0 units| ≤ 8 * C2 k k * Real.exp (8 * c.δ₁) * e := by
    rw [hsumR]
    have hE : 0 ≤ 8 * C2 k k * Real.exp (8 * c.δ₁) * e := by
      have := hC20 k k
      positivity
    rcases R.eq_empty_or_nonempty with h0 | ⟨cb, hcb⟩
    · rw [h0]
      simpa using hE
    have hdiam : directionDiameter q ≤ 1 := by
      unfold directionDiameter
      refine Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_
      have t1 := htouch l cb ((Finset.mem_filter.mp hcb).2 l)
      have t2 := htouch l' cb ((Finset.mem_filter.mp hcb).2 l')
      rcases t1 with t1 | t1 <;> rcases t2 with t2 | t2 <;> rw [t1, t2]
      · rw [cellSupDist_self]
        omega
      · exact cellSupDist_add_unitStep_le hs _ _
      · rw [cellSupDist_comm]
        exact cellSupDist_add_unitStep_le hs _ _
      · rw [cellSupDist_self]
        omega
    have h1 : (1 : ℝ) ≤ Real.exp (8 * c.δ₁) * e := by
      rw [he, ← Real.exp_add]
      refine Real.one_le_exp ?_
      have : (directionDiameter q : ℝ) ≤ 1 := by exact_mod_cast hdiam
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
      _ ≤ 8 * C2 k k * (Real.exp (8 * c.δ₁) * e) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  rw [hsplit]
  have habs := abs_add_le (iteratedFDeriv ℝ k (fun σ => f (translatedChart w V ξ μ σ)) 0 units)
    (a * ∑ cb ∈ B, iteratedFDeriv ℝ k (fitc cb) 0 units)
  rw [abs_mul, abs_of_pos ha0] at habs
  refine habs.trans ?_
  have h3 := mul_le_mul_of_nonneg_left hsum2 ha0.le
  have h4 : C1 k M * (Nx k * Real.exp (8 * c.δ₁) * e) + a * (8 * C2 k k * Real.exp (8 * c.δ₁) * e) ≤
      (C1 k M * (Nx k * Real.exp (8 * c.δ₁)) + a * (8 * C2 k k * Real.exp (8 * c.δ₁)) + 1) * e := by
    nlinarith
  linarith
end Estimates
end YangMills.Construction
end
