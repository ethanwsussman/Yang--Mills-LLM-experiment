import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheBlockEnergyProof
import YangMills.Construction.ResponseInTheExpansion.KernelsOfAShare
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets
namespace YangMills.Construction.WeightedResponses
variable {F : BlockFrame} {k : ℕ}
private theorem cellSupDist_le_siteSupDist (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x y : F.Site F.depth) :
    cellSupDist (enclosingCell x) (enclosingCell y) ≤ siteSupDist x y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellEnergyKernels.cellSupDist_enclosingCell_le <;> assumption
open Classical in
private def directionBonds : ChartDirection F → Finset (F.Site F.depth × Fin 4)
  | .inl p => {(p.1, p.2.1)}
  | .inr p => (centredCube F.blockSide).image fun h =>
      (cellCentre F.depth p.1 + siteOfCoords F.depth h, p.2.1)
private theorem card_directionBonds_le (q : ChartDirection F) :
    (directionBonds q).card ≤ (centredCube F.blockSide).card + 1 := by
  rcases q with p | p
  · simp [directionBonds]
  · exact Finset.card_image_le.trans (Nat.le_succ _)
private theorem enclosingCell_of_mem_directionBonds (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    {q : ChartDirection F} {b : F.Site F.depth × Fin 4} (hb : b ∈ directionBonds q) :
    enclosingCell b.1 = directionCell q := by
  rcases q with p | p
  · have : b = (p.1, p.2.1) := by simpa [directionBonds] using hb
    subst this
    rfl
  · obtain ⟨h, hh, e⟩ := Finset.mem_image.mp hb
    subst e
    exact enclosingCell_offset hL hs p.1 h hh
private theorem mem_directionBonds_of_moves (hsites : SiteDecomposition) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (q₀ : ChartDirection F) (b : F.Site F.depth × Fin 4)
    (h : directionCoordinate q₀ b.1 b.2 ≠ 0 ∨
      (IsCrossingBond b ∧ directionMove q₀ (enclosingCell b.1) b.2 ≠ 0)) :
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
theorem siteShareKernelBound_of_coldEstimates (hch : ColdEstimatesAtEveryDepth)
    (hth : TranslatedChartCompositeBound) (hsites : SiteDecomposition) (hcover : BlocksCoverLowerLevel) :
    SiteShareKernelBound := by
  classical
  obtain ⟨C1, hC10, hth⟩ := hth
  intro a L c ha hLo hL40 hc
  obtain ⟨N, hN0, hNc⟩ := hch a L c ha hLo hL40 hc
  set M : ℕ := (centredCube L).card + 1 with hM
  set Nx : ℕ → ℝ := fun k => ∑ p ∈ Finset.range (k + 1), N p with hNx
  have hNx0 : ∀ k, 0 ≤ Nx k := fun k => Finset.sum_nonneg fun p _ => (hN0 p).le
  refine ⟨fun k => C1 k M * Nx k + 1, fun k => ?_, ?_⟩
  · have h1 := hC10 k M
    have h2 := hNx0 k
    positivity
  intro F w V hF hS y k q
  have hFL : F.blockSide = L := hF.1
  obtain ⟨nside, h64, hside⟩ := hF.2
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside i]
    omega
  have hLF : Odd F.blockSide := by rw [hFL]; exact hLo
  set ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions :=
    fun l => directionCoordinate (q l) with hξdef
  set μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions :=
    fun l => directionMove (q l) with hμdef
  have hshare : siteShareAlong a y w V q =
      fun σ => minimalSiteShare a y (translatedChart w V ξ μ σ) := rfl
  have hJ : ∀ l b, ParameterMovesBond ξ μ l b → b ∈ directionBonds (q l) :=
    fun l b h => mem_directionBonds_of_moves hsites hLF hs (q l) b h
  have hHold : ColdEstimatesBelow a c.δ₁ c.σA N (chartedField w V) :=
    hNc.1 F c.σA _ ⟨hFL, nside, h64, hside⟩ hc.positivity.2.2.2.1 le_rfl hS.small_curvature
  set e : ℝ := Real.exp (-(c.δ₁ * (directionReach (enclosingCell y) q : ℝ))) with he
  have he0 : 0 < e := Real.exp_pos _
  have hthy := hth F (minimalSiteShare a y) w V k ξ μ (fun l => directionBonds (q l)) M (Nx k * e) hJ
    (fun n b X => hHold.siteShare_analytic y n b X)
  refine ⟨?_, ?_⟩
  · rw [hshare]
    exact hthy.1
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
  have hcell : ∀ l b, b ∈ directionBonds (q l) → enclosingCell b.1 = directionCell (q l) :=
    fun l b hb => enclosingCell_of_mem_directionBonds hLF hs hb
  have hbound : ∀ (p : ℕ) (b : Fin p → F.Site F.depth × Fin 4) (X : Fin p → imaginaryQuaternions),
      1 ≤ p → p ≤ k → AreUnitVectors X → (∀ l, ∃ m, b m ∈ directionBonds (q l)) →
      |bondDeriv (minimalSiteShare a y) (chartedField w V) b X| ≤ Nx k * e := by
    intro p b X hp hpk hX hcomp
    have h1 := hHold.siteShare_deriv_decay y p b X hp hX
    have hd : directionReach (enclosingCell y) q ≤ bondListDist y b := by
      unfold directionReach
      refine Finset.sup_le fun l _ => ?_
      obtain ⟨m, hm⟩ := hcomp l
      rw [← hcell l _ hm]
      refine (cellSupDist_le_siteSupDist hLF hs _ _).trans ?_
      unfold bondListDist
      exact Finset.le_sup (f := fun m => siteSupDist y (b m).1) (Finset.mem_univ m)
    have hδ : 0 < c.δ₁ := hc.positivity.1
    have h2 : Real.exp (-c.δ₁ * (bondListDist y b : ℝ)) ≤ e := by
      refine Real.exp_le_exp.mpr ?_
      have : (directionReach (enclosingCell y) q : ℝ) ≤ bondListDist y b := by exact_mod_cast hd
      nlinarith
    have h3 : N p ≤ Nx k := Finset.single_le_sum (f := fun p => N p) (fun p _ => (hN0 p).le)
      (Finset.mem_range.mpr (by omega))
    refine h1.trans ?_
    exact mul_le_mul h3 h2 (Real.exp_pos _).le (hNx0 k)
  have hy1 : |siteShareMixedDeriv a y w V q| ≤ C1 k M * (Nx k * e) :=
    hthy.2 hw1 hξ hμ hcard (mul_nonneg (hNx0 k) he0.le) hk1 hbound
  refine hy1.trans ?_
  have : C1 k M * (Nx k * e) = C1 k M * Nx k * e := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (by linarith) he0.le
end YangMills.Construction.WeightedResponses
end
