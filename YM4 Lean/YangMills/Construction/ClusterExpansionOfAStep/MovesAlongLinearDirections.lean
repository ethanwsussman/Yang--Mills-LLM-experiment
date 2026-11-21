import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoToriProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TopLevelSites
namespace LinearDirections
theorem iteratedFDeriv_comp_clm_zero {E E' W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (f : E → W) (A : E' →L[ℝ] E) (hf : AnalyticAt ℝ f 0) (k : ℕ) (v : Fin k → E') :
    iteratedFDeriv ℝ k (f ∘ A) 0 v = iteratedFDeriv ℝ k f 0 (fun l => A (v l)) := by
  set s : Set E := {x | AnalyticAt ℝ f x} with hs
  have hopen : IsOpen s := isOpen_analyticAt ℝ f
  have h0 : (0 : E) ∈ s := hf
  have hpre : IsOpen (A ⁻¹' s) := hopen.preimage A.continuous
  have h0' : (0 : E') ∈ A ⁻¹' s := by simpa using h0
  have hon : ContDiffOn ℝ k f s := fun x hx => (AnalyticAt.contDiffAt hx).contDiffWithinAt
  have key := ContinuousLinearMap.iteratedFDerivWithin_comp_right A hon hopen.uniqueDiffOn hpre.uniqueDiffOn
    (x := 0) (by simpa using h0) (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hpre h0', map_zero, iteratedFDerivWithin_of_isOpen k hopen h0] at key
  rw [key]
  rfl
variable {F : BlockFrame}
theorem bondSpread_sum {k : ℕ} {ι : Type} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (S : Finset ι) (a : ι → ℝ) (w : ι → Fin k → ℝ) (z : F.Site F.top) (i : Fin 4) :
    BlockAverages.bondSpread c X (∑ q ∈ S, a q • w q) z i =
      ∑ q ∈ S, a q • BlockAverages.bondSpread c X (w q) z i := by
  unfold BlockAverages.bondSpread
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : c l = (z, i)
  · simp only [h, if_true, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul]
  · simp [h]
theorem bondSpread_single {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l : Fin k)
    (z : F.Site F.top) (i : Fin 4) :
    BlockAverages.bondSpread c X (Pi.single l (1 : ℝ)) z i = if c l = (z, i) then X l else 0 := by
  classical
  unfold BlockAverages.bondSpread
  rw [Finset.sum_eq_single l]
  · simp
  · intro l' _ hl
    simp [Pi.single_eq_of_ne hl]
  · simp
theorem analyticAt_and_iteratedFDeriv_linearMove {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {k : ℕ}
    (G : F.GaugeField F.top → E) (U : F.GaugeField F.top) (hG : IsBondAnalyticAt G U)
    (Y : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) (J : Fin k → Finset (F.Site F.top × Fin 4))
    (hY : ∀ l z i, (z, i) ∉ J l → Y l z i = 0) :
    AnalyticAt ℝ (fun τ : Fin k → ℝ => G (rotatedField (fun z i => ∑ l, τ l • Y l z i) U)) 0 ∧
    iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => G (rotatedField (fun z i => ∑ l, τ l • Y l z i) U)) 0
        (fun l => Pi.single l 1) =
      ∑ r ∈ Fintype.piFinset J, mixedBondDerivative G U r (fun l => Y l (r l).1 (r l).2) := by
  classical
  set T : Finset (Σ _ : Fin k, F.Site F.top × Fin 4) := Finset.univ.sigma J with hT
  set K := Fintype.card T with hK
  let e : T ≃ Fin K := Fintype.equivFin T
  let c' : Fin K → F.Site F.top × Fin 4 := fun i => (e.symm i).1.2
  let X' : Fin K → imaginaryQuaternions := fun i => Y (e.symm i).1.1 (e.symm i).1.2.1 (e.symm i).1.2.2
  let f : (Fin K → ℝ) → E := fun σ => G (rotatedField (BlockAverages.bondSpread c' X' σ) U)
  have hf : AnalyticAt ℝ f 0 := hG K c' X'
  have hmem : ∀ {l p}, p ∈ J l → (⟨l, p⟩ : Σ _ : Fin k, F.Site F.top × Fin 4) ∈ T := fun {l p} h => by
    simp [hT, h]
  let g : (l : Fin k) → (F.Site F.top × Fin 4) → Fin K → ℝ := fun l p =>
    if h : p ∈ J l then Pi.single (e ⟨⟨l, p⟩, hmem h⟩) 1 else 0
  let A : (Fin k → ℝ) →L[ℝ] (Fin K → ℝ) :=
    ∑ l, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).smulRight (∑ p ∈ J l, g l p)
  have hAτ : ∀ τ : Fin k → ℝ, A τ = ∑ l, τ l • ∑ p ∈ J l, g l p := by
    intro τ
    simp [A]
  have hAs : ∀ l, A (Pi.single l 1) = ∑ p ∈ J l, g l p := by
    intro l
    rw [hAτ, Finset.sum_eq_single l]
    · simp
    · intro l' _ hl
      simp [Pi.single_eq_of_ne hl]
    · simp
  have hg_spread : ∀ l p z i, p ∈ J l →
      BlockAverages.bondSpread c' X' (g l p) z i = if p = (z, i) then Y l p.1 p.2 else 0 := by
    intro l p z i hp
    simp only [g, dif_pos hp]
    rw [bondSpread_single]
    simp [c', X']
  have hspread : ∀ τ : Fin k → ℝ,
      BlockAverages.bondSpread c' X' (A τ) = fun z i => ∑ l, τ l • Y l z i := by
    intro τ
    funext z i
    rw [hAτ]
    have : (∑ l, τ l • ∑ p ∈ J l, g l p) = ∑ l, τ l • (∑ p ∈ J l, (1 : ℝ) • g l p) := by simp
    rw [this, bondSpread_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    rw [bondSpread_sum]
    simp only [one_smul]
    rw [Finset.sum_congr rfl fun p hp => hg_spread l p z i hp]
    by_cases hzi : (z, i) ∈ J l
    · rw [Finset.sum_ite_eq' (J l) (z, i)]
      simp [hzi]
    · rw [Finset.sum_ite_eq' (J l) (z, i)]
      simp [hzi, hY l z i hzi]
  have hcomp : (fun τ : Fin k → ℝ => G (rotatedField (fun z i => ∑ l, τ l • Y l z i) U)) = f ∘ A := by
    funext τ
    simp only [f, Function.comp, hspread]
  rw [hcomp]
  refine ⟨?_, ?_⟩
  · have hA0 : AnalyticAt ℝ f (A 0) := by simpa using hf
    exact hA0.comp (ContinuousLinearMap.analyticAt A 0)
  rw [LinearDirections.iteratedFDeriv_comp_clm_zero f A hf]
  simp only [hAs]
  rw [ContinuousMultilinearMap.map_sum_finset]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : ∀ l, r l ∈ J l := fun l => Fintype.mem_piFinset.mp hr l
  let ρ : Fin k → Fin K := fun l => e ⟨⟨l, r l⟩, hmem (hr' l)⟩
  have hgr : ∀ l, g l (r l) = Pi.single (ρ l) 1 := fun l => by simp only [g, dif_pos (hr' l), ρ]
  let B : (Fin k → ℝ) →L[ℝ] (Fin K → ℝ) :=
    ∑ l, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).smulRight (Pi.single (ρ l) 1)
  have hBτ : ∀ τ : Fin k → ℝ, B τ = ∑ l, τ l • (Pi.single (ρ l) 1 : Fin K → ℝ) := by
    intro τ
    simp [B]
  have hBs : ∀ l, B (Pi.single l 1) = Pi.single (ρ l) 1 := by
    intro l
    rw [hBτ, Finset.sum_eq_single l]
    · simp
    · intro l' _ hl
      simp [Pi.single_eq_of_ne hl]
    · simp
  have hBspread : ∀ τ : Fin k → ℝ,
      BlockAverages.bondSpread c' X' (B τ) = BlockAverages.bondSpread r (fun l => Y l (r l).1 (r l).2) τ := by
    intro τ
    funext z i
    rw [hBτ, bondSpread_sum]
    unfold BlockAverages.bondSpread
    refine Finset.sum_congr rfl fun l _ => ?_
    have := bondSpread_single c' X' (ρ l) z i
    unfold BlockAverages.bondSpread at this
    rw [this]
    have e1 : c' (ρ l) = r l := by simp [c', ρ]
    have e2 : X' (ρ l) = Y l (r l).1 (r l).2 := by simp [X', ρ]
    rw [e1, e2]
    by_cases h : r l = (z, i) <;> simp [h]
  have hfB : (f ∘ B) = fun σ : Fin k → ℝ =>
      G (rotatedField (BlockAverages.bondSpread r (fun l => Y l (r l).1 (r l).2) σ) U) := by
    funext τ
    simp only [f, Function.comp, hBspread]
  have := LinearDirections.iteratedFDeriv_comp_clm_zero f B hf k (fun l => Pi.single l 1)
  rw [hfB] at this
  unfold mixedBondDerivative
  rw [this]
  congr 1
  funext l
  rw [hBs, hgr]
theorem sixteen_le_boxRadius {x : ℝ} (hx : (2 : ℝ) ^ 1600 ≤ x) : 16 ≤ RenormalizationStepParameters.boxRadius x := by
  have h1 : (2 : ℝ) ^ 16 ≤ x ^ ((1 : ℝ) / 100) := by
    have e : ((2 : ℝ) ^ 1600) ^ ((1 : ℝ) / 100) = 2 ^ 16 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
      norm_num
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have h2 : 2 ^ 16 ≤ TorusLumps.clusterRange x := by
    have h3 : ((2 ^ 16 : ℕ) : ℝ) ≤ (TorusLumps.clusterRange x : ℝ) := by
      have e : ((2 ^ 16 : ℕ) : ℝ) = (2 : ℝ) ^ 16 := by norm_num
      rw [e]
      exact h1.trans (Nat.le_ceil _)
    exact_mod_cast h3
  unfold RenormalizationStepParameters.boxRadius
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
theorem mem_sitesOfCells_finiteCells {F : BlockFrame} (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) :
    x ∈ sitesOfCells (finiteCells F) F.depth := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoTori.mem_sitesOfCells_finiteCells <;> assumption
theorem mem_chordBonds_finiteCells {F : BlockFrame} (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) (i : Fin 4)
    (hnt : ¬ IsAxialTreeBond (x, i)) : (x, i) ∈ chordBonds (finiteCells F) := by
  classical
  unfold chordBonds innerBonds
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨mem_sitesOfCells_finiteCells hL hs x, Finset.mem_univ _⟩,
    mem_sitesOfCells_finiteCells hL hs _⟩, hnt⟩
theorem reflectedBond_mem_chordBonds {F : BlockFrame} (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {m : ℕ}
    (hm : 1 ≤ m) (x : F.Site F.depth) (i : Fin 4)
    (hnt : ¬ IsAxialTreeBond (x, i)) :
    reflectedBond m (x, i) ∈ chordBonds (finiteCells (reflectedFrame F m)) := by
  have hs' : ∀ i, 2 ≤ (reflectedFrame F m).extent i := fun i => by
    change 2 ≤ 4 * m
    omega
  have hL' : Odd (reflectedFrame F m).blockSide := hL
  have hne' : ∀ i, NeZero ((reflectedFrame F m).period (reflectedFrame F m).top i) :=
    fun i => ⟨by rw [period_top]; have := hs' i; omega⟩
  obtain ⟨hc, he⟩ := centre_cellOffset hL hs x
  have hsite : cellCentre (reflectedFrame F m).depth
      ((0 : (reflectedFrame F m).Cell) + siteOfCoords (reflectedFrame F m).top 0) +
      siteOfCoords (reflectedFrame F m).depth (cellOffset x) =
        siteOfCoords (reflectedFrame F m).depth (cellOffset x) :=
    congrArg Prod.fst (fineBondAt_zero (F' := reflectedFrame F m) hne' (cellOffset x) i)
  refine mem_chordBonds_finiteCells hL' hs' _ _ ?_
  intro ht
  apply hnt
  have hc' : cellOffset x ∈ centredCube (reflectedFrame F m).blockSide := hc
  have e1 : IsAxialTreeBond ((cellCentre (reflectedFrame F m).depth
      ((0 : (reflectedFrame F m).Cell) + siteOfCoords (reflectedFrame F m).top 0) +
      siteOfCoords (reflectedFrame F m).depth (cellOffset x) : (reflectedFrame F m).Site (reflectedFrame F m).depth),
        i) := by
    rw [hsite]
    exact ht
  have e2 := (isAxialTreeBond_iff hL' hs' _ _ hc' i).mp e1
  rw [← he]
  exact (isAxialTreeBond_iff hL hs _ _ hc i).mpr e2
end LinearDirections
end YangMills.Construction
end
