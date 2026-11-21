import YangMills.Construction.ColdChainAtEveryLevel.DifferencesInAPatch
import YangMills.Construction.ColdChainAtEveryLevel.FormsInAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PatchPotentials
open BlockAverages GaugeMap PatchFrames PatchPoints LatticeFractionalIntegration PatchForms BondShares
section Hypotheses
variable {F : BlockFrame}
structure HomotopyKernels (l : ℕ) (c : Lattice4) (P : Finset Lattice4)
    (H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ) (G : Lattice4 → Lattice4 × Fin 4 → ℝ) (C : ℝ) : Prop where
  plaquette_bound : ∀ b p, |H b p| ≤ C * cubicKernel (b.1 - p.1)
  bond_bound : ∀ x b, |G x b| ≤ C * cubicKernel (x - b.1)
  pathMean_eq : ∀ (w : Lattice4 → Fin 4 → ℍ[ℝ]), ∀ x ∈ P,
    randomPathMean l c w x = ∑ b ∈ bondsOf P, G x b • w b.1 b.2
  curl_formula : ∀ (w : Lattice4 → Fin 4 → ℍ[ℝ]) (x : Lattice4) (i : Fin 4), x ∈ P → x + basisVector i ∈ P →
    w x i + (randomPathMean l c w (x + basisVector i) - randomPathMean l c w x) =
      ∑ p ∈ orientedPlaquettesOf P, H (x, i) p • plaquetteCurl w p.1 p.2.1 p.2.2
  endpoint_formula : ∀ (φ : Lattice4 → ℍ[ℝ]), ∀ x ∈ P,
    φ x - endpointMean l c φ = - randomPathMean l c (latticeDifference φ) x
structure PotentialSetting (S : Finset F.Cell) (V : F.GaugeField F.top) (Cs r C : ℝ) : Prop where
  ambient : IsAdmissibleAmbient F
  odd_side : Odd F.blockSide
  regular : ∃ m, 32 ≤ m ∧ IsOrthantRegular S m
  frames : ∀ z ∈ S, ∃ R : Lattice4 → Lattice4 → UnitQuaternion, IsPatchFrame S V z R Cs r
  scale : 1 ≤ r * cellSideLength F
  coldness_nonneg : 0 ≤ Cs
  coldness_le_one : Cs ≤ 1
  kernelConst_nonneg : 0 ≤ C
  homotopy : ∀ (l : ℕ) (c : Lattice4) (P : Finset Lattice4), 1 ≤ l → IsFilledToward l c P →
    ∃ H G, HomotopyKernels l c P H G C
variable {S : Finset F.Cell} {V : F.GaugeField F.top} {Cs r C : ℝ}
theorem PotentialSetting.closedOrthant_cases (h : PotentialSetting S V Cs r C) (z : F.Cell) (i : Fin 4) :
    closedOrthant S z i = 1 ∨ closedOrthant S z i = -1 := by
  obtain ⟨m, hm, hreg⟩ := h.regular
  exact (closedOrthant_spec hreg hm z).1 i
theorem PotentialSetting.isOrthantClosedNear (h : PotentialSetting S V Cs r C) (z : F.Cell) :
    IsOrthantClosedNear S z (closedOrthant S z) := by
  obtain ⟨m, hm, hreg⟩ := h.regular
  exact (closedOrthant_spec hreg hm z).2
theorem PotentialSetting.cellSideLength_pos (h : PotentialSetting S V Cs r C) : (0 : ℝ) < cellSideLength F := by
  exact_mod_cast BlockAverages.cellSideLength_pos (F := F) h.odd_side.pos
theorem PotentialSetting.patchSiteSet_subset (h : PotentialSetting S V Cs r C) (z : F.Cell) :
    patchSiteSet S z ⊆ sitesOfCells S 0 := by
  classical
  obtain ⟨m, hm, hreg⟩ := h.regular
  intro t ht
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ht
  exact patchSite_mem_sitesOfCells h.ambient h.odd_side hreg hm hb
theorem PotentialSetting.not_mem_patchSiteSet_of_not_mem_cellBall (h : PotentialSetting S V Cs r C) {z y : F.Cell}
    (hy : y ∈ S) (hn : y ∉ cellBall S z 20) :
    ∀ x ∈ cellSites S y, x ∉ patchSiteSet S z := by
  classical
  obtain ⟨m, hm, hreg⟩ := h.regular
  intro x hx hxp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hxp
  have h1 := (enclosingCell_patchSite h.ambient h.odd_side hreg hm hb).2
  rw [(Finset.mem_filter.1 hx).2] at h1
  exact hn (Finset.mem_filter.2 ⟨hy, by rw [cellSupDist_symm]; exact h1⟩)
theorem PotentialSetting.mem_patchSiteSet_of_cellSupDist_le (h : PotentialSetting S V Cs r C) {z y : F.Cell}
    (hy : y ∈ S) (hd : cellSupDist z y ≤ 10) {t : F.Site 0} (ht : t ∈ cellSites S y) : t ∈ patchSiteSet S z := by
  classical
  obtain ⟨y', hy', g, hg, e⟩ := mem_sitesOfCells.1 (Finset.mem_filter.1 ht).1
  have hg' : g ∈ centredCube (F.blockSide ^ F.top) := by simpa using hg
  have hc : enclosingCell t = y' := by
    rw [e]
    exact LocalPartition.enclosingCell_cellCentre_add h.odd_side y' g hg'
  have hyy : y' = y := by rw [← hc]; exact (Finset.mem_filter.1 ht).2
  subst hyy
  have h1 := patchChart_mem_patchDomain h.ambient h.odd_side (h.closedOrthant_cases z) hy hd hg'
  refine Finset.mem_image.2 ⟨_, h1, ?_⟩
  rw [patchSite_patchChart (h.closedOrthant_cases z), e]
end Hypotheses
section Sums
theorem cubicKernel_nonneg (v : Lattice4) : 0 ≤ cubicKernel v := by apply _root_.YangMills.Construction.PatchDifferences.cubicKernel_nonneg_apply <;> assumption
theorem supNorm_sub_le (a b : Lattice4) : supNorm (a - b) ≤ supNorm a + supNorm b := by
  refine Finset.sup_le fun i _ => ?_
  have h1 : (a i).natAbs ≤ supNorm a := Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)
  have h2 : (b i).natAbs ≤ supNorm b := Finset.le_sup (f := fun i => (b i).natAbs) (Finset.mem_univ i)
  have h3 : ((a - b) i).natAbs ≤ (a i).natAbs + (b i).natAbs := by
    simp only [Pi.sub_apply]
    omega
  omega
theorem supNorm_add_le (a b : Lattice4) : supNorm (a + b) ≤ supNorm a + supNorm b := by apply _root_.YangMills.Construction.LatticePaths.supNorm_add_le <;> assumption
theorem cubicKernel_le_of_supNorm_le_two (v δ : Lattice4) (hδ : supNorm δ ≤ 2) :
    cubicKernel v ≤ 27 * cubicKernel (v - δ) := by
  unfold cubicKernel
  set A : ℕ := max 1 (supNorm v) with hA
  set B : ℕ := max 1 (supNorm (v - δ)) with hB
  have hA1 : 1 ≤ A := le_max_left _ _
  have hB1 : 1 ≤ B := le_max_left _ _
  have hle : B ≤ 3 * A := by
    have h1 := supNorm_sub_le v δ
    have h2 : supNorm v ≤ A := le_max_right _ _
    rw [hB]
    exact max_le (by omega) (by omega)
  have hler : (B : ℝ) ≤ 3 * A := by exact_mod_cast hle
  have h3 : (B : ℝ) ^ 3 ≤ 27 * (A : ℝ) ^ 3 := by
    calc (B : ℝ) ^ 3 ≤ (3 * (A : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hler 3
      _ = 27 * (A : ℝ) ^ 3 := by ring
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith
theorem sum_bondsOf_eq {P : Finset Lattice4} (g : Lattice4 × Fin 4 → ℝ) :
    ∑ b ∈ bondsOf P, g b = ∑ y ∈ P, ∑ i, if y + basisVector i ∈ P then g (y, i) else 0 := by apply _root_.YangMills.Construction.PatchDifferences.sum_bondsOf <;> assumption
theorem sum_orientedPlaquettesOf_eq {P : Finset Lattice4} (g : Lattice4 × Fin 4 × Fin 4 → ℝ) :
    ∑ p ∈ orientedPlaquettesOf P, g p =
      ∑ y ∈ P, ∑ μ, ∑ ν, if (y, μ, ν) ∈ orientedPlaquettesOf P then g (y, μ, ν) else 0 := by apply _root_.YangMills.Construction.PatchDifferences.sum_orientedPlaquettesOf <;> assumption
theorem sum_cubicKernel_mul_shift_le {P Q : Finset Lattice4} (a δ : Lattice4) (hδ : supNorm δ ≤ 2) (g : Lattice4 → ℝ)
    (hg : ∀ y, 0 ≤ g y) (hin : ∀ y ∈ Q, y + δ ∈ P) :
    ∑ y ∈ Q, cubicKernel (a - y) * g (y + δ) ≤ 27 * ∑ y ∈ P, cubicKernel (a - y) * g y := by
  classical
  have hinj : Set.InjOn (fun y : Lattice4 => y + δ) (Q : Set Lattice4) := fun y _ y' _ e => add_right_cancel e
  have h1 : ∑ y ∈ Q, cubicKernel (a - y) * g (y + δ) ≤
      ∑ y ∈ Q, 27 * (cubicKernel (a - (y + δ)) * g (y + δ)) := by
    refine Finset.sum_le_sum fun y _ => ?_
    have h2 := cubicKernel_le_of_supNorm_le_two (a - y) δ hδ
    have e : a - y - δ = a - (y + δ) := by abel
    rw [e] at h2
    calc _ ≤ (27 * cubicKernel (a - (y + δ))) * g (y + δ) := mul_le_mul_of_nonneg_right h2 (hg _)
      _ = _ := by ring
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have e2 : ∑ y ∈ Q, cubicKernel (a - (y + δ)) * g (y + δ) =
      ∑ y ∈ Q.image (fun y => y + δ), cubicKernel (a - y) * g y :=
    (Finset.sum_image (f := fun y => cubicKernel (a - y) * g y) hinj).symm
  rw [e2]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ => mul_nonneg (cubicKernel_nonneg _) (hg y)
  intro y hy
  obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
  exact hin y' hy'
theorem sum_orientedPlaquettes_cubicKernel_le {P : Finset Lattice4} (a : Lattice4) (g : Lattice4 → ℝ)
    (hg : ∀ y, 0 ≤ g y) (D : Fin 4 → Fin 4 → Lattice4) (hD : ∀ μ ν, supNorm (D μ ν) ≤ 2)
    (hin : ∀ y μ ν, (y, μ, ν) ∈ orientedPlaquettesOf P → y + D μ ν ∈ P) :
    ∑ p ∈ orientedPlaquettesOf P, cubicKernel (a - p.1) * g (p.1 + D p.2.1 p.2.2) ≤
      432 * ∑ y ∈ P, cubicKernel (a - y) * g y := by
  classical
  rw [sum_orientedPlaquettesOf_eq, Finset.sum_comm]
  have h1 : ∀ μ : Fin 4, ∑ y ∈ P, ∑ ν, (if (y, μ, ν) ∈ orientedPlaquettesOf P then
      cubicKernel (a - y) * g (y + D μ ν) else 0) ≤ 4 * (27 * ∑ y ∈ P, cubicKernel (a - y) * g y) := by
    intro μ
    rw [Finset.sum_comm]
    have h2 : ∀ ν : Fin 4, ∑ y ∈ P, (if (y, μ, ν) ∈ orientedPlaquettesOf P then
        cubicKernel (a - y) * g (y + D μ ν) else 0) ≤ 27 * ∑ y ∈ P, cubicKernel (a - y) * g y := by
      intro ν
      rw [← Finset.sum_filter]
      refine sum_cubicKernel_mul_shift_le a (D μ ν) (hD μ ν) g hg fun y hy => hin y μ ν (Finset.mem_filter.1 hy).2
    calc _ ≤ ∑ _ν : Fin 4, 27 * ∑ y ∈ P, cubicKernel (a - y) * g y := Finset.sum_le_sum fun ν _ => h2 ν
      _ = _ := by simp
  calc _ ≤ ∑ _μ : Fin 4, 4 * (27 * ∑ y ∈ P, cubicKernel (a - y) * g y) := Finset.sum_le_sum fun μ _ => h1 μ
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
end Sums
section Sizes
variable {F : BlockFrame} {S : Finset F.Cell}
theorem sectionNormOn_nonneg (ξ : F.Site 0 → ℍ[ℝ]) (t : F.Site 0) : 0 ≤ PatchDifferences.sectionNormOn S ξ t := by apply _root_.YangMills.Construction.PatchDifferences.sectionNormOn_nonneg <;> assumption
variable {z : F.Cell}
theorem restrictToPatch_nonneg {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t) (t : F.Site 0) : 0 ≤ restrictToPatch S z f t := by apply _root_.YangMills.Construction.PatchDifferences.restrictToPatch_nonneg <;> assumption
theorem restrictToPatch_of_mem {f : F.Site 0 → ℝ} {t : F.Site 0} (ht : t ∈ patchSiteSet S z) :
    restrictToPatch S z f t = f t := by apply _root_.YangMills.Construction.PatchDifferences.restrictToPatch_of_mem <;> assumption
theorem restrictToPatch_of_not_mem {f : F.Site 0 → ℝ} {t : F.Site 0} (ht : t ∉ patchSiteSet S z) :
    restrictToPatch S z f t = 0 := by apply _root_.YangMills.Construction.PatchDifferences.restrictToPatch_of_not_mem <;> assumption
theorem restrictToPatch_le {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t) (t : F.Site 0) : restrictToPatch S z f t ≤ f t := by
  classical
  simp only [restrictToPatch]
  split_ifs
  · exact le_rfl
  · exact hf t
def neighbourSum (S : Finset F.Cell) (z : F.Cell) (f : F.Site 0 → ℝ) : F.Site 0 → ℝ :=
  restrictToPatch S z (fun t => f t + ∑ st : PathStep, f (t + stepDisplacement 0 st))
theorem neighbourSum_nonneg {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t) (t : F.Site 0) : 0 ≤ neighbourSum S z f t := by apply _root_.YangMills.Construction.PatchDifferences.neighbourSum_nonneg <;> assumption
theorem le_neighbourSum_self {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t) {t : F.Site 0} (ht : t ∈ patchSiteSet S z) :
    f t ≤ neighbourSum S z f t := by apply _root_.YangMills.Construction.PatchDifferences.le_neighbourSum_self <;> assumption
theorem le_neighbourSum_step {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t) {t : F.Site 0} (ht : t ∈ patchSiteSet S z)
    (st : PathStep) : f (t + stepDisplacement 0 st) ≤ neighbourSum S z f t := by apply _root_.YangMills.Construction.PatchDifferences.le_neighbourSum_step <;> assumption
theorem le_neighbourSum_of_bond {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {a : Lattice4} {i : Fin 4} (ha : a ∈ patchDomain S z) (ha' : a + basisVector i ∈ patchDomain S z) :
    f (patchSite S z (a + basisVector i)) ≤ neighbourSum S z f (patchSite S z a) ∧
      f (patchSite S z a) ≤ neighbourSum S z f (patchSite S z (a + basisVector i)) := by apply _root_.YangMills.Construction.PatchDifferences.le_neighbourSum_of_bond <;> assumption
theorem patchCubicKernel_nonneg {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t) (t : F.Site 0) :
    0 ≤ patchCubicKernel S z f t := by
  classical
  simp only [patchCubicKernel]
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => mul_nonneg (cubicKernel_nonneg _) (hf _)
  · exact le_rfl
theorem patchCubicKernel_of_not_mem {f : F.Site 0 → ℝ} {t : F.Site 0} (ht : t ∉ patchSiteSet S z) :
    patchCubicKernel S z f t = 0 := by
  classical
  simp [patchCubicKernel, ht]
theorem cellSeminorm_eq_zero_of_vanish {M : (F.Site 0 → ℝ) → F.Cell → ℝ} (hM : IsCellSeminorm S M)
    {f : F.Site 0 → ℝ} {y : F.Cell} (h : ∀ x ∈ cellSites S y, f x = 0) : M f y = 0 := by apply _root_.YangMills.Construction.PatchDifferences.cellSeminorm_eq_zero_of_vanish <;> assumption
theorem card_pathStep : Fintype.card PathStep = 8 := by apply _root_.YangMills.Construction.PatchDifferences.card_pathStep <;> assumption
theorem card_le_of_cellSupDist_le (hamb : IsAdmissibleAmbient F) (y1 : F.Cell) (r : ℕ) (A : Finset F.Cell)
    (hA : ∀ y ∈ A, cellSupDist y1 y ≤ r) : A.card ≤ (2 * r + 1) ^ 4 := by apply _root_.YangMills.Construction.PatchDifferences.card_le_of_cellSupDist_le <;> assumption
theorem card_cellBall_le (hamb : IsAdmissibleAmbient F) (z : F.Cell) (r : ℕ) :
    ((cellBall S z r).card : ℝ) ≤ ((2 * r + 1) ^ 4 : ℕ) := by
  have := card_le_of_cellSupDist_le hamb z r (cellBall S z r) fun y hy => (Finset.mem_filter.1 hy).2
  exact_mod_cast this
theorem base_neighbourSum_le {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
    (hN : CellNormFamily S Md Lf Sr σ K) {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t)
    (hoff : ∀ x, x ∉ sitesOfCells S 0 → f x = 0) (y : F.Cell) :
    Md (neighbourSum S z f) y ≤ Md f y + 8 * (K * ∑ y1 ∈ cellBall S y 1, Md f y1) := by
  classical
  have h1 : Md (neighbourSum S z f) y ≤ Md (fun t => f t + ∑ st : PathStep, f (t + stepDisplacement 0 st)) y := by
    refine hN.isSeminorm_base.mono_abs _ _ _ fun x _ => ?_
    have h0 : 0 ≤ f x + ∑ st : PathStep, f (x + stepDisplacement 0 st) :=
      add_nonneg (hf x) (Finset.sum_nonneg fun _ _ => hf _)
    rw [abs_of_nonneg (neighbourSum_nonneg hf x), abs_of_nonneg h0]
    exact restrictToPatch_le (fun t => add_nonneg (hf t) (Finset.sum_nonneg fun _ _ => hf _)) x
  refine h1.trans ((hN.isSeminorm_base.add_le _ _ y).trans ?_)
  have h2 := hN.isSeminorm_base.sum_le Finset.univ (fun (st : PathStep) x => f (x + stepDisplacement 0 st)) y
  have h3 : ∑ st : PathStep, Md (fun x => f (x + stepDisplacement 0 st)) y ≤
      ∑ _st : PathStep, K * ∑ y1 ∈ cellBall S y 1, Md f y1 :=
    Finset.sum_le_sum fun st _ => hN.base_shift_le st f y hoff
  rw [Finset.sum_const, Finset.card_univ, card_pathStep] at h3
  simp only [nsmul_eq_mul] at h3
  push_cast at h3
  linarith
end Sizes
section Cells
variable {F : BlockFrame} {S : Finset F.Cell}
theorem cellSideLength_cast (F : BlockFrame) : (cellSideLength F : ℝ) = (F.blockSide : ℝ) ^ F.top := by
  simp [cellSideLength]
theorem siteOfCoords_injOn_centredCube (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {h h' : Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ F.top)) (hh' : h' ∈ centredCube (F.blockSide ^ F.top))
    (e : siteOfCoords (F := F) 0 h = siteOfCoords 0 h') : h = h' := by
  have hL := hodd.pos
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  funext i
  have a := (mem_centredCube_iff h).1 hh i
  have b := (mem_centredCube_iff h').1 hh' i
  have e1 : ((h i : ℤ) : ZMod (F.period 0 i)) = ((h' i : ℤ) : ZMod (F.period 0 i)) := congrFun e i
  have e2 := congrArg ZMod.valMinAbs e1
  rwa [valMinAbs_of_abs_lt hamb hL i (by rw [abs_lt]; constructor <;> omega),
    valMinAbs_of_abs_lt hamb hL i (by rw [abs_lt]; constructor <;> omega)] at e2
theorem sum_cellOffsets_patchSite {M : Type} [AddCommMonoid M] {z : F.Cell} (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (G : F.Site 0 → M) :
    ∑ a ∈ cellOffsets F, G (patchSite S z a) =
      ∑ h ∈ centredCube (F.blockSide ^ F.top), G (cellCentre 0 z + siteOfCoords 0 h) := by
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  refine Finset.sum_nbij' (fun a k => closedOrthant S z k * (a k - (cellSideLength F - 1) / 2))
    (fun h k => closedOrthant S z k * h k + (cellSideLength F - 1) / 2) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [mem_centredCube_iff]
    intro i
    have := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 ha i)
    rcases he i with hs | hs <;> rw [hs] <;> constructor <;> omega
  · intro h hh
    have := (mem_centredCube_iff h).1 hh
    refine Fintype.mem_piFinset.2 fun i => Finset.mem_Ico.2 ?_
    have h2 := this i
    rcases he i with hs | hs <;> rw [hs] <;> constructor <;> omega
  · intro a _
    funext k
    have := closedOrthant_mul_self he k
    calc _ = (closedOrthant S z k * closedOrthant S z k) * (a k - (cellSideLength F - 1) / 2) +
          (cellSideLength F - 1) / 2 := by ring
      _ = _ := by rw [this]; ring
  · intro h _
    funext k
    have := closedOrthant_mul_self he k
    calc _ = (closedOrthant S z k * closedOrthant S z k) * h k := by ring
      _ = _ := by rw [this]; ring
  · intro a _
    rfl
theorem sum_centredCube_le_sum_cellSites (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {y : F.Cell}
    (hy : y ∈ S) (f : F.Site 0 → ℝ) (hf : ∀ t, 0 ≤ f t) :
    ∑ h ∈ centredCube (F.blockSide ^ F.top), f (cellCentre 0 y + siteOfCoords 0 h) ≤ ∑ t ∈ cellSites S y, f t := by
  classical
  have hinj : Set.InjOn (fun h : Lattice4 => cellCentre (F := F) 0 y + siteOfCoords 0 h)
      (centredCube (F.blockSide ^ F.top) : Set Lattice4) := by
    intro h hh h' hh' e
    exact siteOfCoords_injOn_centredCube hamb hodd hh hh' (add_left_cancel e)
  rw [← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ => hf t
  intro t ht
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 ht
  refine Finset.mem_filter.2 ⟨mem_sitesOfCells.2 ⟨y, hy, h, by simpa using hh, rfl⟩, ?_⟩
  exact LocalPartition.enclosingCell_cellCentre_add hodd y h (by simpa using hh)
theorem scale_mul_cellMean_le {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
    (hN : CellNormFamily S Md Lf Sr σ K) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {y : F.Cell}
    (hy : y ∈ S) (f : F.Site 0 → ℝ) (hf : ∀ t, 0 ≤ f t) :
    σ y * ((1 / (cellSideLength F : ℝ) ^ 4) *
        ∑ h ∈ centredCube (F.blockSide ^ F.top), f (cellCentre 0 y + siteOfCoords 0 h)) ≤
      K * Md f y / (cellSideLength F : ℝ) := by
  have hNp : (0 : ℝ) < cellSideLength F := by exact_mod_cast BlockAverages.cellSideLength_pos (F := F) hodd.pos
  have h1 := sum_centredCube_le_sum_cellSites hamb hodd hy f hf
  have h2 := hN.mean_le f y
  have h3 : ∑ x ∈ cellSites S y, |f x| = ∑ x ∈ cellSites S y, f x :=
    Finset.sum_congr rfl fun x _ => abs_of_nonneg (hf x)
  rw [h3] at h2
  have h4 : σ y * ∑ h ∈ centredCube (F.blockSide ^ F.top), f (cellCentre 0 y + siteOfCoords 0 h) ≤
      K * (cellSideLength F : ℝ) ^ 3 * Md f y :=
    (mul_le_mul_of_nonneg_left h1 (hN.scale_pos y).le).trans h2
  calc _ = (σ y * ∑ h ∈ centredCube (F.blockSide ^ F.top), f (cellCentre 0 y + siteOfCoords 0 h)) /
        (cellSideLength F : ℝ) ^ 4 := by
        field_simp
    _ ≤ (K * (cellSideLength F : ℝ) ^ 3 * Md f y) / (cellSideLength F : ℝ) ^ 4 :=
        div_le_div_of_nonneg_right h4 (by positivity)
    _ = _ := by field_simp
theorem card_cellOffsets_eq (hL : 0 < F.blockSide) :
    ((cellOffsets F).card : ℝ) = (cellSideLength F : ℝ) ^ 4 := by apply _root_.YangMills.Construction.PatchDifferences.card_cellOffsets_eq <;> assumption
def cellMean (F : BlockFrame) (g : Lattice4 → ℍ[ℝ]) : ℍ[ℝ] :=
  (1 / (cellSideLength F : ℝ) ^ 4) • ∑ x ∈ cellOffsets F, g x
theorem cellMean_const (hL : 0 < F.blockSide) (c : ℍ[ℝ]) : cellMean F (fun _ => c) = c := by apply _root_.YangMills.Construction.PatchDifferences.cellMean_const <;> assumption
theorem cellMean_sub (g g' : Lattice4 → ℍ[ℝ]) :
    cellMean F (fun x => g x - g' x) = cellMean F g - cellMean F g' := by
  simp only [cellMean, Finset.sum_sub_distrib, smul_sub]
theorem cellMean_congr {g g' : Lattice4 → ℍ[ℝ]} (h : ∀ x ∈ cellOffsets F, g x = g' x) :
    cellMean F g = cellMean F g' := by apply _root_.YangMills.Construction.PatchDifferences.cellMean_congr <;> assumption
theorem norm_cellMean_le (hL : 0 < F.blockSide) (g : Lattice4 → ℍ[ℝ]) (b : Lattice4 → ℝ)
    (h : ∀ x ∈ cellOffsets F, ‖g x‖ ≤ b x) :
    ‖cellMean F g‖ ≤ (1 / (cellSideLength F : ℝ) ^ 4) * ∑ x ∈ cellOffsets F, b x := by apply _root_.YangMills.Construction.PatchDifferences.norm_cellMean_le <;> assumption
end Cells
section Patch
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
def toQuaternionForm (u : F.Site 0 → Fin 4 → imaginaryQuaternions) : F.Site 0 → Fin 4 → ℍ[ℝ] :=
  fun t k => (u t k : ℍ[ℝ])
def centredPotential (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (a : Lattice4) : ℍ[ℝ] :=
  localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u) a -
    localPotentialMean S V (referenceFieldChain S V 0) z (toQuaternionForm u)
def potentialSection (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) : ℍ[ℝ] :=
  adjointAction (frameChange S V z t) (centredPotential S V z u (patchChart S z t))
def primitiveDefect (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) (i : Fin 4) : ℍ[ℝ] :=
  toQuaternionForm u t i + covariantDiff (referenceFieldChain S V 0) (potentialSection S V z u) t i
def curlNorm (S : Finset F.Cell) (V : F.GaugeField F.top) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) :
    F.Site 0 → ℝ := by
  classical exact fun t => ∑ μ, ∑ ν, if (t, μ, ν) ∈ innerPlaquettes S 0 then
    ‖linearizedCurl (referenceFieldChain S V 0) u (t, μ, ν)‖ else 0
def curlSource (κ : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (t : F.Site 0) : ℝ :=
  curlNorm S V u t + 24 * κ * PatchDifferences.formNormOn S (toQuaternionForm u) t
def curlKernelSource (κ : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) : F.Site 0 → ℝ :=
  patchCubicKernel S z (restrictToPatch S z (curlSource κ S V u))
def potentialNorm (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) : F.Site 0 → ℝ :=
  restrictToPatch S z fun t => ‖centredPotential S V z u (patchChart S z t)‖
def defectBound (κ C : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) : ℝ :=
  1728 * C * curlKernelSource κ S V z u t + 2 * κ * potentialNorm S V z u t
theorem curlNorm_nonneg (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) : 0 ≤ curlNorm S V u t := by
  classical
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> simp
theorem norm_linearizedCurl_le_curlNorm (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {t : F.Site 0} {μ ν : Fin 4}
    (hp : (t, μ, ν) ∈ innerPlaquettes S 0) :
    ‖linearizedCurl (referenceFieldChain S V 0) u (t, μ, ν)‖ ≤ curlNorm S V u t := by
  classical
  have h1 : (if (t, μ, ν) ∈ innerPlaquettes S 0 then ‖linearizedCurl (referenceFieldChain S V 0) u (t, μ, ν)‖ else 0) ≤
      ∑ ν, if (t, μ, ν) ∈ innerPlaquettes S 0 then ‖linearizedCurl (referenceFieldChain S V 0) u (t, μ, ν)‖ else 0 :=
    Finset.single_le_sum (f := fun ν => if (t, μ, ν) ∈ innerPlaquettes S 0 then
      ‖linearizedCurl (referenceFieldChain S V 0) u (t, μ, ν)‖ else 0) (fun _ _ => by split_ifs <;> simp)
      (Finset.mem_univ ν)
  have h2 := Finset.single_le_sum (f := fun μ => ∑ ν, if (t, μ, ν) ∈ innerPlaquettes S 0 then
    ‖linearizedCurl (referenceFieldChain S V 0) u (t, μ, ν)‖ else 0)
    (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> simp) (Finset.mem_univ μ)
  rw [if_pos hp] at h1
  exact h1.trans (by simpa [curlNorm] using h2)
theorem curlSource_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) :
    0 ≤ curlSource κ S V u t :=
  add_nonneg (curlNorm_nonneg u t) (mul_nonneg (by positivity) (zero_le_formNormOn _ t))
theorem curlKernelSource_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) :
    0 ≤ curlKernelSource κ S V z u t :=
  patchCubicKernel_nonneg (restrictToPatch_nonneg (curlSource_nonneg hκ u)) t
theorem potentialNorm_nonneg (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) :
    0 ≤ potentialNorm S V z u t :=
  restrictToPatch_nonneg (fun _ => norm_nonneg _) t
theorem defectBound_nonneg {κ C : ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (t : F.Site 0) : 0 ≤ defectBound κ C S V z u t :=
  add_nonneg (mul_nonneg (by positivity) (curlKernelSource_nonneg hκ u t))
    (mul_nonneg (by positivity) (potentialNorm_nonneg u t))
theorem defectBound_of_not_mem {κ C : ℝ} (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {t : F.Site 0}
    (ht : t ∉ patchSiteSet S z) : defectBound κ C S V z u t = 0 := by
  simp only [defectBound, curlKernelSource, potentialNorm]
  rw [patchCubicKernel_of_not_mem ht, restrictToPatch_of_not_mem ht]
  simp
variable {Cs r C : ℝ}
theorem PotentialSetting.coldnessRatio_nonneg (h : PotentialSetting S V Cs r C) :
    0 ≤ Cs / (cellSideLength F : ℝ) :=
  div_nonneg h.coldness_nonneg h.cellSideLength_pos.le
theorem PotentialSetting.patchChart_patchSite (h : PotentialSetting S V Cs r C) {a : Lattice4}
    (ha : a ∈ patchDomain S z) : patchChart S z (patchSite S z a) = a :=
  PatchPoints.patchChart_patchSite h.ambient h.odd_side (h.closedOrthant_cases z) (patchDomain_coord_bounds ha)
theorem localSection_potentialSection (h : PotentialSetting S V Cs r C) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    {a : Lattice4} (ha : a ∈ patchDomain S z) :
    PatchDifferences.localSection S V z (potentialSection S V z u) a = centredPotential S V z u a := by
  simp only [PatchDifferences.localSection, potentialSection]
  rw [adjointAction_inv_apply_apply, h.patchChart_patchSite ha]
theorem covariantDiff_oriented (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (ξ : F.Site 0 → ℍ[ℝ]) (a : Lattice4) (i : Fin 4) :
    (if closedOrthant S z i = 1 then covariantDiff (referenceFieldChain S V 0) ξ (patchSite S z a) i
      else - adjointAction (referenceFieldChain S V 0 (patchSite S z (a + basisVector i)) i)⁻¹
        (covariantDiff (referenceFieldChain S V 0) ξ (patchSite S z (a + basisVector i)) i)) =
      adjointAction (leadingTransport S V (patchSite S z a) (patchSite S z (a + basisVector i)))
        (ξ (patchSite S z (a + basisVector i))) - ξ (patchSite S z a) := by apply _root_.YangMills.Construction.PatchDifferences.covariantDiff_oriented <;> assumption
variable {R : Lattice4 → Lattice4 → UnitQuaternion}
def frameRemainder (R : Lattice4 → Lattice4 → UnitQuaternion) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (z : F.Cell) (ξ : F.Site 0 → ℍ[ℝ]) : Lattice4 → Fin 4 → ℍ[ℝ] :=
  fun a i => adjointAction (R a (a + basisVector i)) (PatchDifferences.localSection S V z ξ (a + basisVector i)) -
    PatchDifferences.localSection S V z ξ (a + basisVector i)
theorem localForm_covariantDiff (hF : IsPatchFrame S V z R Cs r) (hr1 : 1 ≤ r * cellSideLength F)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (ξ : F.Site 0 → ℍ[ℝ]) {a : Lattice4} {i : Fin 4}
    (ha : a ∈ patchDomain S z) (ha' : a + basisVector i ∈ patchDomain S z) :
    localForm S V (referenceFieldChain S V 0) z (covariantDiff (referenceFieldChain S V 0) ξ) a i =
      latticeDifference (PatchDifferences.localSection S V z ξ) a i + frameRemainder R S V z ξ a i := by
  have hl := hF.leadingTransport_eq a ha (a + basisVector i) ha'
    (by rw [supNorm_add_basisVector_sub_self]; simpa using hr1)
  simp only [localForm, latticeDifference, frameRemainder]
  rw [covariantDiff_oriented he ξ a i, hl, adjointAction_apply_sub]
  simp only [PatchDifferences.localSection]
  rw [← adjointAction_mul_apply, ← adjointAction_mul_apply]
  have e : (frameChange S V z (patchSite S z a))⁻¹ * (frameChange S V z (patchSite S z a) * R a (a + basisVector i) *
      (frameChange S V z (patchSite S z (a + basisVector i)))⁻¹) =
      R a (a + basisVector i) * (frameChange S V z (patchSite S z (a + basisVector i)))⁻¹ := by
    group
  rw [e]
  abel
theorem norm_localSection (ξ : F.Site 0 → ℍ[ℝ]) (a : Lattice4) :
    ‖PatchDifferences.localSection S V z ξ a‖ = ‖ξ (patchSite S z a)‖ := norm_adjointAction_apply _ _
theorem norm_frameRemainder_le (hF : IsPatchFrame S V z R Cs r) (hr1 : 1 ≤ r * cellSideLength F)
    (ξ : F.Site 0 → ℍ[ℝ]) {a : Lattice4} {i : Fin 4}
    (ha : a ∈ patchDomain S z) (ha' : a + basisVector i ∈ patchDomain S z) :
    ‖frameRemainder R S V z ξ a i‖ ≤ 2 * (Cs / (cellSideLength F : ℝ)) * ‖ξ (patchSite S z (a + basisVector i))‖ := by
  have hn := hF.norm_sub_one_le a ha (a + basisVector i) ha'
    (by rw [supNorm_add_basisVector_sub_self]; simpa using hr1)
  rw [supNorm_add_basisVector_sub_self] at hn
  simp only [frameRemainder]
  refine (norm_adjointAction_apply_sub_le _ _).trans ?_
  rw [norm_localSection]
  have h2 : ‖((R a (a + basisVector i) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Cs / (cellSideLength F : ℝ) := by
    simpa [div_eq_mul_inv] using hn
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
theorem norm_plaquetteCurl_localForm_le_of_lt (h : PotentialSetting S V Cs r C) (hF : IsPatchFrame S V z R Cs r)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {y : Lattice4} {μ ν : Fin 4}
    (hμν : μ < ν) (h0 : y ∈ patchDomain S z) (h1 : y + basisVector μ ∈ patchDomain S z)
    (h2 : y + basisVector ν ∈ patchDomain S z) (h3 : y + basisVector μ + basisVector ν ∈ patchDomain S z) :
    ‖plaquetteCurl (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u)) y μ ν‖ ≤
      curlSource (Cs / (cellSideLength F : ℝ)) S V u (patchSite S z y) +
        curlSource (Cs / (cellSideLength F : ℝ)) S V u (patchSite S z (y + basisVector μ)) +
        curlSource (Cs / (cellSideLength F : ℝ)) S V u (patchSite S z (y + basisVector ν)) +
        curlSource (Cs / (cellSideLength F : ℝ)) S V u (patchSite S z (y + basisVector μ + basisVector ν)) := by
  classical
  have hP := h.patchSiteSet_subset z
  have he := h.closedOrthant_cases z
  have hcomm : y + basisVector ν + basisVector μ = y + basisVector μ + basisVector ν := add_right_comm _ _ _
  have h3' : y + basisVector ν + basisVector μ ∈ patchDomain S z := by rwa [hcomm]
  have n1 := norm_localForm_sub_signedChartForm_le hF h.scale h.ambient h.odd_side he h.coldness_nonneg hP
    (toQuaternionForm u) h0 h1
  have n2 := norm_localForm_sub_signedChartForm_le hF h.scale h.ambient h.odd_side he h.coldness_nonneg hP
    (toQuaternionForm u) h1 h3
  have n3 := norm_localForm_sub_signedChartForm_le hF h.scale h.ambient h.odd_side he h.coldness_nonneg hP
    (toQuaternionForm u) h2 h3'
  have n4 := norm_localForm_sub_signedChartForm_le hF h.scale h.ambient h.odd_side he h.coldness_nonneg hP
    (toQuaternionForm u) h0 h2
  rw [hcomm] at n3
  obtain ⟨x, A, B, D, hQ, eA, eB, eD, hn⟩ :=
    exists_norm_plaquetteCurl_signedChartForm_eq he (patchFrameForm S V z (toQuaternionForm u)) y μ ν
  have hm : ∀ {q : Lattice4}, q ∈ patchDomain S z → patchSite S z q ∈ patchSiteSet S z :=
    fun hq => Finset.mem_image_of_mem _ hq
  obtain ⟨hx, hA, hB, hD⟩ := hQ (fun t => t ∈ patchSiteSet S z) (hm h0) (hm h1) (hm h2) (hm h3)
  set κ := Cs / (cellSideLength F : ℝ) with hκ
  have hκ0 : 0 ≤ κ := h.coldnessRatio_nonneg
  set P0 := patchSite S z y with hP0
  set P1 := patchSite S z (y + basisVector μ) with hP1
  set P2 := patchSite S z (y + basisVector ν) with hP2
  set P3 := patchSite S z (y + basisVector μ + basisVector ν) with hP3
  obtain ⟨sc, hsc⟩ : ∃ sc, sc = curlNorm S V u P0 + curlNorm S V u P1 + curlNorm S V u P2 + curlNorm S V u P3 :=
    ⟨_, rfl⟩
  obtain ⟨sz, hsz⟩ : ∃ sz, sz = PatchDifferences.formNormOn S (toQuaternionForm u) P0 +
      PatchDifferences.formNormOn S (toQuaternionForm u) P1 + PatchDifferences.formNormOn S (toQuaternionForm u) P2 +
      PatchDifferences.formNormOn S (toQuaternionForm u) P3 := ⟨_, rfl⟩
  have c0 := curlNorm_nonneg (S := S) (V := V) u P0
  have c1 := curlNorm_nonneg (S := S) (V := V) u P1
  have c2 := curlNorm_nonneg (S := S) (V := V) u P2
  have c3 := curlNorm_nonneg (S := S) (V := V) u P3
  have z0 := zero_le_formNormOn (S := S) (toQuaternionForm u) P0
  have z1 := zero_le_formNormOn (S := S) (toQuaternionForm u) P1
  have z2 := zero_le_formNormOn (S := S) (toQuaternionForm u) P2
  have z3 := zero_le_formNormOn (S := S) (toQuaternionForm u) P3
  obtain ⟨qx, qA, qB, qD⟩ := hQ (fun t => curlNorm S V u t ≤ sc ∧
      PatchDifferences.formNormOn S (toQuaternionForm u) t ≤ sz)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  subst eA eB eD
  have near := norm_linearizedCurl_sub_flatCurl_le hF h.scale h.ambient h.odd_side he u hx hA hB hD
  have hplaq : (x, μ, ν) ∈ innerPlaquettes S 0 := by
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hP hx,
      Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩, hμν, ?_⟩
    intro t ht
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact hP hx
    · exact hP hA
    · exact hP hB
    · exact hP hD
  have hDu := norm_linearizedCurl_le_curlNorm (V := V) u hplaq
  have b1 := norm_le_formNormOn (S := S) (toQuaternionForm u) (mem_innerBonds_of_step (k := ν) (hP hA) (hP hD) rfl)
  have hD' : x + unitStep 0 ν + unitStep 0 μ = x + unitStep 0 μ + unitStep 0 ν := add_right_comm _ _ _
  have b2 := norm_le_formNormOn (S := S) (toQuaternionForm u) (mem_innerBonds_of_step (k := μ) (hP hB) (hP hD) hD')
  have b3 := norm_le_formNormOn (S := S) (toQuaternionForm u) (mem_innerBonds_of_step (k := ν) (hP hx) (hP hB) rfl)
  have e1 : ‖flatCurl (patchFrameForm S V z (toQuaternionForm u)) x μ ν‖ ≤
      ‖linearizedCurl (referenceFieldChain S V 0) u (x, μ, ν)‖ +
      κ * (2 * ‖(u (x + unitStep 0 μ) ν : ℍ[ℝ])‖ + 6 * ‖(u (x + unitStep 0 ν) μ : ℍ[ℝ])‖ +
        8 * ‖(u x ν : ℍ[ℝ])‖) := by
    have t1 := norm_sub_le (adjointAction (frameChange S V z x)⁻¹ (linearizedCurl (referenceFieldChain S V 0) u (x, μ, ν)))
      (adjointAction (frameChange S V z x)⁻¹ (linearizedCurl (referenceFieldChain S V 0) u (x, μ, ν)) -
        flatCurl (patchFrameForm S V z (toQuaternionForm u)) x μ ν)
    rw [sub_sub_cancel, norm_adjointAction_apply] at t1
    exact t1.trans (add_le_add le_rfl near)
  have e2 : 2 * ‖(u (x + unitStep 0 μ) ν : ℍ[ℝ])‖ + 6 * ‖(u (x + unitStep 0 ν) μ : ℍ[ℝ])‖ +
      8 * ‖(u x ν : ℍ[ℝ])‖ ≤ 16 * sz := by
    have q1 := qA.2
    have q2 := qB.2
    have q3 := qx.2
    have r1 : ‖(u (x + unitStep 0 μ) ν : ℍ[ℝ])‖ ≤ sz := b1.trans q1
    have r2 : ‖(u (x + unitStep 0 ν) μ : ℍ[ℝ])‖ ≤ sz := b2.trans q2
    have r3 : ‖(u x ν : ℍ[ℝ])‖ ≤ sz := b3.trans q3
    linarith
  have e3 := mul_le_mul_of_nonneg_left e2 hκ0
  have ecurl : plaquetteCurl (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u)) y μ ν =
      plaquetteCurl (signedChartForm S z (patchFrameForm S V z (toQuaternionForm u))) y μ ν +
      ((localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u) y μ -
          signedChartForm S z (patchFrameForm S V z (toQuaternionForm u)) y μ) +
        (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u) (y + basisVector μ) ν -
          signedChartForm S z (patchFrameForm S V z (toQuaternionForm u)) (y + basisVector μ) ν) -
        (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u) (y + basisVector ν) μ -
          signedChartForm S z (patchFrameForm S V z (toQuaternionForm u)) (y + basisVector ν) μ) -
        (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u) y ν -
          signedChartForm S z (patchFrameForm S V z (toQuaternionForm u)) y ν)) := by
    simp only [plaquetteCurl]
    abel
  have e4 : ‖plaquetteCurl (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u)) y μ ν‖ ≤
      ‖flatCurl (patchFrameForm S V z (toQuaternionForm u)) x μ ν‖ +
      (2 * κ * PatchDifferences.formNormOn S (toQuaternionForm u) P1 +
        2 * κ * PatchDifferences.formNormOn S (toQuaternionForm u) P3 +
        2 * κ * PatchDifferences.formNormOn S (toQuaternionForm u) P3 +
        2 * κ * PatchDifferences.formNormOn S (toQuaternionForm u) P2) := by
    rw [ecurl, ← hn]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add n1 n2)) n3)) n4)
  have e5 : 2 * κ * PatchDifferences.formNormOn S (toQuaternionForm u) P1 +
      2 * κ * PatchDifferences.formNormOn S (toQuaternionForm u) P3 +
      2 * κ * PatchDifferences.formNormOn S (toQuaternionForm u) P3 +
      2 * κ * PatchDifferences.formNormOn S (toQuaternionForm u) P2 ≤ 2 * κ * (4 * sz) := by
    have e6 : PatchDifferences.formNormOn S (toQuaternionForm u) P1 +
        PatchDifferences.formNormOn S (toQuaternionForm u) P3 +
        PatchDifferences.formNormOn S (toQuaternionForm u) P3 +
        PatchDifferences.formNormOn S (toQuaternionForm u) P2 ≤ 4 * sz := by
      rw [hsz]
      linarith
    have := mul_le_mul_of_nonneg_left e6 (by positivity : 0 ≤ 2 * κ)
    linarith
  have e7 : curlSource κ S V u P0 + curlSource κ S V u P1 + curlSource κ S V u P2 + curlSource κ S V u P3 =
      sc + 24 * κ * sz := by
    simp only [curlSource]
    rw [hsc, hsz]
    ring
  rw [e7]
  have e8 := qx.1
  have e9 := hDu.trans e8
  nlinarith
theorem norm_plaquetteCurl_localForm_le (h : PotentialSetting S V Cs r C) (hF : IsPatchFrame S V z R Cs r)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {y : Lattice4} {μ ν : Fin 4}
    (hp : (y, μ, ν) ∈ orientedPlaquettesOf (patchDomain S z)) :
    ‖plaquetteCurl (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u)) y μ ν‖ ≤
      curlSource (Cs / (cellSideLength F : ℝ)) S V u (patchSite S z y) +
        curlSource (Cs / (cellSideLength F : ℝ)) S V u (patchSite S z (y + basisVector μ)) +
        curlSource (Cs / (cellSideLength F : ℝ)) S V u (patchSite S z (y + basisVector ν)) +
        curlSource (Cs / (cellSideLength F : ℝ)) S V u (patchSite S z (y + basisVector μ + basisVector ν)) := by
  classical
  obtain ⟨hm, hne, h1, h2, h3⟩ := Finset.mem_filter.1 hp
  have h0 : y ∈ patchDomain S z := (Finset.mem_product.1 hm).1
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact norm_plaquetteCurl_localForm_le_of_lt h hF u hlt h0 h1 h2 h3
  · have hcomm : y + basisVector ν + basisVector μ = y + basisVector μ + basisVector ν := add_right_comm _ _ _
    have h3' : y + basisVector ν + basisVector μ ∈ patchDomain S z := by rwa [hcomm]
    have key := norm_plaquetteCurl_localForm_le_of_lt h hF u hlt h0 h2 h1 h3'
    rw [hcomm] at key
    have e : plaquetteCurl (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u)) y μ ν =
        - plaquetteCurl (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u)) y ν μ := by
      simp only [plaquetteCurl]
      abel
    rw [e, norm_neg]
    linarith
theorem norm_sum_plaquetteKernel_curl_le (h : PotentialSetting S V Cs r C) (hF : IsPatchFrame S V z R Cs r)
    {H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ}
    (hH : ∀ b p, |H b p| ≤ C * cubicKernel (b.1 - p.1)) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    {a : Lattice4} {i : Fin 4} (ha : a ∈ patchDomain S z) :
    ‖∑ p ∈ orientedPlaquettesOf (patchDomain S z), H (a, i) p •
        plaquetteCurl (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u)) p.1 p.2.1 p.2.2‖ ≤
      1728 * C * curlKernelSource (Cs / (cellSideLength F : ℝ)) S V z u (patchSite S z a) := by
  classical
  have hκ0 := h.coldnessRatio_nonneg
  have hC := h.kernelConst_nonneg
  set κ := Cs / (cellSideLength F : ℝ) with hκ
  set P := patchDomain S z with hPd
  set G : Lattice4 → ℝ := fun y => curlSource κ S V u (patchSite S z y) with hG
  have hG0 : ∀ y, 0 ≤ G y := fun y => curlSource_nonneg hκ0 u _
  have hmem : ∀ {y μ ν}, (y, μ, ν) ∈ orientedPlaquettesOf P →
      y ∈ P ∧ y + basisVector μ ∈ P ∧ y + basisVector ν ∈ P ∧ y + basisVector μ + basisVector ν ∈ P := by
    intro y μ ν hp
    obtain ⟨hm, -, h1, h2, h3⟩ := Finset.mem_filter.1 hp
    exact ⟨(Finset.mem_product.1 hm).1, h1, h2, h3⟩
  have hthrough : curlKernelSource κ S V z u (patchSite S z a) = ∑ y ∈ P, cubicKernel (a - y) * G y := by
    simp only [curlKernelSource]
    rw [patchCubicKernel_patchSite_eq h.ambient h.odd_side (h.closedOrthant_cases z) _ ha]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [restrictToPatch_of_mem (Finset.mem_image_of_mem _ hy)]
  rw [hthrough]
  have s0 := sum_orientedPlaquettes_cubicKernel_le (P := P) a G hG0 (fun _ _ => 0) (fun _ _ => by simp [supNorm])
    (fun y μ ν hp => by simpa using (hmem hp).1)
  have s1 := sum_orientedPlaquettes_cubicKernel_le (P := P) a G hG0 (fun μ _ => basisVector μ)
    (fun μ _ => by rw [supNorm_basisVector_eq_one]; norm_num) (fun y μ ν hp => (hmem hp).2.1)
  have s2 := sum_orientedPlaquettes_cubicKernel_le (P := P) a G hG0 (fun _ ν => basisVector ν)
    (fun _ ν => by rw [supNorm_basisVector_eq_one]; norm_num) (fun y μ ν hp => (hmem hp).2.2.1)
  have s3 := sum_orientedPlaquettes_cubicKernel_le (P := P) a G hG0 (fun μ ν => basisVector μ + basisVector ν)
    (fun μ ν => (supNorm_add_le _ _).trans (by rw [supNorm_basisVector_eq_one, supNorm_basisVector_eq_one]))
    (fun y μ ν hp => by rw [← add_assoc]; exact (hmem hp).2.2.2)
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ p ∈ orientedPlaquettesOf P, ‖H (a, i) p •
      plaquetteCurl (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u)) p.1 p.2.1 p.2.2‖ ≤
      C * (cubicKernel (a - p.1) * G (p.1 + 0) + cubicKernel (a - p.1) * G (p.1 + basisVector p.2.1) +
        cubicKernel (a - p.1) * G (p.1 + basisVector p.2.2) +
        cubicKernel (a - p.1) * G (p.1 + (basisVector p.2.1 + basisVector p.2.2))) := by
    rintro ⟨y, μ, ν⟩ hp
    rw [norm_smul, Real.norm_eq_abs]
    have hc := norm_plaquetteCurl_localForm_le h hF u hp
    have hb := hH (a, i) (y, μ, ν)
    simp only [] at hb ⊢
    rw [add_zero, ← add_assoc]
    have hi := cubicKernel_nonneg (a - y)
    calc _ ≤ (C * cubicKernel (a - y)) *
          (G y + G (y + basisVector μ) + G (y + basisVector ν) + G (y + basisVector μ + basisVector ν)) :=
          mul_le_mul hb hc (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hs := add_le_add (add_le_add (add_le_add s0 s1) s2) s3
  have := mul_le_mul_of_nonneg_left hs hC
  refine this.trans (le_of_eq ?_)
  ring
theorem norm_localForm_of_sign_pos {R0 : F.GaugeField 0} {f : F.Site 0 → Fin 4 → ℍ[ℝ]} {i : Fin 4}
    (hs : closedOrthant S z i = 1) (a : Lattice4) :
    ‖localForm S V R0 z f a i‖ = ‖f (patchSite S z a) i‖ := by
  rw [localForm_of_sign_pos hs, norm_adjointAction_apply]
theorem norm_localForm_of_sign_neg {R0 : F.GaugeField 0} {f : F.Site 0 → Fin 4 → ℍ[ℝ]} {i : Fin 4}
    (hs : closedOrthant S z i = -1) (a : Lattice4) :
    ‖localForm S V R0 z f a i‖ = ‖f (patchSite S z (a + basisVector i)) i‖ := by
  rw [localForm_of_sign_neg hs, norm_adjointAction_apply, norm_neg, norm_adjointAction_apply]
theorem norm_localForm_le (h : PotentialSetting S V Cs r C) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) {a : Lattice4} {i : Fin 4}
    (ha : a ∈ patchDomain S z) (ha' : a + basisVector i ∈ patchDomain S z) :
    ‖localForm S V (referenceFieldChain S V 0) z f a i‖ ≤
      PatchDifferences.formNormOn S f (patchSite S z a) +
        PatchDifferences.formNormOn S f (patchSite S z (a + basisVector i)) := by
  classical
  have hP := h.patchSiteSet_subset z
  have he := h.closedOrthant_cases z
  have hs : patchSite S z a ∈ sitesOfCells S 0 := hP (Finset.mem_image_of_mem _ ha)
  have hs' : patchSite S z (a + basisVector i) ∈ sitesOfCells S 0 := hP (Finset.mem_image_of_mem _ ha')
  obtain ⟨k1, k2⟩ := patchSite_add_basisVector_cases he a i
  have n0 := zero_le_formNormOn (S := S) f (patchSite S z a)
  have n1 := zero_le_formNormOn (S := S) f (patchSite S z (a + basisVector i))
  rcases he i with hh | hh
  · rw [norm_localForm_of_sign_pos hh]
    have := norm_le_formNormOn (S := S) f (mem_innerBonds_of_step hs hs' (k1 hh).symm)
    linarith
  · rw [norm_localForm_of_sign_neg hh]
    have := norm_le_formNormOn (S := S) f (mem_innerBonds_of_step hs' hs (k2 hh).symm)
    linarith
theorem localForm_primitiveDefect (h : PotentialSetting S V Cs r C) (hF : IsPatchFrame S V z R Cs r)
    {H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {G : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hk : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H G C)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {a : Lattice4} {i : Fin 4} (ha : a ∈ patchDomain S z)
    (ha' : a + basisVector i ∈ patchDomain S z) :
    localForm S V (referenceFieldChain S V 0) z (primitiveDefect S V z u) a i =
      (∑ p ∈ orientedPlaquettesOf (patchDomain S z), H (a, i) p •
        plaquetteCurl (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u)) p.1 p.2.1 p.2.2) +
      frameRemainder R S V z (potentialSection S V z u) a i := by
  have e1 : localForm S V (referenceFieldChain S V 0) z (primitiveDefect S V z u) a i =
      localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u) a i +
        localForm S V (referenceFieldChain S V 0) z
          (covariantDiff (referenceFieldChain S V 0) (potentialSection S V z u)) a i :=
    localForm_apply_add_fun _ _ _ a i
  have e2 : latticeDifference (PatchDifferences.localSection S V z (potentialSection S V z u)) a i =
      localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u) (a + basisVector i) -
        localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u) a := by
    simp only [latticeDifference]
    rw [localSection_potentialSection h u ha', localSection_potentialSection h u ha]
    simp only [centredPotential]
    abel
  rw [e1, localForm_covariantDiff hF h.scale (h.closedOrthant_cases z) _ ha ha', e2, ← hk.curl_formula _ a i ha ha']
  simp only [localPotential]
  abel
theorem norm_potentialSection (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {t : F.Site 0}
    (ht : t ∈ patchSiteSet S z) : ‖potentialSection S V z u t‖ = potentialNorm S V z u t := by
  rw [potentialNorm, restrictToPatch_of_mem ht]
  exact norm_adjointAction_apply _ _
theorem norm_primitiveDefect_le (h : PotentialSetting S V Cs r C) (hF : IsPatchFrame S V z R Cs r)
    {H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {G : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hk : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H G C)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {t : F.Site 0} {i : Fin 4} (ht : t ∈ patchSiteSet S z)
    (ht' : t + unitStep 0 i ∈ patchSiteSet S z) :
    ‖primitiveDefect S V z u t i‖ ≤ defectBound (Cs / (cellSideLength F : ℝ)) C S V z u t +
      defectBound (Cs / (cellSideLength F : ℝ)) C S V z u (t + unitStep 0 i) := by
  obtain ⟨a, ha, ha', hc⟩ := exists_bond_in_patchChart h.ambient h.odd_side (h.closedOrthant_cases z) ht ht'
  have hκ := h.coldnessRatio_nonneg
  have hC := h.kernelConst_nonneg
  set κ := Cs / (cellSideLength F : ℝ) with hκd
  have hb : ‖localForm S V (referenceFieldChain S V 0) z (primitiveDefect S V z u) a i‖ ≤
      1728 * C * curlKernelSource κ S V z u (patchSite S z a) +
        2 * κ * potentialNorm S V z u (patchSite S z (a + basisVector i)) := by
    rw [localForm_primitiveDefect h hF hk u ha ha']
    refine (norm_add_le _ _).trans (add_le_add (norm_sum_plaquetteKernel_curl_le h hF hk.plaquette_bound u ha) ?_)
    rw [← norm_potentialSection u (Finset.mem_image_of_mem _ ha')]
    exact norm_frameRemainder_le hF h.scale _ ha ha'
  have c0 := curlKernelSource_nonneg (S := S) (V := V) (z := z) hκ u t
  have c1 := curlKernelSource_nonneg (S := S) (V := V) (z := z) hκ u (t + unitStep 0 i)
  have p0 := potentialNorm_nonneg (S := S) (V := V) (z := z) u t
  have p1 := potentialNorm_nonneg (S := S) (V := V) (z := z) u (t + unitStep 0 i)
  have d0 : 0 ≤ 1728 * C * curlKernelSource κ S V z u t := mul_nonneg (by positivity) c0
  have d1 : 0 ≤ 1728 * C * curlKernelSource κ S V z u (t + unitStep 0 i) := mul_nonneg (by positivity) c1
  have d2 : 0 ≤ 2 * κ * potentialNorm S V z u t := mul_nonneg (mul_nonneg (by norm_num) hκ) p0
  have d3 : 0 ≤ 2 * κ * potentialNorm S V z u (t + unitStep 0 i) := mul_nonneg (mul_nonneg (by norm_num) hκ) p1
  simp only [defectBound]
  rcases hc with ⟨hs, e1, e2⟩ | ⟨hs, e1, e2⟩
  · rw [norm_localForm_of_sign_pos hs, e1, e2] at hb
    linarith
  · rw [norm_localForm_of_sign_neg hs, e1, e2] at hb
    linarith
open Classical in
def stepNorms (P : Finset Lattice4) (S : Finset F.Cell) (z : F.Cell) (η : Lattice4 → ℍ[ℝ]) : F.Site 0 → ℝ :=
  fun t => if t ∈ patchSiteSet S z then
    ∑ i, if patchChart S z t ∈ P ∧ patchChart S z t + basisVector i ∈ P then
      ‖η (patchChart S z t + basisVector i) - η (patchChart S z t)‖ else 0 else 0
theorem stepNorms_nonneg (P : Finset Lattice4) (η : Lattice4 → ℍ[ℝ]) (t : F.Site 0) : 0 ≤ stepNorms P S z η t := by
  classical
  simp only [stepNorms]
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => by split_ifs <;> simp
  · exact le_rfl
theorem stepNorms_of_not_mem (P : Finset Lattice4) (η : Lattice4 → ℍ[ℝ]) {t : F.Site 0}
    (ht : t ∉ patchSiteSet S z) : stepNorms P S z η t = 0 := by
  classical
  simp [stepNorms, ht]
theorem stepNorms_patchSite (h : PotentialSetting S V Cs r C) (P : Finset Lattice4) (η : Lattice4 → ℍ[ℝ])
    {a : Lattice4} (ha : a ∈ patchDomain S z) :
    stepNorms P S z η (patchSite S z a) =
      ∑ i, if a ∈ P ∧ a + basisVector i ∈ P then ‖η (a + basisVector i) - η a‖ else 0 := by
  classical
  have hs : patchSite S z a ∈ patchSiteSet S z := Finset.mem_image_of_mem _ ha
  simp only [stepNorms, if_pos hs, h.patchChart_patchSite ha]
theorem norm_sub_endpointMean_le (h : PotentialSetting S V Cs r C) {l : ℕ} {c : Lattice4} {P : Finset Lattice4}
    {H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {G : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hk : HomotopyKernels l c P H G C) (hPP : P ⊆ patchDomain S z) (η : Lattice4 → ℍ[ℝ]) {x : Lattice4} (hx : x ∈ P) :
    ‖η x - endpointMean l c η‖ ≤ C * patchCubicKernel S z (stepNorms P S z η) (patchSite S z x) := by
  classical
  have hC := h.kernelConst_nonneg
  rw [hk.endpoint_formula η x hx, norm_neg, hk.pathMean_eq _ x hx,
    patchCubicKernel_patchSite_eq h.ambient h.odd_side (h.closedOrthant_cases z) _ (hPP hx), Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ b ∈ bondsOf P, ‖G x b • latticeDifference η b.1 b.2‖ ≤
      C * cubicKernel (x - b.1) * ‖η (b.1 + basisVector b.2) - η b.1‖ := by
    intro b _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hk.bond_bound x b) (norm_nonneg _)
  refine (Finset.sum_le_sum h1).trans ?_
  rw [sum_bondsOf_eq]
  have h2 : ∀ y ∈ P, (∑ i, if y + basisVector i ∈ P then
      C * cubicKernel (x - y) * ‖η (y + basisVector i) - η y‖ else 0) =
      C * (cubicKernel (x - y) * stepNorms P S z η (patchSite S z y)) := by
    intro y hy
    rw [stepNorms_patchSite h P η (hPP hy), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h3 : y + basisVector i ∈ P
    · rw [if_pos h3, if_pos ⟨hy, h3⟩]
      ring
    · rw [if_neg h3, if_neg fun h4 => h3 h4.2]
      simp
  rw [Finset.sum_congr rfl h2]
  refine Finset.sum_le_sum_of_subset_of_nonneg hPP fun y _ _ => ?_
  exact mul_nonneg hC (mul_nonneg (cubicKernel_nonneg _) (stepNorms_nonneg P η _))
theorem norm_sub_cellMean_le (h : PotentialSetting S V Cs r C) {H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ}
    {G : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hk : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H G C)
    (hz : z ∈ S) (η : Lattice4 → ℍ[ℝ]) {a : Lattice4} (ha : a ∈ patchDomain S z) :
    ‖η a - cellMean F η‖ ≤ C * patchCubicKernel S z (stepNorms (patchDomain S z) S z η) (patchSite S z a) +
      C * ((1 / (cellSideLength F : ℝ) ^ 4) *
        ∑ x ∈ cellOffsets F, patchCubicKernel S z (stepNorms (patchDomain S z) S z η) (patchSite S z x)) := by
  have hL := h.odd_side.pos
  set E := endpointMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) η with hE
  have e : η a - cellMean F η = (η a - E) - cellMean F (fun x => η x - E) := by
    rw [cellMean_sub, cellMean_const hL]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add (norm_sub_endpointMean_le h hk (Finset.Subset.refl _) η ha) ?_)
  have h2 := norm_cellMean_le hL (fun x => η x - E)
    (fun x => C * patchCubicKernel S z (stepNorms (patchDomain S z) S z η) (patchSite S z x))
    (fun x hx => norm_sub_endpointMean_le h hk (Finset.Subset.refl _) η
      (mem_patchDomain_of_mem_cellOffsets hz hL hx))
  refine h2.trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  ring
theorem stepNorms_localPotential_le (h : PotentialSetting S V Cs r C) (hF : IsPatchFrame S V z R Cs r)
    {H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {G : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hk : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H G C)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) :
    stepNorms (patchDomain S z) S z (localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u)) t ≤
      8 * neighbourSum S z (restrictToPatch S z (PatchDifferences.formNormOn S (toQuaternionForm u))) t +
        6912 * C * curlKernelSource (Cs / (cellSideLength F : ℝ)) S V z u t := by
  classical
  have hκ := h.coldnessRatio_nonneg
  have hC := h.kernelConst_nonneg
  have hf0 : ∀ t, 0 ≤ restrictToPatch S z (PatchDifferences.formNormOn S (toQuaternionForm u)) t :=
    restrictToPatch_nonneg (zero_le_formNormOn _)
  have n0 := neighbourSum_nonneg (S := S) (z := z) hf0 t
  have c0 := curlKernelSource_nonneg (S := S) (V := V) (z := z) hκ u t
  by_cases ht : t ∈ patchSiteSet S z
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
    rw [stepNorms_patchSite h _ _ ha]
    have hone : ∀ i : Fin 4, (if a ∈ patchDomain S z ∧ a + basisVector i ∈ patchDomain S z then
        ‖localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u) (a + basisVector i) -
          localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u) a‖ else 0) ≤
        2 * neighbourSum S z (restrictToPatch S z (PatchDifferences.formNormOn S (toQuaternionForm u)))
            (patchSite S z a) +
          1728 * C * curlKernelSource (Cs / (cellSideLength F : ℝ)) S V z u (patchSite S z a) := by
      intro i
      have hb0 : 0 ≤ 2 * neighbourSum S z (restrictToPatch S z (PatchDifferences.formNormOn S (toQuaternionForm u)))
            (patchSite S z a) +
          1728 * C * curlKernelSource (Cs / (cellSideLength F : ℝ)) S V z u (patchSite S z a) :=
        add_nonneg (mul_nonneg (by norm_num) n0) (mul_nonneg (by positivity) c0)
      split_ifs with hc
      · have h2 := hk.curl_formula (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u)) a i ha hc.2
        have e : localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u) (a + basisVector i) -
            localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u) a =
            (∑ p ∈ orientedPlaquettesOf (patchDomain S z), H (a, i) p •
              plaquetteCurl (localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u)) p.1 p.2.1 p.2.2) -
            localForm S V (referenceFieldChain S V 0) z (toQuaternionForm u) a i := by
          rw [← h2]
          simp only [localPotential]
          abel
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        have b1 := norm_sum_plaquetteKernel_curl_le (i := i) h hF hk.plaquette_bound u ha
        have b2 := norm_localForm_le h (toQuaternionForm u) ha hc.2
        have hs : patchSite S z a ∈ patchSiteSet S z := Finset.mem_image_of_mem _ ha
        have hs' : patchSite S z (a + basisVector i) ∈ patchSiteSet S z := Finset.mem_image_of_mem _ hc.2
        have b3 := (le_neighbourSum_of_bond hf0 (h.closedOrthant_cases z) ha hc.2).1
        rw [restrictToPatch_of_mem hs'] at b3
        have b4 := le_neighbourSum_self hf0 hs
        rw [restrictToPatch_of_mem hs] at b4
        linarith
      · exact hb0
    calc _ ≤ ∑ _i : Fin 4, (2 * neighbourSum S z (restrictToPatch S z
            (PatchDifferences.formNormOn S (toQuaternionForm u))) (patchSite S z a) +
          1728 * C * curlKernelSource (Cs / (cellSideLength F : ℝ)) S V z u (patchSite S z a)) :=
          Finset.sum_le_sum fun i _ => hone i
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  · rw [stepNorms_of_not_mem _ _ ht]
    exact add_nonneg (mul_nonneg (by norm_num) n0) (mul_nonneg (by positivity) c0)
end Patch
section Norms
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell} {Cs r C : ℝ}
  {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
theorem sum_sum_cellBall_one_le (hamb : IsAdmissibleAmbient F) (A : F.Cell → ℝ) (hA : ∀ y, 0 ≤ A y)
    (B : Finset F.Cell) (hB : B ⊆ S) (hoff : ∀ y ∈ S, y ∉ B → A y = 0) :
    ∑ y ∈ B, ∑ y1 ∈ cellBall S y 1, A y1 ≤ 81 * ∑ y1 ∈ B, A y1 := by apply _root_.YangMills.Construction.PatchDifferences.sum_sum_cellBall_one_le <;> assumption
theorem sum_base_neighbourSum_le (h : PotentialSetting S V Cs r C) (hK : 0 ≤ K) (hN : CellNormFamily S Md Lf Sr σ K)
    {f : F.Site 0 → ℝ} (hf0 : ∀ t, 0 ≤ f t) (hf : ∀ t, t ∉ patchSiteSet S z → f t = 0) :
    ∑ y ∈ cellBall S z 20, Md (neighbourSum S z f) y ≤ (1 + 8 * K * 81) * ∑ y ∈ cellBall S z 20, Md f y := by
  classical
  have hP := h.patchSiteSet_subset z
  have hoffS : ∀ x, x ∉ sitesOfCells S 0 → f x = 0 := fun x hx => hf x fun h => hx (hP h)
  have hB : cellBall S z 20 ⊆ S := Finset.filter_subset _ _
  have hd := sum_sum_cellBall_one_le h.ambient (fun y => Md f y) (fun y => hN.isSeminorm_base.nonneg f y)
    (cellBall S z 20) hB
    (fun y hy hn => cellSeminorm_eq_zero_of_vanish hN.isSeminorm_base fun x hx =>
      hf x (h.not_mem_patchSiteSet_of_not_mem_cellBall hy hn x hx))
  calc _ ≤ ∑ y ∈ cellBall S z 20, (Md f y + 8 * (K * ∑ y1 ∈ cellBall S y 1, Md f y1)) :=
        Finset.sum_le_sum fun y _ => base_neighbourSum_le hN hf0 hoffS y
    _ = ∑ y ∈ cellBall S z 20, Md f y + 8 * K * ∑ y ∈ cellBall S z 20, ∑ y1 ∈ cellBall S y 1, Md f y1 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ ≤ ∑ y ∈ cellBall S z 20, Md f y + 8 * K * (81 * ∑ y ∈ cellBall S z 20, Md f y) := by
        have := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 8 * K)
        linarith
    _ = _ := by ring
def curlTotal (Sr : (F.Site 0 → ℝ) → F.Cell → ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (z : F.Cell) : ℝ :=
  ∑ x ∈ cellBall S z 20, Sr (curlNorm S V u) x
def formTotal (Md : (F.Site 0 → ℝ) → F.Cell → ℝ) (S : Finset F.Cell) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (z : F.Cell) : ℝ :=
  ∑ x ∈ cellBall S z 20, Md (PatchDifferences.formNormOn S (toQuaternionForm u)) x
theorem curlTotal_nonneg (hN : CellNormFamily S Md Lf Sr σ K) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (z : F.Cell) : 0 ≤ curlTotal Sr S V u z :=
  Finset.sum_nonneg fun _ _ => hN.isSeminorm_source.nonneg _ _
theorem formTotal_nonneg (hN : CellNormFamily S Md Lf Sr σ K) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (z : F.Cell) : 0 ≤ formTotal Md S u z :=
  Finset.sum_nonneg fun _ _ => hN.isSeminorm_base.nonneg _ _
theorem target_curlKernelSource_le (h : PotentialSetting S V Cs r C) (hK : 0 ≤ K) (hN : CellNormFamily S Md Lf Sr σ K)
    (hz : z ∈ S) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (y : F.Cell) :
    Lf (curlKernelSource (Cs / (cellSideLength F : ℝ)) S V z u) y ≤
      K * (curlTotal Sr S V u z + 24 * Cs * K * formTotal Md S u z) := by
  classical
  have hκ := h.coldnessRatio_nonneg
  have hNp := h.cellSideLength_pos
  refine (hN.kernel_le z hz _ y).trans (mul_le_mul_of_nonneg_left ?_ hK)
  have hx : ∀ x, Sr (restrictToPatch S z (restrictToPatch S z (curlSource (Cs / (cellSideLength F : ℝ)) S V u))) x ≤
      Sr (curlNorm S V u) x + 24 * Cs * K * Md (PatchDifferences.formNormOn S (toQuaternionForm u)) x := by
    intro x
    have h1 : Sr (restrictToPatch S z (restrictToPatch S z (curlSource (Cs / (cellSideLength F : ℝ)) S V u))) x ≤
        Sr (fun t => curlNorm S V u t + 24 * (Cs / (cellSideLength F : ℝ)) *
          PatchDifferences.formNormOn S (toQuaternionForm u) t) x := by
      refine hN.isSeminorm_source.mono_abs _ _ _ fun t _ => ?_
      have h0 := curlSource_nonneg (S := S) (V := V) hκ u t
      have h2 := restrictToPatch_nonneg (S := S) (z := z) (curlSource_nonneg (S := S) (V := V) hκ u) t
      rw [abs_of_nonneg (restrictToPatch_nonneg (restrictToPatch_nonneg (curlSource_nonneg hκ u)) t),
        show curlNorm S V u t + 24 * (Cs / (cellSideLength F : ℝ)) *
          PatchDifferences.formNormOn S (toQuaternionForm u) t =
          curlSource (Cs / (cellSideLength F : ℝ)) S V u t from rfl,
        abs_of_nonneg h0]
      exact (restrictToPatch_le (restrictToPatch_nonneg (curlSource_nonneg hκ u)) t).trans
        (restrictToPatch_le (curlSource_nonneg hκ u) t)
    refine h1.trans ((hN.isSeminorm_source.add_le _ _ x).trans (add_le_add le_rfl ?_))
    rw [hN.isSeminorm_source.smul, abs_of_nonneg (by positivity : 0 ≤ 24 * (Cs / (cellSideLength F : ℝ)))]
    have h3 := hN.source_le (PatchDifferences.formNormOn S (toQuaternionForm u)) x
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 24 * (Cs / (cellSideLength F : ℝ)))
    refine h4.trans (le_of_eq ?_)
    field_simp
  calc _ ≤ ∑ x ∈ cellBall S z 20, (Sr (curlNorm S V u) x +
        24 * Cs * K * Md (PatchDifferences.formNormOn S (toQuaternionForm u)) x) :=
        Finset.sum_le_sum fun x _ => hx x
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
def stepConstant (K C : ℝ) : ℝ := 8 * (1 + 8 * K * 81) + 6912 * C * 41 ^ 4 * K * (1 + 24 * K)
theorem stepConstant_nonneg (hK : 0 ≤ K) (hC : 0 ≤ C) : 0 ≤ stepConstant K C := by
  unfold stepConstant
  positivity
theorem sum_base_stepNorms_le {R : Lattice4 → Lattice4 → UnitQuaternion} (h : PotentialSetting S V Cs r C)
    (hF : IsPatchFrame S V z R Cs r)
    {H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {G : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hk : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H G C)
    (hK : 0 ≤ K) (hN : CellNormFamily S Md Lf Sr σ K) (hz : z ∈ S) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) :
    ∑ x ∈ cellBall S z 20,
        Md (stepNorms (patchDomain S z) S z (localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u))) x ≤
      stepConstant K C * (curlTotal Sr S V u z + formTotal Md S u z) := by
  classical
  have hκ := h.coldnessRatio_nonneg
  have hC := h.kernelConst_nonneg
  obtain ⟨κ, hκd⟩ : ∃ κ, κ = Cs / (cellSideLength F : ℝ) := ⟨_, rfl⟩
  rw [← hκd] at hκ
  have hf0 : ∀ t, 0 ≤ restrictToPatch S z (PatchDifferences.formNormOn S (toQuaternionForm u)) t :=
    restrictToPatch_nonneg (zero_le_formNormOn _)
  have hx : ∀ x, Md (stepNorms (patchDomain S z) S z
      (localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u))) x ≤
      8 * Md (neighbourSum S z (restrictToPatch S z (PatchDifferences.formNormOn S (toQuaternionForm u)))) x +
        6912 * C * Md (curlKernelSource κ S V z u) x := by
    intro x
    have h1 : Md (stepNorms (patchDomain S z) S z
        (localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u))) x ≤
        Md (fun t => 8 * neighbourSum S z (restrictToPatch S z (PatchDifferences.formNormOn S (toQuaternionForm u))) t +
          6912 * C * curlKernelSource κ S V z u t) x := by
      refine hN.isSeminorm_base.mono_abs _ _ _ fun t _ => ?_
      have n0 := neighbourSum_nonneg (S := S) (z := z) hf0 t
      have c0 := curlKernelSource_nonneg (S := S) (V := V) (z := z) hκ u t
      rw [abs_of_nonneg (stepNorms_nonneg _ _ t),
        abs_of_nonneg (add_nonneg (mul_nonneg (by norm_num) n0) (mul_nonneg (by positivity) c0))]
      have := stepNorms_localPotential_le h hF hk u t
      rwa [← hκd] at this
    refine h1.trans ((hN.isSeminorm_base.add_le _ _ x).trans (add_le_add ?_ ?_))
    · rw [hN.isSeminorm_base.smul, abs_of_nonneg (by norm_num)]
    · rw [hN.isSeminorm_base.smul, abs_of_nonneg (by positivity)]
  have t1 := sum_base_neighbourSum_le h hK hN hf0 (z := z) (fun t ht => restrictToPatch_of_not_mem ht)
  have t2 : ∑ y ∈ cellBall S z 20, Md (restrictToPatch S z (PatchDifferences.formNormOn S (toQuaternionForm u))) y ≤
      formTotal Md S u z := by
    refine Finset.sum_le_sum fun y _ => hN.isSeminorm_base.mono_abs _ _ _ fun t _ => ?_
    rw [abs_of_nonneg (hf0 t), abs_of_nonneg (zero_le_formNormOn _ t)]
    exact restrictToPatch_le (zero_le_formNormOn _) t
  set M1 := curlTotal Sr S V u z with hM1
  set M2 := formTotal Md S u z with hM2
  have hM10 : 0 ≤ M1 := curlTotal_nonneg hN u z
  have hM20 : 0 ≤ M2 := formTotal_nonneg hN u z
  have t3 : ∑ y ∈ cellBall S z 20, Md (curlKernelSource κ S V z u) y ≤ 41 ^ 4 * (K * (M1 + 24 * K * M2)) := by
    have hb : ∀ y, Md (curlKernelSource κ S V z u) y ≤ K * (M1 + 24 * K * M2) := by
      intro y
      refine (hN.base_le_target _ y).trans ?_
      have := target_curlKernelSource_le h hK hN hz u y
      rw [← hκd] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hK)
      have h5 : 24 * Cs * K * M2 ≤ 24 * 1 * K * M2 := by
        have := h.coldness_le_one
        gcongr
      linarith
    calc _ ≤ ∑ _y ∈ cellBall S z 20, K * (M1 + 24 * K * M2) := Finset.sum_le_sum fun y _ => hb y
      _ = ((cellBall S z 20).card : ℝ) * (K * (M1 + 24 * K * M2)) := by simp
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have := card_cellBall_le (S := S) h.ambient z 20
          norm_num at this ⊢
          exact this
  have hK1 : 0 ≤ 1 + 8 * K * 81 := by positivity
  calc _ ≤ ∑ x ∈ cellBall S z 20,
        (8 * Md (neighbourSum S z (restrictToPatch S z (PatchDifferences.formNormOn S (toQuaternionForm u)))) x +
          6912 * C * Md (curlKernelSource κ S V z u) x) := Finset.sum_le_sum fun x _ => hx x
    _ = 8 * ∑ x ∈ cellBall S z 20,
          Md (neighbourSum S z (restrictToPatch S z (PatchDifferences.formNormOn S (toQuaternionForm u)))) x +
        6912 * C * ∑ x ∈ cellBall S z 20, Md (curlKernelSource κ S V z u) x := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 8 * ((1 + 8 * K * 81) * M2) + 6912 * C * (41 ^ 4 * (K * (M1 + 24 * K * M2))) := by
        refine add_le_add (mul_le_mul_of_nonneg_left (t1.trans (mul_le_mul_of_nonneg_left t2 hK1)) (by norm_num))
          (mul_le_mul_of_nonneg_left t3 (by positivity))
    _ ≤ _ := by
        have e : stepConstant K C * (M1 + M2) =
            8 * ((1 + 8 * K * 81) * M2) + 6912 * C * (41 ^ 4 * (K * (M1 + 24 * K * M2))) +
            (8 * (1 + 8 * K * 81) * M1 + 6912 * C * 41 ^ 4 * K * (24 * K * M1 + M2)) := by
          unfold stepConstant
          ring
        rw [e]
        have : 0 ≤ 8 * (1 + 8 * K * 81) * M1 + 6912 * C * 41 ^ 4 * K * (24 * K * M1 + M2) := by positivity
        linarith
def potentialConstant (K C : ℝ) : ℝ := C * (K ^ 2 + K ^ 5) * stepConstant K C
theorem target_potentialNorm_le {R : Lattice4 → Lattice4 → UnitQuaternion} (h : PotentialSetting S V Cs r C)
    (hF : IsPatchFrame S V z R Cs r)
    {H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {G : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hk : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H G C)
    (hK : 0 ≤ K) (hN : CellNormFamily S Md Lf Sr σ K) (hz : z ∈ S) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    {y : F.Cell} (hy : cellSupDist y z ≤ 22) :
    Lf (potentialNorm S V z u) y ≤
      (cellSideLength F : ℝ) * (potentialConstant K C * (curlTotal Sr S V u z + formTotal Md S u z)) := by
  classical
  have hC := h.kernelConst_nonneg
  have hNp := h.cellSideLength_pos
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = patchCubicKernel S z (stepNorms (patchDomain S z) S z ξ) := ⟨_, rfl⟩
  have hW0 : ∀ t, 0 ≤ W t := fun t => by
    rw [hW]
    exact patchCubicKernel_nonneg (stepNorms_nonneg _ _) t
  obtain ⟨E, hE⟩ : ∃ E, E = stepConstant K C * (curlTotal Sr S V u z + formTotal Md S u z) := ⟨_, rfl⟩
  have hT : ∑ x ∈ cellBall S z 20, Md (stepNorms (patchDomain S z) S z ξ) x ≤ E := by
    rw [hE, hξ]
    exact sum_base_stepNorms_le h hF hk hK hN hz u
  have hWn : ∀ y', Lf W y' ≤ K * (K * (cellSideLength F : ℝ) * E) := by
    intro y'
    rw [hW]
    refine (hN.kernel_le z hz _ y').trans (mul_le_mul_of_nonneg_left ?_ hK)
    have h1 : ∀ x, Sr (restrictToPatch S z (stepNorms (patchDomain S z) S z ξ)) x ≤
        K * (cellSideLength F : ℝ) * Md (stepNorms (patchDomain S z) S z ξ) x := by
      intro x
      refine (hN.source_le _ x).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      refine hN.isSeminorm_base.mono_abs _ _ _ fun t _ => ?_
      rw [abs_of_nonneg (restrictToPatch_nonneg (stepNorms_nonneg _ _) t), abs_of_nonneg (stepNorms_nonneg _ _ t)]
      exact restrictToPatch_le (stepNorms_nonneg _ _) t
    calc _ ≤ ∑ x ∈ cellBall S z 20, K * (cellSideLength F : ℝ) * Md (stepNorms (patchDomain S z) S z ξ) x :=
          Finset.sum_le_sum fun x _ => h1 x
      _ = K * (cellSideLength F : ℝ) * ∑ x ∈ cellBall S z 20, Md (stepNorms (patchDomain S z) S z ξ) x := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by positivity)
  obtain ⟨κ0, hκ0⟩ : ∃ κ0, κ0 = (1 / (cellSideLength F : ℝ) ^ 4) * ∑ x ∈ cellOffsets F, W (patchSite S z x) :=
    ⟨_, rfl⟩
  have hκ00 : 0 ≤ κ0 := by
    rw [hκ0]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => hW0 _)
  have hpt : ∀ t, potentialNorm S V z u t ≤ C * W t + C * κ0 * 1 := by
    intro t
    by_cases ht : t ∈ patchSiteSet S z
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
      rw [potentialNorm, restrictToPatch_of_mem ht, h.patchChart_patchSite ha]
      have := norm_sub_cellMean_le h hk hz ξ ha
      rw [← hW, ← hκ0] at this
      rw [mul_one]
      have e : centredPotential S V z u a = ξ a - cellMean F ξ := by
        rw [hξ]
        rfl
      rw [e]
      exact this
    · rw [potentialNorm, restrictToPatch_of_not_mem ht]
      have := hW0 t
      positivity
  have h1 : Lf (potentialNorm S V z u) y ≤ Lf (fun t => C * W t + C * κ0 * 1) y := by
    refine hN.isSeminorm_target.mono_abs _ _ _ fun t _ => ?_
    have h0 := hW0 t
    rw [abs_of_nonneg (potentialNorm_nonneg u t), abs_of_nonneg (by positivity)]
    exact hpt t
  have h2 : Lf (fun t => C * W t + C * κ0 * 1) y ≤ C * Lf W y + C * κ0 * Lf (fun _ => 1) y := by
    refine (hN.isSeminorm_target.add_le _ _ y).trans (add_le_add ?_ ?_)
    · rw [hN.isSeminorm_target.smul, abs_of_nonneg hC]
    · rw [hN.isSeminorm_target.smul, abs_of_nonneg (by positivity)]
  have hs := hN.scale_le_of_near y z hy
  have hcm : σ z * κ0 ≤ K * Md W z / (cellSideLength F : ℝ) := by
    rw [hκ0, sum_cellOffsets_patchSite h.odd_side (h.closedOrthant_cases z)]
    exact scale_mul_cellMean_le hN h.ambient h.odd_side hz W hW0
  have hmw : Md W z ≤ K * (K * (cellSideLength F : ℝ) * E) := (hN.base_le_target W z).trans (hWn z)
  have h3 : σ y * κ0 ≤ K ^ 4 * E := by
    have a1 : σ y * κ0 ≤ K * σ z * κ0 := mul_le_mul_of_nonneg_right hs hκ00
    have a2 : K * (σ z * κ0) ≤ K * (K * Md W z / (cellSideLength F : ℝ)) := mul_le_mul_of_nonneg_left hcm hK
    have a3 : K * (K * Md W z / (cellSideLength F : ℝ)) ≤
        K * (K * (K * (K * (cellSideLength F : ℝ) * E)) / (cellSideLength F : ℝ)) := by
      gcongr
    have a4 : K * (K * (K * (K * (cellSideLength F : ℝ) * E)) / (cellSideLength F : ℝ)) = K ^ 4 * E := by
      field_simp
    linarith
  have h4 : Lf (fun _ => 1) y ≤ K * (cellSideLength F : ℝ) * σ y := hN.const_le y
  have h5 : C * κ0 * Lf (fun _ => 1) y ≤ C * (cellSideLength F : ℝ) * K * K ^ 4 * E := by
    have b1 : C * κ0 * Lf (fun _ => 1) y ≤ C * κ0 * (K * (cellSideLength F : ℝ) * σ y) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have b2 : C * κ0 * (K * (cellSideLength F : ℝ) * σ y) = C * (cellSideLength F : ℝ) * K * (σ y * κ0) := by ring
    have b3 : C * (cellSideLength F : ℝ) * K * (σ y * κ0) ≤ C * (cellSideLength F : ℝ) * K * (K ^ 4 * E) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    calc _ ≤ _ := b1
      _ = _ := b2
      _ ≤ _ := b3
      _ = _ := by ring
  have h6 : C * Lf W y ≤ C * (K * (K * (cellSideLength F : ℝ) * E)) := mul_le_mul_of_nonneg_left (hWn y) hC
  have e : (cellSideLength F : ℝ) * (potentialConstant K C * (curlTotal Sr S V u z + formTotal Md S u z)) =
      C * (K * (K * (cellSideLength F : ℝ) * E)) + C * (cellSideLength F : ℝ) * K * K ^ 4 * E := by
    rw [hE]
    unfold potentialConstant
    ring
  rw [e]
  linarith
def defectConstant (K C : ℝ) : ℝ := 1728 * C * K * (1 + 24 * K) + 2 * potentialConstant K C
theorem potentialConstant_nonneg (hK : 0 ≤ K) (hC : 0 ≤ C) : 0 ≤ potentialConstant K C :=
  mul_nonneg (mul_nonneg hC (by positivity)) (stepConstant_nonneg hK hC)
theorem defectConstant_nonneg (hK : 0 ≤ K) (hC : 0 ≤ C) : 0 ≤ defectConstant K C := by
  have := potentialConstant_nonneg hK hC
  unfold defectConstant
  positivity
theorem target_defectBound_le {R : Lattice4 → Lattice4 → UnitQuaternion} (h : PotentialSetting S V Cs r C)
    (hF : IsPatchFrame S V z R Cs r)
    {H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {G : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hk : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H G C)
    (hK : 0 ≤ K) (hN : CellNormFamily S Md Lf Sr σ K) (hz : z ∈ S) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    {y : F.Cell} (hy : cellSupDist y z ≤ 22) :
    Lf (defectBound (Cs / (cellSideLength F : ℝ)) C S V z u) y ≤
      defectConstant K C * (curlTotal Sr S V u z + Cs * formTotal Md S u z) := by
  have hC := h.kernelConst_nonneg
  have hNp := h.cellSideLength_pos
  have hc0 := h.coldness_nonneg
  have hc1 := h.coldness_le_one
  have h1 := target_curlKernelSource_le h hK hN hz u y
  have h2 := target_potentialNorm_le h hF hk hK hN hz u hy
  set M1 := curlTotal Sr S V u z with hM1
  set M2 := formTotal Md S u z with hM2
  have hM10 : 0 ≤ M1 := curlTotal_nonneg hN u z
  have hM20 : 0 ≤ M2 := formTotal_nonneg hN u z
  have h3 := hN.isSeminorm_target.add_le
    (fun t => 1728 * C * curlKernelSource (Cs / (cellSideLength F : ℝ)) S V z u t)
    (fun t => 2 * (Cs / (cellSideLength F : ℝ)) * potentialNorm S V z u t) y
  rw [hN.isSeminorm_target.smul, hN.isSeminorm_target.smul, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)] at h3
  have h4 : 1728 * C * Lf (curlKernelSource (Cs / (cellSideLength F : ℝ)) S V z u) y ≤
      1728 * C * (K * (M1 + 24 * Cs * K * M2)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h5 : 2 * (Cs / (cellSideLength F : ℝ)) * Lf (potentialNorm S V z u) y ≤
      2 * (Cs / (cellSideLength F : ℝ)) * ((cellSideLength F : ℝ) * (potentialConstant K C * (M1 + M2))) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e5 : 2 * (Cs / (cellSideLength F : ℝ)) * ((cellSideLength F : ℝ) * (potentialConstant K C * (M1 + M2))) =
      2 * Cs * (potentialConstant K C * (M1 + M2)) := by
    field_simp
  rw [e5] at h5
  have hp := potentialConstant_nonneg hK hC
  have h6 : Cs * M1 ≤ M1 := mul_le_of_le_one_left hM10 hc1
  have h7 : Cs * (potentialConstant K C * M1) ≤ potentialConstant K C * M1 := by
    have := mul_le_mul_of_nonneg_left h6 hp
    nlinarith
  have e : defectConstant K C * (M1 + Cs * M2) = 1728 * C * (K * (M1 + 24 * Cs * K * M2)) +
      2 * Cs * (potentialConstant K C * (M1 + M2)) + (1728 * C * K * 24 * K * M1 + 1728 * C * K * Cs * M2 +
      2 * (potentialConstant K C * M1 - Cs * (potentialConstant K C * M1))) := by
    unfold defectConstant
    ring
  rw [e]
  have h8 : 0 ≤ 1728 * C * K * 24 * K * M1 + 1728 * C * K * Cs * M2 +
      2 * (potentialConstant K C * M1 - Cs * (potentialConstant K C * M1)) := by
    have t1 : 0 ≤ 1728 * C * K * 24 * K * M1 := by positivity
    have t2 : 0 ≤ 1728 * C * K * Cs * M2 := by positivity
    linarith
  show Lf (fun t => 1728 * C * curlKernelSource (Cs / (cellSideLength F : ℝ)) S V z u t +
    2 * (Cs / (cellSideLength F : ℝ)) * potentialNorm S V z u t) y ≤ _
  linarith
end Norms
end PatchPotentials
end YangMills.Construction
end
