import YangMills.Construction.ColdChainAtEveryLevel.TermsAtTheTop
import YangMills.Construction.ColdChainAtEveryLevel.TermsOfThePlaquettes
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.CellSums
variable {F : BlockAverages.BlockFrame}
theorem enclosingCell_near_le_one (hadm : BlockAverages.IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (y : F.Cell) {h g : LatticeFractionalIntegration.Lattice4}
    (hh : h ∈ BlockAverages.centredCube (F.blockSide ^ (F.top - 0))) (hg : ∀ l, |g l| ≤ 1) :
    BlockAverages.cellSupDist (BlockAverages.enclosingCell (BlockAverages.cellCentre 0 y +
      BlockAverages.siteOfCoords 0 (fun l => h l + g l) : F.Site 0)) y ≤ 1 := by
  obtain ⟨K, hK1, hK2, hK3⟩ := BlockLines.odd_pow_eq_two_mul_add_one hodd (F.top - 0)
  set v : LatticeFractionalIntegration.Lattice4 := fun l =>
    if (K : ℤ) < h l + g l then 1 else if h l + g l < -(K : ℤ) then -1 else 0 with hv
  set h₂ : LatticeFractionalIntegration.Lattice4 := fun l =>
    h l + g l - (F.blockSide : ℤ) ^ (F.top - 0) * v l with hh₂
  have e : (BlockAverages.cellCentre 0 y + BlockAverages.siteOfCoords 0 (fun l => h l + g l) : F.Site 0) =
      BlockAverages.cellCentre 0 (y + BlockAverages.siteOfCoords F.top v) + BlockAverages.siteOfCoords 0 h₂ := by
    rw [BlockAverages.cellCentre_add 0 (Nat.zero_le _), add_assoc, ← BlockAverages.siteOfCoords_add]
    congr 2
    funext l
    simp only [Pi.add_apply, hh₂]
    ring
  have hc := (LatticePaths.mem_centredCube_iff _ _).1 hh
  rw [hK2] at hc
  have hcube : h₂ ∈ BlockAverages.centredCube (F.blockSide ^ (F.top - 0)) := by
    refine (LatticePaths.mem_centredCube_iff _ _).2 fun l => ?_
    rw [hK2]
    have h1 := hc l
    have h2 := abs_le.1 (hg l)
    simp only [hh₂, hv, hK3]
    split_ifs <;> constructor <;> omega
  rw [e, BlockLines.enclosingCell_cellCentre_add hodd _ _ hcube]
  refine BlockAverages.cellSupDist_add_le hadm y (by norm_num) fun l => ?_
  simp only [hv]
  split_ifs <;> simp
theorem mem_innerPlaquettes_cellBall_of_mem_plaquettesOver (hadm : BlockAverages.IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (S : Finset F.Cell) (z : F.Cell)
    {q : F.Site 0 × Fin 4 × Fin 4} (hq : q ∈ BlockAverages.plaquettesOver S {z} 0) :
    q ∈ BlockAverages.innerPlaquettes (BlockAverages.cellBall S z 1) 0 := by
  classical
  obtain ⟨hqS, hcell⟩ := Finset.mem_filter.1 hq
  have hcz : BlockAverages.enclosingCell q.1 = z := Finset.mem_singleton.1 hcell
  obtain ⟨hp, hμν, hcor⟩ := Finset.mem_filter.1 hqS
  have hx : q.1 ∈ BlockAverages.sitesOfCells S 0 := (Finset.mem_product.1 hp).1
  obtain ⟨y, hy, h, hh, hxe⟩ := BlockAverages.mem_sitesOfCells.1 hx
  have hyz : y = z := by
    rw [← hcz, hxe, BlockLines.enclosingCell_cellCentre_add hodd y h hh]
  subst hyz
  have near : ∀ g : LatticeFractionalIntegration.Lattice4, (∀ l, |g l| ≤ 1) →
      q.1 + BlockAverages.siteOfCoords 0 g ∈ BlockAverages.sitesOfCells S 0 →
      q.1 + BlockAverages.siteOfCoords 0 g ∈ BlockAverages.sitesOfCells (BlockAverages.cellBall S y 1) 0 := by
    intro g hg hs
    refine BlockLines.mem_sitesOfCells_of_enclosingCell_mem hodd hs
      (Finset.mem_filter.2 ⟨BlockLines.enclosingCell_mem hodd hs, ?_⟩)
    have e : q.1 + BlockAverages.siteOfCoords 0 g =
        (BlockAverages.cellCentre 0 y + BlockAverages.siteOfCoords 0 (fun l => h l + g l) : F.Site 0) := by
      rw [hxe, add_assoc, ← BlockAverages.siteOfCoords_add]
      rfl
    rw [e, BlockLines.cellSupDist_comm]
    exact enclosingCell_near_le_one hadm hodd y hh hg
  have hz0 : ∀ l, |(0 : LatticeFractionalIntegration.Lattice4) l| ≤ 1 := fun l => by simp
  have hzμ : ∀ (μ l : Fin 4), |LatticeFractionalIntegration.basisVector μ l| ≤ 1 := by
    intro μ l
    by_cases e : l = μ
    · subst e
      simp [LatticeFractionalIntegration.basisVector]
    · simp [LatticeFractionalIntegration.basisVector, Pi.single_eq_of_ne e]
  have hz2 : ∀ l, |(LatticeFractionalIntegration.basisVector q.2.1 +
      LatticeFractionalIntegration.basisVector q.2.2) l| ≤ 1 := by
    intro l
    have hne : q.2.1 ≠ q.2.2 := ne_of_lt hμν
    simp only [Pi.add_apply]
    by_cases e1 : l = q.2.1
    · have e2 : l ≠ q.2.2 := fun e => hne (e1 ▸ e)
      simp [LatticeFractionalIntegration.basisVector, e1, Pi.single_eq_of_ne (e1 ▸ e2)]
    · by_cases e2 : l = q.2.2
      · simp [LatticeFractionalIntegration.basisVector, e2, Pi.single_eq_of_ne (e2 ▸ e1)]
      · simp [LatticeFractionalIntegration.basisVector, Pi.single_eq_of_ne e1, Pi.single_eq_of_ne e2]
  have c0 : q.1 ∈ BlockAverages.plaquetteCorners q := by simp [BlockAverages.plaquetteCorners]
  have c1 : q.1 + BlockAverages.unitStep 0 q.2.1 ∈ BlockAverages.plaquetteCorners q := by
    simp [BlockAverages.plaquetteCorners]
  have c2 : q.1 + BlockAverages.unitStep 0 q.2.2 ∈ BlockAverages.plaquetteCorners q := by
    simp [BlockAverages.plaquetteCorners]
  have c3 : q.1 + BlockAverages.unitStep 0 q.2.1 + BlockAverages.unitStep 0 q.2.2 ∈
      BlockAverages.plaquetteCorners q := by
    simp [BlockAverages.plaquetteCorners]
  have e0 : q.1 + BlockAverages.siteOfCoords 0 (0 : LatticeFractionalIntegration.Lattice4) = q.1 := by
    have : BlockAverages.siteOfCoords (F := F) 0 (0 : LatticeFractionalIntegration.Lattice4) = 0 := by
      funext i
      simp [BlockAverages.siteOfCoords]
    rw [this, add_zero]
  have e3 : q.1 + BlockAverages.unitStep 0 q.2.1 + BlockAverages.unitStep 0 q.2.2 =
      q.1 + BlockAverages.siteOfCoords 0 (LatticeFractionalIntegration.basisVector q.2.1 +
        LatticeFractionalIntegration.basisVector q.2.2) := by
    rw [BlockAverages.unitStep_eq, BlockAverages.unitStep_eq, add_assoc, ← BlockAverages.siteOfCoords_add]
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨?_, (Finset.mem_product.1 hp).2⟩, hμν, ?_⟩
  · have := near 0 hz0 (by rw [e0]; exact hcor c0)
    rwa [e0] at this
  · intro c hc
    simp only [BlockAverages.plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · have := near 0 hz0 (by rw [e0]; exact hcor c0)
      rwa [e0] at this
    · exact near _ (hzμ _) (hcor c1)
    · exact near _ (hzμ _) (hcor c2)
    · rw [e3]
      exact near _ hz2 (by rw [← e3]; exact hcor c3)
def cellSecondDiffError (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top)
    (W₁ W₂ W₃ : BlockAverages.ChainChart F) (z : F.Cell) : ℝ :=
  ∑ q ∈ BlockAverages.plaquettesOver S {z} 0, |PlaquetteTerms.plaquetteAction R W₃ q -
      PlaquetteTerms.plaquetteAction R W₁ q - PlaquetteTerms.plaquetteAction R W₂ q +
      PlaquetteTerms.plaquetteAction R (BlockAverages.zeroChart F) q -
      inner ℝ (BlockAverages.linearizedCurl (R 0) W₁.fine q) (BlockAverages.linearizedCurl (R 0) W₂.fine q)| +
    a * ∑ j ∈ Finset.range F.depth, ∑ c ∈ BlockAverages.bondsOver S {z} (j + 1),
      |BondSecondDifference.bondEnergy R W₃ V j c - BondSecondDifference.bondEnergy R W₁ V j c -
        BondSecondDifference.bondEnergy R W₂ V j c +
        BondSecondDifference.bondEnergy R (BlockAverages.zeroChart F) V j c -
        inner ℝ (W₁.coarse j c.1 c.2 : ℍ[ℝ]) (W₂.coarse j c.1 c.2 : ℍ[ℝ])| +
    a * ∑ c ∈ BlockAverages.bondsOver S {z} (F.depth + 1),
      |BondSecondDifference.bondEnergy R W₃ V F.depth c - BondSecondDifference.bondEnergy R W₁ V F.depth c -
        BondSecondDifference.bondEnergy R W₂ V F.depth c +
        BondSecondDifference.bondEnergy R (BlockAverages.zeroChart F) V F.depth c -
        inner ℝ (BlockAverages.linearPart R W₁ (F.depth + 1) c.1 c.2)
          (BlockAverages.linearPart R W₂ (F.depth + 1) c.1 c.2)|
def cellCubicWeight (a : ℝ) (S : Finset F.Cell) (z : F.Cell) : ℝ :=
  ((BlockAverages.plaquettesOver S {z} 0).card : ℝ) * (200000 * 128) +
    a * (∑ j ∈ Finset.range F.depth, ((BlockAverages.bondsOver S {z} (j + 1)).card : ℝ) *
      LowerLevelTerms.lowerCubicConst F.blockSide) +
    a * (((BlockAverages.bondsOver S {z} (F.depth + 1)).card : ℝ) * TopLevelTerms.topCubicConst F.blockSide)
theorem sum_inv_pow_top_sub_le_two (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) :
    ∑ j ∈ Finset.range F.depth, (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) ≤ 2 := by
  have hL2 : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast h2
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) (LevelRecursion.sum_inv_pow_le_two hL2 F.depth)
  have hj' := Finset.mem_range.1 hj
  have h0 : (0 : ℝ) ≤ 1 / (F.blockSide : ℝ) := by positivity
  have h1 : 1 / (F.blockSide : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hn : F.top = F.depth + 1 := rfl
  exact pow_le_pow_of_le_one h0 h1 (by omega)
set_option maxHeartbeats 2000000 in
theorem cellSecondDiffError_le (hadm : BlockAverages.IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) {a : ℝ} (ha : 0 ≤ a) {S : Finset F.Cell}
    {z : F.Cell} {p : F.Site 0} {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {V : F.GaugeField F.top}
    (hV : R F.top = V)
    {W₁ W₂ W₃ : BlockAverages.ChainChart F} {C₀ s T B₁ B₂ G₁ G₂ : ℝ}
    (ref : LowerLevelTerms.ReferenceNear (BlockAverages.cellBall S z 1) R C₀ s)
    (dir : LowerLevelTerms.SmallDirectionTriple (BlockAverages.cellBall S z 1) p θ R W₁ W₂ W₃ C₀ s T B₁ B₂)
    (top : TopLevelTerms.TopDirectionBounds (BlockAverages.cellBall S z 1) p θ R W₁ W₂ T B₁ B₂ G₁ G₂)
    (hcurv : ∀ q ∈ BlockAverages.innerPlaquettes (BlockAverages.cellBall S z 1) 0,
      BlockAverages.plaquetteDefect (R 0) q ≤ C₀ * s * ((1 / (F.blockSide : ℝ)) ^ F.top) ^ 2)
    (hT : 4 * T ≤ 1 / 4000)
    (hu₁ : ∀ b ∈ BlockAverages.innerBonds (BlockAverages.cellBall S z 1) 0, ‖(W₁.fine b.1 b.2 : ℍ[ℝ])‖ ≤ T)
    (hu₂ : ∀ b ∈ BlockAverages.innerBonds (BlockAverages.cellBall S z 1) 0, ‖(W₂.fine b.1 b.2 : ℍ[ℝ])‖ ≤ T)
    (hu₃ : ∀ b ∈ BlockAverages.innerBonds (BlockAverages.cellBall S z 1) 0,
      W₃.fine b.1 b.2 = W₁.fine b.1 b.2 + W₂.fine b.1 b.2)
    (h1 : LevelRecursion.weightedScaleNorm (BlockAverages.cellBall S z 1) p θ 4 0
      (fun x i => ‖(W₁.fine x i : ℍ[ℝ])‖) ≤ B₁)
    (h2' : LevelRecursion.weightedScaleNorm (BlockAverages.cellBall S z 1) p (-θ) 4 0
      (fun x i => ‖(W₂.fine x i : ℍ[ℝ])‖) ≤ B₂) :
    cellSecondDiffError a S R V W₁ W₂ W₃ z ≤
      C₀ * s * ((200000 * 9216 + a * (2 * LowerLevelTerms.lowerMainConst F.blockSide +
        TopLevelTerms.topMainConst F.blockSide)) * (B₁ * B₂)) +
        a * (20 * (HullBounds.hullFactor F.blockSide * 82272) * (G₁ * B₂) +
          2 * TopLevelTerms.topLinearConst F.blockSide * (B₁ * G₂)) +
        cellCubicWeight a S z * T ^ 3 := by
  have hD := BlockLines.card_cellBall_one_le S z
  have hC := dir.C₀_pos
  have hs := dir.s_pos
  have hc₀ : 0 ≤ C₀ * s := by positivity
  have hB₁ := dir.B₁_nonneg
  have hB₂ := dir.B₂_nonneg
  have hlow : 0 ≤ LowerLevelTerms.lowerMainConst F.blockSide := by
    have := LowerLevelTerms.hullFactor_nonneg (F := F) hodd
    have h3 : 0 ≤ LowerLevelTerms.levelSecondConst F.blockSide := by
      unfold LowerLevelTerms.levelSecondConst RealDirections.secondSourceConst
      positivity
    unfold LowerLevelTerms.lowerMainConst
    positivity
  have P := PlaquetteTerms.sum_abs_plaquetteAction_second_diff_le hodd hD hθ (R := R) (W₁ := W₁) (W₂ := W₂)
    (W₃ := W₃) (c₀ := C₀ * s) (T := T) (B₁ := B₁) (B₂ := B₂) (P := BlockAverages.plaquettesOver S {z} 0)
    (fun q hq => mem_innerPlaquettes_cellBall_of_mem_plaquettesOver hadm hodd S z hq) hc₀ hcurv dir.T_nonneg hT
    hu₁ hu₂ hu₃ h1 h2'
  have Lw : ∀ j ∈ Finset.range F.depth, ∑ c ∈ BlockAverages.bondsOver S {z} (j + 1),
      |BondSecondDifference.bondEnergy R W₃ V j c - BondSecondDifference.bondEnergy R W₁ V j c -
        BondSecondDifference.bondEnergy R W₂ V j c +
        BondSecondDifference.bondEnergy R (BlockAverages.zeroChart F) V j c -
        inner ℝ (W₁.coarse j c.1 c.2 : ℍ[ℝ]) (W₂.coarse j c.1 c.2 : ℍ[ℝ])| ≤
      C₀ * s * (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) *
          (LowerLevelTerms.lowerMainConst F.blockSide * (B₁ * B₂)) +
        ((BlockAverages.bondsOver S {z} (j + 1)).card : ℝ) *
          (LowerLevelTerms.lowerCubicConst F.blockSide * T ^ 3) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have hjn : j + 1 < F.top := by
      have : F.top = F.depth + 1 := rfl
      omega
    exact LowerLevelTerms.sum_abs_bondSecondDiff_le hodd hD hθ V ref dir hjn fun c hc =>
      BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hadm hodd S z (by omega) hc
  have Tp := TopLevelTerms.sum_abs_bondEnergy_second_diff_top_le hodd hD hθ V hV ref dir top
    (Bj := BlockAverages.bondsOver S {z} (F.depth + 1))
    fun c hc => BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hadm hodd S z
      (TopLevelTerms.depth_succ_le_top F) hc
  have sumL := Finset.sum_le_sum Lw
  rw [Finset.sum_add_distrib] at sumL
  have hs2 := sum_inv_pow_top_sub_le_two hodd h2
  have eL : ∑ j ∈ Finset.range F.depth, C₀ * s * (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) *
        (LowerLevelTerms.lowerMainConst F.blockSide * (B₁ * B₂)) =
      C₀ * s * (LowerLevelTerms.lowerMainConst F.blockSide * (B₁ * B₂)) *
        ∑ j ∈ Finset.range F.depth, (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have eC : ∑ j ∈ Finset.range F.depth, ((BlockAverages.bondsOver S {z} (j + 1)).card : ℝ) *
        (LowerLevelTerms.lowerCubicConst F.blockSide * T ^ 3) =
      (∑ j ∈ Finset.range F.depth, ((BlockAverages.bondsOver S {z} (j + 1)).card : ℝ) *
        LowerLevelTerms.lowerCubicConst F.blockSide) * T ^ 3 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [eL, eC] at sumL
  have hz : C₀ * s * (LowerLevelTerms.lowerMainConst F.blockSide * (B₁ * B₂)) *
        ∑ j ∈ Finset.range F.depth, (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) ≤
      C₀ * s * (LowerLevelTerms.lowerMainConst F.blockSide * (B₁ * B₂)) * 2 :=
    mul_le_mul_of_nonneg_left hs2 (by positivity)
  have aL := mul_le_mul_of_nonneg_left sumL ha
  have aT := mul_le_mul_of_nonneg_left Tp ha
  have aZ := mul_le_mul_of_nonneg_left hz ha
  simp only [cellSecondDiffError, cellCubicWeight]
  refine (add_le_add (add_le_add P aL) aT).trans ?_
  have e9 : a * (C₀ * s * (LowerLevelTerms.lowerMainConst F.blockSide * (B₁ * B₂)) * 2) =
      2 * a * (C₀ * s * (LowerLevelTerms.lowerMainConst F.blockSide * (B₁ * B₂))) := by ring
  rw [e9] at aZ
  linarith
end YangMills.Construction.CellSums
end
