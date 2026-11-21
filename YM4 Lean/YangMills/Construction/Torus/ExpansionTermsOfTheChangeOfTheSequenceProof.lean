import YangMills.Construction.Torus.ExpansionTermsOfTheChangeOfTheSequence
import YangMills.Construction.Torus.LevelsNearACubeProof
import YangMills.Construction.Torus.PlaquetteTermsOfTheChangeOfTheSequenceProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace GeneralTorus
namespace ChangeBondSum
open SeparatedSequences GreenBounds
abbrev decayRate (L : ℕ) : ℝ := (chosen L).rate
abbrev entryConstant (L : ℕ) : ℝ := compressedEntryConstant 4 L (chosen L).rate (chosen L).bound
theorem levelSpacing_pos (D : ScaleData) (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem levelSpacing_mono (D : ScaleData) {m n : ℕ} (h : m ≤ n) :
    D.levelSpacing m ≤ D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.SupDistBound.levelSpacing_mono <;> assumption
variable {S : ℝ}
theorem torusSupNorm_sub_le_add (x y z : Torus4 S) :
    torusSupNorm (x - z) ≤ torusSupNorm (x - y) + torusSupNorm (y - z) := by apply _root_.YangMills.Construction.GeneralTorus.ChainChangeCurl.torusSupNorm_sub_le <;> assumption
theorem self_mem_supCube {s : ℝ} (hs : 0 ≤ s) (y : Torus4 S) : y ∈ supCube s y := by apply _root_.YangMills.Construction.GeneralTorus.CubePartitions.self_mem_supCube <;> assumption
theorem src_mem_bondSupport (D : ScaleData) {n : ℕ} (c : D.PosBond n) :
    (c.1.src : D.Space) ∈ ScaleData.bondSupport c :=
  Or.inl (self_mem_supCube (levelSpacing_pos D n).le _)
theorem tgt_mem_bondSupport (D : ScaleData) {n : ℕ} (c : D.PosBond n) :
    (c.1.tgt : D.Space) ∈ ScaleData.bondSupport c :=
  Or.inr (self_mem_supCube (levelSpacing_pos D n).le _)
theorem torusSupNorm_sub_endpoint_le (D : ScaleData) {n : ℕ} (c : D.PosBond n) {x y : D.Space}
    (hx : x ∈ ScaleData.bondSupport c)
    (hy : y = (c.1.src : D.Space) ∨ y = (c.1.tgt : D.Space)) :
    torusSupNorm (x - y) ≤ 3 / 2 * D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.CubeLevels.torusSupNorm_sub_end_le <;> assumption
theorem set_antitone {D : ScaleData} (B : SeparatedChain D) {m n : ℕ} (hmn : m ≤ n)
    (hn : n ≤ D.lastLevel) : B.set n ⊆ B.set m := by apply _root_.YangMills.Construction.GeneralTorus.CoarseTestFormMeansAux.set_antitone <;> assumption
theorem localSpacing_eq_of_mem_shellSites (hCells : SeparatedChainStructure) {D : ScaleData}
    (B : SeparatedChain D) {n : ℕ} (hn : n ≤ D.lastLevel) {y : D.Space}
    (hy : y ∈ B.shellSites n) : B.localSpacing y = D.levelSpacing n := by
  have hl := (hCells D B).2.1
  have hmem : y ∈ B.set n := by
    have h := hy
    rw [(hl n hn).2.2.1] at h
    exact h.2.1
  have hinf : sInf {m | y ∈ B.shellSites m} = n := by
    apply le_antisymm (Nat.sInf_le hy)
    refine le_csInf ⟨n, hy⟩ ?_
    intro m hm
    by_contra hlt
    have hm' : y ∈ B.shellSites m := hm
    rw [(hl m (by omega)).2.2.1] at hm'
    exact hm'.2.2 (set_antitone B (by omega) hn hmem)
  unfold SeparatedChain.localSpacing
  rw [hinf]
theorem coarseBond_level_le {W : GaugeSetting} (c : W.CoarseBond) : (c.1 : ℕ) ≤ W.data.lastLevel :=
  Nat.lt_succ_iff.mp c.1.2
theorem coarseAnchor_mem_shellSites (hRows : CoarseBondFormsAndMatricesHold) {W : GaugeSetting}
    (c : W.CoarseBond) : GaugeSetting.coarseAnchor c ∈ W.chain.shellSites c.1 :=
  ((hRows W).1.1 c).2
theorem coarseAnchor_mem_shellSitesUnion (hRows : CoarseBondFormsAndMatricesHold)
    {W : GaugeSetting} (c : W.CoarseBond) :
    GaugeSetting.coarseAnchor c ∈ W.chain.shellSitesUnion := by
  simp only [SeparatedChain.shellSitesUnion, mem_iUnion]
  exact ⟨c.1, by simpa using coarseBond_level_le c, coarseAnchor_mem_shellSites hRows c⟩
theorem localSpacing_coarseAnchor (hRows : CoarseBondFormsAndMatricesHold)
    (hCells : SeparatedChainStructure) {W : GaugeSetting} (c : W.CoarseBond) :
    W.chain.localSpacing (GaugeSetting.coarseAnchor c) = GaugeSetting.coarseSpacing c :=
  localSpacing_eq_of_mem_shellSites hCells W.chain (coarseBond_level_le c)
    (coarseAnchor_mem_shellSites hRows c)
theorem torusSupNorm_sub_coarseAnchor_le (hRows : CoarseBondFormsAndMatricesHold)
    {W : GaugeSetting} (c : W.CoarseBond) {x : W.data.Space}
    (hx : x ∈ ScaleData.bondSupport c.2.1) :
    torusSupNorm (x - GaugeSetting.coarseAnchor c) ≤ 3 / 2 * GaugeSetting.coarseSpacing c :=
  torusSupNorm_sub_endpoint_le W.data c.2.1 hx ((hRows W).1.1 c).1
theorem column_chain_le {Cb X ξy ξ e E v : ℝ} (hCb : 0 ≤ Cb) (hξy : 0 ≤ ξy) (hξ : ξy ≤ ξ)
    (hv : v ≤ Cb * ξy ^ 2 * e) (he0 : 0 ≤ e) (he : e ≤ X * E) : v ≤ Cb * X * ξ ^ 2 * E := by
  have hpow := pow_le_pow_left₀ hξy hξ 2
  calc v ≤ Cb * ξy ^ 2 * e := hv
    _ ≤ Cb * ξ ^ 2 * (X * E) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hCb) he he0 (by positivity)
    _ = Cb * X * ξ ^ 2 * E := by ring
theorem greenColumnConstant_nonneg (W : GaugeSetting) (hB : W.ColumnEstimatesHold)
    (c₁ : W.CoarseBond) :
    0 ≤ greenColumnConstant 4 W.data.L (chosen W.data.L).rate (chosen W.data.L).bound := by
  have h0 := (abs_nonneg _).trans (hB.kernel_le c₁ c₁)
  by_contra hneg
  rw [not_le] at hneg
  have hξ : 0 < GaugeSetting.coarseSpacing c₁ := levelSpacing_pos _ _
  have h1 := mul_neg_of_neg_of_pos hneg
    (Real.exp_pos ((chosen W.data.L).rate * cellRadius 4 W.data.L))
  have h2 := mul_neg_of_neg_of_pos h1 (pow_pos hξ 2)
  have h3 := mul_neg_of_neg_of_pos h2
    (Real.exp_pos (-(chosen W.data.L).rate * GaugeSetting.coarseDist c₁ c₁))
  exact absurd h0 (not_le.mpr h3)
theorem abs_greenColumn_le_of_cell (hCells : SeparatedChainStructure) (W : GaugeSetting)
    (hB : W.ColumnEstimatesHold) (hδ : 0 ≤ decayRate W.data.L) (c₁ c : W.CoarseBond)
    {y : W.data.Space} (hy : y ∈ W.chain.shellSitesUnion) {b : W.data.BaseBond}
    (hb : b ∈ W.bondSet) (hcell : W.chain.LiesInCell b y)
    (hξ : W.chain.localSpacing y ≤ GaugeSetting.coarseSpacing c₁)
    (hd : GaugeSetting.siteCoarseDist y c₁ ≤ cellRadius 4 W.data.L) :
    |(W.greenColumn c).1 b| ≤ entryConstant W.data.L * GaugeSetting.coarseSpacing c₁ ^ 2 *
      Real.exp (-decayRate W.data.L * GaugeSetting.coarseDist c₁ c) := by
  have hp := (hCells W.data W.chain).2.2.2.2.2.2.2.2
  have hsymm := hp.2.2.1
  have htri := hp.2.2.2.2
  have hd' : W.chain.scaledDist y (GaugeSetting.coarseAnchor c₁) ≤ cellRadius 4 W.data.L := hd
  have hdist : W.chain.scaledDist (GaugeSetting.coarseAnchor c₁) (GaugeSetting.coarseAnchor c) ≤
      cellRadius 4 W.data.L + W.chain.scaledDist y (GaugeSetting.coarseAnchor c) := by
    have h1 := htri (GaugeSetting.coarseAnchor c₁) y (GaugeSetting.coarseAnchor c)
    have h2 := hsymm y (GaugeSetting.coarseAnchor c₁)
    linarith
  have hexp : Real.exp (-decayRate W.data.L * GaugeSetting.siteCoarseDist y c) ≤
      Real.exp (decayRate W.data.L * cellRadius 4 W.data.L) *
        Real.exp (-decayRate W.data.L * GaugeSetting.coarseDist c₁ c) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hdist hδ
    show -decayRate W.data.L * W.chain.scaledDist y (GaugeSetting.coarseAnchor c) ≤
      decayRate W.data.L * cellRadius 4 W.data.L +
        -decayRate W.data.L *
          W.chain.scaledDist (GaugeSetting.coarseAnchor c₁) (GaugeSetting.coarseAnchor c)
    linarith
  have hξy : 0 ≤ W.chain.localSpacing y := (levelSpacing_pos _ _).le
  exact column_chain_le (greenColumnConstant_nonneg W hB c₁) hξy hξ (hB.bond_le c y hy b hb hcell)
    (Real.exp_pos _).le hexp
theorem abs_blockBondMean_bondMul_le (hAvg : BlockBondMeanIsLocal)
    (hRows : CoarseBondFormsAndMatricesHold)
    (hCells : SeparatedChainStructure) (W : GaugeSetting)
    (hB : W.ColumnEstimatesHold) (hδ : 0 ≤ decayRate W.data.L) (c₁ c : W.CoarseBond)
    (g : W.data.SiteField) {κ : ℝ} (hκ : 0 ≤ κ)
    (hg : ∀ x : W.data.BaseSite, (x : W.data.Space) ∈ ScaleData.bondSupport c₁.2.1 → |g x| ≤ κ) :
    |W.data.blockBondMean c₁.1 (W.data.bondMul g (W.greenColumn c).1) c₁.2.1| ≤
      κ * (entryConstant W.data.L * GaugeSetting.coarseSpacing c₁ ^ 2 *
        Real.exp (-decayRate W.data.L * GaugeSetting.coarseDist c₁ c)) := by
  have hmul : ∀ b : W.data.BaseBond, (b.1.src : W.data.Space) ∈ ScaleData.bondSupport c₁.2.1 →
      ∀ v, |(W.greenColumn c).1 b| ≤ v → |W.data.bondMul g (W.greenColumn c).1 b| ≤ κ * v := by
    intro b hb v hv
    show |g b.1.src * (W.greenColumn c).1 b| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hg _ hb) hv (abs_nonneg _) hκ
  cases hk : GaugeSetting.coarseLevel c₁ with
  | zero =>
    obtain ⟨b, hb, rfl⟩ :
        ∃ (b : W.data.BaseBond) (h : b ∈ W.coarseBondsAt 0), c₁ = W.baseCoarseBond b h := by
      obtain ⟨⟨k, hk'⟩, b, hb⟩ := c₁
      have h0 : k = 0 := hk
      subst h0
      exact ⟨b, hb, rfl⟩
    obtain ⟨hsingle, hsupp, -⟩ := hB.coarseForms.base_level b hb
    have hbb : b ∈ W.bondSet := by
      obtain ⟨h, -⟩ := hb
      exact h
    have hcell : W.chain.LiesInCell b (GaugeSetting.coarseAnchor (W.baseCoarseBond b hb)) := by
      by_contra hn
      have h0 := hsupp b hbb hn
      rw [hsingle] at h0
      simp at h0
    have hav : W.data.blockBondMean (W.baseCoarseBond b hb).1 (W.data.bondMul g (W.greenColumn c).1)
        (W.baseCoarseBond b hb).2.1 = W.data.bondMul g (W.greenColumn c).1 b :=
      (hRows W).2.1.2.1 _ b
    rw [hav]
    refine hmul b (src_mem_bondSupport W.data b) _ ?_
    have hp := (hCells W.data W.chain).2.2.2.2.2.2.2.2
    have hzero : GaugeSetting.siteCoarseDist (GaugeSetting.coarseAnchor (W.baseCoarseBond b hb))
        (W.baseCoarseBond b hb) = 0 :=
      hp.2.2.2.1 _
    refine abs_greenColumn_le_of_cell hCells W hB hδ _ c (coarseAnchor_mem_shellSitesUnion hRows _)
      hbb hcell (localSpacing_coarseAnchor hRows hCells _).le ?_
    rw [hzero]
    simp only [cellRadius]
    positivity
  | succ k =>
    obtain ⟨-, Cs, hcells, -, hmax⟩ := hB.coarseForms.higher_level c₁ k hk
    classical
    let Ft : W.data.BondField := fun b =>
      if (b.1.src : W.data.Space) ∈ ScaleData.bondSupport c₁.2.1 then
        W.data.bondMul g (W.greenColumn c).1 b else 0
    have hFt : Ft ∈ W.formSubspace := by
      intro b hb
      have h0 : (W.greenColumn c).1 b = 0 := (W.greenColumn c).2 b hb
      show (if (b.1.src : W.data.Space) ∈ ScaleData.bondSupport c₁.2.1 then
        g b.1.src * (W.greenColumn c).1 b else 0) = 0
      rw [h0, mul_zero, ite_self]
    have hsame := hAvg W.data c₁.1 (coarseBond_level_le c₁) c₁.2.1
      (W.data.bondMul g (W.greenColumn c).1) Ft (fun b hb => (if_pos hb).symm)
    rw [hsame]
    obtain ⟨b, hbb, ⟨y, hyC, hyb⟩, hle⟩ := hmax ⟨Ft, hFt⟩
    have hle' : |W.data.blockBondMean c₁.1 Ft c₁.2.1| ≤ |Ft b| := hle
    refine hle'.trans ?_
    have hlev : (c₁.1 : ℕ) = k + 1 := hk
    have htop := coarseBond_level_le c₁
    have hall : y ∈ W.chain.shellSitesUnion := by
      simp only [SeparatedChain.shellSitesUnion, mem_iUnion]
      rcases hcells.2.1 y hyC with h | h
      · exact ⟨k, mem_Iic.2 (by omega), h⟩
      · exact ⟨k + 1, mem_Iic.2 (by omega), h⟩
    obtain ⟨hξ, hd⟩ := hcells.2.2.2 y hyC
    have hcol := abs_greenColumn_le_of_cell hCells W hB hδ c₁ c hall hbb hyb hξ hd
    by_cases hdom : (b.1.src : W.data.Space) ∈ ScaleData.bondSupport c₁.2.1
    · have hFb : Ft b = W.data.bondMul g (W.greenColumn c).1 b := if_pos hdom
      rw [hFb]
      exact hmul b hdom _ hcol
    · have hFb : Ft b = 0 := if_neg hdom
      rw [hFb, abs_zero]
      exact mul_nonneg hκ ((abs_nonneg _).trans hcol)
theorem abs_difference_of_products_le {ξ a b r s P R κ : ℝ} (ha : |a| ≤ P) (hb : |b| ≤ κ * R)
    (hr : |r| ≤ κ * P) (hs : |s| ≤ R) :
    |1 * ξ ^ 2 * (a * b - r * s)| ≤ 2 * κ * ξ ^ 2 * P * R := by
  have hP : 0 ≤ P := (abs_nonneg _).trans ha
  have h1 : |a * b| ≤ P * (κ * R) := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hP
  have h2 : |r * s| ≤ κ * P * R := by
    rw [abs_mul]
    exact mul_le_mul hr hs (abs_nonneg _) ((abs_nonneg _).trans hr)
  have h3 : |a * b - r * s| ≤ P * (κ * R) + κ * P * R := by
    obtain ⟨h1l, h1u⟩ := abs_le.mp h1
    obtain ⟨h2l, h2u⟩ := abs_le.mp h2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [one_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ξ ^ 2)]
  calc ξ ^ 2 * |a * b - r * s| ≤ ξ ^ 2 * (P * (κ * R) + κ * P * R) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 * κ * ξ ^ 2 * P * R := by ring
theorem bondSupport_subset_scaledCube_two (C : CubeGaugeSetting) (Q : C.data.CubeIndex)
    (hρ : 0 < ScaleData.cubeScale Q) (hDom : C.BondSupportsNearCube Q) {c₁ : C.CoarseBond}
    (hmeet : (ScaleData.bondSupport c₁.2.1 ∩ ScaleData.scaledCube Q (5 / 3)).Nonempty) :
    ScaleData.bondSupport c₁.2.1 ⊆ ScaleData.scaledCube Q 2 := by
  have hsub : ScaleData.scaledCube Q (5 / 3) ⊆ ScaleData.scaledCube Q (5 / 3 + 1 / 12) := by
    intro x hx
    have hx' : torusSupNorm (x - Q.2) ≤ 5 / 3 * ScaleData.cubeScale Q := hx
    show torusSupNorm (x - Q.2) ≤ (5 / 3 + 1 / 12) * ScaleData.cubeScale Q
    linarith
  exact hDom.1 c₁.1 c₁.2.1 (Or.inl c₁.2.2) (hmeet.mono (inter_subset_inter_right _ hsub))
theorem abs_changeTerm_le (hAvg : BlockBondMeanIsLocal)
    (hRows : CoarseBondFormsAndMatricesHold)
    (hCells : SeparatedChainStructure) (C : CubeGaugeSetting) (Q : C.data.CubeIndex)
    (hB : C.toGaugeSetting.ColumnEstimatesHold)
    (hB' : (C.localSetting Q).toGaugeSetting.ColumnEstimatesHold)
    (hδ : 0 ≤ decayRate C.data.L) (ha : C.mass = 1) (hρ : 0 < ScaleData.cubeScale Q)
    (hObj : C.LocalObjectsAgreeNearCube Q) (hDom : C.BondSupportsNearCube Q)
    (hDist : C.DistancesNearCube Q)
    (hθ : ∀ x x' : C.data.Space, |ScaleData.cutoffFn Q x - ScaleData.cutoffFn Q x'| ≤
      3 * (ScaleData.cubeScale Q)⁻¹ * torusSupNorm (x - x'))
    (c c'' : C.CoarseBond) (e'' : (C.localSetting Q).CoarseBond)
    (hsite'' : GaugeSetting.coarseAnchor e'' = GaugeSetting.coarseAnchor c'')
    (c₁ : C.CoarseBond) (hc₁ : c₁ ∈ C.changeBonds Q) :
    |C.changeTerm Q (C.greenOp (C.meanOpAdjoint (C.coarseDelta c))).1
        ((C.localSetting Q).greenOp
          ((C.localSetting Q).meanOpAdjoint ((C.localSetting Q).coarseDelta e''))).1 c₁| ≤
      9 * (ScaleData.cubeScale Q)⁻¹ * entryConstant C.data.L ^ 2 *
        (C.chain.localSpacing (GaugeSetting.coarseAnchor c₁) ^ 7 *
          Real.exp (-decayRate C.data.L *
            GaugeSetting.siteCoarseDist (GaugeSetting.coarseAnchor c₁) c) *
          Real.exp (-decayRate C.data.L *
            GaugeSetting.siteCoarseDist (GaugeSetting.coarseAnchor c₁) c'')) := by
  obtain ⟨⟨e₁, he₁⟩, hmeet, -⟩ := hc₁
  have hdom2 := bondSupport_subset_scaledCube_two C Q hρ hDom hmeet
  have ht := hdom2 (src_mem_bondSupport C.data c₁.2.1)
  have hh := hdom2 (tgt_mem_bondSupport C.data c₁.2.1)
  obtain ⟨hiff, hsites⟩ := hObj.2.1 c₁.1 c₁.2.1 ht hh
  have hme : c₁.2.1 ∈ (C.localSetting Q).coarseBondsAt c₁.1 := hiff.1 c₁.2.2
  have hee : e₁ = ⟨c₁.1, c₁.2.1, hme⟩ :=
    GaugeSetting.levelBond_injective (W := (C.localSetting Q).toGaugeSetting) he₁
  subst hee
  have hsite₁ : GaugeSetting.coarseAnchor (W := (C.localSetting Q).toGaugeSetting)
      ⟨c₁.1, c₁.2.1, hme⟩ = GaugeSetting.coarseAnchor c₁ := (hsites c₁.2.2 hme).symm
  have hξ : 0 < GaugeSetting.coarseSpacing c₁ := levelSpacing_pos _ _
  have hκ : 0 ≤ 9 / 2 * (ScaleData.cubeScale Q)⁻¹ * GaugeSetting.coarseSpacing c₁ := by positivity
  have hg : ∀ x : C.data.BaseSite, (x : C.data.Space) ∈ ScaleData.bondSupport c₁.2.1 →
      |C.cutoffShift Q c₁ x| ≤ 9 / 2 * (ScaleData.cubeScale Q)⁻¹ * GaugeSetting.coarseSpacing c₁ := by
    intro x hx
    have h1 := hθ x (GaugeSetting.coarseAnchor c₁)
    have h2 := torusSupNorm_sub_coarseAnchor_le hRows c₁ hx
    show |ScaleData.cutoffFn Q x - ScaleData.cutoffFn Q (GaugeSetting.coarseAnchor c₁)| ≤ _
    calc |ScaleData.cutoffFn Q x - ScaleData.cutoffFn Q (GaugeSetting.coarseAnchor c₁)|
        ≤ 3 * (ScaleData.cubeScale Q)⁻¹ *
            torusSupNorm ((x : C.data.Space) - GaugeSetting.coarseAnchor c₁) := h1
      _ ≤ 3 * (ScaleData.cubeScale Q)⁻¹ * (3 / 2 * GaugeSetting.coarseSpacing c₁) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 9 / 2 * (ScaleData.cubeScale Q)⁻¹ * GaugeSetting.coarseSpacing c₁ := by ring
  have R1 := abs_blockBondMean_bondMul_le hAvg hRows hCells C.toGaugeSetting hB hδ c₁ c
    (C.cutoffShift Q c₁) hκ hg
  have R2 := abs_blockBondMean_bondMul_le hAvg hRows hCells (C.localSetting Q).toGaugeSetting hB' hδ
    ⟨c₁.1, c₁.2.1, hme⟩ e'' (C.cutoffShift Q c₁) hκ hg
  have P1 := hB.kernel_le c₁ c
  have P2 := hB'.kernel_le ⟨c₁.1, c₁.2.1, hme⟩ e''
  have hD : GaugeSetting.coarseDist c₁ c'' ≤
      GaugeSetting.coarseDist (W := (C.localSetting Q).toGaugeSetting) ⟨c₁.1, c₁.2.1, hme⟩ e'' := by
    show C.chain.scaledDist (GaugeSetting.coarseAnchor c₁) (GaugeSetting.coarseAnchor c'') ≤
      (C.chain.localization Q).scaledDist
        (GaugeSetting.coarseAnchor (W := (C.localSetting Q).toGaugeSetting) ⟨c₁.1, c₁.2.1, hme⟩)
        (GaugeSetting.coarseAnchor (W := (C.localSetting Q).toGaugeSetting) e'')
    rw [hsite₁, hsite'']
    exact hDist.1 _ _
  have hE : Real.exp (-decayRate C.data.L *
        GaugeSetting.coarseDist (W := (C.localSetting Q).toGaugeSetting) ⟨c₁.1, c₁.2.1, hme⟩ e'') ≤
      Real.exp (-decayRate C.data.L * GaugeSetting.coarseDist c₁ c'') := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hD hδ
    linarith
  have hEntry : 0 ≤ entryConstant C.data.L * GaugeSetting.coarseSpacing c₁ ^ 2 := by
    have h0 := (abs_nonneg _).trans P1
    by_contra hneg
    exact absurd h0 (not_le.mpr (mul_neg_of_neg_of_pos (not_le.mp hneg) (Real.exp_pos _)))
  have hS : entryConstant C.data.L * GaugeSetting.coarseSpacing c₁ ^ 2 * Real.exp (-decayRate C.data.L *
        GaugeSetting.coarseDist (W := (C.localSetting Q).toGaugeSetting) ⟨c₁.1, c₁.2.1, hme⟩ e'') ≤
      entryConstant C.data.L * GaugeSetting.coarseSpacing c₁ ^ 2 *
        Real.exp (-decayRate C.data.L * GaugeSetting.coarseDist c₁ c'') :=
    mul_le_mul_of_nonneg_left hE hEntry
  have hterm : C.changeTerm Q (C.greenOp (C.meanOpAdjoint (C.coarseDelta c))).1
        ((C.localSetting Q).greenOp
          ((C.localSetting Q).meanOpAdjoint ((C.localSetting Q).coarseDelta e''))).1 c₁ =
      1 * GaugeSetting.coarseSpacing c₁ ^ 2 *
        (C.bondMeanAt c₁ (C.greenOp (C.meanOpAdjoint (C.coarseDelta c))).1 *
            C.bondMeanAt c₁ (C.data.bondMul (C.cutoffShift Q c₁)
              ((C.localSetting Q).greenOp ((C.localSetting Q).meanOpAdjoint
                ((C.localSetting Q).coarseDelta e''))).1) -
          C.bondMeanAt c₁ (C.data.bondMul (C.cutoffShift Q c₁)
              (C.greenOp (C.meanOpAdjoint (C.coarseDelta c))).1) *
            C.bondMeanAt c₁ ((C.localSetting Q).greenOp ((C.localSetting Q).meanOpAdjoint
              ((C.localSetting Q).coarseDelta e''))).1) := by
    rw [← ha]
    rfl
  rw [hterm]
  have hfinal := abs_difference_of_products_le (ξ := GaugeSetting.coarseSpacing c₁) P1 (R2.trans
    (mul_le_mul_of_nonneg_left hS hκ)) R1 (P2.trans hS)
  refine hfinal.trans (le_of_eq ?_)
  have hy := localSpacing_coarseAnchor hRows hCells (W := C.toGaugeSetting) c₁
  have hy' : C.chain.localSpacing (GaugeSetting.coarseAnchor c₁) = GaugeSetting.coarseSpacing c₁ := hy
  have e1 : GaugeSetting.siteCoarseDist (GaugeSetting.coarseAnchor c₁) c =
      GaugeSetting.coarseDist c₁ c := rfl
  have e2 : GaugeSetting.siteCoarseDist (GaugeSetting.coarseAnchor c₁) c'' =
      GaugeSetting.coarseDist c₁ c'' := rfl
  rw [hy', e1, e2]
  ring
theorem shellSitesUnion_finite {D : ScaleData} (B : SeparatedChain D) : B.shellSitesUnion.Finite := by apply _root_.YangMills.Construction.GeneralTorus.ScaledDistExpSums.shellSitesUnion_finite <;> assumption
theorem coarseAnchor_mem_changeSites (hRows : CoarseBondFormsAndMatricesHold)
    (hCells : SeparatedChainStructure) (C : CubeGaugeSetting) (Q : C.data.CubeIndex)
    (hρ : 0 < ScaleData.cubeScale Q) (hLev : C.LevelsNearCube Q)
    (hDom : C.BondSupportsNearCube Q) {c₁ : C.CoarseBond} (hc₁ : c₁ ∈ C.changeBonds Q) :
    GaugeSetting.coarseAnchor c₁ ∈ C.changeSites Q := by
  obtain ⟨-, hmeet, x, hx, hxout⟩ := hc₁
  have hdom2 := bondSupport_subset_scaledCube_two C Q hρ hDom hmeet
  have hlevel : GaugeSetting.coarseLevel c₁ ≤ Q.1 + 1 := by
    obtain ⟨p, hp⟩ := hmeet
    exact hLev.2.2.2 c₁ ⟨p, hp.1, hdom2 hp.1⟩
  have hξ : GaugeSetting.coarseSpacing c₁ ≤ C.data.levelSpacing (Q.1 + 1) :=
    levelSpacing_mono C.data hlevel
  have hs : C.data.levelSpacing (Q.1 + 1) = (C.data.L : ℝ) * C.data.levelSpacing Q.1 := by
    simp only [ScaleData.levelSpacing]
    ring
  have hM : (12 : ℝ) * (C.data.L : ℝ) ≤ (C.data.blockCount : ℝ) := by
    exact_mod_cast C.twelve_mul_L_le_blockCount
  have hρdef : ScaleData.cubeScale Q = (C.data.blockCount : ℝ) * C.data.levelSpacing Q.1 := rfl
  have hsmall : 3 / 2 * C.data.levelSpacing (Q.1 + 1) ≤ ScaleData.cubeScale Q / 8 := by
    have := mul_le_mul_of_nonneg_right hM (levelSpacing_pos C.data Q.1).le
    rw [hs, hρdef]
    linarith
  refine ⟨coarseAnchor_mem_shellSitesUnion hRows (W := C.toGaugeSetting) c₁, ?_, ?_, ?_⟩
  · have hy := localSpacing_coarseAnchor hRows hCells (W := C.toGaugeSetting) c₁
    have hy' : C.chain.localSpacing (GaugeSetting.coarseAnchor c₁) =
        GaugeSetting.coarseSpacing c₁ := hy
    rw [hy']
    exact hξ
  · have hxz : 4 / 3 * ScaleData.cubeScale Q < torusSupNorm ((x : C.data.Space) - Q.2) :=
      not_le.mp hxout
    have h1 := torusSupNorm_sub_le_add (x : C.data.Space) (GaugeSetting.coarseAnchor c₁) Q.2
    have h2 := torusSupNorm_sub_coarseAnchor_le hRows c₁ hx
    linarith
  · have hy : GaugeSetting.coarseAnchor c₁ ∈ ScaleData.bondSupport c₁.2.1 := by
      rcases ((hRows C.toGaugeSetting).1.1 c₁).1 with h | h
      · rw [h]
        exact src_mem_bondSupport C.data c₁.2.1
      · rw [h]
        exact tgt_mem_bondSupport C.data c₁.2.1
    exact hdom2 hy
theorem abs_sum_le_of_fibres_le_eight {R Y : Type*} [DecidableEq Y] (s : Finset R) (t : Finset Y)
    (y : R → Y) (G : Y → ℝ) (f : R → ℝ) {K : ℝ} (hK : 0 ≤ K) (hG : ∀ v, 0 ≤ G v)
    (hmap : ∀ r ∈ s, y r ∈ t) (hcard : ∀ v, (s.filter fun r => y r = v).card ≤ 8)
    (hf : ∀ r ∈ s, |f r| ≤ K * G (y r)) : |∑ r ∈ s, f r| ≤ 8 * K * ∑ v ∈ t, G v := by
  have hfib : ∑ r ∈ s, G (y r) ≤ 8 * ∑ v ∈ t, G v := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    have h1 : ∑ r ∈ s with y r = v, G (y r) = ∑ r ∈ s with y r = v, G v :=
      Finset.sum_congr rfl fun r hr => by rw [(Finset.mem_filter.mp hr).2]
    rw [h1, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard v) (hG v)
  calc |∑ r ∈ s, f r| ≤ ∑ r ∈ s, |f r| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ s, K * G (y r) := Finset.sum_le_sum hf
    _ = K * ∑ r ∈ s, G (y r) := (Finset.mul_sum _ _ _).symm
    _ ≤ K * (8 * ∑ v ∈ t, G v) := mul_le_mul_of_nonneg_left hfib hK
    _ = 8 * K * ∑ v ∈ t, G v := by ring
end ChangeBondSum
theorem LocalChainChangeBondSumBound.holds
    (hAvg : BlockBondMeanIsLocal)
    (hBounds : GreenColumnEstimatesOnSetting)
    (hGeom : CubeGeometryAndLocalChains)
    (hBump : CubeBumpCutoffProperties)
    (hRows : CoarseBondFormsAndMatricesHold)
    (hCells : SeparatedChainStructure)
    (hComp : CubeGreenCompression)
    (hFloors : InverseBoundsStatement)
    (hSP : InnerProductsAdjointsProjections.SettingInnerProductFacts) :
    LocalChainChangeBondSumBound := by
  classical
  intro C m K t hphys hfl Q hQ c hc c'' hc'' e'' he''
  obtain ⟨n, hQn⟩ := mem_iUnion.mp hQ
  have hn : Q.1 = n := hQn.2.1
  subst hn
  have hLM : C.data.L ≤ C.data.blockCount := by
    have := C.twelve_mul_L_le_blockCount
    omega
  have hgap : (GreenBounds.chosen C.data.L).gapLower ≤
      (C.data.gapCount : ℝ) * (C.data.blockCount : ℝ) := (le_max_left _ _).trans hfl.2
  have hB := hBounds C.toGaugeSetting m K t hphys hLM hfl.1 hgap
  have hphys' : (C.localSetting Q).toGaugeSetting.IsExpansionSetting m K t := hphys
  have hB' := hBounds (C.localSetting Q).toGaugeSetting m K t hphys' hLM hfl.1 hgap
  obtain ⟨hr0, hr1, -⟩ := hFloors.1 C.data.L C.data.blocking
  simp only [InverseBounds.decayRateOfInverse] at hr0 hr1
  have hδ : 0 ≤ ChangeBondSum.decayRate C.data.L := by
    show 0 ≤ (GreenBounds.chosen C.data.L).rate
    linarith
  obtain ⟨hLev, -, -, -, hObj, hDom, hDist⟩ := hGeom C Q.1 Q.2 hQn
  have hθ := (hBump C Q.1 Q hQn).2.2.2.2.2.2.2.1
  have hρ : 0 < ScaleData.cubeScale Q := by
    have hM : 0 < C.data.blockCount := by
      have h12 := C.twelve_mul_L_le_blockCount
      have hL := C.data.blocking.thirteen_le
      omega
    have hM' : (0 : ℝ) < (C.data.blockCount : ℝ) := by exact_mod_cast hM
    have hs := ChangeBondSum.levelSpacing_pos C.data Q.1
    show 0 < (C.data.blockCount : ℝ) * C.data.levelSpacing Q.1
    positivity
  have hsite'' : GaugeSetting.coarseAnchor e'' = GaugeSetting.coarseAnchor c'' := by
    obtain ⟨c', hb', -, -, hs'⟩ := (hComp C m K t hphys Q hQ).1 c'' hc''
    have hce : c' = e'' :=
      GaugeSetting.levelBond_injective (W := (C.localSetting Q).toGaugeSetting)
        (hb'.trans he''.symm)
    rw [← hce]
    exact hs'
  have hfinCoarseBond : Finite C.CoarseBond := (hSP C.toGaugeSetting).1
  have hRf : (C.changeBonds Q).Finite := toFinite _
  have hSf : (C.changeSites Q).Finite :=
    (ChangeBondSum.shellSitesUnion_finite C.chain).subset fun y hy => hy.1
  unfold CubeGaugeSetting.changeSiteSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hRf, finsum_mem_eq_finite_toFinset_sum _ hSf]
  have hK : 0 ≤ 9 * (ScaleData.cubeScale Q)⁻¹ *
      ChangeBondSum.entryConstant C.data.L ^ 2 := by positivity
  have hmain := ChangeBondSum.abs_sum_le_of_fibres_le_eight hRf.toFinset hSf.toFinset
    (fun c₁ : C.CoarseBond => GaugeSetting.coarseAnchor c₁)
    (fun y => C.chain.localSpacing y ^ 7 *
      Real.exp (-ChangeBondSum.decayRate C.data.L * GaugeSetting.siteCoarseDist y c) *
      Real.exp (-ChangeBondSum.decayRate C.data.L * GaugeSetting.siteCoarseDist y c''))
    (fun c₁ => C.changeTerm Q (C.greenOp (C.meanOpAdjoint (C.coarseDelta c))).1
      ((C.localSetting Q).greenOp
        ((C.localSetting Q).meanOpAdjoint ((C.localSetting Q).coarseDelta e''))).1 c₁)
    hK
    (fun y => by
      have hξ := ChangeBondSum.levelSpacing_pos C.data
        (sInf {n | y ∈ C.chain.shellSites n})
      have hξ' : 0 < C.chain.localSpacing y := hξ
      positivity)
    (fun c₁ h => hSf.mem_toFinset.mpr
      (ChangeBondSum.coarseAnchor_mem_changeSites hRows hCells C Q hρ hLev hDom
        (hRf.mem_toFinset.mp h)))
    (fun v => by
      have hsub : (↑(hRf.toFinset.filter fun c₁ : C.CoarseBond =>
          GaugeSetting.coarseAnchor c₁ = v) : Set C.CoarseBond) ⊆
          {c₁ : C.CoarseBond | GaugeSetting.coarseAnchor c₁ = v} :=
        fun r hr => (Finset.mem_filter.mp hr).2
      have h1 := (Set.encard_le_encard hsub).trans ((hRows C.toGaugeSetting).1.2 v)
      rw [Set.encard_coe_eq_coe_finsetCard] at h1
      exact_mod_cast h1)
    (fun c₁ h => ChangeBondSum.abs_changeTerm_le hAvg hRows hCells C Q hB hB' hδ hphys.2
      hρ hObj hDom hDist hθ c c'' e'' hsite'' c₁ (hRf.mem_toFinset.mp h))
  refine hmain.trans (le_of_eq ?_)
  ring
end GeneralTorus
end YangMills.Construction
