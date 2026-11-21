import YangMills.Construction.Torus.ColumnsOfTheGreenOperatorOnTheTori
import YangMills.Construction.Torus.ProjectionsOfTheSequenceProof
import YangMills.Construction.Torus.QuadraticFormsAndMatricesOfTheAveragesProof
import YangMills.Construction.Torus.WeightedDistanceAndCellsOfASeparatedSequence
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace GeneralTorus
namespace GreenColumns
section Numbers
variable (D : ScaleData)
theorem one_lt_L_cast : (1 : ℝ) < D.L := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.one_lt_blockFactor <;> assumption
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem levelSpacing_mono {m n : ℕ} (h : m ≤ n) : D.levelSpacing m ≤ D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.SupDistBound.levelSpacing_mono <;> assumption
theorem levelSpacing_succ (n : ℕ) : D.levelSpacing (n + 1) = (D.L : ℝ) * D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ClosedMeanFree.levelSpacing_succ <;> assumption
end Numbers
theorem coarseSpacing_pos {G : GaugeSetting} (c : G.CoarseBond) : 0 < GaugeSetting.coarseSpacing c := by apply _root_.YangMills.Construction.GeneralTorus.CompressedBoundsProof.coarseSpacing_pos <;> assumption
theorem coarseBond_level_le {G : GaugeSetting} (c : G.CoarseBond) : (c.1 : ℕ) ≤ G.data.lastLevel :=
  Nat.lt_succ_iff.1 c.1.2
theorem torusSupNorm_proj_le {S : ℝ} (v : Fin 4 → ℝ) : _root_.YangMills.Construction.TorusMetric.torusSupNorm (torusProj S v) ≤ supNormVec v := by apply _root_.YangMills.Construction.Weighted.ProjectionProof.torusSupNorm_proj_le <;> assumption
theorem self_mem_supCube {S s : ℝ} (hs : 0 ≤ s) (y : Torus4 S) : y ∈ supCube s y := by apply _root_.YangMills.Construction.GeneralTorus.CubePartitions.self_mem_supCube <;> assumption
section Sequences
variable {D : ScaleData} (B : SeparatedChain D)
theorem set_antitone {i j : ℕ} (h : i ≤ j) : B.set j ⊆ B.set i := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.Chain.set_antitone <;> assumption
theorem shellSites_eq_empty {n : ℕ} (hn : D.lastLevel < n) : B.shellSites n = ∅ := by apply _root_.YangMills.Construction.GeneralTorus.CoarseBondForms.shellSites_eq_empty <;> assumption
variable (hc : SeparatedChainStructure)
include hc
theorem mem_shellSites_iff {n : ℕ} (hn : n ≤ D.lastLevel) (y : D.Space) :
    y ∈ B.shellSites n ↔ y ∈ (D.levelSublattice n : Set D.Space) ∧ y ∈ B.set n ∧
      y ∉ B.set (n + 1) := by apply _root_.YangMills.Construction.GeneralTorus.CoarseBondForms.mem_shellSites_iff <;> assumption
theorem shell_level_unique {n m : ℕ} {y : D.Space} (hn : n ≤ D.lastLevel) (hy : y ∈ B.shellSites n)
    (hy' : y ∈ B.shellSites m) : m = n := by
  by_cases hm : m ≤ D.lastLevel
  · have a := (mem_shellSites_iff B hc hm y).1 hy'
    have b := (mem_shellSites_iff B hc hn y).1 hy
    rcases lt_trichotomy m n with h | h | h
    · exact absurd (set_antitone B h b.2.1) a.2.2
    · exact h
    · exact absurd (set_antitone B h a.2.1) b.2.2
  · rw [shellSites_eq_empty B (by omega)] at hy'
    exact absurd hy' (notMem_empty _)
theorem localSpacing_eq {n : ℕ} (hn : n ≤ D.lastLevel) {y : D.Space} (hy : y ∈ B.shellSites n) :
    B.localSpacing y = D.levelSpacing n := by
  have hs : {i | y ∈ B.shellSites i} = {n} := by
    ext i
    simp only [mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun hi => shell_level_unique B hc hn hy hi, fun hi => hi ▸ hy⟩
  unfold SeparatedChain.localSpacing
  rw [hs]
  simp
omit hc in
theorem exists_shell_level {y : D.Space} (hy : y ∈ B.shellSitesUnion) :
    ∃ n ≤ D.lastLevel, y ∈ B.shellSites n := by
  simpa only [SeparatedChain.shellSitesUnion, mem_iUnion, mem_Iic, exists_prop] using hy
theorem localCube_subset_set {n : ℕ} (hn : n ≤ D.lastLevel) {y : D.Space} (hy : y ∈ B.shellSites n) :
    B.localCube y ⊆ B.set n := by
  have hl := ((hc D B).2.1 n hn)
  have h1 : B.localCube y ⊆ B.shell n := by
    rw [hl.2.2.2.1]
    exact subset_biUnion_of_mem (u := B.localCube) hy
  have h2 := hl.1
  intro x hx
  have hx' := h1 hx
  rw [h2] at hx'
  obtain ⟨Q, ⟨-, hQ, -⟩, hxQ⟩ := hx'
  exact hQ hxQ
end Sequences
section Forms
variable (G : GaugeSetting)
variable {G}
theorem unitStep_injective (D : ScaleData) {μ ν : Fin 4}
    (h : unitStep D.torusSide (D.levelSpacing 0) μ = unitStep D.torusSide (D.levelSpacing 0) ν) :
    μ = ν := by
  by_contra hne
  have hσ := levelSpacing_pos D 0
  have h1 : ((coordPoint D.torusSide μ (D.levelSpacing 0) : D.Space)) μ =
      (coordPoint D.torusSide ν (D.levelSpacing 0) : D.Space) μ :=
    congrFun (congrArg Subtype.val h) μ
  simp only [coordPoint, torusProj, Pi.single_eq_same, Pi.single_eq_of_ne hne] at h1
  have hlt : D.levelSpacing 0 < D.torusSide := by
    obtain ⟨k, hk, hS⟩ := D.torusSide_evenMultiple
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hLt : (1 : ℝ) ≤ (D.L : ℝ) ^ D.lastLevel := one_le_pow₀ (one_lt_L_cast D).le
    have hb := D.baseSpacing_pos
    have h0 : D.levelSpacing 0 = D.baseSpacing := by simp [ScaleData.levelSpacing]
    rw [h0, hS]
    nlinarith [mul_pos hb (by linarith : (0 : ℝ) < (D.L : ℝ) ^ D.lastLevel),
      mul_le_mul hk1 hLt (by norm_num) (by linarith : (0 : ℝ) ≤ (k : ℝ))]
  have h2 : ((D.levelSpacing 0 : ℝ) : AddCircle D.torusSide) = 0 := by simpa using h1
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff D.torusSide).1 h2
  have hS0 : 0 < D.torusSide := hσ.trans hlt
  simp only [zsmul_eq_mul] at hn
  have hn1 : (0 : ℝ) < n := by
    by_contra hcon
    have : (n : ℝ) * D.torusSide ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hcon) hS0.le
    linarith
  have hn2 : (1 : ℝ) ≤ n := by
    have : (0 : ℤ) < n := by exact_mod_cast hn1
    exact_mod_cast this
  nlinarith
variable (hd : DiffAndMeans.DiffAndMeanFacts)
include hd
end Forms
section Cells
variable {G : GaugeSetting}
variable (hd : DiffAndMeans.DiffAndMeanFacts) (hc : SeparatedChainStructure)
  (hr : CoarseBondFormsAndMatricesHold)
  (hsp : InnerProductsAdjointsProjections.SettingInnerProductFacts)
end Cells
section Seminorm
variable {L' m' : ℕ} (S : SeparatedSequences.ScaleData)
end Seminorm
section CutGradient
open GreenBounds
variable {L : ℕ} (s : LevelUnitChain L)
end CutGradient
section Columns
open GreenBounds
variable {L : ℕ} (nums : GreenConstants) (s : LevelUnitChain L)
theorem siteDecay_nonneg (y : s.data.Space) (c : s.setting.CoarseBond) : 0 ≤ siteDecay nums s y c :=
  (Real.exp_pos _).le
theorem localSpacing_nonneg {D : ScaleData} (B : SeparatedChain D) (y : D.Space) :
    0 ≤ B.localSpacing y := (levelSpacing_pos D _).le
theorem sum_le_card_mul {ι : Type*} (C : Finset ι) (a : ι → ℝ) {t n : ℝ} (ht : 0 ≤ t)
    (hcard : (C.card : ℝ) ≤ n) (h : ∀ y ∈ C, a y ≤ t) : ∑ y ∈ C, a y ≤ n * t := by
  refine (Finset.sum_le_card_nsmul C a t h).trans ?_
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcard ht
variable {nums s}
end Columns
section Corners
variable {S σ : ℝ}
theorem torusProj_add (v w : Fin 4 → ℝ) : torusProj S (v + w) = torusProj S v + torusProj S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem torusProj_sub (v w : Fin 4 → ℝ) : torusProj S (v - w) = torusProj S v - torusProj S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem torusProj_zero : torusProj S 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.torusProj_zero <;> assumption
theorem corner_eq_basePoint_add (p : LatticePlaquette S σ) {x : LatticeSite S σ} (hx : x ∈ p.cornerSet) :
    ∃ a b : ℝ, (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧
      (x : Torus4 S) = (p.basePoint : Torus4 S) +
        torusProj S (a • Pi.single p.dir₁ σ + b • Pi.single p.dir₂ σ) := by
  have hst : ∀ μ, ((unitStep S σ μ : LatticeSite S σ) : Torus4 S) = torusProj S (Pi.single μ σ) :=
    fun _ => rfl
  simp only [LatticePlaquette.cornerSet, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · refine ⟨0, 0, Or.inl rfl, Or.inl rfl, ?_⟩
    simp only [zero_smul, add_zero, torusProj_zero]
  · refine ⟨1, 0, Or.inr rfl, Or.inl rfl, ?_⟩
    simp only [one_smul, zero_smul, add_zero, AddSubgroup.coe_add, hst]
  · refine ⟨1, 1, Or.inr rfl, Or.inr rfl, ?_⟩
    simp only [one_smul, torusProj_add, AddSubgroup.coe_add, hst]
    abel
  · refine ⟨0, 1, Or.inl rfl, Or.inr rfl, ?_⟩
    simp only [one_smul, zero_smul, zero_add, AddSubgroup.coe_add, hst]
theorem corners_sup_close (hσ : 0 ≤ σ) (p : LatticePlaquette S σ) {x x' : LatticeSite S σ}
    (hx : x ∈ p.cornerSet) (hx' : x' ∈ p.cornerSet) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm ((x : Torus4 S) - (x' : Torus4 S)) ≤ σ := by
  obtain ⟨a, b, ha, hb, e⟩ := corner_eq_basePoint_add p hx
  obtain ⟨a', b', ha', hb', e'⟩ := corner_eq_basePoint_add p hx'
  have hd : (x : Torus4 S) - (x' : Torus4 S) = torusProj S ((a - a') • Pi.single p.dir₁ σ +
      (b - b') • Pi.single p.dir₂ σ) := by
    rw [e, e', add_sub_add_left_eq_sub, ← torusProj_sub]
    congr 1
    ext μ
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1 : |a - a'| ≤ 1 := by
    rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl <;> norm_num
  have h2 : |b - b'| ≤ 1 := by
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl <;> norm_num
  have hne : p.dir₁ ≠ p.dir₂ := p.dir₁_lt_dir₂.ne
  rw [hd]
  refine (torusSupNorm_proj_le _).trans (Finset.sup'_le _ _ fun μ _ => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hμ : μ = p.dir₁
  · subst hμ
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne, mul_zero, add_zero, abs_mul, abs_of_nonneg hσ]
    exact mul_le_of_le_one_left hσ h1
  · rw [Pi.single_eq_of_ne hμ, mul_zero, zero_add]
    by_cases hμ' : μ = p.dir₂
    · subst hμ'
      rw [Pi.single_eq_same, abs_mul, abs_of_nonneg hσ]
      exact mul_le_of_le_one_left hσ h2
    · rw [Pi.single_eq_of_ne hμ', mul_zero, abs_zero]
      exact hσ
theorem ends_mem_cornerSet (p : LatticePlaquette S σ) {β : LatticeBond S σ} (hβ : β ∈ p.boundaryBonds) :
    β.src ∈ p.cornerSet ∧ β.tgt ∈ p.cornerSet := by
  have c1 : p.basePoint ∈ p.cornerSet := Or.inl rfl
  have c2 : p.basePoint + unitStep S σ p.dir₁ ∈ p.cornerSet := Or.inr (Or.inl rfl)
  have c3 : p.basePoint + unitStep S σ p.dir₁ + unitStep S σ p.dir₂ ∈ p.cornerSet :=
    Or.inr (Or.inr (Or.inl rfl))
  have c3' : p.basePoint + unitStep S σ p.dir₂ + unitStep S σ p.dir₁ ∈ p.cornerSet :=
    Or.inr (Or.inr (Or.inl (by abel)))
  have c4 : p.basePoint + unitStep S σ p.dir₂ ∈ p.cornerSet := Or.inr (Or.inr (Or.inr rfl))
  simp only [LatticePlaquette.boundaryBonds, List.mem_cons, List.not_mem_nil, or_false] at hβ
  rcases hβ with rfl | rfl | rfl | rfl
  · exact ⟨c1, c2⟩
  · exact ⟨c2, c3⟩
  · exact ⟨c3', c4⟩
  · exact ⟨c4, c1⟩
end Corners
section Cells
variable {G : GaugeSetting}
theorem plaquetteBond_ends_mem {p : G.data.BasePlaquette} {b : G.data.BaseBond}
    (h : ScaleData.IsPlaquetteBond p b) : b.1.src ∈ p.cornerSet ∧ b.1.tgt ∈ p.cornerSet := by
  rcases h with h | h
  · exact ends_mem_cornerSet p h
  · exact (ends_mem_cornerSet p h).symm
theorem anchor_props {b : G.data.BaseBond} (hb : b ∈ G.bondSet) :
    (G.chain.anchor b : G.data.Space) ∈ G.chain.set 0 ∧
      (G.chain.anchor b = b.1.src ∨ G.chain.anchor b = b.1.tgt) := by
  have hend : (b.1.src : G.data.Space) ∈ G.chain.set 0 ∨
      (b.1.tgt : G.data.Space) ∈ G.chain.set 0 := by
    unfold GaugeSetting.bondSet at hb
    cases hch : G.choice with
    | meeting =>
      rw [hch] at hb
      exact hb
    | interior =>
      rw [hch] at hb
      exact Or.inl hb.1
  unfold SeparatedChain.anchor
  by_cases h : (b.1.src : G.data.Space) ∈ G.chain.set 0
  · rw [if_pos h]
    exact ⟨h, Or.inl rfl⟩
  · rw [if_neg h]
    exact ⟨hend.resolve_left h, Or.inr rfl⟩
variable (hc : SeparatedChainStructure)
  (hw : ScaledDistAndCells) (hL : G.data.L ≤ G.data.blockCount)
include hc hw hL
theorem exists_near_cell {y : G.data.Space} (hy : y ∈ G.chain.shellSitesUnion) (x f : G.data.BaseSite)
    (hx : (x : G.data.Space) ∈ G.chain.localCube y)
    (hf : (f : G.data.Space) ∈ G.chain.set 0)
    (hsup : _root_.YangMills.Construction.TorusMetric.torusSupNorm ((x : G.data.Space) - (f : G.data.Space)) ≤ G.data.levelSpacing 0) :
    ∃ y₂ ∈ G.chain.shellSitesUnion, (f : G.data.Space) ∈ G.chain.localCube y₂ ∧
      G.chain.localSpacing y₂ ≤ (G.data.L : ℝ) * G.chain.localSpacing y ∧
      G.chain.scaledDist y y₂ ≤ 4 := by
  obtain ⟨n, hn, hyn⟩ := exists_shell_level G.chain hy
  have hx0 : (x : G.data.Space) ∈ G.chain.set 0 :=
    set_antitone G.chain (Nat.zero_le n) (localCube_subset_set G.chain hc hn hyn hx)
  have hCM := (hw G hL).2.2.2.1
  have hsup' : _root_.YangMills.Construction.TorusMetric.torusSupNorm ((x : G.data.Space) - (f : G.data.Space)) ≤ G.data.baseSpacing := by
    have : G.data.levelSpacing 0 = G.data.baseSpacing := by simp [ScaleData.levelSpacing]
    exact hsup.trans (le_of_eq this)
  obtain ⟨y₁, hy₁, y₂, hy₂, hxy₁, hfy₂, hmeet⟩ := hCM.2 x x.2 f f.2 hx0 hf hsup'
  have huniq := ((hc G.data G.chain).2.2.2.2.2.2.2.1 x x.2 hx0).1
  have hyy : y₁ = y := huniq.unique ⟨hy₁, hxy₁⟩ ⟨hy, hx⟩
  subst hyy
  obtain ⟨n', hn', hyn'⟩ := exists_shell_level G.chain hy₂
  have hne : (G.chain.localCube y₁ ∩ G.chain.localCube y₂).Nonempty := by
    rcases hmeet with h | h
    · exact ⟨x, hxy₁, h ▸ hxy₁⟩
    · exact h
  obtain ⟨hlev, hdist⟩ := hCM.1 n n' y₁ hyn y₂ hyn' hne
  refine ⟨y₂, hy₂, hfy₂, ?_, hdist⟩
  rw [localSpacing_eq G.chain hc hn hyn, localSpacing_eq G.chain hc hn' hyn',
    ← levelSpacing_succ]
  obtain ⟨hl1, hl2⟩ := abs_le.1 hlev
  exact levelSpacing_mono G.data (by omega)
omit hw in
theorem localSpacing_le_of_off_set_one (z f : G.data.BaseSite) (hz : (z : G.data.Space) ∉ G.chain.set 1)
    (hsup : _root_.YangMills.Construction.TorusMetric.torusSupNorm ((z : G.data.Space) - (f : G.data.Space)) ≤ G.data.levelSpacing 0)
    {y₂ : G.data.Space} (hy₂ : y₂ ∈ G.chain.shellSitesUnion) (hf : (f : G.data.Space) ∈ G.chain.localCube y₂) :
    G.chain.localSpacing y₂ ≤ (G.data.L : ℝ) * G.data.levelSpacing 0 := by
  obtain ⟨n, hn, hyn⟩ := exists_shell_level G.chain hy₂
  rw [localSpacing_eq G.chain hc hn hyn, ← levelSpacing_succ]
  refine levelSpacing_mono G.data ?_
  by_contra hcon
  have hn2 : 2 ≤ n := by omega
  have hf2 : (f : G.data.Space) ∈ G.chain.set (1 + 1) :=
    set_antitone G.chain hn2 (localCube_subset_set G.chain hc hn hyn hf)
  have htop : 1 < G.data.lastLevel := by omega
  have hsep := G.chain.separation 1 htop
  have hzc : (z : G.data.Space) ∈ closedComplement (G.chain.set 1) := subset_closure hz
  have h2 : setSupDist (closedComplement (G.chain.set 1)) (G.chain.set (1 + 1)) ≤
      ENNReal.ofReal (_root_.YangMills.Construction.TorusMetric.torusSupNorm ((z : G.data.Space) - (f : G.data.Space))) :=
    iInf₂_le_of_le _ hzc (iInf₂_le_of_le _ hf2 le_rfl)
  have h3 := (hsep.trans_le h2).trans_le (ENNReal.ofReal_le_ofReal hsup)
  have h4 := (ENNReal.ofReal_lt_ofReal_iff (levelSpacing_pos G.data 0)).1 h3
  have hL1 := one_lt_L_cast G.data
  have hR : (1 : ℝ) ≤ G.data.gapCount := by
    have : G.data.L ≤ G.data.gapCount := G.L_le_gapCount
    have h' : (G.data.L : ℝ) ≤ G.data.gapCount := by exact_mod_cast this
    linarith
  have hM : (1 : ℝ) ≤ G.data.blockCount := by
    have h' : (G.data.L : ℝ) ≤ G.data.blockCount := by exact_mod_cast hL
    linarith
  have hs : G.data.levelSpacing 0 ≤ G.data.levelSpacing 1 := levelSpacing_mono G.data (Nat.zero_le 1)
  unfold ScaleData.blockLength at h4
  have h5 : 1 * G.data.levelSpacing 1 ≤ (G.data.blockCount : ℝ) * G.data.levelSpacing 1 :=
    mul_le_mul_of_nonneg_right hM (levelSpacing_pos G.data 1).le
  have h6 : 1 * ((G.data.blockCount : ℝ) * G.data.levelSpacing 1) ≤
      (G.data.gapCount : ℝ) * ((G.data.blockCount : ℝ) * G.data.levelSpacing 1) :=
    mul_le_mul_of_nonneg_right hR (by positivity [levelSpacing_pos G.data 1])
  linarith
theorem plaquette_bounds (A : ↥G.formSubspace) {K E : ℝ} (hK : 0 ≤ K) (hE : 0 ≤ E)
    (R : G.data.Space → ℝ) (hR0 : ∀ y, 0 ≤ R y)
    (hRn : ∀ y y₂, G.chain.scaledDist y y₂ ≤ 4 → R y₂ ≤ E * R y)
    (hb : ∀ y ∈ G.chain.shellSitesUnion, ∀ b ∈ G.bondSet, G.chain.LiesInCell b y →
      |A.1 b| ≤ K * G.chain.localSpacing y ^ 2 * R y)
    (hs : ∀ y ∈ G.chain.shellSitesUnion, ∀ x : G.data.BaseSite,
      (x : G.data.Space) ∈ G.chain.localCube y → ∀ μ ν : Fin 4,
        |G.data.forwardDiff ν (G.data.formComponent μ A.1) x| ≤
          K * G.chain.localSpacing y * R y)
    (p : G.data.BasePlaquette) {y : G.data.Space} (hy : y ∈ G.chain.shellSitesUnion)
    (hcorner : ∃ x ∈ p.cornerSet, (x : G.data.Space) ∈ G.chain.localCube y) :
    (∀ b : G.data.BaseBond, ScaleData.IsPlaquetteBond p b →
      |A.1 b| ≤ 4 * (G.data.L : ℝ) ^ 2 * K * E * G.chain.localSpacing y ^ 2 * R y) ∧
    |G.data.plaquetteCurl A.1 p| ≤ 4 * (G.data.L : ℝ) ^ 2 * K * E * G.chain.localSpacing y * R y := by
  obtain ⟨x, hxp, hxy⟩ := hcorner
  have hξ0 := levelSpacing_pos G.data 0
  have hL1 := one_lt_L_cast G.data
  set ξy := G.chain.localSpacing y with hξy
  have hξy0 : 0 ≤ ξy := localSpacing_nonneg _ _
  have hRy := hR0 y
  have hT : 0 ≤ K * E * R y := mul_nonneg (mul_nonneg hK hE) hRy
  have hfoot : ∀ b : G.data.BaseBond, ScaleData.IsPlaquetteBond p b → b ∈ G.bondSet →
      ∃ y₂ ∈ G.chain.shellSitesUnion, G.chain.LiesInCell b y₂ ∧
        G.chain.localSpacing y₂ ≤ (G.data.L : ℝ) * ξy ∧
        G.chain.scaledDist y y₂ ≤ 4 := by
    intro b hbp hbb
    obtain ⟨hf0, hf⟩ := anchor_props hbb
    have hfc : G.chain.anchor b ∈ p.cornerSet := by
      rcases hf with hf | hf
      · rw [hf]
        exact (plaquetteBond_ends_mem hbp).1
      · rw [hf]
        exact (plaquetteBond_ends_mem hbp).2
    exact exists_near_cell hc hw hL hy x _ hxy hf0 (corners_sup_close hξ0.le p hxp hfc)
  have hval : ∀ b : G.data.BaseBond, ScaleData.IsPlaquetteBond p b → b ∈ G.bondSet → ∀ {u : ℝ}, 0 ≤ u →
      (∀ y₂ ∈ G.chain.shellSitesUnion, G.chain.LiesInCell b y₂ →
        G.chain.localSpacing y₂ ≤ (G.data.L : ℝ) * ξy →
        G.chain.localSpacing y₂ ≤ u) →
      |A.1 b| ≤ K * E * R y * u ^ 2 := by
    intro b hbp hbb u hu hsp
    obtain ⟨y₂, hy₂, hcell, hsp₂, hd₂⟩ := hfoot b hbp hbb
    have h1 := hb y₂ hy₂ b hbb hcell
    have h2 := hRn y y₂ hd₂
    have h3 := hsp y₂ hy₂ hcell hsp₂
    have h4 : G.chain.localSpacing y₂ ^ 2 ≤ u ^ 2 :=
      pow_le_pow_left₀ (localSpacing_nonneg _ _) h3 2
    calc |A.1 b| ≤ K * G.chain.localSpacing y₂ ^ 2 * R y₂ := h1
      _ ≤ K * u ^ 2 * (E * R y) := mul_le_mul (mul_le_mul_of_nonneg_left h4 hK) h2 (hR0 y₂)
          (mul_nonneg hK (by positivity))
      _ = K * E * R y * u ^ 2 := by ring
  constructor
  · intro b hbp
    by_cases hbb : b ∈ G.bondSet
    · have h1 := hval b hbp hbb (u := (G.data.L : ℝ) * ξy) (by positivity)
        fun _ _ _ h => h
      refine h1.trans ?_
      have e : K * E * R y * ((G.data.L : ℝ) * ξy) ^ 2 =
          1 * ((G.data.L : ℝ) ^ 2 * (K * E * R y) * ξy ^ 2) := by ring
      have e' : 4 * (G.data.L : ℝ) ^ 2 * K * E * ξy ^ 2 * R y =
          4 * ((G.data.L : ℝ) ^ 2 * (K * E * R y) * ξy ^ 2) := by ring
      rw [e, e']
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    · rw [A.2 b hbb, abs_zero]
      positivity
  · by_cases hbase : (p.basePoint : G.data.Space) ∈ G.chain.set 0
    · obtain ⟨y₁, hy₁, hcell, hsp, hd⟩ := exists_near_cell hc hw hL hy x p.basePoint hxy hbase
        (corners_sup_close hξ0.le p hxp (Or.inl rfl))
      have h1 := hs y₁ hy₁ p.basePoint hcell p.dir₂ p.dir₁
      have h2 := hs y₁ hy₁ p.basePoint hcell p.dir₁ p.dir₂
      have e : G.data.plaquetteCurl A.1 p =
          G.data.forwardDiff p.dir₁ (G.data.formComponent p.dir₂ A.1) p.basePoint -
            G.data.forwardDiff p.dir₂ (G.data.formComponent p.dir₁ A.1) p.basePoint := rfl
      have h3 : K * G.chain.localSpacing y₁ * R y₁ ≤ K * ((G.data.L : ℝ) * ξy) * (E * R y) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsp hK) (hRn y y₁ hd) (hR0 y₁)
          (mul_nonneg hK (by positivity))
      rw [e]
      refine (abs_sub _ _).trans ?_
      have h4 : K * ((G.data.L : ℝ) * ξy) * (E * R y) = (G.data.L : ℝ) * ξy * (K * E * R y) := by
        ring
      have h5 : 4 * (G.data.L : ℝ) ^ 2 * K * E * ξy * R y =
          4 * (G.data.L : ℝ) ^ 2 * ξy * (K * E * R y) := by ring
      rw [h5]
      have h6 : 2 * ((G.data.L : ℝ) * ξy * (K * E * R y)) ≤
          4 * (G.data.L : ℝ) ^ 2 * ξy * (K * E * R y) := by
        have : 2 * (G.data.L : ℝ) ≤ 4 * (G.data.L : ℝ) ^ 2 := by nlinarith
        have h7 := mul_le_mul_of_nonneg_right this (mul_nonneg hξy0 hT)
        nlinarith
      linarith
    · have hz : (p.basePoint : G.data.Space) ∉ G.chain.set 1 :=
        fun h => hbase (set_antitone G.chain (Nat.zero_le 1) h)
      have hbond : ∀ b : G.data.BaseBond, ScaleData.IsPlaquetteBond p b →
          |A.1 b| ≤ K * E * R y * ((G.data.L : ℝ) * (G.data.levelSpacing 0)) ^ 2 := by
        intro b hbp
        by_cases hbb : b ∈ G.bondSet
        · refine hval b hbp hbb (by positivity) fun y₂ hy₂ hcell _ => ?_
          obtain ⟨hf0, hf⟩ := anchor_props hbb
          have hfc : G.chain.anchor b ∈ p.cornerSet := by
            rcases hf with hf | hf
            · rw [hf]
              exact (plaquetteBond_ends_mem hbp).1
            · rw [hf]
              exact (plaquetteBond_ends_mem hbp).2
          exact localSpacing_le_of_off_set_one hc hL p.basePoint _ hz
            (corners_sup_close hξ0.le p (Or.inl rfl) hfc) hy₂ hcell
        · rw [A.2 b hbb, abs_zero]
          positivity
      have b1 := hbond (ScaleData.bondFrom p.basePoint p.dir₁)
        (Or.inl (by simp [LatticePlaquette.boundaryBonds, ScaleData.bondFrom]))
      have b2 := hbond (ScaleData.bondFrom (p.basePoint + unitStep G.data.torusSide (G.data.levelSpacing 0) p.dir₁) p.dir₂)
        (Or.inl (by simp [LatticePlaquette.boundaryBonds, ScaleData.bondFrom]))
      have b3 := hbond (ScaleData.bondFrom (p.basePoint + unitStep G.data.torusSide (G.data.levelSpacing 0) p.dir₂) p.dir₁)
        (Or.inr (by simp [LatticePlaquette.boundaryBonds, ScaleData.bondFrom]))
      have b4 := hbond (ScaleData.bondFrom p.basePoint p.dir₂)
        (Or.inr (by simp [LatticePlaquette.boundaryBonds, ScaleData.bondFrom]))
      have e : G.data.plaquetteCurl A.1 p =
          (G.data.levelSpacing 0)⁻¹ * (A.1 (ScaleData.bondFrom (p.basePoint + unitStep G.data.torusSide (G.data.levelSpacing 0) p.dir₁) p.dir₂) -
              A.1 (ScaleData.bondFrom p.basePoint p.dir₂)) -
            (G.data.levelSpacing 0)⁻¹ * (A.1 (ScaleData.bondFrom (p.basePoint + unitStep G.data.torusSide (G.data.levelSpacing 0) p.dir₂) p.dir₁) -
              A.1 (ScaleData.bondFrom p.basePoint p.dir₁)) := rfl
      have hxi : (G.data.levelSpacing 0) ≤ ξy := by
        obtain ⟨n, hn, hyn⟩ := exists_shell_level G.chain hy
        rw [hξy, localSpacing_eq G.chain hc hn hyn]
        exact levelSpacing_mono G.data (Nat.zero_le n)
      set M := K * E * R y * ((G.data.L : ℝ) * (G.data.levelSpacing 0)) ^ 2 with hM
      have hinv : 0 < (G.data.levelSpacing 0)⁻¹ := inv_pos.2 hξ0
      have h8 : |G.data.plaquetteCurl A.1 p| ≤ (G.data.levelSpacing 0)⁻¹ * (4 * M) := by
        rw [e]
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos hinv, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hinv.le
        have a1 := abs_sub (A.1 (ScaleData.bondFrom (p.basePoint + unitStep G.data.torusSide (G.data.levelSpacing 0) p.dir₁) p.dir₂))
          (A.1 (ScaleData.bondFrom p.basePoint p.dir₂))
        have a2 := abs_sub (A.1 (ScaleData.bondFrom (p.basePoint + unitStep G.data.torusSide (G.data.levelSpacing 0) p.dir₂) p.dir₁))
          (A.1 (ScaleData.bondFrom p.basePoint p.dir₁))
        linarith
      refine h8.trans ?_
      have h9 : (G.data.levelSpacing 0)⁻¹ * (4 * M) =
          4 * (G.data.L : ℝ) ^ 2 * (G.data.levelSpacing 0) * (K * E * R y) := by
        rw [hM]
        field_simp
      rw [h9]
      have e2 : 4 * (G.data.L : ℝ) ^ 2 * K * E * ξy * R y =
          4 * (G.data.L : ℝ) ^ 2 * ξy * (K * E * R y) := by ring
      rw [e2]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxi (by positivity)) hT
end Cells
section Matrix
variable {G : GaugeSetting}
end Matrix
section Assembly
open GreenBounds
variable {L : ℕ} {nums : GreenConstants} {s : LevelUnitChain L}
theorem greenColumnConstant_nonneg (hbound : 1 ≤ nums.bound) :
    0 ≤ SeparatedSequences.greenColumnConstant 4 L nums.rate nums.bound := by
  unfold SeparatedSequences.greenColumnConstant
  have : 0 ≤ nums.bound := by linarith
  positivity
end Assembly
end GreenColumns
end GeneralTorus
end YangMills.Construction
