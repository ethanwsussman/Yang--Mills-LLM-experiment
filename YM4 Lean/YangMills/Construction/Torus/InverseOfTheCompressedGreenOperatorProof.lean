import YangMills.Construction.Torus.BoundsOnTheInversesOfTheCubesProof
import YangMills.Construction.Torus.GreenIdentitiesAndBlockForm
import YangMills.Construction.Torus.InverseOfTheCompressedGreenOperator
import Mathlib
set_option autoImplicit false
open Set Matrix
noncomputable section
namespace YangMills.Construction.GeneralTorus.CoarseGreenInverse
theorem inv_apply_of_diagonal_conj {X : Type} [Fintype X] [DecidableEq X] (m : X → ℝ)
    (hm : ∀ x, m x ≠ 0) (Z V S : Matrix X X ℝ)
    (hS : ∀ i j, S i j = (m i)⁻¹ * (m j)⁻¹ * Z i j) (hVZ : V * Z = 1) (i j : X) :
    S⁻¹ i j = m i * V i j * m j := by apply _root_.YangMills.Construction.GeneralTorus.CubeInverse.inv_apply_of_conj_diagonal <;> assumption
theorem posSemidef_sub_smul_one_of_le_form {X : Type} [Fintype X] [DecidableEq X]
    (S : Matrix X X ℝ) (γ : ℝ)
    (hS : S.IsSymm) (h : ∀ v : X → ℝ, γ * ∑ c, v c ^ 2 ≤ ∑ c, ∑ c', v c * S c c' * v c') :
    (S - γ • (1 : Matrix X X ℝ)).PosSemidef := by apply _root_.YangMills.Construction.GeneralTorus.CubeInverse.posSemidef_sub_smul_one <;> assumption
theorem levelSpacing_pos (D : ScaleData) (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem finite_coarseBond (W : GaugeSetting) : Finite W.CoarseBond := by apply _root_.YangMills.Construction.GeneralTorus.InnerProductsAdjointsProjections.finite_coarseBond <;> assumption
theorem isUnit_coarseGreen_of_pos (W : GaugeSetting)
    (h : ∀ f : W.CoarseField, f ≠ 0 → 0 < W.coarseInner f (W.coarseGreen f)) :
    IsUnit W.coarseGreen := by
  have := finite_coarseBond W
  rw [LinearMap.isUnit_iff_ker_eq_bot]
  refine LinearMap.ker_eq_bot'.2 fun f hf => ?_
  by_contra hne
  have hp := h f hne
  rw [hf] at hp
  simp [GaugeSetting.coarseInner] at hp
theorem mem_augmentedShell_of_mem_shellSites {D : ScaleData} (B : SeparatedChain D) {n : ℕ}
    {y : D.Space} (hy : y ∈ B.shellSites n) : y ∈ B.augmentedShell n := by
  have hl : y ∈ B.shell n := hy.2
  cases n with
  | zero =>
    change y ∈ closedComplement (B.set 1)
    unfold SeparatedChain.shell at hl
    split_ifs at hl with h0 h1
    · exact closure_mono (fun x hx => hx.2) hl
    · rw [B.eq_empty_of_gt 1 (by omega)]
      simp [closedComplement]
    · exact absurd hl (by simp)
  | succ k => exact hl
theorem coarseSpacing_div (W : GaugeSetting) (a b : W.CoarseBond) :
    GaugeSetting.coarseSpacing b / GaugeSetting.coarseSpacing a =
      (W.data.L : ℝ) ^ ((1 : ℝ) * (((b.1 : ℕ) : ℝ) - ((a.1 : ℕ) : ℝ))) := by
  have hL : 0 < W.data.L := by
    have := W.data.blocking.thirteen_le
    omega
  have hL' : (0 : ℝ) < W.data.L := by exact_mod_cast hL
  have hx := W.data.baseSpacing_pos
  rw [one_mul, Real.rpow_sub hL', Real.rpow_natCast, Real.rpow_natCast]
  unfold GaugeSetting.coarseSpacing ScaleData.levelSpacing
  field_simp
theorem abs_kernel_le_of_abs_matrix_le (x x' w g E M : ℝ) (hx : 0 < x) (hx' : 0 < x')
    (hg : 0 ≤ g) (hE : 0 ≤ E)
    (hw : |w| ≤ 2 * g * x⁻¹ * x'⁻¹ * (E * E)) (htr : x' / x * E ≤ M) :
    |(x' / x) ^ 2 * w| ≤ 2 * g * M * (x ^ 2)⁻¹ * E := by
  rw [abs_mul, abs_of_nonneg (by positivity)]
  calc (x' / x) ^ 2 * |w| ≤ (x' / x) ^ 2 * (2 * g * x⁻¹ * x'⁻¹ * (E * E)) := by gcongr
    _ = 2 * g * (x ^ 2)⁻¹ * E * (x' / x * E) := by field_simp
    _ ≤ 2 * g * (x ^ 2)⁻¹ * E * M := by gcongr
    _ = 2 * g * M * (x ^ 2)⁻¹ * E := by ring
theorem isUnit_and_abs_matrixEntry_inverse_le (W : GaugeSetting)
    (hdist : W.chain.ScaledDistIsPseudometric)
    (hrows : CoarseBondFormsAndMatricesHold)
    (hdecay : LinearAlgebra.DecayingInverse.InverseEntriesDecay)
    (hpd : W.CoarseGreenPosDef)
    (γ C δ c ε : ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hε : ε = LinearAlgebra.DecayingInverse.inverseDecayRate δ γ C c)
    (hsym : ∀ a b : W.CoarseBond, W.normalizedCoarseEntry a b = W.normalizedCoarseEntry b a)
    (hentry : ∀ a b : W.CoarseBond,
      |W.normalizedCoarseEntry a b| ≤ C * Real.exp (-δ * GaugeSetting.coarseDist a b))
    (hbetween : ∀ v : W.CoarseField,
      γ * ∑ᶠ a, v a ^ 2 ≤ ∑ᶠ a, ∑ᶠ b, v a * W.normalizedCoarseEntry a b * v b)
    (hsum : ∀ a : W.CoarseBond,
      ∑ᶠ b : W.CoarseBond, Real.exp (-(δ / 2) * GaugeSetting.coarseDist a b) ≤ c) :
    IsUnit W.coarseGreen ∧ ∀ a b : W.CoarseBond,
      |W.matrixEntry (Ring.inverse W.coarseGreen) a b| ≤
        2 * γ⁻¹ * (GaugeSetting.coarseSpacing a)⁻¹ * (GaugeSetting.coarseSpacing b)⁻¹ *
          Real.exp (-ε * GaugeSetting.coarseDist a b) := by
  classical
  have := finite_coarseBond W
  let _ : Fintype W.CoarseBond := Fintype.ofFinite W.CoarseBond
  have hunit := isUnit_coarseGreen_of_pos W hpd.2
  refine ⟨hunit, ?_⟩
  obtain ⟨-, -, hcomm, hself, htri⟩ := hdist
  let pm : PseudoMetricSpace W.CoarseBond :=
    { dist := GaugeSetting.coarseDist
      dist_self := fun a => hself _
      dist_comm := fun a b => hcomm _ _
      dist_triangle := fun a b d => htri _ _ _ }
  obtain ⟨-, -, -, -, -, -, ⟨hortho, -⟩, ⟨-, hprod, -⟩, -⟩ := hrows W
  let S : Matrix W.CoarseBond W.CoarseBond ℝ := fun a b => W.normalizedCoarseEntry a b
  have hSsym : S.IsSymm := Matrix.IsSymm.ext fun a b => hsym b a
  have hpsd : (S - γ • (1 : Matrix W.CoarseBond W.CoarseBond ℝ)).PosSemidef :=
    posSemidef_sub_smul_one_of_le_form S γ hSsym fun v => by
      have hv := hbetween v
      simpa only [finsum_eq_sum_of_fintype] using hv
  have hdec := hdecay W.CoarseBond S γ C δ c hSsym hγ hpsd hδ hentry (fun a => by
    have ha := hsum a
    rw [finsum_eq_sum_of_fintype] at ha
    exact ha)
  let Z : Matrix W.CoarseBond W.CoarseBond ℝ := fun a b => W.matrixEntry W.coarseGreen a b
  let V : Matrix W.CoarseBond W.CoarseBond ℝ := fun a b =>
    W.matrixEntry (Ring.inverse W.coarseGreen) a b
  have hcomp : Ring.inverse W.coarseGreen ∘ₗ W.coarseGreen = LinearMap.id :=
    Ring.inverse_mul_cancel _ hunit
  have hVZ : V * Z = 1 := by
    ext a b
    rw [Matrix.mul_apply]
    have h1 := hprod (Ring.inverse W.coarseGreen) W.coarseGreen a b
    rw [finsum_eq_sum_of_fintype, hcomp] at h1
    have h2 : W.matrixEntry LinearMap.id a b = (1 : Matrix W.CoarseBond W.CoarseBond ℝ) a b := by
      change W.coarseInner (W.coarseUnit a) (W.coarseUnit b) = _
      rw [hortho]
      by_cases hab : a = b
      · subst hab
        simp
      · simp [hab]
    exact h1.symm.trans h2
  have hm : ∀ a : W.CoarseBond, GaugeSetting.coarseSpacing a ≠ 0 := fun a =>
    (levelSpacing_pos W.data _).ne'
  have hinv := inv_apply_of_diagonal_conj (fun a : W.CoarseBond => GaugeSetting.coarseSpacing a)
    hm Z V S (fun _ _ => rfl) hVZ
  intro a b
  have h1 := hdec a b
  rw [hinv a b, ← hε] at h1
  have h2 : |GaugeSetting.coarseSpacing a * W.matrixEntry (Ring.inverse W.coarseGreen) a b *
      GaugeSetting.coarseSpacing b| ≤ 2 / γ * Real.exp (-ε * GaugeSetting.coarseDist a b) := h1
  have hpa : 0 < GaugeSetting.coarseSpacing a := levelSpacing_pos W.data _
  have hpb : 0 < GaugeSetting.coarseSpacing b := levelSpacing_pos W.data _
  have h3 : |W.matrixEntry (Ring.inverse W.coarseGreen) a b| =
      (GaugeSetting.coarseSpacing a)⁻¹ * (GaugeSetting.coarseSpacing b)⁻¹ *
        |GaugeSetting.coarseSpacing a * W.matrixEntry (Ring.inverse W.coarseGreen) a b *
          GaugeSetting.coarseSpacing b| := by
    rw [abs_mul, abs_mul, abs_of_pos hpa, abs_of_pos hpb]
    field_simp
  rw [h3]
  calc (GaugeSetting.coarseSpacing a)⁻¹ * (GaugeSetting.coarseSpacing b)⁻¹ *
        |GaugeSetting.coarseSpacing a * W.matrixEntry (Ring.inverse W.coarseGreen) a b *
          GaugeSetting.coarseSpacing b|
      ≤ (GaugeSetting.coarseSpacing a)⁻¹ * (GaugeSetting.coarseSpacing b)⁻¹ *
          (2 / γ * Real.exp (-ε * GaugeSetting.coarseDist a b)) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (inv_nonneg.2 hpa.le) (inv_nonneg.2 hpb.le))
    _ = 2 * γ⁻¹ * (GaugeSetting.coarseSpacing a)⁻¹ * (GaugeSetting.coarseSpacing b)⁻¹ *
          Real.exp (-ε * GaugeSetting.coarseDist a b) := by ring
theorem statement_holds
    (hcells : SeparatedChainStructure)
    (hfloors : InverseBoundsStatement)
    (hrows : CoarseBondFormsAndMatricesHold)
    (halg : GreenIdentitiesAndBlockFormHold)
    (hcols : GreenColumnsStatement)
    (hdecay : LinearAlgebra.DecayingInverse.InverseEntriesDecay)
    (hread : GreenBoundsStatement) :
    CoarseGreenInverse.Statement := by
  intro L hL s hfl
  obtain ⟨hM, hR⟩ := hfl
  have hδ : 0 < (GreenBounds.chosen L).rate := (hread L hL).rate_pos
  obtain ⟨hpos, hle, hfloor⟩ := hfloors.1 L hL
  have hLM : L ≤ s.data.blockCount := by
    have h : (L : ℝ) ≤ (s.data.blockCount : ℝ) := (le_max_right _ _).trans hM
    exact_mod_cast h
  obtain ⟨hsums, htrade⟩ := hfloors.2 s.setting hLM hR
  have hab : (GreenBounds.chosen L).AboveLowerBounds s :=
    ⟨(le_max_left _ _).trans hM, hfloor.trans hR⟩
  obtain ⟨-, -, -, hmat⟩ := hcols L s hab hLM
  obtain ⟨-, -, -, hpd, -⟩ := halg s.setting hLM
  have hγ : 0 < SeparatedSequences.compressedGreenLowerBound 4 1 := by
    unfold SeparatedSequences.compressedGreenLowerBound SeparatedSequences.testFormEnergyConstant
    positivity
  obtain ⟨⟨hsite, -⟩, -, -, -, -, -, -, ⟨hker, -⟩, -⟩ := hrows s.setting
  have hsites : ∀ c : s.setting.CoarseBond,
      GaugeSetting.coarseAnchor c ∈ s.setting.chain.shellSites c.1 := fun c => (hsite c).2
  have hall : ∀ c : s.setting.CoarseBond,
      GaugeSetting.coarseAnchor c ∈ s.setting.chain.shellSitesUnion := fun c =>
    mem_iUnion₂.2 ⟨c.1, mem_Iic.2 (Nat.lt_succ_iff.1 c.1.2), hsites c⟩
  have hrate : SeparatedSequences.inverseDecayRate 4 L (GreenBounds.chosen L).rate
        (GreenBounds.chosen L).bound =
      LinearAlgebra.DecayingInverse.inverseDecayRate (GreenBounds.chosen L).rate
        (SeparatedSequences.compressedGreenLowerBound 4 1)
        (SeparatedSequences.compressedEntryConstant 4 L (GreenBounds.chosen L).rate
          (GreenBounds.chosen L).bound)
        (2 * 4 * SeparatedSequences.expSumConstant 4 L ((GreenBounds.chosen L).rate / 2)) := by
    unfold SeparatedSequences.inverseDecayRate LinearAlgebra.DecayingInverse.inverseDecayRate
    have hden : 8 * ((4 : ℕ) : ℝ) *
          SeparatedSequences.compressedEntryConstant 4 L (GreenBounds.chosen L).rate
            (GreenBounds.chosen L).bound *
          SeparatedSequences.expSumConstant 4 L ((GreenBounds.chosen L).rate / 2) =
        4 * SeparatedSequences.compressedEntryConstant 4 L (GreenBounds.chosen L).rate
            (GreenBounds.chosen L).bound *
          (2 * 4 * SeparatedSequences.expSumConstant 4 L ((GreenBounds.chosen L).rate / 2)) := by
      push_cast
      ring
    rw [hden]
  have hα : 1 / 2 * InverseBounds.decayRateOfInverse L ≤ (GreenBounds.chosen L).rate / 2 := by
    linarith
  obtain ⟨hunit, hbound⟩ := isUnit_and_abs_matrixEntry_inverse_le s.setting
    (hcells s.setting.data s.setting.chain).2.2.2.2.2.2.2.2 hrows hdecay hpd
    (SeparatedSequences.compressedGreenLowerBound 4 1)
    (SeparatedSequences.compressedEntryConstant 4 L (GreenBounds.chosen L).rate
      (GreenBounds.chosen L).bound)
    (GreenBounds.chosen L).rate
    (2 * 4 * SeparatedSequences.expSumConstant 4 L ((GreenBounds.chosen L).rate / 2))
    (SeparatedSequences.inverseDecayRate 4 L (GreenBounds.chosen L).rate
      (GreenBounds.chosen L).bound) hγ hδ hrate
    hmat.symm hmat.entry_le (fun v => (hmat.quadratic_bounds v).1)
    (fun a => (hsums _ hα _ (hall a)).2)
  refine ⟨hpd.1, hpd.2, hunit, hbound, fun a b => ?_⟩
  rw [hker]
  have hK : SeparatedSequences.inverseKernelConstant 4 L =
      2 * (SeparatedSequences.compressedGreenLowerBound 4 1)⁻¹ * (L : ℝ) := by
    unfold SeparatedSequences.inverseKernelConstant
    have h1 : ((4 : ℕ) : ℝ) / 2 - 1 = 1 := by norm_num
    rw [h1, Real.rpow_one]
  rw [hK]
  have hpa : 0 < GaugeSetting.coarseSpacing a := levelSpacing_pos s.setting.data _
  have hpb : 0 < GaugeSetting.coarseSpacing b := levelSpacing_pos s.setting.data _
  have hE : Real.exp (-SeparatedSequences.inverseDecayRate 4 L (GreenBounds.chosen L).rate
        (GreenBounds.chosen L).bound * GaugeSetting.coarseDist a b) =
      Real.exp (-(1 / 2 * SeparatedSequences.inverseDecayRate 4 L (GreenBounds.chosen L).rate
        (GreenBounds.chosen L).bound) * GaugeSetting.coarseDist a b) *
      Real.exp (-(1 / 2 * SeparatedSequences.inverseDecayRate 4 L (GreenBounds.chosen L).rate
        (GreenBounds.chosen L).bound) * GaugeSetting.coarseDist a b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hb := hbound a b
  rw [hE] at hb
  have htr : GaugeSetting.coarseSpacing b / GaugeSetting.coarseSpacing a *
      Real.exp (-(1 / 2 * SeparatedSequences.inverseDecayRate 4 L (GreenBounds.chosen L).rate
        (GreenBounds.chosen L).bound) * GaugeSetting.coarseDist a b) ≤ (L : ℝ) := by
    have h := htrade a.1 b.1 (Nat.lt_succ_iff.1 a.1.2) (Nat.lt_succ_iff.1 b.1.2)
      (GaugeSetting.coarseAnchor a) (mem_augmentedShell_of_mem_shellSites _ (hsites a))
      (GaugeSetting.coarseAnchor b) (mem_augmentedShell_of_mem_shellSites _ (hsites b)) 1
      (1 / 2 * SeparatedSequences.inverseDecayRate 4 L (GreenBounds.chosen L).rate
        (GreenBounds.chosen L).bound)
      (by norm_num) le_rfl
    have h' : ((L : ℕ) : ℝ) ^ |(1 : ℝ)| = (L : ℝ) := by
      rw [abs_one, Real.rpow_one]
    rw [coarseSpacing_div s.setting a b]
    exact h.trans_eq h'
  exact abs_kernel_le_of_abs_matrix_le _ _ _ _ _ _ hpa hpb (inv_nonneg.2 hγ.le)
    (Real.exp_pos _).le hb htr
end YangMills.Construction.GeneralTorus.CoarseGreenInverse
