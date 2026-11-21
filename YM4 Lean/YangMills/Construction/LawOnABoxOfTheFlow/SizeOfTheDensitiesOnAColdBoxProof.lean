import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ColdStepAtMirrorFrames.AxialGaugeOfATop
import YangMills.Construction.ColdStepAtMirrorFrames.NoFirstOrderAtTheFlatField
import YangMills.Construction.LawInAState.WilsonSharesAreACurvatureFamilyProof
import YangMills.Construction.LawOnABoxOfTheFlow.SizeOfTheDensitiesOnAColdBox
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.BoxEvents.ColdBoxDensityBound
section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
private theorem iteratedFDeriv_comp_clm (G : E → ℝ) (L : F →L[ℝ] E) (q : F) {k : ℕ} (hk : k ≤ 3)
    (hG : ContDiffAt ℝ 3 G (L q)) (v : Fin k → F) :
    iteratedFDeriv ℝ k (fun z => G (L z)) q v = iteratedFDeriv ℝ k G (L q) (fun l => L (v l)) := by apply _root_.YangMills.Construction.AbelianSecondOrder.iteratedFDeriv_comp_linear <;> assumption
private theorem iteratedDeriv_along_ray (G : E → ℝ) (α : E) (t : ℝ) {k : ℕ} (hk : k ≤ 3)
    (hG : ContDiffAt ℝ 3 G (t • α)) :
    iteratedDeriv k (fun s : ℝ => G (s • α)) t = iteratedFDeriv ℝ k G (t • α) (fun _ => α) := by apply _root_.YangMills.Construction.AbelianSecondOrder.iteratedDeriv_along_line <;> assumption
private theorem multilinear_apply_const_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => ι → ℝ) ℝ) (α : ι → ℝ) :
    T (fun _ => α) = ∑ c : Fin k → ι, (∏ l, α (c l)) * T (fun l => Pi.single (c l) 1) := by apply _root_.YangMills.Construction.AbelianSecondOrder.multilinear_apply_const_eq_sum <;> assumption
private theorem abs_taylor_one_le (g : ℝ → ℝ) {M : ℝ}
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 g t)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 2 g t| ≤ M) :
    |g 1 - g 0 - iteratedDeriv 1 g 0| ≤ M := by
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc one_pos
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.2 zero_le_one
  have hon : ContDiffOn ℝ ((1 : ℕ) + 1) g (Set.Icc 0 1) := fun t ht => by
    have h2 : ContDiffAt ℝ 2 g t := (hC t ht).of_le (by norm_num)
    have := h2.contDiffWithinAt (s := Set.Icc 0 1)
    exact_mod_cast this
  have h1 := taylor_mean_remainder_bound (n := 1) (C := M) zero_le_one hon (Set.right_mem_Icc.2 zero_le_one)
    (fun y hy => by
      have e := iteratedDerivWithin_eq_iteratedDeriv (n := 1 + 1) hu
        (by exact_mod_cast (hC y hy).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) hy
      rw [e]
      exact hM y hy)
  have e1 : iteratedDerivWithin 1 g (Set.Icc 0 1) 0 = iteratedDeriv 1 g 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (n := 1) hu ((hC 0 h0).of_le (by norm_num)) h0
  have t1 : taylorWithinEval g 1 (Set.Icc 0 1) 0 1 = g 0 + iteratedDeriv 1 g 0 := by
    have a0 := taylorWithinEval_succ g 0 (Set.Icc 0 1) 0 1
    rw [taylor_within_zero_eval] at a0
    have b0 : taylorWithinEval g 1 (Set.Icc 0 1) 0 1 = taylorWithinEval g (0 + 1) (Set.Icc 0 1) 0 1 := rfl
    rw [b0, a0]
    simp [e1]
  have e4 : M * ((1 : ℝ) - 0) ^ (1 + 1) / ((Nat.factorial 1 : ℕ) : ℝ) = M := by
    norm_num [Nat.factorial]
  rw [Real.norm_eq_abs, t1, e4] at h1
  have e3 : g 1 - g 0 - iteratedDeriv 1 g 0 = g 1 - (g 0 + iteratedDeriv 1 g 0) := by ring
  rw [e3]
  exact h1
end Calculus
section Angles
set_option linter.unusedSectionVars false
variable {n : ℕ}
private def angleField (U : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions)
    (a : TorusFields.TorusBond n → ℝ) : TorusFields.TorusField n :=
  fun x i => BlockAverages.expUnit (a (x, i) • U (x, i))
private theorem angleField_zero (U : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) :
    angleField U (0 : TorusFields.TorusBond n → ℝ) = TorusFields.trivialField n := by
  funext x i
  simp [angleField, TorusFields.trivialField, TorusFields.expUnit_zero]
variable [NeZero n]
private def angleIncrement {k : ℕ} (c : Fin k → TorusFields.TorusBond n) :
    (Fin k → ℝ) →L[ℝ] (TorusFields.TorusBond n → ℝ) :=
  ContinuousLinearMap.pi fun b => ∑ l, if c l = b then ContinuousLinearMap.proj l else 0
private theorem angleIncrement_apply {k : ℕ} (c : Fin k → TorusFields.TorusBond n) (σ : Fin k → ℝ)
    (b : TorusFields.TorusBond n) :
    angleIncrement c σ b = ∑ l, if c l = b then σ l else 0 := by
  simp only [angleIncrement, ContinuousLinearMap.coe_pi', FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
private theorem angleIncrement_single {k : ℕ} (c : Fin k → TorusFields.TorusBond n) (l : Fin k) :
    angleIncrement c (Pi.single l 1) = Pi.single (c l) 1 := by
  ext b
  rw [angleIncrement_apply, Finset.sum_eq_single l]
  · simp [Pi.single_apply, eq_comm]
  · intro l' _ hl'
    simp [hl']
  · simp
private theorem perturb_angleField {k : ℕ} (c : Fin k → TorusFields.TorusBond n)
    (U : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (σ : Fin k → ℝ)
    (p : TorusFields.TorusBond n → ℝ) :
    TorusFields.perturb c (U ∘ c) σ (angleField U p) = angleField U (p + angleIncrement c σ) := by
  funext x i
  have h1 : (∑ l, if c l = (x, i) then σ l • (U ∘ c) l else 0) = (angleIncrement c σ (x, i)) • U (x, i) := by
    rw [angleIncrement_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with h
    · simp [h]
    · simp
  simp only [TorusFields.perturb, angleField, h1, TorusFrame.expUnit_smul_mul, Pi.add_apply, add_comm]
private def onAngles (f : TorusFields.TorusField n → ℝ)
    (U : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (a : TorusFields.TorusBond n → ℝ) : ℝ :=
  f (angleField U a)
private theorem contDiffAt_onAngles (f : TorusFields.TorusField n → ℝ)
    (U : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (p : TorusFields.TorusBond n → ℝ)
    (hf : TorusFields.ContDiffThreeAt f (angleField U p)) : ContDiffAt ℝ 3 (onAngles f U) p := by
  classical
  let e := Fintype.equivFin (TorusFields.TorusBond n)
  let c : Fin (Fintype.card (TorusFields.TorusBond n)) → TorusFields.TorusBond n := e.symm
  have h0 := hf _ c (U ∘ c)
  let T : (TorusFields.TorusBond n → ℝ) →L[ℝ] (Fin (Fintype.card (TorusFields.TorusBond n)) → ℝ) :=
    ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (c l)
  have hT : ∀ a, angleIncrement c (T a) = a := by
    intro a
    ext b
    rw [angleIncrement_apply, Finset.sum_eq_single (e b)]
    · simp [c, T]
    · intro l _ hl
      have : c l ≠ b := fun hb => hl (by simp [← hb, c])
      simp [this]
    · simp
  have key : onAngles f U = fun q =>
      (fun σ => f (TorusFields.perturb c (U ∘ c) σ (angleField U p))) (T (q - p)) := by
    funext q
    simp only [onAngles]
    rw [perturb_angleField, hT]
    congr 2
    abel
  have hl : ContDiffAt ℝ 3 (fun q => T (q - p)) p := by
    have : ContDiff ℝ 3 (fun q => T (q - p)) := T.contDiff.comp (contDiff_id.sub contDiff_const)
    exact this.contDiffAt
  have h0' : ContDiffAt ℝ 3 (fun σ => f (TorusFields.perturb c (U ∘ c) σ (angleField U p))) (T (p - p)) := by
    simpa using h0
  rw [key]
  exact ContDiffAt.comp (g := fun σ => f (TorusFields.perturb c (U ∘ c) σ (angleField U p)))
    (f := fun q => T (q - p)) p h0' hl
private theorem mixedDeriv_angleField (f : TorusFields.TorusField n → ℝ)
    (U : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (p : TorusFields.TorusBond n → ℝ)
    (hf : TorusFields.ContDiffThreeAt f (angleField U p))
    {k : ℕ} (hk : k ≤ 3) (c : Fin k → TorusFields.TorusBond n) :
    TorusFields.mixedDeriv f (angleField U p) c (U ∘ c) =
      iteratedFDeriv ℝ k (onAngles f U) p (fun l => Pi.single (c l) 1) := by
  have h0 := contDiffAt_onAngles f U p hf
  have e1 : (fun σ : Fin k → ℝ => f (TorusFields.perturb c (U ∘ c) σ (angleField U p))) =
      fun σ => (fun a => onAngles f U (p + a)) (angleIncrement c σ) := by
    funext σ
    simp only [onAngles]
    rw [perturb_angleField]
  unfold TorusFields.mixedDeriv
  rw [e1]
  have h1 : ContDiffAt ℝ 3 (fun a => onAngles f U (p + a)) (angleIncrement c 0) := by
    have : ContDiffAt ℝ 3 (onAngles f U) (p + angleIncrement c 0) := by simpa using h0
    exact this.comp _ (contDiff_const.add contDiff_id).contDiffAt
  rw [iteratedFDeriv_comp_clm (fun a => onAngles f U (p + a)) (angleIncrement c) 0 hk h1]
  have e2 : (fun l => angleIncrement c (Pi.single l 1 : Fin k → ℝ)) =
      fun l => (Pi.single (c l) 1 : TorusFields.TorusBond n → ℝ) := by
    funext l
    exact angleIncrement_single c l
  rw [e2, map_zero, iteratedFDeriv_comp_add_left]
  simp
end Angles
section FrameTransfer
set_option linter.unusedSectionVars false
variable {m : ℕ} [NeZero m]
private abbrev cellFrame (m : ℕ) : BlockAverages.BlockFrame := TorusFields.torusFrame 1 0 m
private abbrev toCell (z : TorusFields.TorusSite m) : (cellFrame m).Cell :=
  StepCosts.torusSiteInFrame (cellFrame m) (cellFrame m).top z
private theorem toCell_add_unitStep (z : TorusFields.TorusSite m) (i : Fin 4) :
    toCell (z + TorusFields.unitStep m i) = toCell z + BlockAverages.unitStep (cellFrame m).top i := by
  apply TorusFrame.siteOfCell_injective
  rw [TorusFrame.siteOfCell_add, TorusFrame.siteOfCell_torusSiteInFrame, TorusFrame.siteOfCell_torusSiteInFrame,
    TorusFrame.siteOfCell_unitStep]
private theorem toCell_add_siteOfInt (z : TorusFields.TorusSite m) (h : Fin 4 → ℤ) :
    toCell z + BlockAverages.siteOfCoords (cellFrame m).top h = toCell (z + TorusFields.siteOfInt h) := by
  apply TorusFrame.siteOfCell_injective
  rw [TorusFrame.siteOfCell_add, TorusFrame.siteOfCell_torusSiteInFrame, TorusFrame.siteOfCell_torusSiteInFrame,
    TorusFrame.siteOfCell_siteOfCoords]
private theorem toCell_injective {z z' : TorusFields.TorusSite m} (h : toCell z = toCell z') : z = z' := by
  have := congrArg TorusFrame.siteOfCell h
  rwa [TorusFrame.siteOfCell_torusSiteInFrame, TorusFrame.siteOfCell_torusSiteInFrame] at this
private theorem exists_axial_gauge_near_one (hax : ColdStepAtMirrorFrames.AxialGaugeBondBound)
    (W : TorusFields.TorusField m) (y : TorusFields.TorusSite m) {s : ℝ} (hs : 0 < s)
    (hc : TorusFields.IsCold s W) :
    ∃ g : TorusFields.TorusSite m → BlockAverages.UnitQuaternion, ∀ b : TorusFields.TorusBond m,
      2 * (TorusFields.supDist b.1 y + 1) + 2 < m →
      ‖((TorusFields.gaugeTransform g W b.1 b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        3 * ((TorusFields.supDist b.1 y + 1 : ℕ) : ℝ) * s := by
  set V := TorusFields.readAtLevel (cellFrame m) (cellFrame m).top W with hV
  have hcold : ColdStepAtMirrorFrames.IsSmallCurvature s V := by
    rintro ⟨x, μ, ν⟩ hlt
    rw [hV, TorusFrame.plaquetteDefect_torusFrame]
    exact hc _ _ _ hlt
  refine ⟨fun z => ColdStepAtMirrorFrames.axialGaugeHolonomy V (toCell y) (toCell z), fun b hb => ?_⟩
  obtain ⟨z, i⟩ := b
  simp only at hb ⊢
  set h := MirrorDensities.offset y z with hh
  have hz : y + TorusFields.siteOfInt h = z := MirrorDensities.add_siteOfInt_offset y z
  have hoff : ∀ l, |h l| ≤ (TorusFields.supDist z y : ℤ) := fun l => MirrorDensities.abs_offset_le y z l
  have hbox : BlockAverages.BondWithinRadius (TorusFields.supDist z y + 1) (h, i) := by
    constructor
    · intro l
      have := hoff l
      simp only
      push_cast
      omega
    · intro l
      have h1 := hoff l
      have h2 : |(Pi.single i 1 : Fin 4 → ℤ) l| ≤ 1 := by
        by_cases e : l = i
        · subst e; simp
        · simp [Pi.single_eq_of_ne e]
      have h3 := abs_add_le (h l) ((Pi.single i 1 : Fin 4 → ℤ) l)
      simp only [Pi.add_apply]
      push_cast
      omega
  have key := hax (cellFrame m) V (toCell y) s (TorusFields.supDist z y + 1)
    (fun _ => by simpa [TorusFields.torusFrame] using hb) hs hcold (h, i) hbox
  simp only at key
  have e1 : toCell y + BlockAverages.siteOfCoords (cellFrame m).top h = toCell z := by
    rw [toCell_add_siteOfInt, hz]
  rw [e1] at key
  have e2 : BlockAverages.gaugeTransform (ColdStepAtMirrorFrames.axialGaugeHolonomy V (toCell y)) V (toCell z) i =
      TorusFields.gaugeTransform (fun z => ColdStepAtMirrorFrames.axialGaugeHolonomy V (toCell y) (toCell z)) W z i := by
    simp only [BlockAverages.gaugeTransform, TorusFields.gaugeTransform]
    rw [toCell_add_unitStep, hV, TorusFrame.readAtLevel_torusFrame, TorusFrame.siteOfCell_torusSiteInFrame]
  rw [e2] at key
  exact key
private def torusFieldOfCells (V : (cellFrame m).GaugeField (cellFrame m).top) : TorusFields.TorusField m :=
  fun z i => V (toCell z) i
private theorem readAtLevel_torusFieldOfCells (V : (cellFrame m).GaugeField (cellFrame m).top) :
    TorusFields.readAtLevel (cellFrame m) (cellFrame m).top (torusFieldOfCells V) = V := by
  funext x i
  rw [TorusFrame.readAtLevel_torusFrame]
  show V (toCell (TorusFrame.siteOfCell x)) i = V x i
  have e : toCell (TorusFrame.siteOfCell x) = x :=
    TorusFrame.torusSiteInFrame_siteOfCell (L := 1) (t := 0) (m := m) x
  rw [e]
private theorem mixedDeriv_one_trivialField_eq_zero (hno : ColdStepAtMirrorFrames.FirstDerivVanishesAtUniform)
    (G : TorusFields.TorusField m → ℝ) {s : ℝ} (hs : 0 < s)
    (hinv : ∀ (W : TorusFields.TorusField m) (g : TorusFields.TorusSite m → BlockAverages.UnitQuaternion),
      TorusFields.IsCold s W → G (TorusFields.gaugeTransform g W) = G W)
    (c : Fin 1 → TorusFields.TorusBond m) (X : Fin 1 → BlockAverages.imaginaryQuaternions)
    (hX : BlockAverages.AreUnitVectors X) :
    TorusFields.mixedDeriv G (TorusFields.trivialField m) c X = 0 := by
  have hg : ∀ (V : (cellFrame m).GaugeField (cellFrame m).top)
      (γ : (cellFrame m).Site (cellFrame m).top → BlockAverages.UnitQuaternion),
      torusFieldOfCells (BlockAverages.gaugeTransform γ V) =
        TorusFields.gaugeTransform (fun z => γ (toCell z)) (torusFieldOfCells V) := by
    intro V γ
    funext z i
    simp only [torusFieldOfCells, BlockAverages.gaugeTransform, TorusFields.gaugeTransform]
    rw [toCell_add_unitStep]
  have hcold : ∀ V : (cellFrame m).GaugeField (cellFrame m).top,
      ColdStepAtMirrorFrames.IsSmallCurvature s V → TorusFields.IsCold s (torusFieldOfCells V) := by
    intro V hV x μ ν hlt
    have h1 := hV (toCell x, μ, ν) hlt
    have h2 := TorusFrame.plaquetteDefect_torusFrame (L := 1) (t := 0) (torusFieldOfCells V) (toCell x) μ ν
    rw [readAtLevel_torusFieldOfCells, TorusFrame.siteOfCell_torusSiteInFrame] at h2
    rw [← h2]
    exact h1
  have h := hno (cellFrame m) (cellFrame m).top (fun V => G (torusFieldOfCells V)) s
    (fun l => (toCell (c l).1, (c l).2)) X hs
    (fun V γ hV => by
      show G (torusFieldOfCells (BlockAverages.gaugeTransform γ V)) = G (torusFieldOfCells V)
      rw [hg]
      exact hinv _ _ (hcold V hV)) hX
  have e : (fun τ : Fin 1 → ℝ => G (torusFieldOfCells (ColdStepAtMirrorFrames.leftTranslate
      (ColdStepAtMirrorFrames.bondSpread (fun l => (toCell (c l).1, (c l).2)) X τ)
      (ColdStepAtMirrorFrames.uniformField (cellFrame m) (cellFrame m).top)))) =
        fun τ => G (TorusFields.perturb c X τ (TorusFields.trivialField m)) := by
    funext τ
    congr 1
    funext z i
    simp only [torusFieldOfCells, ColdStepAtMirrorFrames.leftTranslate, ColdStepAtMirrorFrames.uniformField,
      TorusFields.perturb, TorusFields.trivialField, ColdStepAtMirrorFrames.bondSpread, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : c l = (z, i)
    · simp [hl]
    · have : ¬ ((toCell (c l).1, (c l).2) = (toCell z, i)) := fun e => hl (by
        have e1 := toCell_injective (congrArg Prod.fst e)
        have e2 := congrArg Prod.snd e
        exact Prod.ext e1 e2)
      rw [if_neg this, if_neg hl]
  unfold ColdStepAtMirrorFrames.bondDeriv at h
  unfold TorusFields.mixedDeriv
  rw [e] at h
  exact h
end FrameTransfer
section SiteTaylor
set_option linter.unusedSectionVars false
variable {ℓ : TorusLumps.StepParameters} {t : ℕ} {x : ℝ} {D : TorusLumps.TorusFunctional}
  {f : TorusLumps.LocalDensity}
private theorem weightRate_pos (hfit : ℓ.Admissible) : 0 < ℓ.weightRate := by apply _root_.YangMills.Construction.AbelianSecondOrder.weightRate_pos <;> assumption
private theorem div_weight_le_exp {C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    C / ℓ.weight m ≤ C * Real.exp (-ℓ.weightRate * m) := by apply _root_.YangMills.Construction.MirrorDensities.div_weight_le_mul_exp <;> assumption
variable {m : ℕ} [NeZero m]
private theorem abs_centered_angleField_le (hno : ColdStepAtMirrorFrames.FirstDerivVanishesAtUniform)
    (hfit : ℓ.Admissible) (hrow : TorusLumps.ColdExpansion ℓ t x D f)
    (hm : ℓ.n₀ ≤ m) (y : TorusFields.TorusSite m) (U : TorusFields.TorusBond m → BlockAverages.imaginaryQuaternions)
    (a : TorusFields.TorusBond m → ℝ) (hU : ∀ b, ‖U b‖ = 1)
    (hcold : ∀ τ ∈ Set.Icc (0 : ℝ) 1, TorusFields.IsCold ℓ.threshold (angleField U (τ • a))) :
    |TorusLumps.centered f m y (angleField U a)| ≤
      ℓ.E * (∑ b : TorusFields.TorusBond m, |a b| *
        Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y b.1)) ^ 2 := by
  set G := onAngles (f m y) U with hG
  set g : ℝ → ℝ := fun s => G (s • a) with hg
  have hsm : ∀ τ ∈ Set.Icc (0 : ℝ) 1, TorusFields.ContDiffThreeAt (f m y) (angleField U (τ • a)) :=
    fun τ h => hrow.smooth m hm y _ (hcold τ h)
  have hGc : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 G (τ • a) :=
    fun τ h => contDiffAt_onAngles _ _ _ (hsm τ h)
  have hC : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 g τ := fun τ h =>
    ContDiffAt.comp (g := G) (f := fun s : ℝ => s • a) τ (hGc τ h)
      (contDiff_id.smul contDiff_const).contDiffAt
  have expand : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ k : ℕ, k ≤ 3 → iteratedDeriv k g τ =
      ∑ c : Fin k → TorusFields.TorusBond m,
        (∏ l, a (c l)) * TorusFields.mixedDeriv (f m y) (angleField U (τ • a)) c (U ∘ c) := by
    intro τ h k hk
    rw [hg, iteratedDeriv_along_ray G a τ hk (hGc τ h), multilinear_apply_const_eq_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mixedDeriv_angleField _ _ _ (hsm τ h) hk c]
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.2 zero_le_one
  have h1 : iteratedDeriv 1 g 0 = 0 := by
    rw [expand 0 h0 1 (by norm_num)]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [zero_smul, angleField_zero,
      mixedDeriv_one_trivialField_eq_zero hno (f m y) hfit.σ_pos (fun W g hW => hrow.gauge m hm y g W hW)
        c (U ∘ c) (fun l => hU _),
      mul_zero]
  set S := ∑ b : TorusFields.TorusBond m, |a b| *
    Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y b.1) with hS
  have hρ := weightRate_pos hfit
  have hE := hfit.E_pos
  have h2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 2 g τ| ≤ ℓ.E * S ^ 2 := by
    intro τ h
    rw [expand τ h 2 (by norm_num), hS, Fintype.sum_pow, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    have hd := hrow.decay m hm y _ (hcold τ h) 2 c (U ∘ c) (by norm_num) (by norm_num) (fun l => hU _)
    rw [if_neg (by norm_num)] at hd
    have hsp : ∀ l : Fin 2, TorusFields.supDist y (c l).1 ≤ TorusFields.supportDiam y c := fun l =>
      le_max_of_le_left (Finset.le_sup (f := fun l : Fin 2 => TorusFields.supDist y (c l).1) (Finset.mem_univ l))
    have hw := div_weight_le_exp (ℓ := ℓ) hE.le (TorusFields.supportDiam y c)
    have hex : Real.exp (-ℓ.weightRate * TorusFields.supportDiam y c) ≤
        Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y (c 0).1) *
          Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y (c 1).1) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have a0 : (TorusFields.supDist y (c 0).1 : ℝ) ≤ TorusFields.supportDiam y c := by exact_mod_cast hsp 0
      have a1 : (TorusFields.supDist y (c 1).1 : ℝ) ≤ TorusFields.supportDiam y c := by exact_mod_cast hsp 1
      nlinarith
    rw [abs_mul, Finset.abs_prod, Fin.prod_univ_two, Fin.prod_univ_two]
    have hdm := hd.trans hw
    have hdm2 : |TorusFields.mixedDeriv (f m y) (angleField U (τ • a)) c (U ∘ c)| ≤
        ℓ.E * (Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y (c 0).1) *
          Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y (c 1).1)) :=
      hdm.trans (mul_le_mul_of_nonneg_left hex hE.le)
    calc |a (c 0)| * |a (c 1)| * |TorusFields.mixedDeriv (f m y) (angleField U (τ • a)) c (U ∘ c)|
        ≤ |a (c 0)| * |a (c 1)| * (ℓ.E * (Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y (c 0).1) *
            Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y (c 1).1))) :=
          mul_le_mul_of_nonneg_left hdm2 (by positivity)
      _ = ℓ.E * (|a (c 0)| * Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y (c 0).1) *
            (|a (c 1)| * Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y (c 1).1))) := by ring
  have hT := abs_taylor_one_le g hC h2
  rw [h1, sub_zero] at hT
  have e1 : g 1 = f m y (angleField U a) := by simp [hg, hG, onAngles]
  have e0 : g 0 = f m y (TorusFields.trivialField m) := by
    have : g 0 = f m y (angleField U ((0 : ℝ) • a)) := rfl
    rw [this, zero_smul, angleField_zero]
  rw [e1, e0] at hT
  exact hT
end SiteTaylor
section SiteBound
set_option linter.unusedSectionVars false
open GaugeFixing
private theorem norm_minimalLog_le_two_mul (g : BlockAverages.UnitQuaternion) :
    ‖((LumpContours.minimalLog g : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.GaugeFixing.norm_minimalLog_le <;> assumption
private theorem exists_eq_smul_unit (X : BlockAverages.imaginaryQuaternions) :
    ∃ (a : ℝ) (U : BlockAverages.imaginaryQuaternions), ‖U‖ = 1 ∧ X = a • U ∧ |a| = ‖X‖ := by apply _root_.YangMills.Construction.TorusLumps.SumOfFourCurvature.exists_smul_unit <;> assumption
variable {ℓ : TorusLumps.StepParameters} {t : ℕ} {x : ℝ} {D : TorusLumps.TorusFunctional}
  {f : TorusLumps.LocalDensity}
private def bondSumBound (ℓ : TorusLumps.StepParameters) : ℝ :=
  4 * (4 / ℓ.weightRate + 1) * ExponentialSums.expLatticeSum (ℓ.weightRate / 4)
variable {m : ℕ} [NeZero m]
private theorem sum_bonds_weighted_le (hρ : 0 < ℓ.weightRate) (y : TorusFields.TorusSite m) :
    ∑ b : TorusFields.TorusBond m, ((TorusFields.supDist b.1 y + 1 : ℕ) : ℝ) *
      Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y b.1) ≤ bondSumBound ℓ := by
  have hpt : ∀ z : TorusFields.TorusSite m, ((TorusFields.supDist z y + 1 : ℕ) : ℝ) *
      Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y z) ≤
      (4 / ℓ.weightRate + 1) * Real.exp (-(ℓ.weightRate / 4) * TorusFields.supDist z y) := by
    intro z
    rw [TorusFields.supDist_comm y z]
    push_cast
    set d : ℝ := (TorusFields.supDist z y : ℝ) with hd
    have h1 : ℓ.weightRate * d / 4 + 1 ≤ Real.exp (ℓ.weightRate * d / 4) := Real.add_one_le_exp _
    have h0 : 0 ≤ ℓ.weightRate * d / 4 := by positivity
    have h2 : d + 1 ≤ (4 / ℓ.weightRate + 1) * Real.exp (ℓ.weightRate * d / 4) := by
      have e1 : d = 4 / ℓ.weightRate * (ℓ.weightRate * d / 4) := by field_simp
      have e2 : 4 / ℓ.weightRate * (ℓ.weightRate * d / 4) ≤ 4 / ℓ.weightRate * Real.exp (ℓ.weightRate * d / 4) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    calc (d + 1) * Real.exp (-(ℓ.weightRate / 2) * d)
        ≤ ((4 / ℓ.weightRate + 1) * Real.exp (ℓ.weightRate * d / 4)) * Real.exp (-(ℓ.weightRate / 2) * d) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = (4 / ℓ.weightRate + 1) * Real.exp (-(ℓ.weightRate / 4) * d) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h4 := ExponentialSums.sum_torus_exp_le (n := m) (c := ℓ.weightRate / 4) (by positivity) y
  calc ∑ z : TorusFields.TorusSite m, ((4 : ℕ) : ℝ) * (((TorusFields.supDist z y + 1 : ℕ) : ℝ) *
        Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y z))
      ≤ ∑ z : TorusFields.TorusSite m, ((4 : ℕ) : ℝ) * ((4 / ℓ.weightRate + 1) *
          Real.exp (-(ℓ.weightRate / 4) * TorusFields.supDist z y)) :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpt z) (by norm_num)
    _ = 4 * (4 / ℓ.weightRate + 1) * ∑ z : TorusFields.TorusSite m,
          Real.exp (-(ℓ.weightRate / 4) * TorusFields.supDist z y) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        push_cast
        ring
    _ ≤ bondSumBound ℓ := mul_le_mul_of_nonneg_left h4 (by positivity)
private theorem mixedDeriv_fin_zero (G : TorusFields.TorusField m → ℝ) (W : TorusFields.TorusField m)
    (c : Fin 0 → TorusFields.TorusBond m) (X : Fin 0 → BlockAverages.imaginaryQuaternions) :
    TorusFields.mixedDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p46649 <;> assumption
private theorem abs_centered_le_at_site (hax : ColdStepAtMirrorFrames.AxialGaugeBondBound)
    (hno : ColdStepAtMirrorFrames.FirstDerivVanishesAtUniform)
    (hfit : ℓ.Admissible) (hrow : TorusLumps.ColdExpansion ℓ t x D f) (hm : ℓ.n₀ ≤ m)
    (W : TorusFields.TorusField m) (y : TorusFields.TorusSite m) {s : ℝ} {r : ℕ}
    (hs : 0 < s) (hc : TorusFields.IsCold s W) (hsσ : s ≤ ℓ.threshold) (hr : 2 * (r + 1) + 2 < m)
    (hsm : 4 * (6 * ((r + 1 : ℕ) : ℝ) * s) < ℓ.threshold) :
    |TorusLumps.centered f m y W| ≤ ℓ.E / ℓ.weight r + ℓ.E * (6 * s * bondSumBound ℓ) ^ 2 := by
  classical
  obtain ⟨g, hg⟩ := exists_axial_gauge_near_one hax W y hs hc
  have hWσ : TorusFields.IsCold ℓ.threshold W := fun z μ ν h => (hc z μ ν h).trans_le hsσ
  set Wg := TorusFields.gaugeTransform g W with hWg
  have hWgσ : TorusFields.IsCold ℓ.threshold Wg := fun z μ ν h => by
    rw [hWg, TorusFields.curvature_gaugeTransform]
    exact hWσ z μ ν h
  set W2 : TorusFields.TorusField m := fun z i => if TorusFields.supDist z y ≤ r then Wg z i else 1 with hW2
  have hnear : ∀ b : TorusFields.TorusBond m,
      ‖((W2 b.1 b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        3 * ((TorusFields.supDist b.1 y + 1 : ℕ) : ℝ) * s ∧
      ‖((W2 b.1 b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 3 * ((r + 1 : ℕ) : ℝ) * s := by
    rintro ⟨z, i⟩
    simp only [hW2]
    by_cases hd : TorusFields.supDist z y ≤ r
    · rw [if_pos hd]
      have h1 := hg (z, i) (by simp only; omega)
      refine ⟨h1, h1.trans ?_⟩
      have : ((TorusFields.supDist z y + 1 : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ hd
      nlinarith
    · rw [if_neg hd]
      simp only [OneMemClass.coe_one, sub_self, norm_zero]
      constructor <;> positivity
  choose a U hU hv ha using fun b : TorusFields.TorusBond m => exists_eq_smul_unit (LumpContours.minimalLog (W2 b.1 b.2))
  have hang : angleField U a = W2 := by
    funext z i
    simp only [angleField]
    rw [← hv (z, i), (minimalLog_spec _).1]
  have hab : ∀ b, |a b| ≤ 2 * ‖((W2 b.1 b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ := fun b => by
    rw [ha b]
    exact norm_minimalLog_le_two_mul _
  have hcold : ∀ τ ∈ Set.Icc (0 : ℝ) 1, TorusFields.IsCold ℓ.threshold (angleField U (τ • a)) := by
    intro τ hτ z μ ν _
    have hclose : ∀ (z' : TorusFields.TorusSite m) (i : Fin 4),
        ‖((angleField U (τ • a) z' i : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
          ((TorusFields.trivialField m z' i : BlockAverages.UnitQuaternion) : ℍ[ℝ])‖ ≤
            6 * ((r + 1 : ℕ) : ℝ) * s := by
      intro z' i
      simp only [angleField, TorusFields.trivialField, Pi.smul_apply, smul_eq_mul, OneMemClass.coe_one]
      refine (TorusFrame.norm_expUnit_sub_one_le _).trans ?_
      have e : ‖(((τ * a (z', i)) • U (z', i) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ =
          |τ| * |a (z', i)| := by
        show ‖(τ * a (z', i)) • U (z', i)‖ = _
        rw [norm_smul, hU, mul_one, Real.norm_eq_abs, abs_mul]
      rw [e, abs_of_nonneg hτ.1]
      have h1 := hab (z', i)
      have h2 := (hnear (z', i)).2
      have h3 : |a (z', i)| ≤ 6 * ((r + 1 : ℕ) : ℝ) * s := by
        simp only at h1 h2
        linarith
      calc τ * |a (z', i)| ≤ 1 * |a (z', i)| := mul_le_mul_of_nonneg_right hτ.2 (abs_nonneg _)
        _ ≤ _ := by linarith
    have h1 := FieldMoves.curvature_le_add_of_close hclose z μ ν
    have h2 : TorusFields.curvature (TorusFields.trivialField m) z μ ν = 0 := by
      simp [TorusFields.curvature, TorusFields.holonomy, TorusFields.trivialField]
    linarith
  have hT := abs_centered_angleField_le hno hfit hrow hm y U a hU hcold
  rw [hang] at hT
  have hρ := weightRate_pos hfit
  have hE := hfit.E_pos
  have hK := sum_bonds_weighted_le (ℓ := ℓ) (m := m) hρ y
  have hsum : ∑ b : TorusFields.TorusBond m, |a b| *
      Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y b.1) ≤ 6 * s * bondSumBound ℓ := by
    calc ∑ b : TorusFields.TorusBond m, |a b| * Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y b.1)
        ≤ ∑ b : TorusFields.TorusBond m, 6 * s * (((TorusFields.supDist b.1 y + 1 : ℕ) : ℝ) *
            Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y b.1)) := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          have h1 := hab b
          have h2 := (hnear b).1
          linarith
      _ = 6 * s * ∑ b : TorusFields.TorusBond m, ((TorusFields.supDist b.1 y + 1 : ℕ) : ℝ) *
            Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y b.1) := by
          rw [Finset.mul_sum]
      _ ≤ 6 * s * bondSumBound ℓ := mul_le_mul_of_nonneg_left hK (by positivity)
  have hsum0 : 0 ≤ ∑ b : TorusFields.TorusBond m, |a b| *
      Real.exp (-(ℓ.weightRate / 2) * TorusFields.supDist y b.1) :=
    Finset.sum_nonneg fun b _ => by positivity
  have hsq := pow_le_pow_left₀ hsum0 hsum 2
  have hT2 : |TorusLumps.centered f m y W2| ≤ ℓ.E * (6 * s * bondSumBound ℓ) ^ 2 :=
    hT.trans (mul_le_mul_of_nonneg_left hsq hE.le)
  have hW2σ : TorusFields.IsCold ℓ.threshold W2 := by
    have := hcold 1 (Set.right_mem_Icc.2 zero_le_one)
    rwa [one_smul, hang] at this
  have hagree : TorusLumps.FieldsAgreeNear Wg W2 y y r := by
    intro h hb
    simp only [hW2]
    have hd : TorusFields.supDist (TorusLumps.bondFrom y h).1 y ≤ r := by
      rw [TorusFields.supDist_comm]
      exact TorusFields.supDist_add_le_of_offsetInBox y hb.1
    rw [if_pos hd]
  have hloc := hrow.local_density m m hm hm y y Wg W2 r (by omega) (by omega) hWgσ hW2σ hagree 0
    Fin.elim0 Fin.elim0 (Nat.zero_le _) (fun l => l.elim0) (fun l => l.elim0)
  rw [mixedDeriv_fin_zero, mixedDeriv_fin_zero] at hloc
  have hgauge : TorusLumps.centered f m y Wg = TorusLumps.centered f m y W := by
    unfold TorusLumps.centered
    rw [hWg, hrow.gauge m hm y g W hWσ]
  rw [hgauge] at hloc
  have h3 := abs_sub_abs_le_abs_sub (TorusLumps.centered f m y W) (TorusLumps.centered f m y W2)
  linarith
end SiteBound
section Assembly
open Filter Topology
private theorem card_supBall_le {R : ℕ} (hR : 1 ≤ R) [NeZero (4 * (2 * R))] :
    ((ResponseInTheExpansion.supBall (0 : TorusFields.TorusSite (4 * (2 * R))) (3 * (R : ℝ) / 2)).card : ℝ) ≤
      625 * (R : ℝ) ^ 4 := by
  classical
  have hsub : (ResponseInTheExpansion.supBall (0 : TorusFields.TorusSite (4 * (2 * R))) (3 * (R : ℝ) / 2)).card ≤
      (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(2 * (R : ℤ))) (2 * (R : ℤ))).card := by
    refine Finset.card_le_card_of_injOn (fun z i => (z i).valMinAbs) ?_ ?_
    · intro z hz
      have hz' : (TorusFields.supDist z (0 : TorusFields.TorusSite (4 * (2 * R))) : ℝ) ≤ 3 * (R : ℝ) / 2 := by
        simpa [ResponseInTheExpansion.supBall] using hz
      have h2 : TorusFields.supDist z (0 : TorusFields.TorusSite (4 * (2 * R))) ≤ 2 * R := by
        have : (TorusFields.supDist z (0 : TorusFields.TorusSite (4 * (2 * R))) : ℝ) ≤ ((2 * R : ℕ) : ℝ) := by
          push_cast
          have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
          linarith
        exact_mod_cast this
      have h3 := (TorusFields.supDist_le_iff z 0 (2 * R)).mp h2
      refine Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr fun i => ?_)
      have h4 := h3 i
      simp only [Pi.zero_apply, sub_zero] at h4
      rw [Finset.mem_Icc]
      show -(2 * (R : ℤ)) ≤ (z i).valMinAbs ∧ (z i).valMinAbs ≤ 2 * (R : ℤ)
      omega
    · intro z _ z' _ h
      funext i
      have h1 := congrFun h i
      have h2 := congrArg (fun e : ℤ => (e : ZMod (4 * (2 * R)))) h1
      simpa [ZMod.coe_valMinAbs] using h2
  have hcard : (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(2 * (R : ℤ))) (2 * (R : ℤ))).card =
      (4 * R + 1) ^ 4 := by
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  rw [hcard] at hsub
  have h1 : ((ResponseInTheExpansion.supBall (0 : TorusFields.TorusSite (4 * (2 * R))) (3 * (R : ℝ) / 2)).card : ℝ) ≤
      ((4 * R + 1 : ℕ) : ℝ) ^ 4 := by
    exact_mod_cast hsub
  have h2 : ((4 * R + 1 : ℕ) : ℝ) ≤ 5 * (R : ℝ) := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    push_cast
    linarith
  have h3 := pow_le_pow_left₀ (by positivity) h2 4
  calc _ ≤ ((4 * R + 1 : ℕ) : ℝ) ^ 4 := h1
    _ ≤ (5 * (R : ℝ)) ^ 4 := h3
    _ = 625 * (R : ℝ) ^ 4 := by ring
private theorem eventually_boxRadius_bounds (ρ σ c : ℝ) (n0 : ℕ) (hρ : 0 < ρ) (hσ : 0 < σ) (hc : 0 ≤ c)
    {κ₀ : ℝ} (h1 : 1 / 27 ≤ κ₀) (h2 : κ₀ ≤ 1 / 21) :
    ∃ xs : ℝ, ∀ x : ℝ, xs ≤ x → 1 ≤ BoxGaussian.boxRadius κ₀ x ∧ n0 ≤ BoxGaussian.boxRadius κ₀ x ∧
      0 < BoxGaussian.boxScale x ∧
      4 * (6 * ((BoxGaussian.boxRadius κ₀ x + 1 : ℕ) : ℝ) *
        (c * (BoxGaussian.boxRadius κ₀ x : ℝ) ^ 2 * BoxGaussian.boxScale x)) < σ ∧
      Real.exp (-ρ * BoxGaussian.boxRadius κ₀ x) ≤
        (BoxGaussian.boxRadius κ₀ x : ℝ) ^ 4 * BoxGaussian.boxScale x ^ 2 := by
  have hκ : 0 < κ₀ := by linarith
  have e1 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ x ^ (1 / 14 : ℝ) := by
    have h := (isLittleO_log_rpow_atTop (r := 1 / 14) (by norm_num)).def (c := 1) one_pos
    filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
    have h3 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h4 : 0 ≤ x ^ (1 / 14 : ℝ) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg h3, Real.norm_of_nonneg h4, one_mul] at hx
    exact hx
  have e2 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ ρ * x ^ κ₀ := by
    have h := (isLittleO_log_rpow_atTop hκ).def hρ
    filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
    have h3 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h4 : 0 ≤ x ^ κ₀ := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg h3, Real.norm_of_nonneg h4] at hx
    exact hx
  have e3 : ∀ᶠ x : ℝ in atTop, (n0 : ℝ) + 1 ≤ x ^ κ₀ := (tendsto_rpow_atTop hκ).eventually_ge_atTop _
  have e4 : ∀ᶠ x : ℝ in atTop, 768 * c * x ^ (-(2 / 7) : ℝ) < σ := by
    have h := (tendsto_rpow_neg_atTop (y := 2 / 7) (by norm_num)).const_mul (768 * c)
    rw [mul_zero] at h
    exact h.eventually_lt_const hσ
  obtain ⟨xs, hxs⟩ := eventually_atTop.mp (e1.and (e2.and (e3.and (e4.and (eventually_ge_atTop (3 : ℝ))))))
  refine ⟨xs, fun x hx => ?_⟩
  obtain ⟨l1, l2, l3, l4, l5⟩ := hxs x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  set u := x ^ κ₀ with hu
  set R := BoxGaussian.boxRadius κ₀ x with hR
  have hRu : u ≤ (R : ℝ) := Nat.le_ceil u
  have hRu2 : (R : ℝ) < u + 1 := Nat.ceil_lt_add_one (by linarith)
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hδ : BoxGaussian.boxScale x = 2 * x ^ (-(1 / 2) : ℝ) * Real.log x := rfl
  have hp : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hδ0 : 0 < BoxGaussian.boxScale x := by
    rw [hδ]
    have : 0 < Real.log x := by linarith
    positivity
  refine ⟨by exact_mod_cast hR1, ?_, hδ0, ?_, ?_⟩
  · have : (n0 : ℝ) ≤ R := by linarith
    exact_mod_cast this
  · have hu3 : u ^ 3 ≤ x ^ (1 / 7 : ℝ) := by
      have e : u ^ 3 = x ^ (3 * κ₀) := by
        rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        congr 1
        push_cast
        ring
      rw [e]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hR2 : (R : ℝ) ≤ 2 * u := by linarith
    have hR3 : ((R + 1 : ℕ) : ℝ) ≤ 4 * u := by
      push_cast
      linarith
    have hbase : ((R + 1 : ℕ) : ℝ) * (R : ℝ) ^ 2 ≤ 16 * u ^ 3 := by
      have h5 : (R : ℝ) ^ 2 ≤ (2 * u) ^ 2 := pow_le_pow_left₀ (by linarith) hR2 2
      calc ((R + 1 : ℕ) : ℝ) * (R : ℝ) ^ 2 ≤ (4 * u) * (2 * u) ^ 2 :=
            mul_le_mul hR3 h5 (by positivity) (by positivity)
        _ = 16 * u ^ 3 := by ring
    have hprod : x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2) : ℝ) * x ^ (1 / 14 : ℝ) = x ^ (-(2 / 7) : ℝ) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      norm_num
    have hδ2 : BoxGaussian.boxScale x ≤ 2 * (x ^ (-(1 / 2) : ℝ) * x ^ (1 / 14 : ℝ)) := by
      rw [hδ, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left l1 hp.le) (by norm_num)
    have hfin : ((R + 1 : ℕ) : ℝ) * (R : ℝ) ^ 2 * BoxGaussian.boxScale x ≤ 32 * x ^ (-(2 / 7) : ℝ) := by
      calc ((R + 1 : ℕ) : ℝ) * (R : ℝ) ^ 2 * BoxGaussian.boxScale x
          ≤ (16 * x ^ (1 / 7 : ℝ)) * (2 * (x ^ (-(1 / 2) : ℝ) * x ^ (1 / 14 : ℝ))) :=
            mul_le_mul (hbase.trans (by linarith)) hδ2 hδ0.le (by positivity)
        _ = 32 * (x ^ (1 / 7 : ℝ) * x ^ (-(1 / 2) : ℝ) * x ^ (1 / 14 : ℝ)) := by ring
        _ = 32 * x ^ (-(2 / 7) : ℝ) := by rw [hprod]
    calc 4 * (6 * ((R + 1 : ℕ) : ℝ) * (c * (R : ℝ) ^ 2 * BoxGaussian.boxScale x))
        = 24 * c * (((R + 1 : ℕ) : ℝ) * (R : ℝ) ^ 2 * BoxGaussian.boxScale x) := by ring
      _ ≤ 24 * c * (32 * x ^ (-(2 / 7) : ℝ)) := mul_le_mul_of_nonneg_left hfin (by positivity)
      _ = 768 * c * x ^ (-(2 / 7) : ℝ) := by ring
      _ < σ := l4
  · have h5 : Real.exp (-ρ * R) ≤ x⁻¹ := by
      have h6 : Real.log x ≤ ρ * R := l2.trans (mul_le_mul_of_nonneg_left hRu hρ.le)
      rw [← Real.exp_log (inv_pos.mpr hx0), Real.log_inv]
      exact Real.exp_le_exp.mpr (by linarith)
    have h7 : (x ^ (-(1 / 2) : ℝ)) ^ 2 = x⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_neg_one]
      norm_num
    have h8 : x⁻¹ ≤ BoxGaussian.boxScale x ^ 2 := by
      rw [hδ, mul_pow, mul_pow, h7]
      have : 1 ≤ Real.log x ^ 2 := one_le_pow₀ hlog
      have hxi : 0 < x⁻¹ := inv_pos.mpr hx0
      nlinarith
    have h9 : (1 : ℝ) ≤ (R : ℝ) ^ 4 := one_le_pow₀ hR1
    nlinarith
theorem coldBoxDensitySum_holds (hax : ColdStepAtMirrorFrames.AxialGaugeBondBound)
    (hno : ColdStepAtMirrorFrames.FirstDerivVanishesAtUniform) :
    BoxEvents.coldBoxDensitySumStatement := by
  intro a _
  refine ⟨0, fun _ => 1, fun _ => one_pos, fun L _ _ T _ _ hD _ => ⟨T.floorMin, fun y hy _ _ => ?_⟩⟩
  intro κ₀ h1 h2 C₁
  have hfit : (T.stepParameters y).Admissible := hD.fits y hy
  have hρ : 0 < (T.stepParameters y).weightRate := weightRate_pos hfit
  have hE := hfit.E_pos
  set c : ℝ := 2 * (|C₁| + 1) with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨xs, hxs⟩ := eventually_boxRadius_bounds (T.stepParameters y).weightRate (T.stepParameters y).threshold c
    (T.stepParameters y).n₀ hρ hfit.σ_pos hc0.le h1 h2
  refine ⟨625 * (1 + (6 * c * bondSumBound (T.stepParameters y)) ^ 2), xs, ?_⟩
  intro Tw β k n _ o x R hdat hx hR W hW
  have hrow : TorusLumps.ColdExpansion (T.stepParameters y) (Tw.stage k).depth (Tw.stage k).coupling
      (Tw.stage k).functional (Tw.stage k).density :=
    (hdat.onFamily.onFamily k (Nat.le_add_right _ _)).isStep.1.1
  have hfl : xs ≤ x := hx ▸ hdat.le_coupling
  obtain ⟨hR1, hRn, hδ, hsm, hex⟩ := hxs x hfl
  rw [← hR] at hR1 hRn hsm hex
  set δ := BoxGaussian.boxScale x with hδd
  set s : ℝ := c * (R : ℝ) ^ 2 * δ with hs
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hs0 : 0 < s := by positivity
  have hlt : ∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o (2 * R)),
      TorusFields.curvature W p.1 p.2.1 p.2.2 < s := by
    intro p hp
    have h3 := hW p hp
    have h4 : C₁ ≤ |C₁| := le_abs_self _
    have h5 : 0 < (R : ℝ) ^ 2 * δ := by positivity
    have h6 : C₁ * (R : ℝ) ^ 2 * δ < s := by
      rw [hs, hc]
      nlinarith [abs_nonneg C₁]
    linarith
  have hN : NeZero (4 * (2 * R)) := ⟨by omega⟩
  have hcold : TorusFields.IsCold s (TorusMirror.mirrorField (2 * R) o W) := by
    refine TorusMirror.isCold_mirrorField (by omega) o W hs0 fun a' μ ν hμν hb => ?_
    refine hlt (o + TorusFields.siteOfInt a', μ, ν) ?_
    have hmem : ∀ d ∈ TorusLumps.plaquetteOffsets μ ν,
        o + TorusFields.siteOfInt (a' + d) ∈ ResponseInTheExpansion.supBall o (2 * R) := by
      intro d hd
      have h3 := TorusFields.supDist_add_le_of_offsetInBox o (hb d hd)
      simp only [ResponseInTheExpansion.supBall, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [TorusFields.supDist_comm]
      exact_mod_cast h3
    simp only [TorusFields.plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hμν, fun z hz => ?_⟩
    simp only [TorusFields.plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · simpa using hmem 0 (by simp [TorusLumps.plaquetteOffsets])
    · have := hmem (Pi.single μ 1) (by simp [TorusLumps.plaquetteOffsets])
      rwa [TorusLumps.add_siteOfInt_add, ← TorusLumps.unitStep_eq_siteOfInt] at this
    · have := hmem (Pi.single ν 1) (by simp [TorusLumps.plaquetteOffsets])
      rwa [TorusLumps.add_siteOfInt_add, ← TorusLumps.unitStep_eq_siteOfInt] at this
    · have := hmem (Pi.single μ 1 + Pi.single ν 1) (by simp [TorusLumps.plaquetteOffsets])
      rwa [← add_assoc, TorusLumps.add_siteOfInt_add, TorusLumps.add_siteOfInt_add,
        ← TorusLumps.unitStep_eq_siteOfInt, ← TorusLumps.unitStep_eq_siteOfInt] at this
  have hsσ : s ≤ (T.stepParameters y).threshold := by
    have h3 : (1 : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    nlinarith
  have hN0 : (T.stepParameters y).n₀ ≤ 4 * (2 * R) := by omega
  have hsite : ∀ z ∈ ResponseInTheExpansion.supBall (0 : TorusFields.TorusSite (4 * (2 * R))) (3 * (R : ℝ) / 2),
      |TorusLumps.centered (Tw.stage k).density (4 * (2 * R)) z (TorusMirror.mirrorField (2 * R) o W)| ≤
        (T.stepParameters y).E / (T.stepParameters y).weight R +
          (T.stepParameters y).E * (6 * s * bondSumBound (T.stepParameters y)) ^ 2 :=
    fun z _ => abs_centered_le_at_site hax hno hfit hrow hN0 _ z hs0 hcold hsσ (by omega) hsm
  have hw : (T.stepParameters y).E / (T.stepParameters y).weight R ≤
      (T.stepParameters y).E * ((R : ℝ) ^ 4 * δ ^ 2) :=
    (div_weight_le_exp hE.le R).trans (mul_le_mul_of_nonneg_left hex hE.le)
  have hB : (T.stepParameters y).E / (T.stepParameters y).weight R +
        (T.stepParameters y).E * (6 * s * bondSumBound (T.stepParameters y)) ^ 2 ≤
      (T.stepParameters y).E * ((R : ℝ) ^ 4 * δ ^ 2) *
        (1 + (6 * c * bondSumBound (T.stepParameters y)) ^ 2) := by
    have e : (6 * s * bondSumBound (T.stepParameters y)) ^ 2 =
        (6 * c * bondSumBound (T.stepParameters y)) ^ 2 * ((R : ℝ) ^ 4 * δ ^ 2) := by
      rw [hs]
      ring
    rw [e]
    nlinarith
  have hcard := card_supBall_le (R := R) hR1
  have hB0 : 0 ≤ (T.stepParameters y).E * ((R : ℝ) ^ 4 * δ ^ 2) *
      (1 + (6 * c * bondSumBound (T.stepParameters y)) ^ 2) := by
    positivity
  unfold BoxEvents.mirrorSum
  rw [dif_neg (by omega)]
  calc ∑ z ∈ ResponseInTheExpansion.supBall (0 : TorusFields.TorusSite (4 * (2 * R))) (3 * (R : ℝ) / 2),
        |TorusLumps.centered (Tw.stage k).density (4 * (2 * R)) z (TorusMirror.mirrorField (2 * R) o W)|
      ≤ ∑ z ∈ ResponseInTheExpansion.supBall (0 : TorusFields.TorusSite (4 * (2 * R))) (3 * (R : ℝ) / 2),
          (T.stepParameters y).E * ((R : ℝ) ^ 4 * δ ^ 2) *
            (1 + (6 * c * bondSumBound (T.stepParameters y)) ^ 2) :=
        Finset.sum_le_sum fun z hz => (hsite z hz).trans hB
    _ = ((ResponseInTheExpansion.supBall (0 : TorusFields.TorusSite (4 * (2 * R))) (3 * (R : ℝ) / 2)).card : ℝ) *
          ((T.stepParameters y).E * ((R : ℝ) ^ 4 * δ ^ 2) *
            (1 + (6 * c * bondSumBound (T.stepParameters y)) ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (625 * (R : ℝ) ^ 4) *
          ((T.stepParameters y).E * ((R : ℝ) ^ 4 * δ ^ 2) *
            (1 + (6 * c * bondSumBound (T.stepParameters y)) ^ 2)) :=
        mul_le_mul_of_nonneg_right hcard hB0
    _ = 625 * (1 + (6 * c * bondSumBound (T.stepParameters y)) ^ 2) * (T.stepParameters y).E *
          (R : ℝ) ^ 8 * δ ^ 2 := by ring
end Assembly
end YangMills.Construction.BoxEvents.ColdBoxDensityBound
end
