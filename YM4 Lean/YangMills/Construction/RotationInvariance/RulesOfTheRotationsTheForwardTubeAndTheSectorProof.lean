import YangMills.Construction.ForwardTube.ElementaryFactsOfTheTubeFramesStripSectorAndPencils
import YangMills.Construction.Matrices.ExpChartHolomorphyProof
import YangMills.Construction.RotationInvariance.RulesOfTheRotationsTheForwardTubeAndTheSector
import YangMills.Construction.Towers.WritingsOfAChainInTheLeftChartProof
import Mathlib
set_option autoImplicit false
open Complex (I)
open ComplexConjugate
open YangMills.Construction.RealPlane
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
noncomputable section
namespace YangMills.Construction.ForwardTube.RotationRules
theorem complexBoost_ofReal_coords (hF : TubeStarAndBoostFacts) (t : ℝ)
    (w : ℂ × ℂ) :
    (complexBoost (t : ℂ) w).1.re = w.1.re * Real.cos t - w.2.re * Real.sin t ∧
    (complexBoost (t : ℂ) w).1.im = w.1.im * Real.cos t - w.2.im * Real.sin t ∧
    (complexBoost (t : ℂ) w).2.re = w.1.re * Real.sin t + w.2.re * Real.cos t ∧
    (complexBoost (t : ℂ) w).2.im = w.1.im * Real.sin t + w.2.im * Real.cos t := by
  obtain ⟨-, -, -, ⟨-, -, -, form, -⟩⟩ := hF
  rw [form]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
theorem complexBoost_ofReal_mem_realVectors (hF : TubeStarAndBoostFacts) (t : ℝ)
    {w : ℂ × ℂ} (hw : w ∈ realVectors) : complexBoost (t : ℂ) w ∈ realVectors := by
  obtain ⟨-, h₁, -, h₂⟩ := complexBoost_ofReal_coords hF t w
  obtain ⟨hw₁, hw₂⟩ := hw
  refine ⟨?_, ?_⟩
  · rw [h₁, hw₁, hw₂]; ring
  · rw [h₂, hw₁, hw₂]; ring
theorem vecRe_complexBoost_ofReal (hF : TubeStarAndBoostFacts) (t : ℝ)
    (w : ℂ × ℂ) :
    vecRe (complexBoost (t : ℂ) w) =
      RealPlane.rotate t (vecRe w) := by
  obtain ⟨h₁, -, h₂, -⟩ := complexBoost_ofReal_coords hF t w
  ext i
  fin_cases i
  · simp [vecRe, RealPlane.rotate, h₁]
  · simp [vecRe, RealPlane.rotate, h₂]
theorem lightConeAndComplexRotationRules_holds
    (hE : TubeFrameStripSectorPencilFacts)
    (hF : TubeStarAndBoostFacts) :
    LightConeAndComplexRotationRules := by
  obtain ⟨⟨hcoord, hlin, hbij, -⟩, -⟩ := hE
  have hF' := hF
  obtain ⟨-, -, -, ⟨-, lin, -, form, -, -, grp, zero⟩⟩ := hF'
  have inv : ∀ (ζ : ℂ) (w : ℂ × ℂ), complexBoost (-ζ) (complexBoost ζ w) = w :=
    fun ζ w => by rw [grp, neg_add_cancel, zero]
  have inv' : ∀ (ζ : ℂ) (w : ℂ × ℂ), complexBoost ζ (complexBoost (-ζ) w) = w :=
    fun ζ w => by rw [grp, add_neg_cancel, zero]
  have back : ∀ (t : ℝ) (w : ℂ × ℂ),
      complexBoost ((-t : ℝ) : ℂ) (complexBoost (t : ℂ) w) = w :=
    fun t w => by rw [Complex.ofReal_neg, inv]
  have back' : ∀ (t : ℝ) (w : ℂ × ℂ),
      complexBoost (t : ℂ) (complexBoost ((-t : ℝ) : ℂ) w) = w :=
    fun t w => by rw [Complex.ofReal_neg, inv']
  refine ⟨hlin, hbij, hcoord, funext zero, fun ζ => ⟨lin ζ, ?_, inv ζ, inv' ζ⟩, fun ζ ζ' => ⟨?_, ?_⟩,
    fun ζ => ?_, fun t w => ?_, fun t => ?_, fun t w => ?_, fun t w => ?_⟩
  · exact ⟨Function.LeftInverse.injective (inv ζ), Function.RightInverse.surjective (inv' ζ)⟩
  · funext w
    exact grp ζ ζ' w
  · funext w
    show _ = complexBoost ζ' (complexBoost ζ w)
    rw [grp, add_comm]
  · funext v
    rw [form, form, Complex.cos_add_two_pi, Complex.sin_add_two_pi]
  · rw [form, Complex.ofReal_cos, Complex.ofReal_sin]
  · ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact complexBoost_ofReal_mem_realVectors hF t hx
    · intro hw
      exact ⟨_, complexBoost_ofReal_mem_realVectors hF (-t) hw, back' t w⟩
  · refine ⟨complexBoost_ofReal_mem_realVectors hF t, fun hw => ?_⟩
    rw [← back t w]
    exact complexBoost_ofReal_mem_realVectors hF (-t) hw
  · exact vecRe_complexBoost_ofReal hF t w
theorem tupleRotationPermutationShiftRules_holds
    (hF : TubeStarAndBoostFacts) :
    TupleRotationPermutationShiftRules := by
  obtain ⟨-, -, -, ⟨-, lin, -⟩⟩ := hF
  intro q _ ζ z u ς ς' φ
  refine ⟨rfl, ?_, ?_, rfl, ?_, rfl, ?_, rfl, rfl⟩
  · funext i
    exact ((lin ζ).map_sub _ _).symm
  · funext i
    exact (lin ζ).map_add _ _
  · funext i
    simp [complexDifferences]
  · funext i
    ext j
    fin_cases j <;>
      simp [tupleRe, vecRe, complexDifferences, successiveDifferences,
        Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]
theorem realPlane_inner_eq (a b : RealPlane) : inner ℝ a b = a 0 * b 0 + a 1 * b 1 := by apply _root_.YangMills.Construction.ForwardTube.inner_eq_coord_sum <;> assumption
theorem rotate_apply_zero (t : ℝ) (a : RealPlane) :
    RealPlane.rotate t a 0 = a 0 * Real.cos t - a 1 * Real.sin t := by
  simp [RealPlane.rotate]
theorem rotate_apply_one (t : ℝ) (a : RealPlane) :
    RealPlane.rotate t a 1 = a 0 * Real.sin t + a 1 * Real.cos t := by
  simp [RealPlane.rotate]
theorem lightConePlus_embedPlane (a : RealPlane) :
    lightConePlus (embedPlane a) = (a 0 : ℂ) + (a 1 : ℂ) * I := by
  simp [lightConePlus, embedPlane, mul_comm]
theorem planeInnerRotationReflectionRules_holds : PlaneInnerRotationReflectionRules := by
  have hinv : Function.Involutive reflectFirst := by
    intro v
    ext i
    fin_cases i <;> simp [reflectFirst]
  have hHalf : ∀ v : RealPlane, (reflectFirst v) 0 = -v 0 := fun v => by simp [reflectFirst]
  refine ⟨fun t a b => ⟨?_, ?_, ?_, ?_, ?_, ?_, fun φ h => ?_⟩, ⟨fun x y => ?_, fun c x => ?_⟩, hinv,
    ?_, ?_⟩
  · rw [realPlane_inner_eq, lightConePlus_embedPlane, lightConePlus_embedPlane]
    simp
  · rw [lightConePlus_embedPlane, Complex.norm_add_mul_I, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
  · have h := Real.sin_sq_add_cos_sq t
    rw [realPlane_inner_eq, realPlane_inner_eq, rotate_apply_zero, rotate_apply_zero,
      rotate_apply_one, rotate_apply_one]
    linear_combination (a 0 * b 0 + a 1 * b 1) * h
  · ext i
    fin_cases i <;> simp [RealPlane.rotate, unitX]
  · rw [realPlane_inner_eq, rotate_apply_zero, rotate_apply_zero, rotate_apply_one]
    simp [unitX]
    ring
  · ext i
    fin_cases i <;> simp [RealPlane.rotate, unitX, reflectFirst]
  · have h₀ := congrArg Complex.re h
    have h₁ := congrArg Complex.im h
    rw [lightConePlus_embedPlane, mul_comm I, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at h₀
    rw [lightConePlus_embedPlane, mul_comm I, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im] at h₁
    simp at h₀ h₁
    rw [rotate_apply_zero, h₀, h₁, Real.cos_add]
    ring
  · ext i
    fin_cases i <;> simp [reflectFirst]
    ring
  · ext i
    fin_cases i <;> simp [reflectFirst]
  · ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      show (reflectFirst w) 0 < 0
      rw [hHalf]
      exact neg_lt_zero.2 hw
    · intro hv
      refine ⟨reflectFirst v, ?_, hinv v⟩
      show 0 < (reflectFirst v) 0
      rw [hHalf]
      exact neg_pos.2 hv
  · ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      show 0 < (reflectFirst w) 0
      rw [hHalf]
      exact neg_pos.2 hw
    · intro hv
      refine ⟨reflectFirst v, ?_, hinv v⟩
      show (reflectFirst v) 0 < 0
      rw [hHalf]
      exact neg_lt_zero.2 hv
theorem isHolomorphicIn_univ_of_differentiable {N N' : ℕ}
    {f : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'}
    (hf : Differentiable ℂ f) : Coordinates.ComplexCoordinates.IsHolomorphicIn Set.univ f := by apply _root_.YangMills.Construction.Tower.FullSpace.ChainRule.isHolomorphicIn_univ <;> assumption
theorem differentiable_mvPolynomial_eval {N : ℕ} (P : MvPolynomial (Fin N) ℂ) :
    Differentiable ℂ fun z : Coordinates.ComplexCoordinates N => MvPolynomial.eval z P := by apply _root_.YangMills.SharedProofs.p63145 <;> assumption
theorem scalarPairTupleEquiv_apply_inl {q : ℕ} (p : ℂ × (Fin q → ℂ × ℂ)) :
    scalarPairTupleEquiv q p (finSumFinEquiv (Sum.inl 0)) = p.1 := by
  simp [scalarPairTupleEquiv, scalarEquiv, Equiv.arrowCongr, Equiv.sumArrowEquivProdArrow]
theorem scalarPairTupleEquiv_apply_inr {q : ℕ} (p : ℂ × (Fin q → ℂ × ℂ)) (k : Fin (q * 2)) :
    scalarPairTupleEquiv q p (finSumFinEquiv (Sum.inr k)) = pairTupleEquiv q p.2 k := by
  simp [scalarPairTupleEquiv, Equiv.arrowCongr, Equiv.sumArrowEquivProdArrow]
theorem differentiable_pairTupleEquiv {N p : ℕ}
    {g : Coordinates.ComplexCoordinates N → Fin p → ℂ × ℂ}
    (h₀ : ∀ i, Differentiable ℂ fun w => (g w i).1) (h₁ : ∀ i, Differentiable ℂ fun w => (g w i).2) :
    Differentiable ℂ fun w => pairTupleEquiv p (g w) := by
  rw [differentiable_pi]
  intro k
  obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective k
  fin_cases c
  · simpa [pairTupleEquiv_apply_fst] using h₀ i
  · simpa [pairTupleEquiv_apply_snd] using h₁ i
theorem affineAndRotationHolomorphy_holds
    (hF : TubeStarAndBoostFacts) :
    AffineAndRotationHolomorphy := by
  obtain ⟨-, -, -, ⟨-, -, -, form, -⟩⟩ := hF
  refine ⟨fun N N' _ _ => ⟨fun P _ => ?_, fun f => ?_⟩, fun q _ => ⟨?_, fun z => ?_⟩⟩
  · exact isHolomorphicIn_univ_of_differentiable
      (differentiable_pi.2 fun j => differentiable_mvPolynomial_eval (P j))
  · exact isHolomorphicIn_univ_of_differentiable (LinearMap.toContinuousLinearMap f).differentiable
  · unfold IsHolomorphicScalarPairMap Coordinates.ComplexCoordinates.IsHolomorphicVia
    rw [Set.image_univ, Equiv.range_eq_univ]
    refine isHolomorphicIn_univ_of_differentiable ?_
    set e := scalarPairTupleEquiv (q + 1) with he
    have hs : Differentiable ℂ fun w => (e.symm w).1 := by
      have : (fun w => (e.symm w).1) = fun w : Coordinates.ComplexCoordinates (1 + (q + 1) * 2) =>
          w (finSumFinEquiv (Sum.inl 0)) := by
        funext w
        rw [← scalarPairTupleEquiv_apply_inl (e.symm w), he, Equiv.apply_symm_apply]
      rw [this]
      exact differentiable_apply _
    have ht₀ : ∀ i, Differentiable ℂ fun w => ((e.symm w).2 i).1 := by
      intro i
      have : (fun w => ((e.symm w).2 i).1) = fun w : Coordinates.ComplexCoordinates (1 + (q + 1) * 2) =>
          w (finSumFinEquiv (Sum.inr (finProdFinEquiv (i, 0)))) := by
        funext w
        rw [← pairTupleEquiv_apply_fst, ← scalarPairTupleEquiv_apply_inr (e.symm w), he,
          Equiv.apply_symm_apply]
      rw [this]
      exact differentiable_apply _
    have ht₁ : ∀ i, Differentiable ℂ fun w => ((e.symm w).2 i).2 := by
      intro i
      have : (fun w => ((e.symm w).2 i).2) = fun w : Coordinates.ComplexCoordinates (1 + (q + 1) * 2) =>
          w (finSumFinEquiv (Sum.inr (finProdFinEquiv (i, 1)))) := by
        funext w
        rw [← pairTupleEquiv_apply_snd, ← scalarPairTupleEquiv_apply_inr (e.symm w), he,
          Equiv.apply_symm_apply]
      rw [this]
      exact differentiable_apply _
    have hang : Differentiable ℂ fun w => I * (e.symm w).1 := (differentiable_const I).mul hs
    have hcos : Differentiable ℂ fun w => Complex.cos (I * (e.symm w).1) :=
      Complex.differentiable_cos.comp hang
    have hsin : Differentiable ℂ fun w => Complex.sin (I * (e.symm w).1) :=
      Complex.differentiable_sin.comp hang
    refine differentiable_pairTupleEquiv
      (g := fun w => complexBoostTuple (I * (e.symm w).1) (e.symm w).2) (fun i => ?_) fun i => ?_
    · simp only [complexBoostTuple, form]
      exact ((ht₀ i).mul hcos).sub ((ht₁ i).mul hsin)
    · simp only [complexBoostTuple, form]
      exact ((ht₀ i).mul hsin).add ((ht₁ i).mul hcos)
  · unfold Coordinates.ComplexCoordinates.IsHolomorphicVia
    rw [Set.image_univ, Equiv.range_eq_univ]
    refine isHolomorphicIn_univ_of_differentiable ?_
    have hs : Differentiable ℂ fun w : Coordinates.ComplexCoordinates 1 => scalarEquiv.symm w := by
      have : (fun w : Coordinates.ComplexCoordinates 1 => scalarEquiv.symm w) = fun w => w 0 := by
        funext w
        simp [scalarEquiv]
      rw [this]
      exact differentiable_apply _
    have hcos : Differentiable ℂ fun w : Coordinates.ComplexCoordinates 1 =>
        Complex.cos (scalarEquiv.symm w) := Complex.differentiable_cos.comp hs
    have hsin : Differentiable ℂ fun w : Coordinates.ComplexCoordinates 1 =>
        Complex.sin (scalarEquiv.symm w) := Complex.differentiable_sin.comp hs
    refine differentiable_pairTupleEquiv
      (g := fun w => complexBoostTuple (scalarEquiv.symm w) z) (fun i => ?_) fun i => ?_
    · simp only [complexBoostTuple, form]
      exact (hcos.const_mul _).sub (hsin.const_mul _)
    · simp only [complexBoostTuple, form]
      exact (hsin.const_mul _).add (hcos.const_mul _)
theorem real_smul_eq_ofReal_smul (l : ℝ) (w : ℂ × ℂ) : l • w = (l : ℂ) • w := by
  ext <;> simp
theorem tubeAndRotatedTubeRules_holds
    (hE : TubeFrameStripSectorPencilFacts)
    (hF : TubeStarAndBoostFacts) :
    TubeAndRotatedTubeRules := by
  obtain ⟨-, -, ⟨hchar, -, -, -, hopen, hconv, hcone, -⟩, -, ⟨himg, -, -⟩, hsix, -⟩ := hE
  have hF' := hF
  obtain ⟨-, ⟨-, -, -, hreal⟩, -, ⟨-, lin, -, form, hext, -, grp, zero⟩⟩ := hF'
  have hcont : ∀ ζ : ℂ, Continuous (complexBoost ζ) := by
    intro ζ
    have : complexBoost ζ = fun v : ℂ × ℂ =>
        (v.1 * Complex.cos ζ - v.2 * Complex.sin ζ, v.1 * Complex.sin ζ + v.2 * Complex.cos ζ) :=
      funext (form ζ)
    rw [this]
    fun_prop
  have hpre : ∀ υ : rightAngleMultiples, rotatedForwardTube υ =
      complexBoost (-((υ : ℝ) : ℂ)) ⁻¹' forwardTube := by
    intro υ
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      show complexBoost _ _ ∈ forwardTube
      rwa [grp, neg_add_cancel, zero]
    · intro hw
      exact ⟨_, hw, by rw [grp, add_neg_cancel, zero]⟩
  refine ⟨hchar, hreal, fun υ => ⟨?_, ?_, ?_, fun s => ?_, ?_, (hsix υ).2⟩, ?_⟩
  · rw [hpre]
    exact hopen.preimage (hcont _)
  · refine hconv.is_linear_image (f := complexBoost ((υ : ℝ) : ℂ))
      ⟨(lin _).map_add, fun c x => ?_⟩
    rw [real_smul_eq_ofReal_smul, real_smul_eq_ofReal_smul]
    exact (lin _).map_smul _ _
  · rintro w ⟨v, hv, rfl⟩ l hl
    refine ⟨l • v, hcone v hv l hl, ?_⟩
    rw [real_smul_eq_ofReal_smul, real_smul_eq_ofReal_smul]
    exact (lin _).map_smul _ _
  · unfold rotatedForwardTube
    rw [Set.image_image]
    have : (fun x => complexBoost (I * (s : ℂ)) (complexBoost ((υ : ℝ) : ℂ) x)) =
        fun x => complexBoost ((υ : ℝ) : ℂ) (complexBoost (I * (s : ℂ)) x) := by
      funext x
      rw [grp, grp, add_comm]
    rw [this, ← Set.image_image (complexBoost ((υ : ℝ) : ℂ)), himg]
  · rintro w ⟨v, hv, rfl⟩
    have hv' : v.1.re > |v.2.im| := by
      have : v ∈ {v : ℂ × ℂ | v.1.re > |v.2.im|} := by
        rw [← hchar]
        exact hv
      exact this
    have hpos : 0 < v.1.re := lt_of_le_of_lt (abs_nonneg _) hv'
    have hmem : embedPlane (vecRe v) ∈ forwardTube ∩ realVectors := by
      rw [hreal]
      refine ⟨vecRe v, ?_, rfl⟩
      show 0 < vecRe v 0
      simpa [vecRe] using hpos
    refine ⟨embedPlane (vecRe v), hmem.1, ?_⟩
    rw [hext, vecRe_complexBoost_ofReal hF]
  · show complexBoost ((0 : ℝ) : ℂ) '' forwardTube = forwardTube
    have hid : complexBoost ((0 : ℝ) : ℂ) = id := by
      funext w
      rw [Complex.ofReal_zero, zero]
      rfl
    rw [hid, Set.image_id]
theorem sectorAndPencilRules_holds (hE : TubeFrameStripSectorPencilFacts) :
    SectorAndPencilRules := by
  obtain ⟨-, -, -, -, -, -, -, h₈⟩ := hE
  intro φ₀
  obtain ⟨hsec, hopen, -, -, hsub, -, -, hpen, -, -⟩ := h₈ φ₀
  have hφ : (φ₀ : ℝ) ∈ Set.Ioo 0 (Real.pi / 4) := φ₀.2
  have htan : 0 < Real.tan φ₀ :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hφ.1 (by linarith [hφ.2, Real.pi_pos])
  have hfirst : unitX ∈ coneSector φ₀ := by
    rw [hsec]
    show |unitX 1| < unitX 0 * Real.tan φ₀
    simpa [unitX] using htan
  refine ⟨?_, hopen, hsub, hfirst, fun q hq => ⟨hpen _ (by omega), fun i => ?_⟩⟩
  · ext a
    constructor
    · intro ha
      refine ⟨hsub ha, ?_⟩
      rw [hsec] at ha
      exact ha
    · rintro ⟨-, h⟩
      rw [hsec]
      exact h
  · have hd : successiveDifferences (fun l : Fin (q + 1) => (((l : ℕ) : ℝ) + 1) • unitX) i =
        unitX := by
      show ((((i : ℕ) + 1 : ℕ) : ℝ) + 1) • unitX -
        (((i : ℕ) : ℝ) + 1) • unitX = unitX
      rw [← sub_smul]
      have h₁ : ((((i : ℕ) + 1 : ℕ) : ℝ) + 1) - (((i : ℕ) : ℝ) + 1) = 1 := by
        push_cast
        ring
      rw [h₁, one_smul]
    rw [hd]
    exact hfirst
theorem holds_of_facts (hE : TubeFrameStripSectorPencilFacts)
    (hF : TubeStarAndBoostFacts) : Holds :=
  ⟨lightConeAndComplexRotationRules_holds hE hF, tupleRotationPermutationShiftRules_holds hF,
    planeInnerRotationReflectionRules_holds, affineAndRotationHolomorphy_holds hF,
    tubeAndRotatedTubeRules_holds hE hF, sectorAndPencilRules_holds hE⟩
end YangMills.Construction.ForwardTube.RotationRules
end
