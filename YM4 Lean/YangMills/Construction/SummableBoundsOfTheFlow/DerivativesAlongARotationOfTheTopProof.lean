import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponential
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongAMoveNearATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongARotationOfTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames Filter Set
open scoped Topology Nat Quaternion
namespace YangMills.Construction.Estimates
namespace RotationOfTop
variable {E E' G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G]
private theorem iteratedFDeriv_comp_affine (f : E → G) (L : E' →L[ℝ] E) (a : E) (x : E') (n : ℕ) (v : Fin n → E')
    (hf : ContDiffAt ℝ n f (a + L x)) :
    iteratedFDeriv ℝ n (fun z => f (a + L z)) x v = iteratedFDeriv ℝ n f (a + L x) fun i => L (v i) := by
  set g : E → G := fun e => f (e + a) with hg
  have hshift : iteratedFDeriv ℝ n g (L x) = iteratedFDeriv ℝ n f (L x + a) :=
    iteratedFDeriv_comp_add_right n a (L x)
  have hgc : ContDiffAt ℝ n g (L x) := by
    have : ContDiffAt ℝ n (fun e : E => e + a) (L x) := contDiffAt_id.add contDiffAt_const
    refine ContDiffAt.comp (g := f) (L x) ?_ this
    simpa [add_comm] using hf
  obtain ⟨u, hu, -, hcd⟩ := (hgc.contDiffWithinAt (s := Set.univ)).contDiffOn le_rfl (by simp)
  rw [Set.insert_eq_of_mem (Set.mem_univ _), nhdsWithin_univ] at hu
  obtain ⟨U, hUu, hUo, hxU⟩ := mem_nhds_iff.mp hu
  have hcdU : ContDiffOn ℝ n g U := hcd.mono hUu
  have hpre : IsOpen (L ⁻¹' U) := hUo.preimage L.continuous
  have hcomp := L.iteratedFDerivWithin_comp_right (f := g) (s := U) (x := x) (n := n) (i := n) hcdU
    hUo.uniqueDiffOn hpre.uniqueDiffOn hxU le_rfl
  have e1 : iteratedFDerivWithin ℝ n (g ∘ L) (L ⁻¹' U) x = iteratedFDeriv ℝ n (g ∘ L) x :=
    iteratedFDerivWithin_of_isOpen n hpre hxU
  have e2 : iteratedFDerivWithin ℝ n g U (L x) = iteratedFDeriv ℝ n g (L x) :=
    iteratedFDerivWithin_of_isOpen n hUo hxU
  rw [e1, e2, hshift] at hcomp
  have e3 : (fun z => f (a + L z)) = g ∘ L := by
    funext z
    simp [hg, add_comm]
  rw [e3, hcomp, add_comm]
  rfl
private theorem exists_isOpen_contDiffOn {f : E → G} {x : E} {n : ℕ} (hf : ContDiffAt ℝ n f x) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ n f U := by
  obtain ⟨u, hu, -, hcd⟩ := (hf.contDiffWithinAt (s := Set.univ)).contDiffOn le_rfl (by simp)
  rw [Set.insert_eq_of_mem (Set.mem_univ _), nhdsWithin_univ] at hu
  obtain ⟨U, hUu, hUo, hxU⟩ := mem_nhds_iff.mp hu
  exact ⟨U, hUo, hxU, hcd.mono hUu⟩
private theorem norm_iteratedFDeriv_comp_le_of_bounds {g : E' → G} {f : E → E'} {x : E} {n : ℕ}
    (hg : ContDiffAt ℝ n g (f x))
    (hf : ContDiffAt ℝ n f x) {C D : ℝ} (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n ! * C * D ^ n := by
  obtain ⟨U, hUo, hxU, hgU⟩ := exists_isOpen_contDiffOn hg
  obtain ⟨S, hSo, hxS, hfS⟩ := exists_isOpen_contDiffOn hf
  have hs : IsOpen (S ∩ f ⁻¹' U) := hfS.continuousOn.isOpen_inter_preimage hSo hUo
  have hxs : x ∈ S ∩ f ⁻¹' U := ⟨hxS, hxU⟩
  have h := norm_iteratedFDerivWithin_comp_le (g := g) (f := f) (n := n) (s := S ∩ f ⁻¹' U) (t := U) (x := x)
    (N := n) hgU (hfS.mono inter_subset_left) le_rfl hUo.uniqueDiffOn hs.uniqueDiffOn
    (fun y hy => hy.2) hxs (C := C) (D := D)
    (fun i hi => by rw [iteratedFDerivWithin_of_isOpen i hUo hxU]; exact hC i hi)
    (fun i h1 hi => by rw [iteratedFDerivWithin_of_isOpen i hs hxs]; exact hD i h1 hi)
  rwa [iteratedFDerivWithin_of_isOpen n hs hxs] at h
private theorem norm_le_of_basis_bound {m i : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin m → ℝ) ℝ)
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ a : Fin i → Fin m, |T fun j => Pi.single (a j) 1| ≤ B) : ‖T‖ ≤ m ^ i * B := by apply _root_.YangMills.SharedProofs.p82038 <;> assumption
private def pureQuat (a b c : ℝ) : ℍ[ℝ] := ⟨0, a, b, c⟩
@[simp] private theorem pureQuat_re (a b c : ℝ) : (pureQuat a b c).re = 0 := rfl
@[simp] private theorem pureQuat_imI (a b c : ℝ) : (pureQuat a b c).imI = a := rfl
@[simp] private theorem pureQuat_imJ (a b c : ℝ) : (pureQuat a b c).imJ = b := rfl
@[simp] private theorem pureQuat_imK (a b c : ℝ) : (pureQuat a b c).imK = c := rfl
private def quatUnit : Fin 3 → imaginaryQuaternions :=
  ![⟨pureQuat 1 0 0, rfl⟩, ⟨pureQuat 0 1 0, rfl⟩, ⟨pureQuat 0 0 1, rfl⟩]
private theorem quatUnit_areUnitVectors : AreUnitVectors quatUnit := by
  have key : ∀ q : ℍ[ℝ], Quaternion.normSq q = 1 → ‖q‖ = 1 := by
    intro q hq
    have h := Quaternion.normSq_eq_norm_mul_self q
    rw [hq] at h
    nlinarith [norm_nonneg q, sq_nonneg (‖q‖ - 1), sq_nonneg (‖q‖ + 1)]
  intro a
  show ‖((quatUnit a : imaginaryQuaternions) : ℍ[ℝ])‖ = 1
  apply key
  fin_cases a <;> simp [quatUnit, Quaternion.normSq_def']
private def quatCoordLinear (a : Fin 3) : imaginaryQuaternions →ₗ[ℝ] ℝ where
  toFun x := ![(x : ℍ[ℝ]).imI, (x : ℍ[ℝ]).imJ, (x : ℍ[ℝ]).imK] a
  map_add' x y := by fin_cases a <;> simp
  map_smul' t x := by fin_cases a <;> simp
private def quatCoord (a : Fin 3) : imaginaryQuaternions →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (quatCoordLinear a)
private theorem sum_quatCoord_smul (x : imaginaryQuaternions) : ∑ a, quatCoord a x • quatUnit a = x := by
  apply Subtype.ext
  have hre : (x : ℍ[ℝ]).re = 0 := x.2
  ext <;> simp [Fin.sum_univ_three, quatCoord, quatCoordLinear, quatUnit, hre]
variable {F : BlockFrame} {k : ℕ}
private def bondLinear (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (b : F.Site F.top × Fin 4) : (Fin k → ℝ) →L[ℝ] imaginaryQuaternions :=
  ∑ l, if c l = b then (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (X l) else 0
private theorem bondLinear_apply (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (b : F.Site F.top × Fin 4) (τ : Fin k → ℝ) : bondLinear c X b τ = bondSpread c X τ b.1 b.2 := by
  unfold bondLinear bondSpread
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : c l = b
  · simp [h]
  · simp [h]
private theorem norm_bondLinear_le (c : Fin k → F.Site F.top × Fin 4) {X : Fin k → imaginaryQuaternions}
    (hX : AreUnitVectors X) (b : F.Site F.top × Fin 4) (τ : Fin k → ℝ) : ‖bondLinear c X b τ‖ ≤ k * ‖τ‖ := by
  rw [bondLinear_apply]
  unfold bondSpread
  refine (norm_sum_le _ _).trans ?_
  calc ∑ l, ‖if c l = (b.1, b.2) then τ l • X l else 0‖ ≤ ∑ _l : Fin k, ‖τ‖ := Finset.sum_le_sum fun l _ => by
        split_ifs
        · rw [norm_smul, hX l, mul_one]
          exact norm_le_pi_norm τ l
        · simp
    _ = _ := by simp
private theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private def localCoords (Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ₀ : Fin k → ℝ)
    (u : Fin k → ℝ) : Fin (k * 3) → ℝ := fun p =>
  ((Finset.univ.filter fun l => c l = c (finProdFinEquiv.symm p).1).card : ℝ)⁻¹ *
    quatCoord (finProdFinEquiv.symm p).2 (Θ (bondLinear c X (c (finProdFinEquiv.symm p).1) (u + τ₀), 0,
      bondLinear c X (c (finProdFinEquiv.symm p).1) τ₀))
private def repeatedBonds (c : Fin k → F.Site F.top × Fin 4) : Fin (k * 3) → F.Site F.top × Fin 4 :=
  fun p => c (finProdFinEquiv.symm p).1
private def repeatedUnits : Fin (k * 3) → imaginaryQuaternions := fun p => quatUnit (finProdFinEquiv.symm p).2
private theorem bondSpread_localCoords
    (Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (τ₀ u : Fin k → ℝ) (y : F.Site F.top) (i : Fin 4) :
    bondSpread (repeatedBonds c) (repeatedUnits (k := k)) (localCoords Θ c X τ₀ u) y i =
      if ∃ l, c l = (y, i) then Θ (bondLinear c X (y, i) (u + τ₀), 0, bondLinear c X (y, i) τ₀) else 0 := by
  classical
  unfold bondSpread
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin k × Fin 3 ≃ Fin (k * 3)), Fintype.sum_prod_type]
  have each : ∀ l : Fin k, (∑ a : Fin 3, if repeatedBonds c (finProdFinEquiv (l, a)) = (y, i) then
      localCoords Θ c X τ₀ u (finProdFinEquiv (l, a)) • repeatedUnits (k := k) (finProdFinEquiv (l, a)) else 0) =
      if c l = (y, i) then ((Finset.univ.filter fun l' => c l' = (y, i)).card : ℝ)⁻¹ •
        Θ (bondLinear c X (y, i) (u + τ₀), 0, bondLinear c X (y, i) τ₀) else 0 := by
    intro l
    by_cases h : c l = (y, i)
    · simp only [repeatedBonds, repeatedUnits, localCoords, Equiv.symm_apply_apply, h, if_true]
      conv_rhs => rw [← sum_quatCoord_smul (Θ (bondLinear c X (y, i) (u + τ₀), 0, bondLinear c X (y, i) τ₀)),
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul]
    · simp [repeatedBonds, h]
  rw [Finset.sum_congr rfl fun l _ => each l]
  by_cases hb : ∃ l, c l = (y, i)
  · rw [if_pos hb, ← Finset.sum_filter, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have hne : ((Finset.univ.filter fun l' => c l' = (y, i)).card : ℝ) ≠ 0 := by
      obtain ⟨l, hl⟩ := hb
      have : 0 < (Finset.univ.filter fun l' => c l' = (y, i)).card :=
        Finset.card_pos.mpr ⟨l, by simp [hl]⟩
      positivity
    rw [mul_inv_cancel₀ hne, one_smul]
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg fun h => hb ⟨l, h⟩]
private theorem leftTranslate_localCoords
    {Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top)
    (τ₀ u : Fin k → ℝ)
    (h : ∀ l, expUnit (Θ (bondLinear c X (c l) (u + τ₀), 0, bondLinear c X (c l) τ₀)) =
      expUnit (bondLinear c X (c l) (u + τ₀)) * expUnit (0 : imaginaryQuaternions) *
        (expUnit (bondLinear c X (c l) τ₀))⁻¹) :
    leftTranslate (bondSpread c X (u + τ₀)) V =
      leftTranslate (bondSpread (repeatedBonds c) (repeatedUnits (k := k)) (localCoords Θ c X τ₀ u))
        (leftTranslate (bondSpread c X τ₀) V) := by
  funext y i
  show expUnit (bondSpread c X (u + τ₀) y i) * V y i = expUnit (bondSpread (repeatedBonds c)
    (repeatedUnits (k := k)) (localCoords Θ c X τ₀ u) y i) * (expUnit (bondSpread c X τ₀ y i) * V y i)
  rw [bondSpread_localCoords]
  by_cases hb : ∃ l, c l = (y, i)
  · rw [if_pos hb]
    obtain ⟨l, hl⟩ := hb
    have h1 := h l
    rw [hl, expUnit_zero] at h1
    rw [h1, ← bondLinear_apply c X (y, i) (u + τ₀), ← bondLinear_apply c X (y, i) τ₀]
    simp [mul_assoc]
  · rw [if_neg hb, expUnit_zero, one_mul, ← bondLinear_apply c X (y, i) (u + τ₀),
      ← bondLinear_apply c X (y, i) τ₀]
    have zero : ∀ τ : Fin k → ℝ, bondLinear c X (y, i) τ = 0 := by
      intro τ
      rw [bondLinear_apply]
      unfold bondSpread
      exact Finset.sum_eq_zero fun l _ => if_neg fun e => hb ⟨l, e⟩
    rw [zero, zero, expUnit_zero, one_mul]
private theorem iteratedFDeriv_basis_eq_bondDeriv (f : F.GaugeField F.top → ℝ) (W : F.GaugeField F.top)
    {m i : ℕ} (cs : Fin m → F.Site F.top × Fin 4)
    (Xs : Fin m → imaginaryQuaternions) (a : Fin i → Fin m)
    (h : ContDiffAt ℝ i (fun w : Fin m → ℝ => f (leftTranslate (bondSpread cs Xs w) W)) 0) :
    iteratedFDeriv ℝ i (fun w : Fin m → ℝ => f (leftTranslate (bondSpread cs Xs w) W)) 0
        (fun j => Pi.single (a j) 1) = bondDeriv f W (cs ∘ a) (Xs ∘ a) := by
  classical
  set L : (Fin i → ℝ) →L[ℝ] (Fin m → ℝ) :=
    ∑ j, (ContinuousLinearMap.proj j : (Fin i → ℝ) →L[ℝ] ℝ).smulRight (Pi.single (a j) (1 : ℝ)) with hL
  have Lapp : ∀ τ : Fin i → ℝ, L τ = ∑ j, τ j • (Pi.single (a j) (1 : ℝ) : Fin m → ℝ) := by
    intro τ
    simp [hL, _root_.sum_apply]
  have hs := iteratedFDeriv_comp_affine (fun w : Fin m → ℝ => f (leftTranslate (bondSpread cs Xs w) W)) L 0 0 i
    (fun j => Pi.single j 1) (by simpa using h)
  have e1 : ∀ j, L (Pi.single j 1) = Pi.single (a j) 1 := by
    intro j
    rw [Lapp]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have e2 : (fun z : Fin i → ℝ => f (leftTranslate (bondSpread cs Xs (0 + L z)) W)) =
      fun τ => f (leftTranslate (bondSpread (cs ∘ a) (Xs ∘ a) τ) W) := by
    funext τ
    congr 2
    funext y i'
    unfold bondSpread
    rw [zero_add, Lapp]
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Function.comp]
    have : ∀ p : Fin m, (if cs p = (y, i') then (∑ j, if p = a j then τ j else 0) • Xs p else 0) =
        ∑ j, if a j = p then (if cs (a j) = (y, i') then τ j • Xs (a j) else 0) else 0 := by
      intro p
      by_cases hp : cs p = (y, i')
      · rw [if_pos hp, Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : a j = p
        · subst hj
          simp [hp]
        · have : p ≠ a j := fun e => hj e.symm
          simp [hj, this]
      · rw [if_neg hp]
        symm
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : a j = p
        · subst hj
          simp [hp]
        · simp [hj]
    rw [Finset.sum_congr rfl fun p _ => this p, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [e2] at hs
  have e3 : (0 : Fin m → ℝ) + L 0 = 0 := by simp
  rw [e3] at hs
  simp only [e1] at hs
  exact hs.symm
private theorem triple_eq_diagonal_add (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (b : F.Site F.top × Fin 4) (τ₀ u : Fin k → ℝ) :
    (bondLinear c X b (u + τ₀), (0 : imaginaryQuaternions), bondLinear c X b τ₀) =
      diagonalTriple (bondLinear c X b τ₀) +
        (ContinuousLinearMap.inl ℝ imaginaryQuaternions (imaginaryQuaternions × imaginaryQuaternions)).comp
          (bondLinear c X b) u := by
  simp [diagonalTriple, add_comm]
private theorem contDiffAt_localCoords
    {Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
    {U : Set (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)} (hUo : IsOpen U)
    (hd : ∀ r, diagonalTriple r ∈ U) (hsm : ContDiffOn ℝ 3 Θ U) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ₀ : Fin k → ℝ) : ContDiffAt ℝ 3 (localCoords Θ c X τ₀) 0 := by
  rw [contDiffAt_pi]
  intro p
  unfold localCoords
  set b := c (finProdFinEquiv.symm p).1
  have hpt : (bondLinear c X b ((0 : Fin k → ℝ) + τ₀), (0 : imaginaryQuaternions), bondLinear c X b τ₀) =
      diagonalTriple (bondLinear c X b τ₀) := by
    simp [diagonalTriple]
  have hΘ : ContDiffAt ℝ 3 Θ
      (bondLinear c X b ((0 : Fin k → ℝ) + τ₀), (0 : imaginaryQuaternions), bondLinear c X b τ₀) := by
    rw [hpt]
    exact hsm.contDiffAt (hUo.mem_nhds (hd _))
  have inner : ContDiff ℝ 3 fun u : Fin k → ℝ =>
      (bondLinear c X b (u + τ₀), (0 : imaginaryQuaternions), bondLinear c X b τ₀) :=
    ((bondLinear c X b).contDiff.comp (contDiff_id.add contDiff_const)).prodMk contDiff_const
  exact contDiffAt_const.mul
    ((quatCoord (finProdFinEquiv.symm p).2).contDiff.contDiffAt.comp (0 : Fin k → ℝ)
      (ContDiffAt.comp (0 : Fin k → ℝ) hΘ inner.contDiffAt))
private theorem localCoords_zero
    {Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
    (hz : ∀ r, Θ (diagonalTriple r) = 0)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ₀ : Fin k → ℝ) :
    localCoords Θ c X τ₀ 0 = 0 := by
  funext p
  have hpt : ∀ b, (bondLinear c X b ((0 : Fin k → ℝ) + τ₀), (0 : imaginaryQuaternions), bondLinear c X b τ₀) =
      diagonalTriple (bondLinear c X b τ₀) := by
    intro b
    simp [diagonalTriple]
  simp only [localCoords]
  rw [hpt, hz]
  simp
private theorem norm_iteratedFDeriv_localCoords_le
    {Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
    {U : Set (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)} {C M : ℝ} (hUo : IsOpen U)
    (hd : ∀ r, diagonalTriple r ∈ U) (hsm : ContDiffOn ℝ 3 Θ U) (hC : 0 ≤ C)
    (hb : ∀ (r : imaginaryQuaternions) (j : ℕ), ‖r‖ ≤ 1 → j ≤ 3 →
      ‖iteratedFDeriv ℝ j Θ (diagonalTriple r)‖ ≤ C)
    (hM : ∀ a, ‖quatCoord a‖ ≤ M) (hM₀ : 0 ≤ M) (c : Fin k → F.Site F.top × Fin 4)
    {X : Fin k → imaginaryQuaternions} (hX : AreUnitVectors X)
    {τ₀ : Fin k → ℝ} (hτ : (k : ℝ) * ‖τ₀‖ ≤ 1) {i : ℕ} (hi : i ≤ 3) :
    ‖iteratedFDeriv ℝ i (localCoords Θ c X τ₀) 0‖ ≤ M * C * (k + 1) ^ 3 := by
  have hcd := contDiffAt_localCoords hUo hd hsm c X τ₀
  have hi' : ((i : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hi
  have hbd : M * C * (k : ℝ) ^ i ≤ M * C * (k + 1) ^ 3 := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (k : ℝ) ^ i ≤ ((k : ℝ) + 1) ^ i := pow_le_pow_left₀ (by positivity) (by linarith) i
      _ ≤ ((k : ℝ) + 1) ^ 3 := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) hi
  refine le_trans ?_ hbd
  refine (iteratedFDeriv ℝ i (localCoords Θ c X τ₀) 0).opNorm_le_bound (by positivity) fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun p => ?_
  set b := c (finProdFinEquiv.symm p).1 with hbdef
  set a := (finProdFinEquiv.symm p).2 with hadef
  set w : ℝ := ((Finset.univ.filter fun l => c l = b).card : ℝ)⁻¹ with hw
  have hw₁ : |w| ≤ 1 := by
    have h1 : 1 ≤ (Finset.univ.filter fun l => c l = b).card :=
      Finset.card_pos.mpr ⟨(finProdFinEquiv.symm p).1, by simp [hbdef]⟩
    have h2 : (1 : ℝ) ≤ ((Finset.univ.filter fun l => c l = b).card : ℝ) := by exact_mod_cast h1
    rw [hw, abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ h2
  set L : imaginaryQuaternions →L[ℝ] ℝ := w • quatCoord a with hL
  have hLn : ‖L‖ ≤ M := by
    refine L.opNorm_le_bound hM₀ fun x => ?_
    have h1 : L x = w * quatCoord a x := rfl
    rw [h1, norm_mul, Real.norm_eq_abs]
    calc |w| * ‖quatCoord a x‖ ≤ 1 * (M * ‖x‖) :=
          mul_le_mul hw₁ (((quatCoord a).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hM a) (norm_nonneg _)))
            (norm_nonneg _) zero_le_one
      _ = M * ‖x‖ := one_mul _
  set T : (Fin k → ℝ) →L[ℝ] (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) :=
    (ContinuousLinearMap.inl ℝ imaginaryQuaternions (imaginaryQuaternions × imaginaryQuaternions)).comp
      (bondLinear c X b) with hT
  have comp : (ContinuousLinearMap.proj p : (Fin (k * 3) → ℝ) →L[ℝ] ℝ) ∘ localCoords Θ c X τ₀ =
      fun u => (L ∘ Θ) (diagonalTriple (bondLinear c X b τ₀) + T u) := by
    funext u
    show localCoords Θ c X τ₀ u p = L (Θ (diagonalTriple (bondLinear c X b τ₀) + T u))
    rw [← triple_eq_diagonal_add]
    rfl
  have e₁ : iteratedFDeriv ℝ i (localCoords Θ c X τ₀) 0 v p =
      iteratedFDeriv ℝ i ((ContinuousLinearMap.proj p : (Fin (k * 3) → ℝ) →L[ℝ] ℝ) ∘ localCoords Θ c X τ₀)
        0 v := by
    rw [(ContinuousLinearMap.proj p : (Fin (k * 3) → ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left
      (hcd.of_le hi') le_rfl]
    rfl
  have ht0 : diagonalTriple (bondLinear c X b τ₀) + T 0 = diagonalTriple (bondLinear c X b τ₀) := by simp
  have hΘ : ContDiffAt ℝ 3 Θ (diagonalTriple (bondLinear c X b τ₀)) := hsm.contDiffAt (hUo.mem_nhds (hd _))
  have hLΘ : ContDiffAt ℝ i (L ∘ Θ) (diagonalTriple (bondLinear c X b τ₀)) :=
    (L.contDiff.contDiffAt.comp _ hΘ).of_le hi'
  rw [e₁, comp, iteratedFDeriv_comp_affine (L ∘ Θ) T (diagonalTriple (bondLinear c X b τ₀)) 0 i v
    (by rwa [ht0]), ht0, Real.norm_eq_abs, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have n₁ : ‖iteratedFDeriv ℝ i (L ∘ Θ) (diagonalTriple (bondLinear c X b τ₀))‖ ≤ M * C := by
    refine (L.norm_iteratedFDeriv_comp_left (hΘ.of_le hi') le_rfl).trans ?_
    refine mul_le_mul hLn (hb _ i ?_ hi) (ContinuousMultilinearMap.opNorm_nonneg _) hM₀
    exact (norm_bondLinear_le c hX b τ₀).trans hτ
  have n₂ : ∏ j, ‖T (v j)‖ ≤ (k : ℝ) ^ i * ∏ j, ‖v j‖ := by
    calc ∏ j, ‖T (v j)‖ ≤ ∏ j, ((k : ℝ) * ‖v j‖) := Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => by
          have : ‖T (v j)‖ = ‖bondLinear c X b (v j)‖ := by
            simp [hT, Prod.norm_def]
          rw [this]
          exact norm_bondLinear_le c hX b (v j)
      _ = _ := by simp [Finset.prod_mul_distrib]
  calc _ ≤ (M * C) * ((k : ℝ) ^ i * ∏ j, ‖v j‖) :=
        mul_le_mul n₁ n₂ (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = _ := by ring
end RotationOfTop
open RotationOfTop in
theorem contDiffBoundAlongRotationOfTop_of_conjugatedExpLogSmooth
    (hΘ : ColdStepAtMirrorFrames.ConjugatedExpLogSmooth) : ContDiffBoundAlongRotationOfTop := by
  intro k
  obtain ⟨Θ, U, CΘ, hUo, hC0, hdiag, hsm, hexp, hzero, hbd, -, -⟩ := hΘ
  set M : ℝ := ∑ a, ‖quatCoord a‖ with hM
  have hM₀ : 0 ≤ M := Finset.sum_nonneg fun _ _ => ContinuousLinearMap.opNorm_nonneg _
  have hMa : ∀ a, ‖quatCoord a‖ ≤ M := fun a =>
    Finset.single_le_sum (f := fun a => ‖quatCoord a‖) (fun _ _ => ContinuousLinearMap.opNorm_nonneg _)
      (Finset.mem_univ a)
  set D : ℝ := 1 + M * CΘ * (k + 1) ^ 3 with hD
  have hD₁ : 1 ≤ D := by
    have : 0 ≤ M * CΘ * ((k : ℝ) + 1) ^ 3 := by positivity
    linarith
  refine ⟨6 * (((k * 3 : ℕ) + 1 : ℝ) ^ 3 * D ^ 3), by positivity, ?_⟩
  intro F V c X f r B hX hr hkr hB htop hbound
  have local₁ : ∀ τ₀ ∈ Metric.ball (0 : Fin k → ℝ) r,
      ContDiffAt ℝ 3 (fun τ => f (leftTranslate (bondSpread c X τ) V)) τ₀ ∧ ∀ j : ℕ, j ≤ 3 →
        ‖iteratedFDeriv ℝ j (fun τ => f (leftTranslate (bondSpread c X τ) V)) τ₀‖ ≤
          6 * (((k * 3 : ℕ) + 1 : ℝ) ^ 3 * D ^ 3) * B := by
    intro τ₀ hτ₀
    set Φ : (Fin k → ℝ) → ℝ := fun τ => f (leftTranslate (bondSpread c X τ) V) with hΦ
    set V₀ := leftTranslate (bondSpread c X τ₀) V with hV₀
    set Ξ := localCoords Θ c X τ₀ with hΞdef
    set ψ : (Fin (k * 3) → ℝ) → ℝ :=
      fun w => f (leftTranslate (bondSpread (repeatedBonds c) (repeatedUnits (k := k)) w) V₀) with hψdef
    have hΞ0 : Ξ 0 = 0 := localCoords_zero hzero c X τ₀
    have hψ : ContDiffAt ℝ 3 ψ 0 := htop τ₀ hτ₀ (k * 3) (repeatedBonds c) repeatedUnits
    have hΞ : ContDiffAt ℝ 3 Ξ 0 := contDiffAt_localCoords hUo hdiag hsm c X τ₀
    have hcomp : ContDiffAt ℝ 3 (ψ ∘ Ξ) 0 := ContDiffAt.comp (0 : Fin k → ℝ) (by rwa [hΞ0]) hΞ
    have ev : (fun u => Φ (u + τ₀)) =ᶠ[𝓝 0] ψ ∘ Ξ := by
      have near : ∀ᶠ u : Fin k → ℝ in 𝓝 0, ∀ l,
          (bondLinear c X (c l) (u + τ₀), (0 : imaginaryQuaternions), bondLinear c X (c l) τ₀) ∈ U := by
        refine eventually_all.2 fun l => ?_
        have cont : Continuous fun u : Fin k → ℝ =>
            (bondLinear c X (c l) (u + τ₀), (0 : imaginaryQuaternions), bondLinear c X (c l) τ₀) :=
          ((bondLinear c X (c l)).continuous.comp (continuous_id.add continuous_const)).prodMk continuous_const
        have h0 : (bondLinear c X (c l) ((0 : Fin k → ℝ) + τ₀), (0 : imaginaryQuaternions),
            bondLinear c X (c l) τ₀) ∈ U := by
          have : (bondLinear c X (c l) ((0 : Fin k → ℝ) + τ₀), (0 : imaginaryQuaternions),
              bondLinear c X (c l) τ₀) = diagonalTriple (bondLinear c X (c l) τ₀) := by simp [diagonalTriple]
          rw [this]
          exact hdiag _
        exact cont.continuousAt.eventually_mem (hUo.mem_nhds h0)
      filter_upwards [near] with u hu
      show f _ = f _
      rw [leftTranslate_localCoords c X V τ₀ u fun l => hexp _ (hu l)]
    have c₀ : ContDiffAt ℝ 3 (fun u => Φ (u + τ₀)) 0 := hcomp.congr_of_eventuallyEq ev
    have hτn : (k : ℝ) * ‖τ₀‖ ≤ 1 := by
      have h1 : ‖τ₀‖ < r := by simpa using hτ₀
      calc (k : ℝ) * ‖τ₀‖ ≤ k * r := mul_le_mul_of_nonneg_left h1.le (by positivity)
        _ ≤ 1 := hkr
    refine ⟨?_, fun j hj => ?_⟩
    · have e : Φ = (fun u => Φ (u + τ₀)) ∘ fun t => t - τ₀ := by
        funext t
        simp
      rw [e]
      refine ContDiffAt.comp τ₀ (by simpa using c₀) (contDiffAt_id.sub contDiffAt_const)
    · have e : iteratedFDeriv ℝ j Φ τ₀ = iteratedFDeriv ℝ j (fun u => Φ (u + τ₀)) 0 := by
        rw [iteratedFDeriv_comp_add_right]
        simp
      have hj' : ((j : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
      rw [e, (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) ev j).eq_of_nhds]
      have hb := norm_iteratedFDeriv_comp_le_of_bounds (n := j) (g := ψ) (f := Ξ) (x := 0)
        (by rw [hΞ0]; exact hψ.of_le hj') (hΞ.of_le hj')
        (C := ((k * 3 : ℕ) + 1 : ℝ) ^ 3 * B) (D := D)
        (fun i hi => by
          rw [hΞ0]
          have hi3 : i ≤ 3 := hi.trans hj
          have hi' : ((i : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hi3
          refine (norm_le_of_basis_bound _ hB fun a => ?_).trans ?_
          · rw [iteratedFDeriv_basis_eq_bondDeriv f V₀ (repeatedBonds c) repeatedUnits a (hψ.of_le hi')]
            exact hbound τ₀ hτ₀ i _ _ hi3 fun j => by
              show ‖quatUnit _‖ = 1
              exact quatUnit_areUnitVectors _
          · refine mul_le_mul_of_nonneg_right ?_ hB
            calc (((k * 3 : ℕ) : ℝ)) ^ i ≤ (((k * 3 : ℕ) : ℝ) + 1) ^ i :=
                  pow_le_pow_left₀ (by positivity) (by linarith) i
              _ ≤ (((k * 3 : ℕ) : ℝ) + 1) ^ 3 :=
                  pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg (k * 3) : (0 : ℝ) ≤ ((k * 3 : ℕ) : ℝ))]) hi3)
        (fun i h1 hi => by
          have hi3 : i ≤ 3 := hi.trans hj
          refine (norm_iteratedFDeriv_localCoords_le hUo hdiag hsm hC0 hbd hMa hM₀ c hX hτn hi3).trans ?_
          calc M * CΘ * ((k : ℝ) + 1) ^ 3 ≤ D := by linarith
            _ = D ^ 1 := (pow_one D).symm
            _ ≤ D ^ i := pow_le_pow_right₀ hD₁ h1)
      refine hb.trans ?_
      have h6 : (j ! : ℝ) ≤ 6 := by
        have : j ! ≤ 6 := by
          interval_cases j <;> decide
        exact_mod_cast this
      have hp : D ^ j ≤ D ^ 3 := pow_le_pow_right₀ hD₁ hj
      have hq : 0 ≤ ((k * 3 : ℕ) + 1 : ℝ) ^ 3 * B := by positivity
      calc (j ! : ℝ) * (((k * 3 : ℕ) + 1 : ℝ) ^ 3 * B) * D ^ j
          ≤ 6 * (((k * 3 : ℕ) + 1 : ℝ) ^ 3 * B) * D ^ 3 :=
            mul_le_mul (mul_le_mul_of_nonneg_right h6 hq) hp (by positivity) (by positivity)
        _ = _ := by ring
  exact ⟨fun τ hτ => (local₁ τ hτ).1.contDiffWithinAt, fun τ hτ j hj => (local₁ τ hτ).2 j hj⟩
end YangMills.Construction.Estimates
end
