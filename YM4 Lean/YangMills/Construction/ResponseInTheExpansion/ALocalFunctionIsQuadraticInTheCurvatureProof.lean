import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASideProof
import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormulaProof
import YangMills.Construction.FormsOnATorus.InteriorRegularityProof
import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfTheImageProof
import YangMills.Construction.ColdStepAtMirrorFrames.AdjointOfTheGroup
import YangMills.Construction.ColdStepAtMirrorFrames.SmallUnitsAndTheirLogarithms
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.LawInAState.DecayOverATorusProof
import YangMills.Construction.ResponseInTheExpansion.ALocalFunctionIsQuadraticInTheCurvature
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
namespace LocalQuadratic
section
private abbrev Offset : Type := Fin 4 → ℤ
private def unitOffset (i : Fin 4) : Offset := Pi.single i 1
section SignedSums
variable {V : Type*} [AddCommGroup V]
private def signedSum (f : ℤ → V) (m : ℤ) : V :=
  ∑ t ∈ Finset.Ico 0 m, f t - ∑ t ∈ Finset.Ico m 0, f t
private theorem signedSum_zero (f : ℤ → V) : signedSum f 0 = 0 := by simp [signedSum]
private theorem signedSum_succ (f : ℤ → V) (m : ℤ) : signedSum f (m + 1) = signedSum f m + f m := by
  unfold signedSum
  rcases le_or_gt 0 m with h | h
  · have e1 : Finset.Ico 0 (m + 1) = insert m (Finset.Ico 0 m) := by
      ext t; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have e2 : Finset.Ico (m + 1) 0 = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    have e3 : Finset.Ico m 0 = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    rw [e1, e2, e3, Finset.sum_insert (by simp)]
    simp only [Finset.sum_empty, sub_zero]
    abel
  · have e1 : Finset.Ico m 0 = insert m (Finset.Ico (m + 1) 0) := by
      ext t; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have e2 : Finset.Ico 0 (m + 1) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    have e3 : Finset.Ico 0 m = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    rw [e1, e2, e3, Finset.sum_insert (by simp)]
    simp only [Finset.sum_empty]
    abel
private theorem signedSum_telescope (g : ℤ → V) (m : ℤ) :
    signedSum (fun t => g (t + 1) - g t) m = g m - g 0 := by
  induction m using Int.induction_on with
  | zero => simp [signedSum_zero]
  | succ i ih =>
    rw [signedSum_succ, ih]
    abel
  | pred i ih =>
    have h := signedSum_succ (fun t => g (t + 1) - g t) (-(i : ℤ) - 1)
    have e : -(i : ℤ) - 1 + 1 = -(i : ℤ) := by ring
    simp only [e] at h
    rw [ih] at h
    have h' : signedSum (fun t => g (t + 1) - g t) (-(i : ℤ) - 1) = g (-(i : ℤ)) - g 0 - (g (-(i : ℤ)) - g (-(i : ℤ) - 1)) := by
      rw [h]; abel
    rw [h']; abel
private theorem signedSum_add (f f' : ℤ → V) (m : ℤ) :
    signedSum (fun t => f t + f' t) m = signedSum f m + signedSum f' m := by
  unfold signedSum
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  abel
private theorem signedSum_sub (f f' : ℤ → V) (m : ℤ) :
    signedSum (fun t => f t - f' t) m = signedSum f m - signedSum f' m := by
  unfold signedSum
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  abel
private theorem signedSum_congr {f f' : ℤ → V} (h : ∀ t, f t = f' t) (m : ℤ) :
    signedSum f m = signedSum f' m := by
  rw [show f = f' from funext h]
end SignedSums
private theorem norm_signedSum_le {V : Type*} [SeminormedAddCommGroup V] (f : ℤ → V) (m : ℤ) (s : ℝ)
    (h : ∀ t, ‖f t‖ ≤ s) : ‖signedSum f m‖ ≤ |(m : ℝ)| * s := by
  have b : ∀ S : Finset ℤ, ‖∑ t ∈ S, f t‖ ≤ S.card * s := fun S => by
    refine (norm_sum_le _ _).trans ?_
    simpa using Finset.sum_le_card_nsmul S (fun t => ‖f t‖) s (fun t _ => h t)
  unfold signedSum
  rcases le_or_gt 0 m with hm | hm
  · have e3 : Finset.Ico m 0 = ∅ := Finset.Ico_eq_empty_of_le hm
    rw [e3]
    simp only [Finset.sum_empty, sub_zero]
    refine (b _).trans (le_of_eq ?_)
    congr 1
    rw [Int.card_Ico, abs_of_nonneg (by exact_mod_cast hm)]
    have : ((m - 0).toNat : ℤ) = m := by simpa using Int.toNat_of_nonneg hm
    exact_mod_cast this
  · have e3 : Finset.Ico 0 m = ∅ := Finset.Ico_eq_empty_of_le hm.le
    rw [e3]
    simp only [Finset.sum_empty, zero_sub, norm_neg]
    refine (b _).trans (le_of_eq ?_)
    congr 1
    rw [Int.card_Ico, abs_of_neg (by exact_mod_cast hm)]
    have : ((0 - m).toNat : ℤ) = -m := by
      have := Int.toNat_of_nonneg (a := 0 - m) (by omega)
      simpa using this
    exact_mod_cast this
private def truncate (j : ℕ) (h : Offset) : Offset := fun l => if l.val < j then h l else 0
private def truncateAt (j : Fin 4) (h : Offset) (t : ℤ) : Offset :=
  fun l => if l < j then h l else if l = j then t else 0
section Comb
variable {V : Type*} [AddCommGroup V] (a : Offset → Fin 4 → V)
private def latticeCurl (h : Offset) (μ ν : Fin 4) : V :=
  a h μ + a (h + unitOffset μ) ν - a (h + unitOffset ν) μ - a h ν
private def partialForm (j : ℕ) (h : Offset) (i : Fin 4) : V := if i.val < j then a (truncate j h) i else 0
private def axisPotential (j : Fin 4) (h : Offset) : V := signedSum (fun t => a (truncateAt j h t) j) (h j)
private def axisComb (j : Fin 4) (h : Offset) (i : Fin 4) : V :=
  if i < j then -signedSum (fun t => latticeCurl a (truncateAt j h t) i j) (h j) else 0
private theorem truncateAt_add_unit_self (j : Fin 4) (h : Offset) (t : ℤ) :
    truncateAt j (h + unitOffset j) t = truncateAt j h t := by
  funext l
  unfold truncateAt unitOffset
  by_cases hl : l < j
  · have : l ≠ j := ne_of_lt hl
    simp [hl, this]
  · simp [hl]
private theorem truncateAt_add_unit_of_lt {i j : Fin 4} (hij : i < j) (h : Offset) (t : ℤ) :
    truncateAt j (h + unitOffset i) t = truncateAt j h t + unitOffset i := by
  funext l
  unfold truncateAt unitOffset
  by_cases hl : l < j
  · simp [hl]
  · have : l ≠ i := fun e => hl (e ▸ hij)
    simp [hl, this]
private theorem truncateAt_add_unit_of_gt {i j : Fin 4} (hij : j < i) (h : Offset) (t : ℤ) :
    truncateAt j (h + unitOffset i) t = truncateAt j h t := by
  funext l
  unfold truncateAt unitOffset
  by_cases hl : l < j
  · have : l ≠ i := ne_of_lt (hl.trans hij)
    simp [hl, this]
  · simp [hl]
private theorem truncateAt_succ (j : Fin 4) (h : Offset) (t : ℤ) :
    truncateAt j h (t + 1) = truncateAt j h t + unitOffset j := by
  funext l
  unfold truncateAt unitOffset
  by_cases hl : l < j
  · have : l ≠ j := ne_of_lt hl
    simp [hl, this]
  · by_cases e : l = j
    · subst e; simp
    · simp [hl, e]
private theorem truncateAt_self (j : Fin 4) (h : Offset) : truncateAt j h (h j) = truncate (j.val + 1) h := by
  funext l
  unfold truncateAt truncate
  by_cases hl : l < j
  · have : l.val < j.val + 1 := by have := Fin.lt_def.mp hl; omega
    simp [hl, this]
  · by_cases e : l = j
    · subst e; simp
    · have : ¬ l.val < j.val + 1 := by
        have h1 := Fin.not_lt.mp hl
        have h2 : l.val ≠ j.val := fun q => e (Fin.ext q)
        omega
      simp [hl, e, this]
private theorem truncateAt_zero (j : Fin 4) (h : Offset) : truncateAt j h 0 = truncate j.val h := by
  funext l
  unfold truncateAt truncate
  by_cases hl : l < j
  · have : l.val < j.val := Fin.lt_def.mp hl
    simp [hl, this]
  · have : ¬ l.val < j.val := fun q => hl (Fin.lt_def.mpr q)
    by_cases e : l = j
    · subst e; simp
    · simp [hl, e, this]
private theorem partialForm_succ_sub (j : Fin 4) (h : Offset) (i : Fin 4) :
    partialForm a (j.val + 1) h i - partialForm a j.val h i =
      axisPotential a j (h + unitOffset i) - axisPotential a j h + axisComb a j h i := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have h1 : i.val < j.val := Fin.lt_def.mp hij
    have hj : (h + unitOffset i) j = h j := by
      simp [unitOffset, (ne_of_lt hij).symm]
    unfold partialForm axisPotential axisComb
    rw [if_pos (by omega), if_pos h1, if_pos hij, hj]
    have key : signedSum (fun t => a (truncateAt j (h + unitOffset i) t) j) (h j) -
        signedSum (fun t => a (truncateAt j h t) j) (h j) =
        signedSum (fun t => latticeCurl a (truncateAt j h t) i j) (h j) +
          (a (truncate (j.val + 1) h) i - a (truncate j.val h) i) := by
      rw [← signedSum_sub]
      have e : ∀ t, a (truncateAt j (h + unitOffset i) t) j - a (truncateAt j h t) j =
          latticeCurl a (truncateAt j h t) i j + (a (truncateAt j h (t + 1)) i - a (truncateAt j h t) i) := by
        intro t
        unfold latticeCurl
        rw [truncateAt_add_unit_of_lt hij, truncateAt_succ]
        abel
      rw [signedSum_congr e, signedSum_add, signedSum_telescope (fun t => a (truncateAt j h t) i),
        truncateAt_self, truncateAt_zero]
    rw [key]
    abel
  · subst hij
    unfold partialForm axisPotential axisComb
    rw [if_pos (by omega), if_neg (by omega), if_neg (lt_irrefl _)]
    have hj : (h + unitOffset i) i = h i + 1 := by simp [unitOffset]
    rw [hj]
    simp only [truncateAt_add_unit_self]
    rw [signedSum_succ, truncateAt_self]
    abel
  · have h1 : j.val < i.val := Fin.lt_def.mp hij
    have hj : (h + unitOffset i) j = h j := by
      simp [unitOffset, ne_of_lt hij]
    unfold partialForm axisPotential axisComb
    rw [if_neg (by omega), if_neg (by omega), if_neg (not_lt.mpr hij.le), hj]
    simp only [truncateAt_add_unit_of_gt hij]
    abel
private def axialPotential (h : Offset) : V := ∑ j : Fin 4, axisPotential a j h
private def curlComb (h : Offset) (i : Fin 4) : V := ∑ j : Fin 4, axisComb a j h i
private theorem partialForm_four (h : Offset) (i : Fin 4) : partialForm a 4 h i = a h i := by
  unfold partialForm
  rw [if_pos i.2]
  congr 1
  funext l
  unfold truncate
  simp [l.2]
private theorem partialForm_zero (h : Offset) (i : Fin 4) : partialForm a 0 h i = 0 := by
  unfold partialForm
  simp
private theorem eq_gradient_add_comb (h : Offset) (i : Fin 4) :
    a h i = axialPotential a (h + unitOffset i) - axialPotential a h + curlComb a h i := by
  have h0 := partialForm_succ_sub a 0 h i
  have h1 := partialForm_succ_sub a 1 h i
  have h2 := partialForm_succ_sub a 2 h i
  have h3 := partialForm_succ_sub a 3 h i
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_add] at h0 h1 h2
  have e3 : ((3 : Fin 4)).val = 3 := rfl
  rw [e3] at h3
  have s4 := partialForm_four a h i
  have s0 := partialForm_zero a h i
  unfold axialPotential curlComb
  simp only [Fin.sum_univ_four]
  have h1' : partialForm a 2 h i - partialForm a 1 h i = _ := h1
  have h2' : partialForm a 3 h i - partialForm a 2 h i = _ := h2
  have h3' : partialForm a 4 h i - partialForm a 3 h i = _ := h3
  calc a h i = partialForm a 4 h i - partialForm a 0 h i := by rw [s4, s0, sub_zero]
    _ = (partialForm a 1 h i - partialForm a 0 h i) + (partialForm a 2 h i - partialForm a 1 h i) +
        (partialForm a 3 h i - partialForm a 2 h i) + (partialForm a 4 h i - partialForm a 3 h i) := by abel
    _ = _ := by rw [h0, h1', h2', h3']; abel
end Comb
end
open scoped Quaternion
open BlockAverages hiding unitStep adjointAction
open TorusFields TorusLumps ColdStepAtMirrorFrames
section
variable {n : ℕ} [NeZero n]
private abbrev LieForm (n : ℕ) : Type := TorusBond n → imaginaryQuaternions
private def expForm (A : LieForm n) (W : TorusField n) : TorusField n := fun x i => expUnit (A (x, i)) * W x i
private def chartFn (G : TorusField n → ℝ) (W : TorusField n) (A : LieForm n) : ℝ := G (expForm A W)
private def coordCLM (e : Fin 3) : imaginaryQuaternions →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := imaginaryComponent e
      map_add' := fun a b => by fin_cases e <;> simp [imaginaryComponent]
      map_smul' := fun r a => by fin_cases e <;> simp [imaginaryComponent] }
private theorem coordCLM_apply (e : Fin 3) (w : imaginaryQuaternions) : coordCLM e w = imaginaryComponent e w := rfl
private def lieBasis : Fin 3 → imaginaryQuaternions :=
  ![⟨⟨0, 1, 0, 0⟩, rfl⟩, ⟨⟨0, 0, 1, 0⟩, rfl⟩, ⟨⟨0, 0, 0, 1⟩, rfl⟩]
private theorem sum_coord_smul_basis (w : imaginaryQuaternions) : ∑ e, coordCLM e w • lieBasis e = w := by
  apply Subtype.ext
  have hr : (w : ℍ[ℝ]).re = 0 := w.2
  simp only [Fin.sum_univ_three, coordCLM_apply, imaginaryComponent, lieBasis]
  have e0 : ∀ a b c : ℝ, a * 0 + b * 0 + c * 0 = (0 : ℝ) := fun a b c => by ring
  ext
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).re
    rw [hr, e0]
  · change (w : ℍ[ℝ]).imI * 1 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imI
    ring
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 1 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imJ
    ring
  · change (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 1 = (w : ℍ[ℝ]).imK
    ring
private theorem norm_lieBasis (e : Fin 3) : ‖lieBasis e‖ = 1 := by
  have h : ‖((lieBasis e : imaginaryQuaternions) : ℍ[ℝ])‖ * ‖((lieBasis e : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    fin_cases e <;> simp [lieBasis]
  have h0 : 0 ≤ ‖((lieBasis e : imaginaryQuaternions) : ℍ[ℝ])‖ := norm_nonneg _
  have : ‖((lieBasis e : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by nlinarith
  exact this
private def placeCLM {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    (Fin k → ℝ) →L[ℝ] LieForm n :=
  ContinuousLinearMap.pi fun b => ∑ l, if c l = b then
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).smulRight (X l) else 0
private theorem placeCLM_apply {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (b : TorusBond n) :
    placeCLM c X σ b = ∑ l, if c l = b then σ l • X l else 0 := by
  simp only [placeCLM, ContinuousLinearMap.coe_pi', ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
private theorem perturb_eq_expForm {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (W : TorusField n) :
    TorusFields.perturb c X σ W = expForm (placeCLM c X σ) W := by
  funext x i
  unfold TorusFields.perturb expForm
  rw [placeCLM_apply]
private theorem chartFn_comp {k : ℕ} (G : TorusField n → ℝ) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (W : TorusField n) :
    (fun σ : Fin k → ℝ => G (TorusFields.perturb c X σ W)) = chartFn G W ∘ placeCLM c X := by
  funext σ
  simp only [Function.comp, chartFn, perturb_eq_expForm]
private theorem placeCLM_single {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (l : Fin k) :
    placeCLM c X (Pi.single l 1) = Pi.single (c l) (X l) := by
  funext b
  rw [placeCLM_apply, Finset.sum_eq_single l]
  · by_cases h : c l = b
    · subst h; simp
    · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h)]
  · intro l' _ hl
    simp [Pi.single_eq_of_ne hl]
  · simp
private theorem iteratedFDeriv_comp_clm {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ℓ : F →L[ℝ] E) (f : E → ℝ) (x : F) (hf : ContDiffAt ℝ 3 f (ℓ x)) (k : ℕ)
    (hk : k ≤ 3) (v : Fin k → F) :
    iteratedFDeriv ℝ k (f ∘ ℓ) x v = iteratedFDeriv ℝ k f (ℓ x) fun i => ℓ (v i) := by
  obtain ⟨u, hu, huc⟩ := hf.contDiffOn le_rfl (by simp)
  have hu' : ℓ x ∈ interior u := mem_interior_iff_mem_nhds.mpr (by simpa using hu)
  have hs : IsOpen (interior u) := isOpen_interior
  have hc : ContDiffOn ℝ 3 f (interior u) := by
    simpa using huc.mono interior_subset
  have hs' : IsOpen (ℓ ⁻¹' interior u) := hs.preimage ℓ.continuous
  have key := ContinuousLinearMap.iteratedFDerivWithin_comp_right ℓ hc hs.uniqueDiffOn hs'.uniqueDiffOn hu'
    (i := k) (by exact_mod_cast hk)
  rw [iteratedFDerivWithin_of_isOpen k hs' (show x ∈ ℓ ⁻¹' interior u from hu'),
    iteratedFDerivWithin_of_isOpen k hs hu'] at key
  rw [key]
  rfl
private theorem mixedDeriv_eq {G : TorusField n → ℝ} {W : TorusField n} {k : ℕ}
    (h : ContDiffAt ℝ 3 (chartFn G W) 0) (hk : k ≤ 3)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv G W c X = iteratedFDeriv ℝ k (chartFn G W) 0 fun l => Pi.single (c l) (X l) := by
  unfold mixedDeriv
  rw [chartFn_comp, iteratedFDeriv_comp_clm (placeCLM c X) (chartFn G W) 0 (by simpa using h) k hk]
  simp only [map_zero, placeCLM_single]
private theorem chartFn_contDiffAt {G : TorusField n → ℝ} {W : TorusField n} (h : ContDiffThreeAt G W) :
    ContDiffAt ℝ 3 (chartFn G W) 0 := by
  classical
  set e := Fintype.equivFin (TorusBond n × Fin 3) with he
  set k := Fintype.card (TorusBond n × Fin 3) with hk
  set c : Fin k → TorusBond n := fun l => (e.symm l).1 with hc
  set X : Fin k → imaginaryQuaternions := fun l => lieBasis (e.symm l).2 with hX
  let ι : LieForm n →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun l => (coordCLM (e.symm l).2).comp (ContinuousLinearMap.proj (e.symm l).1)
  have hι : ∀ A : LieForm n, placeCLM c X (ι A) = A := by
    intro A
    funext b
    rw [placeCLM_apply]
    have : ∀ l, (if c l = b then ι A l • X l else 0) =
        (fun q : TorusBond n × Fin 3 => if q.1 = b then coordCLM q.2 (A q.1) • lieBasis q.2 else 0) (e.symm l) := by
      intro l
      rfl
    simp only [this]
    rw [Equiv.sum_comp e.symm
        (fun q : TorusBond n × Fin 3 => if q.1 = b then coordCLM q.2 (A q.1) • lieBasis q.2 else 0),
      Fintype.sum_prod_type]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_eq_single b]
    · simp [sum_coord_smul_basis]
    · intro b' _ hb
      simp [hb]
    · simp
  have h1 : chartFn G W = (fun σ : Fin k → ℝ => G (TorusFields.perturb c X σ W)) ∘ ι := by
    funext A
    simp only [Function.comp, chartFn, perturb_eq_expForm, hι]
  rw [h1]
  have h2 := h k c X
  refine ContDiffAt.comp _ (by simpa using h2) ι.contDiff.contDiffAt
end
section
variable {n : ℕ} [NeZero n]
variable {σ K del c ρ₀ : ℝ} {G : TorusField n → ℝ} {y : TorusSite n}
private theorem isCold_trivialField (hσ : 0 < σ) : IsCold σ (trivialField n) := by apply _root_.YangMills.Construction.ImageDensities.isCold_trivialField <;> assumption
private theorem iteratedFDeriv_single_le (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K)
    {W : TorusField n} (hW : IsCold σ W)
    {k : ℕ} (h1 : 1 ≤ k) (h3 : k ≤ 3) (b : Fin k → TorusBond n) (Z : Fin k → imaginaryQuaternions) :
    |iteratedFDeriv ℝ k (chartFn G W) 0 (fun l => Pi.single (b l) (Z l))| ≤
      (∏ l, ‖Z l‖) * (K * Real.exp (-(del * (supportDiam y b : ℝ)))) := by
  have hc := chartFn_contDiffAt (hG.smooth W hW)
  by_cases hz : ∃ l, Z l = 0
  · obtain ⟨l, hl⟩ := hz
    have h0 : (fun l => (Pi.single (b l) (Z l) : LieForm n)) l = 0 := by simp [hl]
    rw [ContinuousMultilinearMap.map_coord_zero _ l h0]
    simp only [abs_zero]
    positivity
  · push Not at hz
    set X : Fin k → imaginaryQuaternions := fun l => ‖Z l‖⁻¹ • Z l with hXd
    have hn : ∀ l, ‖Z l‖ ≠ 0 := fun l => norm_ne_zero_iff.mpr (hz l)
    have hX : AreUnitVectors X := fun l => by
      simp only [hXd, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (hn l)
    have e : (fun l => (Pi.single (b l) (Z l) : LieForm n)) =
        fun l => ‖Z l‖ • (Pi.single (b l) (X l) : LieForm n) := by
      funext l
      rw [← Pi.single_smul]
      simp only [hXd, smul_smul, mul_inv_cancel₀ (hn l), one_smul]
    rw [e, ContinuousMultilinearMap.map_smul_univ, ← mixedDeriv_eq hc h3 b X, smul_eq_mul, abs_mul,
      abs_of_nonneg (Finset.prod_nonneg fun l _ => norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hG.decay W hW k b X h1 h3 hX) (Finset.prod_nonneg fun l _ => norm_nonneg _)
private def expSumZ (a : ℝ) : ℝ := ∑' v : ℤ, Real.exp (-(a * |(v : ℝ)|))
private theorem summable_expSumZ {a : ℝ} (ha : 0 < a) : Summable fun v : ℤ => Real.exp (-(a * |(v : ℝ)|)) := by apply _root_.YangMills.SharedProofs.p3695 <;> assumption
private theorem expSumZ_nonneg {a : ℝ} : 0 ≤ expSumZ a := tsum_nonneg fun _ => (Real.exp_pos _).le
private theorem zmod_expSum_le {a : ℝ} (ha : 0 < a) :
    ∑ u : ZMod n, Real.exp (-(a * |((u.valMinAbs : ℤ) : ℝ)|)) ≤ expSumZ a := by
  have hi : Function.Injective (ZMod.valMinAbs : ZMod n → ℤ) := fun u v h => by
    have := congrArg (Int.cast : ℤ → ZMod n) h
    simpa [ZMod.coe_valMinAbs] using this
  have e := Finset.sum_image (s := Finset.univ) (g := (ZMod.valMinAbs : ZMod n → ℤ))
    (f := fun v : ℤ => Real.exp (-(a * |(v : ℝ)|))) (fun u _ v _ h => hi h)
  rw [← e]
  exact (summable_expSumZ ha).sum_le_tsum _ fun _ _ => (Real.exp_pos _).le
abbrev _root_.YangMills.DeltaSharedProofs.p502213 := @zmod_expSum_le
private theorem site_expSum_le {a : ℝ} (ha : 0 < a) (y : TorusSite n) :
    ∑ z : TorusSite n, Real.exp (-(a * (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ))) ≤ expSumZ (a / 4) ^ 4 := by
  have h1 : ∀ z : TorusSite n, Real.exp (-(a * (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ))) ≤
      ∏ l, Real.exp (-(a / 4 * |(((z l - y l).valMinAbs : ℤ) : ℝ)|)) := by
    intro z
    rw [← Real.exp_sum]
    refine Real.exp_le_exp.mpr ?_
    have hb : ∀ l, |(((z l - y l).valMinAbs : ℤ) : ℝ)| ≤ (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) := by
      intro l
      have h2 : ((z l - y l).valMinAbs).natAbs ≤ _root_.YangMills.Construction.TorusFields.supDist z y := by
        unfold supDist
        exact Finset.le_sup (f := fun i => ((z i - y i).valMinAbs).natAbs) (Finset.mem_univ l)
      have h3 : _root_.YangMills.Construction.TorusFields.supDist z y = _root_.YangMills.Construction.TorusFields.supDist y z := by
        unfold supDist
        congr 1
        funext i
        rw [← neg_sub, ZMod.natAbs_valMinAbs_neg]
      rw [h3] at h2
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
      exact_mod_cast h2
    have : ∑ l : Fin 4, -(a / 4 * |(((z l - y l).valMinAbs : ℤ) : ℝ)|) ≥
        ∑ l : Fin 4, -(a / 4 * (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ)) :=
      Finset.sum_le_sum fun l _ => by
        have := mul_le_mul_of_nonneg_left (hb l) (by positivity : 0 ≤ a / 4)
        linarith
    refine le_trans (le_of_eq ?_) this
    simp
    ring
  refine (Finset.sum_le_sum fun z _ => h1 z).trans ?_
  have h2 := Finset.prod_univ_sum (fun _ : Fin 4 => (Finset.univ : Finset (ZMod n)))
    (fun l u => Real.exp (-(a / 4 * |(((u - y l).valMinAbs : ℤ) : ℝ)|)))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  have h3 : ∀ l : Fin 4, ∑ u : ZMod n, Real.exp (-(a / 4 * |(((u - y l).valMinAbs : ℤ) : ℝ)|)) ≤
      expSumZ (a / 4) := by
    intro l
    have e := Equiv.sum_comp (Equiv.subRight (y l))
      (fun u : ZMod n => Real.exp (-(a / 4 * |((u.valMinAbs : ℤ) : ℝ)|)))
    simp only [Equiv.subRight_apply] at e
    rw [e]
    exact zmod_expSum_le (by positivity)
  calc _ ≤ ∏ _l : Fin 4, expSumZ (a / 4) :=
        Finset.prod_le_prod (fun l _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) fun l _ => h3 l
    _ = _ := by simp
abbrev _root_.YangMills.DeltaSharedProofs.p501803 := @site_expSum_le
private def bondConst (a : ℝ) : ℝ := 4 * expSumZ (a / 4) ^ 4
private theorem bondConst_nonneg {a : ℝ} : 0 ≤ bondConst a := by
  have := expSumZ_nonneg (a := a / 4)
  unfold bondConst
  positivity
private theorem bond_expSum_le {a : ℝ} (ha : 0 < a) (y : TorusSite n) :
    ∑ b : TorusBond n, Real.exp (-(a * (_root_.YangMills.Construction.TorusFields.supDist y b.1 : ℝ))) ≤ bondConst a := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have := site_expSum_le ha y
  unfold bondConst
  push_cast
  linarith
private theorem supDist_le_supportDiam {k : ℕ} (y : TorusSite n) (r : Fin k → TorusBond n) (l : Fin k) :
    _root_.YangMills.Construction.TorusFields.supDist y (r l).1 ≤ supportDiam y r :=
  le_max_of_le_left (Finset.le_sup (f := fun l : Fin k => _root_.YangMills.Construction.TorusFields.supDist y (r l).1) (Finset.mem_univ l))
private theorem triple_expSum_le (hd : 0 < del) (y : TorusSite n) :
    ∑ r : Fin 3 → TorusBond n, Real.exp (-(del * (supportDiam y r : ℝ))) ≤ bondConst (del / 3) ^ 3 := by
  have h1 : ∀ r : Fin 3 → TorusBond n, Real.exp (-(del * (supportDiam y r : ℝ))) ≤
      ∏ l, Real.exp (-(del / 3 * (_root_.YangMills.Construction.TorusFields.supDist y (r l).1 : ℝ))) := by
    intro r
    rw [← Real.exp_sum]
    refine Real.exp_le_exp.mpr ?_
    have hb : ∀ l, (_root_.YangMills.Construction.TorusFields.supDist y (r l).1 : ℝ) ≤ (supportDiam y r : ℝ) := fun l => by
      exact_mod_cast supDist_le_supportDiam y r l
    rw [Fin.sum_univ_three]
    nlinarith [mul_le_mul_of_nonneg_left (hb 0) hd.le, mul_le_mul_of_nonneg_left (hb 1) hd.le,
      mul_le_mul_of_nonneg_left (hb 2) hd.le]
  refine (Finset.sum_le_sum fun r _ => h1 r).trans ?_
  rw [← Fintype.sum_pow (fun b : TorusBond n => Real.exp (-(del / 3 * (_root_.YangMills.Construction.TorusFields.supDist y b.1 : ℝ)))) 3]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) (bond_expSum_le (by positivity) y) 3
private theorem sum_single_eq (A : LieForm n) : ∑ b, (Pi.single b (A b) : LieForm n) = A := Finset.univ_sum_single A
private theorem third_deriv_le (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    {W : TorusField n} (hW : IsCold σ W) (A : LieForm n) {a : ℝ} (ha : 0 ≤ a) (hA : ∀ b, ‖A b‖ ≤ a) :
    |iteratedFDeriv ℝ 3 (chartFn G W) 0 (fun _ => A)| ≤ a ^ 3 * (K * bondConst (del / 3) ^ 3) := by
  have e : (fun _ : Fin 3 => A) = fun _ => ∑ b, (Pi.single b (A b) : LieForm n) := by
    funext _; rw [sum_single_eq]
  rw [e, ContinuousMultilinearMap.map_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ r : Fin 3 → TorusBond n,
      |iteratedFDeriv ℝ 3 (chartFn G W) 0 fun l => (Pi.single (r l) (A (r l)) : LieForm n)| ≤
        a ^ 3 * K * Real.exp (-(del * (supportDiam y r : ℝ))) := by
    intro r
    refine (iteratedFDeriv_single_le hG hK hW (by norm_num) le_rfl r fun l => A (r l)).trans ?_
    have hp : ∏ l, ‖A (r l)‖ ≤ a ^ 3 := by
      calc _ ≤ ∏ _l : Fin 3, a := Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun l _ => hA _
        _ = _ := by simp
    calc _ ≤ a ^ 3 * (K * Real.exp (-(del * (supportDiam y r : ℝ)))) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum fun r _ => h1 r).trans ?_
  rw [← Finset.mul_sum]
  calc _ ≤ a ^ 3 * K * bondConst (del / 3) ^ 3 := mul_le_mul_of_nonneg_left (triple_expSum_le hd y) (by positivity)
    _ = _ := by ring
private theorem first_deriv_trivial (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hσ : 0 < σ) (A : LieForm n) :
    iteratedFDeriv ℝ 1 (chartFn G (trivialField n)) 0 (fun _ => A) = 0 := by
  have hc := chartFn_contDiffAt (hG.smooth _ (isCold_trivialField hσ))
  have e : (fun _ : Fin 1 => A) = fun _ => ∑ b, (Pi.single b (A b) : LieForm n) := by
    funext _; rw [sum_single_eq]
  rw [e, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [← mixedDeriv_eq hc (by norm_num) r fun l => A (r l)]
  exact hG.deriv_trivial _ _
private theorem expForm_zero (W : TorusField n) : expForm (0 : LieForm n) W = W := by
  funext x i
  have : expUnit (0 : imaginaryQuaternions) = 1 := TorusFields.expUnit_zero
  simp [expForm, this]
private theorem expForm_smul_add (A : LieForm n) (t u : ℝ) :
    expForm (t • A) (expForm (u • A) (trivialField n)) = expForm ((t + u) • A) (trivialField n) := by
  funext x i
  simp only [expForm, trivialField, Pi.smul_apply, mul_one]
  exact (ColdStepAtMirrorFrames.SmallUnits.expUnit_add_smul t u (A (x, i))).symm
private def ray (G : TorusField n → ℝ) (A : LieForm n) (u : ℝ) : ℝ := G (expForm (u • A) (trivialField n))
private theorem ray_shift (G : TorusField n → ℝ) (A : LieForm n) (u : ℝ) :
    (fun t => ray G A (t + u)) =
      chartFn G (expForm (u • A) (trivialField n)) ∘ ContinuousLinearMap.toSpanSingleton ℝ A := by
  funext t
  simp only [ray, chartFn, Function.comp, ContinuousLinearMap.toSpanSingleton_apply, expForm_smul_add]
private theorem ray_shift_contDiffAt {A : LieForm n} {u : ℝ}
    (h : ContDiffAt ℝ 3 (chartFn G (expForm (u • A) (trivialField n))) 0) :
    ContDiffAt ℝ 3 (fun t => ray G A (t + u)) 0 := by
  rw [ray_shift]
  exact ContDiffAt.comp _ (by simpa using h) (ContinuousLinearMap.toSpanSingleton ℝ A).contDiff.contDiffAt
private theorem ray_contDiffAt {A : LieForm n} {u : ℝ}
    (h : ContDiffAt ℝ 3 (chartFn G (expForm (u • A) (trivialField n))) 0) :
    ContDiffAt ℝ 3 (ray G A) u := by
  have h1 := ray_shift_contDiffAt h
  have h2 : ContDiffAt ℝ 3 ((fun t => ray G A (t + u)) ∘ fun z => z - u) u :=
    ContDiffAt.comp _ (by simpa using h1) (contDiff_id.sub contDiff_const).contDiffAt
  have e : ((fun t => ray G A (t + u)) ∘ fun z => z - u) = ray G A := by
    funext z
    simp
  rwa [e] at h2
private theorem iteratedDeriv_ray {A : LieForm n} {u : ℝ}
    (h : ContDiffAt ℝ 3 (chartFn G (expForm (u • A) (trivialField n))) 0) {j : ℕ} (hj : j ≤ 3) :
    iteratedDeriv j (ray G A) u = iteratedFDeriv ℝ j (chartFn G (expForm (u • A) (trivialField n))) 0 fun _ => A := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have s := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := ray G A) j u 0
  simp only [zero_add] at s
  rw [← s, ray_shift]
  rw [iteratedFDeriv_comp_clm _ _ 0 (by simpa using h) j hj]
  simp
private theorem isCold_expForm {A : LieForm n} {a : ℝ} (hA : ∀ b, ‖A b‖ ≤ a) (h : 4 * a < σ) :
    IsCold σ (expForm A (trivialField n)) := by
  intro x μ ν _
  have hg : ∀ b : TorusBond n, BlockOffsets.distFromOne (expUnit (A b)) ≤ a := fun b =>
    (BlockOffsets.distFromOne_expUnit_le _).trans (hA b)
  have e : curvature (expForm A (trivialField n)) x μ ν =
      BlockOffsets.distFromOne (holonomy (expForm A (trivialField n)) x μ ν) := rfl
  rw [e]
  have ee : ∀ (x : TorusSite n) (i : Fin 4), expForm A (trivialField n) x i = expUnit (A (x, i)) := fun x i => by
    simp [expForm, trivialField]
  unfold holonomy
  simp only [ee]
  have h1 := BlockOffsets.distFromOne_mul
    (expUnit (A (x, μ)) * expUnit (A (x + unitStep n μ, ν)) * (expUnit (A (x + unitStep n ν, μ)))⁻¹)
    (expUnit (A (x, ν)))⁻¹
  have h2 := BlockOffsets.distFromOne_mul (expUnit (A (x, μ)) * expUnit (A (x + unitStep n μ, ν)))
    (expUnit (A (x + unitStep n ν, μ)))⁻¹
  have h3 := BlockOffsets.distFromOne_mul (expUnit (A (x, μ))) (expUnit (A (x + unitStep n μ, ν)))
  rw [BlockOffsets.distFromOne_inv] at h1 h2
  have := hg (x, μ)
  have := hg (x + unitStep n μ, ν)
  have := hg (x + unitStep n ν, μ)
  have := hg (x, ν)
  linarith
private def hessian (G : TorusField n → ℝ) : LieForm n →L[ℝ] LieForm n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (chartFn G (trivialField n))) 0
private theorem taylor_ray {A : LieForm n} {M : ℝ}
    (hc : ∀ u ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 (chartFn G (expForm (u • A) (trivialField n))) 0)
    (hM : ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 3 (ray G A) u| ≤ M) :
    |ray G A 1 - (ray G A 0 + iteratedDeriv 1 (ray G A) 0 + (1 / 2) * iteratedDeriv 2 (ray G A) 0)| ≤ M := by
  have hd : ∀ u ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 (ray G A) u := fun u hu => ray_contDiffAt (hc u hu)
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hw : ∀ (j : ℕ), j ≤ 3 → ∀ u ∈ Set.Icc (0 : ℝ) 1,
      iteratedDerivWithin j (ray G A) (Set.Icc 0 1) u = iteratedDeriv j (ray G A) u := by
    intro j hj u h
    exact iteratedDerivWithin_eq_iteratedDeriv hu ((hd u h).of_le (by exact_mod_cast hj)) h
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have key := taylor_mean_remainder_bound (f := ray G A) (a := 0) (b := 1) (C := M) (x := 1) (n := 2)
    zero_le_one (fun u h => (hd u h).contDiffWithinAt) h1 (fun u h => by
      rw [hw 3 le_rfl u h]
      simpa using hM u h)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 h0)
  have e : taylorWithinEval (ray G A) 2 (Set.Icc 0 1) 0 1 =
      ray G A 0 + iteratedDeriv 1 (ray G A) 0 + (1 / 2) * iteratedDeriv 2 (ray G A) 0 := by
    simp only [taylorWithinEval_succ, taylor_within_zero_eval]
    rw [hw 1 (by norm_num) 0 h0, hw 2 (by norm_num) 0 h0]
    norm_num [Nat.factorial]
  rw [e] at key
  rw [← Real.norm_eq_abs]
  refine key.trans ?_
  norm_num [Nat.factorial]
  linarith
private theorem quadratic_approx (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    (hσ : 0 < σ) {A : LieForm n} {a : ℝ} (ha : 0 ≤ a) (hA : ∀ b, ‖A b‖ ≤ a) (h4 : 4 * a < σ) :
    |G (expForm A (trivialField n)) - (1 / 2) * hessian G A A| ≤ a ^ 3 * (K * bondConst (del / 3) ^ 3) := by
  have hu : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ b, ‖(u • A) b‖ ≤ a := by
    intro u h b
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg h.1]
    calc _ ≤ 1 * a := mul_le_mul h.2 (hA b) (norm_nonneg _) zero_le_one
      _ = a := one_mul _
  have hcold : ∀ u ∈ Set.Icc (0 : ℝ) 1, IsCold σ (expForm (u • A) (trivialField n)) := fun u h =>
    isCold_expForm (hu u h) h4
  have hc : ∀ u ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 (chartFn G (expForm (u • A) (trivialField n))) 0 :=
    fun u h => chartFn_contDiffAt (hG.smooth _ (hcold u h))
  have hM : ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 3 (ray G A) u| ≤ a ^ 3 * (K * bondConst (del / 3) ^ 3) := by
    intro u h
    rw [iteratedDeriv_ray (hc u h) le_rfl]
    exact third_deriv_le hG hK hd (hcold u h) A ha hA
  have key := taylor_ray (G := G) hc hM
  have h00 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have e0 : ((0 : ℝ) • A) = 0 := zero_smul _ _
  have hc0 := hc 0 h00
  have hfl : expForm ((0 : ℝ) • A) (trivialField n) = trivialField n := by rw [e0, expForm_zero]
  rw [hfl] at hc0
  have s0 : ray G A 0 = 0 := by
    unfold ray
    rw [hfl]
    exact hG.map_trivial
  have s1 : iteratedDeriv 1 (ray G A) 0 = 0 := by
    rw [iteratedDeriv_ray (hc 0 h00) (by norm_num), hfl]
    exact first_deriv_trivial hG hσ A
  have s2 : iteratedDeriv 2 (ray G A) 0 = hessian G A A := by
    rw [iteratedDeriv_ray (hc 0 h00) (by norm_num), hfl, iteratedFDeriv_two_apply]
    rfl
  have s3 : ray G A 1 = G (expForm A (trivialField n)) := by
    unfold ray
    rw [one_smul]
  rw [s0, s1, s2, s3] at key
  simpa using key
end
section
variable {n : ℕ} [NeZero n]
variable {σ K del c ρ₀ : ℝ} {G : TorusField n → ℝ} {y : TorusSite n}
private theorem hessian_symm (hc : ContDiffAt ℝ 3 (chartFn G (trivialField n)) 0) (A B : LieForm n) :
    hessian G A B = hessian G B A :=
  (hc.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]; norm_num)) A B
private theorem eq_zero_of_cubic {a C t₀ : ℝ} (ht : 0 < t₀)
    (h : ∀ t, 0 < t → t ≤ t₀ → |t ^ 2 * a| ≤ C * t ^ 3) : a = 0 := by
  by_contra ha
  have ha' : 0 < |a| := abs_pos.mpr ha
  set t := min t₀ (|a| / (2 * (|C| + 1))) with hdef
  have hC : 0 < 2 * (|C| + 1) := by positivity
  have h1 : 0 < t := lt_min ht (by positivity)
  have h2 := h t h1 (min_le_left _ _)
  have h3 : t * (2 * (|C| + 1)) ≤ |a| := by
    have := min_le_right t₀ (|a| / (2 * (|C| + 1)))
    rw [le_div_iff₀ hC] at this
    exact this
  rw [abs_mul, abs_of_pos (by positivity : 0 < t ^ 2)] at h2
  have h4 : t ^ 2 * |a| ≤ |C| * t ^ 3 := h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have h5 : |a| ≤ |C| * t := by
    have : t ^ 2 * |a| ≤ t ^ 2 * (|C| * t) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  nlinarith [abs_nonneg C]
private theorem hessian_single_le_span (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hσ : 0 < σ)
    (b b' : TorusBond n) (X Y : imaginaryQuaternions) : |hessian G (Pi.single b X) (Pi.single b' Y)| ≤
      ‖X‖ * ‖Y‖ * (K * Real.exp (-(del * (supportDiam y ![b, b'] : ℝ)))) := by
  have h := iteratedFDeriv_single_le hG hK (isCold_trivialField hσ) (k := 2) (by norm_num) (by norm_num)
    ![b, b'] ![X, Y]
  rw [iteratedFDeriv_two_apply] at h
  unfold hessian
  simpa [Fin.prod_univ_two] using h
private theorem hessian_expand (A A' : LieForm n) :
    hessian G A A' = ∑ b, ∑ b', hessian G (Pi.single b (A b)) (Pi.single b' (A' b')) := by
  conv_lhs => rw [← sum_single_eq A, ← sum_single_eq A']
  simp only [map_sum, ContinuousLinearMap.sum_apply]
  rw [Finset.sum_comm]
private theorem hessian_le (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del) (hσ : 0 < σ)
    (u w : LieForm n) :
    |hessian G u w| ≤ K * (Fintype.card (TorusBond n) : ℝ) ^ 2 * ‖u‖ * ‖w‖ := by
  rw [hessian_expand]
  have h1 : ∀ b b', |hessian G (Pi.single b (u b)) (Pi.single b' (w b'))| ≤ ‖u‖ * ‖w‖ * K := by
    intro b b'
    refine (hessian_single_le_span hG hK hσ b b' _ _).trans ?_
    have e : Real.exp (-(del * (supportDiam y ![b, b'] : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ del * (supportDiam y ![b, b'] : ℝ) := by positivity
      linarith
    have n1 := norm_le_pi_norm u b
    have n2 := norm_le_pi_norm w b'
    calc _ ≤ ‖u‖ * ‖w‖ * (K * 1) := by gcongr
      _ = _ := by ring
  calc _ ≤ ∑ b : TorusBond n, ∑ b' : TorusBond n, ‖u‖ * ‖w‖ * K :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b' _ => h1 b b'))
    _ = _ := by
      simp [Finset.card_univ]
      ring
private theorem hessian_eq_of_near (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    (hσ : 0 < σ) (v B : LieForm n) {C₁ t₀ : ℝ} (hC : 0 ≤ C₁) (ht₀ : 0 < t₀)
    (h : ∀ t, 0 < t → t ≤ t₀ → ∃ Θ : LieForm n, G (expForm Θ (trivialField n)) = G (expForm (t • B) (trivialField n)) ∧
      ‖Θ - t • v‖ ≤ C₁ * t ^ 2) : hessian G v v = hessian G B B := by
  set M := K * bondConst (del / 3) ^ 3 with hM
  set c1 := ‖v‖ + C₁ with hc1
  have hc10 : 0 ≤ c1 := add_nonneg (norm_nonneg _) hC
  set Nq := K * (Fintype.card (TorusBond n) : ℝ) ^ 2 with hNq
  set t₁ := min (min t₀ 1) (σ / (8 * (c1 + ‖B‖ + 1))) with ht₁
  have hden : 0 < 8 * (c1 + ‖B‖ + 1) := by positivity
  have ht₁0 : 0 < t₁ := lt_min (lt_min ht₀ one_pos) (by positivity)
  have sub : hessian G v v - hessian G B B = 0 := by
    refine eq_zero_of_cubic (C := 2 * (c1 ^ 3 + ‖B‖ ^ 3) * M + Nq * (2 * ‖v‖ * C₁ + C₁ ^ 2)) ht₁0
      fun t ht htt => ?_
    have ht0 : t ≤ t₀ := htt.trans ((min_le_left _ _).trans (min_le_left _ _))
    have ht1 : t ≤ 1 := htt.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hts : t * (8 * (c1 + ‖B‖ + 1)) ≤ σ := by
      have := htt.trans (min_le_right _ _)
      rwa [le_div_iff₀ hden] at this
    obtain ⟨Θ, hΘ, hn⟩ := h t ht ht0
    set ε := Θ - t • v with hε
    have hΘe : Θ = t • v + ε := by rw [hε]; abel
    have hΘn : ‖Θ‖ ≤ t * c1 := by
      rw [hΘe]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have : C₁ * t ^ 2 ≤ C₁ * t := mul_le_mul_of_nonneg_left (by nlinarith) hC
      rw [hc1]
      nlinarith
    have q1 := quadratic_approx hG hK hd hσ (A := Θ) (a := t * c1) (by positivity)
      (fun b => (norm_le_pi_norm Θ b).trans hΘn) (by nlinarith [norm_nonneg B])
    have hB : ∀ b, ‖(t • B) b‖ ≤ t * ‖B‖ := fun b => by
      refine (norm_le_pi_norm (t • B) b).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have q2 := quadratic_approx hG hK hd hσ (A := t • B) (a := t * ‖B‖) (by positivity) hB
      (by nlinarith [norm_nonneg B])
    rw [hΘ] at q1
    rw [← hM] at q1 q2
    have e2 : hessian G (t • B) (t • B) = t ^ 2 * hessian G B B := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    have e3 : hessian G Θ Θ = t ^ 2 * hessian G v v + (t * hessian G v ε + t * hessian G ε v + hessian G ε ε) := by
      rw [hΘe]
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    have b1 : |hessian G v ε| ≤ Nq * ‖v‖ * ‖ε‖ := hessian_le hG hK hd hσ v ε
    have b2 : |hessian G ε v| ≤ Nq * ‖ε‖ * ‖v‖ := hessian_le hG hK hd hσ ε v
    have b3 : |hessian G ε ε| ≤ Nq * ‖ε‖ * ‖ε‖ := hessian_le hG hK hd hσ ε ε
    have b4 : |t * hessian G v ε + t * hessian G ε v + hessian G ε ε| ≤ Nq * (2 * ‖v‖ * C₁ + C₁ ^ 2) * t ^ 3 := by
      have k1 : |t * hessian G v ε| ≤ t * (Nq * ‖v‖ * (C₁ * t ^ 2)) := by
        rw [abs_mul, abs_of_pos ht]
        exact mul_le_mul_of_nonneg_left (b1.trans (mul_le_mul_of_nonneg_left hn (by positivity))) ht.le
      have k2 : |t * hessian G ε v| ≤ t * (Nq * ‖v‖ * (C₁ * t ^ 2)) := by
        rw [abs_mul, abs_of_pos ht]
        refine mul_le_mul_of_nonneg_left (b2.trans ?_) ht.le
        calc Nq * ‖ε‖ * ‖v‖ = Nq * ‖v‖ * ‖ε‖ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)
      have k3 : |hessian G ε ε| ≤ Nq * (C₁ * t ^ 2) * (C₁ * t ^ 2) := b3.trans (by
        have := norm_nonneg ε
        gcongr)
      have k4 : Nq * (C₁ * t ^ 2) * (C₁ * t ^ 2) ≤ Nq * C₁ ^ 2 * t ^ 3 := by
        have : t ^ 4 ≤ t ^ 3 := by nlinarith [pow_pos ht 3]
        calc Nq * (C₁ * t ^ 2) * (C₁ * t ^ 2) = Nq * C₁ ^ 2 * t ^ 4 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
      calc _ ≤ |t * hessian G v ε| + |t * hessian G ε v| + |hessian G ε ε| := abs_add_three _ _ _
        _ ≤ t * (Nq * ‖v‖ * (C₁ * t ^ 2)) + t * (Nq * ‖v‖ * (C₁ * t ^ 2)) + Nq * C₁ ^ 2 * t ^ 3 := by linarith
        _ = _ := by ring
    rw [e3] at q1
    rw [e2] at q2
    have fin1 := abs_le.mp q1
    have fin2 := abs_le.mp q2
    have fin3 := abs_le.mp b4
    have p1 : (t * c1) ^ 3 * M = c1 ^ 3 * M * t ^ 3 := by ring
    have p2 : (t * ‖B‖) ^ 3 * M = ‖B‖ ^ 3 * M * t ^ 3 := by ring
    rw [p1] at fin1
    rw [p2] at fin2
    obtain ⟨f1a, f1b⟩ := fin1
    obtain ⟨f2a, f2b⟩ := fin2
    obtain ⟨f3a, f3b⟩ := fin3
    rw [abs_le]
    constructor <;> linarith
  linarith
private theorem minimalLog_three (a₁ a₂ a₃ : imaginaryQuaternions) (hr : ‖a₁‖ + ‖a₂‖ + ‖a₃‖ ≤ 1 / 2) :
    ‖LumpContours.minimalLog (expUnit a₁ * expUnit a₂ * expUnit a₃) - (a₁ + a₂ + a₃)‖ ≤
      5 * (‖a₁‖ + ‖a₂‖ + ‖a₃‖) ^ 2 := by
  set r := ‖a₁‖ + ‖a₂‖ + ‖a₃‖ with hrd
  have n1 := norm_nonneg a₁
  have n2 := norm_nonneg a₂
  have n3 := norm_nonneg a₃
  have hr1 : ‖a₁‖ ≤ 1 := by linarith
  have hr2 : ‖a₂‖ ≤ 1 := by linarith
  have hr3 : ‖a₃‖ ≤ 1 := by linarith
  set q := expUnit a₁ * expUnit a₂ * expUnit a₃ with hq
  set w := LumpContours.minimalLog q with hw
  have hg : BlockOffsets.distFromOne q ≤ r := by
    have h1 := BlockOffsets.distFromOne_mul (expUnit a₁ * expUnit a₂) (expUnit a₃)
    have h2 := BlockOffsets.distFromOne_mul (expUnit a₁) (expUnit a₂)
    have := BlockOffsets.distFromOne_expUnit_le a₁
    have := BlockOffsets.distFromOne_expUnit_le a₂
    have := BlockOffsets.distFromOne_expUnit_le a₃
    rw [hq, hrd]
    linarith
  have hwn : ‖w‖ ≤ 2 * r := by
    have := GaugeFixing.norm_minimalLog_le q
    have e : BlockOffsets.distFromOne q = ‖(q : ℍ[ℝ]) - 1‖ := rfl
    have e' : ‖w‖ = ‖(LumpContours.minimalLog q : ℍ[ℝ])‖ := rfl
    rw [e']
    linarith
  have hw1 : ‖w‖ ≤ 1 := by linarith
  have hexp := ColdStepAtMirrorFrames.SmallUnits.norm_expUnit_sub_one_sub_le w hw1
  rw [hw, GaugeFixing.expUnit_minimalLog, ← hw] at hexp
  have e1 := ColdStepAtMirrorFrames.SmallUnits.norm_expUnit_sub_one_sub_le a₁ hr1
  have e2 := ColdStepAtMirrorFrames.SmallUnits.norm_expUnit_sub_one_sub_le a₂ hr2
  have e3 := ColdStepAtMirrorFrames.SmallUnits.norm_expUnit_sub_one_sub_le a₃ hr3
  have g1 : ‖((expUnit a₁ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖a₁‖ := BlockOffsets.distFromOne_expUnit_le a₁
  have g2 : ‖((expUnit a₂ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖a₂‖ := BlockOffsets.distFromOne_expUnit_le a₂
  have g3 : ‖((expUnit a₃ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖a₃‖ := BlockOffsets.distFromOne_expUnit_le a₃
  have g23 : ‖((expUnit a₂ * expUnit a₃ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖a₂‖ + ‖a₃‖ :=
    (BlockOffsets.distFromOne_mul _ _).trans
      (add_le_add (BlockOffsets.distFromOne_expUnit_le a₂) (BlockOffsets.distFromOne_expUnit_le a₃))
  set E₁ := ((expUnit a₁ : UnitQuaternion) : ℍ[ℝ]) with hE1
  set E₂ := ((expUnit a₂ : UnitQuaternion) : ℍ[ℝ]) with hE2
  set E₃ := ((expUnit a₃ : UnitQuaternion) : ℍ[ℝ]) with hE3
  have hqc : (q : ℍ[ℝ]) = E₁ * E₂ * E₃ := rfl
  have h23 : ((expUnit a₂ * expUnit a₃ : UnitQuaternion) : ℍ[ℝ]) = E₂ * E₃ := rfl
  rw [h23] at g23
  have D : (q : ℍ[ℝ]) - 1 - ((a₁ : ℍ[ℝ]) + (a₂ : ℍ[ℝ]) + (a₃ : ℍ[ℝ])) =
      (E₁ - 1 - (a₁ : ℍ[ℝ])) + (E₂ - 1 - (a₂ : ℍ[ℝ])) + (E₃ - 1 - (a₃ : ℍ[ℝ])) +
        (E₁ - 1) * (E₂ * E₃ - 1) + (E₂ - 1) * (E₃ - 1) := by
    rw [hqc]
    noncomm_ring
  have hD : ‖(q : ℍ[ℝ]) - 1 - ((a₁ : ℍ[ℝ]) + (a₂ : ℍ[ℝ]) + (a₃ : ℍ[ℝ]))‖ ≤ r ^ 2 := by
    rw [D]
    have m1 : ‖(E₁ - 1) * (E₂ * E₃ - 1)‖ ≤ ‖a₁‖ * (‖a₂‖ + ‖a₃‖) := by
      rw [norm_mul]
      exact mul_le_mul g1 g23 (norm_nonneg _) n1
    have m2 : ‖(E₂ - 1) * (E₃ - 1)‖ ≤ ‖a₂‖ * ‖a₃‖ := by
      rw [norm_mul]
      exact mul_le_mul g2 g3 (norm_nonneg _) n2
    calc _ ≤ ‖E₁ - 1 - (a₁ : ℍ[ℝ])‖ + ‖E₂ - 1 - (a₂ : ℍ[ℝ])‖ + ‖E₃ - 1 - (a₃ : ℍ[ℝ])‖ +
          ‖(E₁ - 1) * (E₂ * E₃ - 1)‖ + ‖(E₂ - 1) * (E₃ - 1)‖ := by
          refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
          refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
          refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
          exact norm_add_le _ _
      _ ≤ ‖a₁‖ ^ 2 + ‖a₂‖ ^ 2 + ‖a₃‖ ^ 2 + ‖a₁‖ * (‖a₂‖ + ‖a₃‖) + ‖a₂‖ * ‖a₃‖ := by linarith
      _ ≤ r ^ 2 := by
        rw [hrd]
        nlinarith [mul_nonneg n1 n2, mul_nonneg n1 n3, mul_nonneg n2 n3]
  have final : ((w - (a₁ + a₂ + a₃) : imaginaryQuaternions) : ℍ[ℝ]) =
      ((q : ℍ[ℝ]) - 1 - ((a₁ : ℍ[ℝ]) + (a₂ : ℍ[ℝ]) + (a₃ : ℍ[ℝ]))) - ((q : ℍ[ℝ]) - 1 - (w : ℍ[ℝ])) := by
    push_cast
    abel
  have e' : ‖w - (a₁ + a₂ + a₃)‖ = ‖((w - (a₁ + a₂ + a₃) : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
  rw [e', final]
  refine (norm_sub_le _ _).trans ?_
  have hsq : ‖w‖ ^ 2 ≤ (2 * r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwn 2
  linarith
end
section
variable {n : ℕ} [NeZero n]
private def offsetOf (y z : TorusSite n) : Offset := fun l => (z l - y l).valMinAbs
private theorem add_siteOfInt_offsetOf (y z : TorusSite n) : y + siteOfInt (offsetOf y z) = z := by apply _root_.YangMills.DeltaSharedProofs.p500399 <;> assumption
private theorem natAbs_valMinAbs_cast_le (m : ℤ) : (((m : ZMod n)).valMinAbs).natAbs ≤ m.natAbs := by apply _root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le <;> assumption
private theorem offsetOf_add_siteOfInt (y : TorusSite n) (h : Offset) (hs : ∀ l, 2 * |h l| < n) :
    offsetOf y (y + siteOfInt h) = h := by apply _root_.YangMills.Construction.AbelianSecondOrder.offsetFrom_add_siteOfInt <;> assumption
private theorem supDist_le_iff_offset (z y : TorusSite n) (r : ℕ) :
    _root_.YangMills.Construction.TorusFields.supDist z y ≤ r ↔ ∀ l, (offsetOf y z l).natAbs ≤ r := by apply _root_.YangMills.Construction.TorusFields.supDist_le_iff <;> assumption
private theorem supDist_symm (x y : TorusSite n) : _root_.YangMills.Construction.TorusFields.supDist x y = _root_.YangMills.Construction.TorusFields.supDist y x := by apply _root_.YangMills.Construction.TorusFields.supDist_comm <;> assumption
private theorem mem_supBall_iff {ρ₀ : ℝ} (h0 : 0 ≤ ρ₀) (y z : TorusSite n) :
    z ∈ supBall y ρ₀ ↔ _root_.YangMills.Construction.TorusFields.supDist z y ≤ ⌊ρ₀⌋₊ := by
  unfold supBall
  simp [Nat.le_floor_iff h0]
private theorem supDist_add_siteOfInt_le (y : TorusSite n) (c : Offset) (r : ℕ) (hc : ∀ l, (c l).natAbs ≤ r) :
    _root_.YangMills.Construction.TorusFields.supDist (y + siteOfInt c) y ≤ r := by
  rw [supDist_le_iff_offset]
  intro l
  unfold offsetOf siteOfInt
  simp only [Pi.add_apply, add_sub_cancel_left]
  exact (natAbs_valMinAbs_cast_le _).trans (hc l)
abbrev _root_.YangMills.DeltaSharedProofs.p502390 := @supDist_add_siteOfInt_le
private theorem siteOfInt_add_unit (h : Offset) (i : Fin 4) :
    (siteOfInt (h + unitOffset i) : TorusSite n) = siteOfInt h + unitStep n i := by apply _root_.YangMills.DeltaSharedProofs.p500445 <;> assumption
private theorem natAbs_add_unit_le (h : Offset) (i l : Fin 4) :
    ((h + unitOffset i) l).natAbs ≤ (h l).natAbs + 1 := by
  unfold unitOffset
  by_cases e : l = i
  · subst e; simp
    omega
  · simp [e]
private theorem supDist_add_unitStep_le (z y : TorusSite n) (i : Fin 4) :
    _root_.YangMills.Construction.TorusFields.supDist (z + unitStep n i) y ≤ _root_.YangMills.Construction.TorusFields.supDist z y + 1 := by apply _root_.YangMills.SharedProofs.p13239 <;> assumption
private def pullback (y : TorusSite n) (A : TorusBond n → imaginaryQuaternions) :
    Offset → Fin 4 → imaginaryQuaternions := fun h i => A (y + siteOfInt h, i)
private theorem latticeCurl_pullback (y : TorusSite n) (A : TorusBond n → imaginaryQuaternions) (h : Offset)
    (μ ν : Fin 4) : latticeCurl (pullback y A) h μ ν = lieFormCurl A (y + siteOfInt h, μ, ν) := by
  unfold latticeCurl pullback lieFormCurl
  simp only [siteOfInt_add_unit, add_assoc]
private def boxPotential (y : TorusSite n) (ρ₀ : ℝ) (A : TorusBond n → imaginaryQuaternions) (z : TorusSite n) :
    imaginaryQuaternions :=
  if z ∈ supBall y ρ₀ then -axialPotential (pullback y A) (offsetOf y z) else 0
private def gradient (lam : TorusSite n → imaginaryQuaternions) (b : TorusBond n) : imaginaryQuaternions :=
  lam b.1 - lam (b.1 + unitStep n b.2)
private def gradientFree (y : TorusSite n) (ρ₀ : ℝ) (A : TorusBond n → imaginaryQuaternions) (b : TorusBond n) :
    imaginaryQuaternions :=
  A b - gradient (boxPotential y ρ₀ A) b
private def IsInnerBond (y : TorusSite n) (ρ₀ : ℝ) (b : TorusBond n) : Prop :=
  b.1 ∈ supBall y ρ₀ ∧ b.1 + unitStep n b.2 ∈ supBall y ρ₀
private def combPlaquette (y : TorusSite n) (h : Offset) (i j : Fin 4) (t : ℤ) : TorusPlaquette n :=
  (y + siteOfInt (truncateAt j h t), i, j)
private def passCount (ψ : ℤ → TorusPlaquette n) (m : ℤ) (p : TorusPlaquette n) : ℝ :=
  signedSum (fun t => if ψ t = p then (1 : ℝ) else 0) m
private theorem signedSum_eq_sum {V : Type*} [AddCommGroup V] [Module ℝ V] (ψ : ℤ → TorusPlaquette n) (m : ℤ)
    (F : TorusPlaquette n → V) (P : Finset (TorusPlaquette n))
    (hP : ∀ t, t ∈ Finset.Ico 0 m ∨ t ∈ Finset.Ico m 0 → ψ t ∈ P) :
    signedSum (fun t => F (ψ t)) m = ∑ p ∈ P, passCount ψ m p • F p := by
  have key : ∀ S : Finset ℤ, (∀ t ∈ S, ψ t ∈ P) →
      ∑ p ∈ P, (∑ t ∈ S, (if ψ t = p then (1 : ℝ) else 0)) • F p = ∑ t ∈ S, F (ψ t) := by
    intro S hS
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t ht => ?_
    simp [ite_smul, hS t ht]
  unfold passCount signedSum
  simp only [sub_smul, Finset.sum_sub_distrib]
  rw [key _ fun t ht => hP t (Or.inl ht), key _ fun t ht => hP t (Or.inr ht)]
private theorem abs_passCount_le (ψ : ℤ → TorusPlaquette n) (m : ℤ) (p : TorusPlaquette n) :
    |passCount ψ m p| ≤ |(m : ℝ)| := by
  have := norm_signedSum_le (fun t => if ψ t = p then (1 : ℝ) else 0) m 1 (fun t => by split_ifs <;> simp)
  simpa [passCount] using this
private theorem exists_of_passCount_ne (ψ : ℤ → TorusPlaquette n) (m : ℤ) (p : TorusPlaquette n)
    (h : passCount ψ m p ≠ 0) :
    ∃ t, (t ∈ Finset.Ico 0 m ∨ t ∈ Finset.Ico m 0) ∧ ψ t = p := by
  by_contra hn
  push_neg at hn
  apply h
  unfold passCount signedSum
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
  · intro t ht; rw [if_neg (hn t (Or.inr ht))]
  · intro t ht; rw [if_neg (hn t (Or.inl ht))]
open Classical in
private def combCoeff (y : TorusSite n) (ρ₀ : ℝ) (b : TorusBond n) (p : TorusPlaquette n) : ℝ :=
  if IsInnerBond y ρ₀ b then
    ∑ j : Fin 4, if b.2 < j then -passCount (combPlaquette y (offsetOf y b.1) b.2 j) (offsetOf y b.1 j) p else 0
  else 0
private theorem combCoeff_outer {y : TorusSite n} {ρ₀ : ℝ} {b : TorusBond n} (h : ¬ IsInnerBond y ρ₀ b)
    (p : TorusPlaquette n) : combCoeff y ρ₀ b p = 0 := by
  unfold combCoeff; rw [if_neg h]
private theorem offsetOf_add_unitStep {y z : TorusSite n} {R : ℕ} (hn : 2 * R + 2 < n) (hz : _root_.YangMills.Construction.TorusFields.supDist z y ≤ R)
    (i : Fin 4) : offsetOf y (z + unitStep n i) = offsetOf y z + unitOffset i := by
  have e : z + unitStep n i = y + siteOfInt (offsetOf y z + unitOffset i) := by
    rw [siteOfInt_add_unit, ← add_assoc, add_siteOfInt_offsetOf]
  rw [e]
  refine offsetOf_add_siteOfInt _ _ fun l => ?_
  have h1 := natAbs_add_unit_le (offsetOf y z) i l
  have h2 := (supDist_le_iff_offset z y R).mp hz l
  have h3 : |(offsetOf y z + unitOffset i) l| = ((offsetOf y z + unitOffset i) l).natAbs := Int.abs_eq_natAbs _
  rw [h3]
  omega
private theorem natAbs_truncateAt_le {h : Offset} {j : Fin 4} {t : ℤ}
    (ht : t ∈ Finset.Ico 0 (h j) ∨ t ∈ Finset.Ico (h j) 0)
    (l : Fin 4) {r : ℕ} (hr : ∀ l, (h l).natAbs ≤ r) : (truncateAt j h t l).natAbs ≤ r := by
  unfold truncateAt
  have hj := hr j
  simp only [Finset.mem_Ico] at ht
  split_ifs
  · exact hr l
  · omega
  · simp
private theorem unitOffset_apply (i l : Fin 4) : unitOffset i l = if l = i then 1 else 0 := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.StaircaseHomotopy.basisVector_apply <;> assumption
private theorem natAbs_corner_le {h : Offset} {i j : Fin 4} {t : ℤ} {R : ℕ} (hij : i < j)
    (h1 : ∀ l, (h l).natAbs ≤ R)
    (h2 : ∀ l, ((h + unitOffset i) l).natAbs ≤ R) (ht : t ∈ Finset.Ico 0 (h j) ∨ t ∈ Finset.Ico (h j) 0)
    (u v : ℤ) (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) (l : Fin 4) :
    (truncateAt j h t l + (if l = i then u else 0) + (if l = j then v else 0)).natAbs ≤ R := by
  have e1 := h1 l
  have e2 := h2 l
  have e3 := h1 j
  simp only [Pi.add_apply, unitOffset_apply] at e2
  simp only [Finset.mem_Ico] at ht
  unfold truncateAt
  rcases lt_trichotomy l j with c | c | c
  · rw [if_pos c, if_neg (ne_of_lt c)]
    by_cases q : l = i
    · rw [if_pos q] at e2 ⊢
      omega
    · rw [if_neg q] at e2 ⊢
      omega
  · subst c
    have q : l ≠ i := ne_of_gt hij
    rw [if_neg (lt_irrefl _), if_pos rfl, if_neg q, if_pos rfl]
    omega
  · have q : l ≠ i := ne_of_gt (hij.trans c)
    rw [if_neg (not_lt.mpr c.le), if_neg (ne_of_gt c), if_neg q, if_neg (ne_of_gt c)]
    simp
private theorem combPlaquette_mem {y : TorusSite n} {ρ₀ : ℝ} (h0 : 0 ≤ ρ₀) (hn : 2 * ⌊ρ₀⌋₊ + 2 < n)
    {b : TorusBond n} (hb : IsInnerBond y ρ₀ b) {j : Fin 4} (hij : b.2 < j) {t : ℤ}
    (ht : t ∈ Finset.Ico 0 (offsetOf y b.1 j) ∨ t ∈ Finset.Ico (offsetOf y b.1 j) 0) :
    combPlaquette y (offsetOf y b.1) b.2 j t ∈ plaquettesIn (supBall y ρ₀) := by
  have h1 : ∀ l, (offsetOf y b.1 l).natAbs ≤ ⌊ρ₀⌋₊ :=
    (supDist_le_iff_offset _ _ _).mp ((mem_supBall_iff h0 _ _).mp hb.1)
  have h2 : ∀ l, ((offsetOf y b.1 + unitOffset b.2) l).natAbs ≤ ⌊ρ₀⌋₊ := by
    have := (supDist_le_iff_offset _ _ _).mp ((mem_supBall_iff h0 _ _).mp hb.2)
    rwa [offsetOf_add_unitStep hn ((mem_supBall_iff h0 _ _).mp hb.1)] at this
  have hc := natAbs_corner_le hij h1 h2 ht
  set c := truncateAt j (offsetOf y b.1) t with hcdef
  have inb : ∀ c' : Offset, (∀ l, (c' l).natAbs ≤ ⌊ρ₀⌋₊) → y + siteOfInt c' ∈ supBall y ρ₀ := fun c' h' =>
    (mem_supBall_iff h0 _ _).mpr (supDist_add_siteOfInt_le _ _ _ h')
  unfold plaquettesIn combPlaquette
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hij, ?_⟩
  intro z hz
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · refine inb c fun l => ?_
    simpa using hc 0 0 (by norm_num) (by norm_num) l
  · rw [add_assoc, ← siteOfInt_add_unit]
    refine inb _ fun l => ?_
    have := hc 1 0 (by norm_num) (by norm_num) l
    simpa [unitOffset_apply] using this
  · rw [add_assoc, ← siteOfInt_add_unit]
    refine inb _ fun l => ?_
    have := hc 0 1 (by norm_num) (by norm_num) l
    simpa [unitOffset_apply] using this
  · have e : y + siteOfInt c + unitStep n b.2 + unitStep n j = y + siteOfInt (c + unitOffset b.2 + unitOffset j) := by
      rw [siteOfInt_add_unit, siteOfInt_add_unit]; simp only [add_assoc]
    rw [e]
    refine inb _ fun l => ?_
    have := hc 1 1 (by norm_num) (by norm_num) l
    simpa [unitOffset_apply, add_assoc] using this
private theorem gradientFree_inner {y : TorusSite n} {ρ₀ : ℝ} (h0 : 0 ≤ ρ₀) (hn : 2 * ⌊ρ₀⌋₊ + 2 < n)
    (A : TorusBond n → imaginaryQuaternions) {b : TorusBond n} (hb : IsInnerBond y ρ₀ b) :
    gradientFree y ρ₀ A b = ∑ p ∈ plaquettesIn (supBall y ρ₀), combCoeff y ρ₀ b p • lieFormCurl A p := by
  obtain ⟨z, i⟩ := b
  have hz : _root_.YangMills.Construction.TorusFields.supDist z y ≤ ⌊ρ₀⌋₊ := (mem_supBall_iff h0 _ _).mp hb.1
  have hform := eq_gradient_add_comb (pullback y A) (offsetOf y z) i
  have e0 : pullback y A (offsetOf y z) i = A (z, i) := by
    unfold pullback; rw [add_siteOfInt_offsetOf]
  have hgrad : gradient (boxPotential y ρ₀ A) (z, i) =
      axialPotential (pullback y A) (offsetOf y z + unitOffset i) - axialPotential (pullback y A) (offsetOf y z) := by
    unfold gradient boxPotential
    simp only
    rw [if_pos hb.1, if_pos hb.2, offsetOf_add_unitStep hn hz]
    abel
  have hl : gradientFree y ρ₀ A (z, i) = curlComb (pullback y A) (offsetOf y z) i := by
    unfold gradientFree
    rw [hgrad, ← e0, hform]
    abel
  rw [hl]
  have hcoef : ∀ p, combCoeff y ρ₀ (z, i) p =
      ∑ j : Fin 4, if i < j then -passCount (combPlaquette y (offsetOf y z) i j) (offsetOf y z j) p else 0 :=
    fun p => by
      unfold combCoeff
      rw [if_pos hb]
  unfold curlComb
  simp only [hcoef, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold axisComb
  by_cases hij : i < j
  · simp only [if_pos hij, neg_smul, Finset.sum_neg_distrib]
    congr 1
    have := signedSum_eq_sum (combPlaquette y (offsetOf y z) i j) (offsetOf y z j) (lieFormCurl A)
      (plaquettesIn (supBall y ρ₀)) (fun t ht => combPlaquette_mem h0 hn hb hij ht)
    rw [← this]
    refine signedSum_congr (fun t => ?_) _
    exact latticeCurl_pullback _ _ _ _ _
  · simp [if_neg hij]
private theorem abs_combCoeff_le (y : TorusSite n) (ρ₀ : ℝ) (b : TorusBond n) (p : TorusPlaquette n) :
    |combCoeff y ρ₀ b p| ≤ 4 * (_root_.YangMills.Construction.TorusFields.supDist b.1 y : ℝ) := by
  unfold combCoeff
  split_ifs with hb
  · have hj : ∀ j : Fin 4,
        |(if b.2 < j then -passCount (combPlaquette y (offsetOf y b.1) b.2 j) (offsetOf y b.1 j) p else 0)| ≤
          (_root_.YangMills.Construction.TorusFields.supDist b.1 y : ℝ) := by
      intro j
      split_ifs
      · rw [abs_neg]
        refine (abs_passCount_le _ _ _).trans ?_
        have h2 := (supDist_le_iff_offset b.1 y _).mp le_rfl j
        have e : |((offsetOf y b.1 j : ℤ) : ℝ)| = (((offsetOf y b.1 j).natAbs : ℕ) : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        rw [e]
        exact_mod_cast h2
      · simp
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ fun j _ => hj j).trans ?_
    simp
  · simp
private theorem combCoeff_support {y : TorusSite n} {ρ₀ : ℝ} {b : TorusBond n} {p : TorusPlaquette n}
    (h : combCoeff y ρ₀ b p ≠ 0) : _root_.YangMills.Construction.TorusFields.supDist p.1 y ≤ _root_.YangMills.Construction.TorusFields.supDist b.1 y := by
  unfold combCoeff at h
  split_ifs at h with hb
  · obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    split_ifs at hj with hij
    · obtain ⟨t, ht, rfl⟩ := exists_of_passCount_ne _ _ _ (neg_ne_zero.mp hj)
      unfold combPlaquette
      exact supDist_add_siteOfInt_le _ _ _ fun l =>
        natAbs_truncateAt_le ht l ((supDist_le_iff_offset _ _ _).mp le_rfl)
    · exact absurd rfl hj
  · exact absurd rfl h
private theorem norm_boxPotential_le {y : TorusSite n} {ρ₀ : ℝ} (h0 : 0 ≤ ρ₀)
    (A : TorusBond n → imaginaryQuaternions) {s : ℝ} (hs : 0 ≤ s)
    (hA : ∀ b, ‖A b‖ ≤ s) (z : TorusSite n) : ‖boxPotential y ρ₀ A z‖ ≤ 4 * (⌊ρ₀⌋₊ : ℝ) * s := by
  unfold boxPotential
  split_ifs with hz
  · rw [norm_neg]
    unfold axialPotential
    have h1 : ∀ l, (offsetOf y z l).natAbs ≤ ⌊ρ₀⌋₊ :=
      (supDist_le_iff_offset _ _ _).mp ((mem_supBall_iff h0 _ _).mp hz)
    have hj : ∀ j : Fin 4, ‖axisPotential (pullback y A) j (offsetOf y z)‖ ≤ (⌊ρ₀⌋₊ : ℝ) * s := by
      intro j
      unfold axisPotential
      refine (norm_signedSum_le _ _ s fun t => hA _).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hs
      have e : |((offsetOf y z j : ℤ) : ℝ)| = (((offsetOf y z j).natAbs : ℕ) : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [e]
      exact_mod_cast h1 j
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ fun j _ => hj j).trans ?_
    simp
    linarith
  · simp only [norm_zero]
    positivity
private theorem norm_gradientFree_le {y : TorusSite n} {ρ₀ : ℝ} (h0 : 0 ≤ ρ₀)
    (A : TorusBond n → imaginaryQuaternions) {s : ℝ} (hs : 0 ≤ s)
    (hA : ∀ b, ‖A b‖ ≤ s) (b : TorusBond n) : ‖gradientFree y ρ₀ A b‖ ≤ (8 * (⌊ρ₀⌋₊ : ℝ) + 1) * s := by
  unfold gradientFree gradient
  have h1 := norm_boxPotential_le (y := y) h0 A hs hA b.1
  have h2 := norm_boxPotential_le (y := y) h0 A hs hA (b.1 + unitStep n b.2)
  have h3 := hA b
  calc _ ≤ ‖A b‖ + ‖boxPotential y ρ₀ A b.1 - boxPotential y ρ₀ A (b.1 + unitStep n b.2)‖ := norm_sub_le _ _
    _ ≤ ‖A b‖ + (‖boxPotential y ρ₀ A b.1‖ + ‖boxPotential y ρ₀ A (b.1 + unitStep n b.2)‖) := by
        gcongr; exact norm_sub_le _ _
    _ ≤ _ := by linarith
private theorem far_of_outer {y : TorusSite n} {ρ₀ : ℝ} (h0 : 0 ≤ ρ₀) {A : TorusBond n → imaginaryQuaternions}
    (hA : ∀ b : TorusBond n, b.1 ∉ supBall y ρ₀ → A b = 0) {b : TorusBond n} (hb : ¬ IsInnerBond y ρ₀ b)
    (hU : gradientFree y ρ₀ A b ≠ 0) : ⌊ρ₀⌋₊ ≤ _root_.YangMills.Construction.TorusFields.supDist b.1 y := by
  by_cases h1 : b.1 ∈ supBall y ρ₀
  · have h2 : b.1 + unitStep n b.2 ∉ supBall y ρ₀ := fun h => hb ⟨h1, h⟩
    rw [mem_supBall_iff h0] at h2
    have := supDist_add_unitStep_le b.1 y b.2
    omega
  · rw [mem_supBall_iff h0] at h1
    omega
end
section
variable {n : ℕ} [NeZero n]
variable {σ K del c ρ₀ : ℝ} {G : TorusField n → ℝ} {y : TorusSite n}
private theorem hessian_add_gradient (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    (hσ : 0 < σ) (lam : TorusSite n → imaginaryQuaternions) (B : LieForm n) :
    hessian G (B + gradient lam) (B + gradient lam) = hessian G B B := by
  set c0 := 2 * ‖lam‖ + ‖B‖ with hc0
  set t₀ := min (1 / (2 * (c0 + 1))) (σ / (8 * (‖B‖ + 1))) with ht₀
  have h1 : 0 < 2 * (c0 + 1) := by positivity
  have h2 : 0 < 8 * (‖B‖ + 1) := by positivity
  have ht₀0 : 0 < t₀ := lt_min (by positivity) (by positivity)
  refine hessian_eq_of_near hG hK hd hσ _ B (C₁ := 5 * c0 ^ 2) (by positivity) ht₀0 fun t ht htt => ?_
  have ha : t * (2 * (c0 + 1)) ≤ 1 := by
    have := htt.trans (min_le_left _ _)
    rwa [le_div_iff₀ h1] at this
  have hb : t * (8 * (‖B‖ + 1)) ≤ σ := by
    have := htt.trans (min_le_right _ _)
    rwa [le_div_iff₀ h2] at this
  have hBt : ∀ b, ‖(t • B) b‖ ≤ t * ‖B‖ := fun b => by
    refine (norm_le_pi_norm (t • B) b).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hcold : IsCold σ (expForm (t • B) (trivialField n)) := isCold_expForm hBt (by nlinarith [norm_nonneg B])
  refine ⟨fun b => LumpContours.minimalLog (expUnit (t • lam b.1) * expUnit (t • B b) *
    expUnit (-(t • lam (b.1 + unitStep n b.2)))), ?_, ?_⟩
  · have e : expForm (fun b : TorusBond n => LumpContours.minimalLog (expUnit (t • lam b.1) * expUnit (t • B b) *
        expUnit (-(t • lam (b.1 + unitStep n b.2))))) (trivialField n) =
        TorusFields.gaugeTransform (fun x => expUnit (t • lam x)) (expForm (t • B) (trivialField n)) := by
      funext x i
      simp only [expForm, trivialField, TorusFields.gaugeTransform, mul_one, GaugeFixing.expUnit_minimalLog,
        Pi.smul_apply, ColdStepAtMirrorFrames.SmallUnits.expUnit_neg]
    rw [e]
    exact hG.gauge_invariant _ _ hcold
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun b => ?_
    have n1 : ‖t • lam b.1‖ ≤ t * ‖lam‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm lam _) ht.le
    have n2 : ‖t • B b‖ ≤ t * ‖B‖ := hBt b
    have n3 : ‖-(t • lam (b.1 + unitStep n b.2))‖ ≤ t * ‖lam‖ := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm lam _) ht.le
    have hr : ‖t • lam b.1‖ + ‖t • B b‖ + ‖-(t • lam (b.1 + unitStep n b.2))‖ ≤ t * c0 := by
      rw [hc0]; nlinarith
    have hr0 : 0 ≤ ‖t • lam b.1‖ + ‖t • B b‖ + ‖-(t • lam (b.1 + unitStep n b.2))‖ := by positivity
    have hl := minimalLog_three (t • lam b.1) (t • B b) (-(t • lam (b.1 + unitStep n b.2))) (by nlinarith)
    have e : (LumpContours.minimalLog (expUnit (t • lam b.1) * expUnit (t • B b) *
        expUnit (-(t • lam (b.1 + unitStep n b.2)))) -
        (t • lam b.1 + t • B b + -(t • lam (b.1 + unitStep n b.2)))) =
        ((fun b : TorusBond n => LumpContours.minimalLog (expUnit (t • lam b.1) * expUnit (t • B b) *
          expUnit (-(t • lam (b.1 + unitStep n b.2))))) - t • (B + gradient lam)) b := by
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, gradient, smul_add, smul_sub]
      abel_nf
    rw [← e]
    refine hl.trans ?_
    have := pow_le_pow_left₀ hr0 hr 2
    nlinarith
private def adjointForm (g : UnitQuaternion) (A : LieForm n) : LieForm n := fun b => _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (A b)
private theorem expForm_adjointForm (g : UnitQuaternion) (A : LieForm n) :
    expForm (adjointForm g A) (trivialField n) =
      TorusFields.gaugeTransform (fun _ => g) (expForm A (trivialField n)) := by
  funext x i
  simp only [expForm, adjointForm, trivialField, TorusFields.gaugeTransform, mul_one,
    ColdStepAtMirrorFrames.Adjoint.expUnit_adjointAction]
private theorem adjointForm_smul (g : UnitQuaternion) (t : ℝ) (A : LieForm n) :
    adjointForm g (t • A) = t • adjointForm g A := by
  funext b
  simp only [adjointForm, Pi.smul_apply, ColdStepAtMirrorFrames.Adjoint.adjointAction_smul]
private theorem adjointForm_add (g : UnitQuaternion) (A B : LieForm n) :
    adjointForm g (A + B) = adjointForm g A + adjointForm g B := by
  funext b
  simp only [adjointForm, Pi.add_apply, ColdStepAtMirrorFrames.Adjoint.adjointAction_add]
private theorem hessian_adjoint_diag (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    (hσ : 0 < σ) (g : UnitQuaternion) (A : LieForm n) :
    hessian G (adjointForm g A) (adjointForm g A) = hessian G A A := by
  have h2 : 0 < 8 * (‖A‖ + 1) := by positivity
  refine hessian_eq_of_near hG hK hd hσ _ A (C₁ := 0) le_rfl (t₀ := σ / (8 * (‖A‖ + 1))) (by positivity)
    fun t ht htt => ?_
  have hb : t * (8 * (‖A‖ + 1)) ≤ σ := by rwa [le_div_iff₀ h2] at htt
  have hBt : ∀ b, ‖(t • A) b‖ ≤ t * ‖A‖ := fun b => by
    refine (norm_le_pi_norm (t • A) b).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hcold : IsCold σ (expForm (t • A) (trivialField n)) := isCold_expForm hBt (by nlinarith [norm_nonneg A])
  refine ⟨t • adjointForm g A, ?_, by simp⟩
  rw [← adjointForm_smul, expForm_adjointForm]
  exact hG.gauge_invariant _ _ hcold
private theorem hessian_adjoint (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    (hσ : 0 < σ) (g : UnitQuaternion) (A B : LieForm n) :
    hessian G (adjointForm g A) (adjointForm g B) = hessian G A B := by
  have hc := chartFn_contDiffAt (hG.smooth _ (isCold_trivialField hσ))
  have h1 := hessian_adjoint_diag hG hK hd hσ g (A + B)
  have h2 := hessian_adjoint_diag hG hK hd hσ g A
  have h3 := hessian_adjoint_diag hG hK hd hσ g B
  rw [adjointForm_add] at h1
  simp only [map_add, ContinuousLinearMap.add_apply] at h1
  have s1 := hessian_symm hc (adjointForm g A) (adjointForm g B)
  have s2 := hessian_symm hc A B
  linarith
private def quat (a b c d : ℝ) : ℍ[ℝ] := ⟨a, b, c, d⟩
@[simp] private theorem quat_re (a b c d : ℝ) : (quat a b c d).re = a := rfl
@[simp] private theorem quat_imI (a b c d : ℝ) : (quat a b c d).imI = b := rfl
@[simp] private theorem quat_imJ (a b c d : ℝ) : (quat a b c d).imJ = c := rfl
@[simp] private theorem quat_imK (a b c d : ℝ) : (quat a b c d).imK = d := rfl
private def unitI : UnitQuaternion := ⟨quat 0 1 0 0, by rw [Unitary.mem_iff]; constructor <;> ext <;> simp⟩
private def unitJ : UnitQuaternion := ⟨quat 0 0 1 0, by rw [Unitary.mem_iff]; constructor <;> ext <;> simp⟩
private def unitCubeRoot : UnitQuaternion := ⟨quat (1 / 2) (1 / 2) (1 / 2) (1 / 2), by
  rw [Unitary.mem_iff]; constructor <;> ext <;> simp <;> norm_num⟩
private theorem adjointAction_of_mul (g : UnitQuaternion) (X Y : imaginaryQuaternions)
    (h : (g : ℍ[ℝ]) * (X : ℍ[ℝ]) = (Y : ℍ[ℝ]) * (g : ℍ[ℝ])) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X = Y := by
  apply Subtype.ext
  rw [ColdStepAtMirrorFrames.Adjoint.coe_adjointAction, h, mul_assoc,
    ColdStepAtMirrorFrames.Adjoint.coe_mul_coe_inv, mul_one]
private theorem adjoint_unitI_zero : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitI (lieBasis 0) = lieBasis 0 := adjointAction_of_mul _ _ _ (by
  show quat 0 1 0 0 * quat 0 1 0 0 = quat 0 1 0 0 * quat 0 1 0 0
  rfl)
private theorem adjoint_unitI_one : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitI (lieBasis 1) = -lieBasis 1 := adjointAction_of_mul _ _ _ (by
  show quat 0 1 0 0 * quat 0 0 1 0 = -(quat 0 0 1 0) * quat 0 1 0 0
  ext <;> simp)
private theorem adjoint_unitI_two : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitI (lieBasis 2) = -lieBasis 2 := adjointAction_of_mul _ _ _ (by
  show quat 0 1 0 0 * quat 0 0 0 1 = -(quat 0 0 0 1) * quat 0 1 0 0
  ext <;> simp)
private theorem adjoint_unitJ_one : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitJ (lieBasis 1) = lieBasis 1 := adjointAction_of_mul _ _ _ (by
  show quat 0 0 1 0 * quat 0 0 1 0 = quat 0 0 1 0 * quat 0 0 1 0
  rfl)
private theorem adjoint_unitJ_two : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitJ (lieBasis 2) = -lieBasis 2 := adjointAction_of_mul _ _ _ (by
  show quat 0 0 1 0 * quat 0 0 0 1 = -(quat 0 0 0 1) * quat 0 0 1 0
  ext <;> simp)
private theorem adjoint_unitCubeRoot_zero : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitCubeRoot (lieBasis 0) = lieBasis 1 :=
  adjointAction_of_mul _ _ _ (by
  show quat (1 / 2) (1 / 2) (1 / 2) (1 / 2) * quat 0 1 0 0 = quat 0 0 1 0 * quat (1 / 2) (1 / 2) (1 / 2) (1 / 2)
  ext <;> simp)
private theorem adjoint_unitCubeRoot_one : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitCubeRoot (lieBasis 1) = lieBasis 2 :=
  adjointAction_of_mul _ _ _ (by
  show quat (1 / 2) (1 / 2) (1 / 2) (1 / 2) * quat 0 0 1 0 = quat 0 0 0 1 * quat (1 / 2) (1 / 2) (1 / 2) (1 / 2)
  ext <;> simp)
private theorem schur_invariant (B : imaginaryQuaternions → imaginaryQuaternions → ℝ)
    (hl : ∀ X Y, B X Y = ∑ e, ∑ e', coordCLM e X * coordCLM e' Y * B (lieBasis e) (lieBasis e'))
    (hr : ∀ X Y, B X (-Y) = -B X Y) (hf : ∀ X Y, B (-X) Y = -B X Y)
    (hinv : ∀ g X Y, B (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X) (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g Y) = B X Y) (X Y : imaginaryQuaternions) :
    B X Y = B (lieBasis 0) (lieBasis 0) * ∑ e, coordCLM e X * coordCLM e Y := by
  have z01 : B (lieBasis 0) (lieBasis 1) = 0 := by
    have := hinv unitI (lieBasis 0) (lieBasis 1)
    rw [adjoint_unitI_zero, adjoint_unitI_one, hr] at this
    linarith
  have z02 : B (lieBasis 0) (lieBasis 2) = 0 := by
    have := hinv unitI (lieBasis 0) (lieBasis 2)
    rw [adjoint_unitI_zero, adjoint_unitI_two, hr] at this
    linarith
  have z10 : B (lieBasis 1) (lieBasis 0) = 0 := by
    have := hinv unitI (lieBasis 1) (lieBasis 0)
    rw [adjoint_unitI_zero, adjoint_unitI_one, hf] at this
    linarith
  have z20 : B (lieBasis 2) (lieBasis 0) = 0 := by
    have := hinv unitI (lieBasis 2) (lieBasis 0)
    rw [adjoint_unitI_zero, adjoint_unitI_two, hf] at this
    linarith
  have z12 : B (lieBasis 1) (lieBasis 2) = 0 := by
    have := hinv unitJ (lieBasis 1) (lieBasis 2)
    rw [adjoint_unitJ_one, adjoint_unitJ_two, hr] at this
    linarith
  have z21 : B (lieBasis 2) (lieBasis 1) = 0 := by
    have := hinv unitJ (lieBasis 2) (lieBasis 1)
    rw [adjoint_unitJ_one, adjoint_unitJ_two, hf] at this
    linarith
  have d1 : B (lieBasis 1) (lieBasis 1) = B (lieBasis 0) (lieBasis 0) := by
    have := hinv unitCubeRoot (lieBasis 0) (lieBasis 0)
    rwa [adjoint_unitCubeRoot_zero] at this
  have d2 : B (lieBasis 2) (lieBasis 2) = B (lieBasis 0) (lieBasis 0) := by
    have := hinv unitCubeRoot (lieBasis 1) (lieBasis 1)
    rw [adjoint_unitCubeRoot_one] at this
    rw [this, d1]
  rw [hl X Y]
  simp only [Fin.sum_univ_three, z01, z02, z10, z20, z12, z21, d1, d2]
  ring
private def bondKernel (G : TorusField n → ℝ) (b b' : TorusBond n) : ℝ :=
  hessian G (Pi.single b (lieBasis 0)) (Pi.single b' (lieBasis 0))
private def lieInner (X Y : imaginaryQuaternions) : ℝ :=
  ∑ e : Fin 3, imaginaryComponent e X * imaginaryComponent e Y
private theorem single_eq_sum (b : TorusBond n) (X : imaginaryQuaternions) :
    (Pi.single b X : LieForm n) = ∑ e, coordCLM e X • (Pi.single b (lieBasis e) : LieForm n) := by
  conv_lhs => rw [← sum_coord_smul_basis X]
  have h := map_sum (LinearMap.single ℝ (fun _ : TorusBond n => imaginaryQuaternions) b)
    (fun e => coordCLM e X • lieBasis e) Finset.univ
  simp only [LinearMap.coe_single] at h
  rw [h]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Pi.single_smul]
private theorem hessian_single (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    (hσ : 0 < σ) (b b' : TorusBond n) (X Y : imaginaryQuaternions) :
    hessian G (Pi.single b X) (Pi.single b' Y) = bondKernel G b b' * lieInner X Y := by
  refine schur_invariant (fun X Y => hessian G (Pi.single b X) (Pi.single b' Y)) ?_ ?_ ?_ ?_ X Y
  · intro X Y
    conv_lhs => rw [single_eq_sum b X, single_eq_sum b' Y]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
    ring
  · intro X Y
    simp only [Pi.single_neg, map_neg]
  · intro X Y
    simp only [Pi.single_neg, map_neg, ContinuousLinearMap.neg_apply]
  · intro g X Y
    have e : ∀ (b : TorusBond n) (X : imaginaryQuaternions),
        (Pi.single b (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X) : LieForm n) = adjointForm g (Pi.single b X) := by
      intro b X
      funext b'
      by_cases h : b' = b
      · subst h; simp [adjointForm]
      · simp [adjointForm, h, ColdStepAtMirrorFrames.Adjoint.adjointAction_zero]
    rw [e, e]
    exact hessian_adjoint hG hK hd hσ g _ _
private theorem hessian_eq_kernel (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    (hσ : 0 < σ) (A A' : LieForm n) : hessian G A A' = ∑ b, ∑ b', bondKernel G b b' * lieInner (A b) (A' b') := by
  rw [hessian_expand]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => hessian_single hG hK hd hσ b b' _ _
private theorem bondKernel_symm (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hσ : 0 < σ) (b b' : TorusBond n) :
    bondKernel G b b' = bondKernel G b' b :=
  hessian_symm (chartFn_contDiffAt (hG.smooth _ (isCold_trivialField hσ))) _ _
private theorem max_le_supportDiam (y : TorusSite n) (b b' : TorusBond n) :
    max (_root_.YangMills.Construction.TorusFields.supDist y b.1 : ℝ) (_root_.YangMills.Construction.TorusFields.supDist y b'.1 : ℝ) ≤ (supportDiam y ![b, b'] : ℝ) := by
  have h1 := supDist_le_supportDiam y ![b, b'] 0
  have h2 := supDist_le_supportDiam y ![b, b'] 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  exact max_le (by exact_mod_cast h1) (by exact_mod_cast h2)
private theorem hessian_single_le (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    (hσ : 0 < σ) (b b' : TorusBond n) (X Y : imaginaryQuaternions) :
    |hessian G (Pi.single b X) (Pi.single b' Y)| ≤
      ‖X‖ * ‖Y‖ * (K * Real.exp (-(del * max (_root_.YangMills.Construction.TorusFields.supDist y b.1 : ℝ) (_root_.YangMills.Construction.TorusFields.supDist y b'.1 : ℝ)))) := by
  refine (hessian_single_le_span hG hK hσ b b' X Y).trans ?_
  have := max_le_supportDiam y b b'
  gcongr
private theorem abs_bondKernel_le (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    (hσ : 0 < σ) (b b' : TorusBond n) :
    |bondKernel G b b'| ≤ K * Real.exp (-(del * max (_root_.YangMills.Construction.TorusFields.supDist y b.1 : ℝ) (_root_.YangMills.Construction.TorusFields.supDist y b'.1 : ℝ))) := by
  have := hessian_single_le hG hK hd hσ b b' (lieBasis 0) (lieBasis 0)
  rw [norm_lieBasis] at this
  simpa [bondKernel] using this
end
section
variable {n : ℕ} [NeZero n]
variable {σ K del c ρ₀ : ℝ} {G : TorusField n → ℝ} {y : TorusSite n}
private def plaquetteKernel (G : TorusField n → ℝ) (y : TorusSite n) (ρ₀ : ℝ) (p p' : TorusPlaquette n) : ℝ :=
  ∑ b, ∑ b', combCoeff y ρ₀ b p * combCoeff y ρ₀ b' p' * bondKernel G b b'
private theorem plaquetteKernel_symm (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hσ : 0 < σ) (r₀ : ℝ)
    (p p' : TorusPlaquette n) : plaquetteKernel G y r₀ p p' = plaquetteKernel G y r₀ p' p := by
  unfold plaquetteKernel
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [bondKernel_symm hG hσ]
  ring
private theorem combCoeff_eq_zero_of_far {r₀ : ℝ} {p : TorusPlaquette n} (h : r₀ < (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ))
    (b : TorusBond n) : combCoeff y r₀ b p = 0 := by
  by_contra hc
  have hb : IsInnerBond y r₀ b := by
    by_contra hb
    exact hc (combCoeff_outer hb p)
  have h1 := combCoeff_support hc
  have h2 : (_root_.YangMills.Construction.TorusFields.supDist b.1 y : ℝ) ≤ r₀ := by
    have := hb.1
    unfold supBall at this
    simpa using this
  have h3 : (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist b.1 y : ℝ) := by exact_mod_cast h1
  linarith
private theorem plaquetteKernel_far {r₀ : ℝ} {p p' : TorusPlaquette n}
    (h : r₀ < (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) ∨ r₀ < (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ)) :
    plaquetteKernel G y r₀ p p' = 0 := by
  unfold plaquetteKernel
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  rcases h with h | h
  · rw [combCoeff_eq_zero_of_far h b]; ring
  · rw [combCoeff_eq_zero_of_far h b']; ring
private theorem le_inv_mul_exp {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) : x ≤ (1 / a) * Real.exp (a * x) := by
  have h := Real.add_one_le_exp (a * x)
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ ha]
  nlinarith
private theorem abs_plaquetteKernel_le (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    (hσ : 0 < σ) (r₀ : ℝ) (p p' : TorusPlaquette n) : |plaquetteKernel G y r₀ p p'| ≤
      ((32 / del) ^ 2 * bondConst (del / 8) ^ 2) * K *
        Real.exp (-(del / 2 * max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ))) := by
  set D := max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ) with hD
  set w : TorusBond n → ℝ := fun b => Real.exp (-(del / 8 * (_root_.YangMills.Construction.TorusFields.supDist y b.1 : ℝ))) with hw
  have hw0 : ∀ b, 0 ≤ w b := fun b => (Real.exp_pos _).le
  have term : ∀ b b', |combCoeff y r₀ b p * combCoeff y r₀ b' p' * bondKernel G b b'| ≤
      ((32 / del) ^ 2 * K * Real.exp (-(del / 2 * D))) * (w b * w b') := by
    intro b b'
    by_cases h1 : combCoeff y r₀ b p = 0
    · rw [h1]; simp only [zero_mul, abs_zero]
      have := hw0 b; have := hw0 b'
      positivity
    by_cases h2 : combCoeff y r₀ b' p' = 0
    · rw [h2]; simp only [mul_zero, zero_mul, abs_zero]
      have := hw0 b; have := hw0 b'
      positivity
    have s1 : (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist y b.1 : ℝ) := by
      rw [supDist_symm y b.1]; exact_mod_cast combCoeff_support h1
    have s2 : (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist y b'.1 : ℝ) := by
      rw [supDist_symm y b'.1]; exact_mod_cast combCoeff_support h2
    set x : ℝ := (supDist y b.1 : ℝ) with hx
    set x' : ℝ := (supDist y b'.1 : ℝ) with hx'
    have hx0 : 0 ≤ x := Nat.cast_nonneg _
    have hx'0 : 0 ≤ x' := Nat.cast_nonneg _
    have c1 : |combCoeff y r₀ b p| ≤ 4 * x := by
      rw [hx, supDist_symm y b.1]; exact abs_combCoeff_le _ _ _ _
    have c2 : |combCoeff y r₀ b' p'| ≤ 4 * x' := by
      rw [hx', supDist_symm y b'.1]; exact abs_combCoeff_le _ _ _ _
    have c3 := abs_bondKernel_le hG hK hd hσ b b'
    have hDm : D ≤ max x x' := max_le_max s1 s2
    have e1 : x ≤ (8 / del) * Real.exp (del / 8 * x) := by
      have := le_inv_mul_exp (a := del / 8) (by positivity) hx0
      calc x ≤ _ := this
        _ = _ := by field_simp
    have e2 : x' ≤ (8 / del) * Real.exp (del / 8 * x') := by
      have := le_inv_mul_exp (a := del / 8) (by positivity) hx'0
      calc x' ≤ _ := this
        _ = _ := by field_simp
    have hmx : x ≤ max x x' := le_max_left _ _
    have hmx' : x' ≤ max x x' := le_max_right _ _
    have e3 : Real.exp (-(del * max x x')) ≤
        Real.exp (-(del / 2 * D)) * Real.exp (-(del / 4 * x)) * Real.exp (-(del / 4 * x')) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [mul_le_mul_of_nonneg_left hDm hd.le, mul_le_mul_of_nonneg_left hmx hd.le,
        mul_le_mul_of_nonneg_left hmx' hd.le]
    rw [abs_mul, abs_mul]
    have f1 : 4 * x * Real.exp (-(del / 4 * x)) ≤ (32 / del) * w b := by
      have k : Real.exp (del / 8 * x) * Real.exp (-(del / 4 * x)) = w b := by
        rw [← Real.exp_add, hw]
        simp only
        congr 1
        ring
      calc 4 * x * Real.exp (-(del / 4 * x)) ≤
            4 * ((8 / del) * Real.exp (del / 8 * x)) * Real.exp (-(del / 4 * x)) := by
            gcongr
        _ = (32 / del) * (Real.exp (del / 8 * x) * Real.exp (-(del / 4 * x))) := by ring
        _ = _ := by rw [k]
    have f2 : 4 * x' * Real.exp (-(del / 4 * x')) ≤ (32 / del) * w b' := by
      have k : Real.exp (del / 8 * x') * Real.exp (-(del / 4 * x')) = w b' := by
        rw [← Real.exp_add, hw]
        simp only
        congr 1
        ring
      calc 4 * x' * Real.exp (-(del / 4 * x')) ≤
            4 * ((8 / del) * Real.exp (del / 8 * x')) * Real.exp (-(del / 4 * x')) := by
            gcongr
        _ = (32 / del) * (Real.exp (del / 8 * x') * Real.exp (-(del / 4 * x'))) := by ring
        _ = _ := by rw [k]
    calc |combCoeff y r₀ b p| * |combCoeff y r₀ b' p'| * |bondKernel G b b'|
        ≤ (4 * x) * (4 * x') *
            (K * (Real.exp (-(del / 2 * D)) * Real.exp (-(del / 4 * x)) * Real.exp (-(del / 4 * x')))) := by
          refine mul_le_mul (mul_le_mul c1 c2 (abs_nonneg _) (by positivity)) (c3.trans ?_) (abs_nonneg _)
            (by positivity)
          exact mul_le_mul_of_nonneg_left e3 hK
      _ = K * Real.exp (-(del / 2 * D)) *
            ((4 * x * Real.exp (-(del / 4 * x))) * (4 * x' * Real.exp (-(del / 4 * x')))) := by ring
      _ ≤ K * Real.exp (-(del / 2 * D)) * (((32 / del) * w b) * ((32 / del) * w b')) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul f1 f2 (by positivity) ?_) (by positivity)
          have := hw0 b
          positivity
      _ = _ := by ring
  unfold plaquetteKernel
  have hsum : ∑ b, w b ≤ bondConst (del / 8) := bond_expSum_le (by positivity) y
  have hs0 : 0 ≤ ∑ b, w b := Finset.sum_nonneg fun b _ => hw0 b
  calc _ ≤ ∑ b : TorusBond n, ∑ b' : TorusBond n, ((32 / del) ^ 2 * K * Real.exp (-(del / 2 * D))) * (w b * w b') :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b' _ => term b b'))
    _ = ((32 / del) ^ 2 * K * Real.exp (-(del / 2 * D))) * ((∑ b, w b) * ∑ b, w b) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ((32 / del) ^ 2 * K * Real.exp (-(del / 2 * D))) * (bondConst (del / 8) * bondConst (del / 8)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hsum hsum hs0 bondConst_nonneg) (by positivity)
    _ = _ := by ring
end
section
variable {n : ℕ} [NeZero n]
variable {σ K del c ρ₀ : ℝ} {G : TorusField n → ℝ} {y : TorusSite n}
private theorem hessian_far_le (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    (hσ : 0 < σ) {P P' : LieForm n} {R : ℕ} {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hP : ∀ b, ‖P b‖ ≤ a)
    (hP' : ∀ b, ‖P' b‖ ≤ a') (hfar : ∀ b, P b ≠ 0 → R ≤ _root_.YangMills.Construction.TorusFields.supDist y b.1) :
    |hessian G P P'| ≤ a * a' * K * bondConst (del / 4) ^ 2 * Real.exp (-(del / 2 * (R : ℝ))) := by
  set w : TorusBond n → ℝ := fun b => Real.exp (-(del / 4 * (_root_.YangMills.Construction.TorusFields.supDist y b.1 : ℝ))) with hw
  have hw0 : ∀ b, 0 ≤ w b := fun b => (Real.exp_pos _).le
  set E := Real.exp (-(del / 2 * (R : ℝ))) with hE
  have term : ∀ b b', |hessian G (Pi.single b (P b)) (Pi.single b' (P' b'))| ≤ (a * a' * K * E) * (w b * w b') := by
    intro b b'
    by_cases h0 : P b = 0
    · rw [h0, Pi.single_zero, map_zero]
      simp only [ContinuousLinearMap.zero_apply, abs_zero]
      have := hw0 b; have := hw0 b'
      positivity
    have hR : (R : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist y b.1 : ℝ) := by exact_mod_cast hfar b h0
    refine (hessian_single_le hG hK hd hσ b b' _ _).trans ?_
    set x : ℝ := (supDist y b.1 : ℝ) with hx
    set x' : ℝ := (supDist y b'.1 : ℝ) with hx'
    have hmx : x ≤ max x x' := le_max_left _ _
    have hmx' : x' ≤ max x x' := le_max_right _ _
    have e3 : Real.exp (-(del * max x x')) ≤ E * (w b * w b') := by
      rw [hw, hE]
      simp only
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [mul_le_mul_of_nonneg_left hR hd.le, mul_le_mul_of_nonneg_left hmx hd.le,
        mul_le_mul_of_nonneg_left hmx' hd.le]
    calc ‖P b‖ * ‖P' b'‖ * (K * Real.exp (-(del * max x x'))) ≤ a * a' * (K * (E * (w b * w b'))) := by
          refine mul_le_mul (mul_le_mul (hP b) (hP' b') (norm_nonneg _) ha) ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left e3 hK
      _ = _ := by ring
  rw [hessian_expand]
  have hsum : ∑ b, w b ≤ bondConst (del / 4) := bond_expSum_le (by positivity) y
  have hs0 : 0 ≤ ∑ b, w b := Finset.sum_nonneg fun b _ => hw0 b
  calc _ ≤ ∑ b : TorusBond n, ∑ b' : TorusBond n, (a * a' * K * E) * (w b * w b') :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b' _ => term b b'))
    _ = (a * a' * K * E) * ((∑ b, w b) * ∑ b, w b) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
    _ ≤ (a * a' * K * E) * (bondConst (del / 4) * bondConst (del / 4)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hsum hsum hs0 bondConst_nonneg) (by positivity)
    _ = _ := by ring
private theorem lieInner_sum {ι ι' : Type} (s : Finset ι) (s' : Finset ι') (a : ι → ℝ) (a' : ι' → ℝ)
    (f : ι → imaginaryQuaternions) (f' : ι' → imaginaryQuaternions) :
    lieInner (∑ p ∈ s, a p • f p) (∑ p' ∈ s', a' p' • f' p') =
      ∑ p ∈ s, ∑ p' ∈ s', a p * a' p' * lieInner (f p) (f' p') := by
  have h : ∀ (e : Fin 3) {κ : Type} (t : Finset κ) (u : κ → ℝ) (v : κ → imaginaryQuaternions),
      imaginaryComponent e (∑ p ∈ t, u p • v p) = ∑ p ∈ t, u p * imaginaryComponent e (v p) := by
    intro e κ t u v
    simp only [← coordCLM_apply, map_sum, map_smul, smul_eq_mul]
  unfold lieInner
  simp only [h]
  have e1 : ∀ e : Fin 3, (∑ p ∈ s, a p * imaginaryComponent e (f p)) *
      (∑ p' ∈ s', a' p' * imaginaryComponent e (f' p')) =
      ∑ p ∈ s, ∑ p' ∈ s', a p * a' p' * (imaginaryComponent e (f p) * imaginaryComponent e (f' p')) := by
    intro e
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
    ring
  simp only [e1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p' _
  rw [Finset.mul_sum]
private theorem hessian_inner (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    (hσ : 0 < σ) {r₀ : ℝ} (A Bf : LieForm n)
    (hB : ∀ b, Bf b = ∑ p ∈ plaquettesIn (supBall y r₀), combCoeff y r₀ b p • lieFormCurl A p) :
    hessian G Bf Bf = 2 * kernelQuadraticForm (plaquetteKernel G y r₀) y r₀ (lieFormCurl A) := by
  have key : hessian G Bf Bf = ∑ p ∈ plaquettesIn (supBall y r₀), ∑ p' ∈ plaquettesIn (supBall y r₀),
      plaquetteKernel G y r₀ p p' * lieInner (lieFormCurl A p) (lieFormCurl A p') := by
    rw [hessian_eq_kernel hG hK hd hσ]
    simp only [hB, lieInner_sum]
    unfold plaquetteKernel
    simp only [Finset.mul_sum, Finset.sum_mul]
    calc _ = ∑ b : TorusBond n, ∑ p ∈ plaquettesIn (supBall y r₀), ∑ b' : TorusBond n,
          ∑ p' ∈ plaquettesIn (supBall y r₀),
          bondKernel G b b' * (combCoeff y r₀ b p * combCoeff y r₀ b' p' *
            lieInner (lieFormCurl A p) (lieFormCurl A p')) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ p ∈ plaquettesIn (supBall y r₀), ∑ b : TorusBond n, ∑ b' : TorusBond n,
          ∑ p' ∈ plaquettesIn (supBall y r₀),
          bondKernel G b b' * (combCoeff y r₀ b p * combCoeff y r₀ b' p' *
            lieInner (lieFormCurl A p) (lieFormCurl A p')) :=
          Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        calc _ = ∑ b : TorusBond n, ∑ p' ∈ plaquettesIn (supBall y r₀), ∑ b' : TorusBond n,
              bondKernel G b b' * (combCoeff y r₀ b p * combCoeff y r₀ b' p' *
                lieInner (lieFormCurl A p) (lieFormCurl A p')) :=
              Finset.sum_congr rfl fun b _ => Finset.sum_comm
          _ = ∑ p' ∈ plaquettesIn (supBall y r₀), ∑ b : TorusBond n, ∑ b' : TorusBond n,
              bondKernel G b b' * (combCoeff y r₀ b p * combCoeff y r₀ b' p' *
                lieInner (lieFormCurl A p) (lieFormCurl A p')) :=
              Finset.sum_comm
          _ = _ := by
            refine Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun b _ =>
              Finset.sum_congr rfl fun b' _ => ?_
            ring
  rw [key]
  unfold kernelQuadraticForm lieInner
  ring
end
section
variable {n : ℕ} [NeZero n]
variable {σ K del c ρ₀ : ℝ} {G : TorusField n → ℝ} {y : TorusSite n}
private theorem sq_le_exp {R : ℝ} (hd : 0 < del) (hR : 0 ≤ R) :
    (8 * R + 1) ^ 2 ≤ (64 / del + 1) ^ 2 * Real.exp (del / 4 * R) := by
  have h1 := Real.add_one_le_exp (del / 8 * R)
  have hD : 0 < 64 / del := by positivity
  have h2 : 8 * R + 1 ≤ (64 / del + 1) * Real.exp (del / 8 * R) := by
    have e : (64 / del) * (del / 8 * R) = 8 * R := by field_simp; ring
    have h3 : 0 ≤ del / 8 * R := by positivity
    calc 8 * R + 1 ≤ (64 / del + 1) * (del / 8 * R + 1) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 := pow_le_pow_left₀ (by positivity : 0 ≤ 8 * R + 1) h2 2
  refine h4.trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring
private theorem gauge_agrees_expForm {g : TorusSite n → UnitQuaternion} {W : TorusField n} (h0 : 0 ≤ ρ₀) :
    FieldsAgreeNear (TorusFields.gaugeTransform g W) (expForm (ballLog g W y ρ₀) (trivialField n)) y y ⌊ρ₀⌋₊ := by
  intro b hb
  have hin : (bondFrom y b).1 ∈ supBall y ρ₀ := by
    rw [mem_supBall_iff h0]
    refine supDist_add_siteOfInt_le _ _ _ fun l => ?_
    have := hb.1 l
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  simp only [expForm, trivialField, mul_one, ballLog]
  rw [if_pos hin, GaugeFixing.expUnit_minimalLog]
  rfl
private theorem isQuadraticInCurvature (hG : IsLocalGaugeFunctional σ K del c ρ₀ G y) (hK : 0 ≤ K) (hd : 0 < del)
    (hσ : 0 < σ) (hc : 0 < c) (h0 : 0 ≤ ρ₀) (hn : 2 * ρ₀ + 2 < n) :
    IsQuadraticInCurvature σ (1 + bondConst (del / 3) ^ 3 +
        bondConst (del / 4) ^ 2 * (σ / 5) ^ 2 * (64 / del + 1) ^ 2 * Real.exp (del / 4) +
        (32 / del) ^ 2 * bondConst (del / 8) ^ 2) (min c (del / 4)) K ρ₀ G y (plaquetteKernel G y ρ₀) := by
  classical
  intro g W s hs h5 hW hN
  set R := ⌊ρ₀⌋₊ with hRd
  have hnN : 2 * R + 2 < n := by
    have h1 : (R : ℝ) ≤ ρ₀ := Nat.floor_le h0
    have : ((2 * R + 2 : ℕ) : ℝ) < n := by
      push_cast
      linarith
    exact_mod_cast this
  set A := ballLog g W y ρ₀ with hAd
  have hA : ∀ b, ‖A b‖ ≤ s := by
    intro b
    rw [hAd]
    unfold ballLog
    split_ifs with hb
    · exact hN.log_le b hb
    · simpa using hs
  have hA0 : ∀ b : TorusBond n, b.1 ∉ supBall y ρ₀ → A b = 0 := by
    intro b hb
    rw [hAd]
    unfold ballLog
    rw [if_neg hb]
  have h4s : 4 * s < σ := by linarith
  have hcoldg : IsCold σ (TorusFields.gaugeTransform g W) := fun x μ ν h => by
    rw [_root_.YangMills.Construction.TorusFields.curvature_gaugeTransform]
    exact hW x μ ν h
  have h1 : |G W - G (expForm A (trivialField n))| ≤ K * Real.exp (-(c * ρ₀)) := by
    rw [← hG.gauge_invariant g W hW]
    exact hG.agreement _ _ hcoldg (isCold_expForm hA h4s) (gauge_agrees_expForm h0)
  have h2 := quadratic_approx hG hK hd hσ hs hA h4s
  set U := gradientFree y ρ₀ A with hU
  set lam := boxPotential y ρ₀ A with hlam
  have hAU : A = U + gradient lam := by
    funext b
    simp [hU, gradientFree, hlam]
  have h3 : hessian G A A = hessian G U U := by
    rw [hAU]
    exact hessian_add_gradient hG hK hd hσ lam U
  set Bf : LieForm n := fun b => if IsInnerBond y ρ₀ b then U b else 0 with hBf
  set Rf : LieForm n := fun b => if IsInnerBond y ρ₀ b then 0 else U b with hRf
  have hUB : U = Bf + Rf := by
    funext b
    simp only [hBf, hRf, Pi.add_apply]
    split_ifs <;> simp
  have hsym := hessian_symm (G := G) (chartFn_contDiffAt (hG.smooth _ (isCold_trivialField hσ)))
  have h4 : hessian G U U = hessian G Bf Bf + hessian G Rf (U + Bf) := by
    have e : U + Bf = Bf + Rf + Bf := by rw [← hUB]
    rw [e]
    conv_lhs => rw [hUB]
    simp only [map_add, ContinuousLinearMap.add_apply]
    have := hsym Bf Rf
    linarith
  set m := (8 * (R : ℝ) + 1) * s with hm
  have hm0 : 0 ≤ m := by positivity
  have hUn : ∀ b, ‖U b‖ ≤ m := fun b => norm_gradientFree_le h0 A hs hA b
  have hBn : ∀ b, ‖Bf b‖ ≤ m := fun b => by
    simp only [hBf]
    split_ifs
    · exact hUn b
    · simpa using hm0
  have hRn : ∀ b, ‖Rf b‖ ≤ m := fun b => by
    simp only [hRf]
    split_ifs
    · simpa using hm0
    · exact hUn b
  have hUBn : ∀ b, ‖(U + Bf) b‖ ≤ 2 * m := fun b => by
    have := norm_add_le (U b) (Bf b)
    have := hUn b
    have := hBn b
    simp only [Pi.add_apply]
    linarith
  have hfar : ∀ b, Rf b ≠ 0 → R ≤ _root_.YangMills.Construction.TorusFields.supDist y b.1 := by
    intro b hb
    simp only [hRf] at hb
    split_ifs at hb with hi
    · exact absurd rfl hb
    · rw [supDist_symm]
      exact far_of_outer h0 hA0 hi hb
  have h6 := hessian_far_le hG hK hd hσ hm0 (by positivity : 0 ≤ 2 * m) hRn hUBn hfar
  have h7 : hessian G Bf Bf = 2 * kernelQuadraticForm (plaquetteKernel G y ρ₀) y ρ₀ (lieFormCurl A) := by
    refine hessian_inner hG hK hd hσ A Bf fun b => ?_
    by_cases hi : IsInnerBond y ρ₀ b
    · simp only [hBf, if_pos hi]
      exact gradientFree_inner h0 hnN A hi
    · simp only [hBf, if_neg hi, combCoeff_outer hi, zero_smul, Finset.sum_const_zero]
  set E := Real.exp (-(min c (del / 4) * ρ₀)) with hE
  have hEc : Real.exp (-(c * ρ₀)) ≤ E :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left c (del / 4)])
  have hR1 : ρ₀ - 1 ≤ (R : ℝ) := by
    have := Nat.lt_floor_add_one ρ₀
    linarith
  have hss : s ^ 2 ≤ (σ / 5) ^ 2 := pow_le_pow_left₀ hs (by linarith) 2
  have hcut := sq_le_exp (R := (R : ℝ)) hd (Nat.cast_nonneg _)
  have hexp : Real.exp (del / 4 * (R : ℝ)) * Real.exp (-(del / 2 * (R : ℝ))) ≤ Real.exp (del / 4) * E := by
    rw [← Real.exp_add, hE, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_le_mul_of_nonneg_left hR1 (by positivity : 0 ≤ del / 4),
      mul_le_mul_of_nonneg_right (min_le_right c (del / 4)) h0]
  have hfarb : (1 / 2) * |hessian G Rf (U + Bf)| ≤
      K * (bondConst (del / 4) ^ 2 * (σ / 5) ^ 2 * (64 / del + 1) ^ 2 * Real.exp (del / 4)) * E := by
    calc (1 / 2) * |hessian G Rf (U + Bf)| ≤
          (1 / 2) * (m * (2 * m) * K * bondConst (del / 4) ^ 2 * Real.exp (-(del / 2 * (R : ℝ)))) := by
          linarith
      _ = K * bondConst (del / 4) ^ 2 * s ^ 2 * ((8 * (R : ℝ) + 1) ^ 2 * Real.exp (-(del / 2 * (R : ℝ)))) := by
          rw [hm]; ring
      _ ≤ K * bondConst (del / 4) ^ 2 * (σ / 5) ^ 2 *
            ((64 / del + 1) ^ 2 * Real.exp (del / 4 * (R : ℝ)) * Real.exp (-(del / 2 * (R : ℝ)))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hss (by positivity))
            (mul_le_mul_of_nonneg_right hcut (Real.exp_pos _).le) (by positivity) (by positivity)
      _ = K * bondConst (del / 4) ^ 2 * (σ / 5) ^ 2 * (64 / del + 1) ^ 2 *
            (Real.exp (del / 4 * (R : ℝ)) * Real.exp (-(del / 2 * (R : ℝ)))) := by ring
      _ ≤ K * bondConst (del / 4) ^ 2 * (σ / 5) ^ 2 * (64 / del + 1) ^ 2 * (Real.exp (del / 4) * E) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  have hsplit : G W - kernelQuadraticForm (plaquetteKernel G y ρ₀) y ρ₀ (lieFormCurl A) =
      (G W - G (expForm A (trivialField n))) + (G (expForm A (trivialField n)) - (1 / 2) * hessian G A A) +
        (1 / 2) * hessian G Rf (U + Bf) := by
    rw [h3, h4, h7]
    ring
  rw [hsplit]
  set cB := bondConst (del / 3) ^ 3 with hcB
  set cF := bondConst (del / 4) ^ 2 * (σ / 5) ^ 2 * (64 / del + 1) ^ 2 * Real.exp (del / 4) with hcF
  set cK := (32 / del) ^ 2 * bondConst (del / 8) ^ 2 with hcK
  have hcB0 : 0 ≤ cB := pow_nonneg bondConst_nonneg 3
  have habs : |(G W - G (expForm A (trivialField n))) +
      (G (expForm A (trivialField n)) - (1 / 2) * hessian G A A) +
      (1 / 2) * hessian G Rf (U + Bf)| ≤ K * E + s ^ 3 * (K * cB) + K * cF * E := by
    have b1 : |G W - G (expForm A (trivialField n))| ≤ K * E := h1.trans (mul_le_mul_of_nonneg_left hEc hK)
    have b3 : |(1 / 2) * hessian G Rf (U + Bf)| ≤ K * cF * E := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact hfarb
    exact (abs_add_three _ _ _).trans (by linarith)
  refine habs.trans ?_
  have hpos : 0 ≤ K * (s ^ 3 + E * cB + s ^ 3 * cF + cK * (s ^ 3 + E)) := by positivity
  calc K * E + s ^ 3 * (K * cB) + K * cF * E ≤
        K * E + s ^ 3 * (K * cB) + K * cF * E + K * (s ^ 3 + E * cB + s ^ 3 * cF + cK * (s ^ 3 + E)) := by linarith
    _ = (1 + cB + cF + cK) * K * (s ^ 3 + E) := by ring
end
end LocalQuadratic
theorem localFunctionalQuadratic : localFunctionalQuadraticStatement := by
  intro σ del c hσ hd hc
  refine ⟨1 + LocalQuadratic.bondConst (del / 3) ^ 3 +
      LocalQuadratic.bondConst (del / 4) ^ 2 * (σ / 5) ^ 2 * (64 / del + 1) ^ 2 * Real.exp (del / 4) +
      (32 / del) ^ 2 * LocalQuadratic.bondConst (del / 8) ^ 2, min c (del / 4), 0,
    lt_min hc (by positivity), ?_⟩
  intro n _ K ρ₀ G y hρ hn hK hG
  refine ⟨LocalQuadratic.plaquetteKernel G y ρ₀, LocalQuadratic.plaquetteKernel_symm hG hσ ρ₀,
    fun p p' h => LocalQuadratic.plaquetteKernel_far h,
    fun p p' => ?_, LocalQuadratic.isQuadraticInCurvature hG hK hd hσ hc hρ hn⟩
  refine (LocalQuadratic.abs_plaquetteKernel_le hG hK hd hσ ρ₀ p p').trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hK) (Real.exp_pos _).le
  have h1 : 0 ≤ LocalQuadratic.bondConst (del / 3) ^ 3 := pow_nonneg LocalQuadratic.bondConst_nonneg 3
  have h2 : 0 ≤ LocalQuadratic.bondConst (del / 4) ^ 2 * (σ / 5) ^ 2 * (64 / del + 1) ^ 2 * Real.exp (del / 4) := by
    positivity
  linarith
end YangMills.Construction.ResponseInTheExpansion
end
