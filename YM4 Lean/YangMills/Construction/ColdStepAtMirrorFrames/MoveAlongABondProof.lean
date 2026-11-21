import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponential
import YangMills.Construction.ColdStepAtMirrorFrames.MoveAlongABond
import YangMills.Construction.ColdStepAtMirrorFrames.ThreeDerivativesOfAVectorComposite
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace ExpProductLog
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
def firstSlot : imaginaryQuaternions →L[ℝ] imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions :=
  ContinuousLinearMap.inl ℝ imaginaryQuaternions (imaginaryQuaternions × imaginaryQuaternions)
def secondSlot (A : P →L[ℝ] imaginaryQuaternions) :
    P →L[ℝ] imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions :=
  (ContinuousLinearMap.inr ℝ imaginaryQuaternions (imaginaryQuaternions × imaginaryQuaternions)).comp
    ((ContinuousLinearMap.inl ℝ imaginaryQuaternions imaginaryQuaternions).comp A)
def affineTriple (A : P →L[ℝ] imaginaryQuaternions) (c : imaginaryQuaternions) :
    P → imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions :=
  fun x => secondSlot A x + ((0, 0, c) : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)
def triple (g : P → imaginaryQuaternions) (A : P →L[ℝ] imaginaryQuaternions) (c : imaginaryQuaternions) :
    P → imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions :=
  (firstSlot ∘ g) + affineTriple A c
theorem triple_apply (g : P → imaginaryQuaternions) (A : P →L[ℝ] imaginaryQuaternions)
    (c : imaginaryQuaternions) (x : P) :
    triple g A c x = (g x, A x, c) := by
  simp [triple, affineTriple, firstSlot, secondSlot]
theorem affineTriple_contDiff (A : P →L[ℝ] imaginaryQuaternions) (c : imaginaryQuaternions) :
    ContDiff ℝ 3 (affineTriple A c) :=
  (secondSlot A).contDiff.add contDiff_const
theorem fderiv_affineTriple (A : P →L[ℝ] imaginaryQuaternions) (c : imaginaryQuaternions) :
    fderiv ℝ (affineTriple A c) = fun _ => secondSlot A := by
  funext x
  exact (((secondSlot A).hasFDerivAt).add_const _).fderiv
theorem iteratedFDeriv_one_affineTriple (A : P →L[ℝ] imaginaryQuaternions) (c : imaginaryQuaternions) (u : P) :
    iteratedFDeriv ℝ 1 (affineTriple A c) 0 ![u] = secondSlot A u := by
  rw [iteratedFDeriv_one_apply, fderiv_affineTriple]
  simp
theorem iteratedFDeriv_two_affineTriple (A : P →L[ℝ] imaginaryQuaternions) (c : imaginaryQuaternions) :
    iteratedFDeriv ℝ 2 (affineTriple A c) 0 = 0 := by
  apply ContinuousMultilinearMap.ext
  intro m
  rw [iteratedFDeriv_two_apply, fderiv_affineTriple]
  simp
theorem iteratedFDeriv_three_affineTriple (A : P →L[ℝ] imaginaryQuaternions) (c : imaginaryQuaternions) :
    iteratedFDeriv ℝ 3 (affineTriple A c) 0 = 0 := by
  apply ContinuousMultilinearMap.ext
  intro m
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply, fderiv_affineTriple]
  simp
theorem iteratedFDeriv_one_triple (g : P → imaginaryQuaternions) (A : P →L[ℝ] imaginaryQuaternions)
    (c : imaginaryQuaternions) (hg : ContDiffAt ℝ 3 g 0) (u : P) :
    iteratedFDeriv ℝ 1 (triple g A c) 0 ![u] = (iteratedFDeriv ℝ 1 g 0 ![u], A u, 0) := by
  have h1 : ContDiffAt ℝ 1 (firstSlot ∘ g) 0 := (firstSlot.contDiff.contDiffAt.comp 0 hg).of_le (by norm_num)
  have h2 : ContDiffAt ℝ 1 (affineTriple A c) 0 := ((affineTriple_contDiff A c).contDiffAt).of_le (by norm_num)
  unfold triple
  rw [iteratedFDeriv_add_apply h1 h2, add_apply, iteratedFDeriv_one_affineTriple,
    firstSlot.iteratedFDeriv_comp_left (hg.of_le (by norm_num)) le_rfl]
  simp [firstSlot, secondSlot]
theorem iteratedFDeriv_two_triple (g : P → imaginaryQuaternions) (A : P →L[ℝ] imaginaryQuaternions)
    (c : imaginaryQuaternions) (hg : ContDiffAt ℝ 3 g 0) (u v : P) :
    iteratedFDeriv ℝ 2 (triple g A c) 0 ![u, v] = (iteratedFDeriv ℝ 2 g 0 ![u, v], 0, 0) := by
  have h1 : ContDiffAt ℝ 2 (firstSlot ∘ g) 0 := (firstSlot.contDiff.contDiffAt.comp 0 hg).of_le (by norm_num)
  have h2 : ContDiffAt ℝ 2 (affineTriple A c) 0 := ((affineTriple_contDiff A c).contDiffAt).of_le (by norm_num)
  unfold triple
  rw [iteratedFDeriv_add_apply h1 h2, add_apply, iteratedFDeriv_two_affineTriple,
    firstSlot.iteratedFDeriv_comp_left (hg.of_le (by norm_num)) le_rfl]
  simp [firstSlot]
  rfl
theorem iteratedFDeriv_three_triple (g : P → imaginaryQuaternions) (A : P →L[ℝ] imaginaryQuaternions)
    (c : imaginaryQuaternions) (hg : ContDiffAt ℝ 3 g 0) (u v w : P) :
    iteratedFDeriv ℝ 3 (triple g A c) 0 ![u, v, w] = (iteratedFDeriv ℝ 3 g 0 ![u, v, w], 0, 0) := by
  have h1 : ContDiffAt ℝ 3 (firstSlot ∘ g) 0 := (firstSlot.contDiff.contDiffAt.comp 0 hg)
  have h2 : ContDiffAt ℝ 3 (affineTriple A c) 0 := (affineTriple_contDiff A c).contDiffAt
  unfold triple
  rw [iteratedFDeriv_add_apply h1 h2, add_apply, iteratedFDeriv_three_affineTriple,
    firstSlot.iteratedFDeriv_comp_left hg le_rfl]
  simp [firstSlot]
  rfl
theorem norm_pair_zero_le (a b : imaginaryQuaternions) :
    ‖((a, b, 0) : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)‖ ≤ ‖a‖ + ‖b‖ := by
  simp only [Prod.norm_def, norm_zero]
  have := norm_nonneg a
  have := norm_nonneg b
  refine max_le (by linarith) (max_le (by linarith) (by linarith))
theorem norm_apply_one_le {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (T : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) G) (a : E) :
    ‖T ![a]‖ ≤ ‖T‖ * ‖a‖ := by
  simpa using T.le_opNorm ![a]
theorem norm_apply_two_le {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) G) (a b : E) :
    ‖T ![a, b]‖ ≤ ‖T‖ * (‖a‖ * ‖b‖) := by
  simpa [Fin.prod_univ_two] using T.le_opNorm ![a, b]
theorem norm_apply_three_le {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) G) (a b c : E) :
    ‖T ![a, b, c]‖ ≤ ‖T‖ * (‖a‖ * ‖b‖ * ‖c‖) := by
  simpa [Fin.prod_univ_three, mul_assoc] using T.le_opNorm ![a, b, c]
end ExpProductLog
open ExpProductLog
theorem expProductLogBounds_of (hΘ : ConjugatedExpLogSmooth)
    (hchain : ThirdOrderChainRuleNormedSpace) : ExpProductLogBounds := by
  obtain ⟨Θ, U, C, hU, hC, hdiag, hcd, hexp, hzero, hbd, hd0, hnear⟩ := hΘ
  refine ⟨1 + C, by positivity, ?_⟩
  intro P _ _ g A hg hc
  unfold IsExpProductLog
  set c := g 0 with hcdef
  set α := triple g A c with hαdef
  have hα0 : α 0 = diagonalTriple c := by
    rw [hαdef, triple_apply]
    simp [diagonalTriple, hcdef]
  have hαc : ContDiffAt ℝ 3 α 0 :=
    (firstSlot.contDiff.contDiffAt.comp 0 hg).add (affineTriple_contDiff A c).contDiffAt
  have hΘc : ContDiffAt ℝ 3 Θ (α 0) := by
    rw [hα0]
    exact hcd.contDiffAt (hU.mem_nhds (hdiag c))
  obtain ⟨hcomp, h1, h2, h3⟩ := hchain Θ α 0 hΘc hαc
  have hev : ∀ᶠ x in 𝓝 (0 : P), α x ∈ U :=
    hαc.continuousAt.eventually (by rw [hα0]; exact hU.mem_nhds (hdiag c))
  refine ⟨Θ ∘ α, hcomp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Θ (α 0) = 0
    rw [hα0, hzero]
  · refine hev.mono fun x hx => ?_
    have := hexp (α x) hx
    rw [hαdef, triple_apply] at this
    show expUnit (Θ (triple g A c x)) * expUnit c = expUnit (g x) * expUnit (A x)
    rw [triple_apply, this]
    simp
  all_goals
    have hx : α 0 = diagonalTriple c := hα0
    have b1 : ‖iteratedFDeriv ℝ 1 Θ (α 0)‖ ≤ C := by rw [hx]; exact hbd c 1 hc (by norm_num)
    have b2 : ‖iteratedFDeriv ℝ 2 Θ (α 0)‖ ≤ C := by rw [hx]; exact hbd c 2 hc (by norm_num)
    have b3 : ‖iteratedFDeriv ℝ 3 Θ (α 0)‖ ≤ C := by rw [hx]; exact hbd c 3 hc (by norm_num)
    have z1 : ∀ u, ‖iteratedFDeriv ℝ 1 α 0 ![u]‖ ≤ firstOrderSize g A u := fun u => by
      rw [hαdef, iteratedFDeriv_one_triple g A c hg]
      exact norm_pair_zero_le _ _
    have z2 : ∀ u v, ‖iteratedFDeriv ℝ 2 α 0 ![u, v]‖ ≤ ‖iteratedFDeriv ℝ 2 g 0 ![u, v]‖ := fun u v => by
      rw [hαdef, iteratedFDeriv_two_triple g A c hg]
      simpa using norm_pair_zero_le (iteratedFDeriv ℝ 2 g 0 ![u, v]) 0
    have z3 : ∀ u v w, ‖iteratedFDeriv ℝ 3 α 0 ![u, v, w]‖ ≤ ‖iteratedFDeriv ℝ 3 g 0 ![u, v, w]‖ :=
      fun u v w => by
      rw [hαdef, iteratedFDeriv_three_triple g A c hg]
      simpa using norm_pair_zero_le (iteratedFDeriv ℝ 3 g 0 ![u, v, w]) 0
    have sl : ∀ u, 0 ≤ firstOrderSize g A u := fun u => by unfold firstOrderSize; positivity
  · intro u
    rw [h1 u, iteratedFDeriv_one_apply, hx]
    have hn := hnear c (iteratedFDeriv ℝ 1 α 0 ![u]) hc
    rw [hd0] at hn
    have e : iteratedFDeriv ℝ 1 α 0 ![u] = (iteratedFDeriv ℝ 1 g 0 ![u], A u, 0) := by
      rw [hαdef, iteratedFDeriv_one_triple g A c hg]
    have hz := z1 u
    rw [e] at hn hz
    rw [e]
    have hn' : ‖fderiv ℝ Θ (diagonalTriple c) (iteratedFDeriv ℝ 1 g 0 ![u], A u, 0) -
        (iteratedFDeriv ℝ 1 g 0 ![u] + A u)‖ ≤
        C * ‖c‖ * ‖((iteratedFDeriv ℝ 1 g 0 ![u], A u, 0) :
          imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)‖ := by
      simpa using hn
    refine hn'.trans ?_
    have hs := sl u
    have hc0 := norm_nonneg c
    calc C * ‖c‖ * ‖((iteratedFDeriv ℝ 1 g 0 ![u], A u, 0) :
          imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)‖
        ≤ C * ‖c‖ * firstOrderSize g A u := mul_le_mul_of_nonneg_left hz (by positivity)
      _ ≤ (1 + C) * ‖c‖ * firstOrderSize g A u := by
        apply mul_le_mul_of_nonneg_right _ hs
        apply mul_le_mul_of_nonneg_right _ hc0
        linarith
  · intro u
    rw [h1 u]
    have hs := sl u
    calc _ ≤ ‖iteratedFDeriv ℝ 1 Θ (α 0)‖ * ‖iteratedFDeriv ℝ 1 α 0 ![u]‖ := norm_apply_one_le _ _
      _ ≤ C * firstOrderSize g A u := mul_le_mul b1 (z1 u) (norm_nonneg _) hC
      _ ≤ (1 + C) * firstOrderSize g A u := mul_le_mul_of_nonneg_right (by linarith) hs
  · intro u v
    rw [h2 u v]
    have hu := sl u
    have hv := sl v
    have t2 : ‖iteratedFDeriv ℝ 2 Θ (α 0) ![iteratedFDeriv ℝ 1 α 0 ![u], iteratedFDeriv ℝ 1 α 0 ![v]]‖ ≤
        C * (firstOrderSize g A u * firstOrderSize g A v) :=
      (norm_apply_two_le _ _ _).trans (mul_le_mul b2 (mul_le_mul (z1 u) (z1 v) (norm_nonneg _) hu)
        (by positivity) hC)
    have t1 : ‖iteratedFDeriv ℝ 1 Θ (α 0) ![iteratedFDeriv ℝ 2 α 0 ![u, v]]‖ ≤
        C * ‖iteratedFDeriv ℝ 2 g 0 ![u, v]‖ :=
      (norm_apply_one_le _ _).trans (mul_le_mul b1 (z2 u v) (norm_nonneg _) hC)
    have hn := norm_nonneg (iteratedFDeriv ℝ 2 g 0 ![u, v])
    have hm := mul_nonneg hu hv
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ C * (firstOrderSize g A u * firstOrderSize g A v) + C * ‖iteratedFDeriv ℝ 2 g 0 ![u, v]‖ :=
          add_le_add t2 t1
      _ ≤ (1 + C) * (firstOrderSize g A u * firstOrderSize g A v + ‖iteratedFDeriv ℝ 2 g 0 ![u, v]‖) := by
          nlinarith
  · intro u v w
    rw [h3 u v w]
    have hu := sl u
    have hv := sl v
    have hw := sl w
    have t3 : ‖iteratedFDeriv ℝ 3 Θ (α 0) ![iteratedFDeriv ℝ 1 α 0 ![u], iteratedFDeriv ℝ 1 α 0 ![v],
        iteratedFDeriv ℝ 1 α 0 ![w]]‖ ≤
        C * (firstOrderSize g A u * firstOrderSize g A v * firstOrderSize g A w) :=
      (norm_apply_three_le _ _ _ _).trans (mul_le_mul b3 (mul_le_mul (mul_le_mul (z1 u) (z1 v) (norm_nonneg _) hu)
        (z1 w) (norm_nonneg _) (by positivity)) (by positivity) hC)
    have t2 : ∀ a b d : P, ‖iteratedFDeriv ℝ 2 Θ (α 0) ![iteratedFDeriv ℝ 2 α 0 ![a, b],
        iteratedFDeriv ℝ 1 α 0 ![d]]‖ ≤ C * (‖iteratedFDeriv ℝ 2 g 0 ![a, b]‖ * firstOrderSize g A d) :=
      fun a b d => (norm_apply_two_le _ _ _).trans (mul_le_mul b2 (mul_le_mul (z2 a b) (z1 d) (norm_nonneg _)
        (norm_nonneg _)) (by positivity) hC)
    have t1 : ‖iteratedFDeriv ℝ 1 Θ (α 0) ![iteratedFDeriv ℝ 3 α 0 ![u, v, w]]‖ ≤
        C * ‖iteratedFDeriv ℝ 3 g 0 ![u, v, w]‖ :=
      (norm_apply_one_le _ _).trans (mul_le_mul b1 (z3 u v w) (norm_nonneg _) hC)
    have n1 : 0 ≤ firstOrderSize g A u * firstOrderSize g A v * firstOrderSize g A w := by positivity
    have n2 : 0 ≤ ‖iteratedFDeriv ℝ 2 g 0 ![u, v]‖ * firstOrderSize g A w := by positivity
    have n3 : 0 ≤ ‖iteratedFDeriv ℝ 2 g 0 ![u, w]‖ * firstOrderSize g A v := by positivity
    have n4 : 0 ≤ ‖iteratedFDeriv ℝ 2 g 0 ![v, w]‖ * firstOrderSize g A u := by positivity
    have n5 := norm_nonneg (iteratedFDeriv ℝ 3 g 0 ![u, v, w])
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add_left (norm_add_le _ _) _).trans ?_
    refine (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _).trans ?_
    refine (add_le_add_left (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _) _).trans ?_
    have := t2 u v w
    have := t2 u w v
    have := t2 v w u
    nlinarith
end ColdStepAtMirrorFrames
end YangMills.Construction
end
