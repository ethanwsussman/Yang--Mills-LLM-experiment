import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponsesProof
import YangMills.Construction.FormsOnATorus.AxialLadderOnACubeProof
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.ResponseInTheExpansion.ALocalFunctionIsQuadraticInTheCurvatureProof
import YangMills.Construction.RunningCouplingSlope.SecondMomentThroughABlockKernelProofForm
import YangMills.Construction.LawByMomentsOfTheFlow.FormsReadCurvature
import YangMills.Construction.LawByMomentsOfTheFlow.TheCutOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheScale
import YangMills.Construction.ResponseInTheExpansion.KernelsCarriedFromAMirror
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps ExponentialSums
section CurlCombinations
variable {n : ℕ} [NeZero n]
private abbrev orderedPlaquettes (n : ℕ) [NeZero n] : Finset (TorusPlaquette n) :=
  plaquettesIn (Finset.univ : Finset (TorusSite n))
private def CurlCombination (w : TorusSite n → ℝ) (f : (TorusBond n → ℝ) → ℝ) (S : ℝ) : Prop :=
  ∃ a : TorusPlaquette n → ℝ, (∀ X, f X = ∑ p ∈ orderedPlaquettes n, a p * WeightedResponses.curl X p) ∧
    ∑ p ∈ orderedPlaquettes n, |a p| * w p.1 ≤ S
private theorem CurlCombination.mono {w : TorusSite n → ℝ} {f : (TorusBond n → ℝ) → ℝ} {S T : ℝ}
    (h : CurlCombination w f S) (hST : S ≤ T) : CurlCombination w f T := by
  obtain ⟨a, h1, h2⟩ := h
  exact ⟨a, h1, h2.trans hST⟩
private theorem CurlCombination.congr {w : TorusSite n → ℝ} {f g : (TorusBond n → ℝ) → ℝ} {S : ℝ}
    (h : CurlCombination w f S) (hfg : ∀ X, g X = f X) : CurlCombination w g S := by
  obtain ⟨a, h1, h2⟩ := h
  exact ⟨a, fun X => (hfg X).trans (h1 X), h2⟩
private theorem curlCombination_zero (w : TorusSite n → ℝ) : CurlCombination w (fun _ => 0) 0 :=
  ⟨fun _ => 0, fun _ => by simp, by simp⟩
private theorem CurlCombination.add {w : TorusSite n → ℝ} (hw : ∀ x, 0 ≤ w x) {f g : (TorusBond n → ℝ) → ℝ}
    {S T : ℝ} (hf : CurlCombination w f S) (hg : CurlCombination w g T) :
    CurlCombination w (fun X => f X + g X) (S + T) := by
  obtain ⟨a, a1, a2⟩ := hf
  obtain ⟨b, b1, b2⟩ := hg
  refine ⟨fun p => a p + b p, fun X => ?_, ?_⟩
  · show f X + g X = _
    rw [a1, b1, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  · calc ∑ p ∈ orderedPlaquettes n, |a p + b p| * w p.1
          ≤ ∑ p ∈ orderedPlaquettes n, (|a p| * w p.1 + |b p| * w p.1) :=
          Finset.sum_le_sum fun p _ => by
            rw [← add_mul]
            exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (hw _)
      _ ≤ S + T := by
          rw [Finset.sum_add_distrib]
          exact add_le_add a2 b2
private theorem CurlCombination.neg {w : TorusSite n → ℝ} {f : (TorusBond n → ℝ) → ℝ} {S : ℝ}
    (hf : CurlCombination w f S) : CurlCombination w (fun X => -f X) S := by
  obtain ⟨a, a1, a2⟩ := hf
  refine ⟨fun p => -a p, fun X => ?_, by simpa using a2⟩
  show -f X = _
  rw [a1, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring
private theorem CurlCombination.sub {w : TorusSite n → ℝ} (hw : ∀ x, 0 ≤ w x) {f g : (TorusBond n → ℝ) → ℝ}
    {S T : ℝ} (hf : CurlCombination w f S) (hg : CurlCombination w g T) :
    CurlCombination w (fun X => f X - g X) (S + T) :=
  (hf.add hw hg.neg).congr fun _ => sub_eq_add_neg _ _
private theorem mem_orderedPlaquettes {x : TorusSite n} {μ ν : Fin 4} (h : μ < ν) :
    ((x, μ, ν) : TorusPlaquette n) ∈ orderedPlaquettes n := by
  simp [orderedPlaquettes, plaquettesIn, h]
private theorem curlCombination_curl_of_lt (w : TorusSite n → ℝ) {x : TorusSite n} {μ ν : Fin 4} (h : μ < ν) :
    CurlCombination w (fun X => WeightedResponses.curl X (x, μ, ν)) (w x) := by
  classical
  refine ⟨fun p => if p = (x, μ, ν) then 1 else 0, fun X => ?_, ?_⟩
  · simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' (orderedPlaquettes n) (x, μ, ν), if_pos (mem_orderedPlaquettes h)]
  · have : ∀ p : TorusPlaquette n,
        |(if p = (x, μ, ν) then (1 : ℝ) else 0)| * w p.1 = if p = (x, μ, ν) then w x else 0 := by
      intro p
      split_ifs with hp
      · simp [hp]
      · simp
    simp only [this]
    rw [Finset.sum_ite_eq' (orderedPlaquettes n) (x, μ, ν), if_pos (mem_orderedPlaquettes h)]
private theorem curlCombination_curl {w : TorusSite n → ℝ} (hw : ∀ x, 0 ≤ w x) (x : TorusSite n) (μ ν : Fin 4) :
    CurlCombination w (fun X => WeightedResponses.curl X (x, μ, ν)) (w x) := by
  rcases lt_trichotomy μ ν with h | h | h
  · exact curlCombination_curl_of_lt w h
  · subst h
    refine ((curlCombination_zero w).mono (hw x)).congr fun X => ?_
    simp only [WeightedResponses.curl]
    ring
  · refine (curlCombination_curl_of_lt w h (x := x)).neg.congr fun X => ?_
    simp only [WeightedResponses.curl]
    ring
private theorem curlCombination_telescope {w : TorusSite n → ℝ} (hw : ∀ x, 0 ≤ w x)
    (g : ℤ → (TorusBond n → ℝ) → ℝ) {S : ℝ} (h0 : ∀ X, g 0 X = 0) (K : ℤ)
    (step : ∀ k : ℤ, min 0 K ≤ k → k < max 0 K → CurlCombination w (fun X => g (k + 1) X - g k X) S) :
    CurlCombination w (g K) (|(K : ℝ)| * S) := by
  have up : ∀ N : ℕ, (N : ℤ) ≤ K → CurlCombination w (g N) ((N : ℝ) * S) := by
    intro N
    induction N with
    | zero =>
      intro _
      refine ((curlCombination_zero w).mono (by simp)).congr fun X => ?_
      simpa using h0 X
    | succ N ih =>
      intro hN
      have h1 := ih (by push_cast at hN; omega)
      have h2 := step N (by
        have : (0 : ℤ) ≤ N := by positivity
        exact (min_le_left _ _).trans this) (by
        refine lt_of_lt_of_le ?_ (le_max_right _ _)
        push_cast at hN
        omega)
      refine (h1.add hw h2).mono (by push_cast; linarith) |>.congr fun X => ?_
      push_cast
      ring
  have dn : ∀ N : ℕ, K ≤ -(N : ℤ) → CurlCombination w (g (-(N : ℤ))) ((N : ℝ) * S) := by
    intro N
    induction N with
    | zero =>
      intro _
      refine ((curlCombination_zero w).mono (by simp)).congr fun X => ?_
      simpa using h0 X
    | succ N ih =>
      intro hN
      have h1 := ih (by push_cast at hN; omega)
      have h2 := step (-((N + 1 : ℕ) : ℤ)) (by
        exact (min_le_right _ _).trans hN) (by
        refine lt_of_lt_of_le ?_ (le_max_left _ _)
        push_cast
        omega)
      refine (h1.add hw h2.neg).mono (by push_cast; linarith) |>.congr fun X => ?_
      have : -((N + 1 : ℕ) : ℤ) + 1 = -(N : ℤ) := by push_cast; ring
      rw [this]
      ring
  rcases le_total 0 K with hK | hK
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hK
    have := up N le_rfl
    simpa using this
  · obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hK)
    have hK' : K = -(N : ℤ) := by omega
    subst hK'
    have := dn N le_rfl
    simpa using this
end CurlCombinations
section LatticePaths
variable {n : ℕ} [NeZero n]
private abbrev basisVec (i : Fin 4) : Fin 4 → ℤ := Pi.single i 1
private def siteAt (y : TorusSite n) (ζ : Fin 4 → ℤ) : TorusSite n := y + siteOfInt ζ
private theorem siteAt_add_basisVec (y : TorusSite n) (ζ : Fin 4 → ℤ) (i : Fin 4) :
    siteAt y (ζ + basisVec i) = siteAt y ζ + unitStep n i := by apply _root_.YangMills.DeltaSharedProofs.p500616 <;> assumption
private theorem siteAt_sub_side (y : TorusSite n) (ζ : Fin 4 → ℤ) (i : Fin 4) :
    siteAt y (ζ - (n : ℤ) • basisVec i) = siteAt y ζ := by
  funext a
  simp only [siteAt, siteOfInt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, basisVec]
  split_ifs <;> simp
private def centredCoords (y z : TorusSite n) : Fin 4 → ℤ := fun a => (z a - y a).valMinAbs
private theorem siteAt_centredCoords (y z : TorusSite n) : siteAt y (centredCoords y z) = z := by apply _root_.YangMills.DeltaSharedProofs.p500399 <;> assumption
private def InCentredCube (n : ℕ) (ζ : Fin 4 → ℤ) : Prop := ∀ a, -(n : ℤ) < 2 * ζ a ∧ 2 * ζ a ≤ n
private theorem inCentredCube_centredCoords (y z : TorusSite n) : InCentredCube n (centredCoords y z) := by
  intro a
  have h := ZMod.valMinAbs_mem_Ioc (z a - y a)
  have h1 := h.1
  have h2 := h.2
  simp only [centredCoords]
  constructor <;> linarith
private theorem centredCoords_siteAt (y : TorusSite n) {ζ : Fin 4 → ℤ} (h : InCentredCube n ζ) :
    centredCoords y (siteAt y ζ) = ζ := by
  funext a
  have e : siteAt y ζ a - y a = ((ζ a : ℤ) : ZMod n) := by simp [siteAt, siteOfInt]
  simp only [centredCoords]
  rw [e]
  refine (ZMod.valMinAbs_spec _ _).2 ⟨rfl, ?_⟩
  have := h a
  constructor <;> linarith [this.1, this.2]
private theorem supDist_siteAt_le (y : TorusSite n) (η : Fin 4 → ℤ) (D : ℕ) (h : ∀ a, (η a).natAbs ≤ D) :
    TorusFields.supDist (siteAt y η) y ≤ D := by apply _root_.YangMills.DeltaSharedProofs.p502390 <;> assumption
private theorem natAbs_centredCoords_le (y z : TorusSite n) (a : Fin 4) :
    (centredCoords y z a).natAbs ≤ TorusFields.supDist z y :=
  (supDist_le_iff z y _).mp le_rfl a
private def primitive (f : ℤ → ℝ) (k : ℤ) : ℝ := ∑ j ∈ Finset.Ico 0 k, f j - ∑ j ∈ Finset.Ico k 0, f j
private theorem primitive_zero (f : ℤ → ℝ) : primitive f 0 = 0 := by simp [primitive]
private theorem primitive_succ_sub (f : ℤ → ℝ) (k : ℤ) : primitive f (k + 1) - primitive f k = f k := by apply _root_.YangMills.Construction.SlopeCoefficient.discretePrimitive_succ_sub <;> assumption
private theorem abs_primitive_le (f : ℤ → ℝ) {M : ℝ} (hf : ∀ j, |f j| ≤ M) (k : ℤ) :
    |primitive f k| ≤ |(k : ℝ)| * M := by
  have up : ∀ N : ℕ, |primitive f N| ≤ (N : ℝ) * M := by
    intro N
    induction N with
    | zero => simp [primitive_zero]
    | succ N ih =>
      have h := primitive_succ_sub f N
      have e : primitive f ((N + 1 : ℕ) : ℤ) = primitive f N + f N := by
        push_cast
        linarith
      rw [e]
      calc _ ≤ |primitive f N| + |f N| := abs_add_le _ _
        _ ≤ (N : ℝ) * M + M := add_le_add ih (hf _)
        _ = _ := by push_cast; ring
  have dn : ∀ N : ℕ, |primitive f (-(N : ℤ))| ≤ (N : ℝ) * M := by
    intro N
    induction N with
    | zero => simp [primitive_zero]
    | succ N ih =>
      have h := primitive_succ_sub f (-((N + 1 : ℕ) : ℤ))
      have e0 : -((N + 1 : ℕ) : ℤ) + 1 = -(N : ℤ) := by push_cast; ring
      rw [e0] at h
      have e : primitive f (-((N + 1 : ℕ) : ℤ)) = primitive f (-(N : ℤ)) - f (-((N + 1 : ℕ) : ℤ)) := by linarith
      rw [e]
      calc _ ≤ |primitive f (-(N : ℤ))| + |f (-((N + 1 : ℕ) : ℤ))| := abs_sub _ _
        _ ≤ (N : ℝ) * M + M := add_le_add ih (hf _)
        _ = _ := by push_cast; ring
  rcases le_total 0 k with hk | hk
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simpa using up N
  · obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hk)
    have hk' : k = -(N : ℤ) := by omega
    subst hk'
    simpa using dn N
private def lineSum (X : TorusBond n → ℝ) (y : TorusSite n) (w : Fin 4 → ℤ) (j : Fin 4) (k : ℤ) : ℝ :=
  primitive (fun l => X (siteAt y (w + l • basisVec j), j)) k
private def truncate (l : ℕ) (ζ : Fin 4 → ℤ) : Fin 4 → ℤ := fun a => if a.val < l then ζ a else 0
private def pathSum (X : TorusBond n → ℝ) (y : TorusSite n) (ζ : Fin 4 → ℤ) : ℝ :=
  ∑ j : Fin 4, lineSum X y (truncate j.val ζ) j (ζ j)
private def stripLoop (X : TorusBond n → ℝ) (y : TorusSite n) (t : Fin 4 → ℤ) (i j : Fin 4) (K : ℤ) : ℝ :=
  X (siteAt y (t + K • basisVec j), i) - X (siteAt y t, i) - lineSum X y (t + basisVec i) j K + lineSum X y t j K
private theorem curlCombination_stripLoop {w : TorusSite n → ℝ} (hw : ∀ x, 0 ≤ w x) (y : TorusSite n)
    (t : Fin 4 → ℤ) (i j : Fin 4) (K : ℤ) {W : ℝ}
    (hW : ∀ k : ℤ, min 0 K ≤ k → k < max 0 K → w (siteAt y (t + k • basisVec j)) ≤ W) :
    CurlCombination w (fun X => stripLoop X y t i j K) (|(K : ℝ)| * W) := by
  refine curlCombination_telescope hw (fun k X => stripLoop X y t i j k) (fun X => ?_) K fun k h1 h2 => ?_
  · simp [stripLoop, lineSum, primitive_zero]
  · refine (((curlCombination_curl hw (siteAt y (t + k • basisVec j)) i j).neg).mono (hW k h1 h2)).congr
      fun X => ?_
    have e1 : siteAt y (t + (k + 1) • basisVec j) = siteAt y (t + k • basisVec j) + unitStep n j := by
      rw [← siteAt_add_basisVec]
      congr 1
      rw [add_smul, one_smul, add_assoc]
    have e2 : siteAt y (t + basisVec i + k • basisVec j) = siteAt y (t + k • basisVec j) + unitStep n i := by
      rw [← siteAt_add_basisVec]
      congr 1
      abel
    have p1 := primitive_succ_sub (fun l => X (siteAt y (t + basisVec i + l • basisVec j), j)) k
    have p2 := primitive_succ_sub (fun l => X (siteAt y (t + l • basisVec j), j)) k
    simp only [stripLoop, lineSum, WeightedResponses.curl]
    rw [e2] at p1
    rw [e1]
    linarith
private theorem truncate_add_of_le {j : ℕ} {i : Fin 4} (h : j ≤ i.val) (ζ : Fin 4 → ℤ) :
    truncate j (ζ + basisVec i) = truncate j ζ := by
  funext a
  simp only [truncate]
  split_ifs with ha
  · have : a ≠ i := fun e => by subst e; omega
    simp [Pi.single_apply, this]
  · rfl
private theorem truncate_add_of_lt {j : ℕ} {i : Fin 4} (h : i.val < j) (ζ : Fin 4 → ℤ) :
    truncate j (ζ + basisVec i) = truncate j ζ + basisVec i := by
  funext a
  simp only [truncate, Pi.add_apply]
  split_ifs with ha
  · rfl
  · have : a ≠ i := fun e => by subst e; omega
    simp [Pi.single_apply, this]
private theorem truncate_succ (j : Fin 4) (ζ : Fin 4 → ℤ) :
    truncate j.val ζ + ζ j • basisVec j = truncate (j.val + 1) ζ := by
  funext a
  simp only [truncate, Pi.add_apply, Pi.smul_apply, Pi.single_apply, basisVec, smul_eq_mul]
  by_cases h : a = j
  · subst h
    simp
  · have : a.val ≠ j.val := fun e => h (Fin.ext e)
    by_cases h2 : a.val < j.val
    · have h3 : a.val < j.val + 1 := by omega
      simp [h, h2, h3]
    · have h3 : ¬ a.val < j.val + 1 := by omega
      simp [h, h2, h3]
private theorem truncate_four (ζ : Fin 4 → ℤ) : truncate 4 ζ = ζ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.leadingCoords_four <;> assumption
private def pathGaugeCoords (X : TorusBond n → ℝ) (y : TorusSite n) (ζ : Fin 4 → ℤ) (i : Fin 4) : ℝ :=
  X (siteAt y ζ, i) - pathSum X y (ζ + basisVec i) + pathSum X y ζ
private theorem lineSum_step (X : TorusBond n → ℝ) (y : TorusSite n) (ζ : Fin 4 → ℤ) (i j : Fin 4) :
    lineSum X y (truncate j.val (ζ + basisVec i)) j ((ζ + basisVec i) j) - lineSum X y (truncate j.val ζ) j (ζ j) =
      if j < i then 0 else if j = i then X (siteAt y (truncate (i.val + 1) ζ), i)
        else lineSum X y (truncate j.val ζ + basisVec i) j (ζ j) - lineSum X y (truncate j.val ζ) j (ζ j) := by
  split_ifs with h1 h2
  · have hne : j ≠ i := ne_of_lt h1
    rw [truncate_add_of_le (le_of_lt h1)]
    simp [Pi.single_apply, hne]
  · subst h2
    rw [truncate_add_of_le le_rfl]
    have e : (ζ + basisVec j) j = ζ j + 1 := by simp
    rw [e]
    have := primitive_succ_sub (fun l => X (siteAt y (truncate j.val ζ + l • basisVec j), j)) (ζ j)
    simp only [lineSum]
    rw [this, truncate_succ]
  · have hgt : i.val < j.val := by
      have : i ≠ j := fun e => h2 e.symm
      have h4 : i.val ≠ j.val := fun e => this (Fin.ext e)
      omega
    rw [truncate_add_of_lt hgt]
    have hne : j ≠ i := h2
    simp [Pi.single_apply, hne]
private theorem stripLoop_truncate (X : TorusBond n → ℝ) (y : TorusSite n) (ζ : Fin 4 → ℤ) (i j : Fin 4) :
    stripLoop X y (truncate j.val ζ) i j (ζ j) = X (siteAt y (truncate (j.val + 1) ζ), i) -
      X (siteAt y (truncate j.val ζ), i) - lineSum X y (truncate j.val ζ + basisVec i) j (ζ j) +
        lineSum X y (truncate j.val ζ) j (ζ j) := by
  simp only [stripLoop, truncate_succ]
private theorem fin_four_cases : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
private theorem pathGaugeCoords_eq (X : TorusBond n → ℝ) (y : TorusSite n) (ζ : Fin 4 → ℤ) (i : Fin 4) :
    pathGaugeCoords X y ζ i = ∑ j : Fin 4, if i < j then stripLoop X y (truncate j.val ζ) i j (ζ j) else 0 := by
  have e : pathGaugeCoords X y ζ i = X (siteAt y ζ, i) - ∑ j : Fin 4,
      (lineSum X y (truncate j.val (ζ + basisVec i)) j ((ζ + basisVec i) j) -
        lineSum X y (truncate j.val ζ) j (ζ j)) := by
    simp only [pathGaugeCoords, pathSum, Finset.sum_sub_distrib]
    ring
  rw [e]
  simp only [lineSum_step, stripLoop_truncate]
  have hX : X (siteAt y ζ, i) = X (siteAt y (truncate 4 ζ), i) := by rw [truncate_four]
  rw [hX]
  obtain rfl | rfl | rfl | rfl := fin_four_cases i <;>
  · simp (decide := true) only [Fin.sum_univ_four, show ((3 : Fin 4) : ℕ) = 3 from rfl,
      show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
      show ((0 : Fin 4) : ℕ) = 0 from rfl, if_true, if_false, zero_add, Nat.reduceAdd]
    ring
private theorem curlCombination_sum {ι : Type} {w : TorusSite n → ℝ} (hw : ∀ x, 0 ≤ w x) (s : Finset ι)
    (f : ι → (TorusBond n → ℝ) → ℝ) (S : ι → ℝ) (h : ∀ j ∈ s, CurlCombination w (f j) (S j)) :
    CurlCombination w (fun X => ∑ j ∈ s, f j X) (∑ j ∈ s, S j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (curlCombination_zero w).congr fun X => by simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine ((h a (Finset.mem_insert_self _ _)).add hw
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).congr fun X => ?_
    rw [Finset.sum_insert ha]
private def distWeight (c : ℝ) (y : TorusSite n) : TorusSite n → ℝ := fun x => Real.exp (c * (TorusFields.supDist x y : ℝ))
private theorem distWeight_nonneg (c : ℝ) (y : TorusSite n) (x : TorusSite n) : 0 ≤ distWeight c y x :=
  (Real.exp_pos _).le
private theorem distWeight_siteAt_le {c : ℝ} (hc : 0 ≤ c) (y : TorusSite n) (η : Fin 4 → ℤ) (D : ℕ)
    (h : ∀ a, (η a).natAbs ≤ D) : distWeight c y (siteAt y η) ≤ Real.exp (c * (D : ℝ)) := by
  refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hc)
  exact_mod_cast supDist_siteAt_le y η D h
private theorem curlCombination_pathGaugeCoords {c : ℝ} (hc : 0 ≤ c) (y : TorusSite n) (ζ : Fin 4 → ℤ) (i : Fin 4)
    (D : ℕ) (h : ∀ a, (ζ a).natAbs ≤ D) :
    CurlCombination (distWeight c y) (fun X => pathGaugeCoords X y ζ i)
      ((∑ a : Fin 4, |(ζ a : ℝ)|) * Real.exp (c * (D : ℝ))) := by
  have hs : ∀ j ∈ (Finset.univ : Finset (Fin 4)), CurlCombination (distWeight c y)
      (fun X => if i < j then stripLoop X y (truncate j.val ζ) i j (ζ j) else 0)
      (|(ζ j : ℝ)| * Real.exp (c * (D : ℝ))) := by
    intro j _
    by_cases hij : i < j
    · simp only [hij, if_true]
      refine curlCombination_stripLoop (distWeight_nonneg c y) y _ i j (ζ j) fun k h1 h2 =>
        distWeight_siteAt_le hc y _ D fun a => ?_
      have hk : k.natAbs ≤ (ζ j).natAbs := by
        rcases le_total 0 (ζ j) with h0 | h0
        · rw [min_eq_left h0] at h1
          rw [max_eq_right h0] at h2
          omega
        · rw [min_eq_right h0] at h1
          rw [max_eq_left h0] at h2
          omega
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, basisVec, smul_eq_mul, truncate]
      by_cases haj : a = j
      · subst haj
        simpa using hk.trans (h a)
      · simp only [haj, if_false, mul_zero, add_zero]
        split_ifs
        · exact h a
        · simp
    · simp only [hij, if_false]
      exact (curlCombination_zero _).mono (by positivity)
  have := curlCombination_sum (distWeight_nonneg c y) Finset.univ _ _ hs
  rw [← Finset.sum_mul] at this
  exact this.congr fun X => pathGaugeCoords_eq X y ζ i
end LatticePaths
section AxialGauge
variable {n : ℕ} [NeZero n]
private def pathGauge (X : TorusBond n → ℝ) (y : TorusSite n) : TorusBond n → ℝ := fun b =>
  X b - pathSum X y (centredCoords y (b.1 + unitStep n b.2)) + pathSum X y (centredCoords y b.1)
private theorem pathGauge_siteAt (X : TorusBond n → ℝ) (y : TorusSite n) {ζ : Fin 4 → ℤ} {i : Fin 4}
    (h1 : InCentredCube n ζ) (h2 : InCentredCube n (ζ + basisVec i)) :
    pathGauge X y (siteAt y ζ, i) = pathGaugeCoords X y ζ i := by
  simp only [pathGauge, pathGaugeCoords]
  rw [← siteAt_add_basisVec, centredCoords_siteAt y h2, centredCoords_siteAt y h1]
private theorem curl_pathGauge (X : TorusBond n → ℝ) (y : TorusSite n) (p : TorusPlaquette n) :
    WeightedResponses.curl (pathGauge X y) p = WeightedResponses.curl X p := by
  obtain ⟨x, i, j⟩ := p
  simp only [WeightedResponses.curl, pathGauge]
  rw [show x + unitStep n j + unitStep n i = x + unitStep n i + unitStep n j by abel]
  ring
private def CrossesWall (n : ℕ) (i : Fin 4) (ζ : Fin 4 → ℤ) : Prop := (n : ℤ) < 2 * (ζ i + 1)
private theorem inCentredCube_add {ζ : Fin 4 → ℤ} {i : Fin 4} (h : InCentredCube n ζ) (hc : ¬ CrossesWall n i ζ) :
    InCentredCube n (ζ + basisVec i) := by
  intro a
  have ha := h a
  simp only [CrossesWall, not_lt] at hc
  by_cases e : a = i
  · subst e
    simp only [Pi.add_apply, Pi.single_eq_same]
    omega
  · simpa [Pi.single_apply, e] using ha
private theorem inCentredCube_wrap {ζ : Fin 4 → ℤ} {i : Fin 4} (h : InCentredCube n ζ) (hc : CrossesWall n i ζ) :
    InCentredCube n (ζ + basisVec i - (n : ℤ) • basisVec i) := by
  intro a
  have ha := h a
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  simp only [CrossesWall] at hc
  by_cases e : a = i
  · subst e
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    omega
  · simpa [Pi.single_apply, e] using ha
private theorem eq_half_of_crossesWall {ζ : Fin 4 → ℤ} {i : Fin 4} (h : InCentredCube n ζ)
    (hc : CrossesWall n i ζ) : ζ i = ((n / 2 : ℕ) : ℤ) := by
  have ha := h i
  simp only [CrossesWall] at hc
  omega
private theorem natAbs_le_half {ζ : Fin 4 → ℤ} (h : InCentredCube n ζ) (a : Fin 4) : (ζ a).natAbs ≤ n / 2 := by
  have ha := h a
  omega
private theorem abs_intCast_le {k : ℤ} {D : ℕ} (h : k.natAbs ≤ D) : |(k : ℝ)| ≤ (D : ℝ) := by
  have h' : ((k.natAbs : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast h
  rwa [Nat.cast_natAbs, Int.cast_abs] at h'
private theorem sum_abs_coords_le {ζ : Fin 4 → ℤ} {D : ℕ} (h : ∀ a, (ζ a).natAbs ≤ D) :
    ∑ a : Fin 4, |(ζ a : ℝ)| ≤ 4 * (D : ℝ) := by
  calc _ ≤ ∑ _a : Fin 4, (D : ℝ) := Finset.sum_le_sum fun a _ => abs_intCast_le (h a)
    _ = _ := by simp
private theorem distWeight_le_half {c : ℝ} (hc : 0 ≤ c) (y x : TorusSite n) :
    distWeight c y x ≤ Real.exp (c * ((n / 2 : ℕ) : ℝ)) := by
  have := distWeight_siteAt_le hc y (centredCoords y x) (n / 2) (natAbs_le_half (inCentredCube_centredCoords y x))
  rwa [siteAt_centredCoords] at this
private theorem curlCombination_wallMove {c : ℝ} (hc : 0 ≤ c) (y : TorusSite n) {θ : Fin 4 → ℤ} {i a : Fin 4}
    (hai : a ≠ i) (h1 : InCentredCube n θ) (h2 : InCentredCube n (θ + basisVec a)) (hx : CrossesWall n i θ) :
    CurlCombination (distWeight c y)
      (fun X => pathGauge X y (siteAt y (θ + basisVec a), i) - pathGauge X y (siteAt y θ, i))
      ((1 + 8 * ((n / 2 : ℕ) : ℝ)) * Real.exp (c * ((n / 2 : ℕ) : ℝ))) := by
  set τ : ℕ := n / 2 with hτ
  set W : ℝ := Real.exp (c * (τ : ℝ)) with hWd
  have hW : 0 ≤ W := (Real.exp_pos _).le
  set θ' : Fin 4 → ℤ := θ + basisVec i - (n : ℤ) • basisVec i with hθ'
  have c1 : InCentredCube n θ' := inCentredCube_wrap h1 hx
  have c2 : InCentredCube n (θ' + basisVec a) := by
    intro b
    by_cases e : b = a
    · subst e
      have := h2 b
      simpa [hθ', Pi.single_apply, hai] using this
    · have := c1 b
      simpa [Pi.single_apply, e] using this
  have hpt : siteAt y θ' = siteAt y θ + unitStep n i := by rw [hθ', siteAt_sub_side, siteAt_add_basisVec]
  have r1 := curlCombination_pathGaugeCoords hc y θ a τ (natAbs_le_half h1)
  have r2 := curlCombination_pathGaugeCoords hc y θ' a τ (natAbs_le_half c1)
  have r0 := curlCombination_curl (distWeight_nonneg c y) (siteAt y θ) i a
  have s1 : (∑ b : Fin 4, |(θ b : ℝ)|) * W ≤ 4 * (τ : ℝ) * W :=
    mul_le_mul_of_nonneg_right (sum_abs_coords_le (natAbs_le_half h1)) hW
  have s2 : (∑ b : Fin 4, |(θ' b : ℝ)|) * W ≤ 4 * (τ : ℝ) * W :=
    mul_le_mul_of_nonneg_right (sum_abs_coords_le (natAbs_le_half c1)) hW
  have s0 : distWeight c y (siteAt y θ) ≤ W := distWeight_le_half hc y _
  refine (((r0.mono s0).neg.add (distWeight_nonneg c y) (r2.mono s2)).sub (distWeight_nonneg c y)
    (r1.mono s1)).mono (by nlinarith) |>.congr fun X => ?_
  have e := curl_pathGauge X y (siteAt y θ, i, a)
  simp only [WeightedResponses.curl] at e
  rw [siteAt_add_basisVec, ← pathGauge_siteAt X y c1 c2, ← pathGauge_siteAt X y h1 h2, hpt]
  simp only [WeightedResponses.curl]
  linarith
private def partialCoords (i : Fin 4) (ζ : Fin 4 → ℤ) (l : ℕ) : Fin 4 → ℤ :=
  fun a => if a.val < l ∨ a = i then ζ a else 0
private theorem partialCoords_four (i : Fin 4) (ζ : Fin 4 → ℤ) : partialCoords i ζ 4 = ζ := by
  funext a
  simp [partialCoords, a.isLt]
private theorem partialCoords_zero (i : Fin 4) (ζ : Fin 4 → ℤ) : partialCoords i ζ 0 = ζ i • basisVec i := by
  funext a
  simp only [partialCoords, Pi.smul_apply, Pi.single_apply, basisVec, smul_eq_mul]
  by_cases e : a = i
  · subst e
    simp
  · simp [e]
private theorem partialCoords_self {i : Fin 4} (ζ : Fin 4 → ℤ) :
    partialCoords i ζ (i.val + 1) = partialCoords i ζ i.val := by
  funext a
  simp only [partialCoords]
  by_cases e : a = i
  · simp [e]
  · have : a.val ≠ i.val := fun h => e (Fin.ext h)
    have h1 : a.val < i.val + 1 ↔ a.val < i.val := by omega
    simp [e, h1]
private theorem partialCoords_succ {i a : Fin 4} (hai : a ≠ i) (ζ : Fin 4 → ℤ) :
    partialCoords i ζ (a.val + 1) = partialCoords i ζ a.val + ζ a • basisVec a := by
  funext b
  simp only [partialCoords, Pi.add_apply, Pi.smul_apply, Pi.single_apply, basisVec, smul_eq_mul]
  by_cases e : b = a
  · subst e
    simp [hai]
  · have h0 : b.val ≠ a.val := fun h => e (Fin.ext h)
    have h1 : b.val < a.val + 1 ↔ b.val < a.val := by omega
    simp [e, h1]
private theorem curlCombination_wallSurface {c : ℝ} (hc : 0 ≤ c) (y : TorusSite n) {ζ : Fin 4 → ℤ} {i : Fin 4}
    (h : InCentredCube n ζ) (hx : CrossesWall n i ζ) (l : ℕ) (hl : l ≤ 4) :
    CurlCombination (distWeight c y)
      (fun X => pathGauge X y (siteAt y (partialCoords i ζ l), i) - pathGauge X y (siteAt y (partialCoords i ζ 0), i))
      ((l : ℝ) * (((n / 2 : ℕ) : ℝ) * ((1 + 8 * ((n / 2 : ℕ) : ℝ)) * Real.exp (c * ((n / 2 : ℕ) : ℝ))))) := by
  set τ : ℕ := n / 2 with hτ
  set S : ℝ := (1 + 8 * (τ : ℝ)) * Real.exp (c * (τ : ℝ)) with hS
  have hS0 : 0 ≤ S := by positivity
  have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg _
  induction l with
  | zero =>
    refine ((curlCombination_zero _).mono (by simp)).congr fun X => ?_
    simp
  | succ l ih =>
    have hl' : l < 4 := by omega
    have ih' := ih (by omega)
    set a : Fin 4 := ⟨l, hl'⟩ with ha
    have hlv : a.val = l := rfl
    by_cases e : a = i
    · have hs := partialCoords_self (i := i) ζ
      have hli : i.val = l := by rw [← e]
      rw [hli] at hs
      rw [hs]
      refine (ih'.mono ?_)
      push_cast
      nlinarith [mul_nonneg hτ0 hS0]
    · have hs := partialCoords_succ e ζ
      rw [hlv] at hs
      have hη : ∀ b, b ≠ a → partialCoords i ζ l b = 0 ∨ partialCoords i ζ l b = ζ b := by
        intro b _
        simp only [partialCoords]
        split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl
      have hηa : partialCoords i ζ l a = 0 := by
        simp only [partialCoords]
        rw [if_neg]
        rintro (h1 | h1)
        · simp [ha] at h1
        · exact e h1
      have hηi : partialCoords i ζ l i = ζ i := by simp [partialCoords]
      have hie : i ≠ a := fun h1 => e h1.symm
      have cubeAt : ∀ k : ℤ, min 0 (ζ a) ≤ k → k ≤ max 0 (ζ a) →
          InCentredCube n (partialCoords i ζ l + k • basisVec a) := by
        intro k k1 k2 b
        have hb := h b
        have hb' := h a
        by_cases eb : b = a
        · subst eb
          simp only [Pi.add_apply, hηa, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, zero_add]
          rcases le_total 0 (ζ a) with h0 | h0
          · rw [min_eq_left h0] at k1
            rw [max_eq_right h0] at k2
            omega
          · rw [min_eq_right h0] at k1
            rw [max_eq_left h0] at k2
            omega
        · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, basisVec, eb, if_false, smul_eq_mul, mul_zero,
            add_zero]
          rcases hη b eb with h1 | h1 <;> rw [h1]
          · have := NeZero.ne n
            omega
          · exact hb
      have step : ∀ k : ℤ, min 0 (ζ a) ≤ k → k < max 0 (ζ a) →
          CurlCombination (distWeight c y)
            (fun X => (pathGauge X y (siteAt y (partialCoords i ζ l + (k + 1) • basisVec a), i) -
                pathGauge X y (siteAt y (partialCoords i ζ l), i)) -
              (pathGauge X y (siteAt y (partialCoords i ζ l + k • basisVec a), i) -
                pathGauge X y (siteAt y (partialCoords i ζ l), i))) S := by
        intro k k1 k2
        have e1 : partialCoords i ζ l + (k + 1) • basisVec a = (partialCoords i ζ l + k • basisVec a) + basisVec a := by
          rw [add_smul, one_smul, add_assoc]
        have hc1 := cubeAt k k1 k2.le
        have hc2 : InCentredCube n (partialCoords i ζ l + k • basisVec a + basisVec a) := by
          rw [← e1]
          exact cubeAt (k + 1) (by omega) (by omega)
        have hx' : CrossesWall n i (partialCoords i ζ l + k • basisVec a) := by
          simp only [CrossesWall, Pi.add_apply, Pi.smul_apply, Pi.single_apply, basisVec, hie, if_false, smul_eq_mul,
            mul_zero, add_zero, hηi]
          exact hx
        refine (curlCombination_wallMove hc y e hc1 hc2 hx').congr fun X => ?_
        rw [e1]
        ring
      have tele := curlCombination_telescope (distWeight_nonneg c y)
        (fun k X => pathGauge X y (siteAt y (partialCoords i ζ l + k • basisVec a), i) -
          pathGauge X y (siteAt y (partialCoords i ζ l), i))
        (fun X => by simp) (ζ a) step
      rw [hs]
      have hza : |(ζ a : ℝ)| ≤ (τ : ℝ) := abs_intCast_le (natAbs_le_half h a)
      refine (ih'.add (distWeight_nonneg c y) tele).mono ?_ |>.congr fun X => by ring
      push_cast
      have := mul_le_mul_of_nonneg_right hza hS0
      nlinarith
open Classical in
private def pathForm (X : TorusBond n → ℝ) (y : TorusSite n) (b : TorusBond n) : ℝ :=
  pathGauge X y b - if CrossesWall n b.2 (centredCoords y b.1) then
    pathGauge X y (siteAt y (((n / 2 : ℕ) : ℤ) • basisVec b.2), b.2) else 0
private def pathFormMass (c : ℝ) (y : TorusSite n) (b : TorusBond n) : ℝ :=
  36 * ((TorusFields.supDist b.1 y : ℝ) + 1) ^ 2 * Real.exp (c * (TorusFields.supDist b.1 y : ℝ))
private theorem curlCombination_pathForm {c : ℝ} (hc : 0 ≤ c) (y : TorusSite n) (b : TorusBond n) :
    CurlCombination (distWeight c y) (fun X => pathForm X y b) (pathFormMass c y b) := by
  obtain ⟨z, i⟩ := b
  set ζ := centredCoords y z with hζ
  have hz : siteAt y ζ = z := siteAt_centredCoords y z
  have hcube : InCentredCube n ζ := inCentredCube_centredCoords y z
  set d : ℕ := TorusFields.supDist z y with hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hnat : ∀ a, (ζ a).natAbs ≤ d := natAbs_centredCoords_le y z
  simp only [pathFormMass]
  by_cases hx : CrossesWall n i ζ
  · have hs := curlCombination_wallSurface hc y hcube hx 4 le_rfl
    have htop := eq_half_of_crossesWall hcube hx
    rw [partialCoords_four, partialCoords_zero, htop, hz] at hs
    refine (hs.mono ?_).congr fun X => ?_
    · have hτd : ((n / 2 : ℕ) : ℝ) ≤ (d : ℝ) := by
        have h1 := hnat i
        rw [htop] at h1
        have h2 : n / 2 ≤ d := by rwa [Int.natAbs_natCast] at h1
        exact_mod_cast h2
      have he : Real.exp (c * ((n / 2 : ℕ) : ℝ)) ≤ Real.exp (c * (d : ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτd hc)
      have he0 : 0 ≤ Real.exp (c * ((n / 2 : ℕ) : ℝ)) := (Real.exp_pos _).le
      have hp : ((n / 2 : ℕ) : ℝ) * (1 + 8 * ((n / 2 : ℕ) : ℝ)) ≤ (d : ℝ) * (1 + 8 * (d : ℝ)) := by
        apply mul_le_mul hτd (by linarith) (by positivity) hd0
      calc ((4 : ℕ) : ℝ) * (((n / 2 : ℕ) : ℝ) * ((1 + 8 * ((n / 2 : ℕ) : ℝ)) * Real.exp (c * ((n / 2 : ℕ) : ℝ))))
          = 4 * (((n / 2 : ℕ) : ℝ) * (1 + 8 * ((n / 2 : ℕ) : ℝ))) * Real.exp (c * ((n / 2 : ℕ) : ℝ)) := by
            push_cast
            ring
        _ ≤ 4 * ((d : ℝ) * (1 + 8 * (d : ℝ))) * Real.exp (c * (d : ℝ)) := by
            apply mul_le_mul (by linarith) he he0 (by positivity)
        _ ≤ 36 * ((d : ℝ) + 1) ^ 2 * Real.exp (c * (d : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            nlinarith
    · simp only [pathForm]
      rw [if_pos hx]
  · have h2 := inCentredCube_add hcube hx
    have hr := curlCombination_pathGaugeCoords hc y ζ i d hnat
    refine (hr.mono ?_).congr fun X => ?_
    · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have := sum_abs_coords_le hnat
      nlinarith
    · simp only [pathForm]
      rw [if_neg hx, ← pathGauge_siteAt X y hcube h2, hz]
      simp
private theorem centredCoords_add_unitStep (y z : TorusSite n) (j : Fin 4) (e : ℤ)
    (he : e = if (n : ℤ) < 2 * (centredCoords y z j + 1) then 1 - (n : ℤ) else 1) :
    centredCoords y (z + unitStep n j) = centredCoords y z + e • basisVec j := by
  by_cases hx : CrossesWall n j (centredCoords y z)
  · have h1 := inCentredCube_wrap (inCentredCube_centredCoords y z) hx
    have h2 : siteAt y (centredCoords y z + basisVec j - (n : ℤ) • basisVec j) = z + unitStep n j := by
      rw [siteAt_sub_side, siteAt_add_basisVec, siteAt_centredCoords]
    rw [← h2, centredCoords_siteAt y h1]
    have hx' : (n : ℤ) < 2 * (centredCoords y z j + 1) := hx
    rw [he, if_pos hx', sub_smul, one_smul]
    abel
  · have h1 := inCentredCube_add (inCentredCube_centredCoords y z) hx
    have h2 : siteAt y (centredCoords y z + basisVec j) = z + unitStep n j := by
      rw [siteAt_add_basisVec, siteAt_centredCoords]
    have hx' : ¬ (n : ℤ) < 2 * (centredCoords y z j + 1) := hx
    rw [← h2, centredCoords_siteAt y h1, he, if_neg hx', one_smul]
private theorem exists_pathForm_decomposition (X : TorusBond n → ℝ) (y : TorusSite n) :
    ∃ (ψ : TorusSite n → ℝ) (v : Fin 4 → ℝ),
      ∀ b, X b = (pathForm X y b + latticeGradient ψ b) + constantOneForm v b := by
  classical
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  set β : Fin 4 → ℝ := fun i => pathGauge X y (siteAt y (((n / 2 : ℕ) : ℤ) • basisVec i), i) with hβ
  refine ⟨fun z => pathSum X y (centredCoords y z) - ∑ i, β i * (centredCoords y z i : ℝ) / n,
    fun i => β i / n, ?_⟩
  rintro ⟨z, j⟩
  set e : ℤ := if (n : ℤ) < 2 * (centredCoords y z j + 1) then 1 - (n : ℤ) else 1 with he
  have hnext := centredCoords_add_unitStep y z j e he
  have hsum : ∑ i, β i * (centredCoords y (z + unitStep n j) i : ℝ) / n -
      ∑ i, β i * (centredCoords y z i : ℝ) / n = β j * (e : ℝ) / n := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · rw [hnext]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      push_cast
      ring
    · intro i _ hij
      rw [hnext]
      simp [Pi.single_apply, hij]
    · simp
  simp only [pathForm, pathGauge, latticeGradient, constantOneForm]
  by_cases hx : CrossesWall n j (centredCoords y z)
  · have hx' : (n : ℤ) < 2 * (centredCoords y z j + 1) := hx
    have he' : (e : ℝ) = 1 - (n : ℝ) := by
      rw [he, if_pos hx']
      push_cast
      ring
    rw [if_pos hx]
    rw [he'] at hsum
    have h3 : β j * (1 - (n : ℝ)) / n = β j / n - β j := by
      field_simp
    have h4 : pathGauge X y (siteAt y (((n / 2 : ℕ) : ℤ) • basisVec j), j) = β j := rfl
    simp only [pathGauge] at h4
    linarith
  · have hx' : ¬ (n : ℤ) < 2 * (centredCoords y z j + 1) := hx
    have he' : (e : ℝ) = 1 := by
      rw [he, if_neg hx']
      simp
    rw [if_neg hx]
    rw [he'] at hsum
    have h3 : β j * 1 / n = β j / n := by ring
    linarith
private theorem bilinearEval_add_left (q : BondBilinear n) (f g A : TorusBond n → ℝ) :
    bilinearEval q (fun b => f b + g b) A = bilinearEval q f A + bilinearEval q g A := by
  simp only [bilinearEval, add_mul, Finset.sum_add_distrib]
private theorem bilinearEval_add_right (q : BondBilinear n) (f g A : TorusBond n → ℝ) :
    bilinearEval q A (fun b => f b + g b) = bilinearEval q A f + bilinearEval q A g := by
  simp only [bilinearEval, mul_add, Finset.sum_add_distrib]
private theorem bilinearEval_pathForm_left {q : BondBilinear n} (h : AnnihilatesClosedForms q)
    (X A : TorusBond n → ℝ) (y : TorusSite n) :
    bilinearEval q X A = bilinearEval q (fun b => pathForm X y b) A := by
  obtain ⟨ψ, v, hd⟩ := exists_pathForm_decomposition X y
  have e : X = fun b => (fun b => pathForm X y b + latticeGradient ψ b) b + constantOneForm v b := funext hd
  conv_lhs => rw [e]
  rw [bilinearEval_add_left, bilinearEval_add_left, (h.1 ψ A).1, (h.2 v A).1]
  simp
private theorem bilinearEval_pathForm_right {q : BondBilinear n} (h : AnnihilatesClosedForms q)
    (X A : TorusBond n → ℝ) (y : TorusSite n) :
    bilinearEval q A X = bilinearEval q A (fun b => pathForm X y b) := by
  obtain ⟨ψ, v, hd⟩ := exists_pathForm_decomposition X y
  have e : X = fun b => (fun b => pathForm X y b + latticeGradient ψ b) b + constantOneForm v b := funext hd
  conv_lhs => rw [e]
  rw [bilinearEval_add_right, bilinearEval_add_right, (h.1 ψ A).2, (h.2 v A).2]
  simp
private theorem sum_comm_four {α β : Type} (s : Finset α) (t : Finset β) (F : α → α → β → β → ℝ) :
    ∑ p ∈ s, ∑ p' ∈ s, ∑ b ∈ t, ∑ b' ∈ t, F p p' b b' = ∑ b ∈ t, ∑ b' ∈ t, ∑ p ∈ s, ∑ p' ∈ s, F p p' b b' := by
  calc _ = ∑ p ∈ s, ∑ b ∈ t, ∑ p' ∈ s, ∑ b' ∈ t, F p p' b b' := Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ b ∈ t, ∑ p ∈ s, ∑ p' ∈ s, ∑ b' ∈ t, F p p' b b' := Finset.sum_comm
    _ = ∑ b ∈ t, ∑ p ∈ s, ∑ b' ∈ t, ∑ p' ∈ s, F p p' b b' :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun b _ => Finset.sum_comm
private theorem exists_curl_kernel {c : ℝ} (hc : 0 ≤ c) (y : TorusSite n) {q : BondBilinear n}
    (h : AnnihilatesClosedForms q) :
    ∃ κ : TorusPlaquette n → TorusPlaquette n → ℝ,
      (∀ X X' : TorusBond n → ℝ, bilinearEval q X X' = ∑ p ∈ orderedPlaquettes n, ∑ p' ∈ orderedPlaquettes n,
        κ p p' * WeightedResponses.curl X p * WeightedResponses.curl X' p') ∧
      ∑ p ∈ orderedPlaquettes n, ∑ p' ∈ orderedPlaquettes n, |κ p p'| * (distWeight c y p.1 * distWeight c y p'.1) ≤
        ∑ b : TorusBond n, ∑ b' : TorusBond n, pathFormMass c y b * |q b b'| * pathFormMass c y b' := by
  choose a ha1 ha2 using fun b => curlCombination_pathForm hc y b
  refine ⟨fun p p' => ∑ b : TorusBond n, ∑ b' : TorusBond n, a b p * q b b' * a b' p', fun X X' => ?_, ?_⟩
  · rw [bilinearEval_pathForm_left h X X' y, bilinearEval_pathForm_right h X' _ y]
    simp only [bilinearEval, ha1, Finset.sum_mul]
    rw [sum_comm_four]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p' _ => by ring
  · have hω := distWeight_nonneg c y
    calc ∑ p ∈ orderedPlaquettes n, ∑ p' ∈ orderedPlaquettes n,
          |∑ b : TorusBond n, ∑ b' : TorusBond n, a b p * q b b' * a b' p'| *
            (distWeight c y p.1 * distWeight c y p'.1)
        ≤ ∑ p ∈ orderedPlaquettes n, ∑ p' ∈ orderedPlaquettes n, ∑ b : TorusBond n, ∑ b' : TorusBond n,
            (|a b p| * distWeight c y p.1) * |q b b'| * (|a b' p'| * distWeight c y p'.1) := by
          refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun p' _ => ?_
          have h1 : |∑ b : TorusBond n, ∑ b' : TorusBond n, a b p * q b b' * a b' p'| ≤
              ∑ b : TorusBond n, ∑ b' : TorusBond n, |a b p| * |q b b'| * |a b' p'| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
            rw [abs_mul, abs_mul]
          have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg (hω p.1) (hω p'.1))
          refine h2.trans (le_of_eq ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun b' _ => by ring
      _ = ∑ b : TorusBond n, ∑ b' : TorusBond n, ∑ p ∈ orderedPlaquettes n, ∑ p' ∈ orderedPlaquettes n,
            (|a b p| * distWeight c y p.1) * |q b b'| * (|a b' p'| * distWeight c y p'.1) := sum_comm_four _ _ _
      _ ≤ _ := by
          refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => ?_
          have e : ∑ p ∈ orderedPlaquettes n, ∑ p' ∈ orderedPlaquettes n,
                (|a b p| * distWeight c y p.1) * |q b b'| * (|a b' p'| * distWeight c y p'.1) =
              (∑ p ∈ orderedPlaquettes n, |a b p| * distWeight c y p.1) * |q b b'| *
                (∑ p' ∈ orderedPlaquettes n, |a b' p'| * distWeight c y p'.1) := by
            rw [Finset.sum_mul, Finset.sum_mul]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.mul_sum]
          rw [e]
          have s0 : 0 ≤ ∑ p' ∈ orderedPlaquettes n, |a b' p'| * distWeight c y p'.1 :=
            Finset.sum_nonneg fun p' _ => mul_nonneg (abs_nonneg _) (hω _)
          have m0 : 0 ≤ pathFormMass c y b := by
            simp only [pathFormMass]
            positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_right (ha2 b) (abs_nonneg _)) (ha2 b') s0 (by positivity)
end AxialGauge
section DoubleSums
variable {n : ℕ} [NeZero n]
private def doubleSumConst (r : ℝ) : ℝ := (1 + 16 / r) ^ 4 * (4 * expLatticeSum (r / 4)) ^ 2
private theorem sq_add_one_le_exp {r : ℝ} (hr : 0 < r) {d : ℝ} (hd : 0 ≤ d) :
    (d + 1) ^ 2 ≤ (1 + 16 / r) ^ 2 * Real.exp (r / 8 * d) := by
  set A : ℝ := 1 + 16 / r with hA
  have hA0 : 0 < A := by positivity
  have h1 : d + 1 ≤ A * Real.exp (r / 16 * d) := by
    have h2 : r / 16 * d + 1 ≤ Real.exp (r / 16 * d) := Real.add_one_le_exp _
    have h3 : d + 1 ≤ A * (r / 16 * d + 1) := by
      have e : A * (r / 16 * d + 1) = r / 16 * d + 1 + 16 / r + d := by
        rw [hA]
        field_simp
        ring
      rw [e]
      have : 0 ≤ r / 16 * d := by positivity
      have : 0 ≤ 16 / r := by positivity
      linarith
    exact h3.trans (mul_le_mul_of_nonneg_left h2 hA0.le)
  have h4 : (d + 1) ^ 2 ≤ (A * Real.exp (r / 16 * d)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  refine h4.trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring
private theorem supDist_le_tripleDiam (y : TorusSite n) (b b' : TorusBond n) :
    TorusFields.supDist b.1 y ≤ tripleDiam y b b' ∧ TorusFields.supDist b'.1 y ≤ tripleDiam y b b' := by
  simp only [tripleDiam, supportDiam]
  constructor
  · rw [supDist_comm]
    exact le_max_of_le_left (Finset.le_sup (f := fun l : Fin 2 => TorusFields.supDist y ((![b, b'] : Fin 2 → TorusBond n) l).1)
      (Finset.mem_univ (0 : Fin 2)))
  · rw [supDist_comm]
    exact le_max_of_le_left (Finset.le_sup (f := fun l : Fin 2 => TorusFields.supDist y ((![b, b'] : Fin 2 → TorusBond n) l).1)
      (Finset.mem_univ (1 : Fin 2)))
private theorem abs_le_of_isDecayingAbout (ℓ : StepParameters) (hr : 0 < ℓ.weightRate) (y : TorusSite n) {sz : ℝ}
    (hsz : 0 ≤ sz) {q : BondBilinear n} (hq : IsDecayingAbout ℓ sz y q) (b b' : TorusBond n) :
    |q b b'| ≤ sz * (Real.exp (-(ℓ.weightRate / 2) * (TorusFields.supDist b.1 y : ℝ)) *
      Real.exp (-(ℓ.weightRate / 2) * (TorusFields.supDist b'.1 y : ℝ))) := by
  refine (hq b b').trans ?_
  set D : ℕ := tripleDiam y b b' with hD
  obtain ⟨h1, h2⟩ := supDist_le_tripleDiam y b b'
  have hw : Real.exp (ℓ.weightRate * (D : ℝ)) ≤ ℓ.weight D := by
    simp only [TorusLumps.StepParameters.weight]
    have hm : (1 : ℝ) ≤ max 1 (((D : ℝ) / ℓ.n₁) ^ 16000) := le_max_left _ _
    nlinarith [Real.exp_pos (ℓ.weightRate * (D : ℝ))]
  have h3 : sz / ℓ.weight D ≤ sz * Real.exp (-(ℓ.weightRate * (D : ℝ))) := by
    rw [Real.exp_neg, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (Real.exp_pos _) hw) hsz
  refine h3.trans (mul_le_mul_of_nonneg_left ?_ hsz)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h4 : (TorusFields.supDist b.1 y : ℝ) ≤ D := by exact_mod_cast h1
  have h5 : (TorusFields.supDist b'.1 y : ℝ) ≤ D := by exact_mod_cast h2
  nlinarith
private theorem doubleSum_le (ℓ : StepParameters) (hr : 0 < ℓ.weightRate) (y : TorusSite n) {sz : ℝ} (hsz : 0 ≤ sz)
    {q : BondBilinear n} (hq : IsDecayingAbout ℓ sz y q) (w : TorusBond n → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (hw0 : ∀ b, 0 ≤ w b)
    (hw : ∀ b, w b ≤ E * ((TorusFields.supDist b.1 y : ℝ) + 1) ^ 2 * Real.exp (ℓ.weightRate / 8 * (TorusFields.supDist b.1 y : ℝ))) :
    ∑ b : TorusBond n, ∑ b' : TorusBond n, w b * |q b b'| * w b' ≤ E ^ 2 * doubleSumConst ℓ.weightRate * sz := by
  set r : ℝ := ℓ.weightRate with hrd
  set A : ℝ := (1 + 16 / r) ^ 2 with hA
  have hW : ∀ b : TorusBond n, w b ≤ E * A * Real.exp (r / 4 * (TorusFields.supDist b.1 y : ℝ)) := by
    intro b
    have hd : (0 : ℝ) ≤ TorusFields.supDist b.1 y := Nat.cast_nonneg _
    have h1 := sq_add_one_le_exp hr hd
    have e : Real.exp (r / 4 * (TorusFields.supDist b.1 y : ℝ)) =
        Real.exp (r / 8 * (TorusFields.supDist b.1 y : ℝ)) * Real.exp (r / 8 * (TorusFields.supDist b.1 y : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    refine (hw b).trans ?_
    rw [e]
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (r / 8 * (TorusFields.supDist b.1 y : ℝ))).le
    have h3 := mul_le_mul_of_nonneg_left h2 hE
    calc _ = E * (((TorusFields.supDist b.1 y : ℝ) + 1) ^ 2 * Real.exp (r / 8 * (TorusFields.supDist b.1 y : ℝ))) := by ring
      _ ≤ _ := h3
      _ = _ := by ring
  set g : TorusBond n → ℝ := fun b => Real.exp (-(r / 4) * (TorusFields.supDist b.1 y : ℝ)) with hg
  have hterm : ∀ b b' : TorusBond n, w b * |q b b'| * w b' ≤ (E * A) ^ 2 * sz * (g b * g b') := by
    intro b b'
    have h1 := abs_le_of_isDecayingAbout ℓ hr y hsz hq b b'
    have hb := hW b
    have hb' := hW b'
    have e1 : Real.exp (r / 4 * (TorusFields.supDist b.1 y : ℝ)) * Real.exp (-(r / 2) * (TorusFields.supDist b.1 y : ℝ)) = g b := by
      simp only [hg]
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (r / 4 * (TorusFields.supDist b'.1 y : ℝ)) * Real.exp (-(r / 2) * (TorusFields.supDist b'.1 y : ℝ)) = g b' := by
      simp only [hg]
      rw [← Real.exp_add]
      congr 1
      ring
    calc w b * |q b b'| * w b'
        ≤ (E * A * Real.exp (r / 4 * (TorusFields.supDist b.1 y : ℝ))) *
            (sz * (Real.exp (-(r / 2) * (TorusFields.supDist b.1 y : ℝ)) * Real.exp (-(r / 2) * (TorusFields.supDist b'.1 y : ℝ)))) *
            (E * A * Real.exp (r / 4 * (TorusFields.supDist b'.1 y : ℝ))) := by
          apply mul_le_mul (mul_le_mul hb h1 (abs_nonneg _) (by positivity)) hb' (hw0 _) (by positivity)
      _ = (E * A) ^ 2 * sz * ((Real.exp (r / 4 * (TorusFields.supDist b.1 y : ℝ)) * Real.exp (-(r / 2) * (TorusFields.supDist b.1 y : ℝ))) *
            (Real.exp (r / 4 * (TorusFields.supDist b'.1 y : ℝ)) * Real.exp (-(r / 2) * (TorusFields.supDist b'.1 y : ℝ)))) := by ring
      _ = _ := by rw [e1, e2]
  have hsum : ∑ b : TorusBond n, g b ≤ 4 * expLatticeSum (r / 4) := sum_bonds_exp_le (by positivity) y Finset.univ
  have hg0 : 0 ≤ ∑ b : TorusBond n, g b := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  calc ∑ b : TorusBond n, ∑ b' : TorusBond n, w b * |q b b'| * w b'
      ≤ ∑ b : TorusBond n, ∑ b' : TorusBond n, (E * A) ^ 2 * sz * (g b * g b') :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => hterm b b'
    _ = (E * A) ^ 2 * sz * (∑ b : TorusBond n, g b) ^ 2 := by
        rw [sq (∑ b : TorusBond n, g b), Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
    _ ≤ (E * A) ^ 2 * sz * (4 * expLatticeSum (r / 4)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0 hsum 2) (by positivity)
    _ = _ := by
        simp only [doubleSumConst, hA]
        ring
private theorem abs_pathSum_le (X : TorusBond n → ℝ) (y : TorusSite n) {V : ℝ} (hX : ∀ b, |X b| ≤ V)
    (ζ : Fin 4 → ℤ) : |pathSum X y ζ| ≤ (∑ a : Fin 4, |(ζ a : ℝ)|) * V := by
  simp only [pathSum]
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  exact abs_primitive_le _ (fun l => hX _) _
private theorem abs_le_of_curlCombination (y : TorusSite n) {f : (TorusBond n → ℝ) → ℝ} {S V : ℝ}
    (h : CurlCombination (distWeight 0 y) f S) (X : TorusBond n → ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ p ∈ orderedPlaquettes n, |WeightedResponses.curl X p| ≤ V) : |f X| ≤ S * V := by
  obtain ⟨a, h1, h2⟩ := h
  rw [h1]
  have e : ∀ p : TorusPlaquette n, |a p| * distWeight 0 y p.1 = |a p| := by
    intro p
    simp [distWeight]
  simp only [e] at h2
  calc _ ≤ ∑ p ∈ orderedPlaquettes n, |a p * WeightedResponses.curl X p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ orderedPlaquettes n, |a p| * V := Finset.sum_le_sum fun p hp => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hV p hp) (abs_nonneg _)
    _ = (∑ p ∈ orderedPlaquettes n, |a p|) * V := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 hV0
private theorem abs_pathGauge_le (X : TorusBond n → ℝ) (y : TorusSite n) {V₁ V₂ m : ℝ} (h1 : 0 ≤ V₁) (h2 : 0 ≤ V₂)
    (hm0 : 0 ≤ m) (hc : ∀ p ∈ orderedPlaquettes n, |WeightedResponses.curl X p| ≤ V₁) (hX : ∀ b, |X b| ≤ m * V₂)
    (hm : m ≤ n) (b : TorusBond n) :
    |pathGauge X y b| ≤ (4 * V₁ + 16 * V₂) * ((TorusFields.supDist b.1 y : ℝ) + 1) ^ 2 := by
  obtain ⟨z, i⟩ := b
  set ζ := centredCoords y z with hζ
  have hz : siteAt y ζ = z := siteAt_centredCoords y z
  have hcube : InCentredCube n ζ := inCentredCube_centredCoords y z
  set d : ℕ := TorusFields.supDist z y with hd
  have hnat : ∀ a, (ζ a).natAbs ≤ d := natAbs_centredCoords_le y z
  by_cases hx : CrossesWall n i ζ
  · have htop := eq_half_of_crossesWall hcube hx
    have hτd : n / 2 ≤ d := by
      have h3 := hnat i
      rw [htop] at h3
      rwa [Int.natAbs_natCast] at h3
    have hτ : ((n / 2 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hτd
    have hn : (n : ℝ) ≤ 2 * (d : ℝ) + 1 := by
      have : n ≤ 2 * d + 1 := by omega
      exact_mod_cast this
    have hV : 0 ≤ m * V₂ := mul_nonneg hm0 h2
    have p1 := abs_pathSum_le X y hX ζ
    have p2 := abs_pathSum_le X y hX (centredCoords y (z + unitStep n i))
    have s1 := sum_abs_coords_le (natAbs_le_half hcube)
    have s2 := sum_abs_coords_le (natAbs_le_half (inCentredCube_centredCoords y (z + unitStep n i)))
    have q1 := mul_le_mul_of_nonneg_right s1 hV
    have q2 := mul_le_mul_of_nonneg_right s2 hV
    have hb := hX (z, i)
    have t : |pathGauge X y (z, i)| ≤
        m * V₂ + 4 * ((n / 2 : ℕ) : ℝ) * (m * V₂) + 4 * ((n / 2 : ℕ) : ℝ) * (m * V₂) := by
      simp only [pathGauge]
      have a1 := abs_le.mp hb
      have a2 := abs_le.mp (p1.trans q1)
      have a3 := abs_le.mp (p2.trans q2)
      rw [abs_le]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
    refine t.trans ?_
    have u1 : (1 + 8 * ((n / 2 : ℕ) : ℝ)) * (m * V₂) ≤ (1 + 8 * (d : ℝ)) * ((2 * (d : ℝ) + 1) * V₂) :=
      mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right (hm.trans hn) h2) hV (by positivity)
    have u2 : (1 + 8 * (d : ℝ)) * (2 * (d : ℝ) + 1) ≤ 16 * ((d : ℝ) + 1) ^ 2 := by nlinarith
    have u3 := mul_le_mul_of_nonneg_right u2 h2
    have u4 : 0 ≤ V₁ * ((d : ℝ) + 1) ^ 2 := by positivity
    nlinarith
  · have h3 := inCentredCube_add hcube hx
    have hr := curlCombination_pathGaugeCoords (c := 0) le_rfl y ζ i d hnat
    have hb := abs_le_of_curlCombination y hr X h1 hc
    rw [← pathGauge_siteAt X y hcube h3, hz] at hb
    refine hb.trans ?_
    simp only [zero_mul, Real.exp_zero, mul_one]
    have s := sum_abs_coords_le hnat
    have s1 := mul_le_mul_of_nonneg_right s h1
    have u : (d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by nlinarith
    have u1 := mul_le_mul_of_nonneg_left u h1
    have u2 : 0 ≤ V₂ * ((d : ℝ) + 1) ^ 2 := by positivity
    nlinarith
private theorem abs_bilinearEval_le_of_gradients (ℓ : StepParameters) (hr : 0 < ℓ.weightRate) (y : TorusSite n)
    {sz : ℝ} (hsz : 0 ≤ sz) {q : BondBilinear n} (hq : IsDecayingAbout ℓ sz y q) (hK : AnnihilatesGradients q)
    (X : TorusBond n → ℝ) {V₁ V₂ m : ℝ} (h1 : 0 ≤ V₁) (h2 : 0 ≤ V₂) (hm0 : 0 ≤ m)
    (hc : ∀ p ∈ orderedPlaquettes n, |WeightedResponses.curl X p| ≤ V₁) (hX : ∀ b, |X b| ≤ m * V₂) (hm : m ≤ n) :
    |bilinearEval q X X| ≤ (4 * V₁ + 16 * V₂) ^ 2 * doubleSumConst ℓ.weightRate * sz := by
  have e : X = fun b => pathGauge X y b + latticeGradient (fun z => pathSum X y (centredCoords y z)) b := by
    funext b
    simp only [pathGauge, latticeGradient]
    ring
  have key : ∀ (B : TorusBond n → ℝ) (ψ : TorusSite n → ℝ),
      bilinearEval q (fun b => B b + latticeGradient ψ b) (fun b => B b + latticeGradient ψ b) =
        bilinearEval q B B := by
    intro B ψ
    rw [bilinearEval_add_left, bilinearEval_add_right, (hK ψ _).1, (hK ψ B).2]
    simp
  have e1 : bilinearEval q X X = bilinearEval q (pathGauge X y) (pathGauge X y) := by
    have h := key (pathGauge X y) (fun z => pathSum X y (centredCoords y z))
    rwa [← e] at h
  rw [e1]
  have hE : 0 ≤ 4 * V₁ + 16 * V₂ := by positivity
  have qs := doubleSum_le ℓ hr y hsz hq (fun b => |pathGauge X y b|) hE (fun _ => abs_nonneg _) (fun b => by
    have h3 := abs_pathGauge_le X y h1 h2 hm0 hc hX hm b
    have h4 : 1 ≤ Real.exp (ℓ.weightRate / 8 * (TorusFields.supDist b.1 y : ℝ)) := Real.one_le_exp (by positivity)
    have h5 : 0 ≤ (4 * V₁ + 16 * V₂) * ((TorusFields.supDist b.1 y : ℝ) + 1) ^ 2 := by positivity
    exact h3.trans (le_mul_of_one_le_right h5 h4))
  refine le_trans ?_ qs
  simp only [bilinearEval]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
  rw [abs_mul, abs_mul]
end DoubleSums
section MomentPointBounds
private theorem clusterRange_sq_le {L N : ℕ} (hL : 0 < L) {x : ℝ} (hx : 2 ≤ x)
    (h : (L : ℝ) ^ (-(N : ℝ) / 4) ≤ x⁻¹) : ((clusterRange x : ℕ) : ℝ) ^ 2 ≤ ((L ^ N : ℕ) : ℝ) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hx0 : 0 < x := by linarith
  have h2 := inv_anti₀ (Real.rpow_pos_of_pos hLp _) h
  rw [inv_inv, ← Real.rpow_neg hLp.le] at h2
  have e0 : -(-(N : ℝ) / 4) = (N : ℝ) / 4 := by ring
  rw [e0] at h2
  have h3 : x ^ 4 ≤ (L : ℝ) ^ N := by
    have h4 := pow_le_pow_left₀ hx0.le h2 4
    refine h4.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast ((L : ℝ) ^ ((N : ℝ) / 4)) 4, ← Real.rpow_mul hLp.le, ← Real.rpow_natCast (L : ℝ) N]
    congr 1
    push_cast
    ring
  have h5 : x ^ ((1 : ℝ) / 100) ≤ x := by
    calc x ^ ((1 : ℝ) / 100) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = x := Real.rpow_one x
  have h6 : ((clusterRange x : ℕ) : ℝ) < x + 1 := by
    have := Nat.ceil_lt_add_one (a := x ^ ((1 : ℝ) / 100)) (Real.rpow_nonneg hx0.le _)
    simp only [clusterRange]
    linarith
  have h7 : (0 : ℝ) ≤ ((clusterRange x : ℕ) : ℝ) := Nat.cast_nonneg _
  push_cast
  refine le_trans ?_ h3
  have h8 : ((clusterRange x : ℕ) : ℝ) ≤ 2 * x := by linarith
  have h9 : ((clusterRange x : ℕ) : ℝ) ^ 2 ≤ (2 * x) ^ 2 := pow_le_pow_left₀ h7 h8 2
  refine h9.trans ?_
  have h10 : (4 : ℝ) ≤ x ^ 2 := by nlinarith
  nlinarith [sq_nonneg x]
private theorem abs_colourEval_cutoff_le {Λ : MomentParameters} (S : MomentPoint Λ) (hr : 0 < Λ.stepParams.weightRate)
    {u n : ℕ} [NeZero n] (y : TorusSite n) {sz : ℝ} (hsz : 0 ≤ sz) {q : BondBilinear n}
    (hq : IsDecayingAbout Λ.stepParams sz y q) (hK : AnnihilatesGradients q) (W : TorusField n) (hm1 : 1 ≤ S.rangeSq)
    (hA : ∀ c : TorusBond n, c.1 ∈ ResponseInTheExpansion.supBall (S.originSite u n) (2 * S.rangeSq) →
      c.1 + unitStep n c.2 ∈ ResponseInTheExpansion.supBall (S.originSite u n) (2 * S.rangeSq) →
      ‖(axialCoords Λ.stepParams W (S.originSite u n) c : Quaternion ℝ)‖ ≤
        4 * ((TorusFields.supDist c.1 (S.originSite u n) : ℝ) + 1) * S.localCurvature u n W)
    (hcurl : ∀ p : WeightedResponses.OrientedPlaquette n,
      curlNorm (S.cutoffColourForm u n W) p.1 ≤ 60 * S.localCurvature u n W)
    (hside : (S.rangeSq : ℝ) ≤ n) :
    |colourEval q (S.cutoffColourForm u n W) (S.cutoffColourForm u n W)| ≤
      3 * 368 ^ 2 * doubleSumConst Λ.stepParams.weightRate * sz * S.localCurvature u n W ^ 2 := by
  set v : ℝ := S.localCurvature u n W with hv
  have hv0 : 0 ≤ v := by
    simp only [hv, MomentPoint.localCurvature, boxCurvature]
    exact Real.iSup_nonneg fun _ => norm_nonneg _
  set o : TorusSite n := S.originSite u n with ho
  have hm0 : (0 : ℝ) ≤ S.rangeSq := Nat.cast_nonneg _
  have hX : ∀ (e : Fin 3) (b : TorusBond n), |S.cutoffColourForm u n W e b| ≤ (S.rangeSq : ℝ) * (8 * v) := by
    intro e b
    simp only [MomentPoint.cutoffColourForm, toColourForm, MomentPoint.cutoffLie, cutoffCoords]
    rw [← ho]
    set cn : ℝ := cutoffProfile o S.rangeSq b.1 with hcn
    set A : BlockAverages.imaginaryQuaternions := axialCoords Λ.stepParams W o b with hAd
    have h1 : |BlockAverages.imaginaryComponent e (cn • A)| ≤
        ‖((cn • A : BlockAverages.imaginaryQuaternions) : Quaternion ℝ)‖ :=
      ResponseInTheExpansion.MirrorKernels.abs_imaginaryComponent_le e _
    have h2 : ‖((cn • A : BlockAverages.imaginaryQuaternions) : Quaternion ℝ)‖ = |cn| * ‖(A : Quaternion ℝ)‖ := by
      rw [Submodule.coe_smul, norm_smul, Real.norm_eq_abs]
    rw [h2] at h1
    refine h1.trans ?_
    have hc0 : 0 ≤ cn := le_max_left _ _
    have hc1 : cn ≤ 1 := max_le zero_le_one (min_le_left _ _)
    by_cases hd : TorusFields.supDist b.1 o + 2 ≤ 2 * S.rangeSq
    · have hdr : ((TorusFields.supDist b.1 o : ℝ) + 2) ≤ 2 * (S.rangeSq : ℝ) := by exact_mod_cast hd
      have c1 : b.1 ∈ ResponseInTheExpansion.supBall o (2 * S.rangeSq) := by
        simp only [ResponseInTheExpansion.supBall, Finset.mem_filter, Finset.mem_univ, true_and]
        linarith
      have c2 : b.1 + unitStep n b.2 ∈ ResponseInTheExpansion.supBall o (2 * S.rangeSq) := by
        simp only [ResponseInTheExpansion.supBall, Finset.mem_filter, Finset.mem_univ, true_and]
        have t1 : TorusFields.supDist (b.1 + unitStep n b.2) o ≤ 1 + TorusFields.supDist b.1 o := by
          refine (supDist_triangle _ b.1 _).trans (Nat.add_le_add_right ?_ _)
          rw [supDist_comm]
          exact supDist_add_unitStep_le _ _
        have t2 : (TorusFields.supDist (b.1 + unitStep n b.2) o : ℝ) ≤ 1 + (TorusFields.supDist b.1 o : ℝ) := by exact_mod_cast t1
        linarith
      have h3 := hA b c1 c2
      have h4 : |cn| ≤ 1 := by rwa [abs_of_nonneg hc0]
      calc |cn| * ‖(A : Quaternion ℝ)‖ ≤ 1 * (4 * ((TorusFields.supDist b.1 o : ℝ) + 1) * v) :=
            mul_le_mul h4 h3 (norm_nonneg _) zero_le_one
        _ ≤ (S.rangeSq : ℝ) * (8 * v) := by nlinarith
    · have hdr : 2 * (S.rangeSq : ℝ) - 1 ≤ (TorusFields.supDist b.1 o : ℝ) := by
        have : 2 * S.rangeSq ≤ TorusFields.supDist b.1 o + 1 := by omega
        have h5 : (2 * (S.rangeSq : ℝ)) ≤ (TorusFields.supDist b.1 o : ℝ) + 1 := by exact_mod_cast this
        linarith
      have hm1' : (1 : ℝ) ≤ S.rangeSq := by exact_mod_cast hm1
      have hz : cn = 0 := by
        have h5 : (2 * (S.rangeSq : ℝ) - 1 - (TorusFields.supDist b.1 o : ℝ)) / ((S.rangeSq : ℝ) - 1) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        simp only [hcn, cutoffProfile]
        exact max_eq_left ((min_le_right _ _).trans h5)
      rw [hz]
      simp only [abs_zero, zero_mul]
      positivity
  have hc : ∀ (e : Fin 3), ∀ p ∈ orderedPlaquettes n,
      |WeightedResponses.curl (S.cutoffColourForm u n W e) p| ≤ 60 * v := by
    intro e p hp
    have hlt : p.2.1 < p.2.2 := (Finset.mem_filter.mp hp).2.1
    refine le_trans ?_ (hcurl ⟨p, hlt⟩)
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun e : Fin 3 => WeightedResponses.curl (S.cutoffColourForm u n W e) p ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ e)
  have hF : ∀ e : Fin 3, |bilinearEval q (S.cutoffColourForm u n W e) (S.cutoffColourForm u n W e)| ≤
      (368 * v) ^ 2 * doubleSumConst Λ.stepParams.weightRate * sz := by
    intro e
    have h1 := abs_bilinearEval_le_of_gradients Λ.stepParams hr y hsz hq hK (S.cutoffColourForm u n W e)
      (V₁ := 60 * v) (V₂ := 8 * v) (m := S.rangeSq) (by positivity) (by positivity) hm0 (hc e) (hX e) hside
    refine h1.trans (le_of_eq ?_)
    ring
  simp only [colourEval]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _e : Fin 3, (368 * v) ^ 2 * doubleSumConst Λ.stepParams.weightRate * sz :=
        Finset.sum_le_sum fun e _ => hF e
    _ = _ := by
      simp
      ring
theorem formsReadCurvature_proof (hCut : goodConfigCutoffStatement) (hWin : scaleWindowStatement) :
    formsReadCurvatureStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hCut a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hWin a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hodd hL Tb hTa hTL hD hCS hOn hrt hCd Kr hKr
  obtain ⟨y₁, G₁⟩ := H₁ L hodd (le_of_max_le_left hL) Tb hTa hTL hD hCS hOn (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hCd) Kr hKr
  obtain ⟨y₂, G₂⟩ := H₂ L hodd (le_of_max_le_right hL) Tb hTa hTL hD hCS hOn (hrt.trans (min_le_right _ _))
    ((le_max_right _ _).trans hCd) Kr hKr
  refine ⟨max y₁ y₂, ?_⟩
  intro y hy hret hrow g hg hgy k _ hk2 hk8 R d hd
  obtain ⟨_, _, X₁, _, _, P₁⟩ := G₁ y (le_of_max_le_left hy) hret hrow g hg hgy k hk2 hk8 R d hd
  obtain ⟨_, _, X₂, _, _, P₂⟩ := G₂ y (le_of_max_le_right hy) hret hrow g hg hgy k hk2 hk8 R d hd
  have hr : 0 < (Tb.stepParameters y).weightRate := by
    have := hD.rt_pos
    show 0 < Tb.rt / 2 ^ 10
    positivity
  obtain ⟨C, hC0, hC1⟩ : ∃ C : ℕ → ℝ, C 0 = 36 ^ 2 * doubleSumConst (Tb.stepParameters y).weightRate ∧
      C 1 = 3 * 368 ^ 2 * doubleSumConst (Tb.stepParameters y).weightRate :=
    ⟨fun i => if i = 0 then 36 ^ 2 * doubleSumConst (Tb.stepParameters y).weightRate
      else 3 * 368 ^ 2 * doubleSumConst (Tb.stepParameters y).weightRate, by simp, by simp⟩
  refine ⟨C, 1, max (max X₁ X₂) (max y 2), one_pos, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro S u hu n _ hn y' sz q hsz hq
  refine ⟨fun hK => ?_, fun hX hu1 hu2 hG _ W Y hGood => ?_⟩
  · have hc0 : 0 ≤ (Tb.stepParameters y).weightRate / 8 := by positivity
    obtain ⟨κ, k1, k2⟩ := exists_curl_kernel hc0 y' hK
    refine ⟨κ, k1, ?_⟩
    have e : ∀ p p' : TorusPlaquette n,
        |κ p p'| * Real.exp ((Tb.stepParameters y).weightRate / 8 * ((TorusFields.supDist p.1 y' : ℝ) + (TorusFields.supDist p'.1 y' : ℝ))) =
          |κ p p'| * (distWeight ((Tb.stepParameters y).weightRate / 8) y' p.1 *
            distWeight ((Tb.stepParameters y).weightRate / 8) y' p'.1) := by
      intro p p'
      simp only [distWeight]
      rw [← Real.exp_add, mul_add]
    refine le_trans (le_of_eq ?_) (k2.trans ?_)
    · exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => e p p'
    · have h1 := doubleSum_le (Tb.stepParameters y) hr y' hsz.le hq
        (pathFormMass ((Tb.stepParameters y).weightRate / 8) y') (E := 36) (by norm_num)
        (fun b => by
          simp only [pathFormMass]
          positivity) (fun b => le_rfl)
      rw [hC0]
      exact h1
  · have hX1 : X₁ ≤ S.scaleCoupling := ((le_max_left _ _).trans (le_max_left _ _)).trans hX
    have hX2 : X₂ ≤ S.scaleCoupling := ((le_max_right _ _).trans (le_max_left _ _)).trans hX
    have hx2 : 2 ≤ S.scaleCoupling := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
    obtain ⟨hA, hcurl, -, -⟩ := P₁ S hX1 u hu1 hu2 n hn W Y hGood
    obtain ⟨w1, -, -, -, -, -, w7⟩ := P₂ S hX2
    have hLpos : 0 < (Tb.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne _)
    have hrange := clusterRange_sq_le hLpos hx2 w1
    have hside : (S.rangeSq : ℝ) ≤ n := by
      have h1 : (Tb.stepParameters y).side ^ S.logIndex ≤ n := by
        rw [hn]
        exact (w7 u hu1 hu2).2
      have h2 : (((Tb.stepParameters y).side ^ S.logIndex : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      have h3 : (S.rangeSq : ℝ) = ((clusterRange S.scaleCoupling : ℕ) : ℝ) ^ 2 := by
        simp only [MomentPoint.rangeSq, MomentPoint.range]
        push_cast
        rfl
      rw [h3]
      exact hrange.trans h2
    have hm1 : 1 ≤ S.rangeSq := by
      have hr1 : 0 < clusterRange S.scaleCoupling := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)
      simp only [MomentPoint.rangeSq, MomentPoint.range]
      exact Nat.one_le_pow _ _ hr1
    have h2 := abs_colourEval_cutoff_le S hr y' hsz.le hq hG W hm1 hA hcurl hside
    rw [hC1]
    exact h2
end MomentPointBounds
end YangMills.Construction.MomentLaw
end
