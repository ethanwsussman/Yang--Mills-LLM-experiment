import YangMills.Construction.Continuum.CoefficientsOfAFunctionOfASystemDecay
import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuplesProof
import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystemProof
import YangMills.Construction.Continuum.FunctionOfASystemSumsItsSeries
import YangMills.Construction.Continuum.PartialSumsOfASystemApproachTheFunction
import YangMills.Construction.Continuum.ScaledDerivativesOfTensorsOfModes
import YangMills.Construction.Continuum.SumOverTheFrequenciesOfASystem
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.ConfigSpace
namespace TruncationApprox
open YangMills.Construction.SmoothMaps YangMills.Construction.TestFunctions YangMills.Construction.ShellPieces
variable {n : ℕ}
theorem foldr_iterate_congr {κ X : Type*} (F : κ → X → X) (l : List κ) (a b : κ → ℕ)
    (hab : ∀ q ∈ l, a q = b q) (h : X) :
    l.foldr (fun q h' => (F q)^[a q] h') h = l.foldr (fun q h' => (F q)^[b q] h') h := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.foldr_cons]
    rw [ih fun q hq => hab q (List.mem_cons_of_mem c hq), hab c List.mem_cons_self]
theorem foldr_iterate_zero {κ X : Type*} (F : κ → X → X) (l : List κ) (a : κ → ℕ)
    (ha : ∀ q ∈ l, a q = 0) (h : X) : l.foldr (fun q h' => (F q)^[a q] h') h = h := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.foldr_cons]
    rw [ih fun q hq => ha q (List.mem_cons_of_mem c hq), ha c List.mem_cons_self]
    rfl
theorem foldr_iterate_peel {κ X : Type*} [DecidableEq κ] (F : κ → X → X) (l : List κ)
    (hl : l.Nodup) (a : κ → ℕ) (h₀ : ∃ p ∈ l, a p ≠ 0) :
    ∃ p ∈ l, a p ≠ 0 ∧ ∀ h : X, l.foldr (fun q h' => (F q)^[a q] h') h =
      F p (l.foldr (fun q h' => (F q)^[Function.update a p (a p - 1) q] h') h) := by
  induction l with
  | nil =>
    obtain ⟨p, hp, -⟩ := h₀
    simp at hp
  | cons b l ih =>
    have hnd := List.nodup_cons.1 hl
    by_cases hb : a b = 0
    · obtain ⟨p, hp, hap⟩ := h₀
      have hpl : p ∈ l := (List.mem_cons.1 hp).resolve_left fun e => hap (e ▸ hb)
      obtain ⟨p', hp', hap', hfold⟩ := ih hnd.2 ⟨p, hpl, hap⟩
      refine ⟨p', List.mem_cons_of_mem b hp', hap', fun h => ?_⟩
      have hne : b ≠ p' := fun e => hnd.1 (e ▸ hp')
      simp only [List.foldr_cons, hb, Function.update_of_ne hne, Function.iterate_zero, id]
      exact hfold h
    · refine ⟨b, List.mem_cons_self, hb, fun h => ?_⟩
      have hsame := foldr_iterate_congr F l (Function.update a b (a b - 1)) a
        (fun q hq => Function.update_of_ne (fun e : q = b => hnd.1 (e ▸ hq)) _ _) h
      simp only [List.foldr_cons, Function.update_self]
      rw [hsame, ← Function.iterate_succ_apply' (F b),
        Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero hb)]
theorem foldr_product {A B X : Type*} (F : A × B → X → X) (l : List A) (l' : List B) (h : X) :
    (l.product l').foldr F h = l.foldr (fun a h' => l'.foldr (fun b h'' => F (a, b) h'') h') h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hc : (a :: l).product l' = l'.map (Prod.mk a) ++ l.product l' := rfl
    rw [hc, List.foldr_append, ih, List.foldr_map]
    rfl
abbrev coordList (n : ℕ) : List (Fin n × Fin 4) := (List.finRange n).product (List.finRange 4)
theorem coordList_nodup : (coordList n).Nodup :=
  (List.nodup_finRange n).product (List.nodup_finRange 4)
theorem iteratedPartial_eq_foldr (α : MultiIndex n) (g : Config n → ℂ) :
    iteratedPartial α g = (coordList n).foldr
      (fun p h => (coordPartial p.1 p.2)^[α p.1 p.2] h) g := by
  rw [foldr_product]
  rfl
abbrev basisVec (p : Fin n × Fin 4) : Config n := Pi.single p.1 (Pi.single p.2 1)
theorem contDiff_iteratedPartial (α : MultiIndex n) {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (iteratedPartial α g) := by apply _root_.YangMills.Construction.ConfigSpace.TensorSupport.contDiff_iteratedPartial <;> assumption
theorem hasSum_iteratedPartial {ι : Type*} (c : ι → ℂ) (g : ι → Config n → ℂ)
    (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hb : ∀ α : MultiIndex n, ∃ u : ι → ℝ, Summable u ∧
      ∀ j x, ‖c j * iteratedPartial α (g j) x‖ ≤ u j)
    (s : ℕ) (α : MultiIndex n) (hs : α.order = s) (x : Config n) :
    HasSum (fun j => c j * iteratedPartial α (g j) x)
      (iteratedPartial α (fun y => ∑' j, c j * g j y) x) := by
  induction s using Nat.strong_induction_on generalizing α x with
  | _ s ih =>
  obtain ⟨u, hu, hbu⟩ := hb α
  have hsummable : Summable fun j => c j * iteratedPartial α (g j) x :=
    Summable.of_norm_bounded hu fun j => hbu j x
  by_cases h₀ : ∃ p ∈ coordList n, α p.1 p.2 ≠ 0
  · obtain ⟨p, -, hap, hfold⟩ := foldr_iterate_peel
      (fun p : Fin n × Fin 4 => coordPartial p.1 p.2)
      (coordList n) coordList_nodup (fun p => α p.1 p.2) h₀
    set a : Fin n × Fin 4 → ℕ := fun p => α p.1 p.2 with ha
    let α' : MultiIndex n := fun i μ => Function.update a p (a p - 1) (i, μ)
    have key : ∀ f : Config n → ℂ, iteratedPartial α f =
        coordPartial p.1 p.2 (iteratedPartial α' f) := by
      intro f
      rw [iteratedPartial_eq_foldr, iteratedPartial_eq_foldr]
      exact hfold f
    have hsize : α'.order < s := by
      have hsz : ∀ β : MultiIndex n, β.order = ∑ q : Fin n × Fin 4, β q.1 q.2 := fun β => by
        rw [Fintype.sum_prod_type]
        rfl
      rw [← hs, hsz, hsz]
      refine Finset.sum_lt_sum (fun q _ => ?_) ⟨p, Finset.mem_univ p, ?_⟩
      · by_cases hq : q = p
        · subst hq
          simp [α', Function.update_self, a]
        · simp [α', Function.update_of_ne (show (q.1, q.2) ≠ p from hq), a]
      · have : α' p.1 p.2 = a p - 1 := Function.update_self _ _ _
        rw [this]
        exact Nat.sub_lt (Nat.pos_of_ne_zero hap) one_pos
    have hα' : ∀ y, HasSum (fun j => c j * iteratedPartial α' (g j) y)
        (iteratedPartial α' (fun y => ∑' j, c j * g j y) y) :=
      fun y => ih _ hsize α' rfl y
    have hG : iteratedPartial α' (fun y => ∑' j, c j * g j y) =
        fun y => ∑' j, c j * iteratedPartial α' (g j) y :=
      funext fun y => (hα' y).tsum_eq.symm
    have hderiv : ∀ j (r : ℝ), HasDerivAt
        (fun r : ℝ => c j * iteratedPartial α' (g j) (x + r • basisVec p))
        (c j * iteratedPartial α (g j) (x + r • basisVec p)) r := by
      intro j r
      have hD := contDiff_iteratedPartial α' (hg j)
      have hF : HasFDerivAt (iteratedPartial α' (g j))
          (fderiv ℝ (iteratedPartial α' (g j)) (x + r • basisVec p)) (x + r • basisVec p) :=
        (hD.differentiable (by simp) _).hasFDerivAt
      have hline : HasDerivAt (fun r : ℝ => x + r • basisVec p) (basisVec p) r := by
        simpa using ((hasDerivAt_id r).smul_const (basisVec p)).const_add x
      have hcomp := (hF.comp_hasDerivAt r hline).const_mul (c j)
      have hval : iteratedPartial α (g j) (x + r • basisVec p) =
          fderiv ℝ (iteratedPartial α' (g j)) (x + r • basisVec p) (basisVec p) := by
        rw [key]
        exact (hD.differentiable (by simp) _).lineDeriv_eq_fderiv
      rw [hval]
      exact hcomp
    have hsum0 : Summable fun j => c j * iteratedPartial α' (g j) (x + (0 : ℝ) • basisVec p) :=
      (hα' _).summable
    have hts := hasDerivAt_tsum (y₀ := (0 : ℝ))
      (g := fun j (r : ℝ) => c j * iteratedPartial α' (g j) (x + r • basisVec p))
      (g' := fun j (r : ℝ) => c j * iteratedPartial α (g j) (x + r • basisVec p))
      hu hderiv (fun j r => hbu j _) hsum0 (0 : ℝ)
    have hl : HasLineDerivAt ℝ (iteratedPartial α' (fun y => ∑' j, c j * g j y))
        (∑' j, c j * iteratedPartial α (g j) (x + (0 : ℝ) • basisVec p)) x (basisVec p) := by
      unfold HasLineDerivAt
      rw [hG]
      exact hts
    have hvalue : iteratedPartial α (fun y => ∑' j, c j * g j y) x =
        ∑' j, c j * iteratedPartial α (g j) x := by
      rw [key]
      have := hl.lineDeriv
      simpa [coordPartial] using this
    rw [hvalue]
    exact hsummable.hasSum
  · have hz : ∀ f : Config n → ℂ, iteratedPartial α f = f := by
      intro f
      rw [iteratedPartial_eq_foldr]
      refine foldr_iterate_zero _ _ (fun p : Fin n × Fin 4 => α p.1 p.2) (fun q hq => ?_) f
      by_contra hne
      exact h₀ ⟨q, hq, hne⟩
    simp only [hz] at hsummable ⊢
    exact hsummable.hasSum
theorem abs_le_coordSupNorm (ξ : Config n) (i : Fin n) (c : Fin 4) : |ξ i c| ≤ coordSupNorm ξ := by apply _root_.YangMills.Construction.ConfigSpace.ModeCost.abs_apply_le_coordSupNorm <;> assumption
theorem coordSupNorm_nonneg (ξ : Config n) : 0 ≤ coordSupNorm ξ :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
theorem finite_freqsWithin (Q : PointSystem n) (t : ℝ) : (Q.freqsWithin t).Finite := by
  have hm := Q.scale_pos
  have hpi := Real.pi_pos
  set N : ℤ := (⌈t * Q.scale / Real.pi⌉₊ : ℤ) with hN
  have hfin : {ζ : Fin n → Fin 4 → ℤ | ∀ i, ζ i ∈ {β : Fin 4 → ℤ | ∀ c, β c ∈ Set.Icc (-N) N}}.Finite :=
    Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => Set.finite_Icc _ _
  refine (hfin.image fun ζ i c => Real.pi / Q.scale * (ζ i c : ℝ)).subset ?_
  rintro ξ ⟨⟨ζ, hζ⟩, ht⟩
  refine ⟨ζ, fun i c => ?_, funext₂ fun i c => (hζ i c).symm⟩
  have h1 : |ξ i c| ≤ t := (abs_le_coordSupNorm ξ i c).trans ht
  rw [hζ, abs_mul, abs_of_pos (div_pos hpi hm)] at h1
  have h2 : |(ζ i c : ℝ)| ≤ t * Q.scale / Real.pi := by
    rw [le_div_iff₀ hpi]
    have : Real.pi / Q.scale * |(ζ i c : ℝ)| * Q.scale = |(ζ i c : ℝ)| * Real.pi := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right h1 hm.le]
  have h3 : |(ζ i c : ℝ)| ≤ (N : ℝ) := by
    refine h2.trans ?_
    rw [hN]
    push_cast
    exact Nat.le_ceil _
  have h4 : |ζ i c| ≤ N := by exact_mod_cast h3
  exact abs_le.1 h4
theorem isClosed_closedBox (a : Fin 4 → ℝ) (s : ℝ) : IsClosed (closedBox a s) := by
  have he : closedBox a s = ⋂ c, {y | |(y - a) c| ≤ s / 2} := by
    ext y
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact ciSup_le_iff (Set.finite_range fun c => |(y - a) c|).bddAbove
  rw [he]
  exact isClosed_iInter fun c => isClosed_le (by fun_prop) continuous_const
theorem isClosed_cylinderSet {S : Fin n → Set (Fin 4 → ℝ)} (hS : ∀ i, IsClosed (S i)) :
    IsClosed (cylinderSet S) := by
  have he : cylinderSet S = ⋂ i, (fun x : Config n => x i) ⁻¹' S i := by
    ext x
    simp [cylinderSet]
  rw [he]
  exact isClosed_iInter fun i => (hS i).preimage (continuous_apply i)
abbrev freqWeight (Q : PointSystem n) (ξ : Config n) : ℝ :=
  (1 + Q.scale * coordSupNorm ξ) ^ (-(4 * (n : ℤ)) - 1)
theorem one_add_scale_mul_pos (Q : PointSystem n) (ξ : Config n) :
    0 < 1 + Q.scale * coordSupNorm ξ := by
  have := mul_nonneg Q.scale_pos.le (coordSupNorm_nonneg ξ)
  linarith
theorem freqWeight_nonneg (Q : PointSystem n) (ξ : Config n) : 0 ≤ freqWeight Q ξ :=
  zpow_nonneg (one_add_scale_mul_pos Q ξ).le _
theorem coeff_mul_deriv_le (Q : PointSystem n) {Φ : Config n → ℂ} (hd : Q.CoeffDecay Φ) (ν : ℕ)
    {K : ℝ} (hK : 0 ≤ K) (ξ : Config n) (hξ : ξ ∈ Q.freqLattice) (α : MultiIndex n) (x : Config n)
    (ht : Q.scale ^ α.order * ‖iteratedPartial α (tensorProd (Q.modeFamily ξ)) x‖ ≤
      K * (1 + Q.scale * coordSupNorm ξ) ^ ν) :
    Q.scale ^ α.order *
        (‖Q.fourierCoeff Φ ξ‖ * ‖iteratedPartial α (tensorProd (Q.modeFamily ξ)) x‖) ≤
      K * (2 ^ (ν + (4 * n + 1)) * scaledSupNorm (ν + (4 * n + 1)) Q.scale Φ) *
        freqWeight Q ξ := by
  have hw := one_add_scale_mul_pos Q ξ
  set w := 1 + Q.scale * coordSupNorm ξ with hwdef
  have hWeq : freqWeight Q ξ = (w ^ (4 * n + 1))⁻¹ := by
    have : -(4 * (n : ℤ)) - 1 = -((4 * n + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [freqWeight, this, zpow_neg, zpow_natCast]
  have hdec := hd (ν + (4 * n + 1)) ξ hξ
  have hc : ‖Q.fourierCoeff Φ ξ‖ * w ^ ν ≤
      2 ^ (ν + (4 * n + 1)) * scaledSupNorm (ν + (4 * n + 1)) Q.scale Φ * freqWeight Q ξ := by
    have hpos : 0 < w ^ (4 * n + 1) := pow_pos hw _
    rw [hWeq, ← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖Q.fourierCoeff Φ ξ‖ * w ^ ν * w ^ (4 * n + 1)
        = w ^ (ν + (4 * n + 1)) * ‖Q.fourierCoeff Φ ξ‖ := by
          rw [pow_add]
          ring
      _ ≤ _ := hdec
  calc Q.scale ^ α.order *
        (‖Q.fourierCoeff Φ ξ‖ * ‖iteratedPartial α (tensorProd (Q.modeFamily ξ)) x‖)
      = ‖Q.fourierCoeff Φ ξ‖ *
          (Q.scale ^ α.order * ‖iteratedPartial α (tensorProd (Q.modeFamily ξ)) x‖) := by ring
    _ ≤ ‖Q.fourierCoeff Φ ξ‖ * (K * w ^ ν) :=
        mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ = K * (‖Q.fourierCoeff Φ ξ‖ * w ^ ν) := by ring
    _ ≤ K * (2 ^ (ν + (4 * n + 1)) * scaledSupNorm (ν + (4 * n + 1)) Q.scale Φ *
          freqWeight Q ξ) :=
        mul_le_mul_of_nonneg_left hc hK
    _ = _ := by ring
theorem hasSum_truncatedSum (Q : PointSystem n) (Φ : Config n → ℂ) (t : ℝ) (x : Config n) :
    HasSum (fun ξ : Q.freqLattice => if coordSupNorm (ξ : Config n) ≤ t then
      Q.fourierCoeff Φ ξ * tensorProd (Q.modeFamily ξ) x else 0) (Q.truncatedSum Φ t x) := by
  classical
  have hU := finite_freqsWithin Q t
  have hmem : ∀ ξ ∈ hU.toFinset, ξ ∈ Q.freqLattice := fun ξ hξ => (hU.mem_toFinset.1 hξ).1
  unfold PointSystem.truncatedSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hU, ← Finset.sum_subtype_of_mem _ hmem]
  have hs := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
    (s := hU.toFinset.subtype (· ∈ Q.freqLattice))
    (f := fun ξ : Q.freqLattice => if coordSupNorm (ξ : Config n) ≤ t then
      Q.fourierCoeff Φ ξ * tensorProd (Q.modeFamily ξ) x else 0) (fun ξ hξ => by
        have hnot : ¬ coordSupNorm (ξ : Config n) ≤ t := fun h => hξ (by
          rw [Finset.mem_subtype]
          exact hU.mem_toFinset.2 ⟨ξ.2, h⟩)
        simp [hnot])
  convert hs using 1
  refine Finset.sum_congr rfl fun ξ hξ => ?_
  have hle : coordSupNorm (ξ : Config n) ≤ t := (hU.mem_toFinset.1 (Finset.mem_subtype.1 hξ)).2
  simp [hle]
theorem tendsto_tsum_tail (Q : PointSystem n) {W : Q.freqLattice → ℝ} (hW : Summable W) :
    Tendsto (fun t : ℝ => ∑' ξ : Q.freqLattice,
      if coordSupNorm (ξ : Config n) ≤ t then 0 else W ξ) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (t : ℝ) (ξ : Q.freqLattice) => if coordSupNorm (ξ : Config n) ≤ t then 0 else W ξ)
    (g := fun _ => (0 : ℝ)) (bound := fun ξ => ‖W ξ‖) hW.norm
    (fun ξ => tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop (coordSupNorm (ξ : Config n))] with t ht
      simp [ht]))
    (Eventually.of_forall fun t ξ => by
      split_ifs
      · simp
      · exact le_rfl)
  simpa using h
end TruncationApprox
open TruncationApprox YangMills.Construction.SmoothMaps YangMills.Construction.TestFunctions
  YangMills.Construction.ShellPieces in
theorem truncationsApproachFunction_holds
    (decay : SystemCoeffsDecay)
    (modes : ModesAreLocalCharacters)
    (expansion : SystemFunctionHasExpansion)
    (tensors : ScaledModeTensorDerivBound)
    (frequencySum : FrequencySum.FrequencySumBound) :
    TruncationsApproachFunction := by
  intro n hn Q Φ hΦ
  have hmodes := modes n hn Q
  have hdec := decay n hn Q Φ hΦ
  have hexp := expansion n hn Q Φ hΦ
  have hm := Q.scale_pos
  unfold PointSystem.TruncationsConverge
  refine ⟨fun t _ => ⟨finite_freqsWithin Q t, ?_⟩, fun ν => ?_⟩
  · unfold tsupport
    refine closure_minimal ?_ (isClosed_cylinderSet fun i => isClosed_closedBox _ _)
    intro x hx
    by_contra hnot
    obtain ⟨i, hi⟩ : ∃ i, x i ∉ Q.outerBox i := by simpa [cylinderSet] using hnot
    apply hx
    have hz : (fun ξ : Q.freqLattice => if coordSupNorm (ξ : Config n) ≤ t then
        Q.fourierCoeff Φ ξ * tensorProd (Q.modeFamily ξ) x else 0) = fun _ => 0 := by
      funext ξ
      have hzero : tensorProd (Q.modeFamily ξ) x = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i)
          (image_eq_zero_of_notMem_tsupport fun h => hi ((hmodes i ξ ξ.2).2.1 h))
      simp [hzero]
    have hs := hasSum_truncatedSum Q Φ t x
    rw [hz] at hs
    exact hs.unique hasSum_zero
  · obtain ⟨K, hK, hT⟩ := tensors n hn Q ν
    have hW0 : Summable fun ξ : Q.freqLattice => freqWeight Q ξ :=
      ((frequencySum n hn Q 1 (fun ξ => freqWeight Q ξ) fun ξ => by
        rw [Real.norm_of_nonneg (freqWeight_nonneg Q ξ), one_mul]).1).of_norm
    set C : ℝ := K * (2 ^ (ν + (4 * n + 1)) * scaledSupNorm (ν + (4 * n + 1)) Q.scale Φ) with hC
    have hWC : Summable fun ξ : Q.freqLattice => C * freqWeight Q ξ := hW0.mul_left C
    let g : Q.freqLattice → Config n → ℂ := fun ξ => tensorProd (Q.modeFamily ξ)
    let c : ℝ → Q.freqLattice → ℂ := fun t ξ =>
      if coordSupNorm (ξ : Config n) ≤ t then 0 else Q.fourierCoeff Φ ξ
    have hsmooth : ∀ ξ, ContDiff ℝ ∞ (g ξ) := fun ξ => (hT ξ ξ.2).1
    have hrem : ∀ t, Φ - Q.truncatedSum Φ t = fun y => ∑' ξ, c t ξ * g ξ y := by
      intro t
      funext y
      have h1 : HasSum (fun ξ : Q.freqLattice =>
          Q.fourierCoeff Φ ξ * tensorProd (Q.modeFamily ξ) y) (Φ y) := by
        have h := (hexp y).1.of_norm.hasSum
        rw [← (hexp y).2] at h
        exact h
      have h2 := h1.sub (hasSum_truncatedSum Q Φ t y)
      rw [Pi.sub_apply, ← h2.tsum_eq]
      refine tsum_congr fun ξ => ?_
      by_cases h : coordSupNorm (ξ : Config n) ≤ t <;> simp [c, g, h]
    have hb : ∀ (t : ℝ) (α : MultiIndex n), ∃ u : Q.freqLattice → ℝ, Summable u ∧
        ∀ ξ x, ‖c t ξ * iteratedPartial α (g ξ) x‖ ≤ u ξ := by
      intro t α
      obtain ⟨K', hK', hT'⟩ := tensors n hn Q α.order
      refine ⟨fun ξ => (Q.scale ^ α.order)⁻¹ * (K' * (2 ^ (α.order + (4 * n + 1)) *
        scaledSupNorm (α.order + (4 * n + 1)) Q.scale Φ) * freqWeight Q ξ),
        (hW0.mul_left _).mul_left _, fun ξ x => ?_⟩
      have hb1 := coeff_mul_deriv_le Q hdec α.order hK' ξ ξ.2 α x ((hT' ξ ξ.2).2 α le_rfl x)
      have hpow : 0 < Q.scale ^ α.order := pow_pos hm _
      have hc : ‖c t ξ‖ ≤ ‖Q.fourierCoeff Φ ξ‖ := by
        simp only [c]
        split_ifs <;> simp
      rw [norm_mul, le_inv_mul_iff₀ hpow]
      exact (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hpow.le).trans hb1
    have hsum : ∀ (t : ℝ) (α : MultiIndex n) (x : Config n),
        HasSum (fun ξ => c t ξ * iteratedPartial α (g ξ) x)
          (iteratedPartial α (Φ - Q.truncatedSum Φ t) x) := fun t α x => by
      rw [hrem t]
      exact hasSum_iteratedPartial (c t) g hsmooth (hb t) _ α rfl x
    have hnorm : ∀ t : ℝ, scaledSupNorm ν Q.scale (Φ - Q.truncatedSum Φ t) ≤
        ∑' ξ : Q.freqLattice, if coordSupNorm (ξ : Config n) ≤ t then 0 else C * freqWeight Q ξ := by
      intro t
      have hsW : Summable fun ξ : Q.freqLattice =>
          if coordSupNorm (ξ : Config n) ≤ t then 0 else C * freqWeight Q ξ :=
        Summable.of_norm_bounded hWC.norm fun ξ => by
          split_ifs
          · rw [norm_zero]
            exact norm_nonneg _
          · exact le_rfl
      have : Nonempty {α : MultiIndex n // α.order ≤ ν} := ⟨⟨0, by simp [MultiIndex.order]⟩⟩
      refine ciSup_le fun α => ?_
      have hpow : 0 < Q.scale ^ α.1.order := pow_pos hm _
      unfold uniformNorm
      rw [Real.mul_iSup_of_nonneg hpow.le]
      refine ciSup_le fun x => ?_
      have hbound := tsum_of_norm_bounded (hsW.hasSum.mul_left (Q.scale ^ α.1.order)⁻¹)
        (f := fun ξ => c t ξ * iteratedPartial α.1 (g ξ) x) fun ξ => by
          by_cases h : coordSupNorm (ξ : Config n) ≤ t
          · simp [c, h]
          · simp only [c, h, if_false]
            rw [norm_mul, le_inv_mul_iff₀ hpow]
            exact coeff_mul_deriv_le Q hdec ν hK ξ ξ.2 α.1 x
              (((hT ξ ξ.2).2 α.1 α.2 x).trans' le_rfl)
      rw [(hsum t α.1 x).tsum_eq, le_inv_mul_iff₀ hpow] at hbound
      exact hbound
    refine squeeze_zero (fun t => ?_) hnorm (tendsto_tsum_tail Q hWC)
    exact Real.iSup_nonneg fun α =>
      mul_nonneg (pow_nonneg hm.le _) (Real.iSup_nonneg fun x => norm_nonneg _)
end YangMills.Construction.ConfigSpace
