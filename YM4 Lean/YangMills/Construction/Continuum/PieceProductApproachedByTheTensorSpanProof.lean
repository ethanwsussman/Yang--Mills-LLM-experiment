import YangMills.Construction.ConfigSpace.IteratedPartialRules
import YangMills.Construction.Continuum.CoefficientsOfAFunctionOfASystemDecayProof
import YangMills.Construction.Continuum.ModesAreCutoffsTimesCharacters
import YangMills.Construction.Continuum.OneClassOfTuplesAndOneNotionOfMultilinearityProof
import YangMills.Construction.Continuum.PartialSumsOfASystemApproachTheFunction
import YangMills.Construction.Continuum.PieceProductApproachedByTheTensorSpan
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ContDiff ENNReal Topology
noncomputable section
namespace YangMills.Construction.ConfigSpace.PieceTensorApprox
open PieceProducts ShellPieces SmoothMaps TestFunctions
variable {n : ℕ}
def reImPart (b : Bool) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (if b then Complex.imCLM else Complex.reCLM)
def partComponent (b : Bool) (g : (Fin 4 → ℝ) → ℂ) : (Fin 4 → ℝ) → ℂ := fun y => reImPart b (g y)
def partWeight (b : Bool) : ℂ := if b then Complex.I else 1
theorem eq_sum_partWeight_mul (g : (Fin 4 → ℝ) → ℂ) (y : Fin 4 → ℝ) :
    g y = ∑ b : Bool, partWeight b * partComponent b g y := by
  simp only [Fintype.sum_bool, partWeight, partComponent, reImPart]
  simp [mul_comm Complex.I, Complex.re_add_im, add_comm]
theorem tensorProd_eq_sum_parts (g : FnTuple n) :
    tensorProd g = ∑ e : Fin n → Bool,
      (∏ i, partWeight (e i)) • tensorProd (fun i => partComponent (e i) (g i)) := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tensorProd]
  rw [Finset.prod_congr rfl fun i _ => eq_sum_partWeight_mul (g i) (x i), Finset.prod_univ_sum,
    Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun e _ => Finset.prod_mul_distrib
theorem parts_mem_smoothRealTupleSet {g : FnTuple n}
    (hs : ∀ i, g i ∈ smoothCompactSet (Fin 4 → ℝ))
    (hd : DisjointSupports g) (e : Fin n → Bool) :
    (fun i => partComponent (e i) (g i)) ∈ smoothRealTupleSet n := by
  have hsm : ∀ i, ContDiff ℝ ∞ (partComponent (e i) (g i)) :=
    fun i => (reImPart (e i)).contDiff.comp (hs i).1
  have hsup : ∀ i, tsupport (partComponent (e i) (g i)) ⊆ tsupport (g i) := fun i =>
    closure_mono fun y hy hy0 => hy (by simp [partComponent, hy0])
  refine ⟨⟨fun i => ⟨fun y => ?_, (hsm i).of_le (by simp), ?_, subset_univ _⟩,
    fun i i' h => (hd i i' h).mono (hsup i) (hsup i')⟩, hsm⟩
  · simp [partComponent, reImPart]
  · exact IsCompact.of_isClosed_subset (hs i).2 (isClosed_tsupport _) (hsup i)
theorem tensorProd_mem_span_real {g : FnTuple n}
    (hs : ∀ i, g i ∈ smoothCompactSet (Fin 4 → ℝ))
    (hd : DisjointSupports g) :
    tensorProd g ∈ Submodule.span ℂ (tensorProd '' smoothRealTupleSet n) := by
  have h := tensorProd_eq_sum_parts g
  rw [h]
  exact Submodule.sum_mem _ fun e _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, parts_mem_smoothRealTupleSet hs hd e, rfl⟩)
theorem contDiff_tensorProd {g : FnTuple n} (hg : ∀ i, ContDiff ℝ ∞ (g i)) :
    ContDiff ℝ ∞ (tensorProd g) :=
  contDiff_prod fun i _ => (hg i).comp (contDiff_apply ℝ _ i)
theorem disjoint_of_setDistR4_pos {A B : Set (Fin 4 → ℝ)} (h : 0 < setDistR4 A B) :
    Disjoint A B := by apply _root_.YangMills.Construction.TestSpaces.UnifiedSeparatedTuples.disjoint_of_setDistR4_pos <;> assumption
theorem modeFamily_disjointSupports (Q : PointSystem n) (hQ : Q.IsSeparated)
    (hm : Q.ModesLocalCharacters) {ξ : Config n} (hξ : ξ ∈ Q.freqLattice) :
    DisjointSupports (Q.modeFamily ξ) := by
  intro i i' h
  have hpos : 0 < setDistR4 (Q.outerBox i) (Q.outerBox i') :=
    lt_of_lt_of_le hQ (iInf_le_of_le i (iInf_le_of_le i' (iInf_le_of_le h le_rfl)))
  exact (disjoint_of_setDistR4_pos hpos).mono (hm i ξ hξ).2.1 (hm i' ξ hξ).2.1
theorem truncatedSum_eq_finset_sum (Q : PointSystem n) (Φ : Config n → ℂ) {t : ℝ}
    (hfin : (Q.freqsWithin t).Finite) :
    Q.truncatedSum Φ t =
      ∑ ξ ∈ hfin.toFinset, Q.fourierCoeff Φ ξ • tensorProd (Q.modeFamily ξ) := by
  funext x
  simp only [PointSystem.truncatedSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact finsum_mem_eq_finite_toFinset_sum _ hfin
theorem mem_closedBox_iff (z a : Fin 4 → ℝ) (s : ℝ) :
    z ∈ closedBox a s ↔ ∀ c, |z c - a c| ≤ s / 2 := by apply _root_.YangMills.Construction.ConfigSpace.FourierDecay.mem_closedBox_iff <;> assumption
def enclosingBox (Q : PointSystem n) : Set (Config n) :=
  Set.pi univ fun i => Set.pi univ fun c => Icc (Q.base i c - Q.scale) (Q.base i c + Q.scale)
theorem isCompact_enclosingBox (Q : PointSystem n) : IsCompact (enclosingBox Q) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
theorem cylinderSet_outerBox_subset (Q : PointSystem n) :
    cylinderSet Q.outerBox ⊆ enclosingBox Q := by
  intro x hx i _ c _
  have h := abs_le.1 ((mem_closedBox_iff _ _ _).1 (hx i) c)
  have e : 2 * Q.scale / 2 = Q.scale := by ring
  rw [e] at h
  constructor <;> linarith [h.1, h.2]
theorem cylinderSet_midBox_subset (Q : PointSystem n) :
    cylinderSet Q.midBox ⊆ cylinderSet Q.outerBox := by apply _root_.YangMills.Construction.ConfigSpace.FourierDecay.midBox_cylinder_subset <;> assumption
theorem entry_le_order (α : MultiIndex n) (i : Fin n) (c : Fin 4) : α i c ≤ α.order :=
  (Finset.single_le_sum (f := fun μ => α i μ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)).trans
    (Finset.single_le_sum (f := fun i => ∑ μ, α i μ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
instance finite_multiIndex_order_le (l : ℕ) : Finite {α : MultiIndex n // α.order ≤ l} :=
  Finite.of_injective
    (fun α => fun i c => (⟨α.1 i c, Nat.lt_succ_of_le ((entry_le_order α.1 i c).trans α.2)⟩ :
      Fin (l + 1)))
    (fun _ _ h => Subtype.ext (funext fun i => funext fun c =>
      congrArg Fin.val (congrFun (congrFun h i) c)))
theorem decaySeminorm_le_scaledSupNorm (hRules : IteratedPartialRules)
    (Q : PointSystem n) {Ψ : Config n → ℂ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hzero : ∀ x, x ∉ enclosingBox Q → Ψ =ᶠ[𝓝 x] 0) {R : ℝ}
    (hR : ∀ x ∈ enclosingBox Q, 1 + euclidNorm x ≤ R) (k l : ℕ) :
    decaySeminorm k l Ψ ≤
      ENNReal.ofReal (R ^ k * Q.scale⁻¹ ^ l * scaledSupNorm l Q.scale Ψ) := by
  obtain ⟨h1, -, -, h4, h5, -⟩ := hRules n
  have hu := Q.scale_pos
  have hu1 : 1 ≤ Q.scale⁻¹ := (one_le_inv₀ hu).2 (by linarith [Q.scale_le_half])
  have hvanish : ∀ (α : MultiIndex n) (x : Config n), x ∉ enclosingBox Q →
      iteratedPartial α Ψ x = 0 := by
    intro α x hx
    have h0 : iteratedPartial α (0 : Config n → ℂ) = 0 := by
      have := h4 α 0 0 contDiff_const
      simpa using this
    rw [h5 α Ψ 0 x (hzero x hx), h0]
    rfl
  have hbdd : ∀ α : MultiIndex n, BddAbove (range fun x => ‖iteratedPartial α Ψ x‖) := by
    intro α
    obtain ⟨C, hC⟩ := (isCompact_enclosingBox Q).exists_bound_of_continuousOn
      (h1 α Ψ hΨ).continuous.continuousOn
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ enclosingBox Q
    · exact (hC x hx).trans (le_max_left _ _)
    · simp [hvanish α x hx]
  unfold decaySeminorm
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun x => ?_
  by_cases hx : x ∈ enclosingBox Q
  · refine ENNReal.ofReal_le_ofReal ?_
    have hsup : ‖iteratedPartial α Ψ x‖ ≤ uniformNorm (iteratedPartial α Ψ) :=
      le_ciSup (hbdd α) x
    have hS : Q.scale ^ α.order * uniformNorm (iteratedPartial α Ψ) ≤
        scaledSupNorm l Q.scale Ψ :=
      le_ciSup (f := fun β : {β : MultiIndex n // β.order ≤ l} =>
        Q.scale ^ β.1.order * uniformNorm (iteratedPartial β.1 Ψ))
        (Set.finite_range _).bddAbove ⟨α, hα⟩
    have hup : 0 < Q.scale ^ α.order := pow_pos hu _
    have hn0 : 0 ≤ ‖iteratedPartial α Ψ x‖ := norm_nonneg _
    have hS0 : 0 ≤ scaledSupNorm l Q.scale Ψ :=
      le_trans (mul_nonneg hup.le (hn0.trans hsup)) hS
    have hnorm : ‖iteratedPartial α Ψ x‖ ≤ Q.scale⁻¹ ^ l * scaledSupNorm l Q.scale Ψ := by
      have e1 : uniformNorm (iteratedPartial α Ψ) ≤
          Q.scale⁻¹ ^ α.order * scaledSupNorm l Q.scale Ψ := by
        rw [inv_pow, inv_mul_eq_div, le_div_iff₀ hup, mul_comm]
        exact hS
      exact hsup.trans (e1.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hu1 hα) hS0))
    have hw0 : 0 ≤ 1 + euclidNorm x := by
      have : 0 ≤ euclidNorm x := Real.sqrt_nonneg _
      linarith
    have hw : (1 + euclidNorm x) ^ k ≤ R ^ k := pow_le_pow_left₀ hw0 (hR x hx) k
    rw [mul_assoc]
    exact mul_le_mul hw hnorm hn0 (hw0.trans (hR x hx) |> pow_nonneg <| k)
  · simp [hvanish α x hx]
theorem pieceMul_approx_by_tensorSpan
    (hFlat : PieceProducts.ProductBounds)
    (hModes : ModesAreLocalCharacters)
    (hSums : TruncationsApproachFunction)
    (hRules : IteratedPartialRules) :
    pieceMul_mem_closure_tensorSpan := by
  intro n hn j z hp f hf k l ε hε
  have hn1 : 1 ≤ n := by omega
  obtain ⟨⟨hsep, -, -, -, -, hprod⟩, -⟩ := hFlat n hn j z hp
  obtain ⟨hΦs, -, hΦc⟩ := hprod f hf.1.1
  generalize hQ : pieceBoxSystem ⟨(j, z), hp⟩ = Q at hsep hΦc
  generalize hΦ : pieceMul j z f = Φ at hΦs hΦc ⊢
  obtain ⟨hpt, hlim⟩ := hSums n hn1 Q Φ hΦc
  have hm := hModes n hn1 Q
  have hcont : Continuous (euclidNorm : Config n → ℝ) := by
    unfold euclidNorm
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_enclosingBox Q).exists_bound_of_continuousOn hcont.continuousOn
  have hR : ∀ x ∈ enclosingBox Q, 1 + euclidNorm x ≤ 1 + C := fun x hx => by
    have := (le_abs_self _).trans (hC x hx)
    linarith
  have hlim' := ((hlim l).const_mul ((1 + C) ^ k * Q.scale⁻¹ ^ l))
  rw [mul_zero] at hlim'
  obtain ⟨t, ht, ht0⟩ := ((hlim'.eventually_lt_const hε).and (eventually_gt_atTop 0)).exists
  obtain ⟨hfin, hts⟩ := hpt t ht0
  have hsum := truncatedSum_eq_finset_sum Q Φ hfin
  refine ⟨Q.truncatedSum Φ t, ?_, ?_⟩
  · rw [hsum]
    refine Submodule.sum_mem _ fun ξ hξ => Submodule.smul_mem _ _ ?_
    have hξ' : ξ ∈ Q.freqLattice := (hfin.mem_toFinset.1 hξ).1
    exact tensorProd_mem_span_real (fun i => (hm i ξ hξ').1)
      (modeFamily_disjointSupports Q hsep hm hξ')
  · have hsmooth : ContDiff ℝ ∞ (Q.truncatedSum Φ t) := by
      have e : (∑ ξ ∈ hfin.toFinset, Q.fourierCoeff Φ ξ • tensorProd (Q.modeFamily ξ)) =
          fun x => ∑ ξ ∈ hfin.toFinset, Q.fourierCoeff Φ ξ • tensorProd (Q.modeFamily ξ) x := by
        funext x
        simp only [Finset.sum_apply, Pi.smul_apply]
      rw [hsum, e]
      refine ContDiff.sum fun ξ hξ =>
        (contDiff_tensorProd fun i => ?_).const_smul (Q.fourierCoeff Φ ξ)
      exact (hm i ξ (hfin.mem_toFinset.1 hξ).1).1.1
    have hzero : ∀ x, x ∉ enclosingBox Q → (Φ - Q.truncatedSum Φ t) =ᶠ[𝓝 x] 0 := by
      intro x hx
      have hx' : x ∉ cylinderSet Q.outerBox := fun h => hx (cylinderSet_outerBox_subset Q h)
      have e₁ : Φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h =>
        hx' (cylinderSet_midBox_subset Q (hΦc.2 h))
      have e₂ : Q.truncatedSum Φ t =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h =>
        hx' (hts h)
      filter_upwards [e₁, e₂] with y a b
      simp [a, b]
    exact lt_of_le_of_lt
      (decaySeminorm_le_scaledSupNorm hRules Q (hΦs.sub hsmooth) hzero hR k l)
      ((ENNReal.ofReal_lt_ofReal_iff hε).2 ht)
end YangMills.Construction.ConfigSpace.PieceTensorApprox
end
