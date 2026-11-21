import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClassProof
import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelow
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheRest
import YangMills.Construction.RunningCouplingSlope.EnergyOfTheCurveHasAFloorProof
import YangMills.Construction.RunningCouplingSlope.EnergyOverTheCurveHasJetsProof
import YangMills.Construction.RunningCouplingSlope.GapAboveGivenFrames
import YangMills.Construction.RunningCouplingSlope.HaarAboveGivenFrames
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.RunningCouplingSlope.ExponentOfAStepAlongACurve
import Mathlib
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAboveTheFrames
set_option autoImplicit false

noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.TorusFields YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings
def ExponentRemainderJetBounds : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ k : ℕ, ∃ C q : ℝ, 0 < C ∧ 0 ≤ q ∧
    ∀ (y : ℝ) (R : StepSetup), T.floorMin ≤ y → R.OnParameters T y →
      ∀ (n : ℕ) [NeZero n] (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), T.n₀ ≤ n → AreUnitVectors X →
        ∀ η : StepVariable (finiteCells (torusFrame R.params.side R.depth n)), (∀ b, ‖η b‖ ≤ T.ballRadius) →
          ContDiffAt ℝ 3 (exponentRemainderAlongCurve R n c X) (0, η) ∧
          ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
            ‖iteratedFDeriv ℝ j (exponentRemainderAlongCurve R n c X) (0, η)‖ ≤ C * (n : ℝ) ^ q
end YangMills.Construction.RunningCouplingSlope
end

noncomputable section
open scoped Topology Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields RenormalizationStepParameters StepSettings Interpolation IteratedDerivative
  Estimates ResponseInTheExpansion.RemainderCalculus WeightedResponses ReferenceDensity StepCosts TorusChain
namespace RunningCouplingSlope
namespace ExponentRemainderJets
section Entries
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem opNorm_le_of_basis_coeffs {I : Type} [Fintype I] [DecidableEq I] {p : ℕ}
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ) (e : I → E) (co : I → E → ℝ)
    (hco : ∀ i x, |co i x| ≤ ‖x‖) (hrep : ∀ x, x = ∑ i, co i x • e i) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ β : Fin p → I, |D fun i => e (β i)| ≤ M) :
    ‖D‖ ≤ (Fintype.card I : ℝ) ^ p * M := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun x => ?_
  have e1 : D x = ∑ β : Fin p → I, (∏ i, co (β i) (x i)) * D fun i => e (β i) := by
    have e2 : x = fun i => ∑ j, co j (x i) • e j := funext fun i => hrep (x i)
    have e3 := D.toMultilinearMap.map_sum (fun (i : Fin p) (j : I) => co j (x i) • e j)
    have e4 : D x = D.toMultilinearMap fun i => ∑ j, co j (x i) • e j := by
      conv_lhs => rw [e2]
      rfl
    rw [e4, e3]
    refine Finset.sum_congr rfl fun β _ => ?_
    have := D.toMultilinearMap.map_smul_univ (fun i => co (β i) (x i)) (fun i => e (β i))
    simpa [smul_eq_mul] using this
  rw [e1, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have e4 : ∀ β : Fin p → I, |(∏ i, co (β i) (x i)) * D fun i => e (β i)| ≤ (∏ i, ‖x i‖) * M := fun β => by
    rw [abs_mul, Finset.abs_prod]
    exact mul_le_mul (Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => hco _ _) (h β) (abs_nonneg _)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  refine (Finset.sum_le_sum fun β _ => e4 β).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
private theorem exists_sorted_slots {α β : Type} {p : ℕ} (f : Fin p → α ⊕ β) :
    ∃ (l j : ℕ) (g : Fin l → α) (h : Fin j → β) (σ : Fin (l + j) ≃ Fin p),
      ∀ i : Fin (l + j), f (σ i) = Fin.addCases (motive := fun _ => α ⊕ β)
        (fun x => Sum.inl (g x)) (fun x => Sum.inr (h x)) i := by
  classical
  have hA : ∀ a : {i : Fin p // (f i).isLeft = true}, ∃ v, f a.1 = Sum.inl v := fun a =>
    Sum.isLeft_iff.1 a.2
  have hB : ∀ a : {i : Fin p // ¬ (f i).isLeft = true}, ∃ v, f a.1 = Sum.inr v := fun a =>
    Sum.isRight_iff.1 (by simpa using a.2)
  choose gA hgA using hA
  choose gB hgB using hB
  let eA := Fintype.equivFin {i : Fin p // (f i).isLeft = true}
  let eB := Fintype.equivFin {i : Fin p // ¬ (f i).isLeft = true}
  refine ⟨_, _, fun x => gA (eA.symm x), fun x => gB (eB.symm x),
    (finSumFinEquiv.symm.trans (Equiv.sumCongr eA.symm eB.symm)).trans (Equiv.sumCompl _), fun i => ?_⟩
  refine Fin.addCases (fun x => ?_) (fun x => ?_) i
  · simp [hgA]
  · simp [hgB]
private theorem iteratedFDeriv_comp_clm_of_contDiffAt {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ} {f : E → H} (A : G →L[ℝ] E) {x : G}
    (hf : ContDiffAt ℝ n f (A x)) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv ℝ i (f ∘ A) x =
      (iteratedFDeriv ℝ i f (A x)).compContinuousLinearMap fun _ => A := by
  obtain ⟨u, hu, hc⟩ := hf.contDiffOn (m := n) le_rfl (by simp)
  obtain ⟨U, hUu, hUo, hxU⟩ := mem_nhds_iff.1 hu
  have hcU : ContDiffOn ℝ n f U := hc.mono hUu
  have ht := (hcU.ftaylorSeriesWithin hUo.uniqueDiffOn).comp_continuousAffineMap A.toContinuousAffineMap
  have hopen : IsOpen (A ⁻¹' U) := hUo.preimage A.continuous
  have h1 := ht.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hi) hopen.uniqueDiffOn
    (show x ∈ A ⁻¹' U from hxU)
  have h2 : iteratedFDerivWithin ℝ i (f ∘ A) (A ⁻¹' U) x = iteratedFDeriv ℝ i (f ∘ A) x :=
    iteratedFDerivWithin_of_isOpen i hopen (show x ∈ A ⁻¹' U from hxU)
  have h3 : iteratedFDerivWithin ℝ i f U (A x) = iteratedFDeriv ℝ i f (A x) :=
    iteratedFDerivWithin_of_isOpen i hUo hxU
  rw [← h2, ← h3]
  exact h1.symm
private theorem iteratedFDeriv_affine_zero {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ}
    {f : E → ℝ} (p₀ : E) (A : G →L[ℝ] E) (hf : ContDiffAt ℝ n f p₀) (v : Fin n → G) :
    iteratedFDeriv ℝ n (fun τ => f (p₀ + A τ)) 0 v = iteratedFDeriv ℝ n f p₀ fun i => A (v i) := by
  have hf' : ContDiffAt ℝ n (fun z => f (p₀ + z)) (A 0) := by
    have e : (fun z => f (p₀ + z)) = f ∘ fun z => p₀ + z := rfl
    rw [e]
    refine ContDiffAt.comp _ ?_ (contDiff_const.add contDiff_id).contDiffAt
    simpa using hf
  have h := iteratedFDeriv_comp_clm_of_contDiffAt (f := fun z => f (p₀ + z)) A hf' (le_refl n)
  have e : (fun τ => f (p₀ + A τ)) = (fun z => f (p₀ + z)) ∘ A := rfl
  rw [e, h, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero,
    iteratedFDeriv_comp_add_left]
  simp
end Entries
section Pull
private def pullbackMap {q k : ℕ} (ι : Fin q → Fin k) : (Fin q → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i => ∑ r, if ι r = i then
    (ContinuousLinearMap.proj r : (Fin q → ℝ) →L[ℝ] ℝ) else 0
private theorem pullbackMap_apply {q k : ℕ} (ι : Fin q → Fin k) (τ : Fin q → ℝ) (i : Fin k) :
    pullbackMap ι τ i = ∑ r, if ι r = i then τ r else 0 := by
  simp only [pullbackMap, ContinuousLinearMap.coe_pi', _root_.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp
private theorem bondSpread_pullback {F : BlockFrame} {J q k : ℕ} (c : Fin k → F.Site J × Fin 4)
    (X : Fin k → imaginaryQuaternions) (ι : Fin q → Fin k) (τ : Fin q → ℝ) :
    ColdStepAtMirrorFrames.bondSpread (fun r => c (ι r)) (fun r => X (ι r)) τ = ColdStepAtMirrorFrames.bondSpread c X (pullbackMap ι τ) := by
  funext y i
  simp only [ColdStepAtMirrorFrames.bondSpread, pullbackMap_apply]
  calc _ = ∑ r, ∑ n, if ι r = n then (if c n = (y, i) then τ r • X n else 0) else 0 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ n, ∑ r, if ι r = n then (if c n = (y, i) then τ r • X n else 0) else 0 := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases h : c n = (y, i)
        · simp only [h, if_true]
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun r _ => ?_
          split_ifs <;> simp
        · simp [h]
end Pull
section Coordinates
variable {F : BlockFrame} {k : ℕ}
private abbrev CoordIndex (F : BlockFrame) (k : ℕ) : Type := (↥(chordBonds (finiteCells F)) × Fin 3) ⊕ Fin k
open Classical in
private def basisVector : CoordIndex F k → (Fin k → ℝ) × StepVariable (finiteCells F)
  | Sum.inl d => (0, Pi.single d.1 (EuclideanSpace.single d.2 1))
  | Sum.inr i => (Pi.single i 1, 0)
private def coordFun : CoordIndex F k → (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ
  | Sum.inl d, q => q.2 d.1 d.2
  | Sum.inr i, q => q.1 i
private theorem abs_coordFun_le (i : CoordIndex F k) (q : (Fin k → ℝ) × StepVariable (finiteCells F)) :
    |coordFun i q| ≤ ‖q‖ := by
  rcases i with d | i
  · have h1 : |q.2 d.1 d.2| ≤ ‖q.2 d.1‖ := by
      have := PiLp.norm_apply_le (q.2 d.1) d.2
      simpa using this
    exact h1.trans ((norm_le_pi_norm q.2 d.1).trans (norm_snd_le q))
  · have h1 : |q.1 i| ≤ ‖q.1‖ := by
      have := norm_le_pi_norm q.1 i
      simpa using this
    exact h1.trans (norm_fst_le q)
private theorem eq_sum_coordFun (q : (Fin k → ℝ) × StepVariable (finiteCells F)) :
    q = ∑ i : CoordIndex F k, coordFun i q • basisVector i := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  refine Prod.ext ?_ ?_
  · funext i
    simp [coordFun, basisVector, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · funext b
    ext a
    simp only [coordFun, basisVector, Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero,
      add_zero]
    rw [Finset.sum_apply, Finset.sum_eq_single b]
    · rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Pi.single_eq_same]
      have e : (∑ x : Fin 3, q.2 b x • EuclideanSpace.single x (1 : ℝ)) a = q.2 b a := by
        simp [Finset.sum_apply, Pi.single_apply]
      simpa using e.symm
    · intro b' _ hb
      simp [Finset.sum_apply, hb.symm]
    · simp
end Coordinates
section Sums
variable {F : BlockFrame} {k : ℕ}
private def slotVectors {l j : ℕ} (g : Fin l → ↥(chordBonds (finiteCells F)) × Fin 3) (ι : Fin j → Fin k) :
    Fin (l + j) → (Fin k → ℝ) × StepVariable (finiteCells F) :=
  Fin.addCases (fun i => basisVector (Sum.inl (g i))) (fun i => basisVector (Sum.inr (ι i)))
private theorem iteratedFDeriv_slotVectors_eq (G : AboveFrames F) (V : F.GaugeField F.top)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)) {l j : ℕ} (g : Fin l → ↥(chordBonds (finiteCells F)) × Fin 3)
    (ι : Fin j → Fin k) (hG : ContDiffAt ℝ ((l + j : ℕ) : WithTop ℕ∞) (paramFirstEval G V c X) (0, η)) :
    iteratedFDeriv ℝ (l + j) (paramFirstEval G V c X) (0, η) (slotVectors g ι) =
      jointMixedDeriv G η V (fun i => (g i).1) (fun i => EuclideanSpace.single (g i).2 1)
        (fun i => c (ι i)) (fun i => X (ι i)) := by
  classical
  set v := slotVectors (F := F) g ι with hv
  let Λ : (Fin (l + j) → ℝ) →L[ℝ] (Fin k → ℝ) × StepVariable (finiteCells F) :=
    ∑ m, (ContinuousLinearMap.proj m : (Fin (l + j) → ℝ) →L[ℝ] ℝ).smulRight (v m)
  have hΛ : ∀ τ, Λ τ = ∑ m, τ m • v m := fun τ => by
    simp [Λ]
  have hsingle : ∀ m, Λ (Pi.single m 1) = v m := fun m => by
    rw [hΛ, Finset.sum_eq_single m]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have hcast : ∀ i, v (Fin.castAdd j i) =
      (0, Pi.single (g i).1 (EuclideanSpace.single (g i).2 1)) := fun i => by
    simp [hv, slotVectors, basisVector]
  have hnat : ∀ i, v (Fin.natAdd l i) = (Pi.single (ι i) 1, 0) := fun i => by
    simp [hv, slotVectors, basisVector]
  have hfst : ∀ τ, (Λ τ).1 = pullbackMap ι fun i => τ (Fin.natAdd l i) := fun τ => by
    funext y
    rw [hΛ, Fin.sum_univ_add, pullbackMap_apply]
    simp only [hcast, hnat]
    simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero, zero_add,
      Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : ι r = y
    · simp [h]
    · simp [h, show ¬ y = ι r from fun e => h e.symm]
  have hsnd : ∀ τ, (Λ τ).2 =
      ∑ i, Pi.single (g i).1 (τ (Fin.castAdd j i) • EuclideanSpace.single (g i).2 (1 : ℝ)) :=
    fun τ => by
    rw [hΛ, Fin.sum_univ_add]
    simp only [hcast, hnat]
    simp [Prod.snd_sum, Pi.single_smul]
  have hmove : jointDisplacement G η V (fun i => (g i).1) (fun i => EuclideanSpace.single (g i).2 1)
      (fun i => c (ι i)) (fun i => X (ι i)) = fun τ => paramFirstEval G V c X ((0, η) + Λ τ) := by
    funext τ
    simp only [jointDisplacement, paramFirstEval, displacedPoint, Prod.fst_add, Prod.snd_add, zero_add, hfst,
      hsnd, bondSpread_pullback]
  unfold jointMixedDeriv
  rw [hmove, iteratedFDeriv_affine_zero _ Λ hG]
  congr 1
  funext i
  exact (hsingle i).symm
private theorem iteratedFDeriv_add_const_of_pos {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (κ : ℝ) {i : ℕ} (hi : 1 ≤ i) (x : E) :
    iteratedFDeriv ℝ i (fun y => f y + κ) x = iteratedFDeriv ℝ i f x := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have e : (fun y => fderiv ℝ (fun y => f y + κ) y) = fun y => fderiv ℝ f y := by
    funext y
    exact fderiv_add_const κ
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, e]
private theorem jointMixedDeriv_neg_add_const (P : AboveFrames F) (κ : ℝ) (η : StepVariable (finiteCells F))
    (V : F.GaugeField F.top) {l j : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions) (hlj : 1 ≤ l + j) :
    jointMixedDeriv (fun ζ V' => -P ζ V' + κ) η V b u c X = -jointMixedDeriv P η V b u c X := by
  unfold jointMixedDeriv
  have e : jointDisplacement (fun ζ V' => -P ζ V' + κ) η V b u c X =
      fun τ => (-jointDisplacement P η V b u c X) τ + κ := rfl
  rw [e, iteratedFDeriv_add_const_of_pos _ _ hlj, iteratedFDeriv_neg_apply]
  rfl
private theorem sum_jet_bounds (hL : DerivAlongRulesHold) {J : Type} (Js : Finset J) (P : J → AboveFrames F)
    (κ : J → ℝ) (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)) (hX : AreUnitVectors X) {M : ℝ} (hM : 0 ≤ M)
    (hsm : ∀ j ∈ Js, ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4) (X' : Fin k' → imaginaryQuaternions),
      AreUnitVectors X' → ContDiffAt ℝ 3 (paramFirstEval (P j) V c' X') (0, η))
    (hb : ∀ j ∈ Js, ∀ (l i : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F))) (u : Fin l → EuclideanSpace ℝ (Fin 3))
      (c' : Fin i → F.Site F.top × Fin 4) (X' : Fin i → imaginaryQuaternions), 1 ≤ l + i → l + i ≤ 3 →
      (∀ m, ‖u m‖ = 1) → AreUnitVectors X' → |jointMixedDeriv (P j) η V b u c' X'| ≤ M) :
    ContDiffAt ℝ 3 (paramFirstEval (fun ζ V' => ∑ j ∈ Js, (-P j ζ V' + κ j)) V c X) (0, η) ∧
      ∀ p, 1 ≤ p → p ≤ 3 →
        ‖iteratedFDeriv ℝ p (paramFirstEval (fun ζ V' => ∑ j ∈ Js, (-P j ζ V' + κ j)) V c X) (0, η)‖ ≤
          (Fintype.card (CoordIndex F k) : ℝ) ^ p * (Js.card * M) := by
  classical
  have hQ : ∀ j ∈ Js, ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4) (X' : Fin k' → imaginaryQuaternions),
      AreUnitVectors X' →
      ContDiffAt ℝ 3 (paramFirstEval (fun ζ V' => -P j ζ V' + κ j) V c' X') (0, η) := fun j hj k' c' X' hX' => by
    have e : paramFirstEval (fun ζ V' => -P j ζ V' + κ j) V c' X' =
        fun q => -(paramFirstEval (P j) V c' X' q) + κ j := rfl
    rw [e]
    exact (hsm j hj k' c' X' hX').neg.add contDiffAt_const
  have hsum : ContDiffAt ℝ 3 (paramFirstEval (fun ζ V' => ∑ j ∈ Js, (-P j ζ V' + κ j)) V c X) (0, η) := by
    have e : paramFirstEval (fun ζ V' => ∑ j ∈ Js, (-P j ζ V' + κ j)) V c X =
        fun q => ∑ j ∈ Js, paramFirstEval (fun ζ V' => -P j ζ V' + κ j) V c X q := rfl
    rw [e]
    exact ContDiffAt.sum fun j hj => hQ j hj k c X hX
  refine ⟨hsum, fun p hp1 hp3 => ?_⟩
  refine opNorm_le_of_basis_coeffs _ basisVector coordFun abs_coordFun_le eq_sum_coordFun (by positivity)
    fun β => ?_
  obtain ⟨l, i, g, ι, σ, hσ⟩ := exists_sorted_slots β
  have hp : l + i = p := by simpa using Fintype.card_congr σ
  subst hp
  have hcp : ContDiffAt ℝ ((l + i : ℕ) : WithTop ℕ∞)
      (paramFirstEval (fun ζ V' => ∑ j ∈ Js, (-P j ζ V' + κ j)) V c X) (0, η) :=
    hsum.of_le (by exact_mod_cast hp3)
  have R := hL.1 ((Fin k → ℝ) × StepVariable (finiteCells F)) ℝ
  have hv : slotVectors g ι = (fun m => basisVector (β m)) ∘ σ := by
    funext m
    refine Fin.addCases (fun x => ?_) (fun x => ?_) m
    · simp [slotVectors, hσ]
    · simp [slotVectors, hσ]
  have e1 : iteratedFDeriv ℝ (l + i) (paramFirstEval (fun ζ V' => ∑ j ∈ Js, (-P j ζ V' + κ j)) V c X) (0, η)
      (fun m => basisVector (β m)) =
      iteratedFDeriv ℝ (l + i) (paramFirstEval (fun ζ V' => ∑ j ∈ Js, (-P j ζ V' + κ j)) V c X) (0, η)
        (slotVectors g ι) := by
    rw [R.iteratedFDeriv_eq _ _ _ _ hcp, R.iteratedFDeriv_eq _ _ _ _ hcp, hv]
    exact R.perm _ _ _ _ (Equiv.Perm.ofFn_comp_perm σ _).symm (by simpa using hcp)
  rw [e1, iteratedFDeriv_slotVectors_eq _ V c X η g ι hcp]
  have hu : ∀ m : Fin l, ‖EuclideanSpace.single (g m).2 (1 : ℝ)‖ = 1 := fun m => by simp
  have hXι : AreUnitVectors fun m => X (ι m) := fun m => hX _
  rw [jointMixedDeriv_finset_sum Js (fun j ζ V' => -P j ζ V' + κ j) _ _ _ _ fun j hj => ?_]
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ j ∈ Js, |jointMixedDeriv (fun ζ V' => -P j ζ V' + κ j) η V (fun m => (g m).1)
        (fun m => EuclideanSpace.single (g m).2 1) (fun m => c (ι m)) (fun m => X (ι m))| ≤ M := fun j hj => by
      rw [jointMixedDeriv_neg_add_const _ _ _ _ _ _ _ _ (by omega), abs_neg]
      exact hb j hj l i _ _ _ _ (by omega) hp3 hu hXι
    refine (Finset.sum_le_card_nsmul _ _ _ this).trans (le_of_eq ?_)
    simp
  · exact (jointDisplacement_contDiffAt _ _ _ _ (rotatedEval_contDiffAt (hQ j hj i _ _ hXι))).of_le
      (by exact_mod_cast hp3)
end Sums
section Flat
variable {F : BlockFrame}
private theorem leftTranslate_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p2043 <;> assumption
private theorem interpolatedFrame_zero (a ρA : ℝ) (m : ℕ) (d : F.Site F.depth × Fin 4) :
    interpolatedFrame 0 a ρA m d = minimizingBondCoordinate a ρA (finiteCells F) d := by
  funext V
  simp [interpolatedFrame, stepFrame]
private theorem interpolatedCoords_zero (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    interpolatedCoords 0 a ρA m V η = coordsAboveFrame true a ρA 0 V η := by apply _root_.YangMills.SharedProofs.p718 <;> assumption
private theorem interpolatedField_zero (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    interpolatedField 0 a ρA m V η = fieldAboveFrame true a ρA 0 V η := by
  unfold interpolatedField fieldAboveFrame
  rw [interpolatedCoords_zero]
private theorem minimizingBondCoordinate_of_not_mem (a ρ : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (b : F.Site F.depth × Fin 4) (hb : b ∉ chordBonds S) : minimizingBondCoordinate a ρ S b V = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.minimizingCoordinates_of_not_mem <;> assumption
abbrev _root_.YangMills.SharedProofs.p604 := @minimizingBondCoordinate_of_not_mem
private theorem plaquetteDefect_of_trivial {j : ℕ} (X : F.GaugeField j) (hX : ∀ x i, X x i = 1)
    (p : F.Site j × Fin 4 × Fin 4) : plaquetteDefect X p = 0 := by
  have e : X = fun _ _ => 1 := funext fun x => funext fun i => hX x i
  subst e
  simp [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue]
private theorem chartedField_uniform (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (hw : ∀ x i, w x i = 0)
    (x : F.Site F.depth) (i : Fin 4) : chartedField w (uniformField F F.top) x i = 1 := by
  have h0 : expUnit (0 : imaginaryQuaternions) = 1 := by
    apply Subtype.ext
    simp [expUnit]
  unfold chartedField
  split_ifs <;> simp [hw, h0, ColdStepAtMirrorFrames.uniformField]
private theorem regularCoordinates_uniform (T : ParameterAssignment) (hT : T.Admissible) (hFL : F.blockSide = T.side)
    (hs : ∀ i, 64 ≤ F.extent i) :
    HasRegularCoordinates T.coupling T.δ₁ T.ρA T.N (finiteCells F) (uniformField F F.top) := by
  obtain ⟨-, -, -, -, -, hσA, -, -, hmain⟩ := hT.chain
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => (by norm_num : 2 ≤ 64).trans (hs i)
  have hall : ∀ z : F.Cell, z ∈ finiteCells F := fun z => BlockOffsets.mem_finiteCells hs2 z
  have hreg : IsOrthantRegular (finiteCells F) 1024 := fun z =>
    ⟨fun _ => 1, fun _ => Or.inl rfl, fun q _ _ h _ _ => hall _⟩
  have hcold : IsCold (finiteCells F) F.top T.σA (uniformField F F.top) := fun p _ => by
    have h := plaquetteDefect_of_trivial (uniformField F F.top) (fun _ _ => rfl) p
    rw [h]
    exact hσA
  exact (hmain F 1024 (finiteCells F) hFL (Or.inr hs) le_rfl hreg T.σA (uniformField F F.top) hσA le_rfl
    hcold).2.2.2.1
private theorem paramFirstEval_contDiffAt_of_rotated {k : ℕ} {n : WithTop ℕ∞} {G : AboveFrames F}
    {V : F.GaugeField F.top} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    {η : StepVariable (finiteCells F)}
    (h : ContDiffAt ℝ n (rotatedEval G V c X) (η, 0)) : ContDiffAt ℝ n (paramFirstEval G V c X) (0, η) :=
  ContDiffAt.comp (g := rotatedEval G V c X)
    (f := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) => (q.2, q.1)) (0, η) h
    (contDiff_snd.prodMk contDiff_fst).contDiffAt
private abbrev RemainderIndex (F : BlockFrame) : Type :=
  (F.Site F.top × Fin 4) ⊕ (↥(chordBonds (finiteCells F)) ⊕ F.Site F.depth)
private def remainderTerms (F : BlockFrame) : Finset (RemainderIndex F) :=
  (innerBonds (finiteCells F) F.top).disjSum (Finset.univ.disjSum (sitesOfCells (finiteCells F) F.depth))
private def remainderTerm (a ρA x : ℝ) (f : LocalFamily) : RemainderIndex F → AboveFrames F
  | Sum.inl c₀ => fun ζ V' => haarGap (a * x * ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField 0 a ρA 0 V' ζ) c₀‖)
  | Sum.inr (Sum.inl b) => fun ζ V' => haarLogRatio (interpolatedCoords 0 a ρA 0 V' ζ b.1.1 b.1.2)
  | Sum.inr (Sum.inr y) => fun ζ V' => interpolatedExpansion 0 a ρA 0 f y ζ V'
private def remainderConstant (a x : ℝ) : RemainderIndex F → ℝ
  | Sum.inl _ => haarGap (a * x)
  | Sum.inr _ => 0
end Flat
private def familyBound (T : ParameterAssignment) (j : ℕ) : ℝ := if j = 3 then T.E₃ else T.E
private theorem runningMax_familyBound_le (T : ParameterAssignment) (hE : 0 ≤ T.E) (hE₃ : 0 ≤ T.E₃) (p : ℕ) :
    runningMax (familyBound T) p ≤ T.E + T.E₃ := by
  induction p with
  | zero =>
    show (0 : ℝ) ≤ _
    positivity
  | succ p ih =>
    refine max_le ih ?_
    unfold familyBound
    split_ifs <;> linarith
private theorem energy_bounds_pos (T : ParameterAssignment) (hT : T.Admissible) : 0 < T.E ∧ 0 < T.E₃ := by
  have hB := hT.B_ge
  have h1 : 0 < T.E := by
    show 0 < 4 * T.B
    linarith
  refine ⟨h1, ?_⟩
  show 0 < T.E / T.η₃
  exact div_pos h1 hT.η₃_pos
private theorem jet_bounds_at_uniform (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hMv : ChartShiftLipschitz) (hB : SiteDecomposition) (hCov : BlocksCoverLowerLevel)
    (hG : HaarGapOfAverageDerivBounds) (hH : HaarLogRatioDerivBounds)
    (hRow : expansionAboveFrameStatement) (T : ParameterAssignment) (hT : T.Admissible) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (F : BlockFrame) (n : ℕ) (x : ℝ) (f : LocalFamily), F.blockSide = T.side → T.n₀ ≤ n →
      (∀ i, F.extent i = n) → 2 ≤ T.coupling * x →
      HasBoundedDerivatives T.side F.depth T.n₀ T.threshold (T.rt / 2 ^ 10) 3 (familyBound T) f →
      (∀ d ∈ chordBonds (finiteCells F),
        minimizingBondCoordinate T.coupling T.ρA (finiteCells F) d (uniformField F F.top) = 0) →
      ∀ (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
        ContDiffAt ℝ 3 (paramFirstEval (fun ζ V' => ∑ j ∈ remainderTerms F,
          (-remainderTerm T.coupling T.ρA x f j ζ V' + remainderConstant T.coupling x j))
          (uniformField F F.top) c X) (0, η) ∧
        ∀ p, 1 ≤ p → p ≤ 3 →
          ‖iteratedFDeriv ℝ p (paramFirstEval (fun ζ V' => ∑ j ∈ remainderTerms F,
            (-remainderTerm T.coupling T.ρA x f j ζ V' + remainderConstant T.coupling x j))
            (uniformField F F.top) c X) (0, η)‖ ≤
            (Fintype.card (CoordIndex F k) : ℝ) ^ p * ((remainderTerms F).card * M) := by
  classical
  obtain ⟨hδ, -, -, -, -, -, -, hNpos, -⟩ := id hT.chain
  have hK : ∀ k, 0 ≤ T.N k := fun k => (hNpos k).le
  have hκ0 : 0 < T.rt := hT.rt_pos
  have hκr : 2 ^ 9 * T.rt ≤ T.δ₁ := by
    have h1 := hT.rt_le
    have h2 := hT.δc_le
    have h3 := hT.δ₁_pos
    have h4 := hT.δc_pos
    have h5 : T.δc / 2 ^ 14 ≤ T.δc := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    have h6 : T.rt * 2 ^ 14 ≤ T.δc := by
      rwa [le_div_iff₀ (by norm_num)] at h1
    have h7 : T.δc * 2 ^ 6 ≤ T.δ₁ := by
      rwa [le_div_iff₀ (by norm_num)] at h2
    nlinarith
  obtain ⟨Cr, hCr, gR⟩ := hRow T.N T.δ₁ T.rt T.side hK hκ0 hκr hT.L_odd hT.L_ge
  obtain ⟨Dg, pDg, gG⟩ := hG T.N T.δ₁ T.rt T.side hK hκ0.le hκr hT.L_odd
  obtain ⟨Dh, pDh, gH⟩ := hH T.N T.δ₁ T.rt hK hδ.le hκ0.le hκr
  obtain ⟨hE, hE₃⟩ := energy_bounds_pos T hT
  have hdg := lowOrderSum_nonneg pDg
  have hdh := lowOrderSum_nonneg pDh
  refine ⟨lowOrderSum Dg + lowOrderSum Dh + Cr * (T.E + T.E₃), by positivity, ?_⟩
  intro F n x f hFL hn hside hax hder h0 η hη k c X hX
  have hσ := hT.σ_pos
  have hσ1 := hT.σ_one
  have hρ0 : 0 < T.ballRadius := by
    show 0 < T.threshold / 64
    positivity
  have hρ1 : T.ballRadius ≤ 1 := by
    show T.threshold / 64 ≤ 1
    linarith
  have hρσ : 4 * T.ballRadius < T.threshold := by
    show 4 * (T.threshold / 64) < T.threshold
    linarith
  have hn64 : 64 ≤ n := by
    have := hT.n₀_ge
    omega
  have hs64 : ∀ i, 64 ≤ F.extent i := fun i => by rw [hside i]; exact hn64
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => (by norm_num : 2 ≤ 64).trans (hs64 i)
  have hcub : IsLargeCubicTorus F := ⟨n, hn64, hside⟩
  have hodd : Odd F.blockSide := hFL ▸ hT.L_odd
  have hL1 : 1 ≤ T.side := hT.L_odd.pos
  have hlow : IsCubicTorusAbove T.side F.depth T.n₀ F :=
    ⟨hFL, rfl, n, hside, hn.trans (Nat.le_mul_of_pos_right n hL1)⟩
  have hne : Nonempty ↥(chordBonds (finiteCells F)) := nonempty_chordBonds hB hCov hodd hs2
  set V₀ : F.GaugeField F.top := uniformField F F.top with hV₀
  have hco := regularCoordinates_uniform T hT hFL hs64
  have hfr0 : ∀ d, minimizingBondCoordinate T.coupling T.ρA (finiteCells F) d V₀ = 0 := fun d => by
    by_cases hd : d ∈ chordBonds (finiteCells F)
    · exact h0 d hd
    · exact minimizingBondCoordinate_of_not_mem _ _ _ _ _ hd
  have habove : ∀ (ζ : StepVariable (finiteCells F)) x i,
      interpolatedCoords 0 T.coupling T.ρA 0 V₀ ζ x i = stepCoordinates ζ x i := by
    intro ζ x i
    have e := congrFun (congrFun (interpolatedCoords_zero T.coupling T.ρA 0 V₀ ζ) x) i
    rw [e]
    simp only [coordsAboveFrame, stepFrame, if_true]
    rw [hfr0, zero_add]
  have han : ∀ d ∈ chordBonds (finiteCells F),
      IsBondAnalyticAt (interpolatedFrame 0 T.coupling T.ρA 0 d) V₀ := fun d hd => by
    rw [interpolatedFrame_zero]
    exact (hco d hd).1
  have hdec : ∀ d ∈ chordBonds (finiteCells F), ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4)
      (X' : Fin k' → imaginaryQuaternions), 1 ≤ k' → AreUnitVectors X' →
      ‖bondDeriv (interpolatedFrame 0 T.coupling T.ρA 0 d) V₀ c' X'‖ ≤
        T.N k' * Real.exp (-(T.δ₁ * bondListDistance (enclosingCell d.1) c')) := fun d hd k' c' X' hk hX' => by
    rw [interpolatedFrame_zero]
    have h := (hco d hd).2 k' c' X' hk hX'
    rw [neg_mul] at h
    exact h
  have hball : ∀ (ζ : StepVariable (finiteCells F)), (∀ b, ‖ζ b‖ ≤ T.ballRadius) →
      ∀ x i, ‖stepCoordinates ζ x i‖ ≤ T.ballRadius :=
    fun ζ hζ => (hMv F V₀ (fun _ _ => 0) ζ T.ballRadius hodd hζ hρ0.le).1
  have hcold : ∀ ζ : StepVariable (finiteCells F), (∀ b, ‖ζ b‖ ≤ T.ballRadius) →
      IsSmallCurvature T.threshold (interpolatedField 0 T.coupling T.ρA 0 V₀ ζ) := fun ζ hζ p _ => by
    have e : interpolatedField 0 T.coupling T.ρA 0 V₀ ζ =
        chartedField (fun x i => (0 : imaginaryQuaternions) + stepCoordinates ζ x i) V₀ := by
      unfold interpolatedField
      congr 1
      funext x i
      rw [habove, zero_add]
    rw [e]
    have h2 := (hMv F V₀ (fun _ _ => 0) ζ T.ballRadius hodd hζ hρ0.le).2.1 p
    have h3 := plaquetteDefect_of_trivial _ (chartedField_uniform (fun _ _ => 0) fun _ _ => rfl) p
    rw [h3] at h2
    linarith
  have hsmall : (T.ballRadius + 2 * T.ballRadius) * (10 * (T.side : ℝ)) ≤ 1 := by
    have h1 := hT.σ_L
    have h2 := hNpos 0
    have hLp : (0 : ℝ) ≤ T.side := Nat.cast_nonneg _
    have e : (T.ballRadius + 2 * T.ballRadius) * (10 * (T.side : ℝ)) = 30 / 64 * (T.side * T.threshold) := by
      show (T.threshold / 64 + 2 * (T.threshold / 64)) * (10 * (T.side : ℝ)) = _
      ring
    have h3 : 0 ≤ (T.side : ℝ) * T.threshold := by positivity
    have h4 : 2 ^ 10 * ((T.side : ℝ) * T.threshold) ≤ 2 ^ 10 * (T.side : ℝ) * (T.N 0 + 1) * T.threshold := by
      have : (T.side : ℝ) * T.threshold ≤ (T.side : ℝ) * T.threshold * (T.N 0 + 1) :=
        le_mul_of_one_le_right h3 (by linarith)
      nlinarith
    rw [e]
    nlinarith
  have hfr : ∀ (j : ℕ) (c' : Fin j → F.Site F.top × Fin 4) (X' : Fin j → imaginaryQuaternions),
      ∀ᶠ τ : Fin j → ℝ in 𝓝 0, ∀ d ∈ chordBonds (finiteCells F),
        ‖interpolatedFrame 0 T.coupling T.ρA 0 d (leftTranslate (ColdStepAtMirrorFrames.bondSpread c' X' τ) V₀)‖ ≤ T.ballRadius := by
    intro j c' X'
    rw [Filter.eventually_all_finset]
    intro d hd
    have hc : ContinuousAt (fun τ : Fin j → ℝ => minimizingBondCoordinate T.coupling T.ρA (finiteCells F) d
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c' X' τ) V₀)) 0 := ((hco d hd).1 j c' X').continuousAt
    have hz : ‖minimizingBondCoordinate T.coupling T.ρA (finiteCells F) d
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c' X' 0) V₀)‖ < T.ballRadius := by
      rw [leftTranslate_bondSpread_zero, hfr0]
      simpa using hρ0
    rw [interpolatedFrame_zero]
    exact (hc.norm.eventually_lt continuousAt_const hz).mono fun _ h => h.le
  have gRy := fun y => gR F T.n₀ 0 T.threshold 0 T.coupling T.ρA T.ballRadius (familyBound T) f V₀ y hFL hcub
    hlow (fun j => by unfold familyBound; split_ifs <;> positivity) hder hcold
    (fun ζ hζ x i _ => by rw [habove]; exact (hball ζ hζ x i).trans hρ1) han hdec
  have gGc := fun (c₀ : F.Site F.top × Fin 4) (l i : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
      (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c' : Fin i → F.Site F.top × Fin 4)
      (X' : Fin i → imaginaryQuaternions) (h1 : 1 ≤ l + i) (hu : ∀ m, ‖u m‖ = 1) (hX' : AreUnitVectors X') =>
    gG F 0 T.coupling T.ρA x T.ballRadius T.ballRadius 0 V₀ η hFL hcub hax hρ0 hρ0.le hsmall hη hfr han hdec
      c₀ l i b u c' X' h1 hu hX'
  have hsz : ∀ b₀ : ↥(chordBonds (finiteCells F)),
      ‖toImaginary (η b₀) + interpolatedFrame 0 T.coupling T.ρA 0 b₀.1 V₀‖ ≤ 1 := fun b₀ => by
    rw [interpolatedFrame_zero, hfr0, add_zero]
    have e : stepCoordinates η b₀.1.1 b₀.1.2 = toImaginary (η b₀) := by
      unfold stepCoordinates
      rw [dif_pos b₀.2]
    rw [← e]
    exact (hball η hη _ _).trans hρ1
  have gHc := fun (b₀ : ↥(chordBonds (finiteCells F))) (l i : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
      (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c' : Fin i → F.Site F.top × Fin 4)
      (X' : Fin i → imaginaryQuaternions) (h1 : 1 ≤ l + i) (hu : ∀ m, ‖u m‖ = 1) (hX' : AreUnitVectors X') =>
    gH F 0 T.coupling T.ρA 0 V₀ η b₀ (hsz b₀) (han _ b₀.2) (hdec _ b₀.2) l i b u c' X' h1 hu hX'
  have hrκ : (0 : ℝ) ≤ 2 ^ 8 * T.rt := by positivity
  have hexp : ∀ m : ℕ, Real.exp (-(2 ^ 8 * T.rt * (m : ℝ))) ≤ 1 := fun m => by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 2 ^ 8 * T.rt * (m : ℝ) := by positivity
    linarith
  have hexp7 : ∀ m : ℕ, Real.exp (-(2 ^ 7 * T.rt * (m : ℝ))) ≤ 1 := fun m => by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 2 ^ 7 * T.rt * (m : ℝ) := by positivity
    linarith
  have hCE : 0 ≤ Cr * (T.E + T.E₃) := by positivity
  refine sum_jet_bounds hL (remainderTerms F) (remainderTerm T.coupling T.ρA x f)
    (remainderConstant T.coupling x) V₀ c X η hX (by positivity) ?_ ?_
  · intro j _ k' c' X' hX'
    rcases j with c₀ | b₀ | y
    · refine paramFirstEval_contDiffAt_of_rotated ?_
      have h := (hA F V₀ (remainderTerm T.coupling T.ρA x f (Sum.inl c₀)) η k' c' X').1 hne
        (fun l b u hl hu => (gGc c₀ l k' b u c' X' (by omega) hu hX').1) 3
      exact_mod_cast h
    · refine paramFirstEval_contDiffAt_of_rotated ?_
      have h := (hA F V₀ (remainderTerm T.coupling T.ρA x f (Sum.inr (Sum.inl b₀))) η k' c' X').1 hne
        (fun l b u hl hu => (gHc b₀ l k' b u c' X' (by omega) hu hX').1) 3
      exact_mod_cast h
    · exact (gRy y).1 k' c' X' η hη
  · intro j _ l i b u c' X' h1 h3 hu hX'
    rcases j with c₀ | b₀ | y
    · have h := (gGc c₀ l i b u c' X' h1 hu hX').2
      have h2 : Dg l i ≤ lowOrderSum Dg := le_lowOrderSum pDg l i (by omega) (by omega)
      have h4 := mul_le_of_le_one_right (pDg l i).le
        (hexp (cellSetDiameter ({c₀.1} ∪ chordBondCells b ∪ topBondCells c')))
      refine h.trans (h4.trans ?_)
      linarith
    · have h := (gHc b₀ l i b u c' X' h1 hu hX').2
      have h2 : Dh l i ≤ lowOrderSum Dh := le_lowOrderSum pDh l i (by omega) (by omega)
      have h4 := mul_le_of_le_one_right (pDh l i).le
        (hexp (cellSetDiameter ({enclosingCell b₀.1.1} ∪ chordBondCells b ∪ topBondCells c')))
      refine h.trans (h4.trans ?_)
      linarith
    · have h := (gRy y).2 η l i b u c' X' hη hu hX' h1 h3
      have h2 := runningMax_familyBound_le T hE.le hE₃.le (l + i)
      have h5 : 0 ≤ runningMax (familyBound T) (l + i) := by
        cases (l + i) with
        | zero => exact le_rfl
        | succ m =>
          refine le_max_of_le_right ?_
          unfold familyBound
          split_ifs <;> positivity
      have h6 : Cr * runningMax (familyBound T) (l + i) ≤ Cr * (T.E + T.E₃) :=
        mul_le_mul_of_nonneg_left h2 hCr.le
      have h4 := mul_le_of_le_one_right (mul_nonneg hCr.le h5)
        (hexp7 (cellSetDiameter (insert (enclosingCell y) (chordBondCells b ∪ topBondCells c'))))
      refine h.trans (h4.trans ?_)
      linarith
section Curve
variable {k : ℕ} (R : StepSetup) (n : ℕ) [NeZero n] (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
private def torusBondsInFrame :
    Fin k → (torusFrame R.params.side R.depth n).Site (torusFrame R.params.side R.depth n).top × Fin 4 :=
  fun l => (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top (c l).1,
    (c l).2)
private theorem perturbedTop_eq_leftTranslate (τ : Fin k → ℝ) :
    perturbedTop R n c X τ =
      leftTranslate (ColdStepAtMirrorFrames.bondSpread (torusBondsInFrame R n c) X τ) (ColdStepAtMirrorFrames.uniformField _ _) := by
  have hp : ∀ i, (torusFrame R.params.side R.depth n).period (torusFrame R.params.side R.depth n).top i = n :=
    fun i => by
    simp [BlockFrame.period, torusFrame]
  have : ∀ i, NeZero ((torusFrame R.params.side R.depth n).period (torusFrame R.params.side R.depth n).top i) :=
    fun i => ⟨by
    rw [hp]
    exact NeZero.ne n⟩
  exact TorusChain.readAtLevel_perturb hp c X τ (trivialField n)
private theorem exponentRemainder_eq_sum : exponentRemainderAlongCurve R n c X =
    paramFirstEval (fun ζ V' => ∑ j ∈ remainderTerms (torusFrame R.params.side R.depth n),
      (-remainderTerm R.params.coupling R.anchorRadius R.coupling (localFamilyOfDensity R.density) j ζ V' +
        remainderConstant R.params.coupling R.coupling j))
      (ColdStepAtMirrorFrames.uniformField _ _) (torusBondsInFrame R n c) X := by
  funext q
  show _ = ∑ j ∈ remainderTerms (torusFrame R.params.side R.depth n),
    (-remainderTerm R.params.coupling R.anchorRadius R.coupling (localFamilyOfDensity R.density) j q.2
      (leftTranslate (ColdStepAtMirrorFrames.bondSpread (torusBondsInFrame R n c) X q.1) (ColdStepAtMirrorFrames.uniformField _ _)) +
      remainderConstant R.params.coupling R.coupling j)
  rw [← perturbedTop_eq_leftTranslate]
  unfold exponentRemainderAlongCurve chartEnergyAlongCurve stepExponent chartedEnergyAtMinimizer remainderTerms
  rw [Finset.sum_disjSum, Finset.sum_disjSum]
  simp only [remainderTerm, remainderConstant]
  have a1 : ∑ c₀ ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n))
        (torusFrame R.params.side R.depth n).top,
      (-haarGap (R.params.coupling * R.coupling *
        ‖_root_.YangMills.Construction.BlockAverages.contourAverage (interpolatedField 0 R.params.coupling R.anchorRadius 0 (perturbedTop R n c X q.1) q.2) c₀‖) +
        haarGap (R.params.coupling * R.coupling)) =
      -∑ c₀ ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n)) (torusFrame R.params.side R.depth n).top,
        haarGapExcess R.params.coupling R.coupling
          (fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c X q.1) q.2) c₀ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c₀ _ => ?_
    unfold haarGapExcess
    rw [interpolatedField_zero]
    ring
  have a2 : ∑ b : ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))),
      (-haarLogRatio (interpolatedCoords 0 R.params.coupling R.anchorRadius 0 (perturbedTop R n c X q.1) q.2
        b.1.1 b.1.2) + 0) =
      -∑ b : ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))),
        haarLogRatio (coordsAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c X q.1) q.2
          b.1.1 b.1.2) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [interpolatedCoords_zero, add_zero]
  have a3 : ∑ y ∈ sitesOfCells (finiteCells (torusFrame R.params.side R.depth n))
        (torusFrame R.params.side R.depth n).depth,
      (-interpolatedExpansion 0 R.params.coupling R.anchorRadius 0 (localFamilyOfDensity R.density) y q.2
        (perturbedTop R n c X q.1) + 0) =
      -∑ y ∈ sitesOfCells (finiteCells (torusFrame R.params.side R.depth n))
          (torusFrame R.params.side R.depth n).depth,
        centredExpansion true R.params.coupling R.anchorRadius 0 (localFamilyOfDensity R.density) y q.2
          (perturbedTop R n c X q.1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold interpolatedExpansion centredExpansion
    rw [interpolatedField_zero, add_zero]
  rw [a1, a2, a3]
  ring
end Curve
private theorem card_finiteCells_torusFrame (L t n : ℕ) [NeZero n] :
    (finiteCells (torusFrame L t n)).card = n ^ 4 := by apply _root_.YangMills.SharedProofs.p57413 <;> assumption
private theorem card_sitesOfCells_le (F : BlockFrame) :
    (sitesOfCells (finiteCells F) F.depth).card ≤ (finiteCells F).card * (centredCube (F.blockSide ^ 1)).card := by
  classical
  unfold sitesOfCells
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((centredCube (F.blockSide ^ 1)).card) fun z _ => ?_).trans
    (le_of_eq (by simp))
  have e : F.top - F.depth = 1 := by simp [BlockFrame.top]
  rw [e]
  exact Finset.card_image_le
private theorem toImaginary_imaginaryToEuclidean (v : imaginaryQuaternions) :
    toImaginary (imaginaryToEuclidean v) = v := by apply _root_.YangMills.SharedProofs.p66610 <;> assumption
private theorem eq_zero_of_imaginaryToEuclidean_eq_zero {v : imaginaryQuaternions}
    (h : imaginaryToEuclidean v = 0) : v = 0 := by
  rw [← toImaginary_imaginaryToEuclidean v, h]
  apply Subtype.ext
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;> simp [toImaginary]
end ExponentRemainderJets
open ExponentRemainderJets in
theorem exponentRemainderJetBounds_holds (hL : DerivAlongRulesHold) (hA : JointMixedDerivEqDerivAlong)
    (hMv : ChartShiftLipschitz) (hB : SiteDecomposition) (hCov : BlocksCoverLowerLevel)
    (hN : BondCount) (hExpansionB : ColdExpansionRegular) (h1 : MinimizerCoordinatesJetBound)
    (hG : HaarGapOfAverageDerivBounds) (hH : HaarLogRatioDerivBounds) (hRow : expansionAboveFrameStatement) :
    ExponentRemainderJetBounds := by
  classical
  intro T hT k
  obtain ⟨M, hM, gM⟩ := jet_bounds_at_uniform hL hA hMv hB hCov hG hH hRow T hT
  obtain ⟨nb, hnb⟩ := hN T.side hT.L_odd
  obtain ⟨C₁, q₁, -, -, g₁⟩ := h1 T hT k
  set cL : ℕ := (centredCube (T.side ^ 1)).card with hcL
  set A : ℝ := (k : ℝ) + 3 * nb + 1 with hA'
  set B : ℝ := 4 + (nb : ℝ) + cL + 1 with hB'
  have hA1 : 1 ≤ A := by
    have h2 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ nb := Nat.cast_nonneg _
    simp only [hA']
    linarith
  have hB0 : 0 < B := by
    have h2 : (0 : ℝ) ≤ cL := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ nb := Nat.cast_nonneg _
    simp only [hB']
    linarith
  refine ⟨A ^ 3 * (B * M) + 1, 16, by positivity, by norm_num, ?_⟩
  intro y R hy hR n _ c X hn hX η hη
  have hL' : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have ha : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hρA : R.anchorRadius = T.ρA := hR.anchorRadius_eq
  have hx : y ≤ R.coupling := hR.le_coupling
  have hax : 2 ≤ T.coupling * R.coupling := by
    have h2 : (2 : ℝ) ^ 1600 ≤ T.floorMin := le_max_right _ _
    have h3 : (2 : ℝ) ≤ 2 ^ 1600 := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ 1600 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h4 : 2 ≤ R.coupling := h3.trans (h2.trans (hy.trans hx))
    have h5 := hT.a_ge
    calc 2 ≤ R.coupling := h4
      _ = 1 * R.coupling := (one_mul _).symm
      _ ≤ T.coupling * R.coupling := mul_le_mul_of_nonneg_right h5 (zero_le_two.trans h4)
  have hrow : IsRegularFamily T.side R.depth T.n₀ T.threshold (T.rt / 2 ^ 10) T.E T.E₃
      (localFamilyOfDensity R.density) := by
    have hf : R.params.Admissible := by
      rw [hR.params_eq]
      exact hT.fits y hy
    have hn₁ : R.params.n₁ = (R.params.side : ℝ) ^ (1 / 640 : ℝ) := by
      rw [hR.params_eq]
      rfl
    have h := hExpansionB R.params R.depth R.coupling R.functional R.density hf hn₁ hR.isStep.1.1
    rw [hR.params_eq] at h
    exact h
  have hder : HasBoundedDerivatives T.side R.depth T.n₀ T.threshold (T.rt / 2 ^ 10) 3 (familyBound T)
      (localFamilyOfDensity R.density) :=
    { smooth := fun F hF y W hW j c X => by exact_mod_cast hrow.smooth F hF y W hW j c X
      gauge_invariant := hrow.gauge_invariant
      decay := fun F hF y W j c X hW h1 h3 hX => hrow.decay F hF y W j c X hW h1 h3 hX }
  have h0 : ∀ d ∈ chordBonds (finiteCells (torusFrame R.params.side R.depth n)),
      minimizingBondCoordinate T.coupling T.ρA (finiteCells (torusFrame R.params.side R.depth n)) d
        (ColdStepAtMirrorFrames.uniformField _ _) = 0 := fun d hd => by
    have h := congrFun (g₁ y R hy hR n c X hn hX).1 ⟨d, hd⟩
    have e : perturbedTop R n c X 0 = ColdStepAtMirrorFrames.uniformField _ _ := by
      rw [perturbedTop_eq_leftTranslate, leftTranslate_bondSpread_zero]
    simp only [minimizerCoordinatesAlong, e, ha, hρA] at h
    exact eq_zero_of_imaginaryToEuclidean_eq_zero h
  obtain ⟨hs, hb⟩ := gM (torusFrame R.params.side R.depth n) n R.coupling (localFamilyOfDensity R.density) hL' hn
    (fun _ => rfl) hax hder h0 η hη k (torusBondsInFrame R n c) X hX
  have e : exponentRemainderAlongCurve R n c X =
      paramFirstEval (fun ζ V' => ∑ j ∈ remainderTerms (torusFrame R.params.side R.depth n),
        (-remainderTerm T.coupling T.ρA R.coupling (localFamilyOfDensity R.density) j ζ V' +
          remainderConstant T.coupling R.coupling j))
        (ColdStepAtMirrorFrames.uniformField _ _) (torusBondsInFrame R n c) X := by
    rw [exponentRemainder_eq_sum, ha, hρA]
  rw [e]
  refine ⟨hs, fun j hj1 hj3 => (hb j hj1 hj3).trans ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by
    have h2 : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast h2
  set N : ℝ := (n : ℝ) ^ 4 with hNd
  have hN1 : 1 ≤ N := one_le_pow₀ hn1
  have hcount := hnb (torusFrame R.params.side R.depth n) n hL' (by have := hT.n₀_ge; omega) (fun _ => rfl)
  have hcells : ((finiteCells (torusFrame R.params.side R.depth n)).card : ℝ) = N := by
    rw [card_finiteCells_torusFrame]
    push_cast
    rfl
  have hcard : (Fintype.card (CoordIndex (torusFrame R.params.side R.depth n) k) : ℝ) ≤ A * N := by
    have e1 : Fintype.card (CoordIndex (torusFrame R.params.side R.depth n) k) =
        (chordBonds (finiteCells (torusFrame R.params.side R.depth n))).card * 3 + k := by
      simp [CoordIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_coe]
    rw [e1, hcount.2]
    push_cast
    rw [hcells]
    have h2 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ nb := Nat.cast_nonneg _
    simp only [hA']
    nlinarith
  have hterms : ((remainderTerms (torusFrame R.params.side R.depth n)).card : ℝ) ≤ B * N := by
    have e1 : (remainderTerms (torusFrame R.params.side R.depth n)).card =
        (innerBonds (finiteCells (torusFrame R.params.side R.depth n))
          (torusFrame R.params.side R.depth n).top).card +
          ((chordBonds (finiteCells (torusFrame R.params.side R.depth n))).card +
            (sitesOfCells (finiteCells (torusFrame R.params.side R.depth n))
              (torusFrame R.params.side R.depth n).depth).card) := by
      simp [remainderTerms, Finset.card_disjSum]
    have h2 := card_sitesOfCells_le (torusFrame R.params.side R.depth n)
    have h2' : (sitesOfCells (finiteCells (torusFrame R.params.side R.depth n))
        (torusFrame R.params.side R.depth n).depth).card ≤
        (finiteCells (torusFrame R.params.side R.depth n)).card * cL := by
      have e2 : (torusFrame R.params.side R.depth n).blockSide = T.side := hL'
      rw [e2] at h2
      exact h2
    have h3 : ((sitesOfCells (finiteCells (torusFrame R.params.side R.depth n))
        (torusFrame R.params.side R.depth n).depth).card : ℝ) ≤ N * cL := by
      rw [← hcells]
      exact_mod_cast h2'
    rw [e1, hcount.1, hcount.2]
    push_cast
    rw [hcells]
    have h4 : (0 : ℝ) ≤ nb := Nat.cast_nonneg _
    simp only [hB']
    nlinarith
  have hAN : 1 ≤ A * N := by nlinarith
  have hp : (Fintype.card (CoordIndex (torusFrame R.params.side R.depth n) k) : ℝ) ^ j ≤ (A * N) ^ 3 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard j).trans (pow_le_pow_right₀ hAN hj3)
  have ht : ((remainderTerms (torusFrame R.params.side R.depth n)).card : ℝ) * M ≤ B * N * M :=
    mul_le_mul_of_nonneg_right hterms hM
  have e16 : (n : ℝ) ^ (16 : ℝ) = N ^ 4 := by
    rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hNd, ← pow_mul]
  rw [e16]
  have hN4 : 0 ≤ N ^ 4 := by positivity
  calc _ ≤ (A * N) ^ 3 * (B * N * M) := mul_le_mul hp ht (by positivity) (by positivity)
    _ = A ^ 3 * (B * M) * N ^ 4 := by ring
    _ ≤ (A ^ 3 * (B * M) + 1) * N ^ 4 := by nlinarith
end RunningCouplingSlope
end YangMills.Construction
end
