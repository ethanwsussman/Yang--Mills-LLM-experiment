import YangMills.Construction.Continuum.TruncationOfSchwartzFunctionsAtInfinityProof
import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuples
import YangMills.Construction.Continuum.FunctionsVanishingOnAnOpenSet
import Mathlib
set_option autoImplicit false
open scoped ContDiff ComplexConjugate
noncomputable section
namespace YangMills.Construction.ConfigSpace.TensorSupport
variable {n : ℕ}
theorem contDiff_coordPartial (i : Fin n) (μ : Fin 4) {g : Config n → ℂ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (coordPartial i μ g) := by
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  have eq : coordPartial i μ g =
      fun x => fderiv ℝ g x (Pi.single i (Pi.single μ 1)) := by
    funext x
    exact (hd x).lineDeriv_eq_fderiv
  rw [eq]
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem contDiff_iteratedPartial (α : MultiIndex n) {φ : Config n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (iteratedPartial α φ) := by
  have iter : ∀ (i : Fin n) (μ : Fin 4) (m : ℕ) (g : Config n → ℂ), ContDiff ℝ ∞ g →
      ContDiff ℝ ∞ ((coordPartial i μ)^[m] g) := by
    intro i μ m
    induction m with
    | zero => intro g hg; exact hg
    | succ m ih =>
      intro g hg
      rw [Function.iterate_succ_apply]
      exact ih _ (contDiff_coordPartial i μ hg)
  have inner : ∀ (i : Fin n) (l : List (Fin 4)) (g : Config n → ℂ), ContDiff ℝ ∞ g →
      ContDiff ℝ ∞ (l.foldr (fun μ h' => (coordPartial i μ)^[α i μ] h') g) := by
    intro i l g hg
    induction l with
    | nil => exact hg
    | cons μ l ih => exact iter i μ _ _ ih
  have outer : ∀ l : List (Fin n), ContDiff ℝ ∞ (l.foldr (fun i h => (List.finRange 4).foldr
      (fun μ h' => (coordPartial i μ)^[α i μ] h') h) φ) := by
    intro l
    induction l with
    | nil => exact hφ
    | cons i l ih => exact inner i _ _ ih
  exact outer _
theorem finite_setOf_order_le (k : ℕ) : {α : MultiIndex n | α.order ≤ k}.Finite := by
  refine (Set.finite_range fun (β : Fin n → Fin 4 → Fin (k + 1)) (i : Fin n) (μ : Fin 4) =>
    (β i μ : ℕ)).subset ?_
  intro α hα
  refine ⟨fun i μ => ⟨α i μ, Nat.lt_succ_of_le ?_⟩, rfl⟩
  calc α i μ ≤ ∑ ν, α i ν :=
        Finset.single_le_sum (f := fun ν => α i ν) (fun _ _ => Nat.zero_le _) (Finset.mem_univ μ)
    _ ≤ ∑ j, ∑ ν, α j ν :=
        Finset.single_le_sum (f := fun j => ∑ ν, α j ν) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
    _ ≤ k := hα
theorem continuous_euclidNorm : Continuous (euclidNorm (n := n)) := by apply _root_.YangMills.Construction.TestSpaces.SchwartzTruncation.continuous_tupleNorm <;> assumption
theorem schwartzSeminorm_lt_top {φ : Config n → ℂ} (hs : ContDiff ℝ ∞ φ)
    (hc : IsCompact (tsupport φ))
    (hz : ∀ (α : MultiIndex n), ∀ x, x ∉ tsupport φ → iteratedPartial α φ x = 0) (k : ℕ) :
    schwartzSeminorm k φ < ⊤ := by
  have bound : ∀ α : MultiIndex n, ∃ C : ℝ, ∀ x : Config n,
      (1 + euclidNorm x ^ 2) ^ ((k : ℝ) / 2) * ‖iteratedPartial α φ x‖ ≤ C := by
    intro α
    have hcont : Continuous fun x : Config n =>
        (1 + euclidNorm x ^ 2) ^ ((k : ℝ) / 2) * ‖iteratedPartial α φ x‖ :=
      ((continuous_const.add (continuous_euclidNorm.pow 2)).rpow_const
        fun _ => Or.inr (by positivity)).mul (contDiff_iteratedPartial α hs).continuous.norm
    have hsupp : HasCompactSupport fun x : Config n =>
        (1 + euclidNorm x ^ 2) ^ ((k : ℝ) / 2) * ‖iteratedPartial α φ x‖ :=
      HasCompactSupport.intro hc fun x hx => by simp [hz α x hx]
    obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hcont
    exact ⟨C, fun x => (le_abs_self _).trans (hC x)⟩
  choose C hC using bound
  obtain ⟨B, hB⟩ := ((finite_setOf_order_le (n := n) k).image C).bddAbove
  refine lt_of_le_of_lt (b := ENNReal.ofReal B) ?_ ENNReal.ofReal_lt_top
  exact iSup_le fun x => iSup_le fun α => iSup_le fun hα =>
    ENNReal.ofReal_le_ofReal ((hC α x).trans (hB (Set.mem_image_of_mem C hα)))
theorem isSchwartz_and_flatOff (hflat : VanishingOnOpenProperties) (hn : 1 ≤ n)
    {V : Set (Config n)} (hV : IsOpen V) {φ : Config n → ℂ} (hφ : φ ∈ smoothCompactSupportIn V) :
    IsSchwartz φ ∧ FlatOff φ V := by
  obtain ⟨-, hs, hc, hsub⟩ := hφ
  have hW : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
  have hz : ∀ x ∈ (tsupport φ)ᶜ, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hcl : FlatOn φ (closure (tsupport φ)ᶜ) := (hflat n hn).1 _ φ hW hs hz
  have hat : ∀ x, x ∉ tsupport φ → FlatAt φ x := fun x hx => hcl.2 x (subset_closure hx)
  exact ⟨⟨hs, fun k _ => schwartzSeminorm_lt_top hs hc (fun α x hx => (hat x hx).2 α) k⟩, hs, hV,
    fun x hx => hat x fun h => hx (hsub h)⟩
variable {f : Fin n → (Fin 4 → ℝ) → ℝ}
theorem contDiff_tensorRealFamily (hsm : AllSmoothCompact f) :
    ContDiff ℝ ∞ (tensorRealFamily f) := by
  unfold tensorRealFamily tensorFamily
  refine contDiff_prod fun i _ => ?_
  have hf := (mem_realSmoothCompactIn_iff.1 (hsm i)).2.1
  exact Complex.ofRealCLM.contDiff.comp (hf.comp (contDiff_apply ℝ (Fin 4 → ℝ) i))
theorem tsupport_tensorRealFamily_subset (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    tsupport (tensorRealFamily f) ⊆ Set.pi Set.univ fun i => tsupport (f i) := by
  refine closure_minimal ?_ (isClosed_set_pi fun i _ => isClosed_tsupport _)
  intro x hx i _
  refine subset_tsupport _ (Function.mem_support.2 fun h0 => hx ?_)
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])
theorem tensorRealFamily_mem_distinctArgs (hf : f ∈ separatedFamilies Set.univ n)
    (hsm : AllSmoothCompact f) :
    tensorRealFamily f ∈ smoothCompactSupportIn (distinctArgs n) := by
  refine ⟨isOpen_distinctArgs, contDiff_tensorRealFamily hsm, ?_, ?_⟩
  · exact IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun i => (mem_realSmoothCompactIn_iff.1 (hsm i)).2.2.1)
      (isClosed_tsupport _) (tsupport_tensorRealFamily_subset f)
  · intro x hx i j e
    by_contra hij
    have hi := tsupport_tensorRealFamily_subset f hx i (Set.mem_univ i)
    have hj := tsupport_tensorRealFamily_subset f hx j (Set.mem_univ j)
    rw [e] at hi
    exact Set.disjoint_left.1 (hf.2 hij) hi hj
theorem tensorRealFamily_mem_posTimeSet (hf : f ∈ separatedFamilies Set.univ n)
    (hsm : AllSmoothCompact f)
    (hpos : ∀ i, tsupport (f i) ⊆ upperHalfSpace) :
    tensorRealFamily f ∈ smoothCompactSupportIn (posTimeSet n) := by
  obtain ⟨-, hs, hc, hsub⟩ := tensorRealFamily_mem_distinctArgs hf hsm
  refine ⟨isOpen_posTimeSet, hs, hc, fun x hx => ⟨hsub hx, fun i => ?_⟩⟩
  exact hpos i (tsupport_tensorRealFamily_subset f hx i (Set.mem_univ i))
theorem motionAct_tensorRealFamily (f : Fin n → (Fin 4 → ℝ) → ℝ) (r : EuclidMotion) :
    motionAct r (tensorRealFamily f) =
      tensorRealFamily fun i => f i ∘ r.invMap :=
  rfl
theorem permAct_tensorRealFamily (f : Fin n → (Fin 4 → ℝ) → ℝ) (ς : Equiv.Perm (Fin n)) :
    permAct ς (tensorRealFamily f) =
      tensorRealFamily fun j => f (ς.symm j) := by
  funext x
  show ∏ i, ((f i (x (ς i)) : ℝ) : ℂ) = ∏ j, ((f (ς.symm j) (x j) : ℝ) : ℂ)
  rw [← Equiv.prod_comp ς fun j => ((f (ς.symm j) (x j) : ℝ) : ℂ)]
  simp
theorem flipConj_tensorRealFamily (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    flipConj (tensorRealFamily f) =
      tensorRealFamily fun i => f i ∘ timeFlip := by
  funext x
  show conj (∏ i, ((f i (timeFlip (x i)) : ℝ) : ℂ)) =
    ∏ i, (((f i ∘ timeFlip) (x i) : ℝ) : ℂ)
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => Complex.conj_ofReal _
theorem compactSupportTensorFacts_of_vanishing (hflat : VanishingOnOpenProperties) :
    CompactSupportTensorFacts := by
  intro n hn
  have hall : ∀ V : Set (Config n), IsOpen V → ∀ φ ∈ smoothCompactSupportIn V,
      IsSchwartz φ ∧ FlatOff φ V :=
    fun V hV φ hφ => isSchwartz_and_flatOff hflat hn hV hφ
  exact ⟨hall, fun φ hφ => hall _ isOpen_distinctArgs φ hφ,
    fun φ hφ => hall _ isOpen_posTimeSet φ hφ, fun φ hφ => hall _ isOpen_negTimeSet φ hφ,
    fun f hf hsm => ⟨tensorRealFamily_mem_distinctArgs hf hsm, tensorRealFamily_mem_posTimeSet hf hsm⟩,
    fun f _ => ⟨motionAct_tensorRealFamily f, permAct_tensorRealFamily f, flipConj_tensorRealFamily f⟩⟩
end YangMills.Construction.ConfigSpace.TensorSupport
end
