module

public import NoContact.Localization

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology ContDiff

namespace NoContact

/-- For at most one slot, locality and compact approximation imply vanishing. -/
theorem subsingleton_zero {ι : Type} [Subsingleton ι]
    {U : Set X} (hU : IsOpen U) (D : Form ι) (hlocal : Local U D)
    (f : ι → L2) (hf : ∀ i, Supported U (f i)) : D f = 0 := by
  classical
  refine continuous_zero_of_compact (fun _ : ι => U) (fun _ => hU.measurableSet)
    D D.cont ?_ f hf
  intro g hg
  choose K hK hKU hgK using hg
  exact hlocal K hK hKU (fun i j hij => (hij (Subsingleton.elim i j)).elim) g hgK

/-- Prove no-contact by strong induction on arity, simultaneously for all open sets. -/
theorem ambient_by_card (n : ℕ) :
    ∀ (ι : Type) [Fintype ι], Fintype.card ι = n → 0 < n →
      ∀ (U : Set X), IsOpen U → ∀ (D : Form ι), Local U D → GradientZero U D →
        ∀ f : ι → L2, (∀ i, Supported U (f i)) → D f = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ι _ hcard hpos U hU D hlocal hgrad f hf
    by_cases hsmall : Fintype.card ι ≤ 1
    · let : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hsmall
      exact subsingleton_zero hU D hlocal f hf
    · have hlarge : 1 < Fintype.card ι := by omega
      have hbelow : KnownBelow (Fintype.card ι) := by
        intro κ _ hκpos hκlt V hV B hBl hBg g hg
        exact ih (Fintype.card κ) (by omega) κ rfl hκpos V hV B hBl hBg g hg
      exact zero_of_splitZero hlarge hU D
        (splitZero_of_lower hlarge hbelow hU D hlocal hgrad) hgrad f hf

/-- The no-contact theorem on ambient `L²` fields supported in `U`. -/
theorem ambient_no_contact {ι : Type} [Fintype ι] (hpos : 0 < Fintype.card ι)
    {U : Set X} (hU : IsOpen U) (D : Form ι) (hlocal : Local U D)
    (hgrad : GradientZero U D) (f : ι → L2) (hf : ∀ i, Supported U (f i)) : D f = 0 :=
  ambient_by_card (Fintype.card ι) ι rfl hpos U hU D hlocal hgrad f hf

/-- Projection from ambient fields to the zero-extension subspace. -/
def projectU (U : Set X) (hU : MeasurableSet U) : L2 →L[ℂ] L2U U :=
  (cutCLM U hU).codRestrict (l2Submodule U) (cut_supported U hU)

/-- The projection to `L²(U)` is multiplication by its indicator. -/
@[simp] theorem projectU_coe (U : Set X) (hU : MeasurableSet U) (f : L2) :
    (projectU U hU f : L2) = cut U hU f := rfl

/-- Projection fixes every field already in `L²(U)`. -/
@[simp] theorem projectU_subtype (U : Set X) (hU : MeasurableSet U) (f : L2U U) :
    projectU U hU (f : L2) = f := by
  apply Subtype.ext
  exact cut_eq_self hU f.property

/-- **QED3 `prop:rotation-no-contact`.** A bounded complex-multilinear form on
`L²(U; ℂ³)`, extended by zero, vanishes if it vanishes on pairwise disjoint
compact essential supports and whenever any entry is the gradient of a real
smooth compactly supported potential in `U`. -/
theorem rotation_no_contact {N : ℕ} (hN : 1 ≤ N) {U : Set X} (hU : IsOpen U)
    (D : ContinuousMultilinearMap ℂ (fun _ : Fin N => L2U U) ℂ)
    (hlocal : ∀ K : Fin N → Set X, (∀ i, IsCompact (K i)) → (∀ i, K i ⊆ U) →
      Pairwise (fun i j => Disjoint (K i) (K j)) →
      ∀ f : Fin N → L2U U, (∀ i, Supported (K i) (f i : L2)) → D f = 0)
    (hgrad : ∀ (i : Fin N) (u : Potential U) (f : Fin N → L2U U),
      f i = u.gradientL2U → D f = 0) : D = 0 := by
  classical
  let A : Form (Fin N) := D.compContinuousLinearMap (fun _ => projectU U hU.measurableSet)
  have hAlocal : Local U A := by
    intro K hK hKU hdis f hf
    apply hlocal K hK hKU hdis (fun i => projectU U hU.measurableSet (f i))
    intro i
    simpa [projectU_coe, cut_eq_self hU.measurableSet ((hf i).mono (hKU i))] using hf i
  have hAgrad : GradientZero U A := by
    intro i u f hf hfi
    apply hgrad i u (fun j => projectU U hU.measurableSet (f j))
    apply Subtype.ext
    change cut U hU.measurableSet (f i) = u.gradientLp
    rw [cut_eq_self hU.measurableSet (hf i), hfi]
  ext f
  have hz := ambient_no_contact
    (by simpa only [Fintype.card_fin] using (Nat.zero_lt_of_lt hN)) hU A hAlocal hAgrad
    (fun i => (f i : L2)) (fun i => (f i).property)
  simpa [A, ContinuousMultilinearMap.compContinuousLinearMap_apply] using hz

end NoContact

#print axioms NoContact.rotation_no_contact
