import YangMills.Construction.Matrices.RealPolynomialsOfADisjointUnionOfIndexSets
import YangMills.Construction.TransferOperators.PolynomialsOfTheNextSymmetricStackDecompose
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics
noncomputable section
namespace YangMills.Construction.TransferOperators.CenteredStack
variable {μ : Fin 4}
theorem isRealEntryPolynomial_comp {A B : Type} (φ : A → B)
    {g : (A → Matrices.ComplexMatrix2.specialUnitary) → ℂ} (hg : IsRealEntryPolynomial g) :
    IsRealEntryPolynomial fun x : B → Matrices.ComplexMatrix2.specialUnitary => g fun a => x (φ a) := by
  obtain ⟨⟨p, hp⟩, hr⟩ := hg
  refine ⟨⟨MvPolynomial.rename (Sum.map (Prod.map φ id) (Prod.map φ id)) p, fun x => ?_⟩,
    fun x => hr _⟩
  have hev : entryEval (fun a => x (φ a)) =
      entryEval x ∘ Sum.map (Prod.map φ id) (Prod.map φ id) := by
    funext y
    rcases y with ⟨c, i, j⟩ | ⟨c, i, j⟩ <;> rfl
  show g (fun a => x (φ a)) = _
  rw [MvPolynomial.eval_rename, hp, hev]
theorem mem_centeredLinkPairs_of {i k j : ℤ} {v : Set (SliceSite μ)} {l : SliceLink μ}
    (hlo : i - k + 1 ≤ j) (hhi : j ≤ i + k) (hl : l ∈ linksWithin v) :
    (j, l) ∈ centeredLinkPairs i k v :=
  ⟨hlo, hhi, hl⟩
theorem centeredLinkPairs_finite (i k : ℤ) {v : Set (SliceSite μ)}
    (h : (linksWithin v).Finite) : (centeredLinkPairs i k v).Finite :=
  ((Set.finite_Icc (i - k + 1) (i + k)).prod h).subset fun _ hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩
def sliceSector (i k j : ℤ) : Fin 3 :=
  if j = i - k then 0 else if j = i + k + 1 then 1 else 2
theorem eq_of_sliceSector_eq_zero {i k j : ℤ} (h : sliceSector i k j = 0) : j = i - k := by
  unfold sliceSector at h
  split_ifs at h with h₁ h₂
  · exact h₁
  · exact absurd h (by decide)
  · exact absurd h (by decide)
theorem eq_of_sliceSector_eq_one {i k j : ℤ} (h : sliceSector i k j = 1) : j = i + k + 1 := by
  unfold sliceSector at h
  split_ifs at h with h₁ h₂
  · exact absurd h (by decide)
  · exact h₂
  · exact absurd h (by decide)
theorem ne_of_sliceSector_eq_two {i k j : ℤ} (h : sliceSector i k j = 2) :
    j ≠ i - k ∧ j ≠ i + k + 1 := by
  unfold sliceSector at h
  split_ifs at h with h₁ h₂
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact ⟨h₁, h₂⟩
theorem sliceSector_bottom (i k : ℤ) : sliceSector i k (i - k) = 0 := if_pos rfl
theorem sliceSector_top (i k : ℤ) : sliceSector i k (i + k + 1) = 1 := by
  unfold sliceSector
  rw [if_neg (by omega), if_pos rfl]
theorem sliceSector_interior {i k : ℤ} (hk : 1 ≤ k) : sliceSector i k (i + k) = 2 := by
  unfold sliceSector
  rw [if_neg (by omega), if_neg (by omega)]
theorem polynomialSplit_holds (hUnion : AllRealPolyDisjointUnionSplit) :
    PolynomialSplitStatement := by
  intro μ D v₀ _ hv hb Ψ hΨ
  have hk := D.one_le_halfWidth
  obtain ⟨l₀, hl₀⟩ := D.block.links_nonempty
  have hl₀' : l₀ ∈ linksWithin v₀ := hb ▸ Finset.mem_coe.2 hl₀
  have hfin : (linksWithin v₀).Finite := hb ▸ D.block.links.finite_toSet
  have hJ : Finite (centeredLinkPairs D.center (D.halfWidth + 1) v₀) :=
    (centeredLinkPairs_finite _ _ hfin).to_subtype
  have hmem : ∀ j : ℤ, D.center - D.halfWidth ≤ j → j ≤ D.center + D.halfWidth + 1 →
      (j, l₀) ∈ centeredLinkPairs D.center (D.halfWidth + 1) v₀ :=
    fun j h₁ h₂ => mem_centeredLinkPairs_of (by omega) (by omega) hl₀'
  have hJ' : Nonempty (centeredLinkPairs D.center (D.halfWidth + 1) v₀) :=
    ⟨⟨_, hmem D.center (by omega) (by omega)⟩⟩
  obtain ⟨m, g, hg, e⟩ := hUnion (centeredLinkPairs D.center (D.halfWidth + 1) v₀) 3
    (fun ρ => {p | sliceSector D.center D.halfWidth p.1.1 = ρ})
    (fun ρ => by
      fin_cases ρ
      · exact ⟨⟨_, hmem (D.center - D.halfWidth) (by omega) (by omega)⟩,
          sliceSector_bottom _ _⟩
      · exact ⟨⟨_, hmem (D.center + D.halfWidth + 1) (by omega) (by omega)⟩,
          sliceSector_top _ _⟩
      · exact ⟨⟨_, hmem (D.center + D.halfWidth) (by omega) (by omega)⟩,
          sliceSector_interior hk⟩)
    (fun ρ σ hρσ => Set.disjoint_left.2 fun p h₁ h₂ => hρσ (h₁.symm.trans h₂))
    (Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 ⟨_, rfl⟩) Ψ hΨ
  let linkOf : centeredLinkPairs D.center (D.halfWidth + 1) v₀ → D.block.links :=
    fun p => ⟨p.1.2, Finset.mem_coe.1 (hb ▸ p.2.2.2)⟩
  let innerOf : {p : centeredLinkPairs D.center (D.halfWidth + 1) v₀ |
      sliceSector D.center D.halfWidth p.1.1 = 2} → D.InnerPairs :=
    fun p => ⟨p.1.1, by
      have h := ne_of_sliceSector_eq_two p.2
      have h₁ := p.1.2.1
      have h₂ := p.1.2.2.1
      exact ⟨by omega, by omega, hv p.1.2.2.2.1, hv p.1.2.2.2.2⟩⟩
  refine ⟨m, fun α x => g α 0 fun p => x (linkOf p.1), fun α x => g α 1 fun p => x (linkOf p.1),
    fun α => ⟨fun u => g α 2 fun p => u (innerOf p),
      (hg α 2).1.continuous.comp (continuous_pi fun p => continuous_apply (innerOf p))⟩,
    fun α => isRealEntryPolynomial_comp _ (hg α 0), fun α => isRealEntryPolynomial_comp _ (hg α 1),
    fun α => isRealEntryPolynomial_comp innerOf (hg α 2), fun w => ?_⟩
  rw [e]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Fin.prod_univ_three]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg (g α 0) ?_) (congrArg (g α 1) ?_)) rfl
  · funext p
    exact congrArg w (Prod.ext (eq_of_sliceSector_eq_zero p.2) rfl)
  · funext p
    exact congrArg w (Prod.ext (eq_of_sliceSector_eq_one p.2) rfl)
end YangMills.Construction.TransferOperators.CenteredStack
end
