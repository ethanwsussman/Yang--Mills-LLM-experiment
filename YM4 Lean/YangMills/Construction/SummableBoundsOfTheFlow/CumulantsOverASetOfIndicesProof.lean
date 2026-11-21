import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfSumsWithMoments
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOverASetOfIndices
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfTheMeanOfAPartProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SetIndexedCumulants
open Set Filter Topology MeasureTheory
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.Cumulants YangMills.Construction.Interpolation YangMills.Construction.ConvexObservables
section Reindexing
variable {Ω α β : Type} [DecidableEq α] [DecidableEq β] [Fintype β]
def finpartitionMap (f : β ↪ α) (π : Finpartition (Finset.univ : Finset β)) :
    Finpartition ((Finset.univ : Finset β).map f) :=
  Finpartition.ofExistsUnique (π.parts.image (Finset.map f))
    (fun p hp => by
      obtain ⟨J, -, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.map_subset_map.mpr (Finset.subset_univ _))
    (fun a ha => by
      obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨t, ⟨ht, hb⟩, hu⟩ := π.existsUnique_mem (Finset.mem_univ b)
      refine ⟨t.map f, ⟨Finset.mem_image_of_mem _ ht, Finset.mem_map_of_mem _ hb⟩, ?_⟩
      rintro u ⟨hu', ha'⟩
      obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hu'
      have hb' : b ∈ J := (Finset.mem_map' f).mp ha'
      rw [hu J ⟨hJ, hb'⟩])
    (fun h => by
      obtain ⟨J, hJ, hJ0⟩ := Finset.mem_image.mp h
      have hne := π.nonempty_of_mem_parts hJ
      rw [Finset.map_eq_empty] at hJ0
      exact hne.ne_empty hJ0)
theorem finpartitionMap_parts (f : β ↪ α) (π : Finpartition (Finset.univ : Finset β)) :
    (finpartitionMap f π).parts = π.parts.image (Finset.map f) := by
  simp [finpartitionMap, Finpartition.ofExistsUnique]
theorem finpartitionMap_bijective (f : β ↪ α) : Function.Bijective (finpartitionMap f) := by
  constructor
  · intro π π' h
    have h1 := congrArg Finpartition.parts h
    rw [finpartitionMap_parts, finpartitionMap_parts] at h1
    have h2 := Finset.image_injective (Finset.map_injective f) h1
    exact Finpartition.ext h2
  · intro π'
    have hback : ∀ J ∈ π'.parts, (Finset.univ.filter fun b => f b ∈ J).map f = J := by
      intro J hJ
      ext a
      constructor
      · intro ha
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
        simpa using hb
      · intro ha
        have h1 : a ∈ (Finset.univ : Finset β).map f := π'.le hJ ha
        obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp h1
        exact Finset.mem_map_of_mem _ (by simpa using ha)
    refine ⟨Finpartition.ofExistsUnique (π'.parts.image fun J => Finset.univ.filter fun b => f b ∈ J)
      (fun _ _ => Finset.subset_univ _) (fun b _ => ?_) (fun h => ?_), ?_⟩
    · obtain ⟨t, ⟨ht, hb⟩, hu⟩ := π'.existsUnique_mem (Finset.mem_map_of_mem f (Finset.mem_univ b))
      refine ⟨Finset.univ.filter fun b => f b ∈ t, ⟨Finset.mem_image_of_mem _ ht, by simpa using hb⟩, ?_⟩
      rintro u ⟨hu', hb'⟩
      obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hu'
      have h1 : f b ∈ J := by simpa using hb'
      rw [hu J ⟨hJ, h1⟩]
    · obtain ⟨J, hJ, hJ0⟩ := Finset.mem_image.mp h
      have h1 := hback J hJ
      rw [hJ0] at h1
      simp at h1
      exact (π'.nonempty_of_mem_parts hJ).ne_empty h1.symm
    · apply Finpartition.ext
      rw [finpartitionMap_parts]
      simp only [Finpartition.ofExistsUnique]
      ext J
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨J', hJ', rfl⟩, rfl⟩
        rw [hback J' hJ']
        exact hJ'
      · intro hJ
        exact ⟨_, ⟨J, hJ, rfl⟩, hback J hJ⟩
theorem jointCumulant_map (m : (Ω → ℝ) → ℝ) (f : β ↪ α) (X : α → Ω → ℝ) :
    jointCumulant m ((Finset.univ : Finset β).map f) X = jointCumulant m (Finset.univ : Finset β) fun b => X (f b) := by
  unfold jointCumulant
  rw [← (Fintype.sum_bijective (finpartitionMap f) (finpartitionMap_bijective f) _ _ fun _ => rfl)]
  refine Finset.sum_congr rfl fun π _ => ?_
  have hinj : Function.Injective (Finset.map f) := Finset.map_injective f
  rw [finpartitionMap_parts, Finset.card_image_of_injective _ hinj, Finset.prod_image fun a _ b _ h => hinj h]
  congr 1
  refine Finset.prod_congr rfl fun J _ => ?_
  congr 1
  funext ω
  simp [blockProd]
end Reindexing
open Classical in
def SummedCumulantBound (N N' : ℕ) (κ lam : ℝ) (M : ℕ) (B : (ℕ → ℝ) → ℝ) : Prop :=
  ∀ (F : BlockFrame) (ι : Type) [Fintype ι] [DecidableEq ι] (y : ι → F.Cell) (ρ x : ℝ) (p : ℝ → ℝ)
    (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (Q : Type) [Fintype Q] (z : Q → F.Cell)
    (P : Fin M → Q → Prop) (O : Fin M → Q → BondField ι → ℝ) (e : Fin M → Q → ℝ)
    (A : Fin M → ℝ) (Cq : ℕ → ℝ) (r₀ n : ℝ) (Y₀ : F.Cell) (i₀ : Fin M),
    0 < ρ → 0 < x → IsCutoff ρ p → (∀ w, (Finset.univ.filter fun b => y b = w).card ≤ N) →
    IsUniformlyConvexDecaying ρ (x * lam / 4) κ (fun b b' => (cellSupDist (y b) (y b') : ℝ)) Ψ K →
    (∀ (b : ι) (u : BondVector), |bondPartialDeriv Ψ b 0 u| ≤ Real.sqrt (x * lam / 4) * ‖u‖) →
    Integrable (ballDensity (cutoffFactor ρ p) Ψ) →
    (∀ q, 0 ≤ Cq q) → (∀ i, 0 ≤ A i) → (∀ i q, 0 ≤ e i q) → κ / 16 ≤ r₀ →
    (∀ i, ∃ q, P i q) → (∀ u : F.Cell, (Finset.univ.filter fun q => z q = u).card ≤ N') →
    (∀ q, P i₀ q → z q = Y₀) →
    (∀ i q, P i q → ContDiffOn ℝ 1 (O i q) {η | ∀ b, ‖η b‖ < ρ}) →
    (∀ i q, P i q → ∀ m : ℕ, 1 ≤ m → Integrable fun η => |O i q η| ^ m * ballDensity (cutoffFactor ρ p) Ψ η) →
    (∀ i q, P i q → HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ (A i * Real.exp (-(r₀ * e i q)))
      (fun b => (cellSupDist (y b) (z q) : ℝ)) (O i q)) →
    (∀ s : Fin M → Q, (∀ i, P i (s i)) →
      n ≤ (cellsDiameter fun i => z (s i)) + ∑ i, e i (s i)) →
    |cumulantFromMoments (cutoffFactor ρ p) Ψ fun i η => ∑ q ∈ Finset.univ.filter (P i), O i q η| ≤
      B Cq * (∏ i, A i) * Real.exp (-(κ / 16 * n))
theorem cellSupDist_le_cellsDiameter {F : BlockFrame} {M : ℕ} (Z : Fin M → F.Cell) (i j : Fin M) :
    cellSupDist (Z i) (Z j) ≤ cellsDiameter Z := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.cellSupDist_le_cellsDiameter <;> assumption
open Classical in
theorem jointCumulant_finset_bound {N N' : ℕ} {κ lam : ℝ} {B : (ℕ → ℝ) → ℝ} {α : Type} [DecidableEq α] (S : Finset α) (a₀ : α)
    (ha₀ : a₀ ∈ S) (hB : SummedCumulantBound N N' κ lam S.card B) {F : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι]
    (y : ι → F.Cell) {ρ x : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} {K : ι → ι → ℝ} {Q : Type} [Fintype Q]
    (z : Q → F.Cell) (P : α → Q → Prop) (O : α → Q → BondField ι → ℝ) (e : α → Q → ℝ) (A : α → ℝ) {Cq : ℕ → ℝ}
    {r₀ n : ℝ} (hρ : 0 < ρ) (hx : 0 < x) (hp : IsCutoff ρ p) (hy : ∀ w, (Finset.univ.filter fun b => y b = w).card ≤ N)
    (hconv : IsUniformlyConvexDecaying ρ (x * lam / 4) κ (fun b b' => (cellSupDist (y b) (y b') : ℝ)) Ψ K)
    (hslope : ∀ (b : ι) (u : BondVector), |bondPartialDeriv Ψ b 0 u| ≤ Real.sqrt (x * lam / 4) * ‖u‖)
    (hint : Integrable (ballDensity (cutoffFactor ρ p) Ψ)) (hCq : ∀ q, 0 ≤ Cq q) (hA : ∀ a ∈ S, 0 ≤ A a)
    (he : ∀ a ∈ S, ∀ q, 0 ≤ e a q) (hr : κ / 16 ≤ r₀) (hne : ∀ a ∈ S, ∃ q, P a q)
    (hz : ∀ u : F.Cell, (Finset.univ.filter fun q => z q = u).card ≤ N') {Y₀ : F.Cell} (hanchor : ∀ q, P a₀ q → z q = Y₀)
    (hC1 : ∀ a ∈ S, ∀ q, P a q → ContDiffOn ℝ 1 (O a q) {η | ∀ b, ‖η b‖ < ρ})
    (hmom : ∀ a ∈ S, ∀ q, P a q → ∀ m : ℕ, 1 ≤ m → Integrable fun η => |O a q η| ^ m * ballDensity (cutoffFactor ρ p) Ψ η)
    (hsize : ∀ a ∈ S, ∀ q, P a q → HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ (A a * Real.exp (-(r₀ * e a q)))
      (fun b => (cellSupDist (y b) (z q) : ℝ)) (O a q))
    (hreach : ∀ (s : α → Q) (D : ℕ), (∀ a ∈ S, P a (s a)) → (∀ a ∈ S, ∀ b ∈ S, cellSupDist (z (s a)) (z (s b)) ≤ D) →
      n ≤ D + ∑ a ∈ S, e a (s a)) :
    |jointCumulant (ballExpectation (cutoffFactor ρ p) Ψ) S fun a η => ∑ q ∈ Finset.univ.filter (P a), O a q η| ≤
      B Cq * (∏ a ∈ S, A a) * Real.exp (-(κ / 16 * n)) := by
  set E : Fin S.card ≃ ↥S := S.equivFin.symm with hE
  set f : Fin S.card ↪ α := E.toEmbedding.trans (Function.Embedding.subtype _) with hf
  have hfS : ∀ i, f i ∈ S := fun i => (E i).2
  have hmap : (Finset.univ : Finset (Fin S.card)).map f = S := by
    ext a
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact hfS i
    · intro ha
      exact ⟨E.symm ⟨a, ha⟩, by simp [hf]⟩
  have hsum : ∀ (g : α → ℝ), ∑ a ∈ S, g a = ∑ i, g (f i) := fun g => by
    conv_lhs => rw [← hmap]
    rw [Finset.sum_map]
  have hprod : ∀ (g : α → ℝ), ∏ a ∈ S, g a = ∏ i, g (f i) := fun g => by
    conv_lhs => rw [← hmap]
    rw [Finset.prod_map]
  have hcum := jointCumulant_map (ballExpectation (cutoffFactor ρ p) Ψ) f
    (fun a η => ∑ q ∈ Finset.univ.filter (P a), O a q η)
  rw [hmap] at hcum
  rw [hcum, hprod]
  set i₀ : Fin S.card := E.symm ⟨a₀, ha₀⟩ with hi₀
  have hf₀ : f i₀ = a₀ := by simp [hf, hi₀]
  have key := hB F ι y ρ x p Ψ K Q z (fun i => P (f i)) (fun i => O (f i)) (fun i => e (f i)) (fun i => A (f i)) Cq r₀ n Y₀ i₀
    hρ hx hp hy hconv hslope hint hCq (fun i => hA _ (hfS i)) (fun i q => he _ (hfS i) q) hr (fun i => hne _ (hfS i)) hz
    (fun q h => hanchor q (hf₀ ▸ h)) (fun i q h => hC1 _ (hfS i) q h) (fun i q h => hmom _ (hfS i) q h)
    (fun i q h => hsize _ (hfS i) q h)
    (fun s hs => by
      set s' : α → Q := fun a => if h : a ∈ S then s (E.symm ⟨a, h⟩) else s i₀ with hs'
      have hss : ∀ i, s' (f i) = s i := fun i => by
        have h : f i ∈ S := hfS i
        simp only [hs', h, dite_true]
        congr 1
        simp [hf]
      have h1 := hreach s' (cellsDiameter fun i => z (s i))
        (fun a ha => by
          have h2 := hs (E.symm ⟨a, ha⟩)
          have h3 : f (E.symm ⟨a, ha⟩) = a := by simp [hf]
          simp only [h3] at h2
          simpa [hs', ha] using h2)
        (fun a ha b hb => by
          simp only [hs', ha, hb, dite_true]
          exact cellSupDist_le_cellsDiameter (fun i => z (s i)) _ _)
      rw [hsum] at h1
      simp only [hss] at h1
      exact h1)
  refine le_trans (le_of_eq ?_) key
  congr 1
theorem setIndexedCumulantBound_of_summed (hC : summedObservableCumulantBound) :
    setIndexedCumulantBoundStatement := by
  intro N N' κ lam hκ hlam
  have hBex := fun (M : ℕ) (h2 : 2 ≤ M) (h9 : M ≤ 9) => hC N N' κ lam M hκ hlam h2 h9
  choose! B hBn hB using hBex
  refine ⟨B, hBn, ?_⟩
  intro α _ S a₀ F ι _ _ y ρ x p Ψ K Q _ z P O e A Cq r₀ n Y₀ ha₀ h2 h9 hρ hx hp hy hconv hslope hint hCq hA he hr hne hz hanchor hC1 hmom
    hsize hreach
  exact jointCumulant_finset_bound S a₀ ha₀ (hB S.card h2 h9) y z P O e A hρ hx hp hy hconv hslope hint hCq hA he hr hne hz hanchor hC1 hmom hsize
    hreach
end YangMills.Construction.SetIndexedCumulants
end
