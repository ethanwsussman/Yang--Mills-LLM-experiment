import YangMills.Construction.InfiniteLattice.FactsOfTheSignsAtACutoffProof
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.ReflectionPositivity.ObservableAsAFunctionOfTheConfiguration
import YangMills.Construction.ReflectionPositivity.TwoFunctionalsOnSeparatedTuples
import YangMills.Construction.TorusOrFourSpace.FiniteCoversByBallsAndPartitionsOfUnityProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.SeparatedFunctionals
section Distance
open MetricNotions
variable {X : Type*} {d : X → X → ℝ}
theorem isOpenWrt_compl_closureWrt (tri : ∀ x y z, d x z ≤ d x y + d y z) (W : Set X) :
    IsOpenWrt d (closureWrt d W)ᶜ := by apply _root_.YangMills.Construction.PeriodicSpace.BallCoverProof.isOpenWrt_compl_closureWrt <;> assumption
theorem isCompactWrt_union {A B : Set X} (hA : IsCompactWrt d A) (hB : IsCompactWrt d B) :
    IsCompactWrt d (A ∪ B) := by apply _root_.YangMills.SharedProofs.p57694 <;> assumption
theorem isCompactWrt_of_subset {Z K : Set X} (hO : IsOpenWrt d Zᶜ) (hK : IsCompactWrt d K)
    (hZ : Z ⊆ K) : IsCompactWrt d Z := by
  intro 𝒰 ho hc
  obtain ⟨𝒰', hs, hf, hcov⟩ := hK (insert Zᶜ 𝒰)
    (by
      rintro U (rfl | hU)
      · exact hO
      · exact ho U hU)
    (by
      intro x _
      by_cases hxZ : x ∈ Z
      · obtain ⟨U, hU, hxU⟩ := hc hxZ
        exact ⟨U, Or.inr hU, hxU⟩
      · exact ⟨Zᶜ, Or.inl rfl, hxZ⟩)
  refine ⟨𝒰' \ {Zᶜ}, ?_, hf.sdiff, ?_⟩
  · rintro U ⟨hU, hne⟩
    exact (hs hU).resolve_left hne
  · intro x hx
    obtain ⟨U, hU, hxU⟩ := hcov (hZ hx)
    refine ⟨U, ⟨hU, ?_⟩, hxU⟩
    intro h
    rw [mem_singleton_iff] at h
    subst h
    exact hxU hx
end Distance
section Spaces
variable (D : MirrorData)
theorem metric_triangle (E : Ambient) (x y z : E.Point D) :
    Ambient.metric D E x z ≤ Ambient.metric D E x y + Ambient.metric D E y z := by
  cases E with
  | torus => exact AmbientPoints.torusEuclidNorm_sub_le x y z
  | euclidean => exact AmbientPoints.euclidNormVec_sub_le x y z
variable {D} {E : Ambient}
theorem isC1_linComb {f g : E.Point D → ℝ} (hf : Ambient.IsC1 D E f)
    (hg : Ambient.IsC1 D E g) (s t : ℝ) : Ambient.IsC1 D E (s • f + t • g) := by apply _root_.YangMills.Construction.AtCutoff.SignFacts.isC1_linComb <;> assumption
theorem closedSupport_linComb_subset (f g : E.Point D → ℝ) (s t : ℝ) :
    Ambient.closedSupport D E (s • f + t • g) ⊆
      Ambient.closedSupport D E f ∪ Ambient.closedSupport D E g := by apply _root_.YangMills.Construction.AtCutoff.SignFacts.closedSupport_linComb_subset <;> assumption
theorem linComb_mem_compactC1SuppIn {A : Set (E.Point D)} {f g : E.Point D → ℝ}
    (hf : f ∈ Ambient.compactC1SuppIn D E A) (hg : g ∈ Ambient.compactC1SuppIn D E A) (s t : ℝ) :
    s • f + t • g ∈ Ambient.compactC1SuppIn D E A := by
  have hs := closedSupport_linComb_subset f g s t
  refine ⟨⟨isC1_linComb hf.1.1 hg.1.1 s t, ?_⟩,
    hs.trans (union_subset hf.2 hg.2)⟩
  exact isCompactWrt_of_subset (isOpenWrt_compl_closureWrt (metric_triangle D E) _)
    (isCompactWrt_union hf.1.2 hg.1.2) hs
theorem evalOrZero_restrictN {σ : Ambient.separatedAll D E → ℝ} {n : ℕ}
    {Y : Ambient.FnList D E} (hY : Y ∈ Ambient.separatedN D E n) :
    Ambient.evalOrZero (Ambient.restrictN D E σ n) Y =
      σ ⟨Y, Ambient.separatedN_subset_separatedAll D E n hY⟩ := by
  rw [Ambient.evalOrZero, dif_pos hY]
  rfl
theorem isSeparatedMultilinear_of_eq {σ : Ambient.separatedAll D E → ℝ} {n : ℕ}
    (Φ : (Fin n → E.Point D → ℝ) → ℝ)
    (hΦ : ∀ (f : Fin n → E.Point D → ℝ) (h : List.ofFn f ∈ Ambient.separatedN D E n),
      σ ⟨List.ofFn f, Ambient.separatedN_subset_separatedAll D E n h⟩ = Φ f)
    (hlin : ∀ A : Fin n → Set (E.Point D),
      (Pairwise fun i j => 0 < Ambient.setDist D E (A i) (A j)) →
      ∀ f : Fin n → E.Point D → ℝ, (∀ i, f i ∈ Ambient.compactC1SuppIn D E (A i)) →
      ∀ (i : Fin n) (g : E.Point D → ℝ), g ∈ Ambient.compactC1SuppIn D E (A i) → ∀ s t : ℝ,
        Φ (Function.update f i (s • f i + t • g)) = s * Φ f + t * Φ (Function.update f i g)) :
    Ambient.IsSeparatedMultilinear D E (Ambient.restrictN D E σ n) := by
  intro A hA f hf i g hg s t
  have hmem : ∀ h ∈ Ambient.compactC1SuppIn D E (A i),
      List.ofFn (Function.update f i h) ∈ Ambient.separatedN D E n := by
    intro h hh
    refine Ambient.ofFn_mem_separatedN D E hA fun k => ?_
    by_cases hk : k = i
    · subst hk
      simpa using hh
    · simpa [Function.update_of_ne hk] using hf k
  have h₀ := Ambient.ofFn_mem_separatedN D E hA hf
  have h₁ := hmem _ (linComb_mem_compactC1SuppIn (hf i) hg s t)
  have h₂ := hmem _ hg
  rw [evalOrZero_restrictN h₁, evalOrZero_restrictN h₀, evalOrZero_restrictN h₂,
    hΦ _ h₁, hΦ _ h₀, hΦ _ h₂]
  exact hlin A hA f hf i g hg s t
end Spaces
section Partitions
theorem sum_nonSingletonPartitions_fin_zero (F : Finset (Fin 0) → ℝ) :
    ∑ π ∈ SetPartition.nonSingletonPartitions 0, ∏ J ∈ π.parts, F J = 1 := by
  have hs : ∀ π : Finpartition (Finset.univ : Finset (Fin 0)), π.parts = ∅ := fun π =>
    Finset.eq_empty_of_forall_notMem fun J hJ => by
      obtain ⟨x, -⟩ := π.nonempty_of_mem_parts hJ
      exact x.elim0
  have hmem : (⊥ : Finpartition (Finset.univ : Finset (Fin 0))) ∈
      SetPartition.nonSingletonPartitions 0 := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun J hJ => ?_⟩
    rw [hs] at hJ
    simp at hJ
  rw [Finset.sum_eq_single_of_mem _ hmem, hs, Finset.prod_empty]
  intro π _ hne
  exact absurd (Finpartition.ext ((hs π).trans (hs ⊥).symm)) hne
theorem notMem_nonSingletonPartitions_of_eq_one {n : ℕ} (hn : n = 1)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    π ∉ SetPartition.nonSingletonPartitions n := by
  subst hn
  intro hπ
  obtain ⟨J, hJ, -⟩ := π.exists_mem (Finset.mem_univ (0 : Fin 1))
  have h₁ := (Finset.mem_filter.1 hπ).2 J hJ
  have h₂ := Finset.card_le_univ J
  simp at h₂
  omega
end Partitions
section Centered
variable {D : MirrorData} {E : Ambient} (S : Ambient.ConnectedFamily D E)
def partValue {n : ℕ} (f : Fin n → E.Point D → ℝ) (J : Finset (Fin n)) : ℝ :=
  S.evalAt J.card (List.ofFn fun k : Fin J.card => f (J.orderEmbOfFin rfl k))
def partitionSum {n : ℕ} (f : Fin n → E.Point D → ℝ) : ℝ :=
  ∑ π ∈ SetPartition.nonSingletonPartitions n, ∏ J ∈ π.parts, partValue S f J
theorem centeredFunctional_eq_partitionSum_of_get {n : ℕ} (f : Fin n → E.Point D → ℝ)
    (Y : Ambient.FnList D E) (hY : Y.length = n)
    (hf : ∀ i : Fin n, Y.get (Fin.cast hY.symm i) = f i)
    (hmem : Y ∈ Ambient.separatedAll D E) :
    S.centeredFunctional ⟨Y, hmem⟩ = partitionSum S f := by
  subst hY
  have : f = Y.get := funext fun i => (hf i).symm
  subst this
  rfl
theorem centeredFunctional_ofFn {n : ℕ} (f : Fin n → E.Point D → ℝ)
    (hmem : List.ofFn f ∈ Ambient.separatedAll D E) :
    S.centeredFunctional ⟨List.ofFn f, hmem⟩ = partitionSum S f :=
  centeredFunctional_eq_partitionSum_of_get S f _ List.length_ofFn (fun i => by simp) hmem
theorem partValue_update_of_notMem {n : ℕ} (f : Fin n → E.Point D → ℝ) {i : Fin n}
    (h : E.Point D → ℝ) {J : Finset (Fin n)} (hi : i ∉ J) :
    partValue S (Function.update f i h) J = partValue S f J := by
  unfold partValue
  congr 2
  funext k
  refine Function.update_of_ne (fun hk => hi ?_) _ _
  rw [← hk]
  exact Finset.orderEmbOfFin_mem J rfl k
theorem partValue_update_linComb {n : ℕ} {A : Fin n → Set (E.Point D)}
    (hA : Pairwise fun i j => 0 < Ambient.setDist D E (A i) (A j))
    {f : Fin n → E.Point D → ℝ} (hf : ∀ i, f i ∈ Ambient.compactC1SuppIn D E (A i)) {i : Fin n}
    {g : E.Point D → ℝ} (hg : g ∈ Ambient.compactC1SuppIn D E (A i)) (s t : ℝ)
    {J : Finset (Fin n)} (hJ : 2 ≤ J.card) (hi : i ∈ J) :
    partValue S (Function.update f i (s • f i + t • g)) J =
      s * partValue S f J + t * partValue S (Function.update f i g) J := by
  have hr : i ∈ Set.range (J.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hi
  obtain ⟨k, rfl⟩ := hr
  have hinj := (J.orderEmbOfFin rfl).injective
  have hupd : ∀ h : E.Point D → ℝ,
      (fun l : Fin J.card => Function.update f (J.orderEmbOfFin rfl k) h (J.orderEmbOfFin rfl l)) =
        Function.update (fun l => f (J.orderEmbOfFin rfl l)) k h := fun h =>
    Function.update_comp_eq_of_injective f hinj k h
  have hm := S.fn_multilinear J.card hJ (fun l => A (J.orderEmbOfFin rfl l))
    (fun l l' hne => hA (hinj.ne hne)) (fun l => f (J.orderEmbOfFin rfl l)) (fun l => hf _) k g hg s t
  unfold partValue
  rw [hupd, hupd]
  simpa only [Ambient.ConnectedFamily.evalAt, dif_pos hJ] using hm
theorem partitionSum_update_linComb {n : ℕ} {A : Fin n → Set (E.Point D)}
    (hA : Pairwise fun i j => 0 < Ambient.setDist D E (A i) (A j))
    {f : Fin n → E.Point D → ℝ} (hf : ∀ i, f i ∈ Ambient.compactC1SuppIn D E (A i)) (i : Fin n)
    {g : E.Point D → ℝ} (hg : g ∈ Ambient.compactC1SuppIn D E (A i)) (s t : ℝ) :
    partitionSum S (Function.update f i (s • f i + t • g)) =
      s * partitionSum S f + t * partitionSum S (Function.update f i g) := by
  unfold partitionSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π hπ => ?_
  obtain ⟨J₀, hJ₀, hi⟩ := π.exists_mem (Finset.mem_univ i)
  have hother : ∀ J ∈ π.parts.erase J₀, i ∉ J := by
    intro J hJ hiJ
    obtain ⟨hne, hJp⟩ := Finset.mem_erase.1 hJ
    exact Finset.disjoint_left.1 (π.disjoint hJp hJ₀ hne) hiJ hi
  have hsplit : ∀ h : E.Point D → ℝ,
      ∏ J ∈ π.parts, partValue S (Function.update f i h) J =
        partValue S (Function.update f i h) J₀ * ∏ J ∈ π.parts.erase J₀, partValue S f J := by
    intro h
    rw [← Finset.mul_prod_erase π.parts _ hJ₀]
    congr 1
    exact Finset.prod_congr rfl fun J hJ => partValue_update_of_notMem S f h (hother J hJ)
  have hself : ∏ J ∈ π.parts, partValue S f J =
      partValue S f J₀ * ∏ J ∈ π.parts.erase J₀, partValue S f J :=
    (Finset.mul_prod_erase π.parts _ hJ₀).symm
  rw [hsplit, hsplit, hself, partValue_update_linComb S hA hf hg s t
    ((Finset.mem_filter.1 hπ).2 J₀ hJ₀) hi]
  ring
theorem centeredFunctional_emptyList : S.centeredFunctional (Ambient.emptyList D E) = 1 :=
  sum_nonSingletonPartitions_fin_zero _
theorem centeredFunctional_of_length_eq_one (X : Ambient.separatedAll D E) (hX : X.1.length = 1) :
    S.centeredFunctional X = 0 :=
  Finset.sum_eq_zero fun π hπ => absurd hπ (notMem_nonSingletonPartitions_of_eq_one hX π)
theorem centeredFunctionalIsSeparated_holds : S.CenteredFunctionalIsSeparated := by
  refine ⟨⟨centeredFunctional_emptyList S, fun n _ => ?_⟩, centeredFunctional_emptyList S,
    centeredFunctional_of_length_eq_one S⟩
  exact isSeparatedMultilinear_of_eq (partitionSum S)
    (fun f h => centeredFunctional_ofFn S f _)
    (fun A hA f hf i g hg s t => partitionSum_update_linComb S hA hf i hg s t)
end Centered
section Lattice
variable (D : MirrorData)
abbrev BondField : Type := D.LatticeBond → Matrices.ComplexMatrix2
abbrev gibbs : Measure (BondField D) := PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β
def IsMeasBdd (F : BondField D → ℝ) : Prop :=
  Measurable F ∧ ∃ C : ℝ, ∀ᵐ U ∂gibbs D, |F U| ≤ C
variable {D}
theorem isMeasBdd_const (c : ℝ) : IsMeasBdd D fun _ => c :=
  ⟨measurable_const, |c|, Filter.Eventually.of_forall fun _ => le_rfl⟩
theorem IsMeasBdd.sub {F G : BondField D → ℝ} (hF : IsMeasBdd D F)
    (hG : IsMeasBdd D G) : IsMeasBdd D fun U => F U - G U := by
  obtain ⟨mF, C₁, h₁⟩ := hF
  obtain ⟨mG, C₂, h₂⟩ := hG
  refine ⟨mF.sub mG, C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with U a b
  have a' := abs_le.1 a
  have b' := abs_le.1 b
  exact abs_le.2 ⟨by linarith [a'.1, a'.2, b'.1, b'.2], by linarith [a'.1, a'.2, b'.1, b'.2]⟩
theorem IsMeasBdd.mul {F G : BondField D → ℝ} (hF : IsMeasBdd D F)
    (hG : IsMeasBdd D G) : IsMeasBdd D fun U => F U * G U := by
  obtain ⟨mF, C₁, h₁⟩ := hF
  obtain ⟨mG, C₂, h₂⟩ := hG
  refine ⟨mF.mul mG, |C₁| * |C₂|, ?_⟩
  filter_upwards [h₁, h₂] with U a b
  rw [abs_mul]
  exact mul_le_mul (a.trans (le_abs_self _)) (b.trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)
theorem IsMeasBdd.finsetProd {ι : Type*} (s : Finset ι) {G : ι → BondField D → ℝ}
    (hG : ∀ i, IsMeasBdd D (G i)) :
    IsMeasBdd D fun U => ∏ i ∈ s, G i U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMeasBdd_const (D := D) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hG a).mul ih
theorem one_lt_sideLength (D : MirrorData) : 1 < D.L :=
  lt_of_lt_of_le (by norm_num) D.isAdmissible.2
theorem isProbabilityMeasure_gibbs (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    IsProbabilityMeasure (gibbs D) := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := hW D.L D.m D.K D.β (one_lt_sideLength D) D.m.pos D.K.pos
  exact h
theorem ae_mem_compactGaugeFields (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    ∀ᵐ U ∂gibbs D, U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := hW D.L D.m D.K D.β (one_lt_sideLength D) D.m.pos D.K.pos
  exact mem_ae_iff.mpr h
theorem IsMeasBdd.integrable (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    {F : BondField D → ℝ} (hF : IsMeasBdd D F) : Integrable F (gibbs D) := by
  have := isProbabilityMeasure_gibbs (D := D) hW
  obtain ⟨m, C, h⟩ := hF
  exact Integrable.of_bound m.aestronglyMeasurable C h
theorem continuous_pathHolonomy (Γ : List D.LatticeBond) :
    Continuous fun U : BondField D => PeriodicLattice.pathHolonomy U Γ := by
  induction Γ with
  | nil => simpa [PeriodicLattice.pathHolonomy] using continuous_const
  | cons b Γ ih =>
    simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons]
    exact (continuous_apply b).matrix_mul ih
theorem measurable_plaquetteEnergy (p : D.LatticePlaquette) :
    Measurable fun U : BondField D => PeriodicLattice.plaquetteCost U p := by
  have hc : Continuous fun U : BondField D => PeriodicLattice.plaquetteCost U p := by
    unfold PeriodicLattice.plaquetteCost PeriodicLattice.plaquetteHolonomy
    exact continuous_const.sub (continuous_const.mul
      (Complex.continuous_re.comp (continuous_pathHolonomy _).matrix_trace))
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact hc.measurable
theorem smearedObservable_eq_sum [Fintype D.LatticePlaquette] (f : D.Torus → ℝ)
    (U : BondField D) :
    PeriodicLattice.smearedObservable f U =
      ∑ p : D.LatticePlaquette, PeriodicLattice.plaquetteCost U p * f p.barycenter :=
  finsum_eq_sum_of_fintype _
theorem isMeasBdd_smearedObservable (hO : ObservableFnFacts)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) (f : D.Torus → ℝ) :
    IsMeasBdd D (PeriodicLattice.smearedObservable f) := by
  have hfin : Finite D.LatticePlaquette := (hO D).1
  have := Fintype.ofFinite D.LatticePlaquette
  refine ⟨?_, 2 * ∑ᶠ p : D.LatticePlaquette, |f p.barycenter|, ?_⟩
  · have : (PeriodicLattice.smearedObservable f : BondField D → ℝ) = fun U =>
        ∑ p : D.LatticePlaquette, PeriodicLattice.plaquetteCost U p * f p.barycenter :=
      funext (smearedObservable_eq_sum f)
    rw [this]
    exact Finset.measurable_sum _ fun p _ => (measurable_plaquetteEnergy p).mul_const _
  · filter_upwards [ae_mem_compactGaugeFields hW] with U hU
    exact ((hO D).2.1 f).2 ⟨U, hU⟩
theorem isMeasBdd_centeredObservable (hO : ObservableFnFacts)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) (f : D.Torus → ℝ) :
    IsMeasBdd D (D.centeredObservable f) :=
  (isMeasBdd_smearedObservable hO hW f).sub (isMeasBdd_const _)
theorem isMeasBdd_list_prod (hO : ObservableFnFacts)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) (X : List (D.Torus → ℝ)) :
    IsMeasBdd D fun U => (X.map fun f => D.centeredObservable f U).prod := by
  induction X with
  | nil => simpa using isMeasBdd_const (D := D) 1
  | cons f X ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (isMeasBdd_centeredObservable hO hW f).mul ih
theorem gibbsExpectation_eq_integral (F : BondField D → ℝ) :
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.β F = ∫ U, F U ∂gibbs D := rfl
theorem smearedObservable_add_smul (hO : ObservableFnFacts)
    (f h : D.Torus → ℝ) (t : ℝ) (U : BondField D) :
    PeriodicLattice.smearedObservable (f + t • h) U =
      PeriodicLattice.smearedObservable f U + t * PeriodicLattice.smearedObservable h U := by
  have hfin : Finite D.LatticePlaquette := (hO D).1
  have := Fintype.ofFinite D.LatticePlaquette
  rw [smearedObservable_eq_sum, smearedObservable_eq_sum, smearedObservable_eq_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem gibbsExpectation_smearedObservable_add_smul (hO : ObservableFnFacts)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) (f h : D.Torus → ℝ) (t : ℝ) :
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.β
        (PeriodicLattice.smearedObservable (f + t • h)) =
      PeriodicLattice.gibbsExpectation D.L D.m D.K D.β (PeriodicLattice.smearedObservable f) +
        t * PeriodicLattice.gibbsExpectation D.L D.m D.K D.β
          (PeriodicLattice.smearedObservable h) := by
  have hf := (isMeasBdd_smearedObservable hO hW f).integrable hW
  have hh := (isMeasBdd_smearedObservable hO hW h).integrable hW
  simp only [gibbsExpectation_eq_integral, smearedObservable_add_smul hO f h t]
  rw [integral_add hf (hh.const_mul t), integral_const_mul]
theorem centeredObservable_add_smul (hO : ObservableFnFacts)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) (f h : D.Torus → ℝ) (t : ℝ)
    (U : BondField D) :
    D.centeredObservable (f + t • h) U = D.centeredObservable f U + t * D.centeredObservable h U := by
  simp only [MirrorData.centeredObservable]
  rw [smearedObservable_add_smul hO f h t, gibbsExpectation_smearedObservable_add_smul hO hW f h t]
  ring
theorem gibbsExpectation_centeredObservable (hO : ObservableFnFacts)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) (f : D.Torus → ℝ) :
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.β (D.centeredObservable f) = 0 := by
  have := isProbabilityMeasure_gibbs (D := D) hW
  have hf := (isMeasBdd_smearedObservable hO hW f).integrable hW
  rw [gibbsExpectation_eq_integral]
  simp only [MirrorData.centeredObservable]
  rw [integral_sub hf (integrable_const _)]
  simp [gibbsExpectation_eq_integral]
theorem centeredObservable_zero (hO : ObservableFnFacts)
    (U : BondField D) :
    D.centeredObservable (0 : D.Torus → ℝ) U = 0 := by
  have h₁ : ∀ V : BondField D, PeriodicLattice.smearedObservable (0 : D.Torus → ℝ) V = 0 :=
    fun V => by
      have := smearedObservable_add_smul hO (0 : D.Torus → ℝ) 0 (-1) V
      simp only [smul_zero, add_zero] at this
      linarith
  have h₂ : (PeriodicLattice.smearedObservable (0 : D.Torus → ℝ) : BondField D → ℝ) =
      fun _ => 0 :=
    funext h₁
  simp [MirrorData.centeredObservable, h₂, gibbsExpectation_eq_integral]
theorem centeredObservable_add (hO : ObservableFnFacts)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) (f h : D.Torus → ℝ)
    (U : BondField D) :
    D.centeredObservable (f + h) U = D.centeredObservable f U + D.centeredObservable h U := by
  simpa using centeredObservable_add_smul hO hW f h 1 U
theorem centeredObservable_smul (hO : ObservableFnFacts)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) (t : ℝ) (h : D.Torus → ℝ)
    (U : BondField D) :
    D.centeredObservable (t • h) U = t * D.centeredObservable h U := by
  have := centeredObservable_add_smul hO hW 0 h t U
  rw [zero_add, centeredObservable_zero hO, zero_add] at this
  exact this
theorem list_prod_update {n : ℕ} (f : Fin n → D.Torus → ℝ) (i : Fin n) (g : D.Torus → ℝ)
    (U : BondField D) :
    ((List.ofFn (Function.update f i g)).map fun h => D.centeredObservable h U).prod =
      D.centeredObservable g U * ∏ k ∈ Finset.univ.erase i, D.centeredObservable (f k) U := by
  rw [List.map_ofFn, List.prod_ofFn,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.comp_apply, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
theorem latticeMoment_update {n : ℕ} (f : Fin n → D.Torus → ℝ) (i : Fin n) (g : D.Torus → ℝ) :
    D.latticeMoment (List.ofFn (Function.update f i g)) =
      ∫ U, D.centeredObservable g U * ∏ k ∈ Finset.univ.erase i, D.centeredObservable (f k) U
        ∂gibbs D := by
  rw [MirrorData.latticeMoment, gibbsExpectation_eq_integral]
  exact integral_congr_ae (Filter.Eventually.of_forall fun U => list_prod_update f i g U)
theorem latticeMoment_isLinearMap_update (hO : ObservableFnFacts)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) {n : ℕ}
    (f : Fin n → D.Torus → ℝ) (i : Fin n) :
    IsLinearMap ℝ fun g : D.Torus → ℝ =>
      D.latticeMoment (List.ofFn (Function.update f i g)) := by
  have hR : IsMeasBdd D fun U =>
      ∏ k ∈ Finset.univ.erase i, D.centeredObservable (f k) U :=
    IsMeasBdd.finsetProd _ fun k => isMeasBdd_centeredObservable hO hW (f k)
  have hI : ∀ g : D.Torus → ℝ, Integrable (fun U => D.centeredObservable g U *
      ∏ k ∈ Finset.univ.erase i, D.centeredObservable (f k) U) (gibbs D) := fun g =>
    ((isMeasBdd_centeredObservable hO hW g).mul hR).integrable hW
  constructor
  · intro g h
    simp only [latticeMoment_update]
    rw [← integral_add (hI g) (hI h)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp only [centeredObservable_add hO hW]
    ring
  · intro t g
    simp only [latticeMoment_update, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp only [centeredObservable_smul hO hW]
    ring
theorem latticeMoment_update_linComb (hO : ObservableFnFacts)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) {n : ℕ}
    (f : Fin n → D.Torus → ℝ) (i : Fin n) (g : D.Torus → ℝ) (s t : ℝ) :
    D.latticeMoment (List.ofFn (Function.update f i (s • f i + t • g))) =
      s * D.latticeMoment (List.ofFn f) +
        t * D.latticeMoment (List.ofFn (Function.update f i g)) := by
  have hL := latticeMoment_isLinearMap_update hO hW f i
  have h₁ := hL.map_add (s • f i) (t • g)
  have h₂ := hL.map_smul s (f i)
  have h₃ := hL.map_smul t g
  simp only [smul_eq_mul, Function.update_eq_self] at h₁ h₂ h₃
  rw [h₁, h₂, h₃]
theorem latticeMoment_nil (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    D.latticeMoment [] = 1 := by
  have := isProbabilityMeasure_gibbs (D := D) hW
  simp [MirrorData.latticeMoment, gibbsExpectation_eq_integral]
theorem latticeMoment_singleton (hO : ObservableFnFacts)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) (f : D.Torus → ℝ) :
    D.latticeMoment [f] = 0 := by
  have : (fun U => ([f].map fun h => D.centeredObservable h U).prod) =
      D.centeredObservable f := by
    funext U
    simp
  rw [MirrorData.latticeMoment, this]
  exact gibbsExpectation_centeredObservable hO hW f
theorem latticeMoment_isSeparatedFunctional (hO : ObservableFnFacts)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    Ambient.IsSeparatedFunctional D Ambient.torus fun X => D.latticeMoment X.1 := by
  refine ⟨latticeMoment_nil hW, fun n _ => ?_⟩
  exact isSeparatedMultilinear_of_eq (E := Ambient.torus) (fun f => D.latticeMoment (List.ofFn f))
    (fun _ _ => rfl) fun A _ f _ i g _ s t => latticeMoment_update_linComb hO hW f i g s t
end Lattice
theorem bothFunctionalsSeparated (hO : ObservableFnFacts)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) : BothFunctionalsSeparated := by
  intro D
  refine ⟨⟨fun f h t => ?_, gibbsExpectation_centeredObservable hO hW⟩,
    ⟨fun X => (isMeasBdd_list_prod hO hW X).integrable hW, latticeMoment_nil hW,
      latticeMoment_singleton hO hW, fun n f i => latticeMoment_isLinearMap_update hO hW f i,
      latticeMoment_isSeparatedFunctional hO hW⟩, fun E S => centeredFunctionalIsSeparated_holds S⟩
  funext U
  simpa using centeredObservable_add_smul hO hW f h t U
end YangMills.Construction.ReflectionPositivity.AxisMirror.SeparatedFunctionals
