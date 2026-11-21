import YangMills.Construction.Continuum.FiniteSeminormsOnTheSchwartzFunctions
import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import YangMills.Construction.Continuum.MultilinearFunctionalsCoordinatewise
import YangMills.Construction.Continuum.OneSpaceOfTestFunctionsFlatTensorsAndTheDual
import YangMills.Construction.Continuum.TwoFamiliesOfSeminormsOnSchwartzFunctions
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.Continuum.UnifiedTestSpace
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.AmbientPoints
variable {n : ℕ}
theorem sum_coordIndex_lex {M : Type*} [AddCommMonoid M]
    (F : ConfigurationSpace.CoordIndex n → M) :
    ∑ ι, F ι = ∑ i, ∑ c, F (toLex (i, c)) := by
  rw [← Fintype.sum_prod_type' (f := fun i c => F (toLex (i, c)))]
  exact (Fintype.sum_equiv (toLex : Fin n × Fin 4 ≃ Fin n ×ₗ Fin 4) _ _ (fun _ => rfl)).symm
def coordList (n : ℕ) : List (ConfigurationSpace.CoordIndex n) :=
  (List.finRange n).flatMap fun i => (List.finRange 4).map fun c => toLex (i, c)
theorem coordList_pairwise_lt : (coordList n).Pairwise (· < ·) := by
  unfold coordList
  rw [List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact List.Pairwise.imp (R := (· < ·)) (fun {a b} (h : a < b) =>
      (Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, h⟩) : toLex (i, a) < toLex (i, b)))
      (List.pairwise_lt_finRange 4)
  · refine List.Pairwise.imp (R := (· < ·)) ?_ (List.pairwise_lt_finRange n)
    intro i i' h a ha b hb
    simp only [List.mem_map] at ha hb
    obtain ⟨c, _, rfl⟩ := ha
    obtain ⟨c', _, rfl⟩ := hb
    exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)
theorem mem_coordList (ι : ConfigurationSpace.CoordIndex n) :
    ι ∈ coordList n := by
  simp only [coordList, List.mem_flatMap, List.mem_map]
  exact ⟨(ofLex ι).1, List.mem_finRange _, (ofLex ι).2, List.mem_finRange _, rfl⟩
theorem sort_univ_coordIndex :
    (Finset.univ : Finset (ConfigurationSpace.CoordIndex n)).sort (· ≤ ·) =
      coordList n := by
  have hsorted := Finset.pairwise_sort
    (Finset.univ : Finset (ConfigurationSpace.CoordIndex n)) (· ≤ ·)
  have hle : (coordList n).Pairwise (· ≤ ·) := coordList_pairwise_lt.imp le_of_lt
  have hnodup : (coordList n).Nodup := coordList_pairwise_lt.imp ne_of_lt
  have hperm : ((Finset.univ : Finset (ConfigurationSpace.CoordIndex n)).sort
      (· ≤ ·)).Perm (coordList n) :=
    (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) hnodup).2 fun ι => by
      simp [mem_coordList ι]
  exact hperm.eq_of_pairwise (fun _ _ _ _ h h' => le_antisymm h h') hsorted hle
theorem foldr_flatMap_eq {A B C : Type*} (l : List A) (F : A → List B) (step : B → C → C) (g : C) :
    (l.flatMap F).foldr step g = l.foldr (fun a h => (F a).foldr step h) g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.foldr_append, ih]
theorem partialD_eq_multiDeriv (α : ConfigGradients.Idx n) (φ : TestSpaces.PointTuple n → ℂ) :
    ConfigGradients.partialD α φ =
      TestSpaces.multiDeriv (idxByArg n α) φ := by
  show ConfigurationSpace.iterDirDeriv _ α φ = _
  unfold ConfigurationSpace.iterDirDeriv
  rw [sort_univ_coordIndex]
  unfold coordList
  rw [foldr_flatMap_eq]
  simp only [List.foldr_map]
  rfl
theorem ptNorm_eq_tupleNorm (x : ConfigGradients.Pt n) :
    ConfigGradients.ptNorm x = TestSpaces.tupleNorm x := by
  show Real.sqrt (∑ ι, ConfigurationSpace.coords x ι ^ 2) = _
  rw [sum_coordIndex_lex]
  rfl
theorem idxOrder_idxByArg (α : ConfigGradients.Idx n) :
    TestSpaces.idxOrder (idxByArg n α) = ConfigGradients.idxDegree α := by
  show _ = ∑ ι, α ι
  rw [sum_coordIndex_lex]
  rfl
theorem diagLocus_eq_diagonalLocus (n : ℕ) :
    ConfigGradients.diagLocus n = TestSpaces.diagonalLocus n := by
  ext x
  rw [TestSpaces.mem_diagonalLocus_iff]
  simp [ConfigGradients.diagLocus, ConfigurationSpace.fatDiagonal,
    ConfigurationSpace.orderedPairs, ConfigurationSpace.pairDiagonal]
theorem gradientSignsAgree (n : ℕ) : GradientSignsAgree n :=
  ⟨ptNorm_eq_tupleNorm, rfl, idxOrder_idxByArg, fun α φ _ => partialD_eq_multiDeriv α φ,
    diagLocus_eq_diagonalLocus n⟩
theorem weightedSeminorm_eq_sobolevWeightNorm (k : ℕ) (φ : TestSpaces.PointTuple n → ℂ) :
    TestSpaces.weightedSeminorm k φ = ConfigurationSpace.sobolevWeightNorm k φ := by
  unfold TestSpaces.weightedSeminorm ConfigurationSpace.sobolevWeightNorm
  refine iSup_congr fun x => ?_
  refine ((idxByArg n).iSup_congr fun α => ?_).symm
  have h1 := idxOrder_idxByArg α
  have h2 := ptNorm_eq_tupleNorm x
  have h3 := partialD_eq_multiDeriv α φ
  simp only [ConfigGradients.idxDegree,
    ConfigGradients.ptNorm, ConfigGradients.partialD] at h1 h2 h3
  rw [h1, h2, h3]
theorem one_add_pow_le_weight {t : ℝ} (ht : 0 ≤ t) {k' k : ℕ} (h : k' ≤ k) :
    (1 + t) ^ k' ≤ (2 : ℝ) ^ ((k' : ℝ) / 2) * (1 + t ^ 2) ^ ((k : ℝ) / 2) := by
  have ha : 0 ≤ 1 + t := by linarith
  have hb : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have h1 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (1 - t)]
  have h2 : (1 + t) ^ k' = ((1 + t) ^ 2) ^ ((k' : ℝ) / 2) := by
    calc (1 + t) ^ k' = (1 + t) ^ (k' : ℝ) := (Real.rpow_natCast _ _).symm
      _ = (1 + t) ^ ((2 : ℝ) * ((k' : ℝ) / 2)) := by congr 1; ring
      _ = ((1 + t) ^ (2 : ℝ)) ^ ((k' : ℝ) / 2) := Real.rpow_mul ha _ _
      _ = ((1 + t) ^ 2) ^ ((k' : ℝ) / 2) := by rw [Real.rpow_two]
  have hk' : (0 : ℝ) ≤ (k' : ℝ) / 2 := by positivity
  have hkk : (k' : ℝ) / 2 ≤ (k : ℝ) / 2 := by
    have : (k' : ℝ) ≤ k := by exact_mod_cast h
    linarith
  rw [h2]
  calc ((1 + t) ^ 2) ^ ((k' : ℝ) / 2) ≤ (2 * (1 + t ^ 2)) ^ ((k' : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) h1 hk'
    _ = (2 : ℝ) ^ ((k' : ℝ) / 2) * (1 + t ^ 2) ^ ((k' : ℝ) / 2) :=
        Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ (2 : ℝ) ^ ((k' : ℝ) / 2) * (1 + t ^ 2) ^ ((k : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb hkk) (by positivity)
theorem weightedDerivSup_le {k' k : ℕ}
    (α : ConfigurationSpace.MultiIdx (ConfigurationSpace.CoordIndex n))
    (hk' : k' ≤ k) (hα : α.order ≤ k) (φ : TestSpaces.PointTuple n → ℂ) :
    ConfigurationSpace.weightedDerivSup k' α φ ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((k' : ℝ) / 2)) *
        ConfigurationSpace.sobolevWeightNorm k φ := by
  refine iSup_le fun x => ?_
  have ht : 0 ≤ ConfigurationSpace.configNorm x := Real.sqrt_nonneg _
  set D := ‖ConfigurationSpace.configMultiDeriv α φ x‖ with hD
  have hDn : 0 ≤ D := norm_nonneg _
  have hle := mul_le_mul_of_nonneg_right (one_add_pow_le_weight ht hk') hDn
  calc ENNReal.ofReal ((1 + ConfigurationSpace.configNorm x) ^ k' * D)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ ((k' : ℝ) / 2) *
          ((1 + ConfigurationSpace.configNorm x ^ 2) ^ ((k : ℝ) / 2) * D)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_assoc]
        exact hle
    _ = ENNReal.ofReal ((2 : ℝ) ^ ((k' : ℝ) / 2)) *
        ENNReal.ofReal ((1 + ConfigurationSpace.configNorm x ^ 2) ^ ((k : ℝ) / 2) * D) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ _ := by
        gcongr
        unfold ConfigurationSpace.sobolevWeightNorm
        exact le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le hα le_rfl))
theorem mem_schwartzSpace_iff
    (hN : ConfigurationSpace.schwartzSeminormsFinite)
    (hn : 1 ≤ n) {φ : TestSpaces.PointTuple n → ℂ}
    (hφ : φ ∈ ConfigGradients.smoothFns n) :
    φ ∈ SchwartzSeminorms.schwartzSpace n ↔ φ ∈ TestSpaces.schwartzSet n := by
  constructor
  · intro h
    refine ⟨hφ, fun k _ => ?_⟩
    rw [weightedSeminorm_eq_sobolevWeightNorm]
    have hk := (hN n hn k k k).1 φ h
    exact lt_of_le_of_lt hk.2 ((hN n hn k k k).1 φ h).1
  · intro h
    refine ⟨hφ, fun k' α => ?_⟩
    have hk : 0 < max 1 (max k' α.order) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hfin := h.2 _ hk
    rw [weightedSeminorm_eq_sobolevWeightNorm] at hfin
    refine lt_of_le_of_lt (weightedDerivSup_le α ?_ ?_ φ)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
theorem flatSchwartz_eq_flatSchwartzSet
    (hN : ConfigurationSpace.schwartzSeminormsFinite)
    (hn : 1 ≤ n) :
    FlatTensors.flatSchwartz n = TestSpaces.flatSchwartzSet n := by
  ext φ
  constructor
  · rintro ⟨h, hz⟩
    refine ⟨(mem_schwartzSpace_iff hN hn h.1).1 h, fun β x hx => ?_⟩
    have := hz x (by rw [← diagLocus_eq_diagonalLocus] at hx; exact hx) ((idxByArg n).symm β)
    have h3 := congrFun (partialD_eq_multiDeriv ((idxByArg n).symm β) φ) x
    rw [Equiv.apply_symm_apply] at h3
    rw [← h3]
    exact this
  · rintro ⟨h, hz⟩
    refine ⟨(mem_schwartzSpace_iff hN hn h.1).2 h, fun x hx α => ?_⟩
    have h3 := congrFun (partialD_eq_multiDeriv α φ) x
    refine Eq.trans h3 (hz _ x ?_)
    rw [← diagLocus_eq_diagonalLocus]
    exact hx
theorem schwartzSpacesAgree
    (hN : ConfigurationSpace.schwartzSeminormsFinite)
    (hn : 1 ≤ n) : SchwartzSpacesAgree n :=
  ⟨fun _ hφ => mem_schwartzSpace_iff hN hn hφ,
    fun φ k _ => weightedSeminorm_eq_sobolevWeightNorm k φ.1,
    flatSchwartz_eq_flatSchwartzSet hN hn⟩
theorem ofReal_tuple_mem_smoothRealTupleSet {g : Fin n → (Fin 4 → ℝ) → ℝ}
    (hg : g ∈ TestSpaces.disjointSupportTuples Set.univ n) (hs : ∀ i, ContDiff ℝ ∞ (g i)) :
    (fun i x => ((g i x : ℝ) : ℂ)) ∈ ConfigSpace.smoothRealTupleSet n := by
  have hsupp : ∀ i, tsupport (fun x => ((g i x : ℝ) : ℂ)) = tsupport (g i) :=
    fun i => FlatTensors.tsupport_ofReal_comp (g i)
  refine ⟨⟨fun i => ⟨fun x => by simp, ?_, ?_, Set.subset_univ _⟩, fun i i' hne => ?_⟩, fun i => ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (hg.1 i).1
  · rw [HasCompactSupport, hsupp i]
    exact (hg.1 i).2.1
  · rw [hsupp i, hsupp i']
    exact hg.2 hne
  · exact Complex.ofRealCLM.contDiff.comp (hs i)
theorem contDiff_of_contDiff_ofReal {g : (Fin 4 → ℝ) → ℝ}
    (h : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ))) :
    ContDiff ℝ ∞ g := by
  have := Complex.reCLM.contDiff.comp h
  simpa [Function.comp_def] using this
theorem smoothSepTuples_eq
    (hE : EntrywiseMultilinearity.Statement) (s : Conventions.StandingParameters) (hn : 1 ≤ n) :
    FlatTensors.smoothSepTuples s n =
      {f | f ∈ separatedTuples s .euclidean n ∧ TestSpaces.HasSmoothComponents Set.univ f} := by
  have hsep : (separatedTuples s .euclidean n : Set (Fin n → (Fin 4 → ℝ) → ℝ)) =
      TestSpaces.disjointSupportTuples Set.univ n := (hE s).2.1.1 n
  have hcomp : ∀ f : Fin n → Pt s .euclidean → ℝ, f ∈ separatedTuples s .euclidean n →
      ((∀ i, ContDiff ℝ ∞ (fun x : Fin 4 → ℝ => f i x)) ↔
        TestSpaces.HasSmoothComponents Set.univ f) := by
    intro f hf
    have hf' : (f : Fin n → (Fin 4 → ℝ) → ℝ) ∈ TestSpaces.disjointSupportTuples Set.univ n :=
      hsep ▸ hf
    exact ⟨fun h i => ⟨h i, (hf'.1 i).2.1, Set.subset_univ _⟩, fun h i => (h i).1⟩
  ext f
  constructor
  · intro hf
    have hmem := FlatTensors.smoothSepTuples_subset_separatedTuples n hf
    refine ⟨hmem, (hcomp f hmem).1 fun i => ?_⟩
    obtain _ | _ | m := n
    · exact absurd hn (by norm_num)
    · exact contDiff_of_contDiff_ofReal (hf.2 i)
    · exact contDiff_of_contDiff_ofReal (hf.2 i)
  · rintro ⟨hf, hs⟩
    have hf' : (f : Fin n → (Fin 4 → ℝ) → ℝ) ∈ TestSpaces.disjointSupportTuples Set.univ n :=
      hsep ▸ hf
    have hread := ofReal_tuple_mem_smoothRealTupleSet hf' ((hcomp f hf).2 hs)
    obtain _ | _ | m := n
    · exact absurd hn (by norm_num)
    · exact ⟨hf, hread.2⟩
    · exact hread
theorem smoothTupleTensorsFlat
    (hN : ConfigurationSpace.schwartzSeminormsFinite)
    (hF : TestSpaces.Elementary.BasicProperties)
    (hE : EntrywiseMultilinearity.Statement) (s : Conventions.StandingParameters) (hn : 1 ≤ n) :
    SmoothTupleTensorsFlat s n := by
  have heq := smoothSepTuples_eq hE s hn
  refine ⟨heq, fun f hf => ?_⟩
  have hreal : ∀ x, FlatTensors.pointTensor (FlatTensors.toComplexTuple f) x =
      ((FlatTensors.pointTensor (R := ℝ) f x : ℝ) : ℂ) := by
    intro x
    show ∏ i, ((f i (x i) : ℝ) : ℂ) = ((∏ i, f i (x i) : ℝ) : ℂ)
    exact (Complex.ofReal_prod _ _).symm
  refine ⟨?_, hreal⟩
  rw [heq] at hf
  have hsep : (f : Fin n → (Fin 4 → ℝ) → ℝ) ∈ TestSpaces.disjointSupportTuples Set.univ n :=
    ((hE s).2.1.1 n) ▸ hf.1
  have hflat := ((hF n hn).2.2.2.1 Set.univ isOpen_univ f hsep).2 hf.2 |>.2.1
  have htensor : FlatTensors.pointTensor (FlatTensors.toComplexTuple f) =
      TestSpaces.Elementary.tensorProdComplex f := funext hreal
  rw [htensor, flatSchwartz_eq_flatSchwartzSet hN hn]
  exact hflat
theorem dualCharacterizedBySeminorms
    (hN : ConfigurationSpace.schwartzSeminormsFinite)
    (hT : ConfigurationSpace.SeminormFamiliesComparison)
    (hn : 1 ≤ n) : DualCharacterizedBySeminorms n := by
  intro S hS
  constructor
  · rintro ⟨_, k', q, b, hb, hbound⟩
    refine ⟨max 1 (max k' q), b * (2 : ℝ) ^ ((k' : ℝ) / 2),
      lt_of_lt_of_le one_pos (le_max_left _ _), by positivity, fun φ => ?_⟩
    have h1 := (hT n hn).1 k' q (max 1 (max k' q)) (le_max_right _ _) φ.1 φ.2.1
    calc ENNReal.ofReal ‖S φ‖
        ≤ ENNReal.ofReal b * ConfigurationSpace.decaySeminorm k' q φ.1 := hbound φ
      _ ≤ ENNReal.ofReal b * (ENNReal.ofReal ((2 : ℝ) ^ ((k' : ℝ) / 2)) *
            ConfigurationSpace.sobolevWeightNorm (max 1 (max k' q)) φ.1) := by
          gcongr
      _ = _ := by
          rw [ENNReal.ofReal_mul hb, mul_assoc]
  · rintro ⟨k, c, _, hc, hbound⟩
    refine ⟨hS, k, k, c, hc, fun φ => ?_⟩
    refine (hbound φ).trans ?_
    gcongr
    exact ((hN n hn k k k).1 φ.1 φ.2.1).2
theorem testSpacesUnified
    (hN : ConfigurationSpace.schwartzSeminormsFinite)
    (hT : ConfigurationSpace.SeminormFamiliesComparison)
    (hF : TestSpaces.Elementary.BasicProperties)
    (hE : EntrywiseMultilinearity.Statement) : TestSpacesUnified :=
  fun n hn => ⟨⟨gradientSignsAgree n, schwartzSpacesAgree hN hn⟩,
    fun s => smoothTupleTensorsFlat hN hF hE s hn, dualCharacterizedBySeminorms hN hT hn⟩
end YangMills.Construction.Continuum.UnifiedTestSpace
end
