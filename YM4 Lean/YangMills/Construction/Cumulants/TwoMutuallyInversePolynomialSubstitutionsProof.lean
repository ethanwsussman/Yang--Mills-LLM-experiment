import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMomentsProof
import YangMills.Construction.Cumulants.SmallestPartitionsBlocksAndTransportByABijection
import YangMills.Construction.Cumulants.TwoMutuallyInversePolynomialSubstitutions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Cumulants
open Filter
open scoped Topology
variable {q : ℕ}
def subsetMonomialSum (c : Finset (Fin q) → ℂ) : Coordinates.ComplexCoordinates q → ℂ :=
  fun z => ∑ A : Finset (Fin q), c A * ∏ l ∈ A, z l
def coeffDeriv (s : Fin q) (c : Finset (Fin q) → ℂ) : Finset (Fin q) → ℂ :=
  fun B => if s ∈ B then 0 else c (insert s B)
theorem sum_finset_univ_split_mem (s : Fin q) (f : Finset (Fin q) → ℂ) :
    ∑ A, f A = ∑ B ∈ (Finset.univ.erase s).powerset, f B +
      ∑ B ∈ (Finset.univ.erase s).powerset, f (insert s B) := by
  have h : (Finset.univ : Finset (Finset (Fin q))) = (insert s (Finset.univ.erase s)).powerset := by
    rw [Finset.insert_erase (Finset.mem_univ s), Finset.powerset_univ]
  rw [h, Finset.sum_powerset_insert (Finset.notMem_erase _ _)]
theorem subsetMonomialSum_add_smul_sub (c : Finset (Fin q) → ℂ) (s : Fin q)
    (z : Coordinates.ComplexCoordinates q) (ζ : ℂ) :
    subsetMonomialSum c (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector s) -
        subsetMonomialSum c z =
      ζ * subsetMonomialSum (coeffDeriv s c) z := by
  have hnot : ∀ B ∈ (Finset.univ.erase s).powerset, s ∉ B := fun B hB hs =>
    Finset.notMem_erase s _ (Finset.mem_powerset.1 hB hs)
  have hother : ∀ l : Fin q, l ≠ s →
      (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector s) l = z l := by
    intro l hl
    simp [Coordinates.ComplexCoordinates.stdBasisVector, Pi.single_eq_of_ne hl]
  have hself : (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector s) s = z s + ζ := by
    simp [Coordinates.ComplexCoordinates.stdBasisVector]
  have hprod : ∀ B ∈ (Finset.univ.erase s).powerset,
      ∏ l ∈ B, (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector s) l = ∏ l ∈ B, z l :=
    fun B hB => Finset.prod_congr rfl fun l hl => hother l fun h => hnot B hB (h ▸ hl)
  simp only [subsetMonomialSum]
  rw [sum_finset_univ_split_mem s
      (fun A => c A * ∏ l ∈ A, (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector s) l),
    sum_finset_univ_split_mem s (fun A => c A * ∏ l ∈ A, z l),
    sum_finset_univ_split_mem s (fun A => coeffDeriv s c A * ∏ l ∈ A, z l)]
  have h1 : ∑ B ∈ (Finset.univ.erase s).powerset,
      c B * ∏ l ∈ B, (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector s) l =
      ∑ B ∈ (Finset.univ.erase s).powerset, c B * ∏ l ∈ B, z l :=
    Finset.sum_congr rfl fun B hB => by rw [hprod B hB]
  have h2 : ∑ B ∈ (Finset.univ.erase s).powerset,
      c (insert s B) * ∏ l ∈ insert s B, (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector s) l =
      ∑ B ∈ (Finset.univ.erase s).powerset, c (insert s B) * ((z s + ζ) * ∏ l ∈ B, z l) :=
    Finset.sum_congr rfl fun B hB => by
      rw [Finset.prod_insert (hnot B hB), hself, hprod B hB]
  have h3 : ∑ B ∈ (Finset.univ.erase s).powerset, c (insert s B) * ∏ l ∈ insert s B, z l =
      ∑ B ∈ (Finset.univ.erase s).powerset, c (insert s B) * (z s * ∏ l ∈ B, z l) :=
    Finset.sum_congr rfl fun B hB => by rw [Finset.prod_insert (hnot B hB)]
  have h4 : ∑ B ∈ (Finset.univ.erase s).powerset, coeffDeriv s c B * ∏ l ∈ B, z l =
      ∑ B ∈ (Finset.univ.erase s).powerset, c (insert s B) * ∏ l ∈ B, z l :=
    Finset.sum_congr rfl fun B hB => by simp [coeffDeriv, hnot B hB]
  have h5 : ∑ B ∈ (Finset.univ.erase s).powerset,
      coeffDeriv s c (insert s B) * ∏ l ∈ insert s B, z l = 0 :=
    Finset.sum_eq_zero fun B _ => by simp [coeffDeriv]
  rw [h1, h2, h3, h4, h5, add_zero, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun B _ => by ring
theorem partialDeriv_subsetMonomialSum (s : Fin q) (c : Finset (Fin q) → ℂ) :
    ComplexVariables.partialDeriv s (subsetMonomialSum c) =
      subsetMonomialSum (coeffDeriv s c) := by
  funext z
  have hquot : ∀ ζ : ℂ, ζ ≠ 0 → subsetMonomialSum (coeffDeriv s c) z =
      ComplexVariables.diffQuot (subsetMonomialSum c) z s ζ := by
    intro ζ hζ
    rw [ComplexVariables.diffQuot, subsetMonomialSum_add_smul_sub, inv_mul_cancel_left₀ hζ]
  have ht : Tendsto (ComplexVariables.diffQuot (subsetMonomialSum c) z s) (𝓝[≠] (0 : ℂ))
      (𝓝 (subsetMonomialSum (coeffDeriv s c) z)) :=
    tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono fun ζ hζ => hquot ζ hζ)
  exact ht.limUnder_eq
theorem iteratedPartials_subsetMonomialSum (l : List (Fin q)) (c : Finset (Fin q) → ℂ) :
    ComplexVariables.iteratedPartials l (subsetMonomialSum c) =
      subsetMonomialSum (l.foldr coeffDeriv c) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    change ComplexVariables.partialDeriv j
      (ComplexVariables.iteratedPartials l (subsetMonomialSum c)) = _
    rw [ih, partialDeriv_subsetMonomialSum]
    rfl
theorem subsetMonomialSum_zero (c : Finset (Fin q) → ℂ) : subsetMonomialSum c 0 = c ∅ := by
  have h : ∑ A : Finset (Fin q), c A * ∏ l ∈ A, (0 : Coordinates.ComplexCoordinates q) l =
      c ∅ * ∏ l ∈ (∅ : Finset (Fin q)), (0 : Coordinates.ComplexCoordinates q) l := by
    refine Finset.sum_eq_single ∅ (fun A _ hA => ?_) (by simp)
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hA
    rw [Finset.prod_eq_zero hx rfl, mul_zero]
  simpa [subsetMonomialSum] using h
theorem foldr_coeffDeriv_apply (c : Finset (Fin q) → ℂ) (l : List (Fin q)) (hl : l.Nodup)
    (B : Finset (Fin q)) (hB : Disjoint l.toFinset B) :
    l.foldr coeffDeriv c B = c (B ∪ l.toFinset) := by
  induction l generalizing B with
  | nil => simp
  | cons j l ih =>
    have hj : j ∉ l := (List.nodup_cons.1 hl).1
    have hjB : j ∉ B := by
      intro h
      exact Finset.disjoint_left.1 hB (by simp) h
    have hdisj : Disjoint l.toFinset (insert j B) := by
      rw [Finset.disjoint_left]
      intro x hx hxB
      rcases Finset.mem_insert.1 hxB with rfl | hxB
      · exact hj (List.mem_toFinset.1 hx)
      · exact Finset.disjoint_left.1 hB (by simpa using Or.inr (List.mem_toFinset.1 hx)) hxB
    change coeffDeriv j (l.foldr coeffDeriv c) B = _
    rw [coeffDeriv, if_neg hjB, ih (List.nodup_cons.1 hl).2 _ hdisj]
    congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.toFinset_cons]
    tauto
theorem partialOverFinset_subsetMonomialSum_zero (c : Finset (Fin q) → ℂ) (J : Finset (Fin q)) :
    ComplexVariables.partialOverFinset J (subsetMonomialSum c) 0 = c J := by
  rw [ComplexVariables.partialOverFinset, iteratedPartials_subsetMonomialSum,
    subsetMonomialSum_zero,
    foldr_coeffDeriv_apply c _ (Finset.sort_nodup J _) ∅ (Finset.disjoint_empty_right _),
    Finset.empty_union, Finset.sort_toFinset]
def extendByZero (a : SubsetFamily q) : Finset (Fin q) → ℂ :=
  fun A => if h : A.Nonempty then a ⟨A, h⟩ else 0
theorem multilinearPoly_eq_subsetMonomialSum (k : SubsetFamily q) :
    multilinearPoly k = subsetMonomialSum (_root_.YangMills.Construction.Cumulants.extendByZero k) := by
  funext z
  simp only [multilinearPoly, subsetMonomialSum]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun A : Finset (Fin q) => A.Nonempty)
    (fun A => _root_.YangMills.Construction.Cumulants.extendByZero k A * ∏ l ∈ A, z l)]
  have h2 : ∑ A : {A : Finset (Fin q) // ¬ A.Nonempty}, _root_.YangMills.Construction.Cumulants.extendByZero k A.1 * ∏ l ∈ A.1, z l = 0 :=
    Finset.sum_eq_zero fun A _ => by simp [_root_.YangMills.Construction.Cumulants.extendByZero, A.2]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [_root_.YangMills.Construction.Cumulants.extendByZero, dif_pos J.2]
theorem multilinearPoly_zero (k : SubsetFamily q) : multilinearPoly k 0 = 0 := by
  rw [multilinearPoly_eq_subsetMonomialSum, subsetMonomialSum_zero]
  simp [_root_.YangMills.Construction.Cumulants.extendByZero]
theorem partialOverFinset_multilinearPoly_zero (k : SubsetFamily q) (J : Finset (Fin q)) :
    ComplexVariables.partialOverFinset J (multilinearPoly k) 0 = _root_.YangMills.Construction.Cumulants.extendByZero k J := by
  rw [multilinearPoly_eq_subsetMonomialSum, partialOverFinset_subsetMonomialSum_zero]
theorem blockProduct_eq_prod {J : Finset (Fin q)} (a : SubsetFamily q)
    (π : SetPartition.Partitions J) :
    blockProduct a π = ∏ I ∈ π.parts, _root_.YangMills.Construction.Cumulants.extendByZero a I := by
  rw [← Finset.prod_coe_sort π.parts (_root_.YangMills.Construction.Cumulants.extendByZero a)]
  refine Finset.prod_congr rfl fun B _ => ?_
  simp only [_root_.YangMills.Construction.Cumulants.extendByZero, dif_pos (π.nonempty_of_mem_parts B.2)]
  rfl
theorem iteratedDeriv_cexp (n : ℕ) : iteratedDeriv n Complex.exp = Complex.exp := by
  induction n with
  | zero => exact iteratedDeriv_zero
  | succ n ih => rw [iteratedDeriv_succ, ih, Complex.deriv_exp]
theorem isHolomorphicVia_of_differentiableOn {W : Set ℂ} {η : ℂ → ℂ} (hW : IsOpen W)
    (hη : DifferentiableOn ℂ η W) :
    Coordinates.ComplexCoordinates.IsHolomorphicVia (Equiv.funUnique (Fin 1) ℂ).symm
      (Equiv.funUnique (Fin 1) ℂ).symm W η := by apply _root_.YangMills.Construction.Cumulants.MomentCumulantFormulas.isHolomorphicVia_of_differentiableOn <;> assumption
theorem multilinearPoly_isEntire (HF : ComplexVariables.HolomorphicFacts.StandardFacts)
    (hq : 1 ≤ q) (k : SubsetFamily q) : ComplexVariables.IsEntireFun (multilinearPoly k) := by
  have h := (HF q hq Set.univ isOpen_univ).2.1.2.2.2.2.2.2
    (∑ J : NonemptyFinSubset q, MvPolynomial.C (k J) * ∏ l ∈ J.1, MvPolynomial.X l)
  have he : (fun z : Coordinates.ComplexCoordinates q => MvPolynomial.eval z
      (∑ J : NonemptyFinSubset q, MvPolynomial.C (k J) * ∏ l ∈ J.1, MvPolynomial.X l)) =
      multilinearPoly k := by
    funext z
    simp [multilinearPoly, map_sum, map_mul, map_prod]
  rwa [he] at h
theorem multilinearPoly_continuous (k : SubsetFamily q) : Continuous (multilinearPoly k) := by
  unfold multilinearPoly
  fun_prop
theorem expDeriv_eq_partitionSum (HF : ComplexVariables.HolomorphicFacts.StandardFacts)
    (HC : CompositeDerivative.PartitionChainRule) (hq : 1 ≤ q) (k : SubsetFamily q)
    (J : NonemptyFinSubset q) :
    ComplexVariables.HasPartialOverFinset Set.univ J.1
        (ComplexVariables.expComp (multilinearPoly k)) ∧
      expDerivFamily k J = partitionSum k J := by
  obtain ⟨h1, -, h3⟩ := HC q hq Set.univ Set.univ (multilinearPoly k) Complex.exp isOpen_univ
    isOpen_univ (Set.mapsTo_univ _ _) (multilinearPoly_isEntire HF hq k)
    (isHolomorphicVia_of_differentiableOn isOpen_univ
      Complex.differentiable_exp.differentiableOn) J.1 J.2
  refine ⟨h1, ?_⟩
  have hval := h3 0 (Set.mem_univ _)
  change ComplexVariables.partialOverFinset J.1 (Complex.exp ∘ multilinearPoly k) 0 = _
  rw [hval]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [iteratedDeriv_cexp, multilinearPoly_zero, Complex.exp_zero, one_mul, blockProduct_eq_prod]
  exact Finset.prod_congr rfl fun I _ => partialOverFinset_multilinearPoly_zero k I
theorem eq_moebiusPartitionSum_expDerivFamily
    (HF : ComplexVariables.HolomorphicFacts.StandardFacts)
    (HC : CompositeDerivative.PartitionChainRule) (hq : 1 ≤ q) (k : SubsetFamily q)
    (J : NonemptyFinSubset q) : k J = moebiusPartitionSum (expDerivFamily k) J := by
  have hLe : ComplexVariables.IsEntireFun (multilinearPoly k) := multilinearPoly_isEntire HF hq k
  have hpd := (HF q hq Set.univ isOpen_univ).1 (multilinearPoly k) hLe
  have hrestrict := hpd.2.2.2.2.2.2.2
  have hcont := multilinearPoly_continuous k
  have hU : IsOpen {z : Coordinates.ComplexCoordinates q | ‖multilinearPoly k z‖ < 1 / 2} :=
    isOpen_lt hcont.norm continuous_const
  have hW : IsOpen {w : ℂ | ‖w - 1‖ < 1} := isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : Coordinates.ComplexCoordinates q) ∈
      {z : Coordinates.ComplexCoordinates q | ‖multilinearPoly k z‖ < 1 / 2} := by
    simp [multilinearPoly_zero]
  have hLU : ComplexVariables.IsHolomorphicScalar
      {z : Coordinates.ComplexCoordinates q | ‖multilinearPoly k z‖ < 1 / 2} (multilinearPoly k) :=
    (hrestrict _ hU (Set.subset_univ _) (multilinearPoly k) fun _ _ => rfl).1
  have hEU : ComplexVariables.IsHolomorphicScalar
      {z : Coordinates.ComplexCoordinates q | ‖multilinearPoly k z‖ < 1 / 2}
      (ComplexVariables.expComp (multilinearPoly k)) :=
    ((HF q hq _ hU).2.2.1 Set.univ (multilinearPoly k) Complex.exp isOpen_univ hLU
      (Set.mapsTo_univ _ _) Complex.differentiable_exp.differentiableOn).1
  have hmaps : Set.MapsTo (ComplexVariables.expComp (multilinearPoly k))
      {z : Coordinates.ComplexCoordinates q | ‖multilinearPoly k z‖ < 1 / 2}
      {w : ℂ | ‖w - 1‖ < 1} := by
    intro z hz
    have hz' : ‖multilinearPoly k z‖ < 1 / 2 := hz
    have hb := Complex.norm_exp_sub_one_le (x := multilinearPoly k z) (by linarith)
    change ‖Complex.exp (multilinearPoly k z) - 1‖ < 1
    linarith
  have hslit : ∀ w ∈ {w : ℂ | ‖w - 1‖ < 1}, w ∈ Complex.slitPlane := by
    intro w hw
    have := Complex.mem_slitPlane_of_norm_lt_one (z := w - 1) hw
    simpa using this
  have hlog : DifferentiableOn ℂ Complex.log {w : ℂ | ‖w - 1‖ < 1} := fun w hw =>
    (Complex.differentiableAt_log (hslit w hw)).differentiableWithinAt
  obtain ⟨-, -, h3⟩ := HC q hq _ _ (ComplexVariables.expComp (multilinearPoly k)) Complex.log
    hU hW hmaps hEU (isHolomorphicVia_of_differentiableOn hW hlog) J.1 J.2
  have hval := h3 0 h0
  have hEq : Set.EqOn (Complex.log ∘ ComplexVariables.expComp (multilinearPoly k))
      (multilinearPoly k)
      {z : Coordinates.ComplexCoordinates q | ‖multilinearPoly k z‖ < 1 / 2} := by
    intro z hz
    have hz' : ‖multilinearPoly k z‖ < 1 / 2 := hz
    have him : |(multilinearPoly k z).im| ≤ ‖multilinearPoly k z‖ := Complex.abs_im_le_norm _
    have hpi := Real.pi_gt_three
    have hb := abs_le.1 him
    exact Complex.log_exp (by linarith [hb.1]) (by linarith [hb.2])
  have hloc := (hrestrict _ hU (Set.subset_univ _) _ hEq).2 J.1 h0
  have hk : k J = ComplexVariables.partialOverFinset J.1 (multilinearPoly k) 0 := by
    rw [partialOverFinset_multilinearPoly_zero]
    simp only [extendByZero, dif_pos J.2]
  rw [hk, ← hloc, hval]
  refine Finset.sum_congr rfl fun π _ => ?_
  have hE : ComplexVariables.expComp (multilinearPoly k) 0 = 1 := by
    simp [ComplexVariables.expComp, multilinearPoly_zero]
  have hpos : 0 < SetPartition.blockCount π :=
    Finset.card_pos.2 (π.parts_nonempty (by simpa using J.2.ne_empty))
  obtain ⟨n, hn⟩ : ∃ n, SetPartition.blockCount π = n + 1 :=
    ⟨SetPartition.blockCount π - 1, by omega⟩
  rw [hE, hn, iteratedDeriv_succ_log Complex.one_mem_slitPlane, one_zpow, mul_one,
    Nat.add_sub_cancel, blockProduct_eq_prod]
  congr 1
  refine Finset.prod_congr rfl fun I hI => ?_
  simp only [_root_.YangMills.Construction.Cumulants.extendByZero, dif_pos (π.nonempty_of_mem_parts hI)]
  rfl
theorem partitionSum_eq_add_sum_erase (a : SubsetFamily q) (J : NonemptyFinSubset q) :
    partitionSum a J = a J + ∑ π ∈ Finset.univ.erase
      (Finpartition.indiscrete (by simpa using J.2.ne_empty) : SetPartition.Partitions J.1),
      blockProduct a π := by
  have hne : J.1 ≠ ⊥ := by simpa using J.2.ne_empty
  have hone : blockProduct a (Finpartition.indiscrete hne : SetPartition.Partitions J.1) = a J := by
    rw [blockProduct_eq_prod]
    simp [Finpartition.indiscrete, _root_.YangMills.Construction.Cumulants.extendByZero, J.2]
  rw [partitionSum, ← Finset.add_sum_erase Finset.univ _
    (Finset.mem_univ (Finpartition.indiscrete hne : SetPartition.Partitions J.1)), hone]
theorem partitionSum_sub_congr (HS : SetPartition.Elementary.BasicFacts) (a b : SubsetFamily q)
    (J : NonemptyFinSubset q) (hab : ∀ I : NonemptyFinSubset q, I.1 ⊂ J.1 → a I = b I) :
    partitionSum a J - a J = partitionSum b J - b J := by
  rw [partitionSum_eq_add_sum_erase, partitionSum_eq_add_sum_erase, add_sub_cancel_left,
    add_sub_cancel_left]
  refine Finset.sum_congr rfl fun π hπ => ?_
  rw [blockProduct_eq_prod, blockProduct_eq_prod]
  refine Finset.prod_congr rfl fun I hI => ?_
  have hparts : π.parts ≠ {J.1} := by
    intro h
    refine (Finset.mem_erase.1 hπ).1 (Finpartition.ext ?_)
    simpa [Finpartition.indiscrete] using h
  have hsub : I ⊂ J.1 := (HS.2.1 (Fin q) J.1).2 J.2.ne_empty |>.2 π hparts I hI
  have hnI := π.nonempty_of_mem_parts hI
  simp only [_root_.YangMills.Construction.Cumulants.extendByZero, dif_pos hnI]
  exact hab ⟨I, hnI⟩ hsub
theorem exists_partitionSum_eq_of_card_le (HS : SetPartition.Elementary.BasicFacts)
    (m : SubsetFamily q) (n : ℕ) :
    ∃ k : SubsetFamily q, ∀ J : NonemptyFinSubset q, J.1.card ≤ n → partitionSum k J = m J := by
  induction n with
  | zero =>
    refine ⟨fun _ => 0, fun J hJ => ?_⟩
    have := Finset.card_pos.2 J.2
    omega
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    classical
    let k' : SubsetFamily q :=
      fun J => if J.1.card = n + 1 then m J - (partitionSum k J - k J) else k J
    refine ⟨k', fun J hJ => ?_⟩
    have hsame : partitionSum k' J - k' J = partitionSum k J - k J := by
      refine partitionSum_sub_congr HS k' k J fun I hI => ?_
      have hlt := Finset.card_lt_card hI
      have hne : I.1.card ≠ n + 1 := by omega
      simp only [k', if_neg hne]
    by_cases hc : J.1.card = n + 1
    · have hv : k' J = m J - (partitionSum k J - k J) := by simp only [k', if_pos hc]
      linear_combination hsame + hv
    · have hv : k' J = k J := by simp only [k', if_neg hc]
      have hm := hk J (by omega)
      linear_combination hsame + hv + hm
theorem partitionSum_surjective (HS : SetPartition.Elementary.BasicFacts) :
    Function.Surjective (partitionSum (q := q)) := by
  intro m
  obtain ⟨k, hk⟩ := exists_partitionSum_eq_of_card_le HS m q
  refine ⟨k, funext fun J => hk J ?_⟩
  simpa using Finset.card_le_univ J.1
theorem partitionSubstitutionsInverse_holds
    (HF : ComplexVariables.HolomorphicFacts.StandardFacts)
    (HC : CompositeDerivative.PartitionChainRule)
    (HS : SetPartition.Elementary.BasicFacts) :
    PartitionSubstitutionsInverse := by
  intro q hq
  have hL : Function.LeftInverse (moebiusPartitionSum (q := q)) (partitionSum (q := q)) := by
    intro k
    have hm : expDerivFamily k = partitionSum k :=
      funext fun J => (expDeriv_eq_partitionSum HF HC hq k J).2
    rw [← hm]
    exact (funext fun J => eq_moebiusPartitionSum_expDerivFamily HF HC hq k J).symm
  have hS := partitionSum_surjective (q := q) HS
  have hR : Function.RightInverse (moebiusPartitionSum (q := q)) (partitionSum (q := q)) := by
    intro m
    obtain ⟨k, rfl⟩ := hS m
    rw [hL k]
  refine ⟨fun k => ⟨multilinearPoly_zero k, fun J => ⟨?_, ?_⟩,
      fun J => expDeriv_eq_partitionSum HF HC hq k J,
      fun J => eq_moebiusPartitionSum_expDerivFamily HF HC hq k J⟩,
    fun m => ⟨moebiusPartitionSum m, hR m, fun k hk => ?_⟩,
    ⟨hL.injective, hS⟩, ⟨hR.injective, hL.surjective⟩, hL, hR, fun _ => rfl, fun _ => rfl⟩
  · exact ((HF q hq Set.univ isOpen_univ).1 _ (multilinearPoly_isEntire HF hq k)).2.2.1 J.1 |>.1
  · rw [partialOverFinset_multilinearPoly_zero]
    simp only [extendByZero, dif_pos J.2]
  · exact hL.injective (hk.trans (hR m).symm)
end YangMills.Construction.Cumulants
