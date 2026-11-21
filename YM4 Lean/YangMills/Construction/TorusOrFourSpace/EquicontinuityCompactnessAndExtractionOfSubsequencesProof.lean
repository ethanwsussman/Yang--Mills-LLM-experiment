import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsOnProductsOfC1ClassesProof
import YangMills.Construction.Analysis.MultilinearTelescopingBound
import YangMills.Construction.Functions.PropertiesOfTheTopologyOfAFamily
import YangMills.Construction.ReflectionPositivity.NestedLatticesAdicPointsAndMirrorsProof
import YangMills.Construction.TorusOrFourSpace.BoundOfC1FormsAtEveryRadius
import YangMills.Construction.TorusOrFourSpace.ClassC1FunctionsProductsAndNeighbourhoods
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNorm
import YangMills.Construction.TorusOrFourSpace.CompactSetsHaveFiniteDiameters
import YangMills.Construction.TorusOrFourSpace.CountableFamilyOfACountableChoice
import YangMills.Construction.TorusOrFourSpace.EquicontinuityCompactnessAndExtractionOfSubsequences
import YangMills.Construction.TorusOrFourSpace.FactsOnTheEffectiveConstants
import YangMills.Construction.TorusOrFourSpace.FromTheFamilyToAllSeparatedTuples
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesInBallsAndTheirSeparation
import YangMills.Construction.TorusOrFourSpace.UniformApproximationOnHierarchiesObeyingABoundFunction
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal Topology
open Filter
noncomputable section
namespace YangMills.Construction.PeriodicSpace.EquicontinuityCompactness
open Kind
section Bounds
variable {D : Params} {E : Kind}
theorem abs_le_mul_prod_toReal {n : ℕ} {x c : ℝ} {s : Fin n → ℝ≥0∞} (hc : 0 ≤ c)
    (hs : ∀ i, s i < ∞) (h : ENNReal.ofReal |x| ≤ ENNReal.ofReal c * ∏ i, s i) :
    |x| ≤ c * ∏ i, (s i).toReal := by
  have hfin : ENNReal.ofReal c * ∏ i, s i ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.prod_ne_top fun i _ => (hs i).ne)
  have := ENNReal.toReal_mono hfin h
  rwa [ENNReal.toReal_ofReal (abs_nonneg x), ENNReal.toReal_mul, ENNReal.toReal_ofReal hc,
    ENNReal.toReal_prod] at this
theorem ofReal_abs_le_of_approx {z : ℝ} {B : ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → ∃ x : ℝ, |x - z| < ε ∧ ENNReal.ofReal |x| ≤ B) :
    ENNReal.ofReal |z| ≤ B := by
  by_cases hB : B = ∞
  · simp [hB]
  have hB' : ∀ ε : ℝ, 0 < ε → |z| ≤ B.toReal + ε := by
    intro ε hε
    obtain ⟨x, hx, hxB⟩ := h ε hε
    have h1 : |x| ≤ B.toReal := by
      have := ENNReal.toReal_mono hB hxB
      rwa [ENNReal.toReal_ofReal (abs_nonneg x)] at this
    have h2 : |z| ≤ |x| + |x - z| := by
      have := abs_sub_abs_le_abs_sub z x
      rw [abs_sub_comm z x] at this
      linarith
    linarith
  have h3 : |z| ≤ B.toReal := le_of_forall_pos_le_add hB'
  calc ENNReal.ofReal |z| ≤ ENNReal.ofReal B.toReal := ENNReal.ofReal_le_ofReal h3
    _ = B := ENNReal.ofReal_toReal hB
theorem sharpNormQ_lt_top (hC1 : C1ProductsAndThickenings.Statement)
    (hV : VectorClasses.Claim) {n : ℕ} (hn : 1 ≤ n)
    {f : FnTuple D E n} (hf : f ∈ sepC1Tuples D E n) (i : Fin n) :
    sharpNormQ D E (f i) < ∞ :=
  (hV D E).2.1.2.lt_top _ ⟨((hC1 D E).1.2.2 n hn hf).1 i, hf.2.1 i, Set.subset_univ _⟩
theorem multilinear_apply_eq_zero {n : ℕ} {K : Set (FnTuple D E n)} {Ψ : K → ℝ}
    (hΨ : IsMultilinearOn D E K Ψ) (h : K) (i : Fin n) (hi : h.1 i = 0) : Ψ h = 0 := by apply _root_.YangMills.DeltaSharedProofs.p500495 <;> assumption
theorem mem_productSet_of_supports {n : ℕ} {f : FnTuple D E n} (hf : f ∈ sepC1Tuples D E n)
    {A : Fin n → Set (E.Pt D)} (hA : ∀ l, supportQ D E (f l) ⊆ A l) :
    f ∈ productSet D E fun l => c1SupportedIn D E (A l) :=
  fun l _ => ⟨hf.1 l, hf.2.1 l, hA l⟩
theorem supports_inBalls (hT : SeparatedTupleFacts.SeparatedTupleBasics)
    (hB : CompactSupportDiameters.FiniteDiameters) {n : ℕ} (hn : 2 ≤ n) {φ : FnTuple D E n}
    (hφ : φ ∈ sepC1Tuples D E n) (hfin : supportGap D E φ < ∞) :
    0 < (supportGap D E φ).toReal ∧ 0 < tupleRadius D E φ ∧
      InBallsAndSeparated D E (fun i => supportQ D E (φ i))
        (supportGap D E φ).toReal (tupleRadius D E φ) := by
  have hpos := ((hT D E n hn φ hφ).2.1).1.1
  have hR := ((hB D E).2 n (by omega) φ hφ)
  refine ⟨ENNReal.toReal_pos hpos.ne' hfin.ne, ?_, hR.2, ?_⟩
  · exact ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one hR.1.1).ne' hR.1.2.ne
  · intro l l' hll
    rw [ENNReal.ofReal_toReal hfin.ne]
    exact (iInf_le _ l).trans ((iInf_le _ l').trans (iInf_le _ hll))
theorem tupleRadius_pos (hB : CompactSupportDiameters.FiniteDiameters) {n : ℕ} (hn : 1 ≤ n)
    {φ : FnTuple D E n} (hφ : φ ∈ sepC1Tuples D E n) : 0 < tupleRadius D E φ := by
  have hR := ((hB D E).2 n hn φ hφ)
  exact ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one hR.1.1).ne' hR.1.2.ne
variable {θ : RadiusRatio}
theorem tupleBound_nonneg (hFacts : EffectiveConstantFacts.Claim)
    (hT : SeparatedTupleFacts.SeparatedTupleBasics)
    (hB : CompactSupportDiameters.FiniteDiameters) (P : TorusPartitionChoice D θ)
    (C : BoundFamily) {n : ℕ} {φ : FnTuple D E n}
    (hφ : φ ∈ sepC1Tuples D E n) : 0 ≤ tupleBound E P C φ := by
  by_cases h : 2 ≤ n ∧ supportGap D E φ < ∞
  · rw [tupleBound_of_supportGap_lt_top P C h.1 φ h.2]
    obtain ⟨hd, hR, -⟩ := supports_inBalls hT hB h.1 hφ h.2
    exact mul_nonneg (hFacts.2.2.1 D θ P E C n h.1 _ _ hd hR)
      (Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)
  · have : tupleBound E P C φ = 0 := if_neg h
    rw [this]
theorem abs_le_tupleBound (hFacts : EffectiveConstantFacts.Claim)
    (hC1 : C1ProductsAndThickenings.Statement)
    (hV : VectorClasses.Claim)
    (hT : SeparatedTupleFacts.SeparatedTupleBasics)
    (hB : CompactSupportDiameters.FiniteDiameters) (P : TorusPartitionChoice D θ)
    (C : BoundFamily) {n : ℕ} (hn : 2 ≤ n) {φ : FnTuple D E n}
    (hφ : φ ∈ sepC1Tuples D E n) {K : Set (FnTuple D E n)} {Ψ : K → ℝ}
    (hM : IsMultilinearOn D E K Ψ) (hK : φ ∈ K)
    (hO : supportGap D E φ < ∞ →
      BoundedEquicontOnClasses D E K Ψ (fun l => c1SupportedIn D E (supportQ D E (φ l)))
        (effConstAt P E C n (supportGap D E φ).toReal
          (tupleRadius D E φ))) :
    |Ψ ⟨φ, hK⟩| ≤ tupleBound E P C φ := by
  by_cases hfin : supportGap D E φ < ∞
  · rw [tupleBound_of_supportGap_lt_top P C hn φ hfin]
    obtain ⟨hd, hR, -⟩ := supports_inBalls hT hB hn hφ hfin
    have hmem := mem_productSet_of_supports hφ (A := fun i => supportQ D E (φ i)) fun _ => subset_rfl
    exact abs_le_mul_prod_toReal (hFacts.2.2.1 D θ P E C n hn _ _ hd hR)
      (sharpNormQ_lt_top hC1 hV (by omega) hφ) ((hO hfin).2.1 ⟨φ, hK⟩ hmem)
  · have htop : supportGap D E φ = ∞ := le_antisymm le_top (not_lt.mp hfin)
    obtain ⟨i, hi⟩ := ((hT D E n hn φ hφ).2.2 htop).1
    rw [multilinear_apply_eq_zero hM ⟨φ, hK⟩ i hi, tupleBound_of_supportGap_eq_top P C φ htop, abs_zero]
end Bounds
section HeadAndEquicontinuity
theorem headClaims_hold (hFacts : EffectiveConstantFacts.Claim) (D : Params) (E : Kind)
    (θ : RadiusRatio) (P : TorusPartitionChoice D θ) (C : BoundFamily) :
    HeadClaims D E θ P C := by
  refine ⟨allowedRadii_euclidean D, allowedRadii_torus_eq_Ioo_half_pow D,
    ballRadius_mem_allowedRadii D θ E, hFacts.1 D θ P E, hFacts.2.2.2.2,
    fun n hn d R hd hR => ⟨fun h => effConstAt_of_mem P E C n d h,
      fun h => effConstAt_of_not_mem P E C n d h, ?_⟩⟩
  rintro rfl
  exact hFacts.2.2.2.1 D θ P C n hn d R hd hR
theorem equicontinuityPart_holds (hV : VectorClasses.Claim)
    (hForms : Multilinear.MultilinearTelescopingBound) (D : Params) (E : Kind)
    (C : BoundFamily) : EquicontinuityPart D E C := by
  intro n hn d R hd A hball _ Ψ hΨ hbound f g
  have hR : 0 < R := by
    obtain ⟨S, hS, -⟩ := hball ⟨0, by omega⟩
    exact hS.1
  have hc : 0 ≤ C.val n d R := C.nonneg n hn d R hd hR
  have hclass : ∀ l, {h | IsLipschitzQ D E h ∧ supportQ D E h ⊆ A l} =
      lipschitzSupportedIn D E (A l) := by
    intro l
    obtain ⟨S, hS, hAS⟩ := hball l
    exact ((hV D E).2.2 (A l) ⟨S, R, hS, hAS⟩).2.1.symm
  choose W hW using fun l => ((hV D E).1 (A l)).1
  have hWm : ∀ l (h : W l), (h : E.Pt D → ℝ) ∈
      {h | IsLipschitzQ D E h ∧ supportQ D E h ⊆ A l} := by
    intro l h
    rw [hclass l, ← hW l]
    exact h.2
  have hWin : ∀ l u, u ∈ {h | IsLipschitzQ D E h ∧ supportQ D E h ⊆ A l} → u ∈ W l := by
    intro l u hu
    rw [hclass l, ← hW l] at hu
    exact hu
  have hN := (hV D E).2.1.2
  have hUniv : ∀ l (h : W l), (h : E.Pt D → ℝ) ∈ lipschitzSupportedIn D E Set.univ := by
    intro l h
    have h' : (h : E.Pt D → ℝ) ∈ lipschitzSupportedIn D E (A l) := by
      rw [← hW l]
      exact h.2
    exact ⟨h'.1, h'.2.1, Set.subset_univ _⟩
  have hAdd : ∀ l (x y : W l), sharpNormReal D E ((x + y : W l) : E.Pt D → ℝ) ≤
      sharpNormReal D E (x : E.Pt D → ℝ) + sharpNormReal D E (y : E.Pt D → ℝ) := by
    intro l x y
    have hx := (hN.lt_top _ (hUniv l x)).ne
    have hy := (hN.lt_top _ (hUniv l y)).ne
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hx, hy⟩)
      (hN.add_le _ (hUniv l x) _ (hUniv l y))
    rwa [ENNReal.toReal_add hx hy] at this
  have hSmul : ∀ l (a : ℝ) (x : W l), sharpNormReal D E ((a • x : W l) : E.Pt D → ℝ) =
      ‖a‖ * sharpNormReal D E (x : E.Pt D → ℝ) := by
    intro l a x
    have := hN.smul _ (hUniv l x) a
    simp only [sharpNormReal, Submodule.coe_smul]
    rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg a), Real.norm_eq_abs]
  let p : ∀ l, Seminorm ℝ (W l) := fun l =>
    Seminorm.of (fun h => sharpNormReal D E (h : E.Pt D → ℝ)) (hAdd l) (hSmul l)
  have hmem : ∀ x : (∀ l, W l), (fun l => (x l : E.Pt D → ℝ)) ∈
      lipschitzTuplesSupportedIn D E A := fun x l _ => hWm l (x l)
  have hU : ∀ (m : ∀ l, W l) (i : Fin n) (x : W i),
      (fun l => (Function.update m i x l : E.Pt D → ℝ)) =
        Function.update (fun l => (m l : E.Pt D → ℝ)) i (x : E.Pt D → ℝ) := by
    intro m i x
    funext l
    by_cases h : l = i
    · subst h
      simp
    · simp [Function.update_of_ne h]
  have hUm : ∀ (m : ∀ l, W l) (i : Fin n) (x : W i),
      Function.update (fun l => (m l : E.Pt D → ℝ)) i (x : E.Pt D → ℝ) ∈
        lipschitzTuplesSupportedIn D E A := by
    intro m i x
    rw [← hU]
    exact hmem _
  have hlin : ∀ (m : ∀ l, W l) (i : Fin n) (x y : W i) (α β : ℝ),
      Ψ ⟨_, hmem (Function.update m i (α • x + β • y))⟩ =
        α * Ψ ⟨_, hmem (Function.update m i x)⟩ + β * Ψ ⟨_, hmem (Function.update m i y)⟩ := by
    intro m i x y α β
    have key := hΨ.2 (fun l => (m l : E.Pt D → ℝ)) (hmem m) i x (hWm i x) y (hWm i y) α β
      (hUm m i x) (hUm m i y) (hUm m i (α • x + β • y))
    have e0 : Ψ ⟨_, hmem (Function.update m i (α • x + β • y))⟩ =
        Ψ ⟨_, hUm m i (α • x + β • y)⟩ := congrArg Ψ (Subtype.ext (hU _ _ _))
    have e1 : Ψ ⟨_, hmem (Function.update m i x)⟩ = Ψ ⟨_, hUm m i x⟩ :=
      congrArg Ψ (Subtype.ext (hU _ _ _))
    have e2 : Ψ ⟨_, hmem (Function.update m i y)⟩ = Ψ ⟨_, hUm m i y⟩ :=
      congrArg Ψ (Subtype.ext (hU _ _ _))
    rw [e0, e1, e2]
    exact key
  let M : MultilinearMap ℝ (fun l => W l) ℝ :=
    { toFun := fun x => Ψ ⟨_, hmem x⟩
      map_update_add' := by
        intro inst m i x y
        obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
        simpa using hlin m i x y 1 1
      map_update_smul' := by
        intro inst m i a x
        obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
        simpa using hlin m i x x a 0 }
  have hb : ∀ h : ∀ l, W l, |M h| ≤ C.val n d R * ∏ l, p l (h l) := by
    intro h
    exact abs_le_mul_prod_toReal hc (fun l => hN.lt_top _ (hUniv l (h l))) (hbound ⟨_, hmem h⟩)
  let f' : ∀ l, W l := fun l => ⟨f.1 l, hWin l _ (f.2 l (Set.mem_univ l))⟩
  let g' : ∀ l, W l := fun l => ⟨g.1 l, hWin l _ (g.2 l (Set.mem_univ l))⟩
  exact hForms n (by omega) (fun l => W l) p (C.val n d R) hc M hb f' g'
end HeadAndEquicontinuity
section Topologies
open FamilyTopology
theorem isCompactViaCovers_of_compactSpace {S : Type} (T : TopologicalSpace S)
    (h : @CompactSpace S T) : IsCompactViaCovers T := by
  intro 𝒰 hU hcov
  obtain ⟨t, ht⟩ := (@isCompact_univ S T h).elim_finite_subcover
    (fun x : 𝒰 => (x : Set S)) (fun x => hU x x.2)
    (by
      intro y _
      have : y ∈ ⋃₀ 𝒰 := by
        rw [hcov]
        exact Set.mem_univ y
      obtain ⟨U, hU', hy⟩ := this
      exact Set.mem_iUnion.2 ⟨⟨U, hU'⟩, hy⟩)
  refine ⟨(fun x : 𝒰 => (x : Set S)) '' (t : Set 𝒰), ?_, t.finite_toSet.image _, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · refine Set.eq_univ_of_univ_subset fun y hy => ?_
    obtain ⟨x, hx⟩ := Set.mem_iUnion.1 (ht hy)
    obtain ⟨hxt, hy'⟩ := Set.mem_iUnion.1 hx
    exact ⟨x, ⟨x, hxt, rfl⟩, hy'⟩
theorem isMetrizableVia_of_metrizableSpace {S : Type} (T : TopologicalSpace S)
    (h : @TopologicalSpace.MetrizableSpace S T) : IsMetrizableVia T := by
  let := T
  have := h
  let := TopologicalSpace.metrizableSpaceMetric S
  have hball : ∀ (x : S) (r : ℝ), openBallOf dist x r = Metric.ball x r := by
    intro x r
    ext y
    simp [openBallOf, Metric.mem_ball, dist_comm]
  refine ⟨dist, ⟨fun _ _ => dist_nonneg, fun x y => dist_eq_zero, dist_comm, dist_triangle⟩, fun U => ?_⟩
  constructor
  · intro hU
    refine ⟨{B | (∃ x, ∃ r : ℝ, 0 < r ∧ B = openBallOf dist x r) ∧ B ⊆ U}, fun B hB => hB.1, ?_⟩
    ext y
    constructor
    · intro hy
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hU y hy
      exact ⟨Metric.ball y r, ⟨⟨y, r, hr, (hball y r).symm⟩, hsub⟩, Metric.mem_ball_self hr⟩
    · rintro ⟨B, hB, hy⟩
      exact hB.2 hy
  · rintro ⟨ℬ, hℬ, rfl⟩
    refine isOpen_sUnion fun B hB => ?_
    obtain ⟨x, r, -, rfl⟩ := hℬ B hB
    rw [hball]
    exact Metric.isOpen_ball
theorem boxTopology_eq_subtype
    (hT : FamilyTopology.Properties.IsCoarsestMakingContinuous) {𝔄 : Type}
    (c : 𝔄 → ℝ≥0) :
    boxTopology c = instTopologicalSpaceSubtype := by
  obtain ⟨-, hcont, hmin⟩ := hT (intervalBox c) 𝔄 (boxCoord c)
  apply le_antisymm
  · refine continuous_iff_le_induced.1 ?_
    exact @continuous_pi _ _ _ (boxTopology c) _ _ fun α => hcont α
  · refine fun U hU => hmin instTopologicalSpaceSubtype (fun α => ?_) U hU
    exact (continuous_apply α).comp continuous_subtype_val
theorem closedEmbedding_consequences
    (hT : FamilyTopology.Properties.IsCoarsestMakingContinuous) {H 𝔄 : Type}
    [Countable 𝔄] (TH : TopologicalSpace H) (c : 𝔄 → ℝ≥0) (g : H → intervalBox c)
    (hg : @Topology.IsClosedEmbedding H _ TH instTopologicalSpaceSubtype g) :
    IsCompactViaCovers TH ∧ IsMetrizableVia TH ∧
      IsCompactViaCovers (boxTopology c) ∧
      IsMetrizableVia (boxTopology c) ∧
      @Topology.IsClosedEmbedding H _ TH (boxTopology c) g := by
  rw [boxTopology_eq_subtype hT c]
  have hPc : CompactSpace (intervalBox c) := by
    rw [← isCompact_iff_compactSpace]
    have : intervalBox c = Set.pi Set.univ fun α => Set.Icc (-(c α : ℝ)) (c α) := by
      ext p
      constructor
      · intro h α _
        exact abs_le.1 (h α)
      · intro h α
        exact abs_le.2 (h α (Set.mem_univ α))
    rw [this]
    exact isCompact_univ_pi fun α => isCompact_Icc
  have hPm : TopologicalSpace.MetrizableSpace (intervalBox c) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  let := TH
  have hHc : CompactSpace H := hg.compactSpace
  have hHm : TopologicalSpace.MetrizableSpace H := hg.isEmbedding.metrizableSpace
  exact ⟨isCompactViaCovers_of_compactSpace _ hHc, isMetrizableVia_of_metrizableSpace _ hHm,
    isCompactViaCovers_of_compactSpace _ hPc, isMetrizableVia_of_metrizableSpace _ hPm, hg⟩
theorem tendsto_pnat_iff_int (x : ℕ+ → ℝ) (z : ℝ) :
    Tendsto x atTop (𝓝 z) ↔
      ∀ ε : ℝ, 0 < ε → ∃ j' : ℤ, ∀ j : ℕ+, j' ≤ ((j : ℕ) : ℤ) → |x j - z| < ε := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨((N : ℕ) : ℤ), fun j hj => ?_⟩
    have := hN j ((PNat.coe_le_coe _ _).1 (by exact_mod_cast hj))
    rwa [Real.dist_eq] at this
  · intro h ε hε
    obtain ⟨j', hj'⟩ := h ε hε
    refine ⟨Nat.succPNat j'.toNat, fun j hj => ?_⟩
    rw [Real.dist_eq]
    refine hj' j ?_
    have : j'.toNat + 1 ≤ (j : ℕ) := (PNat.coe_le_coe _ _).2 hj
    omega
theorem tendsto_pnat_coe_atTop : Tendsto (fun j : ℕ+ => (j : ℕ)) atTop atTop := by apply _root_.YangMills.Construction.ReflectionPositivity.AdicLattices.tendsto_pnat_coe_atTop <;> assumption
end Topologies
section Family
variable {D : Params} {E : Kind}
theorem isCountableDenseChoice_sets (F : DenseChoiceFamily D E) : IsCountableDenseChoice D E F.sets :=
  ⟨fun Q => ⟨(F.isDense Q).2.1, (F.isDense Q).2.2⟩,
    fun Q => (F.isDense Q).1⟩
theorem sepC1_of_mem_tuples (hFam : CountableChoiceFamilyFacts)
    (F : DenseChoiceFamily D E) {n : ℕ} {φ : FnTuple D E n}
    (h : (⟨n, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ F.tuples) :
    φ ∈ sepC1Tuples D E n := by
  obtain ⟨h1, Q, hQ⟩ := h
  exact (((hFam D E).2.2.2 F.sets (isCountableDenseChoice_sets F)).2 n φ Q ⟨h1, Q, hQ⟩ hQ).1
theorem countable_tuples (hFam : CountableChoiceFamilyFacts)
    (F : DenseChoiceFamily D E) : Countable F.tuples :=
  ((hFam D E).2.2.2 F.sets (isCountableDenseChoice_sets F)).1.to_subtype
theorem evalSigma_of_lt_two (Φ : Hierarchy D E) {φ : Σ n : ℕ, FnTuple D E n}
    (h : ¬ 2 ≤ φ.1) : Φ.evalSigma φ = 0 :=
  dif_neg fun h' => h h'.1
variable {θ : RadiusRatio}
theorem exists_uniform_approx (hU : UniformHierarchyApprox.Claim)
    (hT : SeparatedTupleFacts.SeparatedTupleBasics) (P : TorusPartitionChoice D θ)
    (F : DenseChoiceFamily D E) (C : BoundFamily) {n : ℕ} (hn : 2 ≤ n)
    (f : sepC1Tuples D E n) :
    ∃ (φ : ℕ+ → FnTuple D E n) (hφ : ∀ s, φ s ∈ sepC1Tuples D E n) (b : ℕ+ → ℝ),
      (∀ s, (⟨n, φ s⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ F.tuples) ∧
      Tendsto b atTop (𝓝 0) ∧
      ∀ s, ∀ Φ ∈ boundedHierarchies D E C,
        |Φ.func n hn f - Φ.func n hn ⟨φ s, hφ s⟩| ≤ b s := by
  obtain ⟨ρ, h0, htop, hρ⟩ := (hT D E n hn f.1 f.2).1
  have hr : 0 < ρ.toReal := ENNReal.toReal_pos h0.ne' htop.ne
  have hρ' : f.1 ∈ sepC1TuplesInBall D E n (ENNReal.ofReal ρ.toReal) := by
    rwa [ENNReal.ofReal_toReal htop.ne]
  obtain ⟨hd, -, -, hex, -, huni⟩ := hU.1 D E θ P F C n hn f.1 f.2 ρ.toReal hr hρ'
  choose φ hφ using hex
  obtain ⟨h2, h3, h4⟩ := huni φ hφ
  choose hsep hb using h3
  exact ⟨φ, hsep, _, fun s => (h2 s).1, h4, fun s Φ hΦ => hb s Φ hΦ⟩
theorem boundedDeterminedOn_holds (hU : UniformHierarchyApprox.Claim)
    (hT : SeparatedTupleFacts.SeparatedTupleBasics) (P : TorusPartitionChoice D θ)
    (F : DenseChoiceFamily D E) (C : BoundFamily) :
    BoundedDeterminedOn F C := by
  intro Φ hΦ Φ' hΦ' hv
  refine Hierarchy.ext ?_
  funext n hn f
  obtain ⟨φ, hφ, b, hF, hb, hle⟩ := exists_uniform_approx hU hT P F C hn f
  have hz : ∀ s, |Φ.func n hn f - Φ'.func n hn f| ≤ 2 * b s := by
    intro s
    have h1 := hle s Φ hΦ
    have h2 := hle s Φ' hΦ'
    have h3 : Φ.func n hn ⟨φ s, hφ s⟩ = Φ'.func n hn ⟨φ s, hφ s⟩ := by
      have := hv _ (hF s)
      rwa [Φ.evalSigma_of_sep hn ⟨φ s, hφ s⟩,
        Φ'.evalSigma_of_sep hn ⟨φ s, hφ s⟩] at this
    rw [h3] at h1
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have h4 : Tendsto (fun s => 2 * b s) atTop (𝓝 0) := by
    simpa using hb.const_mul 2
  have h5 := ge_of_tendsto' h4 hz
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h5)
variable {J₀ : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞} {C : BoundFamily}
theorem tendsTo_of_restrictFamily {Ψ : BoundedC1FormSeq D E J₀ ρ C} {J : Sequences.PNatIndexSet}
    {hJ : J.carrier ⊆ J₀.carrier}
    {hdef : SeparatedExtension.EventuallyDefinedAlong Ψ hJ}
    {Ξ : Hierarchy D E}
    (h : (SeparatedExtension.restrictFamily Ψ hJ hdef).TendsToOnSep Ξ)
    {n : ℕ} (hn : 2 ≤ n) (f : sepC1Tuples D E n) {ε : ℝ} (hε : 0 < ε) :
    ∃ j' : ℤ, ∀ (j : ℕ+) (hj : j ∈ J.carrier), j' ≤ ((j : ℕ) : ℤ) →
      ∃ hfj : f.1 ∈ sepC1TuplesInBall D E n (ρ ⟨j, hJ hj⟩),
        |Ψ.func ⟨j, hJ hj⟩ n hn ⟨f.1, hfj⟩ - Ξ.func n hn f| < ε := by
  obtain ⟨j₁, hf, hc⟩ := h n hn f
  obtain ⟨j₂, hj₂⟩ := hc ε hε
  refine ⟨max j₁ j₂, fun j hj hle => ?_⟩
  have hm : j ∈ (J.filterGe j₁).carrier := ⟨hj, (le_max_left _ _).trans hle⟩
  refine ⟨hf ⟨j, hm⟩, ?_⟩
  have := hj₂ j hj ((le_max_right _ _).trans hle) hm
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
  exact this
theorem hasLimitAt_of_int {Ψ : BoundedC1FormSeq D E J₀ ρ C} {J : Sequences.PNatIndexSet}
    (hJ : J.carrier ⊆ J₀.carrier) {m : ℕ} (hm : 2 ≤ m) {φ : FnTuple D E m} (j' : ℤ)
    (hg : ∀ j : (J.filterGe j').carrier,
      φ ∈ sepC1TuplesInBall D E m (ρ ⟨j.1, hJ j.2.1⟩)) (z : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ j'' : ℤ, ∀ j : (J.filterGe j').carrier, j'' ≤ (((j.1 : ℕ+) : ℕ) : ℤ) →
      |Ψ.func ⟨j.1, hJ j.2.1⟩ m hm ⟨φ, hg j⟩ - z| < ε) :
    SeparatedExtension.HasLimitAt Ψ hJ m hm φ := by
  refine ⟨j', hg, (z : ℂ), fun ε hε => ?_⟩
  obtain ⟨j'', h''⟩ := h ε hε
  refine ⟨j'', fun j _ hle hj => ?_⟩
  have := h'' ⟨j, hj⟩ hle
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact this
theorem exists_limit_in_boundedHierarchies (hK : C1FormSeqKinds.Statement)
    (hProp : SeparatedExtension.Statement)
    (hFam : CountableChoiceFamilyFacts) (P : TorusPartitionChoice D θ)
    (F : DenseChoiceFamily D E) (C : BoundFamily) (Φ : ℕ+ → Hierarchy D E)
    (hΦ : ∀ j, Φ j ∈ boundedHierarchies D E C)
    (hlim : ∀ φ ∈ F.tuples, ConvergesAtSigma Φ φ) :
    ∃ Ξ ∈ boundedHierarchies D E C, ∀ (n : ℕ) (hn : 2 ≤ n) (f : sepC1Tuples D E n),
      Tendsto (fun j => (Φ j).func n hn f) atTop (𝓝 (Ξ.func n hn f)) := by
  obtain ⟨Ψ, hΨ, -⟩ := (hK D θ E C).2.2.1 C1FormSeqKinds.allPNat
    (fun j => Φ j.1) (fun j => hΦ j.1)
  have hJ : C1FormSeqKinds.allPNat.carrier ⊆
      C1FormSeqKinds.allPNat.carrier := subset_rfl
  obtain ⟨hdef, Ξ, hconv, hmem⟩ := (hProp D E θ P F C).2.2
    C1FormSeqKinds.allPNat (fun _ => ∞) Ψ
    C1FormSeqKinds.allPNat hJ (by
      intro m hm φ hφ
      have hsep := sepC1_of_mem_tuples hFam F hφ.1
      obtain ⟨x, hx⟩ := hlim _ hφ.1
      have hg : ∀ j : (C1FormSeqKinds.allPNat.filterGe 0).carrier,
          φ ∈ sepC1TuplesInBall D E m ∞ := fun _ => by
        rw [sepC1TuplesInBall_top]
        exact hsep
      refine hasLimitAt_of_int hJ hm 0 hg x fun ε hε => ?_
      obtain ⟨j', hj'⟩ := (tendsto_pnat_iff_int _ _).1 hx ε hε
      refine ⟨j', fun j hle => ?_⟩
      have := hj' j.1 hle
      rw [(Φ j.1).evalSigma_of_sep hm ⟨φ, hsep⟩] at this
      rw [hΨ.2 ⟨j.1, hJ j.2.1⟩ m hm ⟨φ, hg j⟩]
      exact this)
  refine ⟨Ξ, hmem, fun n hn f => ?_⟩
  rw [tendsto_pnat_iff_int]
  intro ε hε
  obtain ⟨j', hj'⟩ := tendsTo_of_restrictFamily hconv hn f hε
  refine ⟨j', fun j hle => ?_⟩
  obtain ⟨hfj, hlt⟩ := hj' j trivial hle
  rw [hΨ.2 ⟨j, hJ trivial⟩ n hn ⟨f.1, hfj⟩] at hlt
  exact hlt
theorem tendsto_evalSigma (hFam : CountableChoiceFamilyFacts)
    (F : DenseChoiceFamily D E) {Φ : ℕ+ → Hierarchy D E} {Ξ : Hierarchy D E}
    (h : ∀ (n : ℕ) (hn : 2 ≤ n) (f : sepC1Tuples D E n),
      Tendsto (fun j => (Φ j).func n hn f) atTop (𝓝 (Ξ.func n hn f)))
    {φ : Σ n : ℕ, FnTuple D E n} (hφ : φ ∈ F.tuples) :
    Tendsto (fun j => (Φ j).evalSigma φ) atTop (𝓝 (Ξ.evalSigma φ)) := by
  obtain ⟨n, φ⟩ := φ
  by_cases hn : 2 ≤ n
  · have hsep := sepC1_of_mem_tuples hFam F hφ
    simp only [fun Φ : Hierarchy D E => Φ.evalSigma_of_sep hn ⟨φ, hsep⟩]
    exact h n hn ⟨φ, hsep⟩
  · simp only [fun Φ : Hierarchy D E => evalSigma_of_lt_two Φ
      (φ := ⟨n, φ⟩) hn]
    exact tendsto_const_nhds
theorem ofHierarchy_tendsToOnSep_iff {Φ : C1FormSeqKinds.allPNat.carrier →
      Hierarchy D E} {Ξ : Hierarchy D E} :
    (IndexedFunctionalFamily.ofHierarchy Φ).TendsToOnSep Ξ ↔
      ∀ (n : ℕ) (hn : 2 ≤ n) (f : sepC1Tuples D E n),
        Tendsto (fun j : ℕ+ => (Φ ⟨j, trivial⟩).func n hn f) atTop
          (𝓝 (Ξ.func n hn f)) := by
  constructor
  · intro h n hn f
    obtain ⟨j₁, hf, hc⟩ := h n hn f
    rw [tendsto_pnat_iff_int]
    intro ε hε
    obtain ⟨j₂, hj₂⟩ := hc ε hε
    refine ⟨max j₁ j₂, fun j hle => ?_⟩
    have hm : j ∈ (C1FormSeqKinds.allPNat.filterGe j₁).carrier :=
      ⟨trivial, (le_max_left _ _).trans hle⟩
    have := hj₂ j trivial ((le_max_right _ _).trans hle) hm
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  · intro h n hn f
    refine ⟨0, fun _ => f.2, fun ε hε => ?_⟩
    obtain ⟨j', hj'⟩ := (tendsto_pnat_iff_int _ _).1 (h n hn f) ε hε
    refine ⟨j', fun j _ hle hj => ?_⟩
    have := hj' j hle
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact this
end Family
section Compactness
open FamilyTopology
variable {D : Params} {E : Kind} {θ : RadiusRatio}
theorem evalMap_mem_intervalBox (hFacts : EffectiveConstantFacts.Claim)
    (hC1 : C1ProductsAndThickenings.Statement)
    (hV : VectorClasses.Claim)
    (hT : SeparatedTupleFacts.SeparatedTupleBasics)
    (hB : CompactSupportDiameters.FiniteDiameters)
    (hFam : CountableChoiceFamilyFacts)
    (hRad : UniformC1Bounds) (P : TorusPartitionChoice D θ)
    (F : DenseChoiceFamily D E) (C : BoundFamily) (Φ : boundedHierarchies D E C) :
    evalMap F C Φ ∈ intervalBox (tupleBoundsNN P F C) := by
  rintro ⟨⟨n, φ⟩, hφ⟩
  have hsep := sepC1_of_mem_tuples hFam F hφ
  show |Φ.1.evalSigma ⟨n, φ⟩| ≤ ((Real.toNNReal (tupleBound E P C φ) : ℝ≥0) : ℝ)
  have h0 := tupleBound_nonneg hFacts hT hB P C hsep
  rw [Real.coe_toNNReal _ h0]
  by_cases hn : 2 ≤ n
  · rw [Φ.1.evalSigma_of_sep hn ⟨φ, hsep⟩]
    refine abs_le_tupleBound hFacts hC1 hV hT hB P C hn hsep (Φ.1.multilinear n hn) hsep
      fun hfin => ?_
    obtain ⟨hd, hR, hA⟩ := supports_inBalls hT hB hn hsep hfin
    exact (hRad D E θ P C).2 Φ.1 Φ.2 n hn _ _ hd hR _ hA
  · rw [evalSigma_of_lt_two Φ.1 (φ := ⟨n, φ⟩) hn, abs_zero]
    exact h0
theorem continuous_of_uniform_approx {Z : Type} (TZ : TopologicalSpace Z) (u : Z → ℝ)
    (v : ℕ+ → Z → ℝ) (b : ℕ+ → ℝ) (hb : Tendsto b atTop (𝓝 0))
    (hv : ∀ s, @Continuous Z ℝ TZ _ (v s)) (hle : ∀ s z, |v s z - u z| ≤ b s) :
    @Continuous Z ℝ TZ _ u := by
  let := TZ
  have hu : TendstoUniformly v u atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hb.eventually (gt_mem_nhds hε)] with s hs z
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hle s z) hs
  exact hu.continuous (Eventually.of_forall hv).frequently
theorem continuous_comp_of_induced {A B : Type} [TB : TopologicalSpace B] (g : A → B) (h : B → ℝ)
    (hh : Continuous h) : @Continuous A ℝ (TopologicalSpace.induced g TB) _ (h ∘ g) := by
  let := TopologicalSpace.induced g TB
  exact hh.comp continuous_induced_dom
theorem evalMap_isClosedEmbedding (hU : UniformHierarchyApprox.Claim)
    (hT : SeparatedTupleFacts.SeparatedTupleBasics)
    (hFam : CountableChoiceFamilyFacts)
    (hK : C1FormSeqKinds.Statement)
    (hProp : SeparatedExtension.Statement) (P : TorusPartitionChoice D θ)
    (F : DenseChoiceFamily D E) (C : BoundFamily)
    (hMaps : ∀ Φ, evalMap F C Φ ∈ intervalBox (tupleBoundsNN P F C)) :
    @Topology.IsClosedEmbedding _ _
      (sepConvTopology (boundedHierarchies D E C))
      instTopologicalSpaceSubtype (fun Φ => ⟨evalMap F C Φ, hMaps Φ⟩) := by
  have hcount := countable_tuples hFam F
  let TH := sepConvTopology (boundedHierarchies D E C)
  let g : boundedHierarchies D E C → intervalBox (tupleBoundsNN P F C) :=
    fun Φ => ⟨evalMap F C Φ, hMaps Φ⟩
  have hev : ∀ φ : F.tuples,
      Continuous fun Φ : boundedHierarchies D E C => evalMap F C Φ φ := by
    rintro ⟨⟨n, φ⟩, hφ⟩
    by_cases hn : 2 ≤ n
    · have hsep := sepC1_of_mem_tuples hFam F hφ
      have e : (fun Φ : boundedHierarchies D E C => evalMap F C Φ ⟨⟨n, φ⟩, hφ⟩) =
          fun Φ => Hierarchy.evalAll Φ.1 ⟨⟨n, hn⟩, ⟨φ, hsep⟩⟩ := by
        funext Φ
        exact Φ.1.evalSigma_of_sep hn ⟨φ, hsep⟩
      rw [e]
      have hval : Continuous fun Φ : boundedHierarchies D E C => Hierarchy.evalAll Φ.1 :=
        continuous_induced_dom
      exact (continuous_apply (⟨⟨n, hn⟩, ⟨φ, hsep⟩⟩ : SepTuplesAll D E)).comp hval
    · have e : (fun Φ : boundedHierarchies D E C => evalMap F C Φ ⟨⟨n, φ⟩, hφ⟩) =
          fun _ => 0 := funext fun Φ => evalSigma_of_lt_two Φ.1 (φ := ⟨n, φ⟩) hn
      rw [e]
      exact continuous_const
  have hcont : Continuous g := Continuous.subtype_mk (continuous_pi hev) _
  have hind : Topology.IsInducing g := by
    refine ⟨le_antisymm (continuous_iff_le_induced.1 hcont) ?_⟩
    refine continuous_iff_le_induced.1 ?_
    refine @continuous_pi _ _ _ (TopologicalSpace.induced g _) _ _ fun x => ?_
    obtain ⟨⟨n, hn⟩, f⟩ := x
    obtain ⟨φ, hφ, b, hF, hb, hle⟩ := exists_uniform_approx hU hT P F C hn f
    refine continuous_of_uniform_approx _ _
      (fun s (Φ : boundedHierarchies D E C) => Φ.1.func n hn ⟨φ s, hφ s⟩) b hb
      (fun s => ?_) (fun s Φ => ?_)
    · have e : (fun Φ : boundedHierarchies D E C => Φ.1.func n hn ⟨φ s, hφ s⟩) =
          (fun p : intervalBox (tupleBoundsNN P F C) => p.1 ⟨⟨n, φ s⟩, hF s⟩) ∘ g := by
        funext Φ
        exact (Φ.1.evalSigma_of_sep hn ⟨φ s, hφ s⟩).symm
      rw [e]
      exact continuous_comp_of_induced g _ ((continuous_apply _).comp continuous_subtype_val)
    · rw [abs_sub_comm]
      exact hle s Φ.1 Φ.2
  have hinj : Function.Injective g := by
    intro Φ Φ' h
    have h' : evalMap F C Φ = evalMap F C Φ' := congrArg Subtype.val h
    exact Subtype.ext (boundedDeterminedOn_holds hU hT P F C Φ.1 Φ.2 Φ'.1 Φ'.2
      fun φ hφ => congrFun h' ⟨φ, hφ⟩)
  have hclosed : IsClosed (Set.range g) := by
    apply IsSeqClosed.isClosed
    intro x p hx hp
    choose Φ hΦ using hx
    have hcoord : ∀ φ : F.tuples,
        Tendsto (fun j : ℕ+ => (Φ (j : ℕ)).1.evalSigma φ.1) atTop (𝓝 (p.1 φ)) := by
      intro φ
      have h1 : Tendsto (fun k => (x k).1 φ) atTop (𝓝 (p.1 φ)) :=
        (((continuous_apply φ).comp continuous_subtype_val).tendsto p).comp hp
      have h2 := h1.comp tendsto_pnat_coe_atTop
      refine h2.congr fun j => ?_
      simp only [Function.comp, ← hΦ]
      rfl
    obtain ⟨Ξ, hΞ, hlim⟩ := exists_limit_in_boundedHierarchies hK hProp hFam P F C
      (fun j => (Φ (j : ℕ)).1) (fun j => (Φ (j : ℕ)).2)
      (fun φ hφ => ⟨_, hcoord ⟨φ, hφ⟩⟩)
    refine ⟨⟨Ξ, hΞ⟩, Subtype.ext (funext fun φ => ?_)⟩
    exact tendsto_nhds_unique (tendsto_evalSigma hFam F hlim φ.2) (hcoord φ)
  exact ⟨⟨hind, hinj⟩, hclosed⟩
theorem boundedHierarchies_isSeqClosed (D : Params) (E : Kind) (C : BoundFamily) :
    IsSeqClosedHierarchies (boundedHierarchies D E C) := by
  intro J Φ Ξ hΦ hc n hn d R hd hR f hf
  refine ofReal_abs_le_of_approx fun ε hε => ?_
  obtain ⟨j₁, hdom, hconv⟩ := hc n hn f
  obtain ⟨j₂, h₂⟩ := hconv ε hε
  obtain ⟨k, hk⟩ := (J.filterGe (max j₁ j₂)).infinite.nonempty
  have hm : k ∈ (J.filterGe j₁).carrier := ⟨hk.1, (le_max_left _ _).trans hk.2⟩
  have hlt := h₂ k hk.1 ((le_max_right _ _).trans hk.2) hm
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hlt
  exact ⟨_, hlt, hΦ ⟨k, hk.1⟩ n hn d R hd hR f hf⟩
theorem compactnessPart_holds (hFacts : EffectiveConstantFacts.Claim)
    (hC1 : C1ProductsAndThickenings.Statement)
    (hV : VectorClasses.Claim)
    (hT : SeparatedTupleFacts.SeparatedTupleBasics)
    (hB : CompactSupportDiameters.FiniteDiameters)
    (hFam : CountableChoiceFamilyFacts)
    (hRad : UniformC1Bounds)
    (hU : UniformHierarchyApprox.Claim)
    (hK : C1FormSeqKinds.Statement)
    (hProp : SeparatedExtension.Statement)
    (hCoarse : FamilyTopology.Properties.IsCoarsestMakingContinuous)
    (P : TorusPartitionChoice D θ) (F : DenseChoiceFamily D E) (C : BoundFamily) :
    CompactnessPart D E P F C := by
  have hMaps := evalMap_mem_intervalBox hFacts hC1 hV hT hB hFam hRad P F C
  have hemb := evalMap_isClosedEmbedding hU hT hFam hK hProp P F C hMaps
  have hcount := countable_tuples hFam F
  obtain ⟨h1, h2, h3, h4, h5⟩ := closedEmbedding_consequences hCoarse _ _ _ hemb
  refine ⟨h1, h2, boundedHierarchies_isSeqClosed D E C, ?_, ?_, ?_, ⟨hMaps, h3, h4, h5⟩,
    boundedDeterminedOn_holds hU hT P F C, ?_⟩
  · rintro ⟨n, φ⟩ hφ i
    exact ((hB D E).2 n hφ.1 φ (sepC1_of_mem_tuples hFam F hφ)).2 i
  · rintro ⟨n, φ⟩ hφ
    exact tupleBound_nonneg hFacts hT hB P C (sepC1_of_mem_tuples hFam F hφ)
  · rintro ⟨n, φ⟩ hφ hn hfin
    exact tupleBound_of_supportGap_lt_top P C hn φ hfin
  · intro Φ hΦ
    constructor
    · rintro ⟨Ξ, hΞ⟩ φ hφ
      exact ⟨_, tendsto_evalSigma hFam F (ofHierarchy_tendsToOnSep_iff.1 hΞ) hφ⟩
    · intro h
      obtain ⟨Ξ, -, hl⟩ := exists_limit_in_boundedHierarchies hK hProp hFam P F C Φ hΦ h
      exact ⟨Ξ, ofHierarchy_tendsToOnSep_iff.2 hl⟩
end Compactness
section Sequences
variable {D : Params} {E : Kind} {θ : RadiusRatio} {J₀ : Sequences.PNatIndexSet}
  {ρ : J₀.carrier → ℝ≥0∞} {C : BoundFamily}
def toPNatOfInt (j : ℤ) : ℕ+ := Nat.toPNat' j.toNat
theorem toPNatOfInt_natCast (k : ℕ+) : toPNatOfInt ((k : ℕ) : ℤ) = k := by
  apply PNat.eq
  simp [toPNatOfInt]
theorem coe_toPNatOfInt {j : ℤ} (hj : 1 ≤ j) : (((toPNatOfInt j : ℕ+) : ℕ) : ℤ) = j := by
  have h : 0 < j.toNat := by omega
  simp only [toPNatOfInt, Nat.toPNat'_coe, h, if_true]
  omega
theorem dite_mem_of_eq {A : Set ℕ+} (G : A → ℂ) {k p : ℕ+} (hk : k ∈ A) (hp : p = k) :
    (open Classical in if h : p ∈ A then G ⟨p, h⟩ else 0) = G ⟨k, hk⟩ := by
  subst hp
  exact dif_pos hk
theorem evalAt_eq_func {Φ : BoundedPartialHierarchySeq D E J₀ ρ C}
    {Ψ : BoundedC1FormSeq D E J₀ ρ C} (h : Ψ.IsRestrictionOf Φ) (j : J₀.carrier) {n : ℕ}
    (hn : 2 ≤ n) {f : FnTuple D E n} (hf : f ∈ sepC1TuplesInBall D E n (ρ j)) :
    Φ.toPartialHierarchySeq.evalAt j n hn f = Ψ.func j n hn ⟨f, hf⟩ := by
  obtain ⟨hL, e⟩ := h.2 j n hn ⟨f, hf⟩
  rw [e]
  exact Φ.toPartialHierarchySeq.evalAt_of_mem j hn ⟨f, hL⟩
theorem tendsToOnSepAlong_of_restrictFamily {Φ : BoundedPartialHierarchySeq D E J₀ ρ C}
    {Ψ : BoundedC1FormSeq D E J₀ ρ C} (hR : Ψ.IsRestrictionOf Φ) {J : Sequences.PNatIndexSet}
    {hJ : J.carrier ⊆ J₀.carrier}
    {hdef : SeparatedExtension.EventuallyDefinedAlong Ψ hJ}
    {Ξ : Hierarchy D E}
    (h : (SeparatedExtension.restrictFamily Ψ hJ hdef).TendsToOnSep Ξ) :
    Φ.toPartialHierarchySeq.TendsToOnSepAlong J hJ Ξ := by
  intro n hn f ε hε
  obtain ⟨j', hj'⟩ := tendsTo_of_restrictFamily h hn f hε
  refine ⟨j', fun j hj hle => ?_⟩
  obtain ⟨hfj, hlt⟩ := hj' j hj hle
  refine ⟨⟨hJ hj, hfj⟩, ?_⟩
  rw [Real.norm_eq_abs]
  show |Φ.toPartialHierarchySeq.evalAt ⟨j, hJ hj⟩ n hn f.1 - _| < ε
  rw [evalAt_eq_func hR _ hn hfj]
  exact hlt
theorem satisfiesSepEstimate_of_mem (hRad : UniformC1Bounds)
    (P : TorusPartitionChoice D θ) {Ξ : Hierarchy D E} (hΞ : Ξ ∈ boundedHierarchies D E C) :
    Ξ.SatisfiesSepEstimate C := by
  intro n hn d R hd hR A hball hdist f g hfg
  have hR0 : 0 < R := by
    obtain ⟨S, hS, -⟩ := hball ⟨0, by omega⟩
    exact hS.1
  have hO := (hRad D E θ P C).2 Ξ hΞ n hn d R hd hR0 A ⟨hball, hdist⟩
  rw [effConstAt_of_mem P E C n d hR] at hO
  exact hO.2.2 f g
    (mem_productSet_of_supports f.2 fun l => Set.subset_union_left.trans (hfg l))
    (mem_productSet_of_supports g.2 fun l => Set.subset_union_right.trans (hfg l))
theorem extractionPart_holds (hFacts : EffectiveConstantFacts.Claim)
    (hC1 : C1ProductsAndThickenings.Statement)
    (hV : VectorClasses.Claim)
    (hT : SeparatedTupleFacts.SeparatedTupleBasics)
    (hB : CompactSupportDiameters.FiniteDiameters)
    (hFam : CountableChoiceFamilyFacts)
    (hRad : UniformC1Bounds)
    (hK : C1FormSeqKinds.Statement)
    (hProp : SeparatedExtension.Statement)
    (hApprox : DiagonalLimits.FamilyApproximation.Statement)
    (hDiag : DiagonalSubsequence.CountableBoundedFamilyConverges)
    (P : TorusPartitionChoice D θ) (F : DenseChoiceFamily D E) (C : BoundFamily) :
    ExtractionPart D E P F C := by
  intro J₀ ρ Φ I _ start v hv
  obtain ⟨-, -, Ψ, hΨ⟩ := (hK D θ E C).2.1 J₀ ρ Φ
  have hdom := (hK D θ E C).1 J₀ ρ Ψ.toC1FormSeq
  constructor
  · have hcount := countable_tuples hFam F
    have hbd : ∀ φ : F.tuples, ∃ (s : ℤ) (B : ℝ), 1 ≤ s ∧ 0 ≤ B ∧
        ∀ j : J₀.carrier, s ≤ (((j.1 : ℕ+) : ℕ) : ℤ) →
          (∀ _ : 2 ≤ φ.1.1, φ.1.2 ∈ sepC1TuplesInBall D E φ.1.1 (ρ j)) ∧
          |Φ.toPartialHierarchySeq.evalSigma j φ.1| ≤ B := by
      rintro ⟨⟨n, φ⟩, hφ⟩
      by_cases hn : 2 ≤ n
      · have hsep := sepC1_of_mem_tuples hFam F hφ
        obtain ⟨jf, hjf⟩ := hdom n hn φ hsep
        have hR0 := tupleRadius_pos hB (by omega) hsep
        refine ⟨max 1 (max jf (Ψ.thresholdAtRadius θ n hn (tupleRadius D E φ) hR0)),
          tupleBound E P C φ, le_max_left _ _, tupleBound_nonneg hFacts hT hB P C hsep,
          fun j hj => ?_⟩
        have hj1 := (le_max_right _ _).trans hj
        have hjφ := hjf j ((le_max_left _ _).trans hj1)
        refine ⟨fun _ => hjφ, ?_⟩
        have e : Φ.toPartialHierarchySeq.evalSigma j ⟨n, φ⟩ =
            Φ.toPartialHierarchySeq.evalAt j n hn φ := dif_pos hn
        show |Φ.toPartialHierarchySeq.evalSigma j ⟨n, φ⟩| ≤ _
        rw [e, evalAt_eq_func hΨ j hn hjφ]
        refine abs_le_tupleBound hFacts hC1 hV hT hB P C hn hsep (Ψ.multilinear j n hn) hjφ
          fun hfin => ?_
        obtain ⟨hd, -, hA⟩ := supports_inBalls hT hB hn hsep hfin
        exact ((hRad D E θ P C).1 J₀ ρ Ψ n hn _ _ hd hR0 _ hA j
          ((le_max_right _ _).trans hj1) hjφ.2).2
      · refine ⟨1, 0, le_rfl, le_rfl, fun j _ => ⟨fun h => absurd h hn, ?_⟩⟩
        have e : Φ.toPartialHierarchySeq.evalSigma j ⟨n, φ⟩ = 0 := dif_neg hn
        show |Φ.toPartialHierarchySeq.evalSigma j ⟨n, φ⟩| ≤ 0
        rw [e, abs_zero]
    choose s B hs1 hB0 hsB using hbd
    classical
    let vs : F.tuples → ℤ → ℂ := fun φ j =>
      if h : toPNatOfInt j ∈ J₀.carrier then
        ((Φ.toPartialHierarchySeq.evalSigma ⟨toPNatOfInt j, h⟩ φ.1 : ℝ) : ℂ)
      else 0
    let start' : F.tuples ⊕ I → ℤ := Sum.elim s start
    let v' : ∀ ι : F.tuples ⊕ I, {j : ℤ // start' ι ≤ j} → ℂ := fun ι =>
      match ι with
      | Sum.inl φ => fun j => vs φ j.1
      | Sum.inr ι => v ι
    have hbdd : ∀ ι : F.tuples ⊕ I, ∃ c : ℝ, ∀ j : {j : ℤ // start' ι ≤ j}, ‖v' ι j‖ ≤ c := by
      rintro (φ | ι)
      · refine ⟨B φ, fun j => ?_⟩
        show ‖vs φ j.1‖ ≤ B φ
        have hj : s φ ≤ j.1 := j.2
        have hj1 : 1 ≤ j.1 := (hs1 φ).trans hj
        simp only [vs]
        split_ifs with h
        · rw [Complex.norm_real, Real.norm_eq_abs]
          refine (hsB φ ⟨_, h⟩ ?_).2
          show s φ ≤ (((toPNatOfInt j.1 : ℕ+) : ℕ) : ℤ)
          rw [coe_toPNatOfInt hj1]
          exact hj
        · simpa using hB0 φ
      · exact hv ι
    obtain ⟨J, hJ, hconv⟩ := hDiag (F.tuples ⊕ I) start' v' hbdd J₀
    have hLim : ∀ (m : ℕ) (hm : 2 ≤ m) (φ : FnTuple D E m),
        (⟨m, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ F.tuplesGeTwo →
          SeparatedExtension.HasLimitAt Ψ hJ m hm φ := by
      intro m hm φ hφ
      let x : F.tuples := ⟨⟨m, φ⟩, hφ.1⟩
      obtain ⟨z, hz⟩ := hconv (Sum.inl x)
      have hg : ∀ j : (J.filterGe (s x)).carrier,
          φ ∈ sepC1TuplesInBall D E m (ρ ⟨j.1, hJ j.2.1⟩) :=
        fun j => (hsB x ⟨j.1, hJ j.2.1⟩ j.2.2).1 hm
      refine ⟨s x, hg, z, (DiagonalLimits.tendsToAlong_iff_tendsTo J _ _ z).2 ?_⟩
      have e : (fun j : (J.filterGe (s x)).carrier =>
          ((Ψ.func ⟨j.1, hJ j.2.1⟩ m hm ⟨φ, hg j⟩ : ℝ) : ℂ)) =
          DiagonalSubsequence.restrictAlong (v' (Sum.inl x)) J := by
        funext j
        show _ = vs x (((j.1 : ℕ+) : ℕ) : ℤ)
        have e1 := dite_mem_of_eq
          (fun k : J₀.carrier =>
            ((Φ.toPartialHierarchySeq.evalSigma k x.1 : ℝ) : ℂ))
          (hJ j.2.1) (toPNatOfInt_natCast j.1)
        have e2 : Φ.toPartialHierarchySeq.evalSigma ⟨j.1, hJ j.2.1⟩ x.1 =
            Φ.toPartialHierarchySeq.evalAt ⟨j.1, hJ j.2.1⟩ m hm φ := dif_pos hm
        simp only [vs]
        rw [e1, e2, evalAt_eq_func hΨ _ hm (hg j)]
      rw [e]
      exact hz
    obtain ⟨hdef, Ξ, hconvΞ, hΞ⟩ := (hProp D E θ P F C).2.2 J₀ ρ Ψ J hJ hLim
    choose w hw using fun ι : I => hconv (Sum.inr ι)
    have hlimit : LimitsAlong Φ.toPartialHierarchySeq start v J hJ w Ξ :=
      ⟨fun ι => (DiagonalLimits.tendsToAlong_iff_tendsTo J _ _ _).2 (hw ι),
        tendsToOnSepAlong_of_restrictFamily hΨ hconvΞ⟩
    refine ⟨J, hJ, Ξ, w, hlimit, hΞ, fun n hn => satisfiesSepEstimate_of_mem hRad P hΞ n hn,
      fun J' hJ' => ⟨fun ι ε hε => ?_, fun n hn f ε hε => ?_⟩⟩
    · obtain ⟨j', h⟩ := hlimit.1 ι ε hε
      exact ⟨j', fun j hj hle hm => h j (hJ' hj) hle ⟨hJ' hm.1, hm.2⟩⟩
    · obtain ⟨j', h⟩ := hlimit.2 n hn f ε hε
      exact ⟨j', fun j hj hle => h j (hJ' hj) hle⟩
  · intro n hn f hf r hr d hd hlet
    have hd' : ENNReal.ofReal d ≤ supportGap D E f := by
      by_cases h : supportGap D E f = ∞
      · simp [h]
      · rw [hlet.1 h, ENNReal.ofReal_toReal h]
    have hrpos : 0 < r.toReal := ENNReal.toReal_pos hr.1.ne' hr.2.1.ne
    have hfr : f ∈ sepC1TuplesInBall D E n (ENNReal.ofReal r.toReal) := by
      rw [ENNReal.ofReal_toReal hr.2.1.ne]
      exact mem_sepC1TuplesInBall_of_supportsInBall D E hf hr
    have hA := hApprox D E F n hn f hf d hd hd'
    constructor
    · intro ε hε
      obtain ⟨-, ⟨φ, hφ⟩, -, -⟩ := hA ε hε
      obtain ⟨⟨j₁, hj₁⟩, huse⟩ := (hProp D E θ P F C).1 J₀ ρ Ψ n hn r.toReal hrpos f hfr d hd hd'
      refine ⟨φ, hφ.1, fun i => ⟨(hφ.2 i).2.1, fun y hy => ((hφ.2 i).2.2.1 hy).le⟩, j₁,
        fun j hj => ?_⟩
      obtain ⟨hfj, hφj, hle⟩ := huse j₁ hj₁ ε hε φ hφ j hj
      refine ⟨hfj, hφj, ?_⟩
      rw [evalAt_eq_func hΨ j hn hfj, evalAt_eq_func hΨ j hn hφj]
      exact hle
    · obtain ⟨-, -, -, hτ⟩ := hA 1 one_pos
      have := hτ.const_mul (effConstAt P E C n (d / 3) (r.toReal + d / 3))
      rw [mul_zero] at this
      exact this
theorem clusterPointPart_holds (hU : UniformHierarchyApprox.Claim)
    (hT : SeparatedTupleFacts.SeparatedTupleBasics)
    (hFam : CountableChoiceFamilyFacts)
    (hK : C1FormSeqKinds.Statement)
    (hProp : SeparatedExtension.Statement)
    (P : TorusPartitionChoice D θ) (F : DenseChoiceFamily D E) (C : BoundFamily) :
    ClusterPointPart D E C := by
  intro J₀ ρ Φ Ξ hcl
  obtain ⟨hsub, -, Ψ, hΨ⟩ := (hK D θ E C).2.1 J₀ ρ Φ
  have hdom := (hK D θ E C).1 J₀ ρ Ψ.toC1FormSeq
  have hΞ : Ξ ∈ boundedHierarchies D E C := by
    intro n hn d R hd hR f hf
    refine ofReal_abs_le_of_approx fun ε hε => ?_
    obtain ⟨jf, hjf⟩ := hdom n hn f.1 f.2
    obtain ⟨j, hj, hp⟩ := hcl {⟨⟨n, hn⟩, f⟩} ε hε (max (Φ.threshold n hn R hR) jf)
    obtain ⟨hdef, hlt⟩ := hp ⟨⟨n, hn⟩, f⟩ (Finset.mem_singleton_self _)
    have hL := hsub j n (by omega) hdef
    have hlt' : |Φ.toPartialHierarchySeq.evalAt j n hn f.1 - Ξ.func n hn f| < ε := hlt
    refine ⟨_, hlt', ?_⟩
    have e : Φ.toPartialHierarchySeq.evalAt j n hn f.1 =
        Φ.toPartialHierarchySeq.func j n hn ⟨f.1, hL⟩ :=
      Φ.toPartialHierarchySeq.evalAt_of_mem j hn ⟨f.1, hL⟩
    rw [e]
    exact Φ.boundedFrom n hn R hR j ((le_max_left _ _).trans hj) d hd ⟨f.1, hL⟩ hf
  let G : Set (SepTuplesAll D E) :=
    {x | (⟨x.1.1, x.2.1⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ F.tuples}
  have hGc : Countable G := by
    have hcount := countable_tuples hFam F
    refine Function.Injective.countable
      (f := fun x : G => (⟨⟨x.1.1.1, x.1.2.1⟩, x.2⟩ : F.tuples)) ?_
    rintro ⟨⟨⟨n, hn⟩, ⟨f, hf⟩⟩, hx⟩ ⟨⟨⟨m, hm⟩, ⟨g, hg⟩⟩, hy⟩ h
    have h' := congrArg Subtype.val h
    simp only [Sigma.mk.injEq] at h'
    obtain ⟨rfl, h'⟩ := h'
    obtain rfl := eq_of_heq h'
    rfl
  obtain ⟨e, he⟩ := exists_injective_nat G
  have hfin : ∀ k : ℕ, {x : G | e x ≤ k}.Finite := fun k =>
    (Set.finite_le_nat k).preimage he.injOn
  let S : ℕ → Finset (SepTuplesAll D E) := fun k =>
    ((hfin k).image Subtype.val).toFinset
  have hS : ∀ (x : G) (k : ℕ), e x ≤ k → x.1 ∈ S k := fun x k hk =>
    (Set.Finite.mem_toFinset _).2 ⟨x, hk, rfl⟩
  let Q : ℕ → ℕ → Prop := fun k m => ∃ (hm : 0 < m) (hj : (⟨m, hm⟩ : ℕ+) ∈ J₀.carrier),
    ∀ p ∈ S k, Φ.toPartialHierarchySeq.HoldsAt ⟨⟨m, hm⟩, hj⟩ p.1.2 p.2.1
      fun x => |x - Ξ.func p.1.1 p.1.2 p.2| < 1 / ((k : ℝ) + 1)
  have hQ : ∀ k, ∃ᶠ m in atTop, Q k m := by
    intro k
    refine frequently_atTop.2 fun a => ?_
    obtain ⟨j, hj, hq⟩ := hcl (S k) (1 / ((k : ℝ) + 1)) (by positivity) (a : ℤ)
    exact ⟨(j.1 : ℕ), by exact_mod_cast hj, j.1.pos, j.2, hq⟩
  obtain ⟨a, hmono, ha⟩ := extraction_forall_of_frequently hQ
  choose hpos hJ₀ hprop using ha
  have hinj : Function.Injective fun k => (⟨a k, hpos k⟩ : ℕ+) := fun k k' h =>
    hmono.injective (congrArg (fun j : ℕ+ => (j : ℕ)) h)
  let J : Sequences.PNatIndexSet := ⟨Set.range fun k => (⟨a k, hpos k⟩ : ℕ+),
    Set.infinite_range_of_injective hinj⟩
  have hJ : J.carrier ⊆ J₀.carrier := by
    rintro _ ⟨k, rfl⟩
    exact hJ₀ k
  have hkey : ∀ (x : G) (ε : ℝ), 0 < ε → ∃ K : ℕ, ∀ k, K ≤ k →
      Φ.toPartialHierarchySeq.IsDefinedAt ⟨⟨a k, hpos k⟩, hJ₀ k⟩ x.1.2.1 ∧
      |Φ.toPartialHierarchySeq.evalAt ⟨⟨a k, hpos k⟩, hJ₀ k⟩ x.1.1.1 x.1.1.2 x.1.2.1 -
        Ξ.func x.1.1.1 x.1.1.2 x.1.2| < ε := by
    intro x ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨max (e x) N, fun k hk => ?_⟩
    obtain ⟨hd, hlt⟩ := hprop k x.1 (hS x k ((le_max_left _ _).trans hk))
    refine ⟨hd, lt_of_lt_of_le hlt ?_⟩
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast (le_max_right _ _).trans hk
    exact (one_div_le_one_div_of_le (by positivity) (by linarith)).trans hN.le
  have hLim : ∀ (m : ℕ) (hm : 2 ≤ m) (φ : FnTuple D E m),
      (⟨m, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ F.tuplesGeTwo →
        SeparatedExtension.HasLimitAt Ψ hJ m hm φ := by
    intro m hm φ hφ
    have hsep := sepC1_of_mem_tuples hFam F hφ.1
    obtain ⟨jf, hjf⟩ := hdom m hm φ hsep
    have hg : ∀ j : (J.filterGe jf).carrier,
        φ ∈ sepC1TuplesInBall D E m (ρ ⟨j.1, hJ j.2.1⟩) :=
      fun j => hjf ⟨j.1, hJ j.2.1⟩ j.2.2
    refine hasLimitAt_of_int hJ hm jf hg (Ξ.func m hm ⟨φ, hsep⟩) fun ε hε => ?_
    obtain ⟨K, hK'⟩ := hkey ⟨⟨⟨m, hm⟩, ⟨φ, hsep⟩⟩, hφ.1⟩ ε hε
    refine ⟨((a K : ℕ) : ℤ) + 1, fun j hle => ?_⟩
    obtain ⟨j, hj⟩ := j
    obtain ⟨k, rfl⟩ := hj.1
    have hk : K ≤ k := by
      have : a K ≤ a k := by
        have h1 : ((a K : ℕ) : ℤ) + 1 ≤ ((a k : ℕ) : ℤ) := hle
        omega
      exact hmono.le_iff_le.1 this
    obtain ⟨-, hlt⟩ := hK' k hk
    have := evalAt_eq_func hΨ ⟨⟨a k, hpos k⟩, hJ₀ k⟩ hm (hg ⟨_, hj⟩)
    rw [← this]
    exact hlt
  obtain ⟨hdef, Ξ', hconv, hΞ'⟩ := (hProp D E θ P F C).2.2 J₀ ρ Ψ J hJ hLim
  have heq : Ξ' = Ξ := by
    refine boundedDeterminedOn_holds hU hT P F C Ξ' hΞ' Ξ hΞ ?_
    rintro ⟨n, φ⟩ hφ
    by_cases hn : 2 ≤ n
    · have hsep := sepC1_of_mem_tuples hFam F hφ
      rw [Ξ'.evalSigma_of_sep hn ⟨φ, hsep⟩, Ξ.evalSigma_of_sep hn ⟨φ, hsep⟩]
      refine sub_eq_zero.1 (abs_nonpos_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_))
      have hε2 : 0 < ε / 2 := by positivity
      obtain ⟨j', hj'⟩ := tendsTo_of_restrictFamily hconv hn ⟨φ, hsep⟩ hε2
      obtain ⟨K, hK'⟩ := hkey ⟨⟨⟨n, hn⟩, ⟨φ, hsep⟩⟩, hφ⟩ (ε / 2) hε2
      let k := max K j'.toNat
      have hk : j' ≤ ((a k : ℕ) : ℤ) := by
        have h1 : k ≤ a k := hmono.le_apply
        have h2 : j'.toNat ≤ k := le_max_right _ _
        omega
      obtain ⟨hfj, hlt⟩ := hj' ⟨a k, hpos k⟩ ⟨k, rfl⟩ hk
      obtain ⟨-, hlt'⟩ := hK' k (le_max_left _ _)
      have := evalAt_eq_func hΨ ⟨⟨a k, hpos k⟩, hJ₀ k⟩ hn hfj
      have hlt'' : |Ψ.func ⟨⟨a k, hpos k⟩, hJ₀ k⟩ n hn ⟨φ, hfj⟩ -
          Ξ.func n hn ⟨φ, hsep⟩| < ε / 2 := by
        rw [← this]
        exact hlt'
      rw [abs_lt] at hlt hlt''
      rw [abs_le]
      constructor <;> linarith [hlt.1, hlt.2, hlt''.1, hlt''.2]
    · rw [evalSigma_of_lt_two Ξ' (φ := ⟨n, φ⟩) hn,
        evalSigma_of_lt_two Ξ (φ := ⟨n, φ⟩) hn]
  have hconv' : (SeparatedExtension.restrictFamily Ψ hJ hdef).TendsToOnSep Ξ := heq ▸ hconv
  exact ⟨⟨J, hJ, tendsToOnSepAlong_of_restrictFamily hΨ hconv'⟩, hΞ⟩
end Sequences
theorem statement_holds (hFacts : EffectiveConstantFacts.Claim)
    (hC1 : C1ProductsAndThickenings.Statement)
    (hV : VectorClasses.Claim)
    (hForms : Multilinear.MultilinearTelescopingBound)
    (hT : SeparatedTupleFacts.SeparatedTupleBasics)
    (hB : CompactSupportDiameters.FiniteDiameters)
    (hFam : CountableChoiceFamilyFacts)
    (hRad : UniformC1Bounds)
    (hU : UniformHierarchyApprox.Claim)
    (hK : C1FormSeqKinds.Statement)
    (hProp : SeparatedExtension.Statement)
    (hApprox : DiagonalLimits.FamilyApproximation.Statement)
    (hDiag : DiagonalSubsequence.CountableBoundedFamilyConverges)
    (hTop : FamilyTopology.Properties.TopologyProperties) : Statement := by
  intro D E θ P F C
  exact ⟨headClaims_hold hFacts D E θ P C, equicontinuityPart_holds hV hForms D E C,
    compactnessPart_holds hFacts hC1 hV hT hB hFam hRad hU hK hProp hTop.1 P F C,
    extractionPart_holds hFacts hC1 hV hT hB hFam hRad hK hProp hApprox hDiag P F C,
    clusterPointPart_holds hU hT hFam hK hProp P F C⟩
end YangMills.Construction.PeriodicSpace.EquicontinuityCompactness
