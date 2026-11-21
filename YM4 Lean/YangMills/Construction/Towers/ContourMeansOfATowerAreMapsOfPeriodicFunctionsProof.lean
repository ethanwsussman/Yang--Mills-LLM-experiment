import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnASide
import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnTheWhole
import YangMills.Construction.Towers.ContourMeansOfATowerAreMapsOfPeriodicFunctions
import YangMills.Construction.Towers.CovariantAveragesAsDifferentialsProof
import YangMills.Construction.Towers.IsometryCovarianceOfTheCovariantAveragesOnTheWholeLatticeProof
import YangMills.Construction.Towers.QuotientCarriesTheLinearObjects
import YangMills.Construction.Towers.QuotientOfATowerCarriesConfigurationsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open TorusMetric (torusProj)
open Matrices
namespace Tower.UnitScale.ContourAveragesPeriodic
open OneStepChart
section FiniteEvaluations
variable {a : ℝ}
def ReadsFinitely (Φ : (InfiniteLattice.Link a → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  ∃ K : FullSpace.PositiveEdge a → ℝ, {p | K p ≠ 0}.Finite ∧
    ∀ f ∈ FullSpace.complexEdgeForms a, Φ f = ∑ᶠ p, K p • FullSpace.restrictToPositiveEdges f p
theorem complex_ofReal_smul (r : ℝ) (M : ComplexMatrix2) : ((r : ℂ)) • M = r • M := by apply _root_.YangMills.Construction.Tower.AsDifferentials.ofReal_smul_matrix <;> assumption
theorem support_smul_subset (K : FullSpace.PositiveEdge a → ℝ)
    (v : FullSpace.PositiveEdge a → ComplexMatrix2) :
    Function.support (fun p => K p • v p) ⊆ {p | K p ≠ 0} := fun p hp h => hp (by simp [h])
theorem ReadsFinitely.congr {Φ Ψ : (InfiniteLattice.Link a → ComplexMatrix2) → ComplexMatrix2}
    (h : ReadsFinitely Φ) (e : ∀ f ∈ FullSpace.complexEdgeForms a, Ψ f = Φ f) :
    ReadsFinitely Ψ := by
  obtain ⟨K, hK, r⟩ := h
  exact ⟨K, hK, fun f hf => (e f hf).trans (r f hf)⟩
theorem readsFinitely_zero : ReadsFinitely (a := a) fun _ => 0 :=
  ⟨0, by simp, fun f _ => by simp⟩
theorem ReadsFinitely.add {Φ Ψ : (InfiniteLattice.Link a → ComplexMatrix2) → ComplexMatrix2}
    (h : ReadsFinitely Φ) (h' : ReadsFinitely Ψ) : ReadsFinitely fun f => Φ f + Ψ f := by
  obtain ⟨K, hK, r⟩ := h
  obtain ⟨K', hK', r'⟩ := h'
  refine ⟨K + K', (hK.union hK').subset fun p hp => ?_, fun f hf => ?_⟩
  · by_contra hc
    simp only [mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hp (by simp [hc.1, hc.2])
  · show Φ f + Ψ f = _
    rw [r f hf, r' f hf, ← finsum_add_distrib (hK.subset (support_smul_subset K _))
      (hK'.subset (support_smul_subset K' _))]
    exact finsum_congr fun p => by simp [add_smul]
theorem ReadsFinitely.smul {Φ : (InfiniteLattice.Link a → ComplexMatrix2) → ComplexMatrix2}
    (h : ReadsFinitely Φ) (c : ℝ) : ReadsFinitely fun f => c • Φ f := by
  obtain ⟨K, hK, r⟩ := h
  refine ⟨c • K, hK.subset fun p hp h0 => hp (by simp [h0]), fun f hf => ?_⟩
  show c • Φ f = _
  rw [r f hf, smul_finsum' c (hK.subset (support_smul_subset K _))]
  exact finsum_congr fun p => by simp [mul_smul]
theorem ReadsFinitely.neg {Φ : (InfiniteLattice.Link a → ComplexMatrix2) → ComplexMatrix2}
    (h : ReadsFinitely Φ) : ReadsFinitely fun f => -Φ f :=
  (h.smul (-1)).congr fun f _ => by simp
theorem ReadsFinitely.sum {ι : Type*} (s : Finset ι)
    {Φ : ι → (InfiniteLattice.Link a → ComplexMatrix2) → ComplexMatrix2}
    (h : ∀ i ∈ s, ReadsFinitely (Φ i)) : ReadsFinitely fun f => ∑ i ∈ s, Φ i f := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using readsFinitely_zero
  | insert i s hi ih =>
    refine ((h i (Finset.mem_insert_self _ _)).add
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))).congr fun f _ => ?_
    rw [Finset.sum_insert hi]
theorem ReadsFinitely.finsum_mem {ι : Type*} {s : Set ι} (hs : s.Finite)
    {Φ : ι → (InfiniteLattice.Link a → ComplexMatrix2) → ComplexMatrix2}
    (h : ∀ i ∈ s, ReadsFinitely (Φ i)) : ReadsFinitely fun f => ∑ᶠ i ∈ s, Φ i f :=
  (ReadsFinitely.sum hs.toFinset (Φ := Φ) fun i hi => h i (hs.mem_toFinset.1 hi)).congr
    fun _ _ => finsum_mem_eq_finite_toFinset_sum _ hs
theorem link_positive_or_opposite (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem readsFinitely_positive (p : FullSpace.PositiveEdge a) :
    ReadsFinitely fun f => f p.1 := by
  classical
  refine ⟨fun q => if q = p then 1 else 0, (finite_singleton p).subset fun q hq => ?_,
    fun f _ => ?_⟩
  · by_contra hc
    exact hq (by simp [show q ≠ p from hc])
  · rw [finsum_eq_single _ p fun q hq => by simp [hq]]
    simp [FullSpace.restrictToPositiveEdges]
theorem readsFinitely_link (b : InfiniteLattice.Link a) : ReadsFinitely fun f => f b := by
  rcases link_positive_or_opposite b with h | h
  · exact readsFinitely_positive ⟨b, h⟩
  · refine (readsFinitely_positive ⟨b.opposite, h⟩).neg.congr fun f hf => ?_
    have := hf.2 b
    simp only [this, neg_neg]
theorem readsFinitely_sumAlong (Γ : List (InfiniteLattice.Link a)) :
    ReadsFinitely fun f => FullSpace.sumAlong f Γ := by
  induction Γ with
  | nil => exact readsFinitely_zero.congr fun f _ => rfl
  | cons b Γ ih =>
    refine (readsFinitely_link b).add ih |>.congr fun f _ => ?_
    simp [FullSpace.sumAlong]
end FiniteEvaluations
section PathAverages
variable {a' : ℝ}
def nonzeroAxes (ν : Fin 4 → ℤ) : Finset (Fin 4) := Finset.univ.filter fun μ => ν μ ≠ 0
def pathAverage (B : InfiniteLattice.Link a' → ComplexMatrix2) (ν : Fin 4 → ℤ)
    (x₀ : InfiniteLattice.LatticePoint a') : ComplexMatrix2 :=
  (((Fintype.card (Fin (nonzeroAxes ν).card ≃ nonzeroAxes ν) : ℝ)⁻¹ : ℝ) : ℂ) •
    ∑ σ : Fin (nonzeroAxes ν).card ≃ nonzeroAxes ν, FullSpace.sumAlong B
      (FullSpace.stepsInOrder ν x₀ ((List.finRange _).map fun i => ((σ i : nonzeroAxes ν) : Fin 4)))
theorem contourAverage_eq_pathAverage (L : ℕ) {a : ℝ} (B : InfiniteLattice.Link a' → ComplexMatrix2)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    FullSpace.contourAverage L B y x =
      pathAverage B (FullSpace.cubeOffset L y x) (FullSpace.toFiner a' y) := rfl
theorem readsFinitely_pathAverage (ν : Fin 4 → ℤ) (x₀ : InfiniteLattice.LatticePoint a') :
    ReadsFinitely fun B => pathAverage B ν x₀ := by
  refine ((ReadsFinitely.sum (Finset.univ : Finset (Fin (nonzeroAxes ν).card ≃ nonzeroAxes ν))
    (Φ := fun σ B => FullSpace.sumAlong B (FullSpace.stepsInOrder ν x₀
      ((List.finRange _).map fun i => ((σ i : nonzeroAxes ν) : Fin 4))))
    fun σ _ => readsFinitely_sumAlong _).smul
    ((Fintype.card (Fin (nonzeroAxes ν).card ≃ nonzeroAxes ν) : ℝ)⁻¹)).congr fun f _ => ?_
  exact complex_ofReal_smul _ _
theorem forwardSteps_add (w x : InfiniteLattice.LatticePoint a') (μ : Fin 4) (n : ℕ) :
    FullSpace.forwardSteps (x + w) μ n =
      (FullSpace.forwardSteps x μ n).map fun b => linkTranslate b w := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [FullSpace.forwardSteps, List.map_cons]
    rw [add_right_comm, ih]
    congr 1
    exact InfiniteLattice.Link.ext rfl (add_right_comm _ _ _)
theorem backwardSteps_add (w x : InfiniteLattice.LatticePoint a') (μ : Fin 4) (n : ℕ) :
    FullSpace.backwardSteps (x + w) μ n =
      (FullSpace.backwardSteps x μ n).map fun b => linkTranslate b w := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [FullSpace.backwardSteps, List.map_cons]
    rw [add_sub_right_comm, ih]
    congr 1
    exact InfiniteLattice.Link.ext rfl (add_sub_right_comm _ _ _)
theorem signedSteps_add (w x : InfiniteLattice.LatticePoint a') (μ : Fin 4) (n : ℤ) :
    FullSpace.signedSteps (x + w) μ n =
      (FullSpace.signedSteps x μ n).map fun b => linkTranslate b w := by
  unfold FullSpace.signedSteps
  split_ifs
  · exact forwardSteps_add w x μ _
  · exact backwardSteps_add w x μ _
theorem stepsInOrder_add (w : InfiniteLattice.LatticePoint a') (ν : Fin 4 → ℤ)
    (x : InfiniteLattice.LatticePoint a') (l : List (Fin 4)) :
    FullSpace.stepsInOrder ν (x + w) l =
      (FullSpace.stepsInOrder ν x l).map fun b => linkTranslate b w := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    simp only [FullSpace.stepsInOrder, List.map_append]
    rw [signedSteps_add, add_right_comm, ih]
theorem pathAverage_shift (w : InfiniteLattice.LatticePoint a')
    (B : InfiniteLattice.Link a' → ComplexMatrix2) (ν : Fin 4 → ℤ)
    (x₀ : InfiniteLattice.LatticePoint a') :
    pathAverage (fun b => B (linkTranslate b w)) ν x₀ = pathAverage B ν (x₀ + w) := by
  unfold pathAverage
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [stepsInOrder_add]
  simp [FullSpace.sumAlong, List.map_map, Function.comp_def]
end PathAverages
section Shifts
variable {a a' : ℝ}
theorem coe_toFiner {y : InfiniteLattice.LatticePoint a}
    (h : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a') :
    ((FullSpace.toFiner a' y : InfiniteLattice.LatticePoint a') : AmbientSpace) = y := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.coe_toFiner <;> assumption
theorem cubeOffset_add (L : ℕ) {y w : InfiniteLattice.LatticePoint a}
    {x w' : InfiniteLattice.LatticePoint a'} (hw : (w : AmbientSpace) = w') :
    FullSpace.cubeOffset L (y + w) (x + w') = FullSpace.cubeOffset L y x := by
  have e : ((x + w' : InfiniteLattice.LatticePoint a') : AmbientSpace) -
      ((y + w : InfiniteLattice.LatticePoint a) : AmbientSpace) =
        (x : AmbientSpace) - (y : AmbientSpace) := by
    show (x : AmbientSpace) + (w' : AmbientSpace) - ((y : AmbientSpace) + (w : AmbientSpace)) = _
    rw [hw]
    abel
  unfold FullSpace.cubeOffset
  congr 1
  funext ν
  unfold FullSpace.IsCubeOffset
  rw [e]
theorem toFiner_add
    (hle : InfiniteLattice.latticeSubgroup a ≤ InfiniteLattice.latticeSubgroup a')
    {y w : InfiniteLattice.LatticePoint a} {w' : InfiniteLattice.LatticePoint a'}
    (hw : (w : AmbientSpace) = w') :
    FullSpace.toFiner a' (y + w) = FullSpace.toFiner a' y + w' := by
  refine Subtype.ext ?_
  rw [coe_toFiner (hle (y + w).2)]
  show (y : AmbientSpace) + (w : AmbientSpace) =
    ((FullSpace.toFiner a' y : InfiniteLattice.LatticePoint a') : AmbientSpace) +
      (w' : AmbientSpace)
  rw [coe_toFiner (hle y.2), hw]
theorem contourAverage_shift (L : ℕ)
    (hle : InfiniteLattice.latticeSubgroup a ≤ InfiniteLattice.latticeSubgroup a')
    {w : InfiniteLattice.LatticePoint a} {w' : InfiniteLattice.LatticePoint a'}
    (hw : (w : AmbientSpace) = w')
    (f : InfiniteLattice.Link a' → ComplexMatrix2) (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') :
    FullSpace.contourAverage L (fun b => f (linkTranslate b w')) y x =
      FullSpace.contourAverage L f (y + w) (x + w') := by
  rw [contourAverage_eq_pathAverage, contourAverage_eq_pathAverage, pathAverage_shift,
    cubeOffset_add L hw, toFiner_add hle hw]
theorem bijOn_add_cubeVertices (L : ℕ) {w : InfiniteLattice.LatticePoint a}
    {w' : InfiniteLattice.LatticePoint a'} (hw : (w : AmbientSpace) = w')
    (y : InfiniteLattice.LatticePoint a) :
    BijOn (fun x : InfiniteLattice.LatticePoint a' => x + w') (FullSpace.cubeVertices L a' y)
      (FullSpace.cubeVertices L a' (y + w)) := by
  refine ⟨?_, (add_left_injective w').injOn, ?_⟩
  · rintro x ⟨ν, h, e⟩
    refine ⟨ν, h, ?_⟩
    show (x : AmbientSpace) + (w' : AmbientSpace) = (y : AmbientSpace) + (w : AmbientSpace) + _
    rw [e, hw]
    abel
  · rintro x ⟨ν, h, e⟩
    refine ⟨x - w', ⟨ν, h, ?_⟩, sub_add_cancel _ _⟩
    have e' : (x : AmbientSpace) = (y : AmbientSpace) + (w : AmbientSpace) + _ := e
    show (x : AmbientSpace) - (w' : AmbientSpace) = _
    rw [e', hw]
    abel
theorem cubeContourAverage_shift (L : ℕ)
    (hle : InfiniteLattice.latticeSubgroup a ≤ InfiniteLattice.latticeSubgroup a')
    {w : InfiniteLattice.LatticePoint a} {w' : InfiniteLattice.LatticePoint a'}
    (hw : (w : AmbientSpace) = w')
    (f : InfiniteLattice.Link a' → ComplexMatrix2) (y : InfiniteLattice.LatticePoint a) :
    FullSpace.cubeContourAverage L (a := a) (fun b => f (linkTranslate b w')) y =
      FullSpace.cubeContourAverage L (a := a) f (y + w) := by
  have e : (∑ᶠ x ∈ FullSpace.cubeVertices L a' y,
        FullSpace.contourAverage L (fun b => f (linkTranslate b w')) y x) =
      ∑ᶠ x ∈ FullSpace.cubeVertices L a' (y + w), FullSpace.contourAverage L f (y + w) x :=
    finsum_mem_eq_of_bijOn _ (bijOn_add_cubeVertices L hw y) fun x _ =>
      contourAverage_shift L hle hw f y x
  exact congrArg (fun v => PeriodicLattice.inverseFourthPowerWeight L • v) e
end Shifts
section TracelessValues
variable {a a' : ℝ}
theorem form_mem_traceless {f : InfiniteLattice.Link a' → ComplexMatrix2}
    (hf : f ∈ FullSpace.complexEdgeForms a') (b : InfiniteLattice.Link a') :
    f b ∈ ComplexMatrix2.traceless := by
  rcases link_positive_or_opposite b with h | h
  · exact hf.1 b h
  · have h2 : f b.opposite ∈ ComplexMatrix2.traceless := hf.1 _ h
    rw [hf.2 b] at h2
    exact (Submodule.neg_mem_iff _).1 h2
theorem contourAverage_mem_traceless (L : ℕ) {f : InfiniteLattice.Link a' → ComplexMatrix2}
    (hf : f ∈ FullSpace.complexEdgeForms a') (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') :
    FullSpace.contourAverage L f y x ∈ ComplexMatrix2.traceless := by
  refine ComplexMatrix2.traceless.smul_mem _
    (Submodule.sum_mem _ fun σ _ => list_sum_mem fun v hv => ?_)
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hv
  exact form_mem_traceless hf b
end TracelessValues
section Meshes
variable {L m k j : ℕ}
theorem meshAt_succ (hL : 0 < L) :
    meshAt L k (j + 1) = (L : ℝ) * meshAt L k j := by apply _root_.YangMills.Construction.Tower.FieldProjection.meshAt_succ <;> assumption
theorem latticeSubgroup_succ_le (hL : 0 < L) :
    InfiniteLattice.latticeSubgroup (meshAt L k (j + 1)) ≤
      InfiniteLattice.latticeSubgroup (meshAt L k j) := by
  rintro x ⟨n, hn⟩
  refine ⟨fun μ => n μ * (L : ℤ), fun μ => ?_⟩
  rw [hn μ, meshAt_succ hL]
  push_cast
  ring
theorem pow_mul_meshAt_eq_one (hL : 0 < L) {i : ℕ} (hi : i ≤ k) :
    (L : ℝ) ^ (k - i) * meshAt L k i = 1 := by
  have h : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold meshAt
  rw [← zpow_natCast, ← zpow_add₀ h]
  have : (((k - i : ℕ) : ℤ)) + ((i : ℤ) - (k : ℤ)) = 0 := by omega
  rw [this, zpow_zero]
theorem intVector_mem (hL : 0 < L) {i : ℕ} (hi : i ≤ k) (z : Fin 4 → ℤ) :
    (fun μ => (z μ : ℝ)) ∈ InfiniteLattice.latticeSubgroup (meshAt L k i) :=
  ⟨fun μ => z μ * (L : ℤ) ^ (k - i), fun μ => by
    push_cast
    rw [mul_assoc, pow_mul_meshAt_eq_one hL hi, mul_one]⟩
theorem coe_integerPoint (hL : 0 < L) {i : ℕ} (hi : i ≤ k) (z : Fin 4 → ℤ) :
    ((integerPoint (meshAt L k i) z : InfiniteLattice.LatticePoint (meshAt L k i)) :
      AmbientSpace) = fun μ => (z μ : ℝ) :=
  coe_toFiner (a := 1) (y := ⟨fun μ => (z μ : ℝ), z, fun μ => by simp⟩) (intVector_mem hL hi z)
theorem sideMultiple_mem (hL : 0 < L) {i : ℕ} (hi : i ≤ k) {d : AmbientSpace}
    (hd : ∀ μ, ∃ n : ℤ, d μ = (n : ℝ) * PeriodicLattice.torusSide L m) :
    d ∈ InfiniteLattice.latticeSubgroup (meshAt L k i) := by
  choose v hv using hd
  have e : d = fun μ => ((v μ * (2 * (L : ℤ) ^ m) : ℤ) : ℝ) := by
    funext μ
    rw [hv μ]
    simp [PeriodicLattice.torusSide]
  rw [e]
  exact intVector_mem hL hi _
theorem sub_eq_of_torusProj_eq {p q : AmbientSpace}
    (e : torusProj (PeriodicLattice.torusSide L m) p = torusProj (PeriodicLattice.torusSide L m) q)
    (μ : Fin 4) : ∃ n : ℤ, p μ - q μ = (n : ℝ) * PeriodicLattice.torusSide L m := by
  have hμ : ((p μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) =
      ((q μ : ℝ) : AddCircle _) := congrFun e μ
  have h0 : ((p μ - q μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) = 0 := by
    rw [AddCircle.coe_sub, hμ, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h0
  exact ⟨n, by rw [← hn]; simp⟩
theorem torusProj_add {p d : AmbientSpace}
    (hd : ∀ μ, ∃ n : ℤ, d μ = (n : ℝ) * PeriodicLattice.torusSide L m) :
    torusProj (PeriodicLattice.torusSide L m) (p + d) =
      torusProj (PeriodicLattice.torusSide L m) p := by
  funext μ
  obtain ⟨n, hn⟩ := hd μ
  have h0 : (((n : ℝ) * PeriodicLattice.torusSide L m : ℝ) :
      AddCircle (PeriodicLattice.torusSide L m)) = 0 :=
    (AddCircle.coe_eq_zero_iff _).2 ⟨n, by simp⟩
  show ((p μ + d μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) = ((p μ : ℝ) : AddCircle _)
  rw [hn, AddCircle.coe_add, h0, add_zero]
end Meshes
section CubeCentres
variable {L m k j : ℕ}
abbrev FineVertex (L k j : ℕ) : Type :=
  FullSpace.FineOnlyVertex (meshAt L k (j + 1)) (meshAt L k j)
theorem exists_cubeCentre (hp : FullSpace.CubesOfOrderPartition L k (j + 1) 1)
    (x : FineVertex L k j) :
    ∃ y : FullSpace.Vertex L k (j + 1), x.1 ∈ FullSpace.cubeVertices L (meshAt L k j) y ∧
      (x.1 : AmbientSpace) ≠ y := by
  have hu : (⋃ y : FullSpace.Vertex L k (j + 1), FullSpace.cubeOfOrder L (meshAt L k j) 1 y) =
      (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) := hp.iUnion_cube
  have hx : (x.1 : AmbientSpace) ∈
      ⋃ y : FullSpace.Vertex L k (j + 1), FullSpace.cubeOfOrder L (meshAt L k j) 1 y := by
    rw [hu]
    exact x.1.2
  obtain ⟨y, hy⟩ := mem_iUnion.1 hx
  refine ⟨y, hy, fun e => x.2 ?_⟩
  rw [e]
  exact y.2
theorem cubeCentre_spec (hp : FullSpace.CubesOfOrderPartition L k (j + 1) 1)
    (x : FineVertex L k j) :
    x.1 ∈ FullSpace.cubeVertices L (meshAt L k j) (FullSpace.cubeCentre L x) ∧
      (x.1 : AmbientSpace) ≠ (FullSpace.cubeCentre L x : FullSpace.Vertex L k (j + 1)) :=
  Classical.epsilon_spec (exists_cubeCentre hp x)
theorem cubeCentre_eq (hp : FullSpace.CubesOfOrderPartition L k (j + 1) 1)
    (x : FineVertex L k j) {y : FullSpace.Vertex L k (j + 1)}
    (hy : x.1 ∈ FullSpace.cubeVertices L (meshAt L k j) y) :
    FullSpace.cubeCentre L x = y := by
  by_contra hne
  have hd : Disjoint (FullSpace.cubeOfOrder L (meshAt L k j) 1 (FullSpace.cubeCentre L x))
      (FullSpace.cubeOfOrder L (meshAt L k j) 1 y) := hp.pairwise_disjoint_cube hne
  have h1 : (x.1 : AmbientSpace) ∈
      FullSpace.cubeOfOrder L (meshAt L k j) 1 (FullSpace.cubeCentre L x) :=
    (cubeCentre_spec hp x).1
  have h2 : (x.1 : AmbientSpace) ∈ FullSpace.cubeOfOrder L (meshAt L k j) 1 y := hy
  exact Set.disjoint_left.1 hd h1 h2
theorem cubeVertices_finite (hL : 0 < L) (hp : FullSpace.CubesOfOrderPartition L k (j + 1) 1)
    (y : FullSpace.Vertex L k (j + 1)) :
    (FullSpace.cubeVertices L (meshAt L k j) y).Finite := by
  have hn : (FullSpace.cubeOfOrder L (meshAt L k j) 1 y).ncard = L ^ (4 * 1) := hp.cube_ncard y
  have h : (FullSpace.cubeOfOrder L (meshAt L k j) 1 y).Finite :=
    Set.finite_of_ncard_pos (by rw [hn]; exact Nat.pow_pos hL)
  exact h.preimage Subtype.val_injective.injOn
theorem fineOnlyContourAverage_shift (hL : 0 < L)
    (hp : FullSpace.CubesOfOrderPartition L k (j + 1) 1)
    {w : FullSpace.Vertex L k (j + 1)} {w' : FullSpace.Vertex L k j}
    (hw : (w : AmbientSpace) = w')
    (f : FullSpace.Edge L k j → ComplexMatrix2) (x : FineVertex L k j)
    (h : ((x.1 + w' : FullSpace.Vertex L k j) : AmbientSpace) ∉
      InfiniteLattice.latticeSubgroup (meshAt L k (j + 1))) :
    FullSpace.fineOnlyContourAverage L (a := meshAt L k (j + 1)) (a' := meshAt L k j)
        (fun b => f (linkTranslate b w')) x =
      FullSpace.fineOnlyContourAverage L (a := meshAt L k (j + 1)) (a' := meshAt L k j) f
        ⟨x.1 + w', h⟩ := by
  have hc : FullSpace.cubeCentre L (a := meshAt L k (j + 1)) (a' := meshAt L k j)
      ⟨x.1 + w', h⟩ = FullSpace.cubeCentre L x + w :=
    cubeCentre_eq hp _ ((bijOn_add_cubeVertices L hw _).mapsTo (cubeCentre_spec hp x).1)
  show FullSpace.contourAverage L _ (FullSpace.cubeCentre L x) x.1 =
    FullSpace.contourAverage L f (FullSpace.cubeCentre L (a := meshAt L k (j + 1))
      (a' := meshAt L k j) ⟨x.1 + w', h⟩) (x.1 + w')
  rw [hc]
  exact contourAverage_shift L (latticeSubgroup_succ_le hL) hw f _ _
end CubeCentres
section Projection
variable {L m k j : ℕ}
structure StepHypotheses (L m k j : ℕ) : Prop where
  pos : 0 < L
  lt : j < k
  partition : FullSpace.CubesOfOrderPartition L k (j + 1) 1
  paths : FullSpace.PathsStayInCubes L k (j + 1)
  lattices : FullSpace.ProjSublattices L m k
  sets : ∀ y : FullSpace.Vertex L k (j + 1),
    FullSpace.ProjPreservesSets L m k j (InfiniteLattice.Link.forwardFrom y 0)
  linear : ∀ (y : FullSpace.Vertex L k (j + 1)) (B : FullSpace.Edge L k j → ComplexMatrix2),
    ∀ x ∈ FullSpace.cubeVertices L (meshAt L k j) y,
      PeriodicLattice.contourFormAverage
          (FullSpace.pushforwardForm L m k j (FullSpace.doubleCubeLinks L (meshAt L k j)
            (InfiniteLattice.Link.forwardFrom y 0)) B)
          (FullSpace.projVertex L m k (j + 1) y) (FullSpace.projVertex L m k j x) =
        FullSpace.contourAverage L B y x
  initial_eq : ∀ c : FullSpace.Edge L k (j + 1),
    (FullSpace.projEdge L m k (j + 1) c).source = FullSpace.projVertex L m k (j + 1) c.initial
theorem forwardFrom_isPositivelyOriented (y : FullSpace.Vertex L k (j + 1)) :
    (InfiniteLattice.Link.forwardFrom y 0).IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.IsometryEquivariance.forwardFrom_positive <;> assumption
namespace StepHypotheses
theorem bijOn_projVertex (h : StepHypotheses L m k j) (y : FullSpace.Vertex L k (j + 1)) :
    BijOn (FullSpace.projVertex L m k j) (FullSpace.cubeVertices L (meshAt L k j) y)
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (FullSpace.projVertex L m k (j + 1) y)) := by
  have Q := h.sets y
  have hdt : (FullSpace.projEdge L m k (j + 1) (InfiniteLattice.Link.forwardFrom y 0)).source =
      FullSpace.projVertex L m k (j + 1) y := h.initial_eq _
  rw [← hdt]
  refine ⟨fun x hx => ?_, fun x hx x' hx' e => ?_, fun x' hx' => ?_⟩
  · show ((FullSpace.projVertex L m k j x : Tower.Vertex L m k j) :
        PeriodicLattice.FourTorus L m) ∈
      PeriodicLattice.unitBlock (FullSpace.projEdge L m k (j + 1)
        (InfiniteLattice.Link.forwardFrom y 0)).source
    rw [← Q.cube_initial]
    exact ⟨_, hx, rfl⟩
  · exact Subtype.ext (Q.injOn_doubleCube (Or.inl hx) (Or.inl hx') (congrArg Subtype.val e))
  · have hx'' : (x' : PeriodicLattice.FourTorus L m) ∈
        PeriodicLattice.unitBlock (FullSpace.projEdge L m k (j + 1)
          (InfiniteLattice.Link.forwardFrom y 0)).source := hx'
    rw [← Q.cube_initial] at hx''
    obtain ⟨p, hp, he⟩ := hx''
    have hps : p ∈ (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) := by
      have hu : (⋃ y : FullSpace.Vertex L k (j + 1),
          FullSpace.cubeOfOrder L (meshAt L k j) 1 y) =
          (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) :=
        h.partition.iUnion_cube
      rw [← hu]
      exact mem_iUnion.2 ⟨y, hp⟩
    exact ⟨⟨p, hps⟩, hp, Subtype.ext he⟩
theorem contour_mem_doubleCubeLinks (h : StepHypotheses L m k j)
    {y : FullSpace.Vertex L k (j + 1)} {x : FullSpace.Vertex L k j}
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) y)
    {Γ : List (FullSpace.Edge L k j)} (hΓ : Γ ∈ FullSpace.contourSet L y x) :
    ∀ b ∈ Γ, b ∈ FullSpace.doubleCubeLinks L (meshAt L k j)
      (InfiniteLattice.Link.forwardFrom y 0) := by
  have hs := h.paths.contour_vertex_mem y x hx Γ hΓ
  have hsub : FullSpace.cube L (meshAt L k j) y ⊆
      FullSpace.doubleCube L (meshAt L k j) (InfiniteLattice.Link.forwardFrom y 0) :=
    subset_union_left
  intro b hb
  exact ⟨hsub (hs b.initial (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩))),
    hsub (hs b.terminal (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩)))⟩
theorem pushforwardForm_projEdge (f : Tower.Edge L m k j → ComplexMatrix2)
    {P : Set (FullSpace.Edge L k j)} {b : FullSpace.Edge L k j} (hb : b ∈ P) :
    FullSpace.pushforwardForm L m k j P (fun b => f (FullSpace.projEdge L m k j b))
        (FullSpace.projEdge L m k j b) = f (FullSpace.projEdge L m k j b) := by
  have hex : ∃ b' ∈ P, FullSpace.projEdge L m k j b' = FullSpace.projEdge L m k j b :=
    ⟨b, hb, rfl⟩
  unfold FullSpace.pushforwardForm
  rw [dif_pos hex]
  show f (FullSpace.projEdge L m k j hex.choose) = _
  rw [hex.choose_spec.2]
theorem contourAverage_periodic (h : StepHypotheses L m k j)
    (f : Tower.Edge L m k j → ComplexMatrix2)
    {y : FullSpace.Vertex L k (j + 1)} {x : FullSpace.Vertex L k j}
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) y) :
    FullSpace.contourAverage L (fun b => f (FullSpace.projEdge L m k j b)) y x =
      PeriodicLattice.contourFormAverage f (FullSpace.projVertex L m k (j + 1) y)
        (FullSpace.projVertex L m k j x) := by
  rw [← h.linear y _ x hx]
  unfold PeriodicLattice.contourFormAverage
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hm : PeriodicLattice.orderedContour (FullSpace.projVertex L m k (j + 1) y)
      (FullSpace.projVertex L m k j x) σ ∈
      PeriodicLattice.contourSet (FullSpace.projVertex L m k (j + 1) y)
        (FullSpace.projVertex L m k j x) :=
    mem_range_self σ
  rw [← (h.sets y).contourSet_image y (Or.inl rfl) x hx] at hm
  obtain ⟨Γ, hΓ, he⟩ := hm
  rw [← he]
  unfold PeriodicLattice.bondFormSumAlong FullSpace.projPath
  rw [List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun b hb =>
    pushforwardForm_projEdge f (h.contour_mem_doubleCubeLinks hx hΓ b hb)
theorem cubeContourAverage_periodic (h : StepHypotheses L m k j)
    (f : Tower.Edge L m k j → ComplexMatrix2) (y : FullSpace.Vertex L k (j + 1)) :
    FullSpace.cubeContourAverage L (a := meshAt L k (j + 1))
        (fun b => f (FullSpace.projEdge L m k j b)) y =
      Tower.cubeContourAverage L m k j f (FullSpace.projVertex L m k (j + 1) y) := by
  have e : (∑ᶠ x ∈ FullSpace.cubeVertices L (meshAt L k j) y,
        FullSpace.contourAverage L (fun b => f (FullSpace.projEdge L m k j b)) y x) =
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (FullSpace.projVertex L m k (j + 1) y),
        PeriodicLattice.contourFormAverage f (FullSpace.projVertex L m k (j + 1) y) x :=
    finsum_mem_eq_of_bijOn _ (h.bijOn_projVertex y) fun x hx => h.contourAverage_periodic f hx
  exact congrArg (fun v => PeriodicLattice.inverseFourthPowerWeight L • v) e
theorem projVertex_not_mem (h : StepHypotheses L m k j) (x : FineVertex L k j) :
    ((FullSpace.projVertex L m k j x.1 : Tower.Vertex L m k j) : PeriodicLattice.FourTorus L m) ∉
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k (j + 1)) := by
  intro hx
  have hl : torusProj (PeriodicLattice.torusSide L m) ''
      (InfiniteLattice.latticeSubgroup (meshAt L k (j + 1)) : Set AmbientSpace) =
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k (j + 1)) :=
    h.lattices (j + 1) h.lt
  have hx' : torusProj (PeriodicLattice.torusSide L m) (x.1 : AmbientSpace) ∈
      torusProj (PeriodicLattice.torusSide L m) ''
        (InfiniteLattice.latticeSubgroup (meshAt L k (j + 1)) : Set AmbientSpace) := by
    rw [hl]
    exact hx
  obtain ⟨p, hp, e⟩ := hx'
  have hd : p - (x.1 : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (meshAt L k (j + 1)) :=
    sideMultiple_mem (m := m) h.pos h.lt fun μ => sub_eq_of_torusProj_eq e μ
  apply x.2
  have := (InfiniteLattice.latticeSubgroup (meshAt L k (j + 1))).sub_mem hp hd
  simpa using this
theorem cubeCentre_projVertex (h : StepHypotheses L m k j) (x : FineVertex L k j)
    (hx : ((FullSpace.projVertex L m k j x.1 : Tower.Vertex L m k j) :
      PeriodicLattice.FourTorus L m) ∉
        PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k (j + 1))) :
    Tower.cubeCentre (L := L) (n := m) (k := k) (j := j)
        ⟨FullSpace.projVertex L m k j x.1, hx⟩ =
      FullSpace.projVertex L m k (j + 1) (FullSpace.cubeCentre L x) := by
  have hc := cubeCentre_spec h.partition x
  have hin := (h.bijOn_projVertex _).mapsTo hc.1
  have hne : ∀ y : Tower.Vertex L m k (j + 1),
      ((FullSpace.projVertex L m k j x.1 : Tower.Vertex L m k j) :
        PeriodicLattice.FourTorus L m) ≠ y := fun y e => hx (by rw [e]; exact y.2)
  have hspec : FullSpace.projVertex L m k j x.1 ∈
      PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (Tower.cubeCentre (L := L) (n := m) (k := k) (j := j)
          ⟨FullSpace.projVertex L m k j x.1, hx⟩) :=
    (Classical.epsilon_spec (p := fun y : Tower.Vertex L m k (j + 1) =>
        FullSpace.projVertex L m k j x.1 ∈
            PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y ∧
          ((FullSpace.projVertex L m k j x.1 : Tower.Vertex L m k j) :
            PeriodicLattice.FourTorus L m) ≠ y)
      ⟨_, hin, hne _⟩).1
  generalize Tower.cubeCentre (L := L) (n := m) (k := k) (j := j)
    ⟨FullSpace.projVertex L m k j x.1, hx⟩ = y' at hspec ⊢
  have hl : torusProj (PeriodicLattice.torusSide L m) ''
      (InfiniteLattice.latticeSubgroup (meshAt L k (j + 1)) : Set AmbientSpace) =
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k (j + 1)) :=
    h.lattices (j + 1) h.lt
  have hlat : (y' : PeriodicLattice.FourTorus L m) ∈ torusProj (PeriodicLattice.torusSide L m) ''
      (InfiniteLattice.latticeSubgroup (meshAt L k (j + 1)) : Set AmbientSpace) := by
    rw [hl]
    exact y'.2
  obtain ⟨p, hp, e⟩ := hlat
  obtain rfl : y' = FullSpace.projVertex L m k (j + 1) ⟨p, hp⟩ := Subtype.ext e.symm
  obtain ⟨x₂, hx₂, e₂⟩ := (h.bijOn_projVertex ⟨p, hp⟩).surjOn hspec
  have hd : ∀ μ, ∃ n : ℤ, ((x₂ : AmbientSpace) - (x.1 : AmbientSpace)) μ =
      (n : ℝ) * PeriodicLattice.torusSide L m :=
    fun μ => sub_eq_of_torusProj_eq (congrArg Subtype.val e₂) μ
  have hdc : (x₂ : AmbientSpace) - (x.1 : AmbientSpace) ∈
      InfiniteLattice.latticeSubgroup (meshAt L k (j + 1)) :=
    sideMultiple_mem (m := m) h.pos h.lt hd
  have hdf : (x₂ : AmbientSpace) - (x.1 : AmbientSpace) ∈
      InfiniteLattice.latticeSubgroup (meshAt L k j) :=
    sub_mem x₂.2 x.1.2
  have hmem := (bijOn_add_cubeVertices L (w := -(⟨_, hdc⟩ : FullSpace.Vertex L k (j + 1)))
    (w' := -(⟨_, hdf⟩ : FullSpace.Vertex L k j)) rfl ⟨p, hp⟩).mapsTo hx₂
  have hx₁ : x₂ + -(⟨_, hdf⟩ : FullSpace.Vertex L k j) = x.1 := Subtype.ext (by
    show (x₂ : AmbientSpace) + -((x₂ : AmbientSpace) - (x.1 : AmbientSpace)) = x.1
    abel)
  rw [hx₁] at hmem
  rw [cubeCentre_eq h.partition x hmem]
  refine Subtype.ext ?_
  show torusProj (PeriodicLattice.torusSide L m) p = torusProj (PeriodicLattice.torusSide L m)
    (p + -((x₂ : AmbientSpace) - (x.1 : AmbientSpace)))
  refine (torusProj_add fun μ => ?_).symm
  obtain ⟨n, hn⟩ := hd μ
  refine ⟨-n, ?_⟩
  simp only [Pi.neg_apply, hn]
  push_cast
  ring
theorem fineOnlyContourAverage_periodic (h : StepHypotheses L m k j)
    (f : Tower.Edge L m k j → ComplexMatrix2) (x : FineVertex L k j) :
    FullSpace.fineOnlyContourAverage L (a := meshAt L k (j + 1)) (a' := meshAt L k j)
        (fun b => f (FullSpace.projEdge L m k j b)) x =
      (fineOnlyVertexFunctions L m k j).extend (Tower.fineOnlyContourAverage L m k j f) x := by
  have hx := h.projVertex_not_mem x
  have e : (fineOnlyVertexFunctions L m k j).extend
      (Tower.fineOnlyContourAverage L m k j f) x =
      Tower.fineOnlyContourAverage L m k j f ⟨FullSpace.projVertex L m k j x.1, hx⟩ :=
    dif_pos hx
  rw [e]
  show FullSpace.contourAverage L _ (FullSpace.cubeCentre L x) x.1 =
    PeriodicLattice.contourFormAverage f (Tower.cubeCentre (L := L) (n := m) (k := k) (j := j)
      ⟨FullSpace.projVertex L m k j x.1, hx⟩) (FullSpace.projVertex L m k j x.1)
  rw [h.cubeCentre_projVertex x hx]
  exact h.contourAverage_periodic f (cubeCentre_spec h.partition x).1
end StepHypotheses
end Projection
section TwoOperators
variable {L m k j : ℕ}
theorem hasRealFiniteKernel_of_readsFinitely (Y : TwoScaleFunctions)
    (O : ((edgeForms L m k j).fullSpace.index → ComplexMatrix2) → Y.fullSpace.index →
      ComplexMatrix2)
    (h : ∀ q : Y.Slot, ReadsFinitely (a := meshAt L k j) fun f => Y.eval (O f) q) :
    HasRealFiniteKernel (edgeForms L m k j) Y O := by
  unfold ReadsFinitely at h
  choose K hK hr using h
  exact ⟨K, hK, fun f hf q => hr q f hf⟩
theorem readsFinitely_contourAverage (y : FullSpace.Vertex L k (j + 1))
    (x : FullSpace.Vertex L k j) :
    ReadsFinitely (a := meshAt L k j) fun B => FullSpace.contourAverage L B y x :=
  readsFinitely_pathAverage _ _
theorem readsFinitely_cubeContourAverage (hL : 0 < L)
    (hp : FullSpace.CubesOfOrderPartition L k (j + 1) 1) (y : FullSpace.Vertex L k (j + 1)) :
    ReadsFinitely (a := meshAt L k j) fun B =>
      FullSpace.cubeContourAverage L (a := meshAt L k (j + 1)) B y := by
  refine ((ReadsFinitely.finsum_mem (cubeVertices_finite hL hp y)
    (Φ := fun x B => FullSpace.contourAverage L B y x)
    fun x _ => readsFinitely_contourAverage y x).smul ((L : ℝ) ^ (-4 : ℤ))).congr fun f _ => ?_
  exact complex_ofReal_smul _ _
theorem periodic_contourAverage_mem_traceless
    (hP : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j < k)
    {f : Tower.Edge L m k j → ComplexMatrix2} (hf : f ∈ Tower.complexEdgeForms L m k j)
    (y : Tower.Vertex L m k (j + 1)) (x : Tower.Vertex L m k j) :
    PeriodicLattice.contourFormAverage f y x ∈ ComplexMatrix2.traceless := by
  refine ComplexMatrix2.traceless.smul_mem _
    (Submodule.sum_mem _ fun σ _ => list_sum_mem fun v hv => ?_)
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hv
  rcases hP L m k hL hm (by omega) j hj.le b with ⟨h, -⟩ | ⟨h, -⟩
  · exact hf.1 b h
  · have h2 : f b.opposite ∈ ComplexMatrix2.traceless := hf.1 _ h
    rw [hf.2 b] at h2
    exact (Submodule.neg_mem_iff _).1 h2
end TwoOperators
theorem holds (hS : Tower.ProjectionCarriesSetsStatement)
    (hC : FullSpace.ProjectionCommutesWithSmoothing)
    (hQ : Tower.EdgeProjectionProperties)
    (hB : FullSpace.CubesCorridorsPivotEdgesAndPaths)
    (hW : FullSpace.OneStepComplexForms.OneStepClaim)
    (hT : Tower.PeriodicCoarseningStep.Holds)
    (hP : PeriodicLattice.LevelBondOrientationDichotomy) : Statement := by
  intro L hL m k j hm hj
  have hL0 : 0 < L := by have := hL.2; omega
  have hk : 1 ≤ k := by omega
  have hB' := hB L hL k (j + 1) 1 hk (by omega) hj le_rfl (by omega)
  have hS' := hS L hL0 hL k hk m hm
  have A : StepHypotheses L m k j :=
    { pos := hL0
      lt := hj
      partition := hB'.1
      paths := hB'.2.2.2
      lattices := hS'.1
      sets := fun y => hS'.2 j hj _ (forwardFrom_isPositivelyOriented y)
      linear := fun y B x hx =>
        (hC L k j m hL hj hm _ (forwardFrom_isPositivelyOriented y) B).1 y (Or.inl rfl) x hx
      initial_eq := fun c => ((hQ L m k (j + 1) hL hm hj).1 c).1 }
  have hw : ∀ z : Fin 4 → ℤ,
      ((integerPoint (meshAt L k (j + 1)) (-z) : FullSpace.Vertex L k (j + 1)) : AmbientSpace) =
        (integerPoint (meshAt L k j) (-z) : FullSpace.Vertex L k j) := fun z => by
    rw [coe_integerPoint hL0 hj, coe_integerPoint hL0 (Nat.le_of_lt hj)]
  refine ⟨⟨(hW L hL k j hj).cubeContourAverage_mapsTo,
      (hT L hL m k j hm hj).cubeContourAverage_mapsTo,
      fun f _ => funext fun y => A.cubeContourAverage_periodic f y,
      fun z f _ => funext fun y =>
        cubeContourAverage_shift L (latticeSubgroup_succ_le hL0) (hw z) f y,
      hasRealFiniteKernel_of_readsFinitely _ _ fun y =>
        readsFinitely_cubeContourAverage hL0 A.partition y⟩,
    ⟨fun f hf x _ => contourAverage_mem_traceless L hf _ _,
      fun f hf x _ => periodic_contourAverage_mem_traceless hP hL hm hj hf _ _,
      fun f _ => funext fun x => A.fineOnlyContourAverage_periodic f x,
      fun z f _ => funext fun x => ?_,
      hasRealFiniteKernel_of_readsFinitely _ _ fun x => readsFinitely_contourAverage _ _⟩⟩
  have hwa : ((integerPoint (meshAt L k j) (-z) : FullSpace.Vertex L k j) : AmbientSpace) ∈
      InfiniteLattice.latticeSubgroup (meshAt L k (j + 1)) := by
    rw [← hw z]
    exact (integerPoint (meshAt L k (j + 1)) (-z) : FullSpace.Vertex L k (j + 1)).2
  have hnot : ((x.1 + integerPoint (meshAt L k j) (-z) : FullSpace.Vertex L k j) :
      AmbientSpace) ∉ InfiniteLattice.latticeSubgroup (meshAt L k (j + 1)) := fun hc => x.2 (by
    have := (InfiniteLattice.latticeSubgroup (meshAt L k (j + 1))).sub_mem hc hwa
    simpa using this)
  have e : (fineOnlyVertexFunctions L m k j).shift z
      (FullSpace.fineOnlyContourAverage L (a := meshAt L k (j + 1)) (a' := meshAt L k j) f) x =
      FullSpace.fineOnlyContourAverage L (a := meshAt L k (j + 1)) (a' := meshAt L k j) f
        ⟨x.1 + integerPoint (meshAt L k j) (-z), hnot⟩ := dif_pos hnot
  exact (fineOnlyContourAverage_shift hL0 A.partition (hw z) f x hnot).trans e.symm
end Tower.UnitScale.ContourAveragesPeriodic
end YangMills.Construction
end
