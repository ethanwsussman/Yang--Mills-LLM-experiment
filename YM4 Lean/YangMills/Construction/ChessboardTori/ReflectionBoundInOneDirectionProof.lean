import YangMills.Construction.ChessboardTori.AssertionsOfTheTransferPicture
import YangMills.Construction.ChessboardTori.CellFunctionsReadOnASlab
import YangMills.Construction.ChessboardTori.ElementsCarryingLayersOfCells
import YangMills.Construction.ChessboardTori.ReflectionBoundInOneDirection
import YangMills.Construction.ChessboardTori.ReflectionsAndTranslationsOfSlabs
import YangMills.Construction.ChessboardTori.TraceFormula
import YangMills.Construction.ChessboardTori.WilsonWeightAsASlabIntegral
import YangMills.Construction.InequalityOnMirroredCopies.ArrayMeanIsTheMeanOnTheTorusProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
namespace OneAxisReflectionBound
instance instSecondCountableGaugeGroup :
    SecondCountableTopology Conventions.StandingParameters.gaugeGroup := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact TopologicalSpace.Subtype.secondCountableTopology _
section Residues
variable {n : ℕ} [NeZero n]
def residueRep (a : ℤ) (c : ZMod n) : ℤ := a + ((c - (a : ZMod n)).val : ℤ)
theorem residueRep_mem (a : ℤ) (c : ZMod n) : residueRep a c ∈ Finset.Ico a (a + n) := by
  have := ZMod.val_lt (c - (a : ZMod n))
  simp only [residueRep, Finset.mem_Ico]
  omega
theorem cast_residueRep (a : ℤ) (c : ZMod n) : ((residueRep a c : ℤ) : ZMod n) = c := by
  simp only [residueRep]
  push_cast
  rw [ZMod.natCast_zmod_val]
  ring
theorem residueRep_cast (a : ℤ) {i : ℤ} (hi : i ∈ Finset.Ico a (a + n)) :
    residueRep a ((i : ℤ) : ZMod n) = i := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
  have hc : ((i : ℤ) : ZMod n) - (a : ZMod n) = ((i - a : ℤ) : ZMod n) := by push_cast; rfl
  have hv := ZMod.val_intCast (n := n) (i - a)
  rw [Int.emod_eq_of_lt (by omega) (by omega)] at hv
  rw [residueRep, hc, hv]
  ring
theorem prod_Ico_eq_prod_zmod {M : Type*} [CommMonoid M] (a : ℤ) (f : ℤ → M) :
    ∏ i ∈ Finset.Ico a (a + n), f i = ∏ c : ZMod n, f (residueRep a c) := by
  refine Finset.prod_nbij' (fun i => ((i : ℤ) : ZMod n)) (residueRep a) (fun _ _ => Finset.mem_univ _)
    (fun c _ => residueRep_mem a c) (fun i hi => residueRep_cast a hi)
    (fun c _ => cast_residueRep a c) fun i hi => ?_
  rw [residueRep_cast a hi]
theorem even_residueRep_iff (hn : Even n) (a : ℤ) (c : ZMod n) :
    Even (residueRep a c) ↔ Even c.val := by
  have h := ZMod.val_intCast (n := n) (residueRep a c)
  rw [cast_residueRep] at h
  have h2 : (2 : ℤ) ∣ (n : ℤ) := by
    obtain ⟨d, hd⟩ := hn
    exact ⟨d, by rw [hd]; push_cast; ring⟩
  rw [← Int.even_coe_nat, h, Int.even_iff, Int.even_iff, Int.emod_emod_of_dvd _ h2]
end Residues
theorem signedConj_prod {ι : Type*} (σ : ℤˣ) (s : Finset ι) (f : ι → ℂ) :
    Conventions.signedConj σ (∏ i ∈ s, f i) = ∏ i ∈ s, Conventions.signedConj σ (f i) := by
  unfold Conventions.signedConj
  split_ifs
  · rfl
  · exact map_prod _ _ _
theorem isBoundedObservable_prod {a : ℝ} {ι : Type*} (s : Finset ι)
    (A : ι → InfiniteLattice.GaugeField a → ℂ)
    (h : ∀ i ∈ s, InfiniteLattice.IsBoundedObservable (A i)) :
    InfiniteLattice.IsBoundedObservable fun U => ∏ i ∈ s, A i U := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.isBoundedObservable_finset_prod <;> assumption
theorem isBoundedObservable_of_mem_cellObservables {D : ChessboardSetup}
    {S : Set InfiniteLattice.AmbientSpace}
    {F : D.GaugeField → ℂ} (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    InfiniteLattice.IsBoundedObservable F := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.isBoundedObservable_of_mem_cellObservables <;> assumption
theorem update_mem_cubeIndexBox {k₀ k : Fin 4 → ℤ} {n : ℕ} {μ : Fin 4} {i : ℤ}
    (hk : k ∈ cubeIndexBox k₀ n) (hi : i ∈ Finset.Ico (k₀ μ) (k₀ μ + n)) :
    Function.update k μ i ∈ cubeIndexBox k₀ n := by
  refine Fintype.mem_piFinset.mpr fun ν => ?_
  by_cases h : ν = μ
  · subst h
    simpa using hi
  · rw [Function.update_of_ne h]
    exact Fintype.mem_piFinset.mp hk ν
theorem PeriodSubgroup.ext_mult {D : ChessboardSetup} {P Q : PeriodSubgroup D}
    (h : P.mult = Q.mult) : P = Q := by apply _root_.YangMills.SharedProofs.p50270 <;> assumption
section Slabs
variable {D : ChessboardSetup} (T : TransferSetup D) (m : SlabCount)
theorem isBoundedMeasurable_prod {ι : Type*} (s : Finset ι) (ψ : ι → T.SlabConfig → ℂ)
    (h : ∀ i ∈ s, T.IsBoundedMeasurable (ψ i)) :
    T.IsBoundedMeasurable fun η => ∏ i ∈ s, ψ i η := by
  refine ⟨Finset.measurable_prod _ fun i hi => (h i hi).1, ?_⟩
  have hb : ∀ i, ∃ C : ℝ, i ∈ s → ∀ η, ‖ψ i η‖ ≤ C := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨C, hC⟩ := (h i hi).2
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h' => absurd h' hi⟩
  choose C hC using hb
  refine ⟨∏ i ∈ s, C i, fun η => ?_⟩
  rw [norm_prod]
  exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i hi => hC i hi η
theorem isBoundedMeasurable_mul {Φ Ψ : T.SlabConfig → ℂ} (hΦ : T.IsBoundedMeasurable Φ)
    (hΨ : T.IsBoundedMeasurable Ψ) : T.IsBoundedMeasurable (Φ * Ψ) := by
  obtain ⟨h1, C, hC⟩ := hΦ
  obtain ⟨h2, C', hC'⟩ := hΨ
  refine ⟨h1.mul h2, C * C', fun η => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hC η) (hC' η) (norm_nonneg _) ((norm_nonneg _).trans (hC η))
theorem slabBoltzmann_zero_eq (c c' : ZMod (m : ℕ)) :
    T.slabBoltzmann m (fun _ => 0) c = T.slabBoltzmann m (fun _ => 0) c' := by
  funext η
  simp only [TransferSetup.slabBoltzmann]
theorem slabProductIntegral_alternating (hm : Even (m : ℕ)) {Φ : T.SlabConfig → ℂ}
    (hinv : T.reflectConj (T.reflectConj Φ) = Φ)
    (halt : T.alternatingSlabIntegral m hm (T.reflectConj Φ) = T.alternatingSlabIntegral m hm Φ)
    (a i : ℤ) :
    T.slabProductIntegral m (fun c => if Even (residueRep a c - i) then Φ else T.reflectConj Φ) =
      T.alternatingSlabIntegral m hm Φ := by
  by_cases hi : Even i
  · unfold TransferSetup.alternatingSlabIntegral
    congr 1
    funext c
    have : Even (residueRep a c - i) ↔ Even c.val := by
      rw [Int.even_sub, even_residueRep_iff hm]
      tauto
    simp only [this]
  · rw [← halt]
    unfold TransferSetup.alternatingSlabIntegral
    congr 1
    funext c
    have : Even (residueRep a c - i) ↔ ¬ Even c.val := by
      rw [Int.even_sub, even_residueRep_iff hm]
      tauto
    by_cases h : Even c.val
    · simp [this, h]
    · simp [this, h, hinv]
theorem familyExpectation_eq (hB : SlabDecompositionOfWilsonWeight.Statement) (Z : ℝ)
    (hZ : ∀ H : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable H →
      D.liftedExpectation H =
        (∫ U, H ((T.torusPeriods m).liftGaugeField U) *
            Complex.exp (-(D.β : ℂ) * ((T.torusPeriods m).wilsonAction U : ℂ))
              ∂(T.torusPeriods m).haarMeasure) /
          (Z : ℂ))
    (k₀ : Fin 4 → ℤ) (G : (Fin 4 → ℤ) → D.GaugeField → ℂ)
    (hG : ∀ k ∈ cubeIndexBox k₀ (m : ℕ), InfiniteLattice.IsBoundedObservable (G k))
    (Ψ : ℤ → T.SlabConfig → ℂ)
    (hread : ∀ i ∈ Finset.Ico (k₀ T.axis) (k₀ T.axis + ((m : ℕ) : ℤ)), ∀ U,
      ∏ k ∈ (cubeIndexBox k₀ (m : ℕ)).filter (fun k => k T.axis = i),
          G k ((T.torusPeriods m).liftGaugeField U) =
        Ψ i (T.slabRestriction m ((i : ℤ) : ZMod (m : ℕ)) U)) :
    D.familyExpectation k₀ (m : ℕ) G =
      T.slabProductIntegral m
          (fun c => T.slabBoltzmann m (fun _ => 0) 0 * Ψ (residueRep (k₀ T.axis) c)) /
        (Z : ℂ) := by
  have hprod : ∀ U : (T.torusPeriods m).GaugeConfig,
      ∏ k ∈ cubeIndexBox k₀ (m : ℕ), G k ((T.torusPeriods m).liftGaugeField U) =
        ∏ c : ZMod (m : ℕ), Ψ (residueRep (k₀ T.axis) c) (T.slabRestriction m c U) := by
    intro U
    have hmaps : ∀ k ∈ cubeIndexBox k₀ (m : ℕ),
        k T.axis ∈ Finset.Ico (k₀ T.axis) (k₀ T.axis + ((m : ℕ) : ℤ)) :=
      fun k hk => Fintype.mem_piFinset.mp hk T.axis
    rw [← Finset.prod_fiberwise_of_maps_to hmaps, Finset.prod_congr rfl fun i hi => hread i hi U,
      prod_Ico_eq_prod_zmod (k₀ T.axis)
        (fun i => Ψ i (T.slabRestriction m ((i : ℤ) : ZMod (m : ℕ)) U))]
    exact Finset.prod_congr rfl fun c _ => by rw [cast_residueRep]
  unfold ChessboardSetup.familyExpectation
  rw [hZ _ (isBoundedObservable_prod _ _ hG)]
  congr 1
  simp only [hprod]
  rw [hB D T m fun c => Ψ (residueRep (k₀ T.axis) c)]
  congr 1
end Slabs
theorem reflectFamily_mem {D : ChessboardSetup} (g : ReflectionGrid D)
    (hG : GridBasicProperties.Statement)
    (k₀ : Fin 4 → ℤ) (n : ℕ) (μ : Fin 4) (F : (Fin 4 → ℤ) → D.GaugeField → ℂ)
    (hF : ∀ k ∈ cubeIndexBox k₀ n, F k ∈ ReflectionGrid.cellObservables (D := D) (g.cell k))
    {i : ℤ} (hi : i ∈ Finset.Ico (k₀ μ) (k₀ μ + n)) {k : Fin 4 → ℤ} (hk : k ∈ cubeIndexBox k₀ n) :
    g.reflectFamily μ i F k ∈ ReflectionGrid.cellObservables (D := D) (g.cell k) := by
  obtain ⟨_, _, _, hcoord, hrules, _, _⟩ := hG D g
  have hk' := update_mem_cubeIndexBox hk hi
  have hS : g.cell (Function.update k μ i) ∈ g.cellSet := ⟨_, rfl⟩
  have hS' : g.cell k ∈ g.cellSet := ⟨_, rfl⟩
  obtain ⟨r, hr, _⟩ := hcoord.2.2.2.2.2.2.1 _ hS _ hS'
  exact (hrules _ hS _ hS' _ hS' r hr _ (hF _ hk') _ (hF _ hk') 1).1
theorem reflectFamily_layer_prod {D : ChessboardSetup} (T : TransferSetup D) (m : SlabCount)
    (hG : GridBasicProperties.Statement) (hcarry : LayerCarryingElements.Statement)
    (hside : 2 * T.grid.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    (hn : ((m : ℕ) : ℝ) = T.grid.cellsAcross) (hcross : ∀ ν, T.transverseCells ν = ((m : ℕ) : ℤ))
    (k₀ : Fin 4 → ℤ) (F : (Fin 4 → ℤ) → D.GaugeField → ℂ)
    (ψ : (Fin 4 → ℤ) → T.SlabConfig → ℂ)
    (hψ : ∀ k ∈ cubeIndexBox k₀ (m : ℕ), ∀ U : (T.torusPeriods m).GaugeConfig,
      F k ((T.torusPeriods m).liftGaugeField U) =
        ψ k (T.slabRestriction m ((k T.axis : ℤ) : ZMod (m : ℕ)) U))
    {i i' : ℤ} (hi : i ∈ Finset.Ico (k₀ T.axis) (k₀ T.axis + ((m : ℕ) : ℤ)))
    (hi' : i' ∈ Finset.Ico (k₀ T.axis) (k₀ T.axis + ((m : ℕ) : ℤ)))
    (U : (T.torusPeriods m).GaugeConfig) :
    ∏ k ∈ (cubeIndexBox k₀ (m : ℕ)).filter (fun k => k T.axis = i'),
        T.grid.reflectFamily T.axis i F k ((T.torusPeriods m).liftGaugeField U) =
      (if Even (i' - i) then
          (fun η => ∏ k ∈ (cubeIndexBox k₀ (m : ℕ)).filter (fun k => k T.axis = i), ψ k η)
        else T.reflectConj
          (fun η => ∏ k ∈ (cubeIndexBox k₀ (m : ℕ)).filter (fun k => k T.axis = i), ψ k η))
        (T.slabRestriction m ((i' : ℤ) : ZMod (m : ℕ)) U) := by
  obtain ⟨r, s, hcar, hsgn, hrs, hη⟩ := hcarry D T m hside hn hcross i i'
  obtain ⟨_, _, _, hcoord, _, _, _⟩ := hG D T.grid
  have huniq := hcoord.2.2.2.2.2.2.1
  have hterm : ∀ k ∈ (cubeIndexBox k₀ (m : ℕ)).filter (fun k => k T.axis = i'),
      T.grid.reflectFamily T.axis i F k ((T.torusPeriods m).liftGaugeField U) =
        Conventions.signedConj (orientationSign r.1) (ψ (Function.update k T.axis i)
          (T.slabRestriction m ((i : ℤ) : ZMod (m : ℕ)) (s U))) := by
    intro k hk
    obtain ⟨hkI, hki⟩ := Finset.mem_filter.mp hk
    have hk' := update_mem_cubeIndexBox hkI hi
    have hupd : Function.update k T.axis i' = k := by
      rw [← hki]
      exact Function.update_eq_self _ _
    have hr : r.1 '' T.grid.cell (Function.update k T.axis i) = T.grid.cell k := by
      have := hcar k
      rwa [hupd] at this
    have hmov : T.grid.mover (T.grid.cell (Function.update k T.axis i))
        (T.grid.cell k) = r := by
      have hex : ∃ r' : T.grid.reflectionGroup,
          r'.1 '' T.grid.cell (Function.update k T.axis i) = T.grid.cell k := ⟨r, hr⟩
      exact (huniq _ ⟨_, rfl⟩ _ ⟨_, rfl⟩).unique (Classical.epsilon_spec hex) hr
    have hval := hψ _ hk' (s U)
    rw [Function.update_self] at hval
    unfold ReflectionGrid.reflectFamily ReflectionGrid.transportTo
    rw [hmov]
    change Conventions.signedConj (orientationSign r.1) (F (Function.update k T.axis i)
      ((T.grid.toLatticeSym r).pullbackField
        ((T.torusPeriods m).liftGaugeField U))) = _
    rw [hrs U, hval]
  have hbij : ∏ k ∈ (cubeIndexBox k₀ (m : ℕ)).filter (fun k => k T.axis = i'),
        ψ (Function.update k T.axis i) (T.slabRestriction m ((i : ℤ) : ZMod (m : ℕ)) (s U)) =
      ∏ k ∈ (cubeIndexBox k₀ (m : ℕ)).filter (fun k => k T.axis = i),
        ψ k (T.slabRestriction m ((i : ℤ) : ZMod (m : ℕ)) (s U)) := by
    refine Finset.prod_nbij' (fun k => Function.update k T.axis i)
      (fun k => Function.update k T.axis i') ?_ ?_ ?_ ?_ fun _ _ => rfl
    · intro k hk
      obtain ⟨hkI, _⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨update_mem_cubeIndexBox hkI hi, Function.update_self _ _ _⟩
    · intro k hk
      obtain ⟨hkI, _⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨update_mem_cubeIndexBox hkI hi', Function.update_self _ _ _⟩
    · intro k hk
      obtain ⟨_, hki⟩ := Finset.mem_filter.mp hk
      simp only [Function.update_idem]
      rw [← hki]
      exact Function.update_eq_self _ _
    · intro k hk
      obtain ⟨_, hki⟩ := Finset.mem_filter.mp hk
      simp only [Function.update_idem]
      rw [← hki]
      exact Function.update_eq_self _ _
  rw [Finset.prod_congr rfl hterm, ← signedConj_prod, hbij]
  by_cases he : Even (i' - i)
  · have h1 : orientationSign r.1 = 1 := by rw [hsgn]; exact Int.negOnePow_even _ he
    rw [if_pos he, h1, hη U, if_pos he]
    simp [Conventions.signedConj]
  · have h1 : orientationSign r.1 = -1 := by
      rw [hsgn]
      exact Int.negOnePow_odd _ (Int.not_even_iff_odd.mp he)
    rw [if_neg he, h1, hη U, if_neg he]
    simp [Conventions.signedConj, TransferSetup.reflectConj]
theorem bound_of_transferSetup {D : ChessboardSetup} (T : TransferSetup D) (m : SlabCount)
    (hG : GridBasicProperties.Statement)
    (hPic : TransferAssertions.Statement)
    (hSlabs : SlabSymmetries.Statement)
    (hTrace : CyclicTraceFormula.Statement)
    (hExp : PeriodExpectation.Statement)
    (hB : SlabDecompositionOfWilsonWeight.Statement)
    (hC : SlabRestrictionOfCellFunctions.Statement)
    (hcarry : LayerCarryingElements.Statement)
    (hside : 2 * T.grid.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    (hn : ((m : ℕ) : ℝ) = T.grid.cellsAcross) (hcross : ∀ ν, T.transverseCells ν = ((m : ℕ) : ℤ))
    (hP : T.torusPeriods m = D.cubicPeriod) (hm : Even (m : ℕ))
    (k₀ : Fin 4 → ℤ) (F : (Fin 4 → ℤ) → D.GaugeField → ℂ)
    (hF : ∀ k ∈ cubeIndexBox k₀ (m : ℕ),
      F k ∈ ReflectionGrid.cellObservables (D := D) (T.grid.cell k)) :
    (∀ i ∈ Finset.Ico (k₀ T.axis) (k₀ T.axis + ((m : ℕ) : ℤ)),
      (D.familyExpectation k₀ (m : ℕ) (T.grid.reflectFamily T.axis i F)).im = 0 ∧
        0 ≤ (D.familyExpectation k₀ (m : ℕ) (T.grid.reflectFamily T.axis i F)).re) ∧
    ‖D.familyExpectation k₀ (m : ℕ) F‖ ≤
      ∏ i ∈ Finset.Ico (k₀ T.axis) (k₀ T.axis + ((m : ℕ) : ℤ)),
        (D.familyExpectation k₀ (m : ℕ) (T.grid.reflectFamily T.axis i F)).re ^
          (1 / ((m : ℕ) : ℝ)) := by
  obtain ⟨Z, hZpos, hZ⟩ := hExp D (T.torusPeriods m) hP
  have hread := fun k (hk : k ∈ cubeIndexBox k₀ (m : ℕ)) =>
    hC D T m hside hn hcross k (F k) (hF k hk)
  choose! ψ hψb hψ using hread
  let Ψ : ℤ → T.SlabConfig → ℂ := fun i η =>
    ∏ k ∈ (cubeIndexBox k₀ (m : ℕ)).filter (fun k => k T.axis = i), ψ k η
  have hΨb : ∀ i, T.IsBoundedMeasurable (Ψ i) := fun i =>
    isBoundedMeasurable_prod T _ _ fun k hk => hψb k (Finset.mem_filter.mp hk).1
  let B : T.SlabConfig → ℂ := T.slabBoltzmann m (fun _ => 0) 0
  have hpic := hPic D T m
  have hrevAll := hpic.2.2.2.2.2.1
  have hweights := hpic.2.2.2.2.2.2.2.2
  have hBb : T.IsBoundedMeasurable B := by
    obtain ⟨hc, hb, _⟩ := (hweights (fun _ => 0) ⟨0, by simp⟩).1 0
    exact ⟨hc.measurable, hb⟩
  obtain ⟨_, _, _, hrev⟩ := hrevAll
  have hBrev : T.reflectConj B = B := by
    have h := (hSlabs D T m hm 0).2.2.2.2.2.2.2.2.2 (fun _ => 0) ⟨0, by simp⟩
    have h2 := h.2 fun _ _ => by simp
    have h3 : T.slabBoltzmann m (fun _ => 0) (0 + 1) = B := slabBoltzmann_zero_eq T m _ _
    rw [h3] at h2
    exact h2.symm
  let Φ : ℤ → T.SlabConfig → ℂ := fun i => B * Ψ i
  have hΦb : ∀ i, T.IsBoundedMeasurable (Φ i) := fun i => isBoundedMeasurable_mul T hBb (hΨb i)
  obtain ⟨_, _, htrace⟩ := hTrace D T
  obtain ⟨halt, hbound, _⟩ := htrace m hm
  have hnumF : D.familyExpectation k₀ (m : ℕ) F =
      T.slabProductIntegral m (fun c => Φ (residueRep (k₀ T.axis) c)) / (Z : ℂ) := by
    refine familyExpectation_eq T m hB Z hZ k₀ F
      (fun k hk => isBoundedObservable_of_mem_cellObservables (hF k hk)) Ψ fun i _ U => ?_
    refine Finset.prod_congr rfl fun k hk => ?_
    obtain ⟨hkI, hki⟩ := Finset.mem_filter.mp hk
    rw [hψ k hkI U, hki]
  have hnumR : ∀ i ∈ Finset.Ico (k₀ T.axis) (k₀ T.axis + ((m : ℕ) : ℤ)),
      D.familyExpectation k₀ (m : ℕ) (T.grid.reflectFamily T.axis i F) =
        T.alternatingSlabIntegral m hm (Φ i) / (Z : ℂ) := by
    intro i hi
    have h1 := familyExpectation_eq T m hB Z hZ k₀ (T.grid.reflectFamily T.axis i F)
      (fun k hk => isBoundedObservable_of_mem_cellObservables
        (reflectFamily_mem T.grid hG k₀ (m : ℕ) T.axis F hF hi hk))
      (fun i' => if Even (i' - i) then Ψ i else T.reflectConj (Ψ i))
      (fun i' hi' U => reflectFamily_layer_prod T m hG hcarry hside hn hcross k₀ F ψ hψ hi hi' U)
    rw [h1]
    congr 1
    obtain ⟨_, hinv, _, _⟩ := hrev (Φ i) (Φ i) (hΦb i) (hΦb i)
    have halt' := (halt (Φ i) (hΦb i)).2.2.2.2
    rw [← slabProductIntegral_alternating T m hm hinv halt' (k₀ T.axis) i]
    congr 1
    funext c
    by_cases he : Even (residueRep (k₀ T.axis) c - i)
    · simp only [if_pos he, Φ]
      rfl
    · simp only [if_neg he]
      obtain ⟨_, _, hmul, _⟩ := hrev B (Ψ i) hBb (hΨb i)
      change B * T.reflectConj (Ψ i) = T.reflectConj (B * Ψ i)
      rw [hmul, hBrev]
  have haltform : ∀ i, ∃ x : ℝ, 0 ≤ x ∧ T.alternatingSlabIntegral m hm (Φ i) = (x : ℂ) :=
    fun i => ⟨_, (halt (Φ i) (hΦb i)).2.2.2.1, (halt (Φ i) (hΦb i)).2.2.1⟩
  choose a ha haeq using haltform
  have hfam : ∀ i ∈ Finset.Ico (k₀ T.axis) (k₀ T.axis + ((m : ℕ) : ℤ)),
      D.familyExpectation k₀ (m : ℕ) (T.grid.reflectFamily T.axis i F) =
        ((a i / Z : ℝ) : ℂ) := by
    intro i hi
    rw [hnumR i hi, haeq i]
    push_cast
    rfl
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hfam i hi]
    exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact div_nonneg (ha i) hZpos.le⟩
  · have hm0 : ((m : ℕ) : ℝ) ≠ 0 := by
      have := m.2
      positivity
    have hprodZ : ∏ _i ∈ Finset.Ico (k₀ T.axis) (k₀ T.axis + ((m : ℕ) : ℤ)),
        Z ^ (1 / ((m : ℕ) : ℝ)) = Z := by
      rw [Finset.prod_const, Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast, one_div,
        Real.rpow_inv_natCast_pow hZpos.le (by have := m.2; omega)]
    have hright : ∏ i ∈ Finset.Ico (k₀ T.axis) (k₀ T.axis + ((m : ℕ) : ℤ)),
        (D.familyExpectation k₀ (m : ℕ) (T.grid.reflectFamily T.axis i F)).re ^
          (1 / ((m : ℕ) : ℝ)) =
        (∏ c : ZMod (m : ℕ), a (residueRep (k₀ T.axis) c) ^ (1 / ((m : ℕ) : ℝ))) / Z := by
      rw [Finset.prod_congr rfl fun i hi => by
        rw [hfam i hi, Complex.ofReal_re, Real.div_rpow (ha i) hZpos.le],
        Finset.prod_div_distrib, hprodZ,
        prod_Ico_eq_prod_zmod (k₀ T.axis) (fun i => a i ^ (1 / ((m : ℕ) : ℝ)))]
    rw [hright, hnumF, norm_div, Complex.norm_real, Real.norm_of_nonneg hZpos.le]
    refine div_le_div_of_nonneg_right ?_ hZpos.le
    refine (hbound (fun c => Φ (residueRep (k₀ T.axis) c)) fun c => hΦb _).trans (le_of_eq ?_)
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [haeq, Complex.ofReal_re]
end OneAxisReflectionBound
open OneAxisReflectionBound in
theorem OneAxisReflectionBound.statement_holds
    (hArith : ReflectionGridArithmetic.Statement)
    (hG : GridBasicProperties.Statement)
    (hPic : TransferAssertions.Statement)
    (hSlabs : SlabSymmetries.Statement)
    (hTrace : CyclicTraceFormula.Statement)
    (hExp : PeriodExpectation.Statement)
    (hB : SlabDecompositionOfWilsonWeight.Statement)
    (hC : SlabRestrictionOfCellFunctions.Statement)
    (hcarry : LayerCarryingElements.Statement) :
    OneAxisReflectionBound.Statement := by
  intro D g hside k₀ n hn μ F hF
  obtain ⟨_, hcp, heven, h2, hgrp, _⟩ := ((hArith D).2.2.2 g).2 hside |>.1
  have hnc : (n : ℤ) = g.cellsPerTorusSide := by
    have : (n : ℝ) = (g.cellsPerTorusSide : ℝ) := hn.trans hcp
    exact_mod_cast this
  have hn2 : 2 ≤ n := by omega
  have hevenn : Even n := by
    rw [← Int.even_coe_nat, hnc]
    exact heven
  let T : TransferSetup D := ⟨g, μ, fun _ => (n : ℤ), fun _ => by omega⟩
  let m : SlabCount := ⟨n, hn2⟩
  have hP : T.torusPeriods m = D.cubicPeriod := by
    rw [← hgrp]
    refine OneAxisReflectionBound.PeriodSubgroup.ext_mult (funext fun ν => ?_)
    change T.cellCounts m ν * g.cellRatio = g.cellsPerTorusSide * g.cellRatio
    rw [TransferSetup.cellCounts]
    split_ifs
    · change (n : ℤ) * g.cellRatio = _
      rw [hnc]
    · change (n : ℤ) * g.cellRatio = _
      rw [hnc]
  exact bound_of_transferSetup T m hG hPic hSlabs hTrace hExp hB hC hcarry hside hn
    (fun _ => rfl) hP hevenn k₀ F hF
end YangMills.Construction.ChessboardTori
end
