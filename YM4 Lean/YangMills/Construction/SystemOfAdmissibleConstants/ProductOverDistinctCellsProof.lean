import YangMills.Construction.ChessboardTori.CoarseGridsOfAGrid
import YangMills.Construction.MirrorGridsOfEverySide.DominationByTheChessboardProof
import YangMills.Construction.SystemOfAdmissibleConstants.ProductOverDistinctCells
import Mathlib
set_option autoImplicit false
open Filter Set MeasureTheory
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
open ChessboardTori ReflectedCopies
namespace DistinctCellProduct
private theorem finprod_eq_prod_of_injective_of_one {α β M : Type*} [CommMonoid M] [Fintype α]
    (i : α → β) (hi : Function.Injective i) (e : β → M) (f : α → M) (hon : ∀ a, e (i a) = f a)
    (hoff : ∀ b, b ∉ range i → e b = 1) : ∏ᶠ b, e b = ∏ a, f a := by apply _root_.YangMills.Construction.MirrorGridsAllSides.ChessboardDomination.finprod_eq_fintype_prod_of_injective <;> assumption
private theorem prod_le_prod_of_subset_of_one_le {ι : Type*} {O T : Finset ι} (hOT : O ⊆ T)
    (Q : ι → ℝ) (hnonneg : ∀ S ∈ O, 0 ≤ Q S) (hone : ∀ S ∈ T, S ∉ O → 1 ≤ Q S) :
    ∏ S ∈ O, Q S ≤ ∏ S ∈ T, Q S := by
  classical
  rw [← Finset.prod_sdiff hOT]
  have hrest : (1 : ℝ) ≤ ∏ S ∈ T \ O, Q S := by
    calc (1 : ℝ) = ∏ _S ∈ T \ O, (1 : ℝ) := by simp
      _ ≤ ∏ S ∈ T \ O, Q S := Finset.prod_le_prod (fun _ _ => zero_le_one) fun S hS =>
        hone S (Finset.mem_sdiff.mp hS).1 (Finset.mem_sdiff.mp hS).2
  exact le_mul_of_one_le_left (Finset.prod_nonneg hnonneg) hrest
private theorem tendsto_torusSide (D : ChessboardSetup) :
    Tendsto (fun j : ℕ+ => PeriodicLattice.torusSide D.L j) atTop atTop := by
  have hnat : Tendsto (fun j : ℕ+ => (j : ℕ)) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ h => h) fun b =>
      ⟨b.succPNat, by simp⟩
  have hpow : Tendsto (fun t : ℕ => (D.L : ℝ) ^ t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt D.one_lt_factor
  exact (hpow.comp hnat).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
private theorem chessboardNormOfCell_nonneg {D : ChessboardSetup} (g : ReflectionGrid D)
    (S : Set InfiniteLattice.AmbientSpace) (F : D.GaugeField → ℂ) :
    0 ≤ g.chessboardNormOfCell S F := by apply _root_.YangMills.Construction.MirrorGridsAllSides.ChessboardDomination.chessboardNormOfCell_nonneg <;> assumption
private theorem one_mem_cellObservables {D : ChessboardSetup} (S : Set InfiniteLattice.AmbientSpace) :
    (1 : D.GaugeField → ℂ) ∈ ReflectionGrid.cellObservables (D := D) S :=
  ⟨fun _ => 1, measurable_const, ⟨1, fun _ => by simp⟩, rfl⟩
private theorem chessboardNormOfCell_one
    (hC : MirrorGridsAllSides.chessboardEstimate_allSides)
    {D : ChessboardSetup} (g : ReflectionGrid D) (hg : g.HasAdmissibleSide) {m' : ℕ+}
    (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m') (k : Fin 4 → ℤ) :
    (g.withExponent m').chessboardNormOfCell (g.cell k) (1 : D.GaugeField → ℂ) = 1 := by
  obtain ⟨-, hii, -⟩ := hC (D.withExponent m') (g.withExponent m') hg hside
  exact (hii _ ⟨_, ⟨k, rfl⟩, rfl⟩).2.2
private theorem torusAverage_norm_le
    (hC : MirrorGridsAllSides.chessboardEstimate_allSides)
    (hG : MirrorGridsAllSides.ReflectionGridProperties)
    {D : ChessboardSetup} (g : ReflectionGrid D) (hg : g.HasAdmissibleSide) {n : ℕ}
    (k : Fin n → Fin 4 → ℤ) (F : Fin n → D.GaugeField → ℂ) (q : Fin n → ℝ)
    (hF : ∀ i, F i ∈ ReflectionGrid.cellObservables (D := D) (g.cell (k i))) (m' : ℕ+)
    (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m')
    (hinj : Function.Injective fun i => (D.withExponent m').proj '' g.cell (k i))
    (hq : ∀ i, (g.withExponent m').chessboardNormOfCell (g.cell (k i)) (F i) ≤ q i) :
    ‖torusAverage D m' fun U => ∏ i, F i U‖ ≤ ∏ i, q i := by
  obtain ⟨-, -, -, -, -, -, htor, -, -⟩ := hG (D.withExponent m') (g.withExponent m') hg
  obtain ⟨-, -, -, -, -, hread, -⟩ := htor hside
  obtain ⟨⟨hest, -⟩, hii, -⟩ := hC (D.withExponent m') (g.withExponent m') hg hside
  let c : Fin n → (g.withExponent m').torusCellSet := fun a =>
    ⟨(D.withExponent m').proj '' g.cell (k a), ⟨g.cell (k a), ⟨k a, rfl⟩, rfl⟩⟩
  have hc : Function.Injective c := fun a b h => hinj (congrArg Subtype.val h)
  let f : Fin n → ((D.withExponent m').PeriodicLink → Matrices.ComplexMatrix2) → ℂ := fun a =>
    (D.withExponent m').liftedObservable (F a)
  let F' : (g.withExponent m').torusCellSet →
      ((D.withExponent m').PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
    Function.extend c f fun _ _ => 1
  have hF'c : ∀ a, F' (c a) = f a := fun a => hc.extend_apply _ _ a
  have hF'n : ∀ C, C ∉ range c → F' C = fun _ => 1 := fun C hC' =>
    Function.extend_apply' _ _ _ hC'
  have hF'mem : ∀ C, F' C ∈ (g.withExponent m').torusCellObservables C.1 := by
    intro C
    by_cases h : C ∈ range c
    · obtain ⟨a, rfl⟩ := h
      rw [hF'c]
      exact (hread (g.cell (k a)) ⟨k a, rfl⟩ (F a) (hF a)).1
    · rw [hF'n C h]
      exact (hii C.1 C.2).2.1
  have hest' := hest F' hF'mem
  have hprod : (fun U => ∏ᶠ C, F' C U) =
      (D.withExponent m').liftedObservable (fun U => ∏ i, F i U) := by
    funext U
    exact finprod_eq_prod_of_injective_of_one c hc (fun C => F' C U) (fun a => f a U)
      (fun a => by simp only [hF'c]) (fun C hC' => by simp only [hF'n C hC'])
  have hfun : ∏ᶠ C, (g.withExponent m').cellChessboardSeminorm C.1 (F' C) =
      ∏ a, (g.withExponent m').chessboardNormOfCell (g.cell (k a)) (F a) :=
    finprod_eq_prod_of_injective_of_one c hc
      (fun C => (g.withExponent m').cellChessboardSeminorm C.1 (F' C))
      (fun a => (g.withExponent m').chessboardNormOfCell (g.cell (k a)) (F a))
      (fun a => by simp only [hF'c]; rfl)
      (fun C hC' => by simp only [hF'n C hC']; exact (hii C.1 C.2).2.2)
  rw [hprod, hfun] at hest'
  exact hest'.trans
    (Finset.prod_le_prod (fun a _ => chessboardNormOfCell_nonneg _ _ _) fun a _ => hq a)
private theorem integral_norm_le
    (hdom : MirrorGridsAllSides.ChessboardDomination.Statement)
    (hC : MirrorGridsAllSides.chessboardEstimate_allSides)
    {D : ChessboardSetup} (g : ReflectionGrid D) (hg : g.HasAdmissibleSide) {n : ℕ}
    (k : Fin n → Fin 4 → ℤ) (hk : Function.Injective k) (F : Fin n → D.GaugeField → ℂ)
    (q : Fin n → ℝ) (hF : ∀ i, F i ∈ ReflectionGrid.cellObservables (D := D) (g.cell (k i)))
    (hq : ∀ i, ∀ m' : ℕ+, 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m' →
      (g.withExponent m').chessboardNormOfCell (g.cell (k i)) (F i) ≤ q i)
    (ν : Measure D.GaugeField) (hν : ν ∈ InfiniteLattice.periodicGibbsSet D.L D.K D.β) :
    ‖∫ U, ∏ i, F i U ∂ν‖ ≤ ∏ i, q i := by
  classical
  have hlarge : ∀ᶠ j : ℕ+ in atTop, 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L j :=
    (tendsto_torusSide D).eventually_ge_atTop _
  obtain ⟨m₀, hm₀⟩ := hlarge.exists
  let c : Fin n → g.cellSet := fun a => ⟨g.cell (k a), k a, rfl⟩
  have hc : Function.Injective c := fun a b h =>
    hk (g.cell_injective (congrArg Subtype.val h))
  let G : g.cellSet → D.GaugeField → ℂ := Function.extend c F fun _ => 1
  have hGc : ∀ a, G (c a) = F a := fun a => hc.extend_apply _ _ a
  have hGn : ∀ S, S ∉ range c → G S = 1 := fun S hS => Function.extend_apply' _ _ _ hS
  have hGmem : ∀ S, G S ∈ ReflectionGrid.cellObservables (D := D) S.1 := by
    intro S
    by_cases h : S ∈ range c
    · obtain ⟨a, rfl⟩ := h
      rw [hGc]
      exact hF a
    · rw [hGn S h]
      exact one_mem_cellObservables _
  have hfin : {S | G S ≠ 1}.Finite :=
    (finite_range c).subset fun S hS => by_contra fun h => hS (hGn S h)
  obtain ⟨hdomin, -⟩ := hdom D ν hν g hg (fun j => j) (tendsto_torusSide D) G hGmem hfin
  let T : Finset g.cellSet := Finset.univ.image c
  have hOT : hfin.toFinset ⊆ T := by
    intro S hS
    by_contra hST
    have hSr : S ∉ range c := fun ⟨a, ha⟩ =>
      hST (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩)
    exact (hfin.mem_toFinset.mp hS) (hGn S hSr)
  have hoff : ∀ S ∈ T, S ∉ hfin.toFinset → G S = 1 := by
    intro S _ hS
    by_contra h
    exact hS (hfin.mem_toFinset.mpr h)
  have hprod : (fun U => ∏ S ∈ hfin.toFinset, G S U) = fun U => ∏ a, F a U := by
    funext U
    rw [Finset.prod_subset hOT fun S hT hS => by rw [hoff S hT hS]; rfl,
      Finset.prod_image fun a _ b _ h => hc h]
    exact Finset.prod_congr rfl fun a _ => by rw [hGc]
  let Q : g.cellSet → ℝ := Function.extend c q fun _ => 1
  have hQc : ∀ a, Q (c a) = q a := fun a => hc.extend_apply _ _ a
  have hQT : ∏ S ∈ T, Q S = ∏ a, q a := by
    rw [Finset.prod_image fun a _ b _ h => hc h]
    exact Finset.prod_congr rfl fun a _ => hQc a
  have hev : ∀ᶠ j : ℕ+ in atTop,
      ∏ S ∈ hfin.toFinset, (g.withExponent j).chessboardNormOfCell S.1 (G S) ≤ ∏ a, q a := by
    filter_upwards [hlarge] with j hj
    have hfac : ∀ S ∈ hfin.toFinset,
        (g.withExponent j).chessboardNormOfCell S.1 (G S) ≤ Q S := by
      intro S hS
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp (hOT hS)
      rw [hGc, hQc]
      exact hq a j hj
    have hQ0 : ∀ S ∈ hfin.toFinset, 0 ≤ Q S := fun S hS =>
      (chessboardNormOfCell_nonneg _ _ _).trans (hfac S hS)
    have hQ1 : ∀ S ∈ T, S ∉ hfin.toFinset → 1 ≤ Q S := by
      intro S hT hS
      have hGS := hoff S hT hS
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hT
      rw [hGc] at hGS
      rw [hQc]
      have h := hq a j hj
      rw [hGS, chessboardNormOfCell_one hC g hg hj (k a)] at h
      exact h
    calc ∏ S ∈ hfin.toFinset, (g.withExponent j).chessboardNormOfCell S.1 (G S)
        ≤ ∏ S ∈ hfin.toFinset, Q S :=
          Finset.prod_le_prod (fun _ _ => chessboardNormOfCell_nonneg _ _ _) hfac
      _ ≤ ∏ S ∈ T, Q S := prod_le_prod_of_subset_of_one_le hOT Q hQ0 hQ1
      _ = ∏ a, q a := hQT
  have hnn : ∀ᶠ j : ℕ+ in atTop, 0 ≤
      ∏ S ∈ hfin.toFinset, (g.withExponent j).chessboardNormOfCell S.1 (G S) :=
    Eventually.of_forall fun j => Finset.prod_nonneg fun _ _ => chessboardNormOfCell_nonneg _ _ _
  have hlim := liminf_le_of_frequently_le hev.frequently (isBoundedUnder_of_eventually_ge hnn)
  have hbound : ‖∫ U, ∏ S ∈ hfin.toFinset, G S U ∂ν‖ ≤ ∏ a, q a := hdomin.trans hlim
  have hint : (∫ U, ∏ S ∈ hfin.toFinset, G S U ∂ν) = ∫ U, ∏ a, F a U ∂ν :=
    congrArg (fun A : D.GaugeField → ℂ => ∫ U, A U ∂ν) hprod
  rw [hint] at hbound
  exact hbound
end DistinctCellProduct
theorem distinctCellProductBound_holds
    (hdom : MirrorGridsAllSides.ChessboardDomination.Statement)
    (hC : MirrorGridsAllSides.chessboardEstimate_allSides)
    (hG : MirrorGridsAllSides.ReflectionGridProperties) :
    DistinctCellProductBound := by
  intro D g hg n k hk F q hF hq
  exact ⟨fun ν hν => DistinctCellProduct.integral_norm_le hdom hC g hg k hk F q hF hq ν hν,
    fun m' hside hinj => DistinctCellProduct.torusAverage_norm_le hC hG g hg k F q hF m' hside hinj
      fun i => hq i m' hside⟩
end YangMills.Construction.AdmissibleConstants
end
