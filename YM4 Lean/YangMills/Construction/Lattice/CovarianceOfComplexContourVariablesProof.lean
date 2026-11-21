import YangMills.Construction.Averaging.MeanInTheComplexGroup
import YangMills.Construction.Lattice.CovarianceOfComplexContourVariables
import YangMills.Construction.Lattice.IsometryCarriesTheObjectsOfTheAverage
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegions
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace ContourCovariance
open Matrices
variable {L m : ℕ} {j : ℤ}
theorem familyDiameter_comp_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    {V : ι → ComplexMatrix2} {V' : ι' → ComplexMatrix2} (hV : ∀ i, V' (e i) = V i) :
    ComplexMatrix2.familyDiameter V' = ComplexMatrix2.familyDiameter V := by
  unfold ComplexMatrix2.familyDiameter
  rw [← (e.prodCongr e).iSup_comp]
  exact iSup_congr fun p => by simp [hV]
theorem isLogMean_comp_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    {V : ι → ComplexMatrix2} {V' : ι' → ComplexMatrix2} (hV : ∀ i, V' (e i) = V i)
    (S : Set ComplexMatrix2) (W : ComplexMatrix2) :
    ComplexMatrix2.IsLogMean S V' W ↔ ComplexMatrix2.IsLogMean S V W := by
  unfold ComplexMatrix2.IsLogMean
  refine and_congr_right fun _ => and_congr ?_ ?_
  · exact ⟨fun t i => by simpa [hV] using t (e i),
      fun t i' => by obtain ⟨i, rfl⟩ := e.surjective i'; rw [hV]; exact t i⟩
  · rw [← Fintype.sum_equiv e (fun i => ComplexMatrix2.logSeries (V i * W⁻¹))
      (fun i' => ComplexMatrix2.logSeries (V' i' * W⁻¹)) (fun i => by rw [hV])]
theorem complexLogMean_comp_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    {V : ι → ComplexMatrix2} {V' : ι' → ComplexMatrix2} (hV : ∀ i, V' (e i) = V i) :
    complexLogMean V' = complexLogMean V := by
  have hclose : ∀ W : ComplexMatrix2,
      (∃ i', ComplexMatrix2.operatorNorm (V' i' * W⁻¹ - 1) ≤ complexMeanTolerance) ↔
      ∃ i, ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) ≤ complexMeanTolerance := fun W =>
    ⟨fun ⟨i', t⟩ => by
      obtain ⟨i, rfl⟩ := e.surjective i'
      exact ⟨i, by rwa [hV] at t⟩,
      fun ⟨i, t⟩ => ⟨e i, by rwa [hV]⟩⟩
  have hpred : (fun W => ComplexMatrix2.IsLogMean complexGaugeGroup V' W ∧
        ∃ i, ComplexMatrix2.operatorNorm (V' i * W⁻¹ - 1) ≤ complexMeanTolerance) =
      fun W => ComplexMatrix2.IsLogMean complexGaugeGroup V W ∧
        ∃ i, ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) ≤ complexMeanTolerance :=
    funext fun W => propext (and_congr (isLogMean_comp_equiv e hV complexGaugeGroup W) (hclose W))
  unfold complexLogMean
  rw [hpred]
theorem pathHolonomy_mem_complexGaugeGroup {U : Bond L m j → ComplexMatrix2}
    {γ : List (Bond L m j)} (hU : ∀ b ∈ γ, U b ∈ complexGaugeGroup) :
    pathHolonomy U γ ∈ complexGaugeGroup := by
  induction γ with
  | nil => simp [pathHolonomy, ComplexMatrix2.unitDeterminant]
  | cons b γ ih =>
    have h₁ : (U b).det = 1 := hU b List.mem_cons_self
    have h₂ : (pathHolonomy U γ).det = 1 := ih fun c hc => hU c (List.mem_cons_of_mem b hc)
    have e : pathHolonomy U (b :: γ) = U b * pathHolonomy U γ := by simp [pathHolonomy]
    change (pathHolonomy U (b :: γ)).det = 1
    rw [e, Matrix.det_mul, h₁, h₂, one_mul]
theorem bondPreimage_bondImage {σ : FourTorus L m ≃ FourTorus L m} (hσ : MapsCellsAndCubes σ j)
    (hσ' : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    bondPreimage σ (bondImage σ b) = b := by
  have t₁ : ((bondPreimage σ (bondImage σ b)).source : FourTorus L m) = b.source := by
    rw [show ((bondPreimage σ (bondImage σ b)).source : FourTorus L m) =
      σ.symm (bondImage σ b).source from (hσ'.2.2.2.1 (bondImage σ b)).1, (hσ.2.2.2.1 b).1,
      Equiv.symm_apply_apply]
  have t₂ : ((bondPreimage σ (bondImage σ b)).target : FourTorus L m) = b.target := by
    rw [show ((bondPreimage σ (bondImage σ b)).target : FourTorus L m) =
      σ.symm (bondImage σ b).target from (hσ'.2.2.2.1 (bondImage σ b)).2, (hσ.2.2.2.1 b).2,
      Equiv.symm_apply_apply]
  exact Bond.ext (Subtype.ext t₁) (Subtype.ext t₂)
theorem pathHolonomy_transport_pathImage {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : MapsCellsAndCubes σ j) (hσ' : MapsCellsAndCubes σ.symm j) (U : Bond L m j → ComplexMatrix2)
    (γ : List (Bond L m j)) :
    pathHolonomy (transportGaugeField σ U) (pathImage σ γ) = pathHolonomy U γ := by
  simp only [pathHolonomy, pathImage, List.map_map]
  congr 1
  exact List.map_congr_left fun b _ => by
    simp only [Function.comp, transportGaugeField, bondPreimage_bondImage hσ hσ']
theorem isHolomorphicOnFields_complexLogMean {ι : Type*} [Fintype ι] [Nonempty ι]
    {B : Set (Bond L m j)} [Fintype ↥B] (hM : ∀ n : ℕ, 1 ≤ n → Averaging.ComplexLogMeanProperties n)
    (γ : ι → List (Bond L m j)) (hγ : ∀ τ, ∀ b ∈ γ τ, b ∈ B) :
    IsAnalyticOnSupport (complexGaugeFields B) B
      {U ∈ complexGaugeFields B |
        ComplexMatrix2.familyDiameter (fun τ => pathHolonomy U (γ τ)) < Averaging.centreOfMassDiameter}
      (fun U => complexLogMean fun τ => pathHolonomy U (γ τ)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ : ∃ n : ℕ, 1 ≤ n ∧ Nonempty (ι ≃ Fin n) :=
    ⟨_, Fintype.card_pos, ⟨Fintype.equivFin ι⟩⟩
  have hF := hM n hn
  let H : (↥B → ComplexMatrix2) → Fin n → ComplexMatrix2 :=
    fun w i => pathHolonomy (extendWithIdentity B w) (γ (e.symm i))
  have hHan : ∀ w, AnalyticAt ℂ H w := fun w =>
    analyticAt_pi_iff.2 fun i => analyticAt_pathHolonomy_extendByOne (hγ _) w
  have hHc : Continuous H := continuous_iff_continuousAt.2 fun w => (hHan w).continuousAt
  have hval : ∀ W : Bond L m j → ComplexMatrix2,
      H (restrictToBonds B W) = fun i => pathHolonomy W (γ (e.symm i)) := fun W =>
    funext fun i => pathHolonomy_extendByOne W (hγ _)
  have hdiam : ∀ W : Bond L m j → ComplexMatrix2,
      ComplexMatrix2.familyDiameter (H (restrictToBonds B W)) =
      ComplexMatrix2.familyDiameter fun τ => pathHolonomy W (γ τ) := fun W => by
    rw [hval]
    exact familyDiameter_comp_equiv e fun τ => by simp
  have hmean : ∀ W : Bond L m j → ComplexMatrix2, complexLogMean (H (restrictToBonds B W)) =
      complexLogMean fun τ => pathHolonomy W (γ τ) := fun W => by
    rw [hval]
    exact complexLogMean_comp_equiv e fun τ => by simp
  have hmem : ∀ W ∈ complexGaugeFields B, ∀ i, H (restrictToBonds B W) i ∈ complexGaugeGroup := by
    intro W hW i
    rw [hval]
    exact pathHolonomy_mem_complexGaugeGroup fun b hb => hW.1 b (hγ _ b hb)
  have hsmall : ∀ W ∈ {U ∈ complexGaugeFields B |
      ComplexMatrix2.familyDiameter (fun τ => pathHolonomy U (γ τ)) < Averaging.centreOfMassDiameter},
      H (restrictToBonds B W) ∈ Averaging.smallComplexFamilies n := fun W hW =>
    ⟨hmem W hW.1, by rw [hdiam]; exact hW.2⟩
  obtain ⟨O, hO, hOs⟩ := hF.isOpen
  refine ⟨inferInstance, sep_subset _ _, ⟨H ⁻¹' O, hO.preimage hHc, ?_⟩, ?_⟩
  · ext w
    constructor
    · rintro ⟨W, hW, rfl⟩
      have t := hsmall W hW
      rw [hOs] at t
      exact ⟨t.1, W, hW.1, rfl⟩
    · rintro ⟨hw, W, hW, rfl⟩
      have t : H (restrictToBonds B W) ∈ Averaging.smallComplexFamilies n := by
        rw [hOs]
        exact ⟨hw, hmem W hW⟩
      exact ⟨W, ⟨hW, by rw [← hdiam]; exact t.2⟩, rfl⟩
  · intro U hU
    obtain ⟨-, -, hol⟩ := hF.holomorphicInEntries
    obtain ⟨G, hG, hev⟩ := hol _ (hsmall U hU)
    have hGH : AnalyticAt ℂ (fun w => G (H w)) (restrictToBonds B U) := hG.comp (hHan _)
    refine ⟨fun w => G (H w) (), analyticAt_pi_iff.1 hGH (), ?_⟩
    filter_upwards [(hHc.tendsto (restrictToBonds B U)).eventually
      (eventually_nhdsWithin_iff.1 hev)] with w hw W hW hWw
    subst hWw
    rw [← hmean]
    exact congrFun (hw (hsmall W hW)) ()
theorem orderedContour_subset_bondsInside (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K k : ℕ} (hk : k < K)
    (y : SiteAtLevel L m K (k + 1)) {x : SiteAtLevel L m K k}
    (hx : x ∈ sitesInBlock (levelDepth K k) y) (τ : AxisOrdering y x) :
    ∀ b ∈ orderedContour y x τ, b ∈ (bondsInside (unitBlock y) : Set (BondAtLevel L m K k)) := by
  obtain ⟨⟨⟨-, himg⟩, -, -⟩, -, hp⟩ := (hP L m K hL.1 hL.2 hm k hk).1 y
  have hxb : (x : FourTorus L m) ∈ (fun p =>
      (offsetSite (y.toSublattice (levelDepth K k)) p : FourTorus L m)) '' blockIndexBox L := by
    rw [himg]
    exact hx
  obtain ⟨p, hpQ, hpx⟩ := hxb
  obtain rfl : offsetSite (y.toSublattice (levelDepth K k)) p = x := Subtype.ext hpx
  exact ((hp p hpQ).1 _ ⟨τ, rfl⟩).2.2.2.2
theorem complexContourHolonomyCovariance_holds (hG : LatticeIsometryGroupActionStatement)
    (hO : IsometryImages.Statement) (hP : BlockPaths.Statement)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies) : ComplexContourHolonomyCovariance := by
  intro L m i σ hLs hm hi hσ K k hk hik y x hx
  have hL0 : 0 < L := by
    have := hLs.2
    omega
  obtain ⟨⟨⟨H, hH⟩, -⟩, -, -, -, hall⟩ := hG L m i hLs hm hi
  have hinv : σ.symm ∈ latticeIsometries L m i := by
    have h₁ : σ ∈ H := by
      rw [← SetLike.mem_coe, hH]
      exact hσ
    have h₂ : σ⁻¹ ∈ H := H.inv_mem h₁
    rw [← hH]
    exact h₂
  have hj' : levelDepth K k = levelDepth K (k + 1) + 1 := by
    simp only [levelDepth]
    push_cast
    ring
  have hj0 : 0 ≤ levelDepth K (k + 1) := by
    simp only [levelDepth]
    push_cast
    omega
  have hik' : i ≤ levelDepth K k := by omega
  have hc := (hall σ hσ (levelDepth K k) hik').1
  have hs := (hall σ.symm hinv (levelDepth K k) hik').1
  obtain ⟨e, he⟩ := ((hO L m hLs hm i hi σ hσ _ _ hik hj0 hj').1 y).2 x hx
  have hv : ∀ (U : BondAtLevel L m K k → ComplexMatrix2) s,
      contourHolonomies (transportGaugeField σ U) (sitePreimage σ.symm y)
        (sitePreimage σ.symm x) (e s) = contourHolonomies U y x s := fun U s => by
    simp only [contourHolonomies]
    rw [he, pathHolonomy_transport_pathImage hc hs]
  have hdiam : ∀ U : BondAtLevel L m K k → ComplexMatrix2,
      ComplexMatrix2.familyDiameter (contourHolonomies (transportGaugeField σ U)
        (sitePreimage σ.symm y) (sitePreimage σ.symm x)) =
        ComplexMatrix2.familyDiameter (contourHolonomies U y x) := fun U =>
    familyDiameter_comp_equiv e (hv U)
  have hfun : ∀ U : BondAtLevel L m K k → ComplexMatrix2,
      complexMeanContourHolonomy (transportGaugeField σ U) (sitePreimage σ.symm y)
        (sitePreimage σ.symm x) = complexMeanContourHolonomy U y x := fun U =>
    complexLogMean_comp_equiv e (hv U)
  have : Finite (Site L m (levelDepth K k)) := SeparatedSequences.BaseParameters.site_finite hL0 m _
  have : Finite (BondAtLevel L m K k) :=
    Finite.of_injective (fun b : BondAtLevel L m K k => (b.source, b.target)) fun b b' hb =>
      Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  have : Fintype ↥(bondsInside (unitBlock y) : Set (BondAtLevel L m K k)) := Fintype.ofFinite _
  have : Nonempty (AxisOrdering y x) := ⟨(offsetAxes y x).equivFin.symm⟩
  have hhol : IsAnalyticOnSupport
      (complexGaugeFields (bondsInside (unitBlock y) : Set (BondAtLevel L m K k)))
      (bondsInside (unitBlock y) : Set (BondAtLevel L m K k))
      {U ∈ complexGaugeFields (bondsInside (unitBlock y) : Set (BondAtLevel L m K k)) |
        ComplexMatrix2.familyDiameter (contourHolonomies U y x) < Averaging.centreOfMassDiameter}
      (fun U => complexMeanContourHolonomy U y x) :=
    isHolomorphicOnFields_complexLogMean (fun n hn => hM.2.2.2.1 n hn) (orderedContour y x)
      (orderedContour_subset_bondsInside hP hLs hm hk y hx)
  refine ⟨fun U _ => hdiam U, ?_⟩
  simp only [hdiam, hfun]
  exact ⟨by simpa only [IsAnalyticOnSupport, inter_self] using hhol,
    by simpa only [IsAnalyticOnSupport, inter_self] using hhol, fun _ _ => rfl,
    fun _ => rfl⟩
end ContourCovariance
end PeriodicLattice
end YangMills.Construction
