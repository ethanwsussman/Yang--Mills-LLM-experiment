import YangMills.Construction.Lattice.CombGaugeRoundACoarsePlaquetteProof
import YangMills.Construction.Lattice.FlatConfigurationsOnBoxesAndTheirAverages
import YangMills.Construction.Lattice.LatticesCubesDoubleBlocksAndLocalityOfAverages
import YangMills.Construction.Lattice.LiftingIsConsistentWithTheAverages
import YangMills.Construction.Lattice.LocalityAndGaugeCovarianceOfTheAveragingMap
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m K : ℕ} {j : ℤ}
private theorem inv_mul_self_of_mem_su2 {A : ComplexMatrix2}
    (h : A ∈ ComplexMatrix2.specialUnitary) : A⁻¹ * A = 1 := by apply _root_.YangMills.SharedProofs.p1227 <;> assumption
private theorem mul_inv_self_of_mem_su2 {A : ComplexMatrix2}
    (h : A ∈ ComplexMatrix2.specialUnitary) : A * A⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p21267 <;> assumption
private theorem inv_inv_of_mem_su2 {A : ComplexMatrix2}
    (h : A ∈ ComplexMatrix2.specialUnitary) : A⁻¹⁻¹ = A := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
private theorem mul_mul_inv_mul_cancel {A B C : ComplexMatrix2}
    (h : B ∈ ComplexMatrix2.specialUnitary) : A * B * (B⁻¹ * C) = A * C := by
  rw [mul_assoc, ← mul_assoc B, mul_inv_self_of_mem_su2 h, one_mul]
private theorem pathHolonomy_mem_su2 {U : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, U b ∈ ComplexMatrix2.specialUnitary)
    (γ : List (Bond L m j)) : pathHolonomy U γ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.PeriodicLattice.CoarsePlaquetteGauge.pathHolonomy_mem <;> assumption
private theorem exists_coordCount_le (hL : 0 < L) (S : Set (Site L m j)) :
    ∃ r : ℕ, ∀ μ, coordCount μ S ≤ (r : ℕ∞) + 1 := by
  have := SeparatedSequences.BaseParameters.site_finite hL m j
  refine ⟨∑ μ : Fin 4, ((fun x : Site L m j => (x : FourTorus L m) μ) '' S).ncard, fun μ => ?_⟩
  have hfin : ((fun x : Site L m j => (x : FourTorus L m) μ) '' S).Finite :=
    (Set.toFinite S).image _
  have hle : ((fun x : Site L m j => (x : FourTorus L m) μ) '' S).ncard ≤
      ∑ μ : Fin 4, ((fun x : Site L m j => (x : FourTorus L m) μ) '' S).ncard :=
    Finset.single_le_sum
      (f := fun μ : Fin 4 => ((fun x : Site L m j => (x : FourTorus L m) μ) '' S).ncard)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ μ)
  unfold coordCount
  rw [← hfin.cast_ncard_eq]
  exact le_trans (by exact_mod_cast hle) le_self_add
private theorem pathHolonomy_forwardFlow {U : Bond L m j → ComplexMatrix2}
    {g : Site L m j → ComplexMatrix2} {S : Set (Site L m j)}
    (hg : ∀ x, g x ∈ ComplexMatrix2.specialUnitary)
    (hU : ∀ b : Bond L m j, b.LiesIn S → U b = (g b.source)⁻¹ * g b.target) (μ : Fin 4) (n : ℕ) :
    ∀ x : Site L m j, (∀ z ∈ sitesOfPath x (forwardAxisPath x μ n), z ∈ S) →
      pathHolonomy U (forwardAxisPath x μ n) = (g x)⁻¹ * g (x + n • unitStep L m j μ) := by
  induction n with
  | zero =>
    intro x _
    simp [forwardAxisPath, pathHolonomy, inv_mul_self_of_mem_su2 (hg x)]
  | succ n ih =>
    intro x hS
    have hx : x ∈ S := hS x (by simp [sitesOfPath])
    have hx' : x + unitStep L m j μ ∈ S :=
      hS _ (by simp [sitesOfPath, forwardAxisPath, Bond.forwardFrom])
    have hrest := ih (x + unitStep L m j μ) (fun z hz => hS z (by
      simp only [sitesOfPath, forwardAxisPath, List.map_cons, List.mem_cons] at hz ⊢
      exact Or.inr (by simpa [Bond.forwardFrom] using hz)))
    have hb : U (Bond.forwardFrom x μ) = (g x)⁻¹ * g (x + unitStep L m j μ) :=
      hU (Bond.forwardFrom x μ) ⟨hx, hx'⟩
    have hshift : x + unitStep L m j μ + n • unitStep L m j μ = x + (n + 1) • unitStep L m j μ := by
      rw [succ_nsmul]
      abel
    have hcons : pathHolonomy U (forwardAxisPath x μ (n + 1)) =
        U (Bond.forwardFrom x μ) * pathHolonomy U (forwardAxisPath (x + unitStep L m j μ) μ n) := by
      simp [pathHolonomy, forwardAxisPath]
    rw [hcons, hrest, hb, hshift, mul_mul_inv_mul_cancel (hg _)]
private theorem pathHolonomy_backwardFlow {U : Bond L m j → ComplexMatrix2}
    {g : Site L m j → ComplexMatrix2} {S : Set (Site L m j)}
    (hg : ∀ x, g x ∈ ComplexMatrix2.specialUnitary)
    (hU : ∀ b : Bond L m j, b.LiesIn S → U b = (g b.source)⁻¹ * g b.target) (μ : Fin 4) (n : ℕ) :
    ∀ x : Site L m j, (∀ z ∈ sitesOfPath x (backwardAxisPath x μ n), z ∈ S) →
      pathHolonomy U (backwardAxisPath x μ n) = (g x)⁻¹ * g (x - n • unitStep L m j μ) := by
  induction n with
  | zero =>
    intro x _
    simp [backwardAxisPath, pathHolonomy, inv_mul_self_of_mem_su2 (hg x)]
  | succ n ih =>
    intro x hS
    have hx : x ∈ S := hS x (by simp [sitesOfPath])
    have hx' : x - unitStep L m j μ ∈ S :=
      hS _ (by simp [sitesOfPath, backwardAxisPath, Bond.backwardFrom])
    have hrest := ih (x - unitStep L m j μ) (fun z hz => hS z (by
      simp only [sitesOfPath, backwardAxisPath, List.map_cons, List.mem_cons] at hz ⊢
      exact Or.inr (by simpa [Bond.backwardFrom] using hz)))
    have hb : U (Bond.backwardFrom x μ) = (g x)⁻¹ * g (x - unitStep L m j μ) :=
      hU (Bond.backwardFrom x μ) ⟨hx, hx'⟩
    have hshift : x - unitStep L m j μ - n • unitStep L m j μ = x - (n + 1) • unitStep L m j μ := by
      rw [succ_nsmul]
      abel
    have hcons : pathHolonomy U (backwardAxisPath x μ (n + 1)) =
        U (Bond.backwardFrom x μ) * pathHolonomy U (backwardAxisPath (x - unitStep L m j μ) μ n) := by
      simp [pathHolonomy, backwardAxisPath]
    rw [hcons, hrest, hb, hshift, mul_mul_inv_mul_cancel (hg _)]
private theorem pathHolonomy_axialPath {U : Bond L m j → ComplexMatrix2}
    {g : Site L m j → ComplexMatrix2} {S : Set (Site L m j)}
    (hg : ∀ x, g x ∈ ComplexMatrix2.specialUnitary)
    (hU : ∀ b : Bond L m j, b.LiesIn S → U b = (g b.source)⁻¹ * g b.target)
    {x x' : Site L m j} {μ : Fin 4} {n : ℤ} (hax : IsAxialDisplacement x x' μ n)
    (hS : ∀ z ∈ sitesOfPath x (axialPath x x'), z ∈ S) :
    pathHolonomy U (axialPath x x') = (g x)⁻¹ * g x' := by
  have hex : ∃ p : Fin 4 × ℤ, IsAxialDisplacement x x' p.1 p.2 := ⟨(μ, n), hax⟩
  unfold axialPath at hS ⊢
  rw [dif_pos hex] at hS ⊢
  have hspec := hex.choose_spec
  generalize hex.choose = p at hspec hS ⊢
  have hd : x' - x = p.2 • unitStep L m j p.1 := hspec.1
  unfold flowAlong at hS ⊢
  by_cases hn : 0 ≤ p.2
  · rw [if_pos hn] at hS ⊢
    rw [pathHolonomy_forwardFlow hg hU p.1 _ x hS, ← natCast_zsmul, Int.toNat_of_nonneg hn, ← hd,
      add_sub_cancel]
  · rw [if_neg hn] at hS ⊢
    have hneg : (((-p.2).toNat : ℕ) : ℤ) = -p.2 := Int.toNat_of_nonneg (by omega)
    rw [pathHolonomy_backwardFlow hg hU p.1 _ x hS, ← natCast_zsmul, hneg, neg_smul,
      sub_neg_eq_add, ← hd, add_sub_cancel]
private theorem eq_combTransport_of_isFlatOver (hComb : CombTransportOnBox.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {S : Set (SiteAtLevel L m K 0)}
    (hS : IsSiteBox (levelDepth K 0) S) {y : SiteAtLevel L m K 0} (hy : y ∈ S)
    {W : BondAtLevel L m K 0 → ComplexMatrix2} (hW : W ∈ gaugeFieldsAtLevel L m K 0)
    (hflat : IsFlatOver W S) :
    ∀ b : BondAtLevel L m K 0, b.LiesIn S →
      W b = (combTransport W y b.source)⁻¹ * combTransport W y b.target := by
  have hW' : IsGaugeField compactGaugeGroup univ W := hW
  have hg : ∀ z, combTransport W y z ∈ ComplexMatrix2.specialUnitary := fun z =>
    pathHolonomy_mem_su2 (fun b => hW'.1 b (mem_univ b)) _
  obtain ⟨r, hr⟩ := exists_coordCount_le (by have := hL.2; omega) S
  have hc := hComb L hL m K 0 hm (Nat.zero_le K) S r y W 0 hS hr hy
    ⟨fun b _ => hW'.1 b (mem_univ b), fun b _ => hW'.2 b (mem_univ b)⟩ le_rfl
    (fun p hp => by rw [hflat p hp]; simp)
  have hfwd : ∀ (x : SiteAtLevel L m K 0) (ν : Fin 4), (Bond.forwardFrom x ν).LiesIn S →
      W (Bond.forwardFrom x ν) =
        (combTransport W y x)⁻¹ * combTransport W y (x + unitStep L m (levelDepth K 0) ν) := by
    intro x ν hin
    have h0 : ComplexMatrix2.operatorNorm
        (gaugeTransform (combTransport W y) W (Bond.forwardFrom x ν) - 1) ≤ 0 := by
      simpa using (hc.2.1 x ν hin).1
    have h1 : gaugeTransform (combTransport W y) W (Bond.forwardFrom x ν) = 1 :=
      sub_eq_zero.mp (norm_le_zero_iff.mp h0)
    have h2 : combTransport W y x * W (Bond.forwardFrom x ν) *
        (combTransport W y (x + unitStep L m (levelDepth K 0) ν))⁻¹ = 1 := h1
    calc W (Bond.forwardFrom x ν)
        = (combTransport W y x)⁻¹ * (combTransport W y x * W (Bond.forwardFrom x ν) *
            (combTransport W y (x + unitStep L m (levelDepth K 0) ν))⁻¹) *
            combTransport W y (x + unitStep L m (levelDepth K 0) ν) := by
          rw [mul_assoc (combTransport W y x), ← mul_assoc (combTransport W y x)⁻¹,
            inv_mul_self_of_mem_su2 (hg x), one_mul, mul_assoc, inv_mul_self_of_mem_su2 (hg _),
            mul_one]
      _ = _ := by rw [h2, mul_one]
  intro b hb
  obtain ⟨μ, hμ | hμ⟩ := b.isNeighbour
  · have htarget : b.target = b.source + unitStep L m (levelDepth K 0) μ := by rw [← hμ]; abel
    have hbf : b = Bond.forwardFrom b.source μ := Bond.ext rfl htarget
    have hin : (Bond.forwardFrom b.source μ).LiesIn S := by rw [← hbf]; exact hb
    rw [htarget]
    conv_lhs => rw [hbf]
    exact hfwd _ _ hin
  · have hsource : b.source = b.target + unitStep L m (levelDepth K 0) μ := by
      have : unitStep L m (levelDepth K 0) μ = b.source - b.target := by
        rw [← neg_neg (unitStep L m (levelDepth K 0) μ), ← hμ]
        abel
      rw [this]
      abel
    have hbo : b = (Bond.forwardFrom b.target μ).opposite := Bond.ext hsource rfl
    have hin : (Bond.forwardFrom b.target μ).LiesIn S := ⟨hb.2, by
      change b.target + unitStep L m (levelDepth K 0) μ ∈ S
      rw [← hsource]
      exact hb.1⟩
    have hopp := hW'.2 (Bond.forwardFrom b.target μ) (mem_univ _)
    have hf := hfwd _ _ hin
    rw [← hsource] at hf
    conv_lhs => rw [hbo]
    rw [hopp, hf, Matrix.mul_inv_rev, inv_inv_of_mem_su2 (hg _)]
private theorem flatBoxHolonomyPathIndependent_of_comb (hComb : CombTransportOnBox.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) :
    FlatBoxHolonomyPathIndependent L m K := by
  intro S U hS hU hflat γ₁ γ₂ z z' h₁ h₂ i₁ i₂
  by_cases hne : S.Nonempty
  · obtain ⟨y, hy⟩ := hne
    obtain ⟨r, hr⟩ := exists_coordCount_le (by have := hL.2; omega) S
    have hc := hComb L hL m K 0 hm (Nat.zero_le K) S r y U 0 hS hr hy hU le_rfl
      (fun p hp => by rw [hflat p hp]; simp)
    have h0 : ComplexMatrix2.operatorNorm (pathHolonomy U γ₁ - pathHolonomy U γ₂) ≤ 0 := by
      simpa using hc.2.2.2 γ₁ γ₂ z z' h₁ h₂ i₁ i₂
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  · have he : ∀ γ : List (BondAtLevel L m K 0), (∀ b ∈ γ, b.LiesIn S) → γ = [] := by
      intro γ hγ
      cases γ with
      | nil => rfl
      | cons b t => exact absurd ⟨b.source, (hγ b (by simp)).1⟩ hne
    rw [he γ₁ i₁, he γ₂ i₂]
private theorem trivialGaugeField_mem_compactGaugeFields {j : ℤ} :
    (trivialGaugeField : Bond L m j → ComplexMatrix2) ∈ compactGaugeFields L m j :=
  ⟨fun _ _ => ComplexMatrix2.specialUnitary.one_mem, fun _ _ => by simp [trivialGaugeField]⟩
private theorem bareLiftFromLevel_trivialGaugeField (q : ℕ) :
    bareLiftFromLevel (K := K) (trivialGaugeField : BondAtLevel L m K q → ComplexMatrix2) =
      trivialGaugeField := by
  cases q with
  | zero => rfl
  | succ q =>
    funext b
    simp only [bareLiftFromLevel, bareLift, liftToFinerLevel]
    split_ifs <;> rfl
private theorem blockFieldTrivial_of_lift (hLift : LiftConsistentWithAverages)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K) {q : ℕ}
    (hq : q ≤ K) : BlockFieldTrivial L m K q := by
  have hV : (trivialGaugeField : BondAtLevel L m K q → ComplexMatrix2) ∈
      gaugeFieldsAtLevel L m K q :=
    trivialGaugeField_mem_compactGaugeFields
  have hVc : IsGaugeField compactGaugeGroup univ
      (trivialGaugeField : BondAtLevel L m K q → ComplexMatrix2) := hV
  obtain ⟨-, -, -, -, hR, hWh, -⟩ := hLift L m K hL hm hK q hq univ (fun _ _ => mem_univ _)
    trivialGaugeField (Or.inl hVc)
  have hval := ((hWh rfl hV).2 q le_rfl).2.2
  obtain ⟨-, -, hk, -⟩ := (hR hVc).1
  rw [bareLiftFromLevel_trivialGaugeField] at hval
  unfold BlockFieldTrivial
  rw [← hval]
  funext c
  exact hk.2 c (by rw [hk.1]; exact mem_univ c)
private theorem flatBlockAverageEqTransport_of_parts (hComb : CombTransportOnBox.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {q : ℕ}
    (hBox : BareBlockPairsAreSiteBoxes L m K q) (hLoc : PartialBareBlockFieldLocalCovariant L m K q)
    (hCov : BlockFieldGaugeCovariant L m K q) (hOne : BlockFieldTrivial L m K q) :
    FlatBlockAverageEqTransport L m K q := by
  intro c U hU hflat
  obtain ⟨hD, -, ⟨μ, n, hax⟩, hsites⟩ := hBox c
  have hx : c.source.toSublattice (levelDepth K 0) ∈
      (sitesIn (bareBlockPair c) : Set (SiteAtLevel L m K 0)) :=
    hsites _ (by simp [sitesOfPath])
  have hdef : IsDefinedOnBareBlockPair (bareBondsInBlockPair c) U c :=
    ⟨bondsAmong_isReversalClosed _, hU, subset_rfl⟩
  have hU₁ := bareBlockPairExtension_mem hdef
  have hagree : ∀ b : BondAtLevel L m K 0, b.LiesIn (sitesIn (bareBlockPair c)) →
      bareBlockPairExtension U c b = U b := fun b hb => if_pos hb
  have hflat₁ : IsFlatOver (bareBlockPairExtension U c) (sitesIn (bareBlockPair c)) :=
    (isFlatOver_congr hagree).mpr hflat
  have hU₁' : IsGaugeField compactGaugeGroup univ (bareBlockPairExtension U c) := hU₁
  have hg : ∀ z, combTransport (bareBlockPairExtension U c)
      (c.source.toSublattice (levelDepth K 0)) z ∈ ComplexMatrix2.specialUnitary :=
    fun z => pathHolonomy_mem_su2 (fun b => hU₁'.1 b (mem_univ b)) _
  have hpure := eq_combTransport_of_isFlatOver hComb hL hm hD hx hU₁ hflat₁
  generalize combTransport (bareBlockPairExtension U c)
    (c.source.toSublattice (levelDepth K 0)) = g at hg hpure
  have hpureU : ∀ b : BondAtLevel L m K 0, b.LiesIn (sitesIn (bareBlockPair c)) →
      U b = (g b.source)⁻¹ * g b.target := fun b hb => by rw [← hagree b hb, hpure b hb]
  have hgauge : IsGaugeMap compactGaugeGroup fun z => (g z)⁻¹ :=
    fun z => inv_mem_specialUnitary (hg z)
  have hval : ∀ b : BondAtLevel L m K 0,
      gaugeTransform (fun z => (g z)⁻¹) trivialGaugeField b = (g b.source)⁻¹ * g b.target := by
    intro b
    simp only [gaugeTransform, trivialGaugeField, mul_one, inv_inv_of_mem_su2 (hg _)]
  have hU' : gaugeTransform (fun z => (g z)⁻¹) trivialGaugeField ∈
      gaugeFieldsAtLevel L m K 0 := by
    refine ⟨fun b _ => ?_, fun b _ => ?_⟩
    · rw [hval]
      exact ComplexMatrix2.specialUnitary.mul_mem (inv_mem_specialUnitary (hg _)) (hg _)
    · rw [hval, hval, Matrix.mul_inv_rev, inv_inv_of_mem_su2 (hg _)]
      rfl
  have hloc := (hLoc c _ U hdef).1 _ hU' (fun b hb => by rw [hval, hpureU b hb])
  have hcov := congrFun (hCov trivialGaugeField trivialGaugeField_mem_compactGaugeFields _ hgauge) c
  unfold BlockFieldTrivial at hOne
  rw [hOne] at hcov
  rw [hloc, hcov, bareParallelTransport, bareAxialPath,
    pathHolonomy_axialPath hg hpureU hax hsites]
  simp only [gaugeTransform, restrictGaugeMap, trivialGaugeField, mul_one,
    inv_inv_of_mem_su2 (hg _)]
theorem flatFieldsAndTheirAverages_proof
    (hComb : CombTransportOnBox.Statement)
    (hLift : LiftConsistentWithAverages)
    (hFacts : GeometryAndLocalityOfBlockAverages.Statement)
    (hCov : BlockAverageLocalityAndCovariance) :
    FlatFieldsAndTheirAverages := by
  intro L m K hL hm hK
  obtain ⟨-, -, -, -, -, hBox, hLoc, -⟩ := hFacts L m K hL hm hK
  obtain ⟨-, -, hN⟩ := hCov L m K hL hm
  refine ⟨flatBoxHolonomyPathIndependent_of_comb hComb hL hm, fun q hq => ?_⟩
  have hOne := blockFieldTrivial_of_lift hLift hL hm hK hq
  exact ⟨hOne, flatBlockAverageEqTransport_of_parts hComb hL hm (hBox q hq) (hLoc q hq)
    (hN q hq).1 hOne⟩
end YangMills.Construction.PeriodicLattice
