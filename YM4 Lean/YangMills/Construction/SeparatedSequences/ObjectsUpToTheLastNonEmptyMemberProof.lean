import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
import YangMills.Construction.SeparatedSequences.ObjectsUpToTheLastNonEmptyMember
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.TorusMetric
namespace YangMills.Construction
namespace SeparatedClasses
namespace LastNonempty
theorem choose_eq_of_eq {α : Type*} {p q : α → Prop} (h : p = q) (hp : ∃ x, p x) (hq : ∃ x, q x) :
    hp.choose = hq.choose := by
  subst h
  rfl
theorem finsum_subtype_eq {ι : Type*} {A B : Set ι} (h : A = B) (g : ι → ℝ) :
    ∑ᶠ y : ↥A, g y = ∑ᶠ y : ↥B, g y := by
  subst h
  rfl
theorem adjoint_conj_eq {V ι : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {A B : Set ι} [FiniteDimensional ℝ (↥A → ℝ)] [FiniteDimensional ℝ (↥B → ℝ)] (h : A = B)
    (ip : V → V → ℝ) (ipA : (↥A → ℝ) → (↥A → ℝ) → ℝ) (ipB : (↥B → ℝ) → (↥B → ℝ) → ℝ)
    (QA : V →ₗ[ℝ] (↥A → ℝ)) (QB : V →ₗ[ℝ] (↥B → ℝ))
    (wA : (↥A → ℝ) →ₗ[ℝ] (↥A → ℝ)) (wB : (↥B → ℝ) →ₗ[ℝ] (↥B → ℝ))
    (hip : ∀ f g : ↥A → ℝ,
      ipA f g = ipB (fun y => f ⟨y.1, h ▸ y.2⟩) (fun y => g ⟨y.1, h ▸ y.2⟩))
    (hQ : ∀ v (y : ↥A), QA v y = QB v ⟨y.1, h ▸ y.2⟩)
    (hw : ∀ (f : ↥A → ℝ) (y : ↥A),
      wA f y = wB (fun z => f ⟨z.1, h ▸ z.2⟩) ⟨y.1, h ▸ y.2⟩) :
    FiniteDimReal.adjointFor ip ipA QA ∘ₗ wA ∘ₗ QA =
      FiniteDimReal.adjointFor ip ipB QB ∘ₗ wB ∘ₗ QB := by
  subst h
  obtain rfl : ipA = ipB := funext₂ hip
  obtain rfl : QA = QB := LinearMap.ext fun v => funext (hQ v)
  obtain rfl : wA = wB := LinearMap.ext fun f => funext (hw f)
  rfl
section Scales
variable {L m : ℕ} (S : SeparatedSequences.ScaleData) (Ω : ℕ → Set (FourTorus L m))
theorem truncatedMember_of_le {n : ℕ} (h : n ≤ S.top) :
    SeparatedSequences.truncatedMember S Ω n = Ω n := by
  unfold SeparatedSequences.truncatedMember
  rw [if_pos h]
theorem truncatedMember_of_gt {n : ℕ} (h : S.top < n) :
    SeparatedSequences.truncatedMember S Ω n = ∅ := by
  unfold SeparatedSequences.truncatedMember
  rw [if_neg (not_le.mpr h)]
theorem layerSet_of_lt {n : ℕ} (h : n < S.top) :
    SeparatedSequences.layerSet S Ω n = closure (Ω n \ Ω (n + 1)) := by
  unfold SeparatedSequences.layerSet
  rw [if_pos h]
theorem layerSet_top : SeparatedSequences.layerSet S Ω S.top = Ω S.top := by
  unfold SeparatedSequences.layerSet
  rw [if_neg (lt_irrefl _), if_pos rfl]
theorem layerSet_of_gt {n : ℕ} (h : S.top < n) : SeparatedSequences.layerSet S Ω n = ∅ := by
  unfold SeparatedSequences.layerSet
  rw [if_neg (by omega), if_neg (by omega)]
end Scales
theorem sitesIn_empty {L m : ℕ} {j : ℤ} : (sitesIn ∅ : Set (Site L m j)) = ∅ :=
  Set.ext fun _ => Iff.rfl
theorem bondsMeeting_empty {L m : ℕ} {j : ℤ} : (bondsMeeting ∅ : Set (Bond L m j)) = ∅ := by
  ext b
  simp [bondsMeeting]
theorem pathLengthIn_empty (S : ℝ) (Γ : List LiftedSegment) : pathLengthIn S Γ ∅ = 0 := by
  induction Γ with
  | nil => simp [pathLengthIn]
  | cons s Γ ih => simp [pathLengthIn]
section Class
variable {C : ClassData} {Ω : ℕ → Set C.Point} {T : ℕ}
theorem memberAt_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (n : ℕ) :
    C.memberAt Ω n = ClassData.truncMember Ω hT n := by
  by_cases h : n ≤ T
  · exact (truncatedMember_of_le C.scales Ω (h.trans hT)).trans
      (truncatedMember_of_le (ClassData.truncScales hT) Ω h).symm
  · refine Eq.trans ?_ (truncatedMember_of_gt (ClassData.truncScales hT) Ω (not_le.mp h)).symm
    by_cases h' : n ≤ C.t
    · exact (truncatedMember_of_le C.scales Ω h').trans (hE n (not_le.mp h))
    · exact truncatedMember_of_gt C.scales Ω (not_le.mp h')
theorem layerAt_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T)) (n : ℕ) :
    C.layerAt Ω n = ClassData.truncLayer Ω hT n := by
  rcases lt_trichotomy n T with h | h | h
  · exact (layerSet_of_lt C.scales Ω (h.trans_le hT)).trans
      (layerSet_of_lt (ClassData.truncScales hT) Ω h).symm
  · rw [h]
    have hb : ClassData.truncLayer Ω hT T = Ω T := layerSet_top (ClassData.truncScales hT) Ω
    rw [hb]
    rcases hT.lt_or_eq with h' | h'
    · refine (layerSet_of_lt C.scales Ω h').trans ?_
      rw [hE (T + 1) (Nat.lt_succ_self T), sdiff_empty, hC.closure_eq]
    · rw [h']
      exact layerSet_top C.scales Ω
  · have hb : ClassData.truncLayer Ω hT n = ∅ := layerSet_of_gt (ClassData.truncScales hT) Ω h
    rw [hb]
    rcases lt_trichotomy n C.t with a | a | a
    · refine (layerSet_of_lt C.scales Ω a).trans ?_
      rw [hE n h, empty_sdiff, closure_empty]
    · have hlt : T < C.t := by omega
      rw [a]
      exact (layerSet_top C.scales Ω).trans (hE C.t hlt)
    · exact layerSet_of_gt C.scales Ω a
theorem layerAt_eq_empty (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T))
    {n : ℕ} (h : T < n) : C.layerAt Ω n = ∅ :=
  (layerAt_eq hT hE hC n).trans (layerSet_of_gt (ClassData.truncScales hT) Ω h)
theorem annulusSites_of_le (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) {j : ℕ} (hj : j ≤ T) :
    annulusSites C.cutoff C.t Ω j = annulusSites C.cutoff T Ω j := by
  rcases hj.lt_or_eq with h | h
  · unfold annulusSites
    rw [if_pos h, if_pos (h.trans_le hT)]
  · rw [h]
    rcases hT.lt_or_eq with h' | h'
    · unfold annulusSites
      rw [if_pos h', if_neg (lt_irrefl _), hE (T + 1) (Nat.lt_succ_self T), sdiff_empty]
    · rw [h']
theorem annulusSites_of_gt (hE : ∀ n, T < n → Ω n = ∅) {j : ℕ} (hj : T < j) (hjt : j ≤ C.t) :
    annulusSites C.cutoff C.t Ω j = ∅ := by
  rcases hjt.lt_or_eq with h | h
  · unfold annulusSites
    rw [if_pos h, hE j hj, empty_sdiff]
    exact sitesIn_empty
  · rw [h]
    have e : Ω C.t = ∅ := hE _ (h ▸ hj)
    unfold annulusSites
    rw [if_neg (lt_irrefl _), e]
    exact sitesIn_empty
theorem determiningBondsAt_of_le (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) {j : ℕ} (hj : j ≤ T) :
    determiningBondsAt C.cutoff C.t Ω j = determiningBondsAt C.cutoff T Ω j := by
  unfold determiningBondsAt
  rw [annulusSites_of_le hT hE hj]
theorem determiningBondsAt_of_gt (hE : ∀ n, T < n → Ω n = ∅) {j : ℕ} (hj : T < j)
    (hjt : j ≤ C.t) : determiningBondsAt C.cutoff C.t Ω j = ∅ := by
  unfold determiningBondsAt
  rw [annulusSites_of_gt hE hj hjt]
  ext b
  simp
theorem determiningBondSet_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) :
    determiningBondSet C.cutoff C.t Ω = determiningBondSet C.cutoff T Ω := by
  ext ⟨j, b⟩
  constructor
  · rintro ⟨hj, hb⟩
    have hb' : b ∈ determiningBondsAt C.cutoff C.t Ω j := hb
    by_cases h : j ≤ T
    · rw [determiningBondsAt_of_le hT hE h] at hb'
      exact ⟨h, hb'⟩
    · rw [determiningBondsAt_of_gt hE (not_le.mp h) hj] at hb'
      exact hb'.elim
  · rintro ⟨hj, hb⟩
    have hb' : b ∈ determiningBondsAt C.cutoff T Ω j := hb
    have hj' : j ≤ T := hj
    rw [← determiningBondsAt_of_le hT hE hj'] at hb'
    exact ⟨hj'.trans hT, hb'⟩
theorem isInward_iff (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) {j : ℕ} (hj : j ≤ T)
    (b : C.LatticeBond j) :
    IsInwardPointingBond C.cutoff C.t Ω j b ↔ IsInwardPointingBond C.cutoff T Ω j b := by
  unfold IsInwardPointingBond
  rw [determiningBondsAt_of_le hT hE hj]
  constructor
  · rintro ⟨-, h2, h3⟩
    refine ⟨?_, h2, h3⟩
    by_contra h
    rw [hE (j + 1) (by omega), bondsMeeting_empty] at h3
    exact h3
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.trans_le hT, h2, h3⟩
theorem activeBonds_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) :
    C.activeBonds Ω = activeBondSet C.cutoff T Ω := by
  ext ⟨j, b⟩
  change ((⟨j, b⟩ : Σ n : ℕ, C.LatticeBond n) ∈ determiningBondSet C.cutoff C.t Ω ∧
      ¬IsInwardPointingBond C.cutoff C.t Ω j b) ↔
    ((⟨j, b⟩ : Σ n : ℕ, C.LatticeBond n) ∈ determiningBondSet C.cutoff T Ω ∧
      ¬IsInwardPointingBond C.cutoff T Ω j b)
  rw [determiningBondSet_eq hT hE]
  exact and_congr_right fun h => not_congr (isInward_iff hT hE h.1 b)
theorem layerSitesAt_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T))
    (n : ℕ) : C.layerSitesAt Ω n = ClassData.truncLayerSites Ω hT n := by
  change sitesIn (C.layerAt Ω n) = sitesIn (ClassData.truncLayer Ω hT n)
  rw [layerAt_eq hT hE hC n]
theorem truncLayerSites_of_gt (hT : T ≤ C.t) {n : ℕ} (h : T < n) :
    ClassData.truncLayerSites Ω hT n = ∅ := by
  change sitesIn (ClassData.truncLayer Ω hT n) = ∅
  have hb : ClassData.truncLayer Ω hT n = ∅ := layerSet_of_gt (ClassData.truncScales hT) Ω h
  rw [hb]
  exact sitesIn_empty
theorem mem_layerSitesAt_iff (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T))
    (n : ℕ) (y : C.LatticeSite n) :
    (n ≤ C.t ∧ y ∈ C.layerSitesAt Ω n) ↔ (n ≤ T ∧ y ∈ ClassData.truncLayerSites Ω hT n) := by
  rw [layerSitesAt_eq hT hE hC n]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨?_, h⟩
    by_contra hn
    rw [truncLayerSites_of_gt hT (not_le.mp hn)] at h
    exact h
  · rintro ⟨h1, h2⟩
    exact ⟨h1.trans hT, h2⟩
theorem layerPts_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T)) :
    C.layerPts Ω = SeparatedSequences.layerPoints (ClassData.truncScales hT) Ω := by
  ext y
  constructor
  · intro h
    obtain ⟨n, hn, z, hz, rfl⟩ := mem_iUnion₂.mp h
    obtain ⟨h1, h2⟩ := (mem_layerSitesAt_iff hT hE hC n z).mp ⟨hn, hz⟩
    exact mem_iUnion₂.mpr ⟨n, h1, z, h2, rfl⟩
  · intro h
    obtain ⟨n, hn, z, hz, rfl⟩ := mem_iUnion₂.mp h
    obtain ⟨h1, h2⟩ := (mem_layerSitesAt_iff hT hE hC n z).mpr ⟨hn, hz⟩
    exact mem_iUnion₂.mpr ⟨n, h1, z, h2, rfl⟩
theorem apexes_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T)) :
    {y : Σ n : ℕ, C.LatticeSite n | y.1 ≤ C.t ∧ y.2 ∈ C.layerSitesAt Ω y.1} =
      ClassData.truncApexes Ω hT :=
  Set.ext fun y => mem_layerSitesAt_iff hT hE hC y.1 y.2
theorem chainLength_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T))
    (Γ : List LiftedSegment) : C.chainLength Ω Γ = ClassData.truncChainLength Ω hT Γ := by
  have hsum : ∑ n ∈ Finset.Icc 1 C.t, (C.coarseMesh n)⁻¹ *
        C.toLevelUnits (pathLengthIn (torusSide C.L C.m) Γ (C.layerAt Ω n)) =
      ∑ n ∈ Finset.Icc 1 T, (C.coarseMesh n)⁻¹ *
        C.toLevelUnits (pathLengthIn (torusSide C.L C.m) Γ (ClassData.truncLayer Ω hT n)) := by
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hT) ?_).symm.trans
      (Finset.sum_congr rfl fun n _ => ?_)
    · intro n hn hn'
      have hlt : T < n := by
        rw [Finset.mem_Icc] at hn hn'
        omega
      rw [layerAt_eq_empty hT hE hC hlt, pathLengthIn_empty]
      simp [Conventions.LeveledParameters.toLevelUnits, PeriodicLattice.toLevelUnits]
    · rw [layerAt_eq hT hE hC n]
  change ∑ n ∈ Finset.Icc 1 C.t, (C.coarseMesh n)⁻¹ *
        C.toLevelUnits (pathLengthIn (torusSide C.L C.m) Γ (C.layerAt Ω n)) +
      (C.coarseMesh 0)⁻¹ * C.toLevelUnits (pathLengthIn (torusSide C.L C.m) Γ (C.memberAt Ω 1)ᶜ) = _
  rw [hsum, memberAt_eq hT hE 1]
  rfl
theorem chainDist_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T))
    (y y' : C.Point) : C.chainDist Ω y y' = ClassData.truncChainDist Ω hT y y' := by
  unfold ClassData.chainDist SeparatedSequences.layerWeightedDist ClassData.truncChainDist
  exact iInf_congr fun Γ => iInf_congr fun _ =>
    congrArg ENNReal.ofReal (chainLength_eq hT hE hC Γ)
theorem siteLayerSup_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T))
    (γ : ℝ) (f : C.SiteFn) :
    C.siteLayerSup Ω γ f = ClassData.truncSiteLayerSup Ω hT γ f := by
  unfold ClassData.siteLayerSup ClassData.truncSiteLayerSup
  refine congrArg sSup (Set.ext fun r => ?_)
  constructor
  · rintro ⟨n, -, x, hx, hr⟩
    have hnT : n ≤ T := by
      by_contra h
      rw [layerAt_eq_empty hT hE hC (not_le.mp h)] at hx
      exact hx
    rw [layerAt_eq hT hE hC n] at hx
    exact ⟨n, hnT, x, hx, hr⟩
  · rintro ⟨n, hn, x, hx, hr⟩
    rw [← layerAt_eq hT hE hC n] at hx
    exact ⟨n, hn.trans hT, x, hx, hr⟩
theorem bondLayerSup_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T))
    (γ : ℝ) (f : C.BondFn) :
    C.bondLayerSup Ω γ f = ClassData.truncBondLayerSup Ω hT γ f := by
  unfold ClassData.bondLayerSup ClassData.truncBondLayerSup
  refine congrArg sSup (Set.ext fun r => ?_)
  constructor
  · rintro ⟨n, -, x, hx, hr⟩
    have hnT : n ≤ T := by
      by_contra h
      rw [layerAt_eq_empty hT hE hC (not_le.mp h)] at hx
      exact hx
    rw [layerAt_eq hT hE hC n] at hx
    exact ⟨n, hnT, x, hx, hr⟩
  · rintro ⟨n, hn, x, hx, hr⟩
    rw [← layerAt_eq hT hE hC n] at hx
    exact ⟨n, hn.trans hT, x, hx, hr⟩
theorem layerBonds_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T))
    (j : ℕ) : C.layerBonds Ω j = ClassData.truncLayerBonds Ω hT j := by
  unfold ClassData.layerBonds ClassData.truncLayerBonds
  rw [layerSitesAt_eq hT hE hC j, memberAt_eq hT hE (j + 1)]
theorem layerBonds_of_gt (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T))
    {j : ℕ} (hj : T < j) : C.layerBonds Ω j = ∅ := by
  rw [layerBonds_eq hT hE hC j]
  unfold ClassData.truncLayerBonds
  rw [truncLayerSites_of_gt hT hj]
  ext c
  simp
theorem expansionSetAt_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T))
    (φ : BondFrame) (j : ℕ) : C.expansionSetAt Ω φ j = ClassData.truncatedBondSetAt Ω hT φ j := by
  cases j with
  | zero =>
    simp only [ClassData.expansionSetAt, ClassData.truncatedBondSetAt]
    rw [memberAt_eq hT hE 1]
  | succ j =>
    simp only [ClassData.expansionSetAt, ClassData.truncatedBondSetAt]
    rw [layerBonds_eq hT hE hC (j + 1)]
theorem expansionSetAt_of_gt (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T))
    (φ : BondFrame) {n : ℕ} (hn : T < n) : C.expansionSetAt Ω φ n = ∅ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  simp only [ClassData.expansionSetAt, Nat.succ_eq_add_one]
  rw [layerBonds_of_gt hT hE hC hn]
  ext c
  simp
theorem expansionSet_eq (hT : T ≤ C.t) (hE : ∀ n, T < n → Ω n = ∅) (hC : IsClosed (Ω T))
    (φ : BondFrame) : C.expansionSet Ω φ = ClassData.truncatedBondSet Ω hT φ := by
  ext ⟨j, c⟩
  constructor
  · rintro ⟨-, h⟩
    have h' : c ∈ C.expansionSetAt Ω φ j := h
    have hj : j ≤ T := by
      by_contra hn
      rw [expansionSetAt_of_gt hT hE hC φ (not_le.mp hn)] at h'
      exact h'
    rw [expansionSetAt_eq hT hE hC φ j] at h'
    exact ⟨hj, h'⟩
  · rintro ⟨hj, h⟩
    have h' : c ∈ ClassData.truncatedBondSetAt Ω hT φ j := h
    rw [← expansionSetAt_eq hT hE hC φ j] at h'
    exact ⟨le_trans hj hT, h'⟩
end Class
section Base
variable (D : SeparatedSequences.BaseParameters) {T : ℕ} (hT : T ≤ D.t) (Ω : ℕ → Set D.Torus)
theorem base_mem_layerSites_iff (hLS : ∀ n, D.layerSites Ω n = D.truncLayerSites hT Ω n)
    (hHigh : ∀ n, T < n → D.truncLayerSites hT Ω n = ∅) (n : ℕ) (z : D.LatticeSite n) :
    (n ≤ D.t ∧ z ∈ D.layerSites Ω n) ↔ (n ≤ T ∧ z ∈ D.truncLayerSites hT Ω n) := by
  rw [hLS n]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨?_, h⟩
    by_contra hn
    rw [hHigh n (not_le.mp hn)] at h
    exact h
  · rintro ⟨h1, h2⟩
    exact ⟨h1.trans hT, h2⟩
theorem allLayerPoints_eq (hLS : ∀ n, D.layerSites Ω n = D.truncLayerSites hT Ω n)
    (hHigh : ∀ n, T < n → D.truncLayerSites hT Ω n = ∅) :
    D.allLayerPoints Ω = D.truncLayerPoints hT Ω := by
  ext y
  constructor
  · intro h
    obtain ⟨n, hn, z, hz, rfl⟩ := mem_iUnion₂.mp h
    obtain ⟨h1, h2⟩ := (base_mem_layerSites_iff D hT Ω hLS hHigh n z).mp ⟨hn, hz⟩
    exact mem_iUnion₂.mpr ⟨n, h1, z, h2, rfl⟩
  · intro h
    obtain ⟨n, hn, z, hz, rfl⟩ := mem_iUnion₂.mp h
    obtain ⟨h1, h2⟩ := (base_mem_layerSites_iff D hT Ω hLS hHigh n z).mpr ⟨hn, hz⟩
    exact mem_iUnion₂.mpr ⟨n, h1, z, h2, rfl⟩
theorem levelSite_eq (hLS : ∀ n, D.layerSites Ω n = D.truncLayerSites hT Ω n)
    (hHigh : ∀ n, T < n → D.truncLayerSites hT Ω n = ∅) (y : ↥(D.allLayerPoints Ω))
    (y' : ↥(D.truncLayerPoints hT Ω)) (h : y.1 = y'.1) :
    D.levelSite Ω y = D.truncLevelSite hT Ω y' := by
  change (D.exists_levelSite Ω y).choose = (D.exists_truncLevelSite hT Ω y').choose
  refine choose_eq_of_eq ?_ _ _
  funext p
  apply propext
  rw [← and_assoc, ← and_assoc, base_mem_layerSites_iff D hT Ω hLS hHigh p.1 p.2, h]
theorem averageZero_eq (hLS : ∀ n, D.layerSites Ω n = D.truncLayerSites hT Ω n)
    (hHigh : ∀ n, T < n → D.truncLayerSites hT Ω n = ∅) (f : ↥(zeroFormsOn D.K (Ω 0)))
    (y : ↥(D.allLayerPoints Ω)) (y' : ↥(D.truncLayerPoints hT Ω)) (h : y.1 = y'.1) :
    D.averageZero Ω f y = D.truncBlockAverage hT Ω f y' := by
  change D.blockAverageZero (D.levelSite Ω y).1 f.1 (D.levelSite Ω y).2 =
    D.blockAverageZero (D.truncLevelSite hT Ω y').1 f.1 (D.truncLevelSite hT Ω y').2
  rw [levelSite_eq D hT Ω hLS hHigh y y' h]
theorem coarseZeroInner_eq (hLS : ∀ n, D.layerSites Ω n = D.truncLayerSites hT Ω n)
    (hHigh : ∀ n, T < n → D.truncLayerSites hT Ω n = ∅)
    (hall : D.allLayerPoints Ω = D.truncLayerPoints hT Ω) (ω ω' : D.CoarseZeroForms Ω) :
    D.coarseZeroInner Ω ω ω' = D.truncCoarseInner hT Ω
      (fun y => ω ⟨y.1, hall.symm.subset y.2⟩) (fun y => ω' ⟨y.1, hall.symm.subset y.2⟩) := by
  have hv : ∀ (w : D.CoarseZeroForms Ω) (p : D.Torus),
      SeparatedSequences.BaseParameters.pointValue w p =
        extendZero (D.truncLayerPoints hT Ω) (fun y => w ⟨y.1, hall.symm.subset y.2⟩) p := by
    intro w p
    unfold SeparatedSequences.BaseParameters.pointValue extendZero
    by_cases h : p ∈ D.allLayerPoints Ω
    · rw [dif_pos h, dif_pos (hall.subset h)]
    · rw [dif_neg h, dif_neg fun h' => h (hall.symm.subset h')]
  unfold SeparatedSequences.BaseParameters.coarseZeroInner
    SeparatedSequences.BaseParameters.truncCoarseInner
  refine Eq.trans (Finset.sum_subset (fun n hn => ?_) fun n _ hn => ?_).symm
    (Finset.sum_congr rfl fun n _ => ?_)
  · exact Finset.mem_range.2 (by have := Finset.mem_range.1 hn; omega)
  · have hlt : T < n := by
      rw [Finset.mem_range] at hn
      omega
    have e : D.layerSites Ω n = ∅ := (hLS n).trans (hHigh n hlt)
    have : IsEmpty ↥(D.layerSites Ω n) := by
      rw [e]
      exact Set.isEmpty_coe_sort.2 rfl
    rw [finsum_of_isEmpty, mul_zero]
  · congr 1
    refine (finsum_subtype_eq (hLS n) fun z : D.LatticeSite n =>
      SeparatedSequences.BaseParameters.pointValue ω (z : D.Torus) *
        SeparatedSequences.BaseParameters.pointValue ω' (z : D.Torus)).trans
      (finsum_congr fun y => ?_)
    rw [hv ω, hv ω']
theorem weightMulZero_eq (hLS : ∀ n, D.layerSites Ω n = D.truncLayerSites hT Ω n)
    (hHigh : ∀ n, T < n → D.truncLayerSites hT Ω n = ∅)
    (hall : D.allLayerPoints Ω = D.truncLayerPoints hT Ω) (w : D.CoarseZeroForms Ω)
    (y : ↥(D.allLayerPoints Ω)) :
    D.weightMulZero Ω w y = D.truncWeightMul hT Ω
      (fun z => w ⟨z.1, hall.symm.subset z.2⟩) ⟨y.1, hall.subset y.2⟩ := by
  change D.levelWeight (D.levelSite Ω y).1 * (D.levelMeshRatio (D.levelSite Ω y).1 ^ 2)⁻¹ * w y =
    D.levelWeight (D.truncLevelSite hT Ω ⟨y.1, hall.subset y.2⟩).1 *
      (D.levelMeshRatio (D.truncLevelSite hT Ω ⟨y.1, hall.subset y.2⟩).1 ^ 2)⁻¹ * w y
  rw [levelSite_eq D hT Ω hLS hHigh y ⟨y.1, hall.subset y.2⟩ rfl]
theorem zeroGreen_eq (hLS : ∀ n, D.layerSites Ω n = D.truncLayerSites hT Ω n)
    (hHigh : ∀ n, T < n → D.truncLayerSites hT Ω n = ∅) :
    D.zeroGreen Ω = D.truncZeroGreen hT Ω := by
  have hall := allLayerPoints_eq D hT Ω hLS hHigh
  have hform : D.weightedAverageZero Ω =
      D.truncBlockAverageAdjoint hT Ω ∘ₗ D.truncWeightMul hT Ω ∘ₗ
        D.truncBlockAverage hT Ω :=
    adjoint_conj_eq hall (D.restrictedZeroInner Ω) (D.coarseZeroInner Ω)
      (D.truncCoarseInner hT Ω) (D.averageZero Ω) (D.truncBlockAverage hT Ω)
      (D.weightMulZero Ω) (D.truncWeightMul hT Ω)
      (coarseZeroInner_eq D hT Ω hLS hHigh hall)
      (fun f y => averageZero_eq D hT Ω hLS hHigh f y _ rfl)
      (weightMulZero_eq D hT Ω hLS hHigh hall)
  unfold SeparatedSequences.BaseParameters.zeroGreen SeparatedSequences.BaseParameters.truncZeroGreen
    SeparatedSequences.BaseParameters.massiveZeroOperator
  rw [hform]
end Base
end LastNonempty
end SeparatedClasses
end YangMills.Construction
