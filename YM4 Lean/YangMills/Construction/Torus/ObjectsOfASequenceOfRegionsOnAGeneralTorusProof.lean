import YangMills.Construction.SeparatedSequences.NumbersOfThePropagatorServeOnTheToriProof
import YangMills.Construction.Torus.LayersCellsBlocksAndTheDistanceProof
import YangMills.Construction.Torus.PartitionsAndLatticesOfATorusProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.GeneralTorus.RegionObjects
section Forms
variable {V U : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup U] [Module ℝ U]
structure IsPosSymmBilin (p : V → V → ℝ) : Prop where
  add_left : ∀ u v w, p (u + v) w = p u w + p v w
  smul_left : ∀ (r : ℝ) u v, p (r • u) v = r * p u v
  symm : ∀ u v, p u v = p v u
  pos : ∀ v, v ≠ 0 → 0 < p v v
namespace IsPosSymmBilin
variable {p : V → V → ℝ} (hp : IsPosSymmBilin p)
include hp
theorem add_right (u v w : V) : p u (v + w) = p u v + p u w := by
  rw [hp.symm, hp.add_left, hp.symm v, hp.symm w]
theorem smul_right (r : ℝ) (u v : V) : p u (r • v) = r * p u v := by
  rw [hp.symm, hp.smul_left, hp.symm v]
theorem sub_left (u v w : V) : p (u - v) w = p u w - p v w := by
  have h1 := hp.add_left (u - v) v w
  rw [sub_add_cancel] at h1
  linarith
theorem sub_right (u v w : V) : p u (v - w) = p u v - p u w := by
  rw [hp.symm, hp.sub_left, hp.symm v, hp.symm w]
theorem eq_zero_of_self (v : V) (h : p v v = 0) : v = 0 := by
  by_contra hv
  exact (hp.pos v hv).ne' h
theorem restrict (E : Submodule ℝ V) : IsPosSymmBilin (fun a b : ↥E => p a b) where
  add_left u v w := by simpa using hp.add_left u v w
  smul_left r u v := by simpa using hp.smul_left r u v
  symm u v := hp.symm u v
  pos v hv := hp.pos v (by simpa using hv)
end IsPosSymmBilin
end Forms
section Choices
theorem orthProjValue_eq {V : Type} [Nonempty V] [Sub V] {Y : Set V} {p : V → V → ℝ} {f r : V}
    (hr : r ∈ Y) (h : ∀ w ∈ Y, p (f - r) w = 0)
    (uniq : ∀ r' ∈ Y, (∀ w ∈ Y, p (f - r') w = 0) → r' = r) :
    RegionSequence.orthProjValue Y p f = r := by
  have hs : ∃ r, r ∈ Y ∧ ∀ w ∈ Y, p (f - r) w = 0 := ⟨r, hr, h⟩
  have := Classical.epsilon_spec hs
  exact uniq _ this.1 this.2
end Choices
section Scales
variable (D : ScaleData)
theorem one_lt_blockFactor : (1 : ℝ) < D.L := by
  have := D.blocking.thirteen_le
  exact_mod_cast (by omega : 1 < D.L)
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem isEvenMultipleOf_levelSpacing {n : ℕ} (h : n ≤ D.lastLevel) :
    IsEvenMultipleOf D.torusSide (D.levelSpacing n) := by
  obtain ⟨k, hk, hS⟩ := D.torusSide_evenMultiple
  have hL : 0 < D.L := by have := D.blocking.thirteen_le; omega
  refine ⟨k * D.L ^ (D.lastLevel - n), Nat.mul_pos hk (pow_pos hL _), ?_⟩
  have hp : (D.L : ℝ) ^ D.lastLevel = (D.L : ℝ) ^ (D.lastLevel - n) * (D.L : ℝ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel h]
  rw [hS, ScaleData.levelSpacing, hp]
  push_cast
  ring
theorem levelSpacing_lt_torusSide {n : ℕ} (h : n ≤ D.lastLevel) :
    D.levelSpacing n < D.torusSide := by
  obtain ⟨k, hk, hS⟩ := isEvenMultipleOf_levelSpacing D h
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 := levelSpacing_pos D n
  rw [hS]
  nlinarith
theorem finite_latticeBond {S σ : ℝ} [Finite (LatticeSite S σ)] : Finite (LatticeBond S σ) :=
  Finite.of_injective (fun b : LatticeBond S σ => (b.src, b.tgt)) fun a b h => by
    have h' := Prod.ext_iff.1 h
    exact LatticeBond.ext h'.1 h'.2
theorem finite_latticePlaquette {S σ : ℝ} [Finite (LatticeSite S σ)] :
    Finite (LatticePlaquette S σ) :=
  Finite.of_injective (fun b : LatticePlaquette S σ => (b.basePoint, b.dir₁, b.dir₂))
    fun a b h => by
    have h' := Prod.ext_iff.1 h
    have h'' := Prod.ext_iff.1 h'.2
    exact LatticePlaquette.ext h'.1 h''.1 h''.2
theorem finite_posBond {n : ℕ} (h : n ≤ D.lastLevel) : Finite (D.PosBond n) :=
  have : Finite (D.SiteAt n) := finite_latticeSite (isEvenMultipleOf_levelSpacing D h)
  have : Finite (D.BondAt n) := finite_latticeBond
  Subtype.finite
instance : Finite D.BaseBond := finite_posBond D (Nat.zero_le _)
instance : Finite D.BasePlaquette := finite_latticePlaquette
theorem unitStep_injective {n : ℕ} (hn : n ≤ D.lastLevel) {μ ν : Fin 4}
    (h : unitStep D.torusSide (D.levelSpacing n) μ = unitStep D.torusSide (D.levelSpacing n) ν) :
    μ = ν := by
  by_contra hne
  have h1 : coordPoint D.torusSide μ (D.levelSpacing n) μ =
      coordPoint D.torusSide ν (D.levelSpacing n) μ :=
    congrFun (congrArg Subtype.val h) μ
  simp only [coordPoint, TorusMetric.torusProj, Pi.single_eq_same, Pi.single_eq_of_ne hne,
    AddCircle.coe_zero] at h1
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff D.torusSide).1 h1
  have hs := levelSpacing_pos D n
  have hl := levelSpacing_lt_torusSide D hn
  rw [zsmul_eq_mul] at hk
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
    nlinarith
  · rw [hk0] at hk
    simp at hk
    linarith
  · have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    nlinarith
variable {D}
theorem posBondDir_bondFrom {n : ℕ} (hn : n ≤ D.lastLevel) (x : D.SiteAt n) (μ : Fin 4) :
    ScaleData.posBondDir (ScaleData.bondFrom x μ) = μ := by
  have h := (ScaleData.bondFrom x μ).2.choose_spec
  have h' : unitStep D.torusSide (D.levelSpacing n) μ =
      unitStep D.torusSide (D.levelSpacing n) (ScaleData.posBondDir (ScaleData.bondFrom x μ)) := by
    have : (ScaleData.bondFrom x μ).1.tgt - (ScaleData.bondFrom x μ).1.src =
        unitStep D.torusSide (D.levelSpacing n) μ := by
      simp [ScaleData.bondFrom, LatticeBond.plus]
    rw [← this]
    exact h
  exact (unitStep_injective D hn h').symm
end Scales
section Transfer
theorem siteCast_bijective {S σ σ' : ℝ} (h : σ = σ') :
    Function.Bijective (siteCast (S := S) h) := by
  subst h
  refine ⟨fun a b hab => Subtype.ext (congrArg (fun z : LatticeSite S σ => z.1) hab), fun y => ?_⟩
  obtain ⟨k, hk⟩ := y.2
  refine ⟨⟨y.1, k, ?_⟩, Subtype.ext rfl⟩
  rw [hk]
  funext μ
  simp only [Torus.torusProj, TorusMetric.torusProj, mul_comm]
variable (D : ScaleData)
theorem bondFrom_comp_bijective {n : ℕ} (hn : n ≤ D.lastLevel) {σ : ℝ}
    (h : σ = D.levelSpacing n) :
    Function.Bijective fun c : Dirichlet.LatticeBond 4 D.torusSide σ =>
      (ScaleData.bondFrom (D := D) (n := n) (siteCast h c.source) c.dir) := by
  have hb := siteCast_bijective (S := D.torusSide) h
  constructor
  · rintro ⟨x, μ⟩ ⟨x', μ'⟩ hab
    have h1 : siteCast h x = siteCast h x' :=
      congrArg (fun c : D.PosBond n => c.1.src) hab
    have h2 : siteCast h x + unitStep D.torusSide (D.levelSpacing n) μ =
        siteCast h x' + unitStep D.torusSide (D.levelSpacing n) μ' :=
      congrArg (fun c : D.PosBond n => c.1.tgt) hab
    rw [h1] at h2
    have h3 := unitStep_injective D hn (add_left_cancel h2)
    have h4 := hb.1 h1
    subst h3 h4
    rfl
  · rintro ⟨c, μ, hμ⟩
    obtain ⟨x, hx⟩ := hb.2 c.src
    refine ⟨⟨x, μ⟩, Subtype.ext (LatticeBond.ext hx ?_)⟩
    change siteCast h x + unitStep D.torusSide (D.levelSpacing n) μ = c.tgt
    rw [hx, ← hμ]
    abel
theorem toBaseSite_bijective : Function.Bijective (toBaseSite D) :=
  siteCast_bijective (levelSpacing_zero D).symm
theorem toBaseBond_bijective : Function.Bijective (toBaseBond D) :=
  bondFrom_comp_bijective D (Nat.zero_le _) _
theorem toBasePlaquette_bijective : Function.Bijective (toBasePlaquette D) := by
  have hb := toBaseSite_bijective D
  constructor
  · rintro ⟨x, ⟨⟨a, b⟩, hab⟩⟩ ⟨x', ⟨⟨a', b'⟩, hab'⟩⟩ h
    have h1 : toBaseSite D x = toBaseSite D x' := congrArg LatticePlaquette.basePoint h
    have h2 : a = a' := congrArg LatticePlaquette.dir₁ h
    have h3 : b = b' := congrArg LatticePlaquette.dir₂ h
    have h4 := hb.1 h1
    subst h2 h3 h4
    rfl
  · rintro ⟨x, a, b, hab⟩
    obtain ⟨y, rfl⟩ := hb.2 x
    exact ⟨⟨y, ⟨⟨a, b⟩, hab⟩⟩, rfl⟩
instance instFiniteDirichletBaseSite :
    Finite (Dirichlet.LatticeSite 4 D.torusSide D.baseSpacing) :=
  Finite.of_injective _ (toBaseSite_bijective D).1
instance instFiniteDirichletBaseBond :
    Finite (Dirichlet.LatticeBond 4 D.torusSide D.baseSpacing) :=
  Finite.of_injective _ (toBaseBond_bijective D).1
end Transfer
section Cubes
variable {S : ℝ}
theorem cubeAt_eq_supCube (y : Torus4 S) (σ : ℝ) :
    Torus.cubeAt y σ = supCube σ y := by apply _root_.YangMills.Construction.GeneralTorus.GreenBounds.FromPropagator.cubeAt_eq_supCube <;> assumption
theorem isClosed_supCube (s : ℝ) (y : Torus4 S) : IsClosed (supCube s y) := by apply _root_.YangMills.Construction.GeneralTorus.CubePartitions.isClosed_supCube <;> assumption
theorem mem_spacingLattice_iff {σ σ' : ℝ} (h : σ = σ') (y : Torus4 S) :
    y ∈ Torus.spacingLattice 4 S σ ↔ y ∈ spacingLattice S σ' := by
  subst h
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, funext fun μ => ?_⟩
    simp only [Torus.torusProj, TorusMetric.torusProj, mul_comm]
  · rintro ⟨k, rfl⟩
    refine ⟨k, funext fun μ => ?_⟩
    simp only [Torus.torusProj, TorusMetric.torusProj, mul_comm]
end Cubes
section Shells
variable {D : ScaleData} (B : SeparatedChain D)
theorem isClosed_set_lastLevel (hc : SeparatedChainStructure) :
    IsClosed (B.set D.lastLevel) := by
  obtain ⟨C, hC, hX⟩ := ((hc D B).1 D.lastLevel D.lastLevel le_rfl le_rfl).2.1
  rw [hX, sUnion_eq_biUnion]
  have := finite_latticeSite (isEvenMultipleOf_levelSpacing D (le_refl D.lastLevel))
  have hfin : (D.cubePartition (D.levelSpacing D.lastLevel)).Finite := by
    have h1 : ((fun y : D.SiteAt D.lastLevel => supCube (D.levelSpacing D.lastLevel) (y : D.Space)) ''
        univ).Finite := (toFinite _).image _
    refine h1.subset ?_
    rintro Q ⟨-, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, mem_univ _, rfl⟩
  refine (hfin.subset hC).isClosed_biUnion fun Q hQ => ?_
  obtain ⟨-, y, -, rfl⟩ := hC hQ
  exact isClosed_supCube _ _
theorem shell_eq (hc : SeparatedChainStructure) (n : ℕ) :
    Torus.shell B.set n = B.shell n := by
  unfold Torus.shell SeparatedChain.shell
  split_ifs with h1 h2
  · rfl
  · subst h2
    rw [B.eq_empty_of_gt (D.lastLevel + 1) (by omega), sdiff_empty]
    exact (isClosed_set_lastLevel B hc).closure_eq
  · rw [B.eq_empty_of_gt n (by omega)]
    simp
theorem shellSites_eq (hc : SeparatedChainStructure) (n : ℕ) :
    Torus.shellSites D.L D.baseSpacing B.set n = B.shellSites n := by
  have hbd : BddAbove {m | (B.set m).Nonempty} := by
    refine ⟨D.lastLevel, fun m hm => ?_⟩
    by_contra hlt
    rw [mem_ofPred_eq, B.eq_empty_of_gt m (by omega)] at hm
    exact not_nonempty_empty hm
  have hlat : ∀ y, y ∈ Torus.spacingLattice 4 D.torusSide
      (Torus.scaleSpacing D.L D.baseSpacing (n : ℤ)) ↔ y ∈ D.levelSublattice n :=
    fun y => mem_spacingLattice_iff (scaleSpacing_natCast D n) y
  ext y
  simp only [Torus.shellSites, mem_ofPred_eq, SeparatedChain.shellSites, mem_inter_iff,
    SetLike.mem_coe, hlat, shell_eq B hc]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have h1 : y ∈ Torus.shell B.set n := by
    rw [shell_eq B hc]
    exact h.2
  obtain ⟨z, hz⟩ := closure_nonempty_iff.1 ⟨y, h1⟩
  exact le_csSup hbd ⟨z, hz.1⟩
end Shells
section Regions
variable (W : GaugeSetting)
variable {W} (h : SetsAreCubeUnions W) (hc : SeparatedChainStructure)
include hc
theorem level_eq_shellIndex (y : W.data.Space) :
    (toNestedRegions W h).level y = W.chain.shellIndex y := by
  change sInf {n | y ∈ Torus.shellSites W.data.L W.data.baseSpacing W.chain.set n} =
    sInf {n | y ∈ W.chain.shellSites n}
  simp only [shellSites_eq W.chain hc]
theorem levelScale_eq (y : W.data.Space) :
    (toNestedRegions W h).levelScale y = W.chain.localSpacing y := by
  change Torus.scaleSpacing W.data.L W.data.baseSpacing
    ((toNestedRegions W h).level y : ℤ) = W.data.levelSpacing (W.chain.shellIndex y)
  rw [level_eq_shellIndex h hc, scaleSpacing_natCast]
theorem cellOf_eq (y : W.data.Space) : (toNestedRegions W h).cellOf y = W.chain.localCube y := by
  change Torus.cubeAt y ((toNestedRegions W h).levelScale y) = _
  rw [levelScale_eq h hc, cubeAt_eq_supCube]
  rfl
theorem allCentres_eq : (toNestedRegions W h).allCentres = W.chain.shellSitesUnion := by
  ext y
  change (∃ n ≤ W.data.lastLevel, y ∈ Torus.shellSites W.data.L W.data.baseSpacing
    W.chain.set n) ↔ _
  simp only [shellSites_eq W.chain hc]
  constructor
  · rintro ⟨n, hn, hy⟩
    exact mem_iUnion₂.2 ⟨n, hn, hy⟩
  · intro hy
    obtain ⟨n, hn, hy⟩ := mem_iUnion₂.1 hy
    exact ⟨n, hn, hy⟩
end Regions
open RegionSequence.NestedRegions
section Subspaces
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
theorem IsPosSymmBilin.ext_on {p : V → V → ℝ} (hp : IsPosSymmBilin p) (E : Submodule ℝ V)
    {a b : V} (ha : a ∈ E) (hb : b ∈ E) (h : ∀ u ∈ E, p a u = p b u) : a = b := by
  apply sub_eq_zero.1
  apply hp.eq_zero_of_self
  rw [hp.sub_left]
  exact sub_eq_zero.2 (h _ (E.sub_mem ha hb))
end Subspaces
section Comaps
variable (W : GaugeSetting)
variable {W} (h : SetsAreCubeUnions W)
theorem anchor_eq (b : Dirichlet.LatticeBond 4 W.data.torusSide W.data.baseSpacing)
    (hb : toBaseBond W.data b ∈ W.bondSet) :
    ((toNestedRegions W h).anchor b).1 = (W.chain.anchor (toBaseBond W.data b)).1 := by
  have ht : ((toBaseBond W.data b).1.src : W.data.Space) = (b.source : W.data.Space) :=
    toBaseBond_src W.data b
  have hh : ((toBaseBond W.data b).1.tgt : W.data.Space) = (b.target : W.data.Space) :=
    toBaseBond_tgt W.data b
  have hstar : (b.source : W.data.Space) ∈ W.chain.set 0 ∨
      (b.target : W.data.Space) ∈ W.chain.set 0 := by
    rw [← ht, ← hh]
    rcases bondSet_cases W with h' | h' <;> rw [h'] at hb
    · exact hb
    · exact Or.inl hb.1
  by_cases hT : (b.source : W.data.Space) ∈ W.chain.set 0
  · have h1 : (toNestedRegions W h).anchor b = b.source := if_neg fun hn => hn.1 hT
    have h2 : W.chain.anchor (toBaseBond W.data b) = (toBaseBond W.data b).1.src :=
      if_pos (by rw [ht]; exact hT)
    rw [h1, h2, ht]
  · have hH := hstar.resolve_left hT
    have h1 : (toNestedRegions W h).anchor b = b.target := if_pos ⟨hT, hH⟩
    have h2 : W.chain.anchor (toBaseBond W.data b) = (toBaseBond W.data b).1.tgt :=
      if_neg (by rw [ht]; exact hT)
    rw [h1, h2, hh]
variable (hc : SeparatedChainStructure)
include hc
end Comaps
section Differences
variable {W : GaugeSetting}
variable (h : SetsAreCubeUnions W)
end Differences
section Averages
variable {W : GaugeSetting} (h : SetsAreCubeUnions W)
variable (hc : SeparatedChainStructure)
include hc
end Averages
section Coarse
variable {W : GaugeSetting} (h : SetsAreCubeUnions W)
end Coarse
section Operators
variable (W : GaugeSetting)
theorem finite_coarseBondsAt (n : Fin (W.data.lastLevel + 1)) : Finite ↥(W.coarseBondsAt n) :=
  have := finite_posBond W.data (Nat.lt_succ_iff.1 n.2)
  Subtype.finite
instance : Finite W.CoarseBond :=
  have := finite_coarseBondsAt W
  inferInstance
variable {W} (h : SetsAreCubeUnions W)
variable (hc : SeparatedChainStructure)
include hc
end Operators
end YangMills.Construction.GeneralTorus.RegionObjects
