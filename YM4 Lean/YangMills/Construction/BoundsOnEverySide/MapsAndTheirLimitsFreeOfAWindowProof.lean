import YangMills.Construction.BoundsOnEverySide.MapsAndTheirLimitsFreeOfAWindow
import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.Cumulants.SmallestPartitionsBlocksAndTransportByABijection
import YangMills.Construction.Cumulants.TwoMutuallyInversePolynomialSubstitutions
import YangMills.Construction.InfiniteLattice.CentredIdentityInAState
import YangMills.Construction.PassageToTheLimit.WhatPassesToTheLimitProof
import YangMills.Construction.Torus.ConnectedFunctionsAndCentredFunctionalInvertEachOther
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
open AmbientPoints SetPartition
namespace StateLimits
open InfiniteLattice R4TupleForms
namespace SeparatedFunctionals
variable {s : Conventions.StandingParameters} {E : ReflectionPositivity.AxisMirror.Ambient}
section PushPartition
variable (hT : SetPartition.Elementary.TransportUnderEquiv)
  {α β : Type} [DecidableEq α] [DecidableEq β] {A : Finset α} {A' : Finset β}
include hT in
private theorem exists_partitionImage_eq (e : A ≃ A') (P : Partitions A) :
    ∃ P' : Partitions A', P'.parts = partitionImage e P :=
  (hT α β A A' e).1.mapsTo (Set.mem_univ P)
private def pushPartition (e : A ≃ A') (P : Partitions A) : Partitions A' :=
  Classical.choose (exists_partitionImage_eq hT e P)
private theorem pushPartition_parts (e : A ≃ A') (P : Partitions A) :
    (pushPartition hT e P).parts = partitionImage e P :=
  Classical.choose_spec (exists_partitionImage_eq hT e P)
private theorem pushPartition_bijective (e : A ≃ A') : Function.Bijective (pushPartition hT e) := by
  constructor
  · intro P₁ P₂ h
    have h' : partitionImage e P₁ = partitionImage e P₂ := by
      rw [← pushPartition_parts hT, ← pushPartition_parts hT, h]
    exact (hT α β A A' e).1.injOn (Set.mem_univ _) (Set.mem_univ _) h'
  · intro P'
    obtain ⟨P, -, hP⟩ := (hT α β A A' e).1.surjOn
      (show P'.parts ∈ partitionSets A' from ⟨P', rfl⟩)
    exact ⟨P, Finpartition.ext (by rw [pushPartition_parts hT, hP])⟩
private theorem prod_pushPartition {M : Type*} [CommMonoid M] (e : A ≃ A') (P : Partitions A)
    (g : Finset β → M) :
    ∏ I ∈ (pushPartition hT e P).parts, g I = ∏ J ∈ P.parts, g (blockImage e J) := by
  rw [pushPartition_parts hT]
  unfold partitionImage
  exact Finset.prod_image ((hT α β A A' e).2 P).1.injOn
private theorem blockCount_pushPartition (e : A ≃ A') (P : Partitions A) :
    blockCount (pushPartition hT e P) = blockCount P := by
  unfold blockCount
  rw [pushPartition_parts hT]
  exact ((hT α β A A' e).2 P).2.2
end PushPartition
private def finCardEquiv {q : ℕ} (J : Finset (Fin q)) : (Finset.univ : Finset (Fin J.card)) ≃ J :=
  (Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _).trans (J.orderIsoOfFin rfl).toEquiv
private theorem blockImage_finCardEquiv {q : ℕ} (J : Finset (Fin q)) (I : Finset (Fin J.card)) :
    blockImage (finCardEquiv J) I = I.map (J.orderEmbOfFin rfl).toEmbedding := by
  ext y
  rw [mem_blockImage, Finset.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.1, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, Finset.mem_univ l⟩, hl, rfl⟩
private def reindexTuple {n k : ℕ} (f : separatedTuples s E n) (a : Fin k → Fin n)
    (ha : Function.Injective a) : allSeparatedTuples s E :=
  ⟨⟨k, f.1 ∘ a⟩, comp_mem_separatedTuples f.2 ha⟩
private theorem eq_of_range_eq_of_injective {n k k' : ℕ} {a : Fin k → Fin n} {b : Fin k' → Fin n}
    (ha : Function.Injective a) (hb : Function.Injective b) (h : Set.range a = Set.range b) :
    k = k' := by
  have h1 : Finset.univ.image a = Finset.univ.image b := by
    apply Finset.coe_injective
    simpa [Finset.coe_image] using h
  have h2 := congrArg Finset.card h1
  rwa [Finset.card_image_of_injective _ ha, Finset.card_image_of_injective _ hb,
    Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at h2
abbrev _root_.YangMills.SharedProofs.p12723 := @eq_of_range_eq_of_injective
private theorem reindexTuple_eq_of_strictMono {n k k' : ℕ} (f : separatedTuples s E n)
    {a : Fin k → Fin n} {b : Fin k' → Fin n} (ha : StrictMono a) (hb : StrictMono b)
    (h : Set.range a = Set.range b) : reindexTuple f a ha.injective = reindexTuple f b hb.injective := by
  have hk : k = k' := eq_of_range_eq_of_injective ha.injective hb.injective h
  subst hk
  have hab : a = b := (ha.range_inj hb).1 h
  subst hab
  rfl
section PartitionSum
variable (σ : allSeparatedTuples s E → ℝ)
private def valueOn {n : ℕ} (f : separatedTuples s E n) (J : Finset (Fin n)) : ℝ :=
  σ (toAllSeparated (restrictSeparated f J))
private theorem valueOn_restrictSeparated {q : ℕ} (f : separatedTuples s E q) (J : Finset (Fin q))
    (I : Finset (Fin J.card)) :
    valueOn σ (restrictSeparated f J) I =
      valueOn σ f (I.map (J.orderEmbOfFin rfl).toEmbedding) := by
  unfold valueOn
  congr 1
  have ha : StrictMono (J.orderEmbOfFin rfl ∘ I.orderEmbOfFin rfl) :=
    (J.orderEmbOfFin rfl).strictMono.comp (I.orderEmbOfFin rfl).strictMono
  refine reindexTuple_eq_of_strictMono f ha
    ((I.map (J.orderEmbOfFin rfl).toEmbedding).orderEmbOfFin rfl).strictMono ?_
  rw [Set.range_comp, Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin, Finset.coe_map]
  rfl
abbrev _root_.YangMills.DeltaSharedProofs.p501450 := @valueOn_restrictSeparated
private theorem toAllSeparated_restrict_univ {n : ℕ} (f : separatedTuples s E n) :
    toAllSeparated (restrictSeparated f Finset.univ) = toAllSeparated f :=
  reindexTuple_eq_of_strictMono f ((Finset.univ : Finset (Fin n)).orderEmbOfFin rfl).strictMono
    (strictMono_id : StrictMono (id : Fin n → Fin n))
    (by rw [Finset.range_orderEmbOfFin]; simp)
private def momentFamily {q : ℕ} (f : separatedTuples s E q) : Cumulants.SubsetFamily q :=
  fun J => (valueOn σ f J.1 : ℂ)
private theorem blockProduct_momentFamily {q : ℕ} (f : separatedTuples s E q)
    {J : Finset (Fin q)} (P : Partitions J) :
    Cumulants.blockProduct (momentFamily σ f) P =
      ((∏ I ∈ P.parts, valueOn σ f I : ℝ) : ℂ) := by
  rw [Complex.ofReal_prod, ← Finset.prod_coe_sort P.parts]
  rfl
private theorem moebiusPartitionSum_momentFamily
    (hT : SetPartition.Elementary.TransportUnderEquiv) {q : ℕ}
    (f : separatedTuples s E q) (J : Cumulants.NonemptyFinSubset q) :
    Cumulants.moebiusPartitionSum (momentFamily σ f) J =
      ((connectedOf σ J.1.card (restrictSeparated f J.1) : ℝ) : ℂ) := by
  have hterm : ∀ P : PartitionsFin J.1.card,
      ∏ I ∈ (pushPartition hT (finCardEquiv J.1) P).parts, valueOn σ f I =
        ∏ I ∈ P.parts, valueOn σ (restrictSeparated f J.1) I := by
    intro P
    rw [prod_pushPartition hT]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [blockImage_finCardEquiv, valueOn_restrictSeparated]
  have hsum := (pushPartition_bijective hT (finCardEquiv J.1)).sum_comp
    (fun P' : Partitions J.1 =>
      (-1 : ℂ) ^ (blockCount P' - 1) * ((blockCount P' - 1).factorial : ℂ) *
        ((∏ I ∈ P'.parts, valueOn σ f I : ℝ) : ℂ))
  unfold Cumulants.moebiusPartitionSum
  simp only [blockProduct_momentFamily]
  rw [← hsum]
  simp only [hterm, blockCount_pushPartition hT]
  unfold connectedOf
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  push_cast
  rfl
abbrev _root_.YangMills.DeltaSharedProofs.p501175 := @moebiusPartitionSum_momentFamily
private theorem eq_sum_partitions_prod_connected
    (hT : SetPartition.Elementary.TransportUnderEquiv)
    (hPoly : Cumulants.PartitionSubstitutionsInverse) {n : ℕ} (hn : 1 ≤ n)
    (f : separatedTuples s E n) :
    σ (toAllSeparated f) =
      ∑ P : PartitionsFin n, ∏ J ∈ P.parts,
        connectedOf σ J.card (restrictSeparated f J) := by
  have hback := congrFun ((hPoly n hn).2.2.2.2.2.1 (momentFamily σ f))
    (Cumulants.univSubset hn)
  rw [(hPoly n hn).2.2.2.2.2.2.1] at hback
  have hwhole : momentFamily σ f (Cumulants.univSubset hn) =
      ((σ (toAllSeparated f) : ℝ) : ℂ) := by
    show ((σ (toAllSeparated (restrictSeparated f Finset.univ)) : ℝ) : ℂ) = _
    rw [toAllSeparated_restrict_univ]
  rw [hwhole] at hback
  apply Complex.ofReal_injective
  rw [← hback, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Complex.ofReal_prod, ← Finset.prod_coe_sort P.parts]
  refine Finset.prod_congr rfl fun B _ => ?_
  exact moebiusPartitionSum_momentFamily σ hT f (Cumulants.blockSubset P B)
private theorem connectedOf_one (f : separatedTuples s E 1) :
    connectedOf σ 1 f = σ (toAllSeparated f) := by
  have huniv : (Finset.univ : Finset (Fin 1)) ≠ ⊥ := by
    intro h
    have h0 : (0 : Fin 1) ∈ (Finset.univ : Finset (Fin 1)) := Finset.mem_univ _
    rw [h] at h0
    simp at h0
  let top : PartitionsFin 1 := Finpartition.indiscrete huniv
  have htop : top.parts = {Finset.univ} := Finpartition.indiscrete_parts huniv
  have hall : ∀ P : PartitionsFin 1, P = top := by
    intro P
    refine Finpartition.ext ?_
    rw [htop]
    ext J
    rw [Finset.mem_singleton]
    constructor
    · intro hJ
      obtain ⟨k, hk⟩ := P.nonempty_of_mem_parts hJ
      exact Finset.eq_univ_of_forall fun l => by rwa [Subsingleton.elim l k]
    · rintro rfl
      obtain ⟨J₀, hJ₀, h0⟩ := P.exists_mem (Finset.mem_univ (0 : Fin 1))
      have hJ : J₀ = Finset.univ :=
        Finset.eq_univ_of_forall fun l => by rwa [Subsingleton.elim l 0]
      exact hJ ▸ hJ₀
  unfold connectedOf
  rw [Fintype.sum_eq_single top (fun P hP => absurd (hall P) hP)]
  have hone : blockCount top = 1 := by
    rw [blockCount, htop, Finset.card_singleton]
  rw [hone, htop]
  simp only [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul,
    Finset.prod_singleton]
  rw [toAllSeparated_restrict_univ]
end PartitionSum
section Limits
variable {σs : ℕ → allSeparatedTuples s E → ℝ} {σ : allSeparatedTuples s E → ℝ}
private theorem tendsto_connectedOf (h : ∀ X, Tendsto (fun j => σs j X) atTop (𝓝 (σ X))) (n : ℕ)
    (f : separatedTuples s E n) :
    Tendsto (fun j => connectedOf (σs j) n f) atTop
      (𝓝 (connectedOf σ n f)) := by
  unfold connectedOf
  refine tendsto_finsetSum _ fun P _ => ?_
  exact tendsto_const_nhds.mul (tendsto_finsetProd _ fun J _ => h _)
private theorem isTupleFunctional_of_tendsto (h : ∀ X, Tendsto (fun j => σs j X) atTop (𝓝 (σ X)))
    (hσs : ∀ j, IsTupleFunctional (σs j)) : IsTupleFunctional σ := by
  refine ⟨tendsto_nhds_unique (h _) ?_, fun n hn A hA => ?_⟩
  · simp only [(hσs _).1]
    exact tendsto_const_nhds
  · choose L hL using fun j => (hσs j).2 n hn A hA
    let T : ((i : Fin n) → c1Submodule (A i)) → separatedTuples s E n := fun g =>
      ⟨fun i => (g i : Pt s E → ℝ),
        mem_separatedTuples_of_forall_mem_c1 hA fun i => (g i).2⟩
    have ht : ∀ g, Tendsto (fun j => L j g) atTop (𝓝 (ofLength σ n (T g))) := fun g => by
      simp only [hL]
      exact h _
    refine ⟨MultilinearMap.mk' (fun g => ofLength σ n (T g)) ?_ ?_, fun g => rfl⟩
    · intro g i x y
      refine tendsto_nhds_unique (ht _) ?_
      simp only [MultilinearMap.map_update_add]
      exact (ht _).add (ht _)
    · intro g i c x
      refine tendsto_nhds_unique (ht _) ?_
      simp only [MultilinearMap.map_update_smul, smul_eq_mul]
      exact (ht _).const_mul c
private theorem isSymmetric_of_tendsto (h : ∀ X, Tendsto (fun j => σs j X) atTop (𝓝 (σ X)))
    (hσs : ∀ j, IsSymmetricTupleFunctional (σs j)) : IsSymmetricTupleFunctional σ := by
  intro n hn f e
  refine tendsto_nhds_unique (h _) ((h (toAllSeparated f)).congr fun j => ?_)
  exact (hσs j n hn f e).symm
end Limits
section Bounded
open Probability (IsBoundedRealRV)
variable {Ω : Type*} [MeasurableSpace Ω]
private theorem isBoundedRealRV_prod {ι : Type*} (t : Finset ι) (x : ι → Ω → ℝ)
    (h : ∀ i, IsBoundedRealRV (x i)) :
    IsBoundedRealRV fun ω => ∏ i ∈ t, x i ω := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (⟨measurable_const, 1, by simp⟩ :
      IsBoundedRealRV fun _ : Ω => (1 : ℝ))
  | insert i t hi ih =>
    simp only [Finset.prod_insert hi]
    obtain ⟨C, hC⟩ := (h i).bounded
    obtain ⟨D, hD⟩ := ih.bounded
    exact ⟨(h i).measurable.mul ih.measurable, C * D, fun ω => by
      rw [abs_mul]
      exact mul_le_mul (hC ω) (hD ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))⟩
private theorem integrable_of_isBoundedRealRV {x : Ω → ℝ} (h : IsBoundedRealRV x)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Integrable x μ := by
  obtain ⟨C, hC⟩ := h.bounded
  exact Integrable.of_bound h.measurable.aestronglyMeasurable C
    (Eventually.of_forall fun ω => by simpa using hC ω)
end Bounded
private theorem abs_coord_sub_le_dist (x y : Pt s .euclidean) (μ : Fin 4) :
    |(show Fin 4 → ℝ from x) μ - (show Fin 4 → ℝ from y) μ| ≤ dist x y := by
  have h : dist x y = TorusMetric.euclidNormVec
      ((show Fin 4 → ℝ from x) - (show Fin 4 → ℝ from y)) := rfl
  rw [h, euclidNormVec_eq_norm, ← Real.norm_eq_abs]
  exact PiLp.norm_apply_le
    (WithLp.toLp 2 ((show Fin 4 → ℝ from x) - (show Fin 4 → ℝ from y))) μ
private theorem continuous_toAmbientSpace :
    Continuous (fun x : Pt s .euclidean => (show InfiniteLattice.AmbientSpace from x)) := by
  refine continuous_pi fun μ => ?_
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => ?_)
  simpa [Real.dist_eq] using abs_coord_sub_le_dist x y μ
private theorem mem_compactTestFunctions {f : Pt s .euclidean → ℝ}
    (h : IsC1Fn f) (hc : IsCompact (tsupport f)) :
    (f : InfiniteLattice.AmbientSpace → ℝ) ∈ compactTestFunctions := by
  have hcont : Continuous (fun x : InfiniteLattice.AmbientSpace => f x) :=
    ((isC1Fn_euclidean_iff f).1 h).continuous
  have hK : IsCompact
      ((fun x : Pt s .euclidean => (show InfiniteLattice.AmbientSpace from x)) '' tsupport f) :=
    hc.image continuous_toAmbientSpace
  have hsupp : HasCompactSupport (fun x : InfiniteLattice.AmbientSpace => f x) :=
    HasCompactSupport.intro hK fun x hx => by
      by_contra hne
      exact hx ⟨x, subset_tsupport f hne, rfl⟩
  exact ⟨hcont.measurable, hcont.bounded_above_of_compact_support hsupp, hsupp⟩
private theorem entry_mem_compactTestFunctions {n : ℕ} (f : separatedTuples s .euclidean n)
    (l : Fin n) : (f.1 l : InfiniteLattice.AmbientSpace → ℝ) ∈ compactTestFunctions :=
  mem_compactTestFunctions (f.2.1 l).1 (f.2.1 l).2
section Centred
open Probability (IsBoundedRealRV)
variable {a : ℝ}
private structure EnergyLinearity (a : ℝ) : Prop where
  bounded : ∀ f ∈ compactTestFunctions,
    IsBoundedRealRV (smearedEnergy f : GaugeField a → ℝ)
  add : ∀ f ∈ compactTestFunctions, ∀ g ∈ compactTestFunctions,
    (smearedEnergy (f + g) : GaugeField a → ℝ) = smearedEnergy f + smearedEnergy g
  smul : ∀ (c : ℝ), ∀ f ∈ compactTestFunctions,
    (smearedEnergy (c • f) : GaugeField a → ℝ) = c • smearedEnergy f
private theorem energyLinearity (hState : InfiniteLattice.CenteredIdentity.Statement)
    (s : Conventions.StandingParameters) (k : ℕ) (hk : 0 < k)
    (ν : Measure (GaugeField (PeriodicLattice.meshSize s.L (k : ℤ))))
    (hν : IsProbabilityMeasure ν) : EnergyLinearity (PeriodicLattice.meshSize s.L (k : ℤ)) := by
  obtain ⟨⟨h1, F, hF, O, hO⟩, -, -⟩ := hState { s with K := ⟨k, hk⟩ } ν hν
  have hmem : ∀ {f}, f ∈ compactTestFunctions → f ∈ F := fun {f} hf => by
    rw [← SetLike.mem_coe, hF]
    exact hf
  refine ⟨fun f hf => (h1 f hf).2, fun f hf g hg => ?_, fun c f hf => ?_⟩
  · have h := O.map_add ⟨f, hmem hf⟩ ⟨g, hmem hg⟩
    rw [hO, hO, hO] at h
    exact h
  · have h := O.map_smul c ⟨f, hmem hf⟩
    rw [hO, hO] at h
    exact h
private def centredEnergy (ν : Measure (GaugeField a)) (f : InfiniteLattice.AmbientSpace → ℝ)
    (U : GaugeField a) : ℝ :=
  smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν
private theorem centredEnergy_bounded (hO : EnergyLinearity a) (ν : Measure (GaugeField a))
    {f : InfiniteLattice.AmbientSpace → ℝ} (hf : f ∈ compactTestFunctions) :
    IsBoundedRealRV (centredEnergy ν f) := by
  obtain ⟨C, hC⟩ := (hO.bounded f hf).bounded
  refine ⟨(hO.bounded f hf).measurable.sub_const _, C + |∫ V, smearedEnergy f V ∂ν|, fun U => ?_⟩
  exact (abs_sub _ _).trans (add_le_add_left (hC U) _)
private theorem centredEnergy_add (hO : EnergyLinearity a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] {f g : InfiniteLattice.AmbientSpace → ℝ}
    (hf : f ∈ compactTestFunctions) (hg : g ∈ compactTestFunctions) :
    centredEnergy ν (f + g) = centredEnergy ν f + centredEnergy ν g := by
  funext U
  have hi : ∫ V, smearedEnergy (f + g) V ∂ν =
      (∫ V, smearedEnergy f V ∂ν) + ∫ V, smearedEnergy g V ∂ν := by
    rw [hO.add f hf g hg]
    exact integral_add (integrable_of_isBoundedRealRV (hO.bounded f hf) ν)
      (integrable_of_isBoundedRealRV (hO.bounded g hg) ν)
  have hp := congrFun (hO.add f hf g hg) U
  show smearedEnergy (f + g) U - ∫ V, smearedEnergy (f + g) V ∂ν =
    (smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν) +
      (smearedEnergy g U - ∫ V, smearedEnergy g V ∂ν)
  rw [hi, hp, Pi.add_apply]
  ring
private theorem centredEnergy_smul (hO : EnergyLinearity a) (ν : Measure (GaugeField a))
    (c : ℝ) {f : InfiniteLattice.AmbientSpace → ℝ} (hf : f ∈ compactTestFunctions) :
    centredEnergy ν (c • f) = c • centredEnergy ν f := by
  funext U
  have hi : ∫ V, smearedEnergy (c • f) V ∂ν = c * ∫ V, smearedEnergy f V ∂ν := by
    rw [hO.smul c f hf]
    exact integral_const_mul c _
  have hp := congrFun (hO.smul c f hf) U
  show smearedEnergy (c • f) U - ∫ V, smearedEnergy (c • f) V ∂ν =
    c * (smearedEnergy f U - ∫ V, smearedEnergy f V ∂ν)
  rw [hi, hp, Pi.smul_apply, smul_eq_mul]
  ring
private theorem c1Submodule_mem {A : Set (Pt s .euclidean)} (z : c1Submodule A) :
    ((z : Pt s .euclidean → ℝ) : InfiniteLattice.AmbientSpace → ℝ) ∈ compactTestFunctions :=
  mem_compactTestFunctions z.2.1 z.2.2.1
private def centredEnergyMap (hO : EnergyLinearity a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] (A : Set (Pt s .euclidean)) :
    c1Submodule A →ₗ[ℝ] (GaugeField a → ℝ) where
  toFun z := centredEnergy ν (z : Pt s .euclidean → ℝ)
  map_add' x y := centredEnergy_add hO ν (c1Submodule_mem x) (c1Submodule_mem y)
  map_smul' c x := centredEnergy_smul hO ν c (c1Submodule_mem x)
private def centredProductMap (hO : EnergyLinearity a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] {n : ℕ} (A : Fin n → Set (Pt s .euclidean)) :
    MultilinearMap ℝ (fun i => c1Submodule (A i)) (GaugeField a → ℝ) :=
  (MultilinearMap.mkPiAlgebra ℝ (Fin n) (GaugeField a → ℝ)).compLinearMap
    fun i => centredEnergyMap hO ν (A i)
private theorem centredProductMap_apply (hO : EnergyLinearity a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] {n : ℕ} (A : Fin n → Set (Pt s .euclidean))
    (g : (i : Fin n) → c1Submodule (A i)) (U : GaugeField a) :
    centredProductMap hO ν A g U = ∏ i, centredEnergy ν (g i : Pt s .euclidean → ℝ) U := by
  simp only [centredProductMap, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Finset.prod_apply]
  rfl
private theorem centredProductMap_integrable (hO : EnergyLinearity a)
    (ρ ν : Measure (GaugeField a)) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν] {n : ℕ}
    (A : Fin n → Set (Pt s .euclidean)) (g : (i : Fin n) → c1Submodule (A i)) :
    Integrable (centredProductMap hO ν A g) ρ := by
  have h := isBoundedRealRV_prod Finset.univ
    (fun i => centredEnergy ν (g i : Pt s .euclidean → ℝ))
    fun i => centredEnergy_bounded hO ν (c1Submodule_mem (g i))
  have he : centredProductMap hO ν A g =
      fun U => ∏ i, centredEnergy ν (g i : Pt s .euclidean → ℝ) U :=
    funext (centredProductMap_apply hO ν A g)
  rw [he]
  exact integrable_of_isBoundedRealRV h ρ
end Centred
section PairedStates
open Probability (IsBoundedRealRV)
variable {k : ℕ} (ρ₀ ν₀ : Measure (GaugeField (PeriodicLattice.meshSize s.L (k : ℤ))))
private def pairedIntegral (k : ℕ)
    (ρ₀ ν₀ : Measure (GaugeField (PeriodicLattice.meshSize s.L (k : ℤ))))
    (X : FinTuple s) : ℝ :=
  ∫ U, centeredProduct k ν₀ X U ∂ρ₀
private theorem prod_comp_orderEmbOfFin {n : ℕ} (J : Finset (Fin n)) (g : Fin n → ℝ) :
    ∏ i, g (J.orderEmbOfFin rfl i) = ∏ l ∈ J, g l := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.LimitPassage.prod_comp_orderEmbOfFin <;> assumption
variable [IsProbabilityMeasure ρ₀] [IsProbabilityMeasure ν₀]
private theorem pairedIntegral_isTupleFunctional
    (hO : EnergyLinearity (PeriodicLattice.meshSize s.L (k : ℤ))) :
    IsTupleFunctional (pairedIntegral k ρ₀ ν₀) := by
  refine ⟨?_, fun n _ A hA => ?_⟩
  · have h : (fun U => centeredProduct k ν₀ ⟨nilTuple s .euclidean, nilTuple_mem_allSeparatedTuples⟩ U) =
        fun _ => (1 : ℝ) := funext (centeredProduct_nil k ν₀)
    show ∫ U, centeredProduct k ν₀ ⟨nilTuple s .euclidean, nilTuple_mem_allSeparatedTuples⟩ U ∂ρ₀ = 1
    rw [h]
    simp
  · refine ⟨MultilinearMap.mk' (fun g => ∫ U, centredProductMap hO ν₀ A g U ∂ρ₀) ?_ ?_,
      fun g => ?_⟩
    · intro g i x y
      simp only [MultilinearMap.map_update_add]
      exact integral_add (centredProductMap_integrable hO ρ₀ ν₀ A _)
        (centredProductMap_integrable hO ρ₀ ν₀ A _)
    · intro g i c x
      simp only [MultilinearMap.map_update_smul]
      exact integral_smul c _
    · show ∫ U, centredProductMap hO ν₀ A g U ∂ρ₀ =
        ∫ U, ∏ i, centredEnergy ν₀ (g i : Pt s .euclidean → ℝ) U ∂ρ₀
      exact integral_congr_ae (Eventually.of_forall (centredProductMap_apply hO ν₀ A g))
private theorem pairedIntegral_isSymmetric : IsSymmetricTupleFunctional (pairedIntegral k ρ₀ ν₀) := by
  intro n _ f e
  show ∫ U, ∏ i, centredEnergy ν₀ (f.1 (e i)) U ∂ρ₀ = ∫ U, ∏ i, centredEnergy ν₀ (f.1 i) U ∂ρ₀
  exact congrArg (fun F : GaugeField _ → ℝ => ∫ U, F U ∂ρ₀)
    (funext fun U => Equiv.prod_comp e fun i => centredEnergy ν₀ (f.1 i) U)
private theorem ofReal_pairedIntegral_restrict {n : ℕ} (f : separatedTuples s .euclidean n)
    {J : Finset (Fin n)} (hJ : J.Nonempty) :
    ((pairedIntegral k ρ₀ ν₀ (toAllSeparated (restrictSeparated f J)) : ℝ) : ℂ) =
      Cumulants.finsetMoment ρ₀ (fun l => centredEnergy ν₀ (f.1 l)) J := by
  unfold Cumulants.finsetMoment
  rw [if_neg hJ.ne_empty, Probability.complexExpectation, integral_complex_ofReal]
  congr 1
  show ∫ U, ∏ i, centredEnergy ν₀ (f.1 (J.orderEmbOfFin rfl i)) U ∂ρ₀ = _
  exact congrArg (fun F : GaugeField _ → ℝ => ∫ U, F U ∂ρ₀)
    (funext fun U => prod_comp_orderEmbOfFin J fun l => centredEnergy ν₀ (f.1 l) U)
private theorem centredEnergy_entries_bounded
    (hO : EnergyLinearity (PeriodicLattice.meshSize s.L (k : ℤ))) {n : ℕ}
    (f : separatedTuples s .euclidean n) (l : Fin n) :
    IsBoundedRealRV (centredEnergy ν₀ (f.1 l)) :=
  centredEnergy_bounded hO ν₀ (entry_mem_compactTestFunctions f l)
private theorem ofReal_connectedOf_pairedIntegral (hCum : Cumulants.CumulantMomentRelations)
    (hO : EnergyLinearity (PeriodicLattice.meshSize s.L (k : ℤ))) {n : ℕ} (hn : 1 ≤ n)
    (f : separatedTuples s .euclidean n) :
    ((connectedOf (pairedIntegral k ρ₀ ν₀) n f : ℝ) : ℂ) =
      Cumulants.mixedCumulant ρ₀ fun l => centredEnergy ν₀ (f.1 l) := by
  obtain ⟨-, -, -, -, -, -, hc⟩ := hCum _ ρ₀ n (fun l => centredEnergy ν₀ (f.1 l))
    (centredEnergy_entries_bounded ν₀ hO f)
  rw [hc hn]
  unfold connectedOf
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_prod]
  push_cast
  congr 1
  exact Finset.prod_congr rfl fun J hJ =>
    ofReal_pairedIntegral_restrict ρ₀ ν₀ f (P.nonempty_of_mem_parts hJ)
private theorem ofReal_connectedOf_pairedIntegral_of_two_le
    (hCum : Cumulants.CumulantMomentRelations)
    (hO : EnergyLinearity (PeriodicLattice.meshSize s.L (k : ℤ))) {n : ℕ} (hn : 2 ≤ n)
    (f : separatedTuples s .euclidean n) :
    ((connectedOf (pairedIntegral k ρ₀ ν₀) n f : ℝ) : ℂ) = smearedEnergyCumulant ρ₀ f.1 := by
  rw [ofReal_connectedOf_pairedIntegral ρ₀ ν₀ hCum hO (by omega)]
  obtain ⟨-, -, -, hs, -⟩ := hCum _ ρ₀ n (fun l => centredEnergy ν₀ (f.1 l))
    (centredEnergy_entries_bounded ν₀ hO f)
  have he : (fun l => centredEnergy ν₀ (f.1 l)) =
      Cumulants.shiftTuple (fun i U => smearedEnergy (f.1 i) U)
        (fun i => -∫ V, smearedEnergy (f.1 i) V ∂ν₀) := by
    funext l U
    simp [centredEnergy, Cumulants.shiftTuple, sub_eq_add_neg]
  rw [he, hs n _ _ hn fun i => hO.bounded _ (entry_mem_compactTestFunctions f i)]
  rfl
private theorem connectedOf_pairedIntegral_isTupleSymmetric
    (hCum : Cumulants.CumulantMomentRelations)
    (hO : EnergyLinearity (PeriodicLattice.meshSize s.L (k : ℤ))) {n : ℕ} (hn : 1 ≤ n) :
    IsTupleSymmetric (connectedOf (pairedIntegral k ρ₀ ν₀) n) := by
  intro f e
  apply Complex.ofReal_injective
  rw [ofReal_connectedOf_pairedIntegral ρ₀ ν₀ hCum hO hn,
    ofReal_connectedOf_pairedIntegral ρ₀ ν₀ hCum hO hn]
  obtain ⟨ha, -⟩ := hCum _ ρ₀ n (fun l => centredEnergy ν₀ (f.1 l))
    (centredEnergy_entries_bounded ν₀ hO f)
  have hb := centredEnergy_entries_bounded ν₀ hO f
  exact (ha n _ (centredEnergy ν₀ (f.1 ⟨0, hn⟩)) hn hb (hb _)).2.1 e
private theorem pairedIntegral_one (hO : EnergyLinearity (PeriodicLattice.meshSize s.L (k : ℤ)))
    (f : separatedTuples s .euclidean 1) :
    pairedIntegral k ρ₀ ν₀ (toAllSeparated f) =
      (∫ U, smearedEnergy (f.1 0) U ∂ρ₀) - ∫ U, smearedEnergy (f.1 0) U ∂ν₀ := by
  show ∫ U, ∏ i : Fin 1, centredEnergy ν₀ (f.1 i) U ∂ρ₀ = _
  simp only [Fin.prod_univ_one, centredEnergy]
  rw [integral_sub (integrable_of_isBoundedRealRV (hO.bounded _ (entry_mem_compactTestFunctions f 0)) ρ₀)
    (integrable_const _)]
  simp
end PairedStates
theorem _root_.YangMills.Construction.BoundsOnEverySide.stateMapsAndLimitsAreSeparatedFunctionals_holds
    (hCum : Cumulants.CumulantMomentRelations)
    (hPart : SetPartition.Elementary.BasicFacts)
    (hPoly : Cumulants.PartitionSubstitutionsInverse)
    (hState : InfiniteLattice.CenteredIdentity.Statement)
    (hInv : TorusOrFourSpace.ConnectedFamilyCentredInverse) :
    BoundsOnEverySide.StateMapsAndLimitsAreSeparatedFunctionals := by
  have hT : SetPartition.Elementary.TransportUnderEquiv := hPart.2.2.1
  refine ⟨?_, fun s σ _ n hn f => eq_sum_partitions_prod_connected σ hT hPoly hn f⟩
  intro s K β ρ ν hK hseq
  have hρ : ∀ j, IsProbabilityMeasure (ρ j) := fun j =>
    (show IsPeriodicGibbs (β j) (ρ j) from hseq.left_mem j).1.1
  have hν : ∀ j, IsProbabilityMeasure (ν j) := fun j =>
    (show IsPeriodicGibbs (β j) (ν j) from hseq.right_mem j).1.1
  have hO : ∀ j, EnergyLinearity (PeriodicLattice.meshSize s.L (K j : ℤ)) := fun j =>
    energyLinearity hState s (K j) (hK j) (ρ j) (hρ j)
  have hval : ∀ j, pairedValue K ρ ν j = pairedIntegral (K j) (ρ j) (ν j) := fun _ => rfl
  have hmap : ∀ j, HasConnectedParts K ρ ν j := fun j => by
    refine ⟨⟨pairedIntegral_isTupleFunctional (ρ j) (ν j) (hO j),
      pairedIntegral_isSymmetric (ρ j) (ν j)⟩, fun f => ?_, fun n hn f => ?_⟩
    · rw [hval, connectedOf_one, pairedIntegral_one (ρ j) (ν j) (hO j)]
    · rw [hval]
      exact ofReal_connectedOf_pairedIntegral_of_two_le (ρ j) (ν j) hCum (hO j) hn f
  refine ⟨hmap, fun σ hσ => ?_⟩
  have hlim : ∀ X, Tendsto (fun j => pairedValue K ρ ν j X) atTop (𝓝 (σ X)) := hσ.pointwise
  have hfun : IsTupleFunctional σ :=
    isTupleFunctional_of_tendsto hlim fun j => (hmap j).1.1
  have hconn : ∀ (n : ℕ) (f : separatedTuples s .euclidean n),
      Tendsto (fun j => connectedOf (pairedValue K ρ ν j) n f) atTop
        (𝓝 (connectedOf σ n f)) := tendsto_connectedOf hlim
  obtain ⟨hml, -⟩ := hInv s .euclidean σ hfun
  refine ⟨⟨hfun, isSymmetric_of_tendsto hlim fun j => (hmap j).1.2⟩, fun n _ f => hconn n f,
    fun f => ⟨connectedOf_one σ f, ?_⟩, fun n hn f => ?_, fun n hn => ⟨?_, hml n hn⟩,
    ⟨fun n _ => connectedOf σ n, fun n hn => hml n (by omega)⟩,
    fun n hn => rfl⟩
  · refine (hlim (toAllSeparated f)).congr fun j => ?_
    rw [hval]
    exact pairedIntegral_one (ρ j) (ν j) (hO j) f
  · refine ((Complex.continuous_ofReal.tendsto _).comp (hconn n f)).congr fun j => ?_
    exact (hmap j).2.2 n hn f
  · intro f e
    refine tendsto_nhds_unique (hconn n _) ((hconn n f).congr fun j => ?_)
    exact (connectedOf_pairedIntegral_isTupleSymmetric (ρ j) (ν j) hCum (hO j) hn f e).symm
end SeparatedFunctionals
end StateLimits
end YangMills.Construction
