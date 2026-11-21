import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
open Matrices
abbrev AmbientSpace : Type := Fin 4 → ℝ
def latticeSubgroup (a : ℝ) : AddSubgroup AmbientSpace where
  carrier := {x | ∃ n : Fin 4 → ℤ, ∀ μ, x μ = (n μ : ℝ) * a}
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨n', hn'⟩
    exact ⟨n + n', fun μ => by simp [hn, hn', add_mul]⟩
  zero_mem' := ⟨0, fun μ => by simp⟩
  neg_mem' := by
    rintro x ⟨n, hn⟩
    exact ⟨-n, fun μ => by simp [hn]⟩
abbrev LatticePoint (a : ℝ) : Type := ↥(latticeSubgroup a)
def axisStep (a : ℝ) (μ : Fin 4) : LatticePoint a :=
  ⟨Pi.single μ a, Pi.single μ 1, fun ν => by
    by_cases h : ν = μ
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]⟩
@[ext]
structure Link (a : ℝ) where
  initial : LatticePoint a
  terminal : LatticePoint a
  isAdjacent : ∃ μ : Fin 4, terminal - initial = axisStep a μ ∨ terminal - initial = -axisStep a μ
variable {a : ℝ}
namespace Link
def IsPositivelyOriented (b : Link a) : Prop := ∃ μ : Fin 4, b.terminal - b.initial = axisStep a μ
def opposite (b : Link a) : Link a where
  initial := b.terminal
  terminal := b.initial
  isAdjacent := by
    obtain ⟨μ, h | h⟩ := b.isAdjacent
    · exact ⟨μ, Or.inr (by rw [← h]; abel)⟩
    · exact ⟨μ, Or.inl (by rw [← neg_eq_iff_eq_neg.mpr h]; abel)⟩
def forwardFrom (x : LatticePoint a) (μ : Fin 4) : Link a := ⟨x, x + axisStep a μ, μ, Or.inl (by abel)⟩
end Link
@[ext]
structure ElementaryPlaquette (a : ℝ) where
  corner : LatticePoint a
  lowAxis : Fin 4
  highAxis : Fin 4
  lowAxis_lt_highAxis : lowAxis < highAxis
namespace ElementaryPlaquette
def center (p : ElementaryPlaquette a) : AmbientSpace :=
  (p.corner : AmbientSpace) + Pi.single p.lowAxis (a / 2) + Pi.single p.highAxis (a / 2)
def edges (p : ElementaryPlaquette a) : List (Link a) :=
  [Link.forwardFrom p.corner p.lowAxis, Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis,
    Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis, Link.forwardFrom p.corner p.highAxis]
end ElementaryPlaquette
def faceHolonomy (U : Link a → ComplexMatrix2.specialUnitary) (p : ElementaryPlaquette a) :
    ComplexMatrix2.specialUnitary :=
  U (Link.forwardFrom p.corner p.lowAxis) * U (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis) *
    (U (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis))⁻¹ *
    (U (Link.forwardFrom p.corner p.highAxis))⁻¹
def faceEnergy (U : Link a → ComplexMatrix2.specialUnitary) (p : ElementaryPlaquette a) : ℝ :=
  1 - (1 / 2) * (ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re
def GaugeField (a : ℝ) : Type :=
  {U : Link a → ComplexMatrix2.specialUnitary // ∀ b, U b.opposite = (U b)⁻¹}
instance : CoeFun (GaugeField a) fun _ => Link a → ComplexMatrix2.specialUnitary := ⟨Subtype.val⟩
instance : TopologicalSpace (GaugeField a) :=
  inferInstanceAs (TopologicalSpace {U : Link a → ComplexMatrix2.specialUnitary // ∀ b, U b.opposite = (U b)⁻¹})
instance : MeasurableSpace (GaugeField a) := borel (GaugeField a)
instance : BorelSpace (GaugeField a) := ⟨rfl⟩
@[reducible] def linkSigma (ℬ : Set (Link a)) : MeasurableSpace (GaugeField a) :=
  ⨆ b ∈ ℬ, MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance
def linksWithin (S : Set AmbientSpace) : Set (Link a) :=
  {b | (b.initial : AmbientSpace) ∈ S ∧ (b.terminal : AmbientSpace) ∈ S}
@[reducible] def regionSigma (S : Set AmbientSpace) : MeasurableSpace (GaugeField a) :=
  linkSigma (linksWithin S)
def IsBoundedObservable (A : GaugeField a → ℂ) : Prop :=
  Measurable A ∧ ∃ C : ℝ, ∀ U, ‖A U‖ ≤ C
def observableSupNorm (A : GaugeField a → ℂ) : ℝ := ⨆ U, ‖A U‖
def IsRegionMeasurable (S : Set AmbientSpace) (A : GaugeField a → ℂ) : Prop :=
  Measurable[regionSigma S] A
def IsLocalObservable (A : GaugeField a → ℂ) : Prop :=
  ∃ S : Set AmbientSpace, Bornology.IsBounded S ∧ IsRegionMeasurable S A
def cube (q : AmbientSpace) (r : ℝ) : Set AmbientSpace := {x | ∀ μ, q μ ≤ x μ ∧ x μ ≤ q μ + r}
def IsBoundedBorelCompactlySupported {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (f : AmbientSpace → E) : Prop :=
  Measurable f ∧ (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧ HasCompactSupport f
def smearedEnergy {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : AmbientSpace → E)
    (U : GaugeField a) : E :=
  ∑ᶠ p : ElementaryPlaquette a, faceEnergy U p • f p.center
structure LatticeSymmetry (a : ℝ) where
  toFun : AmbientSpace → AmbientSpace
  preservesDist : ∀ x y, TorusMetric.euclidNormVec (toFun x - toFun y) =
    TorusMetric.euclidNormVec (x - y)
  image_eq : toFun '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a
theorem int_vec_unit_of_sum_sq_eq_one (n : Fin 4 → ℤ) (h : ∑ ν, n ν ^ 2 = 1) :
    ∃ μ, n = Pi.single μ 1 ∨ n = -Pi.single μ 1 := by
  obtain ⟨μ, hμ⟩ : ∃ μ, n μ ≠ 0 := by
    by_contra hc
    have hz : ∀ ν, n ν = 0 := fun ν => by
      by_contra hν
      exact hc ⟨ν, hν⟩
    simp [hz] at h
  have hsplit := Finset.add_sum_erase Finset.univ (fun ν => n ν ^ 2) (Finset.mem_univ μ)
  have hrest : 0 ≤ ∑ ν ∈ Finset.univ.erase μ, n ν ^ 2 :=
    Finset.sum_nonneg fun ν _ => sq_nonneg _
  have hpos : 1 ≤ n μ ^ 2 := by
    have := sq_pos_of_ne_zero hμ
    omega
  have hone : n μ ^ 2 = 1 := by omega
  have hzero : ∑ ν ∈ Finset.univ.erase μ, n ν ^ 2 = 0 := by omega
  have hother : ∀ ν, ν ≠ μ → n ν = 0 := fun ν hν => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun ν _ => sq_nonneg (n ν)).mp hzero ν
      (Finset.mem_erase.mpr ⟨hν, Finset.mem_univ ν⟩)
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  refine ⟨μ, ?_⟩
  have hfac : (n μ - 1) * (n μ + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left
    have h1 : n μ = 1 := by omega
    funext ν
    by_cases hν : ν = μ
    · subst hν; simp [h1]
    · simp [Pi.single_eq_of_ne hν, hother ν hν]
  · right
    have h1 : n μ = -1 := by omega
    funext ν
    by_cases hν : ν = μ
    · subst hν; simp [h1]
    · simp [Pi.single_eq_of_ne hν, hother ν hν]
theorem euclidNormVec_single (μ : Fin 4) (t : ℝ) :
    TorusMetric.euclidNormVec (Pi.single μ t : AmbientSpace) = |t| := by
  have h : ∑ ν, (Pi.single μ t : AmbientSpace) ν ^ 2 = t ^ 2 := by
    rw [Finset.sum_eq_single μ]
    · simp
    · intro ν _ hν
      simp [Pi.single_eq_of_ne hν]
    · simp
  rw [TorusMetric.euclidNormVec, h, Real.sqrt_sq_eq_abs]
theorem isAdjacent_of_euclidNormVec (x y : LatticePoint a)
    (h : TorusMetric.euclidNormVec ((y : AmbientSpace) - x) = |a|) :
    ∃ μ : Fin 4, y - x = axisStep a μ ∨ y - x = -axisStep a μ := by
  obtain ⟨n, hn⟩ := (y - x).2
  by_cases ha : a = 0
  · subst ha
    refine ⟨0, Or.inl (Subtype.ext (funext fun ν => ?_))⟩
    have := hn ν
    simp only [mul_zero] at this
    rw [this]
    simp [axisStep]
  · have hn' : ∀ ν, ((y : AmbientSpace) - x) ν = (n ν : ℝ) * a := hn
    have hsq : ∑ ν, ((y : AmbientSpace) - x) ν ^ 2 = a ^ 2 := by
      have h0 : 0 ≤ ∑ ν, ((y : AmbientSpace) - x) ν ^ 2 := Finset.sum_nonneg fun ν _ => sq_nonneg _
      have h1 := Real.sq_sqrt h0
      rw [TorusMetric.euclidNormVec] at h
      rw [h, sq_abs] at h1
      exact h1.symm
    have hsum : ∑ ν, n ν ^ 2 = 1 := by
      have h2 : (∑ ν, (n ν : ℝ) ^ 2) * a ^ 2 = a ^ 2 := by
        rw [Finset.sum_mul]
        calc ∑ ν, (n ν : ℝ) ^ 2 * a ^ 2 = ∑ ν, ((y : AmbientSpace) - x) ν ^ 2 :=
              Finset.sum_congr rfl fun ν _ => by rw [hn' ν, mul_pow]
          _ = a ^ 2 := hsq
      have h3 : ∑ ν, (n ν : ℝ) ^ 2 = 1 := by
        have := pow_ne_zero 2 ha
        exact mul_right_cancel₀ this (by rw [h2, one_mul])
      exact_mod_cast h3
    obtain ⟨μ, h1 | h1⟩ := int_vec_unit_of_sum_sq_eq_one n hsum
    · refine ⟨μ, Or.inl (Subtype.ext (funext fun ν => ?_))⟩
      have : ((y - x : LatticePoint a) : AmbientSpace) ν = (n ν : ℝ) * a := hn ν
      rw [this, h1]
      by_cases hν : ν = μ
      · subst hν; simp [axisStep]
      · simp [axisStep, Pi.single_eq_of_ne hν]
    · refine ⟨μ, Or.inr (Subtype.ext (funext fun ν => ?_))⟩
      have : ((y - x : LatticePoint a) : AmbientSpace) ν = (n ν : ℝ) * a := hn ν
      rw [this, h1]
      by_cases hν : ν = μ
      · subst hν; simp [axisStep]
      · simp [axisStep, Pi.single_eq_of_ne hν]
namespace LatticeSymmetry
variable (s : LatticeSymmetry a)
def pointMap (x : LatticePoint a) : LatticePoint a :=
  ⟨s.toFun x, by
    have h : s.toFun x ∈ s.toFun '' (latticeSubgroup a : Set AmbientSpace) := ⟨x, x.2, rfl⟩
    rw [s.image_eq] at h
    exact h⟩
def linkMap (b : Link a) : Link a where
  initial := s.pointMap b.initial
  terminal := s.pointMap b.terminal
  isAdjacent := by
    apply isAdjacent_of_euclidNormVec
    change TorusMetric.euclidNormVec (s.toFun b.terminal - s.toFun b.initial) = |a|
    rw [s.preservesDist]
    obtain ⟨μ, h | h⟩ := b.isAdjacent
    · have h' : (b.terminal : AmbientSpace) - (b.initial : AmbientSpace) = (Pi.single μ a : AmbientSpace) :=
        congrArg Subtype.val h
      rw [h', euclidNormVec_single]
    · have h' : (b.terminal : AmbientSpace) - (b.initial : AmbientSpace) =
          (Pi.single μ (-a) : AmbientSpace) := by
        rw [Pi.single_neg]
        exact congrArg Subtype.val h
      rw [h', euclidNormVec_single, abs_neg]
def pullbackField (U : GaugeField a) : GaugeField a :=
  ⟨fun b => U (s.linkMap b), fun b => U.2 (s.linkMap b)⟩
def actOn {E : Type*} (A : GaugeField a → E) : GaugeField a → E :=
  fun U => A (s.pullbackField U)
theorem actOn_indicator_eq_iff (I : Set (GaugeField a)) :
    s.actOn (I.indicator (1 : GaugeField a → ℂ)) = I.indicator 1 ↔
      s.pullbackField ⁻¹' I = I := by
  constructor
  · intro h
    ext U
    have h' := congrFun h U
    by_cases h1 : s.pullbackField U ∈ I <;> by_cases h2 : U ∈ I <;>
      simp_all [actOn, Set.indicator]
  · intro h
    funext U
    have h' : s.pullbackField U ∈ I ↔ U ∈ I := by
      conv_rhs => rw [← h]
      rfl
    by_cases h2 : U ∈ I
    · simp [actOn, Set.indicator, h', h2]
    · simp [actOn, Set.indicator, h', h2]
end LatticeSymmetry
def shift (v : LatticePoint a) : LatticeSymmetry a where
  toFun x := x + v
  preservesDist x y := by simp
  image_eq := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact add_mem hy v.2
    · intro hx
      exact ⟨x - v, sub_mem hx v.2, by simp⟩
def IsSymmetricUnder (ν : Measure (GaugeField a)) (s : LatticeSymmetry a) : Prop :=
  ∀ A : GaugeField a → ℂ, IsBoundedObservable A → ∫ U, s.actOn A U ∂ν = ∫ U, A U ∂ν
def IsShiftInvariant (ν : Measure (GaugeField a)) : Prop :=
  ∀ v : LatticePoint a, IsSymmetricUnder ν (shift v)
def IsShiftInvariantSet (I : Set (GaugeField a)) : Prop :=
  MeasurableSet I ∧ ∀ v : LatticePoint a,
    (shift v).actOn (I.indicator (1 : GaugeField a → ℂ)) = I.indicator 1
@[reducible] def shiftInvariantSigma (a : ℝ) : MeasurableSpace (GaugeField a) where
  MeasurableSet' := IsShiftInvariantSet
  measurableSet_empty := ⟨MeasurableSet.empty, fun v =>
    ((shift v).actOn_indicator_eq_iff ∅).mpr rfl⟩
  measurableSet_compl I h := ⟨h.1.compl, fun v =>
    ((shift v).actOn_indicator_eq_iff Iᶜ).mpr (by
      rw [preimage_compl, ((shift v).actOn_indicator_eq_iff I).mp (h.2 v)])⟩
  measurableSet_iUnion f h := ⟨MeasurableSet.iUnion fun i => (h i).1, fun v =>
    ((shift v).actOn_indicator_eq_iff (⋃ i, f i)).mpr (by
      rw [preimage_iUnion]
      exact iUnion_congr fun i =>
        ((shift v).actOn_indicator_eq_iff (f i)).mp ((h i).2 v))⟩
def condExpShiftInvariant (ν : Measure (GaugeField a)) (B : GaugeField a → ℂ) :
    GaugeField a → ℂ :=
  condExp (shiftInvariantSigma a) ν B
def restrictTo (𝓛 : Finset (Link a)) (U : GaugeField a) : 𝓛 → ComplexMatrix2.specialUnitary :=
  fun b => U b
def patch (𝓛 : Finset (Link a)) (v : 𝓛 → ComplexMatrix2.specialUnitary)
    (U : Link a → ComplexMatrix2.specialUnitary) : Link a → ComplexMatrix2.specialUnitary :=
  open Classical in fun b => if h : b ∈ 𝓛 then v ⟨b, h⟩ else U b
def facesTouching (𝓛 : Finset (Link a)) : Set (ElementaryPlaquette a) :=
  {p | ∃ b ∈ p.edges, b ∈ 𝓛}
def boltzmannWeight (β : ℝ) (𝓛 : Finset (Link a)) (U : GaugeField a)
    (v : 𝓛 → ComplexMatrix2.specialUnitary) : ℝ :=
  Real.exp (-β * ∑ᶠ p ∈ facesTouching 𝓛, faceEnergy (patch 𝓛 v U) p)
def partitionFunction (β : ℝ) (𝓛 : Finset (Link a)) (U : GaugeField a) : ℝ :=
  ∫ v, boltzmannWeight β 𝓛 U v ∂ComplexMatrix2.haarPi 𝓛
def wilsonSpecification (β : ℝ) (𝓛 : Finset (Link a)) (U : GaugeField a) :
    Measure (𝓛 → ComplexMatrix2.specialUnitary) :=
  (ENNReal.ofReal (partitionFunction β 𝓛 U))⁻¹ •
    (ComplexMatrix2.haarPi 𝓛).withDensity fun v => ENNReal.ofReal (boltzmannWeight β 𝓛 U v)
@[reducible] def exteriorSigma (𝓛 : Finset (Link a)) : MeasurableSpace (GaugeField a) :=
  linkSigma {b | b ∉ 𝓛 ∧ b.opposite ∉ 𝓛}
def IsGibbs (β : ℝ) (ν : Measure (GaugeField a)) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ 𝓛 : Finset (Link a), (∀ b ∈ 𝓛, b.IsPositivelyOriented) →
    ∀ B : Set (𝓛 → ComplexMatrix2.specialUnitary), MeasurableSet B →
      (fun U => (wilsonSpecification β 𝓛 U B).toReal) =ᵐ[ν]
        condExp (exteriorSigma 𝓛) ν ((restrictTo 𝓛 ⁻¹' B).indicator fun _ => (1 : ℝ))
def IsPeriodicMeasure (ν : Measure (GaugeField a)) : Prop :=
  ∃ H : AddSubgroup (LatticePoint a), H.FiniteIndex ∧ ∀ v ∈ H, IsSymmetricUnder ν (shift v)
def IsPeriodicGibbs (β : ℝ) (ν : Measure (GaugeField a)) : Prop :=
  IsGibbs β ν ∧ IsPeriodicMeasure ν
def IsExtremalPeriodicGibbs (β : ℝ) (ν : Measure (GaugeField a)) : Prop :=
  IsPeriodicGibbs β ν ∧ ∀ ν₁ ν₂ : Measure (GaugeField a),
    IsPeriodicGibbs β ν₁ → IsPeriodicGibbs β ν₂ → ∀ t : ℝ, 0 < t → t < 1 →
      ν = ENNReal.ofReal t • ν₁ + ENNReal.ofReal (1 - t) • ν₂ → ν₁ = ν ∧ ν₂ = ν
def smearedEnergyCumulant {n : ℕ} (ν : Measure (GaugeField a)) (f : Fin n → AmbientSpace → ℝ) : ℂ :=
  Cumulants.mixedCumulant ν fun i U => smearedEnergy (f i) U
def projectPoint (L m : ℕ) (j : ℤ) (x : LatticePoint (PeriodicLattice.meshSize L j)) :
    PeriodicLattice.Site L m j :=
  ⟨TorusMetric.torusProj (PeriodicLattice.torusSide L m) x, by
    obtain ⟨n, hn⟩ := x.2
    exact ⟨n, fun μ => by simp [TorusMetric.torusProj, hn]⟩⟩
theorem projectPoint_sub (L m : ℕ) (j : ℤ) (x y : LatticePoint (PeriodicLattice.meshSize L j)) :
    projectPoint L m j (x - y) = projectPoint L m j x - projectPoint L m j y := by
  refine Subtype.ext (funext fun μ => ?_)
  simp [projectPoint, TorusMetric.torusProj]
theorem projectPoint_neg (L m : ℕ) (j : ℤ) (x : LatticePoint (PeriodicLattice.meshSize L j)) :
    projectPoint L m j (-x) = -projectPoint L m j x := by
  refine Subtype.ext (funext fun μ => ?_)
  simp [projectPoint, TorusMetric.torusProj]
theorem projectPoint_axisStep (L m : ℕ) (j : ℤ) (μ : Fin 4) :
    projectPoint L m j (axisStep _ μ) = PeriodicLattice.unitStep L m j μ := by
  refine Subtype.ext (funext fun ν => ?_)
  by_cases h : ν = μ
  · subst h
    simp [projectPoint, TorusMetric.torusProj, axisStep, PeriodicLattice.unitStep,
      PeriodicLattice.pointOnAxis]
  · simp [projectPoint, TorusMetric.torusProj, axisStep, PeriodicLattice.unitStep,
      PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
def projectLink (L m : ℕ) (j : ℤ) (b : Link (PeriodicLattice.meshSize L j)) :
    PeriodicLattice.Bond L m j where
  source := projectPoint L m j b.initial
  target := projectPoint L m j b.terminal
  isNeighbour := by
    obtain ⟨μ, h | h⟩ := b.isAdjacent
    · exact ⟨μ, Or.inl (by rw [← projectPoint_sub, h, projectPoint_axisStep])⟩
    · exact ⟨μ, Or.inr (by rw [← projectPoint_sub, h, projectPoint_neg, projectPoint_axisStep])⟩
theorem specialUnitary_coe_inv (x : ComplexMatrix2.specialUnitary) :
    ((x⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = (x : ComplexMatrix2)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  have h : x * x⁻¹ = 1 := mul_inv_cancel x
  exact congrArg Subtype.val h
def liftField (L m : ℕ) (j : ℤ) (U : PeriodicLattice.Bond L m j → ComplexMatrix2) :
    GaugeField (PeriodicLattice.meshSize L j) :=
  open Classical in
  if h : U ∈ PeriodicLattice.compactGaugeFields L m j then
    ⟨fun b => ⟨U (projectLink L m j b), h.1 _ (mem_univ _)⟩, fun b => Subtype.ext (by
      rw [specialUnitary_coe_inv]
      exact h.2 (projectLink L m j b) (mem_univ _))⟩
  else ⟨fun _ => 1, fun _ => by simp⟩
def periodicFields (L m : ℕ) (j : ℤ) : Set (GaugeField (PeriodicLattice.meshSize L j)) :=
  {U | ∀ v : LatticePoint (PeriodicLattice.meshSize L j),
    (∃ n : Fin 4 → ℤ, ∀ μ, (v : AmbientSpace) μ = (n μ : ℝ) * PeriodicLattice.torusSide L m) →
      (shift v).pullbackField U = U}
def liftedWilsonMeasure (L m K : ℕ) (β : ℝ) :
    Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ))) :=
  (PeriodicLattice.wilsonGibbsMeasure L m K β).map (liftField L m (K : ℤ))
def IsWeakSubsequentialLimit {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (ν : Measure Ω) : Prop :=
  IsProbabilityMeasure ν ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ F : BoundedContinuousFunction Ω ℝ,
    Tendsto (fun n => ∫ x, F x ∂μ (φ n)) atTop (𝓝 (∫ x, F x ∂ν))
def IsInfiniteVolumeLimit (L K : ℕ) (β : ℝ)
    (ν : Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) : Prop :=
  IsWeakSubsequentialLimit (fun m => liftedWilsonMeasure L m K β) ν
def hyperplaneReflect (n : AmbientSpace) (c : ℝ) (x : AmbientSpace) : AmbientSpace :=
  x - (2 * (n ⬝ᵥ x - c) / (n ⬝ᵥ n)) • n
theorem dotProduct_hyperplaneReflect_sub {n : AmbientSpace} (hn : n ⬝ᵥ n ≠ 0) (c : ℝ)
    (x : AmbientSpace) :
    n ⬝ᵥ hyperplaneReflect n c x - c = -(n ⬝ᵥ x - c) := by
  simp only [hyperplaneReflect, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  field_simp
  ring
theorem hyperplaneReflect_hyperplaneReflect {n : AmbientSpace} (hn : n ⬝ᵥ n ≠ 0) (c : ℝ)
    (x : AmbientSpace) :
    hyperplaneReflect n c (hyperplaneReflect n c x) = x := by
  have h := dotProduct_hyperplaneReflect_sub hn c x
  change hyperplaneReflect n c x - (2 * (n ⬝ᵥ hyperplaneReflect n c x - c) / (n ⬝ᵥ n)) • n = x
  rw [h]
  simp only [hyperplaneReflect]
  funext μ
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem euclidNormVec_hyperplaneReflect_sub {n : AmbientSpace} (hn : n ⬝ᵥ n ≠ 0) (c : ℝ)
    (x y : AmbientSpace) :
    TorusMetric.euclidNormVec (hyperplaneReflect n c x - hyperplaneReflect n c y) =
      TorusMetric.euclidNormVec (x - y) := by
  unfold TorusMetric.euclidNormVec
  congr 1
  set d := x - y with hd
  set t := 2 * (n ⬝ᵥ d) / (n ⬝ᵥ n) with ht
  have hdiff : ∀ μ, (hyperplaneReflect n c x - hyperplaneReflect n c y) μ = d μ - t * n μ := by
    intro μ
    have hdot : n ⬝ᵥ d = n ⬝ᵥ x - n ⬝ᵥ y := by rw [hd, dotProduct_sub]
    have hdμ : d μ = x μ - y μ := rfl
    rw [ht, hdot, hdμ]
    simp only [hyperplaneReflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hD : n ⬝ᵥ d = ∑ μ, n μ * d μ := rfl
  have hN : n ⬝ᵥ n = ∑ μ, n μ * n μ := rfl
  calc ∑ μ, (hyperplaneReflect n c x - hyperplaneReflect n c y) μ ^ 2
      = ∑ μ, (d μ - t * n μ) ^ 2 := Finset.sum_congr rfl fun μ _ => by rw [hdiff]
    _ = ∑ μ, d μ ^ 2 - 2 * t * (n ⬝ᵥ d) + t ^ 2 * (n ⬝ᵥ n) := by
        rw [hD, hN]
        simp only [Fin.sum_univ_four]
        ring
    _ = ∑ μ, d μ ^ 2 := by
        rw [ht]
        field_simp
        ring
inductive ReflectionClass where
  | axial (μ : Fin 4)
  | diagonal (μ ν : Fin 4) (lt : μ < ν) (sign : ℤˣ)
namespace ReflectionClass
def intNormal : ReflectionClass → Fin 4 → ℤ
  | axial μ => Pi.single μ 1
  | diagonal μ ν _ s => Pi.single μ 1 + (s : ℤ) • Pi.single ν 1
def realNormal (F : ReflectionClass) : AmbientSpace := fun κ => (F.intNormal κ : ℝ)
def IsAdmissibleLevel (a : ℝ) (c : ℝ) : ReflectionClass → Prop
  | axial _ => ∃ q : ℤ, c = (q : ℝ) * (a / 2)
  | diagonal _ _ _ _ => ∃ q : ℤ, c = (q : ℝ) * a
theorem realNormal_dot_axial (μ : Fin 4) :
    (axial μ).realNormal ⬝ᵥ (axial μ).realNormal = 1 := by
  fin_cases μ <;> simp [realNormal, intNormal, dotProduct, Fin.sum_univ_four]
theorem realNormal_dot_diagonal (μ ν : Fin 4) (lt : μ < ν) (s : ℤˣ) :
    (diagonal μ ν lt s).realNormal ⬝ᵥ (diagonal μ ν lt s).realNormal = 2 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> fin_cases μ <;> fin_cases ν <;>
    first
    | exact absurd lt (by decide)
    | (simp [realNormal, intNormal, dotProduct, Fin.sum_univ_four]; try norm_num)
theorem realNormal_dot_ne_zero (F : ReflectionClass) : F.realNormal ⬝ᵥ F.realNormal ≠ 0 := by
  cases F with
  | axial μ => rw [realNormal_dot_axial]; norm_num
  | diagonal μ ν lt s => rw [realNormal_dot_diagonal]; norm_num
end ReflectionClass
structure LatticeMirror (a : ℝ) where
  cls : ReflectionClass
  level : ℝ
  level_mem : cls.IsAdmissibleLevel a level
namespace LatticeMirror
def plane (P : LatticeMirror a) : Set AmbientSpace := {x | P.cls.realNormal ⬝ᵥ x = P.level}
def ContainsSites (P : LatticeMirror a) : Prop := ∃ q : ℤ, P.level = (q : ℝ) * a
def BisectsLinks (P : LatticeMirror a) : Prop := ∃ q : ℤ, P.level = ((q : ℝ) + 1 / 2) * a
theorem reflect_mem (P : LatticeMirror a) {x : AmbientSpace} (hx : x ∈ latticeSubgroup a) :
    hyperplaneReflect P.cls.realNormal P.level x ∈ latticeSubgroup a := by
  obtain ⟨p, hp⟩ := hx
  have hdot : P.cls.realNormal ⬝ᵥ x = ((∑ κ, P.cls.intNormal κ * p κ : ℤ) : ℝ) * a := by
    simp only [dotProduct, ReflectionClass.realNormal, hp]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun κ _ => by ring
  set I : ℤ := ∑ κ, P.cls.intNormal κ * p κ with hI
  obtain ⟨t, ht⟩ : ∃ t : ℤ, 2 * (P.cls.realNormal ⬝ᵥ x - P.level) /
      (P.cls.realNormal ⬝ᵥ P.cls.realNormal) = (t : ℝ) * a := by
    obtain ⟨F, c, hc⟩ := P
    cases F with
    | axial μ =>
      obtain ⟨q, rfl⟩ := hc
      refine ⟨2 * I - q, ?_⟩
      rw [ReflectionClass.realNormal_dot_axial, hdot]
      push_cast
      ring
    | diagonal μ ν lt s =>
      obtain ⟨q, rfl⟩ := hc
      refine ⟨I - q, ?_⟩
      rw [ReflectionClass.realNormal_dot_diagonal, hdot]
      push_cast
      ring
  refine ⟨p - t • P.cls.intNormal, fun μ => ?_⟩
  simp only [hyperplaneReflect, ht, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hp,
    ReflectionClass.realNormal]
  push_cast
  ring
def symmetry (P : LatticeMirror a) : LatticeSymmetry a where
  toFun := hyperplaneReflect P.cls.realNormal P.level
  preservesDist := euclidNormVec_hyperplaneReflect_sub P.cls.realNormal_dot_ne_zero P.level
  image_eq := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact P.reflect_mem hy
    · intro hx
      exact ⟨_, P.reflect_mem hx,
        hyperplaneReflect_hyperplaneReflect P.cls.realNormal_dot_ne_zero P.level x⟩
def conjReflect (P : LatticeMirror a) (A : GaugeField a → ℂ) : GaugeField a → ℂ :=
  fun U => conj (P.symmetry.actOn A U)
def IsHalfSpace (P : LatticeMirror a) (H : Set AmbientSpace) : Prop :=
  H = {x | P.level ≤ P.cls.realNormal ⬝ᵥ x} ∨ H = {x | P.cls.realNormal ⬝ᵥ x ≤ P.level}
end LatticeMirror
def ReflectionClass.mirrors (a : ℝ) (F : ReflectionClass) : Set (LatticeMirror a) := {P | P.cls = F}
structure PeriodicMirror (L m : ℕ) (j : ℤ) where
  axis : Fin 4
  level : ℝ
  level_mem : ∃ q : ℤ, level = (q : ℝ) * (PeriodicLattice.meshSize L j / 2)
namespace PeriodicMirror
variable {L m : ℕ} {j : ℤ}
def planes (P : PeriodicMirror L m j) : Set (PeriodicLattice.FourTorus L m) :=
  TorusMetric.torusProj (PeriodicLattice.torusSide L m) ''
    ({x | x P.axis = P.level} ∪
      {x | x P.axis = P.level + PeriodicLattice.torusSide L m / 2})
def reflectPoint (P : PeriodicMirror L m j) (x : PeriodicLattice.FourTorus L m) :
    PeriodicLattice.FourTorus L m :=
  Function.update x P.axis (((2 * P.level : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) -
    x P.axis)
def reflectEquiv (P : PeriodicMirror L m j) :
    PeriodicLattice.FourTorus L m ≃ PeriodicLattice.FourTorus L m :=
  Function.Involutive.toPerm P.reflectPoint fun x => by
    funext ν
    by_cases h : ν = P.axis
    · subst h
      simp [reflectPoint]
    · simp [reflectPoint, Function.update_of_ne h]
theorem reflectEquiv_torusProj (P : PeriodicMirror L m j) (x : AmbientSpace) :
    P.reflectEquiv (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L m)
        (x - (2 * (x P.axis - P.level)) • Pi.single P.axis 1) := by
  funext ν
  change P.reflectPoint (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x) ν = _
  by_cases h : ν = P.axis
  · subst h
    simp only [reflectPoint, Function.update_self, TorusMetric.torusProj, Pi.sub_apply,
      Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    rw [← AddCircle.coe_sub]
    congr 1
    ring
  · simp [reflectPoint, Function.update_of_ne h, TorusMetric.torusProj, Pi.single_eq_of_ne h]
def IsHalf (P : PeriodicMirror L m j) (H : Set (PeriodicLattice.FourTorus L m)) : Prop :=
  ∃ x ∈ P.planesᶜ, H = closure (connectedComponentIn P.planesᶜ x)
end PeriodicMirror
def IsReflectionPositiveAt (ν : Measure (GaugeField a)) (P : LatticeMirror a) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ H, P.IsHalfSpace H → ∀ A : GaugeField a → ℂ,
    IsBoundedObservable A → IsLocalObservable A → IsRegionMeasurable H A →
      0 ≤ ∫ U, A U * P.conjReflect A U ∂ν
def IsReflectionPositiveOn (ν : Measure (GaugeField a)) (𝓕 : Set (LatticeMirror a)) : Prop :=
  ∀ P ∈ 𝓕, IsReflectionPositiveAt ν P
def IsPeriodicObservable {L m : ℕ} {j : ℤ} (A : (PeriodicLattice.Bond L m j → ComplexMatrix2) → ℂ) :
    Prop :=
  Measurable A ∧ ∃ C : ℝ, ∀ U ∈ PeriodicLattice.compactGaugeFields L m j, ‖A U‖ ≤ C
end InfiniteLattice
end YangMills.Construction
