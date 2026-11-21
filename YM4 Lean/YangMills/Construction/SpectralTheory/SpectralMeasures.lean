import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction
namespace SpectralTheory
section Operators
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
def IsContractive (T : H →L[ℂ] K) : Prop :=
  ‖T‖ ≤ 1
def TendstoStrongly {ι : Type*} (l : Filter ι) (T : ι → H →L[ℂ] K) (T₀ : H →L[ℂ] K) : Prop :=
  ∀ v : H, Tendsto (fun i => T i v) l (𝓝 (T₀ v))
def StronglyContinuous {X : Type*} [TopologicalSpace X] (T : X → H →L[ℂ] K) : Prop :=
  ∀ v : H, Continuous fun x => T x v
structure IsOperatorSemigroup (S : ℝ≥0 → H →L[ℂ] H) : Prop where
  map_zero : S 0 = 1
  map_add : ∀ s t, S (s + t) = S s * S t
structure IsAddUnitaryRep {G : Type*} [AddGroup G] (U : G → H →L[ℂ] H) :
    Prop where
  map_zero : U 0 = 1
  map_add : ∀ g h, U (g + h) = U g * U h
  isUnitary : ∀ g, ∃ W : H ≃ₗᵢ[ℂ] H, ∀ v, U g v = W v
abbrev UnboundedOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Type _ :=
  H →ₗ.[ℂ] H
theorem unboundedOperator_eq_iff (A B : UnboundedOperator H) :
    A = B ↔ A.domain = B.domain ∧
      ∀ (x : A.domain) (y : B.domain), (x : H) = y → A x = B y := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun x y h => congrArg A (Subtype.ext h)⟩
  · rintro ⟨hd, hv⟩
    exact LinearPMap.ext hd fun x hx hy => hv ⟨x, hx⟩ ⟨x, hy⟩ rfl
def unitaryConj (W : H ≃ₗᵢ[ℂ] K) (A : UnboundedOperator H) : UnboundedOperator K where
  domain := A.domain.map W.toLinearEquiv.toLinearMap
  toFun := W.toLinearEquiv.toLinearMap ∘ₗ A.toFun ∘ₗ
    (W.toLinearEquiv.submoduleMap A.domain).symm.toLinearMap
theorem unitaryConj_apply (W : H ≃ₗᵢ[ℂ] K) (A : UnboundedOperator H) (v : A.domain)
    (hv : W v ∈ (unitaryConj W A).domain) : unitaryConj W A ⟨W v, hv⟩ = W (A v) := by
  have hsymm : (W.toLinearEquiv.submoduleMap A.domain).symm ⟨W v, hv⟩ = v :=
    (LinearEquiv.symm_apply_eq _).mpr (Subtype.ext rfl)
  change W (A.toFun ((W.toLinearEquiv.submoduleMap A.domain).symm ⟨W v, hv⟩)) = W (A v)
  rw [hsymm]
  rfl
def LoewnerGe (A B : H →L[ℂ] H) : Prop :=
  ∀ v : H, 0 ≤ ⟪v, (A - B) v⟫_ℂ
end Operators
abbrev BorelSets (n : ℕ) : Type := {S : Set (Fin n → ℝ) // MeasurableSet S}
structure ProjectionMeasure (n : ℕ) [NeZero n] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  toFun : BorelSets n → H →L[ℂ] H
  isStarProjection : ∀ S, IsStarProjection (toFun S)
  map_empty : toFun ⟨∅, MeasurableSet.empty⟩ = 0
  map_univ : toFun ⟨univ, MeasurableSet.univ⟩ = 1
  map_inter : ∀ S T : BorelSets n, toFun ⟨S.1 ∩ T.1, S.2.inter T.2⟩ = toFun S * toFun T
  tendsto_sum : ∀ S : ℕ → BorelSets n, (Pairwise fun i j => Disjoint (S i).1 (S j).1) →
    ∀ v : H, Tendsto (fun N => ∑ i ∈ Finset.range N, toFun (S i) v) atTop
      (𝓝 (toFun ⟨⋃ i, (S i).1, MeasurableSet.iUnion fun i => (S i).2⟩ v))
namespace ProjectionMeasure
variable {n : ℕ} [NeZero n] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
instance : CoeFun (ProjectionMeasure n H) fun _ => BorelSets n → H →L[ℂ] H := ⟨toFun⟩
def spectralValue (P : ProjectionMeasure n H) (v : H) (S : BorelSets n) : ℂ :=
  ⟪v, P S v⟫_ℂ
def spectralPairing (P : ProjectionMeasure n H) (u v : H) (S : BorelSets n) : ℂ :=
  ⟪u, P S v⟫_ℂ
theorem spectralValue_eq_norm_sq (P : ProjectionMeasure n H) (v : H) (S : BorelSets n) :
    P.spectralValue v S = ((‖P S v‖ ^ 2 : ℝ) : ℂ) := by
  have hproj := P.isStarProjection S
  have hidem : P S (P S v) = P S v :=
    congrArg (fun T : H →L[ℂ] H => T v) hproj.isIdempotentElem.eq
  have hsym : ⟪P S v, P S v⟫_ℂ = ⟪v, P S (P S v)⟫_ℂ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hproj.isSelfAdjoint v (P S v)
  rw [spectralValue, ← hidem, ← hsym, hidem, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
def spectralValueMeasure (P : ProjectionMeasure n H) (v : H) : Measure (Fin n → ℝ) :=
  Measure.ofMeasurable (fun S hS => ENNReal.ofReal (‖P ⟨S, hS⟩ v‖ ^ 2))
    (by
      rw [P.map_empty]
      simp)
    (by
      intro f hf hdisj
      have hlim := P.tendsto_sum (fun i => ⟨f i, hf i⟩) hdisj v
      have hcont : Continuous fun w : H => (⟪v, w⟫_ℂ).re := by fun_prop
      have hre_lim := (hcont.tendsto _).comp hlim
      have hre : ∀ S : BorelSets n, (⟪v, P S v⟫_ℂ).re = ‖P S v‖ ^ 2 := fun S => by
        have hval := congrArg Complex.re (P.spectralValue_eq_norm_sq v S)
        rw [Complex.ofReal_re] at hval
        exact hval
      have hnorm : Tendsto (fun N => ∑ i ∈ Finset.range N, ‖P ⟨f i, hf i⟩ v‖ ^ 2) atTop
          (𝓝 (‖P ⟨⋃ i, f i, MeasurableSet.iUnion hf⟩ v‖ ^ 2)) := by
        rw [← hre]
        refine hre_lim.congr fun N => ?_
        simp only [Function.comp_apply, inner_sum, Complex.re_sum]
        exact Finset.sum_congr rfl fun i _ => hre _
      have hsum := (hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity) _).2 hnorm
      rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsum.summable])
theorem spectralValueMeasure_apply (P : ProjectionMeasure n H) (v : H) (S : BorelSets n) :
    P.spectralValueMeasure v S.1 = ENNReal.ofReal (‖P S v‖ ^ 2) :=
  Measure.ofMeasurable_apply S.1 S.2
theorem spectralValue_eq_spectralValueMeasure (P : ProjectionMeasure n H) (v : H) (S : BorelSets n) :
    P.spectralValue v S = (((P.spectralValueMeasure v S.1).toReal : ℝ) : ℂ) := by
  rw [spectralValueMeasure_apply, ENNReal.toReal_ofReal (by positivity), spectralValue_eq_norm_sq]
def VanishesOn (P : ProjectionMeasure n H) (S : BorelSets n) : Prop :=
  P S = 0
def IsConcentratedOn (P : ProjectionMeasure n H) (C : BorelSets n) : Prop :=
  P.VanishesOn ⟨C.1ᶜ, C.2.compl⟩
def support (P : ProjectionMeasure n H) : Set (Fin n → ℝ) :=
  (⋃₀ {U | ∃ hU : IsOpen U, P.VanishesOn ⟨U, hU.measurableSet⟩})ᶜ
end ProjectionMeasure
abbrev BorelSubsets {n : ℕ} (Y : BorelSets n) : Type :=
  {S : Set (Fin n → ℝ) // MeasurableSet S ∧ S ⊆ Y.1}
structure SpectralMeasureOn {n : ℕ} [NeZero n] (Y : BorelSets n) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  toFun : BorelSubsets Y → H →L[ℂ] H
  isStarProjection : ∀ S, IsStarProjection (toFun S)
  map_empty : toFun ⟨∅, MeasurableSet.empty, empty_subset _⟩ = 0
  map_whole : toFun ⟨Y.1, Y.2, Subset.rfl⟩ = 1
  map_inter : ∀ S T : BorelSubsets Y,
    toFun ⟨S.1 ∩ T.1, S.2.1.inter T.2.1, inter_subset_left.trans S.2.2⟩ = toFun S * toFun T
  tendsto_sum : ∀ S : ℕ → BorelSubsets Y, (Pairwise fun i j => Disjoint (S i).1 (S j).1) →
    ∀ v : H, Tendsto (fun N => ∑ i ∈ Finset.range N, toFun (S i) v) atTop
      (𝓝 (toFun ⟨⋃ i, (S i).1, MeasurableSet.iUnion fun i => (S i).2.1,
        iUnion_subset fun i => (S i).2.2⟩ v))
namespace SpectralMeasureOn
variable {n : ℕ} [NeZero n] {Y : BorelSets n} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]
instance : CoeFun (SpectralMeasureOn Y H) fun _ => BorelSubsets Y → H →L[ℂ] H := ⟨toFun⟩
def restrictSet (Y : BorelSets n) (S : BorelSets n) : BorelSubsets Y :=
  ⟨S.1 ∩ Y.1, S.2.inter Y.2, inter_subset_right⟩
def extend (P : SpectralMeasureOn Y H) : ProjectionMeasure n H where
  toFun S := P (restrictSet Y S)
  isStarProjection S := P.isStarProjection _
  map_empty := by
    have he : restrictSet Y ⟨∅, MeasurableSet.empty⟩ = ⟨∅, MeasurableSet.empty, empty_subset _⟩ :=
      Subtype.ext (empty_inter _)
    rw [he, P.map_empty]
  map_univ := by
    have hu : restrictSet Y ⟨univ, MeasurableSet.univ⟩ = ⟨Y.1, Y.2, Subset.rfl⟩ :=
      Subtype.ext (univ_inter _)
    rw [hu, P.map_whole]
  map_inter S T := by
    rw [← P.map_inter]
    exact congrArg P (Subtype.ext (inter_inter_distrib_right _ _ _))
  tendsto_sum S hS v := by
    have hun : restrictSet Y ⟨⋃ i, (S i).1, MeasurableSet.iUnion fun i => (S i).2⟩ =
        ⟨⋃ i, (restrictSet Y (S i)).1, MeasurableSet.iUnion fun i => (restrictSet Y (S i)).2.1,
          iUnion_subset fun i => (restrictSet Y (S i)).2.2⟩ :=
      Subtype.ext (iUnion_inter _ _)
    rw [hun]
    exact P.tendsto_sum (fun i => restrictSet Y (S i))
      (fun i j hij => (hS hij).mono inter_subset_left inter_subset_left) v
theorem extend_apply (P : SpectralMeasureOn Y H) (S : BorelSets n) :
    P.extend S = P (restrictSet Y S) :=
  rfl
theorem extend_isConcentratedOn (P : SpectralMeasureOn Y H) : P.extend.IsConcentratedOn Y := by
  have hc : restrictSet Y ⟨Y.1ᶜ, Y.2.compl⟩ = ⟨∅, MeasurableSet.empty, empty_subset _⟩ :=
    Subtype.ext (compl_inter_self _)
  change P (restrictSet Y ⟨Y.1ᶜ, Y.2.compl⟩) = 0
  rw [hc, P.map_empty]
end SpectralMeasureOn
section Functions
variable {n : ℕ}
def IsSimpleBorel (g : (Fin n → ℝ) → ℂ) : Prop :=
  Measurable g ∧ (range g).Finite
variable [NeZero n] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def simpleIntegral (P : ProjectionMeasure n H) (g : (Fin n → ℝ) → ℂ) (hg : IsSimpleBorel g) :
    H →L[ℂ] H :=
  ∑ z ∈ hg.2.toFinset, z • P ⟨g ⁻¹' {z}, hg.1 (measurableSet_singleton z)⟩
def functionalDomain (P : ProjectionMeasure n H) (f : (Fin n → ℝ) → ℂ) : Set H :=
  {v | ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(P.spectralValueMeasure v) < ∞}
end Functions
end SpectralTheory
end YangMills.Construction
