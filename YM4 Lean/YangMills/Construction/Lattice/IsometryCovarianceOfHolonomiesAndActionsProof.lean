import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeAtOneSpacingProof
import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairsProof
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.Lattice.CovarianceOfComplexContourVariablesProof
import YangMills.Construction.Lattice.ElementaryBoundsOfOneStepProof
import YangMills.Construction.Lattice.IsometryCarriesTheObjectsOfTheAverageProof
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActions
import YangMills.Construction.Lattice.TreeOfALocalisationDomainProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.PeriodicLattice.IsometryCovariance
variable {L m : ℕ} {j : ℤ}
theorem bond_ext_of_endpoints {b b' : Bond L m j} (hs : (b.source : FourTorus L m) = b'.source)
    (ht : (b.target : FourTorus L m) = b'.target) : b = b' :=
  Bond.ext (Subtype.ext hs) (Subtype.ext ht)
section
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem bondImage_source (h : MapsCellsAndCubes σ j) (b : Bond L m j) :
    ((bondImage σ b).source : FourTorus L m) = σ b.source := (h.2.2.2.1 b).1
theorem bondImage_target (h : MapsCellsAndCubes σ j) (b : Bond L m j) :
    ((bondImage σ b).target : FourTorus L m) = σ b.target := (h.2.2.2.1 b).2
theorem bondPreimage_source (h : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    ((bondPreimage σ b).source : FourTorus L m) = σ.symm b.source := (h.2.2.2.1 b).1
theorem bondPreimage_target (h : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    ((bondPreimage σ b).target : FourTorus L m) = σ.symm b.target := (h.2.2.2.1 b).2
theorem bondPreimage_bondImage (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    bondPreimage σ (bondImage σ b) = b := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.bondPreimage_bondImage <;> assumption
theorem bondImage_opposite (h : MapsCellsAndCubes σ j) (b : Bond L m j) :
    bondImage σ b.opposite = (bondImage σ b).opposite :=
  bond_ext_of_endpoints (by rw [bondImage_source h]; exact (bondImage_target h b).symm)
    (by rw [bondImage_target h]; exact (bondImage_source h b).symm)
theorem bondImage_injective (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) :
    Function.Injective (bondImage σ : Bond L m j → Bond L m j) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.bondImage_injective <;> assumption
theorem transportGaugeField_bondImage (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (U : Bond L m j → ComplexMatrix2) (b : Bond L m j) :
    transportGaugeField σ U (bondImage σ b) = U b := by
  simp only [transportGaugeField, bondPreimage_bondImage h h']
theorem pathHolonomy_pathImage (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (U : Bond L m j → ComplexMatrix2)
    (Γ : List (Bond L m j)) :
    pathHolonomy (transportGaugeField σ U) (pathImage σ Γ) = pathHolonomy U Γ := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.pathHolonomy_transport_pathImage <;> assumption
theorem carriesHolonomies_of_maps (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (ℬ : Set (Bond L m j))
    (U : Bond L m j → ComplexMatrix2) (hℬ : IsReversalClosed ℬ)
    (hU : IsGaugeField compactGaugeGroup ℬ U) :
    CarriesHolonomies σ ℬ U := by
  refine ⟨?_, ⟨?_, ?_⟩, fun Γ _ _ => pathHolonomy_pathImage h h' U Γ⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact ⟨b.opposite, hℬ b hb, bondImage_opposite h b⟩
  · rintro _ ⟨b, hb, rfl⟩
    rw [transportGaugeField_bondImage h h']
    exact hU.1 b hb
  · rintro _ ⟨b, hb, rfl⟩
    rw [← bondImage_opposite h, transportGaugeField_bondImage h h',
      transportGaugeField_bondImage h h']
    exact hU.2 b hb
end
theorem toFourTorus_add (x y : Fin 4 → ℝ) :
    toFourTorus L m (x + y) = toFourTorus L m x + toFourTorus L m y := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.torusProj_add <;> assumption
theorem toFourTorus_surjective : Function.Surjective (toFourTorus L m) := by
  intro z
  choose f hf using fun μ => QuotientAddGroup.mk_surjective (z μ)
  exact ⟨f, funext hf⟩
theorem pointOnAxis_eq_toFourTorus (μ : Fin 4) (t : ℝ) :
    pointOnAxis L m μ t = toFourTorus L m (Pi.single μ t) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [pointOnAxis, toFourTorus]
  · simp [pointOnAxis, toFourTorus, Pi.single_eq_of_ne h]
theorem pointOnAxis_add (μ : Fin 4) (s t : ℝ) :
    pointOnAxis L m μ (s + t) = pointOnAxis L m μ s + pointOnAxis L m μ t := by apply _root_.YangMills.Construction.TorusBound.LocalisationDomainTree.pointOnAxis_add <;> assumption
theorem pointOnAxis_neg (μ : Fin 4) (t : ℝ) :
    pointOnAxis L m μ (-t) = -pointOnAxis L m μ t := by apply _root_.YangMills.Construction.CellGrid.pointOnAxis_neg <;> assumption
theorem pointOnAxis_units_mul (μ : Fin 4) (c : ℤˣ) (t : ℝ) :
    pointOnAxis L m μ (((c : ℤ) : ℝ) * t) = (c : ℤ) • pointOnAxis L m μ t := by
  rcases Int.units_eq_one_or c with rfl | rfl
  · simp
  · simp [pointOnAxis_neg]
theorem actOnVector_add (r : SignedFrame) (x y : Fin 4 → ℝ) :
    r.actOnVector (x + y) = r.actOnVector x + r.actOnVector y := by apply _root_.YangMills.Construction.AffineTorusIsometries.signedFrame_act_add <;> assumption
theorem actOnVector_single (r : SignedFrame) (μ : Fin 4) (t : ℝ) :
    r.actOnVector (Pi.single μ t) =
      Pi.single (r.1.symm μ) (((r.2 (r.1.symm μ) : ℤ) : ℝ) * t) := by
  funext κ
  by_cases h : κ = r.1.symm μ
  · subst h
    simp [SignedFrame.actOnVector]
  · have h' : r.1 κ ≠ μ := fun e => h (by rw [← e]; simp)
    simp [SignedFrame.actOnVector, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
theorem apply_add_toFourTorus {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame}
    {v : Fin 4 → ℝ} (hind : IsInducedByAffine σ r v) (y : FourTorus L m) (w : Fin 4 → ℝ) :
    σ (y + toFourTorus L m w) = σ y + toFourTorus L m (r.actOnVector w) := by apply _root_.YangMills.Construction.AffineTorusIsometries.induced_add_torusProj <;> assumption
theorem apply_add_pointOnAxis {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame}
    {v : Fin 4 → ℝ} (hind : IsInducedByAffine σ r v) (y : FourTorus L m) (μ : Fin 4) (t : ℝ) :
    σ (y + pointOnAxis L m μ t) =
      σ y + (r.2 (r.1.symm μ) : ℤ) • pointOnAxis L m (r.1.symm μ) t := by
  rw [pointOnAxis_eq_toFourTorus, apply_add_toFourTorus hind, actOnVector_single,
    ← pointOnAxis_eq_toFourTorus, pointOnAxis_units_mul]
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem torusSide_eq_mul_meshSize (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    ∃ d : ℕ, torusSide L m = 2 * (L : ℝ) ^ d * meshSize L j := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryImages.torusSide_eq_pow_mul <;> assumption
theorem half_meshSize_ne_multiple (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (n : ℤ) :
    ((meshSize L j / 2 : ℝ) : AddCircle (torusSide L m)) ≠ ((n : ℝ) * meshSize L j : ℝ) := by
  intro h
  obtain ⟨d, hd⟩ := torusSide_eq_mul_meshSize (m := m) hL hj
  obtain ⟨t, ht⟩ := (QuotientAddGroup.eq).1 h
  have ha := (meshSize_pos hL j).ne'
  have ht' : (t : ℝ) * (2 * (L : ℝ) ^ d * meshSize L j) =
      -(meshSize L j / 2) + (n : ℝ) * meshSize L j := by
    rw [← hd, ← ht]
    simp
  have e : (4 * (t * (L : ℤ) ^ d) : ℤ) = 2 * n - 1 := by
    have : (4 * ((t : ℝ) * (L : ℝ) ^ d)) = 2 * (n : ℝ) - 1 := by
      apply mul_right_cancel₀ ha
      linear_combination 2 * ht'
    exact_mod_cast this
  generalize t * (L : ℤ) ^ d = w at e
  omega
theorem axis_eq_of_half_shift (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {b x : FourTorus L m}
    (hb : b ∈ sublattice L m j) (hx : x ∈ sublattice L m j) {f' g' f g : Fin 4} (hfg' : f' ≠ g')
    (c₁ c₂ : ℤˣ)
    (h : b + pointOnAxis L m f' (meshSize L j / 2) + pointOnAxis L m g' (meshSize L j / 2) =
      x + (c₁ : ℤ) • pointOnAxis L m f (meshSize L j / 2) +
        (c₂ : ℤ) • pointOnAxis L m g (meshSize L j / 2)) :
    f' = f ∨ f' = g := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨n₁, hn₁⟩ := hb
  obtain ⟨n₂, hn₂⟩ := hx
  have e := congrFun h f'
  simp only [Pi.add_apply, Pi.smul_apply, pointOnAxis, Pi.single_eq_same,
    Pi.single_eq_of_ne hfg', Pi.single_eq_of_ne hne.1, Pi.single_eq_of_ne hne.2, smul_zero,
    add_zero, hn₁ f', hn₂ f'] at e
  apply half_meshSize_ne_multiple (m := m) hL hj (n₂ f' - n₁ f')
  have e' : ((meshSize L j / 2 : ℝ) : AddCircle (torusSide L m)) =
      (((n₂ f' : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) -
        (((n₁ f' : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
    rw [← e]
    abel
  rw [e', ← AddCircle.coe_sub]
  congr 1
  push_cast
  ring
theorem barycenter_injective (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {p p' : Plaquette L m j}
    (h : p.barycenter = p'.barycenter) : p = p' := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryImages.eq_of_barycenter_eq <;> assumption
def parallelogramVertex {T : Type*} [Add T] (x A B : T) (k : Fin 4) : T :=
  ![x, x + A, x + A + B, x + B] k
def vertex (p : Plaquette L m j) : Fin 4 → FourTorus L m :=
  parallelogramVertex (p.origin : FourTorus L m) (pointOnAxis L m p.firstAxis (meshSize L j))
    (pointOnAxis L m p.secondAxis (meshSize L j))
def boundaryBond (p : Plaquette L m j) (k : Fin 4) : Bond L m j :=
  ![Bond.forwardFrom p.origin p.firstAxis,
    Bond.forwardFrom (p.origin + unitStep L m j p.firstAxis) p.secondAxis,
    (Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis).opposite,
    (Bond.forwardFrom p.origin p.secondAxis).opposite] k
theorem boundaryBonds_eq (p : Plaquette L m j) :
    p.boundaryBonds = [boundaryBond p 0, boundaryBond p 1, boundaryBond p 2, boundaryBond p 3] :=
  rfl
theorem boundaryBond_source (p : Plaquette L m j) (k : Fin 4) :
    ((boundaryBond p k).source : FourTorus L m) = vertex p k := by
  fin_cases k
  · rfl
  · rfl
  · change (p.origin : FourTorus L m) + pointOnAxis L m p.secondAxis (meshSize L j) +
      pointOnAxis L m p.firstAxis (meshSize L j) = _
    simp only [vertex, parallelogramVertex]
    change _ = (p.origin : FourTorus L m) + pointOnAxis L m p.firstAxis (meshSize L j) +
      pointOnAxis L m p.secondAxis (meshSize L j)
    abel
  · rfl
theorem boundaryBond_target (p : Plaquette L m j) (k : Fin 4) :
    ((boundaryBond p k).target : FourTorus L m) = vertex p (k + 1) := by
  fin_cases k
  · rfl
  · rfl
  · rfl
  · rfl
theorem parallelogram_vertices_of_signs {T : Type*} [AddCommGroup T] (x h₁ h₂ b : T)
    (c₁ c₂ : ℤˣ) (hb : b + h₁ + h₂ = x + (c₁ : ℤ) • h₁ + (c₂ : ℤ) • h₂) :
    ∃ q : Fin 4,
      (c₁ * c₂ = 1 ∧ ∀ k, parallelogramVertex b (h₁ + h₁) (h₂ + h₂) k =
        parallelogramVertex x ((c₁ : ℤ) • (h₁ + h₁)) ((c₂ : ℤ) • (h₂ + h₂)) (k + q)) ∨
      (c₁ * c₂ = -1 ∧ ∀ k, parallelogramVertex b (h₁ + h₁) (h₂ + h₂) k =
        parallelogramVertex x ((c₁ : ℤ) • (h₁ + h₁)) ((c₂ : ℤ) • (h₂ + h₂)) (q - k)) := by
  have hb' : b = x + (c₁ : ℤ) • h₁ + (c₂ : ℤ) • h₂ - h₁ - h₂ := by
    rw [← hb]
    abel
  subst hb'
  rcases Int.units_eq_one_or c₁ with rfl | rfl <;> rcases Int.units_eq_one_or c₂ with rfl | rfl
  · refine ⟨0, Or.inl ⟨by decide, fun k => ?_⟩⟩
    fin_cases k <;> simp [parallelogramVertex] <;> abel
  · refine ⟨3, Or.inr ⟨by decide, fun k => ?_⟩⟩
    fin_cases k <;> simp [parallelogramVertex] <;> abel
  · refine ⟨1, Or.inr ⟨by decide, fun k => ?_⟩⟩
    fin_cases k <;> simp [parallelogramVertex] <;> abel
  · refine ⟨2, Or.inl ⟨by decide, fun k => ?_⟩⟩
    fin_cases k <;> simp [parallelogramVertex] <;> abel
theorem parallelogram_vertices_of_signs_swap {T : Type*} [AddCommGroup T] (x h₁ h₂ b : T)
    (c₁ c₂ : ℤˣ) (hb : b + h₂ + h₁ = x + (c₁ : ℤ) • h₁ + (c₂ : ℤ) • h₂) :
    ∃ q : Fin 4,
      (c₁ * c₂ = -1 ∧ ∀ k, parallelogramVertex b (h₂ + h₂) (h₁ + h₁) k =
        parallelogramVertex x ((c₁ : ℤ) • (h₁ + h₁)) ((c₂ : ℤ) • (h₂ + h₂)) (k + q)) ∨
      (c₁ * c₂ = 1 ∧ ∀ k, parallelogramVertex b (h₂ + h₂) (h₁ + h₁) k =
        parallelogramVertex x ((c₁ : ℤ) • (h₁ + h₁)) ((c₂ : ℤ) • (h₂ + h₂)) (q - k)) := by
  have hb' : b = x + (c₁ : ℤ) • h₁ + (c₂ : ℤ) • h₂ - h₁ - h₂ := by
    rw [← hb]
    abel
  subst hb'
  rcases Int.units_eq_one_or c₁ with rfl | rfl <;> rcases Int.units_eq_one_or c₂ with rfl | rfl
  · refine ⟨0, Or.inr ⟨by decide, fun k => ?_⟩⟩
    fin_cases k <;> simp [parallelogramVertex] <;> abel
  · refine ⟨3, Or.inl ⟨by decide, fun k => ?_⟩⟩
    fin_cases k <;> simp [parallelogramVertex] <;> abel
  · refine ⟨1, Or.inl ⟨by decide, fun k => ?_⟩⟩
    fin_cases k <;> simp [parallelogramVertex] <;> abel
  · refine ⟨2, Or.inr ⟨by decide, fun k => ?_⟩⟩
    fin_cases k <;> simp [parallelogramVertex] <;> abel
def orientationSign (r : SignedFrame) (μ ν : Fin 4) : ℤˣ :=
  r.2 (r.1.symm μ) * r.2 (r.1.symm ν) * (if r.1.symm μ < r.1.symm ν then 1 else -1)
theorem pointOnAxis_meshSize_eq_add (μ : Fin 4) : pointOnAxis L m μ (meshSize L j) =
    pointOnAxis L m μ (meshSize L j / 2) + pointOnAxis L m μ (meshSize L j / 2) := by
  rw [← pointOnAxis_add]
  congr 1
  ring
theorem vertices_of_barycenter (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {x : FourTorus L m}
    (hx : x ∈ sublattice L m j) (p' : Plaquette L m j) {f g : Fin 4} (c₁ c₂ : ℤˣ)
    (hbar : p'.barycenter = x + (c₁ : ℤ) • pointOnAxis L m f (meshSize L j / 2) +
      (c₂ : ℤ) • pointOnAxis L m g (meshSize L j / 2)) :
    (f < g → ∃ q : Fin 4,
      (c₁ * c₂ = 1 ∧ ∀ k, vertex p' k =
        parallelogramVertex x ((c₁ : ℤ) • (pointOnAxis L m f (meshSize L j / 2) +
            pointOnAxis L m f (meshSize L j / 2)))
          ((c₂ : ℤ) • (pointOnAxis L m g (meshSize L j / 2) +
            pointOnAxis L m g (meshSize L j / 2))) (k + q)) ∨
      (c₁ * c₂ = -1 ∧ ∀ k, vertex p' k =
        parallelogramVertex x ((c₁ : ℤ) • (pointOnAxis L m f (meshSize L j / 2) +
            pointOnAxis L m f (meshSize L j / 2)))
          ((c₂ : ℤ) • (pointOnAxis L m g (meshSize L j / 2) +
            pointOnAxis L m g (meshSize L j / 2))) (q - k))) ∧
    (g < f → ∃ q : Fin 4,
      (c₁ * c₂ = -1 ∧ ∀ k, vertex p' k =
        parallelogramVertex x ((c₁ : ℤ) • (pointOnAxis L m f (meshSize L j / 2) +
            pointOnAxis L m f (meshSize L j / 2)))
          ((c₂ : ℤ) • (pointOnAxis L m g (meshSize L j / 2) +
            pointOnAxis L m g (meshSize L j / 2))) (k + q)) ∨
      (c₁ * c₂ = 1 ∧ ∀ k, vertex p' k =
        parallelogramVertex x ((c₁ : ℤ) • (pointOnAxis L m f (meshSize L j / 2) +
            pointOnAxis L m f (meshSize L j / 2)))
          ((c₂ : ℤ) • (pointOnAxis L m g (meshSize L j / 2) +
            pointOnAxis L m g (meshSize L j / 2))) (q - k))) := by
  have h' : (p'.origin : FourTorus L m) + pointOnAxis L m p'.firstAxis (meshSize L j / 2) +
      pointOnAxis L m p'.secondAxis (meshSize L j / 2) = _ := hbar
  have h'' : (p'.origin : FourTorus L m) + pointOnAxis L m p'.secondAxis (meshSize L j / 2) +
      pointOnAxis L m p'.firstAxis (meshSize L j / 2) =
      x + (c₁ : ℤ) • pointOnAxis L m f (meshSize L j / 2) +
        (c₂ : ℤ) • pointOnAxis L m g (meshSize L j / 2) := by
    rw [add_right_comm]
    exact h'
  have d₁ := axis_eq_of_half_shift hL hj p'.origin.2 hx p'.firstAxis_lt_secondAxis.ne c₁ c₂ h'
  have d₂ := axis_eq_of_half_shift hL hj p'.origin.2 hx p'.firstAxis_lt_secondAxis.ne' c₁ c₂ h''
  have l := p'.firstAxis_lt_secondAxis
  constructor
  · intro hlt
    have e₁ : p'.firstAxis = f := by
      rcases d₁ with d₁ | d₁
      · exact d₁
      · rcases d₂ with d₂ | d₂
        · rw [d₁, d₂] at l
          exact absurd l (not_lt.2 hlt.le)
        · rw [d₁, d₂] at l
          exact absurd l (lt_irrefl _)
    have e₂ : p'.secondAxis = g := by
      rcases d₂ with d₂ | d₂
      · rw [e₁, d₂] at l
        exact absurd l (lt_irrefl _)
      · exact d₂
    rw [e₁, e₂] at h'
    obtain ⟨q, hq⟩ := parallelogram_vertices_of_signs x _ _ (p'.origin : FourTorus L m) c₁ c₂ h'
    refine ⟨q, ?_⟩
    simpa only [vertex, e₁, e₂, ← pointOnAxis_meshSize_eq_add] using hq
  · intro hgt
    have e₁ : p'.firstAxis = g := by
      rcases d₁ with d₁ | d₁
      · rcases d₂ with d₂ | d₂
        · rw [d₁, d₂] at l
          exact absurd l (lt_irrefl _)
        · rw [d₁, d₂] at l
          exact absurd l (not_lt.2 hgt.le)
      · exact d₁
    have e₂ : p'.secondAxis = f := by
      rcases d₂ with d₂ | d₂
      · exact d₂
      · rw [e₁, d₂] at l
        exact absurd l (lt_irrefl _)
    rw [e₁, e₂] at h'
    obtain ⟨q, hq⟩ :=
      parallelogram_vertices_of_signs_swap x _ _ (p'.origin : FourTorus L m) c₁ c₂ h'
    refine ⟨q, ?_⟩
    simpa only [vertex, e₁, e₂, ← pointOnAxis_meshSize_eq_add] using hq
section
variable {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame} {v : Fin 4 → ℝ}
theorem apply_vertex (hind : IsInducedByAffine σ r v) (p : Plaquette L m j) (k : Fin 4) :
    σ (vertex p k) = parallelogramVertex (σ p.origin)
      ((r.2 (r.1.symm p.firstAxis) : ℤ) •
        (pointOnAxis L m (r.1.symm p.firstAxis) (meshSize L j / 2) +
          pointOnAxis L m (r.1.symm p.firstAxis) (meshSize L j / 2)))
      ((r.2 (r.1.symm p.secondAxis) : ℤ) •
        (pointOnAxis L m (r.1.symm p.secondAxis) (meshSize L j / 2) +
          pointOnAxis L m (r.1.symm p.secondAxis) (meshSize L j / 2))) k := by
  fin_cases k
  · rfl
  · change σ ((p.origin : FourTorus L m) + pointOnAxis L m p.firstAxis (meshSize L j)) =
      (σ p.origin) + _
    rw [apply_add_pointOnAxis hind, pointOnAxis_meshSize_eq_add (r.1.symm p.firstAxis)]
  · change σ ((p.origin : FourTorus L m) + pointOnAxis L m p.firstAxis (meshSize L j) +
      pointOnAxis L m p.secondAxis (meshSize L j)) = (σ p.origin) + _ + _
    rw [apply_add_pointOnAxis hind, apply_add_pointOnAxis hind,
      pointOnAxis_meshSize_eq_add (r.1.symm p.firstAxis),
      pointOnAxis_meshSize_eq_add (r.1.symm p.secondAxis)]
  · change σ ((p.origin : FourTorus L m) + pointOnAxis L m p.secondAxis (meshSize L j)) =
      (σ p.origin) + _
    rw [apply_add_pointOnAxis hind, pointOnAxis_meshSize_eq_add (r.1.symm p.secondAxis)]
theorem apply_barycenter (hind : IsInducedByAffine σ r v) (p : Plaquette L m j) :
    σ p.barycenter = σ p.origin +
      (r.2 (r.1.symm p.firstAxis) : ℤ) •
        pointOnAxis L m (r.1.symm p.firstAxis) (meshSize L j / 2) +
      (r.2 (r.1.symm p.secondAxis) : ℤ) •
        pointOnAxis L m (r.1.symm p.secondAxis) (meshSize L j / 2) := by
  change σ ((p.origin : FourTorus L m) + pointOnAxis L m p.firstAxis (meshSize L j / 2) +
    pointOnAxis L m p.secondAxis (meshSize L j / 2)) = _
  rw [apply_add_pointOnAxis hind, apply_add_pointOnAxis hind]
theorem plaquetteImage_barycenter (h : MapsCellsAndCubes σ j) (p : Plaquette L m j) :
    (plaquetteImage σ p).barycenter = σ p.barycenter := h.2.2.2.2.2.2.2.1 p
theorem vertex_plaquetteImage (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (h : MapsCellsAndCubes σ j) (hind : IsInducedByAffine σ r v)
    (p : Plaquette L m j) :
    ∃ q : Fin 4,
      (orientationSign r p.firstAxis p.secondAxis = 1 ∧
        ∀ k, vertex (plaquetteImage σ p) k = σ (vertex p (k + q))) ∨
      (orientationSign r p.firstAxis p.secondAxis = -1 ∧
        ∀ k, vertex (plaquetteImage σ p) k = σ (vertex p (q - k))) := by
  have hx : σ p.origin ∈ sublattice L m j := by
    have e : σ p.origin ∈ σ '' (sublattice L m j : Set (FourTorus L m)) :=
      mem_image_of_mem σ p.origin.2
    rw [h.1] at e
    exact e
  have hfg : r.1.symm p.firstAxis ≠ r.1.symm p.secondAxis :=
    fun e => p.firstAxis_lt_secondAxis.ne (r.1.symm.injective e)
  have hb := plaquetteImage_barycenter h p
  rw [apply_barycenter hind] at hb
  obtain ⟨c₁, c₂⟩ := vertices_of_barycenter hL hj hx (plaquetteImage σ p) _ _ hb
  rcases lt_or_gt_of_ne hfg with hlt | hgt
  · have he : orientationSign r p.firstAxis p.secondAxis =
        r.2 (r.1.symm p.firstAxis) * r.2 (r.1.symm p.secondAxis) := by
      simp [orientationSign, hlt]
    obtain ⟨q, hq⟩ := c₁ hlt
    refine ⟨q, ?_⟩
    rcases hq with ⟨hc, hk⟩ | ⟨hc, hk⟩
    · exact Or.inl ⟨he.trans hc, fun k => by rw [apply_vertex hind]; exact hk k⟩
    · exact Or.inr ⟨he.trans hc, fun k => by rw [apply_vertex hind]; exact hk k⟩
  · have he : orientationSign r p.firstAxis p.secondAxis =
        -(r.2 (r.1.symm p.firstAxis) * r.2 (r.1.symm p.secondAxis)) := by
      simp [orientationSign, not_lt.2 hgt.le]
    obtain ⟨q, hq⟩ := c₂ hgt
    refine ⟨q, ?_⟩
    rcases hq with ⟨hc, hk⟩ | ⟨hc, hk⟩
    · exact Or.inl ⟨by rw [he, hc, neg_neg], fun k => by rw [apply_vertex hind]; exact hk k⟩
    · exact Or.inr ⟨by rw [he, hc], fun k => by rw [apply_vertex hind]; exact hk k⟩
theorem bondPreimage_boundaryBond_of_rotation (h' : MapsCellsAndCubes σ.symm j)
    {p p' : Plaquette L m j} {q : Fin 4}
    (hc : ∀ k, vertex p' k = σ (vertex p (k + q))) (k : Fin 4) :
    bondPreimage σ (boundaryBond p' k) = boundaryBond p (k + q) :=
  bond_ext_of_endpoints
    (by rw [bondPreimage_source h', boundaryBond_source, hc, Equiv.symm_apply_apply,
      boundaryBond_source])
    (by rw [bondPreimage_target h', boundaryBond_target, hc, Equiv.symm_apply_apply,
      boundaryBond_target, add_right_comm])
theorem bondPreimage_boundaryBond_of_reflection (h' : MapsCellsAndCubes σ.symm j)
    {p p' : Plaquette L m j} {q : Fin 4}
    (hc : ∀ k, vertex p' k = σ (vertex p (q - k))) (k : Fin 4) :
    bondPreimage σ (boundaryBond p' k) = (boundaryBond p (q - k - 1)).opposite :=
  bond_ext_of_endpoints
    (by
      rw [bondPreimage_source h', boundaryBond_source, hc, Equiv.symm_apply_apply]
      change _ = (((boundaryBond p (q - k - 1)).target : Site L m j) : FourTorus L m)
      rw [boundaryBond_target, sub_add_cancel])
    (by
      rw [bondPreimage_target h', boundaryBond_target, hc, Equiv.symm_apply_apply]
      change _ = (((boundaryBond p (q - k - 1)).source : Site L m j) : FourTorus L m)
      rw [boundaryBond_source, sub_sub])
end
theorem coe_units_conj (Q X Y : ComplexMatrix2ˣ) (h : Y = Q * X * Q⁻¹) :
    (Y : ComplexMatrix2) = (Q : ComplexMatrix2) * (X : ComplexMatrix2) * (Q : ComplexMatrix2)⁻¹ := by
  rw [h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
theorem cyclic_products_conj {G : Type*} [Group G] (a b c d : G) :
    a * (b * (c * d)) = a * (b * (c * d)) * (a * (b * (c * d))) * (a * (b * (c * d)))⁻¹ ∧
    b * (c * (d * a)) = b * (c * d) * (a * (b * (c * d))) * (b * (c * d))⁻¹ ∧
    c * (d * (a * b)) = c * d * (a * (b * (c * d))) * (c * d)⁻¹ ∧
    d * (a * (b * c)) = d * (a * (b * (c * d))) * d⁻¹ ∧
    d⁻¹ * (c⁻¹ * (b⁻¹ * a⁻¹)) =
      a * (b * (c * d)) * (a * (b * (c * d)))⁻¹ * (a * (b * (c * d)))⁻¹ ∧
    a⁻¹ * (d⁻¹ * (c⁻¹ * b⁻¹)) = b * (c * d) * (a * (b * (c * d)))⁻¹ * (b * (c * d))⁻¹ ∧
    b⁻¹ * (a⁻¹ * (d⁻¹ * c⁻¹)) = c * d * (a * (b * (c * d)))⁻¹ * (c * d)⁻¹ ∧
    c⁻¹ * (b⁻¹ * (a⁻¹ * d⁻¹)) = d * (a * (b * (c * d)))⁻¹ * d⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> group
theorem fin_four_eq_cases (q : Fin 4) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by apply _root_.YangMills.Construction.GaugeFixing.fin_four_cases <;> assumption
theorem rotated_product_eq_conj {β : Type*} (U : β → ComplexMatrix2) (e : Fin 4 → β)
    (hu : ∀ k, IsUnit (U (e k))) (q : Fin 4) :
    U (e (0 + q)) * (U (e (1 + q)) * (U (e (2 + q)) * U (e (3 + q)))) =
      (([e 0, e 1, e 2, e 3].drop q).map U).prod * ([e 0, e 1, e 2, e 3].map U).prod *
        ((([e 0, e 1, e 2, e 3].drop q).map U).prod)⁻¹ := by
  obtain ⟨a, ha⟩ := hu 0
  obtain ⟨b, hb⟩ := hu 1
  obtain ⟨c, hc⟩ := hu 2
  obtain ⟨d, hd⟩ := hu 3
  obtain ⟨r₀, r₁, r₂, r₃, -, -, -, -⟩ := cyclic_products_conj a b c d
  rcases fin_four_eq_cases q with rfl | rfl | rfl | rfl
  · change U (e 0) * (U (e 1) * (U (e 2) * U (e 3))) = _
    rw [show [e 0, e 1, e 2, e 3].drop ((0 : Fin 4) : ℕ) = [e 0, e 1, e 2, e 3] from rfl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← ha, ← hb, ← hc, ← hd]
    simpa only [Units.val_mul] using coe_units_conj _ _ _ r₀
  · change U (e 1) * (U (e 2) * (U (e 3) * U (e 0))) = _
    rw [show [e 0, e 1, e 2, e 3].drop ((1 : Fin 4) : ℕ) = [e 1, e 2, e 3] from rfl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← ha, ← hb, ← hc, ← hd]
    simpa only [Units.val_mul] using coe_units_conj _ _ _ r₁
  · change U (e 2) * (U (e 3) * (U (e 0) * U (e 1))) = _
    rw [show [e 0, e 1, e 2, e 3].drop ((2 : Fin 4) : ℕ) = [e 2, e 3] from rfl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← ha, ← hb, ← hc, ← hd]
    simpa only [Units.val_mul] using coe_units_conj _ _ _ r₂
  · change U (e 3) * (U (e 0) * (U (e 1) * U (e 2))) = _
    rw [show [e 0, e 1, e 2, e 3].drop ((3 : Fin 4) : ℕ) = [e 3] from rfl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← ha, ← hb, ← hc, ← hd]
    simpa only [Units.val_mul] using coe_units_conj _ _ _ r₃
theorem reflected_product_eq_conj {β : Type*} (U : β → ComplexMatrix2) (e : Fin 4 → β)
    (hu : ∀ k, IsUnit (U (e k))) (q : Fin 4) :
    (U (e (q - 0 - 1)))⁻¹ * ((U (e (q - 1 - 1)))⁻¹ * ((U (e (q - 2 - 1)))⁻¹ *
        (U (e (q - 3 - 1)))⁻¹)) =
      (([e 0, e 1, e 2, e 3].drop q).map U).prod * (([e 0, e 1, e 2, e 3].map U).prod)⁻¹ *
        ((([e 0, e 1, e 2, e 3].drop q).map U).prod)⁻¹ := by
  obtain ⟨a, ha⟩ := hu 0
  obtain ⟨b, hb⟩ := hu 1
  obtain ⟨c, hc⟩ := hu 2
  obtain ⟨d, hd⟩ := hu 3
  obtain ⟨-, -, -, -, r₀, r₁, r₂, r₃⟩ := cyclic_products_conj a b c d
  rcases fin_four_eq_cases q with rfl | rfl | rfl | rfl
  · change (U (e 3))⁻¹ * ((U (e 2))⁻¹ * ((U (e 1))⁻¹ * (U (e 0))⁻¹)) = _
    rw [show [e 0, e 1, e 2, e 3].drop ((0 : Fin 4) : ℕ) = [e 0, e 1, e 2, e 3] from rfl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← ha, ← hb, ← hc, ← hd]
    simpa only [Units.val_mul, Matrix.coe_units_inv] using coe_units_conj _ _ _ r₀
  · change (U (e 0))⁻¹ * ((U (e 3))⁻¹ * ((U (e 2))⁻¹ * (U (e 1))⁻¹)) = _
    rw [show [e 0, e 1, e 2, e 3].drop ((1 : Fin 4) : ℕ) = [e 1, e 2, e 3] from rfl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← ha, ← hb, ← hc, ← hd]
    simpa only [Units.val_mul, Matrix.coe_units_inv] using coe_units_conj _ _ _ r₁
  · change (U (e 1))⁻¹ * ((U (e 0))⁻¹ * ((U (e 3))⁻¹ * (U (e 2))⁻¹)) = _
    rw [show [e 0, e 1, e 2, e 3].drop ((2 : Fin 4) : ℕ) = [e 2, e 3] from rfl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← ha, ← hb, ← hc, ← hd]
    simpa only [Units.val_mul, Matrix.coe_units_inv] using coe_units_conj _ _ _ r₂
  · change (U (e 2))⁻¹ * ((U (e 1))⁻¹ * ((U (e 0))⁻¹ * (U (e 3))⁻¹)) = _
    rw [show [e 0, e 1, e 2, e 3].drop ((3 : Fin 4) : ℕ) = [e 3] from rfl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← ha, ← hb, ← hc, ← hd]
    simpa only [Units.val_mul, Matrix.coe_units_inv] using coe_units_conj _ _ _ r₃
theorem det_eq_one_of_mem {X : ComplexMatrix2} (h : X ∈ compactGaugeGroup) : X.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem mem_unitaryGroup_of_mem {X : ComplexMatrix2} (h : X ∈ compactGaugeGroup) :
    X ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.1 h).1
theorem isUnit_of_mem {X : ComplexMatrix2} (h : X ∈ compactGaugeGroup) : IsUnit X :=
  (Matrix.isUnit_iff_isUnit_det X).2 (by rw [det_eq_one_of_mem h]; exact isUnit_one)
theorem pathHolonomy_mem {ℬ : Set (Bond L m j)} {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup ℬ U) {Γ : List (Bond L m j)} (hΓ : ∀ b ∈ Γ, b ∈ ℬ) :
    pathHolonomy U Γ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.pathHolonomy_mem <;> assumption
theorem boundaryBond_mem (p : Plaquette L m j) (k : Fin 4) :
    boundaryBond p k ∈ p.boundaryBonds := by
  rw [boundaryBonds_eq]
  rcases fin_four_eq_cases k with rfl | rfl | rfl | rfl <;> simp
theorem plaquetteHolonomy_eq_product (U : Bond L m j → ComplexMatrix2) (p : Plaquette L m j) :
    plaquetteHolonomy U p =
      U (boundaryBond p 0) * (U (boundaryBond p 1) *
        (U (boundaryBond p 2) * U (boundaryBond p 3))) := by
  simp only [plaquetteHolonomy, pathHolonomy, boundaryBonds_eq, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
section
variable {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame} {v : Fin 4 → ℝ}
theorem plaquetteHolonomy_plaquetteImage (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (h : MapsCellsAndCubes σ j) (h' : MapsCellsAndCubes σ.symm j)
    (hind : IsInducedByAffine σ r v) {ℬ : Set (Bond L m j)} {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup ℬ U) (p : Plaquette L m j)
    (hp : ∀ b ∈ p.boundaryBonds, b ∈ ℬ) :
    ∃ Γ : List (Bond L m j), Γ <:+: p.boundaryBonds ∧ (∀ b ∈ Γ, b ∈ ℬ) ∧
      plaquetteHolonomy (transportGaugeField σ U) (plaquetteImage σ p) =
        pathHolonomy U Γ *
          plaquetteHolonomy U p ^ ((orientationSign r p.firstAxis p.secondAxis : ℤˣ) : ℤ) *
          (pathHolonomy U Γ)⁻¹ := by
  have hu : ∀ k, IsUnit (U (boundaryBond p k)) :=
    fun k => isUnit_of_mem (hU.1 _ (hp _ (boundaryBond_mem p k)))
  obtain ⟨q, ⟨he, hc⟩ | ⟨he, hc⟩⟩ := vertex_plaquetteImage hL hj h hind p
  · refine ⟨p.boundaryBonds.drop q, (List.drop_suffix _ _).isInfix,
      fun b hb => hp b (List.mem_of_mem_drop hb), ?_⟩
    rw [he, plaquetteHolonomy_eq_product]
    simp only [transportGaugeField, bondPreimage_boundaryBond_of_rotation h' hc, Units.val_one,
      zpow_one]
    exact rotated_product_eq_conj U (boundaryBond p) hu q
  · refine ⟨p.boundaryBonds.drop q, (List.drop_suffix _ _).isInfix,
      fun b hb => hp b (List.mem_of_mem_drop hb), ?_⟩
    rw [he, plaquetteHolonomy_eq_product]
    simp only [transportGaugeField, bondPreimage_boundaryBond_of_reflection h' hc, Units.val_neg,
      Units.val_one, Int.reduceNeg, zpow_neg_one]
    simp only [hU.2 _ (hp _ (boundaryBond_mem p _))]
    exact reflected_product_eq_conj U (boundaryBond p) hu q
theorem fullTrace_conj {Q : ComplexMatrix2} (hQ : Q ∈ compactGaugeGroup) (Y : ComplexMatrix2) :
    ComplexMatrix2.fullTrace (Q * Y * Q⁻¹) = ComplexMatrix2.fullTrace Y := by
  have hd : IsUnit Q.det := by rw [det_eq_one_of_mem hQ]; exact isUnit_one
  simp only [ComplexMatrix2.fullTrace]
  rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ hd, one_mul]
theorem fullTrace_inv {X : ComplexMatrix2} (hX : X ∈ compactGaugeGroup) :
    ComplexMatrix2.fullTrace X⁻¹ = ComplexMatrix2.fullTrace X := by
  simp only [ComplexMatrix2.fullTrace]
  rw [Matrix.inv_def, det_eq_one_of_mem hX]
  simp [Matrix.adjugate_fin_two, Matrix.trace_fin_two, add_comm]
theorem fullTrace_zpow_units {X : ComplexMatrix2} (hX : X ∈ compactGaugeGroup) (c : ℤˣ) :
    ComplexMatrix2.fullTrace (X ^ (c : ℤ)) = ComplexMatrix2.fullTrace X := by
  rcases Int.units_eq_one_or c with rfl | rfl
  · simp
  · simpa using fullTrace_inv hX
theorem operatorNorm_zpow_units_sub_one (h₃ : ComplexMatrix2.OperatorNormUnderConjugation)
    {X : ComplexMatrix2} (hX : X ∈ compactGaugeGroup) (c : ℤˣ) :
    ComplexMatrix2.operatorNorm (X ^ (c : ℤ) - 1) = ComplexMatrix2.operatorNorm (X - 1) := by
  rcases Int.units_eq_one_or c with rfl | rfl
  · simp
  · simpa using h₃.2.2.1 X (mem_unitaryGroup_of_mem hX)
theorem operatorNorm_conj_sub_one (h₃ : ComplexMatrix2.OperatorNormUnderConjugation)
    {Q : ComplexMatrix2} (hQ : Q ∈ compactGaugeGroup) (Y : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (Q * Y * Q⁻¹ - 1) = ComplexMatrix2.operatorNorm (Y - 1) := by
  have hd : IsUnit Q.det := by rw [det_eq_one_of_mem hQ]; exact isUnit_one
  have e : Q * Y * Q⁻¹ - 1 = Q * (Y - 1) * Q⁻¹ := by
    rw [mul_sub, sub_mul, mul_one, Matrix.mul_nonsing_inv _ hd]
  rw [e]
  exact h₃.2.1 _ _ (mem_unitaryGroup_of_mem hQ)
theorem carriesPlaquette_of_maps (h₃ : ComplexMatrix2.OperatorNormUnderConjugation)
    (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (hind : IsInducedByAffine σ r v)
    {ℬ : Set (Bond L m j)} {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup ℬ U)
    (p : Plaquette L m j) (hp : ∀ b ∈ p.boundaryBonds, b ∈ ℬ) :
    CarriesPlaquette σ (orientationSign r p.firstAxis p.secondAxis) U p := by
  obtain ⟨Γ, hΓ, hm, he⟩ := plaquetteHolonomy_plaquetteImage hL hj h h' hind hU p hp
  have hX : plaquetteHolonomy U p ∈ compactGaugeGroup := pathHolonomy_mem hU hp
  have hQ : pathHolonomy U Γ ∈ compactGaugeGroup := pathHolonomy_mem hU hm
  have ht : ComplexMatrix2.fullTrace
      (plaquetteHolonomy (transportGaugeField σ U) (plaquetteImage σ p)) =
      ComplexMatrix2.fullTrace (plaquetteHolonomy U p) := by
    rw [he, fullTrace_conj hQ, fullTrace_zpow_units hX]
  refine ⟨⟨Γ, hΓ, he⟩, ?_, ?_, ?_⟩
  · simp only [plaquetteCost, ht]
  · simp only [plaquetteEnergy, ht]
  · rw [he, operatorNorm_conj_sub_one h₃ hQ, operatorNorm_zpow_units_sub_one h₃ hX]
end
section
variable {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame} {v : Fin 4 → ℝ}
theorem plaquetteImage_symm_plaquetteImage (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (h : MapsCellsAndCubes σ j) (h' : MapsCellsAndCubes σ.symm j)
    (p : Plaquette L m j) : plaquetteImage σ.symm (plaquetteImage σ p) = p :=
  barycenter_injective hL hj
    (by rw [plaquetteImage_barycenter h', plaquetteImage_barycenter h, Equiv.symm_apply_apply])
theorem plaquetteImage_plaquetteImage_symm (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (h : MapsCellsAndCubes σ j) (h' : MapsCellsAndCubes σ.symm j)
    (p : Plaquette L m j) : plaquetteImage σ (plaquetteImage σ.symm p) = p :=
  barycenter_injective hL hj
    (by rw [plaquetteImage_barycenter h, plaquetteImage_barycenter h', Equiv.apply_symm_apply])
def plaquetteImageEquiv (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) : Plaquette L m j ≃ Plaquette L m j where
  toFun := plaquetteImage σ
  invFun := plaquetteImage σ.symm
  left_inv := plaquetteImage_symm_plaquetteImage hL hj h h'
  right_inv := plaquetteImage_plaquetteImage_symm hL hj h h'
theorem mem_plaquettesInside_iff (X : Set (FourTorus L m)) (p : Plaquette L m j) :
    p ∈ (plaquettesInside X : Set (Plaquette L m j)) ↔ ∀ k, vertex p k ∈ X := by
  constructor
  · intro h k
    rcases fin_four_eq_cases k with rfl | rfl | rfl | rfl
    · exact h p.origin (by simp [Plaquette.vertices])
    · exact h (p.origin + unitStep L m j p.firstAxis) (by simp [Plaquette.vertices])
    · exact h (p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis)
        (by simp [Plaquette.vertices])
    · exact h (p.origin + unitStep L m j p.secondAxis) (by simp [Plaquette.vertices])
  · rintro h c (rfl | rfl | rfl | rfl)
    · exact h 0
    · exact h 1
    · exact h 2
    · exact h 3
theorem plaquetteImage_mem_plaquettesInside_iff (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (h : MapsCellsAndCubes σ j) (hind : IsInducedByAffine σ r v)
    (X : Set (FourTorus L m)) (p : Plaquette L m j) :
    plaquetteImage σ p ∈ (plaquettesInside (σ '' X) : Set (Plaquette L m j)) ↔
      p ∈ (plaquettesInside X : Set (Plaquette L m j)) := by
  rw [mem_plaquettesInside_iff, mem_plaquettesInside_iff]
  obtain ⟨q, ⟨-, hc⟩ | ⟨-, hc⟩⟩ := vertex_plaquetteImage hL hj h hind p
  · constructor
    · intro hk k
      have t := hk (k - q)
      rw [hc, sub_add_cancel] at t
      exact σ.injective.mem_set_image.1 t
    · intro hk k
      rw [hc]
      exact mem_image_of_mem σ (hk _)
  · constructor
    · intro hk k
      have t := hk (q - k)
      rw [hc, sub_sub_cancel] at t
      exact σ.injective.mem_set_image.1 t
    · intro hk k
      rw [hc]
      exact mem_image_of_mem σ (hk _)
theorem finsum_plaquettesInside_image {M : Type*} [AddCommMonoid M] (hL : 0 < L)
    (hj : -(m : ℤ) ≤ j) (h : MapsCellsAndCubes σ j) (h' : MapsCellsAndCubes σ.symm j)
    (hind : IsInducedByAffine σ r v) (X : Set (FourTorus L m)) (F G : Plaquette L m j → M)
    (hFG : ∀ p ∈ (plaquettesInside X : Set (Plaquette L m j)), G (plaquetteImage σ p) = F p) :
    ∑ᶠ p ∈ (plaquettesInside (σ '' X) : Set (Plaquette L m j)), G p =
      ∑ᶠ p ∈ (plaquettesInside X : Set (Plaquette L m j)), F p := by
  symm
  refine finsum_mem_eq_of_bijOn (plaquetteImage σ) ⟨?_, ?_, ?_⟩ fun p hp => (hFG p hp).symm
  · exact fun p hp => (plaquetteImage_mem_plaquettesInside_iff hL hj h hind X p).2 hp
  · exact fun p _ p' _ e => (plaquetteImageEquiv hL hj h h').injective e
  · intro p' hp'
    refine ⟨plaquetteImage σ.symm p', ?_, plaquetteImage_plaquetteImage_symm hL hj h h' p'⟩
    rw [← plaquetteImage_mem_plaquettesInside_iff hL hj h hind X,
      plaquetteImage_plaquetteImage_symm hL hj h h']
    exact hp'
theorem boundaryBonds_mem_bondsInside {X : Set (FourTorus L m)} {p : Plaquette L m j}
    (hp : p ∈ (plaquettesInside X : Set (Plaquette L m j))) :
    ∀ b ∈ p.boundaryBonds, b ∈ (bondsInside X : Set (Bond L m j)) := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.boundaryBonds_mem_bondsInside <;> assumption
theorem carriesWeightedEnergies_of_maps (h₃ : ComplexMatrix2.OperatorNormUnderConjugation)
    (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (h : MapsCellsAndCubes σ j)
    (h' : MapsCellsAndCubes σ.symm j) (hind : IsInducedByAffine σ r v)
    {U : Bond L m j → ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j) :
    CarriesWeightedEnergies σ U := by
  have hp : ∀ p : Plaquette L m j,
      CarriesPlaquette σ (orientationSign r p.firstAxis p.secondAxis) U p :=
    fun p => carriesPlaquette_of_maps h₃ hL hj h h' hind hU p fun _ _ => mem_univ _
  have hb : ∀ p : Plaquette L m j, σ.symm (plaquetteImage σ p).barycenter = p.barycenter :=
    fun p => by rw [plaquetteImage_barycenter h, Equiv.symm_apply_apply]
  refine ⟨fun c => ?_, fun c => ?_, fun E _ _ f => ?_⟩
  · unfold plaquetteWeightedEnergy
    rw [← finsum_comp_equiv (plaquetteImageEquiv hL hj h h')]
    refine finsum_congr fun p => ?_
    change c (plaquetteImage σ.symm (plaquetteImage σ p)) *
      plaquetteEnergy (transportGaugeField σ U) (plaquetteImage σ p) = _
    rw [plaquetteImage_symm_plaquetteImage hL hj h h', (hp p).2.2.1]
  · unfold barycenterWeightedEnergy plaquetteWeightedEnergy
    rw [← finsum_comp_equiv (plaquetteImageEquiv hL hj h h')]
    refine finsum_congr fun p => ?_
    change c (σ.symm (plaquetteImage σ p).barycenter) *
      plaquetteEnergy (transportGaugeField σ U) (plaquetteImage σ p) = _
    rw [hb, (hp p).2.2.1]
  · unfold smearedObservable
    rw [← finsum_comp_equiv (plaquetteImageEquiv hL hj h h')]
    refine finsum_congr fun p => ?_
    change plaquetteCost (transportGaugeField σ U) (plaquetteImage σ p) •
      f (σ.symm (plaquetteImage σ p).barycenter) = _
    rw [hb, (hp p).2.1]
end
theorem orderedContour_injective {j' : ℤ} (hL : 0 < L) (hj : -(m : ℤ) ≤ j') (y : Site L m j)
    (x : Site L m j') : Function.Injective (orderedContour y x) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryImages.orderedContour_injective <;> assumption
theorem exists_equiv_of_image_range {ι ι' α : Type*} {F : α → α} {f : ι → α} {g : ι' → α}
    (hF : Function.Injective F) (hf : Function.Injective f) (hg : Function.Injective g)
    (h : F '' range f = range g) : ∃ e : ι ≃ ι', ∀ i, F (f i) = g (e i) := by
  have he : ∀ i, ∃ i', g i' = F (f i) := fun i => by
    exact show F (f i) ∈ range g from h ▸ mem_image_of_mem F (mem_range_self i)
  choose e he using he
  refine ⟨Equiv.ofBijective e ⟨fun i i' hi => hf (hF ?_), fun i' => ?_⟩, fun i => (he i).symm⟩
  · rw [← he, ← he, hi]
  · have t : g i' ∈ F '' range f := h ▸ mem_range_self i'
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := t
    exact ⟨i, hg (by rw [he, hi])⟩
theorem familyDiameter_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    {V : ι → ComplexMatrix2} {V' : ι' → ComplexMatrix2} (h : ∀ i, V' (e i) = V i) :
    ComplexMatrix2.familyDiameter V' = ComplexMatrix2.familyDiameter V := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.familyDiameter_comp_equiv <;> assumption
theorem isLogMean_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    {V : ι → ComplexMatrix2} {V' : ι' → ComplexMatrix2} (h : ∀ i, V' (e i) = V i)
    (𝒢 : Set ComplexMatrix2) (W : ComplexMatrix2) :
    ComplexMatrix2.IsLogMean 𝒢 V' W ↔ ComplexMatrix2.IsLogMean 𝒢 V W := by apply _root_.YangMills.Construction.PeriodicLattice.ContourCovariance.isLogMean_comp_equiv <;> assumption
theorem carriesContourMean_of_maps {σ : FourTorus L m ≃ FourTorus L m} (hL : 0 < L)
    (hj : -(m : ℤ) ≤ j + 1)
    (h : MapsCellsAndCubes σ (j + 1))
    (h' : MapsCellsAndCubes σ.symm (j + 1))
    (hc : IsometryInvariance.MapsContourSets σ j)
    (U : Bond L m (j + 1) → ComplexMatrix2) (y : Site L m j) (x : Site L m (j + 1))
    (hx : x ∈ sitesInBlock (j + 1) y) : CarriesContourMean σ U y x := by
  have hinj : Function.Injective (pathImage σ : List (Bond L m (j + 1)) → _) :=
    List.map_injective_iff.2 (bondImage_injective h h')
  obtain ⟨e, he⟩ := exists_equiv_of_image_range hinj (orderedContour_injective hL hj y x)
    (orderedContour_injective hL hj (sitePreimage σ.symm y) (sitePreimage σ.symm x)) (hc y x hx)
  have hv : ∀ τ, contourHolonomies (transportGaugeField σ U) (sitePreimage σ.symm y)
      (sitePreimage σ.symm x) (e τ) = contourHolonomies U y x τ := fun τ => by
    simp only [contourHolonomies]
    rw [← he, pathHolonomy_pathImage h h']
  have hm : ∀ W, ComplexMatrix2.IsLogMean compactGaugeGroup
      (contourHolonomies (transportGaugeField σ U) (sitePreimage σ.symm y)
        (sitePreimage σ.symm x)) W ↔
      ComplexMatrix2.IsLogMean compactGaugeGroup (contourHolonomies U y x) W :=
    isLogMean_reindex e hv compactGaugeGroup
  have hfun : ComplexMatrix2.IsLogMean compactGaugeGroup
      (contourHolonomies (transportGaugeField σ U) (sitePreimage σ.symm y)
        (sitePreimage σ.symm x)) =
      ComplexMatrix2.IsLogMean compactGaugeGroup (contourHolonomies U y x) :=
    funext fun W => propext (hm W)
  refine ⟨familyDiameter_reindex e hv, ?_, fun _ => ?_⟩
  · unfold HasContourMean ComplexMatrix2.HasUniqueLogMean
    rw [hfun]
  · unfold meanContourHolonomy ComplexMatrix2.logMean
    rw [hfun]
theorem statement_holds (h₁ : LatticeIsometryGroupActionStatement)
    (h₂ : IsometryInvariance.InvariantUnderIsometries)
    (h₃ : ComplexMatrix2.OperatorNormUnderConjugation) :
    IsometryCovariance.Statement := by
  refine ⟨orientationSign, fun L m hL hm i hi σ hσ => ?_⟩
  have hpos : 0 < L := by
    have := hL.2
    omega
  have hg := h₁ L m i hL hm hi
  have hσ' : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨⟨H, hH⟩, -⟩ := hg.1
    have t : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
    have t' := H.inv_mem t
    rw [← hH]
    exact t'
  have hcar : ∀ j : ℤ, i ≤ j → MapsCellsAndCubes σ j :=
    fun j hj => (hg.2.2.2.2 σ hσ j hj).1
  have hcar' : ∀ j : ℤ, i ≤ j → MapsCellsAndCubes σ.symm j :=
    fun j hj => (hg.2.2.2.2 σ.symm hσ' j hj).1
  obtain ⟨v, hind⟩ : HasLinearPart σ (linearComponent σ) := by
    obtain ⟨r, v, -, hrv⟩ := hσ
    have hex : ∃ r : SignedFrame, HasLinearPart σ r := ⟨r, v, hrv⟩
    unfold linearComponent
    rw [dif_pos hex]
    exact hex.choose_spec
  have hcont := (h₂ L m hL hm i hi σ hσ).1
  have hreal : ∀ (j : ℤ), i ≤ j → ∀ (Ω₀ : Set (FourTorus L m)) (U : Bond L m j → ComplexMatrix2),
      IsGaugeField compactGaugeGroup (bondsInside Ω₀) U →
        ∀ p ∈ (plaquettesInside Ω₀ : Set (Plaquette L m j)),
          CarriesPlaquette σ (orientationSign (linearComponent σ) p.firstAxis p.secondAxis) U p :=
    fun j hj Ω₀ U hU p hp => carriesPlaquette_of_maps h₃ hpos (hi.trans hj) (hcar j hj)
      (hcar' j hj) hind hU p (boundaryBonds_mem_bondsInside hp)
  refine ⟨fun j hj => ⟨fun ℬ U hℬ hU =>
      ⟨carriesHolonomies_of_maps (hcar j hj) (hcar' j hj) ℬ U hℬ hU,
        fun p hp => carriesPlaquette_of_maps h₃ hpos (hi.trans hj) (hcar j hj) (hcar' j hj)
          hind hU p hp⟩,
    fun i' Ω₀ U _ _ hU => ?_, fun U hU => carriesWeightedEnergies_of_maps h₃ hpos (hi.trans hj)
      (hcar j hj) (hcar' j hj) hind hU, fun y x ℬ U hx _ _ _ => carriesContourMean_of_maps hpos
      (by omega) (hcar (j + 1) (by omega)) (hcar' (j + 1) (by omega)) (hcont j hj).2.2 U y x hx⟩,
    fun K i' Ω₀ U hK _ _ hU => ?_⟩
  · exact finsum_plaquettesInside_image hpos (hi.trans hj) (hcar j hj) (hcar' j hj) hind Ω₀ _ _
      fun p hp => (hreal j hj Ω₀ U hU p hp).2.2.1
  · exact finsum_plaquettesInside_image hpos (hi.trans hK) (hcar _ hK) (hcar' _ hK) hind Ω₀ _ _
      fun p hp => (hreal _ hK Ω₀ U hU p hp).2.1
end YangMills.Construction.PeriodicLattice.IsometryCovariance
end
