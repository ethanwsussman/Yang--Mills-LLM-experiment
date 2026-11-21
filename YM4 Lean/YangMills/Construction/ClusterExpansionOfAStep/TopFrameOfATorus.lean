import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.MatchingClasses
import YangMills.Construction.ClusterExpansionOfAStep.SharesOnARegionOfATorus
import YangMills.Construction.ColdChainAtEveryLevel.ShareOfTheCriticalChainProof
import YangMills.Construction.HoleBesideASecondHole.TermsOfSmallCoordinatesProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusFrame
open BlockAverages TorusFields TorusLumps TorusShares StepCosts
section CellsAsSites
variable {L t m : ℕ} [NeZero m]
theorem period_torusFrame (i : Fin 4) :
    (torusFrame L t m).period (torusFrame L t m).top i = m := by
  simp [BlockFrame.period, torusFrame, BlockFrame.top]
instance neZero_period_torusFrame (i : Fin 4) :
    NeZero ((torusFrame L t m).period (torusFrame L t m).top i) :=
  ⟨by rw [period_torusFrame]; exact NeZero.ne m⟩
def siteOfCell (x : (torusFrame L t m).Cell) : TorusSite m := fun k => ((siteCoords x k : ℤ) : ZMod m)
theorem readAtLevel_torusFrame (W : TorusField m) (x : (torusFrame L t m).Cell) (i : Fin 4) :
    readAtLevel (torusFrame L t m) (torusFrame L t m).top W x i = W (siteOfCell x) i := rfl
theorem siteOfCell_torusSiteInFrame (y : TorusSite m) :
    siteOfCell (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top y) = y := by
  funext k
  have h := castInt_intCast (period_torusFrame (L := L) (t := t) (m := m) k) ((y k).cast : ℤ)
  simpa [siteOfCell, siteCoords, torusSiteInFrame, siteOfCoords] using h
theorem siteOfCell_add (x y : (torusFrame L t m).Cell) :
    siteOfCell (x + y) = siteOfCell x + siteOfCell y := by
  funext k
  exact castInt_add (period_torusFrame k) (x k) (y k)
theorem siteOfCell_neg (x : (torusFrame L t m).Cell) : siteOfCell (-x) = - siteOfCell x := by
  funext k
  exact castInt_neg (period_torusFrame k) (x k)
theorem siteOfCell_siteOfCoords (h : Fin 4 → ℤ) :
    siteOfCell (siteOfCoords (torusFrame L t m).top h : (torusFrame L t m).Cell) = siteOfInt h := by
  funext k
  exact castInt_intCast (period_torusFrame k) (h k)
theorem siteOfCell_unitStep (i : Fin 4) :
    siteOfCell (BlockAverages.unitStep (torusFrame L t m).top i : (torusFrame L t m).Cell) =
      TorusFields.unitStep m i := by
  unfold BlockAverages.unitStep
  rw [siteOfCell_siteOfCoords, unitStep_eq_siteOfInt]
theorem siteOfCell_injective {x y : (torusFrame L t m).Cell} (h : siteOfCell x = siteOfCell y) :
    x = y := by
  funext k
  exact castInt_injective (period_torusFrame k) (x k) (y k) (congrFun h k)
theorem torusSiteInFrame_siteOfCell (x : (torusFrame L t m).Cell) :
    torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top (siteOfCell x) = x :=
  siteOfCell_injective (siteOfCell_torusSiteInFrame _)
theorem valMinAbs_sub_castInt {p q : ℕ} (hp : p = q) [NeZero p] (a b : ZMod p) :
    (a - b).valMinAbs = (((a.cast : ℤ) : ZMod q) - ((b.cast : ℤ) : ZMod q)).valMinAbs := by
  subst hp
  simp
theorem cellSupDist_torusFrame (x z : (torusFrame L t m).Cell) :
    cellSupDist x z = supDist (siteOfCell x) (siteOfCell z) := by
  unfold cellSupDist supDist
  refine Finset.sup_congr rfl fun i _ => ?_
  rw [valMinAbs_sub_castInt (period_torusFrame i)]
  rfl
theorem mem_sitesOfCells_torusFrame (S : Finset (torusFrame L t m).Cell) (x : (torusFrame L t m).Cell) :
    x ∈ sitesOfCells S (torusFrame L t m).top ↔ x ∈ S := by
  have hc : ∀ z : (torusFrame L t m).Cell, cellCentre (torusFrame L t m).top z = z := by
    intro z
    funext i
    simp [cellCentre, siteOfCoords, siteCoords]
  unfold sitesOfCells
  simp only [Finset.mem_biUnion, Finset.mem_image, Nat.sub_self, pow_zero]
  constructor
  · rintro ⟨z, hz, h, hh, rfl⟩
    have h0 : h = 0 := by
      funext i
      have := Fintype.mem_piFinset.mp hh i
      simpa using this
    subst h0
    have : (siteOfCoords (torusFrame L t m).top (0 : Fin 4 → ℤ) : (torusFrame L t m).Cell) = 0 := by
      funext i
      simp [siteOfCoords]
    rw [this, add_zero, hc]
    exact hz
  · intro hx
    refine ⟨x, hx, 0, ?_, ?_⟩
    · refine Fintype.mem_piFinset.mpr fun i => ?_
      simp
    · have : (siteOfCoords (torusFrame L t m).top (0 : Fin 4 → ℤ) : (torusFrame L t m).Cell) = 0 := by
        funext i
        simp [siteOfCoords]
      rw [this, add_zero, hc]
theorem plaquetteDefect_torusFrame (W : TorusField m) (x : (torusFrame L t m).Cell) (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel (torusFrame L t m) (torusFrame L t m).top W) (x, μ, ν) =
      TorusFields.curvature W (siteOfCell x) μ ν := by
  unfold plaquetteDefect TorusFields.curvature TorusFields.holonomy
  have hv : plaquetteHolonomy (readAtLevel (torusFrame L t m) (torusFrame L t m).top W) (x, μ, ν) =
      W (siteOfCell x) μ * W (siteOfCell x + TorusFields.unitStep m μ) ν *
        (W (siteOfCell x + TorusFields.unitStep m ν) μ)⁻¹ * (W (siteOfCell x) ν)⁻¹ := by
    have a1 : x + BlockAverages.unitStep (torusFrame L t m).top μ +
        BlockAverages.unitStep (torusFrame L t m).top ν - BlockAverages.unitStep (torusFrame L t m).top μ =
        x + BlockAverages.unitStep (torusFrame L t m).top ν := by abel
    have a2 : x + BlockAverages.unitStep (torusFrame L t m).top μ +
        BlockAverages.unitStep (torusFrame L t m).top ν + -BlockAverages.unitStep (torusFrame L t m).top μ -
        BlockAverages.unitStep (torusFrame L t m).top ν = x := by abel
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
      if_false, mul_one, a1, a2, readAtLevel_torusFrame, siteOfCell_add, siteOfCell_unitStep, mul_assoc]
  rw [hv]
theorem isOrthantRegular_torusFrame {X : Finset (TorusSite m)} {k : ℕ} (h : IsLocallyOrthantClosed X k) :
    IsOrthantRegular (cellsOfSites (torusFrame L t m) X) k := by
  intro z
  obtain ⟨eps, he, hX⟩ := h (siteOfCell z)
  refine ⟨eps, he, ?_⟩
  intro q hq hd v hv hb
  obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hq
  have hq' : cellSupDist (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top q₀) z ≤ k := hd
  rw [cellSupDist_torusFrame, siteOfCell_torusSiteInFrame] at hq'
  have := hX q₀ hq₀ hq' v hv hb
  refine Finset.mem_image.mpr ⟨q₀ + siteOfInt v, this, ?_⟩
  apply siteOfCell_injective
  show siteOfCell (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top (q₀ + siteOfInt v)) =
    siteOfCell (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top q₀ +
      siteOfCoords (torusFrame L t m).top v)
  rw [siteOfCell_torusSiteInFrame, siteOfCell_add, siteOfCell_siteOfCoords, siteOfCell_torusSiteInFrame]
theorem mem_cellsOfSites_torusFrame {X : Finset (TorusSite m)} {x : (torusFrame L t m).Cell} :
    x ∈ cellsOfSites (torusFrame L t m) X ↔ siteOfCell x ∈ X := by
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
    have : siteOfCell (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top q) = q :=
      siteOfCell_torusSiteInFrame q
    rw [show (siteOfCoords (torusFrame L t m).top fun i => ((q i).cast : ℤ)) =
      torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top q from rfl, this]
    exact hq
  · intro h
    exact Finset.mem_image.mpr ⟨_, h, torusSiteInFrame_siteOfCell x⟩
theorem isCold_torusFrame {X : Finset (TorusSite m)} {s : ℝ} {W : TorusField m} (h : IsColdOn X s W) :
    BlockAverages.IsCold (cellsOfSites (torusFrame L t m) X) (torusFrame L t m).top s
      (readAtLevel (torusFrame L t m) (torusFrame L t m).top W) := by
  rintro ⟨x, μ, ν⟩ hp
  simp only [innerPlaquettes, Finset.mem_filter] at hp
  obtain ⟨_, hlt, hc⟩ := hp
  rw [plaquetteDefect_torusFrame]
  have key : ∀ c ∈ plaquetteCorners ((x, μ, ν) : (torusFrame L t m).Cell × Fin 4 × Fin 4),
      siteOfCell c ∈ X := fun c hcm =>
    mem_cellsOfSites_torusFrame.mp ((mem_sitesOfCells_torusFrame _ _).mp (hc hcm))
  refine h _ μ ν hlt fun z hz => ?_
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact key x (by simp [plaquetteCorners])
  · have := key (x + BlockAverages.unitStep _ μ) (by simp [plaquetteCorners])
    rwa [siteOfCell_add, siteOfCell_unitStep] at this
  · have := key (x + BlockAverages.unitStep _ ν) (by simp [plaquetteCorners])
    rwa [siteOfCell_add, siteOfCell_unitStep] at this
  · have := key (x + BlockAverages.unitStep _ μ + BlockAverages.unitStep _ ν) (by simp [plaquetteCorners])
    rwa [siteOfCell_add, siteOfCell_add, siteOfCell_unitStep, siteOfCell_unitStep] at this
theorem isAdmissibleAmbient_torusFrame (h : 64 ≤ m) : IsAdmissibleAmbient (torusFrame L t m) :=
  Or.inr fun _ => h
end CellsAsSites
section Lipschitz
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem norm_mul_sub_mul_le (g h g' h' : UnitQuaternion) :
    ‖((g * h : UnitQuaternion) : ℍ[ℝ]) - ((g' * h' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(g : ℍ[ℝ]) - g'‖ + ‖(h : ℍ[ℝ]) - h'‖ := by apply _root_.YangMills.Construction.BlockAverages.CriticalShare.norm_coe_mul_sub_coe_mul_le <;> assumption
theorem norm_inv_sub_inv (g h : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((h⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(g : ℍ[ℝ]) - h‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
variable {m : ℕ}
theorem norm_holonomy_sub_le (W W' : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    ‖((TorusFields.holonomy W x μ ν : UnitQuaternion) : ℍ[ℝ]) - TorusFields.holonomy W' x μ ν‖ ≤
      ‖(W x μ : ℍ[ℝ]) - W' x μ‖ +
        ‖(W (x + TorusFields.unitStep m μ) ν : ℍ[ℝ]) - W' (x + TorusFields.unitStep m μ) ν‖ +
        ‖(W (x + TorusFields.unitStep m ν) μ : ℍ[ℝ]) - W' (x + TorusFields.unitStep m ν) μ‖ +
        ‖(W x ν : ℍ[ℝ]) - W' x ν‖ := by
  unfold TorusFields.holonomy
  refine (norm_mul_sub_mul_le _ _ _ _).trans ?_
  have h1 := norm_mul_sub_mul_le (W x μ * W (x + TorusFields.unitStep m μ) ν)
    (W (x + TorusFields.unitStep m ν) μ)⁻¹
    (W' x μ * W' (x + TorusFields.unitStep m μ) ν) (W' (x + TorusFields.unitStep m ν) μ)⁻¹
  have h2 := norm_mul_sub_mul_le (W x μ) (W (x + TorusFields.unitStep m μ) ν) (W' x μ)
    (W' (x + TorusFields.unitStep m μ) ν)
  rw [norm_inv_sub_inv] at h1 ⊢
  linarith
theorem curvature_le_add (W W' : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    TorusFields.curvature W x μ ν ≤ TorusFields.curvature W' x μ ν +
      (‖(W x μ : ℍ[ℝ]) - W' x μ‖ +
        ‖(W (x + TorusFields.unitStep m μ) ν : ℍ[ℝ]) - W' (x + TorusFields.unitStep m μ) ν‖ +
        ‖(W (x + TorusFields.unitStep m ν) μ : ℍ[ℝ]) - W' (x + TorusFields.unitStep m ν) μ‖ +
        ‖(W x ν : ℍ[ℝ]) - W' x ν‖) := by apply _root_.YangMills.Construction.TopLevelSites.curvature_le_add <;> assumption
theorem plaquetteEnergy_le_two (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    plaquetteEnergy W x μ ν ≤ 2 := by
  unfold plaquetteEnergy
  have h := abs_re_le_norm ((TorusFields.holonomy W x μ ν : UnitQuaternion) : ℍ[ℝ])
  rw [norm_unitQuaternion] at h
  have := (abs_le.mp h).1
  linarith
theorem norm_expUnit_sub_one_le (v : imaginaryQuaternions) :
    ‖((expUnit v : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(v : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.SmallCellTerms.norm_coe_expUnit_sub_one_le <;> assumption
theorem expUnit_smul_mul (v : imaginaryQuaternions) (p q : ℝ) :
    expUnit (p • v) * expUnit (q • v) = expUnit ((p + q) • v) := by
  apply Subtype.ext
  show NormedSpace.exp ((p • v : imaginaryQuaternions) : ℍ[ℝ]) *
      NormedSpace.exp ((q • v : imaginaryQuaternions) : ℍ[ℝ]) =
    NormedSpace.exp (((p + q) • v : imaginaryQuaternions) : ℍ[ℝ])
  have hc : Commute ((p • v : imaginaryQuaternions) : ℍ[ℝ]) ((q • v : imaginaryQuaternions) : ℍ[ℝ]) := by
    simp only [Submodule.coe_smul]
    exact ((Commute.refl _).smul_left _).smul_right _
  have hr : ∀ z : ℍ[ℝ], z ∈ Metric.eball (0 : ℍ[ℝ]) (NormedSpace.expSeries ℝ ℍ[ℝ]).radius := fun z =>
    (NormedSpace.expSeries_radius_eq_top ℝ ℍ[ℝ]).symm ▸ edist_lt_top _ _
  rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hc (hr _) (hr _)]
  congr 1
  simp [add_smul]
end Lipschitz
end YangMills.Construction.TorusFrame
end
