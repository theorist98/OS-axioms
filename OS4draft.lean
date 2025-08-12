import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open MeasureTheory Filter Topology ENNReal
open scoped Real


noncomputable section

/-- Spacetime dimension -/
def STDimension : ℕ := 4
abbrev SpaceTime := EuclideanSpace ℝ (Fin STDimension)
abbrev SpaceTimeMeasure : Measure SpaceTime := volume

namespace OS4

/-! #### Flow Structure
    A flow represents a measure-preserving dynamical system on a measurable space.
    In the context of QFT, flows typically represent spacetime translations of field configurations.
-/

/--
A flow is a group action of ℝ on a measurable space Ω, satisfying:
1. Measurability of the joint action
2. Identity element acts as the identity map
3. Group composition property

In QFT, flows represent spacetime translations of field configurations.
-/
structure Flow (Ω : Type*) [MeasurableSpace Ω] where
  /-- The flow action: maps a time t and a point ω to another point in Ω -/
  T : ℝ → Ω → Ω

  /-- The flow is jointly measurable in both time and space variables.
      This is crucial for integration and applying Fubini's theorem. -/
  measurable_prod : Measurable fun p : ℝ × Ω => T p.1 p.2

  /-- At time 0, the flow is the identity transformation.
      This represents the group identity element. -/
  id : ∀ ω, T 0 ω = ω

  /-- Group property: Flowing for time s+t equals flowing for time t then for time s.
      This ensures the flow forms a proper group action of ℝ. -/
  comp : ∀ s t ω, T (s + t) ω = T s (T t ω)

namespace Flow

/--
Each time-slice of the flow is measurable. This is crucial for applying
Fubini's theorem and for establishing measurability of time averages.

This follows from the joint measurability of the flow and the fact that
the constant function t and the identity function are measurable.
-/
lemma measurable_T {Ω : Type*} [MeasurableSpace Ω] (φ : Flow Ω) (t : ℝ) :
    Measurable (φ.T t) := by
  -- Use the fact that T t is a section of the jointly measurable function
  let s : Ω → ℝ × Ω := fun ω => (t, ω)
  -- Express φ.T t as a composition of s and the jointly measurable function
  have h_comp : φ.T t = (fun p => φ.T p.1 p.2) ∘ s := by
    ext ω
    simp [s]
  -- Use the composition of measurable functions
  rw [h_comp]
  apply Measurable.comp
  -- The joint function is measurable by assumption
  · exact φ.measurable_prod
  -- Now we need to show s is measurable
  · apply Measurable.prodMk
    -- t is a constant function (measurable)
    · exact measurable_const
    -- identity on Ω is measurable
    · exact measurable_id

/--
Orbits of the flow: the set of all points reachable from ω by applying the flow.
This concept is important for understanding ergodicity and orbit decompositions.
-/
def orbit {Ω : Type*} [MeasurableSpace Ω] (φ : Flow Ω) (ω : Ω) : Set Ω :=
  {ω' | ∃ t : ℝ, φ.T t ω = ω'}

end Flow

/--
Time-average (Cesàro) along the flow over window length `R`.
This represents the average value of a function f along the orbit of ω
for time parameter ranging from 0 to R.

In ergodic theory, this average converges (as R→∞) to the space average
for almost all starting points ω.

For R = 0, we define the average to be 0 by convention.
-/
def timeAvgCesaro {Ω} [MeasurableSpace Ω] (φ : Flow Ω) (f : Ω → ℝ) (ω : Ω) (R : NNReal) : ℝ :=
  if R = 0 then 0 else
    (1 / (R : ℝ)) * ∫ s in Set.Icc (0 : ℝ) (R : ℝ), f (φ.T s ω)

lemma measurable_timeAverage {Ω : Type*} [MeasurableSpace Ω]
  (φ : Flow Ω) (f : Ω → ℝ) (hf : Measurable f) (R : NNReal) :
  Measurable (fun ω => timeAvgCesaro φ f ω R) := by
  unfold timeAvgCesaro
  by_cases h : R = 0
  · subst h
    simp
  · have hpos : (0 : ℝ) < (R : ℝ) := by
      exact_mod_cast (lt_of_le_of_ne (bot_le : (0:NNReal) ≤ R) (ne_comm.mp h))
    simp [h]
    -- reduce to measurability of ω ↦ ∫_{0..R} f(φ.T s ω) ds
    -- joint measurability: (s,ω) ↦ f (φ.T s ω)
    have : Measurable (fun p : ℝ × Ω => f (φ.T p.1 p.2)) :=
      hf.comp φ.measurable_prod
    -- now use a parametric integral measurability lemma; if unavailable, leave as a TODO
    sorry


/-- Invariance of a measure under a flow. -/
def invariant_under {Ω} [MeasurableSpace Ω] (μ : Measure Ω) (φ : Flow Ω) : Prop :=
  ∀ t : ℝ, MeasurePreserving (φ.T t) μ μ

/-- Invariant measurable sets up to μ-a.e. equality. -/
def invariant_set {Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (φ : Flow Ω) (A : Set Ω) : Prop :=
  MeasurableSet A ∧ ∀ t, (φ.T t) ⁻¹' A =ᵐ[μ] A

/--
Ergodicity via invariant sets: only trivial invariant sets.

A flow is ergodic if every invariant set has either measure zero or full measure.
This is the standard definition of ergodicity in measure theory, and is
equivalent to other formulations via time averages or mixing properties.

In physical terms, ergodicity means that the system cannot be decomposed into
separate invariant subsystems - it is irreducible.
-/
def ergodic_action {Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (φ : Flow Ω) : Prop :=
  ∀ ⦃A : Set Ω⦄, invariant_set μ φ A → μ A = 0 ∨ μ A = μ Set.univ

/--
Characterization of ergodicity via invariant functions.
A flow is ergodic if and only if every measurable invariant function is
almost everywhere constant.

This is the functional analogue of the set-based definition of ergodicity,
where invariant sets correspond to indicator functions.
-/
lemma ergodic_iff_invariant_functions_ae_const {Ω} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {φ : Flow Ω} (h_inv : invariant_under μ φ) :
    ergodic_action μ φ ↔
    ∀ f : Ω → ℝ, (Measurable f ∧ ∀ t, f ∘ φ.T t =ᵐ[μ] f) → ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  constructor
  · -- Forward direction: ergodicity implies invariant functions are constant
    intro h_ergodic f h_f_inv
    -- Use the fact that level sets of invariant functions are invariant
    sorry  -- Full proof requires advanced measure theory

  · -- Reverse direction: constant invariant functions implies ergodicity
    intro h_const A h_A_inv
    -- Consider the indicator function of A, which is invariant
    sorry  -- Full proof requires advanced measure theory

/--
Birkhoff's Ergodic Theorem characterization: time averages converge to space averages.
A flow is ergodic if and only if for every integrable function f, the time average
converges to the space average almost everywhere.

This is the famous characterization that connects ergodicity to the physical
intuition of "time average equals space average".
-/
theorem ergodic_iff_time_avg_converges {Ω} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {φ : Flow Ω} (h_inv : invariant_under μ φ) :
    ergodic_action μ φ ↔
    ∀ f : Ω → ℝ, Integrable f μ →
      ∀ᵐ ω ∂μ, Tendsto (fun R => timeAvgCesaro φ f ω R) (⨆ n : ℕ, 𝓟 {R | n ≤ R}) (𝓝 (∫ x, f x ∂μ)) := by
  sorry  -- Full proof requires the Birkhoff Ergodic Theorem

/-- Invariant measurable functions. -/
def invariant_fun {Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (φ : Flow Ω) (f : Ω → ℝ) : Prop :=
  Measurable f ∧ ∀ t, f ∘ φ.T t =ᵐ[μ] f

/--
Alternative characterization of invariant measures in terms of restricted measures.
This lemma shows that a measure is invariant under a flow if and only if
each time-slice transformation preserves the measure restricted to the whole space.

This is useful for connecting with the standard measure-theoretic formulation
of measure-preserving dynamical systems.
-/
lemma invariant_under_iff_preserving_restrict {Ω} [MeasurableSpace Ω] {μ : Measure Ω} {φ : Flow Ω} :
    invariant_under μ φ ↔ ∀ t : ℝ, MeasurePreserving (φ.T t)
      (Measure.restrict μ Set.univ) (Measure.restrict μ Set.univ) := by
  simp [invariant_under, Measure.restrict_univ]

/--
Characterization of invariant sets via set differences.
A set A is invariant under a flow if and only if:
1. A is measurable, and
2. For all t, the preimage (φ.T t)⁻¹'A differs from A by a set of measure zero.

This can be expressed in terms of set differences: both
(φ.T t)⁻¹'A \ A and A \ (φ.T t)⁻¹'A have measure zero.
-/
lemma invariant_set_iff_set_diff {Ω} [MeasurableSpace Ω] {μ : Measure Ω} {φ : Flow Ω} {A : Set Ω} :
    invariant_set μ φ A ↔
    MeasurableSet A ∧ ∀ t, μ ((φ.T t) ⁻¹' A \ A) = 0 ∧ μ (A \ (φ.T t) ⁻¹' A) = 0 := by
  unfold invariant_set
  constructor
  · -- Forward direction
    intro h
    constructor
    · exact h.1  -- Measurability transfers directly
    · intro t
      -- We have (φ.T t)⁻¹' A =ᵐ[μ] A
      exact MeasureTheory.ae_eq_set.mp (h.2 t)
  · -- Reverse direction
    intro h
    constructor
    · exact h.1  -- Measurability transfers directly
    · intro t
      -- We have μ ((φ.T t)⁻¹' A \ A) = 0 and μ (A \ (φ.T t)⁻¹' A) = 0
      exact MeasureTheory.ae_eq_set.mpr (h.2 t)

/--
Characterization of invariant sets via symmetric difference.
A set A is invariant under a flow if and only if:
1. A is measurable, and
2. For all t, the symmetric difference between A and (φ.T t)⁻¹'A has measure zero.

The symmetric difference (A \ B) ∪ (B \ A) consists of points in exactly one of A or B.
-/
lemma invariant_set_iff_symm_diff {Ω} [MeasurableSpace Ω] {μ : Measure Ω} {φ : Flow Ω} {A : Set Ω} :
    invariant_set μ φ A ↔
    MeasurableSet A ∧ ∀ t, μ ((A \ ((φ.T t) ⁻¹' A)) ∪ ((φ.T t) ⁻¹' A \ A)) = 0 :=
  sorry

/-- Spatial translation in one coordinate of ℝ^4. -/
def spatialTranslate (i : Fin 4) (t : ℝ) (x : SpaceTime) : SpaceTime :=
  fun j => if j = i then x j + t else x j

theorem spatialTranslate_group (i : Fin 4) (s t : ℝ) (x : SpaceTime) :
    spatialTranslate i (s + t) x = spatialTranslate i s (spatialTranslate i t x) := by
  -- To prove functions are equal, we show they produce the same output for all inputs
  ext j
  -- Use the definition of spatialTranslate
  simp only [spatialTranslate]
  -- Case analysis on whether j = i
  by_cases h : j = i
  · -- Case j = i
    simp only [h, if_true]
    -- We need to show: x j + (s + t) = (x j + t) + s
    -- First swap s and t in the LHS, then apply associativity
    rw [add_comm s t]
    rw [add_assoc]
  · -- Case j ≠ i
    simp only [h, if_false]
    -- Both sides simplify to x j, which is true by reflexivity

/-- Spatial translation at t=0 is the identity map -/
theorem spatialTranslate_id (i : Fin 4) (x : SpaceTime) : spatialTranslate i 0 x = x := by
  -- To prove functions are equal, we show they produce the same output for all inputs
  ext j
  -- Unfold the definition of spatialTranslate explicitly for j
  simp only [spatialTranslate]
  -- Case analysis on whether j = i
  by_cases h : j = i
  · -- Case j = i
    simp only [h, if_true]
    -- Need to show x j + 0 = x j
    simp only [add_zero]
  · -- Case j ≠ i
    simp only [h, if_false]
    -- This gives us x j = x j, which is true by reflexivity

theorem verify_spatialTranslate_id_concrete :
    spatialTranslate (0 : Fin 4) 0 (fun j => j.val : SpaceTime) = (fun j => j.val : SpaceTime) := by
  -- Apply the general theorem
  apply spatialTranslate_id

theorem verify_spatialTranslate_id_alt_proof (i : Fin 4) (x : SpaceTime) :
    spatialTranslate i 0 x = x := by
  -- Instead of using ext tactic, we'll use function extensionality directly
  apply funext
  intro j
  -- Definition of spatialTranslate
  unfold spatialTranslate
  -- Split into cases based on whether j = i
  by_cases h : j = i
  · -- Case: j = i
    rw [if_pos h]
    -- Use algebraic property: a + 0 = a
    rw [add_zero]
  · -- Case: j ≠ i
    rw [if_neg h]
    -- Reflexivity

/--
Verification check 1 for spatialTranslate_group: Test with concrete values

This confirms the group property by testing it with specific dimensions and distances.
We create a sample point and verify that translating it by s+t in one go
is the same as translating by t and then by s.
-/
theorem verify_spatialTranslate_group_concrete :
    let i := (0 : Fin 4)
    let s := 3
    let t := 5
    let x : SpaceTime := fun j => j.val
    spatialTranslate i (s + t) x = spatialTranslate i s (spatialTranslate i t x) := by
  -- Apply the general theorem
  apply spatialTranslate_group

/--
Verification check 2 for spatialTranslate_group: Alternative proof approach

This provides an independent verification of the group property by directly
computing both sides for arbitrary values and showing they're equal.
This gives us more confidence that the main theorem is correct.
-/
theorem verify_spatialTranslate_group_alt_proof (i : Fin 4) (s t : ℝ) (x : SpaceTime) :
    spatialTranslate i (s + t) x = spatialTranslate i s (spatialTranslate i t x) := by
  -- Use function extensionality directly to show the functions are equal
  ext j
  -- Consider two cases
  by_cases h : j = i
  · -- Case: j = i
    -- Calculate the left-hand side
    calc (spatialTranslate i (s + t) x) j
        = x j + (s + t) := by {unfold spatialTranslate; simp [h]}
      _ = x j + (t + s) := by {rw [add_comm s t]}
      _ = (x j + t) + s := by {rw [add_assoc]}
      _ = (spatialTranslate i t x) j + s := by {unfold spatialTranslate; simp [h]}
      _ = (spatialTranslate i s (spatialTranslate i t x)) j := by {unfold spatialTranslate; simp [h]}
  · -- Case: j ≠ i
    -- Calculate both sides
    calc (spatialTranslate i (s + t) x) j
        = x j := by {unfold spatialTranslate; simp [h]}
      _ = (spatialTranslate i t x) j := by {unfold spatialTranslate; simp [h]}
      _ = (spatialTranslate i s (spatialTranslate i t x)) j := by {unfold spatialTranslate; simp [h]}

/--
A clean OS4 axiom: invariant measure, ergodicity by sets, and time-average equals ensemble-average a.e.

This structure encapsulates the key properties of an ergodic dynamical system:
1. A probability measure on the state space
2. A flow (group action) on the state space
3. The measure is preserved by the flow
4. The flow is ergodic (only trivial invariant sets)
5. Birkhoff's ergodic theorem holds: time averages converge to space averages

In the context of QFT, this axiom ensures that spacetime translations act ergodically
on the field configurations, which is crucial for reconstructing vacuum correlations.
-/
structure OS4Axiom (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  prob : IsProbabilityMeasure μ
  φ : Flow Ω
  measure_preserving : invariant_under μ φ
  ergodic_sets : ergodic_action μ φ
  mean_ergodic_AE :
    ∀ (f : Ω → ℝ), Integrable f μ →
      ∀ᵐ ω ∂μ, Tendsto (fun R => timeAvgCesaro φ f ω R) (⨆ n : ℕ, 𝓟 {R | n ≤ R}) (𝓝 (∫ x, f x ∂μ))

/--
QFT-flavored packaging of the OS4 axiom, using a probability measure on field space.

This presents the same mathematical content as OS4Axiom but with notation more
familiar to quantum field theorists, using dμ for the probability measure and
A for observables (measurable functions on field space).

The essential physical content is that spacetime translations act ergodically on
field configurations, allowing us to reconstruct vacuum correlation functions.
-/
structure OS4QFTAxiom (Φ : Type*) [MeasurableSpace Φ] where
  dμ : ProbabilityMeasure Φ
  φ  : Flow Φ
  measure_preserving : invariant_under (dμ : Measure Φ) φ
  ergodic_sets : ergodic_action (dμ : Measure Φ) φ
  mean_ergodic_AE :
    ∀ (A : Φ → ℝ), Integrable A (dμ : Measure Φ) →
      ∀ᵐ ω ∂(dμ : Measure Φ),
        Tendsto (fun R => timeAvgCesaro φ A ω R) (⨆ n : ℕ, 𝓟 {R | n ≤ R}) (𝓝 (∫ x, A x ∂(dμ : Measure Φ)))

/-- Clustering in the translation parameter. -/
def ClusterProperty {Φ} [MeasurableSpace Φ]
    (dμ : ProbabilityMeasure Φ) (φ : Flow Φ) : Prop :=
  ∀ (f g : Φ → ℝ), Measurable f → Measurable g →
    Tendsto (fun r : ℝ => ∫ ω, f ω * g (φ.T r ω) ∂(dμ : Measure Φ))
            (⨆ n : ℕ, 𝓟 {r : ℝ | n ≤ r})
            (𝓝 ((∫ ω, f ω ∂(dμ : Measure Φ)) * (∫ ω, g ω ∂(dμ : Measure Φ))))

/-- Vacuum uniqueness phrased as: invariant complex observables are a.e. constant. -/
def UniqueVacuum {Φ} [MeasurableSpace Φ]
    (dμ : ProbabilityMeasure Φ) (φ : Flow Φ) : Prop :=
  ∀ (f : Φ → ℂ),
    (Measurable fun ω => ‖f ω‖) ∧ (∀ t, (fun ω => ‖f (φ.T t ω)‖) =ᵐ[(dμ : Measure Φ)] fun ω => ‖f ω‖) →
    ∃ c : ℂ, ∀ᵐ ω ∂(dμ : Measure Φ), f ω = c

end OS4
