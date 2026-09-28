import Mathlib

/-!
# Ellipse smoothing

An axiom-free algebraic core for lifting a scalar control law to an ellipse.

The main distinction is between:

* the geometric trace, which is always the same ellipse; and
* the control law, which determines how the ellipse is traversed.

The triangular control law is proved admissible on the fundamental interval.
The smoothed odd-harmonic series is defined exactly; its analytic properties
(summability, bounds, endpoint jets and limits) are deliberately exposed as
the next proof obligations rather than postulated as axioms.
-/

namespace EllipseSmoothing

open scoped BigOperators

noncomputable section

/-- Centre and semiaxes of an axis-aligned ellipse. -/
structure Ellipse where
  cx : ℝ
  cy : ℝ
  a : ℝ
  b : ℝ

/-- Division-free ellipse equation.  For nonzero semiaxes this is equivalent
to the usual normalized equation. -/
def OnEllipse (E : Ellipse) (p : ℝ × ℝ) : Prop :=
  E.b ^ 2 * (p.1 - E.cx) ^ 2 + E.a ^ 2 * (p.2 - E.cy) ^ 2 =
    E.a ^ 2 * E.b ^ 2

/-- Lift a horizontal control value `g ∈ [-1,1]` to one of the two ellipse
branches.  The branch parameter is intended to be `+1` or `-1`. -/
def ellipseLift (E : Ellipse) (g branch : ℝ) : ℝ × ℝ :=
  (E.cx + E.a * g,
   E.cy + E.b * branch * Real.sqrt (1 - g ^ 2))

/-- The geometric invariant: every admissible scalar control value lifts to
the same ellipse, independently of how that control value was generated. -/
theorem ellipseLift_onEllipse
    (E : Ellipse) {g branch : ℝ}
    (hg : g ^ 2 ≤ 1) (hbranch : branch ^ 2 = 1) :
    OnEllipse E (ellipseLift E g branch) := by
  have hnonneg : 0 ≤ 1 - g ^ 2 := by linarith
  have hsqrt : (Real.sqrt (1 - g ^ 2)) ^ 2 = 1 - g ^ 2 := by
    simpa using Real.sq_sqrt hnonneg
  unfold OnEllipse ellipseLift
  dsimp only
  calc
    E.b ^ 2 * (E.cx + E.a * g - E.cx) ^ 2 +
          E.a ^ 2 * (E.cy + E.b * branch * Real.sqrt (1 - g ^ 2) - E.cy) ^ 2 =
        E.a ^ 2 * E.b ^ 2 *
          (g ^ 2 + branch ^ 2 * (Real.sqrt (1 - g ^ 2)) ^ 2) := by ring
    _ = E.a ^ 2 * E.b ^ 2 := by rw [hbranch, hsqrt]; ring

/-- A control law contains precisely the boundedness required by the lift. -/
structure ControlLaw (G : ℝ → ℝ) : Prop where
  sq_le_one : ∀ θ, G θ ^ 2 ≤ 1

/-- Alternating upper/lower branch. At a zero of `sin θ` the square-root term
vanishes for endpoint-preserving controls, so the branch choice is immaterial. -/
def branchSign (θ : ℝ) : ℝ :=
  if 0 ≤ Real.sin θ then 1 else -1

@[simp]
theorem branchSign_sq (θ : ℝ) : branchSign θ ^ 2 = 1 := by
  unfold branchSign
  split <;> norm_num

/-- Parametric path induced by a control function. -/
def controlledPath (E : Ellipse) (G : ℝ → ℝ) (θ : ℝ) : ℝ × ℝ :=
  ellipseLift E (G θ) (branchSign θ)

/-- Any admissible control law traces the ellipse exactly. -/
theorem controlledPath_onEllipse
    (E : Ellipse) (G : ℝ → ℝ) (hG : ControlLaw G) (θ : ℝ) :
    OnEllipse E (controlledPath E G θ) := by
  exact ellipseLift_onEllipse E (hG.sq_le_one θ) (branchSign_sq θ)

/-! ## The atomic triangular control -/

/-- Fundamental falling branch, with normalized time `u ∈ [0,1]`. -/
def triangleControl (u : ℝ) : ℝ :=
  1 - 2 * u

@[simp] theorem triangleControl_zero : triangleControl 0 = 1 := by
  simp [triangleControl]

@[simp] theorem triangleControl_one : triangleControl 1 = -1 := by
  norm_num [triangleControl]

/-- The falling linear branch never leaves the admissible interval. -/
theorem triangleControl_sq_le_one {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    triangleControl u ^ 2 ≤ 1 := by
  have hproduct : 0 ≤ u * (1 - u) :=
    mul_nonneg h0 (sub_nonneg.mpr h1)
  unfold triangleControl
  nlinarith

/-- Both halves of the atomic traversal lie on the same ellipse. -/
theorem triangleLift_onEllipse
    (E : Ellipse) {u branch : ℝ}
    (h0 : 0 ≤ u) (h1 : u ≤ 1) (hbranch : branch ^ 2 = 1) :
    OnEllipse E (ellipseLift E (triangleControl u) branch) := by
  exact ellipseLift_onEllipse E (triangleControl_sq_le_one h0 h1) hbranch

/-! ## Smoothed odd-harmonic control -/

/-- The `(2k+1)`-st odd harmonic. -/
def oddHarmonic (k : ℕ) : ℕ :=
  2 * k + 1

/-- Weight used by the normalized smoothing formula.  At `λ = 0` all odd
harmonics retain their triangular-wave weights.  At `λ = 1` only the first
harmonic survives. -/
def smoothingWeight (lam : ℝ) (k : ℕ) : ℝ :=
  (1 - lam) ^ (oddHarmonic k ^ 2 - 1) /
    (oddHarmonic k : ℝ) ^ 2

/-- Denominator of the normalized infinite control series. -/
def smoothDenominator (lam : ℝ) : ℝ :=
  ∑' k : ℕ, smoothingWeight lam k

/-- Numerator of the normalized infinite control series. -/
def smoothNumerator (lam θ : ℝ) : ℝ :=
  ∑' k : ℕ,
    smoothingWeight lam k * Real.cos ((oddHarmonic k : ℝ) * θ)

/-- The exact smoothing formula from the model. -/
def smoothControl (lam θ : ℝ) : ℝ :=
  smoothNumerator lam θ / smoothDenominator lam

/-- The corresponding smoothed ellipse traversal. -/
def smoothedPath (E : Ellipse) (lam θ : ℝ) : ℝ × ℝ :=
  controlledPath E (smoothControl lam) θ

/-- Once the analytic bound is discharged, the smoothed series inherits the
ellipse invariant for free.  This theorem isolates the remaining analysis from
the already completed algebraic geometry. -/
theorem smoothedPath_onEllipse
    (E : Ellipse) (lam θ : ℝ)
    (hbound : smoothControl lam θ ^ 2 ≤ 1) :
    OnEllipse E (smoothedPath E lam θ) := by
  unfold smoothedPath controlledPath
  exact ellipseLift_onEllipse E hbound (branchSign_sq θ)

/-! ## Explicit audit statements -/

#check ellipseLift_onEllipse
#check controlledPath_onEllipse
#check triangleLift_onEllipse
#check smoothedPath_onEllipse

end

end EllipseSmoothing
