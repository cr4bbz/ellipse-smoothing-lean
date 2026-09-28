# Ellipse smoothing in Lean 4

This gate formalizes the structural claim behind the model:

> Changing the control law changes the traversal, not the ellipse invariant.

## What is already proved

- a division-free ellipse invariant;
- the generic square-root lift from any value `g` with `g² ≤ 1`;
- independence from the upper/lower branch;
- admissibility and endpoints of the normalized triangular branch;
- inheritance of the ellipse invariant by any bounded control law;
- the exact infinite odd-harmonic smoothing formula.

No project-specific axioms or `sorry` declarations are used.

## Intentionally separated analytic obligations

The next gate should prove, for `0 ≤ λ ≤ 1`:

1. summability and positivity of `smoothDenominator`;
2. `smoothControl λ θ ^ 2 ≤ 1`;
3. `smoothControl 0 θ` equals the periodic triangle wave;
4. `smoothControl 1 θ = cos θ`;
5. smoothness for `0 < λ` and the finite endpoint-speed formula.

The last theorem in the current gate shows that item 2 is the only fact needed
to transfer the already-proved ellipse invariant to the smoothed path.

## Local build

Clang is sufficient as the native compiler dependency. In PowerShell:

```powershell
lake update
lake exe cache get
lake build
```

To inspect the theorem dependencies in a temporary Lean file:

```lean
import EllipseSmoothing

#print axioms EllipseSmoothing.ellipseLift_onEllipse
#print axioms EllipseSmoothing.triangleLift_onEllipse
#print axioms EllipseSmoothing.smoothedPath_onEllipse
```

The project targets Lean `v4.30.0` and the matching mathlib tag.
