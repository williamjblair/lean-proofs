# Erdős 686 Two-Prime Second Lift Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove an exact second-order local congruence and use a finite fixed-row certificate to exclude every target-size odd-tail solution whose gap has two distinct prime-power components with bases at least the block length.

**Architecture:** Define the constant and linear coefficients of the local cofactor polynomial, prove its remainder after those two terms is divisible by the square of the local variable, and combine this with the exact block equation after dividing by the concentrated prime power.  An exact Python table will verify that the two fixed obstruction integers cannot vanish simultaneously and will supply a uniform explicit bound small enough for `10^120`; Lean will consume only transparent finite arithmetic, never the Python result as an oracle.

**Tech Stack:** Lean 4.29.1, mathlib, exact Python integer arithmetic, pytest.

---

### Task 1: Audit the algebra and build the exact table

**Files:**
- Create: `compute/campaign686/two_prime_second_lift_verify.py`
- Create: `compute/campaign686/test_two_prime_second_lift_verify.py`

**Step 1:** Define exact signed coefficients

```python
def local_coefficients(k: int, i: int) -> tuple[int, int]:
    offsets = [j - i for j in range(1, k + 1) if j != i]
    C = math.prod(offsets)
    D = sum(math.prod(offsets[:t] + offsets[t + 1 :]) for t in range(len(offsets)))
    return C, D
```

**Step 2:** Exhaustively enumerate each target row, distinct noncentral `i,j`, `1 <= a,b`, and `a*b < A^2`; record

```text
X = C_i*a*b + 4*D_i*(i-j)
Y = C_j*a*b - 4*D_j*(i-j).
```

Assert `(X,Y) != (0,0)` and record the maximum of `abs(X)` and `abs(Y)`.

**Step 3:** Add sign-regression tests by expanding the block equation modulo symbolic prime powers on small exact fixtures.

**Step 4:** Run `python3 -m pytest compute/campaign686/test_two_prime_second_lift_verify.py -q`; expect all tests to pass or an exact zero witness to terminate the route.

### Task 2: Prove the local cofactor expansion and second lift

**Files:**
- Create: `ErdosProblems/Erdos686TwoPrimeSecondLift.lean`

**Step 1:** Define transparent signed coefficients `localSecondConstant` and `localSecondLinear` from the offset finset.

**Step 2:** Prove for every integer `z` that

```text
z^2 ∣ Q_i(z) - C_i - D_i*z.
```

Use finite-product induction, keeping the invariant `Q=C+D*z+z^2*R`.

**Step 3:** For `h | d`, `h | n+i`, `d=h*m`, and `3(n+i)-d=a*h^2`, rewrite the exact block equation and prove

```text
h ∣ 3*C_i*a - 4*D_i*m^2.
```

Keep all divisions witness-based (`d=h*m`), and perform the calculation in `ℤ` to avoid natural subtraction.

**Step 4:** Compile with `lake env lean ErdosProblems/Erdos686TwoPrimeSecondLift.lean`; expect no errors and no forbidden declarations.

### Task 3: Derive the two fixed obstruction divisibilities

**Files:**
- Modify only the new Lean module.

**Step 1:** From `d=P*Q`, the two residual identities, and

```text
a*P^2 - b*Q^2 = 3*(i-j),
```

prove exactly

```text
P ∣ 3*(C_i*a*b + 4*D_i*(i-j)),
Q ∣ 3*(C_j*a*b - 4*D_j*(i-j)).
```

**Step 2:** Under prime bases at least five, cancel the factor `3` from each prime-power divisor.

**Step 3:** Convert nonzero signed divisibility into natural bounds by `Int.natAbs` without changing either sign.

### Task 4: Formalize the finite nonzero certificate and close the clean regime

**Files:**
- Modify only the new Lean module.
- Create: `compute/campaign686/two_prime_second_lift_findings.md`

**Step 1:** State a transparent fixed-row predicate for `k,A,i,j,a,b` and prove its six instances by bounded interval splitting and `norm_num`/`native_decide`-free arithmetic.

**Step 2:** Use `a*b<A^2`, positivity, and the exact table maximum `M` to show at least one of `P,Q` is at most `M`.

**Step 3:** Use the already-proved Pell ratio bounds `a*P<A*Q` and `b*Q<A*P` to bound the other component and prove `P*Q<10^120`.

**Step 4:** Add six unconditional wrappers for `k=5,7,9,11,13,15` excluding two-large-prime target-size gaps.

### Task 5: Verify the intake

**Files:**
- New files only; do not edit `Audit.lean`, `proofs.yaml`, or shared dashboards.

**Step 1:** Run the focused pytest file.

**Step 2:** Run direct Lean compilation and `lake build ErdosProblems.Erdos686TwoPrimeSecondLift`.

**Step 3:** Print axioms for the local lift, the fixed obstruction theorem, and all six wrappers; require a subset of `[propext, Classical.choice, Quot.sound]`.

**Step 4:** Scan for `sorry`, `admit`, `axiom`, `native_decide`, and `unsafe`; require no forbidden source declarations.

**Step 5:** Record exact SHA-256 hashes and the single remaining regime if the route closes only the clean large-prime slice.
