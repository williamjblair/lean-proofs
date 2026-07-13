# Hostile audit: GPT Pro centered-interval passes

## Dependency tree and per-node verdicts

```text
Exact block equation                                      BANKED
+- one-factorial centered-lcm compression (D)            ALREADY BANKED
+- sharp ratio 1218443*k*d < 1853952*n                   BANKED
|  +- coarse exact ratio 13*k*d < 20*n                   NEW, PROVED
|  +- product lower bound                                NEW, PROVED
+- centered interval product/lcm bridge                  NEW, PROVED
|  +- Kummer carry bound for every interval term         NEW, PROVED
|  +- m!*L_interval | B_interval*Lambda(m)               NEW, PROVED
|  +- Lambda(m) <= 4^m                                   NEW, PROVED
|  +- centered product < d^(2*k-1)                       NEW, PROVED
+- factorial-tail pairing                                NEW, PROVED
|  +- all terms paired when k is even                    NEW, PROVED
|  +- one term >= k retained when k is odd               NEW, PROVED
|  +- exact pair-unit certificate under 18*d<=k^2        NEW, PROVED
+- quadratic_strip_certificate                           NEW, PROVED
   +- no_four_solution_of_quadratic_strip, all parities  NEW, PROVED

+- reflection-center square lift                         ALREADY BANKED
|  +- 2*q^2 < 5*H                                        NEW, PROVED
+- paired centered polynomial                            NEW, PROVED
|  +- gcd(d,H) | (k-1)!!                                 NEW, PROVED
+- parity-free logarithmic strips                        NEW, PROVED

Full uniform large-row theorem                           OPEN
```

No theorem-strength assertion is hidden behind words such as “essentially”
or “uniformly.”  The new theorem's exact hypotheses are:

```text
16 <= k,
k <= d,
18*d <= k^2.
```

## Adversarial boundaries and falsifiers

| Boundary or falsifier | Exact verdict |
| --- | --- |
| Parity restriction in the submitted quadratic theorem | **UNNECESSARY**.  The Lean theorem covers odd and even `k`. |
| `k=16,17` | **VACUOUS STRIP** because no `d>=k` satisfies `18*d<=k^2`. |
| First nonempty boundary | **PASS** at exactly `(k,d)=(18,18)`; the exact certificate is reproduced. |
| Standalone boxed B | **FAILS** at `(3,0,1)`, `H=5`; inherited even/large-gap hypotheses are mandatory. |
| `d=k`, reflected owner `i=k` | **PASS**; `H-2(n+i)=1`, so strictness survives. |
| Prime boundary `p=k` in the gcd corollary | **PASS**; the theorem explicitly includes `k<=p`. |
| `(984,3177026,4480)` | **PASS** as a non-equation fixture and is inside the quadratic strip since `18*4480<=984^2`.  Its old logarithmic endpoints remain `1476,1640`. |
| `(244,48502,277)` | **PASS** as a non-equation fixture and is inside the quadratic strip since `18*277<=244^2`. |
| Row-22 pseudo-fixture | **OUTSIDE** the quadratic strip; `gcd(d,H)=1` and the exact equation is false. |
| Even `d=1` telescopes `(6,1,1)`, `(12,3,1)` | **OUTSIDE** `d>=k`; they remain valid gcd checks. |
| Odd `d=1` telescopes and MalekZ `k=5` family | **OUTSIDE** the large-row and gap hypotheses. |
| Finite per-row search | **NOT USED** as a proof premise. |
| `native_decide` | **ABSENT**. |

## Exact-arithmetic reproduction verdict

The checker uses arbitrary-precision integers, deterministic trial-division
primality where needed, and exact divisibility.  Its finite scans are
reproductions, not premises of the Lean theorem.  In particular it checks
the factorial-scaled certificate itself, not a floating approximation to its
logarithm.

## Kernel verdict

Direct compilation:

```text
lake env lean ErdosProblems/Erdos686CenterComponentLogStrip.lean
```

prints only `[propext, Classical.choice, Quot.sound]` for the new interval,
lcm, certificate, and strip headline theorems.

## Exact remaining gap

After this pass, any hypothetical large-row solution not already excluded by
the portfolio must satisfy the single quantified complement

```text
k >= 16,
k <= d,
18*d > k^2.
```

It must also satisfy all previously banked ratio, smoothness, owner,
component, matching, and centered-support restrictions.  The present proof
does not aggregate those restrictions into a contradiction in this
superquadratic-complement region.  An assertion that a contradiction-producing
owner always exists there would be target-strength and is not counted as
progress without a proof.
