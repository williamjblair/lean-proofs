# Hostile audit: the `k=22` quadratic/Runge/local-sieve probe

## Verdict

**PASS as a rigorously scoped failed-route artifact.  This is not a proof that
the row `k=22` is closed.**

The exact arithmetic establishes a useful Runge trap and reproduces a bounded
prime-field sieve, but the sieve currently has no kernel-feasible certificate
representation.  In particular, the Python packed-integer calculation is not
a substitute for Lean, and `native_decide` is forbidden.

## Dependency tree

| Node | Exact statement | Evidence | Verdict |
|---|---|---|---|
| Q | The all-parity quadratic theorem covers exactly `22<=d<=26` at `k=22`; its strict complement starts at `d=27`. | `18*26=468<=484<486=18*27`; the theorem itself is banked in `Erdos686CenterComponentLogStrip.lean`. | PASS |
| A | The centered data have scale `256`, `deg T=11`, `deg D=10`, `T^2=256^2*S+D`, and fixed divisor `33|T(2a+1)`. | Exact reconstruction from elementary symmetric functions and `Fraction`; first twelve values plus extra-value audit. | PASS |
| R27 | For every hypothetical solution with `d>=27`, `m=T(w)-2T(v)` obeys `-1161715983142<m<0` and `33|m`. | Exact power bracket, 78 positive shifted coefficients, 11 negative upper coefficients. | PASS |
| F | The unrestricted local-mask route at R27 can never close. | Three exact integral root pairs below. | **FALSIFIED** |
| R250 | At `d>=250`, the coefficientwise-minimal integer trap is `-125239835548<m<0`; hence `m=-33t` with `1<=t<=3795146531`. | The bound has 78 positive coefficients; at one less, the constant coefficient is negative. | PASS |
| S | Parity and the `p=23` mask compress R250 to exactly 330,012,742 candidates; all effective prime masks through `p=953` leave zero candidates in an exact packed-integer reproduction. | Exact Python integers only; no floating point or probabilistic hashing. | PASS as arithmetic reproduction |
| K | The R250 sieve has a proof-producing ordinary-kernel certificate of feasible size. | No such certificate is supplied. Direct enumeration still has 330,012,742 compressed candidates. | **OPEN** |

## Exact centered data

For

```text
S(W)=product_{j=1}^{11}(W^2-(2j-1)^2),
```

the verifier reconstructs

```text
T(W)=256W^11-226688W^9+67609696W^7-8111362160W^5
     +352497378310W^3-6055670906453W,

D(W)=463278576995462272W^10-216425162804858318080W^8
     +31355359404386247301764W^6
     -1470309582711394865435644W^4
     +21668018076062298043697209W^2
     +12389157521837708451840000,
```

with `T(W)^2=256^2*S(W)+D(W)`.  The odd-argument fixed divisor is
exactly `33`.

The explicit coefficient-certificate threshold from these concrete data is

```text
355590574284571694620549691.
```

This number is an exact instance of the universal construction.  It is not a
claim that Lean's noncomputable choice term definitionally reduces to this
numeral.

## The unrestricted root fixtures

The trap beginning at `d=27` leaves

```text
1 <= t <= 35203514640,   m=-33t.
```

No collection of unrestricted local masks of the form

```text
exists w,v (mod q), S(w)=4S(v), T(w)-2T(v)=-33t
```

can remove the following values:

| `t` | `(w,v)` | `T(w)` | `T(v)` | `m` |
|---:|:---:|---:|---:|---:|
| 28,643,526,033 | `(-3,-1)` | 10,477,198,654,989 | 5,711,217,507,039 | -945,236,359,089 |
| 19,687,413,989 | `(-7,-1)` | 10,772,750,352,441 | 5,711,217,507,039 | -649,684,661,637 |
| 3,809,308,513 | `(13,15)` | -18,690,506,282,019 | -9,282,399,550,545 | -125,707,180,929 |

Every displayed `w` and `v` is a signed odd root of `S`, so
`S(w)=S(v)=0` over the integers.  The displayed `m=-33t` identities are also
integer identities.  Consequently these witnesses survive reduction modulo
every positive modulus, not merely every tested prime.  They are outside the
positive large-center domain and are not block-product solutions; their role
is to falsify an over-broad local cover.

## Corrected `d>=250` trap

The exact brackets

```text
4*15^22 < 16^22,      82^22 < 4*77^22
```

give `n>=15d-21`, and therefore at `d>=250`

```text
v>=7481,  w>=7981,  14w<=15v.
```

For

```text
B=125239835548,
```

all 78 coefficients of

```text
D(w)+B*T(w)+2B*T(v)-4D(v)
```

after `v=7481+a`, `w=7981+a+b` are positive.  The least is
`32061397900288`, at degree `(a^0,b^11)`.  At `B-1`, the constant
coefficient is

```text
-1817345074172497194186936919169215485171977862,
```

so `B` is the coefficientwise-minimal integer bound for this shifted proof.
The conservative upper polynomial under `14w<=15v` has eleven strictly
negative shifted coefficients.  Thus a hypothetical solution has

```text
m=-33t,  1<=t<=3795146531.
```

The three universal root fixtures all lie strictly above this corrected
bound.

On the remaining strip `27<=d<=249`, the two exact ratio brackets leave
exactly 16,859 `(d,n)` pairs, with `n<=3833`.  Direct integer evaluation finds
no equality.  The smallest absolute error is

```text
40621652211656167398869943532480959321608781848296764211200000
```

at `(d,n)=(28,419)`.  This finite scan is reproduced here but is not Lean
banked by this artifact.

## Bounded sieve and the kernel gap

Since `T` is odd on odd inputs, `m` and `t` are odd.  Modulo 23 the exact
unrestricted mask is

```text
t mod 23 in {2,6,17,21}.
```

Equivalently,

```text
t=46q+a,  a in {17,21,25,29}.
```

The four exact branch lengths are

```text
82503186, 82503186, 82503185, 82503185,
```

for a total of 330,012,742 candidates.  The verifier represents each branch
as a Python integer bitset and intersects every nontrivial unrestricted prime
mask through 953.  The last counts are

```text
p=857: 11, 859: 11, 863: 8, 877: 6, 881: 4, 883: 3,
887: 3, 907: 2, 911: 2, 919: 1, 929: 1, 937: 1,
941: 1, 947: 1, 953: 0.
```

This is exact arithmetic, but it is not yet intake step 3.  A direct
`by decide` theorem over 330 million candidates is not a credible ordinary
kernel certificate.  A future closure needs either:

1. a proof-producing packed-bitset/reflection lemma whose own kernel checking
   remains within the axiom and resource gates; or
2. new mathematics that compresses the candidate interval before the local
   cover.

Until one of those exists and compiles, `k=22` remains open.

## Reproduction

```bash
PYTHONDONTWRITEBYTECODE=1 python3 \
  compute/campaign686/agent_k22_sieve_probe/k22_sieve_probe_verify.py --pretty

PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  compute/campaign686/agent_k22_sieve_probe/test_k22_sieve_probe_verify.py
```

The verifier uses only Python integers, `Fraction`, and exact polynomial
arithmetic.  It imports neither NumPy nor a computer algebra system.

The canonical JSON payload SHA-256 at this checkpoint is

```text
322a6e04727cb85cf097938fed19f57698fb10bbaf9a1ae4b7813c84114e3ed4
```
