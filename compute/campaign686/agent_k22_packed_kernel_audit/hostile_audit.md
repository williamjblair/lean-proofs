# Hostile audit: k=22 packed-kernel cover

## Verdict

**FAIL at the Lean kernel gate.**  The independently reconstructed arithmetic
and the generated source snapshot passed, but the production
`Erdos686EvenK22Tables.olean` used to compile `PackedDefs` was a temporary
stub object containing named axioms.  Consequently no table theorem, packed
shard theorem, or packed-cover theorem built through that object is admissible.

The contaminated generated sources and object files were subsequently
quarantined/removed.  This is the correct current state: the packed cover is a
source-level candidate, not a banked Lean theorem.

## Exact failure witness

The audit module imported the installed packed definitions and asked Lean for
the axiom sets of representative table theorems.  Lean reported:

```text
'Erdos686.Erdos686Variant.even22_allowed_83' depends on axioms:
[propext, Quot.sound, even22_allowed_83]

'Erdos686.Erdos686Variant.even22_allowed_953' depends on axioms:
[propext, Quot.sound, even22_allowed_953]
```

The last entries are theorem-specific named axioms, outside the permitted gate
`[propext, Classical.choice, Quot.sound]`.  They came from the temporary stub
producer `generate_stub_tables.py`, not from the real generated table proofs.
Any successful downstream typecheck against that aggregate object is therefore
invalid evidence.

After quarantine, the same audit correctly stops at the missing
`Erdos686EvenK22PackedDefs.olean`; it cannot accidentally reuse the stub.

## Dependency tree and node verdicts

```text
Erdos686EvenK22Defs                         source arithmetic PASS
  -> Erdos686EvenK22TableDefs               133 masks PASS
     -> 602 TableP<p>S<s> shards            generated source PASS; kernel unbuilt
        -> 133 TableP<p> dispatch modules   generated source PASS; kernel unbuilt
           -> Tables                        FAIL: installed object was an axiom stub
              -> PackedDefs                 INADMISSIBLE downstream of FAIL
                 -> 24 PackedB<b>S<s>       arithmetic/source PASS; kernel unbuilt
                    -> PackedShards         unbuilt
                       -> PackedCover       unbuilt
```

No theorem below `Tables` may be promoted until all 602 real table shards, all
133 dispatch modules, `Tables`, `PackedDefs`, all 24 packed shards, and the
terminal cover have been rebuilt from the checked sources, followed by
`#print axioms` at the terminal theorem.

## Independent exact-arithmetic reproduction

The verifier in this directory does not import the producer generator or its
k=22 arithmetic verifier.  It independently:

1. reconstructs
   `S(W) = product_{j=1}^{11} (W^2 - (2j-1)^2)`;
2. reconstructs the scaled square-root polynomial
   `T(W) = 256 W^11 - 226688 W^9 + 67609696 W^7 - 8111362160 W^5
   + 352497378310 W^3 - 6055670906453 W`;
3. enumerates `S(w)=4S(v)` over each prime field and forms the direct
   `m=T(w)-2T(v)` set;
4. verifies every generated table mask uses exactly those `m` residues;
5. independently applies `m=-33t`, then
   `t=46q+b`, so the local-index mask at chunk offset `lo` is
   `q_residue-lo (mod p)`; and
6. intersects Python integer bitsets for every chunk.

The checked source snapshot had:

- scale `256`;
- 133 table primes (`23` plus 132 active primes from `83` through `953`);
- 602 table shards and 737 generated table files;
- branch residues `(17,21,25,29)` modulo 46;
- branch lengths `82,503,186`, `82,503,186`, `82,503,185`,
  `82,503,185`, totaling `330,012,742` candidates;
- 24 chunks: five of width `16,000,000` and one terminal chunk per branch;
- no `native_decide`, `sorry`, or `admit` in the 764 generated
  table/packed files; and
- no missing source imports at the time of reproduction.

The source-level payload digest was
`2af4adf0aad0459fd3af2cb4d80654c203d7865741e88667080e020d0460d395`.
Before quarantine, the three independent tests passed in 6.73 seconds.

In the checked-in quarantined state, the independent verifier still
reconstructs all 24 exact empty intersections, confirms that no generated
table or packed declaration remains, and reports the expected verdict
`FAIL_KERNEL_QUARANTINED`.  Its payload digest is
`f51939fb7b2015ee97310d3458a1474832a161949b43a44a3a137d3430df70d9`;
all three quarantine tests pass.

## All 24 exact empty-intersection witnesses

For each row below, `survivors before kill` is the complete set of local bit
indices remaining immediately before the listed prime is intersected.  The
listed prime removes all of them, yielding the zero bitvector.  Thus these
records check the boundary and offset direction more strongly than merely
testing that the final bitset is empty.

| branch | shard | lo | width | kill prime | survivors before kill |
|---:|---:|---:|---:|---:|:---|
| 17 | 0 | 0 | 16,000,000 | 857 | 88,193 |
| 17 | 1 | 16,000,000 | 16,000,000 | 823 | 4,272,914 |
| 17 | 2 | 32,000,000 | 16,000,000 | 857 | 111,689 |
| 17 | 3 | 48,000,000 | 16,000,000 | 919 | 5,730,695 |
| 17 | 4 | 64,000,000 | 16,000,000 | 839 | 843,261; 1,259,563 |
| 17 | 5 | 80,000,000 | 2,503,186 | 907 | 2,297,010 |
| 21 | 0 | 0 | 16,000,000 | 877 | 12,687,134 |
| 21 | 1 | 16,000,000 | 16,000,000 | 881 | 564,167 |
| 21 | 2 | 32,000,000 | 16,000,000 | 821 | 13,923,406 |
| 21 | 3 | 48,000,000 | 16,000,000 | 881 | 8,447,313 |
| 21 | 4 | 64,000,000 | 16,000,000 | 797 | 12,765,533 |
| 21 | 5 | 80,000,000 | 2,503,186 | 761 | 689,289 |
| 25 | 0 | 0 | 16,000,000 | 827 | 12,678,617 |
| 25 | 1 | 16,000,000 | 16,000,000 | 953 | 7,775,358 |
| 25 | 2 | 32,000,000 | 16,000,000 | 821 | 447,869 |
| 25 | 3 | 48,000,000 | 16,000,000 | 839 | 15,029,291 |
| 25 | 4 | 64,000,000 | 16,000,000 | 883 | 2,959,393 |
| 25 | 5 | 80,000,000 | 2,503,185 | 751 | 1,808,792 |
| 29 | 0 | 0 | 16,000,000 | 821 | 11,654,428 |
| 29 | 1 | 16,000,000 | 16,000,000 | 853 | 13,243,689 |
| 29 | 2 | 32,000,000 | 16,000,000 | 857 | 111,711 |
| 29 | 3 | 48,000,000 | 16,000,000 | 787 | 15,495,036 |
| 29 | 4 | 64,000,000 | 16,000,000 | 853 | 4,718,938 |
| 29 | 5 | 80,000,000 | 2,503,185 | 839 | 1,521,729 |

The verifier output also records the corresponding global `q` and `t=46q+b`
values for every survivor.

## Cast and bound audit

- The generic integer-to-`ZMod p` bridge `even22_allowed_int` was expanded at
  `p=23` and typechecked.  Its own axiom set was only
  `[propext, Quot.sound]`; there is no cast gap in that bridge.
- The periodic-mask and balanced-tree semantic lemmas typechecked with only
  permitted standard axioms before quarantine.
- Every width satisfies `width <= 83 * 2^18 = 21,757,952`, which is the exact
  hypothesis needed by every leaf mask.
- The last-chunk upper endpoints are exactly the four branch lengths.  From
  `t=46q+b` and `t<=3,795,146,531`, the generated final dispatch bounds are the
  required strict `q<branch_length` bounds.
- The only decisive gap is not arithmetic or casting: it is the absent clean
  kernel build of the real table-to-cover dependency chain.

## Reproduction commands

Current quarantine and exact-arithmetic audit (no generated declarations
required):

```sh
python3 -m pytest -q \
  compute/campaign686/agent_k22_packed_kernel_audit/test_packed_kernel_hostile_verify.py
PYTHONDONTWRITEBYTECODE=1 python3 \
  compute/campaign686/agent_k22_packed_kernel_audit/packed_kernel_hostile_verify.py
```

The contaminated Lean import harness was removed with the generated
declarations, so the checked-in tree contains no packed audit target importing
those absent declarations.  Any future regenerated cover must add a fresh audit harness
and show that representative `even22_allowed_*` declarations and the terminal
packed theorem report no named axioms beyond `propext`, `Classical.choice`,
and `Quot.sound` before any theorem is promoted.
