# k=22 packed-kernel hostile audit plan

1. Reconstruct the `S,T` local tables directly from the exact row polynomial,
   without importing `generate_full_cover.py`.
2. Parse every generated table mask and all 24 packed shard item lists; compare
   them with the independent reconstruction prime by prime and shard by shard.
3. Recompute branch lengths, chunk endpoints, local/global residue directions,
   and every 16,000,000-bit intersection using exact Python integers.
4. Inspect the Lean semantic bridge, casts, imports, dispatch bounds, and axiom
   surfaces; compile the terminal module if its dependency graph is complete.
5. Record PASS/FAIL with the smallest exact witness and focused regression tests.
