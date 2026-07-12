# Erdős 686 center/reflected fifth specialization

## Exact fifth calculation

For the center owner of an odd row, `D = F = 0`.  With reflected offsets
`(r,-r)`, the reduced fifth coefficient is exactly

`R5(d) = 8748 r^4 C (255 C G + 180 E^2) d`.

Thus its constant coefficient is zero and its `d^2` coefficient is zero in
all 54 oriented views.  The linear slope is nonzero in all 27 unoriented
pairs.  The squared fifth congruence therefore does not become a fixed-divisor
contradiction and does not by itself improve the center cubic bound.

## Endpoint determinant

Let `X` be the center residual and let `T_-`, `T_+` be the endpoint third
obstructions.  Exact expansion gives

`(X-3r)T_+ - (X+3r)T_- = 54r(Ct - 8DXg^2r - 40Eg^2r^2d)`.

The left side is divisible by `Q^2 R^2`.  If its inner factor vanished, the
three residual identities would force

`C X(X^2-9r^2) - 8D Xr d^2 - 40E r^2 d^3 = 0`.

The exact ratio bound `R_k d < H_k X`, together with the standard upper
residual ceiling, rules this cubic out in every one of the 27 pairs.  The
finite certificate uses the two positive integer margins

`|C|R_k^2 - 8|D|rH_k^2`

and

`R_k(|C|R_k^2 - 8|D|rH_k^2) - 40|E|r^2H_k^3`.

## Exact packing result

Combining `P^3 < H d`, `Q^2R^2 < K g^2d`, `d=gPQR`, and `g <= G_k` gives

`d < H^2 K^3 G_k^12`.

This is below `10^120` for 12 of the 27 pairs: every pair in rows 5, 7, and
9, and `r=1,2,3` in row 11.  It closes 24 of the 54 oriented views.

The exact surviving gap is a 15-pair (30-oriented-view) list:

- `k=11`, `r=4,5`;
- `k=13`, `1 <= r <= 6`;
- `k=15`, `1 <= r <= 7`.

The first failed cutoff is `k=11,r=4`, where the bound is about `5.574` times
`10^120`; the exact integer is emitted by `reflected_three_bucket_verify.py`.
The minimum row-13 and row-15 failed cutoffs are respectively above
`4.797 * 10^150` and `5.079 * 10^182`.  No higher-order lift is claimed.
