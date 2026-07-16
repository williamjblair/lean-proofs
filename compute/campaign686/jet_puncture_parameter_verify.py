#!/usr/bin/env python3
"""Exact parameter and reduced-dimension audit for punctured-grid jets."""

from __future__ import annotations

import json
import math


ROWS = ((5, 1), (7, 1), (9, 1), (11, 2), (13, 3), (15, 6))


def raw_budget_sides(k: int, s: int) -> tuple[int, int, int, int, int]:
    genus = (k - 1) * (k - 2) // 2
    mu = k * s + 2 * genus
    r = k * mu - s
    left = math.factorial(k - 1) ** mu * (k + 1) ** r
    right = 3 ** (k * mu) * 10 ** (1000 * s)
    return genus, mu, r, left, right


def layer_dimension(k: int, residual_degree: int) -> int:
    if residual_degree < 0:
        return 0
    return sum(
        1
        for a in range(k)
        for b in range(k)
        if a + b <= residual_degree
    )


def audit_row(k: int, expected_s: int) -> dict[str, object]:
    genus, mu, r, left, right = raw_budget_sides(k, expected_s)
    assert left < right
    for s in range(1, expected_s):
        _, _, _, earlier_left, earlier_right = raw_budget_sides(k, s)
        assert earlier_left >= earlier_right

    full_layers: list[int] = []
    top_layers: list[dict[str, int]] = []
    for q in range(mu):
        residual_degree = r - k * q
        dimension = layer_dimension(k, residual_degree)
        if residual_degree >= 2 * k - 2:
            assert dimension == k * k
            full_layers.append(q)
        else:
            top_layers.append({
                "q": q,
                "residual_degree": residual_degree,
                "dimension": dimension,
            })

    punctured_grid_size = k * k - 1
    residual_rows = len(top_layers) * punctured_grid_size
    residual_columns = len(full_layers) + sum(layer["dimension"] for layer in top_layers)
    nullity = residual_columns - residual_rows
    assert nullity == genus + 1
    full_columns = len(full_layers) * k * k
    top_columns = sum(layer["dimension"] for layer in top_layers)
    assert full_columns + top_columns == k * r - genus + 1

    return {
        "k": k,
        "first_positive_s": expected_s,
        "genus": genus,
        "mu": mu,
        "r": r,
        "raw_budget_pass": True,
        "raw_budget_ratio_floor_digits": len(str(right // left)) - 1,
        "full_layer_count": len(full_layers),
        "top_layers": top_layers,
        "residual_rows": residual_rows,
        "residual_columns": residual_columns,
        "residual_nullity": nullity,
    }


def main() -> None:
    result = [audit_row(k, s) for k, s in ROWS]
    print(json.dumps({"rows": result, "verdict": "PASS"}, indent=2))


if __name__ == "__main__":
    main()
