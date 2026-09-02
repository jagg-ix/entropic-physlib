#!/usr/bin/env python3
"""Derive a one-level LDDL linewidth calibration from finite Ohmic bath data.

The exact formal relation is

    gamma = pi * coupling_strength_sq * shape_sum / (4 * cutoff**3).

This tool validates a microscopic-rate input artifact and emits:

* a standard ``calibration.json`` accepted by ``one_level_benchmark.py``; and
* a deterministic ``ohmic-rate-derivation.json`` sidecar recording the source
  digest, formula, theorem identifier, inputs, and the still-conditional physical
  Born--Markov/secular identification.

It never edits the Lean evidence registry and never grants external validation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence

SCHEMA_VERSION = "1.0"
FORMULA_ID = "gamma_eq_pi_coupling_sq_shape_over_4_cutoff_cubed"
UNIT_CONTRACT = "coupling_sq_times_shape_over_cutoff_cubed_is_rate"
LEAN_THEOREM = (
    "lean:QuantumMechanics.LindbladDrivenLeads."
    "gammaFromOhmicCoupling_couplingSq"
)
PHYSICAL_BRIDGE = "weak-coupling-born-markov-secular-identification"


class DerivationError(RuntimeError):
    """Invalid microscopic input or deterministic-output failure."""


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> Any:
    try:
        with path.open("r", encoding="utf-8") as handle:
            return json.load(handle)
    except (OSError, json.JSONDecodeError) as exc:
        raise DerivationError(f"cannot read JSON {path}: {exc}") from exc


def require_mapping(value: Any, field: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        raise DerivationError(f"{field} must be an object")
    return value


def require_string(value: Any, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise DerivationError(f"{field} must be a non-empty string")
    return value


def require_number(value: Any, field: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise DerivationError(f"{field} must be a number")
    result = float(value)
    if not math.isfinite(result):
        raise DerivationError(f"{field} must be finite")
    return result


def require_positive(value: Any, field: str) -> float:
    result = require_number(value, field)
    if result <= 0:
        raise DerivationError(f"{field} must be positive")
    return result


def require_probability(value: Any, field: str) -> float:
    result = require_number(value, field)
    if not 0 < result < 1:
        raise DerivationError(f"{field} must lie in (0,1)")
    return result


def require_unique_strings(value: Any, field: str) -> list[str]:
    if not isinstance(value, list) or not value:
        raise DerivationError(f"{field} must be a non-empty array")
    items = [require_string(item, f"{field}[]") for item in value]
    if len(set(items)) != len(items):
        raise DerivationError(f"{field} must contain unique strings")
    return items


def write_json(path: Path, value: Any) -> str:
    data = canonical_json_bytes(value)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return sha256_bytes(data)


def derive_rate(source_path: Path, output_dir: Path) -> dict[str, Any]:
    source_path = source_path.resolve()
    source = require_mapping(load_json(source_path), "source")
    if source.get("schema_version") != SCHEMA_VERSION:
        raise DerivationError("source.schema_version must equal '1.0'")

    calibration_id = require_string(source.get("calibration_id"), "calibration_id")
    ohmic = require_mapping(source.get("ohmic_coupling"), "ohmic_coupling")
    if ohmic.get("observable") != "finite_ohmic_coupling":
        raise DerivationError(
            "ohmic_coupling.observable must equal 'finite_ohmic_coupling'"
        )
    if ohmic.get("formula_id") != FORMULA_ID:
        raise DerivationError(f"ohmic_coupling.formula_id must equal '{FORMULA_ID}'")
    if ohmic.get("unit_contract") != UNIT_CONTRACT:
        raise DerivationError(
            f"ohmic_coupling.unit_contract must equal '{UNIT_CONTRACT}'"
        )

    coupling_sq = require_positive(
        ohmic.get("coupling_strength_sq"), "ohmic_coupling.coupling_strength_sq"
    )
    cutoff = require_positive(ohmic.get("cutoff"), "ohmic_coupling.cutoff")
    shape_sum = require_positive(ohmic.get("shape_sum"), "ohmic_coupling.shape_sum")
    rate_unit = require_string(ohmic.get("rate_unit"), "ohmic_coupling.rate_unit")
    gamma = math.pi * coupling_sq * shape_sum / (4.0 * cutoff**3)
    if not math.isfinite(gamma) or gamma <= 0:
        raise DerivationError("derived gamma must be finite and positive")

    equilibrium = require_mapping(source.get("equilibrium"), "equilibrium")
    if equilibrium.get("method") != "fermi_dirac_beta_gap":
        raise DerivationError(
            "equilibrium.method must equal 'fermi_dirac_beta_gap'"
        )
    beta_gap = require_number(
        equilibrium.get("beta_energy_gap"), "equilibrium.beta_energy_gap"
    )
    if abs(beta_gap) > 700:
        raise DerivationError(
            "equilibrium.beta_energy_gap must have absolute value <= 700"
        )
    expected = equilibrium.get("expected_occupation")
    if expected is not None:
        require_probability(expected, "equilibrium.expected_occupation")

    initial = require_mapping(source.get("initial_condition"), "initial_condition")
    require_probability(initial.get("occupation"), "initial_condition.occupation")
    source_ids = require_unique_strings(
        source.get("source_observation_ids"), "source_observation_ids"
    )
    if source.get("independent_of_target") is not True:
        raise DerivationError("independent_of_target must be true")

    source_digest = sha256_file(source_path)
    lineage_ids = [
        f"derived-rate-formula:{FORMULA_ID}",
        f"derived-rate-source-sha256:{source_digest}",
        f"derived-rate-theorem:{LEAN_THEOREM}",
    ]
    combined_ids = source_ids + [item for item in lineage_ids if item not in source_ids]

    calibration = {
        "schema_version": SCHEMA_VERSION,
        "calibration_id": calibration_id,
        "linewidth": {
            "observable": "lorentzian_half_width",
            "value": gamma,
            "unit": rate_unit,
        },
        "equilibrium": dict(equilibrium),
        "initial_condition": dict(initial),
        "source_observation_ids": combined_ids,
        "independent_of_target": True,
    }
    calibration_path = output_dir / "calibration.json"
    calibration_digest = write_json(calibration_path, calibration)

    derivation = {
        "schema_version": SCHEMA_VERSION,
        "calibration_id": calibration_id,
        "source_path": source_path.name,
        "source_sha256": source_digest,
        "calibration_sha256": calibration_digest,
        "formula_id": FORMULA_ID,
        "unit_contract": UNIT_CONTRACT,
        "lean_theorem": LEAN_THEOREM,
        "inputs": {
            "coupling_strength_sq": coupling_sq,
            "cutoff": cutoff,
            "shape_sum": shape_sum,
            "rate_unit": rate_unit,
        },
        "derived": {
            "gamma": gamma,
            "lorentzian_half_width": gamma,
            "relaxation_coefficient": 2.0 * gamma,
            "lorentzian_full_width": 2.0 * gamma,
        },
        "physical_bridge": {
            "status": "conditional-model",
            "required_identification": PHYSICAL_BRIDGE,
            "external_calibration_claimed": False,
            "physical_identity_claimed": False,
        },
        "registry_mutation_performed": False,
    }
    derivation_path = output_dir / "ohmic-rate-derivation.json"
    derivation_digest = write_json(derivation_path, derivation)

    return {
        "calibration_path": str(calibration_path),
        "calibration_digest": calibration_digest,
        "derivation_path": str(derivation_path),
        "derivation_digest": derivation_digest,
        "gamma": gamma,
        "physical_bridge_status": "conditional-model",
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="finite-Ohmic calibration source JSON")
    parser.add_argument(
        "--output-dir",
        type=Path,
        required=True,
        help="directory for deterministic outputs",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        summary = derive_rate(args.source, args.output_dir.resolve())
    except DerivationError as exc:
        print(f"Ohmic rate derivation error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
